@file:Suppress("DEPRECATION")
package com.reactnativeposprinter

import android.bluetooth.BluetoothAdapter
import android.bluetooth.BluetoothSocket
import android.content.Context
import android.graphics.Bitmap
import android.net.nsd.NsdManager
import android.net.nsd.NsdServiceInfo
import java.net.InetSocketAddress
import java.net.NetworkInterface
import java.net.Socket as TcpSocket
import android.graphics.BitmapFactory
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.ColorMatrix
import android.graphics.ColorMatrixColorFilter
import android.graphics.Paint
import android.graphics.Rect
import android.util.Base64
import android.util.Log
import com.facebook.react.bridge.*
import com.facebook.react.module.annotations.ReactModule
import com.facebook.react.modules.core.DeviceEventManagerModule
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.Channel
import java.io.ByteArrayOutputStream
import java.io.IOException
import java.io.OutputStream
import java.util.*
import java.util.concurrent.ConcurrentHashMap

@ReactModule(name = PosPrinterModule.NAME)
class PosPrinterModule(reactContext: ReactApplicationContext) : ReactContextBaseJavaModule(reactContext) {
    data class FormattingResult(
        val shouldUseBitmapRendering: Boolean,
        val fontSizePt: Int?,
        val letterSpacing: Float?
    )

    private var printerService: Any? = null

    companion object {
        const val NAME = "PosPrinter"
        private const val TAG = "PosPrinterModule"
        private val PRINTER_UUID = UUID.fromString("00001101-0000-1000-8000-00805F9B34FB")
        private const val WIFI_DEFAULT_PORT = 9100
        private const val WIFI_CONNECTION_TIMEOUT_MS = 10_000
        private const val WIFI_DISCOVERY_TIMEOUT_MS_DEFAULT = 5_000L
        private const val WIFI_PROBE_TIMEOUT_MS = 200
        private val MDNS_SERVICE_TYPES = listOf("_pdl-datastream._tcp")
        
        private val ESC_COMMANDS = mapOf(
            "INIT" to byteArrayOf(0x1B, 0x40),
            "CUT" to byteArrayOf(0x1D, 0x56, 0x00),
            "ALIGN_LEFT" to byteArrayOf(0x1B, 0x61, 0x00),
            "ALIGN_CENTER" to byteArrayOf(0x1B, 0x61, 0x01),
            "ALIGN_RIGHT" to byteArrayOf(0x1B, 0x61, 0x02),
            "BOLD_ON" to byteArrayOf(0x1B, 0x45, 0x01),
            "BOLD_OFF" to byteArrayOf(0x1B, 0x45, 0x00),
            "UNDERLINE_ON" to byteArrayOf(0x1B, 0x2D, 0x01),
            "UNDERLINE_OFF" to byteArrayOf(0x1B, 0x2D, 0x00),
            "CASH_DRAWER" to byteArrayOf(0x1B, 0x70, 0x00, 0x19, 0xFA.toByte())
        )

        private var lastFontSizeMethod: String = "unknown"
    
        fun getLastFontSizeMethod(): String = lastFontSizeMethod
        fun setLastFontSizeMethod(method: String) {
            lastFontSizeMethod = method
        }
        
        object Events {
            const val DEVICE_CONNECTED = "DEVICE_CONNECTED"
            const val DEVICE_DISCONNECTED = "DEVICE_DISCONNECTED"
            const val DEVICE_CONNECTION_LOST = "DEVICE_CONNECTION_LOST"
            const val PRINT_STATUS = "PRINT_STATUS"
        }
        
        object Errors {
            const val BLUETOOTH_NOT_AVAILABLE = "BLUETOOTH_NOT_AVAILABLE"
            const val BLUETOOTH_DISABLED = "BLUETOOTH_DISABLED"
            const val NOT_CONNECTED = "NOT_CONNECTED"
            const val CONNECTION_FAILED = "CONNECTION_FAILED"
            const val UNSUPPORTED_TYPE = "UNSUPPORTED_TYPE"
            const val PRINT_FAILED = "PRINT_FAILED"
            const val WIFI_CONNECTION_FAILED = "WIFI_CONNECTION_FAILED"
        }
    }
    
    private val bluetoothAdapter: BluetoothAdapter? = BluetoothAdapter.getDefaultAdapter()
    private var bluetoothSocket: BluetoothSocket? = null
    @Volatile private var wifiSocket: TcpSocket? = null
    @Volatile private var wifiAddress: String? = null
    private var outputStream: OutputStream? = null
    private var connectionJob: Job? = null
    
    @Volatile
    private var isConnected = false
    private val scope = CoroutineScope(Dispatchers.IO + SupervisorJob())
    override fun getName(): String = NAME
    override fun onCatalystInstanceDestroy() {
        super.onCatalystInstanceDestroy()
        scope.cancel()
        disconnectPrinter(null)
    }
    
    @ReactMethod
    fun init(@Suppress("UNUSED_PARAMETER") options: ReadableMap?, promise: Promise) {
        try {
            promise.resolve(null)
        } catch (e: Exception) {
            promise.reject("INIT_ERROR", e.message, e)
        }
    }
    
    @ReactMethod
    fun getDeviceList(options: ReadableMap?, promise: Promise) {
        val timeoutMs = options?.takeIf { it.hasKey("discoveryTimeout") }
            ?.getInt("discoveryTimeout")?.toLong()
            ?: WIFI_DISCOVERY_TIMEOUT_MS_DEFAULT

        scope.launch {
            try {
                val deviceList = Arguments.createArray()

                // 1. Bluetooth bonded devices
                if (bluetoothAdapter != null && bluetoothAdapter.isEnabled) {
                    val pairedDevices = bluetoothAdapter.bondedDevices
                    for (device in pairedDevices) {
                        val deviceInfo = Arguments.createMap().apply {
                            putString("name", device.name ?: "Unknown")
                            putString("address", device.address)
                            putString("type", "bluetooth")
                        }
                        deviceList.pushMap(deviceInfo)
                    }
                }

                // 2. WIFI printer discovery: mDNS + ARP-cache fallback
                val wifiDevices = discoverWifiPrinters(timeoutMs)
                for (info in wifiDevices) {
                    deviceList.pushMap(info)
                }

                withContext(Dispatchers.Main) {
                    promise.resolve(deviceList)
                }
            } catch (e: Exception) {
                withContext(Dispatchers.Main) {
                    promise.reject("GET_DEVICES_ERROR", e.message, e)
                }
            }
        }
    }

    /**
     * Discovers ESC/POS WIFI printers using two complementary strategies:
     *  1. mDNS / Bonjour (NsdManager) on `_pdl-datastream._tcp` — catches printers that
     *     advertise themselves as raw ESC/POS listeners on the LAN.
     *  2. Full /24 subnet port scan on port 9100 — catches ESC/POS printers that are on
     *     the same subnet but do not advertise via mDNS (common with low-cost devices).
     *
     * Both strategies run in parallel for [timeoutMs] milliseconds, then results are merged and
     * deduplicated by IP address.
     */
    private suspend fun discoverWifiPrinters(timeoutMs: Long): List<WritableMap> {
        // Keyed by IP address to deduplicate across both strategies
        val discovered = ConcurrentHashMap<String, WritableMap>()

        val mdnsJob = scope.async { discoverViaMdns(timeoutMs, discovered) }
        val scanJob = scope.async { discoverViaSubnetScan(discovered) }

        // Wait for both, ignoring individual failures so we always return what we found
        mdnsJob.runCatching { await() }
        scanJob.runCatching { await() }

        return discovered.values.toList()
    }

    /**
     * Runs NsdManager discovery for the standard ESC/POS and printing service types.
     * Each discovered + resolved service is added to [out] keyed by its IP address.
     */
    private suspend fun discoverViaMdns(
        timeoutMs: Long,
        out: ConcurrentHashMap<String, WritableMap>
    ) {
        val nsdManager = try {
            reactApplicationContext.getSystemService(Context.NSD_SERVICE) as? NsdManager
        } catch (_: Exception) { null } ?: return

        // Channel receives resolved NsdServiceInfo objects; we close it when discovery ends
        val channel = Channel<NsdServiceInfo>(Channel.UNLIMITED)

        // Keep track of active discovery listeners so we can stop them all
        val listeners = mutableListOf<NsdManager.DiscoveryListener>()

        for (serviceType in MDNS_SERVICE_TYPES) {
            val discoveryListener = object : NsdManager.DiscoveryListener {
                override fun onStartDiscoveryFailed(serviceType: String, errorCode: Int) {
                    Log.w(TAG, "mDNS start failed for $serviceType: $errorCode")
                }
                override fun onStopDiscoveryFailed(serviceType: String, errorCode: Int) {
                    Log.w(TAG, "mDNS stop failed for $serviceType: $errorCode")
                }
                override fun onDiscoveryStarted(serviceType: String) {
                    Log.d(TAG, "mDNS discovery started for $serviceType")
                }
                override fun onDiscoveryStopped(serviceType: String) {}
                override fun onServiceFound(serviceInfo: NsdServiceInfo) {
                    // Resolve to get host + port
                    nsdManager.resolveService(serviceInfo, object : NsdManager.ResolveListener {
                        override fun onResolveFailed(serviceInfo: NsdServiceInfo, errorCode: Int) {
                            Log.w(TAG, "mDNS resolve failed: $errorCode")
                        }
                        override fun onServiceResolved(serviceInfo: NsdServiceInfo) {
                            channel.trySend(serviceInfo)
                        }
                    })
                }
                override fun onServiceLost(serviceInfo: NsdServiceInfo) {}
            }
            try {
                nsdManager.discoverServices(serviceType, NsdManager.PROTOCOL_DNS_SD, discoveryListener)
                listeners.add(discoveryListener)
            } catch (e: Exception) {
                Log.w(TAG, "Could not start mDNS discovery for $serviceType: ${e.message}")
            }
        }

        // Drain the channel for [timeoutMs] ms
        val deadline = System.currentTimeMillis() + timeoutMs
        while (System.currentTimeMillis() < deadline) {
            val remaining = deadline - System.currentTimeMillis()
            if (remaining <= 0) break
            val info = withTimeoutOrNull(remaining) { channel.receive() } ?: break

            val host = info.host?.hostAddress ?: continue
            val port = info.port.takeIf { it > 0 } ?: WIFI_DEFAULT_PORT
            val name = info.serviceName ?: "WiFi Printer ($host)"
            val address = "$host:$port"

            out.putIfAbsent(host, Arguments.createMap().apply {
                putString("name", name)
                putString("address", address)
                putString("type", "wifi")
            })
        }

        // Stop all discovery listeners
        for (listener in listeners) {
            try { nsdManager.stopServiceDiscovery(listener) } catch (_: Exception) {}
        }
        channel.close()
    }

    /**
     * Scans all 254 host addresses in the device's /24 subnet for an open ESC/POS port (9100).
     * Already-discovered IPs (from mDNS) and the device's own IP are skipped.
     * All probes run in parallel and each is limited to [WIFI_PROBE_TIMEOUT_MS] ms.
     */
    private suspend fun discoverViaSubnetScan(out: ConcurrentHashMap<String, WritableMap>) {
        val localIp = getLocalIpAddress() ?: return
        val subnet = localIp.substringBeforeLast('.')

        val probeJobs = (1..254).mapNotNull { i ->
            val ip = "$subnet.$i"
            if (ip == localIp || out.containsKey(ip)) return@mapNotNull null
            scope.async {
                val reachable = withContext(Dispatchers.IO) {
                    probePort(ip, WIFI_DEFAULT_PORT, WIFI_PROBE_TIMEOUT_MS)
                }
                if (reachable) {
                    out.putIfAbsent(ip, Arguments.createMap().apply {
                        putString("name", "ESC/POS Printer ($ip)")
                        putString("address", "$ip:$WIFI_DEFAULT_PORT")
                        putString("type", "wifi")
                    })
                }
            }
        }
        probeJobs.forEach { it.runCatching { await() } }
    }

    /** Returns the IPv4 address of the first active non-loopback network interface, or null. */
    private fun getLocalIpAddress(): String? {
        return try {
            Collections.list(NetworkInterface.getNetworkInterfaces())
                .filter { iface -> !iface.isLoopback && iface.isUp }
                .flatMap { iface -> Collections.list(iface.inetAddresses) }
                .firstOrNull { addr ->
                    !addr.isLoopbackAddress &&
                    !addr.hostAddress.isNullOrEmpty() &&
                    !addr.hostAddress!!.contains(':') // skip IPv6
                }
                ?.hostAddress
        } catch (e: Exception) {
            Log.w(TAG, "Could not determine local IP address: ${e.message}")
            null
        }
    }

    /** Attempts a TCP connection to [host]:[port] within [timeoutMs]; returns true on success. */
    private fun probePort(host: String, port: Int, timeoutMs: Int): Boolean {
        return try {
            TcpSocket().use { socket ->
                socket.connect(InetSocketAddress(host, port), timeoutMs)
                true
            }
        } catch (_: Exception) {
            false
        }
    }
    
    @ReactMethod
    fun connectPrinter(address: String, type: String, promise: Promise) {
        when (type.lowercase()) {
            "bluetooth" -> connectBluetoothPrinter(address, promise)
            "wifi", "ethernet" -> connectWifiPrinter(address, promise)
            else -> promise.reject(Errors.UNSUPPORTED_TYPE, "Unsupported printer type: $type")
        }
    }
    
    @ReactMethod
    fun disconnectPrinter(promise: Promise?) {
        try {
            connectionJob?.cancel()
            outputStream?.close()
            bluetoothSocket?.close()
            wifiAddress = null
            wifiSocket?.close()
            outputStream = null
            bluetoothSocket = null
            wifiSocket = null
            isConnected = false
            
            sendEvent(Events.DEVICE_DISCONNECTED, Arguments.createMap())
            promise?.resolve(true)
        } catch (e: Exception) {
            promise?.reject("DISCONNECT_ERROR", e.message, e)
        }
    }
    
    @ReactMethod
    fun isConnected(promise: Promise) {
        promise.resolve(isConnected)
    }

    @ReactMethod
    fun printText(text: String, options: ReadableMap?, promise: Promise) {
        if (text.isEmpty()) {
            promise.reject(Errors.UNSUPPORTED_TYPE, "Text cannot be empty")
            return
        }

        executeWithConnection(promise) { stream ->
            try {
                var usedBitmapRendering = false
                var formattingResult: TextFormattingHandler.FormattingResult? = null
                var bitmapStyle: TextToBitmapHandler.TextStyle? = null
                var bitmapFontSize: Float = 12.0f
                var bitmapLetterSpacing: Float = 1.0f
                val alignValue = options?.getString("align")?.lowercase() ?: "left"

                options?.let {
                    formattingResult = applyTextFormatting(it, stream)

                    val needsBitmapForFont = options.hasKey("fontType") && options.getString("fontType") != "A"
                    val needsBitmapForStyling = (options.hasKey("bold") && options.getBoolean("bold")) ||
                                                (options.hasKey("italic") && options.getBoolean("italic")) ||
                                                (options.hasKey("underline") && options.getBoolean("underline"))
                    val needsBitmapForSize = options.hasKey("size") && (options.getInt("size") > 0)
                    val needsBitmapForAlignment = alignValue != "left"

                    if (formattingResult?.shouldUseBitmapRendering == true || needsBitmapForFont || needsBitmapForStyling || needsBitmapForSize || needsBitmapForAlignment) {
                        usedBitmapRendering = true

                        val fontFamily = if (options.hasKey("fontType")) {
                            when (options.getString("fontType")?.uppercase()) {
                                "A" -> "monospace"
                                "B" -> "sans-serif"
                                "C" -> "serif"
                                else -> "monospace"
                            }
                        } else "monospace"

                        val isBold = if (options.hasKey("bold")) options.getBoolean("bold") else false
                        val isItalic = if (options.hasKey("italic")) options.getBoolean("italic") else false
                        val isUnderline = if (options.hasKey("underline")) options.getBoolean("underline") else false
                        val isStrikethrough = if (options.hasKey("strikethrough")) options.getBoolean("strikethrough") else false
                        val doubleWidth = if (options.hasKey("doubleWidth")) options.getBoolean("doubleWidth") else false
                        val doubleHeight = if (options.hasKey("doubleHeight")) options.getBoolean("doubleHeight") else false

                        bitmapStyle = TextToBitmapHandler.TextStyle(
                            isBold = isBold,
                            isItalic = isItalic,
                            isUnderline = isUnderline,
                            isStrikethrough = isStrikethrough,
                            fontFamily = fontFamily,
                            align = alignValue,
                            doubleWidth = doubleWidth,
                            doubleHeight = doubleHeight
                        )

                        bitmapFontSize = formattingResult?.fontSizePt?.toFloat() ?: 12.0f
                        bitmapLetterSpacing = formattingResult?.letterSpacing ?: 1.0f 
                    } else {
                        stream.write(ESC_COMMANDS["ALIGN_LEFT"]!!)
                    }
                } ?: run {
                    stream.write(ESC_COMMANDS["ALIGN_LEFT"]!!)
                }

                fun containsBangla(s: String): Boolean {
                    for (ch in s) {
                        if (ch in '\u0980'..'\u09FF') return true
                    }
                    return false
                }

                if (!usedBitmapRendering && containsBangla(text)) {
                    usedBitmapRendering = true
                    if (bitmapStyle == null) {
                        bitmapStyle = TextToBitmapHandler.TextStyle(
                            fontFamily = "sans-serif",
                            align = alignValue
                        )
                    }
                    bitmapFontSize = formattingResult?.fontSizePt?.toFloat() ?: 12.0f
                    bitmapLetterSpacing = formattingResult?.letterSpacing ?: 1.0f
                }

                if (usedBitmapRendering) {
                    val maxLineWidth = 32
                    val textToBitmapHandler = TextToBitmapHandler(reactApplicationContext)
                    val allLines = breakTextIntoLinesWithWordBreaking(text, maxLineWidth)
                    val multiLineText = allLines.filter { it.isNotEmpty() }.joinToString("\n")
                    val isBanglaText = containsBangla(text)
                    val lineSpacing = if (isBanglaText) 1.0f else TextToBitmapHandler.DEFAULT_LINE_SPACING
                    when (alignValue.uppercase()) {
                        "CENTER" -> stream.write(ESC_COMMANDS["ALIGN_CENTER"]!!)
                        "RIGHT" -> stream.write(ESC_COMMANDS["ALIGN_RIGHT"]!!)
                        else -> stream.write(ESC_COMMANDS["ALIGN_LEFT"]!!)
                    }
                    stream.flush()

                    val ok = try {
                        textToBitmapHandler.printTextAsBitmap(
                            multiLineText,
                            bitmapFontSize,
                            stream,
                            bitmapLetterSpacing,
                            lineSpacing = lineSpacing,
                            style = bitmapStyle!!,
                            appendLineFeed = true
                        )
                    } catch (e: Exception) {
                        Log.e(TAG, "Exception while printing bitmap: ${e.message}")
                        false
                    }

                    if (!ok) {
                        try {
                            stream.write(ESC_COMMANDS["INIT"]!!)
                            stream.flush()
                        } catch (_: Exception) {
                        }
                        Log.e(TAG, "Bitmap printing failed — sent INIT to recover printer state")
                    }
                } else {
                    val maxLineWidth = 32
                    val allLines = breakTextIntoLines(text, maxLineWidth)

                    for (line in allLines) {
                        stream.write("$line\n".toByteArray(Charsets.UTF_8))
                    }
                }

                stream.flush()
            } catch (e: Exception) {
                throw IOException("Failed to write text: ${e.message}", e)
            }
        }
    }

    private fun breakTextIntoLinesWithWordBreaking(text: String, maxLineWidth: Int): List<String> {
        val lines = mutableListOf<String>()
        val originalLines = text.split("\n")

        for (line in originalLines) {
            if (line.isEmpty()) {
                lines.add("")
                continue
            }

            var remaining = line
            while (remaining.length > maxLineWidth) {
                val candidate = remaining.substring(0, maxLineWidth)
                val lastSpaceIndex = candidate.indexOfLast { it.isWhitespace() }

                if (lastSpaceIndex >= 0) {
                    lines.add(remaining.substring(0, lastSpaceIndex))
                    remaining = remaining.substring(lastSpaceIndex + 1)
                } else {
                    lines.add(candidate)
                    remaining = remaining.substring(maxLineWidth)
                }
            }
            if (remaining.isNotEmpty()) {
                lines.add(remaining)
            }
        }

        return lines
    }

    private fun breakTextIntoLines(text: String, maxLineWidth: Int): List<String> {
        val lines = mutableListOf<String>()
        val originalLines = text.split("\n")

        for (line in originalLines) {
            if (line.isEmpty()) {
                lines.add("")
                continue
            }

            if (line.length <= maxLineWidth) {
                lines.add(line)
            } else {
                var currentLine = ""
                val words = line.split("\\s+".toRegex())

                for (word in words) {
                    val trimmedWord = word.trim()
                    if (trimmedWord.isEmpty()) continue

                    if (currentLine.isEmpty()) {
                        currentLine = trimmedWord
                    } else {
                        val newLine = "$currentLine $trimmedWord"
                        if (newLine.length > maxLineWidth) {
                            lines.add(currentLine)
                            currentLine = trimmedWord
                        } else {
                            currentLine = newLine
                        }
                    }
                }

                if (currentLine.isNotEmpty()) {
                    lines.add(currentLine)
                }
            }
        }

        return lines
    }

    private fun applyTextFormatting(options: ReadableMap, stream: OutputStream): TextFormattingHandler.FormattingResult {
        val formattingHandler = TextFormattingHandler(printerService, reactApplicationContext)
        return formattingHandler.applyFormatting(options, stream)
    }

    @ReactMethod
    fun printImage(base64Image: String, options: ReadableMap?, promise: Promise) {
        executeWithConnection(promise) { stream ->
            try {
                val align = options?.getString("align") ?: "LEFT"
                when (align.uppercase()) {
                    "CENTER" -> stream.write(ESC_COMMANDS["ALIGN_CENTER"]!!)
                    "RIGHT" -> stream.write(ESC_COMMANDS["ALIGN_RIGHT"]!!)
                    else -> stream.write(ESC_COMMANDS["ALIGN_LEFT"]!!)
                }

                val imageBytes = Base64.decode(base64Image, Base64.DEFAULT)
                val factoryOptions = BitmapFactory.Options().apply { inSampleSize = 2 }
                var originalBitmap = BitmapFactory.decodeByteArray(imageBytes, 0, imageBytes.size, factoryOptions)
                originalBitmap = convertToWhiteBackground(originalBitmap)

                val maxWidth = 384
                val chunkHeight = 8
                val widthAligned = (maxWidth / 8) * 8
                val aspectRatio = originalBitmap.height.toFloat() / originalBitmap.width
                val scaledHeight = (widthAligned * aspectRatio).toInt()
                val paddedHeight = ((scaledHeight + chunkHeight - 1) / chunkHeight) * chunkHeight

                val finalBitmap = Bitmap.createBitmap(widthAligned, paddedHeight, Bitmap.Config.ARGB_8888)
                val canvas = Canvas(finalBitmap)
                val paint = Paint(Paint.ANTI_ALIAS_FLAG or Paint.FILTER_BITMAP_FLAG)
                canvas.drawColor(Color.WHITE)
                canvas.drawBitmap(originalBitmap, Rect(0, 0, originalBitmap.width, originalBitmap.height), Rect(0, 0, widthAligned, scaledHeight), paint)

                val rasterBytes = convertBitmapToRasterChunks(finalBitmap, chunkHeight)
                for (chunk in rasterBytes) {
                    stream.write(chunk)
                    Thread.sleep(50)
                }

                stream.write(byteArrayOf(0x1B, 0x33, 0x00))
                stream.write(byteArrayOf(0x0A, 0x0A))
                stream.write(ESC_COMMANDS["ALIGN_LEFT"]!!)

            } catch (e: Exception) {
                throw IOException("Failed to print image: ${e.message}")
            }
        }
    }

    private fun convertToWhiteBackground(bitmap: Bitmap): Bitmap {
        val result = Bitmap.createBitmap(bitmap.width, bitmap.height, Bitmap.Config.ARGB_8888)
        val canvas = Canvas(result)
        canvas.drawColor(Color.WHITE)
        val paint = Paint().apply {
            colorFilter = ColorMatrixColorFilter(ColorMatrix().apply { setSaturation(0f) })
        }
        canvas.drawBitmap(bitmap, 0f, 0f, paint)
        return result
    }

    private fun convertBitmapToRasterChunks(bitmap: Bitmap, chunkHeight: Int): List<ByteArray> {
        val width = bitmap.width
        val height = bitmap.height
        val widthBytes = width / 8
        val chunks = mutableListOf<ByteArray>()
        var y = 0

        while (y < height) {
            val blockHeight = minOf(chunkHeight, height - y)
            val baos = ByteArrayOutputStream()

            baos.write(byteArrayOf(0x1D, 0x76, 0x30, 0x00))
            baos.write(widthBytes and 0xFF)
            baos.write((widthBytes shr 8) and 0xFF)
            baos.write(blockHeight and 0xFF)
            baos.write((blockHeight shr 8) and 0xFF)

            for (row in 0 until blockHeight) {
                for (byteX in 0 until widthBytes) {
                    var byte = 0
                    for (bit in 0 until 8) {
                        val x = byteX * 8 + bit
                        val pixel = bitmap.getPixel(x, y + row)
                        val r = (pixel shr 16) and 0xFF
                        val g = (pixel shr 8) and 0xFF
                        val b = pixel and 0xFF
                        val luminance = (0.299 * r + 0.587 * g + 0.114 * b).toInt()
                        if (luminance < 127) byte = byte or (1 shl (7 - bit))
                    }
                    baos.write(byte)
                }
            }

            chunks.add(baos.toByteArray())
            y += blockHeight
        }

        return chunks
    }

    @ReactMethod
    fun printBarcode(data: String, type: String, options: ReadableMap?, promise: Promise) {
        executeWithConnection(promise) { stream ->
            try {
                val align = options?.getString("align") ?: "CENTER"
                val height = options?.getInt("height") ?: 60
                val width = options?.getInt("width") ?: 2
                val textPosition = options?.getString("textPosition") ?: "BELOW"
                
                when (align.uppercase()) {
                    "LEFT" -> stream.write(ESC_COMMANDS["ALIGN_LEFT"]!!)
                    "CENTER" -> stream.write(ESC_COMMANDS["ALIGN_CENTER"]!!)
                    "RIGHT" -> stream.write(ESC_COMMANDS["ALIGN_RIGHT"]!!)
                }
                
                val barcodeType = when (type.uppercase()) {
                    "UPC_A" -> 0
                    "UPC_E" -> 1
                    "EAN13" -> 2
                    "EAN8" -> 3
                    "CODE39" -> 4
                    "ITF" -> 5
                    "CODABAR" -> 6
                    "CODE93" -> 7
                    "CODE128" -> 8
                    else -> 8
                }
                
                stream.write(byteArrayOf(0x1D, 0x68, height.toByte()))
                stream.write(byteArrayOf(0x1D, 0x77, width.toByte()))
                
                val hriPosition = when (textPosition.uppercase()) {
                    "NONE" -> 0
                    "ABOVE" -> 1
                    "BELOW" -> 2
                    "BOTH" -> 3
                    else -> 2
                }
                stream.write(byteArrayOf(0x1D, 0x48, hriPosition.toByte()))
                
                stream.write(byteArrayOf(0x1D, 0x6B, barcodeType.toByte()))
                stream.write(data.toByteArray())
                stream.write(byteArrayOf(0x00))
                
                stream.write(ESC_COMMANDS["ALIGN_LEFT"]!!)
            } catch (e: Exception) {
                throw IOException("Failed to print barcode: ${e.message}", e)
            }
        }
    }
    
    @ReactMethod
    fun printQRCode(data: String, options: ReadableMap?, promise: Promise) {
        executeWithConnection(promise) { stream ->
            try {
                val align = options?.getString("align") ?: "CENTER"
                val size = options?.getInt("size") ?: 5
                val errorLevel = options?.getString("errorLevel") ?: "M"
                
                when (align.uppercase()) {
                    "LEFT" -> stream.write(ESC_COMMANDS["ALIGN_LEFT"]!!)
                    "CENTER" -> stream.write(ESC_COMMANDS["ALIGN_CENTER"]!!)
                    "RIGHT" -> stream.write(ESC_COMMANDS["ALIGN_RIGHT"]!!)
                }
                
                stream.write(byteArrayOf(0x1D, 0x28, 0x6B, 0x04, 0x00, 0x31, 0x41, 0x32, 0x00))
                stream.write(byteArrayOf(0x1D, 0x28, 0x6B, 0x03, 0x00, 0x31, 0x43, size.toByte()))
                
                val errorLevelByte = when (errorLevel.uppercase()) {
                    "L" -> 0x30.toByte()
                    "M" -> 0x31.toByte()
                    "Q" -> 0x32.toByte()
                    "H" -> 0x33.toByte()
                    else -> 0x31.toByte()
                }
                stream.write(byteArrayOf(0x1D, 0x28, 0x6B, 0x03, 0x00, 0x31, 0x45, errorLevelByte))
                
                val dataBytes = data.toByteArray(Charsets.UTF_8)
                val dataLength = dataBytes.size + 3
                val pL = (dataLength and 0xFF).toByte()
                val pH = ((dataLength shr 8) and 0xFF).toByte()
                
                stream.write(byteArrayOf(0x1D, 0x28, 0x6B, pL, pH, 0x31, 0x50, 0x30))
                stream.write(dataBytes)
                
                stream.write(byteArrayOf(0x1D, 0x28, 0x6B, 0x03, 0x00, 0x31, 0x51, 0x30))
                
                stream.flush()
                Thread.sleep(100)
                
                stream.write(ESC_COMMANDS["ALIGN_LEFT"]!!)
            } catch (e: Exception) {
                throw IOException("Failed to print QR code: ${e.message}", e)
            }
        }
    }
    
    @ReactMethod
    fun cutPaper(promise: Promise) {
        executeWithConnection(promise) { stream ->
            stream.write(ESC_COMMANDS["CUT"]!!)
        }
    }
    
    @ReactMethod
    fun openCashDrawer(promise: Promise) {
        executeWithConnection(promise) { stream ->
            stream.write(ESC_COMMANDS["CASH_DRAWER"]!!)
        }
    }
    
    @ReactMethod
    fun sendRawCommand(command: ReadableArray, promise: Promise) {
        executeWithConnection(promise) { stream ->
            val bytes = ByteArray(command.size())
            for (i in 0 until command.size()) {
                bytes[i] = command.getInt(i).toByte()
            }
            stream.write(bytes)
        }
    }
    
    @ReactMethod
    fun getStatus(promise: Promise) {
        val status = Arguments.createMap().apply {
            putBoolean("connected", isConnected)
            putString("platform", "android")
        }
        promise.resolve(status)
    }

    @ReactMethod
    fun enterPrinterBuffer(clear: Boolean, promise: Promise) {
        try {
            printerService?.let { service ->
                val method = service.javaClass.getMethod("enterPrinterBuffer", Boolean::class.java)
                method.invoke(service, clear)
                promise.resolve(true)
            } ?: promise.reject("NO_SERVICE", "Printer service not available")
        } catch (e: Exception) {
            promise.reject("BUFFER_ERROR", "enterPrinterBuffer failed: ${e.message}")
        }
    }
    
    @ReactMethod
    fun exitPrinterBuffer(commit: Boolean, promise: Promise) {
        try {
            printerService?.let { service ->
                val method = service.javaClass.getMethod("exitPrinterBuffer", Boolean::class.java)
                method.invoke(service, commit)
                promise.resolve(true)
            } ?: promise.reject("NO_SERVICE", "Printer service not available")
        } catch (e: Exception) {
            promise.reject("BUFFER_ERROR", "exitPrinterBuffer failed: ${e.message}")
        }
    }
    
    @ReactMethod
    fun commitPrinterBuffer(promise: Promise) {
        try {
            printerService?.let { service ->
                val method = service.javaClass.getMethod("commitPrinterBuffer")
                method.invoke(service)
                promise.resolve(true)
            } ?: promise.reject("NO_SERVICE", "Printer service not available")
        } catch (e: Exception) {
            promise.reject("BUFFER_ERROR", "commitPrinterBuffer failed: ${e.message}")
        }
    }

    @ReactMethod
    fun resetPrinter(promise: Promise) {
        executeWithConnection(promise) { stream ->
            stream.write(ESC_COMMANDS["INIT"]!!)
            stream.flush()
        }
    }
    
    private fun connectBluetoothPrinter(address: String, promise: Promise) {
        connectionJob = scope.launch {
            try {
                val device = bluetoothAdapter?.getRemoteDevice(address)
                if (device == null) {
                    withContext(Dispatchers.Main) {
                        promise.reject(Errors.CONNECTION_FAILED, "Device not found")
                    }
                    return@launch
                }
                
                bluetoothSocket = device.createRfcommSocketToServiceRecord(PRINTER_UUID)
                bluetoothSocket?.connect()
                outputStream = bluetoothSocket?.outputStream
                
                withContext(Dispatchers.Main) {
                    if (bluetoothSocket?.isConnected == true) {
                        isConnected = true

                        outputStream?.write(ESC_COMMANDS["INIT"]!!)
                        outputStream?.flush()

                        sendEvent(Events.DEVICE_CONNECTED, Arguments.createMap())
                        promise.resolve(true)
                    } else {
                        promise.reject(Errors.CONNECTION_FAILED, "Failed to connect")
                    }
                }
            } catch (e: Exception) {
                withContext(Dispatchers.Main) {
                    promise.reject(Errors.CONNECTION_FAILED, e.message, e)
                }
            }
        }
    }

    private fun connectWifiPrinter(address: String, promise: Promise) {
        connectionJob = scope.launch {
            val socket = TcpSocket()
            try {
                // Support "host:port" format; fall back to the default ESC/POS port
                val host: String
                val port: Int
                if (address.contains(':')) {
                    val parts = address.split(':', limit = 2)
                    host = parts[0]
                    port = parts[1].toIntOrNull() ?: WIFI_DEFAULT_PORT
                } else {
                    host = address
                    port = WIFI_DEFAULT_PORT
                }

                socket.connect(InetSocketAddress(host, port), WIFI_CONNECTION_TIMEOUT_MS)
                wifiAddress = address
                wifiSocket = socket
                outputStream = socket.getOutputStream()

                isConnected = true
                outputStream?.write(ESC_COMMANDS["INIT"] ?: byteArrayOf(0x1B, 0x40))
                outputStream?.flush()

                withContext(Dispatchers.Main) {
                    sendEvent(Events.DEVICE_CONNECTED, Arguments.createMap())
                    promise.resolve(true)
                }
            } catch (e: Exception) {
                // Close the socket if we failed or the job was cancelled before assignment
                if (wifiSocket !== socket) {
                    runCatching { socket.close() }
                }
                withContext(Dispatchers.Main) {
                    promise.reject(Errors.WIFI_CONNECTION_FAILED, "Failed to connect to WIFI printer: ${e.message}", e)
                }
            }
        }
    }
    
    private inline fun executeWithConnection(promise: Promise, action: (OutputStream) -> Unit) {
        if (!isConnected || outputStream == null) {
            promise.reject(Errors.NOT_CONNECTED, "Printer not connected")
            return
        }
        
        try {
            action(outputStream!!)
            promise.resolve(null)
        } catch (e: IOException) {
            Log.e(TAG, "Print operation failed", e)
            promise.reject(Errors.CONNECTION_FAILED, "Print failed: ${e.message}", e)
        }
    }
    
    private fun sendEvent(eventName: String, params: WritableMap) {
        reactApplicationContext
            .getJSModule(DeviceEventManagerModule.RCTDeviceEventEmitter::class.java)
            .emit(eventName, params)
    }

    private fun convertToMonochrome(bitmap: Bitmap): Bitmap {
        val monoBitmap = Bitmap.createBitmap(bitmap.width, bitmap.height, Bitmap.Config.ARGB_8888)
        val canvas = Canvas(monoBitmap)

        val paint = Paint().apply {
            colorFilter = ColorMatrixColorFilter(ColorMatrix().apply { setSaturation(0f) })
        }

        canvas.drawBitmap(bitmap, 0f, 0f, paint)

        val pixels = IntArray(bitmap.width * bitmap.height)
        monoBitmap.getPixels(pixels, 0, bitmap.width, 0, 0, bitmap.width, bitmap.height)

        for (i in pixels.indices) {
            val gray = Color.red(pixels[i])
            pixels[i] = if (gray < 128) Color.BLACK else Color.WHITE
        }

        monoBitmap.setPixels(pixels, 0, bitmap.width, 0, 0, bitmap.width, bitmap.height)
        return monoBitmap
    }
}