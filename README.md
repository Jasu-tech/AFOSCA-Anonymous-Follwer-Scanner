# AFOSCA V2.MAP5

ESP32-C5 BLE/WiFi tracker with GPS tracking, SD card storage, deauth detection, and web interface
![Screenshot_20260214_155947_Chrome](https://github.com/user-attachments/assets/80e656d8-5793-4494-9567-9ced368d09f1)

## Features

- **BLE Scanning** - Detects and tracks Bluetooth Low Energy devices with NimBLE library
- **WiFi Scanning** - Identifies nearby WiFi networks and access points (async, non-blocking)
- **GPS Tracking** - Records device encounter locations using phone GPS and/or external GPS module
- **Automatic GPS Baud Detection** - Tries 9600, 38400, 57600, 115200 automatically when external GPS module is connected
- **SD Card Storage** - Persistent storage for all findings, whitelist, and settings with automatic reinit on failure
- **NVS Backup** - Whitelist, hotspot config, GPS settings and filter state saved to ESP32 internal flash - survives SD card failures
- **Deauth Detection** - Monitors for WiFi deauthentication attacks with LED alarm
- **Web Interface** - Built-in web server for viewing tracked devices, maps, and settings
- **Persistence Score** - Calculates threat level (1-7) based on time windows, RSSI variance, and encounter frequency
- **Offline Map** - Self-contained canvas-drawn map showing device encounter route (no internet needed)
- **Maps App Integration** - Opens encounter location in phone's native maps app (Google Maps on Android, Apple Maps on iOS)
- **Encounter Detection** - Automatically detects new encounters based on time gap (5 min) or distance (500m)

## Hardware Requirements

- ESP32-C5 development board
- GPS module (serial connection, optional - phone GPS can be used instead)
- SD card module (SPI connection)
- Onboard RGB LED (for deauth alarm, GPIO 27)

## Pin Configuration

### SPI (SD Card)

| Signal | ESP32-C5 Pin |
|--------|-------------|
| MOSI   | GPIO 2      |
| MISO   | GPIO 3      |
| SCK    | GPIO 1      |
| CS     | GPIO 0      |

### GPS Module (Optional)

| Signal | ESP32-C5 Pin |
|--------|-------------|
| GPS TX → ESP32 RX | GPIO 4 |
| GPS RX ← ESP32 TX | GPIO 5 |

## Software Requirements

- Arduino IDE
- ESP32-C5 board support package (Arduino Core 3.x)
- Required libraries:
  - **NimBLE-Arduino** - BLE scanning
  - **TinyGPS++** - GPS data parsing
  - **SD** - SD card file system (included with ESP32 core)
  - **WebServer** - HTTP server (included with ESP32 core)
  - **Preferences** - NVS flash storage (included with ESP32 core)

## Installation

1. Install Arduino IDE
2. Add ESP32-C5 board support via Board Manager
3. Install NimBLE-Arduino and TinyGPS++ libraries via Library Manager
4. Open `AFOSCA_V2_MAP5.ino`
5. Select your ESP32-C5 board and port
6. Upload

![Settings](https://github.com/user-attachments/assets/494b70fa-6e1a-48dc-a1b3-38b83b6d950d)

---

## User Guide

### 1. SD Card Preparation

The SD card must be formatted as **FAT32** before first use. ExFAT and NTFS are not supported.

**Windows:** For cards 32 GB or smaller, the built-in Windows formatter works fine. For cards larger than 32 GB, use the "guiformat" tool to format as FAT32.

### 2. Hotspot Configuration (WiFi Connection to Phone)

The device connects to your phone's WiFi hotspot. The connection settings are defined in a text file stored on the SD card.

**Create the file:** On your computer, create a file named `hotspot_config.txt` in the root of the SD card and write:

```
SSID=YourPhoneHotspotName
PASSWORD=YourHotspotPassword
```

**Example:** If your phone's hotspot name is "iPhone-John" and the password is "mypassword123":

```
SSID=iPhone-John
PASSWORD=mypassword123
```

**How to change hotspot name on your phone:**
- **iPhone:** Settings > General > About > Name > Change to your preferred name
- **Android:** Settings > Mobile Hotspot > Hotspot name > Change name
- Then update the SAME name in the `hotspot_config.txt` file on the SD card

**Optional: Static IP Address**

If you want the device to always get the same IP address (easier to remember), add these lines:

```
SSID=YourPhoneHotspotName
PASSWORD=YourHotspotPassword
STATIC_IP=192.168.43.100
GATEWAY=192.168.43.1
USE_STATIC_IP=1
```

- `STATIC_IP` = The device's IP address (use an address within the hotspot's network range)
- `GATEWAY` = The phone's IP address (usually 192.168.43.1 on Android)
- `USE_STATIC_IP=1` = Enable static IP (0 = disable)

**iPhone hotspot:** Use gateway `172.20.10.1` and IP e.g. `172.20.10.100`

```
SSID=iPhone-John
PASSWORD=mypassword123
STATIC_IP=172.20.10.100
GATEWAY=172.20.10.1
USE_STATIC_IP=1
```

**Note:** Hotspot settings are automatically backed up to the device's internal memory. If the SD card fails, the device can still connect to your hotspot using saved settings.

### 3. Startup and Connection

1. Insert the SD card into the device (with hotspot_config.txt ready)
2. Turn on your phone's hotspot
3. Power on the device (USB power or battery)
4. The device connects automatically to your phone's hotspot
5. The IP address is shown in Serial Monitor (Arduino IDE, 115200 baud):
   ```
   [WiFi] CONNECTED SUCCESSFULLY!
   [WiFi] IP address: 192.168.43.100
   [WiFi] Open in browser: http://192.168.43.100
   ```
6. If you used a static IP, you already know the address

### 4. Browser and Web Interface

Open your phone's browser and go to the device's IP address (shown in Serial Monitor or the static IP you configured).

**Browser choice and GPS location:**

The device can use your phone's GPS to improve location accuracy. This requires browser location permission.

- **Firefox (recommended):** Works out of the box with no extra settings. Allows GPS location over HTTP connections.

- **Chrome:** Requires an extra setting because Chrome blocks GPS on HTTP pages:
  1. Type in the address bar: `chrome://flags`
  2. Search for: "Insecure origins treated as secure"
  3. Add to the field: `http://YOUR_DEVICE_IP` (e.g., `http://192.168.43.100`)
  4. Press "Enable" and restart Chrome

- **Safari (iPhone):** Usually works directly, just allow location when the browser asks

**Web interface pages:**
- **Main view** - All detected devices sorted by threat level
- **BLE** - Bluetooth devices
- **WiFi** - WiFi devices and routers
- **Randomized** - Devices with randomized MAC addresses
- **Whitelist** - Your own/known devices (no alerts triggered)
- **Routers** - Identified routers

### 5. Device Management

**Whitelist (your own devices):**
- Add your own devices to the whitelist so they don't trigger alerts
- From the web interface: press "Add to Whitelist" on the device card
- To remove: press "Remove from Whitelist"
- Whitelist is automatically backed up to internal memory and survives SD card failures

**Routers:**
- Known routers are automatically identified by name
- You can also add/remove them manually from the web interface

### 6. Threat Levels and Alerts

The device calculates a threat level (1-7) for each detected device:

| Level | Color | Meaning |
|-------|-------|---------|
| 1 | Green | Normal, no threat |
| 2 | Light green | Low |
| 3 | Yellow | Minor attention |
| 4 | Orange | Moderate |
| 5 | Red | High - map buttons available |
| 6 | Dark red | Very high |
| 7 | Black | Critical |

Levels 5-7 display two map buttons:
- **Maps App** - Opens the encounter location in your phone's native maps app (supports offline maps)
- **Offline Map** - Shows a self-contained map drawn directly on the page (works without any internet connection)

### 7. GPS Source Selection

The device supports three GPS modes (configurable from the web interface):

- **Phone** - Uses your phone's browser GPS (default, no extra hardware needed)
- **Device** - Uses an external GPS module connected via serial (GPIO 4/5)
- **Both** - Uses both sources simultaneously for best accuracy

When an external GPS module is connected, the device automatically detects the correct baud rate (tries 9600, 38400, 57600, 115200). The web interface shows the GPS status:
- **Init** (blue) - Waiting for first data
- **Auto** (blue) - Trying different baud rates
- **Satellite count** (green) - GPS module working
- **NoGPS** (orange) - No GPS module detected after all baud rates tried
- **RX/TX!** (red) - Wires may be swapped

GPS settings are locked by default (lock icon in the web interface). Unlock to change settings.

### 8. Deauth Alert

If the device detects a WiFi deauthentication attack:
- The RGB LED flashes red
- A warning icon appears in the web interface
- The counter resets after 5 minutes of inactivity

### 9. SD Card and Firmware Updates

The SD card does NOT need to be formatted when updating the firmware. The device automatically detects both old and new storage formats. The SD card can remain inserted during code upload.

### 10. SD Card Reliability

The device includes multiple protections against SD card failures:
- Automatic reinitilization when the SD card disconnects
- Health check every 30 seconds
- Failure counter with automatic recovery
- All critical settings (whitelist, hotspot, GPS config) backed up to internal memory (NVS)
- The device continues to function without the SD card using NVS backups

> **Suomenkieliset ohjeet:** Katso [README_FI.md](README_FI.md)

---

## SD Card File Structure

```
/hotspot_config.txt  - WiFi hotspot settings (SSID, password, IP)
/all_findings.txt    - All tracked devices (auto-saved)
/whitelist.txt       - Whitelisted device MACs
/routers.txt         - Known router MACs
/gps_source_config.txt - GPS source setting (0=Device, 1=Phone, 2=Both)
/gps_lock_config.txt   - Settings lock state
```

The device supports two SD file formats and auto-detects which one is in use:
- **New format**: `TYPE,MAC,NAME,HIT_COUNT,ENC_COUNT,FIRST_SEEN,LAST_SEEN,ENCOUNTER_COORDS`
- **Old format**: `MAC,TYPE,NAME,LAST_SEEN,RSSI,LAT,LON,...`

## Persistence Score System

Devices are scored 0.0-1.0 based on:
- **Time windows** - Presence across 3 configurable time windows (0-10, 10-20, 20-30 min)
- **Encounter count** - Number of separate encounters (normalized, cap at 7)
- **RSSI stability** - Low variance indicates consistent following distance
- **Appearance frequency** - How often device appears in scans

Threat levels: 1 (Low) through 7 (Critical)

## NVS Backup (Internal Memory)

The following settings are automatically saved to the ESP32's internal flash memory and restored when the SD card is unavailable:
- Whitelist (up to ~200 MAC addresses)
- Hotspot configuration (SSID, password, static IP, gateway)
- GPS source setting (Phone/Device/Both)
- GPS lock state
- Filter state (enabled/disabled)

## Version History

### V2.MAP5 (Current)
- Offline map feature with canvas-drawn encounter route
- Cross-platform Maps App button (Android/iOS)
- External GPS module support with automatic baud rate detection
- NVS backup for whitelist, hotspot config, GPS settings, filter state
- SD card reliability: watchdog, failure counter, automatic reinit, health check
- WiFi async scanning (non-blocking)
- WiFi reconnect with static IP restoration
- WiFi band mode fix for ESP32-C5 (2.4GHz mode)
- GPS coordinate precision fix (toFloat -> toDouble)
- Millis timestamp overflow fix (toInt -> strtoul)
- Millis rollover protection (safeTimeDiff) across all time comparisons
- SD file format auto-detection in whitelist restore
- RSSI variance accumulator overflow fix (int -> long)
- CSV coordinate parsing fix (semicolon separator to avoid field collision)
- Chunked HTML streaming to prevent heap exhaustion
- HTTP response optimization (deferred SD saves during HTTP)

## License

MIT License
