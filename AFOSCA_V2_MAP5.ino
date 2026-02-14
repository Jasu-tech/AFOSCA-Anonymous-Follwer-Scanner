/* AFOSCA - Anonymous Follwer Scanner (c) MIT https://github.com/Jasu-tech
 *
 * BLE/WiFi Tracker with GPS and Encounter-Based Follow Detection
 * ESP32-C5-WROOM-KIT + GPS-module + SD-card reader
 * 
 * Features:
 * - BLE and WiFi device scanning
 * - GPS tracking and distance calculation
 * - Encounter-based follow detection with Persistence Score
 * - 7-level follower detection with color-coded warnings
 * - Time window analysis (3 overlapping windows: 0-10min, 10-20min, 20-30min)
 * - Deauthentication attack detection with RGB LED alarm
 * - Web interface with blinking alerts for levels 5-7
 * - SD card logging with 7-day retention
 * - Whitelist and router filtering
 * - Google Maps integration for high threat level devices (5-7) with GPS data
 * - Route plotting with all encounter coordinates as a path with markers
 * - Encounter coordinates list stored per device (max 20 encounters for memory efficiency)
 * - Kalman filter for RSSI stabilization (BLE + WiFi) - reduces noise in signal strength readings
 * - Separate distance estimation functions for BLE and WiFi with different RSSI-to-distance characteristics
 * - Distance-based persistence score weighting (closer devices = higher risk)
 * - 5 GHz WiFi detection and RSSI correction (-10 dB attenuation compensation)
 * - Web UI displays estimated distance based on RSSI
 * - Device sorting by threat level first, then hit count, then recency
 * - Phone GPS support with automatic location updates
 * - Optimized memory management with String object cleanup
 * - GPS update interval: 10 seconds for device GPS (reduced CPU load)
 */

#include <NimBLEDevice.h>
#include <TinyGPS++.h>
#include <WiFi.h>
#include <Preferences.h>
#include <WiFiClientSecure.h>
#include <WebServer.h>
#include <SD.h>
#include <SPI.h>
#include "FS.h"
#include <time.h>
#include <set>
#include <map>
#include <vector>
#include <algorithm>
#include <cmath>
#include <esp_wifi.h>

// --- Kalman filter for RSSI stabilization (BLE + WiFi) ---
class KalmanFilter {
private:
    float _q;     // Process noise
    float _r;     // Measurement noise
    float _x;     // Estimated state (filtered RSSI)
    float _p;     // Estimation error
    float _k;     // Kalman Gain

public:
    KalmanFilter(float q, float r, float p, float initial_value) {
        _q = q;
        _r = r;
        _p = p;
        _x = initial_value;
    }

    float update(float measurement) {
        // 1. Prediction phase
        _p = _p + _q;

        // 2. Update phase (Kalman Gain)
        _k = _p / (_p + _r);
        _x = _x + _k * (measurement - _x);
        _p = (1.0f - _k) * _p;

        return _x;
    }

    float getState() const {
        return _x;
    }
};

// One Kalman filter per MAC address (BLE + WiFi)
std::map<String, KalmanFilter> rssiFilters;

// --- 1. SETTINGS & PINS ---
// ESP32-C5 compatible pin configuration
// Verify ESP32-C5 pinout and modify if needed!
// Hotspot SSID and password loaded from SD card (hotspot_config.txt)
String hotspot_ssid = "";
String hotspot_password = "";

// Static IP configuration (can be overridden from SD card)
IPAddress static_ip(192, 168, 43, 100);      // ESP32 static IP
IPAddress gateway(192, 168, 43, 1);          // Hotspot gateway (usually phone IP)
IPAddress subnet(255, 255, 255, 0);          // Subnet mask
IPAddress dns(192, 168, 43, 1);              // DNS server (usually same as gateway)
bool use_static_ip = true;                   // Use static IP by default


// SD Card SPI pins - ESP32-C5 (WORKING VERSION!)
#define SD_MOSI 2  // Master Out Slave In
#define SD_MISO 3  // Master In Slave Out
#define SD_SCK  1  // Serial Clock
#define SD_CS   0  // Chip Select
//
// PHYSICAL WIRING:
// SD GND  -> GND
// SD VCC  -> 5V (module has LDO regulator)
// SD MISO -> GPIO 3
// SD MOSI -> GPIO 2
// SD SCK  -> GPIO 1
// SD CS   -> GPIO 0

// External GPS module UART pins (connect GPS TX → ESP32 RX, GPS RX → ESP32 TX)
// PHYSICAL WIRING:
// GPS VCC  -> 3.3V (check module voltage! some need 5V)
// GPS GND  -> GND
// GPS TX   -> ESP32 GPIO 4 (GPS_RX_PIN - ESP32 receives data here)
// GPS RX   -> ESP32 GPIO 5 (GPS_TX_PIN - optional, most GPS modules don't need commands)
// NOTE: If no GPS data appears, try swapping GPIO 4 and 5 wires
#define GPS_RX_PIN 4  // ESP32 RX pin ← GPS module TX
#define GPS_TX_PIN 5  // ESP32 TX pin → GPS module RX (not needed for most GPS modules)
#define GPS_BAUD 9600 // Most GPS modules use 9600 baud (some use 38400 or 115200)

// RGB LED for deauther alarm (onboard WS2812 or similar)
#define RGB_LED_PIN 27

// Deauther detection settings
volatile int deauthCount = 0;           // Number of deauth frames detected
volatile unsigned long lastDeauthTime = 0;  // Last deauth detection timestamp
volatile bool deauthAlarmActive = false;    // Alarm state
volatile bool deauthDetectedFlag = false;   // Flag for new deauth detection (for debug output)
volatile uint8_t lastDeauthSubtype = 0;     // Last detected deauth subtype (for debug)
const unsigned long DEAUTH_ALARM_DURATION = 5000;  // Alarm duration in ms (5 sec)
const unsigned long DEAUTH_COUNT_RESET_MS = 300000;  // Reset deauth count after 5 min (300000ms)
const unsigned long DEAUTH_LED_BLINK_INTERVAL = 500;  // 0.5 sec blink interval
unsigned long lastLedToggle = 0;
bool ledState = false;
// WiFi connection status LED blinking
unsigned long lastWifiStatusBlink = 0;
const unsigned long WIFI_STATUS_BLINK_INTERVAL = 20000;  // 20 seconds
bool wifiStatusLedState = false;

// Timing constants
const unsigned long WIFI_SCAN_INTERVAL = 25000;  // 25 seconds
const unsigned long BLE_SCAN_INTERVAL = 35000;   // 35 seconds
const unsigned long GPS_UPDATE_INTERVAL = 10000;  // 10 seconds (reduced frequency to save CPU and serial reads)
const float MIN_GPS_SPEED_KMH = 2.0;
const float MIN_DISTANCE_M = 10.0;
const uint32_t BLE_SCAN_DURATION = 15;  // Duration in seconds (increased for better detection of infrequent advertisers)
const int DATA_UPDATE_INTERVAL = 10000;  // Web UI update interval (10 seconds)

struct TrackingInfo {
    unsigned long lastSeen = 0;
    int lastRSSI = -100;
    double lastLat = 0.0;
    double lastLon = 0.0;
    double totalDist = 0.0;
    String type = "";
    String name = "";
    bool isRouter = false;
    bool needsSave = false;
    unsigned long firstSeen = 0;
    int hitCount = 0;
    int encounterCount = 1;
    unsigned long lastEncounterStart = 0;
    unsigned long lastEncounterEnd = 0;
    double encounterLat = 0.0;  // V2.MAP1: Last encounter (kept for compatibility)
    double encounterLon = 0.0;  // V2.MAP1: Last encounter (kept for compatibility)
    // V2.MAP1: List of all encounter coordinates (lat, lon pairs)
    std::vector<std::pair<double, double>> encounterCoordinates;
    int minRSSI = -100;
    int maxRSSI = -100;
    // BLE-specific data
    String serviceUUIDs = "";      // Comma-separated list of service UUIDs
    String manufacturerData = "";  // Hex-encoded manufacturer data
    uint16_t manufacturerId = 0;   // Manufacturer ID (e.g., 0x004C = Apple)
   // V2.4.5: Persistence Score fields
    float persistenceScore = 0.0;  // Combined threat score (0.0-1.0)
    bool timeWindow1 = false;      // Seen in last 0-5 minutes
    bool timeWindow2 = false;      // Seen in last 5-10 minutes
    bool timeWindow3 = false;      // Seen in last 10-20 minutes
    unsigned long windowUpdateTime = 0;  // Last time windows were updated
    int rssiSum = 0;               // Sum of RSSI values for variance calc
    long rssiSumSq = 0;             // Sum of squared RSSI for variance calc
    int rssiSampleCount = 0;       // Number of RSSI samples
    int appearanceCount = 0;       // Appearances in last 20 minutes
    // V2.4.5: WiFi channel for frequency detection (1-13 = 2.4 GHz, 36+ = 5 GHz)
    int wifiChannel = 0;           // WiFi channel (0 = unknown)
};

unsigned long safeTimeDiff(unsigned long now, unsigned long past) {
    if (now >= past) {
        return now - past;
    } else {
        return (ULONG_MAX - past) + now + 1;
    }
}

// Encounter detection constants
const unsigned long ENCOUNTER_GAP_MS = 300000;   // 5 min gap = new encounter
const float ENCOUNTER_DISTANCE_M = 500.0;        // 500m movement = new encounter

// Persistence Score constants (0-10min, 10-20min, 20-30min)
const unsigned long TIME_WINDOW_1_MS = 600000;   // 0-10 minutes
const unsigned long TIME_WINDOW_2_MS = 1200000;  // 10-20 minutes  
unsigned long TIME_WINDOW_3_MS = 1800000;  // 20-30 minutes (configurable - user can adjust from web UI)
const unsigned long WINDOW_UPDATE_INTERVAL = 30000;  // Update windows every 30 seconds

// V2.4.5: Default values for TIME_WINDOW_3_MS (saved to SD card)
const unsigned long TIME_WINDOW_3_DEFAULT = 1800000;  // 30 min (default)
const unsigned long TIME_WINDOW_3_1H = 3600000;       // 1 hour
const unsigned long TIME_WINDOW_3_2H = 7200000;       // 2 hours
const unsigned long TIME_WINDOW_3_4H = 14400000;      // 4 hours
const unsigned long TIME_WINDOW_3_8H = 28800000;      // 8 tuntia
const unsigned long TIME_WINDOW_3_12H = 43200000;     // 12 tuntia
const unsigned long TIME_WINDOW_3_24H = 86400000;     // 24 tuntia

// Persistence Score weights (total = 1.0)
const float WEIGHT_WINDOWS = 0.30;      // Time window presence (reduced from 0.35)
const float WEIGHT_ENCOUNTERS = 0.25;   // Encounter count (reduced from 0.30)
const float WEIGHT_RSSI_STABILITY = 0.15;  // RSSI variance (stability) (reduced from 0.20)
const float WEIGHT_FREQUENCY = 0.15;    // Appearance frequency (unchanged)
const float WEIGHT_DISTANCE = 0.15;     // V2.4.5: Distance proximity (closer = higher risk)

// Memory limits
const int MAX_FINDINGS_TO_LOAD = 1000;  // Maximum number of findings to load from SD card (prevents memory overflow)
const int MAX_OUI_CACHE_SIZE = 200;     // Maximum OUI cache entries (prevents memory overflow)

// --- 2. GLOBALS ---
TinyGPSPlus gps;  // Used for coordinate storage and distance calculations
WebServer server(80);  // ESP32 WebServer handles one request at a time
Preferences preferences;  // NVS storage for filter state and other settings
// ESP32-C5: Using default SPI (Arduino core uses FSPI internally)
std::set<String> whitelist;
std::set<String> knownRouters;
bool hotspotAddedToWhitelist = false;  // Track if connected hotspot is already in whitelist 
std::map<String, TrackingInfo> potentialFollowers;
std::map<String, String> ouiCache;  // Cache for OUI lookups from SD card
bool sdReady = false;
bool filterEnabled = true;
volatile bool bleScanInProgress = false;
// Safe shutdown state
bool safeShutdownRequested = false;  // User requested safe shutdown
bool safeShutdownReady = false;     // Safe to power off (no SD writes in progress)
unsigned long lastGpsUpdate = 0;
double currentLat = 0.0, currentLon = 0.0;
bool gpsValid = false;
bool gpsModuleDetected = false;
bool gpsRxTxSwapped = false;
unsigned long gpsSerialStartTime = 0;
unsigned long gpsLastDiagCheck = 0;
uint32_t gpsCharsAtLastCheck = 0;
bool gpsSwapWarningShown = false;
bool gpsNoDataWarningShown = false;
const long gpsBaudRates[] = {9600, 38400, 57600, 115200};
const int gpsBaudRateCount = 4;
int gpsBaudIndex = 0;
long gpsCurrentBaud = GPS_BAUD;
bool gpsAutoBaudDone = false;

// V2.MAP1: GPS source selection
enum GpsSource {
    GPS_SOURCE_DEVICE = 0,    // Device GPS only
    GPS_SOURCE_PHONE = 1,     // Phone GPS only
    GPS_SOURCE_BOTH = 2       // Both (phone first, then device)
};
GpsSource gpsSource = GPS_SOURCE_PHONE;  // Default: phone GPS only
bool gpsSourceLocked = true;  // Lock GPS source selection (default: locked)
unsigned long lastPhoneLocationUpdate = 0;  // Timestamp when phone location was last updated
// Flags for background SD card saves
bool needsSaveWhitelist = false;
bool needsSaveRouters = false;
bool wifiScanPending = false;
bool reconnectInProgress = false;
bool needsSaveFindings = false;
bool needsReloadFindings = false;
unsigned long lastHttpResponseTime = 0;
volatile bool sdBusy = false;  // Prevents re-entrant SD operations during HTTP handlers
volatile unsigned long sdBusyStartTime = 0;  // Track when sdBusy was set (for timeout detection)
int sdFailCount = 0;  // Track consecutive SD failures
const int SD_FAIL_THRESHOLD = 3;  // After 3 consecutive failures, mark SD as not ready
unsigned long lastSdCheck = 0;
unsigned long lastCacheCleanup = 0;
unsigned long lastWindowUpdate = 0;  // V2.4.5: Last time window update
const unsigned long CACHE_CLEANUP_INTERVAL = 86400000UL;  // Check daily (24h in ms), removes entries >7 days old
const unsigned long SD_CHECK_INTERVAL = 30000;  // Check SD status every 30 seconds (reduced frequency to save SD card)

// SD card OUI lookup removed - using only internal list + maclookup.app API

// MAC vendor API integration (OPTIONAL - can be disabled by setting ENABLE_MACVENDORS_API to false)
// Primary: maclookup.app (general MAC addresses)
// Fallback: macaddress.io (if primary fails or returns no result)
#define ENABLE_MACVENDORS_API true  // Set to false to disable API calls and revert to original behavior
#define USE_FALLBACK_API true  // Use fallback API if primary fails
std::vector<String> macVendorsApiQueue;
const int MAX_API_QUEUE = 10;  // Limit API queue size
unsigned long lastApiCall = 0;
const unsigned long API_CALL_INTERVAL = 2000;  // Minimum 2 seconds between API calls (rate limiting)

// Router detection keywords
const char* routerKeywords[] = {
    "linksys", "tp-link", "asus", "d-link", "netgear", "huawei", 
    "zyxel", "telia", "dna", "elisa", "hotspot", "ap-", "wifi-", 
    "box-", "nokia", "zte", "fiber", "home", "mobile", "airties"
};
const int routerKeywordCount = sizeof(routerKeywords) / sizeof(routerKeywords[0]);

// Forward declarations
void processDevice(String type, String id, int rssi, String name = "", int wifiChannel = 0);
void updateGpsCoordinates();
// processOuiQueue() removed - using only internal list + API (no SD card lookup)
void processMacVendorsApiQueue();  // Background API lookup (OPTIONAL - disabled if ENABLE_MACVENDORS_API is false)
void setRgbLed(uint8_t r, uint8_t g, uint8_t b);
void handleDeauthAlarm();
// V2.4.5: Persistence Score functions
void updateTimeWindows();
void updateRssiVariance(TrackingInfo& info, int rssi);
float calculatePersistenceScore(const TrackingInfo& info);
int getPersistenceLevel(float score);
void updateAllPersistenceScores();
int getMaxPersistenceLevel();
String getPersistenceColor(int level);
String getBlinkClass(int level);
// V2.4.5: Distance estimation functions
float estimateBleDistance(int rssi);
float estimateWifiDistance(int rssi, int channel = 0, const String& name = "");
String formatDistance(float meters);

// --- DEAUTHER DETECTION ---
// WiFi promiscuous mode callback for detecting deauthentication frames
// Deauth frame: Type 0 (Management), Subtype 12 (Deauthentication)
typedef struct {
    unsigned frame_ctrl:16;
    unsigned duration_id:16;
    uint8_t addr1[6];
    uint8_t addr2[6];
    uint8_t addr3[6];
    unsigned sequence_ctrl:16;
} wifi_ieee80211_mac_hdr_t;

typedef struct {
    wifi_ieee80211_mac_hdr_t hdr;
    uint8_t payload[0];
} wifi_ieee80211_packet_t;

void IRAM_ATTR promiscuousCallback(void* buf, wifi_promiscuous_pkt_type_t type) {
    if (type != WIFI_PKT_MGMT) return;  // Only management frames
    
    wifi_promiscuous_pkt_t* pkt = (wifi_promiscuous_pkt_t*)buf;
    wifi_ieee80211_packet_t* ipkt = (wifi_ieee80211_packet_t*)pkt->payload;
    
    // Extract frame type and subtype from frame control field
    uint16_t frameControl = ipkt->hdr.frame_ctrl;
    uint8_t frameType = (frameControl & 0x0C) >> 2;     // Bits 2-3
    uint8_t frameSubtype = (frameControl & 0xF0) >> 4;  // Bits 4-7
    
    // Check for deauthentication frame (type 0, subtype 12)
    // Also check for disassociation frame (type 0, subtype 10)
    if (frameType == 0 && (frameSubtype == 12 || frameSubtype == 10)) {
        deauthCount++;
        // Use IRAM-safe tick count (ESP32-C5: portTICK_PERIOD_MS is typically 1ms)
        // Convert ticks to milliseconds (xTaskGetTickCountFromISR returns ticks)
        TickType_t ticks = xTaskGetTickCountFromISR();
        lastDeauthTime = (unsigned long)(ticks * portTICK_PERIOD_MS);
        deauthAlarmActive = true;
        lastDeauthSubtype = frameSubtype;  // Store for debug output
        deauthDetectedFlag = true;          // Flag for debug output in loop()
    }
}

// RGB LED control using neopixelWrite (ESP32 Arduino Core 3.x)
// ESP32-C5 onboard LED uses GRB color order, so we swap R and G
void setRgbLed(uint8_t r, uint8_t g, uint8_t b) {
    // GRB order: first param is Green, second is Red, third is Blue
    neopixelWrite(RGB_LED_PIN, g, r, b);
}

// Handle deauth alarm LED flashing and counter reset
// V2.4.5: Get highest persistence level among all devices
int getMaxPersistenceLevel() {
    int maxLevel = 1;
    for (const auto& pair : potentialFollowers) {
        const TrackingInfo& info = pair.second;
        // Skip whitelist and routers
        if (whitelist.count(pair.first) > 0 || info.isRouter) continue;
        int level = getPersistenceLevel(info.persistenceScore);
        if (level > maxLevel) maxLevel = level;
    }
    return maxLevel;
}


void handleDeauthAlarm() {
    unsigned long now = millis();
    
    // Handle debug output for new deauth detections (moved from ISR)
    if (deauthDetectedFlag) {
        Serial.print("[DEAUTH DETECTED!] Count: ");
        Serial.print(deauthCount);
        Serial.print(" Type: ");
        Serial.println(lastDeauthSubtype == 12 ? "Deauth" : "Disassoc");
        deauthDetectedFlag = false;  // Clear flag
    }
    
    // Reset deauth count after 5 minutes of no new detections
    if (deauthCount > 0 && lastDeauthTime > 0) {
        if (safeTimeDiff(now, lastDeauthTime) > DEAUTH_COUNT_RESET_MS) {
            deauthCount = 0;
            Serial.println("[DEAUTH] Counter reset after 5 min inactivity");
        }
    }
    
    if (deauthAlarmActive) {
        // Check if alarm should still be active
        if (safeTimeDiff(now, lastDeauthTime) > DEAUTH_ALARM_DURATION) {
            deauthAlarmActive = false;
            setRgbLed(0, 0, 0);  // Turn off LED
            ledState = false;
            return;
        }
        
        // Blink red LED at 0.5 sec interval
        if (now - lastLedToggle >= DEAUTH_LED_BLINK_INTERVAL) {
            lastLedToggle = now;
            ledState = !ledState;
            if (ledState) {
                setRgbLed(255, 0, 0);  // Red ON
            } else {
                setRgbLed(0, 0, 0);    // OFF
            }
        }
    }
}

// Clean old entries from potentialFollowers (7 day retention)
void cleanOldCacheEntries() {
    unsigned long now = millis();
    const unsigned long SEVEN_DAYS_MS = 604800000UL;
    int removed = 0;
    
    // Clean potentialFollowers - remove entries older than 7 days
    // BUT: Keep entries that are in whitelist or knownRouters (they should always be visible)
    for (auto it = potentialFollowers.begin(); it != potentialFollowers.end(); ) {
        String id = it->first;
        bool isWhitelisted = (whitelist.count(id) > 0);
        bool isRouter = (knownRouters.count(id) > 0 || it->second.isRouter);
        
        // Don't remove whitelisted devices or routers - they should always be visible
        if (isWhitelisted || isRouter) {
            ++it;
            continue;
        }
        
        if (safeTimeDiff(now, it->second.lastSeen) > SEVEN_DAYS_MS) {
            it = potentialFollowers.erase(it);
            removed++;
        } else {
            ++it;
        }
    }
    
    if (removed > 0) {
        Serial.printf("[CLEANUP] Removed %d entries older than 7 days\n", removed);
        
        // Save cleaned data to SD card
        if (sdReady) {
            saveAllFindings();
            Serial.println("[CLEANUP] SD card updated with cleaned data");
        }
    }
}

// --- 3. BLE CALLBACK HANDLER ---
// Counter for BLE discoveries
volatile int bleDevicesFoundThisScan = 0;

class MyScanCallbacks: public NimBLEScanCallbacks {
    // NimBLE 2.x: onResult uses const pointer
    // NimBLE 1.x: uses non-const pointer
    // Trying WITHOUT override keyword for compatibility
    void onResult(const NimBLEAdvertisedDevice* advertisedDevice) {
        String addr = String(advertisedDevice->getAddress().toString().c_str());
        String name = advertisedDevice->haveName() ? String(advertisedDevice->getName().c_str()) : "";
        int rssi = advertisedDevice->getRSSI();
        
        bleDevicesFoundThisScan++;
        
        // Extract Service UUIDs and check for Fast Pair (0xFE2C)
        String serviceUUIDs = "";
        bool hasFastPair = false;
        uint32_t fastPairModelId = 0;
        if (advertisedDevice->haveServiceUUID()) {
            int uuidCount = advertisedDevice->getServiceUUIDCount();
            for (int i = 0; i < uuidCount && i < 5; i++) {  // Max 5 UUIDs
                if (i > 0) serviceUUIDs += ",";
                String uuid = String(advertisedDevice->getServiceUUID(i).toString().c_str());
                serviceUUIDs += uuid;
                
                // Check for Fast Pair Service UUID (0xFE2C)
                // Fast Pair uses UUID 0xFE2C (can be short or full UUID format)
                String uuidShort = uuid;
                uuidShort.toUpperCase();
                if (uuidShort.indexOf("FE2C") >= 0) {
                    hasFastPair = true;
                    
                    // Try to extract Fast Pair Model ID from Service Data
                    // Fast Pair Model ID is 24-bit (3 bytes) in big-endian format in Service Data
                    // Note: NimBLE may need getServiceData() or we parse from advertisement payload
                    // For now, mark as Fast Pair device - Model ID extraction may require GATT connection
                    // Fast Pair devices are typically Google Pixel phones, Chromecast, etc.
                }
            }
        }
        
        // Extract Manufacturer Data FIRST (needed for Fast Pair detection)
        String mfgDataHex = "";
        uint16_t mfgId = 0;
        if (advertisedDevice->haveManufacturerData()) {
            const std::string& mfgData = advertisedDevice->getManufacturerData();
            if (mfgData.length() >= 2) {
                // First 2 bytes are manufacturer ID (little-endian)
                mfgId = (uint8_t)mfgData[0] | ((uint8_t)mfgData[1] << 8);
                
                // Check for Google Company ID (0x00E0) which may contain Fast Pair data
                if (mfgId == 0x00E0 && mfgData.length() >= 5) {
                    // Google devices may have Fast Pair Model ID in manufacturer data
                    // Try to extract Model ID from bytes 2-4 (if present)
                    uint32_t possibleModelId = ((uint8_t)mfgData[2] << 16) | 
                                              ((uint8_t)mfgData[3] << 8) | 
                                              (uint8_t)mfgData[4];
                    // Model IDs are typically in range 0x000001-0xFFFFFF
                    if (possibleModelId > 0 && possibleModelId <= 0xFFFFFF) {
                        hasFastPair = true;
                        fastPairModelId = possibleModelId;
                    }
                }
                
                // Convert rest to hex string (max 20 bytes)
                int maxBytes = min((int)mfgData.length(), 22);
                for (int i = 0; i < maxBytes; i++) {
                    char hex[3];
                    sprintf(hex, "%02X", (uint8_t)mfgData[i]);
                    mfgDataHex += hex;
                }
            }
        }
        
        // Debug: print detected BLE device
        Serial.print("[BLE] ");
        Serial.print(addr);
        if (name.length() > 0) {
            Serial.print(" \"");
            Serial.print(name);
            Serial.print("\"");
        }
        Serial.print(" RSSI:");
        Serial.print(rssi);
        if (serviceUUIDs.length() > 0) {
            Serial.print(" UUID:");
            Serial.print(serviceUUIDs);
        }
        if (hasFastPair) {
            Serial.print(" [Fast Pair");
            if (fastPairModelId > 0) {
                Serial.print(" ModelID:0x");
                Serial.print(fastPairModelId, HEX);
            }
            Serial.print("]");
        }
        if (mfgId > 0) {
            Serial.print(" MFG:");
            Serial.print(mfgId, HEX);
        }
        Serial.println();
        
        // Store BLE-specific data in potentialFollowers
        processDevice("BLE", addr, rssi, name);
        
        // Update BLE-specific fields
        auto it = potentialFollowers.find(addr);
        if (it != potentialFollowers.end()) {
            if (serviceUUIDs.length() > 0) it->second.serviceUUIDs = serviceUUIDs;
            if (mfgDataHex.length() > 0) it->second.manufacturerData = mfgDataHex;
            if (mfgId > 0) it->second.manufacturerId = mfgId;
            
            // Mark as Fast Pair device if detected
            if (hasFastPair) {
                // Add Fast Pair indicator to device name if not already present
                if (it->second.name.length() == 0 || it->second.name.indexOf("Fast Pair") < 0) {
                    if (it->second.name.length() > 0) {
                        it->second.name += " [Fast Pair]";
                    } else {
                        it->second.name = "Fast Pair Device";
                        if (fastPairModelId > 0) {
                            it->second.name += " (ModelID:0x";
                            char modelIdStr[9];
                            sprintf(modelIdStr, "%06X", fastPairModelId);
                            it->second.name += modelIdStr;
                            it->second.name += ")";
                        }
                    }
                }
            }
        }
    }
    
    // NimBLE 2.x: onScanEnd ottaa const NimBLEScanResults& ja int reason
    void onScanEnd(const NimBLEScanResults& results, int reason) {
        Serial.print("[BLE] Scan complete. Reason: ");
        Serial.print(reason);
        Serial.print(", Devices found: ");
        Serial.println(bleDevicesFoundThisScan);
        bleDevicesFoundThisScan = 0;
        bleScanInProgress = false;
    }
};

MyScanCallbacks myScanCallbacks;

// --- 4. DATA LOGIC ---
void saveList(const char* path, std::set<String>& list) {
    if (!sdReady) {
        Serial.println("SD card not ready - cannot save list");
        return;
    }
    if (safeShutdownRequested) {
        Serial.println("Safe shutdown requested - skipping save");
        return;
    }
    if (sdBusy) {
        Serial.println("SD busy - skipping save, will retry");
        return;
    }
    sdBusy = true;
    sdBusyStartTime = millis();
    
    // OPTIMIZED SPEED: Write directly to final file
    // Data is already in RAM, so this is just a backup to SD card
    // If write fails, data is still in RAM and will retry later
    
    unsigned long startTime = millis();
    const unsigned long SD_TIMEOUT_MS = 5000;  // 5 second timeout
    
    // Remove old file (if exists) - with timeout check
    if (millis() - startTime < SD_TIMEOUT_MS) {
        if (SD.exists(path)) {
            SD.remove(path);
        }
    }
    
    // Write directly to final file with retry logic and timeout
    File f;
    int retries = 3;
    while (retries > 0 && (millis() - startTime < SD_TIMEOUT_MS)) {
        f = SD.open(path, FILE_WRITE);
        if (f) break;
        retries--;
        if (retries > 0) {
            delay(50);  // Reduced delay
            yield();  // Allow web server to process
        }
    }
    
    if (!f || (millis() - startTime >= SD_TIMEOUT_MS)) {
        Serial.print("ERROR: Failed to open file for writing (timeout or retries): ");
        Serial.println(path);
        if (f) f.close();
        sdFailCount++;
        if (sdFailCount >= SD_FAIL_THRESHOLD) {
            Serial.println("[SD] Too many failures - marking SD as not ready for reinit");
            sdReady = false;
            sdFailCount = 0;
        }
        sdBusy = false;
        return;
    }
    sdFailCount = 0;
    
    // CHUNKED BUFFERING: Collect lines in RAM buffer, write chunks to SD card
    // This reduces flush() calls and corruption risk without excessive RAM usage
    const int CHUNK_SIZE = 50;  // Write 50 lines at a time
    String chunk = "";
    chunk.reserve(2048);  // Pre-allocate ~2KB for chunk (50 lines * ~40 bytes each)
    
    int written = 0;
    bool timeoutOccurred = false;
    for (auto const& id : list) {
        // Check timeout during write
        if (millis() - startTime >= SD_TIMEOUT_MS) {
            Serial.println("SD write timeout - closing file");
            timeoutOccurred = true;
            break;
        }
        
        // Add line to chunk buffer
        chunk += id;
        // Include device name if we have it in potentialFollowers (optimized: single lookup)
        auto it = potentialFollowers.find(id);
        if (it != potentialFollowers.end() && it->second.name.length() > 0) {
            chunk += ",";
            chunk += it->second.name;
        }
        chunk += "\n";
        written++;
        
        // When chunk is full, write it to SD card and flush
        if (written % CHUNK_SIZE == 0) {
            f.print(chunk);
            f.flush();  // Flush after each chunk
            delay(10);  // Small delay to ensure flush completes
            chunk = "";  // Clear chunk buffer
            chunk.reserve(2048);  // Re-allocate for next chunk
        }
        
        // Yield every 10 items (NO server.handleClient - causes re-entrancy freeze!)
        if (written % 10 == 0) {
            yield();
        }
    }
    
    // Write remaining chunk if any
    if (chunk.length() > 0) {
        f.print(chunk);
        chunk = "";  // Free memory
    }
    
    // CRITICAL: Always flush and close file, even on timeout
    f.flush();  // Force write to SD card
    delay(10);  // Small delay to ensure flush completes
    f.close();  // CRITICAL: Always close file to prevent corruption
    delay(10);  // Small delay to ensure close completes
    
    // If timeout occurred, remove incomplete file
    if (timeoutOccurred) {
        Serial.println("SD write timeout - removing incomplete file");
        delay(50);  // Wait before removing
        if (SD.exists(path)) {
            SD.remove(path);
        }
        sdBusy = false;
        return;
    }
    
    // VERIFY that file exists and is not empty (with timeout)
    if (millis() - startTime < SD_TIMEOUT_MS) {
        if (!SD.exists(path)) {
            Serial.print("ERROR: File was not created: ");
            Serial.println(path);
            sdBusy = false;
            return;
        }
        
        File checkFile = SD.open(path, FILE_READ);
        if (!checkFile || checkFile.size() == 0) {
            Serial.print("ERROR: File is empty or invalid: ");
            Serial.println(path);
            if (checkFile) checkFile.close();
            SD.remove(path);  // Remove empty file
            sdBusy = false;
            return;
        }
        checkFile.close();
    }
    
    sdBusy = false;
    Serial.print("Saved ");
    Serial.print(written);
    Serial.print(" items to ");
    Serial.println(path);
}

void loadLists() {
    if (!sdReady) {
        Serial.println("loadLists: SD card not ready!");
        return;
    }
    if (sdBusy) {
        Serial.println("loadLists: SD busy, skipping");
        return;
    }
    sdBusy = true;  // Lock SD during load
    sdBusyStartTime = millis();
    
    unsigned long startTime = millis();
    const unsigned long SD_TIMEOUT_MS = 5000;  // 5 second timeout
    
    Serial.println("loadLists: Starting to load lists from SD card...");
    
    auto loader = [&](const char* path, bool isRouter) {
        Serial.print("loadLists: Checking for file: ");
        Serial.println(path);
        
        if (!SD.exists(path)) {
            Serial.print("loadLists: File does not exist: ");
            Serial.println(path);
            return 0;  // Return count of loaded items
        }
        
        Serial.print("loadLists: File exists, opening: ");
        Serial.println(path);
        
        File f = SD.open(path, FILE_READ);
        if (!f) {
            Serial.print("loadLists: ERROR - Failed to open file: ");
            Serial.println(path);
            sdFailCount++;
            if (sdFailCount >= SD_FAIL_THRESHOLD) {
                Serial.println("[SD] Too many load failures - marking SD as not ready");
                sdReady = false;
                sdFailCount = 0;
            }
            return 0;
        }
        sdFailCount = 0;
        
        Serial.print("loadLists: File opened successfully. Size: ");
        Serial.print(f.size());
        Serial.println(" bytes");
        
        int loaded = 0;
        int lineNum = 0;
        // CRITICAL: Add yield() calls to prevent web server from freezing
        while (f.available() && (millis() - startTime < SD_TIMEOUT_MS)) {
            lineNum++;
            String line = f.readStringUntil('\n');
            line.trim();
            
            // Skip empty lines
            if (line.length() == 0) continue;
            
            // MAC address should be at least 12 characters (XX:XX:XX:XX:XX:XX)
            if (line.length() < 12) {
                Serial.print("loadLists: Skipping line ");
                Serial.print(lineNum);
                Serial.print(" (too short): ");
                Serial.println(line);
                continue;
            }
            
            int comma = line.indexOf(',');
            String mac = (comma != -1) ? line.substring(0, comma) : line;
            String name = (comma != -1) ? line.substring(comma + 1) : "";
            mac.trim();
            name.trim();
            mac.toUpperCase();
            
            // Validate MAC address format (basic check)
            if (mac.length() < 12 || mac.length() > 17) {
                Serial.print("loadLists: Skipping invalid MAC on line ");
                Serial.print(lineNum);
                Serial.print(": ");
                Serial.println(mac);
                continue;
            }
            
            if (isRouter) {
                knownRouters.insert(mac);
            } else {
                whitelist.insert(mac);
            }
            
            unsigned long now = millis();
            if (!potentialFollowers.count(mac)) {
                // New device - create entry
                TrackingInfo newInfo;
                newInfo.lastSeen = now;
                newInfo.lastRSSI = -100;
                newInfo.type = isRouter ? "WiFi" : "Unknown";  // Default whitelist=Unknown (will be set on first detection), routers=WiFi
                newInfo.name = name;
                newInfo.isRouter = isRouter;
                newInfo.firstSeen = now;
                newInfo.hitCount = 1;
                potentialFollowers[mac] = newInfo;
            } else {
                // Device already exists - only update name and router status
                // DO NOT TOUCH THE TYPE!
                if (name.length() > 0) {
                    potentialFollowers[mac].name = name;
                }
                potentialFollowers[mac].isRouter = isRouter;
            }
            
            loaded++;
            
            // Yield every 10 items (NO server.handleClient - causes re-entrancy!)
            if (loaded % 10 == 0) {
                yield();
            }
        }
        f.close();
        
            Serial.print("loadLists: Loaded ");
            Serial.print(loaded);
            Serial.print(" items from ");
            Serial.println(path);
            
            // Debug: Print first few loaded items to verify
            if (loaded > 0) {
                Serial.print("loadLists: Sample items from ");
                Serial.print(path);
                Serial.print(": ");
                int printed = 0;
                for (auto const& mac : (isRouter ? knownRouters : whitelist)) {
                    if (printed++ < 3) {
                        Serial.print(mac);
                        if (potentialFollowers.count(mac) && potentialFollowers[mac].name.length() > 0) {
                            Serial.print(" (");
                            Serial.print(potentialFollowers[mac].name);
                            Serial.print(")");
                        }
                        Serial.print(" ");
                    }
                }
                Serial.println();
            }
            
            return loaded;
    };
    
    int whitelistCount = loader("/whitelist.txt", false);
    int routersCount = loader("/routers.txt", true);
    
    sdBusy = false;  // Release SD lock after load
    
    Serial.print("loadLists: Summary - Whitelist: ");
    Serial.print(whitelistCount);
    Serial.print(", Routers: ");
    Serial.print(routersCount);
    Serial.print(" (Total in memory - Whitelist: ");
    Serial.print(whitelist.size());
    Serial.print(", Routers: ");
    Serial.print(knownRouters.size());
    Serial.println(")");
}

// Cleanup function to remove orphaned temp files on startup
void cleanupTempFiles() {
    if (!sdReady) return;
    if (sdBusy) return;
    
    Serial.println("[CLEANUP] Removing orphaned temp files...");
    const char* tempFiles[] = {
        "/all_findings.txt.tmp",
        "/all_findings.txt.bak"
    };
    
    int removed = 0;
    for (int i = 0; i < 2; i++) {
        if (SD.exists(tempFiles[i])) {
            SD.remove(tempFiles[i]);  // Remove file (don't check return value)
            Serial.print("[CLEANUP] Removed: ");
            Serial.println(tempFiles[i]);
            removed++;
        }
    }
    
    if (removed == 0) {
        Serial.println("[CLEANUP] No orphaned temp files found");
    } else {
        Serial.print("[CLEANUP] Cleaned up ");
        Serial.print(removed);
        Serial.println(" temp file(s)");
    }
}

void saveAllFindings() {
    if (!sdReady) {
        Serial.println("SD card not ready - cannot save findings");
        return;
    }
    if (safeShutdownRequested) {
        Serial.println("Safe shutdown requested - skipping findings save");
        return;
    }
    if (sdBusy) {
        Serial.println("SD busy - skipping findings save, will retry");
        return;
    }
    sdBusy = true;
    sdBusyStartTime = millis();
    
    const char* path = "/all_findings.txt";
    const char* tempPath = "/all_findings.txt.tmp";  // Use const char* to avoid encoding issues
    
    unsigned long startTime = millis();
    const unsigned long SD_TIMEOUT_MS = 10000;  // 10 second timeout for large file
    
    // Remove old temp file if it exists
    if (millis() - startTime < SD_TIMEOUT_MS) {
        if (SD.exists(tempPath)) {
            SD.remove(tempPath);
        }
    }
    
    // Write to temp file with retry logic and timeout
    File f;
    int retries = 3;
    while (retries > 0 && (millis() - startTime < SD_TIMEOUT_MS)) {
        f = SD.open(tempPath, FILE_WRITE);
        if (f) break;
        retries--;
        if (retries > 0) {
            delay(50);  // Reduced delay
            yield();  // Allow web server to process
        }
    }
    
    if (!f || (millis() - startTime >= SD_TIMEOUT_MS)) {
        Serial.println("ERROR: Failed to open findings temp file for writing (timeout or retries)");
        if (f) f.close();
        sdFailCount++;
        if (sdFailCount >= SD_FAIL_THRESHOLD) {
            Serial.println("[SD] Too many failures - marking SD as not ready for reinit");
            sdReady = false;
            sdFailCount = 0;
        }
        sdBusy = false;
        return;
    }
    sdFailCount = 0;
    
    // Write CSV header (V2.MAP5 simplified format: 8 fields)
    f.println("TYPE,MAC,NAME,HIT_COUNT,ENC_COUNT,FIRST_SEEN,LAST_SEEN,ENCOUNTER_COORDS");
    
    // CHUNKED BUFFERING: Collect lines in RAM buffer, write chunks to SD card
    // This reduces flush() calls and corruption risk without excessive RAM usage
    const int CHUNK_SIZE = 50;  // Write 50 lines at a time
    String chunk = "";
    chunk.reserve(4096);  // Pre-allocate ~4KB for chunk (50 lines * ~80 bytes each for findings)
    
    int written = 0;
    bool timeoutOccurred = false;
    for (auto const& pair : potentialFollowers) {
        // Check timeout during write
        if (millis() - startTime >= SD_TIMEOUT_MS) {
            Serial.println("SD write timeout - closing file");
            timeoutOccurred = true;
            break;
        }
        
        String id = pair.first;
        const TrackingInfo& info = pair.second;
        
        // Build line in chunk buffer
        chunk += info.type;
        chunk += ",";
        chunk += id;
        chunk += ",";
        chunk += (info.name.length() > 0 ? info.name : "Unknown");
        chunk += ",";
        chunk += String(info.hitCount);
        chunk += ",";
        chunk += String(info.encounterCount);
        chunk += ",";
        chunk += String(info.firstSeen);
        chunk += ",";
        chunk += String(info.lastSeen);
        chunk += ",";
        // V2.MAP5: Save encounter coordinates (format: lat1;lon1|lat2;lon2|...)
        // CRITICAL: Use semicolon between lat;lon (NOT comma) to avoid breaking CSV parsing
        if (info.encounterCoordinates.size() > 0) {
            for (size_t i = 0; i < info.encounterCoordinates.size(); i++) {
                if (i > 0) chunk += "|";
                chunk += String(info.encounterCoordinates[i].first, 6);
                chunk += ";";
                chunk += String(info.encounterCoordinates[i].second, 6);
            }
        }
        chunk += "\n";
        written++;
        
        // When chunk is full, write it to SD card and flush
        if (written % CHUNK_SIZE == 0) {
            f.print(chunk);
            f.flush();  // Flush after each chunk
            delay(10);  // Small delay to ensure flush completes
            chunk = "";  // Clear chunk buffer
            chunk.reserve(4096);  // Re-allocate for next chunk
        }
        
        // Yield every 10 items (NO server.handleClient - causes re-entrancy freeze!)
        if (written % 10 == 0) {
            yield();
        }
    }
    
    // Write remaining chunk if any
    if (chunk.length() > 0) {
        f.print(chunk);
        chunk = "";  // Free memory
    }
    
    // CRITICAL: Always flush and close file, even on timeout
    f.flush();  // Force write to SD card
    delay(10);  // Small delay to ensure flush completes
    f.close();  // CRITICAL: Always close file to prevent corruption
    delay(10);  // Small delay to ensure close completes
    
    // If timeout occurred, remove incomplete temp file
    if (timeoutOccurred) {
        Serial.println("SD write timeout - removing incomplete temp file");
        delay(50);  // Wait before removing
        if (SD.exists(tempPath)) {
            SD.remove(tempPath);
        }
        sdBusy = false;
        return;
    }
    
    // VERIFY that write succeeded
    if (!SD.exists(tempPath)) {
        Serial.println("ERROR: Findings temp file was not created");
        sdBusy = false;
        return;
    }
    
    File checkFile = SD.open(tempPath, FILE_READ);
    if (!checkFile || checkFile.size() == 0) {
        Serial.println("ERROR: Findings temp file is empty");
        if (checkFile) checkFile.close();
        SD.remove(tempPath);
        sdBusy = false;
        return;
    }
    checkFile.close();
    
    // Create backup
    const char* backupPath = "/all_findings.txt.bak";  // Use const char* to avoid encoding issues
    if (SD.exists(path)) {
        if (SD.exists(backupPath)) {
            SD.remove(backupPath);
        }
        File oldFile = SD.open(path, FILE_READ);
        if (oldFile) {
            File backupFile = SD.open(backupPath, FILE_WRITE);
            if (backupFile) {
                // Optimized: Use buffer for faster copying
                uint8_t buffer[128];  // 128 byte buffer for faster copy
                size_t bytesRead;
                int copyCount = 0;
                while ((bytesRead = oldFile.read(buffer, sizeof(buffer))) > 0) {
                    backupFile.write(buffer, bytesRead);
                    copyCount++;
                    // CRITICAL: Flush backup file every 50 buffers to prevent corruption
                    if (copyCount % 50 == 0) {
                        backupFile.flush();
                        delay(5);
                    }
                    // Yield every 100 buffers (NO server.handleClient!)
                    if (copyCount % 100 == 0) {
                        yield();
                    }
                }
                backupFile.flush();  // Final flush before close
                delay(10);
                backupFile.close();
            }
            oldFile.close();
        }
        SD.remove(path);
    }
    
    // Copy temp file to final destination (optimized: use buffer for faster copying)
    // Note: f is already closed at this point (line 925)
    // Check timeout before starting copy
    if (millis() - startTime >= SD_TIMEOUT_MS) {
        Serial.println("SD operation timeout - skipping file copy");
        SD.remove(tempPath);
        sdBusy = false;
        return;
    }
    
    File srcFile = SD.open(tempPath, FILE_READ);
    if (!srcFile) {
        Serial.println("ERROR: Cannot read findings temp file");
        sdBusy = false;
        return;
    }
    
    File destFile = SD.open(path, FILE_WRITE);
    if (!destFile) {
        Serial.println("ERROR: Cannot create final findings file");
        srcFile.close();
        sdBusy = false;
        return;
    }
    
    // Optimized: Use buffer for faster copying with timeout check
    uint8_t buffer[128];  // 128 byte buffer for faster copy
    size_t bytesRead;
    int copyCount = 0;
    bool copyTimeout = false;
    while ((bytesRead = srcFile.read(buffer, sizeof(buffer))) > 0) {
        // Check timeout during copy
        if (millis() - startTime >= SD_TIMEOUT_MS) {
            Serial.println("SD copy timeout - closing files");
            copyTimeout = true;
            break;
        }
        destFile.write(buffer, bytesRead);
        copyCount++;
        // CRITICAL: Flush destination file every 50 buffers to prevent corruption
        if (copyCount % 50 == 0) {
            destFile.flush();
            delay(5);
        }
        // Yield every 100 buffers (NO server.handleClient - causes freeze!)
        if (copyCount % 100 == 0) {
            yield();
        }
    }
    
    // CRITICAL: Always flush and close files, even on timeout
    destFile.flush();  // Force write to SD card
    delay(10);  // Small delay to ensure flush completes
    destFile.close();  // CRITICAL: Always close files
    srcFile.close();   // CRITICAL: Always close files
    delay(10);  // Small delay to ensure close completes
    
    // If copy timeout occurred, remove incomplete files
    if (copyTimeout) {
        Serial.println("SD copy timeout - removing incomplete files");
        delay(50);  // Wait before removing
        if (SD.exists(path)) {
            SD.remove(path);
        }
        if (SD.exists(tempPath)) {
            SD.remove(tempPath);
        }
        sdBusy = false;
        return;
    }
    
    // Only remove temp file if copy succeeded
    delay(50);  // Wait before removing temp file
    if (SD.exists(tempPath)) {
        SD.remove(tempPath);
    }
    
    sdBusy = false;
    Serial.print("Saved ");
    Serial.print(written);
    Serial.println(" findings to /all_findings.txt");
}

void loadAllFindings() {
    if (!sdReady) return;
    if (sdBusy) {
        Serial.println("loadAllFindings: SD busy, skipping");
        return;
    }
    sdBusy = true;  // Lock SD during load
    sdBusyStartTime = millis();
    
    const char* path = "/all_findings.txt";
    if (!SD.exists(path)) {
        sdBusy = false;
        return;  // No findings file exists yet
    }
    
    File f = SD.open(path, FILE_READ);
    if (!f) {
        Serial.println("[SD] ERROR: Failed to open findings file for reading");
        sdFailCount++;
        if (sdFailCount >= SD_FAIL_THRESHOLD) {
            Serial.println("[SD] Too many load failures - marking SD as not ready");
            sdReady = false;
            sdFailCount = 0;
        }
        sdBusy = false;
        return;
    }
    
    // Skip header line
    if (f.available()) {
        f.readStringUntil('\n');
    }
    
    int loaded = 0;
    unsigned long now = millis();
    const unsigned long SEVEN_DAYS_MS = 604800000UL;  // 7 days (7 * 24 * 60 * 60 * 1000)
    
    while (f.available() && loaded < MAX_FINDINGS_TO_LOAD) {
        String line = f.readStringUntil('\n');
        line.trim();
        if (line.length() < 12) continue;
        
        // Parse CSV: TYPE,MAC,NAME,HIT_COUNT,ENC_COUNT,FIRST_SEEN,LAST_SEEN,ENCOUNTER_COORDS
        // CRITICAL: Field 8 (ENCOUNTER_COORDS) may contain commas (old: lat,lon) or semicolons (new: lat;lon)
        // So we CANNOT count all commas - parse first 7 comma-separated fields, rest = field 8
        
        // Detect format: new format starts with TYPE (BLE/WiFi/Unknown), old starts with MAC
        // Quick check: does first field look like a MAC address? (contains ':')
        int firstComma = line.indexOf(',');
        if (firstComma < 0) continue;
        String firstField = line.substring(0, firstComma);
        bool isNewFormat = (firstField == "BLE" || firstField == "WiFi" || firstField == "Unknown");
        
        String fields[19];
        int fieldCount = 0;
        int pos = 0;
        
        if (isNewFormat) {
            // New format: parse exactly 7 commas, everything after 7th comma = encounter coords (field 8)
            for (int i = 0; i < 7; i++) {
                int nextComma = line.indexOf(',', pos);
                if (nextComma == -1) {
                    fields[i] = line.substring(pos);
                    fieldCount = i + 1;
                    break;
                }
                fields[i] = line.substring(pos, nextComma);
                pos = nextComma + 1;
                fieldCount = i + 1;
            }
            // Field 8: everything remaining (may contain commas in old coord format)
            if (pos < (int)line.length()) {
                fields[7] = line.substring(pos);
                fieldCount = 8;
            }
            // Require at least 7 fields (TYPE,MAC,NAME,HIT,ENC,FIRST,LAST) for valid new format
            if (fieldCount < 7) {
                Serial.print("[LOAD] Skipping malformed new-format line (");
                Serial.print(fieldCount);
                Serial.println(" fields)");
                continue;
            }
        } else {
            // Old format: MAC,TYPE,NAME,... (19 fields, no embedded commas)
            for (int i = 0; i < 19; i++) {
                int nextComma = line.indexOf(',', pos);
                if (nextComma == -1) {
                    fields[i] = line.substring(pos);
                    fieldCount = i + 1;
                    break;
                }
                fields[i] = line.substring(pos, nextComma);
                pos = nextComma + 1;
                fieldCount = i + 1;
            }
        }
        
        String mac, type, name;
        unsigned long firstSeen = 0, lastSeen = 0;
        int hitCount = 0, encounterCount = 0;
        String encounterCoords = "";
        
        if (isNewFormat) {
            // New format: TYPE,MAC,NAME,HIT_COUNT,ENC_COUNT,FIRST_SEEN,LAST_SEEN,ENCOUNTER_COORDS
            type = fields[0];
            mac = fields[1];
            name = fields[2];
            hitCount = (fields[3].length() > 0) ? fields[3].toInt() : 0;
            encounterCount = (fields[4].length() > 0) ? fields[4].toInt() : 0;
            firstSeen = (fields[5].length() > 0) ? strtoul(fields[5].c_str(), NULL, 10) : 0;
            lastSeen = (fields[6].length() > 0) ? strtoul(fields[6].c_str(), NULL, 10) : 0;
            encounterCoords = (fields[7].length() > 0) ? fields[7] : "";
        } else {
            // Old format: MAC,TYPE,NAME,LAST_SEEN,RSSI,LAT,LON,TOTAL_DIST,IS_ROUTER,FIRST_SEEN,HIT_COUNT,ENC_COUNT,ENC_START,ENC_END,ENC_LAT,ENC_LON,MIN_RSSI,MAX_RSSI,ENCOUNTER_COORDS
            mac = fields[0];
            type = fields[1];
            name = fields[2];
            lastSeen = (fields[3].length() > 0) ? strtoul(fields[3].c_str(), NULL, 10) : 0;
            firstSeen = (fields[9].length() > 0) ? strtoul(fields[9].c_str(), NULL, 10) : 0;
            hitCount = (fields[10].length() > 0) ? fields[10].toInt() : 0;
            encounterCount = (fields[11].length() > 0) ? fields[11].toInt() : 0;
            encounterCoords = (fields[18].length() > 0) ? fields[18] : "";
        }
        
        // Validate MAC address format (must be 17 chars: XX:XX:XX:XX:XX:XX or 12 chars: XXXXXXXXXXXX)
        if (mac.length() < 12 || mac.length() > 17) continue;
        
        // Basic MAC format validation (should contain only hex chars and colons/dashes)
        bool validMac = true;
        String macCheck = mac;
        macCheck.toUpperCase();
        for (int j = 0; j < macCheck.length(); j++) {
            char c = macCheck.charAt(j);
            if (!((c >= '0' && c <= '9') || (c >= 'A' && c <= 'F') || c == ':' || c == '-')) {
                validMac = false;
                break;
            }
        }
        if (!validMac) continue;
        
        mac.toUpperCase();
        
        // Filter: Only load findings from last 7 days to prevent memory overflow
        if (lastSeen > 0 && now > lastSeen) {
            unsigned long age = (now >= lastSeen) ? (now - lastSeen) : (ULONG_MAX - lastSeen + now + 1);
            if (age > SEVEN_DAYS_MS) {
                continue;  // Skip findings older than 7 days
            }
        }
        
        // Create or update TrackingInfo
        // FIXED: Don't overwrite existing data - only add new entries
        if (potentialFollowers.count(mac) > 0) {
            // Device already exists - update only stats, NOT the type!
            auto& existing = potentialFollowers[mac];
            // Preserve original type (BLE/WiFi) - never overwrite!
            // Update only if SD card has newer data
            if (lastSeen > existing.lastSeen) {
                existing.lastSeen = lastSeen;
            }
            // Update encounter data if better
            if (encounterCount > existing.encounterCount) {
                existing.encounterCount = encounterCount;
            }
            if (hitCount > existing.hitCount) {
                existing.hitCount = hitCount;
            }
            
            // V2.MAP5: Load encounter coordinates if available
            // Supports both semicolon (new: lat;lon) and comma (old: lat,lon) separators
            if (encounterCoords.length() > 0) {
                String coordsStr = encounterCoords;
                existing.encounterCoordinates.clear();
                int pipePos = 0;
                while (pipePos >= 0) {
                    int nextPipe = coordsStr.indexOf('|', pipePos);
                    String coordPair = (nextPipe >= 0) ? coordsStr.substring(pipePos, nextPipe) : coordsStr.substring(pipePos);
                    int sepPos = coordPair.indexOf(';');
                    if (sepPos < 0) sepPos = coordPair.indexOf(',');
                    if (sepPos > 0) {
                        double lat = coordPair.substring(0, sepPos).toDouble();
                        double lon = coordPair.substring(sepPos + 1).toDouble();
                        if (lat != 0.0 && lon != 0.0) {
                            existing.encounterCoordinates.push_back({lat, lon});
                        }
                    }
                    pipePos = (nextPipe >= 0) ? nextPipe + 1 : -1;
                }
            }
            
            loaded++;
            continue;
        }
        
        // New device - create new entry
        TrackingInfo info;
        info.type = type.length() > 0 ? type : "Unknown";
        info.name = name.length() > 0 && name != "Unknown" ? name : "";
        info.lastSeen = lastSeen;
        info.firstSeen = firstSeen > 0 ? firstSeen : lastSeen;
        info.hitCount = hitCount > 0 ? hitCount : 1;
        info.encounterCount = encounterCount > 0 ? encounterCount : 1;
        info.needsSave = false;
        
        // Initialize default values for fields not in simplified format
        info.lastRSSI = 0;
        info.lastLat = 0.0;
        info.lastLon = 0.0;
        info.totalDist = 0.0;
        info.isRouter = false;
        info.lastEncounterStart = lastSeen;
        info.lastEncounterEnd = 0;
        info.encounterLat = 0.0;
        info.encounterLon = 0.0;
        info.minRSSI = 0;
        info.maxRSSI = 0;
        
        // V2.MAP5: Load encounter coordinates (supports both semicolon and comma separators)
        if (encounterCoords.length() > 0) {
            String coordsStr = encounterCoords;
            int pipePos = 0;
            while (pipePos >= 0) {
                int nextPipe = coordsStr.indexOf('|', pipePos);
                String coordPair = (nextPipe >= 0) ? coordsStr.substring(pipePos, nextPipe) : coordsStr.substring(pipePos);
                int sepPos = coordPair.indexOf(';');
                if (sepPos < 0) sepPos = coordPair.indexOf(',');
                if (sepPos > 0) {
                    double lat = coordPair.substring(0, sepPos).toDouble();
                    double lon = coordPair.substring(sepPos + 1).toDouble();
                    if (lat != 0.0 && lon != 0.0) {
                        info.encounterCoordinates.push_back({lat, lon});
                        if (info.lastLat == 0.0 && info.lastLon == 0.0) {
                            info.lastLat = lat;
                            info.lastLon = lon;
                        }
                    }
                }
                pipePos = (nextPipe >= 0) ? nextPipe + 1 : -1;
            }
        }
        
        potentialFollowers[mac] = info;
        
        // Add to appropriate lists if needed
        if (info.isRouter) {
            knownRouters.insert(mac);
        }
        
        loaded++;
    }
    
    f.close();
    sdBusy = false;  // Release SD lock after load
    
    if (loaded > 0) {
        Serial.print("Loaded ");
        Serial.print(loaded);
        Serial.print(" findings from SD card");
        if (loaded >= MAX_FINDINGS_TO_LOAD) {
            Serial.print(" (limited to ");
            Serial.print(MAX_FINDINGS_TO_LOAD);
            Serial.print(" for memory safety)");
        }
        Serial.println();
    }
}

String getManufacturerInternal(const String& mac) {
    String oui = mac.substring(0, 8);
    oui.toUpperCase();
    
    // Most common phone manufacturers - only most common OUIs
    // Apple (iPhone, iPad) - most common OUIs
    if (oui.startsWith("AC:DE:48") || oui.startsWith("D0:03:DF") || oui.startsWith("F0:DB:E2") || 
        oui.startsWith("00:23:DF") || oui.startsWith("00:25:00") || oui.startsWith("00:03:93") ||
        oui.startsWith("00:05:02") || oui.startsWith("00:0A:95") || oui.startsWith("00:0D:93") ||
        oui.startsWith("FC:FB:FB")) return "Apple";
    // Samsung (most common OUIs)
    if (oui.startsWith("00:1C:43") || oui.startsWith("28:F0:76") || oui.startsWith("F8:04:2E") ||
        oui.startsWith("CC:F9:E8") || oui.startsWith("00:00:F0") || oui.startsWith("00:07:AB") ||
        oui.startsWith("00:12:47") || oui.startsWith("38:E0:8E") || oui.startsWith("8C:71:F8")) return "Samsung";
    // Huawei (most common OUIs)
    if (oui.startsWith("00:0C:E7") || oui.startsWith("8C:BE:BE") || oui.startsWith("D8:49:0B") ||
        oui.startsWith("A4:50:46") || oui.startsWith("00:E0:FC") || oui.startsWith("24:DF:6A") ||
        oui.startsWith("34:2E:B4") || oui.startsWith("80:38:BC") || oui.startsWith("A4:A4:6B") ||
        oui.startsWith("88:40:3B")) return "HUAWEI TECHNOLOGIES CO.,LTD";
    // Nokia (most common OUIs)
    if (oui.startsWith("D4:12:43") || oui.startsWith("AC:9B:0A") || oui.startsWith("F0:EE:10")) return "Nokia";
    // OnePlus / Oppo (most common OUIs)
    if (oui.startsWith("F4:8B:32") || oui.startsWith("A0:75:91") || oui.startsWith("E4:50:EB") ||
        oui.startsWith("64:A2:F9") || oui.startsWith("50:8F:4C") || oui.startsWith("7C:46:85") ||
        oui.startsWith("98:ED:5C")) return "OnePlus/Oppo";
    // Xiaomi (most common OUIs)
    if (oui.startsWith("34:CE:00") || oui.startsWith("C0:EE:FB") || oui.startsWith("DC:66:72") ||
        oui.startsWith("64:B4:73") || oui.startsWith("18:59:36") || oui.startsWith("28:6C:07") ||
        oui.startsWith("64:CC:2E") || oui.startsWith("AC:F7:F3")) return "Xiaomi";
    
    // Google (Pixel phones)
    if (oui.startsWith("3C:5A:B4") || oui.startsWith("D8:EB:46") || oui.startsWith("F4:F5:D8")) return "Google";
    
    // Sony (Xperia phones)
    if (oui.startsWith("00:01:4A") || oui.startsWith("00:0A:D9") || oui.startsWith("00:1E:45") ||
        oui.startsWith("F8:E0:79")) return "Sony";
    
    // TP-Link (common router/access point manufacturer)
    if (oui.startsWith("E4:FA:C4") || oui.startsWith("00:27:19") || oui.startsWith("50:C7:BF") ||
        oui.startsWith("F4:EC:38") || oui.startsWith("C8:3A:35") || oui.startsWith("A0:F3:C1")) return "TP-Link Systems Inc";
    
    // DNA / Sagemcom Broadband (router/modems)
    if (oui.startsWith("38:E1:F4")) return "DNA / Sagemcom Broadband";
    
    // ACCU-TIME SYSTEMS
    if (oui.startsWith("00:60:95")) return "ACCU-TIME SYSTEMS";
    
    // ASUSTek COMPUTER INC. (ASUS routers, laptops, etc.)
    if (oui.startsWith("3C:7C:3F")) return "ASUSTek COMPUTER INC.";
    
    // ZTE Corporation (phones, routers, modems)
    if (oui.startsWith("B8:D4:BC")) return "ZTE Corporation";
    
    // Cypress (common WiFi/BLE chips)
    if (oui.startsWith("00:A0:50")) return "Cypress Semiconductor";
    
    // Silicon Laboratories (common WiFi/BLE chips)
    if (oui.startsWith("5C:C7:C1")) return "Silicon Laboratories";
    
    // Smartwatches and rings
    // Oura (ring) - most common OUIs
    if (oui.startsWith("F4:CF:E2") || oui.startsWith("E4:67:1D") || oui.startsWith("F0:3D:29") ||
        oui.startsWith("C8:3C:85") || oui.startsWith("00:25:7E")) return "Oura Health";
    // Polar (smartwatches) - most common OUIs
    if (oui.startsWith("00:1C:2A") || oui.startsWith("00:17:E5") || oui.startsWith("D4:4B:5E") ||
        oui.startsWith("00:22:D7") || oui.startsWith("00:22:D0")) return "Polar";
    // Garmin (smartwatches) - most common OUIs
    if (oui.startsWith("00:0A:3A") || oui.startsWith("04:FE:31") || oui.startsWith("28:FD:80") ||
        oui.startsWith("20:15:06") || oui.startsWith("E0:42:DC") || oui.startsWith("00:1E:31") ||
        oui.startsWith("10:C6:1F") || oui.startsWith("EC:FE:7E")) return "Garmin";
    // Fitbit (smartwatches) - most common OUIs
    if (oui.startsWith("D0:26:AB") || oui.startsWith("D8:31:34") || oui.startsWith("DC:97:91") ||
        oui.startsWith("F4:F5:DB") || oui.startsWith("DC:3A:5E") || oui.startsWith("18:B4:30") ||
        oui.startsWith("20:F0:76") || oui.startsWith("8C:58:77")) return "Fitbit";
    // Amazfit (smartwatches) - most common OUIs
    if (oui.startsWith("90:03:B7") || oui.startsWith("88:DC:96") || oui.startsWith("0C:8B:FD")) return "Amazfit";
    // Suunto (smartwatches) - most common OUIs
    if (oui.startsWith("E0:68:6D") || oui.startsWith("E0:7F:88") || oui.startsWith("F0:43:47") ||
        oui.startsWith("00:0A:31")) return "Suunto";
    // Fossil (smartwatches) - most common OUIs
    if (oui.startsWith("78:28:CA") || oui.startsWith("B0:35:9F") || oui.startsWith("4C:CC:6A")) return "Fossil";
    
    // Withings (smartwatches/health devices)
    if (oui.startsWith("00:24:E4")) return "Withings";
    
    // Casio (smartwatches)
    if (oui.startsWith("00:0B:07") || oui.startsWith("44:D8:32")) return "Casio";
    
    // Ultrahuman (smart ring)
    if (oui.startsWith("E4:E1:12")) return "Ultrahuman";
    
    // Whoop (fitness tracker)
    if (oui.startsWith("D0:CF:5E")) return "Whoop";
    
    // Check OUI cache (populated by maclookup.app API)
    if (ouiCache.count(oui) > 0) {
        return ouiCache[oui];
    }
    
    // Limit cache size to prevent memory overflow
    // Priority: Remove routers first, then others, phones last (never if possible)
    if (ouiCache.size() >= MAX_OUI_CACHE_SIZE) {
        int removeCount = MAX_OUI_CACHE_SIZE / 5;  // Remove 20%
        int removed = 0;
        
        // Step 1: Remove router OUIs first (TP-Link, ASUS, DNA/Sagemcom, etc.)
        auto it = ouiCache.begin();
        while (it != ouiCache.end() && removed < removeCount) {
            String oui = it->first;
            String mfg = it->second;
            mfg.toUpperCase();
            
            // Check if this is a router manufacturer
            bool isRouter = (mfg.indexOf("TP-LINK") >= 0 || mfg.indexOf("ASUS") >= 0 || 
                           mfg.indexOf("DNA") >= 0 || mfg.indexOf("SAGEMCOM") >= 0 ||
                           mfg.indexOf("LINKSYS") >= 0 || mfg.indexOf("NETGEAR") >= 0 ||
                           mfg.indexOf("D-LINK") >= 0 || mfg.indexOf("ZTE") >= 0 ||
                           mfg.indexOf("HUAWEI") >= 0);  // Huawei can be router or phone
            
            if (isRouter) {
                it = ouiCache.erase(it);
                removed++;
            } else {
                ++it;
            }
        }
        
        // Step 2: Remove other (non-phone) entries if still need more
        it = ouiCache.begin();
        while (it != ouiCache.end() && removed < removeCount) {
            String mfg = it->second;
            mfg.toUpperCase();
            
            // Check if this is a phone manufacturer (keep these!)
            bool isPhone = (mfg.indexOf("APPLE") >= 0 || mfg.indexOf("SAMSUNG") >= 0 ||
                          mfg.indexOf("XIAOMI") >= 0 || mfg.indexOf("ONEPLUS") >= 0 ||
                          mfg.indexOf("OPPO") >= 0 || mfg.indexOf("GOOGLE") >= 0 ||
                          mfg.indexOf("SONY") >= 0 || mfg.indexOf("NOKIA") >= 0);
            
            // Also check for smartwatches/rings (keep these too)
            bool isWearable = (mfg.indexOf("GARMIN") >= 0 || mfg.indexOf("POLAR") >= 0 ||
                             mfg.indexOf("FITBIT") >= 0 || mfg.indexOf("SUUNTO") >= 0 ||
                             mfg.indexOf("OURA") >= 0 || mfg.indexOf("AMAZFIT") >= 0 ||
                             mfg.indexOf("FOSSIL") >= 0 || mfg.indexOf("WITHINGS") >= 0 ||
                             mfg.indexOf("CASIO") >= 0 || mfg.indexOf("ULTRHUMAN") >= 0 ||
                             mfg.indexOf("WHOOP") >= 0);
            
            if (!isPhone && !isWearable) {
                it = ouiCache.erase(it);
                removed++;
            } else {
                ++it;
            }
        }
        
        // Step 3: Only remove phones if absolutely necessary (cache still too large)
        if (ouiCache.size() >= MAX_OUI_CACHE_SIZE && removed < removeCount) {
            it = ouiCache.begin();
            while (it != ouiCache.end() && removed < removeCount) {
                it = ouiCache.erase(it);
                removed++;
            }
        }
        
        Serial.print("[OUI] Cache limit reached, removed ");
        Serial.print(removed);
        Serial.println(" entries (routers first, phones last)");
    }
    
    // OPTIONAL: Add to Maclookup.app API queue if enabled and not found elsewhere
    // (SD card lookup removed - using only internal list + API)
    #if ENABLE_MACVENDORS_API
    if (WiFi.status() == WL_CONNECTED && macVendorsApiQueue.size() < MAX_API_QUEUE) {
        bool alreadyQueued = false;
        for (const auto& queuedOui : macVendorsApiQueue) {
            if (queuedOui == oui) {
                alreadyQueued = true;
                break;
            }
        }
        if (!alreadyQueued && ouiCache.count(oui) == 0) {
            macVendorsApiQueue.push_back(oui);
        }
    }
    #endif
    
    return "";
}

// SD card OUI lookup removed - using only internal list + maclookup.app API
// This simplifies code and improves performance (no SD card reads needed)

// OPTIONAL: Maclookup.app API lookup (can be disabled by setting ENABLE_MACVENDORS_API to false)
#if ENABLE_MACVENDORS_API
void processMacVendorsApiQueue() {
    if (macVendorsApiQueue.empty()) return;
    if (WiFi.status() != WL_CONNECTED) return;  // Need internet connection
    
    // Rate limiting: minimum 2 seconds between API calls (maclookup.app: 2 req/sec without API key)
    unsigned long now = millis();
    if (now - lastApiCall < API_CALL_INTERVAL) return;
    
    // Process ONE OUI per cycle
    String oui = macVendorsApiQueue.front();
    macVendorsApiQueue.erase(macVendorsApiQueue.begin());
    
    // Skip if already in cache (might have been found from SD card)
    if (ouiCache.count(oui) > 0 && ouiCache[oui].length() > 0) return;
    
    // Build MAC address from OUI (add dummy suffix: 00:00:00)
    String mac = oui + ":00:00:00";
    
    lastApiCall = now;
    
    // Make HTTPS request to maclookup.app API
    WiFiClientSecure client;
    client.setInsecure();  // Skip certificate validation (faster, less secure but OK for public API)
    
    const int httpsPort = 443;
    const char* host = "api.maclookup.app";
    
    if (!client.connect(host, httpsPort)) {
        Serial.print("[API] Failed to connect to ");
        Serial.println(host);
        // Don't cache failure - allow retry later
        return;
    }
    
    // Send HTTP GET request to API V2 endpoint
    client.print("GET /v2/macs/");
    client.print(mac);
    client.println(" HTTP/1.1");
    client.print("Host: ");
    client.println(host);
    client.println("Connection: close");
    client.println();
    
    // Wait for response (with timeout)
    unsigned long timeout = millis() + 5000;  // 5 second timeout
    while (client.available() == 0 && millis() < timeout) {
        delay(10);
    }
    
    if (millis() >= timeout) {
        Serial.println("[API] Request timeout");
        client.stop();
        return;
    }
    
    // Read response (skip HTTP headers, get JSON body)
    String response = "";
    bool headersDone = false;
    while (client.available()) {
        String line = client.readStringUntil('\n');
        line.trim();
        if (line.length() == 0) {
            headersDone = true;  // Empty line = end of headers
            continue;
        }
        if (headersDone) {
            // Accumulate JSON response (may be multiple lines)
            if (response.length() > 0) response += "\n";
            response += line;
        }
    }
    client.stop();
    
    // Parse JSON response to extract "company" field
    // Simple JSON parsing: look for "company":"value"
    String manufacturer = "";
    int companyIndex = response.indexOf("\"company\"");
    if (companyIndex >= 0) {
        int colonIndex = response.indexOf(":", companyIndex);
        if (colonIndex >= 0) {
            int quoteStart = response.indexOf("\"", colonIndex);
            if (quoteStart >= 0) {
                int quoteEnd = response.indexOf("\"", quoteStart + 1);
                if (quoteEnd >= 0) {
                    manufacturer = response.substring(quoteStart + 1, quoteEnd);
                }
            }
        }
    }
    
    // Process response from primary API (maclookup.app)
    if (manufacturer.length() > 0 && manufacturer.length() < 100) {  // Valid manufacturer name
        manufacturer.trim();
        ouiCache[oui] = manufacturer;
        Serial.print("[API] Found manufacturer: ");
        Serial.print(oui);
        Serial.print(" = ");
        Serial.println(manufacturer);
        return;  // Success - no need for fallback
    }
    
    // Primary API didn't find result - try fallback API (macaddress.io)
    #if USE_FALLBACK_API
    Serial.print("[API] Primary API no result, trying fallback for ");
    Serial.println(oui);
    
    // Wait a bit before fallback (respect rate limits)
    delay(500);
    
    WiFiClientSecure clientFallback;
    clientFallback.setInsecure();
    const char* hostFallback = "api.macaddress.io";
    
    if (!clientFallback.connect(hostFallback, httpsPort)) {
        Serial.print("[API] Fallback failed to connect to ");
        Serial.println(hostFallback);
        ouiCache[oui] = "";  // Cache empty to avoid retry
        return;
    }
    
    // Build MAC without colons for macaddress.io (format: AABBCCDDEEFF)
    String macNoColons = mac;
    macNoColons.replace(":", "");
    
    // Send HTTP GET request to macaddress.io API
    clientFallback.print("GET /v1?output=json&search=");
    clientFallback.print(macNoColons);
    clientFallback.println(" HTTP/1.1");
    clientFallback.print("Host: ");
    clientFallback.println(hostFallback);
    clientFallback.println("Connection: close");
    clientFallback.println();
    
    // Wait for response (with timeout)
    timeout = millis() + 5000;
    while (clientFallback.available() == 0 && millis() < timeout) {
        delay(10);
    }
    
    if (millis() >= timeout) {
        Serial.println("[API] Fallback request timeout");
        clientFallback.stop();
        ouiCache[oui] = "";
        return;
    }
    
    // Read fallback response
    String responseFallback = "";
    headersDone = false;
    while (clientFallback.available()) {
        String line = clientFallback.readStringUntil('\n');
        line.trim();
        if (line.length() == 0) {
            headersDone = true;
            continue;
        }
        if (headersDone) {
            if (responseFallback.length() > 0) responseFallback += "\n";
            responseFallback += line;
        }
    }
    clientFallback.stop();
    
    // Parse fallback JSON response (macaddress.io format may differ)
    // Try to find vendor/company name in JSON
    String manufacturerFallback = "";
    int vendorIndex = responseFallback.indexOf("\"vendor\"");
    if (vendorIndex < 0) vendorIndex = responseFallback.indexOf("\"company\"");
    if (vendorIndex < 0) vendorIndex = responseFallback.indexOf("\"organization\"");
    
    if (vendorIndex >= 0) {
        int colonIndex = responseFallback.indexOf(":", vendorIndex);
        if (colonIndex >= 0) {
            int quoteStart = responseFallback.indexOf("\"", colonIndex);
            if (quoteStart >= 0) {
                int quoteEnd = responseFallback.indexOf("\"", quoteStart + 1);
                if (quoteEnd >= 0) {
                    manufacturerFallback = responseFallback.substring(quoteStart + 1, quoteEnd);
                }
            }
        }
    }
    
    // Process fallback response
    if (manufacturerFallback.length() > 0 && manufacturerFallback.length() < 100) {
        manufacturerFallback.trim();
        ouiCache[oui] = manufacturerFallback;
        Serial.print("[API] Fallback found manufacturer: ");
        Serial.print(oui);
        Serial.print(" = ");
        Serial.println(manufacturerFallback);
    } else {
        // Both APIs failed - cache empty
        ouiCache[oui] = "";
        Serial.print("[API] No result from primary or fallback for ");
        Serial.println(oui);
    }
    #else
    // Fallback disabled - just cache empty
    ouiCache[oui] = "";
    Serial.print("[API] No result for ");
    Serial.println(oui);
    #endif
}
#else
// API disabled - empty function
void processMacVendorsApiQueue() {
    // API calls disabled - set ENABLE_MACVENDORS_API to true to enable
}
#endif

bool isRandomized(const String& mac) {
    if (mac.length() < 2) return false;
    char secondChar = toupper(mac.charAt(1));
    // If second character is 2, 6, A or E, it's a randomized/private MAC
    return (secondChar == '2' || secondChar == '6' || secondChar == 'A' || secondChar == 'E');
}

// V2.4.5: Load TIME_WINDOW_3_MS from SD card config file
void loadWindow3Config() {
    if (!sdReady) {
        TIME_WINDOW_3_MS = TIME_WINDOW_3_DEFAULT;  // Use default if SD not ready
        return;
    }
    if (sdBusy) return;
    
    if (!SD.exists("/window3_config.txt")) {
        TIME_WINDOW_3_MS = TIME_WINDOW_3_DEFAULT;  // Use default if file doesn't exist
        return;
    }
    
    sdBusy = true;
    sdBusyStartTime = millis();
    File f = SD.open("/window3_config.txt", FILE_READ);
    if (f) {
        String value = f.readStringUntil('\n');
        value.trim();
        unsigned long configValue = value.toInt();
        if (configValue >= TIME_WINDOW_3_DEFAULT && configValue <= TIME_WINDOW_3_24H) {
            TIME_WINDOW_3_MS = configValue;
            Serial.print("[CONFIG] Loaded TIME_WINDOW_3_MS: ");
            Serial.print(TIME_WINDOW_3_MS / 60000);
            Serial.println(" minutes");
        } else {
            TIME_WINDOW_3_MS = TIME_WINDOW_3_DEFAULT;
        }
        f.close();
    } else {
        TIME_WINDOW_3_MS = TIME_WINDOW_3_DEFAULT;
    }
    sdBusy = false;
}

// V2.4.5: Save TIME_WINDOW_3_MS to SD card config file
void saveWindow3Config() {
    if (!sdReady || sdBusy) return;
    
    sdBusy = true;
    sdBusyStartTime = millis();
    if (SD.exists("/window3_config.txt")) {
        SD.remove("/window3_config.txt");
    }
    
    File f = SD.open("/window3_config.txt", FILE_WRITE);
    if (f) {
        f.println(String(TIME_WINDOW_3_MS));
        f.close();
        Serial.print("[CONFIG] Saved TIME_WINDOW_3_MS: ");
        Serial.print(TIME_WINDOW_3_MS / 60000);
        Serial.println(" minutes");
    }
    sdBusy = false;
}

// V2.MAP1: Load GPS source from SD card config file
void loadGpsSourceConfig() {
    if (!sdReady || sdBusy) {
        preferences.begin("afosca", true);
        int saved = preferences.getInt("gps_source", -1);
        preferences.end();
        if (saved >= 0 && saved <= 2) {
            gpsSource = (GpsSource)saved;
            Serial.print("[NVS] Loaded GPS source: ");
            if (gpsSource == GPS_SOURCE_DEVICE) Serial.println("Device GPS");
            else if (gpsSource == GPS_SOURCE_PHONE) Serial.println("Phone GPS");
            else Serial.println("Both");
        } else {
            Serial.println("[NVS] No GPS source saved, using default");
        }
        return;
    }
    
    if (!SD.exists("/gps_source_config.txt")) {
        preferences.begin("afosca", true);
        int saved = preferences.getInt("gps_source", -1);
        preferences.end();
        if (saved >= 0 && saved <= 2) {
            gpsSource = (GpsSource)saved;
            Serial.print("[NVS] Loaded GPS source (no SD file): ");
            Serial.println((int)gpsSource);
        } else {
            Serial.print("[CONFIG] GPS source config not found, using default: ");
            Serial.println((int)gpsSource);
        }
        return;
    }
    
    sdBusy = true;
    sdBusyStartTime = millis();
    File f = SD.open("/gps_source_config.txt", FILE_READ);
    if (f) {
        String value = f.readStringUntil('\n');
        value.trim();
        int sourceValue = value.toInt();
        if (sourceValue >= 0 && sourceValue <= 2) {
            gpsSource = (GpsSource)sourceValue;
            Serial.print("[CONFIG] Loaded GPS source: ");
            if (gpsSource == GPS_SOURCE_DEVICE) Serial.println("Device GPS");
            else if (gpsSource == GPS_SOURCE_PHONE) Serial.println("Phone GPS");
            else Serial.println("Both");
        }
        f.close();
    }
    sdBusy = false;
}

// V2.MAP1: Save GPS source to SD card config file
void saveGpsSourceConfig() {
    preferences.begin("afosca", false);
    preferences.putInt("gps_source", (int)gpsSource);
    preferences.end();

    if (!sdReady || sdBusy) return;
    
    sdBusy = true;
    sdBusyStartTime = millis();
    if (SD.exists("/gps_source_config.txt")) {
        SD.remove("/gps_source_config.txt");
    }
    
    File f = SD.open("/gps_source_config.txt", FILE_WRITE);
    if (f) {
        f.println(String((int)gpsSource));
        f.close();
        Serial.print("[CONFIG] Saved GPS source: ");
        Serial.println((int)gpsSource);
    }
    sdBusy = false;
}

// V2.MAP1: Load GPS lock state from SD card or NVS
void loadGpsLockConfig() {
    if (!sdReady || sdBusy) {
        preferences.begin("afosca", true);
        int saved = preferences.getInt("gps_lock", -1);
        preferences.end();
        if (saved >= 0) {
            gpsSourceLocked = (saved == 1);
            Serial.print("[NVS] Loaded GPS lock: ");
            Serial.println(gpsSourceLocked ? "Locked" : "Unlocked");
        }
        return;
    }
    
    if (!SD.exists("/gps_lock_config.txt")) {
        preferences.begin("afosca", true);
        int saved = preferences.getInt("gps_lock", -1);
        preferences.end();
        if (saved >= 0) {
            gpsSourceLocked = (saved == 1);
            Serial.print("[NVS] Loaded GPS lock (no SD file): ");
            Serial.println(gpsSourceLocked ? "Locked" : "Unlocked");
        }
        return;
    }
    
    sdBusy = true;
    sdBusyStartTime = millis();
    File f = SD.open("/gps_lock_config.txt", FILE_READ);
    if (f) {
        String value = f.readStringUntil('\n');
        value.trim();
        gpsSourceLocked = (value.toInt() == 1);
        Serial.print("[CONFIG] Loaded GPS lock: ");
        Serial.println(gpsSourceLocked ? "Locked" : "Unlocked");
        f.close();
    }
    sdBusy = false;
}

// V2.MAP1: Save GPS lock state to SD card config file
void saveGpsLockConfig() {
    preferences.begin("afosca", false);
    preferences.putInt("gps_lock", gpsSourceLocked ? 1 : 0);
    preferences.end();

    if (!sdReady || sdBusy) return;
    
    sdBusy = true;
    sdBusyStartTime = millis();
    if (SD.exists("/gps_lock_config.txt")) {
        SD.remove("/gps_lock_config.txt");
    }
    
    File f = SD.open("/gps_lock_config.txt", FILE_WRITE);
    if (f) {
        f.println(String(gpsSourceLocked ? "1" : "0"));
        f.close();
        Serial.print("[CONFIG] Saved GPS lock: ");
        Serial.println(gpsSourceLocked ? "Locked" : "Unlocked");
    }
    sdBusy = false;
}

// Load filter state from internal NVS memory (fast, no SD card wear)
void loadFilterConfig() {
    preferences.begin("afosca", true);  // Read-only mode, namespace "afosca"
    
    // Get filter state, default to true (enabled) if not found
    filterEnabled = preferences.getBool("filter", true);
    
    preferences.end();
    
    Serial.print("[CONFIG] Loaded filter state from NVS: ");
    Serial.println(filterEnabled ? "Enabled" : "Disabled");
}

// Save filter state to internal NVS memory (fast, no SD card wear)
void saveFilterConfig() {
    preferences.begin("afosca", false);  // Read-write mode
    
    preferences.putBool("filter", filterEnabled);
    
    preferences.end();
    
    Serial.print("[CONFIG] Saved filter state to NVS: ");
    Serial.println(filterEnabled ? "Enabled" : "Disabled");
}

void saveWhitelistToNVS() {
    preferences.begin("afosca", false);
    String packed = "";
    int count = 0;
    for (auto const& id : whitelist) {
        if (packed.length() + id.length() + 1 > 3800) break;
        if (packed.length() > 0) packed += ";";
        packed += id;
        count++;
    }
    preferences.putString("wl_data", packed);
    preferences.putInt("wl_count", count);
    preferences.end();
    Serial.print("[NVS] Saved whitelist backup: ");
    Serial.print(count);
    Serial.println(" items");
}

void loadWhitelistFromNVS() {
    preferences.begin("afosca", true);
    int count = preferences.getInt("wl_count", 0);
    if (count == 0) {
        preferences.end();
        Serial.println("[NVS] No whitelist backup found");
        return;
    }
    String packed = preferences.getString("wl_data", "");
    preferences.end();
    if (packed.length() == 0) {
        Serial.println("[NVS] WARNING: wl_count>0 but wl_data empty - NVS may be corrupt");
        return;
    }
    
    whitelist.clear();
    int loaded = 0;
    int start = 0;
    for (int i = 0; i <= (int)packed.length(); i++) {
        if (i == (int)packed.length() || packed.charAt(i) == ';') {
            if (i > start) {
                String mac = packed.substring(start, i);
                mac.trim();
                if (mac.length() >= 17) {
                    whitelist.insert(mac);
                    loaded++;
                }
            }
            start = i + 1;
        }
    }
    Serial.print("[NVS] Loaded whitelist backup: ");
    Serial.print(loaded);
    Serial.print(" items (stored count: ");
    Serial.print(count);
    Serial.println(")");
}

// Load hotspot SSID and password from SD card
void loadHotspotConfig() {
    if (!sdReady) {
        Serial.println("[HOTSPOT] SD card not ready, cannot load hotspot config!");
        return;
    }
    if (sdBusy) {
        Serial.println("[HOTSPOT] SD busy, skipping hotspot config load");
        return;
    }
    
    if (!SD.exists("/hotspot_config.txt")) {
        Serial.println("[HOTSPOT] File /hotspot_config.txt does not exist!");
        Serial.println("[HOTSPOT] Create file with format:");
        Serial.println("[HOTSPOT] SSID=YourHotspotName");
        Serial.println("[HOTSPOT] PASSWORD=YourPassword");
        Serial.println("[HOTSPOT] STATIC_IP=192.168.43.100  (optional, default IP)");
        Serial.println("[HOTSPOT] GATEWAY=192.168.43.1      (optional, default gateway)");
        Serial.println("[HOTSPOT] USE_STATIC_IP=1           (optional, 1=yes, 0=no, default=1)");
        return;
    }
    
    sdBusy = true;
    sdBusyStartTime = millis();
    File f = SD.open("/hotspot_config.txt", FILE_READ);
    if (f) {
        Serial.println("[HOTSPOT] Reading hotspot config from SD card...");
        while (f.available()) {
            String line = f.readStringUntil('\n');
            line.trim();
            
            if (line.length() == 0) continue;
            
            // Parse SSID=value or PASSWORD=value format
            int eqPos = line.indexOf('=');
            if (eqPos > 0) {
                String key = line.substring(0, eqPos);
                key.trim();
                key.toUpperCase();
                String value = line.substring(eqPos + 1);
                value.trim();
                
                if (key == "SSID") {
                    hotspot_ssid = value;
                    Serial.print("[HOTSPOT] Loaded SSID: ");
                    Serial.println(hotspot_ssid);
                } else if (key == "PASSWORD") {
                    hotspot_password = value;
                    Serial.print("[HOTSPOT] Loaded PASSWORD: ");
                    Serial.println(hotspot_password.length() > 0 ? "***" : "(empty)");
                } else if (key == "STATIC_IP") {
                    // Parse IP address (format: 192.168.43.100)
                    int dots = 0;
                    int lastDot = -1;
                    int octets[4] = {0};
                    bool valid = true;
                    for (int i = 0; i < value.length() && dots < 4; i++) {
                        if (value[i] == '.') {
                            if (dots < 3) {
                                String octet = value.substring(lastDot + 1, i);
                                octets[dots] = octet.toInt();
                                if (octets[dots] < 0 || octets[dots] > 255) valid = false;
                                dots++;
                                lastDot = i;
                            }
                        }
                    }
                    if (dots == 3 && valid) {
                        String octet = value.substring(lastDot + 1);
                        octets[3] = octet.toInt();
                        if (octets[3] >= 0 && octets[3] <= 255) {
                            static_ip = IPAddress(octets[0], octets[1], octets[2], octets[3]);
                            use_static_ip = true;
                            Serial.print("[HOTSPOT] Loaded STATIC_IP: ");
                            Serial.println(static_ip);
                        }
                    }
                } else if (key == "GATEWAY") {
                    // Parse gateway IP (format: 192.168.43.1)
                    int dots = 0;
                    int lastDot = -1;
                    int octets[4] = {0};
                    bool valid = true;
                    for (int i = 0; i < value.length() && dots < 4; i++) {
                        if (value[i] == '.') {
                            if (dots < 3) {
                                String octet = value.substring(lastDot + 1, i);
                                octets[dots] = octet.toInt();
                                if (octets[dots] < 0 || octets[dots] > 255) valid = false;
                                dots++;
                                lastDot = i;
                            }
                        }
                    }
                    if (dots == 3 && valid) {
                        String octet = value.substring(lastDot + 1);
                        octets[3] = octet.toInt();
                        if (octets[3] >= 0 && octets[3] <= 255) {
                            gateway = IPAddress(octets[0], octets[1], octets[2], octets[3]);
                            dns = gateway;  // DNS usually same as gateway
                            Serial.print("[HOTSPOT] Loaded GATEWAY: ");
                            Serial.println(gateway);
                        }
                    }
                } else if (key == "USE_STATIC_IP") {
                    String valueUpper = value;
                    valueUpper.toUpperCase();
                    use_static_ip = (value == "1" || valueUpper == "TRUE");
                    Serial.print("[HOTSPOT] USE_STATIC_IP: ");
                    Serial.println(use_static_ip ? "YES" : "NO");
                }
            }
        }
        f.close();
        
        if (hotspot_ssid.length() == 0) {
            Serial.println("[HOTSPOT] ERROR: SSID not found in config file!");
        }
        if (hotspot_password.length() == 0) {
            Serial.println("[HOTSPOT] WARNING: PASSWORD is empty!");
        }
    } else {
        Serial.println("[HOTSPOT] ERROR: Failed to open /hotspot_config.txt");
    }
    sdBusy = false;
}

bool isRouterByName(const String& name) {
    if (name.length() == 0) return false;
    
    String nameLower = name;
    nameLower.toLowerCase();
    
    for (int i = 0; i < routerKeywordCount; i++) {
        if (nameLower.indexOf(routerKeywords[i]) != -1) {
            return true;
        }
    }
    return false;
}

void updateGpsCoordinates() {
    // Update GPS coordinates - throttled to reduce calculations, but always check phone GPS age
    unsigned long now = millis();
    
    // For phone GPS, always check if location is still valid (age check is fast)
    // For device GPS, throttle to reduce serial reads
    bool needsFullUpdate = (now - lastGpsUpdate >= GPS_UPDATE_INTERVAL);
    
    // V2.MAP1: Handle different GPS sources
    if (gpsSource == GPS_SOURCE_PHONE) {
        // Phone GPS only - check if phone location is recent (within 5 minutes)
        if (lastPhoneLocationUpdate > 0 && 
            (now - lastPhoneLocationUpdate) < 300000) {  // 5 minutes max age
            gpsValid = true;  // Phone location is valid
            // currentLat and currentLon are already set by /update_location endpoint
        } else {
            // Only set to false if we've been waiting for more than 15 seconds
            // This gives JavaScript time to get location on page load (2s delay + 10s timeout + 3s buffer)
            static unsigned long startupTime = 0;
            if (startupTime == 0) startupTime = now;
            
            if (lastPhoneLocationUpdate == 0 && (now - startupTime) < 15000) {
                // Still waiting for first location update (allow 15 seconds grace period)
                // Don't set gpsValid to false yet - keep it as is
            } else if (lastPhoneLocationUpdate > 0) {
                // Had location before, but it's now too old
                gpsValid = false;
            } else {
                // No location yet, and grace period expired
                gpsValid = false;
            }
        }
        
        // Phone GPS already updated above, skip device GPS check
        if (!needsFullUpdate) {
            return;
        }
        lastGpsUpdate = now;
    }
    else if (gpsSource == GPS_SOURCE_DEVICE) {
        lastGpsUpdate = now;
        // Device GPS only (original logic)
        gpsValid = gps.location.isValid();
        if (gpsValid) {
            currentLat = gps.location.lat();
            currentLon = gps.location.lng();
        }
    }
    else if (gpsSource == GPS_SOURCE_BOTH) {
        lastGpsUpdate = now;
        // Both - priority: phone first, then device
        bool phoneValid = (lastPhoneLocationUpdate > 0 && 
                          (now - lastPhoneLocationUpdate) < 300000);  // 5 minutes max age
        bool deviceValid = gps.location.isValid();
        
        if (phoneValid) {
            // Use phone GPS
            gpsValid = true;
            // currentLat and currentLon are already set
        } else if (deviceValid) {
            // Use device GPS
            gpsValid = true;
            currentLat = gps.location.lat();
            currentLon = gps.location.lng();
        } else {
            gpsValid = false;
        }
    }
}

void processDevice(String type, String id, int rssi, String name, int wifiChannel) {
    id.toUpperCase();
    
    // Filter out randomized MAC addresses from tracking (but still allow them to be shown on randomized page)
    // Note: We don't filter here - we'll filter in display logic instead to allow viewing randomized MACs
    
    // Check if device is a known router
    bool isR = (knownRouters.count(id) > 0);
    
    // Additional router detection by name
    if (!isR && name.length() > 0) {
        isR = isRouterByName(name);
    }
    
    unsigned long now = millis();

    // Kalman filtering for BLE and WiFi RSSI per MAC address
    if (type == "BLE" || type == "WiFi") {
        float rawRssi = (float)rssi;
        auto itFilter = rssiFilters.find(id);
        if (itFilter == rssiFilters.end()) {
            // First measurement for this device
            rssiFilters.emplace(id, KalmanFilter(0.01f, 2.0f, 1.0f, rawRssi));
            itFilter = rssiFilters.find(id);
        }
        float filtered = itFilter->second.update(rawRssi);
        rssi = (int)roundf(filtered);
    }
    
    if (potentialFollowers.count(id)) {
        auto& it = potentialFollowers[id];
        
        // ===== ENCOUNTER DETECTION =====
        // New encounter if: 5+ min gap OR 500m+ distance from last encounter
        bool newEncounter = false;
        unsigned long timeSinceLastSeen = safeTimeDiff(now, it.lastSeen);
        
        // Time-based encounter detection
        if (timeSinceLastSeen > ENCOUNTER_GAP_MS) {
            newEncounter = true;
        }
        
        // Distance-based encounter detection (if GPS available)
        if (!newEncounter && gpsValid && it.encounterLat != 0.0) {
            double distFromEncounter = TinyGPSPlus::distanceBetween(
                it.encounterLat, it.encounterLon, currentLat, currentLon);
            if (distFromEncounter > ENCOUNTER_DISTANCE_M) {
                newEncounter = true;
            }
        }
        
        if (newEncounter) {
            it.lastEncounterEnd = it.lastSeen;  // Previous encounter ended
            it.lastEncounterStart = now;        // New encounter starts
            it.encounterCount++;
            it.needsSave = true;  // Log this new encounter
            
            // V2.MAP1: Store encounter GPS location (both old way and new list)
            if (gpsValid) {
                it.encounterLat = currentLat;  // Keep for compatibility
                it.encounterLon = currentLon;  // Keep for compatibility
                // Add to encounter coordinates list
                it.encounterCoordinates.push_back({currentLat, currentLon});
                // Limit list size to prevent memory issues (keep last 20 encounters)
                if (it.encounterCoordinates.size() > 20) {
                    it.encounterCoordinates.erase(it.encounterCoordinates.begin());
                }
            }
            
            // Serial.print("NEW ENCOUNTER #");
            // Serial.print(it.encounterCount);
            // Serial.print(" for ");
            // Serial.println(id);
        }
        
        // Update basic tracking
        it.lastSeen = now;
        it.lastRSSI = rssi;
        
        // Track RSSI range
        if (rssi < it.minRSSI) it.minRSSI = rssi;
        if (rssi > it.maxRSSI) it.maxRSSI = rssi;
        
        // V2.4.5: Update RSSI variance and time windows
        updateRssiVariance(it, rssi);
        
        if (name.length() > 0) {
            it.name = name;
        }
        
        it.isRouter = isR;
        // Update type if it was Unknown or if we have a more specific detection
        if (it.type == "Unknown" || it.type.length() == 0) {
            it.type = type;  // Set actual detected type (BLE or WiFi)
        }
        
        // V2.4.5: Store WiFi channel for frequency detection (1-13 = 2.4 GHz, 36+ = 5 GHz)
        if (type == "WiFi" && wifiChannel > 0) {
            it.wifiChannel = wifiChannel;
        }
        
        // Update hitCount and check for 12-hour reset
        const unsigned long TWELVE_HOURS_MS = 43200000UL;
        unsigned long timeSinceFirstSeen = safeTimeDiff(now, it.firstSeen);
        if (timeSinceFirstSeen > TWELVE_HOURS_MS) {
            // Reset after 12 hours
            it.firstSeen = now;
            it.hitCount = 1;
            it.encounterCount = 1;  // Reset encounters too
        } else {
            it.hitCount++;
        }
        
        // Update GPS-based tracking if GPS is valid
        // Update distance whenever device is detected (not just when we're moving)
        // This allows tracking device movement even when we're stationary
        if (gpsValid) {
            if (it.lastLat != 0.0 && it.lastLon != 0.0) {
                double d = TinyGPSPlus::distanceBetween(
                    it.lastLat, it.lastLon, currentLat, currentLon);
                
                // Update distance if it changed by more than minimum threshold
                // This prevents tiny GPS jitter from accumulating
                if (d > MIN_DISTANCE_M) {
                    it.totalDist += d;
                    it.needsSave = true;
                }
            }
            
            // Always update last known position when GPS is valid
            it.lastLat = currentLat;
            it.lastLon = currentLon;
        }
        // Note: If GPS is not valid and no position exists, it will remain 0.0,0.0
    } else {
        // New device - first encounter
        TrackingInfo newInfo;
        newInfo.lastSeen = now;
        newInfo.lastRSSI = rssi;
        newInfo.lastLat = gpsValid ? currentLat : 0.0;
        newInfo.lastLon = gpsValid ? currentLon : 0.0;
        newInfo.totalDist = 0.0;
        newInfo.type = type;
        newInfo.name = name;
        newInfo.isRouter = isR;
        newInfo.needsSave = false;
        newInfo.firstSeen = now;
        newInfo.hitCount = 1;
        // Encounter fields
        newInfo.encounterCount = 1;
        newInfo.lastEncounterStart = now;
        newInfo.lastEncounterEnd = 0;
        newInfo.encounterLat = gpsValid ? currentLat : 0.0;
        newInfo.encounterLon = gpsValid ? currentLon : 0.0;
        // V2.MAP1: Initialize encounter coordinates list with first encounter
        if (gpsValid) {
            newInfo.encounterCoordinates.push_back({currentLat, currentLon});
        }
        newInfo.minRSSI = rssi;
        newInfo.maxRSSI = rssi;
        // V2.4.5: WiFi channel for frequency detection
        if (type == "WiFi" && wifiChannel > 0) {
            newInfo.wifiChannel = wifiChannel;
        }
        // V2.4.5: Persistence Score fields
        newInfo.persistenceScore = 0.0;
        newInfo.timeWindow1 = true;  // Currently seen
        newInfo.timeWindow2 = false;
        newInfo.timeWindow3 = false;
        newInfo.windowUpdateTime = now;
        newInfo.rssiSum = rssi;
        newInfo.rssiSumSq = (long)rssi * rssi;
        newInfo.rssiSampleCount = 1;
        newInfo.appearanceCount = 1;
        
        potentialFollowers[id] = newInfo;
    }
}

// --- 5. UI ---
String getStyles() {
    return F(
        "<style>"
        "body{font-family:sans-serif;background:#0d0d0d;color:#eee;padding:10px;text-align:center;margin:0;}"
        ".top-bar{display:flex;flex-direction:row;justify-content:space-between;align-items:center;padding:8px 12px;background:#111;border-bottom:1px solid #333;}"
        ".header-title{font-weight:bold;color:#4caf50;text-shadow:0 0 10px #4caf50,0 0 20px #4caf50,0 0 30px #2e7d32;letter-spacing:2px;}"
        ".status-group{display:flex;flex-direction:row;gap:8px;align-items:center;flex-wrap:nowrap;} "
        ".status-icons{display:flex;gap:3px;align-items:center;flex-shrink:0;} "
        ".settings-group{display:flex;flex-direction:column;gap:4px;align-items:center;flex-shrink:0;min-width:60px;} "
        ".stat-icon{font-size:1.1em; filter:grayscale(100%); transition:0.5s;} "
        ".icon-ok{filter:grayscale(0%); color:#4caf50;} "
        ".icon-invalid{filter:grayscale(0%); color:#ff9800;} "
        ".sd-text{font-size:0.7em; font-weight:bold; color:#b71c1c;} "
        ".sd-ok{color:#2e7d32;}"
        ".nav{display:flex;gap:5px;margin:12px 0;justify-content:center;}"
        ".nav-btn{padding:10px 5px; border-radius:6px; background:#222; color:white; text-decoration:none; font-weight:bold; border:1px solid #444; font-size:0.7em; flex:1;}"
        ".btn-active{background:#2e7d32; border-color:#4caf50;}"
        ".card{background:#1a1a1a;padding:12px;margin:8px auto;border-radius:10px;text-align:left;max-width:500px;border-left:8px solid #333;position:relative;overflow:hidden;}"
        ".wifi-border{border-left-color:#ff5252;} "
        ".ble-border{border-left-color:#00bcd4;} "
        ".white-border{border-left-color:#42a5f5;} "
        ".router-border{border-left-color:#4caf50;}"
        ".chk-box{position:absolute;right:12px;top:50%;transform:translateY(-50%) scale(1.4);z-index:10;}"
        ".radar{width:120px;height:120px;position:relative;margin:10px auto;border:2px solid #4caf50;border-radius:50%;background:#001a00;overflow:hidden;}"
        ".r-circle{position:absolute;top:50%;left:50%;transform:translate(-50%,-50%);border:1px solid #4caf5044;border-radius:50%;}"
        ".r-cross-v{position:absolute;top:0;left:50%;width:1px;height:100%;background:#4caf5044;}"
        ".r-cross-h{position:absolute;top:50%;left:0;width:100%;height:1px;background:#4caf5044;}"
        ".sweep{position:absolute;top:50%;left:50%;width:50%;height:2px;background:linear-gradient(90deg,#4caf50,transparent);transform-origin:0 50%;animation:rot 3s linear infinite;} "
        "@keyframes rot{from{transform:rotate(0deg);}to{transform:rotate(360deg);}}"
        ".blip{position:absolute;width:8px;height:8px;background:#fff;border-radius:50%;box-shadow:0 0 10px #fff;z-index:9;animation:f 6s forwards;} "
        "@keyframes f{0%{opacity:1;} 100%{opacity:0; transform:scale(0.5);}} "
        "@keyframes blink{0%,100%{opacity:1;} 50%{opacity:0.5;}}"
        "@keyframes blink-alert{0%,50%{opacity:1;} 51%,100%{opacity:0.3;}}"
        ".blink-slow{animation:blink-alert 1.5s infinite;}"
        ".blink-medium{animation:blink-alert 1.0s infinite;}"
        ".blink-fast{animation:blink-alert 0.5s infinite;}"
        ".score-badge{position:absolute;top:8px;right:50px;font-size:0.75em;font-weight:bold;padding:2px 8px;border-radius:10px;}"
        ".rssi-bar{height:8px; background:#444; border-radius:4px; margin:8px 0; overflow:hidden; width:80%;} "
        ".rssi-fill{height:100%; transition: 0.5s;}"
        ".deauth-icon{font-size:1.1em; color:#666; transition:0.3s; display:none;} "
        ".deauth-visible{display:block !important; text-align:center;} "
        ".deauth-alarm{color:#ff1744; animation:deauth-blink 0.5s infinite;} "
        ".deauth-warning{color:#ff9800; background:#4a2800; padding:2px 6px; border-radius:4px;} "
        "@keyframes deauth-blink{0%,100%{opacity:1;} 50%{opacity:0.3;}}"
        "</style>"
    );
}

void handleGetData() {
    // Check client connection before starting
    if (!server.client().connected()) {
        return;
    }
    
    Serial.print("[HTTP] GET /get_data, heap: ");
    Serial.println(ESP.getFreeHeap());
    
    String type = server.arg("type");
    
    // V2.MAP1: Update GPS coordinates BEFORE building header to ensure gpsValid is current
    // Throttled: Only update if enough time has passed (GPS_UPDATE_INTERVAL) to avoid blocking
    // Phone GPS age check is fast, device GPS serial read is slower
    static unsigned long lastGpsCheck = 0;
    if (millis() - lastGpsCheck > 1000) {  // Check at most once per second
        updateGpsCoordinates();
        lastGpsCheck = millis();
    }
    
    // Debug: Log GPS status periodically
    static unsigned long lastDebugLog = 0;
    if (millis() - lastDebugLog > 5000) {  // Log every 5 seconds
        lastDebugLog = millis();
        Serial.print("[DEBUG] GPS Status - Source: ");
        Serial.print((int)gpsSource);
        Serial.print(" (");
        if (gpsSource == GPS_SOURCE_DEVICE) Serial.print("Device");
        else if (gpsSource == GPS_SOURCE_PHONE) Serial.print("Phone");
        else Serial.print("Both");
        Serial.print("), Valid: ");
        Serial.print(gpsValid ? "YES" : "NO");
        Serial.print(", lastPhoneUpdate: ");
        if (lastPhoneLocationUpdate == 0) {
            Serial.println("NEVER");
        } else {
            Serial.print((millis() - lastPhoneLocationUpdate) / 1000);
            Serial.println(" seconds ago");
        }
    }
    
    // STREAMING: Send response in chunks to prevent heap fragmentation
    server.setContentLength(CONTENT_LENGTH_UNKNOWN);
    server.sendHeader("Connection", "close");
    server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
    server.sendHeader("Pragma", "no-cache");
    server.sendHeader("Expires", "0");
    server.send(200, "text/html", "");
    
    // Check connection after send
    if (!server.client().connected()) return;
    
    // Status header format:
    // Main: SD|GPS_SAT|GPS_VALID|TIME_SET|MAC_LIST|FILTER_STATE|DEAUTH_COUNT|DEAUTH_ALARM|CARDS|
    // White/Router: SD|GPS_SAT|GPS_VALID|TIME_SET|||||CARDS|
    struct tm timeinfo;
    bool timeSet = getLocalTime(&timeinfo) && (timeinfo.tm_year + 1900 >= 2024);
    
    String header = "";
    // Debug: Log SD status
    static unsigned long lastSdDebug = 0;
    if (millis() - lastSdDebug > 10000) {  // Log every 10 seconds
        lastSdDebug = millis();
        Serial.print("[DEBUG] SD Status - sdReady: ");
        Serial.print(sdReady ? "YES" : "NO");
        Serial.print(", Header will send: ");
        Serial.println(sdReady ? "1" : "0");
    }
    // SD status: ensure clean "1" or "0" without newlines
    header += String(sdReady ? "1" : "0");
    header += "|";
    if (gpsSource == GPS_SOURCE_PHONE) {
        header += "Phone";
    } else if (gpsRxTxSwapped) {
        header += "RX/TX!";
    } else if (!gpsModuleDetected && gpsAutoBaudDone) {
        header += "NoGPS";
    } else if (!gpsModuleDetected && !gpsAutoBaudDone && gpsBaudIndex > 0) {
        header += "Auto";
    } else if (!gpsModuleDetected) {
        header += "Init";
    } else {
        header += String(gps.satellites.value());
    }
    header += "|";
    // GPS status: ensure clean "1" or "0" without newlines
    header += String(gpsValid ? "1" : "0");
    header += "|";
    header += String(timeSet ? "1" : "0");
    header += "|";

    // MAC list for radar (only main view)
    if (type == "main") {
        String macs = "";
        int count = 0;
        for (auto const& pair : potentialFollowers) {
            if (!server.client().connected()) break;  // Check connection during loop
            if (!whitelist.count(pair.first)) {
                if (filterEnabled && (pair.second.isRouter || isRandomized(pair.first))) {
                    continue;
                }
                if (macs.length() > 0) macs += ",";
                macs += pair.first;
                count++;
                if (count >= 50) break;
            }
        }
        header += macs;
        header += "|";
        header += String(filterEnabled ? "1" : "0");
        header += "|";
        header += String(deauthCount);
        header += "|";
        header += String(deauthAlarmActive ? "1" : "0");
        header += "|";
    } else {
        header += "||||";  // Empty MAC_LIST, FILTER_STATE, DEAUTH_COUNT, DEAUTH_ALARM (4 pipes - line 1258 added first pipe)
    }
    
    // Send header immediately
    server.sendContent(header);
    header = "";  // Free memory
    
    // Check connection after sending header
    if (!server.client().connected()) return;

    // STREAMING: Send device cards one by one to prevent heap fragmentation
    // OPTIMIZED: Reduced limit to 50 cards for faster updates
    int cardCount = 0;
    const int MAX_CARDS = 50;  // Reduced from 100 for better performance
    
    // For whitelist and router views, also include devices that might not be in potentialFollowers yet
    // Create a set to track already shown devices to avoid duplicates
    std::set<String> shownDevices;
    
    // V2.MAP1: Update persistence scores BEFORE sorting to ensure correct order
    // OPTIMIZED: Only update if enough time has passed (reduce CPU load)
    static unsigned long lastScoreUpdate = 0;
    if (millis() - lastScoreUpdate > 5000) {  // Update scores every 5 seconds max
        updateAllPersistenceScores();
        lastScoreUpdate = millis();
    }
    
    // REMOVED: loadAllFindings() call from handleGetData() - it was causing page navigation lag
    // SD card reloading is now handled in loop() background task to avoid blocking HTTP responses
    
    // Cached sort: refresh at most every 10s to avoid re-sorting on every get_data request
    static std::vector<std::pair<String, TrackingInfo>> sortedDevices;
    static unsigned long lastSortTime = 0;
    const unsigned long SORT_CACHE_MS = 10000;
    unsigned long now = millis();
    if (sortedDevices.size() != potentialFollowers.size() || (now - lastSortTime >= SORT_CACHE_MS)) {
        sortedDevices.clear();
        sortedDevices.reserve(potentialFollowers.size());
        sortedDevices.assign(potentialFollowers.begin(), potentialFollowers.end());
        std::sort(sortedDevices.begin(), sortedDevices.end(),
            [](const std::pair<String, TrackingInfo>& a, const std::pair<String, TrackingInfo>& b) {
                int levelA = getPersistenceLevel(a.second.persistenceScore);
                int levelB = getPersistenceLevel(b.second.persistenceScore);
                if (levelA != levelB) return levelA > levelB;
                if (a.second.hitCount != b.second.hitCount) return a.second.hitCount > b.second.hitCount;
                return a.second.lastSeen > b.second.lastSeen;
            });
        lastSortTime = now;
    }
    
    // First, show devices from sorted list
    for (auto const& pair : sortedDevices) {
        if (cardCount >= MAX_CARDS) break;
        
        String id = pair.first;
        bool isW = (whitelist.count(id) > 0);
        bool isR = (pair.second.isRouter || knownRouters.count(id) > 0);
        bool show = false;

        if (type == "white") {
            show = isW;
        } else if (type == "router") {
            show = isR && !isW;  // Don't show whitelisted on router page
        } else if (type == "randomized") {
            // Show only randomized MAC addresses, but not if whitelisted
            show = isRandomized(id) && !isW;
        } else if (type == "ble") {
            // Show ONLY BLE devices - exclude WiFi explicitly
            String typeUpper = pair.second.type;
            typeUpper.toUpperCase();
            bool isBleType = (typeUpper == "BLE");
            bool isWifiType = (typeUpper == "WIFI" || typeUpper.indexOf("WIFI") >= 0);
            show = isBleType && !isWifiType && !isW && !isR;
        } else {  // main view
            // Whitelisted devices NEVER show on main page (not even in ALL mode)
            if (!isW) {
                if (filterEnabled) {
                    // FILTER ON: hide routers, randomized AND unnamed devices
                    bool isRandom = isRandomized(id);
                    bool isUnnamed = (pair.second.name.length() == 0);
                    if (isR || isRandom || isUnnamed) {
                        show = false;
                    } else {
                        show = true;
                    }
                } else {
                    show = true;  // ALL: show all including routers (except whitelisted)
                }
            }
        }

        if (show) {
            shownDevices.insert(id);
            
            String tC = (pair.second.type == "BLE") ? " ble-border" : " wifi-border";
            if (isR) tC = " router-border";
            // Whitelist devices keep their own type color (no longer blue)
            
            int rssi = constrain(pair.second.lastRSSI, -100, -40);
            int rP = map(rssi, -100, -40, 5, 100);
            int hue = map(rP, 0, 100, 120, 0);

            String displayName = pair.second.name;
            if (displayName.length() == 0) {
                // V2.4.5: Show manufacturer ONLY for BLE devices
                if (pair.second.type == "BLE") {
                    // First try manufacturer from OUI
                    displayName = getManufacturerInternal(id);
                    
                    // If no manufacturer found, try to identify from Service UUIDs
                    if (displayName.length() == 0 && pair.second.serviceUUIDs.length() > 0) {
                        String uuidUpper = pair.second.serviceUUIDs;
                        uuidUpper.toUpperCase();
                        
                        // Common BLE service UUIDs for device identification
                        if (uuidUpper.indexOf("FE95") >= 0) {
                            displayName = "Xiaomi Device";  // Xiaomi MiBeacon
                        } else if (uuidUpper.indexOf("FE9A") >= 0) {
                            displayName = "Tile Tracker";  // Tile
                        } else if (uuidUpper.indexOf("FE2C") >= 0) {
                            displayName = "Fast Pair Device";  // Google Fast Pair
                        } else if (uuidUpper.indexOf("FE9F") >= 0) {
                            displayName = "Samsung Device";  // Samsung SmartThings
                        } else if (uuidUpper.indexOf("FE6C") >= 0) {
                            displayName = "Apple Device";  // Apple iBeacon
                        } else if (uuidUpper.indexOf("FEAA") >= 0) {
                            displayName = "Eddystone Beacon";  // Google Eddystone
                        } else if (uuidUpper.indexOf("180F") >= 0 || uuidUpper.indexOf("0000180F") >= 0) {
                            displayName = "Battery Service";  // Battery Service
                        } else if (uuidUpper.indexOf("180A") >= 0 || uuidUpper.indexOf("0000180A") >= 0) {
                            displayName = "Device Info";  // Device Information Service
                        } else if (uuidUpper.indexOf("1812") >= 0 || uuidUpper.indexOf("00001812") >= 0) {
                            displayName = "Human Interface";  // HID Service
                        } else if (uuidUpper.indexOf("1811") >= 0 || uuidUpper.indexOf("00001811") >= 0) {
                            displayName = "Alert Notification";  // Alert Notification Service
                        } else if (uuidUpper.indexOf("1800") >= 0 || uuidUpper.indexOf("00001800") >= 0) {
                            displayName = "Generic Access";  // Generic Access Service
                        }
                    }
                }
                if (displayName.length() == 0) displayName = "Unnamed";
            }
            
            // Calculate time since last seen (overflow-safe)
            unsigned long secsAgo = safeTimeDiff(millis(), pair.second.lastSeen) / 1000;
            String lastSeenStr;
            if (secsAgo < 60) {
                lastSeenStr = String(secsAgo) + "s";
            } else if (secsAgo < 3600) {
                lastSeenStr = String(secsAgo / 60) + "m";
            } else if (secsAgo < 86400) {
                unsigned long hours = secsAgo / 3600;
                unsigned long mins = (secsAgo % 3600) / 60;
                lastSeenStr = String(hours) + "h " + String(mins) + "m";
            } else {
                unsigned long days = secsAgo / 86400;
                unsigned long hours = (secsAgo % 86400) / 3600;
                lastSeenStr = String(days) + "d " + String(hours) + "h";
            }
            
            // âš ï¸ FOLLOW WARNING LOGIC (encounter-based)
            // V2.MAP1: Calculate persistence level for map button
            int persistLevel = getPersistenceLevel(pair.second.persistenceScore);
            
            // Level 1 (Yellow): 2 encounters - same device in 2 different contexts
            // Level 2 (Orange): 3 encounters - following pattern emerging
            // Level 3 (Red):    4+ encounters - definite follower!
            int warningLevel = 0;
            String warningText = "";
            bool isTimeWindowWarning = false;
            
            if (type == "main") {
                unsigned long minsSinceFirst = (safeTimeDiff(millis(), pair.second.firstSeen) / 1000) / 60;
                int hits = pair.second.hitCount;
                int encounters = pair.second.encounterCount;
                int rssiRange = pair.second.maxRSSI - pair.second.minRSSI;
                
                // Calculate hit density (hits per minute)
                float hitsPerMin = (minsSinceFirst > 0) ? (float)hits / (float)minsSinceFirst : 0;
                
                // Calculate RSSI-based distance estimate
                float rssiDistance = 0.0f;
                if (pair.second.type == "BLE") {
                    rssiDistance = estimateBleDistance(pair.second.lastRSSI);
                } else if (pair.second.type == "WiFi") {
                    rssiDistance = estimateWifiDistance(pair.second.lastRSSI, pair.second.wifiChannel, pair.second.name);
                }
                
                // === TIME-WINDOW LOGIC (works WITHOUT GPS) ===
                // This is the primary warning when GPS is not in use
                // Time windows: 10 min - 2 h (over 2h = static environment)
                bool inTimeWindow = (minsSinceFirst >= 10 && minsSinceFirst <= 120);
                
                if (inTimeWindow) {
                    // Distance-based thresholds: closer devices need fewer hits, distant devices need more
                    // Close (< 20m): Easy to track, lower thresholds
                    // Medium (20-40m): Moderate tracking, medium thresholds
                    // Far (> 40m): Hard to track, higher thresholds (likely static device)
                    
                    bool isClose = (rssiDistance > 0 && rssiDistance < 20.0f);
                    bool isMedium = (rssiDistance >= 20.0f && rssiDistance <= 40.0f);
                    bool isFar = (rssiDistance > 40.0f);
                    
                    // Level 3 (Red) - STALKER: Very dense tracking OR high RSSI variation
                    // Close: hits > 25 OR (hits > 15 AND rssiRange > 20) OR encounters >= 4
                    // Medium: hits > 40 OR (hits > 30 AND rssiRange > 25) OR encounters >= 4
                    // Far: hits > 50 OR (hits > 40 AND rssiRange > 30) OR encounters >= 4
                    bool stalkerCondition = false;
                    if (isClose) {
                        stalkerCondition = (hits > 25 || (hits > 15 && rssiRange > 20) || encounters >= 4);
                    } else if (isMedium) {
                        stalkerCondition = (hits > 40 || (hits > 30 && rssiRange > 25) || encounters >= 4);
                    } else if (isFar) {
                        stalkerCondition = (hits > 50 || (hits > 40 && rssiRange > 30) || encounters >= 4);
                    } else {
                        // No distance estimate - use original logic but stricter
                        stalkerCondition = (hits > 35 || (hits > 25 && rssiRange > 25) || encounters >= 4);
                    }
                    
                    if (stalkerCondition) {
                        warningLevel = 3;
                        isTimeWindowWarning = true;
                        warningText = "STALKER! ";
                        warningText += String(hits);
                        warningText += "x/";
                        warningText += String(minsSinceFirst);
                        warningText += "m";
                    }
                    // Level 2 (Orange) - FOLLOW: Clear tracking
                    // Close: hits > 10 OR (hits > 8 AND hitsPerMin > 0.4) OR encounters >= 2
                    // Medium: hits > 20 OR (hits > 15 AND hitsPerMin > 0.5) OR (hits > 12 AND rssiRange > 20) OR encounters >= 3
                    // Far: hits > 30 OR (hits > 25 AND rssiRange > 25) OR encounters >= 3
                    else {
                        bool followCondition = false;
                        if (isClose) {
                            followCondition = (hits > 10 || (hits > 8 && hitsPerMin > 0.4) || encounters >= 2);
                        } else if (isMedium) {
                            followCondition = (hits > 20 || (hits > 15 && hitsPerMin > 0.5) || (hits > 12 && rssiRange > 20) || encounters >= 3);
                        } else if (isFar) {
                            followCondition = (hits > 30 || (hits > 25 && rssiRange > 25) || encounters >= 3);
                        } else {
                            // No distance estimate - use original logic
                            followCondition = (hits > 15 || (hits > 10 && hitsPerMin > 0.5) || encounters >= 2);
                        }
                        
                        if (followCondition) {
                            warningLevel = 2;
                            isTimeWindowWarning = true;
                            warningText = "FOLLOW? ";
                            warningText += String(hits);
                            warningText += "x/";
                            warningText += String(minsSinceFirst);
                            warningText += "m";
                        }
                        // Level 1 (Yellow) - SEEN: Possible tracking
                        // Close: hits > 6
                        // Medium: hits > 12 OR (hits > 8 AND rssiRange > 15)
                        // Far: hits > 20 OR (hits > 15 AND rssiRange > 20)
                        else {
                            bool seenCondition = false;
                            if (isClose) {
                                seenCondition = (hits > 6);
                            } else if (isMedium) {
                                seenCondition = (hits > 12 || (hits > 8 && rssiRange > 15));
                            } else if (isFar) {
                                seenCondition = (hits > 20 || (hits > 15 && rssiRange > 20));
                            } else {
                                // No distance estimate - use original logic
                                seenCondition = (hits > 8);
                            }
                            
                            if (seenCondition) {
                                warningLevel = 1;
                                isTimeWindowWarning = true;
                                warningText = "SEEN ";
                                warningText += String(hits);
                                warningText += "x/";
                                warningText += String(minsSinceFirst);
                                warningText += "m";
                            }
                        }
                    }
                }
                
                // === ENCOUNTER-BASED LOGIC (needs GPS/movement) ===
                // This ELEVATES warning level if GPS detects movement
                // Encounter = 5 min pause OR 500m movement
                if (encounters >= 4) {
                    warningLevel = 3;  // Red - confirmed follower
                    isTimeWindowWarning = false;
                    warningText = "FOLLOWER! ";
                    warningText += String(encounters);
                    warningText += "x/";
                    warningText += String(minsSinceFirst);
                    warningText += "m";
                }
                else if (encounters >= 3) {
                    if (warningLevel < 3) warningLevel = 2;  // Orange - suspicious
                    if (!isTimeWindowWarning || warningLevel == 2) {
                        isTimeWindowWarning = false;
                        warningText = "SUSPICIOUS ";
                        warningText += String(encounters);
                        warningText += "x/";
                        warningText += String(minsSinceFirst);
                        warningText += "m";
                    }
                }
                else if (encounters >= 2 && warningLevel < 1) {
                    warningLevel = 1;  // Yellow - seen again
                    isTimeWindowWarning = false;
                    warningText = "RE-SEEN ";
                    warningText += String(encounters);
                    warningText += "x/";
                    warningText += String(minsSinceFirst);
                    warningText += "m";
                }
                
                // === COMBINED WARNING ===
                // If BOTH (time-window + encounter) trigger, stronger warning
                if (isTimeWindowWarning && encounters >= 2) {
                    warningLevel = 3;  // Maximum level
                    warningText = "STALKER! ";
                    warningText += String(hits);
                    warningText += "x+";
                    warningText += String(encounters);
                    warningText += "enc";
                }
                
                // === STATIC ENVIRONMENT (over 2h) ===
                // Device visible for over 2 hours = static environment
                // Not a threat, but shown with gray "STATIC" indicator
                // If device is far (> 30m) and visible > 2h, it's definitely static
                if (minsSinceFirst > 120 && warningLevel == 0) {
                    bool isStatic = false;
                    if (rssiDistance > 30.0f) {
                        // Far device (> 30m) visible > 2h = definitely static
                        isStatic = (hits > 3);
                    } else if (rssiDistance > 0 && rssiDistance <= 30.0f) {
                        // Closer device - need more hits to be considered static
                        isStatic = (hits > 10 && rssiRange < 15);  // Low RSSI variation = stationary
                    } else {
                        // No distance estimate - use original logic
                        isStatic = (hits > 5);
                    }
                    
                    if (isStatic) {
                        warningLevel = -1;  // Special: static indicator (gray)
                        warningText = "STATIC ";
                        warningText += String(hits);
                        warningText += "x/";
                        unsigned long hoursSinceFirst = minsSinceFirst / 60;
                        warningText += String(hoursSinceFirst);
                        warningText += "h";
                    }
                }
            }
            
            // Warning colors
            String warningColor = "";
            String warningGlow = "";
            if (warningLevel == 3) {
                warningColor = "#d32f2f";  // Red
                warningGlow = "0 0 15px #d32f2f";
            } else if (warningLevel == 2) {
                warningColor = "#ff5722";  // Orange
                warningGlow = "0 0 12px #ff5722";
            } else if (warningLevel == 1) {
                warningColor = "#ffc107";  // Yellow
                warningGlow = "0 0 8px #ffc107";
            } else if (warningLevel == -1) {
                warningColor = "#607d8b";  // Gray (blue-gray)
                warningGlow = "none";      // No glow for static
            }

            // STREAMING: Build card in small buffer, send immediately
            String card = "";
            card.reserve(1024);  // Pre-allocate to reduce fragmentation
            
            // Card with warning style if needed
            if (warningLevel > 0 || warningLevel == -1) {
                card += "<div class='card";
                card += tC;
                card += "' style='border-color:";
                card += warningColor;
                if (warningLevel > 0) {
                    card += "; box-shadow:";
                    card += warningGlow;
                }
                card += ";'>";
            } else {
                card += "<div class='card";
                card += tC;
                card += "'>";
            }
            card += "<input type='checkbox' name='ids' value='";
            card += id;
            card += "' class='chk-box'>";
            
            // Warning header if applicable
            if (warningLevel > 0 || warningLevel == -1) {
                const char* icon;
                const char* animation;
                if (warningLevel == 3) {
                    icon = "&#128680;";
                    animation = "animation:blink 0.5s infinite;";
                } else if (warningLevel == 2) {
                    icon = "&#9888;";
                    animation = "animation:blink 1s infinite;";
                } else if (warningLevel == 1) {
                    icon = "&#128065;";
                    animation = "animation:blink 1.5s infinite;";
                } else {
                    icon = "&#128205;";
                    animation = "";
                }
                card += "<div style='background:";
                card += warningColor;
                card += "; color:#fff; padding:4px 8px; margin:-12px -12px 8px -12px; border-radius:8px 8px 0 0; font-weight:bold; ";
                card += animation;
                card += "'>";
                card += icon;
                card += " ";
                card += warningText;
                card += "</div>";
            }
            
            card += "<b>[";
            card += pair.second.type;
            card += "] ";
            card += displayName;
            card += "</b><br><small style='font-family:monospace; color:#aaa;'>";
            card += id;
            // Show vendor/OUI name if available (for both BLE and WiFi)
            String vendorName = getManufacturerInternal(id);
            if (vendorName.length() > 0) {
                card += " <span style='color:#ffeb3b;'>(";
                card += vendorName;
                card += ")</span>";
            }
            vendorName = "";  // Clear vendorName immediately after use
            vendorName.reserve(0);  // Release reserved memory
            card += "</small>";
            
            // RSSI bar + RSSI-based distance estimate
            float estDistMain = 0.0f;
            String estDistStrMain = "N/A";
            estDistStrMain.reserve(16);  // Pre-allocate for distance string
            if (pair.second.type == "BLE") {
                estDistMain = estimateBleDistance(pair.second.lastRSSI);
                estDistStrMain = formatDistance(estDistMain);
            } else if (pair.second.type == "WiFi") {
                estDistMain = estimateWifiDistance(pair.second.lastRSSI, pair.second.wifiChannel, pair.second.name);
                estDistStrMain = formatDistance(estDistMain);
            }

            card += "<div class='rssi-bar'><div class='rssi-fill' style='width:";
            card += String(rP);
            card += "%; background:hsl(";
            card += String(hue);
            card += ",80%,50%);'></div></div>";
            card += "<div style='font-size:0.75em; color:#ccc; margin-top:2px;'>RSSI dist: ~";
            card += estDistStrMain;
            card += "</div>";
            
            // Info grid
            card += "<div style='display:grid; grid-template-columns:1fr 1fr; gap:4px; font-size:0.75em; color:#aaa; margin-top:6px;'>";
            card += "<span>RSSI: <b style='color:#fff;'>";
            card += String(pair.second.lastRSSI);
            card += " dBm</b></span><span>Seen: <b style='color:#fff;'>";
            card += lastSeenStr;
            card += " ago</b></span><span>Dist: <b style='color:#4caf50;'>";
            card += String(pair.second.totalDist, 0);
            card += " m</b></span><span>Hits: <b style='color:#888;'>";
            card += String(pair.second.hitCount);
            card += "</b></span>";
            
            // Encounter count
            const char* encColor = (pair.second.encounterCount >= 3) ? "#ff5722" : 
                              (pair.second.encounterCount >= 2) ? "#ffc107" : "#4caf50";
            card += "<span style='grid-column:1/3;'>Encounters: <b style='color:";
            card += encColor;
            card += ";'>";
            card += String(pair.second.encounterCount);
            card += "</b> (RSSI ";
            card += String(pair.second.minRSSI);
            card += " to ";
            card += String(pair.second.maxRSSI);
            card += ")</span>";
            
            // GPS coordinates if available
            if (pair.second.lastLat != 0.0 && pair.second.lastLon != 0.0) {
                card += "<span style='grid-column:1/3;'>GPS: <b style='color:#42a5f5;'>";
                card += String(pair.second.lastLat, 5);
                card += ", ";
                card += String(pair.second.lastLon, 5);
                card += "</b></span>";
            }
            
            // BLE-specific data: Service UUIDs
            if (pair.second.serviceUUIDs.length() > 0) {
                card += "<span style='grid-column:1/3;'>UUID: <b style='color:#9c27b0;font-size:0.9em;'>";
                card += pair.second.serviceUUIDs;
                card += "</b></span>";
            }
            
            // BLE-specific data: Manufacturer ID and Data
            if (pair.second.manufacturerId > 0) {
                card += "<span style='grid-column:1/3;'>MFG: <b style='color:#ff9800;'>";
                // Common manufacturer IDs (Bluetooth SIG assigned)
                uint16_t mfgId = pair.second.manufacturerId;
                if (mfgId == 0x004C) card += "Apple";
                else if (mfgId == 0x0006) card += "Microsoft";
                else if (mfgId == 0x004E) card += "Avago";
                else if (mfgId == 0x0059) card += "Nordic";
                else if (mfgId == 0x006B) card += "Polar";
                else if (mfgId == 0x0075) card += "Samsung";
                else if (mfgId == 0x0087) card += "Garmin";
                else if (mfgId == 0x009E) card += "Bose";
                else if (mfgId == 0x009F) card += "Suunto";
                else if (mfgId == 0x00C3) card += "Adidas";
                else if (mfgId == 0x00D0) card += "Dexcom";
                else if (mfgId == 0x00D1) card += "Polar EU";
                else if (mfgId == 0x00E0) card += "Google";
                else if (mfgId == 0x0157) card += "Xiaomi";
                else if (mfgId == 0x0310) card += "Fitbit";
                else if (mfgId == 0x038F) card += "Oura";
                else {
                    char hexId[7];
                    sprintf(hexId, "0x%04X", mfgId);
                    card += hexId;
                }
                card += "</b>";
                if (pair.second.manufacturerData.length() > 4) {
                    card += " <small style='color:#666;'>";
                    card += pair.second.manufacturerData.substring(4, min(24, (int)pair.second.manufacturerData.length()));
                    card += "...</small>";
                }
                card += "</span>";
            }
            
            // V2.MAP5: Map buttons for devices with GPS data (all page types)
            if (persistLevel >= 5 && (pair.second.lastLat != 0.0 && pair.second.lastLon != 0.0)) {
                card += "<span style='grid-column:1/3; margin-top:8px; display:flex; gap:6px; flex-wrap:wrap;'>";
                // Cross-platform maps link: geo: for Android, maps: for iOS
                card += "<a onclick=\"var la=";
                card += String(pair.second.lastLat, 6);
                card += ",lo=";
                card += String(pair.second.lastLon, 6);
                card += ";if(/iPhone|iPad|iPod/i.test(navigator.userAgent)){window.location='https://maps.apple.com/?q='+la+','+lo;}else{window.location='geo:'+la+','+lo+'?q='+la+','+lo;}\" style='padding:6px 12px; background:#4caf50; color:#fff; text-decoration:none; border-radius:4px; font-size:0.8em; font-weight:bold; cursor:pointer;'>";
                card += "📍 Maps App";
                card += "</a>";
                card += "<a href='/device_map?id=";
                card += id;
                card += "' style='padding:6px 12px; background:#1565c0; color:#fff; text-decoration:none; border-radius:4px; font-size:0.8em; font-weight:bold;'>";
                card += "🗺️ Offline Map";
                card += "</a>";
                card += "</span>";
            }
            
            card += "</div></div>";
            
            // STREAM: Send card immediately, free memory
            // Check connection before sending
            if (!server.client().connected()) break;
            server.sendContent(card);
            // Clear all String objects immediately to free memory
            card = "";
            card.reserve(0);  // Release reserved memory
            estDistStrMain = "";
            estDistStrMain.reserve(0);  // Release reserved memory
            
            cardCount++;
            
            // Flush periodically and check connection
            if (cardCount % 5 == 0) {
                server.client().flush();
                if (!server.client().connected()) break;
                yield();  // Allow other tasks to run
            }
        }
    }
    
    // REMOVED: Redundant second iteration for sub-pages (white/router/randomized/ble)
    // First loop above already handles all page types and adds items to shownDevices
    // This second pass was iterating ALL devices again just to skip everything = wasted CPU

    
    // Also show devices from whitelist/knownRouters that aren't in potentialFollowers (OPTIMIZED: skip slow lookups)
        // For BLE and RANDOM pages, also check all potentialFollowers for devices that match criteria
        // even if they were removed from map (re-add them temporarily for display)
        if (type == "white" || type == "router" || type == "ble" || type == "randomized") {
            const std::set<String>* sourceList = nullptr;
            if (type == "white") {
                sourceList = &whitelist;
            } else if (type == "router") {
                sourceList = &knownRouters;
            } else if (type == "ble" || type == "randomized") {
                // For BLE and RANDOM, we need to check all devices that match criteria
                // even if they're not in potentialFollowers anymore
                // We'll handle this by checking SD card data or keeping them in a separate list
                // For now, skip this section for BLE/RANDOM as they're already handled above
                sourceList = nullptr;
            }
            
            if (sourceList != nullptr) {
            
            for (auto const& id : *sourceList) {
                if (cardCount >= MAX_CARDS) break;
                if (shownDevices.count(id) > 0) continue;  // Skip if already shown
                
                shownDevices.insert(id);
                
                // Try to get info from potentialFollowers (fast lookup)
                String displayName = "";
                String deviceType = "Unknown";
                int rssi = -100;
                double totalDist = 0.0;
                bool isDetected = false;
                int hitCount = 0;
                double lastLat = 0.0, lastLon = 0.0;
                String lastSeenStr = "N/A";
                
                auto it = potentialFollowers.find(id);
                if (it != potentialFollowers.end()) {
                    const TrackingInfo& info = it->second;
                    displayName = info.name;
                    deviceType = info.type;
                    rssi = info.lastRSSI;
                    totalDist = info.totalDist;
                    isDetected = (info.lastSeen > 0 && safeTimeDiff(millis(), info.lastSeen) < 300000);
                    hitCount = info.hitCount;
                    lastLat = info.lastLat;
                    lastLon = info.lastLon;
                    
                    unsigned long secsAgo = safeTimeDiff(millis(), info.lastSeen) / 1000;
                    if (secsAgo < 60) {
                        lastSeenStr = String(secsAgo) + "s";
                    } else if (secsAgo < 3600) {
                        lastSeenStr = String(secsAgo / 60) + "m";
                    } else if (secsAgo < 86400) {
                        unsigned long hours = secsAgo / 3600;
                        unsigned long mins = (secsAgo % 3600) / 60;
                        lastSeenStr = String(hours) + "h " + String(mins) + "m";
                    } else {
                        unsigned long days = secsAgo / 86400;
                        unsigned long hours = (secsAgo % 86400) / 3600;
                        lastSeenStr = String(days) + "d " + String(hours) + "h";
                    }
                }
                
                // Use name from potentialFollowers if available, otherwise use default (FAST - skip manufacturer lookup)
                if (displayName.length() == 0) {
                    if (type == "router") {
                        displayName = "Router";
                    } else {
                        displayName = "Whitelisted Device";
                    }
                }
                
                // Keep device type as-is - don't guess if unknown
                // Type will be set correctly when device is actually detected
                if (deviceType == "Unknown" && type == "router") {
                    deviceType = "WiFi";  // Routers are always WiFi
                }
                // Whitelist devices stay "Unknown" until detected
                
                // Whitelist shows device's own type color
                String tC;
                if (type == "white") {
                    if (deviceType == "BLE") tC = " ble-border";
                    else if (deviceType == "WiFi") tC = " wifi-border";
                    else tC = " white-border";  // Unknown type = blue (whitelist color)
                } else {
                    tC = " router-border";
                }
                
                // STREAMING: Build and send card immediately
                String card = "";
                card.reserve(768);
                card += "<div class='card";
                card += tC;
                card += "'><input type='checkbox' name='ids' value='";
                card += id;
                card += "' class='chk-box' onclick='up=false;'><b>[";
                card += deviceType;
                card += "] ";
                card += displayName;
                card += "</b><br><small style='font-family:monospace; color:#aaa;'>";
                card += id;
                card += "</small>";
                
                // V2.4.5: Calculate estimated distance based on device type
                float estimatedDist2 = 0.0f;
                String distStr2 = "N/A";
                if (deviceType == "BLE") {
                    estimatedDist2 = estimateBleDistance(rssi);
                    distStr2 = formatDistance(estimatedDist2);
                } else if (deviceType == "WiFi") {
                    // Get WiFi channel from potentialFollowers if available
                    int wifiCh = 0;
                    String wifiName = "";
                    auto it = potentialFollowers.find(id);
                    if (it != potentialFollowers.end()) {
                        wifiCh = it->second.wifiChannel;
                        wifiName = it->second.name;
                    }
                    estimatedDist2 = estimateWifiDistance(rssi, wifiCh, wifiName);
                    distStr2 = formatDistance(estimatedDist2);
                }
                
                card += "<div style='display:grid; grid-template-columns:1fr 1fr; gap:4px; font-size:0.75em; color:#aaa; margin-top:6px;'>";
                card += "<span>RSSI: <b style='color:#fff;'>";
                card += String(rssi);
                card += " dBm</b></span><span>Est. Dist: <b style='color:#ff9800;'>";
                card += distStr2;
                card += "</b></span><span>Seen: <b style='color:#fff;'>";
                card += lastSeenStr;
                card += " ago</b></span><span>Tracked: <b style='color:#4caf50;'>";
                card += String(totalDist, 0);
                card += " m</b></span><span>Hits: <b style='color:#ff9800;'>";
                card += String(hitCount);
                card += "</b></span>";
                
                if (!isDetected) {
                    card += "<span style='grid-column:1/3; color:#888;'>Status: <b>Loaded from SD</b></span>";
                } else {
                    card += "<span style='grid-column:1/3; color:#4caf50;'>Status: <b>Recently detected</b></span>";
                }
                
                if (lastLat != 0.0 && lastLon != 0.0) {
                    card += "<span style='grid-column:1/3;'>GPS: <b style='color:#42a5f5;'>";
                    card += String(lastLat, 5);
                    card += ", ";
                    card += String(lastLon, 5);
                    card += "</b></span>";
                    card += "<span style='grid-column:1/3; margin-top:8px; display:flex; gap:6px; flex-wrap:wrap;'>";
                    card += "<a onclick=\"var la=";
                    card += String(lastLat, 6);
                    card += ",lo=";
                    card += String(lastLon, 6);
                    card += ";if(/iPhone|iPad|iPod/i.test(navigator.userAgent)){window.location='https://maps.apple.com/?q='+la+','+lo;}else{window.location='geo:'+la+','+lo+'?q='+la+','+lo;}\" style='padding:6px 12px; background:#4caf50; color:#fff; text-decoration:none; border-radius:4px; font-size:0.8em; font-weight:bold; cursor:pointer;'>";
                    card += "📍 Maps App";
                    card += "</a>";
                    card += "<a href='/device_map?id=";
                    card += id;
                    card += "' style='padding:6px 12px; background:#1565c0; color:#fff; text-decoration:none; border-radius:4px; font-size:0.8em; font-weight:bold;'>";
                    card += "🗺️ Offline Map";
                    card += "</a>";
                    card += "</span>";
                }
                card += "</div></div>";
                
                // STREAM: Send card immediately, free memory
                // Check connection before sending
                if (!server.client().connected()) break;
                server.sendContent(card);
                // Clear all String objects immediately to free memory
                card = "";
                card.reserve(0);  // Release reserved memory
                distStr2 = "";
                distStr2.reserve(0);  // Release reserved memory
                
                cardCount++;
                
                // Flush periodically
                if (cardCount % 5 == 0) {
                    server.client().flush();
                    if (!server.client().connected()) break;
                    yield();
                }
            }
        }
    }
    
    // STREAMING: Send end marker and close
    if (server.client().connected()) {
        server.sendContent("|");
        server.sendContent("");  // End chunked transfer
        server.client().flush();
        server.client().stop();
    }
    
    Serial.print("[HTTP] Sent ");
    Serial.print(cardCount);
    Serial.print(" cards, heap: ");
    Serial.println(ESP.getFreeHeap());
}

void handleRoot() {
    String uri = server.uri();
    Serial.print("[HTTP] GET ");
    Serial.println(uri);
    
    String type;
    if (uri == "/router_page" || uri.startsWith("/router_page")) {
        type = F("router");
    } else if (uri == "/whitelist_page" || uri.startsWith("/whitelist_page")) {
        type = F("white");
    } else if (uri == "/randomized_page" || uri.startsWith("/randomized_page")) {
        type = F("randomized");
    } else if (uri == "/ble_page" || uri.startsWith("/ble_page")) {
        type = F("ble");
    } else {
        type = F("main");
    }
    
    // Check client connection before building HTML
    if (!server.client().connected()) {
        return;
    }
    
    // CHUNKED STREAMING: Send HTML in small pieces to avoid 25KB+ heap allocation
    server.sendHeader("Connection", "close");
    server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
    server.sendHeader("Pragma", "no-cache");
    server.sendHeader("Expires", "0");
    server.setContentLength(CONTENT_LENGTH_UNKNOWN);
    server.send(200, "text/html", "");
    
    // Chunk 1: HTML head + CSS (sent from flash, minimal heap)
    server.sendContent(F("<!DOCTYPE html><html><head><meta charset='UTF-8'>"));
    server.sendContent(F("<meta name='viewport' content='width=device-width, initial-scale=1'>"));
    server.sendContent(F("<meta http-equiv='Cache-Control' content='no-cache, no-store, must-revalidate'>"));
    server.sendContent(F("<meta http-equiv='Pragma' content='no-cache'>"));
    server.sendContent(F("<meta http-equiv='Expires' content='0'>"));
    server.sendContent(F("<meta name='mobile-web-app-capable' content='yes'>"));
    server.sendContent(F("<meta name='apple-mobile-web-app-capable' content='yes'>"));
    server.sendContent(F("<meta name='apple-mobile-web-app-status-bar-style' content='black-translucent'>"));
    server.sendContent(F("<meta name='theme-color' content='#000000'>"));
    server.sendContent(F("<meta name='apple-mobile-web-app-title' content='AFOSCA'>"));
    server.sendContent(getStyles());
    server.sendContent(F("</head><body>"));
    if (!server.client().connected()) return;
    
    // Chunk 2: Header bar (use small buffer, ~4KB max)
    String html = "";
    html.reserve(4096);
    const char* pageTitle = (type == "white") ? "WHITELIST" : 
                            (type == "router") ? "ROUTERS" :
                            (type == "randomized") ? "RANDOM" :
                            (type == "ble") ? "BLUETOOTH" : "";
    html += "<div class='top-bar'><div class='header-title' style='display:flex; flex-direction:column; align-items:flex-start;'>";
    html += "<div style='font-size:1.5em; line-height:1.2;'>AFOSCA</div>";
    html += "<div style='font-size:0.6em; color:#888; margin-top:2px;'>V2.MAP5";
    if (pageTitle && strlen(pageTitle) > 0) {
        html += " - ";
        html += pageTitle;
    }
    html += "</div></div>";
    
    // Status and settings only on main page
    if (type == "main") {
        html += F("<div class='status-group'>");
        
        html += F("<div class='status-icons' style='display:flex; flex-direction:column; gap:4px; align-items:center; flex-shrink:0;'>");
        html += sdReady ? F("<span id='sd-icon' class='sd-text sd-ok'>SD</span>") : F("<span id='sd-icon' class='sd-text'>SD</span>");
        
        html += F("<div style='display:flex; flex-direction:column; align-items:center; gap:2px;'>");
        html += F("<span id='gps-icon' class='stat-icon'>&#128752;<small id='sat-count'>0</small></span>");
        html += F("<small id='gps-debug' style='font-size:0.65em;color:#666;display:block;text-align:center;max-width:100px;'>Waiting...</small>");
        html += F("</div>");
        
        html += F("<button id='gpsLockBtn' onclick='toggleGpsLock()' class='nav-btn' style='padding:6px; font-size:1em; background:#333; border:1px solid #555; border-radius:4px; min-width:32px; min-height:32px; width:32px; height:32px; display:flex; align-items:center; justify-content:center;' title='Lock settings'>");
        html += F("<span id='gpsLockIcon'>");
        html += gpsSourceLocked ? F("🔒") : F("🔓");
        html += F("</span></button>");
        html += F("<span id='deauth-icon' class='deauth-icon' title='Deauther Detection'>&#9888;<small id='deauth-count'>0</small></span>");
        html += F("</div>");
        
        html += F("<div class='settings-group'>");
        html += F("<button id='timeBtn' onclick='showTimeDialog()' class='nav-btn' style='padding:6px 10px; font-size:0.7em; background:#333; border:1px solid #555; border-radius:4px; min-width:50px; min-height:32px; width:100%;'>TIME</button>");
        html += F("<button id='shutdownBtn' onclick='requestSafeShutdown()' class='nav-btn' style='padding:6px 10px; font-size:0.7em; background:#");
        html += safeShutdownReady ? F("4caf50") : F("f44336");
        html += F("; border:1px solid #");
        html += safeShutdownReady ? F("2e7d32") : F("b71c1c");
        html += F("; border-radius:4px; min-width:50px; min-height:32px; width:100%;'>");
        html += safeShutdownReady ? F("✓ SAFE") : F("SHUTDOWN");
        html += F("</button>");
        html += F("<span id='shutdownStatus' style='font-size:0.6em; color:#");
        html += safeShutdownReady ? F("4caf50") : (safeShutdownRequested ? F("ff9800") : F("666"));
        html += F("; text-align:center; display:block; margin-top:2px;'>");
        if (safeShutdownReady) {
            html += F("✓ Safe to power off");
        } else if (safeShutdownRequested) {
            html += F("Waiting...");
        }
        html += F("</span>");
        
        html += F("<select id='window3Select' onchange='setWindow3()' style='padding:6px 10px; font-size:0.7em; background:#333; color:#eee; border:1px solid #555; border-radius:4px; min-width:50px; min-height:32px; width:100%;'");
        if (gpsSourceLocked) html += F(" disabled");
        html += F(">");
        html += F("<option value='1800000'");
        if (TIME_WINDOW_3_MS == TIME_WINDOW_3_DEFAULT) html += F(" selected");
        html += F(">30min</option>");
        html += F("<option value='3600000'");
        if (TIME_WINDOW_3_MS == TIME_WINDOW_3_1H) html += F(" selected");
        html += F(">1h</option>");
        html += F("<option value='7200000'");
        if (TIME_WINDOW_3_MS == TIME_WINDOW_3_2H) html += F(" selected");
        html += F(">2h</option>");
        html += F("<option value='14400000'");
        if (TIME_WINDOW_3_MS == TIME_WINDOW_3_4H) html += F(" selected");
        html += F(">4h</option>");
        html += F("<option value='28800000'");
        if (TIME_WINDOW_3_MS == TIME_WINDOW_3_8H) html += F(" selected");
        html += F(">8h</option>");
        html += F("<option value='43200000'");
        if (TIME_WINDOW_3_MS == TIME_WINDOW_3_12H) html += F(" selected");
        html += F(">12h</option>");
        html += F("<option value='86400000'");
        if (TIME_WINDOW_3_MS == TIME_WINDOW_3_24H) html += F(" selected");
        html += F(">24h</option>");
        html += F("</select>");
        
        html += F("<select id='gpsSourceSelect' onchange='setGpsSource()' style='padding:6px 10px; font-size:0.7em; background:#333; color:#eee; border:1px solid #555; border-radius:4px; min-width:50px; min-height:32px; width:100%;'");
        if (gpsSourceLocked) html += F(" disabled");
        html += F(">");
        html += F("<option value='0'");
        if (gpsSource == GPS_SOURCE_DEVICE) html += F(" selected");
        html += F(">Device</option>");
        html += F("<option value='1'");
        if (gpsSource == GPS_SOURCE_PHONE) html += F(" selected");
        html += F(">Phone</option>");
        html += F("<option value='2'");
        if (gpsSource == GPS_SOURCE_BOTH) html += F(" selected");
        html += F(">Both</option>");
        html += F("</select>");
        html += F("</div>");

        html += F("</div>");  // Close status-group
        html += F("</div>");  // Close top-bar
    } else {
        html += F("<div class='status-group' style='min-width:1px;'></div>");
        html += F("</div>");  // Close top-bar
    }
    
    // Flush chunk 2 (header + status bar)
    server.sendContent(html);
    html = "";
    if (!server.client().connected()) return;
    
    html += F("<div class='nav'>");
    if (type != "main") {
        html += F("<a href='/' class='nav-btn'>BACK</a>");
    } else {
        html += F("<a href='/whitelist_page' class='nav-btn' style='background:#42a5f5;border-color:#1976d2;'>WHITE</a>");
        html += F("<a href='/router_page' class='nav-btn' style='background:#4caf50;border-color:#2e7d32;'>ROUTERS</a>");
        html += F("<a href='/ble_page' class='nav-btn' style='background:#00bcd4;border-color:#006064;'>BLE</a>");
        html += F("<a href='/randomized_page' class='nav-btn' style='background:#9c27b0;border-color:#6a1b9a;'>RANDOM</a>");
        html += F("<button id='filterBtn' onclick='toggleFilter()' class='nav-btn ");
        html += filterEnabled ? F("btn-active") : F("");
        html += F("'>");
        html += filterEnabled ? F("FILTER") : F("ALL");
        html += F("</button>");
    }
    html += F("</div>");
    
    // Time dialog only on main page
    if (type == "main") {
        html += F("<div id='timeDialogOverlay' onclick='hideTimeDialog()' style='display:none; position:fixed; top:0; left:0; width:100%; height:100%; background:rgba(0,0,0,0.7); z-index:999;'></div>");
        html += F("<div id='timeDialog' style='display:none; position:fixed; top:50%; left:50%; transform:translate(-50%,-50%); background:#1a1a1a; padding:20px; border-radius:10px; border:2px solid #4caf50; z-index:1000; box-shadow:0 4px 20px rgba(0,0,0,0.5); min-width:280px;'>");
        html += F("<h3 style='margin-top:0; color:#4caf50;'>Set Date & Time</h3>");
        html += F("<input type='datetime-local' id='datetimeInput' style='padding:8px; width:100%; max-width:250px; background:#222; color:#eee; border:1px solid #444; border-radius:5px; font-size:14px; margin:10px 0;'>");
        html += F("<div style='margin-top:15px; display:flex; gap:10px;'>");
        html += F("<button onclick='setTime()' class='nav-btn btn-active' style='flex:1;'>SET</button>");
        html += F("<button onclick='hideTimeDialog()' class='nav-btn' style='flex:1; background:#666;'>CANCEL</button>");
        html += F("</div>");
        html += F("<div id='timeStatus' style='margin-top:10px; font-size:0.8em; color:#4caf50; text-align:center;'></div>");
        html += F("</div>");
    }
    
    if (type == "main") {
        html += F("<div class='radar' id='rdr'>");
        html += F("<div class='r-circle' style='width:90px;height:90px;'></div>");
        html += F("<div class='r-circle' style='width:45px;height:45px;'></div>");
        html += F("<div class='r-cross-v'></div><div class='r-cross-h'></div>");
        html += F("<div class='sweep'></div></div>");
    }

    String action = (type == "router") ? "/rem_router" : 
                    (type == "white") ? "/rem_white" : 
                    (type == "ble") ? "/add_multi_white" :
                    (type == "randomized") ? "/add_multi_white" : "/add_multi_white";
    html += "<form id='devForm' action='";
    html += action;
    html += "' method='POST'>";
    html += F("<div id='container'></div><div class='nav' style='margin-top:10px;'>");
    
    if (type == "main") {
        html += F("<button type='button' onclick='submitTo(\"/add_multi_white\")' class='nav-btn btn-active'>+ WHITE</button>");
        html += F("<button type='button' onclick='submitTo(\"/add_multi_router\")' class='nav-btn' style='background:#6a1b9a;border-color:#9c27b0;'>+ ROUTER</button>");
    } else if (type == "randomized" || type == "ble") {
        html += F("<button type='button' onclick='submitTo(\"/add_multi_white\")' class='nav-btn btn-active'>+ WHITE</button>");
        html += F("<button type='button' onclick='submitTo(\"/add_multi_router\")' class='nav-btn' style='background:#6a1b9a;border-color:#9c27b0;'>+ ROUTER</button>");
    } else if (type == "router") {
        html += F("<button type='button' onclick='submitTo(\"/add_multi_white\")' class='nav-btn btn-active'>+ WHITE</button>");
        html += F("<button type='submit' class='nav-btn' style='background:#b71c1c; border:none;'>REMOVE</button>");
    } else {
        html += F("<button type='submit' class='nav-btn' style='background:#b71c1c; border:none;'>REMOVE SELECTED</button>");
    }
    html += F("</div></form>");
    
    // Flush chunk 3 (nav + dialog + form)
    server.sendContent(html);
    html = "";
    if (!server.client().connected()) return;
    
    // Chunk 4: JavaScript (reuse html buffer)
    html += F("<script>let up=true; let kM=[];");
    html += F("function shoot(){ let r=document.getElementById('rdr'); if(!r)return; let b=document.createElement('div'); b.className='blip'; b.style.left=(Math.random()*70+15)+'%'; b.style.top=(Math.random()*70+15)+'%'; r.appendChild(b); setTimeout(()=>b.remove(),6000); }");
    html += F("function submitTo(u){ let f=document.getElementById('devForm'); f.action=u; f.submit(); }");
    html += F("async function toggleFilter(){ let btn=document.getElementById('filterBtn'); if(!btn||btn.disabled)return; btn.disabled=true; try{ let res=await fetch('/toggle_filter'); let data=await res.json(); let isFilter=data.filter; btn.className=isFilter?'nav-btn btn-active':'nav-btn'; btn.innerText=isFilter?'FILTER':'ALL'; up=true; setTimeout(()=>update(),100); }catch(e){} setTimeout(()=>btn.disabled=false,300); }");
    // GPS and TIME functions only on main page
    if (type == "main") {
        html += F("function showTimeDialog(){ let d=document.getElementById('timeDialog'); let o=document.getElementById('timeDialogOverlay'); if(!d||!o)return; let now=new Date(); let year=now.getFullYear(); let month=String(now.getMonth()+1).padStart(2,'0'); let day=String(now.getDate()).padStart(2,'0'); let hours=String(now.getHours()).padStart(2,'0'); let minutes=String(now.getMinutes()).padStart(2,'0'); let datetimeString=year+'-'+month+'-'+day+'T'+hours+':'+minutes; document.getElementById('datetimeInput').value=datetimeString; o.style.display='block'; d.style.display='block'; }");
        html += F("function hideTimeDialog(){ let d=document.getElementById('timeDialog'); let o=document.getElementById('timeDialogOverlay'); if(d)d.style.display='none'; if(o)o.style.display='none'; let s=document.getElementById('timeStatus'); if(s)s.innerText=''; }");
        html += F("async function setTime(){ let input=document.getElementById('datetimeInput'); if(!input||!input.value){ document.getElementById('timeStatus').innerText='Please select date and time'; return; } let datetime=new Date(input.value+'Z'); if(isNaN(datetime.getTime())){ document.getElementById('timeStatus').innerText='Invalid date/time'; return; } let timestamp=Math.floor(datetime.getTime()/1000); document.getElementById('timeStatus').innerText='Getting location...'; try{ let position=await new Promise((resolve,reject)=>{ if(!navigator.geolocation){ reject(new Error('Geolocation not supported')); return; } navigator.geolocation.getCurrentPosition(resolve,reject,{timeout:5000,maximumAge:60000,enableHighAccuracy:true}); }); let lat=position.coords.latitude; let lon=position.coords.longitude; document.getElementById('timeStatus').innerText='Setting time and location...'; let res=await fetch('/set_time?timestamp='+timestamp+'&lat='+lat+'&lon='+lon); let data=await res.json(); if(data.success){ document.getElementById('timeStatus').innerText='Time and location set successfully!'; setTimeout(()=>hideTimeDialog(),2000); }else{ document.getElementById('timeStatus').innerText='Failed: '+data.error; } }catch(e){ if(e.message&&e.message.includes('Geolocation')){ document.getElementById('timeStatus').innerText='Location not available, setting time only...'; try{ let res=await fetch('/set_time?timestamp='+timestamp); let data=await res.json(); if(data.success){ document.getElementById('timeStatus').innerText='Time set (no location)'; setTimeout(()=>hideTimeDialog(),2000); }else{ document.getElementById('timeStatus').innerText='Failed: '+data.error; } }catch(e2){ document.getElementById('timeStatus').innerText='Error: '+e2.message; } }else{ document.getElementById('timeStatus').innerText='Error: '+e.message; } } }");
        html += F("async function setWindow3(){ let sel=document.getElementById('window3Select'); if(!sel||gpsLocked)return; let val=sel.value; try{ let res=await fetch('/set_window3?ms='+val); let data=await res.json(); if(data.success){ console.log('Window3 set to '+val+'ms'); }else{ console.log('Failed to set window3'); sel.value=window3Value; } }catch(e){ console.log('Error setting window3: '+e.message); sel.value=window3Value; } }");
        html += F("async function requestSafeShutdown(){ let btn=document.getElementById('shutdownBtn'); let status=document.getElementById('shutdownStatus'); if(!btn||!status)return; btn.disabled=true; btn.innerText='Waiting...'; status.innerText='Stopping SD writes...'; status.style.color='#ff9800'; try{ let res=await fetch('/safe_shutdown',{method:'POST'}); let data=await res.json(); if(data.success){ if(data.ready){ btn.style.background='#4caf50'; btn.style.borderColor='#2e7d32'; btn.innerText='✓ SAFE'; status.innerText='✓ Safe to power off'; status.style.color='#4caf50'; }else{ status.innerText='Waiting for SD operations...'; setTimeout(function(){ location.reload(); },2000); } }else{ status.innerText='Error'; status.style.color='#f44336'; btn.disabled=false; } }catch(e){ status.innerText='Error: '+e.message; status.style.color='#f44336'; btn.disabled=false; } }");
        html += F("async function autoSetTime(){ let now=new Date(); let timestamp=Math.floor(now.getTime()/1000); console.log('Auto-setting time and location from browser...'); try{ let position=await new Promise((resolve,reject)=>{ if(!navigator.geolocation){ reject(new Error('Geolocation not supported')); return; } navigator.geolocation.getCurrentPosition(resolve,reject,{timeout:5000,maximumAge:60000,enableHighAccuracy:true}); }); let lat=position.coords.latitude; let lon=position.coords.longitude; console.log('Got location: '+lat+','+lon); let res=await fetch('/set_time?timestamp='+timestamp+'&lat='+lat+'&lon='+lon); let data=await res.json(); if(data.success){ console.log('Time and location auto-set successfully!'); }else{ console.log('Auto-set failed, showing dialog'); showTimeDialog(); } }catch(e){ console.log('Location error, trying time only...'); try{ let res=await fetch('/set_time?timestamp='+timestamp); let data=await res.json(); if(data.success){ console.log('Time auto-set (no location)'); }else{ console.log('Auto-set failed, showing dialog'); showTimeDialog(); } }catch(e2){ console.log('Auto-set error, showing dialog'); showTimeDialog(); } } }");
        html += F("let gpsLocked=");
        html += gpsSourceLocked ? F("true") : F("false");
        html += F("; let gpsSource=");
        html += String((int)gpsSource);
        html += F("; let window3Value='");
        html += String(TIME_WINDOW_3_MS);
        html += F("'; async function setGpsSource(){ let sel=document.getElementById('gpsSourceSelect'); if(!sel||gpsLocked)return; let val=sel.value; try{ let res=await fetch('/set_gps_source?source='+val); let data=await res.json(); if(data.success){ gpsSource=parseInt(val); console.log('GPS source set to '+val); }else{ console.log('Failed to set GPS source'); sel.value=gpsSource; } }catch(e){ console.log('Error setting GPS source: '+e.message); sel.value=gpsSource; } }");
        html += F("async function toggleGpsLock(){ gpsLocked=!gpsLocked; let gpsSelect=document.getElementById('gpsSourceSelect'); let window3Select=document.getElementById('window3Select'); let icon=document.getElementById('gpsLockIcon'); if(!gpsSelect||!window3Select||!icon)return; if(gpsLocked){ gpsSelect.disabled=true; window3Select.disabled=true; icon.innerText='🔒'; }else{ gpsSelect.disabled=false; window3Select.disabled=false; icon.innerText='🔓'; } try{ let res=await fetch('/set_gps_lock?locked='+(gpsLocked?1:0)); let data=await res.json(); if(data.success){ console.log('Settings lock set to '+gpsLocked); }else{ console.log('Failed to set lock'); } }catch(e){ console.log('Error setting lock: '+e.message); } }");
        html += F("let gpsRetryCount=0; const MAX_GPS_RETRIES=3; let gpsRequestInProgress=false; let gpsLocationSent=false; async function updateLocationFromPhone(){ if(gpsRequestInProgress)return; if(gpsSource!==1&&gpsSource!==2){let debug=document.getElementById('gps-debug');if(debug){let satEl=document.getElementById('sat-count');let satTxt=satEl?satEl.innerText:'';if(satTxt==='RX/TX!'){debug.innerText='RX/TX swapped!';debug.style.color='#f44336';}else if(satTxt==='NoGPS'){debug.innerText='No GPS module';debug.style.color='#ff9800';}else if(satTxt==='Init'){debug.innerText='GPS init...';debug.style.color='#2196f3';}else if(satTxt==='Auto'){debug.innerText='Auto-baud...';debug.style.color='#2196f3';}else{debug.innerText='Device GPS';debug.style.color='#4caf50';}}return;} let debug=document.getElementById('gps-debug'); function setDebug(msg,color){ if(debug){ debug.innerText=msg; debug.style.color=color||'#666'; } } if(!navigator.geolocation){ setDebug('Not supported','#ff9800'); return; } gpsRequestInProgress=true; try{ if(!gpsLocationSent){setDebug('Requesting...','#666');} let position=await new Promise((resolve,reject)=>{ let timeoutId=setTimeout(()=>reject(new Error('Timeout')),15000); navigator.geolocation.getCurrentPosition((pos)=>{ clearTimeout(timeoutId); resolve(pos); },(err)=>{ clearTimeout(timeoutId); reject(err); },{timeout:15000,maximumAge:3600000,enableHighAccuracy:false}); }); let lat=position.coords.latitude; let lon=position.coords.longitude; let res=await fetch('/update_location?lat='+lat+'&lon='+lon); if(!res.ok){ throw new Error('Server error: '+res.status); } let data=await res.json(); if(data.success){ gpsLocationSent=true; gpsRetryCount=0; setDebug('OK','#4caf50'); }else{ setDebug('Error: '+data.error,'#ff9800'); } gpsRequestInProgress=false; }catch(e){ let msg=e.message||String(e); gpsRequestInProgress=false; if(msg.includes('secure')||msg.includes('HTTPS')||msg.includes('insecure')){ setDebug('HTTP blocked - Try Firefox','#ff9800'); }else if(msg.includes('Timeout')||msg.includes('timeout')||e.code===3){ gpsRetryCount++; if(gpsRetryCount<MAX_GPS_RETRIES){ setDebug('Retry '+gpsRetryCount+'/'+MAX_GPS_RETRIES,'#ff9800'); setTimeout(()=>updateLocationFromPhone(),10000); }else{ setDebug('No signal - open Maps first','#ff9800'); gpsRetryCount=0; setTimeout(()=>updateLocationFromPhone(),60000); } }else if(msg.includes('denied')||msg.includes('Permission')||e.code===1){ setDebug('Permission denied','#ff9800'); }else if(e.code===2){ setDebug('Position unavailable','#ff9800'); }else{ setDebug('Error: '+msg.substring(0,20),'#ff9800'); } } }");
        html += F("setInterval(updateLocationFromPhone,15000);");
    html += F("setTimeout(()=>{ console.log('Calling updateLocationFromPhone on page load, gpsSource='+gpsSource); if(gpsSource===1||gpsSource===2){ updateLocationFromPhone().catch(e=>{ console.error('GPS init error:',e); }); }else{ console.log('GPS source is Device, checking status'); let debug=document.getElementById('gps-debug'); if(debug){let satEl=document.getElementById('sat-count');let satTxt=satEl?satEl.innerText:'';if(satTxt==='RX/TX!'){debug.innerText='RX/TX swapped!';debug.style.color='#f44336';}else if(satTxt==='NoGPS'){debug.innerText='No GPS module';debug.style.color='#ff9800';}else if(satTxt==='Auto'){debug.innerText='Auto-baud...';debug.style.color='#2196f3';}else{debug.innerText='Device GPS';debug.style.color='#4caf50';}} } },1000);");
    }
    
    // Flush chunk 4 (main-page JS functions)
    server.sendContent(html);
    html = "";
    if (!server.client().connected()) return;
    
    // Chunk 5: Shared update() JS function (reuse html buffer)
    html += "let isScrolling=false; let scrollTimeout=null; let lastScrollTop=0; ";
    html += "window.addEventListener('scroll',function(){ isScrolling=true; if(scrollTimeout)clearTimeout(scrollTimeout); scrollTimeout=setTimeout(function(){ isScrolling=false; },150); },{passive:true}); ";
    html += "let lastContainerHTML=''; let updatePending=false; ";
    html += "async function update(){ if(updatePending)return; updatePending=true; try{ ";
    html += "let fetchPromise=fetch('/get_data?type=";
    html += type;
    html += "'); let timeoutPromise=new Promise((_,r)=>setTimeout(()=>r(new Error('timeout')),5000)); ";
    html += "let res=await Promise.race([fetchPromise,timeoutPromise]); if(!res||!res.ok){console.log('Fetch failed:',res?res.status:'no response');updatePending=false;return;} let txt=await res.text(); if(!txt||txt.length<5){console.log('Empty response');updatePending=false;return;} let p=txt.split('|'); ";
    html += "if(p.length<6){console.log('Header too short:',p.length,'parts:',p);updatePending=false;return;} ";
    html += "try{ let sdEl=document.getElementById('sd-icon'); if(sdEl){ let sdVal=(p[0]||'').trim(); let sdOk=sdVal==='1'||sdVal==='1\\r'||sdVal==='1\\n'; sdEl.className='sd-text '+(sdOk?'sd-ok':\"\"); if(window.lastSdStatus!==sdOk){console.log('SD status:',sdOk?'OK':'FAIL','value=['+sdVal+']');window.lastSdStatus=sdOk;} } }catch(e){console.error('SD update error:',e);} ";
    html += "try{ let satEl=document.getElementById('sat-count'); if(satEl){ let satText=(p[1]||'0').trim(); satEl.innerText=satText; if(satText==='RX/TX!'){satEl.style.color='#f44336';}else if(satText==='NoGPS'){satEl.style.color='#ff9800';}else if(satText==='Init'||satText==='Auto'){satEl.style.color='#2196f3';}else{satEl.style.color='';} } }catch(e){console.error('Sat update error:',e);} ";
    html += "try{ let gpsEl=document.getElementById('gps-icon'); if(gpsEl){ let gpsVal=(p[2]||'').trim(); let gpsOk=gpsVal==='1'||gpsVal==='1\\r'||gpsVal==='1\\n'; gpsEl.className='stat-icon '+(gpsOk?'icon-ok':'icon-invalid'); if(window.lastGpsStatus!==gpsOk){console.log('GPS status changed:',gpsOk?'OK':'INVALID','p[2]=['+gpsVal+']');window.lastGpsStatus=gpsOk;} } let gpsDebug=document.getElementById('gps-debug'); if(gpsDebug){ let gpsVal=(p[2]||'').trim(); let gpsOk=gpsVal==='1'||gpsVal==='1\\r'||gpsVal==='1\\n'; if(gpsSource===0){let satTxt=(p[1]||'').trim();if(satTxt==='RX/TX!'){gpsDebug.innerText='RX/TX swapped!';gpsDebug.style.color='#f44336';}else if(satTxt==='NoGPS'){gpsDebug.innerText='No GPS module';gpsDebug.style.color='#ff9800';}else if(satTxt==='Init'){gpsDebug.innerText='GPS init...';gpsDebug.style.color='#2196f3';}else if(satTxt==='Auto'){gpsDebug.innerText='Auto-baud...';gpsDebug.style.color='#2196f3';}else if(gpsOk){gpsDebug.innerText='OK';gpsDebug.style.color='#4caf50';}else{gpsDebug.innerText='No fix';gpsDebug.style.color='#666';}}else{if(gpsOk&&gpsDebug.innerText!=='OK'){gpsDebug.innerText='OK';gpsDebug.style.color='#4caf50';}else if(!gpsOk&&gpsDebug.innerText==='OK'){gpsDebug.innerText='Waiting...';gpsDebug.style.color='#666';}} } }catch(e){console.error('GPS icon update error:',e);}";
    html += "if(p[3]==='0'&&!window.timeAutoSet&&typeof autoSetTime==='function'){ window.timeAutoSet=true; setTimeout(()=>autoSetTime(),500); }";
    
    // Flush chunk 5a (update function header)
    server.sendContent(html);
    html = "";
    if (!server.client().connected()) return;
    
    // Chunk 5b: Page-specific update logic
    if (type == "main") {
        html += "if(p[4]&&p[4].length>0){ p[4].split(',').forEach(m => { if(m && m.length>5 && !kM.includes(m)){ shoot(); kM.push(m); } }); }";
        html += "if(p[5]!==undefined){ let filterState=p[5]==='1'; let btn=document.getElementById('filterBtn'); if(btn){ btn.className=filterState?'nav-btn btn-active':'nav-btn'; btn.innerText=filterState?'FILTER':'ALL'; } }";
        html += "let dc=parseInt(p[6])||0; document.getElementById('deauth-count').innerText=dc;";
        html += "let di=document.getElementById('deauth-icon'); let wasAlarm=window.lastDeauthAlarm||false; let isAlarm=p[7]==='1';";
        html += "if(dc>0){ di.className='deauth-icon deauth-visible '+(isAlarm?'deauth-alarm':'deauth-warning');";
        html += "if(isAlarm && !wasAlarm && 'Notification' in window && Notification.permission==='granted'){";
        html += "new Notification('\\u26a0\\ufe0f DEAUTH ATTACK DETECTED!',{body:'Count: '+dc+', Check device immediately!',icon:'data:image/svg+xml,<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 100 100\"><circle cx=\"50\" cy=\"50\" r=\"40\" fill=\"red\"/><text x=\"50\" y=\"60\" font-size=\"40\" fill=\"white\" text-anchor=\"middle\">\\u26a0</text></svg>',tag:'deauth-alarm',requireInteraction:true});";
        html += "}";
        html += "window.lastDeauthAlarm=isAlarm;";
        html += "}else{ di.className='deauth-icon'; window.lastDeauthAlarm=false; }";
        html += "try{ let container=document.getElementById('container'); if(container){ let newHTML=p[8]||\"\"; if(newHTML!==lastContainerHTML && !isScrolling){ container.innerHTML=newHTML; lastContainerHTML=newHTML; }else if(newHTML!==lastContainerHTML){ setTimeout(function(){ if(!isScrolling && container){ container.innerHTML=newHTML; lastContainerHTML=newHTML; } },200); } } }catch(e){console.log('Container update error:',e);}";
    } else {
        html += "try{ let container=document.getElementById('container'); if(container){ let newHTML=p[8]||\"\"; if(newHTML!==lastContainerHTML && !isScrolling){ container.innerHTML=newHTML; lastContainerHTML=newHTML; }else if(newHTML!==lastContainerHTML){ setTimeout(function(){ if(!isScrolling && container){ container.innerHTML=newHTML; lastContainerHTML=newHTML; } },200); } } }catch(e){console.log('Container update error:',e);}";
    }
    html += "updatePending=false; }catch(e){console.log('Update error:',e);updatePending=false;} } ";
    html += "if('Notification' in window && Notification.permission==='default'){ Notification.requestPermission(); }";
    html += "if(window.updateInterval){clearInterval(window.updateInterval);} ";
    html += "window.updateInterval=setInterval(update,";
    html += String(DATA_UPDATE_INTERVAL);
    html += "); update();";
    html += "</script></body></html>";
    
    // Flush final chunk and close connection
    if (server.client().connected()) {
        server.sendContent(html);
        server.sendContent("");
        server.client().flush();
        server.client().stop();
    }
    html = "";
    lastHttpResponseTime = millis();
}

void handleAddWhite() {
    Serial.println("[HTTP] POST /add_multi_white");
    
    // Check if SD operation is in progress - skip data modification to prevent iterator invalidation
    if (sdBusy) {
        Serial.println("[HTTP] SD busy - rejecting add_white request");
        server.sendHeader("Connection", "close");
        server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
        server.send(503, "text/plain", "SD busy, try again");
        server.client().stop();
        return;
    }
    
    for (int i = 0; i < server.args(); i++) {
        if (server.argName(i) == "ids") {
            String id = server.arg(i);
            id.toUpperCase();
            whitelist.insert(id);
            // Remove from potentialFollowers so it doesn't show on other lists
            potentialFollowers.erase(id);
            // Also remove from knownRouters if present
            knownRouters.erase(id);
        }
    }
    needsSaveWhitelist = true;
    saveWhitelistToNVS();
    server.sendHeader("Connection", "close");
    server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
    server.sendHeader("Location", "/");
    server.send(303);
    server.client().stop();
    lastHttpResponseTime = millis();
}

void handleAddRouter() {
    Serial.println("[HTTP] POST /add_multi_router");
    
    // Check if SD operation is in progress
    if (sdBusy) {
        Serial.println("[HTTP] SD busy - rejecting add_router request");
        server.sendHeader("Connection", "close");
        server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
        server.send(503, "text/plain", "SD busy, try again");
        server.client().stop();
        return;
    }
    
    for (int i = 0; i < server.args(); i++) {
        if (server.argName(i) == "ids") {
            String idM = server.arg(i);
            idM.toUpperCase();
            knownRouters.insert(idM);
            if (potentialFollowers.count(idM)) {
                potentialFollowers[idM].isRouter = true;
            }
        }
    }
    // Mark for background save - do NOT save here!
    needsSaveRouters = true;
    // Send redirect immediately
    server.sendHeader("Connection", "close");
    server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
    server.sendHeader("Location", "/");
    server.send(303);
    server.client().stop();
    lastHttpResponseTime = millis();
}

void handleRemWhite() {
    Serial.println("[HTTP] POST /rem_white");
    
    // Check if SD operation is in progress
    if (sdBusy) {
        Serial.println("[HTTP] SD busy - rejecting rem_white request");
        server.sendHeader("Connection", "close");
        server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
        server.send(503, "text/plain", "SD busy, try again");
        server.client().stop();
        return;
    }
    
    std::vector<String> removedIds;
    for (int i = 0; i < server.args(); i++) {
        if (server.argName(i) == "ids") {
            String id = server.arg(i);
            id.toUpperCase();
            whitelist.erase(id);
            removedIds.push_back(id);
        }
    }
    
    needsSaveWhitelist = true;
    needsReloadFindings = true;
    saveWhitelistToNVS();
    server.sendHeader("Connection", "close");
    server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
    server.sendHeader("Location", "/whitelist_page");
    server.send(303);
    server.client().stop();
    lastHttpResponseTime = millis();
}

void handleRemRouter() {
    Serial.println("[HTTP] POST /rem_router");
    
    // Check if SD operation is in progress
    if (sdBusy) {
        Serial.println("[HTTP] SD busy - rejecting rem_router request");
        server.sendHeader("Connection", "close");
        server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
        server.send(503, "text/plain", "SD busy, try again");
        server.client().stop();
        return;
    }
    
    for (int i = 0; i < server.args(); i++) {
        if (server.argName(i) == "ids") {
            String idM = server.arg(i);
            idM.toUpperCase();
            knownRouters.erase(idM);
            if (potentialFollowers.count(idM)) {
                potentialFollowers[idM].isRouter = false;
            }
        }
    }
    // Mark for background save - do NOT save here!
    needsSaveRouters = true;
    // Send redirect immediately
    server.sendHeader("Connection", "close");
    server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
    server.sendHeader("Location", "/router_page");
    server.send(303);
    server.client().stop();
    lastHttpResponseTime = millis();
}

void handleToggleFilter() {
    Serial.println("[HTTP] GET /toggle_filter");
    
    filterEnabled = !filterEnabled;
    saveFilterConfig();  // Save filter state to SD card so it persists across page navigations
    
    // Return JSON response instead of redirect for faster toggle
    String jsonResponse = "{\"filter\":";
    jsonResponse += String(filterEnabled ? "true" : "false");
    jsonResponse += "}";
    server.sendHeader("Connection", "close");
    server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
    server.send(200, "application/json", jsonResponse);
    server.client().stop();
}

// V2.4.5: Handle TIME_WINDOW_3_MS setting
void handleSetWindow3() {
    Serial.println("[HTTP] GET /set_window3");
    
    if (server.hasArg("ms")) {
        unsigned long newValue = server.arg("ms").toInt();
        
        // Validate value (must be one of the allowed values)
        if (newValue == TIME_WINDOW_3_DEFAULT || newValue == TIME_WINDOW_3_1H || 
            newValue == TIME_WINDOW_3_2H || newValue == TIME_WINDOW_3_4H || 
            newValue == TIME_WINDOW_3_8H || newValue == TIME_WINDOW_3_12H || 
            newValue == TIME_WINDOW_3_24H) {
            
            TIME_WINDOW_3_MS = newValue;
            saveWindow3Config();  // Save to SD card
            
            // CRITICAL: Immediately update time windows and recalculate scores with new window
            updateTimeWindows();
            updateAllPersistenceScores();
            
            Serial.print("[CONFIG] TIME_WINDOW_3_MS set to: ");
            Serial.print(TIME_WINDOW_3_MS / 60000);
            Serial.println(" minutes");
            Serial.println("[CONFIG] Time windows and persistence scores updated immediately");
            
            server.sendHeader("Connection", "close");
            server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
            server.send(200, "application/json", "{\"success\":true}");
            server.client().stop();
        } else {
            Serial.println("[CONFIG] Invalid TIME_WINDOW_3_MS value");
            server.sendHeader("Connection", "close");
            server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
            server.send(400, "application/json", "{\"success\":false,\"error\":\"Invalid value\"}");
            server.client().stop();
        }
    } else {
        server.sendHeader("Connection", "close");
        server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
        server.send(400, "application/json", "{\"success\":false,\"error\":\"Missing ms parameter\"}");
        server.client().stop();
    }
}

void handleSafeShutdown() {
    Serial.println("[HTTP] POST /safe_shutdown");
    safeShutdownRequested = true;
    Serial.println("[SHUTDOWN] Safe shutdown requested - stopping new SD writes");
    
    // Wait for any ongoing SD operations to complete (with timeout)
    unsigned long startWait = millis();
    const unsigned long MAX_WAIT_MS = 5000;  // Max 5 seconds wait
    
    while (sdBusy && (millis() - startWait < MAX_WAIT_MS)) {
        delay(100);
        yield();
    }
    
    // Check if SD is now idle
    if (!sdBusy) {
        safeShutdownReady = true;
        Serial.println("[SHUTDOWN] Safe to power off - all SD operations complete");
        setRgbLed(0, 255, 0);  // Green LED = safe to power off
    } else {
        Serial.println("[SHUTDOWN] WARNING: SD operations still in progress after timeout");
    }
    
    server.sendHeader("Connection", "close");
    server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
    server.send(200, "application/json", "{\"success\":true,\"ready\":" + String(safeShutdownReady ? "true" : "false") + "}");
}

void handleSetTime() {
    Serial.println("[HTTP] POST /set_time");
    
    if (server.hasArg("timestamp")) {
        unsigned long timestamp = server.arg("timestamp").toInt();
        
            // V2.MAP1: Get location from phone if available
            bool locationSet = false;
            if (server.hasArg("lat") && server.hasArg("lon")) {
                double lat = server.arg("lat").toDouble();
                double lon = server.arg("lon").toDouble();
                
                // Validate coordinates (rough bounds check)
                if (lat >= -90.0 && lat <= 90.0 && lon >= -180.0 && lon <= 180.0 && lat != 0.0 && lon != 0.0) {
                    currentLat = lat;
                    currentLon = lon;
                    lastPhoneLocationUpdate = millis();  // Update timestamp
                    // V2.MAP1: Update gpsValid immediately if using phone GPS
                    if (gpsSource == GPS_SOURCE_PHONE || gpsSource == GPS_SOURCE_BOTH) {
                        gpsValid = true;
                    }
                    locationSet = true;
                    Serial.print("Location set from phone: ");
                    Serial.print(currentLat, 6);
                    Serial.print(", ");
                    Serial.println(currentLon, 6);
                } else {
                    Serial.println("Invalid location coordinates received");
                }
            }
        
        // Set time using timeval structure for ESP32
        struct timeval tv;
        tv.tv_sec = (time_t)timestamp;
        tv.tv_usec = 0;
        
        if (settimeofday(&tv, NULL) == 0) {
            // Verify the time was set
            time_t now = time(NULL);
            struct tm timeinfo;
            localtime_r(&now, &timeinfo);
            
            Serial.print("Time set successfully to: ");
            Serial.print(timeinfo.tm_year + 1900);
            Serial.print("-");
            Serial.print(timeinfo.tm_mon + 1 < 10 ? "0" : "");
            Serial.print(timeinfo.tm_mon + 1);
            Serial.print("-");
            Serial.print(timeinfo.tm_mday < 10 ? "0" : "");
            Serial.print(timeinfo.tm_mday);
            Serial.print(" ");
            Serial.print(timeinfo.tm_hour < 10 ? "0" : "");
            Serial.print(timeinfo.tm_hour);
            Serial.print(":");
            Serial.print(timeinfo.tm_min < 10 ? "0" : "");
            Serial.print(timeinfo.tm_min);
            Serial.print(":");
            Serial.print(timeinfo.tm_sec < 10 ? "0" : "");
            Serial.println(timeinfo.tm_sec);
            
            String jsonResponse = "{\"success\":true,\"time\":";
            jsonResponse += String(timestamp);
            if (locationSet) {
                jsonResponse += ",\"location\":true";
            }
            jsonResponse += "}";
            server.sendHeader("Connection", "close");
            server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
            server.send(200, "application/json", jsonResponse);
            server.client().stop();
        } else {
            Serial.println("ERROR: Failed to set time");
            server.sendHeader("Connection", "close");
            server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
            server.send(500, "application/json", "{\"success\":false,\"error\":\"Failed to set time\"}");
            server.client().stop();
        }
    } else {
        server.sendHeader("Connection", "close");
        server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
        server.send(400, "application/json", "{\"success\":false,\"error\":\"No timestamp provided\"}");
        server.client().stop();
    }
}

// Return ESP32 IP address as JSON
void handleGetIp() {
    Serial.println("[HTTP] GET /ip");
    IPAddress ip = WiFi.localIP();
    String json = "{\"ip\":\"" + String(ip[0]) + "." + String(ip[1]) + "." + String(ip[2]) + "." + String(ip[3]) + "\",\"status\":\"" + (WiFi.status() == WL_CONNECTED ? "connected" : "disconnected") + "\"}";
    server.sendHeader("Connection", "close");
    server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
    server.send(200, "application/json", json);
    server.client().stop();
}

// V2.MAP1: Update location from phone (called periodically by JavaScript)
void handleUpdateLocation() {
    Serial.println("[HTTP] GET /update_location - RECEIVED!");
    Serial.print("GPS source: ");
    Serial.println((int)gpsSource);
    
    if (server.hasArg("lat") && server.hasArg("lon")) {
        double lat = server.arg("lat").toDouble();
        double lon = server.arg("lon").toDouble();
        
        Serial.print("Received coordinates: ");
        Serial.print(lat, 6);
        Serial.print(", ");
        Serial.println(lon, 6);
        
        // Validate coordinates
        if (lat >= -90.0 && lat <= 90.0 && lon >= -180.0 && lon <= 180.0 && lat != 0.0 && lon != 0.0) {
            currentLat = lat;
            currentLon = lon;
            lastPhoneLocationUpdate = millis();
            // V2.MAP1: Update gpsValid immediately if using phone GPS
            if (gpsSource == GPS_SOURCE_PHONE || gpsSource == GPS_SOURCE_BOTH) {
                gpsValid = true;
                Serial.println("gpsValid set to TRUE (phone GPS active)");
            } else {
                Serial.println("gpsValid NOT updated (phone GPS not selected)");
            }
            Serial.print("Location updated from phone: ");
            Serial.print(currentLat, 6);
            Serial.print(", ");
            Serial.println(currentLon, 6);
            server.sendHeader("Connection", "close");
            server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
            server.send(200, "application/json", "{\"success\":true}");
            server.client().stop();
        } else {
            Serial.println("Invalid location coordinates received");
            server.sendHeader("Connection", "close");
            server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
            server.send(400, "application/json", "{\"success\":false,\"error\":\"Invalid coordinates\"}");
            server.client().stop();
        }
    } else {
        Serial.println("Missing lat/lon parameters");
        server.sendHeader("Connection", "close");
        server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
        server.send(400, "application/json", "{\"success\":false,\"error\":\"Missing lat/lon parameters\"}");
        server.client().stop();
    }
}

// V2.MAP1: Set GPS source (Device/Phone/Both)
void handleSetGpsSource() {
    Serial.println("[HTTP] POST /set_gps_source");
    
    if (gpsSourceLocked) {
        server.sendHeader("Connection", "close");
        server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
        server.send(403, "application/json", "{\"success\":false,\"error\":\"GPS source is locked\"}");
        server.client().stop();
        return;
    }
    
    if (server.hasArg("source")) {
        int sourceValue = server.arg("source").toInt();
        if (sourceValue >= 0 && sourceValue <= 2) {
            gpsSource = (GpsSource)sourceValue;
            saveGpsSourceConfig();
            Serial.print("GPS source set to: ");
            if (gpsSource == GPS_SOURCE_DEVICE) Serial.println("Device GPS");
            else if (gpsSource == GPS_SOURCE_PHONE) Serial.println("Phone GPS");
            else Serial.println("Both");
            server.sendHeader("Connection", "close");
            server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
            server.send(200, "application/json", "{\"success\":true,\"source\":" + String(sourceValue) + "}");
            server.client().stop();
        } else {
            server.sendHeader("Connection", "close");
            server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
            server.send(400, "application/json", "{\"success\":false,\"error\":\"Invalid source value\"}");
            server.client().stop();
        }
    } else {
        server.sendHeader("Connection", "close");
        server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
        server.send(400, "application/json", "{\"success\":false,\"error\":\"Missing source parameter\"}");
        server.client().stop();
    }
}

// V2.MAP1: Toggle GPS source lock
void handleSetGpsLock() {
    Serial.println("[HTTP] POST /set_gps_lock");
    
    if (server.hasArg("locked")) {
        gpsSourceLocked = (server.arg("locked").toInt() == 1);
        saveGpsLockConfig();
        Serial.print("GPS lock set to: ");
        Serial.println(gpsSourceLocked ? "Locked" : "Unlocked");
        server.sendHeader("Connection", "close");
        server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
        server.send(200, "application/json", "{\"success\":true,\"locked\":" + String(gpsSourceLocked ? "true" : "false") + "}");
        server.client().stop();
    } else {
        server.sendHeader("Connection", "close");
        server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
        server.send(400, "application/json", "{\"success\":false,\"error\":\"Missing locked parameter\"}");
        server.client().stop();
    }
}

// ============================================================================
// V2.4.5: PERSISTENCE SCORE SYSTEM
// ============================================================================

// Update RSSI variance tracking for a device
void updateRssiVariance(TrackingInfo& info, int rssi) {
    info.rssiSum += rssi;
    info.rssiSumSq += (long)rssi * rssi;
    info.rssiSampleCount++;
    info.appearanceCount++;
    
    // Mark as seen in window1
    // Only update windowUpdateTime if entering window1 for first time
    // This preserves the "entry time" for correct window aging
    if (!info.timeWindow1) {
        info.windowUpdateTime = millis();
    }
    info.timeWindow1 = true;
}

// Calculate RSSI variance (lower = more stable = more suspicious)
float getRssiVariance(const TrackingInfo& info) {
    if (info.rssiSampleCount < 2) return 100.0;  // High variance if not enough samples
    
    float mean = (float)info.rssiSum / info.rssiSampleCount;
    float variance = ((float)info.rssiSumSq / info.rssiSampleCount) - (mean * mean);
    return variance > 0 ? variance : 0;
}

// Update time windows for all devices (call every 30 seconds)
// V2.4.5 FINAL: Windows accumulate during continuous detection, then age through windows when silent
void updateTimeWindows() {
    unsigned long now = millis();
    
    for (auto& pair : potentialFollowers) {
        TrackingInfo& info = pair.second;
        unsigned long timeSinceLastSeen = safeTimeDiff(now, info.lastSeen);
        unsigned long timeSinceWindowEntry = safeTimeDiff(now, info.windowUpdateTime);
        
        // More than 30 minutes since last seen - clear everything
        if (timeSinceLastSeen >= TIME_WINDOW_3_MS) {
            if (info.timeWindow1 || info.timeWindow2 || info.timeWindow3) {
                info.timeWindow1 = false;
                info.timeWindow2 = false;
                info.timeWindow3 = false;
                info.appearanceCount = 0;
                info.rssiSum = 0;
                info.rssiSumSq = 0;
                info.rssiSampleCount = 0;
            }
            continue;
        }
        
        // Save previous states BEFORE any modifications
        bool wasInWindow1 = info.timeWindow1;
        bool wasInWindow2 = info.timeWindow2;
        
        // ACCUMULATION (continuous detection): If device stays in window1 for extended time,
        // it also gets marked as present in older windows (sustained presence)
        if (wasInWindow1 && timeSinceWindowEntry >= TIME_WINDOW_1_MS) {
            info.timeWindow2 = true;
        }
        if (wasInWindow1 && timeSinceWindowEntry >= TIME_WINDOW_2_MS) {
            info.timeWindow3 = true;
        }
        
        // AGING (device stopped being detected): When window expires, 
        // device ages into the next older window
        if (timeSinceLastSeen >= TIME_WINDOW_1_MS) {
            // Device leaving window1 range (not seen in last 10 min)
            if (wasInWindow1) {
                // Device WAS in window1, now ages into window2
                info.timeWindow2 = true;
            }
            info.timeWindow1 = false;
        }
        
        if (timeSinceLastSeen >= TIME_WINDOW_2_MS) {
            // Device leaving window2 range (not seen in last 20 min)
            if (wasInWindow2) {
                // Device WAS in window2, now ages into window3
                info.timeWindow3 = true;
            }
            info.timeWindow2 = false;
        }
        
        // Note: window3 expires when timeSinceLastSeen >= TIME_WINDOW_3_MS (handled above)
    }
}

// V2.4.5: Estimate distance from BLE RSSI (meters)
// Based on typical indoor environment with reference power -62 dBm at 1 meter
float estimateBleDistance(int rssi) {
    if (rssi >= -30) return 0.05f;  // 0-10 cm (immediate)
    if (rssi >= -40) return 0.15f;   // 10-20 cm (very strong)
    if (rssi >= -50) return 0.375f;  // 25-50 cm (strong)
    if (rssi >= -62) return 1.0f;    // ~1 meter (good)
    if (rssi >= -70) return 2.5f;    // 2-3 meters (stable)
    if (rssi >= -80) return 7.5f;    // 5-10 meters (weak)
    if (rssi >= -90) return 20.0f;   // 15-25 meters (very weak)
    return 30.0f;  // Beyond range
}

// V2.4.5: Estimate distance from WiFi RSSI (meters)
// Based on typical indoor environment
// Detects 5 GHz from channel (36+ = 5 GHz) OR name containing "5G" / "5GHz" / "5Ghz"
// 5 GHz attenuates ~10 dB more than 2.4 GHz, so same RSSI = shorter distance
// NOTE: Correction is applied ONLY ONCE, even if both channel and name indicate 5 GHz
float estimateWifiDistance(int rssi, int channel, const String& name) {
    // Detect 5 GHz: channel 36+ OR name contains "5G" / "5GHz" / "5Ghz"
    // Check channel first, then name (not both at the same time)
    bool is5GHz = false;
    
    if (channel >= 36) {
        // Channel 36+ = 5 GHz (most accurate method)
        is5GHz = true;
    } else if (name.length() > 0) {
        // Check name only if channel was not 5 GHz
        String nameLower = name;
        nameLower.toLowerCase();
        // Check for "5g", "5ghz" or "5ghz" (case-insensitive)
        if (nameLower.indexOf("5g") != -1) {
            is5GHz = true;
        }
    }
    
    // If 5 GHz, adjust RSSI by +10 dB (5 GHz attenuates 10 dB more, same RSSI = shorter distance)
    // NOTE: Correction is applied ONLY ONCE, even if both channel and name indicate 5 GHz
    int adjustedRssi = rssi;
    if (is5GHz) {
        adjustedRssi = rssi + 10;  // Compensate for 5 GHz attenuation (only once!)
    }
    
    // Use adjusted RSSI for distance calculation (2.4 GHz table)
    if (adjustedRssi >= -30) return 0.5f;   // < 0.5 meters (maximum power)
    if (adjustedRssi >= -42) return 2.0f;   // 1-3 meters (excellent)
    if (adjustedRssi >= -60) return 7.5f;   // 5-10 meters (good and reliable)
    if (adjustedRssi >= -70) return 15.0f;  // 10-20 meters (satisfactory)
    if (adjustedRssi >= -80) return 25.0f;  // > 20 meters (weak)
    return 50.0f;  // Beyond range
}

// V2.4.5: Format distance for display
String formatDistance(float meters) {
    if (meters < 1.0f) {
        return String((int)(meters * 100)) + " cm";
    } else if (meters < 1000.0f) {
        return String(meters, 1) + " m";
    } else {
        return String(meters / 1000.0f, 1) + " km";
    }
}

// V2.MAP5: Self-contained offline map - draws encounter coordinates on canvas
// No external resources needed, works without internet
void handleDeviceMap() {
    String id = server.arg("id");
    id.toUpperCase();
    
    if (id.length() == 0 || potentialFollowers.count(id) == 0) {
        server.send(404, "text/html", "<html><body style='background:#0d0d0d;color:#eee;font-family:sans-serif;text-align:center;padding:40px;'><h2>Device not found</h2><a href='/' style='color:#4caf50;'>Back</a></body></html>");
        return;
    }
    
    const TrackingInfo& info = potentialFollowers[id];
    
    std::vector<std::pair<double, double>> coords;
    if (info.encounterCoordinates.size() > 0) {
        coords = info.encounterCoordinates;
    } else if (info.encounterLat != 0.0 && info.encounterLon != 0.0) {
        coords.push_back({info.encounterLat, info.encounterLon});
    }
    if (info.lastLat != 0.0 && info.lastLon != 0.0) {
        if (coords.empty()) {
            coords.push_back({info.lastLat, info.lastLon});
        } else {
            double dist = TinyGPSPlus::distanceBetween(
                coords.back().first, coords.back().second, info.lastLat, info.lastLon);
            if (dist >= 10.0) {
                coords.push_back({info.lastLat, info.lastLon});
            }
        }
    }
    
    if (coords.empty()) {
        server.send(200, "text/html", "<html><body style='background:#0d0d0d;color:#eee;font-family:sans-serif;text-align:center;padding:40px;'><h2>No GPS data</h2><a href='/' style='color:#4caf50;'>Back</a></body></html>");
        return;
    }
    
    String name = info.name.length() > 0 ? info.name : "Unnamed";
    
    server.setContentLength(CONTENT_LENGTH_UNKNOWN);
    server.sendHeader("Connection", "close");
    server.sendHeader("Cache-Control", "no-store, no-cache, must-revalidate");
    server.send(200, "text/html", "");
    
    server.sendContent(F("<!DOCTYPE html><html><head><meta charset='UTF-8'><meta name='viewport' content='width=device-width,initial-scale=1'><title>Map</title>"
        "<style>body{margin:0;background:#0d0d0d;color:#eee;font-family:sans-serif;text-align:center;}"
        ".hdr{padding:10px;background:#111;border-bottom:1px solid #333;}"
        "canvas{border:1px solid #333;margin:10px auto;display:block;background:#001a00;border-radius:8px;}"
        ".info{font-size:0.85em;color:#aaa;margin:4px;}"
        ".back{display:inline-block;margin:10px;padding:8px 16px;background:#2e7d32;color:#fff;text-decoration:none;border-radius:6px;font-weight:bold;}"
        ".coord-list{text-align:left;max-width:350px;margin:10px auto;padding:10px;background:#1a1a1a;border-radius:8px;font-size:0.8em;}"
        ".coord-item{padding:3px 0;border-bottom:1px solid #222;}</style></head><body>"));
    
    server.sendContent("<div class='hdr'><b style='color:#4caf50;'>");
    server.sendContent(name);
    server.sendContent("</b><br><span style='font-size:0.7em;color:#888;'>");
    server.sendContent(id);
    server.sendContent("</span></div>");
    
    // Build coordinate data as JS array
    String jsCoords = "<script>var pts=[";
    for (size_t i = 0; i < coords.size(); i++) {
        if (i > 0) jsCoords += ",";
        jsCoords += "[";
        jsCoords += String(coords[i].first, 6);
        jsCoords += ",";
        jsCoords += String(coords[i].second, 6);
        jsCoords += "]";
    }
    jsCoords += "];";
    server.sendContent(jsCoords);
    jsCoords = "";
    
    // Canvas drawing script - self-contained
    server.sendContent(F(
        "function draw(){"
        "var c=document.getElementById('map'),ctx=c.getContext('2d');"
        "var W=c.width,H=c.height,pad=40;"
        "if(pts.length==0)return;"
        "var minLat=pts[0][0],maxLat=pts[0][0],minLon=pts[0][1],maxLon=pts[0][1];"
        "for(var i=1;i<pts.length;i++){if(pts[i][0]<minLat)minLat=pts[i][0];if(pts[i][0]>maxLat)maxLat=pts[i][0];"
        "if(pts[i][1]<minLon)minLon=pts[i][1];if(pts[i][1]>maxLon)maxLon=pts[i][1];}"
        "var dLat=maxLat-minLat,dLon=maxLon-minLon;"
        "if(dLat<0.0005)dLat=0.0005;if(dLon<0.0005)dLon=0.0005;"
        "var cLat=(minLat+maxLat)/2,cLon=(minLon+maxLon)/2;"
        "minLat=cLat-dLat*0.7;maxLat=cLat+dLat*0.7;minLon=cLon-dLon*0.7;maxLon=cLon+dLon*0.7;"
        "dLat=maxLat-minLat;dLon=maxLon-minLon;"
        "function toX(lon){return pad+(lon-minLon)/dLon*(W-2*pad);}"
        "function toY(lat){return H-pad-(lat-minLat)/dLat*(H-2*pad);}"
    ));
    
    server.sendContent(F(
        "ctx.fillStyle='#001a00';ctx.fillRect(0,0,W,H);"
        "ctx.strokeStyle='#0a3a0a';ctx.lineWidth=0.5;"
        "for(var g=0;g<5;g++){var gy=pad+g*(H-2*pad)/4;ctx.beginPath();ctx.moveTo(pad,gy);ctx.lineTo(W-pad,gy);ctx.stroke();"
        "var gx=pad+g*(W-2*pad)/4;ctx.beginPath();ctx.moveTo(gx,pad);ctx.lineTo(gx,H-pad);ctx.stroke();}"
        "ctx.font='11px sans-serif';ctx.fillStyle='#4caf50';"
        "ctx.textAlign='center';ctx.fillText('N',W/2,14);ctx.fillText('S',W/2,H-4);"
        "ctx.textAlign='left';ctx.fillText('W',4,H/2);ctx.textAlign='right';ctx.fillText('E',W-4,H/2);"
    ));
    
    server.sendContent(F(
        "if(pts.length>1){ctx.strokeStyle='#4caf5088';ctx.lineWidth=2;ctx.setLineDash([6,4]);"
        "ctx.beginPath();ctx.moveTo(toX(pts[0][1]),toY(pts[0][0]));"
        "for(var i=1;i<pts.length;i++){ctx.lineTo(toX(pts[i][1]),toY(pts[i][0]));}"
        "ctx.stroke();ctx.setLineDash([]);}"
        "for(var i=0;i<pts.length;i++){"
        "var x=toX(pts[i][1]),y=toY(pts[i][0]);"
        "var col=(i==0)?'#4caf50':(i==pts.length-1)?'#f44336':'#ff9800';"
        "ctx.beginPath();ctx.arc(x,y,7,0,Math.PI*2);ctx.fillStyle=col;ctx.fill();"
        "ctx.strokeStyle='#fff';ctx.lineWidth=1.5;ctx.stroke();"
        "ctx.fillStyle='#fff';ctx.font='bold 10px sans-serif';ctx.textAlign='center';ctx.textBaseline='middle';"
        "ctx.fillText(''+(i+1),x,y);}"
    ));
    
    // Scale bar calculation
    server.sendContent(F(
        "var R=6371000,latR=cLat*Math.PI/180;"
        "var totalD=0;for(var i=1;i<pts.length;i++){"
        "var dla=(pts[i][0]-pts[i-1][0])*Math.PI/180,dlo=(pts[i][1]-pts[i-1][1])*Math.PI/180;"
        "var a=Math.sin(dla/2)*Math.sin(dla/2)+Math.cos(pts[i-1][0]*Math.PI/180)*Math.cos(pts[i][0]*Math.PI/180)*Math.sin(dlo/2)*Math.sin(dlo/2);"
        "totalD+=R*2*Math.atan2(Math.sqrt(a),Math.sqrt(1-a));}"
        "var scaleM=dLat*111320;var barLen=100,barM=scaleM*barLen/(H-2*pad);"
        "var nice=[10,20,50,100,200,500,1000,2000,5000];var sM=nice[0];"
        "for(var i=0;i<nice.length;i++){if(nice[i]<=barM*1.5){sM=nice[i];}}"
        "var sLen=sM/scaleM*(H-2*pad);"
        "ctx.strokeStyle='#eee';ctx.lineWidth=2;ctx.beginPath();"
        "ctx.moveTo(W-pad-sLen,H-18);ctx.lineTo(W-pad,H-18);ctx.stroke();"
        "ctx.fillStyle='#eee';ctx.font='10px sans-serif';ctx.textAlign='center';"
        "ctx.fillText((sM>=1000?(sM/1000)+'km':sM+'m'),W-pad-sLen/2,H-8);"
        "ctx.textAlign='left';ctx.fillStyle='#aaa';ctx.font='11px sans-serif';"
        "ctx.fillText('Total: '+(totalD>=1000?(totalD/1000).toFixed(1)+'km':Math.round(totalD)+'m'),pad,H-6);"
        "ctx.fillStyle='#4caf50';ctx.fillText('● Start',pad,22);"
        "ctx.fillStyle='#f44336';ctx.fillText('● End',pad+60,22);"
        "if(pts.length>2){ctx.fillStyle='#ff9800';ctx.fillText('● Mid',pad+105,22);}"
        "}</script>"
    ));
    
    server.sendContent(F("<canvas id='map' width='350' height='350'></canvas>"
        "<script>draw();</script>"));
    
    // Coordinate list
    server.sendContent("<div class='coord-list'>");
    for (size_t i = 0; i < coords.size(); i++) {
        server.sendContent("<div class='coord-item'><span style='color:");
        server.sendContent(i == 0 ? "#4caf50" : (i == coords.size() - 1 ? "#f44336" : "#ff9800"));
        server.sendContent(";font-weight:bold;'>");
        server.sendContent(String(i + 1));
        server.sendContent(".</span> ");
        server.sendContent(String(coords[i].first, 6));
        server.sendContent(", ");
        server.sendContent(String(coords[i].second, 6));
        server.sendContent("</div>");
    }
    server.sendContent("</div>");
    
    // Calculate total distance for display
    double totalDist = 0;
    for (size_t i = 1; i < coords.size(); i++) {
        totalDist += TinyGPSPlus::distanceBetween(
            coords[i-1].first, coords[i-1].second, coords[i].first, coords[i].second);
    }
    server.sendContent("<div class='info'>");
    server.sendContent(String(coords.size()));
    server.sendContent(" encounters | ");
    if (totalDist >= 1000) {
        server.sendContent(String(totalDist / 1000.0, 1));
        server.sendContent(" km");
    } else {
        server.sendContent(String((int)totalDist));
        server.sendContent(" m");
    }
    server.sendContent(" total</div>");
    
    server.sendContent(F("<a class='back' href='/'>&#8592; Back</a>"));
    server.sendContent(F("</body></html>"));
}

// Calculate persistence score for a device (0.0 - 1.0)
float calculatePersistenceScore(const TrackingInfo& info) {
    // 1. Window score (0-1): How many time windows is device present in?
    int windowCount = (info.timeWindow1 ? 1 : 0) + 
                      (info.timeWindow2 ? 1 : 0) + 
                      (info.timeWindow3 ? 1 : 0);
    float windowScore = windowCount / 3.0;
    
    // 2. Encounter score (0-1): Normalize encounter count (cap at 7)
    int encounters = min(info.encounterCount, 7);
    float encounterScore = (encounters - 1) / 6.0;  // 1 encounter = 0, 7+ = 1.0
    
    // 3. RSSI stability score (0-1): Low variance = high score
    float variance = getRssiVariance(info);
    // Variance typically ranges 0-400 for RSSI (-100 to -30 dBm)
    // Low variance (< 50) = very stable = suspicious
    float rssiScore = 1.0 - min(variance / 200.0f, 1.0f);
    
    // 4. Frequency score (0-1): How often seen in last 20 minutes
    // Expect 0-40 appearances in 20 minutes (scan every 30 seconds)
    float freqScore = min((float)info.appearanceCount / 30.0f, 1.0f);
    
    // 5. V2.4.5: Distance proximity score (0-1): Closer = higher risk
    // Estimate distance based on device type (BLE or WiFi)
    float estimatedDistance = 50.0f;  // Default: far away
    if (info.type == "BLE") {
        estimatedDistance = estimateBleDistance(info.lastRSSI);
    } else if (info.type == "WiFi") {
        estimatedDistance = estimateWifiDistance(info.lastRSSI, info.wifiChannel, info.name);
    }
    
    // Distance score: closer = higher score
    // Normalize: 0m = 1.0, 5m = 0.5, 10m = 0.25, 20m+ = 0.0
    // Use exponential decay for more realistic scoring
    float distanceScore = 0.0f;
    if (estimatedDistance < 20.0f) {
        // Exponential decay: score = e^(-distance/5)
        distanceScore = expf(-estimatedDistance / 5.0f);
    }
    
    // Weighted combination
    float score = (windowScore * WEIGHT_WINDOWS) +
                  (encounterScore * WEIGHT_ENCOUNTERS) +
                  (rssiScore * WEIGHT_RSSI_STABILITY) +
                  (freqScore * WEIGHT_FREQUENCY) +
                  (distanceScore * WEIGHT_DISTANCE);
    
    return min(max(score, 0.0f), 1.0f);  // Clamp to 0-1
}

// Get persistence level (1-7) from score
int getPersistenceLevel(float score) {
    if (score >= 0.90) return 7;  // FOLLOWER
    if (score >= 0.75) return 6;  // Severe
    if (score >= 0.60) return 5;  // Warning
    if (score >= 0.45) return 4;  // Suspicious
    if (score >= 0.30) return 3;  // Notable
    if (score >= 0.15) return 2;  // Recurring
    return 1;  // Normal
}

// Update persistence scores for all devices
void updateAllPersistenceScores() {
    for (auto& pair : potentialFollowers) {
        TrackingInfo& info = pair.second;
        info.persistenceScore = calculatePersistenceScore(info);
    }
}

// Get color for persistence level (returns CSS color string)
String getPersistenceColor(int level) {
    switch(level) {
        case 1: return "#4CAF50";  // Green
        case 2: return "#8BC34A";  // Light green
        case 3: return "#FFC107";  // Yellow/Amber
        case 4: return "#FF9800";  // Orange
        case 5: return "#f44336";  // Red
        case 6: return "#b71c1c";  // Dark red
        case 7: return "#000000";  // Black
        default: return "#9E9E9E"; // Gray
    }
}

// Get CSS class for blinking (levels 5-7)
String getBlinkClass(int level) {
    switch(level) {
        case 5: return "blink-slow";   // 1.5s
        case 6: return "blink-medium"; // 1.0s
        case 7: return "blink-fast";   // 0.5s
        default: return "";
    }
}

void setup() {
    Serial.begin(115200);
    delay(1000);  // Give Serial time to initialize
    
    // Test Serial output immediately
    Serial.println();
    Serial.println("========================================");
    Serial.println("AFOSCA V2.MAP5 starting...");
    Serial.println("========================================");
    Serial.println("ESP32-C5 detected - verify pin configuration!");
    
    // Initialize SD card - V3.2 METHOD: SPI.begin() BEFORE SD.begin()!
    Serial.println("=== SD CARD INITIALIZATION (V3.2 METHOD) ===");
    Serial.print("  Pins: CS=");
    Serial.print(SD_CS);
    Serial.print(", SCK=");
    Serial.print(SD_SCK);
    Serial.print(", MOSI=");
    Serial.print(SD_MOSI);
    Serial.print(", MISO=");
    Serial.println(SD_MISO);
    
    bool sdInitOk = false;
    
    // V3.2 METHOD: MUST call SPI.begin() with pins BEFORE SD.begin()!
    pinMode(SD_CS, OUTPUT);
    digitalWrite(SD_CS, HIGH);
    delay(100);
    
    // CRITICAL: Initialize SPI bus with correct pins FIRST
    SPI.begin(SD_SCK, SD_MISO, SD_MOSI, SD_CS);
    delay(100);
    
    // Try different speeds (start with slower speeds for better stability)
    // Slower speeds = more reliable, less corruption risk
    uint32_t speeds[] = {1000000, 400000, 4000000};  // Start with 1MHz for stability
    const char* speedNames[] = {"1MHz", "400kHz", "4MHz"};
    
    for (int i = 0; i < 3 && !sdInitOk; i++) {
        Serial.print("  Trying ");
        Serial.print(speedNames[i]);
        Serial.print("... ");
        
        if (SD.begin(SD_CS, SPI, speeds[i])) {
            Serial.println("SUCCESS!");
            sdInitOk = true;
        } else {
            Serial.println("failed");
            delay(100);
        }
    }
    
    if (!sdInitOk) {
        Serial.println("  === SD INIT FAILED ===");
        Serial.print("  Check wiring: CS=GPIO");
        Serial.print(SD_CS);
        Serial.print(", SCK=GPIO");
        Serial.print(SD_SCK);
        Serial.print(", MOSI=GPIO");
        Serial.print(SD_MOSI);
        Serial.print(", MISO=GPIO");
        Serial.println(SD_MISO);
        Serial.println("  Verify: GND->GND, VCC->3.3V or 5V, card inserted, FAT32 format");
    }
    
    if (sdInitOk) {
        sdReady = true;
        Serial.println("=== SD CARD READY ===");
        
        // Show card info
        uint8_t cardType = SD.cardType();
        Serial.print("  Card type: ");
        if (cardType == CARD_NONE) {
            Serial.println("NONE (no card?)");
            sdReady = false;
        } else if (cardType == CARD_MMC) {
            Serial.println("MMC");
        } else if (cardType == CARD_SD) {
            Serial.println("SD");
        } else if (cardType == CARD_SDHC) {
            Serial.println("SDHC");
        } else {
            Serial.println("UNKNOWN");
        }
        
        if (sdReady) {
            uint64_t cardSize = SD.cardSize() / (1024 * 1024);
            Serial.print("  Card size: ");
            Serial.print((unsigned long)cardSize);
            Serial.println(" MB");
        }
        delay(50);  // Small delay before file operations
        
        // List root directory to verify SD card access
        File root = SD.open("/");
        if (root) {
            Serial.println("SD card root directory contents:");
            File file = root.openNextFile();
            int fileCount = 0;
            while (file) {
                Serial.print("  ");
                Serial.print(file.name());
                if (!file.isDirectory()) {
                    Serial.print(" (");
                    Serial.print(file.size());
                    Serial.println(" bytes)");
                } else {
                    Serial.println(" (DIR)");
                }
                file.close();
                file = root.openNextFile();
                fileCount++;
                if (fileCount > 20) break;  // Limit output
            }
            root.close();
            Serial.println("End of directory listing");
        } else {
            Serial.println("WARNING: Could not open SD root directory");
        }
        
        cleanupTempFiles();  // Remove orphaned temp files first
        delay(50);
        loadLists();  // Load whitelist and routers first
        delay(50);
        loadWindow3Config();
        loadHotspotConfig();
        
        gpsSource = GPS_SOURCE_PHONE;
        Serial.println("[GPS] Using phone GPS only");
        
        // Load GPS source and lock config from SD card (overrides default if saved)
        // Note: User can still change to GPS_SOURCE_BOTH if they add device GPS later
        loadGpsSourceConfig();
        loadGpsLockConfig();
        loadFilterConfig();  // Load filter state from internal NVS memory
        
        loadAllFindings();  // Then load all previous findings
        
        // Clean entries older than 7 days on startup
        cleanOldCacheEntries();
        lastCacheCleanup = millis();  // Reset timer after startup cleanup
        
        Serial.println("SD card data loading completed");
        saveWhitelistToNVS();
    } else {
        Serial.println("ERROR: SD card initialization failed!");
        Serial.println("Check SD card connections and card format (must be FAT16/FAT32)");
        sdReady = false;
        loadWhitelistFromNVS();
        loadGpsSourceConfig();
        loadGpsLockConfig();
        loadFilterConfig();
    }
    
    WiFi.mode(WIFI_AP_STA);
    WiFi.setAutoReconnect(false);
    
    // ESP32-C5: Use 2.4GHz only for reliable hotspot connection
    // WIFI_BAND_MODE_AUTO causes "can not get wifi protocol" errors on some ESP32-C5 boards
    #if ESP_IDF_VERSION_MAJOR >= 5 && defined(CONFIG_IDF_TARGET_ESP32C5)
    esp_err_t band_err = esp_wifi_set_band_mode(WIFI_BAND_MODE_2G_ONLY);
    if (band_err == ESP_OK) {
        Serial.println("[WiFi] WiFi band set to 2.4GHz (ESP32-C5)");
    } else {
        Serial.print("[WiFi] WARNING: Failed to set WiFi band mode, error: ");
        Serial.println(band_err);
    }
    #endif
    
    // Check if hotspot config was loaded
    if (hotspot_ssid.length() == 0) {
        Serial.println("[WiFi] ERROR: Hotspot SSID not loaded from SD card!");
        Serial.println("[WiFi] Create /hotspot_config.txt with:");
        Serial.println("[WiFi] SSID=YourHotspotName");
        Serial.println("[WiFi] PASSWORD=YourPassword");
        Serial.println("[WiFi] STATIC_IP=192.168.43.100  (optional)");
        Serial.println("[WiFi] GATEWAY=192.168.43.1      (optional)");
    } else {
        Serial.print("[WiFi] Connecting to hotspot: ");
        Serial.println(hotspot_ssid);
        
        // Configure static IP if enabled
        if (use_static_ip) {
            if (!WiFi.config(static_ip, gateway, subnet, dns)) {
                Serial.println("[WiFi] WARNING: Failed to configure static IP!");
            } else {
                Serial.print("[WiFi] Static IP configured: ");
                Serial.println(static_ip);
            }
        }
        
        WiFi.begin(hotspot_ssid.c_str(), hotspot_password.c_str());
        
        int attempts = 0;
        while (WiFi.status() != WL_CONNECTED && attempts < 20) {
            delay(500);
            Serial.print(".");
            attempts++;
        }
        Serial.println();
        
        if (WiFi.status() == WL_CONNECTED) {
            IPAddress ip = WiFi.localIP();
            Serial.println();
            Serial.println("========================================");
            Serial.println("[WiFi] CONNECTED SUCCESSFULLY!");
            Serial.print("[WiFi] IP address: ");
            Serial.println(ip);
            Serial.print("[WiFi] Open in browser: http://");
            Serial.println(ip);
            Serial.println("========================================");
            Serial.println();
        } else {
            WiFi.setAutoReconnect(false);
            WiFi.disconnect(false);
            Serial.println("[WiFi] ERROR: Failed to connect to hotspot!");
            Serial.println("[WiFi] Radio released for scanning");
        }
        if (WiFi.status() == WL_CONNECTED) {
            
            // Automatically add connected hotspot to whitelist
            if (!hotspotAddedToWhitelist) {
                String hotspotBSSID = WiFi.BSSIDstr();
                hotspotBSSID.toUpperCase();
                if (hotspotBSSID.length() > 0) {
                    bool wasInWhitelist = (whitelist.count(hotspotBSSID) > 0);
                    
                    if (!wasInWhitelist) {
                        whitelist.insert(hotspotBSSID);
                        needsSaveWhitelist = true;
                        Serial.print("[WiFi] Hotspot added to whitelist: ");
                        Serial.print(hotspotBSSID);
                        Serial.print(" (");
                        Serial.print(hotspot_ssid);
                        Serial.println(")");
                    } else {
                        Serial.print("[WiFi] Hotspot already in whitelist: ");
                        Serial.println(hotspotBSSID);
                    }
                    
                    // Always update name in potentialFollowers (in case MAC changed or name updated)
                    unsigned long now = millis();
                    if (potentialFollowers.count(hotspotBSSID) == 0) {
                        // New device - create entry
                        TrackingInfo newInfo;
                        newInfo.lastSeen = now;
                        newInfo.lastRSSI = WiFi.RSSI();
                        newInfo.type = "WiFi";
                        newInfo.name = hotspot_ssid;
                        newInfo.isRouter = false;  // Hotspot is not a router
                        newInfo.firstSeen = now;
                        newInfo.hitCount = 1;
                        potentialFollowers[hotspotBSSID] = newInfo;
                    } else {
                        // Device exists - update name and last seen
                        potentialFollowers[hotspotBSSID].name = hotspot_ssid;
                        potentialFollowers[hotspotBSSID].lastSeen = now;
                        potentialFollowers[hotspotBSSID].lastRSSI = WiFi.RSSI();
                        potentialFollowers[hotspotBSSID].type = "WiFi";
                    }
                    needsSaveWhitelist = true;  // Ensure name is saved
                    
                    hotspotAddedToWhitelist = true;
                }
            }
            
            lastWifiStatusBlink = millis();
            wifiStatusLedState = false;
        }
    }
    
    // Configure NTP for time synchronization (via internet through phone hotspot)
    configTime(2 * 3600, 0, "pool.ntp.org", "time.nist.gov");  // UTC+2 (EET), DST handled automatically
    Serial.println("[NTP] NTP time synchronization configured");
    
    Serial1.begin(GPS_BAUD, SERIAL_8N1, GPS_RX_PIN, GPS_TX_PIN);
    gpsSerialStartTime = millis();
    Serial.println("=== GPS MODULE INITIALIZATION ===");
    Serial.print("  UART1 pins: RX=GPIO");
    Serial.print(GPS_RX_PIN);
    Serial.print(" (← GPS TX), TX=GPIO");
    Serial.print(GPS_TX_PIN);
    Serial.println(" (→ GPS RX)");
    Serial.print("  Baud rate: ");
    Serial.println(GPS_BAUD);
    Serial.println("  Waiting for NMEA data...");

    // Setup web server routes
    server.on("/", handleRoot);
    server.on("/get_data", handleGetData);
    server.on("/router_page", handleRoot);
    server.on("/whitelist_page", handleRoot);
    server.on("/randomized_page", handleRoot);
    server.on("/ble_page", handleRoot);
    server.on("/toggle_filter", handleToggleFilter);
    server.on("/set_time", handleSetTime);
    server.on("/set_window3", handleSetWindow3);  // V2.4.5: TIME_WINDOW_3_MS setting
    server.on("/update_location", handleUpdateLocation);  // V2.MAP1: Update location from phone
    server.on("/safe_shutdown", HTTP_POST, handleSafeShutdown);  // Safe shutdown request
    server.on("/set_gps_source", handleSetGpsSource);  // V2.MAP1: Set GPS source
    server.on("/set_gps_lock", handleSetGpsLock);  // V2.MAP1: Toggle GPS lock
    server.on("/add_multi_white", HTTP_POST, handleAddWhite);
    server.on("/add_multi_router", HTTP_POST, handleAddRouter);
    server.on("/rem_white", HTTP_POST, handleRemWhite);
    server.on("/rem_router", HTTP_POST, handleRemRouter);
    server.on("/ip", handleGetIp);  // Return ESP32 IP address as JSON
    server.on("/device_map", handleDeviceMap);  // V2.MAP5: Self-contained offline map
    
    server.begin();
    Serial.println("Web server started");
    
    // Initialize BLE
    // NOTE: DON'T start scanning here! WiFi connection is still establishing
    // and BLE scanning fails silently on ESP32-C5.
    // First scan is started in loop() after WiFi settles.
    Serial.println("Initializing BLE...");
    NimBLEDevice::init("AFOSCA");
    
    // Verify BLE initialized
    Serial.print("BLE Address: ");
    Serial.println(NimBLEDevice::getAddress().toString().c_str());
    
    NimBLEScan* pBLEScan = NimBLEDevice::getScan();
    pBLEScan->setScanCallbacks(&myScanCallbacks, false);
    pBLEScan->setActiveScan(true);  // Active scan requests scan response for more data
    
    // ESP32-C5 optimized scan parameters (much shorter interval/window for better detection)
    // Interval: 100 * 0.625ms = 62.5ms
    // Window: 99 * 0.625ms = 61.875ms (almost continuous scanning)
    pBLEScan->setInterval(100);
    pBLEScan->setWindow(99);
    pBLEScan->setMaxResults(0);  // Don't store results in memory, use callbacks instead
    
    // IMPORTANT: Disable duplicate filtering to catch all advertisements
    // Some devices (like smartwatches) may advertise infrequently
    pBLEScan->setDuplicateFilter(false);
    
    // IMPORTANT: Ensure bleScanInProgress is false so loop() can start scanning
    bleScanInProgress = false;
    
    Serial.println("BLE initialized - first scan will start in loop() after WiFi settles");
    
    // Initialize RGB LED
    pinMode(RGB_LED_PIN, OUTPUT);
    setRgbLed(0, 0, 0);  // Start with LED off
    Serial.println("RGB LED initialized on GPIO 27");
    
    // Enable promiscuous mode for deauthentication detection
    // Note: Promiscuous mode works in both AP and STA (client) mode
    esp_wifi_set_promiscuous(true);
    esp_wifi_set_promiscuous_rx_cb(&promiscuousCallback);
    Serial.println("Deauther detection (promiscuous mode) enabled");
    
    // Flash green briefly to indicate successful startup
    setRgbLed(0, 50, 0);
    delay(200);
    setRgbLed(0, 0, 0);
}

void loop() {
    // Check WiFi connection and reconnect if needed
    static unsigned long lastIpPrint = 0;
    if (WiFi.status() == WL_CONNECTED) {
        // Automatically add connected hotspot to whitelist (if not already added)
        if (!hotspotAddedToWhitelist) {
            String hotspotBSSID = WiFi.BSSIDstr();
            hotspotBSSID.toUpperCase();
            if (hotspotBSSID.length() > 0) {
                bool wasInWhitelist = (whitelist.count(hotspotBSSID) > 0);
                
                if (!wasInWhitelist) {
                    whitelist.insert(hotspotBSSID);
                    needsSaveWhitelist = true;
                    Serial.print("[WiFi] Hotspot added to whitelist: ");
                    Serial.print(hotspotBSSID);
                    Serial.print(" (");
                    Serial.print(hotspot_ssid);
                    Serial.println(")");
                } else {
                    Serial.print("[WiFi] Hotspot already in whitelist: ");
                    Serial.println(hotspotBSSID);
                }
                
                // Always update name in potentialFollowers (in case MAC changed or name updated)
                unsigned long now = millis();
                if (potentialFollowers.count(hotspotBSSID) == 0) {
                    // New device - create entry
                    TrackingInfo newInfo;
                    newInfo.lastSeen = now;
                    newInfo.lastRSSI = WiFi.RSSI();
                    newInfo.type = "WiFi";
                    newInfo.name = hotspot_ssid;
                    newInfo.isRouter = false;  // Hotspot is not a router
                    newInfo.firstSeen = now;
                    newInfo.hitCount = 1;
                    potentialFollowers[hotspotBSSID] = newInfo;
                } else {
                    // Device exists - update name and last seen
                    potentialFollowers[hotspotBSSID].name = hotspot_ssid;
                    potentialFollowers[hotspotBSSID].lastSeen = now;
                    potentialFollowers[hotspotBSSID].lastRSSI = WiFi.RSSI();
                    potentialFollowers[hotspotBSSID].type = "WiFi";
                }
                needsSaveWhitelist = true;  // Ensure name is saved
                
                hotspotAddedToWhitelist = true;
            }
        }
        
        // Print IP address once every 30 seconds (in case user missed it)
        unsigned long now = millis();
        if (lastIpPrint == 0 || (now - lastIpPrint > 30000)) {
            lastIpPrint = now;
            IPAddress ip = WiFi.localIP();
            Serial.print("[WiFi] Connected - IP: http://");
            Serial.println(ip);
        }
    } else {
        lastIpPrint = 0;
        hotspotAddedToWhitelist = false;
        static unsigned long lastReconnectAttempt = 0;
        // reconnectInProgress is global (used by WiFi scan guard too)
        unsigned long now = millis();
        if (reconnectInProgress) {
            if (WiFi.status() == WL_CONNECTED) {
                reconnectInProgress = false;
                Serial.println("[WiFi] Reconnected!");
            } else if (safeTimeDiff(now, lastReconnectAttempt) > 10000) {
                reconnectInProgress = false;
                WiFi.setAutoReconnect(false);
                WiFi.disconnect(false);
                Serial.println("[WiFi] Reconnect timeout, radio released for scanning");
            }
        } else if (safeTimeDiff(now, lastReconnectAttempt) > 50000) {
            if (hotspot_ssid.length() > 0 && !wifiScanPending) {
                Serial.println("[WiFi] Attempting to reconnect...");
                WiFi.setAutoReconnect(false);
                WiFi.disconnect(false);
                delay(100);
                if (use_static_ip) {
                    WiFi.config(static_ip, gateway, subnet, dns);
                }
                WiFi.begin(hotspot_ssid.c_str(), hotspot_password.c_str());
                reconnectInProgress = true;
                lastReconnectAttempt = now;
            }
        }
    }
    
    server.handleClient();
    
    // Safe shutdown state check - update ready status and LED
    if (safeShutdownRequested && !sdBusy && !safeShutdownReady) {
        safeShutdownReady = true;
        Serial.println("[SHUTDOWN] Safe to power off - all SD operations complete");
        setRgbLed(0, 255, 0);  // Green LED = safe to power off
    }
    
    // Periodic memory check (every ~30 seconds)
    static unsigned long lastMemoryCheck = 0;
    unsigned long now = millis();
    if (now - lastMemoryCheck > 30000) {
        lastMemoryCheck = now;
        uint32_t freeHeap = ESP.getFreeHeap();
        Serial.print("[MEM] Free heap: ");
        Serial.print(freeHeap);
        Serial.print(" bytes, potentialFollowers: ");
        Serial.print(potentialFollowers.size());
        Serial.print(", ouiCache: ");
        Serial.print(ouiCache.size());
        Serial.print("/");
        Serial.println(MAX_OUI_CACHE_SIZE);
        
        // Warning if memory is getting low
        if (freeHeap < 20000) {  // Less than 20KB free
            Serial.println("[MEM] WARNING: Low memory! Cleaning up...");
            // Force cleanup of old potentialFollowers entries
            unsigned long sevenDaysAgo = now - (7 * 24 * 60 * 60 * 1000UL);
            int removed = 0;
            for (auto it = potentialFollowers.begin(); it != potentialFollowers.end(); ) {
                if (it->second.lastSeen < sevenDaysAgo) {
                    it = potentialFollowers.erase(it);
                    removed++;
                } else {
                    ++it;
                }
            }
            Serial.print("[MEM] Removed ");
            Serial.print(removed);
            Serial.print(" old entries. New heap: ");
            Serial.println(ESP.getFreeHeap());
            
            // Also try to free heap fragmentation
            if (freeHeap < 15000) {  // Critical: less than 15KB
                Serial.println("[MEM] CRITICAL: Forcing heap compaction...");
                // Force garbage collection by clearing temporary strings
                String temp = "";
                temp.reserve(0);
            }
        }
    }
    
    // Handle deauthentication alarm LED flashing (has priority)
    handleDeauthAlarm();
    
    // WiFi connection status LED blinking (blue, brief flash every 20 seconds when connected)
    // Only blink if deauth alarm is not active
    if (!deauthAlarmActive && WiFi.status() == WL_CONNECTED) {
        unsigned long now = millis();
        if (now - lastWifiStatusBlink >= WIFI_STATUS_BLINK_INTERVAL) {
            lastWifiStatusBlink = now;
            // Brief flash: turn on for 100ms, then off
            setRgbLed(0, 0, 255);  // Blue LED on (GRB order: G=0, R=0, B=255)
            wifiStatusLedState = true;
        } else if (wifiStatusLedState && (now - lastWifiStatusBlink >= 100)) {
            // Turn off after 100ms flash
            wifiStatusLedState = false;
            setRgbLed(0, 0, 0);  // LED off
        }
    } else if (WiFi.status() != WL_CONNECTED) {
        // WiFi not connected - turn off status LED if it was on
        if (wifiStatusLedState) {
            wifiStatusLedState = false;
            // Only turn off if deauth alarm is not active
            if (!deauthAlarmActive) {
                setRgbLed(0, 0, 0);
            }
        }
    }
    
    // Clean old cache entries every 7 days
    if (millis() - lastCacheCleanup > CACHE_CLEANUP_INTERVAL) {
        lastCacheCleanup = millis();
        cleanOldCacheEntries();
    }
    
    // V2.4.5: Update time windows and persistence scores every 30 seconds
    if (millis() - lastWindowUpdate > WINDOW_UPDATE_INTERVAL) {
        lastWindowUpdate = millis();
        updateTimeWindows();
        updateAllPersistenceScores();
    }
    
    // Watchdog: Release stuck sdBusy lock (if stuck for more than 30 seconds)
    // 30s is well above worst-case SD ops (10s timeout) to avoid interrupting legitimate operations
    if (sdBusy && safeTimeDiff(millis(), sdBusyStartTime) > 30000) {
        Serial.println("[SD] WARNING: sdBusy stuck for 30+ seconds - force releasing lock");
        sdBusy = false;
        sdFailCount++;
        if (sdFailCount >= SD_FAIL_THRESHOLD) {
            Serial.println("[SD] Too many timeouts - marking SD as not ready for reinit");
            sdReady = false;
            sdFailCount = 0;
        }
    }
    
    // Check SD card status periodically
    if (millis() - lastSdCheck > SD_CHECK_INTERVAL) {
        lastSdCheck = millis();
        
        if (sdReady && !sdBusy) {
            // PROACTIVE HEALTH CHECK: Verify SD card is still accessible
            File testFile = SD.open("/", FILE_READ);
            if (!testFile) {
                Serial.println("[SD] Health check FAILED - SD card not accessible!");
                sdReady = false;
                sdFailCount = 0;
            } else {
                testFile.close();
            }
        }
        
        if (!sdReady) {
            // V3.2 METHOD: SPI.begin() BEFORE SD.begin()!
            Serial.println("[SD] Attempting to reinitialize SD card...");
            SD.end();
            delay(50);
            SPI.end();
            delay(50);
            SPI.begin(SD_SCK, SD_MISO, SD_MOSI, SD_CS);
            delay(100);
            
            uint32_t speeds[] = {1000000, 400000, 4000000};
            bool reinitOk = false;
            for (int i = 0; i < 3 && !reinitOk; i++) {
                if (SD.begin(SD_CS, SPI, speeds[i])) {
                    reinitOk = true;
                }
                delay(50);
            }
            
            if (reinitOk) {
                Serial.println("[SD] Reinitialized successfully!");
                sdReady = true;
                sdBusy = false;
                sdFailCount = 0;
                delay(50);
                loadLists();
                saveWhitelistToNVS();
            } else {
                Serial.println("[SD] Reinitialization failed - will retry in 30s");
            }
        }
    }
    
    int gpsBytes = 0;
    while (Serial1.available() > 0 && gpsBytes < 512) {
        char c = Serial1.read();
        gps.encode(c);
        gpsBytes++;
    }

    if (!gpsModuleDetected && gps.passedChecksum() > 0) {
        gpsModuleDetected = true;
        gpsRxTxSwapped = false;
        Serial.println("[GPS] External GPS module detected - valid NMEA data");
        Serial.print("[GPS] Passed checksums: ");
        Serial.print(gps.passedChecksum());
        Serial.print(", Satellites: ");
        Serial.println(gps.satellites.value());
    }

    if (!gpsModuleDetected) {
        unsigned long elapsed = safeTimeDiff(millis(), gpsSerialStartTime);
        unsigned long diagInterval = gpsAutoBaudDone ? 60000 : 10000;
        if (elapsed > diagInterval && safeTimeDiff(millis(), gpsLastDiagCheck) > diagInterval) {
            gpsLastDiagCheck = millis();
            uint32_t chars = gps.charsProcessed();
            if (chars == 0 && !gpsNoDataWarningShown) {
                gpsNoDataWarningShown = true;
                gpsAutoBaudDone = true;
                Serial.println("[GPS] WARNING: No data from GPS module after 10s");
                Serial.println("[GPS] Possible causes:");
                Serial.println("[GPS]   1. GPS module not connected or not powered");
                Serial.println("[GPS]   2. RX/TX pins swapped - swap wires on GPIO" + String(GPS_RX_PIN) + " and GPIO" + String(GPS_TX_PIN));
                Serial.println("[GPS]   3. Wrong baud rate (current: " + String(GPS_BAUD) + ")");
                Serial.print("[GPS]   4. Check wiring: GPS TX → ESP32 GPIO");
                Serial.print(GPS_RX_PIN);
                Serial.print(", GPS RX → ESP32 GPIO");
                Serial.println(GPS_TX_PIN);
            } else if (chars > 0 && gps.failedChecksum() > 0 && gps.passedChecksum() == 0) {
                if (!gpsAutoBaudDone) {
                    gpsBaudIndex++;
                    if (gpsBaudIndex >= gpsBaudRateCount) {
                        gpsBaudIndex = 0;
                        gpsAutoBaudDone = true;
                        gpsSwapWarningShown = true;
                        gpsRxTxSwapped = true;
                        Serial.println("[GPS] AUTO-BAUD: All baud rates tried, none worked!");
                        Serial.println("[GPS] Possible cause: RX/TX pins swapped - swap wires on GPIO" + String(GPS_RX_PIN) + " and GPIO" + String(GPS_TX_PIN));
                    } else {
                        gpsCurrentBaud = gpsBaudRates[gpsBaudIndex];
                        Serial1.end();
                        delay(50);
                        Serial1.begin(gpsCurrentBaud, SERIAL_8N1, GPS_RX_PIN, GPS_TX_PIN);
                        gpsSerialStartTime = millis();
                        gpsLastDiagCheck = millis();
                        Serial.print("[GPS] AUTO-BAUD: Trying ");
                        Serial.print(gpsCurrentBaud);
                        Serial.println(" baud...");
                    }
                }
            }
        }
    }

    // Update GPS coordinates periodically
    updateGpsCoordinates();
    
    // Background SD card operations (do NOT block HTTP responses)
    if (sdReady) {
        // OPTIONAL: Maclookup.app API lookup (if enabled)
        // (SD card OUI lookup removed - using only internal list + API)
        #if ENABLE_MACVENDORS_API
        processMacVendorsApiQueue();
        #endif
        
        // Background reload of findings from SD card (for router/ble/randomized pages)
        // Only reload when no HTTP request is active to avoid blocking page navigation
        static unsigned long lastBackgroundReload = 0;
        bool httpActive = false;
        WiFiClient client = server.client();
        if (client && client.connected()) {
            httpActive = true;
        }
        bool httpCooldown = (lastHttpResponseTime > 0 && safeTimeDiff(millis(), lastHttpResponseTime) < 500);
        // Defer ALL SD operations while HTTP client is connected OR during cooldown after redirect
        // Cooldown gives browser time to send redirect GET before SD blocks the server
        if (!httpActive && !httpCooldown && !sdBusy) {
            if (needsReloadFindings || (safeTimeDiff(millis(), lastBackgroundReload) > 120000)) {
                needsReloadFindings = false;
                loadAllFindings();
                lastBackgroundReload = millis();
                server.handleClient();
            }
            if (needsSaveWhitelist) {
                needsSaveWhitelist = false;
                saveList("/whitelist.txt", whitelist);
                server.handleClient();
            }
            if (needsSaveRouters) {
                needsSaveRouters = false;
                saveList("/routers.txt", knownRouters);
                server.handleClient();
            }
            if (needsSaveFindings && ESP.getFreeHeap() > 30000) {
                needsSaveFindings = false;
                saveAllFindings();
                server.handleClient();
            }
        }
    }
    
    // WiFi scan - ASYNC (non-blocking, keeps web server responsive)
    static unsigned long lastWiFiScan = 0;
    static unsigned int wifiScanFailCount = 0;
    static unsigned long lastScanFailLog = 0;
    // wifiScanPending is global (used by reconnect guard too)
    const unsigned long SCAN_FAIL_LOG_INTERVAL = 300000;
    unsigned long scanInterval = WIFI_SCAN_INTERVAL;
    if (wifiScanFailCount >= 3) scanInterval = 120000;

    if (!wifiScanPending && !reconnectInProgress && safeTimeDiff(millis(), lastWiFiScan) > scanInterval && !bleScanInProgress) {
        lastWiFiScan = millis();
        int result = WiFi.scanNetworks(true, true, false, 0);  // true = ASYNC, non-blocking
        if (result == WIFI_SCAN_RUNNING) {
            wifiScanPending = true;
        } else if (result == WIFI_SCAN_FAILED) {
            wifiScanFailCount++;
            if (safeTimeDiff(millis(), lastScanFailLog) >= SCAN_FAIL_LOG_INTERVAL) {
                lastScanFailLog = millis();
                Serial.println("[WiFi] Async scan start failed");
            }
        }
    }

    if (wifiScanPending) {
        int n = WiFi.scanComplete();
        if (n >= 0) {
            wifiScanPending = false;
            if (n > 0) {
                wifiScanFailCount = 0;
                Serial.print("[WiFi] Scan found ");
                Serial.print(n);
                Serial.println(" networks");
                for (int i = 0; i < n; i++) {
                    int channel = WiFi.channel(i);
                    processDevice("WiFi", WiFi.BSSIDstr(i), WiFi.RSSI(i), WiFi.SSID(i), channel);
                }
            } else {
                wifiScanFailCount = 0;
            }
            WiFi.scanDelete();
        } else if (n == WIFI_SCAN_FAILED) {
            wifiScanPending = false;
            wifiScanFailCount++;
            WiFi.scanDelete();
            if (safeTimeDiff(millis(), lastScanFailLog) >= SCAN_FAIL_LOG_INTERVAL) {
                lastScanFailLog = millis();
                Serial.println("[WiFi] Scan failed - async AUTO 2.4+5GHz");
            }
        }
    }
    
    // BLE scan
    static unsigned long lastBLEScan = 0;
    static bool firstBLEScanStarted = false;
    static unsigned long setupCompleteTime = 0;
    
    // Track when setup completed (first loop iteration)
    if (setupCompleteTime == 0) {
        setupCompleteTime = millis();
    }
    
    // Start first BLE scan 2 seconds after setup (give WiFi time to settle)
    // ESP32-C5: WiFi and BLE share the same radio, WiFi must settle first
    if (!firstBLEScanStarted && !bleScanInProgress && (millis() - setupCompleteTime > 2000)) {
        firstBLEScanStarted = true;
        lastBLEScan = millis();
        bleScanInProgress = true;
        bleDevicesFoundThisScan = 0;
        Serial.println("[BLE] Starting first scan (WiFi settled)...");
        NimBLEScan* pScan = NimBLEDevice::getScan();
        pScan->clearResults();
        
        bool started = pScan->start(BLE_SCAN_DURATION, false);
        if (!started) {
            Serial.println("[BLE] ERROR: Failed to start first scan!");
            bleScanInProgress = false;
            firstBLEScanStarted = false;
            delay(1000);
        } else {
            Serial.print("[BLE] Scan started, duration: ");
            Serial.print(BLE_SCAN_DURATION);
            Serial.println(" seconds");
        }
    }
    
    // Periodic BLE scans (after first scan)
    if (firstBLEScanStarted && safeTimeDiff(millis(), lastBLEScan) > BLE_SCAN_INTERVAL && !bleScanInProgress) {
        lastBLEScan = millis();
        bleScanInProgress = true;
        bleDevicesFoundThisScan = 0;
        Serial.println("[BLE] Starting periodic scan...");
        NimBLEScan* pScan = NimBLEDevice::getScan();
        pScan->clearResults();
        
        bool started = pScan->start(BLE_SCAN_DURATION, false);
        if (!started) {
            Serial.println("[BLE] ERROR: Failed to start scan!");
            bleScanInProgress = false;
        } else {
            Serial.print("[BLE] Periodic scan started, duration: ");
            Serial.print(BLE_SCAN_DURATION);
            Serial.println(" seconds");
        }
    }
    
    // Save all findings periodically (every 5 minutes) to SD card
    // BUT: Don't save during HTTP requests or if memory is low
    static unsigned long lastSaveFindings = 0;
    const unsigned long FINDINGS_SAVE_INTERVAL = 300000;  // 5 minutes
    if (sdReady && millis() - lastSaveFindings > FINDINGS_SAVE_INTERVAL) {
        // Check if HTTP request is in progress (check if client is connected)
        bool httpActive2 = false;
        WiFiClient client2 = server.client();
        if (client2 && client2.connected()) {
            httpActive2 = true;
        }
        bool httpCooldown2 = (lastHttpResponseTime > 0 && safeTimeDiff(millis(), lastHttpResponseTime) < 500);
        
        // Check memory before saving (need at least 30KB free)
        uint32_t freeHeap = ESP.getFreeHeap();
        
        if (!httpActive2 && !httpCooldown2 && freeHeap > 30000 && !sdBusy) {
            lastSaveFindings = millis();
            saveAllFindings();
        } else {
            // Skip save if HTTP active, low memory, or SD busy - try again in 30 seconds
            if (millis() - lastSaveFindings > FINDINGS_SAVE_INTERVAL + 30000) {
                lastSaveFindings = millis() - FINDINGS_SAVE_INTERVAL + 30000;  // Retry in 30s
                Serial.print("[SAVE] Skipped SD save - HTTP active: ");
                Serial.print(httpActive2);
                Serial.print(", Free heap: ");
                Serial.print(freeHeap);
                Serial.print(", SD busy: ");
                Serial.println(sdBusy);
            }
        }
    }
}
