# aria-cam-relay

Lets you watch an ESP32-CAM from any phone or browser. The camera sits behind a home router, so it pushes JPEG frames out to this relay, which serves them to viewers as a live MJPEG stream.

```
ESP32-CAM ──POST /push (HTTPS)──▶ relay (Render) ──MJPEG──▶ viewers
```

It has no dependencies and runs on Node's `http` module only. The relay tells the camera how many people are watching, so the camera slows to one frame every 3 seconds when nobody is.

## Deploy on Render

On Render, choose **New → Blueprint** and select this repo. It will ask for two keys:

| Variable   | Purpose |
|------------|---------|
| `CAM_KEY`  | Secret the camera sends in the `X-Cam-Key` header. It must match `RELAY_KEY` in the firmware. |
| `VIEW_KEY` | Key viewers need. Share `https://<service>.onrender.com/?key=<VIEW_KEY>`. |

To revoke everyone's access, change `VIEW_KEY`.

## Endpoints

| Route | Auth | |
|---|---|---|
| `POST /push` | `X-Cam-Key` | JPEG body. Responds with the current viewer count. |
| `GET /?key=` | view key | Mobile-friendly viewer page |
| `GET /stream?key=` | view key | MJPEG stream |
| `GET /snapshot?key=` | view key | Latest JPEG |
| `GET /status?key=` | view key | `{online, lastFrameAgeMs, viewers}` |
| `GET /healthz` | none | Health check |

## Run locally

```
CAM_KEY=ck VIEW_KEY=vk PORT=10000 node server.js
```
