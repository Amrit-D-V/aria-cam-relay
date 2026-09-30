# aria-cam-relay

Lets you watch an ESP32-CAM from any phone or browser. The camera sits behind a home router, so it pushes JPEG frames out to this relay, which serves them to viewers as a live MJPEG stream.

```
ESP32-CAM ──WebSocket (wss)──▶ relay (Render) ──MJPEG──▶ viewers
```

It has no dependencies and runs on Node's `http` module only. The relay tells the camera how many people are watching, so the camera slows to one frame every 3 seconds when nobody is.

## Deploy on Render

On Render, choose **New → Blueprint** and select this repo. It will ask for two keys:

| Variable   | Purpose |
|------------|---------|
| `CAM_KEY`  | Secret the camera sends in the `X-Cam-Key` header. It must match `RELAY_KEY` in the firmware. |
| `VIEW_KEY` | Key viewers need. Share `https://<service>.onrender.com/?key=<VIEW_KEY>`. |

To revoke everyone's access, change `VIEW_KEY`.

Camera controls on the page (privacy, night mode, light, resolution, restart) need an admin key. That is `ADMIN_KEY` if you set it, otherwise `CAM_KEY`. Setting a separate `ADMIN_KEY` is recommended.

## Endpoints

| Route | Auth | |
|---|---|---|
| `GET /ws` | `X-Cam-Key` | Camera WebSocket. Binary messages are JPEG frames, and the relay sends the viewer count as text every second. |
| `POST /push` | `X-Cam-Key` | Older uplink: one JPEG per request. Responds with the viewer count. It's slower because every frame waits a full round trip. |
| `POST /meta` | `X-Cam-Key` | JSON from the face tracker: face boxes, names, emotions and the robot's mood, drawn over the video. |
| `POST /cmd` | `X-Admin-Key` (`ADMIN_KEY`, else `CAM_KEY`) | Camera command `{cmd, args}`: `led`, `ledauto`, `night`, `privacy`, `privhours`, `profile`, `restart` |
| `GET /events?key=` | view key | Server-Sent Events stream of `/meta` updates |
| `GET /?key=` | view key | Mobile-friendly viewer page with the face overlay |
| `GET /stream?key=` | view key | MJPEG stream |
| `GET /snapshot?key=` | view key | Latest JPEG |
| `GET /status?key=` | view key | `{online, lastFrameAgeMs, viewers}` |
| `GET /healthz` | none | Health check |

## Run locally

```
CAM_KEY=ck VIEW_KEY=vk PORT=10000 node server.js
```
