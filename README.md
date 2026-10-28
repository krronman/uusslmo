# Sky Colosseum Online

Multiplayer WASD pixel-walker. Node.js + WebSocket (`ws`), server-authoritative movement.

## Run locally
    npm install
    npm start        # http://localhost:3000  (open in several tabs)

## Deploy on Render.com
1. Push this folder to a GitHub/GitLab repo.
2. Render Dashboard → New → Web Service → select the repo
   (or New → Blueprint, which reads `render.yaml`).
3. Settings: Runtime `Node`, Build `npm install`, Start `node server.js`.
4. Deploy, then open the `.onrender.com` URL.

Notes: the free plan sleeps after inactivity, so the first load can take ~30–60 s.
WebSockets work on Render with no extra configuration.
