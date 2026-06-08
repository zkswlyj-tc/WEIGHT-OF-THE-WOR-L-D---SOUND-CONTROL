window.addEventListener("error", function (e) {
        const b = document.getElementById("bootStatus");
        const err = document.getElementById("errorBanner");
        const msg =
          "JS error: " +
          (e.message || "unknown") +
          " at " +
          (e.filename || "") +
          ":" +
          (e.lineno || "");
        if (b)
          b.textContent = "Code error — check console / use the fixed file.";
        if (err) {
          err.textContent = msg;
          err.classList.add("visible");
        }
      });
      window.addEventListener("unhandledrejection", function (e) {
        const b = document.getElementById("bootStatus");
        const err = document.getElementById("errorBanner");
        const msg =
          "Startup error: " +
          ((e.reason && (e.reason.message || e.reason)) || "unknown");
        if (b) b.textContent = "Startup error — read the red banner.";
        if (err) {
          err.textContent = msg;
          err.classList.add("visible");
        }
      });

let FilesetResolver = null;
      let HandLandmarker = null;
      let DrawingUtils = null;

      async function loadMediaPipeTools() {
        if (FilesetResolver && HandLandmarker && DrawingUtils) return;

        const visionBundle =
          await import("https://cdn.jsdelivr.net/npm/@mediapipe/tasks-vision@latest/vision_bundle.mjs");

        FilesetResolver = visionBundle.FilesetResolver;
        HandLandmarker = visionBundle.HandLandmarker;
        DrawingUtils = visionBundle.DrawingUtils;
      }

      const CONFIG = {
        // Match these to the exported 3-screen video timeline.
        // Stage I: city overload.
        // Stage II: inner voice rupture.
        // Stage III: garden re-grounding.
        stage1EndSeconds: 60,
        stage2EndSeconds: 120,

        audio: {
          cityBase: 0.36,
          voicesBase: 0.3,
          breathBase: 0.08,
          toneBase: 0.03,

          glitchBase: 0.0,
          rumbleBase: 0.0,
          whisperBase: 0.0,
          metalBase: 0.0,
          pulseBase: 0.0,

          gardenBase: 0.0,
          birdsBase: 0.0,
          windBase: 0.0,
          waterBase: 0.0,

          scene1ScoreBase: 0.0,
          scene2ScoreBase: 0.0,
          scene3ScoreBase: 0.0,

          master: 0.9,
        },

        tracking: {
          smoothing: 0.16,
          speedScale: 4.7,
          stillnessScale: 6.5,
          handLostDecay: 0.93,
          centerRadius: 0.34,
          pinchClosed: 0.42,
          pinchOpen: 1.55,
          opennessLow: 1.5,
          opennessHigh: 3.1,
        },

        effect: {
          stageFadeSeconds: 0.08,
          overloadMaxOuter: 1.08,
          blurMaxEcho: 0.62,
          calmMinOuter: 0.08,
          calmMaxInner: 0.88,
          gardenMax: 0.98,
        },
      };

      const webcam = document.getElementById("webcam");
      const handCanvas = document.getElementById("handCanvas");
      const handCtx = handCanvas.getContext("2d");
      const cinematicCanvas = document.getElementById("cinematicCanvas");
      const cinematicCtx = cinematicCanvas.getContext("2d");

      const startOverlay = document.getElementById("startOverlay");
      const startButton = document.getElementById("startButton");
      const bootStatus = document.getElementById("bootStatus");
      const errorBanner = document.getElementById("errorBanner");

      const debugPanel = document.getElementById("debugPanel");
      const debugToggle = document.getElementById("debugToggle");
      const restartButton = document.getElementById("restartButton");
      const pauseButton = document.getElementById("pauseButton");
      const stage1Button = document.getElementById("stage1Button");
      const stage2Button = document.getElementById("stage2Button");
      const stage3Button = document.getElementById("stage3Button");
      const debugReadout = document.getElementById("debugReadout");

      const hud = document.getElementById("hud");
      const stageLabel = document.getElementById("stageLabel");
      const interactionHint = document.getElementById("interactionHint");

      const outerFill = document.getElementById("outerFill");
      const innerFill = document.getElementById("innerFill");
      const chaosFill = document.getElementById("chaosFill");
      const blurFill = document.getElementById("blurFill");
      const gardenFill = document.getElementById("gardenFill");
      const scoreFill = document.getElementById("scoreFill");

      const outerValue = document.getElementById("outerValue");
      const innerValue = document.getElementById("innerValue");
      const chaosValue = document.getElementById("chaosValue");
      const blurValue = document.getElementById("blurValue");
      const gardenValue = document.getElementById("gardenValue");
      const scoreValue = document.getElementById("scoreValue");

      const audioEls = {
        city: document.getElementById("cityAudio"),
        voices: document.getElementById("voicesAudio"),
        breath: document.getElementById("breathAudio"),
        tone: document.getElementById("toneAudio"),

        glitch: document.getElementById("glitchAudio"),
        rumble: document.getElementById("rumbleAudio"),
        whisper: document.getElementById("whisperAudio"),
        metal: document.getElementById("metalAudio"),
        pulse: document.getElementById("pulseAudio"),

        garden: document.getElementById("gardenAudio"),
        birds: document.getElementById("birdsAudio"),
        wind: document.getElementById("windAudio"),
        water: document.getElementById("waterAudio"),

        scene1Score: document.getElementById("scene1ScoreAudio"),
        scene2Score: document.getElementById("scene2ScoreAudio"),
        scene3Score: document.getElementById("scene3ScoreAudio"),
      };

      let appStarted = false;
      let isPaused = false;
      let debugVisible = false;

      let handLandmarker = null;
      let drawingUtils = null;
      let webcamStream = null;
      let lastWebcamTime = -1;
      let lastFrameMs = performance.now();
      let lastHandCenter = null;
      let currentStage = "Not started";

      let audioContext = null;
      let audioGraph = null;

      let timelineStartMs = 0;
      let pausedAtSeconds = 0;
      let timelineRunning = false;

      let lastChaosBurstAt = 0;
      let nextChaosBurstDelay = 1800;

      const latestHands = {
        left: null,
        primary: null,
      };

      const lastHandCenters = {
        left: null,
        primary: null,
      };

      const handTrails = {
        left: [],
        primary: [],
      };

      const particles = [];

      const smoothed = {
        handPresent: 0,
        x: 0.5,
        y: 0.5,
        openness: 0,
        pinch: 1,
        movement: 0,
        stillness: 0,
        centered: 0,
        outer: 0,
        inner: 0,
        chaos: 0,
        blur: 0,
        garden: 0,
        score: 0,
        leftHandPresent: 0,
        leftX: 0.5,
        leftY: 0.5,
        leftOpenness: 0,
        leftMovement: 0,
        leftStillness: 0,
      };

      function clamp(value, min = 0, max = 1) {
        return Math.min(max, Math.max(min, value));
      }

      function lerp(a, b, t) {
        return a + (b - a) * t;
      }

      function smoothValue(key, target, amount = CONFIG.tracking.smoothing) {
        smoothed[key] = lerp(smoothed[key], target, amount);
        return smoothed[key];
      }

      function distance(a, b) {
        const dx = a.x - b.x;
        const dy = a.y - b.y;
        return Math.sqrt(dx * dx + dy * dy);
      }

      function averagePoints(points) {
        const total = points.reduce(
          (acc, point) => ({ x: acc.x + point.x, y: acc.y + point.y }),
          { x: 0, y: 0 },
        );
        return { x: total.x / points.length, y: total.y / points.length };
      }

      function remap(value, inMin, inMax, outMin = 0, outMax = 1) {
        const normalized = clamp((value - inMin) / (inMax - inMin));
        return outMin + normalized * (outMax - outMin);
      }

      function randomRange(min, max) {
        return min + Math.random() * (max - min);
      }

      function getTimelineTime() {
        if (!timelineRunning && isPaused) return pausedAtSeconds;
        if (!timelineRunning) return 0;
        return (performance.now() - timelineStartMs) / 1000;
      }

      function setTimelineTime(seconds) {
        const safeSeconds = Math.max(0, seconds);
        Object.values(audioEls).forEach((audioEl) => {
          try {
            if (Number.isFinite(audioEl.duration) && audioEl.duration > 0) {
              audioEl.currentTime = safeSeconds % audioEl.duration;
            } else {
              audioEl.currentTime = 0;
            }
          } catch (error) {
            audioEl.currentTime = 0;
          }
        });

        pausedAtSeconds = safeSeconds;
        timelineStartMs = performance.now() - safeSeconds * 1000;
        currentStage = "";
      }

      function showError(message) {
        errorBanner.textContent = message;
        errorBanner.classList.add("visible");
      }

      function clearError() {
        errorBanner.textContent = "";
        errorBanner.classList.remove("visible");
      }

      function setBootStatus(message) {
        bootStatus.textContent = message;
      }

      function ramp(param, value, time = CONFIG.effect.stageFadeSeconds) {
        if (!audioContext || !param) return;
        const now = audioContext.currentTime;
        param.cancelScheduledValues(now);
        param.setValueAtTime(param.value, now);
        param.linearRampToValueAtTime(value, now + time);
      }

      function safePercent(value) {
        return `${Math.round(clamp(value) * 100)}%`;
      }

      function setMeters(outer, inner, chaos, blur, garden, score) {
        outerFill.style.width = safePercent(outer);
        innerFill.style.width = safePercent(inner);
        chaosFill.style.width = safePercent(chaos);
        blurFill.style.width = safePercent(blur);
        gardenFill.style.width = safePercent(garden);
        scoreFill.style.width = safePercent(score);

        outerValue.textContent = safePercent(outer);
        innerValue.textContent = safePercent(inner);
        chaosValue.textContent = safePercent(chaos);
        blurValue.textContent = safePercent(blur);
        gardenValue.textContent = safePercent(garden);
        scoreValue.textContent = safePercent(score);
      }

      function createAudioGraph() {
        const AudioContextClass =
          window.AudioContext || window.webkitAudioContext;
        audioContext = new AudioContextClass();

        const masterGain = audioContext.createGain();
        masterGain.gain.value = CONFIG.audio.master;
        masterGain.connect(audioContext.destination);

        const compressor = audioContext.createDynamicsCompressor();
        compressor.threshold.value = -18;
        compressor.knee.value = 24;
        compressor.ratio.value = 8;
        compressor.attack.value = 0.006;
        compressor.release.value = 0.18;
        compressor.connect(masterGain);

        const outerBus = audioContext.createGain();
        outerBus.gain.value = 0.35;

        const outerFilter = audioContext.createBiquadFilter();
        outerFilter.type = "lowpass";
        outerFilter.frequency.value = 14000;
        outerFilter.Q.value = 0.75;

        const outerPan = audioContext.createStereoPanner();
        outerPan.pan.value = 0;

        outerBus.connect(outerFilter);
        outerFilter.connect(outerPan);
        outerPan.connect(compressor);

        const innerBus = audioContext.createGain();
        innerBus.gain.value = 0.08;

        const innerFilter = audioContext.createBiquadFilter();
        innerFilter.type = "lowpass";
        innerFilter.frequency.value = 12000;
        innerFilter.Q.value = 0.5;

        innerBus.connect(innerFilter);
        innerFilter.connect(compressor);

        const chaosBus = audioContext.createGain();
        chaosBus.gain.value = 0.0;

        const chaosFilter = audioContext.createBiquadFilter();
        chaosFilter.type = "bandpass";
        chaosFilter.frequency.value = 1100;
        chaosFilter.Q.value = 1.2;

        const chaosPan = audioContext.createStereoPanner();
        chaosPan.pan.value = 0;

        chaosBus.connect(chaosFilter);
        chaosFilter.connect(chaosPan);
        chaosPan.connect(compressor);

        const lowBus = audioContext.createGain();
        lowBus.gain.value = 0.0;

        const lowFilter = audioContext.createBiquadFilter();
        lowFilter.type = "lowpass";
        lowFilter.frequency.value = 140;
        lowFilter.Q.value = 0.9;

        lowBus.connect(lowFilter);
        lowFilter.connect(compressor);

        const gardenBus = audioContext.createGain();
        gardenBus.gain.value = 0.0;

        const gardenFilter = audioContext.createBiquadFilter();
        gardenFilter.type = "lowpass";
        gardenFilter.frequency.value = 9000;
        gardenFilter.Q.value = 0.45;

        const gardenPan = audioContext.createStereoPanner();
        gardenPan.pan.value = 0;

        gardenBus.connect(gardenFilter);
        gardenFilter.connect(gardenPan);
        gardenPan.connect(compressor);

        const scoreBus = audioContext.createGain();
        scoreBus.gain.value = 0.18;

        const scoreFilter = audioContext.createBiquadFilter();
        scoreFilter.type = "lowpass";
        scoreFilter.frequency.value = 9000;
        scoreFilter.Q.value = 0.55;

        const scorePan = audioContext.createStereoPanner();
        scorePan.pan.value = 0;

        scoreBus.connect(scoreFilter);
        scoreFilter.connect(scorePan);
        scorePan.connect(compressor);

        const delay = audioContext.createDelay(1.6);
        delay.delayTime.value = 0.22;

        const feedback = audioContext.createGain();
        feedback.gain.value = 0.06;

        const echoWet = audioContext.createGain();
        echoWet.gain.value = 0.02;

        outerPan.connect(delay);
        chaosPan.connect(delay);
        scorePan.connect(delay);
        delay.connect(feedback);
        feedback.connect(delay);
        delay.connect(echoWet);
        echoWet.connect(compressor);

        function makeStem(element, gainValue, loop = true) {
          const source = audioContext.createMediaElementSource(element);
          const gain = audioContext.createGain();
          gain.gain.value = gainValue;
          element.loop = loop;
          source.connect(gain);
          return { source, gain };
        }

        const stems = {
          city: makeStem(audioEls.city, CONFIG.audio.cityBase, true),
          voices: makeStem(audioEls.voices, CONFIG.audio.voicesBase, true),
          breath: makeStem(audioEls.breath, CONFIG.audio.breathBase, true),
          tone: makeStem(audioEls.tone, CONFIG.audio.toneBase, true),

          glitch: makeStem(audioEls.glitch, CONFIG.audio.glitchBase, true),
          rumble: makeStem(audioEls.rumble, CONFIG.audio.rumbleBase, true),
          whisper: makeStem(audioEls.whisper, CONFIG.audio.whisperBase, true),
          metal: makeStem(audioEls.metal, CONFIG.audio.metalBase, true),
          pulse: makeStem(audioEls.pulse, CONFIG.audio.pulseBase, true),

          garden: makeStem(audioEls.garden, CONFIG.audio.gardenBase, true),
          birds: makeStem(audioEls.birds, CONFIG.audio.birdsBase, true),
          wind: makeStem(audioEls.wind, CONFIG.audio.windBase, true),
          water: makeStem(audioEls.water, CONFIG.audio.waterBase, true),

          scene1Score: makeStem(
            audioEls.scene1Score,
            CONFIG.audio.scene1ScoreBase,
            true,
          ),
          scene2Score: makeStem(
            audioEls.scene2Score,
            CONFIG.audio.scene2ScoreBase,
            true,
          ),
          scene3Score: makeStem(
            audioEls.scene3Score,
            CONFIG.audio.scene3ScoreBase,
            true,
          ),
        };

        stems.city.gain.connect(outerBus);
        stems.voices.gain.connect(outerBus);

        stems.breath.gain.connect(innerBus);
        stems.tone.gain.connect(innerBus);

        stems.glitch.gain.connect(chaosBus);
        stems.whisper.gain.connect(chaosBus);
        stems.metal.gain.connect(chaosBus);
        stems.pulse.gain.connect(chaosBus);

        stems.rumble.gain.connect(lowBus);

        stems.garden.gain.connect(gardenBus);
        stems.birds.gain.connect(gardenBus);
        stems.wind.gain.connect(gardenBus);
        stems.water.gain.connect(gardenBus);

        stems.scene1Score.gain.connect(scoreBus);
        stems.scene2Score.gain.connect(scoreBus);
        stems.scene3Score.gain.connect(scoreBus);

        audioGraph = {
          masterGain,
          compressor,

          outerBus,
          outerFilter,
          outerPan,

          innerBus,
          innerFilter,

          chaosBus,
          chaosFilter,
          chaosPan,

          lowBus,
          lowFilter,

          gardenBus,
          gardenFilter,
          gardenPan,

          scoreBus,
          scoreFilter,
          scorePan,

          delay,
          feedback,
          echoWet,

          stems,
        };
      }

      async function startAudioOnly() {
        if (!audioContext) createAudioGraph();
        await audioContext.resume();

        Object.values(audioEls).forEach((audioEl) => {
          audioEl.loop = true;
          audioEl.currentTime = 0;
        });

        await Promise.all(
          Object.values(audioEls).map((audioEl) => audioEl.play()),
        );

        pausedAtSeconds = 0;
        timelineStartMs = performance.now();
        timelineRunning = true;
        isPaused = false;
        pauseButton.textContent = "Pause";
      }

      async function resumeAudio() {
        if (!audioContext) return;
        await audioContext.resume();
        await Promise.all(
          Object.values(audioEls).map((audioEl) => audioEl.play()),
        );
        timelineStartMs = performance.now() - pausedAtSeconds * 1000;
        timelineRunning = true;
        isPaused = false;
        pauseButton.textContent = "Pause";
      }

      function pauseAllAudio() {
        pausedAtSeconds = getTimelineTime();
        Object.values(audioEls).forEach((audioEl) => audioEl.pause());
        timelineRunning = false;
        isPaused = true;
        pauseButton.textContent = "Resume";
      }

      async function setupHandTracking() {
        await loadMediaPipeTools();

        if (handLandmarker && webcamStream) {
          setBootStatus("Camera ready.");
          return;
        }

        setBootStatus("Loading hand-tracking model...");

        const vision = await FilesetResolver.forVisionTasks(
          "https://cdn.jsdelivr.net/npm/@mediapipe/tasks-vision@latest/wasm",
        );

        handLandmarker = await HandLandmarker.createFromOptions(vision, {
          baseOptions: {
            modelAssetPath:
              "https://storage.googleapis.com/mediapipe-models/hand_landmarker/hand_landmarker/float16/1/hand_landmarker.task",
          },
          runningMode: "VIDEO",
          numHands: 2,
          minHandDetectionConfidence: 0.55,
          minHandPresenceConfidence: 0.55,
          minTrackingConfidence: 0.5,
        });

        drawingUtils = new DrawingUtils(handCtx);

        setBootStatus("Requesting camera access...");
        webcamStream = await navigator.mediaDevices.getUserMedia({
          video: {
            width: { ideal: 960 },
            height: { ideal: 720 },
            facingMode: "user",
          },
          audio: false,
        });

        webcam.srcObject = webcamStream;
        await webcam.play();

        resizeHandCanvas();
        setBootStatus("Camera ready.");
      }

      function resizeHandCanvas() {
        if (!webcam.videoWidth || !webcam.videoHeight) return;
        handCanvas.width = webcam.videoWidth;
        handCanvas.height = webcam.videoHeight;
      }

      function resizeCinematicCanvas() {
        const dpr = Math.min(window.devicePixelRatio || 1, 2);
        cinematicCanvas.width = Math.floor(window.innerWidth * dpr);
        cinematicCanvas.height = Math.floor(window.innerHeight * dpr);
        cinematicCanvas.style.width = `${window.innerWidth}px`;
        cinematicCanvas.style.height = `${window.innerHeight}px`;
        cinematicCtx.setTransform(dpr, 0, 0, dpr, 0, 0);
      }

      window.addEventListener("resize", () => {
        resizeHandCanvas();
        resizeCinematicCanvas();
      });
      resizeCinematicCanvas();
      webcam.addEventListener("loadedmetadata", resizeHandCanvas);

      function drawDebugLandmarks(landmarks) {
        if (!debugVisible) return;
        handCtx.clearRect(0, 0, handCanvas.width, handCanvas.height);
        if (!landmarks) return;

        drawingUtils.drawConnectors(
          landmarks,
          HandLandmarker.HAND_CONNECTIONS,
          {
            color: "#d71f27",
            lineWidth: 4,
          },
        );

        drawingUtils.drawLandmarks(landmarks, {
          color: "#ffffff",
          radius: 3,
          lineWidth: 2,
        });
      }

      function measureHand(landmarks, dt, role = "primary") {
        const wrist = landmarks[0];
        const thumbTip = landmarks[4];
        const indexBase = landmarks[5];
        const indexTip = landmarks[8];
        const middleBase = landmarks[9];
        const middleTip = landmarks[12];
        const ringTip = landmarks[16];
        const pinkyBase = landmarks[17];
        const pinkyTip = landmarks[20];

        const palmCenter = averagePoints([
          wrist,
          indexBase,
          middleBase,
          pinkyBase,
        ]);
        const palmWidth = Math.max(distance(indexBase, pinkyBase), 0.001);

        const pinchRaw = distance(thumbTip, indexTip) / palmWidth;
        const pinch = remap(
          pinchRaw,
          CONFIG.tracking.pinchClosed,
          CONFIG.tracking.pinchOpen,
          0,
          1,
        );

        const opennessRaw =
          (distance(wrist, indexTip) +
            distance(wrist, middleTip) +
            distance(wrist, ringTip) +
            distance(wrist, pinkyTip)) /
          4 /
          palmWidth;

        const openness = remap(
          opennessRaw,
          CONFIG.tracking.opennessLow,
          CONFIG.tracking.opennessHigh,
          0,
          1,
        );

        let movement = 0;
        if (lastHandCenters[role]) {
          const travel = distance(palmCenter, lastHandCenters[role]);
          movement = clamp(
            (travel / Math.max(dt, 0.016)) * CONFIG.tracking.speedScale,
          );
        }

        lastHandCenters[role] = palmCenter;

        const centerDistance = distance(palmCenter, { x: 0.5, y: 0.5 });
        const centered =
          1 - clamp(centerDistance / CONFIG.tracking.centerRadius);
        const stillness = 1 - clamp(movement * CONFIG.tracking.stillnessScale);

        return {
          x: palmCenter.x,
          y: palmCenter.y,
          pinch,
          openness,
          movement,
          centered,
          stillness,
        };
      }

      function applyHandMetrics(metrics) {
        smoothValue("handPresent", 1, 0.28);
        smoothValue("x", metrics.x);
        smoothValue("y", metrics.y);
        smoothValue("pinch", metrics.pinch);
        smoothValue("openness", metrics.openness);
        smoothValue("movement", metrics.movement);
        smoothValue("centered", metrics.centered);
        smoothValue("stillness", metrics.stillness);
      }

      function decayHandMetrics() {
        smoothValue("handPresent", 0, 0.08);
        smoothValue("movement", 0, 0.14);
        smoothValue(
          "openness",
          smoothed.openness * CONFIG.tracking.handLostDecay,
          0.1,
        );
        smoothValue("pinch", 1, 0.1);
        smoothValue("centered", 0, 0.12);
        smoothValue("stillness", 0, 0.12);
        lastHandCenter = null;
        lastHandCenters.primary = null;
      }

      function classifyHands(result, dt) {
        const landmarksList = result.landmarks || [];
        const handednessList = result.handednesses || [];

        if (!landmarksList.length) {
          decayHandMetrics();
          smoothValue("leftHandPresent", 0, 0.08);
          smoothValue("leftMovement", 0, 0.14);
          smoothValue("leftStillness", 0, 0.12);
          return { primaryLandmarks: null, leftLandmarks: null };
        }

        let leftIndex = -1;
        let primaryIndex = 0;

        for (let i = 0; i < landmarksList.length; i++) {
          const label =
            handednessList[i]?.[0]?.categoryName ||
            handednessList[i]?.[0]?.displayName ||
            "";
          if (label.toLowerCase() === "left") leftIndex = i;
        }

        if (leftIndex < 0 && landmarksList.length > 1) {
          leftIndex = landmarksList[0][0].x < landmarksList[1][0].x ? 0 : 1;
        }

        if (leftIndex >= 0) {
          primaryIndex =
            landmarksList.length > 1 ? (leftIndex === 0 ? 1 : 0) : leftIndex;
        }

        const leftLandmarks = leftIndex >= 0 ? landmarksList[leftIndex] : null;
        const primaryLandmarks =
          landmarksList[primaryIndex] || landmarksList[0];

        if (leftLandmarks) {
          const leftMetrics = measureHand(leftLandmarks, dt, "left");
          smoothValue("leftHandPresent", 1, 0.28);
          smoothValue("leftX", leftMetrics.x);
          smoothValue("leftY", leftMetrics.y);
          smoothValue("leftOpenness", leftMetrics.openness);
          smoothValue("leftMovement", leftMetrics.movement);
          smoothValue("leftStillness", leftMetrics.stillness);
        } else {
          smoothValue("leftHandPresent", 0, 0.08);
          smoothValue("leftMovement", 0, 0.14);
          smoothValue("leftStillness", 0, 0.12);
          lastHandCenters.left = null;
        }

        if (primaryLandmarks)
          applyHandMetrics(measureHand(primaryLandmarks, dt, "primary"));
        else decayHandMetrics();

        return { primaryLandmarks, leftLandmarks };
      }

      function processHandTracking(nowMs, dt) {
        if (!handLandmarker || !webcam.videoWidth) return;
        if (webcam.currentTime === lastWebcamTime) return;

        lastWebcamTime = webcam.currentTime;
        const result = handLandmarker.detectForVideo(webcam, nowMs);
        const { primaryLandmarks, leftLandmarks } = classifyHands(result, dt);
        latestHands.primary = primaryLandmarks;
        latestHands.left = leftLandmarks;
        updateTrailsAndParticles(primaryLandmarks, leftLandmarks, dt);
        drawDebugLandmarks(primaryLandmarks || leftLandmarks);
      }

      function pointToScreen(point) {
        // Mirror X so the cinematic interface behaves like a selfie mirror.
        return {
          x: (1 - point.x) * window.innerWidth,
          y: point.y * window.innerHeight,
        };
      }

      function getPalmPoint(landmarks) {
        if (!landmarks) return null;
        return pointToScreen(
          averagePoints([
            landmarks[0],
            landmarks[5],
            landmarks[9],
            landmarks[17],
          ]),
        );
      }

      function addTrail(role, point, energy, now) {
        if (!point) return;
        handTrails[role].push({
          x: point.x,
          y: point.y,
          life: 1,
          energy,
          born: now,
        });
        if (handTrails[role].length > 48) handTrails[role].shift();
      }

      function updateTrailsAndParticles(primaryLandmarks, leftLandmarks, dt) {
        const now = performance.now();
        const leftPalm = getPalmPoint(leftLandmarks);
        const primaryPalm = getPalmPoint(primaryLandmarks);

        if (leftPalm) {
          addTrail(
            "left",
            leftPalm,
            smoothed.leftOpenness + smoothed.score,
            now,
          );
          [4, 8, 12].forEach((i) =>
            addTrail(
              "left",
              pointToScreen(leftLandmarks[i]),
              smoothed.leftMovement,
              now,
            ),
          );
        }
        if (primaryPalm) {
          addTrail(
            "primary",
            primaryPalm,
            smoothed.openness + smoothed.chaos,
            now,
          );
          [4, 8, 12].forEach((i) =>
            addTrail(
              "primary",
              pointToScreen(primaryLandmarks[i]),
              smoothed.movement,
              now,
            ),
          );
        }

        ["left", "primary"].forEach((role) => {
          handTrails[role].forEach((p) => (p.life -= dt * 0.72));
          handTrails[role] = handTrails[role].filter((p) => p.life > 0);
        });

        const burstEnergy =
          Math.max(smoothed.chaos, smoothed.score) * 0.2 +
          smoothed.movement * 0.28 +
          smoothed.leftMovement * 0.22;
        const spawnPoint = primaryPalm || leftPalm;
        if (spawnPoint && Math.random() < burstEnergy) {
          const amount = currentStage.includes("Blur") ? 3 : 1;
          for (let i = 0; i < amount; i++) {
            particles.push({
              x: spawnPoint.x + randomRange(-18, 18),
              y: spawnPoint.y + randomRange(-18, 18),
              vx: randomRange(-0.35, 0.35),
              vy: randomRange(-0.45, 0.2),
              life: randomRange(0.35, 0.9),
              size: randomRange(1, 3.2),
            });
          }
        }

        particles.forEach((p) => {
          p.x += p.vx * 60 * dt;
          p.y += p.vy * 60 * dt;
          p.life -= dt * 0.65;
        });
        while (particles.length > 180) particles.shift();
        for (let i = particles.length - 1; i >= 0; i--) {
          if (particles[i].life <= 0) particles.splice(i, 1);
        }
      }

      function stagePalette(stageKey) {
        if (stageKey === "stage3") {
          return {
            bg: "rgba(120, 160, 120, ",
            right: "rgba(170, 220, 160, ",
            left: "rgba(190, 210, 255, ",
            core: "rgba(160, 210, 170, ",
          };
        }
        if (stageKey === "stage2") {
          return {
            bg: "rgba(215, 31, 39, ",
            right: "rgba(255, 70, 82, ",
            left: "rgba(190, 170, 255, ",
            core: "rgba(255, 245, 235, ",
          };
        }
        return {
          bg: "rgba(215, 31, 39, ",
          right: "rgba(255, 90, 82, ",
          left: "rgba(160, 190, 255, ",
          core: "rgba(215, 31, 39, ",
        };
      }

      function drawGlowCircle(
        ctx,
        x,
        y,
        radius,
        color,
        alpha,
        lineWidth = 1.2,
      ) {
        ctx.save();
        ctx.shadowBlur = radius * 0.8;
        ctx.shadowColor = color + Math.min(alpha * 0.9, 0.9) + ")";
        ctx.strokeStyle = color + alpha + ")";
        ctx.lineWidth = lineWidth;
        ctx.beginPath();
        ctx.arc(x, y, radius, 0, Math.PI * 2);
        ctx.stroke();
        ctx.restore();
      }

      function drawHandConstellation(landmarks, role, stageKey) {
        if (!landmarks) return;
        const ctx = cinematicCtx;
        const palette = stagePalette(stageKey);
        const color = role === "left" ? palette.left : palette.right;
        const roleEnergy =
          role === "left"
            ? smoothed.score
            : Math.max(smoothed.outer, smoothed.chaos, smoothed.garden);
        const motion =
          role === "left" ? smoothed.leftMovement : smoothed.movement;
        const palm = getPalmPoint(landmarks);
        if (!palm) return;

        ctx.save();
        ctx.globalCompositeOperation = "screen";

        // Hand connection lines.
        ctx.lineCap = "round";
        ctx.lineJoin = "round";
        ctx.lineWidth = 1 + roleEnergy * 1.8;
        ctx.strokeStyle = color + (0.18 + roleEnergy * 0.34) + ")";
        for (const connection of HandLandmarker.HAND_CONNECTIONS) {
          const a = connection.start ?? connection[0];
          const b = connection.end ?? connection[1];
          const pa = pointToScreen(landmarks[a]);
          const pb = pointToScreen(landmarks[b]);
          ctx.beginPath();
          ctx.moveTo(pa.x, pa.y);
          ctx.lineTo(pb.x, pb.y);
          ctx.stroke();
        }

        // Landmarks.
      // Landmarks / fingertip tracking blobs.
landmarks.forEach((lm, i) => {
  const p = pointToScreen(lm);
  const fingertip = [4, 8, 12, 16, 20].includes(i);

  ctx.save();
  ctx.globalCompositeOperation = "screen";

  if (fingertip) {
    const size = 13 + roleEnergy * 18;
    const pulse =
      Math.sin(performance.now() * 0.006 + i * 0.7) * 0.5 + 0.5;

    // soft tracking glow
    ctx.shadowBlur = 22 + roleEnergy * 28;
    ctx.shadowColor = color + "0.85)";
    ctx.fillStyle = color + (0.16 + roleEnergy * 0.16) + ")";
    ctx.fillRect(
      p.x - size * 0.55,
      p.y - size * 0.55,
      size * 1.1,
      size * 1.1
    );

    // sharp tracking square outline
    ctx.shadowBlur = 0;
    ctx.strokeStyle = color + (0.72 + pulse * 0.22) + ")";
    ctx.lineWidth = 1.2 + roleEnergy * 1.4;
    ctx.strokeRect(
      p.x - size / 2,
      p.y - size / 2,
      size,
      size
    );

    // tiny centre point
    ctx.fillStyle = "rgba(255,255,255,0.72)";
    ctx.fillRect(p.x - 1.2, p.y - 1.2, 2.4, 2.4);
  } else {
    // smaller non-fingertip points
    const r = 1.2 + roleEnergy * 1.2;
    ctx.shadowBlur = 8;
    ctx.shadowColor = color + "0.45)";
    ctx.fillStyle = color + "0.28)";
    ctx.beginPath();
    ctx.arc(p.x, p.y, r, 0, Math.PI * 2);
    ctx.fill();
  }

  ctx.restore();
});

        // Palm aura ring.
        const baseR = role === "left" ? 42 : 34;
        const pulse =
          Math.sin(performance.now() * 0.003 + (role === "left" ? 0 : 1.7)) *
            0.5 +
          0.5;
        drawGlowCircle(
          ctx,
          palm.x,
          palm.y,
          baseR + pulse * 18 + roleEnergy * 38,
          color,
          0.18 + roleEnergy * 0.24,
          1.4,
        );
        drawGlowCircle(
          ctx,
          palm.x,
          palm.y,
          baseR * 0.48 + roleEnergy * 18,
          color,
          0.32 + roleEnergy * 0.25,
          1.1,
        );

        // Labels.
        ctx.shadowBlur = 10;
        ctx.fillStyle = color + "0.62)";
        ctx.font = "700 11px Inter, system-ui, sans-serif";
        ctx.letterSpacing = "2px";
        ctx.textAlign = "center";
        ctx.fillText(
          role === "left" ? "SCORE" : "WORLD",
          palm.x,
          palm.y - baseR - 34,
        );

        // Gesture value arc.
        const value =
          role === "left" ? smoothed.leftOpenness : smoothed.openness;
        ctx.strokeStyle = color + "0.5)";
        ctx.lineWidth = 3;
        ctx.beginPath();
        ctx.arc(
          palm.x,
          palm.y,
          baseR + 26,
          -Math.PI * 0.85,
          -Math.PI * 0.85 + Math.PI * 1.7 * value,
        );
        ctx.stroke();

        if (motion > 0.12) {
          drawGlowCircle(
            ctx,
            palm.x,
            palm.y,
            baseR + 40 + motion * 22,
            color,
            0.08 + motion * 0.18,
            0.8,
          );
        }

        ctx.restore();
      }

      function drawTrails(stageKey) {
        const ctx = cinematicCtx;
        const palette = stagePalette(stageKey);
        ctx.save();
        ctx.globalCompositeOperation = "screen";
        [
          ["left", palette.left],
          ["primary", palette.right],
        ].forEach(([role, color]) => {
          const trail = handTrails[role];
          for (let i = 1; i < trail.length; i++) {
            const a = trail[i - 1];
            const b = trail[i];
            const alpha =
              Math.min(a.life, b.life) * (role === "left" ? 0.18 : 0.24);
            ctx.strokeStyle = color + alpha + ")";
            ctx.lineWidth = (role === "left" ? 1.6 : 1.2) + b.energy * 2.2;
            ctx.beginPath();
            ctx.moveTo(a.x, a.y);
            ctx.lineTo(b.x, b.y);
            ctx.stroke();
          }
        });
        particles.forEach((p) => {
          ctx.fillStyle = palette.core + Math.max(0, p.life * 0.22) + ")";
          ctx.beginPath();
          ctx.arc(p.x, p.y, p.size, 0, Math.PI * 2);
          ctx.fill();
        });
        ctx.restore();
      }

      function drawCentralSoundCore(stage) {
        const ctx = cinematicCtx;
        const w = window.innerWidth;
        const h = window.innerHeight;
        const palette = stagePalette(stage.key);
        const energy = clamp(
          (smoothed.outer +
            smoothed.inner +
            smoothed.chaos +
            smoothed.garden +
            smoothed.score) /
            3.2,
        );
        const cx = w * 0.5;
        const cy = h * 0.52;
        const now = performance.now() * 0.001;
        const base = 64 + energy * 72;

        ctx.save();
        ctx.globalCompositeOperation = "screen";

        // Soft core glow.
        const grad = ctx.createRadialGradient(cx, cy, 4, cx, cy, base * 2.2);
        grad.addColorStop(0, palette.core + (0.14 + energy * 0.12) + ")");
        grad.addColorStop(0.45, palette.core + "0.055)");
        grad.addColorStop(1, "rgba(0,0,0,0)");
        ctx.fillStyle = grad;
        ctx.beginPath();
        ctx.arc(cx, cy, base * 2.2, 0, Math.PI * 2);
        ctx.fill();

        // Wave rings.
        for (let i = 0; i < 4; i++) {
          const r =
            base +
            i * 26 +
            Math.sin(now * (1.1 + i * 0.18) + i) * (6 + energy * 10);
          ctx.strokeStyle =
            palette.core + (0.09 + energy * 0.08 - i * 0.014) + ")";
          ctx.lineWidth = 1.1;
          ctx.beginPath();
          for (let a = 0; a <= Math.PI * 2 + 0.05; a += 0.08) {
            const warp =
              Math.sin(a * 5 + now * (stage.key === "stage2" ? 2.8 : 0.8)) *
              (stage.key === "stage2" ? 9 * smoothed.chaos : 3 * energy);
            const x = cx + Math.cos(a) * (r + warp);
            const y = cy + Math.sin(a) * (r + warp);
            if (a === 0) ctx.moveTo(x, y);
            else ctx.lineTo(x, y);
          }
          ctx.stroke();
        }

        ctx.font = "700 10px Inter, system-ui, sans-serif";
        ctx.textAlign = "center";
        ctx.fillStyle = "rgba(255,255,255,0.42)";
        ctx.fillText("ROOM ENERGY", cx, cy + base + 48);
        ctx.restore();
      }

      function drawHandBridge(stageKey) {
        const leftPalm = getPalmPoint(latestHands.left);
        const primaryPalm = getPalmPoint(latestHands.primary);
        if (!leftPalm || !primaryPalm) return;
        const ctx = cinematicCtx;
        const palette = stagePalette(stageKey);
        const spread = clamp(
          distance(leftPalm, primaryPalm) /
            Math.max(window.innerWidth * 0.65, 1),
        );
        const energy = clamp(
          spread * 0.6 + smoothed.score * 0.28 + smoothed.chaos * 0.24,
        );

        ctx.save();
        ctx.globalCompositeOperation = "screen";
        ctx.shadowBlur = 28;
        ctx.shadowColor = palette.core + "0.6)";
        ctx.strokeStyle = palette.core + (0.12 + energy * 0.24) + ")";
        ctx.lineWidth = 1 + energy * 4;
        ctx.setLineDash([12, 18]);
        ctx.lineDashOffset = -performance.now() * 0.018;
        ctx.beginPath();
        const midX = (leftPalm.x + primaryPalm.x) / 2;
        const midY =
          (leftPalm.y + primaryPalm.y) / 2 -
          60 * Math.sin(performance.now() * 0.0012);
        ctx.moveTo(leftPalm.x, leftPalm.y);
        ctx.quadraticCurveTo(midX, midY, primaryPalm.x, primaryPalm.y);
        ctx.stroke();
        ctx.setLineDash([]);
        ctx.restore();
      }

      function drawCinematicMeters(stage) {
        const ctx = cinematicCtx;
        const meters = [
          ["CITY", smoothed.outer],
          ["SELF", smoothed.inner],
          ["RUPTURE", smoothed.chaos],
          ["GARDEN", smoothed.garden],
          ["SCORE", smoothed.score],
        ];
        const w = window.innerWidth;
        const y = window.innerHeight - 92;
        const totalW = Math.min(720, w - 80);
        const startX = (w - totalW) / 2;
        const gap = 18;
        const barW = (totalW - gap * (meters.length - 1)) / meters.length;
        const palette = stagePalette(stage.key);

        ctx.save();
        ctx.font = "700 9px Inter, system-ui, sans-serif";
        ctx.textAlign = "left";
        meters.forEach(([label, value], i) => {
          const x = startX + i * (barW + gap);
          ctx.fillStyle = "rgba(255,255,255,0.35)";
          ctx.fillText(label, x, y - 10);
          ctx.fillStyle = "rgba(255,255,255,0.09)";
          ctx.fillRect(x, y, barW, 3);
          ctx.shadowBlur = 14;
          ctx.shadowColor = palette.core + "0.5)";
          ctx.fillStyle = palette.core + (0.32 + value * 0.42) + ")";
          ctx.fillRect(x, y, barW * clamp(value), 3);
          ctx.shadowBlur = 0;
        });
        ctx.restore();
      }

      function formatTime(seconds) {
        const m = Math.floor(seconds / 60)
          .toString()
          .padStart(2, "0");
        const s = Math.floor(seconds % 60)
          .toString()
          .padStart(2, "0");
        return `${m}:${s}`;
      }

      function drawCinematicInterface(stage) {
        const ctx = cinematicCtx;
        const w = window.innerWidth;
        const h = window.innerHeight;
        const palette = stagePalette(stage.key);

        ctx.clearRect(0, 0, w, h);
        ctx.save();
        ctx.globalCompositeOperation = "source-over";

        // Film haze and stage tint.
        const bg = ctx.createRadialGradient(
          w * 0.5,
          h * 0.46,
          40,
          w * 0.5,
          h * 0.5,
          Math.max(w, h) * 0.72,
        );
        bg.addColorStop(0, palette.bg + "0.065)");
        bg.addColorStop(0.45, "rgba(255,255,255,0.015)");
        bg.addColorStop(1, "rgba(0,0,0,0)");
        ctx.fillStyle = bg;
        ctx.fillRect(0, 0, w, h);

        // Thin scan atmosphere.
        ctx.globalAlpha = stage.key === "stage2" ? 0.14 : 0.08;
        ctx.strokeStyle = "rgba(255,255,255,0.09)";
        ctx.lineWidth = 1;
        for (let y = 0; y < h; y += 38) {
          ctx.beginPath();
          ctx.moveTo(0, y + Math.sin(performance.now() * 0.001 + y * 0.01) * 3);
          ctx.lineTo(w, y + Math.sin(performance.now() * 0.001 + y * 0.01) * 3);
          ctx.stroke();
        }
        ctx.globalAlpha = 1;
        ctx.restore();

        drawCentralSoundCore(stage);
        drawTrails(stage.key);
        drawHandBridge(stage.key);
        drawHandConstellation(latestHands.left, "left", stage.key);
        drawHandConstellation(latestHands.primary, "primary", stage.key);
        drawCinematicMeters(stage);

        // Stage/time readout on canvas for cinematic mode.
        ctx.save();
        ctx.fillStyle = "rgba(255,255,255,0.66)";
        ctx.font = "900 18px Inter, system-ui, sans-serif";
        ctx.textAlign = "right";
        ctx.fillText(`${stage.label.toUpperCase()}`, w - 28, 34);
        ctx.fillStyle = "rgba(215,31,39,0.64)";
        ctx.font = "800 11px Inter, system-ui, sans-serif";
        ctx.fillText(`${formatTime(stage.time)} / LEFT SCORE · RIGHT WORLD · SPACE PANNING`, w - 28, 56);
        ctx.restore();
      }

      function getStage() {
        const time = getTimelineTime();

        if (time < CONFIG.stage1EndSeconds) {
          return { key: "stage1", label: "I. Sensory Overload", time };
        }

        if (time < CONFIG.stage2EndSeconds) {
          return { key: "stage2", label: "II. Blur of the Inner Voice", time };
        }

        return {
          key: "stage3",
          label: "III. Garden / Reclaiming the Centre",
          time,
        };
      }

      function setHint(stageKey) {
        if (stageKey === "stage1") {
          interactionHint.textContent =
            "Right hand moves the world. Left hand moves the score. Spread both hands to widen the room.";
        } else if (stageKey === "stage2") {
          interactionHint.textContent =
            "Pinch through the noise. The rupture may move on its own; use both hands to widen or compress it.";
        } else {
          interactionHint.textContent =
            "Plant the right hand. Let the garden breathe. Move the left hand to shift the score gently.";
        }
      }

      function updateStageAudio(stage) {
        if (!audioGraph) return;

        const {
          masterGain,

          outerBus,
          outerFilter,
          outerPan,

          innerBus,
          innerFilter,

          chaosBus,
          chaosFilter,
          chaosPan,

          lowBus,
          lowFilter,

          gardenBus,
          gardenFilter,
          gardenPan,

          scoreBus,
          scoreFilter,
          scorePan,

          feedback,
          echoWet,
          delay,

          stems,
        } = audioGraph;

        const hand = smoothed.handPresent;

        let outerLevel = 0.35;
        let innerLevel = 0.08;
        let chaosLevel = 0.0;
        let lowLevel = 0.0;
        let gardenLevel = 0.0;
        let scoreLevel = 0.0;

        let blurAmount = 0.02;
        let outerFilterHz = 14000;
        let innerFilterHz = 12000;
        let chaosFilterHz = 900;
        let lowFilterHz = 120;
        let gardenFilterHz = 9000;
        let scoreFilterHz = 9000;

        let pan = 0;
        let chaosPanValue = 0;
        let gardenPanValue = 0;
        let scorePanValue = 0;

        let cityGain = CONFIG.audio.cityBase;
        let voicesGain = CONFIG.audio.voicesBase;
        let breathGain = CONFIG.audio.breathBase;
        let toneGain = CONFIG.audio.toneBase;

        let glitchGain = 0;
        let rumbleGain = 0;
        let whisperGain = 0;
        let metalGain = 0;
        let pulseGain = 0;

        let gardenGain = 0;
        let birdsGain = 0;
        let windGain = 0;
        let waterGain = 0;

        let scene1ScoreGain = 0;
        let scene2ScoreGain = 0;
        let scene3ScoreGain = 0;

        const t = stage.time;

        const stage1Progress = clamp(t / CONFIG.stage1EndSeconds);
        const stage2Progress = clamp(
          (t - CONFIG.stage1EndSeconds) /
            (CONFIG.stage2EndSeconds - CONFIG.stage1EndSeconds),
        );
        const stage3Progress = clamp(
          (t - CONFIG.stage2EndSeconds) /
            Math.max(60, CONFIG.stage2EndSeconds - CONFIG.stage1EndSeconds),
        );

        const overloadCurve = Math.sin(stage1Progress * Math.PI * 0.5);
        const blurCurve = Math.sin(stage2Progress * Math.PI);
        const gardenArrival = Math.sin(stage3Progress * Math.PI * 0.5);

        const leftActive = smoothed.leftHandPresent;
        const leftOpen = clamp(smoothed.leftOpenness * leftActive);
        const leftClosed = clamp((1 - smoothed.leftOpenness) * leftActive);
        const leftHeight = clamp((1 - smoothed.leftY) * leftActive);
        const leftMotion = smoothed.leftMovement * leftActive;
        const scoreMaster = clamp(
          0.52 + leftOpen * 0.56 + leftMotion * 0.24 - leftClosed * 0.12,
          0.22,
          1.25,
        );

        // SPACE / PANNING
        // Right hand = moves the world sound.
        // Left hand = moves the score.
        // Hands far apart = wider room.
        // Hands close together = compressed / internal room.
        const rightPan = clamp((smoothed.x - 0.5) * 2 * hand, -1, 1);
        const leftPan = clamp((smoothed.leftX - 0.5) * 2 * leftActive, -1, 1);
        const bothHands = leftActive * hand;
        const rawHandDistance = Math.abs(smoothed.leftX - smoothed.x);
        const handSpread = bothHands
          ? clamp((rawHandDistance - 0.12) / 0.46)
          : 0.46;

        // spaceWidth is the clearest mapping:
        // 0.38 = compressed inward, 1.18 = wide room.
        const spaceWidth = lerp(0.38, 1.18, handSpread);
        const roomLift = 0.9 + handSpread * 0.18;
        const bothStill =
          bothHands * smoothed.leftStillness * smoothed.stillness;

        if (stage.key === "stage1") {
          // Scene I gesture logic:
          // Open palm = the public city floods in.
          // Closed hand = the body tries to protect the self, so the city compresses and breath appears.
          const palmOpen = clamp(smoothed.openness * hand);
          const palmClosed = clamp((1 - smoothed.openness) * hand);
          const motionLift = smoothed.movement * 0.42 * hand;

          outerLevel = clamp(
            0.24 +
              overloadCurve * 0.22 +
              palmOpen * 0.62 +
              motionLift * 0.28 -
              palmClosed * 0.16,
            0.08,
            CONFIG.effect.overloadMaxOuter,
          );

          innerLevel = clamp(
            0.06 + palmClosed * 0.22 - palmOpen * 0.05 - motionLift * 0.03,
            0.035,
            0.28,
          );

          chaosLevel = clamp(
            0.025 +
              overloadCurve * 0.12 +
              palmOpen * 0.36 +
              motionLift * 0.34 -
              palmClosed * 0.08,
            0.01,
            0.72,
          );

          lowLevel = clamp(
            0.035 + overloadCurve * 0.14 + palmOpen * 0.16 + motionLift * 0.08,
            0,
            0.34,
          );

          gardenLevel = 0;

          blurAmount = clamp(
            0.025 +
              palmOpen * 0.24 +
              motionLift * 0.24 +
              overloadCurve * 0.06 -
              palmClosed * 0.06,
            0.015,
            0.36,
          );

          // Closed hand muffles the city, open hand makes it brighter and more exposed.
          outerFilterHz = lerp(2600, 17500, palmOpen);
          chaosFilterHz = lerp(
            550,
            3300,
            clamp(palmOpen + smoothed.movement * 0.45),
          );
          lowFilterHz = lerp(80, 150, overloadCurve);
          gardenFilterHz = 900;

          pan = rightPan * 0.95;
          chaosPanValue =
            rightPan * 0.55 + Math.sin(audioContext.currentTime * 0.42) * 0.08;
          gardenPanValue = 0;

          cityGain =
            CONFIG.audio.cityBase *
            (0.55 + palmOpen * 0.75 + overloadCurve * 0.25 + motionLift * 0.12);
          voicesGain =
            CONFIG.audio.voicesBase *
            (0.38 + palmOpen * 1.35 + overloadCurve * 0.52 - palmClosed * 0.2);

          breathGain = CONFIG.audio.breathBase * (0.5 + palmClosed * 2.4);
          toneGain = CONFIG.audio.toneBase * (0.25 + palmClosed * 1.6);

          glitchGain = chaosLevel * (0.28 + palmOpen * 0.32);
          metalGain = chaosLevel * (0.14 + palmOpen * 0.34);
          pulseGain = lowLevel * (0.22 + palmClosed * 0.42 + palmOpen * 0.16);
          rumbleGain = lowLevel * (0.45 + palmOpen * 0.22);
          whisperGain = palmClosed * 0.14 + chaosLevel * 0.08;

          gardenGain = 0;
          birdsGain = 0;
          windGain = 0;
          waterGain = 0;

          scoreLevel =
            scoreMaster * (0.58 + overloadCurve * 0.34 + palmOpen * 0.08);
          scoreFilterHz = lerp(
            2600,
            15500,
            clamp(leftHeight + leftOpen * 0.45),
          );
          scorePanValue = leftPan * 0.55;
          scene1ScoreGain = scoreLevel * 1.08;
          scene2ScoreGain = 0;
          scene3ScoreGain = 0;
        }

        if (stage.key === "stage2") {
          const pinchClosed = 1 - smoothed.pinch;
          const reveal = pinchClosed * hand;

          const motionChaos = smoothed.movement * 0.36 * hand;
          const openChaos = smoothed.openness * 0.28 * hand;
          const smear = clamp(blurCurve + motionChaos + openChaos, 0, 1);

          // Garden appears here only as a faint memory underneath the rupture.
          const gardenMemory = blurCurve * 0.08;

          outerLevel = clamp(
            0.86 - reveal * 0.34 + motionChaos * 0.2,
            0.28,
            1.05,
          );
          innerLevel = clamp(
            0.12 + reveal * 0.68 + blurCurve * 0.08,
            0.1,
            0.82,
          );
          // Stage II is the collapse point: rupture becomes aggressive and physical.
          chaosLevel = clamp(
            0.34 + blurCurve * 0.72 + motionChaos * 1.15 + openChaos * 0.75,
            0.18,
            1.0,
          );
          lowLevel = clamp(
            0.22 + blurCurve * 0.52 + motionChaos * 0.3,
            0.14,
            0.82,
          );
          gardenLevel = gardenMemory;

          blurAmount = clamp(0.28 + smear * 0.56 - reveal * 0.14, 0.16, 0.76);

          outerFilterHz = lerp(
            420,
            4200,
            clamp(1 - smear * 0.72 + reveal * 0.45),
          );
          innerFilterHz = lerp(1200, 12000, reveal);
          chaosFilterHz = lerp(240, 5200, smear);
          lowFilterHz = lerp(58, 155, blurCurve);
          gardenFilterHz = lerp(900, 2600, blurCurve);

          pan = rightPan * 0.72;
          const ruptureAutoPan =
            Math.sin(audioContext.currentTime * (1.2 + smear * 4.2)) *
            (0.42 + smear * 0.38);
          chaosPanValue = clamp(rightPan * 0.32 + ruptureAutoPan, -1, 1);
          gardenPanValue = Math.sin(audioContext.currentTime * 0.06) * 0.08;

          cityGain = CONFIG.audio.cityBase + 0.05;
          voicesGain = CONFIG.audio.voicesBase + smear * 0.3 - reveal * 0.16;

          breathGain = CONFIG.audio.breathBase + reveal * 0.62;
          toneGain = CONFIG.audio.toneBase + reveal * 0.12;

          glitchGain = chaosLevel * 0.78;
          metalGain = chaosLevel * 0.42;
          whisperGain = clamp(0.18 + blurCurve * 0.58 + reveal * 0.25, 0, 0.86);
          pulseGain = lowLevel * 0.58;
          rumbleGain = lowLevel * 0.86;

          gardenGain = gardenLevel * 0.5;
          birdsGain = 0;
          windGain = gardenLevel * 0.35;
          waterGain = gardenLevel * 0.12;

          scoreLevel =
            scoreMaster *
            (0.7 + blurCurve * 0.48 + leftMotion * 0.22 + smear * 0.08);
          scoreFilterHz = lerp(
            1200,
            12500,
            clamp(leftHeight * 0.55 + reveal * 0.45 + leftOpen * 0.18),
          );
          scorePanValue =
            leftPan * 0.48 +
            Math.sin(audioContext.currentTime * (0.2 + blurCurve * 0.8)) * 0.12;
          scene1ScoreGain = 0;
          scene2ScoreGain = scoreLevel * 1.12;
          scene3ScoreGain = gardenMemory * 0.16;
        }

        if (stage.key === "stage3") {
          // Scene III narrative gesture logic:
          // A low, still hand near the centre feels like "planting" yourself back into the body.
          // A slowly opened palm lets the garden breathe outward.
          // Fast movement becomes a memory of the city trying to return.
          const residualMotion = smoothed.movement * hand;
          const centred = smoothed.centered * hand;
          const still = smoothed.stillness * hand;
          const groundedY = clamp((smoothed.y - 0.42) / 0.36) * hand; // lower hand = more grounded
          const planting = clamp(centred * still * (0.45 + groundedY * 0.55));
          const openingLeaves = clamp(smoothed.openness * still * hand);
          const cityMemory = clamp(residualMotion * (1 - planting));

          outerLevel = clamp(
            0.035 + cityMemory * 0.16 - planting * 0.025,
            0.015,
            0.22,
          );
          innerLevel = clamp(
            0.32 + planting * 0.42 + openingLeaves * 0.14,
            0.28,
            CONFIG.effect.calmMaxInner,
          );
          chaosLevel = clamp(
            0.025 + cityMemory * 0.18 - planting * 0.02,
            0,
            0.22,
          );
          lowLevel = clamp(
            0.025 + cityMemory * 0.07 - planting * 0.015,
            0,
            0.1,
          );

          gardenLevel = clamp(
            0.32 + gardenArrival * 0.5 + planting * 0.36 + openingLeaves * 0.16,
            0,
            CONFIG.effect.gardenMax,
          );

          blurAmount = clamp(
            0.055 + cityMemory * 0.14 - planting * 0.04,
            0.01,
            0.18,
          );

          outerFilterHz = lerp(3200, 12000, planting);
          innerFilterHz = lerp(5200, 14500, planting);
          chaosFilterHz = lerp(700, 1800, cityMemory);
          lowFilterHz = lerp(95, 65, planting);
          gardenFilterHz = lerp(
            4200,
            15500,
            clamp(planting + openingLeaves * 0.4),
          );

          pan = lerp(rightPan * 0.34, 0, planting);
          chaosPanValue = lerp(
            rightPan * 0.16 + Math.sin(audioContext.currentTime * 0.42) * 0.18,
            0,
            planting,
          );
          gardenPanValue =
            rightPan * (0.12 + openingLeaves * 0.16) +
            Math.sin(audioContext.currentTime * 0.07) *
              (0.06 + openingLeaves * 0.12);

          // City becomes almost inaudible unless the hand becomes restless.
          cityGain = CONFIG.audio.cityBase * (0.018 + cityMemory * 0.22);
          voicesGain = CONFIG.audio.voicesBase * (0.004 + cityMemory * 0.07);

          breathGain = clamp(
            CONFIG.audio.breathBase + planting * 0.72 + still * 0.08,
            0,
            0.86,
          );
          toneGain = clamp(
            CONFIG.audio.toneBase + planting * 0.42 + openingLeaves * 0.12,
            0,
            0.56,
          );

          glitchGain = chaosLevel * 0.06;
          metalGain = chaosLevel * 0.02;
          whisperGain = chaosLevel * 0.05 + planting * 0.035;
          pulseGain = lowLevel * 0.1;
          rumbleGain = lowLevel * 0.12;

          gardenGain = gardenLevel * 1.0;
          birdsGain = gardenLevel * (0.2 + openingLeaves * 0.34);
          windGain = gardenLevel * (0.28 + openingLeaves * 0.46);
          waterGain = gardenLevel * (0.18 + planting * 0.12);

          scoreLevel = clamp(
            scoreMaster *
              (0.62 +
                gardenArrival * 0.34 +
                planting * 0.24 +
                openingLeaves * 0.12),
            0.26,
            1.0,
          );
          scoreFilterHz = lerp(
            3200,
            16500,
            clamp(leftHeight * 0.45 + openingLeaves * 0.55 + planting * 0.45),
          );
          scorePanValue =
            leftPan * 0.34 + Math.sin(audioContext.currentTime * 0.05) * 0.08;
          scene1ScoreGain = 0;
          scene2ScoreGain = 0;
          scene3ScoreGain = scoreLevel * 1.08;
        }

        // Apply the two-hand space control to every spatial layer.
        // Together = compressed. Apart = expanded.
        pan = clamp(pan * spaceWidth, -1, 1);
        chaosPanValue = clamp(chaosPanValue * spaceWidth, -1, 1);
        gardenPanValue = clamp(gardenPanValue * spaceWidth, -1, 1);
        scorePanValue = clamp(
          scorePanValue * lerp(0.55, 1.05, handSpread),
          -1,
          1,
        );

        // Stillness calms the room instead of leaving it constantly drifting.
        pan = lerp(pan, 0, bothStill * 0.28);
        chaosPanValue = lerp(chaosPanValue, 0, bothStill * 0.38);
        gardenPanValue = lerp(gardenPanValue, 0, bothStill * 0.24);
        scorePanValue = lerp(scorePanValue, 0, bothStill * 0.18);

        blurAmount = clamp(
          blurAmount + handSpread * 0.055 - bothStill * 0.035,
          0,
          0.82,
        );

        smoothValue("outer", clamp(outerLevel));
        smoothValue("inner", clamp(innerLevel));
        smoothValue("chaos", clamp(chaosLevel));
        smoothValue("blur", clamp(blurAmount));
        smoothValue("garden", clamp(gardenLevel));
        smoothValue("score", clamp(scoreLevel));

        ramp(masterGain.gain, CONFIG.audio.master * roomLift);

        ramp(outerBus.gain, outerLevel);
        ramp(innerBus.gain, innerLevel);
        ramp(chaosBus.gain, chaosLevel);
        ramp(lowBus.gain, lowLevel);
        ramp(gardenBus.gain, gardenLevel);
        ramp(scoreBus.gain, scoreLevel);

        ramp(outerFilter.frequency, outerFilterHz);
        ramp(innerFilter.frequency, innerFilterHz);
        ramp(chaosFilter.frequency, chaosFilterHz);
        ramp(lowFilter.frequency, lowFilterHz);
        ramp(gardenFilter.frequency, gardenFilterHz);
        ramp(scoreFilter.frequency, scoreFilterHz);

        ramp(outerPan.pan, pan);
        ramp(chaosPan.pan, chaosPanValue);
        ramp(gardenPan.pan, gardenPanValue);
        ramp(scorePan.pan, scorePanValue);

        ramp(delay.delayTime, lerp(0.06, 0.55, blurAmount));
        ramp(feedback.gain, clamp(blurAmount * 0.68, 0.02, 0.46));
        ramp(echoWet.gain, clamp(blurAmount * 0.9, 0.01, 0.62));

        ramp(stems.city.gain.gain, clamp(cityGain, 0, 1.2));
        ramp(stems.voices.gain.gain, clamp(voicesGain, 0, 1.2));
        ramp(stems.breath.gain.gain, clamp(breathGain, 0, 1.0));
        ramp(stems.tone.gain.gain, clamp(toneGain, 0, 0.8));

        ramp(stems.glitch.gain.gain, clamp(glitchGain, 0, 0.8));
        ramp(stems.rumble.gain.gain, clamp(rumbleGain, 0, 0.8));
        ramp(stems.whisper.gain.gain, clamp(whisperGain, 0, 0.8));
        ramp(stems.metal.gain.gain, clamp(metalGain, 0, 0.7));
        ramp(stems.pulse.gain.gain, clamp(pulseGain, 0, 0.7));

        ramp(stems.garden.gain.gain, clamp(gardenGain, 0, 0.9));
        ramp(stems.birds.gain.gain, clamp(birdsGain, 0, 0.45));
        ramp(stems.wind.gain.gain, clamp(windGain, 0, 0.6));
        ramp(stems.water.gain.gain, clamp(waterGain, 0, 0.4));

        ramp(stems.scene1Score.gain.gain, clamp(scene1ScoreGain, 0, 1.15));
        ramp(stems.scene2Score.gain.gain, clamp(scene2ScoreGain, 0, 1.2));
        ramp(stems.scene3Score.gain.gain, clamp(scene3ScoreGain, 0, 1.15));

        setMeters(
          smoothed.outer,
          smoothed.inner,
          smoothed.chaos,
          smoothed.blur,
          smoothed.garden,
          smoothed.score,
        );
      }

      function triggerChaosBursts(stage) {
        if (!audioContext || !audioGraph || !appStarted || isPaused) return;

        const now = performance.now();
        if (now - lastChaosBurstAt < nextChaosBurstDelay) return;

        const movementEnergy = smoothed.movement * smoothed.handPresent;
        const opennessEnergy = smoothed.openness * smoothed.handPresent;

        let chance = 0.02;

        if (stage.key === "stage1") {
          chance = 0.08 + movementEnergy * 0.25 + opennessEnergy * 0.12;
          nextChaosBurstDelay = randomRange(1600, 3600);
        }

        if (stage.key === "stage2") {
          chance = 0.34 + movementEnergy * 0.55 + opennessEnergy * 0.28;
          nextChaosBurstDelay = randomRange(360, 1250);
        }

        if (stage.key === "stage3") {
          chance = 0.025 + movementEnergy * 0.08;
          nextChaosBurstDelay = randomRange(3200, 6800);
        }

        if (Math.random() > chance) {
          lastChaosBurstAt = now;
          return;
        }

        const burstChoices =
          stage.key === "stage2"
            ? ["glitch", "metal", "pulse", "whisper"]
            : stage.key === "stage1"
              ? ["glitch", "pulse", "metal"]
              : ["whisper", "pulse"];

        const chosen =
          burstChoices[Math.floor(Math.random() * burstChoices.length)];
        const stem = audioGraph.stems[chosen];
        if (!stem) return;

        const original = Math.max(stem.gain.gain.value, 0.001);

        const peak =
          chosen === "metal"
            ? randomRange(0.25, 0.58)
            : chosen === "pulse"
              ? randomRange(0.18, 0.48)
              : chosen === "whisper"
                ? randomRange(0.14, 0.38)
                : randomRange(0.18, 0.55);

        const attack = randomRange(0.015, 0.08);
        const release =
          stage.key === "stage3"
            ? randomRange(0.42, 1.1)
            : randomRange(0.18, 0.7);
        const t = audioContext.currentTime;

        stem.gain.gain.cancelScheduledValues(t);
        stem.gain.gain.setValueAtTime(original, t);
        stem.gain.gain.linearRampToValueAtTime(peak, t + attack);
        stem.gain.gain.exponentialRampToValueAtTime(
          0.001,
          t + attack + release,
        );

        lastChaosBurstAt = now;
      }

      function updateDebugReadout(stage) {
        if (!debugVisible) return;

        debugReadout.innerHTML = `
          <strong>${stage.label}</strong><br>
          Time: ${stage.time.toFixed(1)}s<br>
          Hand present: ${Math.round(smoothed.handPresent * 100)}%<br>
          Palm X / Y: ${smoothed.x.toFixed(2)} / ${smoothed.y.toFixed(2)}<br>
          Openness: ${smoothed.openness.toFixed(2)}<br>
          Pinch open: ${smoothed.pinch.toFixed(2)}<br>
          Movement: ${smoothed.movement.toFixed(2)}<br>
          Centred: ${smoothed.centered.toFixed(2)}<br>
          Stillness: ${smoothed.stillness.toFixed(2)}<br>
          City: ${smoothed.outer.toFixed(2)}<br>
          Self: ${smoothed.inner.toFixed(2)}<br>
          Rupture: ${smoothed.chaos.toFixed(2)}<br>
          Echo: ${smoothed.blur.toFixed(2)}<br>
          Garden: ${smoothed.garden.toFixed(2)}<br>
          Score: ${smoothed.score.toFixed(2)}<br>
          Left score hand: ${Math.round(smoothed.leftHandPresent * 100)}% / open ${smoothed.leftOpenness.toFixed(2)}
        `;
      }

      function toggleDebug() {
        wakeUi();
        debugVisible = !debugVisible;
        debugPanel.classList.toggle("visible", debugVisible);
        debugToggle.textContent = `Debug: ${debugVisible ? "On" : "Off"}`;

        if (!debugVisible) {
          handCtx.clearRect(0, 0, handCanvas.width, handCanvas.height);
        }
      }

      async function togglePause() {
        if (!appStarted) return;
        wakeUi();

        if (isPaused) {
          await resumeAudio();
        } else {
          pauseAllAudio();
        }
      }

      function jumpToStage(seconds) {
        if (!appStarted) return;
        wakeUi();
        setTimelineTime(seconds);
        currentStage = "";

        if (!isPaused) {
          timelineStartMs = performance.now() - seconds * 1000;
        }
      }

      debugToggle.addEventListener("click", toggleDebug);
      pauseButton.addEventListener("click", togglePause);
      stage1Button.addEventListener("click", () => jumpToStage(0));
      stage2Button.addEventListener("click", () =>
        jumpToStage(CONFIG.stage1EndSeconds),
      );
      stage3Button.addEventListener("click", () =>
        jumpToStage(CONFIG.stage2EndSeconds),
      );

      window.addEventListener("keydown", (event) => {
        const key = event.key.toLowerCase();

        if (key === "d") toggleDebug();
        if (key === "r") restartExperience();
        if (key === " ") {
          event.preventDefault();
          togglePause();
        }
        if (key === "1") jumpToStage(0);
        if (key === "2") jumpToStage(CONFIG.stage1EndSeconds);
        if (key === "3") jumpToStage(CONFIG.stage2EndSeconds);
      });

      function animationLoop(nowMs) {
        const dt = Math.min((nowMs - lastFrameMs) / 1000, 0.1);
        lastFrameMs = nowMs;

        if (appStarted) {
          processHandTracking(nowMs, dt);

          const stage = getStage();
          drawCinematicInterface(stage);

          if (currentStage !== stage.label) {
            currentStage = stage.label;
            stageLabel.textContent = stage.label;
            setHint(stage.key);
          }

          if (!isPaused) {
            updateStageAudio(stage);
            triggerChaosBursts(stage);
          }

          updateDebugReadout(stage);
        }

        requestAnimationFrame(animationLoop);
      }

      requestAnimationFrame(animationLoop);

      async function startExperience() {
        try {
          clearError();
          startButton.disabled = true;

          setBootStatus("Preparing hand tracking...");
          await setupHandTracking();

          setBootStatus("Start the three videos now. Sound begins in 3...");
          await new Promise((resolve) => setTimeout(resolve, 1000));

          setBootStatus("Sound begins in 2...");
          await new Promise((resolve) => setTimeout(resolve, 1000));

          setBootStatus("Sound begins in 1...");
          await new Promise((resolve) => setTimeout(resolve, 1000));

          setBootStatus("Starting sound system...");
          await startAudioOnly();

          appStarted = true;
          document.body.classList.add("started", "ui-awake");
          scheduleUiSleep();

          hud.classList.remove("quiet");
          stageLabel.textContent = "I. Sensory Overload";
          setHint("stage1");

          startOverlay.classList.add("hidden");
          setBootStatus("Running.");
        } catch (error) {
          console.error(error);
          startButton.disabled = false;
          setBootStatus("Could not start yet.");
          showError(
            "Startup failed. Open this through localhost or GitHub Pages, allow camera permission, and make sure all audio files exist in the audio folder.",
          );
        }
      }

      async function restartExperience() {
        if (!appStarted) return;
        wakeUi();

        try {
          pauseAllAudio();

          Object.values(audioEls).forEach((audioEl) => {
            audioEl.currentTime = 0;
          });

          lastChaosBurstAt = 0;
          nextChaosBurstDelay = 1800;
          pausedAtSeconds = 0;

          await startAudioOnly();

          currentStage = "";
          hud.classList.remove("quiet");
        } catch (error) {
          console.error(error);
          showError(
            "The sound system could not restart cleanly. Refresh the page and start again.",
          );
        }
      }

      startButton.addEventListener("click", startExperience);
      startButton.addEventListener("pointerdown", () => {
        if (!appStarted && !startButton.disabled)
          setBootStatus("Start command received...");
      });
      document.body.classList.add("js-ready");
      setBootStatus("Ready. Click Start Sound System.");
      restartButton.addEventListener("click", restartExperience);

      let uiSleepTimer = null;

      function wakeUi() {
        document.body.classList.add("ui-awake");
        scheduleUiSleep();
      }

      function scheduleUiSleep() {
        window.clearTimeout(uiSleepTimer);
        uiSleepTimer = window.setTimeout(() => {
          if (!debugVisible && appStarted) {
            document.body.classList.remove("ui-awake");
          }
        }, 4200);
      }

      ["pointermove", "mousemove", "touchstart", "keydown"].forEach(
        (eventName) => {
          window.addEventListener(eventName, wakeUi, { passive: true });
        },
      );

      Object.entries(audioEls).forEach(([name, audioEl]) => {
        audioEl.addEventListener("error", () => {
          showError(
            `Missing audio file for ${name}. Check audio/${name}.mp3 or update the file path in the HTML.`,
          );
        });
      });