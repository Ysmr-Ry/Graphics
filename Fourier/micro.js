navigator.getUserMedia = navigator.getUserMedia || navigator.webkitGetUserMedia || navigator.mozGetUserMedia || navigator.msGetUserMedia;

var len = 256;
dat = new Float32Array(len);

navigator.getUserMedia(
  { audio: true },
  stream => {
    document.querySelector('audio').src = URL.createObjectURL(stream);
    var audioCtx = new AudioContext();
    var analyser = audioCtx.createAnalyser();
    analyser.fftSize = len;
    analyser.minDecibels = -90;
    analyser.maxDecibels = -10;
    analyser.smoothingTimeConstant = 0.85;

    source = audioCtx.createMediaStreamSource(stream).connect(analyser);
    
    (function animation()
    {
      analyser.getFloatTimeDomainData(dat);

      requestAnimationFrame(animation);
    })();
  },
  err => {}
);