"use strict";

/* Very, very much inspired by https://codepen.io/aymak/pen/eYxEMbd
       I copied significant pieces of code too
       Thank you, Paul Slaymaker
     */

const CSIZE = 400;

const initSpeed = 0.2;
const rMin = 10;
const rMax = 25;

let maxx, maxy; // canvas sizes (in pixels)
let particles;
let click;
let initDir;
let noiseInitDir;
let initHue;
let noiseInitHue;

// shortcuts for Math.…

const mrandom = Math.random;
const mfloor = Math.floor;
const mround = Math.round;
const mceil = Math.ceil;
const mabs = Math.abs;
const mmin = Math.min;
const mmax = Math.max;

const mPI = Math.PI;
const mPIS2 = Math.PI / 2;
const m2PI = Math.PI * 2;
const msin = Math.sin;
const mcos = Math.cos;
const matan2 = Math.atan2;

const mhypot = Math.hypot;
const msqrt = Math.sqrt;

const rac3 = msqrt(3);
const rac3s2 = rac3 / 2;
const mPIS3 = Math.PI / 3;

//-----------------------------------------------------------------------------
// miscellaneous functions
//-----------------------------------------------------------------------------

function alea(min, max) {
  // random number [min..max[ . If no max is provided, [0..min[

  if (typeof max == "undefined") return min * mrandom();
  return min + (max - min) * mrandom();
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

function intAlea(min, max) {
  // random integer number [min..max[ . If no max is provided, [0..min[

  if (typeof max == "undefined") {
    max = min;
    min = 0;
  }
  return mfloor(min + (max - min) * mrandom());
} // intAlea

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
function NoiseGen(
  rndFunc,
  period,
  nbHarmonics,
  attenHarmonics,
  lowValue = 0,
  highValue = 1
) {
  /* this function returns a function which can be used as a noise generator
         the returned functions takes no parameter : it is supposed to be called for
         consecutive, evenly spaced points of time or space.
      - rndFunc is the random generator function used. It must return a value in the range
      [0..1[. If a falsy value is provided (0, false, null, undefined..) Math.random will be used.
      - period determines the speed of variation of the returned value. The higher
      period is, the slowlier the value will change in the noise signal. It must be
      a positive, non zero value (typically a few hundreds).
      - nbHarmonics is an integer giving the number of harmonics used to generate the signal.
      With 0 or 1, a single, smooth signal will be generated
      With 2 or more, internally generated signals of periods up to period / 2, period / 3, will be added.
      nbHarmonics should be kept as low as possible, since every added harmonic increases the
      computation time significantly.
      - attenHarmonics is a float number which should stay in the interval 0..1.
      During harmonics generation, the amplitude of the signal is multiplied by
      attenHarmonics, with respect to the immediatly lower level harmonic.
      attenHarmonics = 0 results in no harmonics at all. attenHarmonics > 1 results in
      harmonics greater than the fundamental, whith the highest harmonics beeing the
      most important. This is not usually the desired behaviour.
      lowValue and highValue are optional floating values. Despite the names, it
      it is not required that highValue > lowValue. The
      returned value will be scaled to the range lowValue..highValue
      (without strict warranty about the limits beeing reached or exceeded, due to
      the finite precision of floating numbers)

      */

  let arP0 = []; // 'preceeding value' for each harmonic
  let arP1 = []; // 'succeding value'
  let amplitudes = []; // amplitudes oh harmonics
  let increments = []; // n / period, wich will be added to phases for every point
  let phases = [];
  let globAmplitude = 0;
  if (!rndFunc) rndFunc = Math.random; // default value for rndFunc
  if (nbHarmonics < 1) nbHarmonics = 1;

  for (let kh = 1; kh <= nbHarmonics; ++kh) {
    arP0[kh] = rndFunc();
    arP1[kh] = rndFunc();
    amplitudes[kh] = kh == 1 ? 1 : amplitudes[kh - 1] * attenHarmonics;
    globAmplitude += amplitudes[kh];
    increments[kh] = kh / period;
    phases[kh] = rndFunc();
  } // for kh

  /* normalize amplitudes */
  amplitudes.forEach(
    (value, kh) =>
      (amplitudes[kh] = (value / globAmplitude) * (highValue - lowValue))
  );

  /* returned function here */
  return function () {
    let pf, pfl;
    let signal = 0;
    for (let kh = nbHarmonics; kh >= 1; --kh) {
      pf = phases[kh] += increments[kh];
      if (phases[kh] >= 1) {
        pf = phases[kh] -= 1;
        arP0[kh] = arP1[kh];
        arP1[kh] = rndFunc();
      } // if full period reached
      pfl = pf * pf * (3 - 2 * pf); // always 0..1, but smoother
      signal += (arP0[kh] * (1 - pfl) + arP1[kh] * pfl) * amplitudes[kh];
    } // for kh
    return signal + lowValue;
  }; // returned function
} // NoiseGen

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

function removeElement(array, element) {
  let idx = array.indexOf(element);
  if (idx == -1) throw "Bug ! indexOf -1 in removeElement";
  array.splice(idx, 1);
} // removeElement

//-----------------------------------------------------------------------------
const getHexPath = (spath) => {
  /* this function copied from https://codepen.io/aymak/pen/eYxEMbd
      thank you, Paul Slaymaker
      */
  const dm1 = new DOMMatrix([0.5, 0.866, -0.866, 0.5, 0, 0]);
  const dm2 = new DOMMatrix([-0.5, 0.866, -0.866, -0.5, 0, 0]);
  const dm3 = new DOMMatrix([-1, 0, 0, 1, 0, 0]);
  let hpath = new Path2D(spath);
  hpath.addPath(spath, dm1);
  hpath.addPath(spath, dm2);
  hpath.addPath(hpath, dm3);
  hpath.addPath(hpath, new DOMMatrix([1, 0, 0, -1, 0, 0]));
  return hpath;
};

//-----------------------------------------------------------------------------
class Particle {
  constructor() {
    this.x = 0;
    this.y = 0;
    this.dir = alea(m2PI);
    this.hue = intAlea(360);
    this.speed = initSpeed * alea(0.5, 0.5);

    this.dir0 = alea(m2PI);
    this.gendir = NoiseGen(null, 300, 2, 0.8, (-2 * mPI) / 3, (2 * mPI) / 3);
    this.genR = NoiseGen(null, 200, 1, 0, rMin, rMax);
    this.gendHue = NoiseGen(null, 800, 1, 0, -0.5, 0.5);
    this.r0 = this.genR();
    this.r = 0.1;

    this.state = 0; // growth
  } // constructor

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

  move() {
    this.hue += this.gendHue();
    this.hue = (this.hue + 360) % 360;

    this.dir = this.dir0 + this.gendir();
    this.speed = mmin(this.speed + 0.005, 0.7);

    this.x += this.speed * mcos(this.dir);
    this.y += this.speed * msin(this.dir);

    if (mmax(mabs(this.x), mabs(this.y)) > CSIZE + this.r) return false;

    switch (this.state) {
      case 0:
        this.r += 0.2;
        if (this.r > this.r0) this.state = 1;
        break;
      case 1:
        this.r = this.genR();
        break;
    }
    return true;
  } // Particle.move

  // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

  draw() {
    let path = new Path2D();
    path.arc(this.x, this.y, this.r, 0, m2PI);
    path = getHexPath(path);

    //ctx.globalAlpha = 1;
    ctx.lineWidth = 1.5;
    ctx.strokeStyle = "#00000020";
    ctx.stroke(path);

    //ctx.globalAlpha = 1;

    ctx.fillStyle = `hsl(${this.hue},100%,50%)`;
    ctx.fill(path);
  } // Particle.draw
} // class Particle
//-----------------------------------------------------------------------------
// returns false if nothing can be done, true if drawing done

function startOver() {
  ctx.clearRect(-CSIZE, -CSIZE, 2 * CSIZE, 2 * CSIZE);
  noiseInitDir = NoiseGen(null, 200, 0, 0, -0.03, 0.03);
  noiseInitHue = NoiseGen(null, 500, 1, 0.8, -2, 2);
  particles = [];

  initDir = alea(m2PI);
  initHue = alea(360);

  return true; // ok
} // startOver

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

function animate(tStamp) {
  if (click && startOver()) click = false;
  if (particles) {
    initDir += noiseInitDir();
    initDir %= m2PI;
    initHue += noiseInitHue();
    initHue %= 360;
    ctx.fillStyle = "#000";
    ctx.fillRect(0, 0, maxx, maxy);
    if (particles.length < 6) {
      particles.push(new Particle());
    }
    particles.forEach((part, k) => {
      if (part.move() == false) {
        removeElement(particles, part);
      } else part.draw();
    });
  }
  window.requestAnimationFrame(animate);
} // animate
//------------------------------------------------------------------------
//------------------------------------------------------------------------
// beginning of execution

const body = document.getElementsByTagName("body").item(0);
body.style.background = "#000";

const ctx = (() => {
  let d = document.createElement("div");
  d.style.textAlign = "center";
  body.append(d);
  let c = document.createElement("canvas");
  c.width = c.height = 2 * CSIZE;
  body.append(c);
  c.style.display = "block";
  c.style.position = "absolute";
  c.style.top = "50%";
  c.style.left = "50%";
  c.style.transform = "translate(-50%,-50%)";
  return c.getContext("2d");
})();
ctx.translate(CSIZE, CSIZE);
ctx.arc(0, 0, CSIZE, 0, m2PI);
ctx.clip();
ctx.lineCap = "round";

onresize = () => {
  let D = Math.min(window.innerWidth, window.innerHeight) - 40;
  ctx.canvas.style.width = ctx.canvas.style.height = D + "px";
};

onresize();

animate();
ctx.canvas.addEventListener("click", () => (click = true));
click = true; // to run startOver