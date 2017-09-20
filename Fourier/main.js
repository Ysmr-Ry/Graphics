"use strict";
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined') window = global;

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(2904464383, 3929545892, true);
  var y = new Long(3027541338, 3270546716, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': new Int16Array(buffer)
        , 'i32': new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': new Uint16Array(buffer)
        , 'w32': new Uint32Array(buffer)
        , 'f32': new Float32Array(buffer)
        , 'f64': new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

var _0="metaKey",_1="shiftKey",_2="altKey",_3="ctrlKey",_4="keyCode",_5=function(_6,_){var _7=__get(_6,E(_4)),_8=__get(_6,E(_3)),_9=__get(_6,E(_2)),_a=__get(_6,E(_1)),_b=__get(_6,E(_0));return new T(function(){var _c=Number(_7),_d=jsTrunc(_c);return new T5(0,_d,E(_8),E(_9),E(_a),E(_b));});},_e=function(_f,_g,_){return new F(function(){return _5(E(_g),_);});},_h="keydown",_i="keyup",_j="keypress",_k=function(_l){switch(E(_l)){case 0:return E(_j);case 1:return E(_i);default:return E(_h);}},_m=new T2(0,_k,_e),_n=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_o=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_p=function(_q,_){return new T1(1,_q);},_r=function(_s){return E(_s);},_t=new T2(0,_r,_p),_u=function(_v,_w,_){var _x=B(A1(_v,_)),_y=B(A1(_w,_));return _x;},_z=function(_A,_B,_){var _C=B(A1(_A,_)),_D=B(A1(_B,_));return new T(function(){return B(A1(_C,_D));});},_E=function(_F,_G,_){var _H=B(A1(_G,_));return _F;},_I=function(_J,_K,_){var _L=B(A1(_K,_));return new T(function(){return B(A1(_J,_L));});},_M=new T2(0,_I,_E),_N=function(_O,_){return _O;},_P=function(_Q,_R,_){var _S=B(A1(_Q,_));return new F(function(){return A1(_R,_);});},_T=new T5(0,_M,_N,_z,_P,_u),_U=new T(function(){return B(unCStr("base"));}),_V=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_W=new T(function(){return B(unCStr("IOException"));}),_X=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_U,_V,_W),_Y=__Z,_Z=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_X,_Y,_Y),_10=function(_11){return E(_Z);},_12=function(_13){return E(E(_13).a);},_14=function(_15,_16,_17){var _18=B(A1(_15,_)),_19=B(A1(_16,_)),_1a=hs_eqWord64(_18.a,_19.a);if(!_1a){return __Z;}else{var _1b=hs_eqWord64(_18.b,_19.b);return (!_1b)?__Z:new T1(1,_17);}},_1c=function(_1d){var _1e=E(_1d);return new F(function(){return _14(B(_12(_1e.a)),_10,_1e.b);});},_1f=new T(function(){return B(unCStr(": "));}),_1g=new T(function(){return B(unCStr(")"));}),_1h=new T(function(){return B(unCStr(" ("));}),_1i=function(_1j,_1k){var _1l=E(_1j);return (_1l._==0)?E(_1k):new T2(1,_1l.a,new T(function(){return B(_1i(_1l.b,_1k));}));},_1m=new T(function(){return B(unCStr("interrupted"));}),_1n=new T(function(){return B(unCStr("system error"));}),_1o=new T(function(){return B(unCStr("unsatisified constraints"));}),_1p=new T(function(){return B(unCStr("user error"));}),_1q=new T(function(){return B(unCStr("permission denied"));}),_1r=new T(function(){return B(unCStr("illegal operation"));}),_1s=new T(function(){return B(unCStr("end of file"));}),_1t=new T(function(){return B(unCStr("resource exhausted"));}),_1u=new T(function(){return B(unCStr("resource busy"));}),_1v=new T(function(){return B(unCStr("does not exist"));}),_1w=new T(function(){return B(unCStr("already exists"));}),_1x=new T(function(){return B(unCStr("resource vanished"));}),_1y=new T(function(){return B(unCStr("timeout"));}),_1z=new T(function(){return B(unCStr("unsupported operation"));}),_1A=new T(function(){return B(unCStr("hardware fault"));}),_1B=new T(function(){return B(unCStr("inappropriate type"));}),_1C=new T(function(){return B(unCStr("invalid argument"));}),_1D=new T(function(){return B(unCStr("failed"));}),_1E=new T(function(){return B(unCStr("protocol error"));}),_1F=function(_1G,_1H){switch(E(_1G)){case 0:return new F(function(){return _1i(_1w,_1H);});break;case 1:return new F(function(){return _1i(_1v,_1H);});break;case 2:return new F(function(){return _1i(_1u,_1H);});break;case 3:return new F(function(){return _1i(_1t,_1H);});break;case 4:return new F(function(){return _1i(_1s,_1H);});break;case 5:return new F(function(){return _1i(_1r,_1H);});break;case 6:return new F(function(){return _1i(_1q,_1H);});break;case 7:return new F(function(){return _1i(_1p,_1H);});break;case 8:return new F(function(){return _1i(_1o,_1H);});break;case 9:return new F(function(){return _1i(_1n,_1H);});break;case 10:return new F(function(){return _1i(_1E,_1H);});break;case 11:return new F(function(){return _1i(_1D,_1H);});break;case 12:return new F(function(){return _1i(_1C,_1H);});break;case 13:return new F(function(){return _1i(_1B,_1H);});break;case 14:return new F(function(){return _1i(_1A,_1H);});break;case 15:return new F(function(){return _1i(_1z,_1H);});break;case 16:return new F(function(){return _1i(_1y,_1H);});break;case 17:return new F(function(){return _1i(_1x,_1H);});break;default:return new F(function(){return _1i(_1m,_1H);});}},_1I=new T(function(){return B(unCStr("}"));}),_1J=new T(function(){return B(unCStr("{handle: "));}),_1K=function(_1L,_1M,_1N,_1O,_1P,_1Q){var _1R=new T(function(){var _1S=new T(function(){var _1T=new T(function(){var _1U=E(_1O);if(!_1U._){return E(_1Q);}else{var _1V=new T(function(){return B(_1i(_1U,new T(function(){return B(_1i(_1g,_1Q));},1)));},1);return B(_1i(_1h,_1V));}},1);return B(_1F(_1M,_1T));}),_1W=E(_1N);if(!_1W._){return E(_1S);}else{return B(_1i(_1W,new T(function(){return B(_1i(_1f,_1S));},1)));}}),_1X=E(_1P);if(!_1X._){var _1Y=E(_1L);if(!_1Y._){return E(_1R);}else{var _1Z=E(_1Y.a);if(!_1Z._){var _20=new T(function(){var _21=new T(function(){return B(_1i(_1I,new T(function(){return B(_1i(_1f,_1R));},1)));},1);return B(_1i(_1Z.a,_21));},1);return new F(function(){return _1i(_1J,_20);});}else{var _22=new T(function(){var _23=new T(function(){return B(_1i(_1I,new T(function(){return B(_1i(_1f,_1R));},1)));},1);return B(_1i(_1Z.a,_23));},1);return new F(function(){return _1i(_1J,_22);});}}}else{return new F(function(){return _1i(_1X.a,new T(function(){return B(_1i(_1f,_1R));},1));});}},_24=function(_25){var _26=E(_25);return new F(function(){return _1K(_26.a,_26.b,_26.c,_26.d,_26.f,_Y);});},_27=function(_28){return new T2(0,_29,_28);},_2a=function(_2b,_2c,_2d){var _2e=E(_2c);return new F(function(){return _1K(_2e.a,_2e.b,_2e.c,_2e.d,_2e.f,_2d);});},_2f=function(_2g,_2h){var _2i=E(_2g);return new F(function(){return _1K(_2i.a,_2i.b,_2i.c,_2i.d,_2i.f,_2h);});},_2j=44,_2k=93,_2l=91,_2m=function(_2n,_2o,_2p){var _2q=E(_2o);if(!_2q._){return new F(function(){return unAppCStr("[]",_2p);});}else{var _2r=new T(function(){var _2s=new T(function(){var _2t=function(_2u){var _2v=E(_2u);if(!_2v._){return E(new T2(1,_2k,_2p));}else{var _2w=new T(function(){return B(A2(_2n,_2v.a,new T(function(){return B(_2t(_2v.b));})));});return new T2(1,_2j,_2w);}};return B(_2t(_2q.b));});return B(A2(_2n,_2q.a,_2s));});return new T2(1,_2l,_2r);}},_2x=function(_2y,_2z){return new F(function(){return _2m(_2f,_2y,_2z);});},_2A=new T3(0,_2a,_24,_2x),_29=new T(function(){return new T5(0,_10,_2A,_27,_1c,_24);}),_2B=new T(function(){return E(_29);}),_2C=function(_2D){return E(E(_2D).c);},_2E=__Z,_2F=7,_2G=function(_2H){return new T6(0,_2E,_2F,_Y,_2H,_2E,_2E);},_2I=function(_2J,_){var _2K=new T(function(){return B(A2(_2C,_2B,new T(function(){return B(A1(_2G,_2J));})));});return new F(function(){return die(_2K);});},_2L=function(_2M,_){return new F(function(){return _2I(_2M,_);});},_2N=function(_2O){return new F(function(){return A1(_2L,_2O);});},_2P=function(_2Q,_2R,_){var _2S=B(A1(_2Q,_));return new F(function(){return A2(_2R,_2S,_);});},_2T=new T5(0,_T,_2P,_P,_N,_2N),_2U=new T2(0,_2T,_r),_2V=new T2(0,_2U,_N),_2W=function(_2X,_){var _2Y=E(_2X);if(!_2Y._){return _Y;}else{var _2Z=B(_2W(_2Y.b,_));return new T2(1,_2Y.a,_2Z);}},_30=0,_31=function(_32,_33,_){return new T2(0,function(_34,_){var _35=B(A3(_32,_34,_33,_));return _30;},_33);},_36=function(_37,_38,_){var _39=B(A1(_37,_));return new T2(0,_39,_38);},_3a=function(_3b,_3c,_3d,_){var _3e=B(A2(_3b,_3d,_)),_3f=B(A2(_3c,new T(function(){return E(E(_3e).b);}),_));return new T2(0,new T(function(){return E(E(_3e).a);}),new T(function(){return E(E(_3f).b);}));},_3g=function(_3h,_3i,_3j,_){var _3k=B(A2(_3h,_3j,_)),_3l=B(A2(_3i,new T(function(){return E(E(_3k).b);}),_));return new T2(0,new T(function(){return E(E(_3l).a);}),new T(function(){return E(E(_3l).b);}));},_3m=function(_3n,_3o,_3p,_){var _3q=B(A2(_3n,_3p,_)),_3r=B(A2(_3o,new T(function(){return E(E(_3q).b);}),_)),_3s=new T(function(){return B(A1(E(_3q).a,new T(function(){return E(E(_3r).a);})));});return new T2(0,_3s,new T(function(){return E(E(_3r).b);}));},_3t=function(_3u,_3v,_3w,_){return new F(function(){return _3m(_3u,_3v,_3w,_);});},_3x=function(_3y,_3z,_){return new T2(0,_3y,_3z);},_3A=function(_3v,_3w,_){return new F(function(){return _3x(_3v,_3w,_);});},_3B=function(_3C,_3D,_3E,_){var _3F=B(A2(_3D,_3E,_));return new T2(0,_3C,new T(function(){return E(E(_3F).b);}));},_3G=function(_3H,_3I,_3J,_){var _3K=B(A2(_3I,_3J,_)),_3L=new T(function(){return B(A1(_3H,new T(function(){return E(E(_3K).a);})));});return new T2(0,_3L,new T(function(){return E(E(_3K).b);}));},_3M=function(_3u,_3v,_3w,_){return new F(function(){return _3G(_3u,_3v,_3w,_);});},_3N=new T2(0,_3M,_3B),_3O=new T5(0,_3N,_3A,_3t,_3g,_3a),_3P=function(_3Q,_3R,_3S,_){var _3T=B(A2(_3Q,_3S,_));return new F(function(){return A2(_3R,new T(function(){return E(E(_3T).b);}),_);});},_3U=function(_3u,_3v,_3w,_){return new F(function(){return _3P(_3u,_3v,_3w,_);});},_3V=function(_3W,_3X,_3Y,_){var _3Z=B(A2(_3W,_3Y,_));return new F(function(){return A3(_3X,new T(function(){return E(E(_3Z).a);}),new T(function(){return E(E(_3Z).b);}),_);});},_40=function(_3u,_3v,_3w,_){return new F(function(){return _3V(_3u,_3v,_3w,_);});},_41=function(_42,_43,_){return new F(function(){return _2I(_42,_);});},_44=function(_3v,_3w,_){return new F(function(){return _41(_3v,_3w,_);});},_45=new T5(0,_3O,_40,_3U,_3A,_44),_46=new T2(0,_45,_36),_47=new T2(0,_46,_31),_48=function(_49,_){return _30;},_4a=new T(function(){return B(unCStr("!!: negative index"));}),_4b=new T(function(){return B(unCStr("Prelude."));}),_4c=new T(function(){return B(_1i(_4b,_4a));}),_4d=new T(function(){return B(err(_4c));}),_4e=new T(function(){return B(unCStr("!!: index too large"));}),_4f=new T(function(){return B(_1i(_4b,_4e));}),_4g=new T(function(){return B(err(_4f));}),_4h=function(_4i,_4j){while(1){var _4k=E(_4i);if(!_4k._){return E(_4g);}else{var _4l=E(_4j);if(!_4l){return E(_4k.a);}else{_4i=_4k.b;_4j=_4l-1|0;continue;}}}},_4m=function(_4n,_4o){if(_4o>=0){return new F(function(){return _4h(_4n,_4o);});}else{return E(_4d);}},_4p=function(_4q){var _4r=I_decodeDouble(_4q);return new T2(0,new T1(1,_4r.b),_4r.a);},_4s=function(_4t,_4u){var _4v=E(_4t);if(!_4v._){var _4w=_4v.a,_4x=E(_4u);return (_4x._==0)?_4w==_4x.a:(I_compareInt(_4x.a,_4w)==0)?true:false;}else{var _4y=_4v.a,_4z=E(_4u);return (_4z._==0)?(I_compareInt(_4y,_4z.a)==0)?true:false:(I_compare(_4y,_4z.a)==0)?true:false;}},_4A=new T1(0,0),_4B=function(_4C){var _4D=B(_4p(_4C));return (!B(_4s(_4D.a,_4A)))?_4D.b+53|0:0;},_4E=function(_4F,_4G){var _4H=E(_4F);return (_4H._==0)?_4H.a*Math.pow(2,_4G):I_toNumber(_4H.a)*Math.pow(2,_4G);},_4I=function(_4J,_4K){var _4L=E(_4J);if(!_4L){return E(_4K);}else{if(_4K!=0){var _4M=isDoubleFinite(_4K);if(!E(_4M)){return E(_4K);}else{var _4N=B(_4p(_4K)),_4O=_4N.a,_4P=_4N.b;if(2257>_4L){if(-2257>_4L){return new F(function(){return _4E(_4O,_4P+(-2257)|0);});}else{return new F(function(){return _4E(_4O,_4P+_4L|0);});}}else{return new F(function(){return _4E(_4O,_4P+2257|0);});}}}else{return E(_4K);}}},_4Q=function(_4R,_4S){var _4T=B(_4B(_4R)),_4U=B(_4B(_4S)),_4V=function(_4W){var _4X= -_4W,_4Y=B(_4I(_4X,_4R)),_4Z=B(_4I(_4X,_4S));return new F(function(){return _4I(_4W,Math.sqrt(_4Y*_4Y+_4Z*_4Z));});};if(_4T>_4U){return new F(function(){return _4V(_4T);});}else{return new F(function(){return _4V(_4U);});}},_50=function(_51,_52){if(_52<=0){var _53=function(_54){var _55=function(_56){var _57=function(_58){var _59=function(_5a){var _5b=isDoubleNegativeZero(_52),_5c=_5b,_5d=function(_5e){var _5f=E(_51);return (_5f!=0)?_52+_5f:(_52>=0)?(E(_5c)==0)?(_52!=0)?_52+_5f:E(_5f):3.141592653589793:3.141592653589793;};if(!E(_5c)){return new F(function(){return _5d(_);});}else{var _5g=E(_51),_5h=isDoubleNegativeZero(_5g);if(!E(_5h)){return new F(function(){return _5d(_);});}else{return  -B(_50( -_5g,_52));}}};if(_52>=0){return new F(function(){return _59(_);});}else{var _5i=E(_51),_5j=isDoubleNegativeZero(_5i);if(!E(_5j)){return new F(function(){return _59(_);});}else{return  -B(_50( -_5i,_52));}}};if(_52>0){return new F(function(){return _57(_);});}else{var _5k=E(_51);if(_5k>=0){return new F(function(){return _57(_);});}else{return  -B(_50( -_5k,_52));}}};if(_52>=0){return new F(function(){return _55(_);});}else{var _5l=E(_51);if(_5l<=0){return new F(function(){return _55(_);});}else{return 3.141592653589793+Math.atan(_5l/_52);}}};if(_52!=0){return new F(function(){return _53(_);});}else{if(E(_51)<=0){return new F(function(){return _53(_);});}else{return 1.5707963267948966;}}}else{return new F(function(){return Math.atan(E(_51)/_52);});}},_5m=function(_5n,_5o){if(_5n!=0){return new F(function(){return _50(_5o,_5n);});}else{if(_5o!=0){return new F(function(){return _50(_5o,_5n);});}else{return 0;}}},_5p=function(_){return _30;},_5q=new T(function(){return eval("(function(ctx, x, y, radius, fromAngle, toAngle){ctx.arc(x, y, radius, fromAngle, toAngle);})");}),_5r=0,_5s=6.283185307179586,_5t=new T(function(){return eval("(function(ctx,x,y){ctx.moveTo(x,y);})");}),_5u=function(_5v,_5w,_5x,_5y,_){var _5z=__app3(E(_5t),_5y,_5v+_5x,_5w),_5A=__apply(E(_5q),new T2(1,_5s,new T2(1,_5r,new T2(1,_5x,new T2(1,_5w,new T2(1,_5v,new T2(1,_5y,_Y)))))));return new F(function(){return _5p(_);});},_5B=new T(function(){return eval("(function(ctx){ctx.beginPath();})");}),_5C=new T(function(){return eval("(function(ctx){ctx.fill();})");}),_5D=function(_5E,_5F,_){var _5G=__app1(E(_5B),_5F),_5H=B(A2(_5E,_5F,_)),_5I=__app1(E(_5C),_5F);return new F(function(){return _5p(_);});},_5J=new T(function(){return eval("(function(ctx){ctx.stroke();})");}),_5K=function(_5L,_5M,_){var _5N=__app1(E(_5B),_5M),_5O=B(A2(_5L,_5M,_)),_5P=__app1(E(_5J),_5M);return new F(function(){return _5p(_);});},_5Q=new T(function(){return eval("(function(ctx){ctx.restore();})");}),_5R=new T(function(){return eval("(function(ctx){ctx.save();})");}),_5S=new T(function(){return eval("(function(ctx,x,y){ctx.translate(x,y);})");}),_5T=function(_5U,_5V,_5W,_5X,_){var _5Y=__app1(E(_5R),_5X),_5Z=__app3(E(_5S),_5X,E(_5U),E(_5V)),_60=B(A2(_5W,_5X,_)),_61=__app1(E(_5Q),_5X);return new F(function(){return _5p(_);});},_62=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_63=function(_64,_65,_66){var _67=new T(function(){return toJSStr(E(_66));});return function(_68,_){var _69=__app4(E(_62),E(_68),E(_67),E(_64),E(_65));return new F(function(){return _5p(_);});};},_6a=function(_6b,_6c){var _6d=E(_6c);if(!_6d._){return __Z;}else{var _6e=_6d.a,_6f=E(_6b);return (_6f==1)?new T2(1,_6e,_Y):new T2(1,_6e,new T(function(){return B(_6a(_6f-1|0,_6d.b));}));}},_6g=false,_6h=true,_6i=0,_6j=0,_6k=new T(function(){return B(unCStr(": empty list"));}),_6l=function(_6m){return new F(function(){return err(B(_1i(_4b,new T(function(){return B(_1i(_6m,_6k));},1))));});},_6n=new T(function(){return B(unCStr("head"));}),_6o=new T(function(){return B(_6l(_6n));}),_6p=new T(function(){return eval("(function(e){e.width = e.width;})");}),_6q=",",_6r="rgba(",_6s=new T(function(){return toJSStr(_Y);}),_6t="rgb(",_6u=")",_6v=new T2(1,_6u,_Y),_6w=function(_6x){var _6y=E(_6x);if(!_6y._){var _6z=jsCat(new T2(1,_6t,new T2(1,new T(function(){return String(_6y.a);}),new T2(1,_6q,new T2(1,new T(function(){return String(_6y.b);}),new T2(1,_6q,new T2(1,new T(function(){return String(_6y.c);}),_6v)))))),E(_6s));return E(_6z);}else{var _6A=jsCat(new T2(1,_6r,new T2(1,new T(function(){return String(_6y.a);}),new T2(1,_6q,new T2(1,new T(function(){return String(_6y.b);}),new T2(1,_6q,new T2(1,new T(function(){return String(_6y.c);}),new T2(1,_6q,new T2(1,new T(function(){return String(_6y.d);}),_6v)))))))),E(_6s));return E(_6A);}},_6B="strokeStyle",_6C="fillStyle",_6D=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_6E=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_6F=function(_6G,_6H){var _6I=new T(function(){return B(_6w(_6G));});return function(_6J,_){var _6K=E(_6J),_6L=E(_6C),_6M=E(_6D),_6N=__app2(_6M,_6K,_6L),_6O=E(_6B),_6P=__app2(_6M,_6K,_6O),_6Q=E(_6I),_6R=E(_6E),_6S=__app3(_6R,_6K,_6L,_6Q),_6T=__app3(_6R,_6K,_6O,_6Q),_6U=B(A2(_6H,_6K,_)),_6V=String(_6N),_6W=__app3(_6R,_6K,_6L,_6V),_6X=String(_6P),_6Y=__app3(_6R,_6K,_6O,_6X);return new F(function(){return _5p(_);});};},_6Z=new T(function(){return eval("(function(){ return dat; })");}),_70=function(_71,_72,_73,_74){var _75=B(_4B(_73)),_76=B(_4B(_74));if(_75>_76){var _77= -_75,_78=B(_4I(_77,_73)),_79=B(_4I(_77,_74)),_7a=_73*_78+_74*_79;return new T2(0,(_71*_78+_72*_79)/_7a,(_72*_78-_71*_79)/_7a);}else{var _7b= -_76,_7c=B(_4I(_7b,_73)),_7d=B(_4I(_7b,_74)),_7e=_73*_7c+_74*_7d;return new T2(0,(_71*_7c+_72*_7d)/_7e,(_72*_7c-_71*_7d)/_7e);}},_7f=function(_7g){var _7h=E(_7g);if(!_7h._){return new T2(0,_Y,_Y);}else{var _7i=E(_7h.a),_7j=new T(function(){var _7k=B(_7f(_7h.b));return new T2(0,_7k.a,_7k.b);});return new T2(0,new T2(1,_7i.a,new T(function(){return E(E(_7j).a);})),new T2(1,_7i.b,new T(function(){return E(E(_7j).b);})));}},_7l=function(_7m,_7n){while(1){var _7o=E(_7m);if(!_7o._){return E(_7n);}else{var _7p=_7n+1|0;_7m=_7o.b;_7n=_7p;continue;}}},_7q=function(_7r){var _7s=new T(function(){return new T2(1,_7r,_7s);});return E(_7s);},_7t=function(_7u){var _7v=B(_7l(_7u,0)),_7w=_7v-1|0;if(0<=_7w){var _7x=function(_7y,_7z){var _7A=E(_7z);if(!_7A._){return __Z;}else{var _7B=new T(function(){var _7C=function(_7D,_7E,_7F){while(1){var _7G=0*_7D,_7H=6.283185307179586*_7D,_7I=B(_70( -(_7G*_7y-_7H*0), -(_7G*0+_7H*_7y),_7v,0)),_7J=E(_7I.b),_7K=B(_4m(_7A.a,_7D)),_7L=E(_7K.a),_7M=E(_7K.b),_7N=Math.exp(E(_7I.a)),_7O=_7N*Math.cos(_7J),_7P=_7N*Math.sin(_7J);if(_7D!=_7w){var _7Q=_7D+1|0,_7R=_7E+(_7L*_7O-_7M*_7P),_7S=_7F+_7L*_7P+_7M*_7O;_7D=_7Q;_7E=_7R;_7F=_7S;continue;}else{return new T2(0,_7E+(_7L*_7O-_7M*_7P),_7F+_7L*_7P+_7M*_7O);}}},_7T=B(_7C(0,0,0));return new T2(0,E(_7T.a),E(_7T.b));});return new T2(1,_7B,new T(function(){if(_7y!=_7w){return B(_7x(_7y+1|0,_7A.b));}else{return __Z;}}));}};return new F(function(){return _7x(0,B(_7q(_7u)));});}else{return __Z;}},_7U=function(_7V,_7W){if(_7V<=_7W){var _7X=function(_7Y){return new T2(1,_7Y,new T(function(){if(_7Y!=_7W){return B(_7X(_7Y+1|0));}else{return __Z;}}));};return new F(function(){return _7X(_7V);});}else{return __Z;}},_7Z=function(_80,_81){return new F(function(){return A1(_81,_80);});},_82=function(_83,_84){return new F(function(){return A1(_84,_83);});},_85=function(_86,_87){var _88=E(_87);return (_88._==0)?__Z:new T2(1,new T(function(){return B(A1(_86,_88.a));}),new T(function(){return B(_85(_86,_88.b));}));},_89=function(_8a){var _8b=E(_8a);if(!_8b._){return __Z;}else{var _8c=E(_8b.b);return (_8c._==0)?__Z:new T2(1,new T2(0,_8b.a,_8c.a),new T(function(){return B(_89(_8c.b));}));}},_8d=function(_8e,_8f,_8g){var _8h=E(_8f);if(!_8h._){return __Z;}else{var _8i=E(_8g);return (_8i._==0)?__Z:new T2(1,new T(function(){return B(A2(_8e,_8h.a,_8i.a));}),new T(function(){return B(_8d(_8e,_8h.b,_8i.b));}));}},_8j=function(_8k){var _8l=E(_8k);if(!_8l._){return __Z;}else{var _8m=function(_8n){var _8o=B(_7f(B(_89(_8l)))),_8p=new T(function(){return B(_8j(_8o.b));}),_8q=new T(function(){var _8r=new T(function(){return B(_8j(_8o.a));}),_8s=new T(function(){var _8t=B(_7l(_8r,0)),_8u=B(_7U(0,(imul(_8t,2)|0)-1|0)),_8v=new T(function(){return B(_85(function(_8w,_8x,_8y){var _8z=E(_8w),_8A=B(_70( -(0*_8z), -(6.283185307179586*_8z),imul(_8t,2)|0,0)),_8B=E(_8A.b),_8C=E(_8x),_8D=E(_8y),_8E=E(_8D.a),_8F=E(_8D.b),_8G=Math.exp(E(_8A.a)),_8H=_8G*Math.cos(_8B),_8I=_8G*Math.sin(_8B);return new T2(0,E(_8C.a)-(_8E*_8H-_8F*_8I),E(_8C.b)-(_8E*_8I+_8F*_8H));},_8u));}),_8J=function(_8K){var _8L=E(_8K);return (_8L._==0)?E(_8v):new T2(1,function(_8M,_8N){var _8O=E(_8L.a),_8P=B(_70( -(0*_8O), -(6.283185307179586*_8O),imul(_8t,2)|0,0)),_8Q=E(_8P.b),_8R=E(_8M),_8S=E(_8N),_8T=E(_8S.a),_8U=E(_8S.b),_8V=Math.exp(E(_8P.a)),_8W=_8V*Math.cos(_8Q),_8X=_8V*Math.sin(_8Q);return new T2(0,E(_8R.a)+(_8T*_8W-_8U*_8X),E(_8R.b)+_8T*_8X+_8U*_8W);},new T(function(){return B(_8J(_8L.b));}));};return B(_8J(_8u));},1);return B(_8d(_7Z,B(_1i(_8r,_8r)),_8s));},1);return new F(function(){return _8d(_82,B(_1i(_8p,_8p)),_8q);});},_8Y=E(_8l.b);if(!_8Y._){return new F(function(){return _8m(_);});}else{if(!E(_8Y.b)._){return new F(function(){return _7t(new T2(1,_8l.a,new T2(1,_8Y.a,_Y)));});}else{return new F(function(){return _8m(_);});}}}},_8Z="font",_90=function(_91,_92){var _93=new T(function(){return toJSStr(E(_91));});return function(_94,_){var _95=E(_94),_96=E(_8Z),_97=__app2(E(_6D),_95,_96),_98=E(_6E),_99=__app3(_98,_95,_96,E(_93)),_9a=B(A2(_92,_95,_)),_9b=String(_97),_9c=__app3(_98,_95,_96,_9b);return new F(function(){return _5p(_);});};},_9d=new T(function(){return eval("(function(ctx,x,y){ctx.lineTo(x,y);})");}),_9e=function(_9f,_9g,_){var _9h=E(_9f);if(!_9h._){return _30;}else{var _9i=E(_9h.a),_9j=E(_9g),_9k=__app3(E(_5t),_9j,E(_9i.a),E(_9i.b)),_9l=E(_9h.b);if(!_9l._){return _30;}else{var _9m=E(_9l.a),_9n=E(_9d),_9o=__app3(_9n,_9j,E(_9m.a),E(_9m.b)),_9p=function(_9q,_){while(1){var _9r=E(_9q);if(!_9r._){return _30;}else{var _9s=E(_9r.a),_9t=__app3(_9n,_9j,E(_9s.a),E(_9s.b));_9q=_9r.b;continue;}}};return new F(function(){return _9p(_9l.b,_);});}}},_9u="lineWidth",_9v=function(_9w,_9x){var _9y=new T(function(){return String(E(_9w));});return function(_9z,_){var _9A=E(_9z),_9B=E(_9u),_9C=__app2(E(_6D),_9A,_9B),_9D=E(_6E),_9E=__app3(_9D,_9A,_9B,E(_9y)),_9F=B(A2(_9x,_9A,_)),_9G=String(_9C),_9H=__app3(_9D,_9A,_9B,_9G);return new F(function(){return _5p(_);});};},_9I=0.5,_9J=2,_9K=new T3(0,40,40,40),_9L=new T(function(){return B(_7U(0,2147483647));}),_9M=new T1(0,1),_9N=function(_9O,_9P){var _9Q=E(_9O);if(!_9Q._){var _9R=_9Q.a,_9S=E(_9P);if(!_9S._){var _9T=_9S.a;return (_9R!=_9T)?(_9R>_9T)?2:0:1;}else{var _9U=I_compareInt(_9S.a,_9R);return (_9U<=0)?(_9U>=0)?1:2:0;}}else{var _9V=_9Q.a,_9W=E(_9P);if(!_9W._){var _9X=I_compareInt(_9V,_9W.a);return (_9X>=0)?(_9X<=0)?1:2:0;}else{var _9Y=I_compare(_9V,_9W.a);return (_9Y>=0)?(_9Y<=0)?1:2:0;}}},_9Z=new T(function(){return B(unCStr("base"));}),_a0=new T(function(){return B(unCStr("GHC.Exception"));}),_a1=new T(function(){return B(unCStr("ArithException"));}),_a2=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_9Z,_a0,_a1),_a3=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_a2,_Y,_Y),_a4=function(_a5){return E(_a3);},_a6=function(_a7){var _a8=E(_a7);return new F(function(){return _14(B(_12(_a8.a)),_a4,_a8.b);});},_a9=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_aa=new T(function(){return B(unCStr("denormal"));}),_ab=new T(function(){return B(unCStr("divide by zero"));}),_ac=new T(function(){return B(unCStr("loss of precision"));}),_ad=new T(function(){return B(unCStr("arithmetic underflow"));}),_ae=new T(function(){return B(unCStr("arithmetic overflow"));}),_af=function(_ag,_ah){switch(E(_ag)){case 0:return new F(function(){return _1i(_ae,_ah);});break;case 1:return new F(function(){return _1i(_ad,_ah);});break;case 2:return new F(function(){return _1i(_ac,_ah);});break;case 3:return new F(function(){return _1i(_ab,_ah);});break;case 4:return new F(function(){return _1i(_aa,_ah);});break;default:return new F(function(){return _1i(_a9,_ah);});}},_ai=function(_aj){return new F(function(){return _af(_aj,_Y);});},_ak=function(_al,_am,_an){return new F(function(){return _af(_am,_an);});},_ao=function(_ap,_aq){return new F(function(){return _2m(_af,_ap,_aq);});},_ar=new T3(0,_ak,_ai,_ao),_as=new T(function(){return new T5(0,_a4,_ar,_at,_a6,_ai);}),_at=function(_au){return new T2(0,_as,_au);},_av=3,_aw=new T(function(){return B(_at(_av));}),_ax=new T(function(){return die(_aw);}),_ay=function(_az){var _aA=E(_az);if(!_aA._){return E(_aA.a);}else{return new F(function(){return I_toInt(_aA.a);});}},_aB=function(_aC,_aD){while(1){var _aE=E(_aC);if(!_aE._){var _aF=_aE.a,_aG=E(_aD);if(!_aG._){var _aH=_aG.a,_aI=addC(_aF,_aH);if(!E(_aI.b)){return new T1(0,_aI.a);}else{_aC=new T1(1,I_fromInt(_aF));_aD=new T1(1,I_fromInt(_aH));continue;}}else{_aC=new T1(1,I_fromInt(_aF));_aD=_aG;continue;}}else{var _aJ=E(_aD);if(!_aJ._){_aC=_aE;_aD=new T1(1,I_fromInt(_aJ.a));continue;}else{return new T1(1,I_add(_aE.a,_aJ.a));}}}},_aK=function(_aL,_aM){while(1){var _aN=E(_aL);if(!_aN._){var _aO=E(_aN.a);if(_aO==(-2147483648)){_aL=new T1(1,I_fromInt(-2147483648));continue;}else{var _aP=E(_aM);if(!_aP._){var _aQ=_aP.a;return new T2(0,new T1(0,quot(_aO,_aQ)),new T1(0,_aO%_aQ));}else{_aL=new T1(1,I_fromInt(_aO));_aM=_aP;continue;}}}else{var _aR=E(_aM);if(!_aR._){_aL=_aN;_aM=new T1(1,I_fromInt(_aR.a));continue;}else{var _aS=I_quotRem(_aN.a,_aR.a);return new T2(0,new T1(1,_aS.a),new T1(1,_aS.b));}}}},_aT=function(_aU,_aV){while(1){var _aW=E(_aU);if(!_aW._){_aU=new T1(1,I_fromInt(_aW.a));continue;}else{return new T1(1,I_shiftLeft(_aW.a,_aV));}}},_aX=function(_aY,_aZ,_b0){if(!B(_4s(_b0,_4A))){var _b1=B(_aK(_aZ,_b0)),_b2=_b1.a;switch(B(_9N(B(_aT(_b1.b,1)),_b0))){case 0:return new F(function(){return _4E(_b2,_aY);});break;case 1:if(!(B(_ay(_b2))&1)){return new F(function(){return _4E(_b2,_aY);});}else{return new F(function(){return _4E(B(_aB(_b2,_9M)),_aY);});}break;default:return new F(function(){return _4E(B(_aB(_b2,_9M)),_aY);});}}else{return E(_ax);}},_b3=function(_b4,_b5){var _b6=E(_b4);if(!_b6._){var _b7=_b6.a,_b8=E(_b5);return (_b8._==0)?_b7>_b8.a:I_compareInt(_b8.a,_b7)<0;}else{var _b9=_b6.a,_ba=E(_b5);return (_ba._==0)?I_compareInt(_b9,_ba.a)>0:I_compare(_b9,_ba.a)>0;}},_bb=new T1(0,1),_bc=function(_bd,_be){var _bf=E(_bd);if(!_bf._){var _bg=_bf.a,_bh=E(_be);return (_bh._==0)?_bg<_bh.a:I_compareInt(_bh.a,_bg)>0;}else{var _bi=_bf.a,_bj=E(_be);return (_bj._==0)?I_compareInt(_bi,_bj.a)<0:I_compare(_bi,_bj.a)<0;}},_bk=new T(function(){return B(unCStr("base"));}),_bl=new T(function(){return B(unCStr("Control.Exception.Base"));}),_bm=new T(function(){return B(unCStr("PatternMatchFail"));}),_bn=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_bk,_bl,_bm),_bo=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_bn,_Y,_Y),_bp=function(_bq){return E(_bo);},_br=function(_bs){var _bt=E(_bs);return new F(function(){return _14(B(_12(_bt.a)),_bp,_bt.b);});},_bu=function(_bv){return E(E(_bv).a);},_bw=function(_bx){return new T2(0,_by,_bx);},_bz=function(_bA,_bB){return new F(function(){return _1i(E(_bA).a,_bB);});},_bC=function(_bD,_bE){return new F(function(){return _2m(_bz,_bD,_bE);});},_bF=function(_bG,_bH,_bI){return new F(function(){return _1i(E(_bH).a,_bI);});},_bJ=new T3(0,_bF,_bu,_bC),_by=new T(function(){return new T5(0,_bp,_bJ,_bw,_br,_bu);}),_bK=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_bL=function(_bM,_bN){return new F(function(){return die(new T(function(){return B(A2(_2C,_bN,_bM));}));});},_bO=function(_bP,_au){return new F(function(){return _bL(_bP,_au);});},_bQ=function(_bR,_bS){var _bT=E(_bS);if(!_bT._){return new T2(0,_Y,_Y);}else{var _bU=_bT.a;if(!B(A1(_bR,_bU))){return new T2(0,_Y,_bT);}else{var _bV=new T(function(){var _bW=B(_bQ(_bR,_bT.b));return new T2(0,_bW.a,_bW.b);});return new T2(0,new T2(1,_bU,new T(function(){return E(E(_bV).a);})),new T(function(){return E(E(_bV).b);}));}}},_bX=32,_bY=new T(function(){return B(unCStr("\n"));}),_bZ=function(_c0){return (E(_c0)==124)?false:true;},_c1=function(_c2,_c3){var _c4=B(_bQ(_bZ,B(unCStr(_c2)))),_c5=_c4.a,_c6=function(_c7,_c8){var _c9=new T(function(){var _ca=new T(function(){return B(_1i(_c3,new T(function(){return B(_1i(_c8,_bY));},1)));});return B(unAppCStr(": ",_ca));},1);return new F(function(){return _1i(_c7,_c9);});},_cb=E(_c4.b);if(!_cb._){return new F(function(){return _c6(_c5,_Y);});}else{if(E(_cb.a)==124){return new F(function(){return _c6(_c5,new T2(1,_bX,_cb.b));});}else{return new F(function(){return _c6(_c5,_Y);});}}},_cc=function(_cd){return new F(function(){return _bO(new T1(0,new T(function(){return B(_c1(_cd,_bK));})),_by);});},_ce=function(_cf){var _cg=function(_ch,_ci){while(1){if(!B(_bc(_ch,_cf))){if(!B(_b3(_ch,_cf))){if(!B(_4s(_ch,_cf))){return new F(function(){return _cc("GHC/Integer/Type.lhs:(555,5)-(557,32)|function l2");});}else{return E(_ci);}}else{return _ci-1|0;}}else{var _cj=B(_aT(_ch,1)),_ck=_ci+1|0;_ch=_cj;_ci=_ck;continue;}}};return new F(function(){return _cg(_bb,0);});},_cl=function(_cm){var _cn=E(_cm);if(!_cn._){var _co=_cn.a>>>0;if(!_co){return -1;}else{var _cp=function(_cq,_cr){while(1){if(_cq>=_co){if(_cq<=_co){if(_cq!=_co){return new F(function(){return _cc("GHC/Integer/Type.lhs:(611,5)-(613,40)|function l2");});}else{return E(_cr);}}else{return _cr-1|0;}}else{var _cs=imul(_cq,2)>>>0,_ct=_cr+1|0;_cq=_cs;_cr=_ct;continue;}}};return new F(function(){return _cp(1,0);});}}else{return new F(function(){return _ce(_cn);});}},_cu=function(_cv){var _cw=E(_cv);if(!_cw._){var _cx=_cw.a>>>0;if(!_cx){return new T2(0,-1,0);}else{var _cy=function(_cz,_cA){while(1){if(_cz>=_cx){if(_cz<=_cx){if(_cz!=_cx){return new F(function(){return _cc("GHC/Integer/Type.lhs:(611,5)-(613,40)|function l2");});}else{return E(_cA);}}else{return _cA-1|0;}}else{var _cB=imul(_cz,2)>>>0,_cC=_cA+1|0;_cz=_cB;_cA=_cC;continue;}}};return new T2(0,B(_cy(1,0)),(_cx&_cx-1>>>0)>>>0&4294967295);}}else{var _cD=_cw.a;return new T2(0,B(_cl(_cw)),I_compareInt(I_and(_cD,I_sub(_cD,I_fromInt(1))),0));}},_cE=function(_cF,_cG){var _cH=E(_cF);if(!_cH._){var _cI=_cH.a,_cJ=E(_cG);return (_cJ._==0)?_cI<=_cJ.a:I_compareInt(_cJ.a,_cI)>=0;}else{var _cK=_cH.a,_cL=E(_cG);return (_cL._==0)?I_compareInt(_cK,_cL.a)<=0:I_compare(_cK,_cL.a)<=0;}},_cM=function(_cN,_cO){while(1){var _cP=E(_cN);if(!_cP._){var _cQ=_cP.a,_cR=E(_cO);if(!_cR._){return new T1(0,(_cQ>>>0&_cR.a>>>0)>>>0&4294967295);}else{_cN=new T1(1,I_fromInt(_cQ));_cO=_cR;continue;}}else{var _cS=E(_cO);if(!_cS._){_cN=_cP;_cO=new T1(1,I_fromInt(_cS.a));continue;}else{return new T1(1,I_and(_cP.a,_cS.a));}}}},_cT=function(_cU,_cV){while(1){var _cW=E(_cU);if(!_cW._){var _cX=_cW.a,_cY=E(_cV);if(!_cY._){var _cZ=_cY.a,_d0=subC(_cX,_cZ);if(!E(_d0.b)){return new T1(0,_d0.a);}else{_cU=new T1(1,I_fromInt(_cX));_cV=new T1(1,I_fromInt(_cZ));continue;}}else{_cU=new T1(1,I_fromInt(_cX));_cV=_cY;continue;}}else{var _d1=E(_cV);if(!_d1._){_cU=_cW;_cV=new T1(1,I_fromInt(_d1.a));continue;}else{return new T1(1,I_sub(_cW.a,_d1.a));}}}},_d2=new T1(0,2),_d3=function(_d4,_d5){var _d6=E(_d4);if(!_d6._){var _d7=(_d6.a>>>0&(2<<_d5>>>0)-1>>>0)>>>0,_d8=1<<_d5>>>0;return (_d8<=_d7)?(_d8>=_d7)?1:2:0;}else{var _d9=B(_cM(_d6,B(_cT(B(_aT(_d2,_d5)),_bb)))),_da=B(_aT(_bb,_d5));return (!B(_b3(_da,_d9)))?(!B(_bc(_da,_d9)))?1:2:0;}},_db=function(_dc,_dd){while(1){var _de=E(_dc);if(!_de._){_dc=new T1(1,I_fromInt(_de.a));continue;}else{return new T1(1,I_shiftRight(_de.a,_dd));}}},_df=function(_dg,_dh,_di,_dj){var _dk=B(_cu(_dj)),_dl=_dk.a;if(!E(_dk.b)){var _dm=B(_cl(_di));if(_dm<((_dl+_dg|0)-1|0)){var _dn=_dl+(_dg-_dh|0)|0;if(_dn>0){if(_dn>_dm){if(_dn<=(_dm+1|0)){if(!E(B(_cu(_di)).b)){return 0;}else{return new F(function(){return _4E(_9M,_dg-_dh|0);});}}else{return 0;}}else{var _do=B(_db(_di,_dn));switch(B(_d3(_di,_dn-1|0))){case 0:return new F(function(){return _4E(_do,_dg-_dh|0);});break;case 1:if(!(B(_ay(_do))&1)){return new F(function(){return _4E(_do,_dg-_dh|0);});}else{return new F(function(){return _4E(B(_aB(_do,_9M)),_dg-_dh|0);});}break;default:return new F(function(){return _4E(B(_aB(_do,_9M)),_dg-_dh|0);});}}}else{return new F(function(){return _4E(_di,(_dg-_dh|0)-_dn|0);});}}else{if(_dm>=_dh){var _dp=B(_db(_di,(_dm+1|0)-_dh|0));switch(B(_d3(_di,_dm-_dh|0))){case 0:return new F(function(){return _4E(_dp,((_dm-_dl|0)+1|0)-_dh|0);});break;case 2:return new F(function(){return _4E(B(_aB(_dp,_9M)),((_dm-_dl|0)+1|0)-_dh|0);});break;default:if(!(B(_ay(_dp))&1)){return new F(function(){return _4E(_dp,((_dm-_dl|0)+1|0)-_dh|0);});}else{return new F(function(){return _4E(B(_aB(_dp,_9M)),((_dm-_dl|0)+1|0)-_dh|0);});}}}else{return new F(function(){return _4E(_di, -_dl);});}}}else{var _dq=B(_cl(_di))-_dl|0,_dr=function(_ds){var _dt=function(_du,_dv){if(!B(_cE(B(_aT(_dv,_dh)),_du))){return new F(function(){return _aX(_ds-_dh|0,_du,_dv);});}else{return new F(function(){return _aX((_ds-_dh|0)+1|0,_du,B(_aT(_dv,1)));});}};if(_ds>=_dh){if(_ds!=_dh){return new F(function(){return _dt(_di,new T(function(){return B(_aT(_dj,_ds-_dh|0));}));});}else{return new F(function(){return _dt(_di,_dj);});}}else{return new F(function(){return _dt(new T(function(){return B(_aT(_di,_dh-_ds|0));}),_dj);});}};if(_dg>_dq){return new F(function(){return _dr(_dg);});}else{return new F(function(){return _dr(_dq);});}}},_dw=new T1(0,2147483647),_dx=new T(function(){return B(_aB(_dw,_bb));}),_dy=function(_dz){var _dA=E(_dz);if(!_dA._){var _dB=E(_dA.a);return (_dB==(-2147483648))?E(_dx):new T1(0, -_dB);}else{return new T1(1,I_negate(_dA.a));}},_dC=new T(function(){return 0/0;}),_dD=new T(function(){return -1/0;}),_dE=new T(function(){return 1/0;}),_dF=0,_dG=function(_dH,_dI){if(!B(_4s(_dI,_4A))){if(!B(_4s(_dH,_4A))){if(!B(_bc(_dH,_4A))){return new F(function(){return _df(-1021,53,_dH,_dI);});}else{return  -B(_df(-1021,53,B(_dy(_dH)),_dI));}}else{return E(_dF);}}else{return (!B(_4s(_dH,_4A)))?(!B(_bc(_dH,_4A)))?E(_dE):E(_dD):E(_dC);}},_dJ=function(_dK){var _dL=E(_dK);return new F(function(){return _dG(_dL.a,_dL.b);});},_dM=function(_dN){return 1/E(_dN);},_dO=function(_dP){var _dQ=E(_dP);return (_dQ!=0)?(_dQ<=0)? -_dQ:E(_dQ):E(_dF);},_dR=function(_dS){var _dT=E(_dS);if(!_dT._){return _dT.a;}else{return new F(function(){return I_toNumber(_dT.a);});}},_dU=function(_dV){return new F(function(){return _dR(_dV);});},_dW=1,_dX=-1,_dY=function(_dZ){var _e0=E(_dZ);return (_e0<=0)?(_e0>=0)?E(_e0):E(_dX):E(_dW);},_e1=function(_e2,_e3){return E(_e2)-E(_e3);},_e4=function(_e5){return  -E(_e5);},_e6=function(_e7,_e8){return E(_e7)+E(_e8);},_e9=function(_ea,_eb){return E(_ea)*E(_eb);},_ec={_:0,a:_e6,b:_e1,c:_e9,d:_e4,e:_dO,f:_dY,g:_dU},_ed=function(_ee,_ef){return E(_ee)/E(_ef);},_eg=new T4(0,_ec,_ed,_dM,_dJ),_eh=new T1(0,1),_ei=function(_ej){return E(E(_ej).a);},_ek=function(_el){return E(E(_el).a);},_em=function(_en){return E(E(_en).g);},_eo=function(_ep,_eq){var _er=E(_eq),_es=new T(function(){var _et=B(_ei(_ep)),_eu=B(_eo(_ep,B(A3(_ek,_et,_er,new T(function(){return B(A2(_em,_et,_eh));})))));return new T2(1,_eu.a,_eu.b);});return new T2(0,_er,_es);},_ev=new T(function(){var _ew=B(_eo(_eg,_6i));return new T2(1,_ew.a,_ew.b);}),_ex=function(_ey,_ez){if(_ey<=0){if(_ey>=0){return new F(function(){return quot(_ey,_ez);});}else{if(_ez<=0){return new F(function(){return quot(_ey,_ez);});}else{return quot(_ey+1|0,_ez)-1|0;}}}else{if(_ez>=0){if(_ey>=0){return new F(function(){return quot(_ey,_ez);});}else{if(_ez<=0){return new F(function(){return quot(_ey,_ez);});}else{return quot(_ey+1|0,_ez)-1|0;}}}else{return quot(_ey-1|0,_ez)-1|0;}}},_eA=new T(function(){return B(_ex(256,2));}),_eB=new T(function(){return 0<E(_eA);}),_eC=new T1(0,10),_eD=new T(function(){return B(unCStr("Off"));}),_eE=new T(function(){return B(unCStr("On"));}),_eF=new T(function(){return B(unCStr("30px \u30d2\u30e9\u30ae\u30ce\u89d2\u30b4"));}),_eG=new T3(0,0,255,128),_eH=3,_eI=function(_eJ,_eK){var _eL=_eJ%_eK;if(_eJ<=0){if(_eJ>=0){return E(_eL);}else{if(_eK<=0){return E(_eL);}else{var _eM=E(_eL);return (_eM==0)?0:_eM+_eK|0;}}}else{if(_eK>=0){if(_eJ>=0){return E(_eL);}else{if(_eK<=0){return E(_eL);}else{var _eN=E(_eL);return (_eN==0)?0:_eN+_eK|0;}}}else{var _eO=E(_eL);return (_eO==0)?0:_eO+_eK|0;}}},_eP="globalAlpha",_eQ=function(_eR,_eS){var _eT=new T(function(){return String(E(_eR));});return function(_eU,_){var _eV=E(_eU),_eW=E(_eP),_eX=__app2(E(_6D),_eV,_eW),_eY=E(_6E),_eZ=__app3(_eY,_eV,_eW,E(_eT)),_f0=B(A2(_eS,_eV,_)),_f1=String(_eX),_f2=__app3(_eY,_eV,_eW,_f1);return new F(function(){return _5p(_);});};},_f3=new T(function(){return B(unCStr("tail"));}),_f4=new T(function(){return B(_6l(_f3));}),_f5=function(_f6){return E(E(_f6).a);},_f7=function(_f8){return E(E(_f8).a);},_f9=function(_fa){return E(E(_fa).b);},_fb=new T(function(){return eval("(function(t,f){window.setInterval(f,t);})");}),_fc=new T(function(){return eval("(function(t,f){window.setTimeout(f,t);})");}),_fd=function(_){return new F(function(){return __jsNull();});},_fe=function(_ff){var _fg=B(A1(_ff,_));return E(_fg);},_fh=new T(function(){return B(_fe(_fd));}),_fi=new T(function(){return E(_fh);}),_fj=function(_fk){return E(E(_fk).b);},_fl=function(_fm){return E(E(_fm).b);},_fn=function(_fo,_fp,_fq){var _fr=B(_f5(_fo)),_fs=new T(function(){return B(_fj(_fr));}),_ft=function(_fu){var _fv=function(_){var _fw=E(_fp);if(!_fw._){var _fx=B(A1(_fu,_30)),_fy=__createJSFunc(0,function(_){var _fz=B(A1(_fx,_));return _fi;}),_fA=__app2(E(_fc),_fw.a,_fy);return new T(function(){var _fB=Number(_fA),_fC=jsTrunc(_fB);return new T2(0,_fC,E(_fw));});}else{var _fD=B(A1(_fu,_30)),_fE=__createJSFunc(0,function(_){var _fF=B(A1(_fD,_));return _fi;}),_fG=__app2(E(_fb),_fw.a,_fE);return new T(function(){var _fH=Number(_fG),_fI=jsTrunc(_fH);return new T2(0,_fI,E(_fw));});}};return new F(function(){return A1(_fs,_fv);});},_fJ=new T(function(){return B(A2(_fl,_fo,function(_fK){return E(_fq);}));});return new F(function(){return A3(_f9,B(_f7(_fr)),_fJ,_ft);});},_fL=function(_fM,_fN){var _fO=E(_fM);if(!_fO._){return __Z;}else{var _fP=E(_fN);return (_fP._==0)?__Z:new T2(1,new T2(0,_fO.a,_fP.a),new T(function(){return B(_fL(_fO.b,_fP.b));}));}},_fQ=function(_fR,_fS,_fT,_fU,_fV,_fW,_fX,_fY,_fZ,_){var _g0=new T(function(){return E(_fS)/2;}),_g1=function(_g2,_g3,_g4,_g5,_g6,_g7,_g8,_){var _g9=E(_fR),_ga=__app1(E(_6p),_g9.b),_gb=function(_gc,_){var _gd=function(_ge,_gf,_gg,_){while(1){var _gh=B((function(_gi,_gj,_gk,_){var _gl=E(_gi);if(!_gl._){return _30;}else{var _gm=_gl.a,_gn=E(_gj);if(!_gn._){return _30;}else{var _go=E(_gn.a),_gp=new T(function(){var _gq=new T(function(){return E(_g0)*E(_gm)/256;}),_gr=new T(function(){return E(_g0)*(E(_gm)+1)/256;}),_gs=function(_gt,_){return new F(function(){return _9e(new T2(1,new T2(0,_gq,200*E(E(_go.a).a)),new T2(1,new T2(0,_gr,200*E(E(_go.b).a)),_Y)),_gt,_);});};return B(_9v(_eH,function(_gu,_){return new F(function(){return _5K(_gs,E(_gu),_);});}));}),_gv=B(A(_6F,[_eG,_gp,_gk,_])),_gw=_gk;_ge=_gl.b;_gf=_gn.b;_gg=_gw;return __continue;}}})(_ge,_gf,_gg,_));if(_gh!=__continue){return _gh;}}},_gx=new T(function(){return B(_fL(_g2,new T(function(){var _gy=E(_g2);if(!_gy._){return E(_f4);}else{return E(_gy.b);}},1)));},1),_gz=B(_gd(_ev,_gx,_gc,_)),_gA=new T(function(){return E(_fW);}),_gB=function(_gC,_gD,_gE){var _gF=E(_gC);if(!_gF._){return function(_gG,_){return _gE;};}else{var _gH=_gF.a,_gI=E(_gD);if(!_gI._){return function(_gJ,_){return _gE;};}else{var _gK=_gI.a,_gL=new T(function(){var _gM=E(_gE),_gN=_gM.a,_gO=_gM.b,_gP=new T(function(){var _gQ=E(_gK),_gR=B(_4Q(E(_gQ.a),E(_gQ.b)))/256;return _gR*200+_gR*200;}),_gS=new T(function(){var _gT=E(_gP);if(_gT<2){return E(_48);}else{var _gU=new T(function(){var _gV=function(_gW,_){return new F(function(){return _5u(E(_gN),E(_gO),_gT,E(_gW),_);});};return B(_9v(_9J,function(_gX,_){return new F(function(){return _5K(_gV,E(_gX),_);});}));});return B(_6F(_9K,_gU));}}),_gY=new T(function(){var _gZ=E(_gK);return B(_5m(E(_gZ.a),E(_gZ.b)));}),_h0=new T(function(){var _h1=E(_gN),_h2=E(_gH);if(!B(_4m(_fX,_h2))){return _h1+-1*E(_gP)*Math.cos(6.283185307179586*_h2*E(_gA)/256+E(_gY)+1.5707963267948966);}else{return _h1+E(_gP)*Math.cos(6.283185307179586*_h2*E(_gA)/256+E(_gY)+1.5707963267948966);}}),_h3=new T(function(){return E(_gO)+E(_gP)*Math.sin(6.283185307179586*E(_gH)*E(_gA)/256+E(_gY)+1.5707963267948966);});return function(_h4,_){var _h5=B(A2(_gS,_h4,_));return new T2(0,_h0,_h3);};});return function(_h6,_){var _h7=B(A2(_gL,_h6,_));return new F(function(){return A(_gB,[_gF.b,_gI.b,_h7,_h6,_]);});};}}},_h8=function(_h9,_ha,_hb,_hc){var _hd=E(_h9);if(!_hd._){return function(_he,_){return new T2(0,_hb,_hc);};}else{var _hf=_hd.a,_hg=E(_ha);if(!_hg._){return function(_hh,_){return new T2(0,_hb,_hc);};}else{var _hi=_hg.a,_hj=new T(function(){var _hk=E(_hi),_hl=B(_4Q(E(_hk.a),E(_hk.b)))/256;return _hl*200+_hl*200;}),_hm=new T(function(){var _hn=E(_hj);if(_hn<2){return E(_48);}else{var _ho=new T(function(){var _hp=function(_hq,_){return new F(function(){return _5u(E(_hb),_hc,_hn,E(_hq),_);});};return B(_9v(_9J,function(_hr,_){return new F(function(){return _5K(_hp,E(_hr),_);});}));});return B(_6F(_9K,_ho));}}),_hs=new T(function(){var _ht=E(_hi);return B(_5m(E(_ht.a),E(_ht.b)));}),_hu=new T(function(){var _hv=E(_hb),_hw=E(_hf);if(!B(_4m(_fX,_hw))){return _hv+-1*E(_hj)*Math.cos(6.283185307179586*_hw*E(_gA)/256+E(_hs)+1.5707963267948966);}else{return _hv+E(_hj)*Math.cos(6.283185307179586*_hw*E(_gA)/256+E(_hs)+1.5707963267948966);}}),_hx=new T(function(){return _hc+E(_hj)*Math.sin(6.283185307179586*E(_hf)*E(_gA)/256+E(_hs)+1.5707963267948966);});return function(_hy,_){var _hz=B(A2(_hm,_hy,_));return new F(function(){return A(_gB,[_hd.b,_hg.b,new T2(0,_hu,_hx),_hy,_]);});};}}},_hA=B(A(_h8,[_9L,_fV,new T(function(){return  -(E(_fS)/4);}),0,_gc,_])),_hB=_hA,_hC=new T(function(){var _hD=new T(function(){var _hE=new T(function(){var _hF=E(_g2);if(!_hF._){return E(_6o);}else{return 200*E(E(_hF.a).a);}}),_hG=function(_hH,_){return new F(function(){return _9e(new T2(1,_hB,new T2(1,new T2(0,_6i,_hE),_Y)),_hH,_);});};return B(_9v(_eH,function(_hI,_){return new F(function(){return _5K(_hG,E(_hI),_);});}));});return B(_6F(_eG,_hD));}),_hJ=B(A(_eQ,[_9I,_hC,_gc,_])),_hK=function(_hL,_){var _hM=E(_hB);return new F(function(){return _5u(E(_hM.a),E(_hM.b),3,E(_hL),_);});},_hN=B(A(_6F,[_eG,function(_hO,_){return new F(function(){return _5D(_hK,E(_hO),_);});},_gc,_])),_hP=new T(function(){var _hQ=E(_g2);if(!_hQ._){return E(_6o);}else{return 200*E(E(_hQ.a).a);}}),_hR=function(_hS,_){return new F(function(){return _5u(0,E(_hP),3,E(_hS),_);});},_hT=B(A(_6F,[_eG,function(_hU,_){return new F(function(){return _5D(_hR,E(_hU),_);});},_gc,_])),_hV=new T(function(){var _hW=new T(function(){return B(unAppCStr("Microphone: ",new T(function(){if(!E(_fZ)){return E(_eE);}else{return E(_eD);}})));},1);return B(_63(new T(function(){return  -(E(_fS)/2)+20;}),new T(function(){return  -(E(_fT)/2)+50;}),_hW));});return new F(function(){return A(_90,[_eF,_hV,_gc,_]);});},_hX=B(_5T(_g0,new T(function(){return E(_fT)/2;},1),_gb,_g9.a,_)),_hY=function(_,_hZ,_i0){var _i1=E(_fY),_i2=rMV(_i1),_i3=function(_i4,_){if(!E(_fZ)){return new T2(0,_30,_i4);}else{var _i5=E(_i4),_i6=E(_i5.c),_i7=new T(function(){var _i8=function(_i9,_ia){while(1){var _ib=E(_ia);if(!_ib._){return __Z;}else{var _ic=_ib.b,_id=E(_i9);if(_id==1){return E(_ic);}else{_i9=_id-1|0;_ia=_ic;continue;}}}};return B(_1i(B(_i8(1,_g2)),new T(function(){return B(_6a(1,_g2));},1)));});return new T2(0,_30,new T4(0,_i5.a,new T2(0,_i7,new T(function(){return E(E(_i5.b).b);})),new T2(0,new T(function(){return B(_eI(E(_i6.a)+1|0,256));}),_i6.b),_i5.d));}};if(!E(_i2)){var _ie=B(_i3(_i0,_)),_if=B(A(_fn,[_47,_eC,function(_ig,_){var _ih=E(_ig),_ii=E(_ih.a),_ij=E(_ih.b),_ik=E(_ih.c),_il=E(_ih.d);return new F(function(){return _fQ(_g9,_ii.a,_ii.b,_ij.a,_ij.b,_ik.a,_ik.b,_il.a,_il.b,_);});},new T(function(){return E(E(_ie).b);}),_]));return new T2(0,_30,new T(function(){return E(E(_if).b);}));}else{var _=wMV(_i1,_6g),_im=B(_i3(new T4(0,new T(function(){return E(E(_i0).a);}),new T(function(){return E(E(_i0).b);}),new T(function(){return E(E(_i0).c);}),new T2(0,new T(function(){return E(E(E(_i0).d).a);}),new T(function(){if(!E(_fZ)){return true;}else{return false;}}))),_)),_in=B(A(_fn,[_47,_eC,function(_io,_){var _ip=E(_io),_iq=E(_ip.a),_ir=E(_ip.b),_is=E(_ip.c),_it=E(_ip.d);return new F(function(){return _fQ(_g9,_iq.a,_iq.b,_ir.a,_ir.b,_is.a,_is.b,_it.a,_it.b,_);});},new T(function(){return E(E(_im).b);}),_]));return new T2(0,_30,new T(function(){return E(E(_in).b);}));}};if(!E(_fZ)){return new F(function(){return _hY(_,_30,new T4(0,_g3,new T2(0,_g4,new T(function(){if(!E(_eB)){return __Z;}else{return B(_6a(E(_eA),B(_8j(_g2))));}})),new T2(0,_6j,_g7),_g8));});}else{return new F(function(){return _hY(_,_30,new T4(0,_g3,new T2(0,_g4,_g5),new T2(0,_g6,_g7),_g8));});}};if(!E(_fZ)){var _iu=__app0(E(_6Z)),_iv=__arr2lst(0,_iu),_iw=B(_2W(_iv,_)),_ix=new T(function(){var _iy=function(_iz,_iA){var _iB=E(_iz);if(!_iB._){return __Z;}else{var _iC=_iB.a,_iD=E(_iA);return (_iD==1)?new T2(1,new T(function(){var _iE=E(_iC);return new T2(0,E(_iE),E(_6i));}),_Y):new T2(1,new T(function(){var _iF=E(_iC);return new T2(0,E(_iF),E(_6i));}),new T(function(){return B(_iy(_iB.b,_iD-1|0));}));}};return B(_iy(_iw,256));});return new F(function(){return _g1(_ix,new T2(0,_fS,_fT),_ix,_fV,_fW,_fX,new T2(0,_fY,_6g),_);});}else{return new F(function(){return _g1(_fU,new T2(0,_fS,_fT),_fU,_fV,_fW,_fX,new T2(0,_fY,_6h),_);});}},_iG=function(_iH,_iI){return imul(E(_iH),E(_iI))|0;},_iJ=function(_iK,_iL){return E(_iK)+E(_iL)|0;},_iM=function(_iN,_iO){return E(_iN)-E(_iO)|0;},_iP=function(_iQ){var _iR=E(_iQ);return (_iR<0)? -_iR:E(_iR);},_iS=function(_iT){return new F(function(){return _ay(_iT);});},_iU=function(_iV){return  -E(_iV);},_iW=-1,_iX=0,_iY=1,_iZ=function(_j0){var _j1=E(_j0);return (_j1>=0)?(E(_j1)==0)?E(_iX):E(_iY):E(_iW);},_j2={_:0,a:_iJ,b:_iM,c:_iG,d:_iU,e:_iP,f:_iZ,g:_iS},_j3=new T1(0,1),_j4=function(_j5,_j6){return new T2(0,E(_j5),E(_j6));},_j7=function(_j8,_j9){var _ja=quot(_j9,52774),_jb=(imul(40692,_j9-(imul(_ja,52774)|0)|0)|0)-(imul(_ja,3791)|0)|0,_jc=new T(function(){if(_jb>=0){return _jb;}else{return _jb+2147483399|0;}}),_jd=quot(_j8,53668),_je=(imul(40014,_j8-(imul(_jd,53668)|0)|0)|0)-(imul(_jd,12211)|0)|0,_jf=new T(function(){if(_je>=0){return _je;}else{return _je+2147483563|0;}});return new T2(0,new T(function(){var _jg=E(_jf)-E(_jc)|0;if(_jg>=1){return _jg;}else{return _jg+2147483562|0;}}),new T(function(){return B(_j4(_jf,_jc));}));},_jh=new T1(0,2147483562),_ji=function(_jj,_jk){var _jl=E(_jj);if(!_jl._){var _jm=_jl.a,_jn=E(_jk);return (_jn._==0)?_jm>=_jn.a:I_compareInt(_jn.a,_jm)<=0;}else{var _jo=_jl.a,_jp=E(_jk);return (_jp._==0)?I_compareInt(_jo,_jp.a)>=0:I_compare(_jo,_jp.a)>=0;}},_jq=new T1(0,0),_jr=new T1(0,1000),_js=function(_jt,_ju){while(1){var _jv=E(_jt);if(!_jv._){var _jw=E(_jv.a);if(_jw==(-2147483648)){_jt=new T1(1,I_fromInt(-2147483648));continue;}else{var _jx=E(_ju);if(!_jx._){return new T1(0,B(_eI(_jw,_jx.a)));}else{_jt=new T1(1,I_fromInt(_jw));_ju=_jx;continue;}}}else{var _jy=_jv.a,_jz=E(_ju);return (_jz._==0)?new T1(1,I_mod(_jy,I_fromInt(_jz.a))):new T1(1,I_mod(_jy,_jz.a));}}},_jA=function(_jB){return new T1(0,_jB);},_jC=function(_jD,_jE){while(1){var _jF=E(_jD);if(!_jF._){var _jG=_jF.a,_jH=E(_jE);if(!_jH._){var _jI=_jH.a;if(!(imul(_jG,_jI)|0)){return new T1(0,imul(_jG,_jI)|0);}else{_jD=new T1(1,I_fromInt(_jG));_jE=new T1(1,I_fromInt(_jI));continue;}}else{_jD=new T1(1,I_fromInt(_jG));_jE=_jH;continue;}}else{var _jJ=E(_jE);if(!_jJ._){_jD=_jF;_jE=new T1(1,I_fromInt(_jJ.a));continue;}else{return new T1(1,I_mul(_jF.a,_jJ.a));}}}},_jK=function(_jL,_jM,_jN,_jO){while(1){var _jP=B((function(_jQ,_jR,_jS,_jT){if(!B(_b3(_jR,_jS))){var _jU=B(_aB(B(_cT(_jS,_jR)),_j3)),_jV=function(_jW,_jX,_jY){while(1){if(!B(_ji(_jW,B(_jC(_jU,_jr))))){var _jZ=E(_jY),_k0=B(_j7(_jZ.a,_jZ.b)),_k1=B(_jC(_jW,_jh)),_k2=B(_aB(B(_jC(_jX,_jh)),B(_cT(B(_jA(E(_k0.a))),_j3))));_jW=_k1;_jX=_k2;_jY=_k0.b;continue;}else{return new T2(0,_jX,_jY);}}},_k3=B(_jV(_j3,_jq,_jT)),_k4=new T(function(){return B(A2(_em,_jQ,new T(function(){if(!B(_4s(_jU,_jq))){return B(_aB(_jR,B(_js(_k3.a,_jU))));}else{return E(_ax);}})));});return new T2(0,_k4,_k3.b);}else{var _k5=_jQ,_k6=_jS,_k7=_jR,_k8=_jT;_jL=_k5;_jM=_k6;_jN=_k7;_jO=_k8;return __continue;}})(_jL,_jM,_jN,_jO));if(_jP!=__continue){return _jP;}}},_k9=function(_ka){var _kb=B(_jK(_j2,_jq,_j3,_ka));return new T2(0,E(_kb.b),new T(function(){if(!E(_kb.a)){return false;}else{return true;}}));},_kc=new T1(0,0),_kd=function(_ke,_kf){while(1){var _kg=E(_ke);if(!_kg._){var _kh=_kg.a,_ki=E(_kf);if(!_ki._){return new T1(0,(_kh>>>0|_ki.a>>>0)>>>0&4294967295);}else{_ke=new T1(1,I_fromInt(_kh));_kf=_ki;continue;}}else{var _kj=E(_kf);if(!_kj._){_ke=_kg;_kf=new T1(1,I_fromInt(_kj.a));continue;}else{return new T1(1,I_or(_kg.a,_kj.a));}}}},_kk=function(_kl){var _km=E(_kl);if(!_km._){return E(_kc);}else{return new F(function(){return _kd(new T1(0,E(_km.a)),B(_aT(B(_kk(_km.b)),31)));});}},_kn=function(_ko,_kp){if(!E(_ko)){return new F(function(){return _dy(B(_kk(_kp)));});}else{return new F(function(){return _kk(_kp);});}},_kq=1420103680,_kr=465,_ks=new T2(1,_kr,_Y),_kt=new T2(1,_kq,_ks),_ku=new T(function(){return B(_kn(_6h,_kt));}),_kv=0,_kw=0,_kx=new T(function(){return B(_at(_kw));}),_ky=new T(function(){return die(_kx);}),_kz=function(_kA,_kB){var _kC=E(_kB);if(!_kC){return E(_ax);}else{var _kD=function(_kE){if(_kA<=0){if(_kA>=0){var _kF=quotRemI(_kA,_kC);return new T2(0,_kF.a,_kF.b);}else{if(_kC<=0){var _kG=quotRemI(_kA,_kC);return new T2(0,_kG.a,_kG.b);}else{var _kH=quotRemI(_kA+1|0,_kC);return new T2(0,_kH.a-1|0,(_kH.b+_kC|0)-1|0);}}}else{if(_kC>=0){if(_kA>=0){var _kI=quotRemI(_kA,_kC);return new T2(0,_kI.a,_kI.b);}else{if(_kC<=0){var _kJ=quotRemI(_kA,_kC);return new T2(0,_kJ.a,_kJ.b);}else{var _kK=quotRemI(_kA+1|0,_kC);return new T2(0,_kK.a-1|0,(_kK.b+_kC|0)-1|0);}}}else{var _kL=quotRemI(_kA-1|0,_kC);return new T2(0,_kL.a-1|0,(_kL.b+_kC|0)+1|0);}}};if(E(_kC)==(-1)){if(E(_kA)==(-2147483648)){return new T2(0,_ky,_kv);}else{return new F(function(){return _kD(_);});}}else{return new F(function(){return _kD(_);});}}},_kM=new T1(0,0),_kN=function(_kO,_kP){while(1){var _kQ=E(_kO);if(!_kQ._){var _kR=E(_kQ.a);if(_kR==(-2147483648)){_kO=new T1(1,I_fromInt(-2147483648));continue;}else{var _kS=E(_kP);if(!_kS._){return new T1(0,_kR%_kS.a);}else{_kO=new T1(1,I_fromInt(_kR));_kP=_kS;continue;}}}else{var _kT=_kQ.a,_kU=E(_kP);return (_kU._==0)?new T1(1,I_rem(_kT,I_fromInt(_kU.a))):new T1(1,I_rem(_kT,_kU.a));}}},_kV=function(_kW,_kX){if(!B(_4s(_kX,_kM))){return new F(function(){return _kN(_kW,_kX);});}else{return E(_ax);}},_kY=function(_kZ,_l0){while(1){if(!B(_4s(_l0,_kM))){var _l1=_l0,_l2=B(_kV(_kZ,_l0));_kZ=_l1;_l0=_l2;continue;}else{return E(_kZ);}}},_l3=function(_l4){var _l5=E(_l4);if(!_l5._){var _l6=E(_l5.a);return (_l6==(-2147483648))?E(_dx):(_l6<0)?new T1(0, -_l6):E(_l5);}else{var _l7=_l5.a;return (I_compareInt(_l7,0)>=0)?E(_l5):new T1(1,I_negate(_l7));}},_l8=function(_l9,_la){while(1){var _lb=E(_l9);if(!_lb._){var _lc=E(_lb.a);if(_lc==(-2147483648)){_l9=new T1(1,I_fromInt(-2147483648));continue;}else{var _ld=E(_la);if(!_ld._){return new T1(0,quot(_lc,_ld.a));}else{_l9=new T1(1,I_fromInt(_lc));_la=_ld;continue;}}}else{var _le=_lb.a,_lf=E(_la);return (_lf._==0)?new T1(0,I_toInt(I_quot(_le,I_fromInt(_lf.a)))):new T1(1,I_quot(_le,_lf.a));}}},_lg=5,_lh=new T(function(){return B(_at(_lg));}),_li=new T(function(){return die(_lh);}),_lj=function(_lk,_ll){if(!B(_4s(_ll,_kM))){var _lm=B(_kY(B(_l3(_lk)),B(_l3(_ll))));return (!B(_4s(_lm,_kM)))?new T2(0,B(_l8(_lk,_lm)),B(_l8(_ll,_lm))):E(_ax);}else{return E(_li);}},_ln=new T1(0,-1),_lo=function(_lp){var _lq=E(_lp);if(!_lq._){var _lr=_lq.a;return (_lr>=0)?(E(_lr)==0)?E(_kc):E(_bb):E(_ln);}else{var _ls=I_compareInt(_lq.a,0);return (_ls<=0)?(E(_ls)==0)?E(_kc):E(_ln):E(_bb);}},_lt=function(_lu,_lv,_lw,_lx){var _ly=B(_jC(_lv,_lw));return new F(function(){return _lj(B(_jC(B(_jC(_lu,_lx)),B(_lo(_ly)))),B(_l3(_ly)));});},_lz=function(_lA){return E(_ku);},_lB=new T1(0,1),_lC=function(_lD,_lE){var _lF=E(_lD);return new T2(0,_lF,new T(function(){var _lG=B(_lC(B(_aB(_lF,_lE)),_lE));return new T2(1,_lG.a,_lG.b);}));},_lH=function(_lI){var _lJ=B(_lC(_lI,_lB));return new T2(1,_lJ.a,_lJ.b);},_lK=function(_lL,_lM){var _lN=B(_lC(_lL,new T(function(){return B(_cT(_lM,_lL));})));return new T2(1,_lN.a,_lN.b);},_lO=new T1(0,0),_lP=function(_lQ,_lR,_lS){if(!B(_ji(_lR,_lO))){var _lT=function(_lU){return (!B(_bc(_lU,_lS)))?new T2(1,_lU,new T(function(){return B(_lT(B(_aB(_lU,_lR))));})):__Z;};return new F(function(){return _lT(_lQ);});}else{var _lV=function(_lW){return (!B(_b3(_lW,_lS)))?new T2(1,_lW,new T(function(){return B(_lV(B(_aB(_lW,_lR))));})):__Z;};return new F(function(){return _lV(_lQ);});}},_lX=function(_lY,_lZ,_m0){return new F(function(){return _lP(_lY,B(_cT(_lZ,_lY)),_m0);});},_m1=function(_m2,_m3){return new F(function(){return _lP(_m2,_lB,_m3);});},_m4=function(_m5){return new F(function(){return _ay(_m5);});},_m6=function(_m7){return new F(function(){return _cT(_m7,_lB);});},_m8=function(_m9){return new F(function(){return _aB(_m9,_lB);});},_ma=function(_mb){return new F(function(){return _jA(E(_mb));});},_mc={_:0,a:_m8,b:_m6,c:_ma,d:_m4,e:_lH,f:_lK,g:_m1,h:_lX},_md=function(_me,_mf){while(1){var _mg=E(_me);if(!_mg._){var _mh=E(_mg.a);if(_mh==(-2147483648)){_me=new T1(1,I_fromInt(-2147483648));continue;}else{var _mi=E(_mf);if(!_mi._){return new T1(0,B(_ex(_mh,_mi.a)));}else{_me=new T1(1,I_fromInt(_mh));_mf=_mi;continue;}}}else{var _mj=_mg.a,_mk=E(_mf);return (_mk._==0)?new T1(1,I_div(_mj,I_fromInt(_mk.a))):new T1(1,I_div(_mj,_mk.a));}}},_ml=function(_mm,_mn){if(!B(_4s(_mn,_kM))){return new F(function(){return _md(_mm,_mn);});}else{return E(_ax);}},_mo=function(_mp,_mq){while(1){var _mr=E(_mp);if(!_mr._){var _ms=E(_mr.a);if(_ms==(-2147483648)){_mp=new T1(1,I_fromInt(-2147483648));continue;}else{var _mt=E(_mq);if(!_mt._){var _mu=_mt.a;return new T2(0,new T1(0,B(_ex(_ms,_mu))),new T1(0,B(_eI(_ms,_mu))));}else{_mp=new T1(1,I_fromInt(_ms));_mq=_mt;continue;}}}else{var _mv=E(_mq);if(!_mv._){_mp=_mr;_mq=new T1(1,I_fromInt(_mv.a));continue;}else{var _mw=I_divMod(_mr.a,_mv.a);return new T2(0,new T1(1,_mw.a),new T1(1,_mw.b));}}}},_mx=function(_my,_mz){if(!B(_4s(_mz,_kM))){var _mA=B(_mo(_my,_mz));return new T2(0,_mA.a,_mA.b);}else{return E(_ax);}},_mB=function(_mC,_mD){if(!B(_4s(_mD,_kM))){return new F(function(){return _js(_mC,_mD);});}else{return E(_ax);}},_mE=function(_mF,_mG){if(!B(_4s(_mG,_kM))){return new F(function(){return _l8(_mF,_mG);});}else{return E(_ax);}},_mH=function(_mI,_mJ){if(!B(_4s(_mJ,_kM))){var _mK=B(_aK(_mI,_mJ));return new T2(0,_mK.a,_mK.b);}else{return E(_ax);}},_mL=function(_mM){return E(_mM);},_mN=function(_mO){return E(_mO);},_mP={_:0,a:_aB,b:_cT,c:_jC,d:_dy,e:_l3,f:_lo,g:_mN},_mQ=function(_mR,_mS){var _mT=E(_mR);if(!_mT._){var _mU=_mT.a,_mV=E(_mS);return (_mV._==0)?_mU!=_mV.a:(I_compareInt(_mV.a,_mU)==0)?false:true;}else{var _mW=_mT.a,_mX=E(_mS);return (_mX._==0)?(I_compareInt(_mW,_mX.a)==0)?false:true:(I_compare(_mW,_mX.a)==0)?false:true;}},_mY=new T2(0,_4s,_mQ),_mZ=function(_n0,_n1){return (!B(_cE(_n0,_n1)))?E(_n0):E(_n1);},_n2=function(_n3,_n4){return (!B(_cE(_n3,_n4)))?E(_n4):E(_n3);},_n5={_:0,a:_mY,b:_9N,c:_bc,d:_cE,e:_b3,f:_ji,g:_mZ,h:_n2},_n6=function(_n7){return new T2(0,E(_n7),E(_eh));},_n8=new T3(0,_mP,_n5,_n6),_n9={_:0,a:_n8,b:_mc,c:_mE,d:_kV,e:_ml,f:_mB,g:_mH,h:_mx,i:_mL},_na=new T1(0,0),_nb=function(_nc,_nd,_ne){var _nf=B(A1(_nc,_nd));if(!B(_4s(_nf,_na))){return new F(function(){return _md(B(_jC(_nd,_ne)),_nf);});}else{return E(_ax);}},_ng=function(_nh){return E(E(_nh).a);},_ni=function(_nj){return E(E(_nj).a);},_nk=function(_nl,_nm,_nn){var _no=new T(function(){if(!B(_4s(_nn,_kM))){var _np=B(_aK(_nm,_nn));return new T2(0,_np.a,_np.b);}else{return E(_ax);}}),_nq=new T(function(){return B(A2(_em,B(_ni(B(_ng(_nl)))),new T(function(){return E(E(_no).a);})));});return new T2(0,_nq,new T(function(){return new T2(0,E(E(_no).b),E(_nn));}));},_nr=function(_ns){return E(E(_ns).b);},_nt=function(_nu,_nv,_nw){var _nx=B(_nk(_nu,_nv,_nw)),_ny=_nx.a,_nz=E(_nx.b);if(!B(_bc(B(_jC(_nz.a,_eh)),B(_jC(_kM,_nz.b))))){return E(_ny);}else{var _nA=B(_ni(B(_ng(_nu))));return new F(function(){return A3(_nr,_nA,_ny,new T(function(){return B(A2(_em,_nA,_eh));}));});}},_nB=479723520,_nC=40233135,_nD=new T2(1,_nC,_Y),_nE=new T2(1,_nB,_nD),_nF=new T(function(){return B(_kn(_6h,_nE));}),_nG=new T1(0,40587),_nH=function(_nI){var _nJ=new T(function(){var _nK=B(_lt(_nI,_eh,_ku,_eh)),_nL=B(_lt(_nF,_eh,_ku,_eh)),_nM=B(_lt(_nK.a,_nK.b,_nL.a,_nL.b));return B(_nt(_n9,_nM.a,_nM.b));});return new T2(0,new T(function(){return B(_aB(_nG,_nJ));}),new T(function(){return B(_cT(_nI,B(_nb(_lz,B(_jC(_nJ,_ku)),_nF))));}));},_nN=new T1(0,0),_nO=function(_nP,_){var _nQ=__get(_nP,0),_nR=__get(_nP,1),_nS=Number(_nQ),_nT=jsTrunc(_nS),_nU=Number(_nR),_nV=jsTrunc(_nU);return new T2(0,_nT,_nV);},_nW=new T(function(){return eval("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");}),_nX=660865024,_nY=465661287,_nZ=new T2(1,_nY,_Y),_o0=new T2(1,_nX,_nZ),_o1=new T(function(){return B(_kn(_6h,_o0));}),_o2=function(_){var _o3=__app0(E(_nW)),_o4=B(_nO(_o3,_));return new T(function(){var _o5=E(_o4);if(!B(_4s(_o1,_na))){return B(_aB(B(_jC(B(_jA(E(_o5.a))),_ku)),B(_md(B(_jC(B(_jC(B(_jA(E(_o5.b))),_ku)),_ku)),_o1))));}else{return E(_ax);}});},_o6=new T1(0,12345),_o7=function(_){var _o8=B(_o2(0)),_o9=B(_lt(B(_nH(_o8)).b,_eh,_ku,_eh)),_oa=_o9.b;if(!B(_4s(_oa,_jq))){var _ob=B(_aK(_o9.a,_oa));return new F(function(){return nMV(new T(function(){var _oc=B(_kz((B(_ay(B(_aB(B(_aB(B(_aB(B(_jC(_ob.a,_o6)),_ob.b)),_nN)),_jq))))>>>0&2147483647)>>>0&4294967295,2147483562));return new T2(0,E(_oc.b)+1|0,B(_eI(E(_oc.a),2147483398))+1|0);}));});}else{return E(_ax);}},_od=new T(function(){return B(_fe(_o7));}),_oe=function(_){var _of=mMV(E(_od),_k9),_og=E(_of);return _of;},_oh=new T2(1,_oe,_Y),_oi=function(_oj){var _ok=E(_oj);return (_ok==1)?E(_oh):new T2(1,_oe,new T(function(){return B(_oi(_ok-1|0));}));},_ol=2,_om=new T(function(){return eval("document");}),_on=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_oo=function(_op,_oq){var _or=function(_){var _os=__app1(E(_on),E(_oq)),_ot=__eq(_os,E(_fi));return (E(_ot)==0)?new T1(1,_os):_2E;};return new F(function(){return A2(_fj,_op,_or);});},_ou=function(_ov){return new F(function(){return fromJSStr(E(_ov));});},_ow=function(_ox){return E(E(_ox).a);},_oy=function(_oz,_oA,_oB,_oC){var _oD=new T(function(){var _oE=function(_){var _oF=__app2(E(_6D),B(A2(_ow,_oz,_oB)),E(_oC));return new T(function(){return String(_oF);});};return E(_oE);});return new F(function(){return A2(_fj,_oA,_oD);});},_oG=function(_oH){return E(E(_oH).d);},_oI=function(_oJ,_oK,_oL,_oM){var _oN=B(_f7(_oK)),_oO=new T(function(){return B(_oG(_oN));}),_oP=function(_oQ){return new F(function(){return A1(_oO,new T(function(){return B(_ou(_oQ));}));});},_oR=new T(function(){return B(_oy(_oJ,_oK,_oL,new T(function(){return toJSStr(E(_oM));},1)));});return new F(function(){return A3(_f9,_oN,_oR,_oP);});},_oS=new T(function(){return B(unCStr("Canvas could not be found!"));}),_oT=new T(function(){return B(err(_oS));}),_oU=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_oV=new T(function(){return B(err(_oU));}),_oW=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_oX=new T(function(){return B(err(_oW));}),_oY=new T(function(){return B(_cc("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_oZ=function(_p0,_p1){while(1){var _p2=B((function(_p3,_p4){var _p5=E(_p3);switch(_p5._){case 0:var _p6=E(_p4);if(!_p6._){return __Z;}else{_p0=B(A1(_p5.a,_p6.a));_p1=_p6.b;return __continue;}break;case 1:var _p7=B(A1(_p5.a,_p4)),_p8=_p4;_p0=_p7;_p1=_p8;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_p5.a,_p4),new T(function(){return B(_oZ(_p5.b,_p4));}));default:return E(_p5.a);}})(_p0,_p1));if(_p2!=__continue){return _p2;}}},_p9=function(_pa,_pb){var _pc=function(_pd){var _pe=E(_pb);if(_pe._==3){return new T2(3,_pe.a,new T(function(){return B(_p9(_pa,_pe.b));}));}else{var _pf=E(_pa);if(_pf._==2){return E(_pe);}else{var _pg=E(_pe);if(_pg._==2){return E(_pf);}else{var _ph=function(_pi){var _pj=E(_pg);if(_pj._==4){var _pk=function(_pl){return new T1(4,new T(function(){return B(_1i(B(_oZ(_pf,_pl)),_pj.a));}));};return new T1(1,_pk);}else{var _pm=E(_pf);if(_pm._==1){var _pn=_pm.a,_po=E(_pj);if(!_po._){return new T1(1,function(_pp){return new F(function(){return _p9(B(A1(_pn,_pp)),_po);});});}else{var _pq=function(_pr){return new F(function(){return _p9(B(A1(_pn,_pr)),new T(function(){return B(A1(_po.a,_pr));}));});};return new T1(1,_pq);}}else{var _ps=E(_pj);if(!_ps._){return E(_oY);}else{var _pt=function(_pu){return new F(function(){return _p9(_pm,new T(function(){return B(A1(_ps.a,_pu));}));});};return new T1(1,_pt);}}}},_pv=E(_pf);switch(_pv._){case 1:var _pw=E(_pg);if(_pw._==4){var _px=function(_py){return new T1(4,new T(function(){return B(_1i(B(_oZ(B(A1(_pv.a,_py)),_py)),_pw.a));}));};return new T1(1,_px);}else{return new F(function(){return _ph(_);});}break;case 4:var _pz=_pv.a,_pA=E(_pg);switch(_pA._){case 0:var _pB=function(_pC){var _pD=new T(function(){return B(_1i(_pz,new T(function(){return B(_oZ(_pA,_pC));},1)));});return new T1(4,_pD);};return new T1(1,_pB);case 1:var _pE=function(_pF){var _pG=new T(function(){return B(_1i(_pz,new T(function(){return B(_oZ(B(A1(_pA.a,_pF)),_pF));},1)));});return new T1(4,_pG);};return new T1(1,_pE);default:return new T1(4,new T(function(){return B(_1i(_pz,_pA.a));}));}break;default:return new F(function(){return _ph(_);});}}}}},_pH=E(_pa);switch(_pH._){case 0:var _pI=E(_pb);if(!_pI._){var _pJ=function(_pK){return new F(function(){return _p9(B(A1(_pH.a,_pK)),new T(function(){return B(A1(_pI.a,_pK));}));});};return new T1(0,_pJ);}else{return new F(function(){return _pc(_);});}break;case 3:return new T2(3,_pH.a,new T(function(){return B(_p9(_pH.b,_pb));}));default:return new F(function(){return _pc(_);});}},_pL=new T(function(){return B(unCStr("("));}),_pM=new T(function(){return B(unCStr(")"));}),_pN=function(_pO,_pP){while(1){var _pQ=E(_pO);if(!_pQ._){return (E(_pP)._==0)?true:false;}else{var _pR=E(_pP);if(!_pR._){return false;}else{if(E(_pQ.a)!=E(_pR.a)){return false;}else{_pO=_pQ.b;_pP=_pR.b;continue;}}}}},_pS=function(_pT,_pU){return E(_pT)!=E(_pU);},_pV=function(_pW,_pX){return E(_pW)==E(_pX);},_pY=new T2(0,_pV,_pS),_pZ=function(_q0,_q1){while(1){var _q2=E(_q0);if(!_q2._){return (E(_q1)._==0)?true:false;}else{var _q3=E(_q1);if(!_q3._){return false;}else{if(E(_q2.a)!=E(_q3.a)){return false;}else{_q0=_q2.b;_q1=_q3.b;continue;}}}}},_q4=function(_q5,_q6){return (!B(_pZ(_q5,_q6)))?true:false;},_q7=new T2(0,_pZ,_q4),_q8=function(_q9,_qa){var _qb=E(_q9);switch(_qb._){case 0:return new T1(0,function(_qc){return new F(function(){return _q8(B(A1(_qb.a,_qc)),_qa);});});case 1:return new T1(1,function(_qd){return new F(function(){return _q8(B(A1(_qb.a,_qd)),_qa);});});case 2:return new T0(2);case 3:return new F(function(){return _p9(B(A1(_qa,_qb.a)),new T(function(){return B(_q8(_qb.b,_qa));}));});break;default:var _qe=function(_qf){var _qg=E(_qf);if(!_qg._){return __Z;}else{var _qh=E(_qg.a);return new F(function(){return _1i(B(_oZ(B(A1(_qa,_qh.a)),_qh.b)),new T(function(){return B(_qe(_qg.b));},1));});}},_qi=B(_qe(_qb.a));return (_qi._==0)?new T0(2):new T1(4,_qi);}},_qj=new T0(2),_qk=function(_ql){return new T2(3,_ql,_qj);},_qm=function(_qn,_qo){var _qp=E(_qn);if(!_qp){return new F(function(){return A1(_qo,_30);});}else{var _qq=new T(function(){return B(_qm(_qp-1|0,_qo));});return new T1(0,function(_qr){return E(_qq);});}},_qs=function(_qt,_qu,_qv){var _qw=new T(function(){return B(A1(_qt,_qk));}),_qx=function(_qy,_qz,_qA,_qB){while(1){var _qC=B((function(_qD,_qE,_qF,_qG){var _qH=E(_qD);switch(_qH._){case 0:var _qI=E(_qE);if(!_qI._){return new F(function(){return A1(_qu,_qG);});}else{var _qJ=_qF+1|0,_qK=_qG;_qy=B(A1(_qH.a,_qI.a));_qz=_qI.b;_qA=_qJ;_qB=_qK;return __continue;}break;case 1:var _qL=B(A1(_qH.a,_qE)),_qM=_qE,_qJ=_qF,_qK=_qG;_qy=_qL;_qz=_qM;_qA=_qJ;_qB=_qK;return __continue;case 2:return new F(function(){return A1(_qu,_qG);});break;case 3:var _qN=new T(function(){return B(_q8(_qH,_qG));});return new F(function(){return _qm(_qF,function(_qO){return E(_qN);});});break;default:return new F(function(){return _q8(_qH,_qG);});}})(_qy,_qz,_qA,_qB));if(_qC!=__continue){return _qC;}}};return function(_qP){return new F(function(){return _qx(_qw,_qP,0,_qv);});};},_qQ=function(_qR){return new F(function(){return A1(_qR,_Y);});},_qS=function(_qT,_qU){var _qV=function(_qW){var _qX=E(_qW);if(!_qX._){return E(_qQ);}else{var _qY=_qX.a;if(!B(A1(_qT,_qY))){return E(_qQ);}else{var _qZ=new T(function(){return B(_qV(_qX.b));}),_r0=function(_r1){var _r2=new T(function(){return B(A1(_qZ,function(_r3){return new F(function(){return A1(_r1,new T2(1,_qY,_r3));});}));});return new T1(0,function(_r4){return E(_r2);});};return E(_r0);}}};return function(_r5){return new F(function(){return A2(_qV,_r5,_qU);});};},_r6=new T0(6),_r7=new T(function(){return B(unCStr("valDig: Bad base"));}),_r8=new T(function(){return B(err(_r7));}),_r9=function(_ra,_rb){var _rc=function(_rd,_re){var _rf=E(_rd);if(!_rf._){var _rg=new T(function(){return B(A1(_re,_Y));});return function(_rh){return new F(function(){return A1(_rh,_rg);});};}else{var _ri=E(_rf.a),_rj=function(_rk){var _rl=new T(function(){return B(_rc(_rf.b,function(_rm){return new F(function(){return A1(_re,new T2(1,_rk,_rm));});}));}),_rn=function(_ro){var _rp=new T(function(){return B(A1(_rl,_ro));});return new T1(0,function(_rq){return E(_rp);});};return E(_rn);};switch(E(_ra)){case 8:if(48>_ri){var _rr=new T(function(){return B(A1(_re,_Y));});return function(_rs){return new F(function(){return A1(_rs,_rr);});};}else{if(_ri>55){var _rt=new T(function(){return B(A1(_re,_Y));});return function(_ru){return new F(function(){return A1(_ru,_rt);});};}else{return new F(function(){return _rj(_ri-48|0);});}}break;case 10:if(48>_ri){var _rv=new T(function(){return B(A1(_re,_Y));});return function(_rw){return new F(function(){return A1(_rw,_rv);});};}else{if(_ri>57){var _rx=new T(function(){return B(A1(_re,_Y));});return function(_ry){return new F(function(){return A1(_ry,_rx);});};}else{return new F(function(){return _rj(_ri-48|0);});}}break;case 16:if(48>_ri){if(97>_ri){if(65>_ri){var _rz=new T(function(){return B(A1(_re,_Y));});return function(_rA){return new F(function(){return A1(_rA,_rz);});};}else{if(_ri>70){var _rB=new T(function(){return B(A1(_re,_Y));});return function(_rC){return new F(function(){return A1(_rC,_rB);});};}else{return new F(function(){return _rj((_ri-65|0)+10|0);});}}}else{if(_ri>102){if(65>_ri){var _rD=new T(function(){return B(A1(_re,_Y));});return function(_rE){return new F(function(){return A1(_rE,_rD);});};}else{if(_ri>70){var _rF=new T(function(){return B(A1(_re,_Y));});return function(_rG){return new F(function(){return A1(_rG,_rF);});};}else{return new F(function(){return _rj((_ri-65|0)+10|0);});}}}else{return new F(function(){return _rj((_ri-97|0)+10|0);});}}}else{if(_ri>57){if(97>_ri){if(65>_ri){var _rH=new T(function(){return B(A1(_re,_Y));});return function(_rI){return new F(function(){return A1(_rI,_rH);});};}else{if(_ri>70){var _rJ=new T(function(){return B(A1(_re,_Y));});return function(_rK){return new F(function(){return A1(_rK,_rJ);});};}else{return new F(function(){return _rj((_ri-65|0)+10|0);});}}}else{if(_ri>102){if(65>_ri){var _rL=new T(function(){return B(A1(_re,_Y));});return function(_rM){return new F(function(){return A1(_rM,_rL);});};}else{if(_ri>70){var _rN=new T(function(){return B(A1(_re,_Y));});return function(_rO){return new F(function(){return A1(_rO,_rN);});};}else{return new F(function(){return _rj((_ri-65|0)+10|0);});}}}else{return new F(function(){return _rj((_ri-97|0)+10|0);});}}}else{return new F(function(){return _rj(_ri-48|0);});}}break;default:return E(_r8);}}},_rP=function(_rQ){var _rR=E(_rQ);if(!_rR._){return new T0(2);}else{return new F(function(){return A1(_rb,_rR);});}};return function(_rS){return new F(function(){return A3(_rc,_rS,_r,_rP);});};},_rT=16,_rU=8,_rV=function(_rW){var _rX=function(_rY){return new F(function(){return A1(_rW,new T1(5,new T2(0,_rU,_rY)));});},_rZ=function(_s0){return new F(function(){return A1(_rW,new T1(5,new T2(0,_rT,_s0)));});},_s1=function(_s2){switch(E(_s2)){case 79:return new T1(1,B(_r9(_rU,_rX)));case 88:return new T1(1,B(_r9(_rT,_rZ)));case 111:return new T1(1,B(_r9(_rU,_rX)));case 120:return new T1(1,B(_r9(_rT,_rZ)));default:return new T0(2);}};return function(_s3){return (E(_s3)==48)?E(new T1(0,_s1)):new T0(2);};},_s4=function(_s5){return new T1(0,B(_rV(_s5)));},_s6=function(_s7){return new F(function(){return A1(_s7,_2E);});},_s8=function(_s9){return new F(function(){return A1(_s9,_2E);});},_sa=10,_sb=new T1(0,10),_sc=function(_sd){return new F(function(){return _jA(E(_sd));});},_se=new T(function(){return B(unCStr("this should not happen"));}),_sf=new T(function(){return B(err(_se));}),_sg=function(_sh,_si){var _sj=E(_si);if(!_sj._){return __Z;}else{var _sk=E(_sj.b);return (_sk._==0)?E(_sf):new T2(1,B(_aB(B(_jC(_sj.a,_sh)),_sk.a)),new T(function(){return B(_sg(_sh,_sk.b));}));}},_sl=new T1(0,0),_sm=function(_sn,_so,_sp){while(1){var _sq=B((function(_sr,_ss,_st){var _su=E(_st);if(!_su._){return E(_sl);}else{if(!E(_su.b)._){return E(_su.a);}else{var _sv=E(_ss);if(_sv<=40){var _sw=function(_sx,_sy){while(1){var _sz=E(_sy);if(!_sz._){return E(_sx);}else{var _sA=B(_aB(B(_jC(_sx,_sr)),_sz.a));_sx=_sA;_sy=_sz.b;continue;}}};return new F(function(){return _sw(_sl,_su);});}else{var _sB=B(_jC(_sr,_sr));if(!(_sv%2)){var _sC=B(_sg(_sr,_su));_sn=_sB;_so=quot(_sv+1|0,2);_sp=_sC;return __continue;}else{var _sC=B(_sg(_sr,new T2(1,_sl,_su)));_sn=_sB;_so=quot(_sv+1|0,2);_sp=_sC;return __continue;}}}}})(_sn,_so,_sp));if(_sq!=__continue){return _sq;}}},_sD=function(_sE,_sF){return new F(function(){return _sm(_sE,new T(function(){return B(_7l(_sF,0));},1),B(_85(_sc,_sF)));});},_sG=function(_sH){var _sI=new T(function(){var _sJ=new T(function(){var _sK=function(_sL){return new F(function(){return A1(_sH,new T1(1,new T(function(){return B(_sD(_sb,_sL));})));});};return new T1(1,B(_r9(_sa,_sK)));}),_sM=function(_sN){if(E(_sN)==43){var _sO=function(_sP){return new F(function(){return A1(_sH,new T1(1,new T(function(){return B(_sD(_sb,_sP));})));});};return new T1(1,B(_r9(_sa,_sO)));}else{return new T0(2);}},_sQ=function(_sR){if(E(_sR)==45){var _sS=function(_sT){return new F(function(){return A1(_sH,new T1(1,new T(function(){return B(_dy(B(_sD(_sb,_sT))));})));});};return new T1(1,B(_r9(_sa,_sS)));}else{return new T0(2);}};return B(_p9(B(_p9(new T1(0,_sQ),new T1(0,_sM))),_sJ));});return new F(function(){return _p9(new T1(0,function(_sU){return (E(_sU)==101)?E(_sI):new T0(2);}),new T1(0,function(_sV){return (E(_sV)==69)?E(_sI):new T0(2);}));});},_sW=function(_sX){var _sY=function(_sZ){return new F(function(){return A1(_sX,new T1(1,_sZ));});};return function(_t0){return (E(_t0)==46)?new T1(1,B(_r9(_sa,_sY))):new T0(2);};},_t1=function(_t2){return new T1(0,B(_sW(_t2)));},_t3=function(_t4){var _t5=function(_t6){var _t7=function(_t8){return new T1(1,B(_qs(_sG,_s6,function(_t9){return new F(function(){return A1(_t4,new T1(5,new T3(1,_t6,_t8,_t9)));});})));};return new T1(1,B(_qs(_t1,_s8,_t7)));};return new F(function(){return _r9(_sa,_t5);});},_ta=function(_tb){return new T1(1,B(_t3(_tb)));},_tc=function(_td){return E(E(_td).a);},_te=function(_tf,_tg,_th){while(1){var _ti=E(_th);if(!_ti._){return false;}else{if(!B(A3(_tc,_tf,_tg,_ti.a))){_th=_ti.b;continue;}else{return true;}}}},_tj=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_tk=function(_tl){return new F(function(){return _te(_pY,_tl,_tj);});},_tm=function(_tn){var _to=new T(function(){return B(A1(_tn,_rU));}),_tp=new T(function(){return B(A1(_tn,_rT));});return function(_tq){switch(E(_tq)){case 79:return E(_to);case 88:return E(_tp);case 111:return E(_to);case 120:return E(_tp);default:return new T0(2);}};},_tr=function(_ts){return new T1(0,B(_tm(_ts)));},_tt=function(_tu){return new F(function(){return A1(_tu,_sa);});},_tv=function(_tw,_tx){var _ty=jsShowI(_tw);return new F(function(){return _1i(fromJSStr(_ty),_tx);});},_tz=41,_tA=40,_tB=function(_tC,_tD,_tE){if(_tD>=0){return new F(function(){return _tv(_tD,_tE);});}else{if(_tC<=6){return new F(function(){return _tv(_tD,_tE);});}else{return new T2(1,_tA,new T(function(){var _tF=jsShowI(_tD);return B(_1i(fromJSStr(_tF),new T2(1,_tz,_tE)));}));}}},_tG=function(_tH){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_tB(9,_tH,_Y));}))));});},_tI=function(_tJ){return new T0(2);},_tK=function(_tL){var _tM=E(_tL);if(!_tM._){return E(_tI);}else{var _tN=_tM.a,_tO=E(_tM.b);if(!_tO._){return E(_tN);}else{var _tP=new T(function(){return B(_tK(_tO));}),_tQ=function(_tR){return new F(function(){return _p9(B(A1(_tN,_tR)),new T(function(){return B(A1(_tP,_tR));}));});};return E(_tQ);}}},_tS=function(_tT,_tU){var _tV=function(_tW,_tX,_tY){var _tZ=E(_tW);if(!_tZ._){return new F(function(){return A1(_tY,_tT);});}else{var _u0=E(_tX);if(!_u0._){return new T0(2);}else{if(E(_tZ.a)!=E(_u0.a)){return new T0(2);}else{var _u1=new T(function(){return B(_tV(_tZ.b,_u0.b,_tY));});return new T1(0,function(_u2){return E(_u1);});}}}};return function(_u3){return new F(function(){return _tV(_tT,_u3,_tU);});};},_u4=new T(function(){return B(unCStr("SO"));}),_u5=14,_u6=function(_u7){var _u8=new T(function(){return B(A1(_u7,_u5));});return new T1(1,B(_tS(_u4,function(_u9){return E(_u8);})));},_ua=new T(function(){return B(unCStr("SOH"));}),_ub=1,_uc=function(_ud){var _ue=new T(function(){return B(A1(_ud,_ub));});return new T1(1,B(_tS(_ua,function(_uf){return E(_ue);})));},_ug=function(_uh){return new T1(1,B(_qs(_uc,_u6,_uh)));},_ui=new T(function(){return B(unCStr("NUL"));}),_uj=0,_uk=function(_ul){var _um=new T(function(){return B(A1(_ul,_uj));});return new T1(1,B(_tS(_ui,function(_un){return E(_um);})));},_uo=new T(function(){return B(unCStr("STX"));}),_up=2,_uq=function(_ur){var _us=new T(function(){return B(A1(_ur,_up));});return new T1(1,B(_tS(_uo,function(_ut){return E(_us);})));},_uu=new T(function(){return B(unCStr("ETX"));}),_uv=3,_uw=function(_ux){var _uy=new T(function(){return B(A1(_ux,_uv));});return new T1(1,B(_tS(_uu,function(_uz){return E(_uy);})));},_uA=new T(function(){return B(unCStr("EOT"));}),_uB=4,_uC=function(_uD){var _uE=new T(function(){return B(A1(_uD,_uB));});return new T1(1,B(_tS(_uA,function(_uF){return E(_uE);})));},_uG=new T(function(){return B(unCStr("ENQ"));}),_uH=5,_uI=function(_uJ){var _uK=new T(function(){return B(A1(_uJ,_uH));});return new T1(1,B(_tS(_uG,function(_uL){return E(_uK);})));},_uM=new T(function(){return B(unCStr("ACK"));}),_uN=6,_uO=function(_uP){var _uQ=new T(function(){return B(A1(_uP,_uN));});return new T1(1,B(_tS(_uM,function(_uR){return E(_uQ);})));},_uS=new T(function(){return B(unCStr("BEL"));}),_uT=7,_uU=function(_uV){var _uW=new T(function(){return B(A1(_uV,_uT));});return new T1(1,B(_tS(_uS,function(_uX){return E(_uW);})));},_uY=new T(function(){return B(unCStr("BS"));}),_uZ=8,_v0=function(_v1){var _v2=new T(function(){return B(A1(_v1,_uZ));});return new T1(1,B(_tS(_uY,function(_v3){return E(_v2);})));},_v4=new T(function(){return B(unCStr("HT"));}),_v5=9,_v6=function(_v7){var _v8=new T(function(){return B(A1(_v7,_v5));});return new T1(1,B(_tS(_v4,function(_v9){return E(_v8);})));},_va=new T(function(){return B(unCStr("LF"));}),_vb=10,_vc=function(_vd){var _ve=new T(function(){return B(A1(_vd,_vb));});return new T1(1,B(_tS(_va,function(_vf){return E(_ve);})));},_vg=new T(function(){return B(unCStr("VT"));}),_vh=11,_vi=function(_vj){var _vk=new T(function(){return B(A1(_vj,_vh));});return new T1(1,B(_tS(_vg,function(_vl){return E(_vk);})));},_vm=new T(function(){return B(unCStr("FF"));}),_vn=12,_vo=function(_vp){var _vq=new T(function(){return B(A1(_vp,_vn));});return new T1(1,B(_tS(_vm,function(_vr){return E(_vq);})));},_vs=new T(function(){return B(unCStr("CR"));}),_vt=13,_vu=function(_vv){var _vw=new T(function(){return B(A1(_vv,_vt));});return new T1(1,B(_tS(_vs,function(_vx){return E(_vw);})));},_vy=new T(function(){return B(unCStr("SI"));}),_vz=15,_vA=function(_vB){var _vC=new T(function(){return B(A1(_vB,_vz));});return new T1(1,B(_tS(_vy,function(_vD){return E(_vC);})));},_vE=new T(function(){return B(unCStr("DLE"));}),_vF=16,_vG=function(_vH){var _vI=new T(function(){return B(A1(_vH,_vF));});return new T1(1,B(_tS(_vE,function(_vJ){return E(_vI);})));},_vK=new T(function(){return B(unCStr("DC1"));}),_vL=17,_vM=function(_vN){var _vO=new T(function(){return B(A1(_vN,_vL));});return new T1(1,B(_tS(_vK,function(_vP){return E(_vO);})));},_vQ=new T(function(){return B(unCStr("DC2"));}),_vR=18,_vS=function(_vT){var _vU=new T(function(){return B(A1(_vT,_vR));});return new T1(1,B(_tS(_vQ,function(_vV){return E(_vU);})));},_vW=new T(function(){return B(unCStr("DC3"));}),_vX=19,_vY=function(_vZ){var _w0=new T(function(){return B(A1(_vZ,_vX));});return new T1(1,B(_tS(_vW,function(_w1){return E(_w0);})));},_w2=new T(function(){return B(unCStr("DC4"));}),_w3=20,_w4=function(_w5){var _w6=new T(function(){return B(A1(_w5,_w3));});return new T1(1,B(_tS(_w2,function(_w7){return E(_w6);})));},_w8=new T(function(){return B(unCStr("NAK"));}),_w9=21,_wa=function(_wb){var _wc=new T(function(){return B(A1(_wb,_w9));});return new T1(1,B(_tS(_w8,function(_wd){return E(_wc);})));},_we=new T(function(){return B(unCStr("SYN"));}),_wf=22,_wg=function(_wh){var _wi=new T(function(){return B(A1(_wh,_wf));});return new T1(1,B(_tS(_we,function(_wj){return E(_wi);})));},_wk=new T(function(){return B(unCStr("ETB"));}),_wl=23,_wm=function(_wn){var _wo=new T(function(){return B(A1(_wn,_wl));});return new T1(1,B(_tS(_wk,function(_wp){return E(_wo);})));},_wq=new T(function(){return B(unCStr("CAN"));}),_wr=24,_ws=function(_wt){var _wu=new T(function(){return B(A1(_wt,_wr));});return new T1(1,B(_tS(_wq,function(_wv){return E(_wu);})));},_ww=new T(function(){return B(unCStr("EM"));}),_wx=25,_wy=function(_wz){var _wA=new T(function(){return B(A1(_wz,_wx));});return new T1(1,B(_tS(_ww,function(_wB){return E(_wA);})));},_wC=new T(function(){return B(unCStr("SUB"));}),_wD=26,_wE=function(_wF){var _wG=new T(function(){return B(A1(_wF,_wD));});return new T1(1,B(_tS(_wC,function(_wH){return E(_wG);})));},_wI=new T(function(){return B(unCStr("ESC"));}),_wJ=27,_wK=function(_wL){var _wM=new T(function(){return B(A1(_wL,_wJ));});return new T1(1,B(_tS(_wI,function(_wN){return E(_wM);})));},_wO=new T(function(){return B(unCStr("FS"));}),_wP=28,_wQ=function(_wR){var _wS=new T(function(){return B(A1(_wR,_wP));});return new T1(1,B(_tS(_wO,function(_wT){return E(_wS);})));},_wU=new T(function(){return B(unCStr("GS"));}),_wV=29,_wW=function(_wX){var _wY=new T(function(){return B(A1(_wX,_wV));});return new T1(1,B(_tS(_wU,function(_wZ){return E(_wY);})));},_x0=new T(function(){return B(unCStr("RS"));}),_x1=30,_x2=function(_x3){var _x4=new T(function(){return B(A1(_x3,_x1));});return new T1(1,B(_tS(_x0,function(_x5){return E(_x4);})));},_x6=new T(function(){return B(unCStr("US"));}),_x7=31,_x8=function(_x9){var _xa=new T(function(){return B(A1(_x9,_x7));});return new T1(1,B(_tS(_x6,function(_xb){return E(_xa);})));},_xc=new T(function(){return B(unCStr("SP"));}),_xd=32,_xe=function(_xf){var _xg=new T(function(){return B(A1(_xf,_xd));});return new T1(1,B(_tS(_xc,function(_xh){return E(_xg);})));},_xi=new T(function(){return B(unCStr("DEL"));}),_xj=127,_xk=function(_xl){var _xm=new T(function(){return B(A1(_xl,_xj));});return new T1(1,B(_tS(_xi,function(_xn){return E(_xm);})));},_xo=new T2(1,_xk,_Y),_xp=new T2(1,_xe,_xo),_xq=new T2(1,_x8,_xp),_xr=new T2(1,_x2,_xq),_xs=new T2(1,_wW,_xr),_xt=new T2(1,_wQ,_xs),_xu=new T2(1,_wK,_xt),_xv=new T2(1,_wE,_xu),_xw=new T2(1,_wy,_xv),_xx=new T2(1,_ws,_xw),_xy=new T2(1,_wm,_xx),_xz=new T2(1,_wg,_xy),_xA=new T2(1,_wa,_xz),_xB=new T2(1,_w4,_xA),_xC=new T2(1,_vY,_xB),_xD=new T2(1,_vS,_xC),_xE=new T2(1,_vM,_xD),_xF=new T2(1,_vG,_xE),_xG=new T2(1,_vA,_xF),_xH=new T2(1,_vu,_xG),_xI=new T2(1,_vo,_xH),_xJ=new T2(1,_vi,_xI),_xK=new T2(1,_vc,_xJ),_xL=new T2(1,_v6,_xK),_xM=new T2(1,_v0,_xL),_xN=new T2(1,_uU,_xM),_xO=new T2(1,_uO,_xN),_xP=new T2(1,_uI,_xO),_xQ=new T2(1,_uC,_xP),_xR=new T2(1,_uw,_xQ),_xS=new T2(1,_uq,_xR),_xT=new T2(1,_uk,_xS),_xU=new T2(1,_ug,_xT),_xV=new T(function(){return B(_tK(_xU));}),_xW=34,_xX=new T1(0,1114111),_xY=92,_xZ=39,_y0=function(_y1){var _y2=new T(function(){return B(A1(_y1,_uT));}),_y3=new T(function(){return B(A1(_y1,_uZ));}),_y4=new T(function(){return B(A1(_y1,_v5));}),_y5=new T(function(){return B(A1(_y1,_vb));}),_y6=new T(function(){return B(A1(_y1,_vh));}),_y7=new T(function(){return B(A1(_y1,_vn));}),_y8=new T(function(){return B(A1(_y1,_vt));}),_y9=new T(function(){return B(A1(_y1,_xY));}),_ya=new T(function(){return B(A1(_y1,_xZ));}),_yb=new T(function(){return B(A1(_y1,_xW));}),_yc=new T(function(){var _yd=function(_ye){var _yf=new T(function(){return B(_jA(E(_ye)));}),_yg=function(_yh){var _yi=B(_sD(_yf,_yh));if(!B(_cE(_yi,_xX))){return new T0(2);}else{return new F(function(){return A1(_y1,new T(function(){var _yj=B(_ay(_yi));if(_yj>>>0>1114111){return B(_tG(_yj));}else{return _yj;}}));});}};return new T1(1,B(_r9(_ye,_yg)));},_yk=new T(function(){var _yl=new T(function(){return B(A1(_y1,_x7));}),_ym=new T(function(){return B(A1(_y1,_x1));}),_yn=new T(function(){return B(A1(_y1,_wV));}),_yo=new T(function(){return B(A1(_y1,_wP));}),_yp=new T(function(){return B(A1(_y1,_wJ));}),_yq=new T(function(){return B(A1(_y1,_wD));}),_yr=new T(function(){return B(A1(_y1,_wx));}),_ys=new T(function(){return B(A1(_y1,_wr));}),_yt=new T(function(){return B(A1(_y1,_wl));}),_yu=new T(function(){return B(A1(_y1,_wf));}),_yv=new T(function(){return B(A1(_y1,_w9));}),_yw=new T(function(){return B(A1(_y1,_w3));}),_yx=new T(function(){return B(A1(_y1,_vX));}),_yy=new T(function(){return B(A1(_y1,_vR));}),_yz=new T(function(){return B(A1(_y1,_vL));}),_yA=new T(function(){return B(A1(_y1,_vF));}),_yB=new T(function(){return B(A1(_y1,_vz));}),_yC=new T(function(){return B(A1(_y1,_u5));}),_yD=new T(function(){return B(A1(_y1,_uN));}),_yE=new T(function(){return B(A1(_y1,_uH));}),_yF=new T(function(){return B(A1(_y1,_uB));}),_yG=new T(function(){return B(A1(_y1,_uv));}),_yH=new T(function(){return B(A1(_y1,_up));}),_yI=new T(function(){return B(A1(_y1,_ub));}),_yJ=new T(function(){return B(A1(_y1,_uj));}),_yK=function(_yL){switch(E(_yL)){case 64:return E(_yJ);case 65:return E(_yI);case 66:return E(_yH);case 67:return E(_yG);case 68:return E(_yF);case 69:return E(_yE);case 70:return E(_yD);case 71:return E(_y2);case 72:return E(_y3);case 73:return E(_y4);case 74:return E(_y5);case 75:return E(_y6);case 76:return E(_y7);case 77:return E(_y8);case 78:return E(_yC);case 79:return E(_yB);case 80:return E(_yA);case 81:return E(_yz);case 82:return E(_yy);case 83:return E(_yx);case 84:return E(_yw);case 85:return E(_yv);case 86:return E(_yu);case 87:return E(_yt);case 88:return E(_ys);case 89:return E(_yr);case 90:return E(_yq);case 91:return E(_yp);case 92:return E(_yo);case 93:return E(_yn);case 94:return E(_ym);case 95:return E(_yl);default:return new T0(2);}};return B(_p9(new T1(0,function(_yM){return (E(_yM)==94)?E(new T1(0,_yK)):new T0(2);}),new T(function(){return B(A1(_xV,_y1));})));});return B(_p9(new T1(1,B(_qs(_tr,_tt,_yd))),_yk));});return new F(function(){return _p9(new T1(0,function(_yN){switch(E(_yN)){case 34:return E(_yb);case 39:return E(_ya);case 92:return E(_y9);case 97:return E(_y2);case 98:return E(_y3);case 102:return E(_y7);case 110:return E(_y5);case 114:return E(_y8);case 116:return E(_y4);case 118:return E(_y6);default:return new T0(2);}}),_yc);});},_yO=function(_yP){return new F(function(){return A1(_yP,_30);});},_yQ=function(_yR){var _yS=E(_yR);if(!_yS._){return E(_yO);}else{var _yT=E(_yS.a),_yU=_yT>>>0,_yV=new T(function(){return B(_yQ(_yS.b));});if(_yU>887){var _yW=u_iswspace(_yT);if(!E(_yW)){return E(_yO);}else{var _yX=function(_yY){var _yZ=new T(function(){return B(A1(_yV,_yY));});return new T1(0,function(_z0){return E(_yZ);});};return E(_yX);}}else{var _z1=E(_yU);if(_z1==32){var _z2=function(_z3){var _z4=new T(function(){return B(A1(_yV,_z3));});return new T1(0,function(_z5){return E(_z4);});};return E(_z2);}else{if(_z1-9>>>0>4){if(E(_z1)==160){var _z6=function(_z7){var _z8=new T(function(){return B(A1(_yV,_z7));});return new T1(0,function(_z9){return E(_z8);});};return E(_z6);}else{return E(_yO);}}else{var _za=function(_zb){var _zc=new T(function(){return B(A1(_yV,_zb));});return new T1(0,function(_zd){return E(_zc);});};return E(_za);}}}}},_ze=function(_zf){var _zg=new T(function(){return B(_ze(_zf));}),_zh=function(_zi){return (E(_zi)==92)?E(_zg):new T0(2);},_zj=function(_zk){return E(new T1(0,_zh));},_zl=new T1(1,function(_zm){return new F(function(){return A2(_yQ,_zm,_zj);});}),_zn=new T(function(){return B(_y0(function(_zo){return new F(function(){return A1(_zf,new T2(0,_zo,_6h));});}));}),_zp=function(_zq){var _zr=E(_zq);if(_zr==38){return E(_zg);}else{var _zs=_zr>>>0;if(_zs>887){var _zt=u_iswspace(_zr);return (E(_zt)==0)?new T0(2):E(_zl);}else{var _zu=E(_zs);return (_zu==32)?E(_zl):(_zu-9>>>0>4)?(E(_zu)==160)?E(_zl):new T0(2):E(_zl);}}};return new F(function(){return _p9(new T1(0,function(_zv){return (E(_zv)==92)?E(new T1(0,_zp)):new T0(2);}),new T1(0,function(_zw){var _zx=E(_zw);if(E(_zx)==92){return E(_zn);}else{return new F(function(){return A1(_zf,new T2(0,_zx,_6g));});}}));});},_zy=function(_zz,_zA){var _zB=new T(function(){return B(A1(_zA,new T1(1,new T(function(){return B(A1(_zz,_Y));}))));}),_zC=function(_zD){var _zE=E(_zD),_zF=E(_zE.a);if(E(_zF)==34){if(!E(_zE.b)){return E(_zB);}else{return new F(function(){return _zy(function(_zG){return new F(function(){return A1(_zz,new T2(1,_zF,_zG));});},_zA);});}}else{return new F(function(){return _zy(function(_zH){return new F(function(){return A1(_zz,new T2(1,_zF,_zH));});},_zA);});}};return new F(function(){return _ze(_zC);});},_zI=new T(function(){return B(unCStr("_\'"));}),_zJ=function(_zK){var _zL=u_iswalnum(_zK);if(!E(_zL)){return new F(function(){return _te(_pY,_zK,_zI);});}else{return true;}},_zM=function(_zN){return new F(function(){return _zJ(E(_zN));});},_zO=new T(function(){return B(unCStr(",;()[]{}`"));}),_zP=new T(function(){return B(unCStr("=>"));}),_zQ=new T2(1,_zP,_Y),_zR=new T(function(){return B(unCStr("~"));}),_zS=new T2(1,_zR,_zQ),_zT=new T(function(){return B(unCStr("@"));}),_zU=new T2(1,_zT,_zS),_zV=new T(function(){return B(unCStr("->"));}),_zW=new T2(1,_zV,_zU),_zX=new T(function(){return B(unCStr("<-"));}),_zY=new T2(1,_zX,_zW),_zZ=new T(function(){return B(unCStr("|"));}),_A0=new T2(1,_zZ,_zY),_A1=new T(function(){return B(unCStr("\\"));}),_A2=new T2(1,_A1,_A0),_A3=new T(function(){return B(unCStr("="));}),_A4=new T2(1,_A3,_A2),_A5=new T(function(){return B(unCStr("::"));}),_A6=new T2(1,_A5,_A4),_A7=new T(function(){return B(unCStr(".."));}),_A8=new T2(1,_A7,_A6),_A9=function(_Aa){var _Ab=new T(function(){return B(A1(_Aa,_r6));}),_Ac=new T(function(){var _Ad=new T(function(){var _Ae=function(_Af){var _Ag=new T(function(){return B(A1(_Aa,new T1(0,_Af)));});return new T1(0,function(_Ah){return (E(_Ah)==39)?E(_Ag):new T0(2);});};return B(_y0(_Ae));}),_Ai=function(_Aj){var _Ak=E(_Aj);switch(E(_Ak)){case 39:return new T0(2);case 92:return E(_Ad);default:var _Al=new T(function(){return B(A1(_Aa,new T1(0,_Ak)));});return new T1(0,function(_Am){return (E(_Am)==39)?E(_Al):new T0(2);});}},_An=new T(function(){var _Ao=new T(function(){return B(_zy(_r,_Aa));}),_Ap=new T(function(){var _Aq=new T(function(){var _Ar=new T(function(){var _As=function(_At){var _Au=E(_At),_Av=u_iswalpha(_Au);return (E(_Av)==0)?(E(_Au)==95)?new T1(1,B(_qS(_zM,function(_Aw){return new F(function(){return A1(_Aa,new T1(3,new T2(1,_Au,_Aw)));});}))):new T0(2):new T1(1,B(_qS(_zM,function(_Ax){return new F(function(){return A1(_Aa,new T1(3,new T2(1,_Au,_Ax)));});})));};return B(_p9(new T1(0,_As),new T(function(){return new T1(1,B(_qs(_s4,_ta,_Aa)));})));}),_Ay=function(_Az){return (!B(_te(_pY,_Az,_tj)))?new T0(2):new T1(1,B(_qS(_tk,function(_AA){var _AB=new T2(1,_Az,_AA);if(!B(_te(_q7,_AB,_A8))){return new F(function(){return A1(_Aa,new T1(4,_AB));});}else{return new F(function(){return A1(_Aa,new T1(2,_AB));});}})));};return B(_p9(new T1(0,_Ay),_Ar));});return B(_p9(new T1(0,function(_AC){if(!B(_te(_pY,_AC,_zO))){return new T0(2);}else{return new F(function(){return A1(_Aa,new T1(2,new T2(1,_AC,_Y)));});}}),_Aq));});return B(_p9(new T1(0,function(_AD){return (E(_AD)==34)?E(_Ao):new T0(2);}),_Ap));});return B(_p9(new T1(0,function(_AE){return (E(_AE)==39)?E(new T1(0,_Ai)):new T0(2);}),_An));});return new F(function(){return _p9(new T1(1,function(_AF){return (E(_AF)._==0)?E(_Ab):new T0(2);}),_Ac);});},_AG=0,_AH=function(_AI,_AJ){var _AK=new T(function(){var _AL=new T(function(){var _AM=function(_AN){var _AO=new T(function(){var _AP=new T(function(){return B(A1(_AJ,_AN));});return B(_A9(function(_AQ){var _AR=E(_AQ);return (_AR._==2)?(!B(_pN(_AR.a,_pM)))?new T0(2):E(_AP):new T0(2);}));}),_AS=function(_AT){return E(_AO);};return new T1(1,function(_AU){return new F(function(){return A2(_yQ,_AU,_AS);});});};return B(A2(_AI,_AG,_AM));});return B(_A9(function(_AV){var _AW=E(_AV);return (_AW._==2)?(!B(_pN(_AW.a,_pL)))?new T0(2):E(_AL):new T0(2);}));}),_AX=function(_AY){return E(_AK);};return function(_AZ){return new F(function(){return A2(_yQ,_AZ,_AX);});};},_B0=function(_B1,_B2){var _B3=function(_B4){var _B5=new T(function(){return B(A1(_B1,_B4));}),_B6=function(_B7){return new F(function(){return _p9(B(A1(_B5,_B7)),new T(function(){return new T1(1,B(_AH(_B3,_B7)));}));});};return E(_B6);},_B8=new T(function(){return B(A1(_B1,_B2));}),_B9=function(_Ba){return new F(function(){return _p9(B(A1(_B8,_Ba)),new T(function(){return new T1(1,B(_AH(_B3,_Ba)));}));});};return E(_B9);},_Bb=function(_Bc,_Bd){var _Be=function(_Bf,_Bg){var _Bh=function(_Bi){return new F(function(){return A1(_Bg,new T(function(){return  -E(_Bi);}));});},_Bj=new T(function(){return B(_A9(function(_Bk){return new F(function(){return A3(_Bc,_Bk,_Bf,_Bh);});}));}),_Bl=function(_Bm){return E(_Bj);},_Bn=function(_Bo){return new F(function(){return A2(_yQ,_Bo,_Bl);});},_Bp=new T(function(){return B(_A9(function(_Bq){var _Br=E(_Bq);if(_Br._==4){var _Bs=E(_Br.a);if(!_Bs._){return new F(function(){return A3(_Bc,_Br,_Bf,_Bg);});}else{if(E(_Bs.a)==45){if(!E(_Bs.b)._){return E(new T1(1,_Bn));}else{return new F(function(){return A3(_Bc,_Br,_Bf,_Bg);});}}else{return new F(function(){return A3(_Bc,_Br,_Bf,_Bg);});}}}else{return new F(function(){return A3(_Bc,_Br,_Bf,_Bg);});}}));}),_Bt=function(_Bu){return E(_Bp);};return new T1(1,function(_Bv){return new F(function(){return A2(_yQ,_Bv,_Bt);});});};return new F(function(){return _B0(_Be,_Bd);});},_Bw=new T(function(){return 1/0;}),_Bx=function(_By,_Bz){return new F(function(){return A1(_Bz,_Bw);});},_BA=new T(function(){return 0/0;}),_BB=function(_BC,_BD){return new F(function(){return A1(_BD,_BA);});},_BE=new T(function(){return B(unCStr("NaN"));}),_BF=new T(function(){return B(unCStr("Infinity"));}),_BG=1024,_BH=-1021,_BI=new T(function(){return B(unCStr("Negative exponent"));}),_BJ=new T(function(){return B(err(_BI));}),_BK=new T1(0,2),_BL=new T(function(){return B(_4s(_BK,_kM));}),_BM=function(_BN,_BO,_BP){while(1){if(!E(_BL)){if(!B(_4s(B(_kN(_BO,_BK)),_kM))){if(!B(_4s(_BO,_eh))){var _BQ=B(_jC(_BN,_BN)),_BR=B(_l8(B(_cT(_BO,_eh)),_BK)),_BS=B(_jC(_BN,_BP));_BN=_BQ;_BO=_BR;_BP=_BS;continue;}else{return new F(function(){return _jC(_BN,_BP);});}}else{var _BQ=B(_jC(_BN,_BN)),_BR=B(_l8(_BO,_BK));_BN=_BQ;_BO=_BR;continue;}}else{return E(_ax);}}},_BT=function(_BU,_BV){while(1){if(!E(_BL)){if(!B(_4s(B(_kN(_BV,_BK)),_kM))){if(!B(_4s(_BV,_eh))){return new F(function(){return _BM(B(_jC(_BU,_BU)),B(_l8(B(_cT(_BV,_eh)),_BK)),_BU);});}else{return E(_BU);}}else{var _BW=B(_jC(_BU,_BU)),_BX=B(_l8(_BV,_BK));_BU=_BW;_BV=_BX;continue;}}else{return E(_ax);}}},_BY=function(_BZ,_C0){if(!B(_bc(_C0,_kM))){if(!B(_4s(_C0,_kM))){return new F(function(){return _BT(_BZ,_C0);});}else{return E(_eh);}}else{return E(_BJ);}},_C1=new T1(0,1),_C2=function(_C3,_C4,_C5){while(1){var _C6=E(_C5);if(!_C6._){if(!B(_bc(_C3,_sl))){return new T2(0,B(_jC(_C4,B(_BY(_sb,_C3)))),_eh);}else{var _C7=B(_BY(_sb,B(_dy(_C3))));return new F(function(){return _lj(B(_jC(_C4,B(_lo(_C7)))),B(_l3(_C7)));});}}else{var _C8=B(_cT(_C3,_C1)),_C9=B(_aB(B(_jC(_C4,_sb)),B(_jA(E(_C6.a)))));_C3=_C8;_C4=_C9;_C5=_C6.b;continue;}}},_Ca=function(_Cb){var _Cc=E(_Cb);if(!_Cc._){var _Cd=_Cc.b;return new F(function(){return _lj(B(_jC(B(_sm(new T(function(){return B(_jA(E(_Cc.a)));}),new T(function(){return B(_7l(_Cd,0));},1),B(_85(_sc,_Cd)))),_C1)),_C1);});}else{var _Ce=_Cc.a,_Cf=_Cc.c,_Cg=E(_Cc.b);if(!_Cg._){var _Ch=E(_Cf);if(!_Ch._){return new F(function(){return _lj(B(_jC(B(_sD(_sb,_Ce)),_C1)),_C1);});}else{var _Ci=_Ch.a;if(!B(_ji(_Ci,_sl))){var _Cj=B(_BY(_sb,B(_dy(_Ci))));return new F(function(){return _lj(B(_jC(B(_sD(_sb,_Ce)),B(_lo(_Cj)))),B(_l3(_Cj)));});}else{return new F(function(){return _lj(B(_jC(B(_jC(B(_sD(_sb,_Ce)),B(_BY(_sb,_Ci)))),_C1)),_C1);});}}}else{var _Ck=_Cg.a,_Cl=E(_Cf);if(!_Cl._){return new F(function(){return _C2(_sl,B(_sD(_sb,_Ce)),_Ck);});}else{return new F(function(){return _C2(_Cl.a,B(_sD(_sb,_Ce)),_Ck);});}}}},_Cm=function(_Cn,_Co){while(1){var _Cp=E(_Co);if(!_Cp._){return __Z;}else{if(!B(A1(_Cn,_Cp.a))){return E(_Cp);}else{_Co=_Cp.b;continue;}}}},_Cq=0,_Cr=function(_Cs,_Ct){return E(_Cs)==E(_Ct);},_Cu=function(_Cv){return new F(function(){return _Cr(_Cq,_Cv);});},_Cw=new T2(0,E(_sl),E(_eh)),_Cx=new T1(1,_Cw),_Cy=new T1(0,-2147483648),_Cz=new T1(0,2147483647),_CA=function(_CB,_CC,_CD){var _CE=E(_CD);if(!_CE._){return new T1(1,new T(function(){var _CF=B(_Ca(_CE));return new T2(0,E(_CF.a),E(_CF.b));}));}else{var _CG=E(_CE.c);if(!_CG._){return new T1(1,new T(function(){var _CH=B(_Ca(_CE));return new T2(0,E(_CH.a),E(_CH.b));}));}else{var _CI=_CG.a;if(!B(_b3(_CI,_Cz))){if(!B(_bc(_CI,_Cy))){var _CJ=function(_CK){var _CL=_CK+B(_ay(_CI))|0;return (_CL<=(E(_CC)+3|0))?(_CL>=(E(_CB)-3|0))?new T1(1,new T(function(){var _CM=B(_Ca(_CE));return new T2(0,E(_CM.a),E(_CM.b));})):E(_Cx):__Z;},_CN=B(_Cm(_Cu,_CE.a));if(!_CN._){var _CO=E(_CE.b);if(!_CO._){return E(_Cx);}else{var _CP=B(_bQ(_Cu,_CO.a));if(!E(_CP.b)._){return E(_Cx);}else{return new F(function(){return _CJ( -B(_7l(_CP.a,0)));});}}}else{return new F(function(){return _CJ(B(_7l(_CN,0)));});}}else{return __Z;}}else{return __Z;}}}},_CQ=function(_CR,_CS){return new T0(2);},_CT=function(_CU){var _CV=E(_CU);switch(_CV._){case 3:var _CW=_CV.a;return (!B(_pN(_CW,_BF)))?(!B(_pN(_CW,_BE)))?E(_CQ):E(_BB):E(_Bx);case 5:var _CX=B(_CA(_BH,_BG,_CV.a));if(!_CX._){return E(_Bx);}else{var _CY=new T(function(){var _CZ=E(_CX.a);return B(_dG(_CZ.a,_CZ.b));});return function(_D0,_D1){return new F(function(){return A1(_D1,_CY);});};}break;default:return E(_CQ);}},_D2=function(_D3){var _D4=function(_D5){return E(new T2(3,_D3,_qj));};return new T1(1,function(_D6){return new F(function(){return A2(_yQ,_D6,_D4);});});},_D7=new T(function(){return B(A3(_Bb,_CT,_AG,_D2));}),_D8=new T1(0,1),_D9=new T1(0,2),_Da=new T(function(){var _Db=B(_lC(_D8,_D9));return new T2(1,_Db.a,_Db.b);}),_Dc=function(_Dd){var _De=new T(function(){var _Df=function(_Dg,_Dh,_Di,_Dj){while(1){var _Dk=E(_Dg);if(!_Dk._){return new T2(0,_Di,_Dj);}else{var _Dl=B(_dR(_Dk.a)),_Dm=6.283185307179586*_Dl,_Dn=0*_Dl,_Do=B(_70(_Dm*_Dd-_Dn*0,_Dm*0+_Dn*_Dd,256,0)),_Dp=E(_Do.a),_Dq=E(_Do.b),_Dr=B(_70(Math.sin(_Dp)*cosh(_Dq),Math.cos(_Dp)*sinh(_Dq),_Dl,0)),_Ds=E(_Dr.a),_Dt=E(_Dr.b),_Du=E(_Dh);if(_Du==1){return new T2(0,_Di+_Ds,_Dj+_Dt);}else{var _Dv=_Di+_Ds,_Dw=_Dj+_Dt;_Dg=_Dk.b;_Dh=_Du-1|0;_Di=_Dv;_Dj=_Dw;continue;}}}},_Dx=B(_Df(_Da,32,0,0));return new T2(0,E(_Dx.a),E(_Dx.b));});return new T2(0,_De,new T(function(){var _Dy=E(_Dd);if(_Dy==255){return __Z;}else{var _Dz=B(_Dc(_Dy+1|0));return new T2(1,_Dz.a,_Dz.b);}}));},_DA=new T(function(){var _DB=B(_Dc(0));return new T2(1,_DB.a,_DB.b);}),_DC=new T(function(){return B(_8j(_DA));}),_DD=new T(function(){var _DE=B(_ex(256,2));if(0>=_DE){return __Z;}else{return B(_6a(_DE,_DC));}}),_DF=new T(function(){return B(unCStr("height"));}),_DG=new T(function(){return B(unCStr("width"));}),_DH="canvas",_DI=new T(function(){return B(unCStr("Canvas ID could not be found!"));}),_DJ=new T(function(){return B(err(_DI));}),_DK=function(_DL){return (!E(_DL))?true:false;},_DM=function(_DN){return E(E(_DN).b);},_DO=function(_DP){return E(E(_DP).a);},_DQ=function(_){return new F(function(){return nMV(_2E);});},_DR=new T(function(){return B(_fe(_DQ));}),_DS=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_DT=function(_DU,_DV,_DW,_DX,_DY,_DZ){var _E0=B(_f5(_DU)),_E1=B(_f7(_E0)),_E2=new T(function(){return B(_fj(_E0));}),_E3=new T(function(){return B(_oG(_E1));}),_E4=new T(function(){return B(A2(_ow,_DV,_DX));}),_E5=new T(function(){return B(A2(_DO,_DW,_DY));}),_E6=function(_E7){return new F(function(){return A1(_E3,new T3(0,_E5,_E4,_E7));});},_E8=function(_E9){var _Ea=new T(function(){var _Eb=new T(function(){var _Ec=__createJSFunc(2,function(_Ed,_){var _Ee=B(A2(E(_E9),_Ed,_));return _fi;}),_Ef=_Ec;return function(_){return new F(function(){return __app3(E(_DS),E(_E4),E(_E5),_Ef);});};});return B(A1(_E2,_Eb));});return new F(function(){return A3(_f9,_E1,_Ea,_E6);});},_Eg=new T(function(){var _Eh=new T(function(){return B(_fj(_E0));}),_Ei=function(_Ej){var _Ek=new T(function(){return B(A1(_Eh,function(_){var _=wMV(E(_DR),new T1(1,_Ej));return new F(function(){return A(_DM,[_DW,_DY,_Ej,_]);});}));});return new F(function(){return A3(_f9,_E1,_Ek,_DZ);});};return B(A2(_fl,_DU,_Ei));});return new F(function(){return A3(_f9,_E1,_Eg,_E8);});},_El=function(_Em){while(1){var _En=B((function(_Eo){var _Ep=E(_Eo);if(!_Ep._){return __Z;}else{var _Eq=_Ep.b,_Er=E(_Ep.a);if(!E(_Er.b)._){return new T2(1,_Er.a,new T(function(){return B(_El(_Eq));}));}else{_Em=_Eq;return __continue;}}})(_Em));if(_En!=__continue){return _En;}}},_Es=function(_Et,_){var _Eu=E(_Et);if(!_Eu._){return _Y;}else{var _Ev=B(A1(_Eu.a,_)),_Ew=B(_Es(_Eu.b,_));return new T2(1,_Ev,_Ew);}},_Ex=function(_){var _Ey=B(A3(_oo,_2U,_DH,_)),_Ez=E(_Ey);if(!_Ez._){return E(_DJ);}else{var _EA=_Ez.a,_EB=B(A(_oI,[_t,_2U,_EA,_DG,_])),_EC=_EB,_ED=B(A(_oI,[_t,_2U,_EA,_DF,_])),_EE=_ED,_EF=B(_ex(256,2)),_EG=function(_,_EH){var _EI=nMV(_6g),_EJ=_EI,_EK=function(_EL,_){if(E(E(_EL).a)==13){var _EM=rMV(_EJ),_=wMV(_EJ,new T(function(){return B(_DK(_EM));}));return _30;}else{return _30;}},_EN=B(A(_DT,[_2V,_t,_m,_om,_ol,_EK,_])),_EO=E(_EA),_EP=__app1(E(_o),_EO);if(!_EP){return E(_oT);}else{var _EQ=__app1(E(_n),_EO),_ER=B(_fQ(new T2(0,_EQ,_EO),new T(function(){var _ES=B(_El(B(_oZ(_D7,_EC))));if(!_ES._){return E(_oV);}else{if(!E(_ES.b)._){return E(_ES.a);}else{return E(_oX);}}}),new T(function(){var _ET=B(_El(B(_oZ(_D7,_EE))));if(!_ET._){return E(_oV);}else{if(!E(_ET.b)._){return E(_ET.a);}else{return E(_oX);}}}),_DA,_DD,_6j,_EH,_EJ,_6h,_));return new T(function(){return E(E(_ER).a);});}};if(0>=_EF){var _EU=B(_Es(_Y,_));return new F(function(){return _EG(_,_EU);});}else{var _EV=B(_Es(B(_oi(_EF)),_));return new F(function(){return _EG(_,_EV);});}}},_EW=function(_){return new F(function(){return _Ex(_);});};
var hasteMain = function() {B(A(_EW, [0]));};window.onload = hasteMain;