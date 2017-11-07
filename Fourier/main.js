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

var _0="metaKey",_1="shiftKey",_2="altKey",_3="ctrlKey",_4="keyCode",_5=function(_6,_){var _7=__get(_6,E(_4)),_8=__get(_6,E(_3)),_9=__get(_6,E(_2)),_a=__get(_6,E(_1)),_b=__get(_6,E(_0));return new T(function(){var _c=Number(_7),_d=jsTrunc(_c);return new T5(0,_d,E(_8),E(_9),E(_a),E(_b));});},_e=function(_f,_g,_){return new F(function(){return _5(E(_g),_);});},_h="keydown",_i="keyup",_j="keypress",_k=function(_l){switch(E(_l)){case 0:return E(_j);case 1:return E(_i);default:return E(_h);}},_m=new T2(0,_k,_e),_n=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_o=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_p=function(_q,_){return new T1(1,_q);},_r=function(_s){return E(_s);},_t=new T2(0,_r,_p),_u=function(_v,_w,_){var _x=B(A1(_v,_)),_y=B(A1(_w,_));return _x;},_z=function(_A,_B,_){var _C=B(A1(_A,_)),_D=B(A1(_B,_));return new T(function(){return B(A1(_C,_D));});},_E=function(_F,_G,_){var _H=B(A1(_G,_));return _F;},_I=function(_J,_K,_){var _L=B(A1(_K,_));return new T(function(){return B(A1(_J,_L));});},_M=new T2(0,_I,_E),_N=function(_O,_){return _O;},_P=function(_Q,_R,_){var _S=B(A1(_Q,_));return new F(function(){return A1(_R,_);});},_T=new T5(0,_M,_N,_z,_P,_u),_U=new T(function(){return B(unCStr("base"));}),_V=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_W=new T(function(){return B(unCStr("IOException"));}),_X=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_U,_V,_W),_Y=__Z,_Z=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_X,_Y,_Y),_10=function(_11){return E(_Z);},_12=function(_13){return E(E(_13).a);},_14=function(_15,_16,_17){var _18=B(A1(_15,_)),_19=B(A1(_16,_)),_1a=hs_eqWord64(_18.a,_19.a);if(!_1a){return __Z;}else{var _1b=hs_eqWord64(_18.b,_19.b);return (!_1b)?__Z:new T1(1,_17);}},_1c=function(_1d){var _1e=E(_1d);return new F(function(){return _14(B(_12(_1e.a)),_10,_1e.b);});},_1f=new T(function(){return B(unCStr(": "));}),_1g=new T(function(){return B(unCStr(")"));}),_1h=new T(function(){return B(unCStr(" ("));}),_1i=function(_1j,_1k){var _1l=E(_1j);return (_1l._==0)?E(_1k):new T2(1,_1l.a,new T(function(){return B(_1i(_1l.b,_1k));}));},_1m=new T(function(){return B(unCStr("interrupted"));}),_1n=new T(function(){return B(unCStr("system error"));}),_1o=new T(function(){return B(unCStr("unsatisified constraints"));}),_1p=new T(function(){return B(unCStr("user error"));}),_1q=new T(function(){return B(unCStr("permission denied"));}),_1r=new T(function(){return B(unCStr("illegal operation"));}),_1s=new T(function(){return B(unCStr("end of file"));}),_1t=new T(function(){return B(unCStr("resource exhausted"));}),_1u=new T(function(){return B(unCStr("resource busy"));}),_1v=new T(function(){return B(unCStr("does not exist"));}),_1w=new T(function(){return B(unCStr("already exists"));}),_1x=new T(function(){return B(unCStr("resource vanished"));}),_1y=new T(function(){return B(unCStr("timeout"));}),_1z=new T(function(){return B(unCStr("unsupported operation"));}),_1A=new T(function(){return B(unCStr("hardware fault"));}),_1B=new T(function(){return B(unCStr("inappropriate type"));}),_1C=new T(function(){return B(unCStr("invalid argument"));}),_1D=new T(function(){return B(unCStr("failed"));}),_1E=new T(function(){return B(unCStr("protocol error"));}),_1F=function(_1G,_1H){switch(E(_1G)){case 0:return new F(function(){return _1i(_1w,_1H);});break;case 1:return new F(function(){return _1i(_1v,_1H);});break;case 2:return new F(function(){return _1i(_1u,_1H);});break;case 3:return new F(function(){return _1i(_1t,_1H);});break;case 4:return new F(function(){return _1i(_1s,_1H);});break;case 5:return new F(function(){return _1i(_1r,_1H);});break;case 6:return new F(function(){return _1i(_1q,_1H);});break;case 7:return new F(function(){return _1i(_1p,_1H);});break;case 8:return new F(function(){return _1i(_1o,_1H);});break;case 9:return new F(function(){return _1i(_1n,_1H);});break;case 10:return new F(function(){return _1i(_1E,_1H);});break;case 11:return new F(function(){return _1i(_1D,_1H);});break;case 12:return new F(function(){return _1i(_1C,_1H);});break;case 13:return new F(function(){return _1i(_1B,_1H);});break;case 14:return new F(function(){return _1i(_1A,_1H);});break;case 15:return new F(function(){return _1i(_1z,_1H);});break;case 16:return new F(function(){return _1i(_1y,_1H);});break;case 17:return new F(function(){return _1i(_1x,_1H);});break;default:return new F(function(){return _1i(_1m,_1H);});}},_1I=new T(function(){return B(unCStr("}"));}),_1J=new T(function(){return B(unCStr("{handle: "));}),_1K=function(_1L,_1M,_1N,_1O,_1P,_1Q){var _1R=new T(function(){var _1S=new T(function(){var _1T=new T(function(){var _1U=E(_1O);if(!_1U._){return E(_1Q);}else{var _1V=new T(function(){return B(_1i(_1U,new T(function(){return B(_1i(_1g,_1Q));},1)));},1);return B(_1i(_1h,_1V));}},1);return B(_1F(_1M,_1T));}),_1W=E(_1N);if(!_1W._){return E(_1S);}else{return B(_1i(_1W,new T(function(){return B(_1i(_1f,_1S));},1)));}}),_1X=E(_1P);if(!_1X._){var _1Y=E(_1L);if(!_1Y._){return E(_1R);}else{var _1Z=E(_1Y.a);if(!_1Z._){var _20=new T(function(){var _21=new T(function(){return B(_1i(_1I,new T(function(){return B(_1i(_1f,_1R));},1)));},1);return B(_1i(_1Z.a,_21));},1);return new F(function(){return _1i(_1J,_20);});}else{var _22=new T(function(){var _23=new T(function(){return B(_1i(_1I,new T(function(){return B(_1i(_1f,_1R));},1)));},1);return B(_1i(_1Z.a,_23));},1);return new F(function(){return _1i(_1J,_22);});}}}else{return new F(function(){return _1i(_1X.a,new T(function(){return B(_1i(_1f,_1R));},1));});}},_24=function(_25){var _26=E(_25);return new F(function(){return _1K(_26.a,_26.b,_26.c,_26.d,_26.f,_Y);});},_27=function(_28){return new T2(0,_29,_28);},_2a=function(_2b,_2c,_2d){var _2e=E(_2c);return new F(function(){return _1K(_2e.a,_2e.b,_2e.c,_2e.d,_2e.f,_2d);});},_2f=function(_2g,_2h){var _2i=E(_2g);return new F(function(){return _1K(_2i.a,_2i.b,_2i.c,_2i.d,_2i.f,_2h);});},_2j=44,_2k=93,_2l=91,_2m=function(_2n,_2o,_2p){var _2q=E(_2o);if(!_2q._){return new F(function(){return unAppCStr("[]",_2p);});}else{var _2r=new T(function(){var _2s=new T(function(){var _2t=function(_2u){var _2v=E(_2u);if(!_2v._){return E(new T2(1,_2k,_2p));}else{var _2w=new T(function(){return B(A2(_2n,_2v.a,new T(function(){return B(_2t(_2v.b));})));});return new T2(1,_2j,_2w);}};return B(_2t(_2q.b));});return B(A2(_2n,_2q.a,_2s));});return new T2(1,_2l,_2r);}},_2x=function(_2y,_2z){return new F(function(){return _2m(_2f,_2y,_2z);});},_2A=new T3(0,_2a,_24,_2x),_29=new T(function(){return new T5(0,_10,_2A,_27,_1c,_24);}),_2B=new T(function(){return E(_29);}),_2C=function(_2D){return E(E(_2D).c);},_2E=__Z,_2F=7,_2G=function(_2H){return new T6(0,_2E,_2F,_Y,_2H,_2E,_2E);},_2I=function(_2J,_){var _2K=new T(function(){return B(A2(_2C,_2B,new T(function(){return B(A1(_2G,_2J));})));});return new F(function(){return die(_2K);});},_2L=function(_2M,_){return new F(function(){return _2I(_2M,_);});},_2N=function(_2O){return new F(function(){return A1(_2L,_2O);});},_2P=function(_2Q,_2R,_){var _2S=B(A1(_2Q,_));return new F(function(){return A2(_2R,_2S,_);});},_2T=new T5(0,_T,_2P,_P,_N,_2N),_2U=new T2(0,_2T,_r),_2V=new T2(0,_2U,_N),_2W=function(_2X,_){var _2Y=E(_2X);if(!_2Y._){return _Y;}else{var _2Z=B(_2W(_2Y.b,_));return new T2(1,_2Y.a,_2Z);}},_30=0,_31=function(_32,_33,_){return new T2(0,function(_34,_){var _35=B(A3(_32,_34,_33,_));return _30;},_33);},_36=function(_37,_38,_){var _39=B(A1(_37,_));return new T2(0,_39,_38);},_3a=function(_3b,_3c,_3d,_){var _3e=B(A2(_3b,_3d,_)),_3f=B(A2(_3c,new T(function(){return E(E(_3e).b);}),_));return new T2(0,new T(function(){return E(E(_3e).a);}),new T(function(){return E(E(_3f).b);}));},_3g=function(_3h,_3i,_3j,_){var _3k=B(A2(_3h,_3j,_)),_3l=B(A2(_3i,new T(function(){return E(E(_3k).b);}),_));return new T2(0,new T(function(){return E(E(_3l).a);}),new T(function(){return E(E(_3l).b);}));},_3m=function(_3n,_3o,_3p,_){var _3q=B(A2(_3n,_3p,_)),_3r=B(A2(_3o,new T(function(){return E(E(_3q).b);}),_)),_3s=new T(function(){return B(A1(E(_3q).a,new T(function(){return E(E(_3r).a);})));});return new T2(0,_3s,new T(function(){return E(E(_3r).b);}));},_3t=function(_3u,_3v,_3w,_){return new F(function(){return _3m(_3u,_3v,_3w,_);});},_3x=function(_3y,_3z,_){return new T2(0,_3y,_3z);},_3A=function(_3v,_3w,_){return new F(function(){return _3x(_3v,_3w,_);});},_3B=function(_3C,_3D,_3E,_){var _3F=B(A2(_3D,_3E,_));return new T2(0,_3C,new T(function(){return E(E(_3F).b);}));},_3G=function(_3H,_3I,_3J,_){var _3K=B(A2(_3I,_3J,_)),_3L=new T(function(){return B(A1(_3H,new T(function(){return E(E(_3K).a);})));});return new T2(0,_3L,new T(function(){return E(E(_3K).b);}));},_3M=function(_3u,_3v,_3w,_){return new F(function(){return _3G(_3u,_3v,_3w,_);});},_3N=new T2(0,_3M,_3B),_3O=new T5(0,_3N,_3A,_3t,_3g,_3a),_3P=function(_3Q,_3R,_3S,_){var _3T=B(A2(_3Q,_3S,_));return new F(function(){return A2(_3R,new T(function(){return E(E(_3T).b);}),_);});},_3U=function(_3u,_3v,_3w,_){return new F(function(){return _3P(_3u,_3v,_3w,_);});},_3V=function(_3W,_3X,_3Y,_){var _3Z=B(A2(_3W,_3Y,_));return new F(function(){return A3(_3X,new T(function(){return E(E(_3Z).a);}),new T(function(){return E(E(_3Z).b);}),_);});},_40=function(_3u,_3v,_3w,_){return new F(function(){return _3V(_3u,_3v,_3w,_);});},_41=function(_42,_43,_){return new F(function(){return _2I(_42,_);});},_44=function(_3v,_3w,_){return new F(function(){return _41(_3v,_3w,_);});},_45=new T5(0,_3O,_40,_3U,_3A,_44),_46=new T2(0,_45,_36),_47=new T2(0,_46,_31),_48=function(_49,_){return _30;},_4a=new T(function(){return B(unCStr("!!: negative index"));}),_4b=new T(function(){return B(unCStr("Prelude."));}),_4c=new T(function(){return B(_1i(_4b,_4a));}),_4d=new T(function(){return B(err(_4c));}),_4e=new T(function(){return B(unCStr("!!: index too large"));}),_4f=new T(function(){return B(_1i(_4b,_4e));}),_4g=new T(function(){return B(err(_4f));}),_4h=function(_4i,_4j){while(1){var _4k=E(_4i);if(!_4k._){return E(_4g);}else{var _4l=E(_4j);if(!_4l){return E(_4k.a);}else{_4i=_4k.b;_4j=_4l-1|0;continue;}}}},_4m=function(_4n,_4o){if(_4o>=0){return new F(function(){return _4h(_4n,_4o);});}else{return E(_4d);}},_4p=function(_4q){var _4r=I_decodeDouble(_4q);return new T2(0,new T1(1,_4r.b),_4r.a);},_4s=function(_4t,_4u){var _4v=E(_4t);if(!_4v._){var _4w=_4v.a,_4x=E(_4u);return (_4x._==0)?_4w==_4x.a:(I_compareInt(_4x.a,_4w)==0)?true:false;}else{var _4y=_4v.a,_4z=E(_4u);return (_4z._==0)?(I_compareInt(_4y,_4z.a)==0)?true:false:(I_compare(_4y,_4z.a)==0)?true:false;}},_4A=new T1(0,0),_4B=function(_4C){var _4D=B(_4p(_4C));return (!B(_4s(_4D.a,_4A)))?_4D.b+53|0:0;},_4E=function(_4F,_4G){var _4H=E(_4F);return (_4H._==0)?_4H.a*Math.pow(2,_4G):I_toNumber(_4H.a)*Math.pow(2,_4G);},_4I=function(_4J,_4K){var _4L=E(_4J);if(!_4L){return E(_4K);}else{if(_4K!=0){var _4M=isDoubleFinite(_4K);if(!E(_4M)){return E(_4K);}else{var _4N=B(_4p(_4K)),_4O=_4N.a,_4P=_4N.b;if(2257>_4L){if(-2257>_4L){return new F(function(){return _4E(_4O,_4P+(-2257)|0);});}else{return new F(function(){return _4E(_4O,_4P+_4L|0);});}}else{return new F(function(){return _4E(_4O,_4P+2257|0);});}}}else{return E(_4K);}}},_4Q=function(_4R,_4S){var _4T=B(_4B(_4R)),_4U=B(_4B(_4S)),_4V=function(_4W){var _4X= -_4W,_4Y=B(_4I(_4X,_4R)),_4Z=B(_4I(_4X,_4S));return new F(function(){return _4I(_4W,Math.sqrt(_4Y*_4Y+_4Z*_4Z));});};if(_4T>_4U){return new F(function(){return _4V(_4T);});}else{return new F(function(){return _4V(_4U);});}},_50=function(_51,_52){if(_52<=0){var _53=function(_54){var _55=function(_56){var _57=function(_58){var _59=function(_5a){var _5b=isDoubleNegativeZero(_52),_5c=_5b,_5d=function(_5e){var _5f=E(_51);return (_5f!=0)?_52+_5f:(_52>=0)?(E(_5c)==0)?(_52!=0)?_52+_5f:E(_5f):3.141592653589793:3.141592653589793;};if(!E(_5c)){return new F(function(){return _5d(_);});}else{var _5g=E(_51),_5h=isDoubleNegativeZero(_5g);if(!E(_5h)){return new F(function(){return _5d(_);});}else{return  -B(_50( -_5g,_52));}}};if(_52>=0){return new F(function(){return _59(_);});}else{var _5i=E(_51),_5j=isDoubleNegativeZero(_5i);if(!E(_5j)){return new F(function(){return _59(_);});}else{return  -B(_50( -_5i,_52));}}};if(_52>0){return new F(function(){return _57(_);});}else{var _5k=E(_51);if(_5k>=0){return new F(function(){return _57(_);});}else{return  -B(_50( -_5k,_52));}}};if(_52>=0){return new F(function(){return _55(_);});}else{var _5l=E(_51);if(_5l<=0){return new F(function(){return _55(_);});}else{return 3.141592653589793+Math.atan(_5l/_52);}}};if(_52!=0){return new F(function(){return _53(_);});}else{if(E(_51)<=0){return new F(function(){return _53(_);});}else{return 1.5707963267948966;}}}else{return new F(function(){return Math.atan(E(_51)/_52);});}},_5m=function(_5n,_5o){if(_5n!=0){return new F(function(){return _50(_5o,_5n);});}else{if(_5o!=0){return new F(function(){return _50(_5o,_5n);});}else{return 0;}}},_5p=function(_){return _30;},_5q=new T(function(){return eval("(function(ctx, x, y, radius, fromAngle, toAngle){ctx.arc(x, y, radius, fromAngle, toAngle);})");}),_5r=0,_5s=6.283185307179586,_5t=new T(function(){return eval("(function(ctx,x,y){ctx.moveTo(x,y);})");}),_5u=function(_5v,_5w,_5x,_5y,_){var _5z=__app3(E(_5t),_5y,_5v+_5x,_5w),_5A=__apply(E(_5q),new T2(1,_5s,new T2(1,_5r,new T2(1,_5x,new T2(1,_5w,new T2(1,_5v,new T2(1,_5y,_Y)))))));return new F(function(){return _5p(_);});},_5B=new T(function(){return eval("(function(ctx){ctx.beginPath();})");}),_5C=new T(function(){return eval("(function(ctx){ctx.fill();})");}),_5D=function(_5E,_5F,_){var _5G=__app1(E(_5B),_5F),_5H=B(A2(_5E,_5F,_)),_5I=__app1(E(_5C),_5F);return new F(function(){return _5p(_);});},_5J=new T(function(){return eval("(function(ctx){ctx.stroke();})");}),_5K=function(_5L,_5M,_){var _5N=__app1(E(_5B),_5M),_5O=B(A2(_5L,_5M,_)),_5P=__app1(E(_5J),_5M);return new F(function(){return _5p(_);});},_5Q=new T(function(){return eval("(function(ctx){ctx.restore();})");}),_5R=new T(function(){return eval("(function(ctx){ctx.save();})");}),_5S=new T(function(){return eval("(function(ctx,x,y){ctx.translate(x,y);})");}),_5T=function(_5U,_5V,_5W,_5X,_){var _5Y=__app1(E(_5R),_5X),_5Z=__app3(E(_5S),_5X,E(_5U),E(_5V)),_60=B(A2(_5W,_5X,_)),_61=__app1(E(_5Q),_5X);return new F(function(){return _5p(_);});},_62=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_63=function(_64,_65,_66){var _67=new T(function(){return toJSStr(E(_66));});return function(_68,_){var _69=__app4(E(_62),E(_68),E(_67),E(_64),E(_65));return new F(function(){return _5p(_);});};},_6a=function(_6b,_6c){var _6d=E(_6c);if(!_6d._){return __Z;}else{var _6e=_6d.a,_6f=E(_6b);return (_6f==1)?new T2(1,_6e,_Y):new T2(1,_6e,new T(function(){return B(_6a(_6f-1|0,_6d.b));}));}},_6g=false,_6h=true,_6i=0,_6j=new T(function(){return B(unCStr(": empty list"));}),_6k=function(_6l){return new F(function(){return err(B(_1i(_4b,new T(function(){return B(_1i(_6l,_6j));},1))));});},_6m=new T(function(){return B(unCStr("head"));}),_6n=new T(function(){return B(_6k(_6m));}),_6o=new T(function(){return eval("(function(e){e.width = e.width;})");}),_6p=",",_6q="rgba(",_6r=new T(function(){return toJSStr(_Y);}),_6s="rgb(",_6t=")",_6u=new T2(1,_6t,_Y),_6v=function(_6w){var _6x=E(_6w);if(!_6x._){var _6y=jsCat(new T2(1,_6s,new T2(1,new T(function(){return String(_6x.a);}),new T2(1,_6p,new T2(1,new T(function(){return String(_6x.b);}),new T2(1,_6p,new T2(1,new T(function(){return String(_6x.c);}),_6u)))))),E(_6r));return E(_6y);}else{var _6z=jsCat(new T2(1,_6q,new T2(1,new T(function(){return String(_6x.a);}),new T2(1,_6p,new T2(1,new T(function(){return String(_6x.b);}),new T2(1,_6p,new T2(1,new T(function(){return String(_6x.c);}),new T2(1,_6p,new T2(1,new T(function(){return String(_6x.d);}),_6u)))))))),E(_6r));return E(_6z);}},_6A="strokeStyle",_6B="fillStyle",_6C=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_6D=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_6E=function(_6F,_6G){var _6H=new T(function(){return B(_6v(_6F));});return function(_6I,_){var _6J=E(_6I),_6K=E(_6B),_6L=E(_6C),_6M=__app2(_6L,_6J,_6K),_6N=E(_6A),_6O=__app2(_6L,_6J,_6N),_6P=E(_6H),_6Q=E(_6D),_6R=__app3(_6Q,_6J,_6K,_6P),_6S=__app3(_6Q,_6J,_6N,_6P),_6T=B(A2(_6G,_6J,_)),_6U=String(_6M),_6V=__app3(_6Q,_6J,_6K,_6U),_6W=String(_6O),_6X=__app3(_6Q,_6J,_6N,_6W);return new F(function(){return _5p(_);});};},_6Y=new T(function(){return eval("(function(){ return dat; })");}),_6Z=function(_70,_71){return E(_70)==E(_71);},_72=function(_73,_74){return E(_73)!=E(_74);},_75=new T2(0,_6Z,_72),_76=function(_77,_78){while(1){var _79=E(_77);if(!_79._){return E(_78);}else{var _7a=_78+1|0;_77=_79.b;_78=_7a;continue;}}},_7b=function(_7c,_7d){var _7e=E(_7d);if(!_7e._){return new T2(0,_Y,_Y);}else{var _7f=_7e.a,_7g=_7e.b,_7h=E(_7c);if(_7h==1){return new T2(0,new T2(1,_7f,_Y),_7g);}else{var _7i=new T(function(){var _7j=B(_7b(_7h-1|0,_7g));return new T2(0,_7j.a,_7j.b);});return new T2(0,new T2(1,_7f,new T(function(){return E(E(_7i).a);})),new T(function(){return E(E(_7i).b);}));}}},_7k=function(_7l,_7m){if(_7l<=0){if(_7l>=0){return new F(function(){return quot(_7l,_7m);});}else{if(_7m<=0){return new F(function(){return quot(_7l,_7m);});}else{return quot(_7l+1|0,_7m)-1|0;}}}else{if(_7m>=0){if(_7l>=0){return new F(function(){return quot(_7l,_7m);});}else{if(_7m<=0){return new F(function(){return quot(_7l,_7m);});}else{return quot(_7l+1|0,_7m)-1|0;}}}else{return quot(_7l-1|0,_7m)-1|0;}}},_7n=new T(function(){return B(unCStr("base"));}),_7o=new T(function(){return B(unCStr("GHC.Exception"));}),_7p=new T(function(){return B(unCStr("ArithException"));}),_7q=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_7n,_7o,_7p),_7r=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_7q,_Y,_Y),_7s=function(_7t){return E(_7r);},_7u=function(_7v){var _7w=E(_7v);return new F(function(){return _14(B(_12(_7w.a)),_7s,_7w.b);});},_7x=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_7y=new T(function(){return B(unCStr("denormal"));}),_7z=new T(function(){return B(unCStr("divide by zero"));}),_7A=new T(function(){return B(unCStr("loss of precision"));}),_7B=new T(function(){return B(unCStr("arithmetic underflow"));}),_7C=new T(function(){return B(unCStr("arithmetic overflow"));}),_7D=function(_7E,_7F){switch(E(_7E)){case 0:return new F(function(){return _1i(_7C,_7F);});break;case 1:return new F(function(){return _1i(_7B,_7F);});break;case 2:return new F(function(){return _1i(_7A,_7F);});break;case 3:return new F(function(){return _1i(_7z,_7F);});break;case 4:return new F(function(){return _1i(_7y,_7F);});break;default:return new F(function(){return _1i(_7x,_7F);});}},_7G=function(_7H){return new F(function(){return _7D(_7H,_Y);});},_7I=function(_7J,_7K,_7L){return new F(function(){return _7D(_7K,_7L);});},_7M=function(_7N,_7O){return new F(function(){return _2m(_7D,_7N,_7O);});},_7P=new T3(0,_7I,_7G,_7M),_7Q=new T(function(){return new T5(0,_7s,_7P,_7R,_7u,_7G);}),_7R=function(_7S){return new T2(0,_7Q,_7S);},_7T=3,_7U=new T(function(){return B(_7R(_7T));}),_7V=new T(function(){return die(_7U);}),_7W=function(_7X){return E(E(_7X).a);},_7Y=function(_7Z,_80,_81){while(1){var _82=E(_81);if(!_82._){return false;}else{if(!B(A3(_7W,_7Z,_80,_82.a))){_81=_82.b;continue;}else{return true;}}}},_83=function(_84,_85){var _86=new T(function(){var _87=B(_83(_84,new T(function(){return B(A1(_84,_85));})));return new T2(1,_87.a,_87.b);});return new T2(0,_85,_86);},_88=function(_89){return imul(E(_89),2)|0;},_8a=1,_8b=new T(function(){var _8c=B(_83(_88,_8a));return new T2(1,_8c.a,_8c.b);}),_8d=function(_8e,_8f){var _8g=_8e%_8f;if(_8e<=0){if(_8e>=0){return E(_8g);}else{if(_8f<=0){return E(_8g);}else{var _8h=E(_8g);return (_8h==0)?0:_8h+_8f|0;}}}else{if(_8f>=0){if(_8e>=0){return E(_8g);}else{if(_8f<=0){return E(_8g);}else{var _8i=E(_8g);return (_8i==0)?0:_8i+_8f|0;}}}else{var _8j=E(_8g);return (_8j==0)?0:_8j+_8f|0;}}},_8k=function(_8l,_8m){var _8n=E(_8m);if(!_8n._){return __Z;}else{var _8o=_8n.a;return (!B(A1(_8l,_8o)))?__Z:new T2(1,_8o,new T(function(){return B(_8k(_8l,_8n.b));}));}},_8p=new T(function(){return B(unCStr("Prelude.undefined"));}),_8q=new T(function(){return B(err(_8p));}),_8r=function(_8s,_8t){if(!B(_7Y(_75,_8s,B(_8k(function(_8u){return E(_8u)<=_8s;},_8b))))){return E(_8q);}else{if(_8s>1){var _8v=_8s-1|0;if(0<=_8v){var _8w=new T(function(){return B(_7k(_8s,2));}),_8x=new T(function(){var _8y=B(_7k(B(_76(_8t,0)),2));if(_8y>0){var _8z=B(_7b(_8y,_8t));return new T2(0,_8z.a,_8z.b);}else{return new T2(0,_Y,_8t);}}),_8A=new T(function(){return B(_8r(E(_8w),new T(function(){return E(E(_8x).a);})));}),_8B=new T(function(){return B(_8r(E(_8w),new T(function(){return E(E(_8x).b);})));}),_8C=new T(function(){return B(_4m(_8B,0));}),_8D=function(_8E){var _8F=new T(function(){var _8G=E(_8w),_8H=function(_8I){var _8J=B(_4m(_8A,_8I)),_8K=E(_8J.a),_8L=E(_8J.b),_8M=E(_8G);switch(_8M){case -1:var _8N=E(_8C),_8O=E(_8N.a),_8P=E(_8N.b),_8Q= -(6.283185307179586*_8E/_8s),_8R=Math.cos(_8Q),_8S=Math.sin(_8Q);return new T2(0,_8K+(_8O*_8R-_8P*_8S),_8L+_8O*_8S+_8P*_8R);case 0:return E(_7V);default:var _8T=B(_4m(_8B,B(_8d(_8E,_8M)))),_8U=E(_8T.a),_8V=E(_8T.b),_8W= -(6.283185307179586*_8E/_8s),_8X=Math.cos(_8W),_8Y=Math.sin(_8W);return new T2(0,_8K+(_8U*_8X-_8V*_8Y),_8L+_8U*_8Y+_8V*_8X);}},_8Z=E(_8G);switch(_8Z){case -1:var _90=B(_8H(0));return new T2(0,E(_90.a),E(_90.b));break;case 0:return E(_7V);break;default:var _91=B(_8H(B(_8d(_8E,_8Z))));return new T2(0,E(_91.a),E(_91.b));}});return new T2(1,_8F,new T(function(){if(_8E!=_8v){return B(_8D(_8E+1|0));}else{return __Z;}}));};return new F(function(){return _8D(0);});}else{return __Z;}}else{return E(_8t);}}},_92=function(_93){var _94=E(_93);return (_94==0)?__Z:new T2(1,_94&1,new T(function(){return B(_92(_94>>1));}));},_95=function(_96,_97){while(1){var _98=E(_96);if(!_98._){return E(_97);}else{var _99=(imul(_97,2)|0)+E(_98.a)|0;_96=_98.b;_97=_99;continue;}}},_9a=function(_9b,_9c){while(1){var _9d=E(_9b);if(!_9d._){return E(_9c);}else{var _9e=(imul(_9c,2)|0)+E(_9d.a)|0;_9b=_9d.b;_9c=_9e;continue;}}},_9f=function(_9g,_9h){if(_9g<=_9h){var _9i=function(_9j){return new T2(1,_9j,new T(function(){if(_9j!=_9h){return B(_9i(_9j+1|0));}else{return __Z;}}));};return new F(function(){return _9i(_9g);});}else{return __Z;}},_9k=new T(function(){return B(_9f(0,2147483647));}),_9l=0,_9m=function(_9n){return new T2(1,_9l,_9n);},_9o=function(_9p){return E(E(E(_9p).b).b);},_9q=function(_9r,_9s){return (_9r>=_9s)?(_9r!=_9s)?2:1:0;},_9t=function(_9u,_9v){return new F(function(){return _9q(E(E(_9u).a),E(E(_9v).a));});},_9w=function(_9x,_9y){var _9z=E(_9y);return (_9z._==0)?__Z:new T2(1,new T(function(){return B(A1(_9x,_9z.a));}),new T(function(){return B(_9w(_9x,_9z.b));}));},_9A=function(_9B,_9C){while(1){var _9D=E(_9B);if(!_9D._){return E(_9C);}else{var _9E=new T2(1,_9D.a,_9C);_9B=_9D.b;_9C=_9E;continue;}}},_9F=new T2(1,_Y,_Y),_9G=function(_9H,_9I){var _9J=function(_9K,_9L){var _9M=E(_9K);if(!_9M._){return E(_9L);}else{var _9N=_9M.a,_9O=E(_9L);if(!_9O._){return E(_9M);}else{var _9P=_9O.a;return (B(A2(_9H,_9N,_9P))==2)?new T2(1,_9P,new T(function(){return B(_9J(_9M,_9O.b));})):new T2(1,_9N,new T(function(){return B(_9J(_9M.b,_9O));}));}}},_9Q=function(_9R){var _9S=E(_9R);if(!_9S._){return __Z;}else{var _9T=E(_9S.b);return (_9T._==0)?E(_9S):new T2(1,new T(function(){return B(_9J(_9S.a,_9T.a));}),new T(function(){return B(_9Q(_9T.b));}));}},_9U=new T(function(){return B(_9V(B(_9Q(_Y))));}),_9V=function(_9W){while(1){var _9X=E(_9W);if(!_9X._){return E(_9U);}else{if(!E(_9X.b)._){return E(_9X.a);}else{_9W=B(_9Q(_9X));continue;}}}},_9Y=new T(function(){return B(_9Z(_Y));}),_a0=function(_a1,_a2,_a3){while(1){var _a4=B((function(_a5,_a6,_a7){var _a8=E(_a7);if(!_a8._){return new T2(1,new T2(1,_a5,_a6),_9Y);}else{var _a9=_a8.a;if(B(A2(_9H,_a5,_a9))==2){var _aa=new T2(1,_a5,_a6);_a1=_a9;_a2=_aa;_a3=_a8.b;return __continue;}else{return new T2(1,new T2(1,_a5,_a6),new T(function(){return B(_9Z(_a8));}));}}})(_a1,_a2,_a3));if(_a4!=__continue){return _a4;}}},_ab=function(_ac,_ad,_ae){while(1){var _af=B((function(_ag,_ah,_ai){var _aj=E(_ai);if(!_aj._){return new T2(1,new T(function(){return B(A1(_ah,new T2(1,_ag,_Y)));}),_9Y);}else{var _ak=_aj.a,_al=_aj.b;switch(B(A2(_9H,_ag,_ak))){case 0:_ac=_ak;_ad=function(_am){return new F(function(){return A1(_ah,new T2(1,_ag,_am));});};_ae=_al;return __continue;case 1:_ac=_ak;_ad=function(_an){return new F(function(){return A1(_ah,new T2(1,_ag,_an));});};_ae=_al;return __continue;default:return new T2(1,new T(function(){return B(A1(_ah,new T2(1,_ag,_Y)));}),new T(function(){return B(_9Z(_aj));}));}}})(_ac,_ad,_ae));if(_af!=__continue){return _af;}}},_9Z=function(_ao){var _ap=E(_ao);if(!_ap._){return E(_9F);}else{var _aq=_ap.a,_ar=E(_ap.b);if(!_ar._){return new T2(1,_ap,_Y);}else{var _as=_ar.a,_at=_ar.b;if(B(A2(_9H,_aq,_as))==2){return new F(function(){return _a0(_as,new T2(1,_aq,_Y),_at);});}else{return new F(function(){return _ab(_as,function(_au){return new T2(1,_aq,_au);},_at);});}}}};return new F(function(){return _9V(B(_9Z(_9I)));});},_av=function(_aw){var _ax=B(_76(_aw,0)),_ay=new T(function(){var _az=new T(function(){var _aA=Math.log(_ax)/Math.log(2),_aB=_aA&4294967295;if(_aA>=_aB){return _aB;}else{return _aB-1|0;}}),_aC=function(_aD,_aE){var _aF=E(_aD);if(!_aF._){return __Z;}else{var _aG=E(_aE);return (_aG._==0)?__Z:new T2(1,new T(function(){var _aH=E(_aF.a),_aI=B(_9A(B(_92(_aH)),_Y)),_aJ=B(_76(_aI,0)),_aK=E(_az);if(_aJ>=_aK){var _aL=B(_95(B(_9A(_aI,_Y)),0));}else{var _aM=B(_83(_9m,_aI)),_aL=B(_9a(B(_9A(B(_4m(new T2(1,_aM.a,_aM.b),_aK-_aJ|0)),_Y)),0));}return new T2(0,_aL,new T2(0,_aH,_aG.a));}),new T(function(){return B(_aC(_aF.b,_aG.b));}));}};return B(_9w(_9o,B(_9G(_9t,B(_aC(_9k,_aw))))));});return new F(function(){return _8r(_ax,_ay);});},_aN="font",_aO=function(_aP,_aQ){var _aR=new T(function(){return toJSStr(E(_aP));});return function(_aS,_){var _aT=E(_aS),_aU=E(_aN),_aV=__app2(E(_6C),_aT,_aU),_aW=E(_6D),_aX=__app3(_aW,_aT,_aU,E(_aR)),_aY=B(A2(_aQ,_aT,_)),_aZ=String(_aV),_b0=__app3(_aW,_aT,_aU,_aZ);return new F(function(){return _5p(_);});};},_b1=new T(function(){return eval("(function(ctx,x,y){ctx.lineTo(x,y);})");}),_b2=function(_b3,_b4,_){var _b5=E(_b3);if(!_b5._){return _30;}else{var _b6=E(_b5.a),_b7=E(_b4),_b8=__app3(E(_5t),_b7,E(_b6.a),E(_b6.b)),_b9=E(_b5.b);if(!_b9._){return _30;}else{var _ba=E(_b9.a),_bb=E(_b1),_bc=__app3(_bb,_b7,E(_ba.a),E(_ba.b)),_bd=function(_be,_){while(1){var _bf=E(_be);if(!_bf._){return _30;}else{var _bg=E(_bf.a),_bh=__app3(_bb,_b7,E(_bg.a),E(_bg.b));_be=_bf.b;continue;}}};return new F(function(){return _bd(_b9.b,_);});}}},_bi="lineWidth",_bj=function(_bk,_bl){var _bm=new T(function(){return String(E(_bk));});return function(_bn,_){var _bo=E(_bn),_bp=E(_bi),_bq=__app2(E(_6C),_bo,_bp),_br=E(_6D),_bs=__app3(_br,_bo,_bp,E(_bm)),_bt=B(A2(_bl,_bo,_)),_bu=String(_bq),_bv=__app3(_br,_bo,_bp,_bu);return new F(function(){return _5p(_);});};},_bw=0.5,_bx=2,_by=new T3(0,40,40,40),_bz=new T1(0,1),_bA=function(_bB,_bC){var _bD=E(_bB);if(!_bD._){var _bE=_bD.a,_bF=E(_bC);if(!_bF._){var _bG=_bF.a;return (_bE!=_bG)?(_bE>_bG)?2:0:1;}else{var _bH=I_compareInt(_bF.a,_bE);return (_bH<=0)?(_bH>=0)?1:2:0;}}else{var _bI=_bD.a,_bJ=E(_bC);if(!_bJ._){var _bK=I_compareInt(_bI,_bJ.a);return (_bK>=0)?(_bK<=0)?1:2:0;}else{var _bL=I_compare(_bI,_bJ.a);return (_bL>=0)?(_bL<=0)?1:2:0;}}},_bM=function(_bN){var _bO=E(_bN);if(!_bO._){return E(_bO.a);}else{return new F(function(){return I_toInt(_bO.a);});}},_bP=function(_bQ,_bR){while(1){var _bS=E(_bQ);if(!_bS._){var _bT=_bS.a,_bU=E(_bR);if(!_bU._){var _bV=_bU.a,_bW=addC(_bT,_bV);if(!E(_bW.b)){return new T1(0,_bW.a);}else{_bQ=new T1(1,I_fromInt(_bT));_bR=new T1(1,I_fromInt(_bV));continue;}}else{_bQ=new T1(1,I_fromInt(_bT));_bR=_bU;continue;}}else{var _bX=E(_bR);if(!_bX._){_bQ=_bS;_bR=new T1(1,I_fromInt(_bX.a));continue;}else{return new T1(1,I_add(_bS.a,_bX.a));}}}},_bY=function(_bZ,_c0){while(1){var _c1=E(_bZ);if(!_c1._){var _c2=E(_c1.a);if(_c2==(-2147483648)){_bZ=new T1(1,I_fromInt(-2147483648));continue;}else{var _c3=E(_c0);if(!_c3._){var _c4=_c3.a;return new T2(0,new T1(0,quot(_c2,_c4)),new T1(0,_c2%_c4));}else{_bZ=new T1(1,I_fromInt(_c2));_c0=_c3;continue;}}}else{var _c5=E(_c0);if(!_c5._){_bZ=_c1;_c0=new T1(1,I_fromInt(_c5.a));continue;}else{var _c6=I_quotRem(_c1.a,_c5.a);return new T2(0,new T1(1,_c6.a),new T1(1,_c6.b));}}}},_c7=function(_c8,_c9){while(1){var _ca=E(_c8);if(!_ca._){_c8=new T1(1,I_fromInt(_ca.a));continue;}else{return new T1(1,I_shiftLeft(_ca.a,_c9));}}},_cb=function(_cc,_cd,_ce){if(!B(_4s(_ce,_4A))){var _cf=B(_bY(_cd,_ce)),_cg=_cf.a;switch(B(_bA(B(_c7(_cf.b,1)),_ce))){case 0:return new F(function(){return _4E(_cg,_cc);});break;case 1:if(!(B(_bM(_cg))&1)){return new F(function(){return _4E(_cg,_cc);});}else{return new F(function(){return _4E(B(_bP(_cg,_bz)),_cc);});}break;default:return new F(function(){return _4E(B(_bP(_cg,_bz)),_cc);});}}else{return E(_7V);}},_ch=function(_ci,_cj){var _ck=E(_ci);if(!_ck._){var _cl=_ck.a,_cm=E(_cj);return (_cm._==0)?_cl>_cm.a:I_compareInt(_cm.a,_cl)<0;}else{var _cn=_ck.a,_co=E(_cj);return (_co._==0)?I_compareInt(_cn,_co.a)>0:I_compare(_cn,_co.a)>0;}},_cp=new T1(0,1),_cq=function(_cr,_cs){var _ct=E(_cr);if(!_ct._){var _cu=_ct.a,_cv=E(_cs);return (_cv._==0)?_cu<_cv.a:I_compareInt(_cv.a,_cu)>0;}else{var _cw=_ct.a,_cx=E(_cs);return (_cx._==0)?I_compareInt(_cw,_cx.a)<0:I_compare(_cw,_cx.a)<0;}},_cy=new T(function(){return B(unCStr("base"));}),_cz=new T(function(){return B(unCStr("Control.Exception.Base"));}),_cA=new T(function(){return B(unCStr("PatternMatchFail"));}),_cB=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_cy,_cz,_cA),_cC=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_cB,_Y,_Y),_cD=function(_cE){return E(_cC);},_cF=function(_cG){var _cH=E(_cG);return new F(function(){return _14(B(_12(_cH.a)),_cD,_cH.b);});},_cI=function(_cJ){return E(E(_cJ).a);},_cK=function(_cL){return new T2(0,_cM,_cL);},_cN=function(_cO,_cP){return new F(function(){return _1i(E(_cO).a,_cP);});},_cQ=function(_cR,_cS){return new F(function(){return _2m(_cN,_cR,_cS);});},_cT=function(_cU,_cV,_cW){return new F(function(){return _1i(E(_cV).a,_cW);});},_cX=new T3(0,_cT,_cI,_cQ),_cM=new T(function(){return new T5(0,_cD,_cX,_cK,_cF,_cI);}),_cY=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_cZ=function(_d0,_d1){return new F(function(){return die(new T(function(){return B(A2(_2C,_d1,_d0));}));});},_d2=function(_d3,_7S){return new F(function(){return _cZ(_d3,_7S);});},_d4=function(_d5,_d6){var _d7=E(_d6);if(!_d7._){return new T2(0,_Y,_Y);}else{var _d8=_d7.a;if(!B(A1(_d5,_d8))){return new T2(0,_Y,_d7);}else{var _d9=new T(function(){var _da=B(_d4(_d5,_d7.b));return new T2(0,_da.a,_da.b);});return new T2(0,new T2(1,_d8,new T(function(){return E(E(_d9).a);})),new T(function(){return E(E(_d9).b);}));}}},_db=32,_dc=new T(function(){return B(unCStr("\n"));}),_dd=function(_de){return (E(_de)==124)?false:true;},_df=function(_dg,_dh){var _di=B(_d4(_dd,B(unCStr(_dg)))),_dj=_di.a,_dk=function(_dl,_dm){var _dn=new T(function(){var _do=new T(function(){return B(_1i(_dh,new T(function(){return B(_1i(_dm,_dc));},1)));});return B(unAppCStr(": ",_do));},1);return new F(function(){return _1i(_dl,_dn);});},_dp=E(_di.b);if(!_dp._){return new F(function(){return _dk(_dj,_Y);});}else{if(E(_dp.a)==124){return new F(function(){return _dk(_dj,new T2(1,_db,_dp.b));});}else{return new F(function(){return _dk(_dj,_Y);});}}},_dq=function(_dr){return new F(function(){return _d2(new T1(0,new T(function(){return B(_df(_dr,_cY));})),_cM);});},_ds=function(_dt){var _du=function(_dv,_dw){while(1){if(!B(_cq(_dv,_dt))){if(!B(_ch(_dv,_dt))){if(!B(_4s(_dv,_dt))){return new F(function(){return _dq("GHC/Integer/Type.lhs:(555,5)-(557,32)|function l2");});}else{return E(_dw);}}else{return _dw-1|0;}}else{var _dx=B(_c7(_dv,1)),_dy=_dw+1|0;_dv=_dx;_dw=_dy;continue;}}};return new F(function(){return _du(_cp,0);});},_dz=function(_dA){var _dB=E(_dA);if(!_dB._){var _dC=_dB.a>>>0;if(!_dC){return -1;}else{var _dD=function(_dE,_dF){while(1){if(_dE>=_dC){if(_dE<=_dC){if(_dE!=_dC){return new F(function(){return _dq("GHC/Integer/Type.lhs:(611,5)-(613,40)|function l2");});}else{return E(_dF);}}else{return _dF-1|0;}}else{var _dG=imul(_dE,2)>>>0,_dH=_dF+1|0;_dE=_dG;_dF=_dH;continue;}}};return new F(function(){return _dD(1,0);});}}else{return new F(function(){return _ds(_dB);});}},_dI=function(_dJ){var _dK=E(_dJ);if(!_dK._){var _dL=_dK.a>>>0;if(!_dL){return new T2(0,-1,0);}else{var _dM=function(_dN,_dO){while(1){if(_dN>=_dL){if(_dN<=_dL){if(_dN!=_dL){return new F(function(){return _dq("GHC/Integer/Type.lhs:(611,5)-(613,40)|function l2");});}else{return E(_dO);}}else{return _dO-1|0;}}else{var _dP=imul(_dN,2)>>>0,_dQ=_dO+1|0;_dN=_dP;_dO=_dQ;continue;}}};return new T2(0,B(_dM(1,0)),(_dL&_dL-1>>>0)>>>0&4294967295);}}else{var _dR=_dK.a;return new T2(0,B(_dz(_dK)),I_compareInt(I_and(_dR,I_sub(_dR,I_fromInt(1))),0));}},_dS=function(_dT,_dU){var _dV=E(_dT);if(!_dV._){var _dW=_dV.a,_dX=E(_dU);return (_dX._==0)?_dW<=_dX.a:I_compareInt(_dX.a,_dW)>=0;}else{var _dY=_dV.a,_dZ=E(_dU);return (_dZ._==0)?I_compareInt(_dY,_dZ.a)<=0:I_compare(_dY,_dZ.a)<=0;}},_e0=function(_e1,_e2){while(1){var _e3=E(_e1);if(!_e3._){var _e4=_e3.a,_e5=E(_e2);if(!_e5._){return new T1(0,(_e4>>>0&_e5.a>>>0)>>>0&4294967295);}else{_e1=new T1(1,I_fromInt(_e4));_e2=_e5;continue;}}else{var _e6=E(_e2);if(!_e6._){_e1=_e3;_e2=new T1(1,I_fromInt(_e6.a));continue;}else{return new T1(1,I_and(_e3.a,_e6.a));}}}},_e7=function(_e8,_e9){while(1){var _ea=E(_e8);if(!_ea._){var _eb=_ea.a,_ec=E(_e9);if(!_ec._){var _ed=_ec.a,_ee=subC(_eb,_ed);if(!E(_ee.b)){return new T1(0,_ee.a);}else{_e8=new T1(1,I_fromInt(_eb));_e9=new T1(1,I_fromInt(_ed));continue;}}else{_e8=new T1(1,I_fromInt(_eb));_e9=_ec;continue;}}else{var _ef=E(_e9);if(!_ef._){_e8=_ea;_e9=new T1(1,I_fromInt(_ef.a));continue;}else{return new T1(1,I_sub(_ea.a,_ef.a));}}}},_eg=new T1(0,2),_eh=function(_ei,_ej){var _ek=E(_ei);if(!_ek._){var _el=(_ek.a>>>0&(2<<_ej>>>0)-1>>>0)>>>0,_em=1<<_ej>>>0;return (_em<=_el)?(_em>=_el)?1:2:0;}else{var _en=B(_e0(_ek,B(_e7(B(_c7(_eg,_ej)),_cp)))),_eo=B(_c7(_cp,_ej));return (!B(_ch(_eo,_en)))?(!B(_cq(_eo,_en)))?1:2:0;}},_ep=function(_eq,_er){while(1){var _es=E(_eq);if(!_es._){_eq=new T1(1,I_fromInt(_es.a));continue;}else{return new T1(1,I_shiftRight(_es.a,_er));}}},_et=function(_eu,_ev,_ew,_ex){var _ey=B(_dI(_ex)),_ez=_ey.a;if(!E(_ey.b)){var _eA=B(_dz(_ew));if(_eA<((_ez+_eu|0)-1|0)){var _eB=_ez+(_eu-_ev|0)|0;if(_eB>0){if(_eB>_eA){if(_eB<=(_eA+1|0)){if(!E(B(_dI(_ew)).b)){return 0;}else{return new F(function(){return _4E(_bz,_eu-_ev|0);});}}else{return 0;}}else{var _eC=B(_ep(_ew,_eB));switch(B(_eh(_ew,_eB-1|0))){case 0:return new F(function(){return _4E(_eC,_eu-_ev|0);});break;case 1:if(!(B(_bM(_eC))&1)){return new F(function(){return _4E(_eC,_eu-_ev|0);});}else{return new F(function(){return _4E(B(_bP(_eC,_bz)),_eu-_ev|0);});}break;default:return new F(function(){return _4E(B(_bP(_eC,_bz)),_eu-_ev|0);});}}}else{return new F(function(){return _4E(_ew,(_eu-_ev|0)-_eB|0);});}}else{if(_eA>=_ev){var _eD=B(_ep(_ew,(_eA+1|0)-_ev|0));switch(B(_eh(_ew,_eA-_ev|0))){case 0:return new F(function(){return _4E(_eD,((_eA-_ez|0)+1|0)-_ev|0);});break;case 2:return new F(function(){return _4E(B(_bP(_eD,_bz)),((_eA-_ez|0)+1|0)-_ev|0);});break;default:if(!(B(_bM(_eD))&1)){return new F(function(){return _4E(_eD,((_eA-_ez|0)+1|0)-_ev|0);});}else{return new F(function(){return _4E(B(_bP(_eD,_bz)),((_eA-_ez|0)+1|0)-_ev|0);});}}}else{return new F(function(){return _4E(_ew, -_ez);});}}}else{var _eE=B(_dz(_ew))-_ez|0,_eF=function(_eG){var _eH=function(_eI,_eJ){if(!B(_dS(B(_c7(_eJ,_ev)),_eI))){return new F(function(){return _cb(_eG-_ev|0,_eI,_eJ);});}else{return new F(function(){return _cb((_eG-_ev|0)+1|0,_eI,B(_c7(_eJ,1)));});}};if(_eG>=_ev){if(_eG!=_ev){return new F(function(){return _eH(_ew,new T(function(){return B(_c7(_ex,_eG-_ev|0));}));});}else{return new F(function(){return _eH(_ew,_ex);});}}else{return new F(function(){return _eH(new T(function(){return B(_c7(_ew,_ev-_eG|0));}),_ex);});}};if(_eu>_eE){return new F(function(){return _eF(_eu);});}else{return new F(function(){return _eF(_eE);});}}},_eK=new T1(0,2147483647),_eL=new T(function(){return B(_bP(_eK,_cp));}),_eM=function(_eN){var _eO=E(_eN);if(!_eO._){var _eP=E(_eO.a);return (_eP==(-2147483648))?E(_eL):new T1(0, -_eP);}else{return new T1(1,I_negate(_eO.a));}},_eQ=new T(function(){return 0/0;}),_eR=new T(function(){return -1/0;}),_eS=new T(function(){return 1/0;}),_eT=0,_eU=function(_eV,_eW){if(!B(_4s(_eW,_4A))){if(!B(_4s(_eV,_4A))){if(!B(_cq(_eV,_4A))){return new F(function(){return _et(-1021,53,_eV,_eW);});}else{return  -B(_et(-1021,53,B(_eM(_eV)),_eW));}}else{return E(_eT);}}else{return (!B(_4s(_eV,_4A)))?(!B(_cq(_eV,_4A)))?E(_eS):E(_eR):E(_eQ);}},_eX=function(_eY){var _eZ=E(_eY);return new F(function(){return _eU(_eZ.a,_eZ.b);});},_f0=function(_f1){return 1/E(_f1);},_f2=function(_f3){var _f4=E(_f3);return (_f4!=0)?(_f4<=0)? -_f4:E(_f4):E(_eT);},_f5=function(_f6){var _f7=E(_f6);if(!_f7._){return _f7.a;}else{return new F(function(){return I_toNumber(_f7.a);});}},_f8=function(_f9){return new F(function(){return _f5(_f9);});},_fa=1,_fb=-1,_fc=function(_fd){var _fe=E(_fd);return (_fe<=0)?(_fe>=0)?E(_fe):E(_fb):E(_fa);},_ff=function(_fg,_fh){return E(_fg)-E(_fh);},_fi=function(_fj){return  -E(_fj);},_fk=function(_fl,_fm){return E(_fl)+E(_fm);},_fn=function(_fo,_fp){return E(_fo)*E(_fp);},_fq={_:0,a:_fk,b:_ff,c:_fn,d:_fi,e:_f2,f:_fc,g:_f8},_fr=function(_fs,_ft){return E(_fs)/E(_ft);},_fu=new T4(0,_fq,_fr,_f0,_eX),_fv=new T1(0,1),_fw=function(_fx){return E(E(_fx).a);},_fy=function(_fz){return E(E(_fz).a);},_fA=function(_fB){return E(E(_fB).g);},_fC=function(_fD,_fE){var _fF=E(_fE),_fG=new T(function(){var _fH=B(_fw(_fD)),_fI=B(_fC(_fD,B(A3(_fy,_fH,_fF,new T(function(){return B(A2(_fA,_fH,_fv));})))));return new T2(1,_fI.a,_fI.b);});return new T2(0,_fF,_fG);},_fJ=new T(function(){var _fK=B(_fC(_fu,_6i));return new T2(1,_fK.a,_fK.b);}),_fL=new T(function(){return B(_7k(256,2));}),_fM=new T(function(){return 0<E(_fL);}),_fN=new T1(0,10),_fO=new T(function(){return B(unCStr("Off"));}),_fP=new T(function(){return B(unCStr("On"));}),_fQ=new T(function(){return B(unCStr("30px \u30d2\u30e9\u30ae\u30ce\u89d2\u30b4"));}),_fR=new T3(0,0,255,128),_fS=3,_fT="globalAlpha",_fU=function(_fV,_fW){var _fX=new T(function(){return String(E(_fV));});return function(_fY,_){var _fZ=E(_fY),_g0=E(_fT),_g1=__app2(E(_6C),_fZ,_g0),_g2=E(_6D),_g3=__app3(_g2,_fZ,_g0,E(_fX)),_g4=B(A2(_fW,_fZ,_)),_g5=String(_g1),_g6=__app3(_g2,_fZ,_g0,_g5);return new F(function(){return _5p(_);});};},_g7=new T(function(){return B(unCStr("tail"));}),_g8=new T(function(){return B(_6k(_g7));}),_g9=function(_ga){return E(E(_ga).a);},_gb=function(_gc){return E(E(_gc).a);},_gd=function(_ge){return E(E(_ge).b);},_gf=new T(function(){return eval("(function(t,f){window.setInterval(f,t);})");}),_gg=new T(function(){return eval("(function(t,f){window.setTimeout(f,t);})");}),_gh=function(_){return new F(function(){return __jsNull();});},_gi=function(_gj){var _gk=B(A1(_gj,_));return E(_gk);},_gl=new T(function(){return B(_gi(_gh));}),_gm=new T(function(){return E(_gl);}),_gn=function(_go){return E(E(_go).b);},_gp=function(_gq){return E(E(_gq).b);},_gr=function(_gs,_gt,_gu){var _gv=B(_g9(_gs)),_gw=new T(function(){return B(_gn(_gv));}),_gx=function(_gy){var _gz=function(_){var _gA=E(_gt);if(!_gA._){var _gB=B(A1(_gy,_30)),_gC=__createJSFunc(0,function(_){var _gD=B(A1(_gB,_));return _gm;}),_gE=__app2(E(_gg),_gA.a,_gC);return new T(function(){var _gF=Number(_gE),_gG=jsTrunc(_gF);return new T2(0,_gG,E(_gA));});}else{var _gH=B(A1(_gy,_30)),_gI=__createJSFunc(0,function(_){var _gJ=B(A1(_gH,_));return _gm;}),_gK=__app2(E(_gf),_gA.a,_gI);return new T(function(){var _gL=Number(_gK),_gM=jsTrunc(_gL);return new T2(0,_gM,E(_gA));});}};return new F(function(){return A1(_gw,_gz);});},_gN=new T(function(){return B(A2(_gp,_gs,function(_gO){return E(_gu);}));});return new F(function(){return A3(_gd,B(_gb(_gv)),_gN,_gx);});},_gP=function(_gQ,_gR){var _gS=E(_gQ);if(!_gS._){return __Z;}else{var _gT=E(_gR);return (_gT._==0)?__Z:new T2(1,new T2(0,_gS.a,_gT.a),new T(function(){return B(_gP(_gS.b,_gT.b));}));}},_gU=function(_gV,_gW,_gX,_gY,_gZ,_h0,_h1,_h2,_h3,_){var _h4=new T(function(){return E(_gW)/2;}),_h5=function(_h6,_h7,_h8,_h9,_ha,_hb,_hc,_){var _hd=E(_gV),_he=__app1(E(_6o),_hd.b),_hf=function(_hg,_){var _hh=function(_hi,_hj,_hk,_){while(1){var _hl=B((function(_hm,_hn,_ho,_){var _hp=E(_hm);if(!_hp._){return _30;}else{var _hq=_hp.a,_hr=E(_hn);if(!_hr._){return _30;}else{var _hs=E(_hr.a),_ht=new T(function(){var _hu=new T(function(){return E(_h4)*E(_hq)/256;}),_hv=new T(function(){return E(_h4)*(E(_hq)+1)/256;}),_hw=function(_hx,_){return new F(function(){return _b2(new T2(1,new T2(0,_hu,200*E(E(_hs.a).a)),new T2(1,new T2(0,_hv,200*E(E(_hs.b).a)),_Y)),_hx,_);});};return B(_bj(_fS,function(_hy,_){return new F(function(){return _5K(_hw,E(_hy),_);});}));}),_hz=B(A(_6E,[_fR,_ht,_ho,_])),_hA=_ho;_hi=_hp.b;_hj=_hr.b;_hk=_hA;return __continue;}}})(_hi,_hj,_hk,_));if(_hl!=__continue){return _hl;}}},_hB=new T(function(){return B(_gP(_h6,new T(function(){var _hC=E(_h6);if(!_hC._){return E(_g8);}else{return E(_hC.b);}},1)));},1),_hD=B(_hh(_fJ,_hB,_hg,_)),_hE=new T(function(){return E(_h0);}),_hF=function(_hG,_hH,_hI){var _hJ=E(_hG);if(!_hJ._){return function(_hK,_){return _hI;};}else{var _hL=_hJ.a,_hM=E(_hH);if(!_hM._){return function(_hN,_){return _hI;};}else{var _hO=_hM.a,_hP=new T(function(){var _hQ=E(_hI),_hR=_hQ.a,_hS=_hQ.b,_hT=new T(function(){var _hU=E(_hO),_hV=B(_4Q(E(_hU.a),E(_hU.b)))/256;return _hV*200+_hV*200;}),_hW=new T(function(){var _hX=E(_hT);if(_hX<2){return E(_48);}else{var _hY=new T(function(){var _hZ=function(_i0,_){return new F(function(){return _5u(E(_hR),E(_hS),_hX,E(_i0),_);});};return B(_bj(_bx,function(_i1,_){return new F(function(){return _5K(_hZ,E(_i1),_);});}));});return B(_6E(_by,_hY));}}),_i2=new T(function(){var _i3=E(_hO);return B(_5m(E(_i3.a),E(_i3.b)));}),_i4=new T(function(){var _i5=E(_hR),_i6=E(_hL);if(!B(_4m(_h1,_i6))){return _i5+-1*E(_hT)*Math.cos(6.283185307179586*_i6*E(_hE)/256+E(_i2)+1.5707963267948966);}else{return _i5+E(_hT)*Math.cos(6.283185307179586*_i6*E(_hE)/256+E(_i2)+1.5707963267948966);}}),_i7=new T(function(){return E(_hS)+E(_hT)*Math.sin(6.283185307179586*E(_hL)*E(_hE)/256+E(_i2)+1.5707963267948966);});return function(_i8,_){var _i9=B(A2(_hW,_i8,_));return new T2(0,_i4,_i7);};});return function(_ia,_){var _ib=B(A2(_hP,_ia,_));return new F(function(){return A(_hF,[_hJ.b,_hM.b,_ib,_ia,_]);});};}}},_ic=function(_id,_ie,_if,_ig){var _ih=E(_id);if(!_ih._){return function(_ii,_){return new T2(0,_if,_ig);};}else{var _ij=_ih.a,_ik=E(_ie);if(!_ik._){return function(_il,_){return new T2(0,_if,_ig);};}else{var _im=_ik.a,_in=new T(function(){var _io=E(_im),_ip=B(_4Q(E(_io.a),E(_io.b)))/256;return _ip*200+_ip*200;}),_iq=new T(function(){var _ir=E(_in);if(_ir<2){return E(_48);}else{var _is=new T(function(){var _it=function(_iu,_){return new F(function(){return _5u(E(_if),_ig,_ir,E(_iu),_);});};return B(_bj(_bx,function(_iv,_){return new F(function(){return _5K(_it,E(_iv),_);});}));});return B(_6E(_by,_is));}}),_iw=new T(function(){var _ix=E(_im);return B(_5m(E(_ix.a),E(_ix.b)));}),_iy=new T(function(){var _iz=E(_if),_iA=E(_ij);if(!B(_4m(_h1,_iA))){return _iz+-1*E(_in)*Math.cos(6.283185307179586*_iA*E(_hE)/256+E(_iw)+1.5707963267948966);}else{return _iz+E(_in)*Math.cos(6.283185307179586*_iA*E(_hE)/256+E(_iw)+1.5707963267948966);}}),_iB=new T(function(){return _ig+E(_in)*Math.sin(6.283185307179586*E(_ij)*E(_hE)/256+E(_iw)+1.5707963267948966);});return function(_iC,_){var _iD=B(A2(_iq,_iC,_));return new F(function(){return A(_hF,[_ih.b,_ik.b,new T2(0,_iy,_iB),_iC,_]);});};}}},_iE=B(A(_ic,[_9k,_gZ,new T(function(){return  -(E(_gW)/4);}),0,_hg,_])),_iF=_iE,_iG=new T(function(){var _iH=new T(function(){var _iI=new T(function(){var _iJ=E(_h6);if(!_iJ._){return E(_6n);}else{return 200*E(E(_iJ.a).a);}}),_iK=function(_iL,_){return new F(function(){return _b2(new T2(1,_iF,new T2(1,new T2(0,_6i,_iI),_Y)),_iL,_);});};return B(_bj(_fS,function(_iM,_){return new F(function(){return _5K(_iK,E(_iM),_);});}));});return B(_6E(_fR,_iH));}),_iN=B(A(_fU,[_bw,_iG,_hg,_])),_iO=function(_iP,_){var _iQ=E(_iF);return new F(function(){return _5u(E(_iQ.a),E(_iQ.b),3,E(_iP),_);});},_iR=B(A(_6E,[_fR,function(_iS,_){return new F(function(){return _5D(_iO,E(_iS),_);});},_hg,_])),_iT=new T(function(){var _iU=E(_h6);if(!_iU._){return E(_6n);}else{return 200*E(E(_iU.a).a);}}),_iV=function(_iW,_){return new F(function(){return _5u(0,E(_iT),3,E(_iW),_);});},_iX=B(A(_6E,[_fR,function(_iY,_){return new F(function(){return _5D(_iV,E(_iY),_);});},_hg,_])),_iZ=new T(function(){var _j0=new T(function(){return B(unAppCStr("Microphone: ",new T(function(){if(!E(_h3)){return E(_fP);}else{return E(_fO);}})));},1);return B(_63(new T(function(){return  -(E(_gW)/2)+20;}),new T(function(){return  -(E(_gX)/2)+50;}),_j0));});return new F(function(){return A(_aO,[_fQ,_iZ,_hg,_]);});},_j1=B(_5T(_h4,new T(function(){return E(_gX)/2;},1),_hf,_hd.a,_)),_j2=function(_,_j3,_j4){var _j5=E(_h2),_j6=rMV(_j5),_j7=function(_j8,_){if(!E(_h3)){return new T2(0,_30,_j8);}else{var _j9=E(_j8),_ja=E(_j9.c),_jb=new T(function(){var _jc=function(_jd,_je){while(1){var _jf=E(_je);if(!_jf._){return __Z;}else{var _jg=_jf.b,_jh=E(_jd);if(_jh==1){return E(_jg);}else{_jd=_jh-1|0;_je=_jg;continue;}}}};return B(_1i(B(_jc(1,_h6)),new T(function(){return B(_6a(1,_h6));},1)));});return new T2(0,_30,new T4(0,_j9.a,new T2(0,_jb,new T(function(){return E(E(_j9.b).b);})),new T2(0,new T(function(){return B(_8d(E(_ja.a)+1|0,256));}),_ja.b),_j9.d));}};if(!E(_j6)){var _ji=B(_j7(_j4,_)),_jj=B(A(_gr,[_47,_fN,function(_jk,_){var _jl=E(_jk),_jm=E(_jl.a),_jn=E(_jl.b),_jo=E(_jl.c),_jp=E(_jl.d);return new F(function(){return _gU(_hd,_jm.a,_jm.b,_jn.a,_jn.b,_jo.a,_jo.b,_jp.a,_jp.b,_);});},new T(function(){return E(E(_ji).b);}),_]));return new T2(0,_30,new T(function(){return E(E(_jj).b);}));}else{var _=wMV(_j5,_6g),_jq=B(_j7(new T4(0,new T(function(){return E(E(_j4).a);}),new T(function(){return E(E(_j4).b);}),new T(function(){return E(E(_j4).c);}),new T2(0,new T(function(){return E(E(E(_j4).d).a);}),new T(function(){if(!E(_h3)){return true;}else{return false;}}))),_)),_jr=B(A(_gr,[_47,_fN,function(_js,_){var _jt=E(_js),_ju=E(_jt.a),_jv=E(_jt.b),_jw=E(_jt.c),_jx=E(_jt.d);return new F(function(){return _gU(_hd,_ju.a,_ju.b,_jv.a,_jv.b,_jw.a,_jw.b,_jx.a,_jx.b,_);});},new T(function(){return E(E(_jq).b);}),_]));return new T2(0,_30,new T(function(){return E(E(_jr).b);}));}};if(!E(_h3)){return new F(function(){return _j2(_,_30,new T4(0,_h7,new T2(0,_h8,new T(function(){if(!E(_fM)){return __Z;}else{return B(_6a(E(_fL),B(_av(_h6))));}})),new T2(0,_9l,_hb),_hc));});}else{return new F(function(){return _j2(_,_30,new T4(0,_h7,new T2(0,_h8,_h9),new T2(0,_ha,_hb),_hc));});}};if(!E(_h3)){var _jy=__app0(E(_6Y)),_jz=__arr2lst(0,_jy),_jA=B(_2W(_jz,_)),_jB=new T(function(){var _jC=function(_jD,_jE){var _jF=E(_jD);if(!_jF._){return __Z;}else{var _jG=_jF.a,_jH=E(_jE);return (_jH==1)?new T2(1,new T(function(){var _jI=E(_jG);return new T2(0,E(_jI),E(_6i));}),_Y):new T2(1,new T(function(){var _jJ=E(_jG);return new T2(0,E(_jJ),E(_6i));}),new T(function(){return B(_jC(_jF.b,_jH-1|0));}));}};return B(_jC(_jA,256));});return new F(function(){return _h5(_jB,new T2(0,_gW,_gX),_jB,_gZ,_h0,_h1,new T2(0,_h2,_6g),_);});}else{return new F(function(){return _h5(_gY,new T2(0,_gW,_gX),_gY,_gZ,_h0,_h1,new T2(0,_h2,_6h),_);});}},_jK=function(_jL,_jM){return imul(E(_jL),E(_jM))|0;},_jN=function(_jO,_jP){return E(_jO)+E(_jP)|0;},_jQ=function(_jR,_jS){return E(_jR)-E(_jS)|0;},_jT=function(_jU){var _jV=E(_jU);return (_jV<0)? -_jV:E(_jV);},_jW=function(_jX){return new F(function(){return _bM(_jX);});},_jY=function(_jZ){return  -E(_jZ);},_k0=-1,_k1=0,_k2=1,_k3=function(_k4){var _k5=E(_k4);return (_k5>=0)?(E(_k5)==0)?E(_k1):E(_k2):E(_k0);},_k6={_:0,a:_jN,b:_jQ,c:_jK,d:_jY,e:_jT,f:_k3,g:_jW},_k7=new T1(0,1),_k8=function(_k9,_ka){return new T2(0,E(_k9),E(_ka));},_kb=function(_kc,_kd){var _ke=quot(_kd,52774),_kf=(imul(40692,_kd-(imul(_ke,52774)|0)|0)|0)-(imul(_ke,3791)|0)|0,_kg=new T(function(){if(_kf>=0){return _kf;}else{return _kf+2147483399|0;}}),_kh=quot(_kc,53668),_ki=(imul(40014,_kc-(imul(_kh,53668)|0)|0)|0)-(imul(_kh,12211)|0)|0,_kj=new T(function(){if(_ki>=0){return _ki;}else{return _ki+2147483563|0;}});return new T2(0,new T(function(){var _kk=E(_kj)-E(_kg)|0;if(_kk>=1){return _kk;}else{return _kk+2147483562|0;}}),new T(function(){return B(_k8(_kj,_kg));}));},_kl=new T1(0,2147483562),_km=function(_kn,_ko){var _kp=E(_kn);if(!_kp._){var _kq=_kp.a,_kr=E(_ko);return (_kr._==0)?_kq>=_kr.a:I_compareInt(_kr.a,_kq)<=0;}else{var _ks=_kp.a,_kt=E(_ko);return (_kt._==0)?I_compareInt(_ks,_kt.a)>=0:I_compare(_ks,_kt.a)>=0;}},_ku=new T1(0,0),_kv=new T1(0,1000),_kw=function(_kx,_ky){while(1){var _kz=E(_kx);if(!_kz._){var _kA=E(_kz.a);if(_kA==(-2147483648)){_kx=new T1(1,I_fromInt(-2147483648));continue;}else{var _kB=E(_ky);if(!_kB._){return new T1(0,B(_8d(_kA,_kB.a)));}else{_kx=new T1(1,I_fromInt(_kA));_ky=_kB;continue;}}}else{var _kC=_kz.a,_kD=E(_ky);return (_kD._==0)?new T1(1,I_mod(_kC,I_fromInt(_kD.a))):new T1(1,I_mod(_kC,_kD.a));}}},_kE=function(_kF){return new T1(0,_kF);},_kG=function(_kH,_kI){while(1){var _kJ=E(_kH);if(!_kJ._){var _kK=_kJ.a,_kL=E(_kI);if(!_kL._){var _kM=_kL.a;if(!(imul(_kK,_kM)|0)){return new T1(0,imul(_kK,_kM)|0);}else{_kH=new T1(1,I_fromInt(_kK));_kI=new T1(1,I_fromInt(_kM));continue;}}else{_kH=new T1(1,I_fromInt(_kK));_kI=_kL;continue;}}else{var _kN=E(_kI);if(!_kN._){_kH=_kJ;_kI=new T1(1,I_fromInt(_kN.a));continue;}else{return new T1(1,I_mul(_kJ.a,_kN.a));}}}},_kO=function(_kP,_kQ,_kR,_kS){while(1){var _kT=B((function(_kU,_kV,_kW,_kX){if(!B(_ch(_kV,_kW))){var _kY=B(_bP(B(_e7(_kW,_kV)),_k7)),_kZ=function(_l0,_l1,_l2){while(1){if(!B(_km(_l0,B(_kG(_kY,_kv))))){var _l3=E(_l2),_l4=B(_kb(_l3.a,_l3.b)),_l5=B(_kG(_l0,_kl)),_l6=B(_bP(B(_kG(_l1,_kl)),B(_e7(B(_kE(E(_l4.a))),_k7))));_l0=_l5;_l1=_l6;_l2=_l4.b;continue;}else{return new T2(0,_l1,_l2);}}},_l7=B(_kZ(_k7,_ku,_kX)),_l8=new T(function(){return B(A2(_fA,_kU,new T(function(){if(!B(_4s(_kY,_ku))){return B(_bP(_kV,B(_kw(_l7.a,_kY))));}else{return E(_7V);}})));});return new T2(0,_l8,_l7.b);}else{var _l9=_kU,_la=_kW,_lb=_kV,_lc=_kX;_kP=_l9;_kQ=_la;_kR=_lb;_kS=_lc;return __continue;}})(_kP,_kQ,_kR,_kS));if(_kT!=__continue){return _kT;}}},_ld=function(_le){var _lf=B(_kO(_k6,_ku,_k7,_le));return new T2(0,E(_lf.b),new T(function(){if(!E(_lf.a)){return false;}else{return true;}}));},_lg=new T1(0,0),_lh=function(_li,_lj){while(1){var _lk=E(_li);if(!_lk._){var _ll=_lk.a,_lm=E(_lj);if(!_lm._){return new T1(0,(_ll>>>0|_lm.a>>>0)>>>0&4294967295);}else{_li=new T1(1,I_fromInt(_ll));_lj=_lm;continue;}}else{var _ln=E(_lj);if(!_ln._){_li=_lk;_lj=new T1(1,I_fromInt(_ln.a));continue;}else{return new T1(1,I_or(_lk.a,_ln.a));}}}},_lo=function(_lp){var _lq=E(_lp);if(!_lq._){return E(_lg);}else{return new F(function(){return _lh(new T1(0,E(_lq.a)),B(_c7(B(_lo(_lq.b)),31)));});}},_lr=function(_ls,_lt){if(!E(_ls)){return new F(function(){return _eM(B(_lo(_lt)));});}else{return new F(function(){return _lo(_lt);});}},_lu=1420103680,_lv=465,_lw=new T2(1,_lv,_Y),_lx=new T2(1,_lu,_lw),_ly=new T(function(){return B(_lr(_6h,_lx));}),_lz=0,_lA=0,_lB=new T(function(){return B(_7R(_lA));}),_lC=new T(function(){return die(_lB);}),_lD=function(_lE,_lF){var _lG=E(_lF);if(!_lG){return E(_7V);}else{var _lH=function(_lI){if(_lE<=0){if(_lE>=0){var _lJ=quotRemI(_lE,_lG);return new T2(0,_lJ.a,_lJ.b);}else{if(_lG<=0){var _lK=quotRemI(_lE,_lG);return new T2(0,_lK.a,_lK.b);}else{var _lL=quotRemI(_lE+1|0,_lG);return new T2(0,_lL.a-1|0,(_lL.b+_lG|0)-1|0);}}}else{if(_lG>=0){if(_lE>=0){var _lM=quotRemI(_lE,_lG);return new T2(0,_lM.a,_lM.b);}else{if(_lG<=0){var _lN=quotRemI(_lE,_lG);return new T2(0,_lN.a,_lN.b);}else{var _lO=quotRemI(_lE+1|0,_lG);return new T2(0,_lO.a-1|0,(_lO.b+_lG|0)-1|0);}}}else{var _lP=quotRemI(_lE-1|0,_lG);return new T2(0,_lP.a-1|0,(_lP.b+_lG|0)+1|0);}}};if(E(_lG)==(-1)){if(E(_lE)==(-2147483648)){return new T2(0,_lC,_lz);}else{return new F(function(){return _lH(_);});}}else{return new F(function(){return _lH(_);});}}},_lQ=new T1(0,0),_lR=function(_lS,_lT){while(1){var _lU=E(_lS);if(!_lU._){var _lV=E(_lU.a);if(_lV==(-2147483648)){_lS=new T1(1,I_fromInt(-2147483648));continue;}else{var _lW=E(_lT);if(!_lW._){return new T1(0,_lV%_lW.a);}else{_lS=new T1(1,I_fromInt(_lV));_lT=_lW;continue;}}}else{var _lX=_lU.a,_lY=E(_lT);return (_lY._==0)?new T1(1,I_rem(_lX,I_fromInt(_lY.a))):new T1(1,I_rem(_lX,_lY.a));}}},_lZ=function(_m0,_m1){if(!B(_4s(_m1,_lQ))){return new F(function(){return _lR(_m0,_m1);});}else{return E(_7V);}},_m2=function(_m3,_m4){while(1){if(!B(_4s(_m4,_lQ))){var _m5=_m4,_m6=B(_lZ(_m3,_m4));_m3=_m5;_m4=_m6;continue;}else{return E(_m3);}}},_m7=function(_m8){var _m9=E(_m8);if(!_m9._){var _ma=E(_m9.a);return (_ma==(-2147483648))?E(_eL):(_ma<0)?new T1(0, -_ma):E(_m9);}else{var _mb=_m9.a;return (I_compareInt(_mb,0)>=0)?E(_m9):new T1(1,I_negate(_mb));}},_mc=function(_md,_me){while(1){var _mf=E(_md);if(!_mf._){var _mg=E(_mf.a);if(_mg==(-2147483648)){_md=new T1(1,I_fromInt(-2147483648));continue;}else{var _mh=E(_me);if(!_mh._){return new T1(0,quot(_mg,_mh.a));}else{_md=new T1(1,I_fromInt(_mg));_me=_mh;continue;}}}else{var _mi=_mf.a,_mj=E(_me);return (_mj._==0)?new T1(0,I_toInt(I_quot(_mi,I_fromInt(_mj.a)))):new T1(1,I_quot(_mi,_mj.a));}}},_mk=5,_ml=new T(function(){return B(_7R(_mk));}),_mm=new T(function(){return die(_ml);}),_mn=function(_mo,_mp){if(!B(_4s(_mp,_lQ))){var _mq=B(_m2(B(_m7(_mo)),B(_m7(_mp))));return (!B(_4s(_mq,_lQ)))?new T2(0,B(_mc(_mo,_mq)),B(_mc(_mp,_mq))):E(_7V);}else{return E(_mm);}},_mr=new T1(0,-1),_ms=function(_mt){var _mu=E(_mt);if(!_mu._){var _mv=_mu.a;return (_mv>=0)?(E(_mv)==0)?E(_lg):E(_cp):E(_mr);}else{var _mw=I_compareInt(_mu.a,0);return (_mw<=0)?(E(_mw)==0)?E(_lg):E(_mr):E(_cp);}},_mx=function(_my,_mz,_mA,_mB){var _mC=B(_kG(_mz,_mA));return new F(function(){return _mn(B(_kG(B(_kG(_my,_mB)),B(_ms(_mC)))),B(_m7(_mC)));});},_mD=function(_mE){return E(_ly);},_mF=new T1(0,1),_mG=function(_mH,_mI){var _mJ=E(_mH);return new T2(0,_mJ,new T(function(){var _mK=B(_mG(B(_bP(_mJ,_mI)),_mI));return new T2(1,_mK.a,_mK.b);}));},_mL=function(_mM){var _mN=B(_mG(_mM,_mF));return new T2(1,_mN.a,_mN.b);},_mO=function(_mP,_mQ){var _mR=B(_mG(_mP,new T(function(){return B(_e7(_mQ,_mP));})));return new T2(1,_mR.a,_mR.b);},_mS=new T1(0,0),_mT=function(_mU,_mV,_mW){if(!B(_km(_mV,_mS))){var _mX=function(_mY){return (!B(_cq(_mY,_mW)))?new T2(1,_mY,new T(function(){return B(_mX(B(_bP(_mY,_mV))));})):__Z;};return new F(function(){return _mX(_mU);});}else{var _mZ=function(_n0){return (!B(_ch(_n0,_mW)))?new T2(1,_n0,new T(function(){return B(_mZ(B(_bP(_n0,_mV))));})):__Z;};return new F(function(){return _mZ(_mU);});}},_n1=function(_n2,_n3,_n4){return new F(function(){return _mT(_n2,B(_e7(_n3,_n2)),_n4);});},_n5=function(_n6,_n7){return new F(function(){return _mT(_n6,_mF,_n7);});},_n8=function(_n9){return new F(function(){return _bM(_n9);});},_na=function(_nb){return new F(function(){return _e7(_nb,_mF);});},_nc=function(_nd){return new F(function(){return _bP(_nd,_mF);});},_ne=function(_nf){return new F(function(){return _kE(E(_nf));});},_ng={_:0,a:_nc,b:_na,c:_ne,d:_n8,e:_mL,f:_mO,g:_n5,h:_n1},_nh=function(_ni,_nj){while(1){var _nk=E(_ni);if(!_nk._){var _nl=E(_nk.a);if(_nl==(-2147483648)){_ni=new T1(1,I_fromInt(-2147483648));continue;}else{var _nm=E(_nj);if(!_nm._){return new T1(0,B(_7k(_nl,_nm.a)));}else{_ni=new T1(1,I_fromInt(_nl));_nj=_nm;continue;}}}else{var _nn=_nk.a,_no=E(_nj);return (_no._==0)?new T1(1,I_div(_nn,I_fromInt(_no.a))):new T1(1,I_div(_nn,_no.a));}}},_np=function(_nq,_nr){if(!B(_4s(_nr,_lQ))){return new F(function(){return _nh(_nq,_nr);});}else{return E(_7V);}},_ns=function(_nt,_nu){while(1){var _nv=E(_nt);if(!_nv._){var _nw=E(_nv.a);if(_nw==(-2147483648)){_nt=new T1(1,I_fromInt(-2147483648));continue;}else{var _nx=E(_nu);if(!_nx._){var _ny=_nx.a;return new T2(0,new T1(0,B(_7k(_nw,_ny))),new T1(0,B(_8d(_nw,_ny))));}else{_nt=new T1(1,I_fromInt(_nw));_nu=_nx;continue;}}}else{var _nz=E(_nu);if(!_nz._){_nt=_nv;_nu=new T1(1,I_fromInt(_nz.a));continue;}else{var _nA=I_divMod(_nv.a,_nz.a);return new T2(0,new T1(1,_nA.a),new T1(1,_nA.b));}}}},_nB=function(_nC,_nD){if(!B(_4s(_nD,_lQ))){var _nE=B(_ns(_nC,_nD));return new T2(0,_nE.a,_nE.b);}else{return E(_7V);}},_nF=function(_nG,_nH){if(!B(_4s(_nH,_lQ))){return new F(function(){return _kw(_nG,_nH);});}else{return E(_7V);}},_nI=function(_nJ,_nK){if(!B(_4s(_nK,_lQ))){return new F(function(){return _mc(_nJ,_nK);});}else{return E(_7V);}},_nL=function(_nM,_nN){if(!B(_4s(_nN,_lQ))){var _nO=B(_bY(_nM,_nN));return new T2(0,_nO.a,_nO.b);}else{return E(_7V);}},_nP=function(_nQ){return E(_nQ);},_nR=function(_nS){return E(_nS);},_nT={_:0,a:_bP,b:_e7,c:_kG,d:_eM,e:_m7,f:_ms,g:_nR},_nU=function(_nV,_nW){var _nX=E(_nV);if(!_nX._){var _nY=_nX.a,_nZ=E(_nW);return (_nZ._==0)?_nY!=_nZ.a:(I_compareInt(_nZ.a,_nY)==0)?false:true;}else{var _o0=_nX.a,_o1=E(_nW);return (_o1._==0)?(I_compareInt(_o0,_o1.a)==0)?false:true:(I_compare(_o0,_o1.a)==0)?false:true;}},_o2=new T2(0,_4s,_nU),_o3=function(_o4,_o5){return (!B(_dS(_o4,_o5)))?E(_o4):E(_o5);},_o6=function(_o7,_o8){return (!B(_dS(_o7,_o8)))?E(_o8):E(_o7);},_o9={_:0,a:_o2,b:_bA,c:_cq,d:_dS,e:_ch,f:_km,g:_o3,h:_o6},_oa=function(_ob){return new T2(0,E(_ob),E(_fv));},_oc=new T3(0,_nT,_o9,_oa),_od={_:0,a:_oc,b:_ng,c:_nI,d:_lZ,e:_np,f:_nF,g:_nL,h:_nB,i:_nP},_oe=new T1(0,0),_of=function(_og,_oh,_oi){var _oj=B(A1(_og,_oh));if(!B(_4s(_oj,_oe))){return new F(function(){return _nh(B(_kG(_oh,_oi)),_oj);});}else{return E(_7V);}},_ok=function(_ol){return E(E(_ol).a);},_om=function(_on){return E(E(_on).a);},_oo=function(_op,_oq,_or){var _os=new T(function(){if(!B(_4s(_or,_lQ))){var _ot=B(_bY(_oq,_or));return new T2(0,_ot.a,_ot.b);}else{return E(_7V);}}),_ou=new T(function(){return B(A2(_fA,B(_om(B(_ok(_op)))),new T(function(){return E(E(_os).a);})));});return new T2(0,_ou,new T(function(){return new T2(0,E(E(_os).b),E(_or));}));},_ov=function(_ow){return E(E(_ow).b);},_ox=function(_oy,_oz,_oA){var _oB=B(_oo(_oy,_oz,_oA)),_oC=_oB.a,_oD=E(_oB.b);if(!B(_cq(B(_kG(_oD.a,_fv)),B(_kG(_lQ,_oD.b))))){return E(_oC);}else{var _oE=B(_om(B(_ok(_oy))));return new F(function(){return A3(_ov,_oE,_oC,new T(function(){return B(A2(_fA,_oE,_fv));}));});}},_oF=479723520,_oG=40233135,_oH=new T2(1,_oG,_Y),_oI=new T2(1,_oF,_oH),_oJ=new T(function(){return B(_lr(_6h,_oI));}),_oK=new T1(0,40587),_oL=function(_oM){var _oN=new T(function(){var _oO=B(_mx(_oM,_fv,_ly,_fv)),_oP=B(_mx(_oJ,_fv,_ly,_fv)),_oQ=B(_mx(_oO.a,_oO.b,_oP.a,_oP.b));return B(_ox(_od,_oQ.a,_oQ.b));});return new T2(0,new T(function(){return B(_bP(_oK,_oN));}),new T(function(){return B(_e7(_oM,B(_of(_mD,B(_kG(_oN,_ly)),_oJ))));}));},_oR=new T1(0,0),_oS=function(_oT,_){var _oU=__get(_oT,0),_oV=__get(_oT,1),_oW=Number(_oU),_oX=jsTrunc(_oW),_oY=Number(_oV),_oZ=jsTrunc(_oY);return new T2(0,_oX,_oZ);},_p0=new T(function(){return eval("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");}),_p1=660865024,_p2=465661287,_p3=new T2(1,_p2,_Y),_p4=new T2(1,_p1,_p3),_p5=new T(function(){return B(_lr(_6h,_p4));}),_p6=function(_){var _p7=__app0(E(_p0)),_p8=B(_oS(_p7,_));return new T(function(){var _p9=E(_p8);if(!B(_4s(_p5,_oe))){return B(_bP(B(_kG(B(_kE(E(_p9.a))),_ly)),B(_nh(B(_kG(B(_kG(B(_kE(E(_p9.b))),_ly)),_ly)),_p5))));}else{return E(_7V);}});},_pa=new T1(0,12345),_pb=function(_){var _pc=B(_p6(0)),_pd=B(_mx(B(_oL(_pc)).b,_fv,_ly,_fv)),_pe=_pd.b;if(!B(_4s(_pe,_ku))){var _pf=B(_bY(_pd.a,_pe));return new F(function(){return nMV(new T(function(){var _pg=B(_lD((B(_bM(B(_bP(B(_bP(B(_bP(B(_kG(_pf.a,_pa)),_pf.b)),_oR)),_ku))))>>>0&2147483647)>>>0&4294967295,2147483562));return new T2(0,E(_pg.b)+1|0,B(_8d(E(_pg.a),2147483398))+1|0);}));});}else{return E(_7V);}},_ph=new T(function(){return B(_gi(_pb));}),_pi=function(_){var _pj=mMV(E(_ph),_ld),_pk=E(_pj);return _pj;},_pl=new T2(1,_pi,_Y),_pm=function(_pn){var _po=E(_pn);return (_po==1)?E(_pl):new T2(1,_pi,new T(function(){return B(_pm(_po-1|0));}));},_pp=2,_pq=new T(function(){return eval("document");}),_pr=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_ps=function(_pt,_pu){var _pv=function(_){var _pw=__app1(E(_pr),E(_pu)),_px=__eq(_pw,E(_gm));return (E(_px)==0)?new T1(1,_pw):_2E;};return new F(function(){return A2(_gn,_pt,_pv);});},_py=function(_pz){return new F(function(){return fromJSStr(E(_pz));});},_pA=function(_pB){return E(E(_pB).a);},_pC=function(_pD,_pE,_pF,_pG){var _pH=new T(function(){var _pI=function(_){var _pJ=__app2(E(_6C),B(A2(_pA,_pD,_pF)),E(_pG));return new T(function(){return String(_pJ);});};return E(_pI);});return new F(function(){return A2(_gn,_pE,_pH);});},_pK=function(_pL){return E(E(_pL).d);},_pM=function(_pN,_pO,_pP,_pQ){var _pR=B(_gb(_pO)),_pS=new T(function(){return B(_pK(_pR));}),_pT=function(_pU){return new F(function(){return A1(_pS,new T(function(){return B(_py(_pU));}));});},_pV=new T(function(){return B(_pC(_pN,_pO,_pP,new T(function(){return toJSStr(E(_pQ));},1)));});return new F(function(){return A3(_gd,_pR,_pV,_pT);});},_pW=new T(function(){return B(unCStr("Canvas could not be found!"));}),_pX=new T(function(){return B(err(_pW));}),_pY=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_pZ=new T(function(){return B(err(_pY));}),_q0=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_q1=new T(function(){return B(err(_q0));}),_q2=new T(function(){return B(_dq("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_q3=function(_q4,_q5){while(1){var _q6=B((function(_q7,_q8){var _q9=E(_q7);switch(_q9._){case 0:var _qa=E(_q8);if(!_qa._){return __Z;}else{_q4=B(A1(_q9.a,_qa.a));_q5=_qa.b;return __continue;}break;case 1:var _qb=B(A1(_q9.a,_q8)),_qc=_q8;_q4=_qb;_q5=_qc;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_q9.a,_q8),new T(function(){return B(_q3(_q9.b,_q8));}));default:return E(_q9.a);}})(_q4,_q5));if(_q6!=__continue){return _q6;}}},_qd=function(_qe,_qf){var _qg=function(_qh){var _qi=E(_qf);if(_qi._==3){return new T2(3,_qi.a,new T(function(){return B(_qd(_qe,_qi.b));}));}else{var _qj=E(_qe);if(_qj._==2){return E(_qi);}else{var _qk=E(_qi);if(_qk._==2){return E(_qj);}else{var _ql=function(_qm){var _qn=E(_qk);if(_qn._==4){var _qo=function(_qp){return new T1(4,new T(function(){return B(_1i(B(_q3(_qj,_qp)),_qn.a));}));};return new T1(1,_qo);}else{var _qq=E(_qj);if(_qq._==1){var _qr=_qq.a,_qs=E(_qn);if(!_qs._){return new T1(1,function(_qt){return new F(function(){return _qd(B(A1(_qr,_qt)),_qs);});});}else{var _qu=function(_qv){return new F(function(){return _qd(B(A1(_qr,_qv)),new T(function(){return B(A1(_qs.a,_qv));}));});};return new T1(1,_qu);}}else{var _qw=E(_qn);if(!_qw._){return E(_q2);}else{var _qx=function(_qy){return new F(function(){return _qd(_qq,new T(function(){return B(A1(_qw.a,_qy));}));});};return new T1(1,_qx);}}}},_qz=E(_qj);switch(_qz._){case 1:var _qA=E(_qk);if(_qA._==4){var _qB=function(_qC){return new T1(4,new T(function(){return B(_1i(B(_q3(B(A1(_qz.a,_qC)),_qC)),_qA.a));}));};return new T1(1,_qB);}else{return new F(function(){return _ql(_);});}break;case 4:var _qD=_qz.a,_qE=E(_qk);switch(_qE._){case 0:var _qF=function(_qG){var _qH=new T(function(){return B(_1i(_qD,new T(function(){return B(_q3(_qE,_qG));},1)));});return new T1(4,_qH);};return new T1(1,_qF);case 1:var _qI=function(_qJ){var _qK=new T(function(){return B(_1i(_qD,new T(function(){return B(_q3(B(A1(_qE.a,_qJ)),_qJ));},1)));});return new T1(4,_qK);};return new T1(1,_qI);default:return new T1(4,new T(function(){return B(_1i(_qD,_qE.a));}));}break;default:return new F(function(){return _ql(_);});}}}}},_qL=E(_qe);switch(_qL._){case 0:var _qM=E(_qf);if(!_qM._){var _qN=function(_qO){return new F(function(){return _qd(B(A1(_qL.a,_qO)),new T(function(){return B(A1(_qM.a,_qO));}));});};return new T1(0,_qN);}else{return new F(function(){return _qg(_);});}break;case 3:return new T2(3,_qL.a,new T(function(){return B(_qd(_qL.b,_qf));}));default:return new F(function(){return _qg(_);});}},_qP=new T(function(){return B(unCStr("("));}),_qQ=new T(function(){return B(unCStr(")"));}),_qR=function(_qS,_qT){while(1){var _qU=E(_qS);if(!_qU._){return (E(_qT)._==0)?true:false;}else{var _qV=E(_qT);if(!_qV._){return false;}else{if(E(_qU.a)!=E(_qV.a)){return false;}else{_qS=_qU.b;_qT=_qV.b;continue;}}}}},_qW=function(_qX,_qY){return E(_qX)!=E(_qY);},_qZ=function(_r0,_r1){return E(_r0)==E(_r1);},_r2=new T2(0,_qZ,_qW),_r3=function(_r4,_r5){while(1){var _r6=E(_r4);if(!_r6._){return (E(_r5)._==0)?true:false;}else{var _r7=E(_r5);if(!_r7._){return false;}else{if(E(_r6.a)!=E(_r7.a)){return false;}else{_r4=_r6.b;_r5=_r7.b;continue;}}}}},_r8=function(_r9,_ra){return (!B(_r3(_r9,_ra)))?true:false;},_rb=new T2(0,_r3,_r8),_rc=function(_rd,_re){var _rf=E(_rd);switch(_rf._){case 0:return new T1(0,function(_rg){return new F(function(){return _rc(B(A1(_rf.a,_rg)),_re);});});case 1:return new T1(1,function(_rh){return new F(function(){return _rc(B(A1(_rf.a,_rh)),_re);});});case 2:return new T0(2);case 3:return new F(function(){return _qd(B(A1(_re,_rf.a)),new T(function(){return B(_rc(_rf.b,_re));}));});break;default:var _ri=function(_rj){var _rk=E(_rj);if(!_rk._){return __Z;}else{var _rl=E(_rk.a);return new F(function(){return _1i(B(_q3(B(A1(_re,_rl.a)),_rl.b)),new T(function(){return B(_ri(_rk.b));},1));});}},_rm=B(_ri(_rf.a));return (_rm._==0)?new T0(2):new T1(4,_rm);}},_rn=new T0(2),_ro=function(_rp){return new T2(3,_rp,_rn);},_rq=function(_rr,_rs){var _rt=E(_rr);if(!_rt){return new F(function(){return A1(_rs,_30);});}else{var _ru=new T(function(){return B(_rq(_rt-1|0,_rs));});return new T1(0,function(_rv){return E(_ru);});}},_rw=function(_rx,_ry,_rz){var _rA=new T(function(){return B(A1(_rx,_ro));}),_rB=function(_rC,_rD,_rE,_rF){while(1){var _rG=B((function(_rH,_rI,_rJ,_rK){var _rL=E(_rH);switch(_rL._){case 0:var _rM=E(_rI);if(!_rM._){return new F(function(){return A1(_ry,_rK);});}else{var _rN=_rJ+1|0,_rO=_rK;_rC=B(A1(_rL.a,_rM.a));_rD=_rM.b;_rE=_rN;_rF=_rO;return __continue;}break;case 1:var _rP=B(A1(_rL.a,_rI)),_rQ=_rI,_rN=_rJ,_rO=_rK;_rC=_rP;_rD=_rQ;_rE=_rN;_rF=_rO;return __continue;case 2:return new F(function(){return A1(_ry,_rK);});break;case 3:var _rR=new T(function(){return B(_rc(_rL,_rK));});return new F(function(){return _rq(_rJ,function(_rS){return E(_rR);});});break;default:return new F(function(){return _rc(_rL,_rK);});}})(_rC,_rD,_rE,_rF));if(_rG!=__continue){return _rG;}}};return function(_rT){return new F(function(){return _rB(_rA,_rT,0,_rz);});};},_rU=function(_rV){return new F(function(){return A1(_rV,_Y);});},_rW=function(_rX,_rY){var _rZ=function(_s0){var _s1=E(_s0);if(!_s1._){return E(_rU);}else{var _s2=_s1.a;if(!B(A1(_rX,_s2))){return E(_rU);}else{var _s3=new T(function(){return B(_rZ(_s1.b));}),_s4=function(_s5){var _s6=new T(function(){return B(A1(_s3,function(_s7){return new F(function(){return A1(_s5,new T2(1,_s2,_s7));});}));});return new T1(0,function(_s8){return E(_s6);});};return E(_s4);}}};return function(_s9){return new F(function(){return A2(_rZ,_s9,_rY);});};},_sa=new T0(6),_sb=new T(function(){return B(unCStr("valDig: Bad base"));}),_sc=new T(function(){return B(err(_sb));}),_sd=function(_se,_sf){var _sg=function(_sh,_si){var _sj=E(_sh);if(!_sj._){var _sk=new T(function(){return B(A1(_si,_Y));});return function(_sl){return new F(function(){return A1(_sl,_sk);});};}else{var _sm=E(_sj.a),_sn=function(_so){var _sp=new T(function(){return B(_sg(_sj.b,function(_sq){return new F(function(){return A1(_si,new T2(1,_so,_sq));});}));}),_sr=function(_ss){var _st=new T(function(){return B(A1(_sp,_ss));});return new T1(0,function(_su){return E(_st);});};return E(_sr);};switch(E(_se)){case 8:if(48>_sm){var _sv=new T(function(){return B(A1(_si,_Y));});return function(_sw){return new F(function(){return A1(_sw,_sv);});};}else{if(_sm>55){var _sx=new T(function(){return B(A1(_si,_Y));});return function(_sy){return new F(function(){return A1(_sy,_sx);});};}else{return new F(function(){return _sn(_sm-48|0);});}}break;case 10:if(48>_sm){var _sz=new T(function(){return B(A1(_si,_Y));});return function(_sA){return new F(function(){return A1(_sA,_sz);});};}else{if(_sm>57){var _sB=new T(function(){return B(A1(_si,_Y));});return function(_sC){return new F(function(){return A1(_sC,_sB);});};}else{return new F(function(){return _sn(_sm-48|0);});}}break;case 16:if(48>_sm){if(97>_sm){if(65>_sm){var _sD=new T(function(){return B(A1(_si,_Y));});return function(_sE){return new F(function(){return A1(_sE,_sD);});};}else{if(_sm>70){var _sF=new T(function(){return B(A1(_si,_Y));});return function(_sG){return new F(function(){return A1(_sG,_sF);});};}else{return new F(function(){return _sn((_sm-65|0)+10|0);});}}}else{if(_sm>102){if(65>_sm){var _sH=new T(function(){return B(A1(_si,_Y));});return function(_sI){return new F(function(){return A1(_sI,_sH);});};}else{if(_sm>70){var _sJ=new T(function(){return B(A1(_si,_Y));});return function(_sK){return new F(function(){return A1(_sK,_sJ);});};}else{return new F(function(){return _sn((_sm-65|0)+10|0);});}}}else{return new F(function(){return _sn((_sm-97|0)+10|0);});}}}else{if(_sm>57){if(97>_sm){if(65>_sm){var _sL=new T(function(){return B(A1(_si,_Y));});return function(_sM){return new F(function(){return A1(_sM,_sL);});};}else{if(_sm>70){var _sN=new T(function(){return B(A1(_si,_Y));});return function(_sO){return new F(function(){return A1(_sO,_sN);});};}else{return new F(function(){return _sn((_sm-65|0)+10|0);});}}}else{if(_sm>102){if(65>_sm){var _sP=new T(function(){return B(A1(_si,_Y));});return function(_sQ){return new F(function(){return A1(_sQ,_sP);});};}else{if(_sm>70){var _sR=new T(function(){return B(A1(_si,_Y));});return function(_sS){return new F(function(){return A1(_sS,_sR);});};}else{return new F(function(){return _sn((_sm-65|0)+10|0);});}}}else{return new F(function(){return _sn((_sm-97|0)+10|0);});}}}else{return new F(function(){return _sn(_sm-48|0);});}}break;default:return E(_sc);}}},_sT=function(_sU){var _sV=E(_sU);if(!_sV._){return new T0(2);}else{return new F(function(){return A1(_sf,_sV);});}};return function(_sW){return new F(function(){return A3(_sg,_sW,_r,_sT);});};},_sX=16,_sY=8,_sZ=function(_t0){var _t1=function(_t2){return new F(function(){return A1(_t0,new T1(5,new T2(0,_sY,_t2)));});},_t3=function(_t4){return new F(function(){return A1(_t0,new T1(5,new T2(0,_sX,_t4)));});},_t5=function(_t6){switch(E(_t6)){case 79:return new T1(1,B(_sd(_sY,_t1)));case 88:return new T1(1,B(_sd(_sX,_t3)));case 111:return new T1(1,B(_sd(_sY,_t1)));case 120:return new T1(1,B(_sd(_sX,_t3)));default:return new T0(2);}};return function(_t7){return (E(_t7)==48)?E(new T1(0,_t5)):new T0(2);};},_t8=function(_t9){return new T1(0,B(_sZ(_t9)));},_ta=function(_tb){return new F(function(){return A1(_tb,_2E);});},_tc=function(_td){return new F(function(){return A1(_td,_2E);});},_te=10,_tf=new T1(0,10),_tg=function(_th){return new F(function(){return _kE(E(_th));});},_ti=new T(function(){return B(unCStr("this should not happen"));}),_tj=new T(function(){return B(err(_ti));}),_tk=function(_tl,_tm){var _tn=E(_tm);if(!_tn._){return __Z;}else{var _to=E(_tn.b);return (_to._==0)?E(_tj):new T2(1,B(_bP(B(_kG(_tn.a,_tl)),_to.a)),new T(function(){return B(_tk(_tl,_to.b));}));}},_tp=new T1(0,0),_tq=function(_tr,_ts,_tt){while(1){var _tu=B((function(_tv,_tw,_tx){var _ty=E(_tx);if(!_ty._){return E(_tp);}else{if(!E(_ty.b)._){return E(_ty.a);}else{var _tz=E(_tw);if(_tz<=40){var _tA=function(_tB,_tC){while(1){var _tD=E(_tC);if(!_tD._){return E(_tB);}else{var _tE=B(_bP(B(_kG(_tB,_tv)),_tD.a));_tB=_tE;_tC=_tD.b;continue;}}};return new F(function(){return _tA(_tp,_ty);});}else{var _tF=B(_kG(_tv,_tv));if(!(_tz%2)){var _tG=B(_tk(_tv,_ty));_tr=_tF;_ts=quot(_tz+1|0,2);_tt=_tG;return __continue;}else{var _tG=B(_tk(_tv,new T2(1,_tp,_ty)));_tr=_tF;_ts=quot(_tz+1|0,2);_tt=_tG;return __continue;}}}}})(_tr,_ts,_tt));if(_tu!=__continue){return _tu;}}},_tH=function(_tI,_tJ){return new F(function(){return _tq(_tI,new T(function(){return B(_76(_tJ,0));},1),B(_9w(_tg,_tJ)));});},_tK=function(_tL){var _tM=new T(function(){var _tN=new T(function(){var _tO=function(_tP){return new F(function(){return A1(_tL,new T1(1,new T(function(){return B(_tH(_tf,_tP));})));});};return new T1(1,B(_sd(_te,_tO)));}),_tQ=function(_tR){if(E(_tR)==43){var _tS=function(_tT){return new F(function(){return A1(_tL,new T1(1,new T(function(){return B(_tH(_tf,_tT));})));});};return new T1(1,B(_sd(_te,_tS)));}else{return new T0(2);}},_tU=function(_tV){if(E(_tV)==45){var _tW=function(_tX){return new F(function(){return A1(_tL,new T1(1,new T(function(){return B(_eM(B(_tH(_tf,_tX))));})));});};return new T1(1,B(_sd(_te,_tW)));}else{return new T0(2);}};return B(_qd(B(_qd(new T1(0,_tU),new T1(0,_tQ))),_tN));});return new F(function(){return _qd(new T1(0,function(_tY){return (E(_tY)==101)?E(_tM):new T0(2);}),new T1(0,function(_tZ){return (E(_tZ)==69)?E(_tM):new T0(2);}));});},_u0=function(_u1){var _u2=function(_u3){return new F(function(){return A1(_u1,new T1(1,_u3));});};return function(_u4){return (E(_u4)==46)?new T1(1,B(_sd(_te,_u2))):new T0(2);};},_u5=function(_u6){return new T1(0,B(_u0(_u6)));},_u7=function(_u8){var _u9=function(_ua){var _ub=function(_uc){return new T1(1,B(_rw(_tK,_ta,function(_ud){return new F(function(){return A1(_u8,new T1(5,new T3(1,_ua,_uc,_ud)));});})));};return new T1(1,B(_rw(_u5,_tc,_ub)));};return new F(function(){return _sd(_te,_u9);});},_ue=function(_uf){return new T1(1,B(_u7(_uf)));},_ug=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_uh=function(_ui){return new F(function(){return _7Y(_r2,_ui,_ug);});},_uj=function(_uk){var _ul=new T(function(){return B(A1(_uk,_sY));}),_um=new T(function(){return B(A1(_uk,_sX));});return function(_un){switch(E(_un)){case 79:return E(_ul);case 88:return E(_um);case 111:return E(_ul);case 120:return E(_um);default:return new T0(2);}};},_uo=function(_up){return new T1(0,B(_uj(_up)));},_uq=function(_ur){return new F(function(){return A1(_ur,_te);});},_us=function(_ut,_uu){var _uv=jsShowI(_ut);return new F(function(){return _1i(fromJSStr(_uv),_uu);});},_uw=41,_ux=40,_uy=function(_uz,_uA,_uB){if(_uA>=0){return new F(function(){return _us(_uA,_uB);});}else{if(_uz<=6){return new F(function(){return _us(_uA,_uB);});}else{return new T2(1,_ux,new T(function(){var _uC=jsShowI(_uA);return B(_1i(fromJSStr(_uC),new T2(1,_uw,_uB)));}));}}},_uD=function(_uE){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_uy(9,_uE,_Y));}))));});},_uF=function(_uG){return new T0(2);},_uH=function(_uI){var _uJ=E(_uI);if(!_uJ._){return E(_uF);}else{var _uK=_uJ.a,_uL=E(_uJ.b);if(!_uL._){return E(_uK);}else{var _uM=new T(function(){return B(_uH(_uL));}),_uN=function(_uO){return new F(function(){return _qd(B(A1(_uK,_uO)),new T(function(){return B(A1(_uM,_uO));}));});};return E(_uN);}}},_uP=function(_uQ,_uR){var _uS=function(_uT,_uU,_uV){var _uW=E(_uT);if(!_uW._){return new F(function(){return A1(_uV,_uQ);});}else{var _uX=E(_uU);if(!_uX._){return new T0(2);}else{if(E(_uW.a)!=E(_uX.a)){return new T0(2);}else{var _uY=new T(function(){return B(_uS(_uW.b,_uX.b,_uV));});return new T1(0,function(_uZ){return E(_uY);});}}}};return function(_v0){return new F(function(){return _uS(_uQ,_v0,_uR);});};},_v1=new T(function(){return B(unCStr("SO"));}),_v2=14,_v3=function(_v4){var _v5=new T(function(){return B(A1(_v4,_v2));});return new T1(1,B(_uP(_v1,function(_v6){return E(_v5);})));},_v7=new T(function(){return B(unCStr("SOH"));}),_v8=1,_v9=function(_va){var _vb=new T(function(){return B(A1(_va,_v8));});return new T1(1,B(_uP(_v7,function(_vc){return E(_vb);})));},_vd=function(_ve){return new T1(1,B(_rw(_v9,_v3,_ve)));},_vf=new T(function(){return B(unCStr("NUL"));}),_vg=0,_vh=function(_vi){var _vj=new T(function(){return B(A1(_vi,_vg));});return new T1(1,B(_uP(_vf,function(_vk){return E(_vj);})));},_vl=new T(function(){return B(unCStr("STX"));}),_vm=2,_vn=function(_vo){var _vp=new T(function(){return B(A1(_vo,_vm));});return new T1(1,B(_uP(_vl,function(_vq){return E(_vp);})));},_vr=new T(function(){return B(unCStr("ETX"));}),_vs=3,_vt=function(_vu){var _vv=new T(function(){return B(A1(_vu,_vs));});return new T1(1,B(_uP(_vr,function(_vw){return E(_vv);})));},_vx=new T(function(){return B(unCStr("EOT"));}),_vy=4,_vz=function(_vA){var _vB=new T(function(){return B(A1(_vA,_vy));});return new T1(1,B(_uP(_vx,function(_vC){return E(_vB);})));},_vD=new T(function(){return B(unCStr("ENQ"));}),_vE=5,_vF=function(_vG){var _vH=new T(function(){return B(A1(_vG,_vE));});return new T1(1,B(_uP(_vD,function(_vI){return E(_vH);})));},_vJ=new T(function(){return B(unCStr("ACK"));}),_vK=6,_vL=function(_vM){var _vN=new T(function(){return B(A1(_vM,_vK));});return new T1(1,B(_uP(_vJ,function(_vO){return E(_vN);})));},_vP=new T(function(){return B(unCStr("BEL"));}),_vQ=7,_vR=function(_vS){var _vT=new T(function(){return B(A1(_vS,_vQ));});return new T1(1,B(_uP(_vP,function(_vU){return E(_vT);})));},_vV=new T(function(){return B(unCStr("BS"));}),_vW=8,_vX=function(_vY){var _vZ=new T(function(){return B(A1(_vY,_vW));});return new T1(1,B(_uP(_vV,function(_w0){return E(_vZ);})));},_w1=new T(function(){return B(unCStr("HT"));}),_w2=9,_w3=function(_w4){var _w5=new T(function(){return B(A1(_w4,_w2));});return new T1(1,B(_uP(_w1,function(_w6){return E(_w5);})));},_w7=new T(function(){return B(unCStr("LF"));}),_w8=10,_w9=function(_wa){var _wb=new T(function(){return B(A1(_wa,_w8));});return new T1(1,B(_uP(_w7,function(_wc){return E(_wb);})));},_wd=new T(function(){return B(unCStr("VT"));}),_we=11,_wf=function(_wg){var _wh=new T(function(){return B(A1(_wg,_we));});return new T1(1,B(_uP(_wd,function(_wi){return E(_wh);})));},_wj=new T(function(){return B(unCStr("FF"));}),_wk=12,_wl=function(_wm){var _wn=new T(function(){return B(A1(_wm,_wk));});return new T1(1,B(_uP(_wj,function(_wo){return E(_wn);})));},_wp=new T(function(){return B(unCStr("CR"));}),_wq=13,_wr=function(_ws){var _wt=new T(function(){return B(A1(_ws,_wq));});return new T1(1,B(_uP(_wp,function(_wu){return E(_wt);})));},_wv=new T(function(){return B(unCStr("SI"));}),_ww=15,_wx=function(_wy){var _wz=new T(function(){return B(A1(_wy,_ww));});return new T1(1,B(_uP(_wv,function(_wA){return E(_wz);})));},_wB=new T(function(){return B(unCStr("DLE"));}),_wC=16,_wD=function(_wE){var _wF=new T(function(){return B(A1(_wE,_wC));});return new T1(1,B(_uP(_wB,function(_wG){return E(_wF);})));},_wH=new T(function(){return B(unCStr("DC1"));}),_wI=17,_wJ=function(_wK){var _wL=new T(function(){return B(A1(_wK,_wI));});return new T1(1,B(_uP(_wH,function(_wM){return E(_wL);})));},_wN=new T(function(){return B(unCStr("DC2"));}),_wO=18,_wP=function(_wQ){var _wR=new T(function(){return B(A1(_wQ,_wO));});return new T1(1,B(_uP(_wN,function(_wS){return E(_wR);})));},_wT=new T(function(){return B(unCStr("DC3"));}),_wU=19,_wV=function(_wW){var _wX=new T(function(){return B(A1(_wW,_wU));});return new T1(1,B(_uP(_wT,function(_wY){return E(_wX);})));},_wZ=new T(function(){return B(unCStr("DC4"));}),_x0=20,_x1=function(_x2){var _x3=new T(function(){return B(A1(_x2,_x0));});return new T1(1,B(_uP(_wZ,function(_x4){return E(_x3);})));},_x5=new T(function(){return B(unCStr("NAK"));}),_x6=21,_x7=function(_x8){var _x9=new T(function(){return B(A1(_x8,_x6));});return new T1(1,B(_uP(_x5,function(_xa){return E(_x9);})));},_xb=new T(function(){return B(unCStr("SYN"));}),_xc=22,_xd=function(_xe){var _xf=new T(function(){return B(A1(_xe,_xc));});return new T1(1,B(_uP(_xb,function(_xg){return E(_xf);})));},_xh=new T(function(){return B(unCStr("ETB"));}),_xi=23,_xj=function(_xk){var _xl=new T(function(){return B(A1(_xk,_xi));});return new T1(1,B(_uP(_xh,function(_xm){return E(_xl);})));},_xn=new T(function(){return B(unCStr("CAN"));}),_xo=24,_xp=function(_xq){var _xr=new T(function(){return B(A1(_xq,_xo));});return new T1(1,B(_uP(_xn,function(_xs){return E(_xr);})));},_xt=new T(function(){return B(unCStr("EM"));}),_xu=25,_xv=function(_xw){var _xx=new T(function(){return B(A1(_xw,_xu));});return new T1(1,B(_uP(_xt,function(_xy){return E(_xx);})));},_xz=new T(function(){return B(unCStr("SUB"));}),_xA=26,_xB=function(_xC){var _xD=new T(function(){return B(A1(_xC,_xA));});return new T1(1,B(_uP(_xz,function(_xE){return E(_xD);})));},_xF=new T(function(){return B(unCStr("ESC"));}),_xG=27,_xH=function(_xI){var _xJ=new T(function(){return B(A1(_xI,_xG));});return new T1(1,B(_uP(_xF,function(_xK){return E(_xJ);})));},_xL=new T(function(){return B(unCStr("FS"));}),_xM=28,_xN=function(_xO){var _xP=new T(function(){return B(A1(_xO,_xM));});return new T1(1,B(_uP(_xL,function(_xQ){return E(_xP);})));},_xR=new T(function(){return B(unCStr("GS"));}),_xS=29,_xT=function(_xU){var _xV=new T(function(){return B(A1(_xU,_xS));});return new T1(1,B(_uP(_xR,function(_xW){return E(_xV);})));},_xX=new T(function(){return B(unCStr("RS"));}),_xY=30,_xZ=function(_y0){var _y1=new T(function(){return B(A1(_y0,_xY));});return new T1(1,B(_uP(_xX,function(_y2){return E(_y1);})));},_y3=new T(function(){return B(unCStr("US"));}),_y4=31,_y5=function(_y6){var _y7=new T(function(){return B(A1(_y6,_y4));});return new T1(1,B(_uP(_y3,function(_y8){return E(_y7);})));},_y9=new T(function(){return B(unCStr("SP"));}),_ya=32,_yb=function(_yc){var _yd=new T(function(){return B(A1(_yc,_ya));});return new T1(1,B(_uP(_y9,function(_ye){return E(_yd);})));},_yf=new T(function(){return B(unCStr("DEL"));}),_yg=127,_yh=function(_yi){var _yj=new T(function(){return B(A1(_yi,_yg));});return new T1(1,B(_uP(_yf,function(_yk){return E(_yj);})));},_yl=new T2(1,_yh,_Y),_ym=new T2(1,_yb,_yl),_yn=new T2(1,_y5,_ym),_yo=new T2(1,_xZ,_yn),_yp=new T2(1,_xT,_yo),_yq=new T2(1,_xN,_yp),_yr=new T2(1,_xH,_yq),_ys=new T2(1,_xB,_yr),_yt=new T2(1,_xv,_ys),_yu=new T2(1,_xp,_yt),_yv=new T2(1,_xj,_yu),_yw=new T2(1,_xd,_yv),_yx=new T2(1,_x7,_yw),_yy=new T2(1,_x1,_yx),_yz=new T2(1,_wV,_yy),_yA=new T2(1,_wP,_yz),_yB=new T2(1,_wJ,_yA),_yC=new T2(1,_wD,_yB),_yD=new T2(1,_wx,_yC),_yE=new T2(1,_wr,_yD),_yF=new T2(1,_wl,_yE),_yG=new T2(1,_wf,_yF),_yH=new T2(1,_w9,_yG),_yI=new T2(1,_w3,_yH),_yJ=new T2(1,_vX,_yI),_yK=new T2(1,_vR,_yJ),_yL=new T2(1,_vL,_yK),_yM=new T2(1,_vF,_yL),_yN=new T2(1,_vz,_yM),_yO=new T2(1,_vt,_yN),_yP=new T2(1,_vn,_yO),_yQ=new T2(1,_vh,_yP),_yR=new T2(1,_vd,_yQ),_yS=new T(function(){return B(_uH(_yR));}),_yT=34,_yU=new T1(0,1114111),_yV=92,_yW=39,_yX=function(_yY){var _yZ=new T(function(){return B(A1(_yY,_vQ));}),_z0=new T(function(){return B(A1(_yY,_vW));}),_z1=new T(function(){return B(A1(_yY,_w2));}),_z2=new T(function(){return B(A1(_yY,_w8));}),_z3=new T(function(){return B(A1(_yY,_we));}),_z4=new T(function(){return B(A1(_yY,_wk));}),_z5=new T(function(){return B(A1(_yY,_wq));}),_z6=new T(function(){return B(A1(_yY,_yV));}),_z7=new T(function(){return B(A1(_yY,_yW));}),_z8=new T(function(){return B(A1(_yY,_yT));}),_z9=new T(function(){var _za=function(_zb){var _zc=new T(function(){return B(_kE(E(_zb)));}),_zd=function(_ze){var _zf=B(_tH(_zc,_ze));if(!B(_dS(_zf,_yU))){return new T0(2);}else{return new F(function(){return A1(_yY,new T(function(){var _zg=B(_bM(_zf));if(_zg>>>0>1114111){return B(_uD(_zg));}else{return _zg;}}));});}};return new T1(1,B(_sd(_zb,_zd)));},_zh=new T(function(){var _zi=new T(function(){return B(A1(_yY,_y4));}),_zj=new T(function(){return B(A1(_yY,_xY));}),_zk=new T(function(){return B(A1(_yY,_xS));}),_zl=new T(function(){return B(A1(_yY,_xM));}),_zm=new T(function(){return B(A1(_yY,_xG));}),_zn=new T(function(){return B(A1(_yY,_xA));}),_zo=new T(function(){return B(A1(_yY,_xu));}),_zp=new T(function(){return B(A1(_yY,_xo));}),_zq=new T(function(){return B(A1(_yY,_xi));}),_zr=new T(function(){return B(A1(_yY,_xc));}),_zs=new T(function(){return B(A1(_yY,_x6));}),_zt=new T(function(){return B(A1(_yY,_x0));}),_zu=new T(function(){return B(A1(_yY,_wU));}),_zv=new T(function(){return B(A1(_yY,_wO));}),_zw=new T(function(){return B(A1(_yY,_wI));}),_zx=new T(function(){return B(A1(_yY,_wC));}),_zy=new T(function(){return B(A1(_yY,_ww));}),_zz=new T(function(){return B(A1(_yY,_v2));}),_zA=new T(function(){return B(A1(_yY,_vK));}),_zB=new T(function(){return B(A1(_yY,_vE));}),_zC=new T(function(){return B(A1(_yY,_vy));}),_zD=new T(function(){return B(A1(_yY,_vs));}),_zE=new T(function(){return B(A1(_yY,_vm));}),_zF=new T(function(){return B(A1(_yY,_v8));}),_zG=new T(function(){return B(A1(_yY,_vg));}),_zH=function(_zI){switch(E(_zI)){case 64:return E(_zG);case 65:return E(_zF);case 66:return E(_zE);case 67:return E(_zD);case 68:return E(_zC);case 69:return E(_zB);case 70:return E(_zA);case 71:return E(_yZ);case 72:return E(_z0);case 73:return E(_z1);case 74:return E(_z2);case 75:return E(_z3);case 76:return E(_z4);case 77:return E(_z5);case 78:return E(_zz);case 79:return E(_zy);case 80:return E(_zx);case 81:return E(_zw);case 82:return E(_zv);case 83:return E(_zu);case 84:return E(_zt);case 85:return E(_zs);case 86:return E(_zr);case 87:return E(_zq);case 88:return E(_zp);case 89:return E(_zo);case 90:return E(_zn);case 91:return E(_zm);case 92:return E(_zl);case 93:return E(_zk);case 94:return E(_zj);case 95:return E(_zi);default:return new T0(2);}};return B(_qd(new T1(0,function(_zJ){return (E(_zJ)==94)?E(new T1(0,_zH)):new T0(2);}),new T(function(){return B(A1(_yS,_yY));})));});return B(_qd(new T1(1,B(_rw(_uo,_uq,_za))),_zh));});return new F(function(){return _qd(new T1(0,function(_zK){switch(E(_zK)){case 34:return E(_z8);case 39:return E(_z7);case 92:return E(_z6);case 97:return E(_yZ);case 98:return E(_z0);case 102:return E(_z4);case 110:return E(_z2);case 114:return E(_z5);case 116:return E(_z1);case 118:return E(_z3);default:return new T0(2);}}),_z9);});},_zL=function(_zM){return new F(function(){return A1(_zM,_30);});},_zN=function(_zO){var _zP=E(_zO);if(!_zP._){return E(_zL);}else{var _zQ=E(_zP.a),_zR=_zQ>>>0,_zS=new T(function(){return B(_zN(_zP.b));});if(_zR>887){var _zT=u_iswspace(_zQ);if(!E(_zT)){return E(_zL);}else{var _zU=function(_zV){var _zW=new T(function(){return B(A1(_zS,_zV));});return new T1(0,function(_zX){return E(_zW);});};return E(_zU);}}else{var _zY=E(_zR);if(_zY==32){var _zZ=function(_A0){var _A1=new T(function(){return B(A1(_zS,_A0));});return new T1(0,function(_A2){return E(_A1);});};return E(_zZ);}else{if(_zY-9>>>0>4){if(E(_zY)==160){var _A3=function(_A4){var _A5=new T(function(){return B(A1(_zS,_A4));});return new T1(0,function(_A6){return E(_A5);});};return E(_A3);}else{return E(_zL);}}else{var _A7=function(_A8){var _A9=new T(function(){return B(A1(_zS,_A8));});return new T1(0,function(_Aa){return E(_A9);});};return E(_A7);}}}}},_Ab=function(_Ac){var _Ad=new T(function(){return B(_Ab(_Ac));}),_Ae=function(_Af){return (E(_Af)==92)?E(_Ad):new T0(2);},_Ag=function(_Ah){return E(new T1(0,_Ae));},_Ai=new T1(1,function(_Aj){return new F(function(){return A2(_zN,_Aj,_Ag);});}),_Ak=new T(function(){return B(_yX(function(_Al){return new F(function(){return A1(_Ac,new T2(0,_Al,_6h));});}));}),_Am=function(_An){var _Ao=E(_An);if(_Ao==38){return E(_Ad);}else{var _Ap=_Ao>>>0;if(_Ap>887){var _Aq=u_iswspace(_Ao);return (E(_Aq)==0)?new T0(2):E(_Ai);}else{var _Ar=E(_Ap);return (_Ar==32)?E(_Ai):(_Ar-9>>>0>4)?(E(_Ar)==160)?E(_Ai):new T0(2):E(_Ai);}}};return new F(function(){return _qd(new T1(0,function(_As){return (E(_As)==92)?E(new T1(0,_Am)):new T0(2);}),new T1(0,function(_At){var _Au=E(_At);if(E(_Au)==92){return E(_Ak);}else{return new F(function(){return A1(_Ac,new T2(0,_Au,_6g));});}}));});},_Av=function(_Aw,_Ax){var _Ay=new T(function(){return B(A1(_Ax,new T1(1,new T(function(){return B(A1(_Aw,_Y));}))));}),_Az=function(_AA){var _AB=E(_AA),_AC=E(_AB.a);if(E(_AC)==34){if(!E(_AB.b)){return E(_Ay);}else{return new F(function(){return _Av(function(_AD){return new F(function(){return A1(_Aw,new T2(1,_AC,_AD));});},_Ax);});}}else{return new F(function(){return _Av(function(_AE){return new F(function(){return A1(_Aw,new T2(1,_AC,_AE));});},_Ax);});}};return new F(function(){return _Ab(_Az);});},_AF=new T(function(){return B(unCStr("_\'"));}),_AG=function(_AH){var _AI=u_iswalnum(_AH);if(!E(_AI)){return new F(function(){return _7Y(_r2,_AH,_AF);});}else{return true;}},_AJ=function(_AK){return new F(function(){return _AG(E(_AK));});},_AL=new T(function(){return B(unCStr(",;()[]{}`"));}),_AM=new T(function(){return B(unCStr("=>"));}),_AN=new T2(1,_AM,_Y),_AO=new T(function(){return B(unCStr("~"));}),_AP=new T2(1,_AO,_AN),_AQ=new T(function(){return B(unCStr("@"));}),_AR=new T2(1,_AQ,_AP),_AS=new T(function(){return B(unCStr("->"));}),_AT=new T2(1,_AS,_AR),_AU=new T(function(){return B(unCStr("<-"));}),_AV=new T2(1,_AU,_AT),_AW=new T(function(){return B(unCStr("|"));}),_AX=new T2(1,_AW,_AV),_AY=new T(function(){return B(unCStr("\\"));}),_AZ=new T2(1,_AY,_AX),_B0=new T(function(){return B(unCStr("="));}),_B1=new T2(1,_B0,_AZ),_B2=new T(function(){return B(unCStr("::"));}),_B3=new T2(1,_B2,_B1),_B4=new T(function(){return B(unCStr(".."));}),_B5=new T2(1,_B4,_B3),_B6=function(_B7){var _B8=new T(function(){return B(A1(_B7,_sa));}),_B9=new T(function(){var _Ba=new T(function(){var _Bb=function(_Bc){var _Bd=new T(function(){return B(A1(_B7,new T1(0,_Bc)));});return new T1(0,function(_Be){return (E(_Be)==39)?E(_Bd):new T0(2);});};return B(_yX(_Bb));}),_Bf=function(_Bg){var _Bh=E(_Bg);switch(E(_Bh)){case 39:return new T0(2);case 92:return E(_Ba);default:var _Bi=new T(function(){return B(A1(_B7,new T1(0,_Bh)));});return new T1(0,function(_Bj){return (E(_Bj)==39)?E(_Bi):new T0(2);});}},_Bk=new T(function(){var _Bl=new T(function(){return B(_Av(_r,_B7));}),_Bm=new T(function(){var _Bn=new T(function(){var _Bo=new T(function(){var _Bp=function(_Bq){var _Br=E(_Bq),_Bs=u_iswalpha(_Br);return (E(_Bs)==0)?(E(_Br)==95)?new T1(1,B(_rW(_AJ,function(_Bt){return new F(function(){return A1(_B7,new T1(3,new T2(1,_Br,_Bt)));});}))):new T0(2):new T1(1,B(_rW(_AJ,function(_Bu){return new F(function(){return A1(_B7,new T1(3,new T2(1,_Br,_Bu)));});})));};return B(_qd(new T1(0,_Bp),new T(function(){return new T1(1,B(_rw(_t8,_ue,_B7)));})));}),_Bv=function(_Bw){return (!B(_7Y(_r2,_Bw,_ug)))?new T0(2):new T1(1,B(_rW(_uh,function(_Bx){var _By=new T2(1,_Bw,_Bx);if(!B(_7Y(_rb,_By,_B5))){return new F(function(){return A1(_B7,new T1(4,_By));});}else{return new F(function(){return A1(_B7,new T1(2,_By));});}})));};return B(_qd(new T1(0,_Bv),_Bo));});return B(_qd(new T1(0,function(_Bz){if(!B(_7Y(_r2,_Bz,_AL))){return new T0(2);}else{return new F(function(){return A1(_B7,new T1(2,new T2(1,_Bz,_Y)));});}}),_Bn));});return B(_qd(new T1(0,function(_BA){return (E(_BA)==34)?E(_Bl):new T0(2);}),_Bm));});return B(_qd(new T1(0,function(_BB){return (E(_BB)==39)?E(new T1(0,_Bf)):new T0(2);}),_Bk));});return new F(function(){return _qd(new T1(1,function(_BC){return (E(_BC)._==0)?E(_B8):new T0(2);}),_B9);});},_BD=0,_BE=function(_BF,_BG){var _BH=new T(function(){var _BI=new T(function(){var _BJ=function(_BK){var _BL=new T(function(){var _BM=new T(function(){return B(A1(_BG,_BK));});return B(_B6(function(_BN){var _BO=E(_BN);return (_BO._==2)?(!B(_qR(_BO.a,_qQ)))?new T0(2):E(_BM):new T0(2);}));}),_BP=function(_BQ){return E(_BL);};return new T1(1,function(_BR){return new F(function(){return A2(_zN,_BR,_BP);});});};return B(A2(_BF,_BD,_BJ));});return B(_B6(function(_BS){var _BT=E(_BS);return (_BT._==2)?(!B(_qR(_BT.a,_qP)))?new T0(2):E(_BI):new T0(2);}));}),_BU=function(_BV){return E(_BH);};return function(_BW){return new F(function(){return A2(_zN,_BW,_BU);});};},_BX=function(_BY,_BZ){var _C0=function(_C1){var _C2=new T(function(){return B(A1(_BY,_C1));}),_C3=function(_C4){return new F(function(){return _qd(B(A1(_C2,_C4)),new T(function(){return new T1(1,B(_BE(_C0,_C4)));}));});};return E(_C3);},_C5=new T(function(){return B(A1(_BY,_BZ));}),_C6=function(_C7){return new F(function(){return _qd(B(A1(_C5,_C7)),new T(function(){return new T1(1,B(_BE(_C0,_C7)));}));});};return E(_C6);},_C8=function(_C9,_Ca){var _Cb=function(_Cc,_Cd){var _Ce=function(_Cf){return new F(function(){return A1(_Cd,new T(function(){return  -E(_Cf);}));});},_Cg=new T(function(){return B(_B6(function(_Ch){return new F(function(){return A3(_C9,_Ch,_Cc,_Ce);});}));}),_Ci=function(_Cj){return E(_Cg);},_Ck=function(_Cl){return new F(function(){return A2(_zN,_Cl,_Ci);});},_Cm=new T(function(){return B(_B6(function(_Cn){var _Co=E(_Cn);if(_Co._==4){var _Cp=E(_Co.a);if(!_Cp._){return new F(function(){return A3(_C9,_Co,_Cc,_Cd);});}else{if(E(_Cp.a)==45){if(!E(_Cp.b)._){return E(new T1(1,_Ck));}else{return new F(function(){return A3(_C9,_Co,_Cc,_Cd);});}}else{return new F(function(){return A3(_C9,_Co,_Cc,_Cd);});}}}else{return new F(function(){return A3(_C9,_Co,_Cc,_Cd);});}}));}),_Cq=function(_Cr){return E(_Cm);};return new T1(1,function(_Cs){return new F(function(){return A2(_zN,_Cs,_Cq);});});};return new F(function(){return _BX(_Cb,_Ca);});},_Ct=new T(function(){return 1/0;}),_Cu=function(_Cv,_Cw){return new F(function(){return A1(_Cw,_Ct);});},_Cx=new T(function(){return 0/0;}),_Cy=function(_Cz,_CA){return new F(function(){return A1(_CA,_Cx);});},_CB=new T(function(){return B(unCStr("NaN"));}),_CC=new T(function(){return B(unCStr("Infinity"));}),_CD=1024,_CE=-1021,_CF=new T(function(){return B(unCStr("Negative exponent"));}),_CG=new T(function(){return B(err(_CF));}),_CH=new T1(0,2),_CI=new T(function(){return B(_4s(_CH,_lQ));}),_CJ=function(_CK,_CL,_CM){while(1){if(!E(_CI)){if(!B(_4s(B(_lR(_CL,_CH)),_lQ))){if(!B(_4s(_CL,_fv))){var _CN=B(_kG(_CK,_CK)),_CO=B(_mc(B(_e7(_CL,_fv)),_CH)),_CP=B(_kG(_CK,_CM));_CK=_CN;_CL=_CO;_CM=_CP;continue;}else{return new F(function(){return _kG(_CK,_CM);});}}else{var _CN=B(_kG(_CK,_CK)),_CO=B(_mc(_CL,_CH));_CK=_CN;_CL=_CO;continue;}}else{return E(_7V);}}},_CQ=function(_CR,_CS){while(1){if(!E(_CI)){if(!B(_4s(B(_lR(_CS,_CH)),_lQ))){if(!B(_4s(_CS,_fv))){return new F(function(){return _CJ(B(_kG(_CR,_CR)),B(_mc(B(_e7(_CS,_fv)),_CH)),_CR);});}else{return E(_CR);}}else{var _CT=B(_kG(_CR,_CR)),_CU=B(_mc(_CS,_CH));_CR=_CT;_CS=_CU;continue;}}else{return E(_7V);}}},_CV=function(_CW,_CX){if(!B(_cq(_CX,_lQ))){if(!B(_4s(_CX,_lQ))){return new F(function(){return _CQ(_CW,_CX);});}else{return E(_fv);}}else{return E(_CG);}},_CY=new T1(0,1),_CZ=function(_D0,_D1,_D2){while(1){var _D3=E(_D2);if(!_D3._){if(!B(_cq(_D0,_tp))){return new T2(0,B(_kG(_D1,B(_CV(_tf,_D0)))),_fv);}else{var _D4=B(_CV(_tf,B(_eM(_D0))));return new F(function(){return _mn(B(_kG(_D1,B(_ms(_D4)))),B(_m7(_D4)));});}}else{var _D5=B(_e7(_D0,_CY)),_D6=B(_bP(B(_kG(_D1,_tf)),B(_kE(E(_D3.a)))));_D0=_D5;_D1=_D6;_D2=_D3.b;continue;}}},_D7=function(_D8){var _D9=E(_D8);if(!_D9._){var _Da=_D9.b;return new F(function(){return _mn(B(_kG(B(_tq(new T(function(){return B(_kE(E(_D9.a)));}),new T(function(){return B(_76(_Da,0));},1),B(_9w(_tg,_Da)))),_CY)),_CY);});}else{var _Db=_D9.a,_Dc=_D9.c,_Dd=E(_D9.b);if(!_Dd._){var _De=E(_Dc);if(!_De._){return new F(function(){return _mn(B(_kG(B(_tH(_tf,_Db)),_CY)),_CY);});}else{var _Df=_De.a;if(!B(_km(_Df,_tp))){var _Dg=B(_CV(_tf,B(_eM(_Df))));return new F(function(){return _mn(B(_kG(B(_tH(_tf,_Db)),B(_ms(_Dg)))),B(_m7(_Dg)));});}else{return new F(function(){return _mn(B(_kG(B(_kG(B(_tH(_tf,_Db)),B(_CV(_tf,_Df)))),_CY)),_CY);});}}}else{var _Dh=_Dd.a,_Di=E(_Dc);if(!_Di._){return new F(function(){return _CZ(_tp,B(_tH(_tf,_Db)),_Dh);});}else{return new F(function(){return _CZ(_Di.a,B(_tH(_tf,_Db)),_Dh);});}}}},_Dj=function(_Dk,_Dl){while(1){var _Dm=E(_Dl);if(!_Dm._){return __Z;}else{if(!B(A1(_Dk,_Dm.a))){return E(_Dm);}else{_Dl=_Dm.b;continue;}}}},_Dn=0,_Do=function(_Dp){return new F(function(){return _6Z(_Dn,_Dp);});},_Dq=new T2(0,E(_tp),E(_fv)),_Dr=new T1(1,_Dq),_Ds=new T1(0,-2147483648),_Dt=new T1(0,2147483647),_Du=function(_Dv,_Dw,_Dx){var _Dy=E(_Dx);if(!_Dy._){return new T1(1,new T(function(){var _Dz=B(_D7(_Dy));return new T2(0,E(_Dz.a),E(_Dz.b));}));}else{var _DA=E(_Dy.c);if(!_DA._){return new T1(1,new T(function(){var _DB=B(_D7(_Dy));return new T2(0,E(_DB.a),E(_DB.b));}));}else{var _DC=_DA.a;if(!B(_ch(_DC,_Dt))){if(!B(_cq(_DC,_Ds))){var _DD=function(_DE){var _DF=_DE+B(_bM(_DC))|0;return (_DF<=(E(_Dw)+3|0))?(_DF>=(E(_Dv)-3|0))?new T1(1,new T(function(){var _DG=B(_D7(_Dy));return new T2(0,E(_DG.a),E(_DG.b));})):E(_Dr):__Z;},_DH=B(_Dj(_Do,_Dy.a));if(!_DH._){var _DI=E(_Dy.b);if(!_DI._){return E(_Dr);}else{var _DJ=B(_d4(_Do,_DI.a));if(!E(_DJ.b)._){return E(_Dr);}else{return new F(function(){return _DD( -B(_76(_DJ.a,0)));});}}}else{return new F(function(){return _DD(B(_76(_DH,0)));});}}else{return __Z;}}else{return __Z;}}}},_DK=function(_DL,_DM){return new T0(2);},_DN=function(_DO){var _DP=E(_DO);switch(_DP._){case 3:var _DQ=_DP.a;return (!B(_qR(_DQ,_CC)))?(!B(_qR(_DQ,_CB)))?E(_DK):E(_Cy):E(_Cu);case 5:var _DR=B(_Du(_CE,_CD,_DP.a));if(!_DR._){return E(_Cu);}else{var _DS=new T(function(){var _DT=E(_DR.a);return B(_eU(_DT.a,_DT.b));});return function(_DU,_DV){return new F(function(){return A1(_DV,_DS);});};}break;default:return E(_DK);}},_DW=function(_DX){var _DY=function(_DZ){return E(new T2(3,_DX,_rn));};return new T1(1,function(_E0){return new F(function(){return A2(_zN,_E0,_DY);});});},_E1=new T(function(){return B(A3(_C8,_DN,_BD,_DW));}),_E2=new T(function(){return B(unCStr("Canvas ID could not be found!"));}),_E3=new T(function(){return B(err(_E2));}),_E4=function(_E5,_E6,_E7,_E8){var _E9=B(_4B(_E7)),_Ea=B(_4B(_E8));if(_E9>_Ea){var _Eb= -_E9,_Ec=B(_4I(_Eb,_E7)),_Ed=B(_4I(_Eb,_E8)),_Ee=_E7*_Ec+_E8*_Ed;return new T2(0,(_E5*_Ec+_E6*_Ed)/_Ee,(_E6*_Ec-_E5*_Ed)/_Ee);}else{var _Ef= -_Ea,_Eg=B(_4I(_Ef,_E7)),_Eh=B(_4I(_Ef,_E8)),_Ei=_E7*_Eg+_E8*_Eh;return new T2(0,(_E5*_Eg+_E6*_Eh)/_Ei,(_E6*_Eg-_E5*_Eh)/_Ei);}},_Ej=new T1(0,1),_Ek=new T1(0,2),_El=new T(function(){var _Em=B(_mG(_Ej,_Ek));return new T2(1,_Em.a,_Em.b);}),_En=function(_Eo){var _Ep=new T(function(){var _Eq=function(_Er,_Es,_Et,_Eu){while(1){var _Ev=E(_Er);if(!_Ev._){return new T2(0,_Et,_Eu);}else{var _Ew=B(_f5(_Ev.a)),_Ex=6.283185307179586*_Ew,_Ey=0*_Ew,_Ez=B(_E4(_Ex*_Eo-_Ey*0,_Ex*0+_Ey*_Eo,256,0)),_EA=E(_Ez.a),_EB=E(_Ez.b),_EC=B(_E4(Math.sin(_EA)*cosh(_EB),Math.cos(_EA)*sinh(_EB),_Ew,0)),_ED=E(_EC.a),_EE=E(_EC.b),_EF=E(_Es);if(_EF==1){return new T2(0,_Et+_ED,_Eu+_EE);}else{var _EG=_Et+_ED,_EH=_Eu+_EE;_Er=_Ev.b;_Es=_EF-1|0;_Et=_EG;_Eu=_EH;continue;}}}},_EI=B(_Eq(_El,32,0,0));return new T2(0,E(_EI.a),E(_EI.b));});return new T2(0,_Ep,new T(function(){var _EJ=E(_Eo);if(_EJ==255){return __Z;}else{var _EK=B(_En(_EJ+1|0));return new T2(1,_EK.a,_EK.b);}}));},_EL=new T(function(){var _EM=B(_En(0));return new T2(1,_EM.a,_EM.b);}),_EN=new T(function(){return B(_av(_EL));}),_EO=new T(function(){var _EP=B(_7k(256,2));if(0>=_EP){return __Z;}else{return B(_6a(_EP,_EN));}}),_EQ=new T(function(){return B(unCStr("height"));}),_ER=new T(function(){return B(unCStr("width"));}),_ES="canvas",_ET=function(_EU){return (!E(_EU))?true:false;},_EV=function(_EW){return E(E(_EW).b);},_EX=function(_EY){return E(E(_EY).a);},_EZ=function(_){return new F(function(){return nMV(_2E);});},_F0=new T(function(){return B(_gi(_EZ));}),_F1=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_F2=function(_F3,_F4,_F5,_F6,_F7,_F8){var _F9=B(_g9(_F3)),_Fa=B(_gb(_F9)),_Fb=new T(function(){return B(_gn(_F9));}),_Fc=new T(function(){return B(_pK(_Fa));}),_Fd=new T(function(){return B(A2(_pA,_F4,_F6));}),_Fe=new T(function(){return B(A2(_EX,_F5,_F7));}),_Ff=function(_Fg){return new F(function(){return A1(_Fc,new T3(0,_Fe,_Fd,_Fg));});},_Fh=function(_Fi){var _Fj=new T(function(){var _Fk=new T(function(){var _Fl=__createJSFunc(2,function(_Fm,_){var _Fn=B(A2(E(_Fi),_Fm,_));return _gm;}),_Fo=_Fl;return function(_){return new F(function(){return __app3(E(_F1),E(_Fd),E(_Fe),_Fo);});};});return B(A1(_Fb,_Fk));});return new F(function(){return A3(_gd,_Fa,_Fj,_Ff);});},_Fp=new T(function(){var _Fq=new T(function(){return B(_gn(_F9));}),_Fr=function(_Fs){var _Ft=new T(function(){return B(A1(_Fq,function(_){var _=wMV(E(_F0),new T1(1,_Fs));return new F(function(){return A(_EV,[_F5,_F7,_Fs,_]);});}));});return new F(function(){return A3(_gd,_Fa,_Ft,_F8);});};return B(A2(_gp,_F3,_Fr));});return new F(function(){return A3(_gd,_Fa,_Fp,_Fh);});},_Fu=function(_Fv){while(1){var _Fw=B((function(_Fx){var _Fy=E(_Fx);if(!_Fy._){return __Z;}else{var _Fz=_Fy.b,_FA=E(_Fy.a);if(!E(_FA.b)._){return new T2(1,_FA.a,new T(function(){return B(_Fu(_Fz));}));}else{_Fv=_Fz;return __continue;}}})(_Fv));if(_Fw!=__continue){return _Fw;}}},_FB=function(_FC,_){var _FD=E(_FC);if(!_FD._){return _Y;}else{var _FE=B(A1(_FD.a,_)),_FF=B(_FB(_FD.b,_));return new T2(1,_FE,_FF);}},_FG=function(_){var _FH=B(A3(_ps,_2U,_ES,_)),_FI=E(_FH);if(!_FI._){return E(_E3);}else{var _FJ=_FI.a,_FK=B(A(_pM,[_t,_2U,_FJ,_ER,_])),_FL=_FK,_FM=B(A(_pM,[_t,_2U,_FJ,_EQ,_])),_FN=_FM,_FO=B(_7k(256,2)),_FP=function(_,_FQ){var _FR=nMV(_6g),_FS=_FR,_FT=function(_FU,_){if(E(E(_FU).a)==13){var _FV=rMV(_FS),_=wMV(_FS,new T(function(){return B(_ET(_FV));}));return _30;}else{return _30;}},_FW=B(A(_F2,[_2V,_t,_m,_pq,_pp,_FT,_])),_FX=E(_FJ),_FY=__app1(E(_o),_FX);if(!_FY){return E(_pX);}else{var _FZ=__app1(E(_n),_FX),_G0=B(_gU(new T2(0,_FZ,_FX),new T(function(){var _G1=B(_Fu(B(_q3(_E1,_FL))));if(!_G1._){return E(_pZ);}else{if(!E(_G1.b)._){return E(_G1.a);}else{return E(_q1);}}}),new T(function(){var _G2=B(_Fu(B(_q3(_E1,_FN))));if(!_G2._){return E(_pZ);}else{if(!E(_G2.b)._){return E(_G2.a);}else{return E(_q1);}}}),_EL,_EO,_9l,_FQ,_FS,_6h,_));return new T(function(){return E(E(_G0).a);});}};if(0>=_FO){var _G3=B(_FB(_Y,_));return new F(function(){return _FP(_,_G3);});}else{var _G4=B(_FB(B(_pm(_FO)),_));return new F(function(){return _FP(_,_G4);});}}},_G5=function(_){return new F(function(){return _FG(_);});};
var hasteMain = function() {B(A(_G5, [0]));};window.onload = hasteMain;