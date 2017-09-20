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

var _0="metaKey",_1="shiftKey",_2="altKey",_3="ctrlKey",_4="keyCode",_5=function(_6,_){var _7=__get(_6,E(_4)),_8=__get(_6,E(_3)),_9=__get(_6,E(_2)),_a=__get(_6,E(_1)),_b=__get(_6,E(_0));return new T(function(){var _c=Number(_7),_d=jsTrunc(_c);return new T5(0,_d,E(_8),E(_9),E(_a),E(_b));});},_e=function(_f,_g,_){return new F(function(){return _5(E(_g),_);});},_h="keydown",_i="keyup",_j="keypress",_k=function(_l){switch(E(_l)){case 0:return E(_j);case 1:return E(_i);default:return E(_h);}},_m=new T2(0,_k,_e),_n="deltaZ",_o="deltaY",_p="deltaX",_q=function(_r,_s){var _t=E(_r);return (_t._==0)?E(_s):new T2(1,_t.a,new T(function(){return B(_q(_t.b,_s));}));},_u=function(_v,_w){var _x=jsShowI(_v);return new F(function(){return _q(fromJSStr(_x),_w);});},_y=41,_z=40,_A=function(_B,_C,_D){if(_C>=0){return new F(function(){return _u(_C,_D);});}else{if(_B<=6){return new F(function(){return _u(_C,_D);});}else{return new T2(1,_z,new T(function(){var _E=jsShowI(_C);return B(_q(fromJSStr(_E),new T2(1,_y,_D)));}));}}},_F=new T(function(){return B(unCStr(")"));}),_G=new T(function(){return B(_A(0,2,_F));}),_H=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_G));}),_I=function(_J){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_A(0,_J,_H));}))));});},_K=function(_L,_){return new T(function(){var _M=Number(E(_L)),_N=jsTrunc(_M);if(_N<0){return B(_I(_N));}else{if(_N>2){return B(_I(_N));}else{return _N;}}});},_O=0,_P=new T3(0,_O,_O,_O),_Q="button",_R=new T(function(){return eval("jsGetMouseCoords");}),_S=__Z,_T=function(_U,_){var _V=E(_U);if(!_V._){return _S;}else{var _W=B(_T(_V.b,_));return new T2(1,new T(function(){var _X=Number(E(_V.a));return jsTrunc(_X);}),_W);}},_Y=function(_Z,_){var _10=__arr2lst(0,_Z);return new F(function(){return _T(_10,_);});},_11=function(_12,_){return new F(function(){return _Y(E(_12),_);});},_13=function(_14,_){return new T(function(){var _15=Number(E(_14));return jsTrunc(_15);});},_16=new T2(0,_13,_11),_17=function(_18,_){var _19=E(_18);if(!_19._){return _S;}else{var _1a=B(_17(_19.b,_));return new T2(1,_19.a,_1a);}},_1b=new T(function(){return B(unCStr("base"));}),_1c=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1d=new T(function(){return B(unCStr("IOException"));}),_1e=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1b,_1c,_1d),_1f=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_1e,_S,_S),_1g=function(_1h){return E(_1f);},_1i=function(_1j){return E(E(_1j).a);},_1k=function(_1l,_1m,_1n){var _1o=B(A1(_1l,_)),_1p=B(A1(_1m,_)),_1q=hs_eqWord64(_1o.a,_1p.a);if(!_1q){return __Z;}else{var _1r=hs_eqWord64(_1o.b,_1p.b);return (!_1r)?__Z:new T1(1,_1n);}},_1s=function(_1t){var _1u=E(_1t);return new F(function(){return _1k(B(_1i(_1u.a)),_1g,_1u.b);});},_1v=new T(function(){return B(unCStr(": "));}),_1w=new T(function(){return B(unCStr(")"));}),_1x=new T(function(){return B(unCStr(" ("));}),_1y=new T(function(){return B(unCStr("interrupted"));}),_1z=new T(function(){return B(unCStr("system error"));}),_1A=new T(function(){return B(unCStr("unsatisified constraints"));}),_1B=new T(function(){return B(unCStr("user error"));}),_1C=new T(function(){return B(unCStr("permission denied"));}),_1D=new T(function(){return B(unCStr("illegal operation"));}),_1E=new T(function(){return B(unCStr("end of file"));}),_1F=new T(function(){return B(unCStr("resource exhausted"));}),_1G=new T(function(){return B(unCStr("resource busy"));}),_1H=new T(function(){return B(unCStr("does not exist"));}),_1I=new T(function(){return B(unCStr("already exists"));}),_1J=new T(function(){return B(unCStr("resource vanished"));}),_1K=new T(function(){return B(unCStr("timeout"));}),_1L=new T(function(){return B(unCStr("unsupported operation"));}),_1M=new T(function(){return B(unCStr("hardware fault"));}),_1N=new T(function(){return B(unCStr("inappropriate type"));}),_1O=new T(function(){return B(unCStr("invalid argument"));}),_1P=new T(function(){return B(unCStr("failed"));}),_1Q=new T(function(){return B(unCStr("protocol error"));}),_1R=function(_1S,_1T){switch(E(_1S)){case 0:return new F(function(){return _q(_1I,_1T);});break;case 1:return new F(function(){return _q(_1H,_1T);});break;case 2:return new F(function(){return _q(_1G,_1T);});break;case 3:return new F(function(){return _q(_1F,_1T);});break;case 4:return new F(function(){return _q(_1E,_1T);});break;case 5:return new F(function(){return _q(_1D,_1T);});break;case 6:return new F(function(){return _q(_1C,_1T);});break;case 7:return new F(function(){return _q(_1B,_1T);});break;case 8:return new F(function(){return _q(_1A,_1T);});break;case 9:return new F(function(){return _q(_1z,_1T);});break;case 10:return new F(function(){return _q(_1Q,_1T);});break;case 11:return new F(function(){return _q(_1P,_1T);});break;case 12:return new F(function(){return _q(_1O,_1T);});break;case 13:return new F(function(){return _q(_1N,_1T);});break;case 14:return new F(function(){return _q(_1M,_1T);});break;case 15:return new F(function(){return _q(_1L,_1T);});break;case 16:return new F(function(){return _q(_1K,_1T);});break;case 17:return new F(function(){return _q(_1J,_1T);});break;default:return new F(function(){return _q(_1y,_1T);});}},_1U=new T(function(){return B(unCStr("}"));}),_1V=new T(function(){return B(unCStr("{handle: "));}),_1W=function(_1X,_1Y,_1Z,_20,_21,_22){var _23=new T(function(){var _24=new T(function(){var _25=new T(function(){var _26=E(_20);if(!_26._){return E(_22);}else{var _27=new T(function(){return B(_q(_26,new T(function(){return B(_q(_1w,_22));},1)));},1);return B(_q(_1x,_27));}},1);return B(_1R(_1Y,_25));}),_28=E(_1Z);if(!_28._){return E(_24);}else{return B(_q(_28,new T(function(){return B(_q(_1v,_24));},1)));}}),_29=E(_21);if(!_29._){var _2a=E(_1X);if(!_2a._){return E(_23);}else{var _2b=E(_2a.a);if(!_2b._){var _2c=new T(function(){var _2d=new T(function(){return B(_q(_1U,new T(function(){return B(_q(_1v,_23));},1)));},1);return B(_q(_2b.a,_2d));},1);return new F(function(){return _q(_1V,_2c);});}else{var _2e=new T(function(){var _2f=new T(function(){return B(_q(_1U,new T(function(){return B(_q(_1v,_23));},1)));},1);return B(_q(_2b.a,_2f));},1);return new F(function(){return _q(_1V,_2e);});}}}else{return new F(function(){return _q(_29.a,new T(function(){return B(_q(_1v,_23));},1));});}},_2g=function(_2h){var _2i=E(_2h);return new F(function(){return _1W(_2i.a,_2i.b,_2i.c,_2i.d,_2i.f,_S);});},_2j=function(_2k,_2l,_2m){var _2n=E(_2l);return new F(function(){return _1W(_2n.a,_2n.b,_2n.c,_2n.d,_2n.f,_2m);});},_2o=function(_2p,_2q){var _2r=E(_2p);return new F(function(){return _1W(_2r.a,_2r.b,_2r.c,_2r.d,_2r.f,_2q);});},_2s=44,_2t=93,_2u=91,_2v=function(_2w,_2x,_2y){var _2z=E(_2x);if(!_2z._){return new F(function(){return unAppCStr("[]",_2y);});}else{var _2A=new T(function(){var _2B=new T(function(){var _2C=function(_2D){var _2E=E(_2D);if(!_2E._){return E(new T2(1,_2t,_2y));}else{var _2F=new T(function(){return B(A2(_2w,_2E.a,new T(function(){return B(_2C(_2E.b));})));});return new T2(1,_2s,_2F);}};return B(_2C(_2z.b));});return B(A2(_2w,_2z.a,_2B));});return new T2(1,_2u,_2A);}},_2G=function(_2H,_2I){return new F(function(){return _2v(_2o,_2H,_2I);});},_2J=new T3(0,_2j,_2g,_2G),_2K=new T(function(){return new T5(0,_1g,_2J,_2L,_1s,_2g);}),_2L=function(_2M){return new T2(0,_2K,_2M);},_2N=__Z,_2O=7,_2P=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:272:5-9"));}),_2Q=new T6(0,_2N,_2O,_S,_2P,_2N,_2N),_2R=new T(function(){return B(_2L(_2Q));}),_2S=function(_){return new F(function(){return die(_2R);});},_2T=function(_2U){return E(E(_2U).a);},_2V=function(_2W,_2X,_2Y,_){var _2Z=__arr2lst(0,_2Y),_30=B(_17(_2Z,_)),_31=E(_30);if(!_31._){return new F(function(){return _2S(_);});}else{var _32=E(_31.b);if(!_32._){return new F(function(){return _2S(_);});}else{if(!E(_32.b)._){var _33=B(A3(_2T,_2W,_31.a,_)),_34=B(A3(_2T,_2X,_32.a,_));return new T2(0,_33,_34);}else{return new F(function(){return _2S(_);});}}}},_35=function(_){return new F(function(){return __jsNull();});},_36=function(_37){var _38=B(A1(_37,_));return E(_38);},_39=new T(function(){return B(_36(_35));}),_3a=new T(function(){return E(_39);}),_3b=function(_3c,_3d,_){if(E(_3c)==7){var _3e=__app1(E(_R),_3d),_3f=B(_2V(_16,_16,_3e,_)),_3g=__get(_3d,E(_p)),_3h=__get(_3d,E(_o)),_3i=__get(_3d,E(_n));return new T(function(){return new T3(0,E(_3f),E(_2N),E(new T3(0,_3g,_3h,_3i)));});}else{var _3j=__app1(E(_R),_3d),_3k=B(_2V(_16,_16,_3j,_)),_3l=__get(_3d,E(_Q)),_3m=__eq(_3l,E(_3a));if(!E(_3m)){var _3n=B(_K(_3l,_));return new T(function(){return new T3(0,E(_3k),E(new T1(1,_3n)),E(_P));});}else{return new T(function(){return new T3(0,E(_3k),E(_2N),E(_P));});}}},_3o=function(_3p,_3q,_){return new F(function(){return _3b(_3p,E(_3q),_);});},_3r="mouseout",_3s="mouseover",_3t="mousemove",_3u="mouseup",_3v="mousedown",_3w="dblclick",_3x="click",_3y="wheel",_3z=function(_3A){switch(E(_3A)){case 0:return E(_3x);case 1:return E(_3w);case 2:return E(_3v);case 3:return E(_3u);case 4:return E(_3t);case 5:return E(_3s);case 6:return E(_3r);default:return E(_3y);}},_3B=new T2(0,_3z,_3o),_3C=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_3D=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_3E=function(_3F,_){return new T1(1,_3F);},_3G=function(_3H){return E(_3H);},_3I=new T2(0,_3G,_3E),_3J=function(_3K,_3L,_){var _3M=B(A1(_3K,_)),_3N=B(A1(_3L,_));return _3M;},_3O=function(_3P,_3Q,_){var _3R=B(A1(_3P,_)),_3S=B(A1(_3Q,_));return new T(function(){return B(A1(_3R,_3S));});},_3T=function(_3U,_3V,_){var _3W=B(A1(_3V,_));return _3U;},_3X=function(_3Y,_3Z,_){var _40=B(A1(_3Z,_));return new T(function(){return B(A1(_3Y,_40));});},_41=new T2(0,_3X,_3T),_42=function(_43,_){return _43;},_44=function(_45,_46,_){var _47=B(A1(_45,_));return new F(function(){return A1(_46,_);});},_48=new T5(0,_41,_42,_3O,_44,_3J),_49=new T(function(){return E(_2K);}),_4a=function(_4b){return E(E(_4b).c);},_4c=function(_4d){return new T6(0,_2N,_2O,_S,_4d,_2N,_2N);},_4e=function(_4f,_){var _4g=new T(function(){return B(A2(_4a,_49,new T(function(){return B(A1(_4c,_4f));})));});return new F(function(){return die(_4g);});},_4h=function(_4i,_){return new F(function(){return _4e(_4i,_);});},_4j=function(_4k){return new F(function(){return A1(_4h,_4k);});},_4l=function(_4m,_4n,_){var _4o=B(A1(_4m,_));return new F(function(){return A2(_4n,_4o,_);});},_4p=new T5(0,_48,_4l,_44,_42,_4j),_4q=new T2(0,_4p,_3G),_4r=new T2(0,_4q,_42),_4s=0,_4t=function(_4u,_4v,_){return new T2(0,function(_4w,_){var _4x=B(A3(_4u,_4w,_4v,_));return _4s;},_4v);},_4y=function(_4z,_4A,_){var _4B=B(A1(_4z,_));return new T2(0,_4B,_4A);},_4C=function(_4D,_4E,_4F,_){var _4G=B(A2(_4D,_4F,_)),_4H=B(A2(_4E,new T(function(){return E(E(_4G).b);}),_));return new T2(0,new T(function(){return E(E(_4G).a);}),new T(function(){return E(E(_4H).b);}));},_4I=function(_4J,_4K,_4L,_){var _4M=B(A2(_4J,_4L,_)),_4N=B(A2(_4K,new T(function(){return E(E(_4M).b);}),_));return new T2(0,new T(function(){return E(E(_4N).a);}),new T(function(){return E(E(_4N).b);}));},_4O=function(_4P,_4Q,_4R,_){var _4S=B(A2(_4P,_4R,_)),_4T=B(A2(_4Q,new T(function(){return E(E(_4S).b);}),_)),_4U=new T(function(){return B(A1(E(_4S).a,new T(function(){return E(E(_4T).a);})));});return new T2(0,_4U,new T(function(){return E(E(_4T).b);}));},_4V=function(_4W,_4X,_4Y,_){return new F(function(){return _4O(_4W,_4X,_4Y,_);});},_4Z=function(_50,_51,_){return new T2(0,_50,_51);},_52=function(_4X,_4Y,_){return new F(function(){return _4Z(_4X,_4Y,_);});},_53=function(_54,_55,_56,_){var _57=B(A2(_55,_56,_));return new T2(0,_54,new T(function(){return E(E(_57).b);}));},_58=function(_59,_5a,_5b,_){var _5c=B(A2(_5a,_5b,_)),_5d=new T(function(){return B(A1(_59,new T(function(){return E(E(_5c).a);})));});return new T2(0,_5d,new T(function(){return E(E(_5c).b);}));},_5e=function(_4W,_4X,_4Y,_){return new F(function(){return _58(_4W,_4X,_4Y,_);});},_5f=new T2(0,_5e,_53),_5g=new T5(0,_5f,_52,_4V,_4I,_4C),_5h=function(_5i,_5j,_5k,_){var _5l=B(A2(_5i,_5k,_));return new F(function(){return A2(_5j,new T(function(){return E(E(_5l).b);}),_);});},_5m=function(_4W,_4X,_4Y,_){return new F(function(){return _5h(_4W,_4X,_4Y,_);});},_5n=function(_5o,_5p,_5q,_){var _5r=B(A2(_5o,_5q,_));return new F(function(){return A3(_5p,new T(function(){return E(E(_5r).a);}),new T(function(){return E(E(_5r).b);}),_);});},_5s=function(_4W,_4X,_4Y,_){return new F(function(){return _5n(_4W,_4X,_4Y,_);});},_5t=function(_5u,_5v,_){return new F(function(){return _4e(_5u,_);});},_5w=function(_4X,_4Y,_){return new F(function(){return _5t(_4X,_4Y,_);});},_5x=new T5(0,_5g,_5s,_5m,_52,_5w),_5y=new T2(0,_5x,_4y),_5z=new T2(0,_5y,_4t),_5A=0,_5B=function(_5C,_5D){return E(_5C)==E(_5D);},_5E=function(_5F,_5G){return E(_5F)!=E(_5G);},_5H=new T2(0,_5B,_5E),_5I=function(_5J,_5K){var _5L=E(_5J),_5M=E(_5K);return (_5L>_5M)?E(_5L):E(_5M);},_5N=function(_5O,_5P){var _5Q=E(_5O),_5R=E(_5P);return (_5Q>_5R)?E(_5R):E(_5Q);},_5S=function(_5T,_5U){return (_5T>=_5U)?(_5T!=_5U)?2:1:0;},_5V=function(_5W,_5X){return new F(function(){return _5S(E(_5W),E(_5X));});},_5Y=function(_5Z,_60){return E(_5Z)>=E(_60);},_61=function(_62,_63){return E(_62)>E(_63);},_64=function(_65,_66){return E(_65)<=E(_66);},_67=function(_68,_69){return E(_68)<E(_69);},_6a={_:0,a:_5H,b:_5V,c:_67,d:_64,e:_61,f:_5Y,g:_5I,h:_5N},_6b=new T(function(){return B(unCStr("printf: formatting string ended prematurely"));}),_6c=new T(function(){return B(err(_6b));}),_6d=function(_6e,_6f){var _6g=E(_6f);return (_6g._==0)?E(_6c):new T3(0,_S,_6g.a,_6g.b);},_6h=new T(function(){return B(unCStr("!!: negative index"));}),_6i=new T(function(){return B(unCStr("Prelude."));}),_6j=new T(function(){return B(_q(_6i,_6h));}),_6k=new T(function(){return B(err(_6j));}),_6l=new T(function(){return B(unCStr("!!: index too large"));}),_6m=new T(function(){return B(_q(_6i,_6l));}),_6n=new T(function(){return B(err(_6m));}),_6o=function(_6p,_6q){while(1){var _6r=E(_6p);if(!_6r._){return E(_6n);}else{var _6s=E(_6q);if(!_6s){return E(_6r.a);}else{_6p=_6r.b;_6q=_6s-1|0;continue;}}}},_6t=function(_6u,_6v){if(_6v>=0){return new F(function(){return _6o(_6u,_6v);});}else{return E(_6k);}},_6w=new T(function(){return B(unCStr("ACK"));}),_6x=new T(function(){return B(unCStr("BEL"));}),_6y=new T(function(){return B(unCStr("BS"));}),_6z=new T(function(){return B(unCStr("SP"));}),_6A=new T2(1,_6z,_S),_6B=new T(function(){return B(unCStr("US"));}),_6C=new T2(1,_6B,_6A),_6D=new T(function(){return B(unCStr("RS"));}),_6E=new T2(1,_6D,_6C),_6F=new T(function(){return B(unCStr("GS"));}),_6G=new T2(1,_6F,_6E),_6H=new T(function(){return B(unCStr("FS"));}),_6I=new T2(1,_6H,_6G),_6J=new T(function(){return B(unCStr("ESC"));}),_6K=new T2(1,_6J,_6I),_6L=new T(function(){return B(unCStr("SUB"));}),_6M=new T2(1,_6L,_6K),_6N=new T(function(){return B(unCStr("EM"));}),_6O=new T2(1,_6N,_6M),_6P=new T(function(){return B(unCStr("CAN"));}),_6Q=new T2(1,_6P,_6O),_6R=new T(function(){return B(unCStr("ETB"));}),_6S=new T2(1,_6R,_6Q),_6T=new T(function(){return B(unCStr("SYN"));}),_6U=new T2(1,_6T,_6S),_6V=new T(function(){return B(unCStr("NAK"));}),_6W=new T2(1,_6V,_6U),_6X=new T(function(){return B(unCStr("DC4"));}),_6Y=new T2(1,_6X,_6W),_6Z=new T(function(){return B(unCStr("DC3"));}),_70=new T2(1,_6Z,_6Y),_71=new T(function(){return B(unCStr("DC2"));}),_72=new T2(1,_71,_70),_73=new T(function(){return B(unCStr("DC1"));}),_74=new T2(1,_73,_72),_75=new T(function(){return B(unCStr("DLE"));}),_76=new T2(1,_75,_74),_77=new T(function(){return B(unCStr("SI"));}),_78=new T2(1,_77,_76),_79=new T(function(){return B(unCStr("SO"));}),_7a=new T2(1,_79,_78),_7b=new T(function(){return B(unCStr("CR"));}),_7c=new T2(1,_7b,_7a),_7d=new T(function(){return B(unCStr("FF"));}),_7e=new T2(1,_7d,_7c),_7f=new T(function(){return B(unCStr("VT"));}),_7g=new T2(1,_7f,_7e),_7h=new T(function(){return B(unCStr("LF"));}),_7i=new T2(1,_7h,_7g),_7j=new T(function(){return B(unCStr("HT"));}),_7k=new T2(1,_7j,_7i),_7l=new T2(1,_6y,_7k),_7m=new T2(1,_6x,_7l),_7n=new T2(1,_6w,_7m),_7o=new T(function(){return B(unCStr("ENQ"));}),_7p=new T2(1,_7o,_7n),_7q=new T(function(){return B(unCStr("EOT"));}),_7r=new T2(1,_7q,_7p),_7s=new T(function(){return B(unCStr("ETX"));}),_7t=new T2(1,_7s,_7r),_7u=new T(function(){return B(unCStr("STX"));}),_7v=new T2(1,_7u,_7t),_7w=new T(function(){return B(unCStr("SOH"));}),_7x=new T2(1,_7w,_7v),_7y=new T(function(){return B(unCStr("NUL"));}),_7z=new T2(1,_7y,_7x),_7A=92,_7B=new T(function(){return B(unCStr("\\DEL"));}),_7C=new T(function(){return B(unCStr("\\a"));}),_7D=new T(function(){return B(unCStr("\\\\"));}),_7E=new T(function(){return B(unCStr("\\SO"));}),_7F=new T(function(){return B(unCStr("\\r"));}),_7G=new T(function(){return B(unCStr("\\f"));}),_7H=new T(function(){return B(unCStr("\\v"));}),_7I=new T(function(){return B(unCStr("\\n"));}),_7J=new T(function(){return B(unCStr("\\t"));}),_7K=new T(function(){return B(unCStr("\\b"));}),_7L=function(_7M,_7N){if(_7M<=127){var _7O=E(_7M);switch(_7O){case 92:return new F(function(){return _q(_7D,_7N);});break;case 127:return new F(function(){return _q(_7B,_7N);});break;default:if(_7O<32){var _7P=E(_7O);switch(_7P){case 7:return new F(function(){return _q(_7C,_7N);});break;case 8:return new F(function(){return _q(_7K,_7N);});break;case 9:return new F(function(){return _q(_7J,_7N);});break;case 10:return new F(function(){return _q(_7I,_7N);});break;case 11:return new F(function(){return _q(_7H,_7N);});break;case 12:return new F(function(){return _q(_7G,_7N);});break;case 13:return new F(function(){return _q(_7F,_7N);});break;case 14:return new F(function(){return _q(_7E,new T(function(){var _7Q=E(_7N);if(!_7Q._){return __Z;}else{if(E(_7Q.a)==72){return B(unAppCStr("\\&",_7Q));}else{return E(_7Q);}}},1));});break;default:return new F(function(){return _q(new T2(1,_7A,new T(function(){return B(_6t(_7z,_7P));})),_7N);});}}else{return new T2(1,_7O,_7N);}}}else{var _7R=new T(function(){var _7S=jsShowI(_7M);return B(_q(fromJSStr(_7S),new T(function(){var _7T=E(_7N);if(!_7T._){return __Z;}else{var _7U=E(_7T.a);if(_7U<48){return E(_7T);}else{if(_7U>57){return E(_7T);}else{return B(unAppCStr("\\&",_7T));}}}},1)));});return new T2(1,_7A,_7R);}},_7V=39,_7W=new T2(1,_7V,_S),_7X=new T(function(){return B(unCStr("\'\\\'\'"));}),_7Y=new T(function(){return B(_q(_7X,_S));}),_7Z=function(_80){var _81=new T(function(){var _82=new T(function(){var _83=E(_80);if(_83==39){return E(_7Y);}else{return new T2(1,_7V,new T(function(){return B(_7L(_83,_7W));}));}});return B(unAppCStr("bad formatting char ",_82));});return new F(function(){return err(B(unAppCStr("printf: ",_81)));});},_84=new T(function(){return B(unCStr("-"));}),_85=new T(function(){return B(unCStr("printf: internal error: impossible dfmt"));}),_86=new T(function(){return B(err(_85));}),_87=function(_88){var _89=E(_88);return new F(function(){return Math.log(_89+(_89+1)*Math.sqrt((_89-1)/(_89+1)));});},_8a=function(_8b){var _8c=E(_8b);return new F(function(){return Math.log(_8c+Math.sqrt(1+_8c*_8c));});},_8d=function(_8e){var _8f=E(_8e);return 0.5*Math.log((1+_8f)/(1-_8f));},_8g=function(_8h,_8i){return Math.log(E(_8i))/Math.log(E(_8h));},_8j=3.141592653589793,_8k=new T1(0,1),_8l=function(_8m,_8n){var _8o=E(_8m);if(!_8o._){var _8p=_8o.a,_8q=E(_8n);if(!_8q._){var _8r=_8q.a;return (_8p!=_8r)?(_8p>_8r)?2:0:1;}else{var _8s=I_compareInt(_8q.a,_8p);return (_8s<=0)?(_8s>=0)?1:2:0;}}else{var _8t=_8o.a,_8u=E(_8n);if(!_8u._){var _8v=I_compareInt(_8t,_8u.a);return (_8v>=0)?(_8v<=0)?1:2:0;}else{var _8w=I_compare(_8t,_8u.a);return (_8w>=0)?(_8w<=0)?1:2:0;}}},_8x=new T(function(){return B(unCStr("base"));}),_8y=new T(function(){return B(unCStr("GHC.Exception"));}),_8z=new T(function(){return B(unCStr("ArithException"));}),_8A=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_8x,_8y,_8z),_8B=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_8A,_S,_S),_8C=function(_8D){return E(_8B);},_8E=function(_8F){var _8G=E(_8F);return new F(function(){return _1k(B(_1i(_8G.a)),_8C,_8G.b);});},_8H=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_8I=new T(function(){return B(unCStr("denormal"));}),_8J=new T(function(){return B(unCStr("divide by zero"));}),_8K=new T(function(){return B(unCStr("loss of precision"));}),_8L=new T(function(){return B(unCStr("arithmetic underflow"));}),_8M=new T(function(){return B(unCStr("arithmetic overflow"));}),_8N=function(_8O,_8P){switch(E(_8O)){case 0:return new F(function(){return _q(_8M,_8P);});break;case 1:return new F(function(){return _q(_8L,_8P);});break;case 2:return new F(function(){return _q(_8K,_8P);});break;case 3:return new F(function(){return _q(_8J,_8P);});break;case 4:return new F(function(){return _q(_8I,_8P);});break;default:return new F(function(){return _q(_8H,_8P);});}},_8Q=function(_8R){return new F(function(){return _8N(_8R,_S);});},_8S=function(_8T,_8U,_8V){return new F(function(){return _8N(_8U,_8V);});},_8W=function(_8X,_8Y){return new F(function(){return _2v(_8N,_8X,_8Y);});},_8Z=new T3(0,_8S,_8Q,_8W),_90=new T(function(){return new T5(0,_8C,_8Z,_91,_8E,_8Q);}),_91=function(_92){return new T2(0,_90,_92);},_93=3,_94=new T(function(){return B(_91(_93));}),_95=new T(function(){return die(_94);}),_96=function(_97,_98){var _99=E(_97);return (_99._==0)?_99.a*Math.pow(2,_98):I_toNumber(_99.a)*Math.pow(2,_98);},_9a=function(_9b,_9c){var _9d=E(_9b);if(!_9d._){var _9e=_9d.a,_9f=E(_9c);return (_9f._==0)?_9e==_9f.a:(I_compareInt(_9f.a,_9e)==0)?true:false;}else{var _9g=_9d.a,_9h=E(_9c);return (_9h._==0)?(I_compareInt(_9g,_9h.a)==0)?true:false:(I_compare(_9g,_9h.a)==0)?true:false;}},_9i=function(_9j){var _9k=E(_9j);if(!_9k._){return E(_9k.a);}else{return new F(function(){return I_toInt(_9k.a);});}},_9l=function(_9m,_9n){while(1){var _9o=E(_9m);if(!_9o._){var _9p=_9o.a,_9q=E(_9n);if(!_9q._){var _9r=_9q.a,_9s=addC(_9p,_9r);if(!E(_9s.b)){return new T1(0,_9s.a);}else{_9m=new T1(1,I_fromInt(_9p));_9n=new T1(1,I_fromInt(_9r));continue;}}else{_9m=new T1(1,I_fromInt(_9p));_9n=_9q;continue;}}else{var _9t=E(_9n);if(!_9t._){_9m=_9o;_9n=new T1(1,I_fromInt(_9t.a));continue;}else{return new T1(1,I_add(_9o.a,_9t.a));}}}},_9u=function(_9v,_9w){while(1){var _9x=E(_9v);if(!_9x._){var _9y=E(_9x.a);if(_9y==(-2147483648)){_9v=new T1(1,I_fromInt(-2147483648));continue;}else{var _9z=E(_9w);if(!_9z._){var _9A=_9z.a;return new T2(0,new T1(0,quot(_9y,_9A)),new T1(0,_9y%_9A));}else{_9v=new T1(1,I_fromInt(_9y));_9w=_9z;continue;}}}else{var _9B=E(_9w);if(!_9B._){_9v=_9x;_9w=new T1(1,I_fromInt(_9B.a));continue;}else{var _9C=I_quotRem(_9x.a,_9B.a);return new T2(0,new T1(1,_9C.a),new T1(1,_9C.b));}}}},_9D=new T1(0,0),_9E=function(_9F,_9G){while(1){var _9H=E(_9F);if(!_9H._){_9F=new T1(1,I_fromInt(_9H.a));continue;}else{return new T1(1,I_shiftLeft(_9H.a,_9G));}}},_9I=function(_9J,_9K,_9L){if(!B(_9a(_9L,_9D))){var _9M=B(_9u(_9K,_9L)),_9N=_9M.a;switch(B(_8l(B(_9E(_9M.b,1)),_9L))){case 0:return new F(function(){return _96(_9N,_9J);});break;case 1:if(!(B(_9i(_9N))&1)){return new F(function(){return _96(_9N,_9J);});}else{return new F(function(){return _96(B(_9l(_9N,_8k)),_9J);});}break;default:return new F(function(){return _96(B(_9l(_9N,_8k)),_9J);});}}else{return E(_95);}},_9O=function(_9P,_9Q){var _9R=E(_9P);if(!_9R._){var _9S=_9R.a,_9T=E(_9Q);return (_9T._==0)?_9S>_9T.a:I_compareInt(_9T.a,_9S)<0;}else{var _9U=_9R.a,_9V=E(_9Q);return (_9V._==0)?I_compareInt(_9U,_9V.a)>0:I_compare(_9U,_9V.a)>0;}},_9W=new T1(0,1),_9X=function(_9Y,_9Z){var _a0=E(_9Y);if(!_a0._){var _a1=_a0.a,_a2=E(_9Z);return (_a2._==0)?_a1<_a2.a:I_compareInt(_a2.a,_a1)>0;}else{var _a3=_a0.a,_a4=E(_9Z);return (_a4._==0)?I_compareInt(_a3,_a4.a)<0:I_compare(_a3,_a4.a)<0;}},_a5=new T(function(){return B(unCStr("base"));}),_a6=new T(function(){return B(unCStr("Control.Exception.Base"));}),_a7=new T(function(){return B(unCStr("PatternMatchFail"));}),_a8=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_a5,_a6,_a7),_a9=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_a8,_S,_S),_aa=function(_ab){return E(_a9);},_ac=function(_ad){var _ae=E(_ad);return new F(function(){return _1k(B(_1i(_ae.a)),_aa,_ae.b);});},_af=function(_ag){return E(E(_ag).a);},_ah=function(_ai){return new T2(0,_aj,_ai);},_ak=function(_al,_am){return new F(function(){return _q(E(_al).a,_am);});},_an=function(_ao,_ap){return new F(function(){return _2v(_ak,_ao,_ap);});},_aq=function(_ar,_as,_at){return new F(function(){return _q(E(_as).a,_at);});},_au=new T3(0,_aq,_af,_an),_aj=new T(function(){return new T5(0,_aa,_au,_ah,_ac,_af);}),_av=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_aw=function(_ax,_ay){return new F(function(){return die(new T(function(){return B(A2(_4a,_ay,_ax));}));});},_az=function(_aA,_92){return new F(function(){return _aw(_aA,_92);});},_aB=function(_aC,_aD){var _aE=E(_aD);if(!_aE._){return new T2(0,_S,_S);}else{var _aF=_aE.a;if(!B(A1(_aC,_aF))){return new T2(0,_S,_aE);}else{var _aG=new T(function(){var _aH=B(_aB(_aC,_aE.b));return new T2(0,_aH.a,_aH.b);});return new T2(0,new T2(1,_aF,new T(function(){return E(E(_aG).a);})),new T(function(){return E(E(_aG).b);}));}}},_aI=32,_aJ=new T(function(){return B(unCStr("\n"));}),_aK=function(_aL){return (E(_aL)==124)?false:true;},_aM=function(_aN,_aO){var _aP=B(_aB(_aK,B(unCStr(_aN)))),_aQ=_aP.a,_aR=function(_aS,_aT){var _aU=new T(function(){var _aV=new T(function(){return B(_q(_aO,new T(function(){return B(_q(_aT,_aJ));},1)));});return B(unAppCStr(": ",_aV));},1);return new F(function(){return _q(_aS,_aU);});},_aW=E(_aP.b);if(!_aW._){return new F(function(){return _aR(_aQ,_S);});}else{if(E(_aW.a)==124){return new F(function(){return _aR(_aQ,new T2(1,_aI,_aW.b));});}else{return new F(function(){return _aR(_aQ,_S);});}}},_aX=function(_aY){return new F(function(){return _az(new T1(0,new T(function(){return B(_aM(_aY,_av));})),_aj);});},_aZ=function(_b0){var _b1=function(_b2,_b3){while(1){if(!B(_9X(_b2,_b0))){if(!B(_9O(_b2,_b0))){if(!B(_9a(_b2,_b0))){return new F(function(){return _aX("GHC/Integer/Type.lhs:(555,5)-(557,32)|function l2");});}else{return E(_b3);}}else{return _b3-1|0;}}else{var _b4=B(_9E(_b2,1)),_b5=_b3+1|0;_b2=_b4;_b3=_b5;continue;}}};return new F(function(){return _b1(_9W,0);});},_b6=function(_b7){var _b8=E(_b7);if(!_b8._){var _b9=_b8.a>>>0;if(!_b9){return -1;}else{var _ba=function(_bb,_bc){while(1){if(_bb>=_b9){if(_bb<=_b9){if(_bb!=_b9){return new F(function(){return _aX("GHC/Integer/Type.lhs:(611,5)-(613,40)|function l2");});}else{return E(_bc);}}else{return _bc-1|0;}}else{var _bd=imul(_bb,2)>>>0,_be=_bc+1|0;_bb=_bd;_bc=_be;continue;}}};return new F(function(){return _ba(1,0);});}}else{return new F(function(){return _aZ(_b8);});}},_bf=function(_bg){var _bh=E(_bg);if(!_bh._){var _bi=_bh.a>>>0;if(!_bi){return new T2(0,-1,0);}else{var _bj=function(_bk,_bl){while(1){if(_bk>=_bi){if(_bk<=_bi){if(_bk!=_bi){return new F(function(){return _aX("GHC/Integer/Type.lhs:(611,5)-(613,40)|function l2");});}else{return E(_bl);}}else{return _bl-1|0;}}else{var _bm=imul(_bk,2)>>>0,_bn=_bl+1|0;_bk=_bm;_bl=_bn;continue;}}};return new T2(0,B(_bj(1,0)),(_bi&_bi-1>>>0)>>>0&4294967295);}}else{var _bo=_bh.a;return new T2(0,B(_b6(_bh)),I_compareInt(I_and(_bo,I_sub(_bo,I_fromInt(1))),0));}},_bp=function(_bq,_br){var _bs=E(_bq);if(!_bs._){var _bt=_bs.a,_bu=E(_br);return (_bu._==0)?_bt<=_bu.a:I_compareInt(_bu.a,_bt)>=0;}else{var _bv=_bs.a,_bw=E(_br);return (_bw._==0)?I_compareInt(_bv,_bw.a)<=0:I_compare(_bv,_bw.a)<=0;}},_bx=function(_by,_bz){while(1){var _bA=E(_by);if(!_bA._){var _bB=_bA.a,_bC=E(_bz);if(!_bC._){return new T1(0,(_bB>>>0&_bC.a>>>0)>>>0&4294967295);}else{_by=new T1(1,I_fromInt(_bB));_bz=_bC;continue;}}else{var _bD=E(_bz);if(!_bD._){_by=_bA;_bz=new T1(1,I_fromInt(_bD.a));continue;}else{return new T1(1,I_and(_bA.a,_bD.a));}}}},_bE=function(_bF,_bG){while(1){var _bH=E(_bF);if(!_bH._){var _bI=_bH.a,_bJ=E(_bG);if(!_bJ._){var _bK=_bJ.a,_bL=subC(_bI,_bK);if(!E(_bL.b)){return new T1(0,_bL.a);}else{_bF=new T1(1,I_fromInt(_bI));_bG=new T1(1,I_fromInt(_bK));continue;}}else{_bF=new T1(1,I_fromInt(_bI));_bG=_bJ;continue;}}else{var _bM=E(_bG);if(!_bM._){_bF=_bH;_bG=new T1(1,I_fromInt(_bM.a));continue;}else{return new T1(1,I_sub(_bH.a,_bM.a));}}}},_bN=new T1(0,2),_bO=function(_bP,_bQ){var _bR=E(_bP);if(!_bR._){var _bS=(_bR.a>>>0&(2<<_bQ>>>0)-1>>>0)>>>0,_bT=1<<_bQ>>>0;return (_bT<=_bS)?(_bT>=_bS)?1:2:0;}else{var _bU=B(_bx(_bR,B(_bE(B(_9E(_bN,_bQ)),_9W)))),_bV=B(_9E(_9W,_bQ));return (!B(_9O(_bV,_bU)))?(!B(_9X(_bV,_bU)))?1:2:0;}},_bW=function(_bX,_bY){while(1){var _bZ=E(_bX);if(!_bZ._){_bX=new T1(1,I_fromInt(_bZ.a));continue;}else{return new T1(1,I_shiftRight(_bZ.a,_bY));}}},_c0=function(_c1,_c2,_c3,_c4){var _c5=B(_bf(_c4)),_c6=_c5.a;if(!E(_c5.b)){var _c7=B(_b6(_c3));if(_c7<((_c6+_c1|0)-1|0)){var _c8=_c6+(_c1-_c2|0)|0;if(_c8>0){if(_c8>_c7){if(_c8<=(_c7+1|0)){if(!E(B(_bf(_c3)).b)){return 0;}else{return new F(function(){return _96(_8k,_c1-_c2|0);});}}else{return 0;}}else{var _c9=B(_bW(_c3,_c8));switch(B(_bO(_c3,_c8-1|0))){case 0:return new F(function(){return _96(_c9,_c1-_c2|0);});break;case 1:if(!(B(_9i(_c9))&1)){return new F(function(){return _96(_c9,_c1-_c2|0);});}else{return new F(function(){return _96(B(_9l(_c9,_8k)),_c1-_c2|0);});}break;default:return new F(function(){return _96(B(_9l(_c9,_8k)),_c1-_c2|0);});}}}else{return new F(function(){return _96(_c3,(_c1-_c2|0)-_c8|0);});}}else{if(_c7>=_c2){var _ca=B(_bW(_c3,(_c7+1|0)-_c2|0));switch(B(_bO(_c3,_c7-_c2|0))){case 0:return new F(function(){return _96(_ca,((_c7-_c6|0)+1|0)-_c2|0);});break;case 2:return new F(function(){return _96(B(_9l(_ca,_8k)),((_c7-_c6|0)+1|0)-_c2|0);});break;default:if(!(B(_9i(_ca))&1)){return new F(function(){return _96(_ca,((_c7-_c6|0)+1|0)-_c2|0);});}else{return new F(function(){return _96(B(_9l(_ca,_8k)),((_c7-_c6|0)+1|0)-_c2|0);});}}}else{return new F(function(){return _96(_c3, -_c6);});}}}else{var _cb=B(_b6(_c3))-_c6|0,_cc=function(_cd){var _ce=function(_cf,_cg){if(!B(_bp(B(_9E(_cg,_c2)),_cf))){return new F(function(){return _9I(_cd-_c2|0,_cf,_cg);});}else{return new F(function(){return _9I((_cd-_c2|0)+1|0,_cf,B(_9E(_cg,1)));});}};if(_cd>=_c2){if(_cd!=_c2){return new F(function(){return _ce(_c3,new T(function(){return B(_9E(_c4,_cd-_c2|0));}));});}else{return new F(function(){return _ce(_c3,_c4);});}}else{return new F(function(){return _ce(new T(function(){return B(_9E(_c3,_c2-_cd|0));}),_c4);});}};if(_c1>_cb){return new F(function(){return _cc(_c1);});}else{return new F(function(){return _cc(_cb);});}}},_ch=new T1(0,2147483647),_ci=new T(function(){return B(_9l(_ch,_9W));}),_cj=function(_ck){var _cl=E(_ck);if(!_cl._){var _cm=E(_cl.a);return (_cm==(-2147483648))?E(_ci):new T1(0, -_cm);}else{return new T1(1,I_negate(_cl.a));}},_cn=new T(function(){return 0/0;}),_co=new T(function(){return -1/0;}),_cp=new T(function(){return 1/0;}),_cq=0,_cr=function(_cs,_ct){if(!B(_9a(_ct,_9D))){if(!B(_9a(_cs,_9D))){if(!B(_9X(_cs,_9D))){return new F(function(){return _c0(-1021,53,_cs,_ct);});}else{return  -B(_c0(-1021,53,B(_cj(_cs)),_ct));}}else{return E(_cq);}}else{return (!B(_9a(_cs,_9D)))?(!B(_9X(_cs,_9D)))?E(_cp):E(_co):E(_cn);}},_cu=function(_cv){var _cw=E(_cv);return new F(function(){return _cr(_cw.a,_cw.b);});},_cx=function(_cy){return 1/E(_cy);},_cz=function(_cA){var _cB=E(_cA);return (_cB!=0)?(_cB<=0)? -_cB:E(_cB):E(_cq);},_cC=function(_cD){var _cE=E(_cD);if(!_cE._){return _cE.a;}else{return new F(function(){return I_toNumber(_cE.a);});}},_cF=function(_cG){return new F(function(){return _cC(_cG);});},_cH=1,_cI=-1,_cJ=function(_cK){var _cL=E(_cK);return (_cL<=0)?(_cL>=0)?E(_cL):E(_cI):E(_cH);},_cM=function(_cN,_cO){return E(_cN)-E(_cO);},_cP=function(_cQ){return  -E(_cQ);},_cR=function(_cS,_cT){return E(_cS)+E(_cT);},_cU=function(_cV,_cW){return E(_cV)*E(_cW);},_cX={_:0,a:_cR,b:_cM,c:_cU,d:_cP,e:_cz,f:_cJ,g:_cF},_cY=function(_cZ,_d0){return E(_cZ)/E(_d0);},_d1=new T4(0,_cX,_cY,_cx,_cu),_d2=function(_d3){return new F(function(){return Math.acos(E(_d3));});},_d4=function(_d5){return new F(function(){return Math.asin(E(_d5));});},_d6=function(_d7){return new F(function(){return Math.atan(E(_d7));});},_d8=function(_d9){return new F(function(){return Math.cos(E(_d9));});},_da=function(_db){return new F(function(){return cosh(E(_db));});},_dc=function(_dd){return new F(function(){return Math.exp(E(_dd));});},_de=function(_df){return new F(function(){return Math.log(E(_df));});},_dg=function(_dh,_di){return new F(function(){return Math.pow(E(_dh),E(_di));});},_dj=function(_dk){return new F(function(){return Math.sin(E(_dk));});},_dl=function(_dm){return new F(function(){return sinh(E(_dm));});},_dn=function(_do){return new F(function(){return Math.sqrt(E(_do));});},_dp=function(_dq){return new F(function(){return Math.tan(E(_dq));});},_dr=function(_ds){return new F(function(){return tanh(E(_ds));});},_dt={_:0,a:_d1,b:_8j,c:_dc,d:_de,e:_dn,f:_dg,g:_8g,h:_dj,i:_d8,j:_dp,k:_d4,l:_d2,m:_d6,n:_dl,o:_da,p:_dr,q:_8a,r:_87,s:_8d},_du=function(_dv,_dw){if(_dw<=0){var _dx=function(_dy){var _dz=function(_dA){var _dB=function(_dC){var _dD=function(_dE){var _dF=isDoubleNegativeZero(_dw),_dG=_dF,_dH=function(_dI){var _dJ=E(_dv);return (_dJ!=0)?_dw+_dJ:(_dw>=0)?(E(_dG)==0)?(_dw!=0)?_dw+_dJ:E(_dJ):3.141592653589793:3.141592653589793;};if(!E(_dG)){return new F(function(){return _dH(_);});}else{var _dK=E(_dv),_dL=isDoubleNegativeZero(_dK);if(!E(_dL)){return new F(function(){return _dH(_);});}else{return  -B(_du( -_dK,_dw));}}};if(_dw>=0){return new F(function(){return _dD(_);});}else{var _dM=E(_dv),_dN=isDoubleNegativeZero(_dM);if(!E(_dN)){return new F(function(){return _dD(_);});}else{return  -B(_du( -_dM,_dw));}}};if(_dw>0){return new F(function(){return _dB(_);});}else{var _dO=E(_dv);if(_dO>=0){return new F(function(){return _dB(_);});}else{return  -B(_du( -_dO,_dw));}}};if(_dw>=0){return new F(function(){return _dz(_);});}else{var _dP=E(_dv);if(_dP<=0){return new F(function(){return _dz(_);});}else{return 3.141592653589793+Math.atan(_dP/_dw);}}};if(_dw!=0){return new F(function(){return _dx(_);});}else{if(E(_dv)<=0){return new F(function(){return _dx(_);});}else{return 1.5707963267948966;}}}else{return new F(function(){return Math.atan(E(_dv)/_dw);});}},_dQ=function(_dR,_dS){return new F(function(){return _du(_dR,E(_dS));});},_dT=function(_dU){var _dV=I_decodeDouble(_dU);return new T2(0,new T1(1,_dV.b),_dV.a);},_dW=function(_dX){var _dY=B(_dT(E(_dX)));return new T2(0,_dY.a,_dY.b);},_dZ=function(_e0,_e1){return new F(function(){return _96(_e0,E(_e1));});},_e2=function(_e3){var _e4=B(_dT(_e3));return (!B(_9a(_e4.a,_9D)))?_e4.b+53|0:0;},_e5=function(_e6){return new F(function(){return _e2(E(_e6));});},_e7=53,_e8=function(_e9){return E(_e7);},_ea=new T1(0,2),_eb=function(_ec){return E(_ea);},_ed=1024,_ee=-1021,_ef=new T2(0,_ee,_ed),_eg=function(_eh){return E(_ef);},_ei=function(_ej){var _ek=isDoubleDenormalized(E(_ej));return (E(_ek)==0)?false:true;},_el=function(_em){return true;},_en=function(_eo){var _ep=isDoubleInfinite(E(_eo));return (E(_ep)==0)?false:true;},_eq=function(_er){var _es=isDoubleNaN(E(_er));return (E(_es)==0)?false:true;},_et=function(_eu){var _ev=isDoubleNegativeZero(E(_eu));return (E(_ev)==0)?false:true;},_ew=function(_ex,_ey){var _ez=E(_ex);if(!_ez){return E(_ey);}else{if(_ey!=0){var _eA=isDoubleFinite(_ey);if(!E(_eA)){return E(_ey);}else{var _eB=B(_dT(_ey)),_eC=_eB.a,_eD=_eB.b;if(2257>_ez){if(-2257>_ez){return new F(function(){return _96(_eC,_eD+(-2257)|0);});}else{return new F(function(){return _96(_eC,_eD+_ez|0);});}}else{return new F(function(){return _96(_eC,_eD+2257|0);});}}}else{return E(_ey);}}},_eE=function(_eF,_eG){return new F(function(){return _ew(E(_eF),E(_eG));});},_eH=function(_eI){return new F(function(){return _96(B(_dT(E(_eI))).a,-53);});},_eJ=function(_eK,_eL){return (E(_eK)!=E(_eL))?true:false;},_eM=function(_eN,_eO){return E(_eN)==E(_eO);},_eP=new T2(0,_eM,_eJ),_eQ=function(_eR,_eS){return E(_eR)<E(_eS);},_eT=function(_eU,_eV){return E(_eU)<=E(_eV);},_eW=function(_eX,_eY){return E(_eX)>E(_eY);},_eZ=function(_f0,_f1){return E(_f0)>=E(_f1);},_f2=function(_f3,_f4){var _f5=E(_f3),_f6=E(_f4);return (_f5>=_f6)?(_f5!=_f6)?2:1:0;},_f7=function(_f8,_f9){var _fa=E(_f8),_fb=E(_f9);return (_fa>_fb)?E(_fa):E(_fb);},_fc=function(_fd,_fe){var _ff=E(_fd),_fg=E(_fe);return (_ff>_fg)?E(_fg):E(_ff);},_fh={_:0,a:_eP,b:_f2,c:_eQ,d:_eT,e:_eW,f:_eZ,g:_f7,h:_fc},_fi=function(_fj){return new T1(0,_fj);},_fk=function(_fl){var _fm=hs_intToInt64(2147483647),_fn=hs_leInt64(_fl,_fm);if(!_fn){return new T1(1,I_fromInt64(_fl));}else{var _fo=hs_intToInt64(-2147483648),_fp=hs_geInt64(_fl,_fo);if(!_fp){return new T1(1,I_fromInt64(_fl));}else{var _fq=hs_int64ToInt(_fl);return new F(function(){return _fi(_fq);});}}},_fr=new T(function(){var _fs=newByteArr(256),_ft=_fs,_=_ft["v"]["i8"][0]=8,_fu=function(_fv,_fw,_fx,_){while(1){if(_fx>=256){if(_fv>=256){return E(_);}else{var _fy=imul(2,_fv)|0,_fz=_fw+1|0,_fA=_fv;_fv=_fy;_fw=_fz;_fx=_fA;continue;}}else{var _=_ft["v"]["i8"][_fx]=_fw,_fA=_fx+_fv|0;_fx=_fA;continue;}}},_=B(_fu(2,0,1,_));return _ft;}),_fB=function(_fC,_fD){var _fE=hs_int64ToInt(_fC),_fF=E(_fr),_fG=_fF["v"]["i8"][(255&_fE>>>0)>>>0&4294967295];if(_fD>_fG){if(_fG>=8){var _fH=hs_uncheckedIShiftRA64(_fC,8),_fI=function(_fJ,_fK){while(1){var _fL=B((function(_fM,_fN){var _fO=hs_int64ToInt(_fM),_fP=_fF["v"]["i8"][(255&_fO>>>0)>>>0&4294967295];if(_fN>_fP){if(_fP>=8){var _fQ=hs_uncheckedIShiftRA64(_fM,8),_fR=_fN-8|0;_fJ=_fQ;_fK=_fR;return __continue;}else{return new T2(0,new T(function(){var _fS=hs_uncheckedIShiftRA64(_fM,_fP);return B(_fk(_fS));}),_fN-_fP|0);}}else{return new T2(0,new T(function(){var _fT=hs_uncheckedIShiftRA64(_fM,_fN);return B(_fk(_fT));}),0);}})(_fJ,_fK));if(_fL!=__continue){return _fL;}}};return new F(function(){return _fI(_fH,_fD-8|0);});}else{return new T2(0,new T(function(){var _fU=hs_uncheckedIShiftRA64(_fC,_fG);return B(_fk(_fU));}),_fD-_fG|0);}}else{return new T2(0,new T(function(){var _fV=hs_uncheckedIShiftRA64(_fC,_fD);return B(_fk(_fV));}),0);}},_fW=function(_fX){var _fY=hs_intToInt64(_fX);return E(_fY);},_fZ=function(_g0){var _g1=E(_g0);if(!_g1._){return new F(function(){return _fW(_g1.a);});}else{return new F(function(){return I_toInt64(_g1.a);});}},_g2=function(_g3){return I_toInt(_g3)>>>0;},_g4=function(_g5){var _g6=E(_g5);if(!_g6._){return _g6.a>>>0;}else{return new F(function(){return _g2(_g6.a);});}},_g7=function(_g8){var _g9=B(_dT(_g8)),_ga=_g9.a,_gb=_g9.b;if(_gb<0){var _gc=function(_gd){if(!_gd){return new T2(0,E(_ga),B(_9E(_8k, -_gb)));}else{var _ge=B(_fB(B(_fZ(_ga)), -_gb));return new T2(0,E(_ge.a),B(_9E(_8k,_ge.b)));}};if(!((B(_g4(_ga))&1)>>>0)){return new F(function(){return _gc(1);});}else{return new F(function(){return _gc(0);});}}else{return new T2(0,B(_9E(_ga,_gb)),_8k);}},_gf=function(_gg){var _gh=B(_g7(E(_gg)));return new T2(0,E(_gh.a),E(_gh.b));},_gi=new T3(0,_cX,_fh,_gf),_gj=function(_gk){return E(E(_gk).a);},_gl=function(_gm){return E(E(_gm).a);},_gn=new T1(0,1),_go=function(_gp,_gq){if(_gp<=_gq){var _gr=function(_gs){return new T2(1,_gs,new T(function(){if(_gs!=_gq){return B(_gr(_gs+1|0));}else{return __Z;}}));};return new F(function(){return _gr(_gp);});}else{return __Z;}},_gt=function(_gu){return new F(function(){return _go(E(_gu),2147483647);});},_gv=function(_gw,_gx,_gy){if(_gy<=_gx){var _gz=new T(function(){var _gA=_gx-_gw|0,_gB=function(_gC){return (_gC>=(_gy-_gA|0))?new T2(1,_gC,new T(function(){return B(_gB(_gC+_gA|0));})):new T2(1,_gC,_S);};return B(_gB(_gx));});return new T2(1,_gw,_gz);}else{return (_gy<=_gw)?new T2(1,_gw,_S):__Z;}},_gD=function(_gE,_gF,_gG){if(_gG>=_gF){var _gH=new T(function(){var _gI=_gF-_gE|0,_gJ=function(_gK){return (_gK<=(_gG-_gI|0))?new T2(1,_gK,new T(function(){return B(_gJ(_gK+_gI|0));})):new T2(1,_gK,_S);};return B(_gJ(_gF));});return new T2(1,_gE,_gH);}else{return (_gG>=_gE)?new T2(1,_gE,_S):__Z;}},_gL=function(_gM,_gN){if(_gN<_gM){return new F(function(){return _gv(_gM,_gN,-2147483648);});}else{return new F(function(){return _gD(_gM,_gN,2147483647);});}},_gO=function(_gP,_gQ){return new F(function(){return _gL(E(_gP),E(_gQ));});},_gR=function(_gS,_gT,_gU){if(_gT<_gS){return new F(function(){return _gv(_gS,_gT,_gU);});}else{return new F(function(){return _gD(_gS,_gT,_gU);});}},_gV=function(_gW,_gX,_gY){return new F(function(){return _gR(E(_gW),E(_gX),E(_gY));});},_gZ=function(_h0,_h1){return new F(function(){return _go(E(_h0),E(_h1));});},_h2=function(_h3){return E(_h3);},_h4=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_h5=new T(function(){return B(err(_h4));}),_h6=function(_h7){var _h8=E(_h7);return (_h8==(-2147483648))?E(_h5):_h8-1|0;},_h9=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_ha=new T(function(){return B(err(_h9));}),_hb=function(_hc){var _hd=E(_hc);return (_hd==2147483647)?E(_ha):_hd+1|0;},_he={_:0,a:_hb,b:_h6,c:_h2,d:_h2,e:_gt,f:_gO,g:_gZ,h:_gV},_hf=function(_hg,_hh){if(_hg<=0){if(_hg>=0){return new F(function(){return quot(_hg,_hh);});}else{if(_hh<=0){return new F(function(){return quot(_hg,_hh);});}else{return quot(_hg+1|0,_hh)-1|0;}}}else{if(_hh>=0){if(_hg>=0){return new F(function(){return quot(_hg,_hh);});}else{if(_hh<=0){return new F(function(){return quot(_hg,_hh);});}else{return quot(_hg+1|0,_hh)-1|0;}}}else{return quot(_hg-1|0,_hh)-1|0;}}},_hi=0,_hj=new T(function(){return B(_91(_hi));}),_hk=new T(function(){return die(_hj);}),_hl=function(_hm,_hn){var _ho=E(_hn);switch(_ho){case -1:var _hp=E(_hm);if(_hp==(-2147483648)){return E(_hk);}else{return new F(function(){return _hf(_hp,-1);});}break;case 0:return E(_95);default:return new F(function(){return _hf(_hm,_ho);});}},_hq=function(_hr,_hs){return new F(function(){return _hl(E(_hr),E(_hs));});},_ht=0,_hu=new T2(0,_hk,_ht),_hv=function(_hw,_hx){var _hy=E(_hw),_hz=E(_hx);switch(_hz){case -1:var _hA=E(_hy);if(_hA==(-2147483648)){return E(_hu);}else{if(_hA<=0){if(_hA>=0){var _hB=quotRemI(_hA,-1);return new T2(0,_hB.a,_hB.b);}else{var _hC=quotRemI(_hA,-1);return new T2(0,_hC.a,_hC.b);}}else{var _hD=quotRemI(_hA-1|0,-1);return new T2(0,_hD.a-1|0,(_hD.b+(-1)|0)+1|0);}}break;case 0:return E(_95);default:if(_hy<=0){if(_hy>=0){var _hE=quotRemI(_hy,_hz);return new T2(0,_hE.a,_hE.b);}else{if(_hz<=0){var _hF=quotRemI(_hy,_hz);return new T2(0,_hF.a,_hF.b);}else{var _hG=quotRemI(_hy+1|0,_hz);return new T2(0,_hG.a-1|0,(_hG.b+_hz|0)-1|0);}}}else{if(_hz>=0){if(_hy>=0){var _hH=quotRemI(_hy,_hz);return new T2(0,_hH.a,_hH.b);}else{if(_hz<=0){var _hI=quotRemI(_hy,_hz);return new T2(0,_hI.a,_hI.b);}else{var _hJ=quotRemI(_hy+1|0,_hz);return new T2(0,_hJ.a-1|0,(_hJ.b+_hz|0)-1|0);}}}else{var _hK=quotRemI(_hy-1|0,_hz);return new T2(0,_hK.a-1|0,(_hK.b+_hz|0)+1|0);}}}},_hL=function(_hM,_hN){var _hO=_hM%_hN;if(_hM<=0){if(_hM>=0){return E(_hO);}else{if(_hN<=0){return E(_hO);}else{var _hP=E(_hO);return (_hP==0)?0:_hP+_hN|0;}}}else{if(_hN>=0){if(_hM>=0){return E(_hO);}else{if(_hN<=0){return E(_hO);}else{var _hQ=E(_hO);return (_hQ==0)?0:_hQ+_hN|0;}}}else{var _hR=E(_hO);return (_hR==0)?0:_hR+_hN|0;}}},_hS=function(_hT,_hU){var _hV=E(_hU);switch(_hV){case -1:return E(_ht);case 0:return E(_95);default:return new F(function(){return _hL(E(_hT),_hV);});}},_hW=function(_hX,_hY){var _hZ=E(_hX),_i0=E(_hY);switch(_i0){case -1:var _i1=E(_hZ);if(_i1==(-2147483648)){return E(_hk);}else{return new F(function(){return quot(_i1,-1);});}break;case 0:return E(_95);default:return new F(function(){return quot(_hZ,_i0);});}},_i2=function(_i3,_i4){var _i5=E(_i3),_i6=E(_i4);switch(_i6){case -1:var _i7=E(_i5);if(_i7==(-2147483648)){return E(_hu);}else{var _i8=quotRemI(_i7,-1);return new T2(0,_i8.a,_i8.b);}break;case 0:return E(_95);default:var _i9=quotRemI(_i5,_i6);return new T2(0,_i9.a,_i9.b);}},_ia=function(_ib,_ic){var _id=E(_ic);switch(_id){case -1:return E(_ht);case 0:return E(_95);default:return E(_ib)%_id;}},_ie=function(_if){return new F(function(){return _fi(E(_if));});},_ig=function(_ih){return new T2(0,E(B(_fi(E(_ih)))),E(_gn));},_ii=function(_ij,_ik){return imul(E(_ij),E(_ik))|0;},_il=function(_im,_in){return E(_im)+E(_in)|0;},_io=function(_ip,_iq){return E(_ip)-E(_iq)|0;},_ir=function(_is){var _it=E(_is);return (_it<0)? -_it:E(_it);},_iu=function(_iv){return new F(function(){return _9i(_iv);});},_iw=function(_ix){return  -E(_ix);},_iy=-1,_iz=0,_iA=1,_iB=function(_iC){var _iD=E(_iC);return (_iD>=0)?(E(_iD)==0)?E(_iz):E(_iA):E(_iy);},_iE={_:0,a:_il,b:_io,c:_ii,d:_iw,e:_ir,f:_iB,g:_iu},_iF=new T3(0,_iE,_6a,_ig),_iG={_:0,a:_iF,b:_he,c:_hW,d:_ia,e:_hq,f:_hS,g:_i2,h:_hv,i:_ie},_iH=function(_iI,_iJ){while(1){var _iK=E(_iI);if(!_iK._){var _iL=_iK.a,_iM=E(_iJ);if(!_iM._){var _iN=_iM.a;if(!(imul(_iL,_iN)|0)){return new T1(0,imul(_iL,_iN)|0);}else{_iI=new T1(1,I_fromInt(_iL));_iJ=new T1(1,I_fromInt(_iN));continue;}}else{_iI=new T1(1,I_fromInt(_iL));_iJ=_iM;continue;}}else{var _iO=E(_iJ);if(!_iO._){_iI=_iK;_iJ=new T1(1,I_fromInt(_iO.a));continue;}else{return new T1(1,I_mul(_iK.a,_iO.a));}}}},_iP=function(_iQ,_iR,_iS){while(1){if(!(_iR%2)){var _iT=B(_iH(_iQ,_iQ)),_iU=quot(_iR,2);_iQ=_iT;_iR=_iU;continue;}else{var _iV=E(_iR);if(_iV==1){return new F(function(){return _iH(_iQ,_iS);});}else{var _iT=B(_iH(_iQ,_iQ)),_iW=B(_iH(_iQ,_iS));_iQ=_iT;_iR=quot(_iV-1|0,2);_iS=_iW;continue;}}}},_iX=function(_iY,_iZ){while(1){if(!(_iZ%2)){var _j0=B(_iH(_iY,_iY)),_j1=quot(_iZ,2);_iY=_j0;_iZ=_j1;continue;}else{var _j2=E(_iZ);if(_j2==1){return E(_iY);}else{return new F(function(){return _iP(B(_iH(_iY,_iY)),quot(_j2-1|0,2),_iY);});}}}},_j3=function(_j4){return E(E(_j4).c);},_j5=function(_j6){return E(E(_j6).a);},_j7=function(_j8){return E(E(_j8).b);},_j9=function(_ja){return E(E(_ja).b);},_jb=function(_jc){return E(E(_jc).c);},_jd=function(_je){return E(E(_je).a);},_jf=new T1(0,0),_jg=new T1(0,2),_jh=function(_ji){return E(E(_ji).g);},_jj=function(_jk){return E(E(_jk).d);},_jl=function(_jm,_jn){var _jo=B(_gj(_jm)),_jp=new T(function(){return B(_gl(_jo));}),_jq=new T(function(){return B(A3(_jj,_jm,_jn,new T(function(){return B(A2(_jh,_jp,_jg));})));});return new F(function(){return A3(_jd,B(_j5(B(_j7(_jo)))),_jq,new T(function(){return B(A2(_jh,_jp,_jf));}));});},_jr=new T(function(){return B(unCStr("Negative exponent"));}),_js=new T(function(){return B(err(_jr));}),_jt=function(_ju){return E(E(_ju).c);},_jv=function(_jw,_jx,_jy,_jz){var _jA=B(_gj(_jx)),_jB=new T(function(){return B(_gl(_jA));}),_jC=B(_j7(_jA));if(!B(A3(_jb,_jC,_jz,new T(function(){return B(A2(_jh,_jB,_jf));})))){if(!B(A3(_jd,B(_j5(_jC)),_jz,new T(function(){return B(A2(_jh,_jB,_jf));})))){var _jD=new T(function(){return B(A2(_jh,_jB,_jg));}),_jE=new T(function(){return B(A2(_jh,_jB,_gn));}),_jF=B(_j5(_jC)),_jG=function(_jH,_jI,_jJ){while(1){var _jK=B((function(_jL,_jM,_jN){if(!B(_jl(_jx,_jM))){if(!B(A3(_jd,_jF,_jM,_jE))){var _jO=new T(function(){return B(A3(_jt,_jx,new T(function(){return B(A3(_j9,_jB,_jM,_jE));}),_jD));});_jH=new T(function(){return B(A3(_j3,_jw,_jL,_jL));});_jI=_jO;_jJ=new T(function(){return B(A3(_j3,_jw,_jL,_jN));});return __continue;}else{return new F(function(){return A3(_j3,_jw,_jL,_jN);});}}else{var _jP=_jN;_jH=new T(function(){return B(A3(_j3,_jw,_jL,_jL));});_jI=new T(function(){return B(A3(_jt,_jx,_jM,_jD));});_jJ=_jP;return __continue;}})(_jH,_jI,_jJ));if(_jK!=__continue){return _jK;}}},_jQ=function(_jR,_jS){while(1){var _jT=B((function(_jU,_jV){if(!B(_jl(_jx,_jV))){if(!B(A3(_jd,_jF,_jV,_jE))){var _jW=new T(function(){return B(A3(_jt,_jx,new T(function(){return B(A3(_j9,_jB,_jV,_jE));}),_jD));});return new F(function(){return _jG(new T(function(){return B(A3(_j3,_jw,_jU,_jU));}),_jW,_jU);});}else{return E(_jU);}}else{_jR=new T(function(){return B(A3(_j3,_jw,_jU,_jU));});_jS=new T(function(){return B(A3(_jt,_jx,_jV,_jD));});return __continue;}})(_jR,_jS));if(_jT!=__continue){return _jT;}}};return new F(function(){return _jQ(_jy,_jz);});}else{return new F(function(){return A2(_jh,_jw,_gn);});}}else{return E(_js);}},_jX=new T(function(){return B(err(_jr));}),_jY=function(_jZ,_k0){var _k1=B(_dT(_k0)),_k2=_k1.a,_k3=_k1.b,_k4=new T(function(){return B(_gl(new T(function(){return B(_gj(_jZ));})));});if(_k3<0){var _k5= -_k3;if(_k5>=0){var _k6=E(_k5);if(!_k6){var _k7=E(_gn);}else{var _k7=B(_iX(_ea,_k6));}if(!B(_9a(_k7,_9D))){var _k8=B(_9u(_k2,_k7));return new T2(0,new T(function(){return B(A2(_jh,_k4,_k8.a));}),new T(function(){return B(_96(_k8.b,_k3));}));}else{return E(_95);}}else{return E(_jX);}}else{var _k9=new T(function(){var _ka=new T(function(){return B(_jv(_k4,_iG,new T(function(){return B(A2(_jh,_k4,_ea));}),_k3));});return B(A3(_j3,_k4,new T(function(){return B(A2(_jh,_k4,_k2));}),_ka));});return new T2(0,_k9,_cq);}},_kb=function(_kc){return E(E(_kc).a);},_kd=function(_ke,_kf){var _kg=B(_jY(_ke,E(_kf))),_kh=_kg.a;if(E(_kg.b)<=0){return E(_kh);}else{var _ki=B(_gl(B(_gj(_ke))));return new F(function(){return A3(_kb,_ki,_kh,new T(function(){return B(A2(_jh,_ki,_8k));}));});}},_kj=function(_kk,_kl){var _km=B(_jY(_kk,E(_kl))),_kn=_km.a;if(E(_km.b)>=0){return E(_kn);}else{var _ko=B(_gl(B(_gj(_kk))));return new F(function(){return A3(_j9,_ko,_kn,new T(function(){return B(A2(_jh,_ko,_8k));}));});}},_kp=function(_kq,_kr){var _ks=B(_jY(_kq,E(_kr)));return new T2(0,_ks.a,_ks.b);},_kt=function(_ku,_kv){var _kw=B(_jY(_ku,_kv)),_kx=_kw.a,_ky=E(_kw.b),_kz=new T(function(){var _kA=B(_gl(B(_gj(_ku))));if(_ky>=0){return B(A3(_kb,_kA,_kx,new T(function(){return B(A2(_jh,_kA,_8k));})));}else{return B(A3(_j9,_kA,_kx,new T(function(){return B(A2(_jh,_kA,_8k));})));}}),_kB=function(_kC){var _kD=_kC-0.5;return (_kD>=0)?(_kD!=0)?E(_kz):(!B(_jl(_ku,_kx)))?E(_kz):E(_kx):E(_kx);};if(_ky!=0){if(_ky<=0){var _kE= -_ky-0.5;return (_kE>=0)?(_kE!=0)?E(_kz):(!B(_jl(_ku,_kx)))?E(_kz):E(_kx):E(_kx);}else{return new F(function(){return _kB(_ky);});}}else{return new F(function(){return _kB(0);});}},_kF=function(_kG,_kH){return new F(function(){return _kt(_kG,E(_kH));});},_kI=function(_kJ,_kK){return E(B(_jY(_kJ,E(_kK))).a);},_kL={_:0,a:_gi,b:_d1,c:_kp,d:_kI,e:_kF,f:_kd,g:_kj},_kM={_:0,a:_kL,b:_dt,c:_eb,d:_e8,e:_eg,f:_dW,g:_dZ,h:_e5,i:_eH,j:_eE,k:_eq,l:_en,m:_ei,n:_et,o:_el,p:_dQ},_kN=0,_kO=1,_kP=2,_kQ=false,_kR=true,_kS=function(_kT){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_A(9,_kT,_S));}))));});},_kU=1,_kV=function(_kW){return new F(function(){return err(B(unAppCStr("Char.intToDigit: not a digit ",new T(function(){if(_kW>=0){var _kX=jsShowI(_kW);return fromJSStr(_kX);}else{var _kY=jsShowI(_kW);return fromJSStr(_kY);}}))));});},_kZ=function(_l0){var _l1=function(_l2){if(_l0<10){return new F(function(){return _kV(_l0);});}else{if(_l0>15){return new F(function(){return _kV(_l0);});}else{return (97+_l0|0)-10|0;}}};if(_l0<0){return new F(function(){return _l1(_);});}else{if(_l0>9){return new F(function(){return _l1(_);});}else{return 48+_l0|0;}}},_l3=function(_l4){return new F(function(){return _kZ(E(_l4));});},_l5=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_l6=function(_l7){return new F(function(){return _az(new T1(0,new T(function(){return B(_aM(_l7,_l5));})),_aj);});},_l8=new T(function(){return B(_l6("GHC/Float.hs:624:11-64|d : ds\'"));}),_l9=function(_la,_lb){var _lc=E(_lb);return (_lc._==0)?__Z:new T2(1,new T(function(){return B(A1(_la,_lc.a));}),new T(function(){return B(_l9(_la,_lc.b));}));},_ld=0,_le=function(_lf,_lg){if(E(_lf)<=0){var _lh=B(_l9(_l3,new T2(1,_ld,_lg)));return (_lh._==0)?E(_l8):new T2(0,_lh.a,_lh.b);}else{var _li=B(_l9(_l3,_lg));return (_li._==0)?E(_l8):new T2(0,_li.a,_li.b);}},_lj=function(_lk){return E(E(_lk).a);},_ll=function(_lm){return E(E(_lm).a);},_ln=function(_lo){return E(E(_lo).a);},_lp=function(_lq){return E(E(_lq).a);},_lr=function(_ls){return E(E(_ls).b);},_lt=46,_lu=48,_lv=new T(function(){return B(unCStr("0"));}),_lw=function(_lx,_ly){while(1){var _lz=E(_lx);if(!_lz._){return E(_ly);}else{var _lA=new T2(1,_lz.a,_ly);_lx=_lz.b;_ly=_lA;continue;}}},_lB=function(_lC,_lD,_lE){while(1){var _lF=B((function(_lG,_lH,_lI){var _lJ=E(_lG);if(!_lJ){var _lK=B(_lw(_lH,_S));if(!_lK._){return new F(function(){return _q(_lv,new T2(1,_lt,new T(function(){var _lL=E(_lI);if(!_lL._){return E(_lv);}else{return E(_lL);}})));});}else{return new F(function(){return _q(_lK,new T2(1,_lt,new T(function(){var _lM=E(_lI);if(!_lM._){return E(_lv);}else{return E(_lM);}})));});}}else{var _lN=E(_lI);if(!_lN._){var _lO=new T2(1,_lu,_lH);_lC=_lJ-1|0;_lD=_lO;_lE=_S;return __continue;}else{var _lO=new T2(1,_lN.a,_lH);_lC=_lJ-1|0;_lD=_lO;_lE=_lN.b;return __continue;}}})(_lC,_lD,_lE));if(_lF!=__continue){return _lF;}}},_lP=function(_lQ){return new F(function(){return _A(0,E(_lQ),_S);});},_lR=function(_lS,_lT,_lU){return new F(function(){return _A(E(_lS),E(_lT),_lU);});},_lV=function(_lW,_lX){return new F(function(){return _A(0,E(_lW),_lX);});},_lY=function(_lZ,_m0){return new F(function(){return _2v(_lV,_lZ,_m0);});},_m1=new T3(0,_lR,_lP,_lY),_m2=0,_m3=function(_m4,_m5,_m6){return new F(function(){return A1(_m4,new T2(1,_2s,new T(function(){return B(A1(_m5,_m6));})));});},_m7=new T(function(){return B(unCStr(": empty list"));}),_m8=function(_m9){return new F(function(){return err(B(_q(_6i,new T(function(){return B(_q(_m9,_m7));},1))));});},_ma=new T(function(){return B(unCStr("foldr1"));}),_mb=new T(function(){return B(_m8(_ma));}),_mc=function(_md,_me){var _mf=E(_me);if(!_mf._){return E(_mb);}else{var _mg=_mf.a,_mh=E(_mf.b);if(!_mh._){return E(_mg);}else{return new F(function(){return A2(_md,_mg,new T(function(){return B(_mc(_md,_mh));}));});}}},_mi=new T(function(){return B(unCStr(" out of range "));}),_mj=new T(function(){return B(unCStr("}.index: Index "));}),_mk=new T(function(){return B(unCStr("Ix{"));}),_ml=new T2(1,_y,_S),_mm=new T2(1,_y,_ml),_mn=0,_mo=function(_mp){return E(E(_mp).a);},_mq=function(_mr,_ms,_mt,_mu,_mv){var _mw=new T(function(){var _mx=new T(function(){var _my=new T(function(){var _mz=new T(function(){var _mA=new T(function(){return B(A3(_mc,_m3,new T2(1,new T(function(){return B(A3(_mo,_mt,_mn,_mu));}),new T2(1,new T(function(){return B(A3(_mo,_mt,_mn,_mv));}),_S)),_mm));});return B(_q(_mi,new T2(1,_z,new T2(1,_z,_mA))));});return B(A(_mo,[_mt,_m2,_ms,new T2(1,_y,_mz)]));});return B(_q(_mj,new T2(1,_z,_my)));},1);return B(_q(_mr,_mx));},1);return new F(function(){return err(B(_q(_mk,_mw)));});},_mB=function(_mC,_mD,_mE,_mF,_mG){return new F(function(){return _mq(_mC,_mD,_mG,_mE,_mF);});},_mH=function(_mI,_mJ,_mK,_mL){var _mM=E(_mK);return new F(function(){return _mB(_mI,_mJ,_mM.a,_mM.b,_mL);});},_mN=function(_mO,_mP,_mQ,_mR){return new F(function(){return _mH(_mR,_mQ,_mP,_mO);});},_mS=new T(function(){return B(unCStr("Int"));}),_mT=function(_mU,_mV,_mW){return new F(function(){return _mN(_m1,new T2(0,_mV,_mW),_mU,_mS);});},_mX=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_mY=new T(function(){return B(err(_mX));}),_mZ=1100,_n0=new T2(0,_ld,_mZ),_n1=function(_n2){return new F(function(){return _mN(_m1,_n0,_n2,_mS);});},_n3=function(_){var _n4=newArr(1101,_mY),_n5=_n4,_n6=function(_n7,_){while(1){var _n8=B((function(_n9,_){if(0>_n9){return new F(function(){return _n1(_n9);});}else{if(_n9>1100){return new F(function(){return _n1(_n9);});}else{var _=_n5[_n9]=new T(function(){if(_n9>=0){var _na=E(_n9);if(!_na){return E(_gn);}else{return B(_iX(_ea,_na));}}else{return E(_jX);}}),_nb=E(_n9);if(_nb==1100){return new T4(0,E(_ld),E(_mZ),1101,_n5);}else{_n7=_nb+1|0;return __continue;}}}})(_n7,_));if(_n8!=__continue){return _n8;}}};return new F(function(){return _n6(0,_);});},_nc=function(_nd){var _ne=B(A1(_nd,_));return E(_ne);},_nf=new T(function(){return B(_nc(_n3));}),_ng=new T1(0,10),_nh=324,_ni=new T2(0,_ld,_nh),_nj=function(_nk){return new F(function(){return _mN(_m1,_ni,_nk,_mS);});},_nl=function(_){var _nm=newArr(325,_mY),_nn=_nm,_no=function(_np,_){while(1){var _nq=B((function(_nr,_){if(0>_nr){return new F(function(){return _nj(_nr);});}else{if(_nr>324){return new F(function(){return _nj(_nr);});}else{var _=_nn[_nr]=new T(function(){if(_nr>=0){var _ns=E(_nr);if(!_ns){return E(_gn);}else{return B(_iX(_ng,_ns));}}else{return E(_jX);}}),_nt=E(_nr);if(_nt==324){return new T4(0,E(_ld),E(_nh),325,_nn);}else{_np=_nt+1|0;return __continue;}}}})(_np,_));if(_nq!=__continue){return _nq;}}};return new F(function(){return _no(0,_);});},_nu=new T(function(){return B(_nc(_nl));}),_nv=function(_nw,_nx){var _ny=function(_nz){if(!B(_9a(_nw,_ng))){if(_nx>=0){var _nA=E(_nx);if(!_nA){return E(_gn);}else{return new F(function(){return _iX(_nw,_nA);});}}else{return E(_jX);}}else{if(_nx>324){if(_nx>=0){var _nB=E(_nx);if(!_nB){return E(_gn);}else{return new F(function(){return _iX(_nw,_nB);});}}else{return E(_jX);}}else{var _nC=E(_nu),_nD=E(_nC.a),_nE=E(_nC.b);if(_nD>_nx){return new F(function(){return _mT(_nx,_nD,_nE);});}else{if(_nx>_nE){return new F(function(){return _mT(_nx,_nD,_nE);});}else{return E(_nC.d[_nx-_nD|0]);}}}}};if(!B(_9a(_nw,_ea))){return new F(function(){return _ny(_);});}else{if(_nx<0){return new F(function(){return _ny(_);});}else{if(_nx>1100){return new F(function(){return _ny(_);});}else{var _nF=E(_nf),_nG=E(_nF.a),_nH=E(_nF.b);if(_nG>_nx){return new F(function(){return _mT(_nx,_nG,_nH);});}else{if(_nx>_nH){return new F(function(){return _mT(_nx,_nG,_nH);});}else{return E(_nF.d[_nx-_nG|0]);}}}}}},_nI=function(_nJ){return E(E(_nJ).f);},_nK=function(_nL){return E(E(_nL).d);},_nM=function(_nN){var _nO=E(_nN);if(!_nO._){return _nO.a;}else{return new F(function(){return I_toNumber(_nO.a);});}},_nP=function(_nQ){return E(E(_nQ).c);},_nR=function(_nS){return E(E(_nS).e);},_nT=new T2(1,_ld,_S),_nU=function(_nV,_nW){while(1){var _nX=E(_nV);if(!_nX._){var _nY=E(_nX.a);if(_nY==(-2147483648)){_nV=new T1(1,I_fromInt(-2147483648));continue;}else{var _nZ=E(_nW);if(!_nZ._){return new T1(0,quot(_nY,_nZ.a));}else{_nV=new T1(1,I_fromInt(_nY));_nW=_nZ;continue;}}}else{var _o0=_nX.a,_o1=E(_nW);return (_o1._==0)?new T1(0,I_toInt(I_quot(_o0,I_fromInt(_o1.a)))):new T1(1,I_quot(_o0,_o1.a));}}},_o2=function(_o3,_o4,_o5){if(!B(A3(_jd,B(_j5(B(_j7(B(_lp(B(_ln(_o3)))))))),_o5,new T(function(){return B(A2(_jh,B(_ll(B(_lj(B(_lr(_o3)))))),_9D));})))){var _o6=new T(function(){return B(A2(_nP,_o3,_o5));}),_o7=new T(function(){return B(A2(_nK,_o3,_o5));}),_o8=new T(function(){return E(B(A2(_nR,_o3,_o5)).a)-E(_o7)|0;}),_o9=new T(function(){return B(A2(_nI,_o3,_o5));}),_oa=new T(function(){return E(E(_o9).b);}),_ob=new T(function(){var _oc=E(_oa),_od=E(_o8)-_oc|0;if(_od<=0){return new T2(0,new T(function(){return E(E(_o9).a);}),_oc);}else{return new T2(0,new T(function(){var _oe=B(_nv(_o6,_od));if(!B(_9a(_oe,_9D))){return B(_nU(E(_o9).a,_oe));}else{return E(_95);}}),_oc+_od|0);}}),_of=new T(function(){return E(E(_ob).b);}),_og=new T(function(){return E(E(_ob).a);}),_oh=new T(function(){var _oi=E(_of);if(_oi<0){if(_oi<=E(_o8)){return new T4(0,new T(function(){return B(_iH(_og,_ea));}),new T(function(){return B(_iH(B(_nv(_o6, -_oi)),_ea));}),_8k,_8k);}else{if(!B(_9a(_og,B(_nv(_o6,E(_o7)-1|0))))){return new T4(0,new T(function(){return B(_iH(_og,_ea));}),new T(function(){return B(_iH(B(_nv(_o6, -_oi)),_ea));}),_8k,_8k);}else{return new T4(0,new T(function(){return B(_iH(B(_iH(_og,_o6)),_ea));}),new T(function(){return B(_iH(B(_nv(_o6, -_oi+1|0)),_ea));}),_o6,_8k);}}}else{var _oj=new T(function(){return B(_nv(_o6,_oi));});if(!B(_9a(_og,B(_nv(_o6,E(_o7)-1|0))))){return new T4(0,new T(function(){return B(_iH(B(_iH(_og,_oj)),_ea));}),_ea,_oj,_oj);}else{return new T4(0,new T(function(){return B(_iH(B(_iH(B(_iH(_og,_oj)),_o6)),_ea));}),new T(function(){return B(_iH(_ea,_o6));}),new T(function(){return B(_iH(_oj,_o6));}),_oj);}}}),_ok=new T(function(){return E(E(_oh).b);}),_ol=new T(function(){return E(E(_oh).c);}),_om=new T(function(){return E(E(_oh).a);}),_on=new T(function(){var _oo=new T(function(){return B(_9l(_om,_ol));}),_op=function(_oq){var _or=(Math.log(B(_nM(B(_9l(_og,_8k)))))+E(_of)*Math.log(B(_nM(_o6))))/Math.log(B(_nM(_o4))),_os=_or&4294967295;return (_os>=_or)?E(_os):_os+1|0;},_ot=function(_ou){while(1){if(_ou<0){if(!B(_bp(B(_iH(B(_nv(_o4, -_ou)),_oo)),_ok))){var _ov=_ou+1|0;_ou=_ov;continue;}else{return E(_ou);}}else{if(!B(_bp(_oo,B(_iH(B(_nv(_o4,_ou)),_ok))))){var _ov=_ou+1|0;_ou=_ov;continue;}else{return E(_ou);}}}};if(!B(_9a(_o6,_ea))){return B(_ot(B(_op(_))));}else{if(!B(_9a(_o4,_ng))){return B(_ot(B(_op(_))));}else{var _ow=(E(_o7)-1|0)+E(_oa)|0;if(_ow<0){return B(_ot(quot(imul(_ow,8651)|0,28738)));}else{return B(_ot(quot(imul(_ow,8651)|0,28738)+1|0));}}}}),_ox=new T(function(){var _oy=E(_on),_oz=function(_oA,_oB,_oC,_oD,_oE){while(1){var _oF=B((function(_oG,_oH,_oI,_oJ,_oK){if(!B(_9a(_oI,_9D))){var _oL=B(_9u(B(_iH(_oH,_o4)),_oI)),_oM=_oL.a,_oN=_oL.b,_oO=B(_iH(_oK,_o4)),_oP=B(_iH(_oJ,_o4));if(!B(_9X(_oN,_oO))){if(!B(_9O(B(_9l(_oN,_oP)),_oI))){var _oQ=new T2(1,_oM,_oG),_oR=_oI;_oA=_oQ;_oB=_oN;_oC=_oR;_oD=_oP;_oE=_oO;return __continue;}else{return new T2(1,new T(function(){return B(_9l(_oM,_8k));}),_oG);}}else{return (!B(_9O(B(_9l(_oN,_oP)),_oI)))?new T2(1,_oM,_oG):(!B(_9X(B(_iH(_oN,_ea)),_oI)))?new T2(1,new T(function(){return B(_9l(_oM,_8k));}),_oG):new T2(1,_oM,_oG);}}else{return E(_95);}})(_oA,_oB,_oC,_oD,_oE));if(_oF!=__continue){return _oF;}}};if(_oy<0){var _oS=B(_nv(_o4, -_oy));return B(_l9(_iu,B(_lw(B(_oz(_S,B(_iH(_om,_oS)),_ok,B(_iH(_ol,_oS)),B(_iH(E(_oh).d,_oS)))),_S))));}else{return B(_l9(_iu,B(_lw(B(_oz(_S,_om,B(_iH(_ok,B(_nv(_o4,_oy)))),_ol,E(_oh).d)),_S))));}});return new T2(0,_ox,_on);}else{return new T2(0,_nT,_ld);}},_oT=function(_oU){var _oV=E(_oU);return (_oV==1)?E(_nT):new T2(1,_ld,new T(function(){return B(_oT(_oV-1|0));}));},_oW=function(_oX,_oY){while(1){var _oZ=E(_oY);if(!_oZ._){return true;}else{if(!B(A1(_oX,_oZ.a))){return false;}else{_oY=_oZ.b;continue;}}}},_p0=function(_p1){return (E(_p1)%2==0)?true:false;},_p2=new T(function(){return B(unCStr("roundTo: bad Value"));}),_p3=new T(function(){return B(err(_p2));}),_p4=function(_p5){return (E(_p5)==0)?true:false;},_p6=function(_p7,_p8,_p9){var _pa=new T(function(){return quot(E(_p7),2);}),_pb=function(_pc,_pd,_pe){var _pf=E(_pe);if(!_pf._){return new T2(0,_ld,new T(function(){var _pg=E(_pc);if(0>=_pg){return __Z;}else{return B(_oT(_pg));}}));}else{var _ph=_pf.a,_pi=_pf.b,_pj=E(_pc);if(!_pj){var _pk=E(_ph),_pl=E(_pa);return (_pk!=_pl)?new T2(0,new T(function(){if(_pk<_pl){return E(_ld);}else{return E(_kU);}}),_S):(!E(_pd))?new T2(0,new T(function(){if(_pk<_pl){return E(_ld);}else{return E(_kU);}}),_S):(!B(_oW(_p4,_pi)))?new T2(0,new T(function(){if(_pk<_pl){return E(_ld);}else{return E(_kU);}}),_S):new T2(0,_ld,_S);}else{var _pm=B(_pb(_pj-1|0,new T(function(){return B(_p0(_ph));},1),_pi)),_pn=_pm.b,_po=E(_pm.a)+E(_ph)|0;return (_po!=E(_p7))?new T2(0,_ld,new T2(1,_po,_pn)):new T2(0,_kU,new T2(1,_ld,_pn));}}},_pp=B(_pb(_p8,_kR,_p9)),_pq=_pp.a,_pr=_pp.b;switch(E(_pq)){case 0:return new T2(0,_pq,_pr);case 1:return new T2(0,_kU,new T2(1,_kU,_pr));default:return E(_p3);}},_ps=function(_pt,_pu){var _pv=E(_pu);if(!_pv._){return new T2(0,_S,_S);}else{var _pw=_pv.a,_px=_pv.b,_py=E(_pt);if(_py==1){return new T2(0,new T2(1,_pw,_S),_px);}else{var _pz=new T(function(){var _pA=B(_ps(_py-1|0,_px));return new T2(0,_pA.a,_pA.b);});return new T2(0,new T2(1,_pw,new T(function(){return E(E(_pz).a);})),new T(function(){return E(E(_pz).b);}));}}},_pB=new T(function(){return B(unCStr("e0"));}),_pC=new T2(1,_lu,_pB),_pD=function(_pE){var _pF=E(_pE);return (_pF==1)?E(_pC):new T2(1,_lu,new T(function(){return B(_pD(_pF-1|0));}));},_pG=10,_pH=function(_pI,_pJ){var _pK=E(_pJ);return (_pK._==0)?__Z:new T2(1,_pI,new T(function(){return B(_pH(_pK.a,_pK.b));}));},_pL=new T(function(){return B(unCStr("init"));}),_pM=new T(function(){return B(_m8(_pL));}),_pN=function(_pO){return E(E(_pO).l);},_pP=function(_pQ){return E(E(_pQ).k);},_pR=function(_pS){return E(E(_pS).n);},_pT=new T(function(){return B(unCStr("NaN"));}),_pU=new T(function(){return B(unCStr("-Infinity"));}),_pV=new T(function(){return B(unCStr("formatRealFloat/doFmt/FFExponent: []"));}),_pW=new T(function(){return B(err(_pV));}),_pX=new T(function(){return B(unCStr("Infinity"));}),_pY=new T2(1,_lt,_S),_pZ=101,_q0=new T(function(){return B(_l6("GHC/Float.hs:596:12-70|(d : ds\')"));}),_q1=new T(function(){return B(unCStr("0.0e0"));}),_q2=function(_q3){return E(E(_q3).d);},_q4=45,_q5=function(_q6,_q7,_q8,_q9,_qa){if(!B(A2(_pP,_q6,_qa))){var _qb=new T(function(){return B(_ll(new T(function(){return B(_lj(new T(function(){return B(_lr(_q6));})));})));});if(!B(A2(_pN,_q6,_qa))){var _qc=function(_qd,_qe,_qf){while(1){var _qg=B((function(_qh,_qi,_qj){switch(E(_qh)){case 0:var _qk=E(_q8);if(!_qk._){var _ql=B(_l9(_l3,_qi));if(!_ql._){return E(_pW);}else{var _qm=_ql.b,_qn=E(_ql.a),_qo=function(_qp){var _qq=E(_qm);if(!_qq._){var _qr=new T(function(){return B(unAppCStr(".0e",new T(function(){return B(_A(0,E(_qj)-1|0,_S));})));});return new T2(1,_qn,_qr);}else{var _qs=new T(function(){var _qt=new T(function(){return B(unAppCStr("e",new T(function(){return B(_A(0,E(_qj)-1|0,_S));})));},1);return B(_q(_qq,_qt));});return new T2(1,_qn,new T2(1,_lt,_qs));}};if(E(_qn)==48){if(!E(_qm)._){return E(_q1);}else{return new F(function(){return _qo(_);});}}else{return new F(function(){return _qo(_);});}}}else{var _qu=new T(function(){var _qv=E(_qk.a);if(_qv>1){return E(_qv);}else{return E(_kU);}}),_qw=function(_qx){var _qy=new T(function(){var _qz=B(_p6(_pG,new T(function(){return E(_qu)+1|0;},1),_qi));return new T2(0,_qz.a,_qz.b);}),_qA=new T(function(){return E(E(_qy).a);}),_qB=new T(function(){if(E(_qA)<=0){var _qC=B(_l9(_l3,E(_qy).b));if(!_qC._){return E(_q0);}else{return new T2(0,_qC.a,_qC.b);}}else{var _qD=E(E(_qy).b);if(!_qD._){return E(_pM);}else{var _qE=B(_l9(_l3,B(_pH(_qD.a,_qD.b))));if(!_qE._){return E(_q0);}else{return new T2(0,_qE.a,_qE.b);}}}}),_qF=new T(function(){return B(_q(E(_qB).b,new T2(1,_pZ,new T(function(){return B(_A(0,(E(_qj)-1|0)+E(_qA)|0,_S));}))));});return new T2(1,new T(function(){return E(E(_qB).a);}),new T2(1,_lt,_qF));},_qG=E(_qi);if(!_qG._){return new F(function(){return _qw(_);});}else{if(!E(_qG.a)){if(!E(_qG.b)._){return new T2(1,_lu,new T2(1,_lt,new T(function(){var _qH=E(_qu);if(0>=_qH){return E(_pB);}else{return B(_pD(_qH));}})));}else{return new F(function(){return _qw(_);});}}else{return new F(function(){return _qw(_);});}}}break;case 1:var _qI=E(_q8);if(!_qI._){var _qJ=E(_qj);if(_qJ>0){return new F(function(){return _lB(_qJ,_S,new T(function(){return B(_l9(_l3,_qi));},1));});}else{var _qK=new T(function(){var _qL= -_qJ;if(0>=_qL){return B(_l9(_l3,_qi));}else{var _qM=new T(function(){return B(_l9(_l3,_qi));}),_qN=function(_qO){var _qP=E(_qO);return (_qP==1)?E(new T2(1,_lu,_qM)):new T2(1,_lu,new T(function(){return B(_qN(_qP-1|0));}));};return B(_qN(_qL));}});return new F(function(){return unAppCStr("0.",_qK);});}}else{var _qQ=_qI.a,_qR=E(_qj);if(_qR<0){var _qS=new T(function(){var _qT= -_qR;if(0>=_qT){var _qU=B(_p6(_pG,new T(function(){var _qV=E(_qQ);if(_qV>0){return E(_qV);}else{return E(_ld);}},1),_qi));return B(_le(_qU.a,_qU.b));}else{var _qW=function(_qX){var _qY=E(_qX);return (_qY==1)?E(new T2(1,_ld,_qi)):new T2(1,_ld,new T(function(){return B(_qW(_qY-1|0));}));},_qZ=B(_p6(_pG,new T(function(){var _r0=E(_qQ);if(_r0>0){return E(_r0);}else{return E(_ld);}},1),B(_qW(_qT))));return B(_le(_qZ.a,_qZ.b));}});return new T2(1,new T(function(){return E(E(_qS).a);}),new T(function(){var _r1=E(E(_qS).b);if(!_r1._){if(!E(_q9)){return __Z;}else{return E(_pY);}}else{return new T2(1,_lt,_r1);}}));}else{var _r2=B(_p6(_pG,new T(function(){var _r3=E(_qQ);if(_r3>0){return _r3+_qR|0;}else{return E(_qR);}},1),_qi)),_r4=_r2.b,_r5=_qR+E(_r2.a)|0;if(_r5>0){var _r6=B(_ps(_r5,B(_l9(_l3,_r4)))),_r7=_r6.b,_r8=E(_r6.a);if(!_r8._){return new F(function(){return _q(_lv,new T(function(){var _r9=E(_r7);if(!_r9._){if(!E(_q9)){return __Z;}else{return E(_pY);}}else{return new T2(1,_lt,_r9);}},1));});}else{return new F(function(){return _q(_r8,new T(function(){var _ra=E(_r7);if(!_ra._){if(!E(_q9)){return __Z;}else{return E(_pY);}}else{return new T2(1,_lt,_ra);}},1));});}}else{return new F(function(){return _q(_lv,new T(function(){var _rb=B(_l9(_l3,_r4));if(!_rb._){if(!E(_q9)){return __Z;}else{return E(_pY);}}else{return new T2(1,_lt,_rb);}},1));});}}}break;default:var _rc=E(_qj);if(_rc>=0){if(_rc<=7){var _rd=_qi;_qd=_kO;_qe=_rd;_qf=_rc;return __continue;}else{var _rd=_qi;_qd=_kN;_qe=_rd;_qf=_rc;return __continue;}}else{var _rd=_qi;_qd=_kN;_qe=_rd;_qf=_rc;return __continue;}}})(_qd,_qe,_qf));if(_qg!=__continue){return _qg;}}},_re=function(_rf){var _rg=new T(function(){var _rh=B(_o2(_q6,_ng,new T(function(){return B(A2(_q2,_qb,_qa));})));return B(_qc(_q7,_rh.a,_rh.b));});return new T2(1,_q4,_rg);};if(!B(A3(_jb,B(_j7(B(_lp(B(_ln(_q6)))))),_qa,new T(function(){return B(A2(_jh,_qb,_9D));})))){if(!B(A2(_pR,_q6,_qa))){var _ri=B(_o2(_q6,_ng,_qa));return new F(function(){return _qc(_q7,_ri.a,_ri.b);});}else{return new F(function(){return _re(_);});}}else{return new F(function(){return _re(_);});}}else{return (!B(A3(_jb,B(_j7(B(_lp(B(_ln(_q6)))))),_qa,new T(function(){return B(A2(_jh,_qb,_9D));}))))?E(_pX):E(_pU);}}else{return E(_pT);}},_rj=function(_rk){var _rl=u_towupper(E(_rk));if(_rl>>>0>1114111){return new F(function(){return _kS(_rl);});}else{return _rl;}},_rm=function(_rn,_ro,_rp,_rq){var _rr=u_iswupper(_rn),_rs=_rr,_rt=u_towlower(_rn);if(_rt>>>0>1114111){var _ru=B(_kS(_rt));}else{switch(_rt){case 101:var _rv=B(_q5(_kM,_kN,_ro,_kQ,_rq));break;case 102:if(!E(_rp)){var _rw=B(_q5(_kM,_kO,_ro,_kQ,_rq));}else{var _rw=B(_q5(_kM,_kO,_ro,_kR,_rq));}var _rv=_rw;break;case 103:if(!E(_rp)){var _rx=B(_q5(_kM,_kP,_ro,_kQ,_rq));}else{var _rx=B(_q5(_kM,_kP,_ro,_kR,_rq));}var _rv=_rx;break;default:var _rv=E(_86);}var _ru=_rv;}if(!E(_rs)){var _ry=E(_ru);return (_ry._==0)?new T2(0,_S,_S):(E(_ry.a)==45)?new T2(0,_84,_ry.b):new T2(0,_S,_ry);}else{var _rz=B(_l9(_rj,_ru));return (_rz._==0)?new T2(0,_S,_S):(E(_rz.a)==45)?new T2(0,_84,_rz.b):new T2(0,_S,_rz);}},_rA=new T(function(){return B(unCStr(" "));}),_rB=new T(function(){return B(unCStr("+"));}),_rC=48,_rD=32,_rE=function(_rF,_rG){while(1){var _rH=E(_rF);if(!_rH._){return E(_rG);}else{var _rI=_rG+1|0;_rF=_rH.b;_rG=_rI;continue;}}},_rJ=function(_rK,_rL,_rM,_rN){var _rO=new T(function(){var _rP=E(_rL);if(!_rP._){return false;}else{if(!E(_rP.a)){return false;}else{return true;}}}),_rQ=new T(function(){var _rR=E(_rK);if(!_rR._){return __Z;}else{var _rS=E(_rR.a),_rT=B(_rE(_rM,0))+B(_rE(_rN,0))|0;if(_rT>=_rS){return __Z;}else{var _rU=_rS-_rT|0;if(0>=_rU){return __Z;}else{var _rV=new T(function(){if(!E(_rO)){return E(_rD);}else{return E(_rC);}}),_rW=function(_rX){var _rY=E(_rX);return (_rY==1)?E(new T2(1,_rV,_S)):new T2(1,_rV,new T(function(){return B(_rW(_rY-1|0));}));};return B(_rW(_rU));}}}}),_rZ=function(_s0){if(!E(_rO)){return new F(function(){return _q(_rQ,new T(function(){return B(_q(_rM,_rN));},1));});}else{return new F(function(){return _q(_rM,new T(function(){return B(_q(_rQ,_rN));},1));});}},_s1=E(_rL);if(!_s1._){return new F(function(){return _rZ(_);});}else{if(!E(_s1.a)){return new F(function(){return _q(_rM,new T(function(){return B(_q(_rN,_rQ));},1));});}else{return new F(function(){return _rZ(_);});}}},_s2=function(_s3,_s4,_s5,_s6,_s7){var _s8=E(_s5);if(!_s8._){return new F(function(){return _rJ(_s3,_s4,_s6,_s7);});}else{if(!E(_s8.a)){var _s9=E(_s6);if(!_s9._){return new F(function(){return _rJ(_s3,_s4,_rB,_s7);});}else{return new F(function(){return _rJ(_s3,_s4,_s9,_s7);});}}else{var _sa=E(_s6);if(!_sa._){return new F(function(){return _rJ(_s3,_s4,_rA,_s7);});}else{return new F(function(){return _rJ(_s3,_s4,_sa,_s7);});}}}},_sb=function(_sc,_sd,_se,_sf,_sg,_sh,_si){var _sj=E(_si);switch(_sj){case 69:var _sk=new T(function(){var _sl=B(_rm(69,_se,_sh,_sc));return B(_s2(_sd,_sf,_sg,_sl.a,_sl.b));});return function(_sm){return new F(function(){return _q(_sk,_sm);});};case 70:var _sn=new T(function(){var _so=B(_rm(70,_se,_sh,_sc));return B(_s2(_sd,_sf,_sg,_so.a,_so.b));});return function(_sm){return new F(function(){return _q(_sn,_sm);});};case 71:var _sp=new T(function(){var _sq=B(_rm(71,_se,_sh,_sc));return B(_s2(_sd,_sf,_sg,_sq.a,_sq.b));});return function(_sm){return new F(function(){return _q(_sp,_sm);});};case 101:var _sr=new T(function(){var _ss=B(_rm(101,_se,_sh,_sc));return B(_s2(_sd,_sf,_sg,_ss.a,_ss.b));});return function(_sm){return new F(function(){return _q(_sr,_sm);});};case 102:var _st=new T(function(){var _su=B(_rm(102,_se,_sh,_sc));return B(_s2(_sd,_sf,_sg,_su.a,_su.b));});return function(_sm){return new F(function(){return _q(_st,_sm);});};case 103:var _sv=new T(function(){var _sw=B(_rm(103,_se,_sh,_sc));return B(_s2(_sd,_sf,_sg,_sw.a,_sw.b));});return function(_sm){return new F(function(){return _q(_sv,_sm);});};case 118:var _sx=new T(function(){var _sy=B(_rm(103,_se,_sh,_sc));return B(_s2(_sd,_sf,_sg,_sy.a,_sy.b));});return function(_sm){return new F(function(){return _q(_sx,_sm);});};default:return new F(function(){return _7Z(_sj);});}},_sz=function(_sA,_sB){var _sC=E(_sB);return new F(function(){return _sb(_sA,_sC.a,_sC.b,_sC.c,_sC.d,_sC.e,E(_sC.g));});},_sD=new T(function(){return B(unCStr("%.2f"));}),_sE=function(_sF){return E(_sF);},_sG=new T(function(){return B(unCStr("printf: argument list ended prematurely"));}),_sH=new T(function(){return B(err(_sG));}),_sI=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_sJ=new T(function(){return B(err(_sI));}),_sK=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_sL=new T(function(){return B(err(_sK));}),_sM=new T(function(){return B(_aX("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_sN=function(_sO,_sP){while(1){var _sQ=B((function(_sR,_sS){var _sT=E(_sR);switch(_sT._){case 0:var _sU=E(_sS);if(!_sU._){return __Z;}else{_sO=B(A1(_sT.a,_sU.a));_sP=_sU.b;return __continue;}break;case 1:var _sV=B(A1(_sT.a,_sS)),_sW=_sS;_sO=_sV;_sP=_sW;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_sT.a,_sS),new T(function(){return B(_sN(_sT.b,_sS));}));default:return E(_sT.a);}})(_sO,_sP));if(_sQ!=__continue){return _sQ;}}},_sX=function(_sY,_sZ){var _t0=function(_t1){var _t2=E(_sZ);if(_t2._==3){return new T2(3,_t2.a,new T(function(){return B(_sX(_sY,_t2.b));}));}else{var _t3=E(_sY);if(_t3._==2){return E(_t2);}else{var _t4=E(_t2);if(_t4._==2){return E(_t3);}else{var _t5=function(_t6){var _t7=E(_t4);if(_t7._==4){var _t8=function(_t9){return new T1(4,new T(function(){return B(_q(B(_sN(_t3,_t9)),_t7.a));}));};return new T1(1,_t8);}else{var _ta=E(_t3);if(_ta._==1){var _tb=_ta.a,_tc=E(_t7);if(!_tc._){return new T1(1,function(_td){return new F(function(){return _sX(B(A1(_tb,_td)),_tc);});});}else{var _te=function(_tf){return new F(function(){return _sX(B(A1(_tb,_tf)),new T(function(){return B(A1(_tc.a,_tf));}));});};return new T1(1,_te);}}else{var _tg=E(_t7);if(!_tg._){return E(_sM);}else{var _th=function(_ti){return new F(function(){return _sX(_ta,new T(function(){return B(A1(_tg.a,_ti));}));});};return new T1(1,_th);}}}},_tj=E(_t3);switch(_tj._){case 1:var _tk=E(_t4);if(_tk._==4){var _tl=function(_tm){return new T1(4,new T(function(){return B(_q(B(_sN(B(A1(_tj.a,_tm)),_tm)),_tk.a));}));};return new T1(1,_tl);}else{return new F(function(){return _t5(_);});}break;case 4:var _tn=_tj.a,_to=E(_t4);switch(_to._){case 0:var _tp=function(_tq){var _tr=new T(function(){return B(_q(_tn,new T(function(){return B(_sN(_to,_tq));},1)));});return new T1(4,_tr);};return new T1(1,_tp);case 1:var _ts=function(_tt){var _tu=new T(function(){return B(_q(_tn,new T(function(){return B(_sN(B(A1(_to.a,_tt)),_tt));},1)));});return new T1(4,_tu);};return new T1(1,_ts);default:return new T1(4,new T(function(){return B(_q(_tn,_to.a));}));}break;default:return new F(function(){return _t5(_);});}}}}},_tv=E(_sY);switch(_tv._){case 0:var _tw=E(_sZ);if(!_tw._){var _tx=function(_ty){return new F(function(){return _sX(B(A1(_tv.a,_ty)),new T(function(){return B(A1(_tw.a,_ty));}));});};return new T1(0,_tx);}else{return new F(function(){return _t0(_);});}break;case 3:return new T2(3,_tv.a,new T(function(){return B(_sX(_tv.b,_sZ));}));default:return new F(function(){return _t0(_);});}},_tz=new T(function(){return B(unCStr("("));}),_tA=new T(function(){return B(unCStr(")"));}),_tB=function(_tC,_tD){while(1){var _tE=E(_tC);if(!_tE._){return (E(_tD)._==0)?true:false;}else{var _tF=E(_tD);if(!_tF._){return false;}else{if(E(_tE.a)!=E(_tF.a)){return false;}else{_tC=_tE.b;_tD=_tF.b;continue;}}}}},_tG=function(_tH,_tI){return E(_tH)!=E(_tI);},_tJ=function(_tK,_tL){return E(_tK)==E(_tL);},_tM=new T2(0,_tJ,_tG),_tN=function(_tO,_tP){while(1){var _tQ=E(_tO);if(!_tQ._){return (E(_tP)._==0)?true:false;}else{var _tR=E(_tP);if(!_tR._){return false;}else{if(E(_tQ.a)!=E(_tR.a)){return false;}else{_tO=_tQ.b;_tP=_tR.b;continue;}}}}},_tS=function(_tT,_tU){return (!B(_tN(_tT,_tU)))?true:false;},_tV=new T2(0,_tN,_tS),_tW=function(_tX,_tY){var _tZ=E(_tX);switch(_tZ._){case 0:return new T1(0,function(_u0){return new F(function(){return _tW(B(A1(_tZ.a,_u0)),_tY);});});case 1:return new T1(1,function(_u1){return new F(function(){return _tW(B(A1(_tZ.a,_u1)),_tY);});});case 2:return new T0(2);case 3:return new F(function(){return _sX(B(A1(_tY,_tZ.a)),new T(function(){return B(_tW(_tZ.b,_tY));}));});break;default:var _u2=function(_u3){var _u4=E(_u3);if(!_u4._){return __Z;}else{var _u5=E(_u4.a);return new F(function(){return _q(B(_sN(B(A1(_tY,_u5.a)),_u5.b)),new T(function(){return B(_u2(_u4.b));},1));});}},_u6=B(_u2(_tZ.a));return (_u6._==0)?new T0(2):new T1(4,_u6);}},_u7=new T0(2),_u8=function(_u9){return new T2(3,_u9,_u7);},_ua=function(_ub,_uc){var _ud=E(_ub);if(!_ud){return new F(function(){return A1(_uc,_4s);});}else{var _ue=new T(function(){return B(_ua(_ud-1|0,_uc));});return new T1(0,function(_uf){return E(_ue);});}},_ug=function(_uh,_ui,_uj){var _uk=new T(function(){return B(A1(_uh,_u8));}),_ul=function(_um,_un,_uo,_up){while(1){var _uq=B((function(_ur,_us,_ut,_uu){var _uv=E(_ur);switch(_uv._){case 0:var _uw=E(_us);if(!_uw._){return new F(function(){return A1(_ui,_uu);});}else{var _ux=_ut+1|0,_uy=_uu;_um=B(A1(_uv.a,_uw.a));_un=_uw.b;_uo=_ux;_up=_uy;return __continue;}break;case 1:var _uz=B(A1(_uv.a,_us)),_uA=_us,_ux=_ut,_uy=_uu;_um=_uz;_un=_uA;_uo=_ux;_up=_uy;return __continue;case 2:return new F(function(){return A1(_ui,_uu);});break;case 3:var _uB=new T(function(){return B(_tW(_uv,_uu));});return new F(function(){return _ua(_ut,function(_uC){return E(_uB);});});break;default:return new F(function(){return _tW(_uv,_uu);});}})(_um,_un,_uo,_up));if(_uq!=__continue){return _uq;}}};return function(_uD){return new F(function(){return _ul(_uk,_uD,0,_uj);});};},_uE=function(_uF){return new F(function(){return A1(_uF,_S);});},_uG=function(_uH,_uI){var _uJ=function(_uK){var _uL=E(_uK);if(!_uL._){return E(_uE);}else{var _uM=_uL.a;if(!B(A1(_uH,_uM))){return E(_uE);}else{var _uN=new T(function(){return B(_uJ(_uL.b));}),_uO=function(_uP){var _uQ=new T(function(){return B(A1(_uN,function(_uR){return new F(function(){return A1(_uP,new T2(1,_uM,_uR));});}));});return new T1(0,function(_uS){return E(_uQ);});};return E(_uO);}}};return function(_uT){return new F(function(){return A2(_uJ,_uT,_uI);});};},_uU=new T0(6),_uV=new T(function(){return B(unCStr("valDig: Bad base"));}),_uW=new T(function(){return B(err(_uV));}),_uX=function(_uY,_uZ){var _v0=function(_v1,_v2){var _v3=E(_v1);if(!_v3._){var _v4=new T(function(){return B(A1(_v2,_S));});return function(_v5){return new F(function(){return A1(_v5,_v4);});};}else{var _v6=E(_v3.a),_v7=function(_v8){var _v9=new T(function(){return B(_v0(_v3.b,function(_va){return new F(function(){return A1(_v2,new T2(1,_v8,_va));});}));}),_vb=function(_vc){var _vd=new T(function(){return B(A1(_v9,_vc));});return new T1(0,function(_ve){return E(_vd);});};return E(_vb);};switch(E(_uY)){case 8:if(48>_v6){var _vf=new T(function(){return B(A1(_v2,_S));});return function(_vg){return new F(function(){return A1(_vg,_vf);});};}else{if(_v6>55){var _vh=new T(function(){return B(A1(_v2,_S));});return function(_vi){return new F(function(){return A1(_vi,_vh);});};}else{return new F(function(){return _v7(_v6-48|0);});}}break;case 10:if(48>_v6){var _vj=new T(function(){return B(A1(_v2,_S));});return function(_vk){return new F(function(){return A1(_vk,_vj);});};}else{if(_v6>57){var _vl=new T(function(){return B(A1(_v2,_S));});return function(_vm){return new F(function(){return A1(_vm,_vl);});};}else{return new F(function(){return _v7(_v6-48|0);});}}break;case 16:if(48>_v6){if(97>_v6){if(65>_v6){var _vn=new T(function(){return B(A1(_v2,_S));});return function(_vo){return new F(function(){return A1(_vo,_vn);});};}else{if(_v6>70){var _vp=new T(function(){return B(A1(_v2,_S));});return function(_vq){return new F(function(){return A1(_vq,_vp);});};}else{return new F(function(){return _v7((_v6-65|0)+10|0);});}}}else{if(_v6>102){if(65>_v6){var _vr=new T(function(){return B(A1(_v2,_S));});return function(_vs){return new F(function(){return A1(_vs,_vr);});};}else{if(_v6>70){var _vt=new T(function(){return B(A1(_v2,_S));});return function(_vu){return new F(function(){return A1(_vu,_vt);});};}else{return new F(function(){return _v7((_v6-65|0)+10|0);});}}}else{return new F(function(){return _v7((_v6-97|0)+10|0);});}}}else{if(_v6>57){if(97>_v6){if(65>_v6){var _vv=new T(function(){return B(A1(_v2,_S));});return function(_vw){return new F(function(){return A1(_vw,_vv);});};}else{if(_v6>70){var _vx=new T(function(){return B(A1(_v2,_S));});return function(_vy){return new F(function(){return A1(_vy,_vx);});};}else{return new F(function(){return _v7((_v6-65|0)+10|0);});}}}else{if(_v6>102){if(65>_v6){var _vz=new T(function(){return B(A1(_v2,_S));});return function(_vA){return new F(function(){return A1(_vA,_vz);});};}else{if(_v6>70){var _vB=new T(function(){return B(A1(_v2,_S));});return function(_vC){return new F(function(){return A1(_vC,_vB);});};}else{return new F(function(){return _v7((_v6-65|0)+10|0);});}}}else{return new F(function(){return _v7((_v6-97|0)+10|0);});}}}else{return new F(function(){return _v7(_v6-48|0);});}}break;default:return E(_uW);}}},_vD=function(_vE){var _vF=E(_vE);if(!_vF._){return new T0(2);}else{return new F(function(){return A1(_uZ,_vF);});}};return function(_vG){return new F(function(){return A3(_v0,_vG,_3G,_vD);});};},_vH=16,_vI=8,_vJ=function(_vK){var _vL=function(_vM){return new F(function(){return A1(_vK,new T1(5,new T2(0,_vI,_vM)));});},_vN=function(_vO){return new F(function(){return A1(_vK,new T1(5,new T2(0,_vH,_vO)));});},_vP=function(_vQ){switch(E(_vQ)){case 79:return new T1(1,B(_uX(_vI,_vL)));case 88:return new T1(1,B(_uX(_vH,_vN)));case 111:return new T1(1,B(_uX(_vI,_vL)));case 120:return new T1(1,B(_uX(_vH,_vN)));default:return new T0(2);}};return function(_vR){return (E(_vR)==48)?E(new T1(0,_vP)):new T0(2);};},_vS=function(_vT){return new T1(0,B(_vJ(_vT)));},_vU=function(_vV){return new F(function(){return A1(_vV,_2N);});},_vW=function(_vX){return new F(function(){return A1(_vX,_2N);});},_vY=10,_vZ=new T1(0,10),_w0=function(_w1){return new F(function(){return _fi(E(_w1));});},_w2=new T(function(){return B(unCStr("this should not happen"));}),_w3=new T(function(){return B(err(_w2));}),_w4=function(_w5,_w6){var _w7=E(_w6);if(!_w7._){return __Z;}else{var _w8=E(_w7.b);return (_w8._==0)?E(_w3):new T2(1,B(_9l(B(_iH(_w7.a,_w5)),_w8.a)),new T(function(){return B(_w4(_w5,_w8.b));}));}},_w9=new T1(0,0),_wa=function(_wb,_wc,_wd){while(1){var _we=B((function(_wf,_wg,_wh){var _wi=E(_wh);if(!_wi._){return E(_w9);}else{if(!E(_wi.b)._){return E(_wi.a);}else{var _wj=E(_wg);if(_wj<=40){var _wk=function(_wl,_wm){while(1){var _wn=E(_wm);if(!_wn._){return E(_wl);}else{var _wo=B(_9l(B(_iH(_wl,_wf)),_wn.a));_wl=_wo;_wm=_wn.b;continue;}}};return new F(function(){return _wk(_w9,_wi);});}else{var _wp=B(_iH(_wf,_wf));if(!(_wj%2)){var _wq=B(_w4(_wf,_wi));_wb=_wp;_wc=quot(_wj+1|0,2);_wd=_wq;return __continue;}else{var _wq=B(_w4(_wf,new T2(1,_w9,_wi)));_wb=_wp;_wc=quot(_wj+1|0,2);_wd=_wq;return __continue;}}}}})(_wb,_wc,_wd));if(_we!=__continue){return _we;}}},_wr=function(_ws,_wt){return new F(function(){return _wa(_ws,new T(function(){return B(_rE(_wt,0));},1),B(_l9(_w0,_wt)));});},_wu=function(_wv){var _ww=new T(function(){var _wx=new T(function(){var _wy=function(_wz){return new F(function(){return A1(_wv,new T1(1,new T(function(){return B(_wr(_vZ,_wz));})));});};return new T1(1,B(_uX(_vY,_wy)));}),_wA=function(_wB){if(E(_wB)==43){var _wC=function(_wD){return new F(function(){return A1(_wv,new T1(1,new T(function(){return B(_wr(_vZ,_wD));})));});};return new T1(1,B(_uX(_vY,_wC)));}else{return new T0(2);}},_wE=function(_wF){if(E(_wF)==45){var _wG=function(_wH){return new F(function(){return A1(_wv,new T1(1,new T(function(){return B(_cj(B(_wr(_vZ,_wH))));})));});};return new T1(1,B(_uX(_vY,_wG)));}else{return new T0(2);}};return B(_sX(B(_sX(new T1(0,_wE),new T1(0,_wA))),_wx));});return new F(function(){return _sX(new T1(0,function(_wI){return (E(_wI)==101)?E(_ww):new T0(2);}),new T1(0,function(_wJ){return (E(_wJ)==69)?E(_ww):new T0(2);}));});},_wK=function(_wL){var _wM=function(_wN){return new F(function(){return A1(_wL,new T1(1,_wN));});};return function(_wO){return (E(_wO)==46)?new T1(1,B(_uX(_vY,_wM))):new T0(2);};},_wP=function(_wQ){return new T1(0,B(_wK(_wQ)));},_wR=function(_wS){var _wT=function(_wU){var _wV=function(_wW){return new T1(1,B(_ug(_wu,_vU,function(_wX){return new F(function(){return A1(_wS,new T1(5,new T3(1,_wU,_wW,_wX)));});})));};return new T1(1,B(_ug(_wP,_vW,_wV)));};return new F(function(){return _uX(_vY,_wT);});},_wY=function(_wZ){return new T1(1,B(_wR(_wZ)));},_x0=function(_x1,_x2,_x3){while(1){var _x4=E(_x3);if(!_x4._){return false;}else{if(!B(A3(_jd,_x1,_x2,_x4.a))){_x3=_x4.b;continue;}else{return true;}}}},_x5=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_x6=function(_x7){return new F(function(){return _x0(_tM,_x7,_x5);});},_x8=function(_x9){var _xa=new T(function(){return B(A1(_x9,_vI));}),_xb=new T(function(){return B(A1(_x9,_vH));});return function(_xc){switch(E(_xc)){case 79:return E(_xa);case 88:return E(_xb);case 111:return E(_xa);case 120:return E(_xb);default:return new T0(2);}};},_xd=function(_xe){return new T1(0,B(_x8(_xe)));},_xf=function(_xg){return new F(function(){return A1(_xg,_vY);});},_xh=function(_xi){return new T0(2);},_xj=function(_xk){var _xl=E(_xk);if(!_xl._){return E(_xh);}else{var _xm=_xl.a,_xn=E(_xl.b);if(!_xn._){return E(_xm);}else{var _xo=new T(function(){return B(_xj(_xn));}),_xp=function(_xq){return new F(function(){return _sX(B(A1(_xm,_xq)),new T(function(){return B(A1(_xo,_xq));}));});};return E(_xp);}}},_xr=function(_xs,_xt){var _xu=function(_xv,_xw,_xx){var _xy=E(_xv);if(!_xy._){return new F(function(){return A1(_xx,_xs);});}else{var _xz=E(_xw);if(!_xz._){return new T0(2);}else{if(E(_xy.a)!=E(_xz.a)){return new T0(2);}else{var _xA=new T(function(){return B(_xu(_xy.b,_xz.b,_xx));});return new T1(0,function(_xB){return E(_xA);});}}}};return function(_xC){return new F(function(){return _xu(_xs,_xC,_xt);});};},_xD=new T(function(){return B(unCStr("SO"));}),_xE=14,_xF=function(_xG){var _xH=new T(function(){return B(A1(_xG,_xE));});return new T1(1,B(_xr(_xD,function(_xI){return E(_xH);})));},_xJ=new T(function(){return B(unCStr("SOH"));}),_xK=1,_xL=function(_xM){var _xN=new T(function(){return B(A1(_xM,_xK));});return new T1(1,B(_xr(_xJ,function(_xO){return E(_xN);})));},_xP=function(_xQ){return new T1(1,B(_ug(_xL,_xF,_xQ)));},_xR=new T(function(){return B(unCStr("NUL"));}),_xS=0,_xT=function(_xU){var _xV=new T(function(){return B(A1(_xU,_xS));});return new T1(1,B(_xr(_xR,function(_xW){return E(_xV);})));},_xX=new T(function(){return B(unCStr("STX"));}),_xY=2,_xZ=function(_y0){var _y1=new T(function(){return B(A1(_y0,_xY));});return new T1(1,B(_xr(_xX,function(_y2){return E(_y1);})));},_y3=new T(function(){return B(unCStr("ETX"));}),_y4=3,_y5=function(_y6){var _y7=new T(function(){return B(A1(_y6,_y4));});return new T1(1,B(_xr(_y3,function(_y8){return E(_y7);})));},_y9=new T(function(){return B(unCStr("EOT"));}),_ya=4,_yb=function(_yc){var _yd=new T(function(){return B(A1(_yc,_ya));});return new T1(1,B(_xr(_y9,function(_ye){return E(_yd);})));},_yf=new T(function(){return B(unCStr("ENQ"));}),_yg=5,_yh=function(_yi){var _yj=new T(function(){return B(A1(_yi,_yg));});return new T1(1,B(_xr(_yf,function(_yk){return E(_yj);})));},_yl=new T(function(){return B(unCStr("ACK"));}),_ym=6,_yn=function(_yo){var _yp=new T(function(){return B(A1(_yo,_ym));});return new T1(1,B(_xr(_yl,function(_yq){return E(_yp);})));},_yr=new T(function(){return B(unCStr("BEL"));}),_ys=7,_yt=function(_yu){var _yv=new T(function(){return B(A1(_yu,_ys));});return new T1(1,B(_xr(_yr,function(_yw){return E(_yv);})));},_yx=new T(function(){return B(unCStr("BS"));}),_yy=8,_yz=function(_yA){var _yB=new T(function(){return B(A1(_yA,_yy));});return new T1(1,B(_xr(_yx,function(_yC){return E(_yB);})));},_yD=new T(function(){return B(unCStr("HT"));}),_yE=9,_yF=function(_yG){var _yH=new T(function(){return B(A1(_yG,_yE));});return new T1(1,B(_xr(_yD,function(_yI){return E(_yH);})));},_yJ=new T(function(){return B(unCStr("LF"));}),_yK=10,_yL=function(_yM){var _yN=new T(function(){return B(A1(_yM,_yK));});return new T1(1,B(_xr(_yJ,function(_yO){return E(_yN);})));},_yP=new T(function(){return B(unCStr("VT"));}),_yQ=11,_yR=function(_yS){var _yT=new T(function(){return B(A1(_yS,_yQ));});return new T1(1,B(_xr(_yP,function(_yU){return E(_yT);})));},_yV=new T(function(){return B(unCStr("FF"));}),_yW=12,_yX=function(_yY){var _yZ=new T(function(){return B(A1(_yY,_yW));});return new T1(1,B(_xr(_yV,function(_z0){return E(_yZ);})));},_z1=new T(function(){return B(unCStr("CR"));}),_z2=13,_z3=function(_z4){var _z5=new T(function(){return B(A1(_z4,_z2));});return new T1(1,B(_xr(_z1,function(_z6){return E(_z5);})));},_z7=new T(function(){return B(unCStr("SI"));}),_z8=15,_z9=function(_za){var _zb=new T(function(){return B(A1(_za,_z8));});return new T1(1,B(_xr(_z7,function(_zc){return E(_zb);})));},_zd=new T(function(){return B(unCStr("DLE"));}),_ze=16,_zf=function(_zg){var _zh=new T(function(){return B(A1(_zg,_ze));});return new T1(1,B(_xr(_zd,function(_zi){return E(_zh);})));},_zj=new T(function(){return B(unCStr("DC1"));}),_zk=17,_zl=function(_zm){var _zn=new T(function(){return B(A1(_zm,_zk));});return new T1(1,B(_xr(_zj,function(_zo){return E(_zn);})));},_zp=new T(function(){return B(unCStr("DC2"));}),_zq=18,_zr=function(_zs){var _zt=new T(function(){return B(A1(_zs,_zq));});return new T1(1,B(_xr(_zp,function(_zu){return E(_zt);})));},_zv=new T(function(){return B(unCStr("DC3"));}),_zw=19,_zx=function(_zy){var _zz=new T(function(){return B(A1(_zy,_zw));});return new T1(1,B(_xr(_zv,function(_zA){return E(_zz);})));},_zB=new T(function(){return B(unCStr("DC4"));}),_zC=20,_zD=function(_zE){var _zF=new T(function(){return B(A1(_zE,_zC));});return new T1(1,B(_xr(_zB,function(_zG){return E(_zF);})));},_zH=new T(function(){return B(unCStr("NAK"));}),_zI=21,_zJ=function(_zK){var _zL=new T(function(){return B(A1(_zK,_zI));});return new T1(1,B(_xr(_zH,function(_zM){return E(_zL);})));},_zN=new T(function(){return B(unCStr("SYN"));}),_zO=22,_zP=function(_zQ){var _zR=new T(function(){return B(A1(_zQ,_zO));});return new T1(1,B(_xr(_zN,function(_zS){return E(_zR);})));},_zT=new T(function(){return B(unCStr("ETB"));}),_zU=23,_zV=function(_zW){var _zX=new T(function(){return B(A1(_zW,_zU));});return new T1(1,B(_xr(_zT,function(_zY){return E(_zX);})));},_zZ=new T(function(){return B(unCStr("CAN"));}),_A0=24,_A1=function(_A2){var _A3=new T(function(){return B(A1(_A2,_A0));});return new T1(1,B(_xr(_zZ,function(_A4){return E(_A3);})));},_A5=new T(function(){return B(unCStr("EM"));}),_A6=25,_A7=function(_A8){var _A9=new T(function(){return B(A1(_A8,_A6));});return new T1(1,B(_xr(_A5,function(_Aa){return E(_A9);})));},_Ab=new T(function(){return B(unCStr("SUB"));}),_Ac=26,_Ad=function(_Ae){var _Af=new T(function(){return B(A1(_Ae,_Ac));});return new T1(1,B(_xr(_Ab,function(_Ag){return E(_Af);})));},_Ah=new T(function(){return B(unCStr("ESC"));}),_Ai=27,_Aj=function(_Ak){var _Al=new T(function(){return B(A1(_Ak,_Ai));});return new T1(1,B(_xr(_Ah,function(_Am){return E(_Al);})));},_An=new T(function(){return B(unCStr("FS"));}),_Ao=28,_Ap=function(_Aq){var _Ar=new T(function(){return B(A1(_Aq,_Ao));});return new T1(1,B(_xr(_An,function(_As){return E(_Ar);})));},_At=new T(function(){return B(unCStr("GS"));}),_Au=29,_Av=function(_Aw){var _Ax=new T(function(){return B(A1(_Aw,_Au));});return new T1(1,B(_xr(_At,function(_Ay){return E(_Ax);})));},_Az=new T(function(){return B(unCStr("RS"));}),_AA=30,_AB=function(_AC){var _AD=new T(function(){return B(A1(_AC,_AA));});return new T1(1,B(_xr(_Az,function(_AE){return E(_AD);})));},_AF=new T(function(){return B(unCStr("US"));}),_AG=31,_AH=function(_AI){var _AJ=new T(function(){return B(A1(_AI,_AG));});return new T1(1,B(_xr(_AF,function(_AK){return E(_AJ);})));},_AL=new T(function(){return B(unCStr("SP"));}),_AM=32,_AN=function(_AO){var _AP=new T(function(){return B(A1(_AO,_AM));});return new T1(1,B(_xr(_AL,function(_AQ){return E(_AP);})));},_AR=new T(function(){return B(unCStr("DEL"));}),_AS=127,_AT=function(_AU){var _AV=new T(function(){return B(A1(_AU,_AS));});return new T1(1,B(_xr(_AR,function(_AW){return E(_AV);})));},_AX=new T2(1,_AT,_S),_AY=new T2(1,_AN,_AX),_AZ=new T2(1,_AH,_AY),_B0=new T2(1,_AB,_AZ),_B1=new T2(1,_Av,_B0),_B2=new T2(1,_Ap,_B1),_B3=new T2(1,_Aj,_B2),_B4=new T2(1,_Ad,_B3),_B5=new T2(1,_A7,_B4),_B6=new T2(1,_A1,_B5),_B7=new T2(1,_zV,_B6),_B8=new T2(1,_zP,_B7),_B9=new T2(1,_zJ,_B8),_Ba=new T2(1,_zD,_B9),_Bb=new T2(1,_zx,_Ba),_Bc=new T2(1,_zr,_Bb),_Bd=new T2(1,_zl,_Bc),_Be=new T2(1,_zf,_Bd),_Bf=new T2(1,_z9,_Be),_Bg=new T2(1,_z3,_Bf),_Bh=new T2(1,_yX,_Bg),_Bi=new T2(1,_yR,_Bh),_Bj=new T2(1,_yL,_Bi),_Bk=new T2(1,_yF,_Bj),_Bl=new T2(1,_yz,_Bk),_Bm=new T2(1,_yt,_Bl),_Bn=new T2(1,_yn,_Bm),_Bo=new T2(1,_yh,_Bn),_Bp=new T2(1,_yb,_Bo),_Bq=new T2(1,_y5,_Bp),_Br=new T2(1,_xZ,_Bq),_Bs=new T2(1,_xT,_Br),_Bt=new T2(1,_xP,_Bs),_Bu=new T(function(){return B(_xj(_Bt));}),_Bv=34,_Bw=new T1(0,1114111),_Bx=92,_By=39,_Bz=function(_BA){var _BB=new T(function(){return B(A1(_BA,_ys));}),_BC=new T(function(){return B(A1(_BA,_yy));}),_BD=new T(function(){return B(A1(_BA,_yE));}),_BE=new T(function(){return B(A1(_BA,_yK));}),_BF=new T(function(){return B(A1(_BA,_yQ));}),_BG=new T(function(){return B(A1(_BA,_yW));}),_BH=new T(function(){return B(A1(_BA,_z2));}),_BI=new T(function(){return B(A1(_BA,_Bx));}),_BJ=new T(function(){return B(A1(_BA,_By));}),_BK=new T(function(){return B(A1(_BA,_Bv));}),_BL=new T(function(){var _BM=function(_BN){var _BO=new T(function(){return B(_fi(E(_BN)));}),_BP=function(_BQ){var _BR=B(_wr(_BO,_BQ));if(!B(_bp(_BR,_Bw))){return new T0(2);}else{return new F(function(){return A1(_BA,new T(function(){var _BS=B(_9i(_BR));if(_BS>>>0>1114111){return B(_kS(_BS));}else{return _BS;}}));});}};return new T1(1,B(_uX(_BN,_BP)));},_BT=new T(function(){var _BU=new T(function(){return B(A1(_BA,_AG));}),_BV=new T(function(){return B(A1(_BA,_AA));}),_BW=new T(function(){return B(A1(_BA,_Au));}),_BX=new T(function(){return B(A1(_BA,_Ao));}),_BY=new T(function(){return B(A1(_BA,_Ai));}),_BZ=new T(function(){return B(A1(_BA,_Ac));}),_C0=new T(function(){return B(A1(_BA,_A6));}),_C1=new T(function(){return B(A1(_BA,_A0));}),_C2=new T(function(){return B(A1(_BA,_zU));}),_C3=new T(function(){return B(A1(_BA,_zO));}),_C4=new T(function(){return B(A1(_BA,_zI));}),_C5=new T(function(){return B(A1(_BA,_zC));}),_C6=new T(function(){return B(A1(_BA,_zw));}),_C7=new T(function(){return B(A1(_BA,_zq));}),_C8=new T(function(){return B(A1(_BA,_zk));}),_C9=new T(function(){return B(A1(_BA,_ze));}),_Ca=new T(function(){return B(A1(_BA,_z8));}),_Cb=new T(function(){return B(A1(_BA,_xE));}),_Cc=new T(function(){return B(A1(_BA,_ym));}),_Cd=new T(function(){return B(A1(_BA,_yg));}),_Ce=new T(function(){return B(A1(_BA,_ya));}),_Cf=new T(function(){return B(A1(_BA,_y4));}),_Cg=new T(function(){return B(A1(_BA,_xY));}),_Ch=new T(function(){return B(A1(_BA,_xK));}),_Ci=new T(function(){return B(A1(_BA,_xS));}),_Cj=function(_Ck){switch(E(_Ck)){case 64:return E(_Ci);case 65:return E(_Ch);case 66:return E(_Cg);case 67:return E(_Cf);case 68:return E(_Ce);case 69:return E(_Cd);case 70:return E(_Cc);case 71:return E(_BB);case 72:return E(_BC);case 73:return E(_BD);case 74:return E(_BE);case 75:return E(_BF);case 76:return E(_BG);case 77:return E(_BH);case 78:return E(_Cb);case 79:return E(_Ca);case 80:return E(_C9);case 81:return E(_C8);case 82:return E(_C7);case 83:return E(_C6);case 84:return E(_C5);case 85:return E(_C4);case 86:return E(_C3);case 87:return E(_C2);case 88:return E(_C1);case 89:return E(_C0);case 90:return E(_BZ);case 91:return E(_BY);case 92:return E(_BX);case 93:return E(_BW);case 94:return E(_BV);case 95:return E(_BU);default:return new T0(2);}};return B(_sX(new T1(0,function(_Cl){return (E(_Cl)==94)?E(new T1(0,_Cj)):new T0(2);}),new T(function(){return B(A1(_Bu,_BA));})));});return B(_sX(new T1(1,B(_ug(_xd,_xf,_BM))),_BT));});return new F(function(){return _sX(new T1(0,function(_Cm){switch(E(_Cm)){case 34:return E(_BK);case 39:return E(_BJ);case 92:return E(_BI);case 97:return E(_BB);case 98:return E(_BC);case 102:return E(_BG);case 110:return E(_BE);case 114:return E(_BH);case 116:return E(_BD);case 118:return E(_BF);default:return new T0(2);}}),_BL);});},_Cn=function(_Co){return new F(function(){return A1(_Co,_4s);});},_Cp=function(_Cq){var _Cr=E(_Cq);if(!_Cr._){return E(_Cn);}else{var _Cs=E(_Cr.a),_Ct=_Cs>>>0,_Cu=new T(function(){return B(_Cp(_Cr.b));});if(_Ct>887){var _Cv=u_iswspace(_Cs);if(!E(_Cv)){return E(_Cn);}else{var _Cw=function(_Cx){var _Cy=new T(function(){return B(A1(_Cu,_Cx));});return new T1(0,function(_Cz){return E(_Cy);});};return E(_Cw);}}else{var _CA=E(_Ct);if(_CA==32){var _CB=function(_CC){var _CD=new T(function(){return B(A1(_Cu,_CC));});return new T1(0,function(_CE){return E(_CD);});};return E(_CB);}else{if(_CA-9>>>0>4){if(E(_CA)==160){var _CF=function(_CG){var _CH=new T(function(){return B(A1(_Cu,_CG));});return new T1(0,function(_CI){return E(_CH);});};return E(_CF);}else{return E(_Cn);}}else{var _CJ=function(_CK){var _CL=new T(function(){return B(A1(_Cu,_CK));});return new T1(0,function(_CM){return E(_CL);});};return E(_CJ);}}}}},_CN=function(_CO){var _CP=new T(function(){return B(_CN(_CO));}),_CQ=function(_CR){return (E(_CR)==92)?E(_CP):new T0(2);},_CS=function(_CT){return E(new T1(0,_CQ));},_CU=new T1(1,function(_CV){return new F(function(){return A2(_Cp,_CV,_CS);});}),_CW=new T(function(){return B(_Bz(function(_CX){return new F(function(){return A1(_CO,new T2(0,_CX,_kR));});}));}),_CY=function(_CZ){var _D0=E(_CZ);if(_D0==38){return E(_CP);}else{var _D1=_D0>>>0;if(_D1>887){var _D2=u_iswspace(_D0);return (E(_D2)==0)?new T0(2):E(_CU);}else{var _D3=E(_D1);return (_D3==32)?E(_CU):(_D3-9>>>0>4)?(E(_D3)==160)?E(_CU):new T0(2):E(_CU);}}};return new F(function(){return _sX(new T1(0,function(_D4){return (E(_D4)==92)?E(new T1(0,_CY)):new T0(2);}),new T1(0,function(_D5){var _D6=E(_D5);if(E(_D6)==92){return E(_CW);}else{return new F(function(){return A1(_CO,new T2(0,_D6,_kQ));});}}));});},_D7=function(_D8,_D9){var _Da=new T(function(){return B(A1(_D9,new T1(1,new T(function(){return B(A1(_D8,_S));}))));}),_Db=function(_Dc){var _Dd=E(_Dc),_De=E(_Dd.a);if(E(_De)==34){if(!E(_Dd.b)){return E(_Da);}else{return new F(function(){return _D7(function(_Df){return new F(function(){return A1(_D8,new T2(1,_De,_Df));});},_D9);});}}else{return new F(function(){return _D7(function(_Dg){return new F(function(){return A1(_D8,new T2(1,_De,_Dg));});},_D9);});}};return new F(function(){return _CN(_Db);});},_Dh=new T(function(){return B(unCStr("_\'"));}),_Di=function(_Dj){var _Dk=u_iswalnum(_Dj);if(!E(_Dk)){return new F(function(){return _x0(_tM,_Dj,_Dh);});}else{return true;}},_Dl=function(_Dm){return new F(function(){return _Di(E(_Dm));});},_Dn=new T(function(){return B(unCStr(",;()[]{}`"));}),_Do=new T(function(){return B(unCStr("=>"));}),_Dp=new T2(1,_Do,_S),_Dq=new T(function(){return B(unCStr("~"));}),_Dr=new T2(1,_Dq,_Dp),_Ds=new T(function(){return B(unCStr("@"));}),_Dt=new T2(1,_Ds,_Dr),_Du=new T(function(){return B(unCStr("->"));}),_Dv=new T2(1,_Du,_Dt),_Dw=new T(function(){return B(unCStr("<-"));}),_Dx=new T2(1,_Dw,_Dv),_Dy=new T(function(){return B(unCStr("|"));}),_Dz=new T2(1,_Dy,_Dx),_DA=new T(function(){return B(unCStr("\\"));}),_DB=new T2(1,_DA,_Dz),_DC=new T(function(){return B(unCStr("="));}),_DD=new T2(1,_DC,_DB),_DE=new T(function(){return B(unCStr("::"));}),_DF=new T2(1,_DE,_DD),_DG=new T(function(){return B(unCStr(".."));}),_DH=new T2(1,_DG,_DF),_DI=function(_DJ){var _DK=new T(function(){return B(A1(_DJ,_uU));}),_DL=new T(function(){var _DM=new T(function(){var _DN=function(_DO){var _DP=new T(function(){return B(A1(_DJ,new T1(0,_DO)));});return new T1(0,function(_DQ){return (E(_DQ)==39)?E(_DP):new T0(2);});};return B(_Bz(_DN));}),_DR=function(_DS){var _DT=E(_DS);switch(E(_DT)){case 39:return new T0(2);case 92:return E(_DM);default:var _DU=new T(function(){return B(A1(_DJ,new T1(0,_DT)));});return new T1(0,function(_DV){return (E(_DV)==39)?E(_DU):new T0(2);});}},_DW=new T(function(){var _DX=new T(function(){return B(_D7(_3G,_DJ));}),_DY=new T(function(){var _DZ=new T(function(){var _E0=new T(function(){var _E1=function(_E2){var _E3=E(_E2),_E4=u_iswalpha(_E3);return (E(_E4)==0)?(E(_E3)==95)?new T1(1,B(_uG(_Dl,function(_E5){return new F(function(){return A1(_DJ,new T1(3,new T2(1,_E3,_E5)));});}))):new T0(2):new T1(1,B(_uG(_Dl,function(_E6){return new F(function(){return A1(_DJ,new T1(3,new T2(1,_E3,_E6)));});})));};return B(_sX(new T1(0,_E1),new T(function(){return new T1(1,B(_ug(_vS,_wY,_DJ)));})));}),_E7=function(_E8){return (!B(_x0(_tM,_E8,_x5)))?new T0(2):new T1(1,B(_uG(_x6,function(_E9){var _Ea=new T2(1,_E8,_E9);if(!B(_x0(_tV,_Ea,_DH))){return new F(function(){return A1(_DJ,new T1(4,_Ea));});}else{return new F(function(){return A1(_DJ,new T1(2,_Ea));});}})));};return B(_sX(new T1(0,_E7),_E0));});return B(_sX(new T1(0,function(_Eb){if(!B(_x0(_tM,_Eb,_Dn))){return new T0(2);}else{return new F(function(){return A1(_DJ,new T1(2,new T2(1,_Eb,_S)));});}}),_DZ));});return B(_sX(new T1(0,function(_Ec){return (E(_Ec)==34)?E(_DX):new T0(2);}),_DY));});return B(_sX(new T1(0,function(_Ed){return (E(_Ed)==39)?E(new T1(0,_DR)):new T0(2);}),_DW));});return new F(function(){return _sX(new T1(1,function(_Ee){return (E(_Ee)._==0)?E(_DK):new T0(2);}),_DL);});},_Ef=0,_Eg=function(_Eh,_Ei){var _Ej=new T(function(){var _Ek=new T(function(){var _El=function(_Em){var _En=new T(function(){var _Eo=new T(function(){return B(A1(_Ei,_Em));});return B(_DI(function(_Ep){var _Eq=E(_Ep);return (_Eq._==2)?(!B(_tB(_Eq.a,_tA)))?new T0(2):E(_Eo):new T0(2);}));}),_Er=function(_Es){return E(_En);};return new T1(1,function(_Et){return new F(function(){return A2(_Cp,_Et,_Er);});});};return B(A2(_Eh,_Ef,_El));});return B(_DI(function(_Eu){var _Ev=E(_Eu);return (_Ev._==2)?(!B(_tB(_Ev.a,_tz)))?new T0(2):E(_Ek):new T0(2);}));}),_Ew=function(_Ex){return E(_Ej);};return function(_Ey){return new F(function(){return A2(_Cp,_Ey,_Ew);});};},_Ez=function(_EA,_EB){var _EC=function(_ED){var _EE=new T(function(){return B(A1(_EA,_ED));}),_EF=function(_EG){return new F(function(){return _sX(B(A1(_EE,_EG)),new T(function(){return new T1(1,B(_Eg(_EC,_EG)));}));});};return E(_EF);},_EH=new T(function(){return B(A1(_EA,_EB));}),_EI=function(_EJ){return new F(function(){return _sX(B(A1(_EH,_EJ)),new T(function(){return new T1(1,B(_Eg(_EC,_EJ)));}));});};return E(_EI);},_EK=function(_EL,_EM){var _EN=function(_EO,_EP){var _EQ=function(_ER){return new F(function(){return A1(_EP,new T(function(){return  -E(_ER);}));});},_ES=new T(function(){return B(_DI(function(_ET){return new F(function(){return A3(_EL,_ET,_EO,_EQ);});}));}),_EU=function(_EV){return E(_ES);},_EW=function(_EX){return new F(function(){return A2(_Cp,_EX,_EU);});},_EY=new T(function(){return B(_DI(function(_EZ){var _F0=E(_EZ);if(_F0._==4){var _F1=E(_F0.a);if(!_F1._){return new F(function(){return A3(_EL,_F0,_EO,_EP);});}else{if(E(_F1.a)==45){if(!E(_F1.b)._){return E(new T1(1,_EW));}else{return new F(function(){return A3(_EL,_F0,_EO,_EP);});}}else{return new F(function(){return A3(_EL,_F0,_EO,_EP);});}}}else{return new F(function(){return A3(_EL,_F0,_EO,_EP);});}}));}),_F2=function(_F3){return E(_EY);};return new T1(1,function(_F4){return new F(function(){return A2(_Cp,_F4,_F2);});});};return new F(function(){return _Ez(_EN,_EM);});},_F5=function(_F6){var _F7=E(_F6);if(!_F7._){var _F8=_F7.b,_F9=new T(function(){return B(_wa(new T(function(){return B(_fi(E(_F7.a)));}),new T(function(){return B(_rE(_F8,0));},1),B(_l9(_w0,_F8))));});return new T1(1,_F9);}else{return (E(_F7.b)._==0)?(E(_F7.c)._==0)?new T1(1,new T(function(){return B(_wr(_vZ,_F7.a));})):__Z:__Z;}},_Fa=function(_Fb,_Fc){return new T0(2);},_Fd=function(_Fe){var _Ff=E(_Fe);if(_Ff._==5){var _Fg=B(_F5(_Ff.a));if(!_Fg._){return E(_Fa);}else{var _Fh=new T(function(){return B(_9i(_Fg.a));});return function(_Fi,_Fj){return new F(function(){return A1(_Fj,_Fh);});};}}else{return E(_Fa);}},_Fk=function(_Fl){var _Fm=function(_Fn){return E(new T2(3,_Fl,_u7));};return new T1(1,function(_Fo){return new F(function(){return A2(_Cp,_Fo,_Fm);});});},_Fp=new T(function(){return B(A3(_EK,_Fd,_Ef,_Fk));}),_Fq=100,_Fr={_:0,a:_2N,b:_2N,c:_2N,d:_2N,e:_kQ,f:_S,g:_Fq},_Fs=function(_Ft){while(1){var _Fu=B((function(_Fv){var _Fw=E(_Fv);if(!_Fw._){return __Z;}else{var _Fx=_Fw.b,_Fy=E(_Fw.a);if(!E(_Fy.b)._){return new T2(1,_Fy.a,new T(function(){return B(_Fs(_Fx));}));}else{_Ft=_Fx;return __continue;}}})(_Ft));if(_Fu!=__continue){return _Fu;}}},_Fz=function(_FA){var _FB=E(_FA);if(!_FB._){return E(_sH);}else{var _FC=new T(function(){var _FD=B(_Fs(B(_sN(_Fp,new T(function(){return B(A2(E(_FB.a).b,_Fr,_S));})))));if(!_FD._){return E(_sJ);}else{if(!E(_FD.b)._){return E(_FD.a);}else{return E(_sL);}}});return new T2(0,_FB.b,_FC);}},_FE=function(_FF){return (E(_FF)-48|0)>>>0<=9;},_FG=0,_FH=new T1(1,_FG),_FI=0,_FJ=0,_FK=new T1(1,_FJ),_FL=1,_FM=new T1(1,_FL),_FN=new T(function(){var _FO=B(_aB(_FE,_S)),_FP=_FO.b,_FQ=E(_FO.a);if(!_FQ._){return new T2(0,_FI,_FP);}else{return new T2(0,new T(function(){var _FR=B(_Fs(B(_sN(_Fp,_FQ))));if(!_FR._){return E(_sJ);}else{if(!E(_FR.b)._){return E(_FR.a);}else{return E(_sL);}}}),_FP);}}),_FS=new T(function(){return E(E(_FN).a);}),_FT=new T1(1,_FS),_FU=new T(function(){return E(E(_FN).b);}),_FV=1,_FW=new T1(1,_FV),_FX=function(_FY,_FZ,_G0,_G1,_G2,_G3){while(1){var _G4=B((function(_G5,_G6,_G7,_G8,_G9,_Ga){var _Gb=E(_G9);if(!_Gb._){return E(_6c);}else{var _Gc=_Gb.b,_Gd=E(_Gb.a);switch(_Gd){case 32:var _Ge=_G5,_Gf=_G6,_Gg=_G8,_Gh=_Ga;_FY=_Ge;_FZ=_Gf;_G0=new T(function(){var _Gi=E(_G7);if(!_Gi._){return E(_FM);}else{if(!E(_Gi.a)){return E(_FK);}else{return E(_FM);}}});_G1=_Gg;_G2=_Gc;_G3=_Gh;return __continue;case 35:var _Ge=_G5,_Gf=_G6,_Gj=_G7,_Gh=_Ga;_FY=_Ge;_FZ=_Gf;_G0=_Gj;_G1=_kR;_G2=_Gc;_G3=_Gh;return __continue;case 42:var _Gk=new T(function(){var _Gl=B(_Fz(_Ga));return new T2(0,_Gl.a,_Gl.b);}),_Gm=new T(function(){var _Gn=E(_Gc);if(!_Gn._){return new T3(0,_2N,_S,new T(function(){return E(E(_Gk).a);}));}else{if(E(_Gn.a)==46){var _Go=E(_Gn.b);if(!_Go._){return new T3(0,_FT,_FU,new T(function(){return E(E(_Gk).a);}));}else{if(E(_Go.a)==42){var _Gp=new T(function(){var _Gq=B(_Fz(E(_Gk).a));return new T2(0,_Gq.a,_Gq.b);});return new T3(0,new T1(1,new T(function(){return E(E(_Gp).b);})),_Go.b,new T(function(){return E(E(_Gp).a);}));}else{var _Gr=new T(function(){var _Gs=B(_aB(_FE,_Go)),_Gt=_Gs.b,_Gu=E(_Gs.a);if(!_Gu._){return new T2(0,_FI,_Gt);}else{return new T2(0,new T(function(){var _Gv=B(_Fs(B(_sN(_Fp,_Gu))));if(!_Gv._){return E(_sJ);}else{if(!E(_Gv.b)._){return E(_Gv.a);}else{return E(_sL);}}}),_Gt);}});return new T3(0,new T1(1,new T(function(){return E(E(_Gr).a);})),new T(function(){return E(E(_Gr).b);}),new T(function(){return E(E(_Gk).a);}));}}}else{return new T3(0,_2N,_Gn,new T(function(){return E(E(_Gk).a);}));}}}),_Gw=new T(function(){return E(E(_Gm).c);}),_Gx=new T(function(){var _Gy=E(_Gw);if(!_Gy._){return E(_sH);}else{return B(A1(E(_Gy.a).a,new T(function(){return E(E(_Gm).b);})));}}),_Gz=new T(function(){return E(E(_Gk).b);});return new T3(0,{_:0,a:new T1(1,new T(function(){return B(_ir(_Gz));})),b:new T(function(){return E(E(_Gm).a);}),c:new T(function(){if(E(_Gz)>=0){if(!E(_G5)){if(!E(_G6)){return __Z;}else{return E(_FW);}}else{return E(_FH);}}else{return E(_FH);}}),d:_G7,e:_G8,f:new T(function(){return E(E(_Gx).a);}),g:new T(function(){return E(E(_Gx).b);})},new T(function(){return E(E(_Gx).c);}),_Gw);case 43:var _Ge=_G5,_Gf=_G6,_Gg=_G8,_Gh=_Ga;_FY=_Ge;_FZ=_Gf;_G0=_FK;_G1=_Gg;_G2=_Gc;_G3=_Gh;return __continue;case 45:var _Gf=_G6,_Gj=_G7,_Gg=_G8,_Gh=_Ga;_FY=_kR;_FZ=_Gf;_G0=_Gj;_G1=_Gg;_G2=_Gc;_G3=_Gh;return __continue;case 46:var _GA=new T(function(){var _GB=E(_Gc);if(!_GB._){var _GC=B(_aB(_FE,_S)),_GD=_GC.b,_GE=E(_GC.a);if(!_GE._){return new T3(0,_FI,_GD,_Ga);}else{return new T3(0,new T(function(){var _GF=B(_Fs(B(_sN(_Fp,_GE))));if(!_GF._){return E(_sJ);}else{if(!E(_GF.b)._){return E(_GF.a);}else{return E(_sL);}}}),_GD,_Ga);}}else{if(E(_GB.a)==42){var _GG=new T(function(){var _GH=B(_Fz(_Ga));return new T2(0,_GH.a,_GH.b);});return new T3(0,new T(function(){return E(E(_GG).b);}),_GB.b,new T(function(){return E(E(_GG).a);}));}else{var _GI=B(_aB(_FE,_GB)),_GJ=_GI.b,_GK=E(_GI.a);if(!_GK._){return new T3(0,_FI,_GJ,_Ga);}else{return new T3(0,new T(function(){var _GL=B(_Fs(B(_sN(_Fp,_GK))));if(!_GL._){return E(_sJ);}else{if(!E(_GL.b)._){return E(_GL.a);}else{return E(_sL);}}}),_GJ,_Ga);}}}}),_GM=new T(function(){return E(E(_GA).c);}),_GN=new T(function(){var _GO=E(_GM);if(!_GO._){return E(_sH);}else{return B(A1(E(_GO.a).a,new T(function(){return E(E(_GA).b);})));}});return new T3(0,{_:0,a:_2N,b:new T1(1,new T(function(){return E(E(_GA).a);})),c:new T(function(){if(!E(_G5)){if(!E(_G6)){return __Z;}else{return E(_FW);}}else{return E(_FH);}}),d:_G7,e:_G8,f:new T(function(){return E(E(_GN).a);}),g:new T(function(){return E(E(_GN).b);})},new T(function(){return E(E(_GN).c);}),_GM);case 48:var _Ge=_G5,_Gj=_G7,_Gg=_G8,_Gh=_Ga;_FY=_Ge;_FZ=_kR;_G0=_Gj;_G1=_Gg;_G2=_Gc;_G3=_Gh;return __continue;default:if((_Gd-48|0)>>>0>9){var _GP=new T(function(){var _GQ=E(_Ga);if(!_GQ._){return E(_sH);}else{return B(A1(E(_GQ.a).a,_Gb));}});return new T3(0,{_:0,a:_2N,b:_2N,c:new T(function(){if(!E(_G5)){if(!E(_G6)){return __Z;}else{return E(_FW);}}else{return E(_FH);}}),d:_G7,e:_G8,f:new T(function(){return E(E(_GP).a);}),g:new T(function(){return E(E(_GP).b);})},new T(function(){return E(E(_GP).c);}),_Ga);}else{var _GR=new T(function(){var _GS=B(_aB(_FE,_Gb)),_GT=_GS.b,_GU=E(_GS.a);if(!_GU._){return new T2(0,_FI,_GT);}else{return new T2(0,new T(function(){var _GV=B(_Fs(B(_sN(_Fp,_GU))));if(!_GV._){return E(_sJ);}else{if(!E(_GV.b)._){return E(_GV.a);}else{return E(_sL);}}}),_GT);}}),_GW=new T(function(){var _GX=E(E(_GR).b);if(!_GX._){return new T3(0,_2N,_S,_Ga);}else{if(E(_GX.a)==46){var _GY=E(_GX.b);if(!_GY._){return new T3(0,_FT,_FU,_Ga);}else{if(E(_GY.a)==42){var _GZ=new T(function(){var _H0=B(_Fz(_Ga));return new T2(0,_H0.a,_H0.b);});return new T3(0,new T1(1,new T(function(){return E(E(_GZ).b);})),_GY.b,new T(function(){return E(E(_GZ).a);}));}else{var _H1=new T(function(){var _H2=B(_aB(_FE,_GY)),_H3=_H2.b,_H4=E(_H2.a);if(!_H4._){return new T2(0,_FI,_H3);}else{return new T2(0,new T(function(){var _H5=B(_Fs(B(_sN(_Fp,_H4))));if(!_H5._){return E(_sJ);}else{if(!E(_H5.b)._){return E(_H5.a);}else{return E(_sL);}}}),_H3);}});return new T3(0,new T1(1,new T(function(){return E(E(_H1).a);})),new T(function(){return E(E(_H1).b);}),_Ga);}}}else{return new T3(0,_2N,_GX,_Ga);}}}),_H6=new T(function(){return E(E(_GW).c);}),_H7=new T(function(){var _H8=E(_H6);if(!_H8._){return E(_sH);}else{return B(A1(E(_H8.a).a,new T(function(){return E(E(_GW).b);})));}}),_H9=new T(function(){return E(E(_GR).a);});return new T3(0,{_:0,a:new T1(1,new T(function(){return B(_ir(_H9));})),b:new T(function(){return E(E(_GW).a);}),c:new T(function(){if(E(_H9)>=0){if(!E(_G5)){if(!E(_G6)){return __Z;}else{return E(_FW);}}else{return E(_FH);}}else{return E(_FH);}}),d:_G7,e:_G8,f:new T(function(){return E(E(_H7).a);}),g:new T(function(){return E(E(_H7).b);})},new T(function(){return E(E(_H7).c);}),_H6);}}}})(_FY,_FZ,_G0,_G1,_G2,_G3));if(_G4!=__continue){return _G4;}}},_Ha=37,_Hb=function(_Hc,_Hd,_He){var _Hf=E(_Hc);if(!_Hf._){return (E(_Hd)._==0)?E(_He):E(_6c);}else{var _Hg=_Hf.b,_Hh=E(_Hf.a);if(E(_Hh)==37){var _Hi=function(_Hj){var _Hk=E(_Hd);if(!_Hk._){return E(_sH);}else{var _Hl=B(_FX(_kQ,_kQ,_2N,_kQ,_Hg,_Hk)),_Hm=E(_Hl.c);if(!_Hm._){return E(_sH);}else{return new F(function(){return A2(E(_Hm.a).b,_Hl.a,new T(function(){return B(_Hb(_Hl.b,_Hm.b,_Hj));}));});}}},_Hn=E(_Hg);if(!_Hn._){return new F(function(){return _Hi(_He);});}else{if(E(_Hn.a)==37){return new T2(1,_Ha,new T(function(){return B(_Hb(_Hn.b,_Hd,_He));}));}else{return new F(function(){return _Hi(_He);});}}}else{return new T2(1,_Hh,new T(function(){return B(_Hb(_Hg,_Hd,_He));}));}}},_Ho=function(_Hp,_Hq){return new F(function(){return _l9(_sE,B(_Hb(_Hp,new T(function(){return B(_lw(_Hq,_S));},1),_S)));});},_Hr=function(_Hs){return new F(function(){return _Ho(_sD,new T2(1,new T2(0,function(_Ht){return new F(function(){return _6d(_Hs,_Ht);});},function(_Ht){return new F(function(){return _sz(_Hs,_Ht);});}),_S));});},_Hu=new T(function(){return B(unCStr(","));}),_Hv=new T(function(){return B(unCStr("]"));}),_Hw=function(_Hx){var _Hy=E(_Hx);if(!_Hy._){return __Z;}else{return new F(function(){return _q(_Hy.a,new T(function(){return B(_Hw(_Hy.b));},1));});}},_Hz=function(_HA,_HB){var _HC=E(_HB);return (_HC._==0)?__Z:new T2(1,_HA,new T2(1,_HC.a,new T(function(){return B(_Hz(_HA,_HC.b));})));},_HD=function(_HE){var _HF=new T(function(){var _HG=B(_l9(_Hr,_HE));if(!_HG._){return E(_Hv);}else{return B(_q(B(_Hw(new T2(1,_HG.a,new T(function(){return B(_Hz(_Hu,_HG.b));})))),_Hv));}});return new F(function(){return unAppCStr("[",_HF);});},_HH=new T(function(){return B(unCStr("None"));}),_HI=new T(function(){return B(unCStr("Tri "));}),_HJ=function(_HK){var _HL=jsShow(E(_HK));return new F(function(){return fromJSStr(_HL);});},_HM=32,_HN=function(_HO,_HP,_HQ){var _HR=E(_HP);if(!_HR._){var _HS=function(_HT){var _HU=E(_HR.a),_HV=new T(function(){var _HW=new T(function(){var _HX=E(_HR.b),_HY=new T(function(){var _HZ=new T(function(){var _I0=E(_HR.c),_I1=new T(function(){var _I2=new T(function(){return B(_HJ(_I0.b));}),_I3=new T(function(){return B(_HJ(_I0.a));});return B(A3(_mc,_m3,new T2(1,function(_Ht){return new F(function(){return _q(_I3,_Ht);});},new T2(1,function(_Ht){return new F(function(){return _q(_I2,_Ht);});},_S)),new T2(1,_y,_HT)));});return new T2(1,_z,_I1);}),_I4=new T(function(){return B(_HJ(_HX.b));}),_I5=new T(function(){return B(_HJ(_HX.a));});return B(A3(_mc,_m3,new T2(1,function(_Ht){return new F(function(){return _q(_I5,_Ht);});},new T2(1,function(_Ht){return new F(function(){return _q(_I4,_Ht);});},_S)),new T2(1,_y,new T2(1,_HM,_HZ))));});return new T2(1,_z,_HY);}),_I6=new T(function(){return B(_HJ(_HU.b));}),_I7=new T(function(){return B(_HJ(_HU.a));});return B(A3(_mc,_m3,new T2(1,function(_Ht){return new F(function(){return _q(_I7,_Ht);});},new T2(1,function(_Ht){return new F(function(){return _q(_I6,_Ht);});},_S)),new T2(1,_y,new T2(1,_HM,_HW))));});return new T2(1,_z,_HV);};if(E(_HO)<11){return new F(function(){return _q(_HI,new T(function(){return B(_HS(_HQ));},1));});}else{var _I8=new T(function(){return B(_q(_HI,new T(function(){return B(_HS(new T2(1,_y,_HQ)));},1)));});return new T2(1,_z,_I8);}}else{return new F(function(){return _q(_HH,_HQ);});}},_I9=function(_Ia){return new F(function(){return _HN(_mn,_Ia,_S);});},_Ib=function(_Ic,_){return _4s;},_Id=new T(function(){return B(unCStr(")"));}),_Ie=function(_If,_Ig){var _Ih=new T(function(){var _Ii=new T(function(){return B(unAppCStr(",",new T(function(){return B(_q(B(_Hr(_Ig)),_Id));})));},1);return B(_q(B(_Hr(_If)),_Ii));});return new F(function(){return unAppCStr("(",_Ih);});},_Ij=function(_){return _4s;},_Ik=new T(function(){return eval("(function(ctx, x, y, radius, fromAngle, toAngle){ctx.arc(x, y, radius, fromAngle, toAngle);})");}),_Il=0,_Im=6.283185307179586,_In=new T(function(){return eval("(function(ctx,x,y){ctx.moveTo(x,y);})");}),_Io=function(_Ip,_Iq,_Ir,_Is,_){var _It=__app3(E(_In),_Is,_Ip+_Ir,_Iq),_Iu=__apply(E(_Ik),new T2(1,_Im,new T2(1,_Il,new T2(1,_Ir,new T2(1,_Iq,new T2(1,_Ip,new T2(1,_Is,_S)))))));return new F(function(){return _Ij(_);});},_Iv=new T(function(){return eval("(function(ctx){ctx.beginPath();})");}),_Iw=new T(function(){return eval("(function(ctx){ctx.fill();})");}),_Ix=function(_Iy,_Iz,_){var _IA=__app1(E(_Iv),_Iz),_IB=B(A2(_Iy,_Iz,_)),_IC=__app1(E(_Iw),_Iz);return new F(function(){return _Ij(_);});},_ID=new T(function(){return eval("(function(ctx){ctx.stroke();})");}),_IE=function(_IF,_IG,_){var _IH=__app1(E(_Iv),_IG),_II=B(A2(_IF,_IG,_)),_IJ=__app1(E(_ID),_IG);return new F(function(){return _Ij(_);});},_IK=function(_IL){var _IM=E(_IL);if(!_IM._){var _IN=E(_IM.b),_IO=E(_IM.a),_IP=E(_IM.c),_IQ=E(_IO.a),_IR=E(_IO.b);return ((E(_IN.a)-_IQ)*(E(_IP.b)-_IR)-(E(_IN.b)-_IR)*(E(_IP.a)-_IQ))/2;}else{return 0;}},_IS=function(_IT,_IU,_IV,_IW,_IX,_IY,_IZ,_J0){var _J1=_IX-_IZ,_J2=function(_J3){if(_J3>=1.0e-9){var _J4=new T(function(){return (E(_J0)-E(_IY))/(_IZ-_IX);});return new T2(0,new T2(0,_IT,new T(function(){return E(_J4)*(E(_IT)-_IX)+E(_IY);})),new T2(0,_IV,new T(function(){return E(_J4)*(E(_IV)-_IX)+E(_IY);})));}else{return new T2(0,new T2(0,_IX,_IU),new T2(0,_IZ,_IW));}};if(_J1!=0){if(_J1<=0){return new F(function(){return _J2( -_J1);});}else{return new F(function(){return _J2(_J1);});}}else{return new F(function(){return _J2(0);});}},_J5=function(_J6){var _J7=E(_J6);if(!_J7._){var _J8=_J7.a,_J9=_J7.b,_Ja=_J7.c;return new T2(1,new T(function(){var _Jb=E(_J9),_Jc=E(_J8),_Jd=E(_Ja),_Je=E(_Jc.a),_Jf=E(_Jc.b),_Jg=E(_Jb.a)-_Je,_Jh=E(_Jd.a)-_Je,_Ji=E(_Jb.b)-_Jf,_Jj=E(_Jd.b)-_Jf;return Math.acos((_Jg*_Jh+_Ji*_Jj)/(Math.sqrt(_Jg*_Jg+_Ji*_Ji)*Math.sqrt(_Jh*_Jh+_Jj*_Jj)));}),new T2(1,new T(function(){var _Jk=E(_J8),_Jl=E(_J9),_Jm=E(_Ja),_Jn=E(_Jl.a),_Jo=E(_Jl.b),_Jp=E(_Jk.a)-_Jn,_Jq=E(_Jm.a)-_Jn,_Jr=E(_Jk.b)-_Jo,_Js=E(_Jm.b)-_Jo;return Math.acos((_Jp*_Jq+_Jr*_Js)/(Math.sqrt(_Jp*_Jp+_Jr*_Jr)*Math.sqrt(_Jq*_Jq+_Js*_Js)));}),new T2(1,new T(function(){var _Jt=E(_J8),_Ju=E(_Ja),_Jv=E(_J9),_Jw=E(_Ju.a),_Jx=E(_Ju.b),_Jy=E(_Jt.a)-_Jw,_Jz=E(_Jv.a)-_Jw,_JA=E(_Jt.b)-_Jx,_JB=E(_Jv.b)-_Jx;return Math.acos((_Jy*_Jz+_JA*_JB)/(Math.sqrt(_Jy*_Jy+_JA*_JA)*Math.sqrt(_Jz*_Jz+_JB*_JB)));}),_S)));}else{return __Z;}},_JC=new T(function(){return B(unCStr("head"));}),_JD=new T(function(){return B(_m8(_JC));}),_JE=function(_JF){var _JG=E(_JF);if(!_JG._){var _JH=_JG.a,_JI=_JG.b,_JJ=_JG.c;return new T2(1,new T(function(){var _JK=E(_JJ),_JL=E(_JI),_JM=E(_JK.a)-E(_JL.a),_JN=E(_JK.b)-E(_JL.b);return Math.sqrt(_JM*_JM+_JN*_JN);}),new T2(1,new T(function(){var _JO=E(_JH),_JP=E(_JJ),_JQ=E(_JO.a)-E(_JP.a),_JR=E(_JO.b)-E(_JP.b);return Math.sqrt(_JQ*_JQ+_JR*_JR);}),new T2(1,new T(function(){var _JS=E(_JI),_JT=E(_JH),_JU=E(_JS.a)-E(_JT.a),_JV=E(_JS.b)-E(_JT.b);return Math.sqrt(_JU*_JU+_JV*_JV);}),_S)));}else{return __Z;}},_JW=function(_JX){var _JY=B(_J5(_JX));if(!_JY._){return 0;}else{var _JZ=B(_JE(_JX));if(!_JZ._){return E(_JD);}else{var _K0=E(_JY.a),_K1=E(_JZ.a)/(Math.sin(_K0)+Math.sin(_K0));return (_K1!=0)?(_K1<=0)? -_K1:E(_K1):0;}}},_K2=function(_K3){return new F(function(){return _aX("main.hs:(205,12)-(207,30)|case");});},_K4=new T(function(){return B(_K2(_));}),_K5=function(_K6){var _K7=B(_JE(_K6));if(!_K7._){return 0;}else{var _K8=E(_K7.b);if(!_K8._){return E(_K4);}else{var _K9=E(_K8.b);if(!_K9._){return E(_K4);}else{if(!E(_K9.b)._){var _Ka=B(_IK(_K6)),_Kb=(_Ka+_Ka)/(E(_K7.a)+E(_K8.a)+E(_K9.a));return (_Kb!=0)?(_Kb<=0)? -_Kb:E(_Kb):0;}else{return E(_K4);}}}}},_Kc=new T(function(){return eval("(function(ctx,s,x,y){ctx.fillText(s,x,y);})");}),_Kd=function(_Ke,_Kf,_Kg){var _Kh=new T(function(){return toJSStr(E(_Kg));});return function(_Ki,_){var _Kj=__app4(E(_Kc),E(_Ki),E(_Kh),E(_Ke),E(_Kf));return new F(function(){return _Ij(_);});};},_Kk=new T3(0,255,200,0),_Kl=new T2(1,_Kk,_S),_Km=new T2(1,_Kk,_Kl),_Kn=new T2(1,_Kk,_Km),_Ko=new T3(0,0,50,255),_Kp=new T2(1,_Ko,_Kn),_Kq=new T3(0,255,50,0),_Kr=new T2(1,_Kq,_Kp),_Ks=new T3(0,0,255,50),_Kt=new T2(1,_Ks,_Kr),_Ku=new T(function(){return eval("(function(e){e.width = e.width;})");}),_Kv=function(_Kw,_Kx,_Ky,_){var _Kz=E(_Kw);return new F(function(){return _Io(E(_Kz.a),E(_Kz.b),E(_Kx),E(_Ky),_);});},_KA=",",_KB="rgba(",_KC=new T(function(){return toJSStr(_S);}),_KD="rgb(",_KE=")",_KF=new T2(1,_KE,_S),_KG=function(_KH){var _KI=E(_KH);if(!_KI._){var _KJ=jsCat(new T2(1,_KD,new T2(1,new T(function(){return String(_KI.a);}),new T2(1,_KA,new T2(1,new T(function(){return String(_KI.b);}),new T2(1,_KA,new T2(1,new T(function(){return String(_KI.c);}),_KF)))))),E(_KC));return E(_KJ);}else{var _KK=jsCat(new T2(1,_KB,new T2(1,new T(function(){return String(_KI.a);}),new T2(1,_KA,new T2(1,new T(function(){return String(_KI.b);}),new T2(1,_KA,new T2(1,new T(function(){return String(_KI.c);}),new T2(1,_KA,new T2(1,new T(function(){return String(_KI.d);}),_KF)))))))),E(_KC));return E(_KK);}},_KL="strokeStyle",_KM="fillStyle",_KN=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_KO=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_KP=function(_KQ,_KR){var _KS=new T(function(){return B(_KG(_KQ));});return function(_KT,_){var _KU=E(_KT),_KV=E(_KM),_KW=E(_KN),_KX=__app2(_KW,_KU,_KV),_KY=E(_KL),_KZ=__app2(_KW,_KU,_KY),_L0=E(_KS),_L1=E(_KO),_L2=__app3(_L1,_KU,_KV,_L0),_L3=__app3(_L1,_KU,_KY,_L0),_L4=B(A2(_KR,_KU,_)),_L5=String(_KX),_L6=__app3(_L1,_KU,_KV,_L5),_L7=String(_KZ),_L8=__app3(_L1,_KU,_KY,_L7);return new F(function(){return _Ij(_);});};},_L9=new T3(0,40,40,40),_La=new T2(1,_L9,_Kt),_Lb=function(_Lc,_Ld,_Le){var _Lf=E(_Le);if(!_Lf._){return __Z;}else{var _Lg=_Lf.a,_Lh=_Lf.b;return (!B(A2(_Lc,_Ld,_Lg)))?new T2(1,_Lg,new T(function(){return B(_Lb(_Lc,_Ld,_Lh));})):E(_Lh);}},_Li="font",_Lj=function(_Lk,_Ll){var _Lm=new T(function(){return toJSStr(E(_Lk));});return function(_Ln,_){var _Lo=E(_Ln),_Lp=E(_Li),_Lq=__app2(E(_KN),_Lo,_Lp),_Lr=E(_KO),_Ls=__app3(_Lr,_Lo,_Lp,E(_Lm)),_Lt=B(A2(_Ll,_Lo,_)),_Lu=String(_Lq),_Lv=__app3(_Lr,_Lo,_Lp,_Lu);return new F(function(){return _Ij(_);});};},_Lw=2147483647,_Lx=new T2(0,_Lw,_Lw),_Ly=new T(function(){return eval("(function(ctx,x,y){ctx.lineTo(x,y);})");}),_Lz=function(_LA,_LB,_){var _LC=E(_LA);if(!_LC._){return _4s;}else{var _LD=E(_LC.a),_LE=E(_LB),_LF=__app3(E(_In),_LE,E(_LD.a),E(_LD.b)),_LG=E(_LC.b);if(!_LG._){return _4s;}else{var _LH=E(_LG.a),_LI=E(_Ly),_LJ=__app3(_LI,_LE,E(_LH.a),E(_LH.b)),_LK=function(_LL,_){while(1){var _LM=E(_LL);if(!_LM._){return _4s;}else{var _LN=E(_LM.a),_LO=__app3(_LI,_LE,E(_LN.a),E(_LN.b));_LL=_LM.b;continue;}}};return new F(function(){return _LK(_LG.b,_);});}}},_LP=function(_LQ,_LR,_LS,_){return new F(function(){return _Lz(new T2(1,_LQ,new T2(1,_LR,_S)),_LS,_);});},_LT="lineWidth",_LU=function(_LV,_LW){var _LX=new T(function(){return String(E(_LV));});return function(_LY,_){var _LZ=E(_LY),_M0=E(_LT),_M1=__app2(E(_KN),_LZ,_M0),_M2=E(_KO),_M3=__app3(_M2,_LZ,_M0,E(_LX)),_M4=B(A2(_LW,_LZ,_)),_M5=String(_M1),_M6=__app3(_M2,_LZ,_M0,_M5);return new F(function(){return _Ij(_);});};},_M7=new T(function(){return B(unCStr("line"));}),_M8=new T(function(){return B(_go(4,6));}),_M9=new T(function(){return B(unCStr("r\'"));}),_Ma=new T(function(){return B(unCStr("r"));}),_Mb=new T(function(){return B(unCStr("R"));}),_Mc=new T(function(){return B(unCStr("S"));}),_Md=new T(function(){return B(unCStr("a,b,c"));}),_Me=25,_Mf=new T(function(){return B(unCStr("20px Ricty Diminished"));}),_Mg=0.7,_Mh=new T3(0,200,0,255),_Mi=0.5,_Mj=2,_Mk=1,_Ml=new T3(0,_Mk,_Mk,_Mk),_Mm=function(_Mn){return new F(function(){return _l6("main.hs:91:11-29|[a, b, c]");});},_Mo=new T(function(){return B(_Mm(_));}),_Mp=function(_Mq){return new F(function(){return _l6("main.hs:93:11-33|[t1, t2, t3]");});},_Mr=new T(function(){return B(_Mp(_));}),_Ms=function(_Mt){var _Mu=E(_Mt);return new F(function(){return Math.sin(_Mu+_Mu);});},_Mv=function(_Mw){return new F(function(){return _l6("main.hs:92:11-42|[s1, s2, s3]");});},_Mx=new T(function(){return B(_Mv(_));}),_My=function(_Mz){return new F(function(){return _l6("main.hs:38:5-34|[a, b, c]");});},_MA=new T(function(){return B(_My(_));}),_MB=new T(function(){return B(_6t(_La,1));}),_MC=new T(function(){return B(_6t(_La,2));}),_MD=function(_ME,_MF){var _MG=E(_ME),_MH=E(_MF);if(E(_MG.a)!=E(_MH.a)){return false;}else{return new F(function(){return _eM(_MG.b,_MH.b);});}},_MI=new T1(0,10),_MJ=32,_MK=5,_ML=function(_MM,_MN){var _MO=E(_MM);return new T2(0,_MO,new T(function(){var _MP=B(_ML(B(_9l(_MO,_MN)),_MN));return new T2(1,_MP.a,_MP.b);}));},_MQ=new T1(0,0),_MR=new T1(0,1),_MS=new T(function(){var _MT=B(_ML(_MQ,_MR));return new T2(1,_MT.a,_MT.b);}),_MU=new T(function(){return B(unCStr("I[C]"));}),_MV=new T2(1,_MU,_S),_MW=new T(function(){return B(unCStr("I[B]"));}),_MX=new T2(1,_MW,_MV),_MY=new T(function(){return B(unCStr("I[A]"));}),_MZ=new T2(1,_MY,_MX),_N0=new T(function(){return B(unCStr("H"));}),_N1=new T2(1,_N0,_MZ),_N2=new T(function(){return B(unCStr("I"));}),_N3=new T2(1,_N2,_N1),_N4=new T(function(){return B(unCStr("O"));}),_N5=new T2(1,_N4,_N3),_N6=new T(function(){return B(unCStr("G"));}),_N7=new T2(1,_N6,_N5),_N8="globalAlpha",_N9=function(_Na,_Nb){var _Nc=new T(function(){return String(E(_Na));});return function(_Nd,_){var _Ne=E(_Nd),_Nf=E(_N8),_Ng=__app2(E(_KN),_Ne,_Nf),_Nh=E(_KO),_Ni=__app3(_Nh,_Ne,_Nf,E(_Nc)),_Nj=B(A2(_Nb,_Ne,_)),_Nk=String(_Ng),_Nl=__app3(_Nh,_Ne,_Nf,_Nk);return new F(function(){return _Ij(_);});};},_Nm=new T(function(){return B(unCStr("tail"));}),_Nn=new T(function(){return B(_m8(_Nm));}),_No=function(_Np){return E(E(_Np).a);},_Nq=function(_Nr){return E(E(_Nr).a);},_Ns=function(_Nt){return E(E(_Nt).b);},_Nu=new T(function(){return eval("(function(t,f){window.setInterval(f,t);})");}),_Nv=new T(function(){return eval("(function(t,f){window.setTimeout(f,t);})");}),_Nw=function(_Nx){return E(E(_Nx).b);},_Ny=function(_Nz){return E(E(_Nz).b);},_NA=function(_NB,_NC,_ND){var _NE=B(_No(_NB)),_NF=new T(function(){return B(_Nw(_NE));}),_NG=function(_NH){var _NI=function(_){var _NJ=E(_NC);if(!_NJ._){var _NK=B(A1(_NH,_4s)),_NL=__createJSFunc(0,function(_){var _NM=B(A1(_NK,_));return _3a;}),_NN=__app2(E(_Nv),_NJ.a,_NL);return new T(function(){var _NO=Number(_NN),_NP=jsTrunc(_NO);return new T2(0,_NP,E(_NJ));});}else{var _NQ=B(A1(_NH,_4s)),_NR=__createJSFunc(0,function(_){var _NS=B(A1(_NQ,_));return _3a;}),_NT=__app2(E(_Nu),_NJ.a,_NR);return new T(function(){var _NU=Number(_NT),_NV=jsTrunc(_NU);return new T2(0,_NV,E(_NJ));});}};return new F(function(){return A1(_NF,_NI);});},_NW=new T(function(){return B(A2(_Ny,_NB,function(_NX){return E(_ND);}));});return new F(function(){return A3(_Ns,B(_Nq(_NE)),_NW,_NG);});},_NY=new T(function(){return B(unCStr("True"));}),_NZ=new T(function(){return B(unCStr("False"));}),_O0=function(_O1){return E(E(_O1).g);},_O2=new T(function(){return B(unCStr("maximum"));}),_O3=new T(function(){return B(_m8(_O2));}),_O4=function(_O5,_O6){var _O7=E(_O6);if(!_O7._){return E(_O3);}else{var _O8=new T(function(){return B(_O0(_O5));}),_O9=function(_Oa,_Ob){while(1){var _Oc=E(_Oa);if(!_Oc._){return E(_Ob);}else{var _Od=B(A2(_O8,E(_Ob),_Oc.a));_Oa=_Oc.b;_Ob=_Od;continue;}}};return new F(function(){return _O9(_O7.b,_O7.a);});}},_Oe=function(_Of){return new F(function(){return _rE(_Of,0);});},_Og=new T(function(){return B(_l9(_Oe,_N7));}),_Oh=function(_Oi,_Oj,_Ok,_Ol,_Om,_){var _On=rMV(_Ol),_Oo=_On,_Op=E(_Om),_Oq=rMV(_Op),_Or=_Oq,_Os=E(_Oi),_Ot=_Os.a,_Ou=__app1(E(_Ku),_Os.b),_Ov=function(_Ow,_Ox,_){while(1){var _Oy=B((function(_Oz,_OA,_){var _OB=E(_Oz);if(!_OB._){return _4s;}else{var _OC=function(_OD,_){var _OE=E(_OB.a);return new F(function(){return _Io(E(_OE.a),E(_OE.b),5,E(_OD),_);});},_OF=B(A(_KP,[_L9,function(_OG,_){return new F(function(){return _Ix(_OC,E(_OG),_);});},_OA,_])),_OH=_OA;_Ow=_OB.b;_Ox=_OH;return __continue;}})(_Ow,_Ox,_));if(_Oy!=__continue){return _Oy;}}},_OI=B(_Ov(_Oo,_Ot,_)),_OJ=B(_rE(_Oo,0)),_OK=function(_){var _OL=function(_){var _OM=B(A(_NA,[_5z,_MI,function(_ON,_){var _OO=E(_ON),_OP=E(_OO.a);return new F(function(){return _Oh(_Os,_OP.a,_OP.b,E(_OO.b),_OO.c,_);});},new T3(0,new T2(0,_Oj,_Ok),_Ol,_Op),_]));return new T2(0,_4s,new T(function(){return E(E(_OM).b);}));};if(E(_OJ)==3){var _OQ=new T(function(){return B(_6t(_Oo,2));}),_OR=new T(function(){return B(_6t(_Oo,1));}),_OS=new T(function(){return B(_6t(_Oo,0));}),_OT=new T(function(){var _OU=B(_JE(new T3(0,_OS,_OR,_OQ)));if(!_OU._){return E(_MA);}else{var _OV=E(_OU.b);if(!_OV._){return E(_MA);}else{var _OW=E(_OV.b);if(!_OW._){return E(_MA);}else{if(!E(_OW.b)._){var _OX=E(_OU.a),_OY=E(_OV.a),_OZ=E(_OW.a),_P0=_OY-_OZ;if(_P0!=0){if(_P0<=0){if( -_P0>=_OX+1.0e-9){return new T0(1);}else{if(_OX>=_OY+_OZ+1.0e-9){return new T0(1);}else{return new T3(0,_OS,_OR,_OQ);}}}else{if(_P0>=_OX+1.0e-9){return new T0(1);}else{if(_OX>=_OY+_OZ+1.0e-9){return new T0(1);}else{return new T3(0,_OS,_OR,_OQ);}}}}else{if(0>=_OX+1.0e-9){return new T0(1);}else{if(_OX>=_OY+_OZ+1.0e-9){return new T0(1);}else{return new T3(0,_OS,_OR,_OQ);}}}}else{return E(_MA);}}}}}),_P1=new T(function(){return B(_J5(_OT));}),_P2=new T(function(){var _P3=B(_l9(_Ms,_P1));if(!_P3._){return E(_Mx);}else{var _P4=E(_P3.b);if(!_P4._){return E(_Mx);}else{var _P5=E(_P4.b);if(!_P5._){return E(_Mx);}else{if(!E(_P5.b)._){return new T3(0,_P3.a,_P4.a,_P5.a);}else{return E(_Mx);}}}}}),_P6=new T(function(){var _P7=B(_JE(_OT));if(!_P7._){return E(_Mo);}else{var _P8=E(_P7.b);if(!_P8._){return E(_Mo);}else{var _P9=E(_P8.b);if(!_P9._){return E(_Mo);}else{if(!E(_P9.b)._){return new T3(0,_P7.a,_P8.a,_P9.a);}else{return E(_Mo);}}}}}),_Pa=new T(function(){return E(E(_P6).a);}),_Pb=new T(function(){return E(E(_P6).b);}),_Pc=new T(function(){return E(E(_P6).c);}),_Pd=new T(function(){var _Pe=B(_l9(_dp,_P1));if(!_Pe._){return E(_Mr);}else{var _Pf=E(_Pe.b);if(!_Pf._){return E(_Mr);}else{var _Pg=E(_Pf.b);if(!_Pg._){return E(_Mr);}else{if(!E(_Pg.b)._){return new T3(0,_Pe.a,_Pf.a,_Pg.a);}else{return E(_Mr);}}}}}),_Ph=new T2(1,_Ml,new T2(1,new T3(0,new T(function(){return E(E(_P2).a);}),new T(function(){return E(E(_P2).b);}),new T(function(){return E(E(_P2).c);})),new T2(1,new T3(0,_Pa,_Pb,_Pc),new T2(1,new T3(0,new T(function(){return E(E(_Pd).a);}),new T(function(){return E(E(_Pd).b);}),new T(function(){return E(E(_Pd).c);})),new T2(1,new T3(0,new T(function(){return  -E(_Pa);}),_Pb,_Pc),new T2(1,new T3(0,_Pa,new T(function(){return  -E(_Pb);}),_Pc),new T2(1,new T3(0,_Pa,_Pb,new T(function(){return  -E(_Pc);})),_S))))))),_Pi=function(_Pj){var _Pk=E(_OT);if(!_Pk._){var _Pl=E(_Pj),_Pm=_Pl.a,_Pn=_Pl.b,_Po=_Pl.c,_Pp=E(_Pk.a),_Pq=E(_Pk.b),_Pr=E(_Pk.c),_Ps=new T(function(){return 1/(E(_Pm)+E(_Pn)+E(_Po));});return new T2(0,new T(function(){return E(_Ps)*(E(_Pm)*E(_Pp.a)+E(_Pn)*E(_Pq.a)+E(_Po)*E(_Pr.a));}),new T(function(){return E(_Ps)*(E(_Pm)*E(_Pp.b)+E(_Pn)*E(_Pq.b)+E(_Po)*E(_Pr.b));}));}else{return E(_Lx);}},_Pt=B(_l9(_Pi,_Ph)),_Pu=function(_Pv,_Pw,_Px,_){while(1){var _Py=B((function(_Pz,_PA,_PB,_){var _PC=E(_Pz);if(!_PC._){return _4s;}else{var _PD=E(_PA);if(!_PD._){return _4s;}else{var _PE=function(_PF,_){var _PG=E(_PC.a);return new F(function(){return _Io(E(_PG.a),E(_PG.b),5,E(_PF),_);});},_PH=B(A(_KP,[_PD.a,function(_PI,_){return new F(function(){return _Ix(_PE,E(_PI),_);});},_PB,_])),_PJ=_PB;_Pv=_PC.b;_Pw=_PD.b;_Px=_PJ;return __continue;}}})(_Pv,_Pw,_Px,_));if(_Py!=__continue){return _Py;}}},_PK=function(_PL,_PM,_PN,_PO,_){var _PP=E(_PL);if(!_PP._){return _4s;}else{var _PQ=function(_PR,_){var _PS=E(_PP.a);return new F(function(){return _Io(E(_PS.a),E(_PS.b),5,E(_PR),_);});},_PT=B(A(_KP,[_PM,function(_PU,_){return new F(function(){return _Ix(_PQ,E(_PU),_);});},_PO,_]));return new F(function(){return _Pu(_PP.b,_PN,_PO,_);});}},_PV=B(_PK(_Pt,_L9,_Kt,_Ot,_)),_PW=new T(function(){var _PX=new T(function(){var _PY=new T(function(){var _PZ=B(_6t(_Pt,0)),_Q0=B(_6t(_Pt,1)),_Q1=B(_IS(_5A,_5A,_Oj,_Ok,E(_PZ.a),_PZ.b,E(_Q0.a),_Q0.b));return new T2(0,_Q1.a,_Q1.b);}),_Q2=new T(function(){return E(E(_PY).a);}),_Q3=new T(function(){return E(E(_PY).b);}),_Q4=function(_Q5,_){return new F(function(){return _Lz(new T2(1,_Q2,new T2(1,_Q3,_S)),_Q5,_);});};return B(_KP(_Mh,function(_Q6,_){return new F(function(){return _IE(_Q4,E(_Q6),_);});}));}),_Q7=new T(function(){var _Q8=function(_Q9,_Qa){var _Qb=E(_Q9);if(!_Qb._){return E(_Ib);}else{var _Qc=E(_Qa);if(!_Qc._){return E(_Ib);}else{var _Qd=new T(function(){return B(_Q8(_Qb.b,_Qc.b));}),_Qe=new T(function(){var _Qf=new T(function(){var _Qg=E(_Qb.a),_Qh=E(_Qc.a),_Qi=B(_IS(_5A,_5A,_Oj,_Ok,E(_Qg.a),_Qg.b,E(_Qh.a),_Qh.b));return new T2(0,_Qi.a,_Qi.b);}),_Qj=new T(function(){return E(E(_Qf).a);}),_Qk=new T(function(){return E(E(_Qf).b);}),_Ql=function(_Qm,_){return new F(function(){return _Lz(new T2(1,_Qj,new T2(1,_Qk,_S)),_Qm,_);});};return B(_KP(_L9,function(_Qn,_){return new F(function(){return _IE(_Ql,E(_Qn),_);});}));});return function(_Qo,_){var _Qp=B(A2(_Qe,_Qo,_));return new F(function(){return A2(_Qd,_Qo,_);});};}}},_Qq=new T(function(){var _Qr=B(_q(_Oo,new T2(1,new T(function(){var _Qs=E(_Oo);if(!_Qs._){return E(_JD);}else{return E(_Qs.a);}}),_S)));if(!_Qr._){return E(_Nn);}else{return E(_Qr.b);}},1);return B(_Q8(_Oo,_Qq));}),_Qt=new T(function(){var _Qu=new T(function(){return B(_6t(_Pt,1));}),_Qv=new T(function(){return B(_JW(_OT));}),_Qw=function(_4Y,_){return new F(function(){return _Kv(_Qu,_Qv,_4Y,_);});},_Qx=new T(function(){var _Qy=new T(function(){return B(_6t(_Pt,1));}),_Qz=new T(function(){var _QA=E(_OS),_QB=E(_OR);return new T2(0,new T(function(){return 0.5*(E(_QA.a)+E(_QB.a));}),new T(function(){return 0.5*(E(_QA.b)+E(_QB.b));}));}),_QC=new T(function(){var _QD=E(_OR),_QE=E(_OQ);return new T2(0,new T(function(){return 0.5*(E(_QD.a)+E(_QE.a));}),new T(function(){return 0.5*(E(_QD.b)+E(_QE.b));}));}),_QF=new T(function(){var _QG=E(_OQ),_QH=E(_OS);return new T2(0,new T(function(){return 0.5*(E(_QG.a)+E(_QH.a));}),new T(function(){return 0.5*(E(_QG.b)+E(_QH.b));}));}),_QI=function(_QJ,_){var _QK=B(_Lz(new T2(1,_Qy,new T2(1,_Qz,_S)),_QJ,_)),_QL=B(_Lz(new T2(1,_Qy,new T2(1,_QC,_S)),_QJ,_));return new F(function(){return _Lz(new T2(1,_Qy,new T2(1,_QF,_S)),_QJ,_);});};return B(_N9(_Mi,function(_QM,_){return new F(function(){return _IE(_QI,E(_QM),_);});}));});return B(_KP(_MB,function(_QN,_){var _QO=E(_QN),_QP=B(_IE(_Qw,_QO,_));if(!E(_Or)){return _4s;}else{return new F(function(){return A2(_Qx,_QO,_);});}}));}),_QQ=new T(function(){var _QR=new T(function(){return B(_6t(_Pt,2));}),_QS=new T(function(){return B(_K5(_OT));}),_QT=function(_4Y,_){return new F(function(){return _Kv(_QR,_QS,_4Y,_);});},_QU=new T(function(){var _QV=new T(function(){return B(_6t(_Pt,2));}),_QW=function(_QX,_){var _QY=B(_Lz(new T2(1,_QV,new T2(1,_OS,_S)),_QX,_)),_QZ=B(_Lz(new T2(1,_QV,new T2(1,_OR,_S)),_QX,_));return new F(function(){return _Lz(new T2(1,_QV,new T2(1,_OQ,_S)),_QX,_);});};return B(_N9(_Mi,function(_R0,_){return new F(function(){return _IE(_QW,E(_R0),_);});}));});return B(_KP(_MC,function(_R1,_){var _R2=E(_R1),_R3=B(_IE(_QT,_R2,_));if(!E(_Or)){return _4s;}else{return new F(function(){return A2(_QU,_R2,_);});}}));}),_R4=new T(function(){var _R5=new T(function(){return B(_6t(_Pt,2));}),_R6=function(_R7){var _R8=E(_R7);if(!_R8._){return E(_Ib);}else{var _R9=_R8.a,_Ra=new T(function(){var _Rb=new T(function(){return B(_6t(_Pt,E(_R9)));}),_Rc=new T(function(){var _Rd=B(_6t(_Ph,E(_R9))),_Re=B(_IK(_OT)),_Rf=(_Re+_Re)/(E(_Rd.a)+E(_Rd.b)+E(_Rd.c));if(_Rf!=0){if(_Rf<=0){return  -_Rf;}else{return _Rf;}}else{return E(_cq);}}),_Rg=function(_4Y,_){return new F(function(){return _Kv(_Rb,_Rc,_4Y,_);});},_Rh=new T(function(){if(!E(_Or)){return E(_Ib);}else{var _Ri=new T(function(){return B(_6t(_Pt,E(_R9)));}),_Rj=function(_Rk,_Rl,_){while(1){var _Rm=E(_Rk);if(!_Rm._){return _4s;}else{var _Rn=B(_Lz(new T2(1,_Ri,new T2(1,_Rm.a,_S)),_Rl,_));_Rk=_Rm.b;continue;}}},_Ro=new T(function(){return B(_Lb(_MD,new T(function(){return B(_6t(_Oo,E(_R9)-4|0));}),_Oo));}),_Rp=function(_4Y,_){return new F(function(){return _Rj(new T2(1,_R5,_Ro),_4Y,_);});};return B(_N9(_Mi,function(_Rq,_){return new F(function(){return _IE(_Rp,E(_Rq),_);});}));}});return B(_KP(new T(function(){return B(_6t(_La,E(_R9)));},1),function(_Rr,_){var _Rs=E(_Rr),_Rt=B(_IE(_Rg,_Rs,_));return new F(function(){return A2(_Rh,_Rs,_);});}));}),_Ru=new T(function(){return B(_R6(_R8.b));});return function(_Rv,_){var _Rw=B(A2(_Ra,_Rv,_));return new F(function(){return A2(_Ru,_Rv,_);});};}};return B(_R6(_M8));});return B(_LU(_Mj,function(_Rx,_){var _Ry=B(A2(_Qt,_Rx,_)),_Rz=B(A2(_QQ,_Rx,_)),_RA=B(A2(_R4,_Rx,_)),_RB=B(A2(_PX,_Rx,_));return new F(function(){return A2(_Q7,_Rx,_);});}));}),_RC=B(A(_N9,[_Mk,_PW,_Ot,_])),_RD=new T(function(){var _RE=new T(function(){var _RF=new T(function(){return B(_Kd(_MK,_Me,new T(function(){return B(_I9(_OT));},1)));}),_RG=new T(function(){return B(_HD(new T2(1,_Pa,new T2(1,_Pb,new T2(1,_Pc,_S)))));}),_RH=new T(function(){var _RI=new T(function(){return B(_IK(_OT));});return B(_Ho(_sD,new T2(1,new T2(0,function(_Ht){return new F(function(){return _6d(_RI,_Ht);});},function(_Ht){return new F(function(){return _sz(_RI,_Ht);});}),_S)));}),_RJ=new T(function(){var _RK=new T(function(){return B(_JW(_OT));});return B(_Ho(_sD,new T2(1,new T2(0,function(_Ht){return new F(function(){return _6d(_RK,_Ht);});},function(_Ht){return new F(function(){return _sz(_RK,_Ht);});}),_S)));}),_RL=new T(function(){var _RM=new T(function(){return B(_K5(_OT));});return B(_Ho(_sD,new T2(1,new T2(0,function(_Ht){return new F(function(){return _6d(_RM,_Ht);});},function(_Ht){return new F(function(){return _sz(_RM,_Ht);});}),_S)));}),_RN=new T(function(){var _RO=new T(function(){return B(_l9(function(_RP){var _RQ=B(_6t(_Ph,E(_RP))),_RR=B(_IK(_OT)),_RS=(_RR+_RR)/(E(_RQ.a)+E(_RQ.b)+E(_RQ.c));return (_RS!=0)?(_RS<=0)? -_RS:_RS:E(_5A);},_M8));},1);return B(_HD(_RO));}),_RT=new T2(1,new T2(0,_Mc,_RH),new T2(1,new T2(0,_Mb,_RJ),new T2(1,new T2(0,_Ma,_RL),new T2(1,new T2(0,_M9,_RN),new T2(1,new T2(0,_M7,new T(function(){if(!E(_Or)){return E(_NZ);}else{return E(_NY);}})),_S))))),_RU=new T(function(){var _RV=function(_RW){var _RX=E(_RW);return (_RX._==0)?E(_Og):new T2(1,new T(function(){return B(_rE(E(_RX.a).a,0));}),new T(function(){return B(_RV(_RX.b));}));},_RY=function(_RZ,_S0,_S1){return new T2(1,new T(function(){return B(_rE(_RZ,0));}),new T(function(){return B(_RV(_S1));}));};return B(_O4(_6a,B(_RY(_Md,_RG,_RT))));}),_S2=new T(function(){var _S3=new T(function(){return E(_RU)+1|0;}),_S4=function(_S5,_S6){var _S7=E(_S5);if(!_S7._){return E(_Ib);}else{var _S8=E(_S6);if(!_S8._){return E(_Ib);}else{var _S9=new T(function(){return B(_S4(_S7.b,_S8.b));}),_Sa=new T(function(){var _Sb=E(_S8.a),_Sc=_Sb.a,_Sd=_Sb.b,_Se=new T(function(){var _Sf=new T(function(){var _Sg=new T(function(){var _Sh=E(_S3)-B(_rE(_Sc,0))|0;if(0>=_Sh){return E(_Sd);}else{var _Si=function(_Sj){var _Sk=E(_Sj);return (_Sk==1)?E(new T2(1,_MJ,_Sd)):new T2(1,_MJ,new T(function(){return B(_Si(_Sk-1|0));}));};return B(_Si(_Sh));}});return B(unAppCStr(":",_Sg));},1);return B(_q(_Sc,_Sf));},1);return B(_Kd(_MK,new T(function(){return 50+B(_cC(_S7.a))*25;}),_Se));});return function(_Sl,_){var _Sm=B(A2(_Sa,_Sl,_));return new F(function(){return A2(_S9,_Sl,_);});};}}},_Sn=function(_So,_Sp,_Sq,_Sr){var _Ss=E(_So);if(!_Ss._){return E(_Ib);}else{var _St=new T(function(){return B(_S4(_Ss.b,_Sr));}),_Su=new T(function(){var _Sv=new T(function(){var _Sw=new T(function(){var _Sx=new T(function(){var _Sy=E(_S3)-B(_rE(_Sp,0))|0;if(0>=_Sy){return E(_Sq);}else{var _Sz=function(_SA){var _SB=E(_SA);return (_SB==1)?E(new T2(1,_MJ,_Sq)):new T2(1,_MJ,new T(function(){return B(_Sz(_SB-1|0));}));};return B(_Sz(_Sy));}});return B(unAppCStr(":",_Sx));},1);return B(_q(_Sp,_Sw));},1);return B(_Kd(_MK,new T(function(){return 50+B(_cC(_Ss.a))*25;}),_Sv));});return function(_SC,_){var _SD=B(A2(_Su,_SC,_));return new F(function(){return A2(_St,_SC,_);});};}};return B(_Sn(_MS,_Md,_RG,_RT));}),_SE=new T(function(){var _SF=B(_rE(_Pt,0))-1|0;if(0<=_SF){var _SG=new T(function(){return 50+B(_rE(new T2(1,new T2(0,_Md,_RG),_RT),0))*25;}),_SH=new T(function(){return E(_RU)+1|0;}),_SI=function(_SJ){var _SK=new T(function(){var _SL=new T(function(){var _SM=new T(function(){var _SN=new T(function(){var _SO=new T(function(){var _SP=E(_SH)-B(_rE(B(_6t(_N7,_SJ)),0))|0;if(0>=_SP){var _SQ=B(_6t(_Pt,_SJ));return B(_Ie(_SQ.a,_SQ.b));}else{var _SR=new T(function(){var _SS=B(_6t(_Pt,_SJ));return B(_Ie(_SS.a,_SS.b));}),_ST=function(_SU){var _SV=E(_SU);return (_SV==1)?E(new T2(1,_MJ,_SR)):new T2(1,_MJ,new T(function(){return B(_ST(_SV-1|0));}));};return B(_ST(_SP));}});return B(unAppCStr(":",_SO));},1);return B(_q(B(_6t(_N7,_SJ)),_SN));},1);return B(_Kd(_MK,new T(function(){return E(_SG)+_SJ*25;}),_SM));});return B(_KP(new T(function(){return B(_6t(_La,_SJ));},1),_SL));}),_SW=new T(function(){if(_SJ!=_SF){return B(_SI(_SJ+1|0));}else{return E(_Ib);}});return function(_SX,_){var _SY=B(A2(_SK,_SX,_));return new F(function(){return A2(_SW,_SX,_);});};};return B(_SI(0));}else{return E(_Ib);}});return B(_Lj(_Mf,function(_SZ,_){var _T0=B(A2(_RF,_SZ,_)),_T1=B(A2(_S2,_SZ,_));return new F(function(){return A2(_SE,_SZ,_);});}));});return B(_KP(_L9,_RE));}),_T2=B(A(_N9,[_Mg,_RD,_Ot,_]));return new F(function(){return _OL(_);});}else{return new F(function(){return _OL(_);});}};if(_OJ<2){return new F(function(){return _OK(_);});}else{var _T3=function(_T4,_T5,_T6,_){while(1){var _T7=B((function(_T8,_T9,_Ta,_){var _Tb=E(_T8);if(!_Tb._){return _4s;}else{var _Tc=E(_T9);if(!_Tc._){return _4s;}else{var _Td=function(_4Y,_){return new F(function(){return _LP(_Tb.a,_Tc.a,_4Y,_);});},_Te=B(A(_KP,[_L9,function(_Tf,_){return new F(function(){return _IE(_Td,E(_Tf),_);});},_Ta,_])),_Tg=_Ta;_T4=_Tb.b;_T5=_Tc.b;_T6=_Tg;return __continue;}}})(_T4,_T5,_T6,_));if(_T7!=__continue){return _T7;}}},_Th=new T(function(){var _Ti=B(_q(_Oo,new T2(1,new T(function(){var _Tj=E(_Oo);if(!_Tj._){return E(_JD);}else{return E(_Tj.a);}}),_S)));if(!_Ti._){return E(_Nn);}else{return E(_Ti.b);}},1),_Tk=B(_T3(_Oo,_Th,_Ot,_));return new F(function(){return _OK(_);});}},_Tl=2,_Tm=2,_Tn=new T(function(){return eval("document.body");}),_To=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_Tp=function(_Tq,_Tr){var _Ts=function(_){var _Tt=__app1(E(_To),E(_Tr)),_Tu=__eq(_Tt,E(_3a));return (E(_Tu)==0)?new T1(1,_Tt):_2N;};return new F(function(){return A2(_Nw,_Tq,_Ts);});},_Tv=function(_Tw){return new F(function(){return fromJSStr(E(_Tw));});},_Tx=function(_Ty){return E(E(_Ty).a);},_Tz=function(_TA,_TB,_TC,_TD){var _TE=new T(function(){var _TF=function(_){var _TG=__app2(E(_KN),B(A2(_Tx,_TA,_TC)),E(_TD));return new T(function(){return String(_TG);});};return E(_TF);});return new F(function(){return A2(_Nw,_TB,_TE);});},_TH=function(_TI){return E(E(_TI).d);},_TJ=function(_TK,_TL,_TM,_TN){var _TO=B(_Nq(_TL)),_TP=new T(function(){return B(_TH(_TO));}),_TQ=function(_TR){return new F(function(){return A1(_TP,new T(function(){return B(_Tv(_TR));}));});},_TS=new T(function(){return B(_Tz(_TK,_TL,_TM,new T(function(){return toJSStr(E(_TN));},1)));});return new F(function(){return A3(_Ns,_TO,_TS,_TQ);});},_TT=function(_TU){return E(_TU);},_TV=new T(function(){return B(unCStr("Canvas could not be found!"));}),_TW=new T(function(){return B(err(_TV));}),_TX=new T(function(){return B(unCStr("Canvas ID could not be found!"));}),_TY=new T(function(){return B(err(_TX));}),_TZ=new T(function(){return B(err(_sI));}),_U0=new T(function(){return B(err(_sK));}),_U1=function(_U2,_U3){var _U4=function(_U5,_U6){var _U7=function(_U8){return new F(function(){return A1(_U6,new T(function(){return  -E(_U8);}));});},_U9=new T(function(){return B(_DI(function(_Ua){return new F(function(){return A3(_U2,_Ua,_U5,_U7);});}));}),_Ub=function(_Uc){return E(_U9);},_Ud=function(_Ue){return new F(function(){return A2(_Cp,_Ue,_Ub);});},_Uf=new T(function(){return B(_DI(function(_Ug){var _Uh=E(_Ug);if(_Uh._==4){var _Ui=E(_Uh.a);if(!_Ui._){return new F(function(){return A3(_U2,_Uh,_U5,_U6);});}else{if(E(_Ui.a)==45){if(!E(_Ui.b)._){return E(new T1(1,_Ud));}else{return new F(function(){return A3(_U2,_Uh,_U5,_U6);});}}else{return new F(function(){return A3(_U2,_Uh,_U5,_U6);});}}}else{return new F(function(){return A3(_U2,_Uh,_U5,_U6);});}}));}),_Uj=function(_Uk){return E(_Uf);};return new T1(1,function(_Ul){return new F(function(){return A2(_Cp,_Ul,_Uj);});});};return new F(function(){return _Ez(_U4,_U3);});},_Um=new T(function(){return 1/0;}),_Un=function(_Uo,_Up){return new F(function(){return A1(_Up,_Um);});},_Uq=new T(function(){return 0/0;}),_Ur=function(_Us,_Ut){return new F(function(){return A1(_Ut,_Uq);});},_Uu=new T(function(){return B(unCStr("NaN"));}),_Uv=new T(function(){return B(unCStr("Infinity"));}),_Uw=function(_Ux,_Uy){while(1){var _Uz=E(_Ux);if(!_Uz._){var _UA=E(_Uz.a);if(_UA==(-2147483648)){_Ux=new T1(1,I_fromInt(-2147483648));continue;}else{var _UB=E(_Uy);if(!_UB._){return new T1(0,_UA%_UB.a);}else{_Ux=new T1(1,I_fromInt(_UA));_Uy=_UB;continue;}}}else{var _UC=_Uz.a,_UD=E(_Uy);return (_UD._==0)?new T1(1,I_rem(_UC,I_fromInt(_UD.a))):new T1(1,I_rem(_UC,_UD.a));}}},_UE=function(_UF,_UG){if(!B(_9a(_UG,_jf))){return new F(function(){return _Uw(_UF,_UG);});}else{return E(_95);}},_UH=function(_UI,_UJ){while(1){if(!B(_9a(_UJ,_jf))){var _UK=_UJ,_UL=B(_UE(_UI,_UJ));_UI=_UK;_UJ=_UL;continue;}else{return E(_UI);}}},_UM=function(_UN){var _UO=E(_UN);if(!_UO._){var _UP=E(_UO.a);return (_UP==(-2147483648))?E(_ci):(_UP<0)?new T1(0, -_UP):E(_UO);}else{var _UQ=_UO.a;return (I_compareInt(_UQ,0)>=0)?E(_UO):new T1(1,I_negate(_UQ));}},_UR=5,_US=new T(function(){return B(_91(_UR));}),_UT=new T(function(){return die(_US);}),_UU=function(_UV,_UW){if(!B(_9a(_UW,_jf))){var _UX=B(_UH(B(_UM(_UV)),B(_UM(_UW))));return (!B(_9a(_UX,_jf)))?new T2(0,B(_nU(_UV,_UX)),B(_nU(_UW,_UX))):E(_95);}else{return E(_UT);}},_UY=new T(function(){return B(_9a(_jg,_jf));}),_UZ=function(_V0,_V1,_V2){while(1){if(!E(_UY)){if(!B(_9a(B(_Uw(_V1,_jg)),_jf))){if(!B(_9a(_V1,_gn))){var _V3=B(_iH(_V0,_V0)),_V4=B(_nU(B(_bE(_V1,_gn)),_jg)),_V5=B(_iH(_V0,_V2));_V0=_V3;_V1=_V4;_V2=_V5;continue;}else{return new F(function(){return _iH(_V0,_V2);});}}else{var _V3=B(_iH(_V0,_V0)),_V4=B(_nU(_V1,_jg));_V0=_V3;_V1=_V4;continue;}}else{return E(_95);}}},_V6=function(_V7,_V8){while(1){if(!E(_UY)){if(!B(_9a(B(_Uw(_V8,_jg)),_jf))){if(!B(_9a(_V8,_gn))){return new F(function(){return _UZ(B(_iH(_V7,_V7)),B(_nU(B(_bE(_V8,_gn)),_jg)),_V7);});}else{return E(_V7);}}else{var _V9=B(_iH(_V7,_V7)),_Va=B(_nU(_V8,_jg));_V7=_V9;_V8=_Va;continue;}}else{return E(_95);}}},_Vb=function(_Vc,_Vd){if(!B(_9X(_Vd,_jf))){if(!B(_9a(_Vd,_jf))){return new F(function(){return _V6(_Vc,_Vd);});}else{return E(_gn);}}else{return E(_jX);}},_Ve=new T1(0,1),_Vf=new T1(0,0),_Vg=new T1(0,-1),_Vh=function(_Vi){var _Vj=E(_Vi);if(!_Vj._){var _Vk=_Vj.a;return (_Vk>=0)?(E(_Vk)==0)?E(_Vf):E(_9W):E(_Vg);}else{var _Vl=I_compareInt(_Vj.a,0);return (_Vl<=0)?(E(_Vl)==0)?E(_Vf):E(_Vg):E(_9W);}},_Vm=function(_Vn,_Vo,_Vp){while(1){var _Vq=E(_Vp);if(!_Vq._){if(!B(_9X(_Vn,_w9))){return new T2(0,B(_iH(_Vo,B(_Vb(_vZ,_Vn)))),_gn);}else{var _Vr=B(_Vb(_vZ,B(_cj(_Vn))));return new F(function(){return _UU(B(_iH(_Vo,B(_Vh(_Vr)))),B(_UM(_Vr)));});}}else{var _Vs=B(_bE(_Vn,_Ve)),_Vt=B(_9l(B(_iH(_Vo,_vZ)),B(_fi(E(_Vq.a)))));_Vn=_Vs;_Vo=_Vt;_Vp=_Vq.b;continue;}}},_Vu=function(_Vv,_Vw){var _Vx=E(_Vv);if(!_Vx._){var _Vy=_Vx.a,_Vz=E(_Vw);return (_Vz._==0)?_Vy>=_Vz.a:I_compareInt(_Vz.a,_Vy)<=0;}else{var _VA=_Vx.a,_VB=E(_Vw);return (_VB._==0)?I_compareInt(_VA,_VB.a)>=0:I_compare(_VA,_VB.a)>=0;}},_VC=function(_VD){var _VE=E(_VD);if(!_VE._){var _VF=_VE.b;return new F(function(){return _UU(B(_iH(B(_wa(new T(function(){return B(_fi(E(_VE.a)));}),new T(function(){return B(_rE(_VF,0));},1),B(_l9(_w0,_VF)))),_Ve)),_Ve);});}else{var _VG=_VE.a,_VH=_VE.c,_VI=E(_VE.b);if(!_VI._){var _VJ=E(_VH);if(!_VJ._){return new F(function(){return _UU(B(_iH(B(_wr(_vZ,_VG)),_Ve)),_Ve);});}else{var _VK=_VJ.a;if(!B(_Vu(_VK,_w9))){var _VL=B(_Vb(_vZ,B(_cj(_VK))));return new F(function(){return _UU(B(_iH(B(_wr(_vZ,_VG)),B(_Vh(_VL)))),B(_UM(_VL)));});}else{return new F(function(){return _UU(B(_iH(B(_iH(B(_wr(_vZ,_VG)),B(_Vb(_vZ,_VK)))),_Ve)),_Ve);});}}}else{var _VM=_VI.a,_VN=E(_VH);if(!_VN._){return new F(function(){return _Vm(_w9,B(_wr(_vZ,_VG)),_VM);});}else{return new F(function(){return _Vm(_VN.a,B(_wr(_vZ,_VG)),_VM);});}}}},_VO=function(_VP,_VQ){while(1){var _VR=E(_VQ);if(!_VR._){return __Z;}else{if(!B(A1(_VP,_VR.a))){return E(_VR);}else{_VQ=_VR.b;continue;}}}},_VS=0,_VT=function(_VU){return new F(function(){return _5B(_VS,_VU);});},_VV=new T2(0,E(_w9),E(_gn)),_VW=new T1(1,_VV),_VX=new T1(0,-2147483648),_VY=new T1(0,2147483647),_VZ=function(_W0,_W1,_W2){var _W3=E(_W2);if(!_W3._){return new T1(1,new T(function(){var _W4=B(_VC(_W3));return new T2(0,E(_W4.a),E(_W4.b));}));}else{var _W5=E(_W3.c);if(!_W5._){return new T1(1,new T(function(){var _W6=B(_VC(_W3));return new T2(0,E(_W6.a),E(_W6.b));}));}else{var _W7=_W5.a;if(!B(_9O(_W7,_VY))){if(!B(_9X(_W7,_VX))){var _W8=function(_W9){var _Wa=_W9+B(_9i(_W7))|0;return (_Wa<=(E(_W1)+3|0))?(_Wa>=(E(_W0)-3|0))?new T1(1,new T(function(){var _Wb=B(_VC(_W3));return new T2(0,E(_Wb.a),E(_Wb.b));})):E(_VW):__Z;},_Wc=B(_VO(_VT,_W3.a));if(!_Wc._){var _Wd=E(_W3.b);if(!_Wd._){return E(_VW);}else{var _We=B(_aB(_VT,_Wd.a));if(!E(_We.b)._){return E(_VW);}else{return new F(function(){return _W8( -B(_rE(_We.a,0)));});}}}else{return new F(function(){return _W8(B(_rE(_Wc,0)));});}}else{return __Z;}}else{return __Z;}}}},_Wf=function(_Wg){var _Wh=E(_Wg);switch(_Wh._){case 3:var _Wi=_Wh.a;return (!B(_tB(_Wi,_Uv)))?(!B(_tB(_Wi,_Uu)))?E(_Fa):E(_Ur):E(_Un);case 5:var _Wj=B(_VZ(_ee,_ed,_Wh.a));if(!_Wj._){return E(_Un);}else{var _Wk=new T(function(){var _Wl=E(_Wj.a);return B(_cr(_Wl.a,_Wl.b));});return function(_Wm,_Wn){return new F(function(){return A1(_Wn,_Wk);});};}break;default:return E(_Fa);}},_Wo=new T(function(){return B(A3(_U1,_Wf,_Ef,_Fk));}),_Wp=new T(function(){return B(unCStr("height"));}),_Wq=new T(function(){return B(unCStr("width"));}),_Wr="canvas",_Ws=function(_Wt){return (!E(_Wt))?true:false;},_Wu=function(_Wv){return E(E(_Wv).b);},_Ww=function(_Wx){return E(E(_Wx).a);},_Wy=function(_){return new F(function(){return nMV(_2N);});},_Wz=new T(function(){return B(_36(_Wy));}),_WA=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_WB=function(_WC,_WD,_WE,_WF,_WG,_WH){var _WI=B(_No(_WC)),_WJ=B(_Nq(_WI)),_WK=new T(function(){return B(_Nw(_WI));}),_WL=new T(function(){return B(_TH(_WJ));}),_WM=new T(function(){return B(A2(_Tx,_WD,_WF));}),_WN=new T(function(){return B(A2(_Ww,_WE,_WG));}),_WO=function(_WP){return new F(function(){return A1(_WL,new T3(0,_WN,_WM,_WP));});},_WQ=function(_WR){var _WS=new T(function(){var _WT=new T(function(){var _WU=__createJSFunc(2,function(_WV,_){var _WW=B(A2(E(_WR),_WV,_));return _3a;}),_WX=_WU;return function(_){return new F(function(){return __app3(E(_WA),E(_WM),E(_WN),_WX);});};});return B(A1(_WK,_WT));});return new F(function(){return A3(_Ns,_WJ,_WS,_WO);});},_WY=new T(function(){var _WZ=new T(function(){return B(_Nw(_WI));}),_X0=function(_X1){var _X2=new T(function(){return B(A1(_WZ,function(_){var _=wMV(E(_Wz),new T1(1,_X1));return new F(function(){return A(_Wu,[_WE,_WG,_X1,_]);});}));});return new F(function(){return A3(_Ns,_WJ,_X2,_WH);});};return B(A2(_Ny,_WC,_X0));});return new F(function(){return A3(_Ns,_WJ,_WY,_WQ);});},_X3=function(_){var _X4=B(A3(_Tp,_4q,_Wr,_)),_X5=E(_X4);if(!_X5._){return E(_TY);}else{var _X6=_X5.a,_X7=B(A(_TJ,[_3I,_4q,_X6,_Wq,_])),_X8=B(A(_TJ,[_3I,_4q,_X6,_Wp,_])),_X9=nMV(_S),_Xa=_X9,_Xb=nMV(_kQ),_Xc=_Xb,_Xd=function(_Xe,_){var _Xf=E(E(_Xe).a),_Xg=_Xf.a,_Xh=_Xf.b,_Xi=rMV(_Xa);if(B(_rE(_Xi,0))==3){var _=wMV(_Xa,_S),_Xj=rMV(_Xa),_=wMV(_Xa,new T2(1,new T2(0,new T(function(){return B(_TT(_Xg));}),new T(function(){return B(_TT(_Xh));})),_Xj));return _4s;}else{var _Xk=rMV(_Xa),_=wMV(_Xa,new T2(1,new T2(0,new T(function(){return B(_TT(_Xg));}),new T(function(){return B(_TT(_Xh));})),_Xk));return _4s;}},_Xl=B(A(_WB,[_4r,_3I,_3B,_Tn,_Tm,_Xd,_])),_Xm=function(_Xn,_){if(E(E(_Xn).a)==13){var _Xo=rMV(_Xc),_=wMV(_Xc,new T(function(){return B(_Ws(_Xo));}));return _4s;}else{return _4s;}},_Xp=B(A(_WB,[_4r,_3I,_m,_Tn,_Tl,_Xm,_])),_Xq=E(_X6),_Xr=__app1(E(_3D),_Xq);if(!_Xr){return E(_TW);}else{var _Xs=__app1(E(_3C),_Xq),_Xt=B(_Oh(new T2(0,_Xs,_Xq),new T(function(){var _Xu=B(_Fs(B(_sN(_Wo,_X7))));if(!_Xu._){return E(_TZ);}else{if(!E(_Xu.b)._){return E(_Xu.a);}else{return E(_U0);}}}),new T(function(){var _Xv=B(_Fs(B(_sN(_Wo,_X8))));if(!_Xv._){return E(_TZ);}else{if(!E(_Xv.b)._){return E(_Xv.a);}else{return E(_U0);}}}),_Xa,_Xc,_));return new T(function(){return E(E(_Xt).a);});}}},_Xw=function(_){return new F(function(){return _X3(_);});};
var hasteMain = function() {B(A(_Xw, [0]));};window.onload = hasteMain;