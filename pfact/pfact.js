/*var xhr = new XMLHttpRequest();
xhr.open( "GET", "https://api.tokyometroapp.jp/api/v2/datapoints?rdf:type=odpt:Railway&dc:title=日比谷&acl:consumerKey=cc66ea238085a6851d9efac3ab639b4313b14d1d8f0684bc53bbac3207be0239", false );
xhr.send();
console.log(xhr.response);*/

var cvs = document.getElementById('canvas');
var ctx = cvs.getContext('2d');

var maxSize = 100000;
var primes = [];
var used = [];

for( var i = 0; i <= maxSize; ++i )
  used[i] = false;

function sieve()
{
  for( var i = 2; i <= maxSize; ++i )
  {
    if( !used[i] )
    {
      primes.push( i );

      for( var j = i; j <= maxSize; j += i )
        used[j] = true;
    }
  }
}

sieve();

function pfact( n )
{
  var ret = [];
  var p = 0;

  while( n != 1 )
  {
    while( n % primes[p] == 0 )
    {
      ret.push( primes[p] );
      n /= primes[p];
    }

    ++p;
  }

  return ret.length == 0 ? [1] : ret;
}

function isPow2( n )
{
  if( n == 0 )
    return false;

  while( n % 2 == 0 )
    n /= 2;

  return n == 1;
}

function rec( n, cx, cy, r, sang, sangF, prvP )
{
  if( n == 0 )
    return [];

  var ret = [],
      fs = pfact(n),
      p = fs[fs.length-1],
      r2 = r/(1+Math.sin(2*Math.PI/p/2));

  if( n == 1 )
    ret.push( { x: cx, y: cy, r: r } );
  else
  {
    var ptr = 0;
    while( fs[ptr] == 2 )
      ++ptr;

    if( p == 2 && ptr % 2 == 0 )
      p = 4;

    for( var i = 0; i < p; ++i )
    {
      var theta = 2*Math.PI/p*i+(sangF||prvP!=0&&p==2&&isPow2(n/p)?sang:0)+(prvP==2?Math.PI/2:0)+(p==4?Math.PI/4:0)-Math.PI/2;
      ret = ret.concat( rec( n/p, cx+r2*Math.cos(theta), cy+r2*Math.sin(theta), (p==2?r2:r2*Math.sin(2*Math.PI/p/2)), theta-Math.PI/2, sangF||prvP!=0&&p==2&&isPow2(n/p), p ) );
    }
  }

  return ret;
}

function hsv2rgb( h, s, v )
{
  var hi = Math.floor(h/60), f = h/60-hi;
  var m = v*(1-s/255), n = v*(1-s/255*f), k = v*(1-s/255*(1-f));

  switch( hi )
  {
    case 0:
      return [v,k,m];
    case 1:
      return [n,v,m];
    case 2:
      return [m,v,k];
    case 3:
      return [m,n,v];
    case 4:
      return [k,m,v];
    case 5:
      return [v,m,n];
  }
}

function morph( f, t, d )
{ return f+(t-f)/d; }

var n = 1/*12503*3*3*3*3*3*/, tim = 0;

var circs = [];

function render()
{
  var w = cvs.width, h = cvs.height;

  ++tim;
  n = Math.floor(tim/60)+1;
  if( n > maxSize )
    n = maxSize;

  var tocircs = rec( n, w/2, h/2, Math.min(w/2,h/2)-40, 0, false, 0 ),
      fs = pfact(n);

  if( circs.length != tocircs.length )
    circs.push( { x: w/2, y: h/2, r: tocircs[tocircs.length-1].r } );

  ctx.clearRect( 0, 0, w, h );

  for( var i = 0; i < circs.length; ++i )
  {
    circs[i].x = morph( circs[i].x, tocircs[i].x, 10 );
    circs[i].y = morph( circs[i].y, tocircs[i].y, 10 );
    circs[i].r = morph( circs[i].r, tocircs[i].r, 10 );

    ctx.beginPath();
    var hsv = hsv2rgb( 360/circs.length*i, 180, 240 );
    hsv = hsv.map( Math.floor );
    ctx.fillStyle = "rgb("+hsv[0].toString()+","+hsv[1].toString()+","+hsv[2].toString()+")";
    ctx.arc( circs[i].x, circs[i].y, circs[i].r, 0, 2*Math.PI, true );
    ctx.fill();
  }

  var s = "";
  for( var i = fs.length-1; i >= 0; --i )
  {
    s += fs[i].toString();

    if( i != 0 )
      s += "*";
  }

  ctx.font = "normal "/*+tim%60*30+*/+"100px 'Yu Gothic'";
  ctx.textAlign = "left";
  ctx.fillStyle = "rgba(40,40,40,"/*+((60-tim%60)/60).toFixed(2)+*/+"1.0"+")"
  ctx.fillText( n.toString(), 40, 110 );
  var wid = ctx.measureText(n.toString()).width;
  ctx.font = "normal 30px 'Yu Gothic'";
  ctx.textAlign = "center";
  ctx.fillStyle = "rgb(150,150,150)";
  ctx.fillText( s, 40+wid/2, 160 );
}

setInterval( render, 1000/60 );