var cvs = document.getElementById('canvas');
var ctx = cvs.getContext('2d');

/*for( var i = 0; i < map.length; ++i ) for( var j = 0; j < map[i].length; ++j )
{
  if( map[i][j][0] >= 180 )
    map[i][j][0] -= 180;
  if( map[i][j][0] <= -180 )
    map[i][j][0] += 180;
}*/

function shuffle( array )
{
  var n = array.length, t, i;

  while( n )
  {
    i = Math.floor( Math.random() * n-- );
    t = array[n];
    array[n] = array[i];
    array[i] = t;
  }

  return array;
}

shuffle(city);

var Rad = Math.PI/180.0;

function qNorm( q )
{ return q[0]*q[0]+q[1]*q[1]+q[2]*q[2]+q[3]*q[3]; }

function qScalar( k, q )
{ return [k*q[0], k*q[1], k*q[2], k*q[3]]; }

function qAdd( q1, q2 )
{ return [q1[0]+q2[0], q1[1]+q2[1], q1[2]+q2[2], q1[3]+q2[3]]; }

function qMul( q1, q2 )
{
  var a1 = q1[0], b1 = q1[1], c1 = q1[2], d1 = q1[3];
  var a2 = q2[0], b2 = q2[1], c2 = q2[2], d2 = q2[3];

  return [a1*a2-b1*b2-c1*c2-d1*d2, a1*b2+a2*b1+c1*d2-d1*c2, a1*c2-b1*d2+c1*a2+d1*b2, a1*d2+b1*c2-c1*b2+d1*a2];
}

function qConj( q )
{ return [q[0], -q[1], -q[2], -q[3]]; }

function qInv( q )
{ return qScalar( 1/qNorm(q), qConj(q) ); }

function qPow( q, n )
{
  if( n == -1 )
    return qInv(q);

  var alpha = Math.acos(q[0]), newalpha = alpha*n;
  var q2 = qScalar( Math.sin(newalpha)/Math.sin(alpha), q );
  q2[0] = Math.cos(newalpha);

  return q2;
}

function vec2Q( v )
{ return [0, v[0], v[1], v[2]]; }

function q2Vec( q )
{ return [q[1],q[2],q[3]]; }

function rotQ( u, theta )
{ return [Math.cos(theta/2), Math.sin(theta/2)*u[0], Math.sin(theta/2)*u[1], Math.sin(theta/2)*u[2]]; }

var defQ = rotQ( [0,0,0], 0 );

function rotXQ( theta )
{ return rotQ( [1,0,0], theta ); }

function rotYQ( theta )
{ return rotQ( [0,1,0], theta ); }

function rotZQ( theta )
{ return rotQ( [0,0,1], theta ); }

function applyQ( v, q )
{ return q2Vec( qMul( qMul( q, vec2Q(v) ), qConj(q) ) ); }

function qSlerp( q1, q2, t )
{
  if( qNorm( qAdd( q2, qScalar( -1, q1 ) ) ) > 0.00005 )
    return qMul( qPow( qMul( q2, qInv(q1) ), t ), q1 );
  else 
    return q2;
}

function longlat2xyz( lon, lat )
{
  var theta = (90-lat)*Rad, phi = lon*Rad;

  return [Math.sin(theta)*Math.cos(phi), Math.sin(theta)*Math.sin(phi), Math.cos(theta)];
}

function longlat2mer( lon, lat )
{
  if( lon < -180 )
    lon += 360;
  if( lon > 180 )
    lon -= 360;
  if( lat < -90 )
    lat += 180;
  if( lat > 90 )
    lat -= 180;

  return [lon*Rad, Math.log(Math.tan(lat*Rad/2+Math.PI/4))];
}

function mer2longlat( x, y )
{ return [x/Rad, (2*Math.atan(Math.exp(y))-Math.PI/2)/Rad]; }

var pyon = [125.754,39.0319], pyonXY = longlat2mer( pyon[0], pyon[1] );

function persp( xyz, xc, yc, zc )
{
  var x = xyz[0], y = xyz[1], z = xyz[2];

  return [xc+zc/(zc-z)*(x-xc), yc+zc/(zc-z)*(y-yc), z];
}

var xc = 0, yc = 0, zc = -100.0;

var tokyo = [139.767052, 35.681167];
//var tokyo = [-74.0059740, 40.7127461];
//var tokyo = [0,0];

function cityQ( lonlat )
{
  var qlat = rotXQ( Math.PI/2+lonlat[1]*Rad );
  var q = defQ;
  q = qMul( qlat, q );
  q = qMul( rotQ( applyQ( [0,0,1], qlat ), -Math.PI/2-lonlat[0]*Rad ), q );

  return q;
}

var sphQ = defQ, tosphQ = defQ;

function trans( xy )
{ return persp( applyQ( longlat2xyz(xy[0], xy[1]), sphQ ), xc, yc, zc ); }

// theta -> a, phi -> b, psi -> c
function rot( v, a, b, c )
{
  var x = v[0], y = v[1], z = v[2];
  var cs = Math.cos, si = Math.sin;

  return [cs(b)*cs(a)*x+(cs(b)*si(a)*si(c)-si(b)*cs(c))*y+(cs(b)*si(a)*cs(c)+si(b)*si(c))*z,
          si(b)*cs(a)*x+(si(b)*si(a)*si(c)+cs(b)*cs(c))*y+(si(b)*si(a)*cs(c)-cs(b)*si(c))*z,
          -si(a)*x+cs(a)*si(c)*y+cs(a)*cs(c)*z];
}

var tim = 0;
var r = cvs.height/2-10;

console.log(map);

function morph( from, to, d )
{ return from+(to-from)/d; }

var mfl = false, bfl = false;
var cnt = 0, ccnt = 0;

document.onkeydown = event => {
  var keyEvent = event || window.event;

  switch( keyEvent.keyCode )
  {
    case 13: // Enter
      bfl ^= true;
      break;
    case 90: // Z
      mfl = true;
      break;
    case 37: // Left
      tosphQ = qMul( rotYQ(15*Rad), tosphQ );
      break;
    case 39: // Right
      tosphQ = qMul( rotYQ(-15*Rad), tosphQ );
      break;
    case 38: // Up
      tosphQ = qMul( rotXQ(-15*Rad), tosphQ );
      break;
    case 40: // Down
      tosphQ = qMul( rotXQ(15*Rad), tosphQ );
      break;
    case 27: // Esc
      tosphQ = cityQ( pyon );
      break;
  }
}

document.onkeyup = event => {
  var keyEvent = event || window.event;

  switch( keyEvent.keyCode )
  {
    case 13:
      ++cnt;
      break;
    case 90:
      mfl = false;
      break;
  }
}

function drawLine( x1, y1, x2, y2 )
{
  ctx.beginPath();
  ctx.moveTo( x1, y1 );
  ctx.lineTo( x2, y2 );
  ctx.closePath();
  ctx.stroke();
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

var slfl = false;

function render()
{
  var w = cvs.width, h = cvs.height;

  ++tim;

  //q = qSlerp( q, cityQ([city[ccnt][1], city[ccnt][2]]), 0.1 );
  if( qNorm(qAdd(sphQ,qScalar(-1,cityQ( pyon )))) < 0.001 )
    slfl = true;

  if( !slfl )
    sphQ = qSlerp( sphQ, cityQ( pyon ), 0.1 ), tosphQ = sphQ;

  sphQ = qSlerp( sphQ, tosphQ, 0.25 );
  
  //cnt = Math.floor(tim/20)%map.length;
  cnt = -1;
  ccnt = Math.floor(tim/40)%city.length;

  r = morph( r, mfl?(Math.min(w/2,h)/2-10)*2:Math.min(w/2,h)/2-10, 10 );

  ctx.clearRect( 0, 0, w, h );

  ctx.lineWidth = 2;
  ctx.strokeStyle = "rgb(40,40,40)";

  for( var i = 0; i < map.length; ++i )
  {
    ctx.strokeStyle = "rgb(40,40,40)";
    if( i == cnt )
      ctx.strokeStyle = "rgb(255,0,0)";
    var fl = true;

    for( var j = 0; j < map[i].length-(i==79||i==80||i==93||i==94||i==99?1:0); ++j )
    {
      var p0 = trans(map[i][j]), p1 = trans(map[i][(j+1)%map[i].length]);
      if( bfl || p0[2] <= 0 && p1[2] <= 0 )
        drawLine( w/4+r*p0[0], h/2+r*p0[1], w/4+r*p1[0], h/2+r*p1[1] );

      var m0 = longlat2mer(map[i][j][0]-pyon[0], map[i][j][1]-pyon[1]), m1 = longlat2mer(map[i][(j+1)%map[i].length][0]-pyon[0], map[i][(j+1)%map[i].length][1]-pyon[1]);
      var maxY = longlat2mer(0,89.5)[1];

      if( Math.abs(m0[0]-m1[0]) < 1.9*Math.PI && Math.abs(m0[1]-m1[1]) < 1.9*maxY )
        drawLine( w*3/4+m0[0]/2/Math.PI*w*3/8, h/2-m0[1]/2/Math.PI*w*3/8, w*3/4+m1[0]/2/Math.PI*w*3/8, h/2-m1[1]/2/Math.PI*w*3/8 );

      /*if( i ==  && j == cnt )
      {
        ctx.font = "normal 30px 'Yu Gothic'";
        ctx.fillStyle = "0x282828";

        ctx.fillText( j.toString(), w/2+r*p0[0], h/2+r*p0[1] );
      }*/

      fl &= p0[2]<=0;
    }

    //if( fl )
    {
      /*if( fl )
      {
        ctx.fillStyle = "rgb(40,40,40)";
        ctx.fill();
        ctx.strokeStyle = "rgb(255,255,255)";
        ctx.stroke();
      }
      else
      {*/
       // ctx.stroke(); 
      //}
    }
  }

  //var p = trans([city[ccnt][1],city[ccnt][2]]);
  var p = trans(pyon);
  ctx.beginPath();
  ctx.arc( w/4+r*p[0], h/2+r*p[1], 5, 0, 2*Math.PI, false );
  //ctx.arc( w/2, h/2, 5, 0, 2*Math.PI, false );
  ctx.strokeStyle = "rgb(255,0,0)";
  ctx.closePath();
  ctx.stroke();

  ctx.beginPath();
  ctx.arc( w/4, h/2, r*Math.sqrt(persp([1,0,0],xc,yc,zc)[0]**2+persp([1,0,0],xc,yc,zc)[1]**2+persp([1,0,0],xc,yc,zc)[2]**2), 0, 2*Math.PI, false );
  ctx.strokeStyle = "rgb(40,40,40)";
  ctx.closePath();
  ctx.stroke();

  for( var i = 1; i <= 18; ++i )
  {
    var rLL = i*longlat2mer(0,85.6)[1]/18;

    for( var j = 0; j < 100; ++j )
    {
      function getLL( k ){
        var x = pyonXY[0]+rLL*Math.cos( 2*Math.PI*k/100 ), y = pyonXY[1]+rLL*Math.sin( 2*Math.PI*k/100 );
        return mer2longlat( x, y );
      }
      function getXY( k ){
        var x = rLL*Math.cos( 2*Math.PI*k/100 ), y = rLL*Math.sin( 2*Math.PI*k/100 );
        return [x,y];
      }

      var p0 = trans(getLL(j)), p1 = trans(getLL((j+1)%100));
      var m0 = getXY(j), m1 = getXY((j+1)%100);

      var hsv = hsv2rgb( 360/18*(i-1), 180, 240 );
      hsv = hsv.map( Math.floor );
      ctx.strokeStyle = "rgb("+hsv[0].toString()+","+hsv[1].toString()+","+hsv[2].toString()+")";
      
      if( bfl || p0[2] <= 0 && p1[2] <= 0 )
        drawLine( w/4+r*p0[0], h/2+r*p0[1], w/4+r*p1[0], h/2+r*p1[1] );

      if( Math.abs(m0[0]-m1[0]) < 1.9*Math.PI && Math.abs(m0[1]-m1[1]) < 1.9*maxY )
          drawLine( w*3/4+m0[0]/2/Math.PI*w*3/8, h/2-m0[1]/2/Math.PI*w*3/8, w*3/4+m1[0]/2/Math.PI*w*3/8, h/2-m1[1]/2/Math.PI*w*3/8 );
    }
  }

  /*ctx.font = "normal 30px 'Yu Gothic'";
  ctx.fillStyle = "0x282828";

  //ctx.fillText( cnt.toString(), 25, 50 );
  ctx.fillText( (ccnt+1).toString(), 25, 50 );
  ctx.fillText( city[ccnt][0], 20, 90 );*/
}

setInterval( render, 1000/60 );