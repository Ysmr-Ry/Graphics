var cvs = document.getElementById('canvas');
var cntnr = document.getElementById('container');
var ctx = cvs.getContext('2d');

function sizing()
{
  cvs.height = cntnr.offsetHeight;
  cvs.width = cntnr.offsetWidth;
}

sizing();

window.addEventListener('resize', function() {
  (!window.requestAnimationFrame) ? setTimeout(sizing, 300): window.requestAnimationFrame(sizing);
});

function drawLine( ctx, x1, y1, x2, y2 )
{
  ctx.beginPath();
  ctx.moveTo(x1,y1);
  ctx.lineTo(x2,y2);
  ctx.closePath();
  ctx.stroke();
};

function persp( v )
{ return [1000*v[0]/(v[2]+1000), 1000*v[1]/(v[2]+1000)]; }

function dist( u, v )
{ return Math.sqrt( (u[0]-v[0])*(u[0]-v[0])+(u[1]-v[1])*(u[1]-v[1])+(u[2]-v[2])*(u[2]-v[2]) ); }

// theta -> a, phi -> b, psi -> c
function rot( v, a, b, c )
{
  var x = v[0], y = v[1], z = v[2];
  var cs = Math.cos, si = Math.sin;

  return [cs(b)*cs(a)*x+(cs(b)*si(a)*si(c)-si(b)*cs(c))*y+(cs(b)*si(a)*cs(c)+si(b)*si(c))*z,
          si(b)*cs(a)*x+(si(b)*si(a)*si(c)+cs(b)*cs(c))*y+(si(b)*si(a)*cs(c)-cs(b)*si(c))*z,
          -si(a)*x+cs(a)*si(c)*y+cs(a)*cs(c)*z];
}

/*function rotY( v, b )
{
  var x = v[0], y = v[1], z = v[2];
  var cs = Math.cos, si = Math.sin;

  return [cs(b)*x+si(b)*z,
          y,
          -si(b)*x+cs(b)*z];
}*/

var phi = (1+Math.sqrt(5))/2;
var vtx = [];

for( var i = 0; i <= 1; ++i ) for( var j = 0; j <= 1; ++j )
{
  var s1 = i == 0 ? -1 : 1, s2 = j == 0 ? -1 : 1;

  vtx.push( [ 100*s1, 100*s2*phi, 0 ] );
  vtx.push( [ 0, 100*s1, 100*s2*phi ] );
  vtx.push( [ 100*s2*phi, 0, 100*s1 ] );
}

var ang = 0;
var fst = true;
var svtx = [];
var fl = false;

document.onkeydown = event => {
  var keyEvent = event || window.event;

  if( keyEvent.keyCode == 13 )
    fl ^= true;
}

function render()
{
  var w = cvs.width, h = cvs.height;
  ctx.clearRect( 0, 0, w, h );

  for( var i = 0; i < 12; ++i ) for( var j = i+1; j < 12; ++j )
  {
    var u = vtx[i], v = vtx[j];

    if( Math.abs( dist(u,v) - 200 ) <= 0.5 )
    {
      if( fst )
      {
        svtx.push( [(2*u[0]+v[0])/3, (2*u[1]+v[1])/3, (2*u[2]+v[2])/3] );
        svtx.push( [(u[0]+2*v[0])/3, (u[1]+2*v[1])/3, (u[2]+2*v[2])/3] );
      }

      var up = persp(rot(u,0,ang,ang)), vp = persp(rot(v,0,ang,ang));
      
      if( fl )
        drawLine( ctx, up[0]+w/2, up[1]+h/2, vp[0]+w/2, vp[1]+h/2 ); 
    }
  }

  for( var i = 0; i < svtx.length; ++i ) for( var j = i+1; j < svtx.length; ++j )
  {
    var u = svtx[i], v = svtx[j];

    if( dist(u,v) <= 67 )
    {
      var up = persp(rot(u,0,ang,ang)), vp = persp(rot(v,0,ang,ang));
      drawLine( ctx, up[0]+w/2, up[1]+h/2, vp[0]+w/2, vp[1]+h/2 ); 
    }
  }

  ang += 0.01;
  fst = false;
}

setInterval( render, 1000/60 );