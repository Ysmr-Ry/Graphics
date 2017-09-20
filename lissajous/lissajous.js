var cvs = document.getElementById('canvas');
var ctx = cvs.getContext('2d');

var delta = 0;
var maxSize = 1000;

function calc( theta )
{ 
  var w = cvs.width, h = cvs.height;

  return [w/2+100*(Math.sin(4*theta+delta)+Math.sin(5*theta+delta)), h/2+100*(Math.sin(7*theta)+Math.sin(3*theta))];
}

function render()
{
  var w = cvs.width, h = cvs.height;

  ctx.clearRect( 0, 0, w, h );

  ctx.lineWidth = 2;
  ctx.strokeStyle = "rgb(40,40,40)";
  ctx.beginPath();
  ctx.moveTo( calc(0)[0], calc(0)[1] );

  for( var i = 0; i < maxSize; ++i )
  {
    var theta = theta = 2*Math.PI/maxSize*(i+1);
    ctx.lineTo( calc(theta)[0], calc(theta)[1] );
  }

  ctx.closePath();
  ctx.stroke();

  ctx.font = "normal 30px 'Yu Gothic'";
  ctx.fillStyle = "0x282828";

  ctx.fillText( "δ = 2π× " + (delta/(2*Math.PI)).toFixed(4).toString(), 30, 80 );
  
  ctx.lineWidth = 2;
  ctx.shadowColor = "rgba(40,40,40,0.5)";
  ctx.shadowBlur = 1;
  ctx.strokeStyle = "rgb(243,156,18)";

  var infoW = ctx.measureText( "δ = 2π× " + (delta/(2*Math.PI)).toFixed(4).toString() ).width+50, infoH = 55*1;

  ctx.beginPath();
  ctx.moveTo( 20, 40 );
  ctx.lineTo( infoW, 40 );
  ctx.lineTo( infoW, 40+infoH );
  ctx.lineTo( 20, 40+infoH );
  ctx.lineTo( 20, 40 );
  ctx.closePath();
  ctx.stroke();

  ctx.shadowColor = "rgba(0,0,0,0)";

  delta += 2*Math.PI/600;

  if( delta >= 2*Math.PI )
    delta -= 2*Math.PI;
}

setInterval( render, 1000/60 );