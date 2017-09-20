var cvs = document.getElementById('canvas');
var ctx = cvs.getContext('2d');
var w = cvs.width, h = cvs.height;

var gInput = //[[0,7,40],[0,14,7],[1,0,28],[1,10,26],[2,14,3],[3,0,47],[3,6,8],[3,12,43],[3,14,38],[5,8,38],[6,7,35],[6,9,43],[6,14,38],[7,4,20],[7,5,11],[7,6,46],[7,11,37],[7,14,10],[8,3,9],[8,11,37],[10,1,18],[10,14,3],[11,8,23],[11,14,0],[12,0,24],[12,4,5],[12,7,33],[13,2,2],[13,6,20],[14,0,37]];
[[0,1,7],[0,2,9],[1,2,10],[1,3,15],[2,3,11],[2,5,2],[3,4,6],[4,5,9],[0,5,14]];
var V = 6, vs = [], s = 0, MAX_V = 100000;
var G = [], rG = [];
var undir = true, undirN = false;
var osX = 0, osY = 0, toosX = 0, toosY = 0, rat = 1, torat = 1, frat = 1;

var prvE = Number.POSITIVE_INFINITY, kQ = 200, kE = 0.003, mu = 0.95;
var fl = true;

document.getElementById("editbox").style.visibility = document.getElementById("button").style.visibility = "hidden";

function initG()
{
  vs = [];
  G = [];
  rG = [];
  for( var i = 0; i < V; ++i )
    G[i] = [], rG[i] = [];

  for( var i = 0; i < V; ++i )
  {
    var randX = w/2+Math.random()*500-250, randY = h/2+Math.random()*400-200;
    vs[i] = { x: w*(i+1)/(V+1), y: randY, tox: w*(i+1)/(V+1), toy: randY, vx: 0, vy: 0 };
  }

  for( var i = 0; i < gInput.length; ++i )
  {
    var gi = gInput[i];
    G[gi[0]].push( { to: gi[1], cost: gi[2] } );
    (undir?G[gi[1]]:rG[gi[1]]).push( { to: gi[0], cost: gi[2] } ); 
  }
}

initG();

console.log(G);

var INF = Number.POSITIVE_INFINITY/4;
var d = (new Array(MAX_V)).fill(INF);

function* dijkstra(s)
{
  var pque = new PriorityQueue( { comparator: (a,b) => { 
    if( a.dist != b.dist )
      return a.dist-b.dist;

    return a.v-b.v;
  } } );
  d[s] = 0;
  pque.queue( { dist: 0, v: s } );

  while( pque.length != 0 )
  {
    var p = pque.dequeue();
    
    if( d[p.v] < p.dist )
      continue;

    yield { type: "focus", v: p.v };

    yield { type: "trans", v: p.v };

    for( var e of G[p.v] )
    {
      if( d[e.to] > d[p.v] + e.cost )
      {
        d[e.to] = d[p.v] + e.cost;
        pque.queue( { dist: d[e.to], v: e.to } );
        yield { type: "upd", v: p.v, to: e.to };
      }
    }
  }
}

function morph(f,t,d)
{ return f+(t-f)/d; }

var dijk;
var auto = true;

var state, tim = 0;
var states, pStates = 0;

function initS(s) 
{
  d.fill(INF);
  states = [ { state: { type: "null", v: -1 }, dist: [].concat(d) } ];

  dijk = dijkstra(s);

  while( true )
  {
    var itr = dijk.next();

    states.push( { state: itr.value, dist: [].concat(d) } );

    if( itr.done )
      break;
  }

  pStates = 0;
  state = states[0].state;
  d = states[0].dist;
}

initS(0);

function keyProcLR( keyEvent )
{
  switch( keyEvent.keyCode )
  {
    case 37: // <-
      if( !auto && pStates > 0 )
      {
        state = states[--pStates].state;
        d = states[pStates].dist;
      }

      break;
    case 39: // ->
      if( !auto )
      {
        if( pStates != states.length-1 )
        {
          state = states[++pStates].state;
          d = states[pStates].dist;
        }
      }

      break;
  }
}

var isShift = false;

document.getElementById("button").onclick = () => {
  var lines = document.getElementById("editbox").value.trim().split('\n');

  gInput = [];

  for( var i = 0; i < lines.length; ++i )
  {
    var xs = lines[i].split(' ');
    
    if( i == 0 )
    {
      V = xs[0];
      s = xs[2];
    }
    else
      gInput[i-1] = xs.map(parseFloat), console.log(xs.map(parseFloat));
  }

  undir = undirN;

  initG();
  initS(s);
}

document.onkeydown = event => {
  var keyEvent = event || window.event;

  switch( keyEvent.keyCode )
  {
    case 16: // Shift
      isShift = true;

      break;
  }

  if( isShift )
    keyProcLR( keyEvent );
}

document.onkeyup = event => {
  var keyEvent = event || window.event;

  switch( keyEvent.keyCode )
  {
    case 90: // Z
      /*state = dijk.next().value;

      for( var dist of d )
        console.log(dist);*/
      pStates = 0;
      state = states[pStates].state;
      d = states[pStates].dist;

      break;
    case 65: // A
      auto ^= true;

      break;
    case 16: // Shift
      isShift = false;

      break;
    case 17: // Ctrl
      if( document.getElementById("editbox").style.visibility == "visible" )
        document.getElementById("editbox").style.visibility = document.getElementById("button").style.visibility = "hidden";
      else
        document.getElementById("editbox").style.visibility = document.getElementById("button").style.visibility = "visible";

      break;
    case 68: // d
      undirN ^= true;

      break;
  }

  keyProcLR( keyEvent );
}

var mX, mY;
document.onmousemove = event => {
  mX = event.clientX;
  mY = event.clientY;
}

var clickN = -1;
document.onmousedown = event => {
  for( var i = 0; i < V; ++i )
  {
    var v = vs[i];

    if( clickN == -1 && (mX-((v.x+osX-w/2)*rat+w/2))**2+(mY-((v.y+osY-h/2)*rat+h/2))**2 < (50*frat)**2 )
    { clickN = i; break; }
  }
}

document.onmouseup = event => {
  clickN = -1;
}

function render() 
{
  ctx.clearRect( 0, 0, w, h );

  var E = 0;

  if( fl )
  {
    for( var i = 0; i < V; ++i )
    {
      var v = vs[i];
      var f = [0,0];

      for( var j = 0; j < V; ++j ) if( i != j )
      {
        var u = vs[j];

        var rsq = (v.tox-u.tox)**2+(v.toy-u.toy)**2;
        f[0] += kQ*(v.tox-u.tox)/rsq;
        f[1] += kQ*(v.toy-u.toy)/rsq;
      }

      //console.log(f);

      for( var j = 0; j < G[i].length; ++j ) 
      {
        var u = vs[G[i][j].to];

        f[0] += kE*(u.tox-v.tox);
        f[1] += kE*(u.toy-v.toy);
      }

      for( var j = 0; j < rG[i].length; ++j ) 
      {
        var u = vs[rG[i][j].to];

        f[0] += kE*(u.tox-v.tox);
        f[1] += kE*(u.toy-v.toy);
      }

      //console.log(f);

      v.vx = (v.vx+2*f[0])*mu;
      v.vy = (v.vy+2*f[1])*mu;
      v.tox += 2*v.vx;
      v.toy += 2*v.vy;

      E += v.vx**2+v.vy**2;

      //console.log(v);
    }
  }

  tim = (tim+1) % 30;
  if( auto && tim == 0 && ( pStates != 0 || E < 1e-2 ) )
  {
    if( pStates != states.length-1 )
    {
      state = states[++pStates].state;
      d = states[pStates].dist;
    }
  }

  for( var v of vs )
  {
    v.x = morph( v.x, v.tox, 1 );
    v.y = morph( v.y, v.toy, 1 );
  }

  //if( E < 1 )
  {
    var minX = Number.POSITIVE_INFINITY, maxX = Number.NEGATIVE_INFINITY, minY = Number.POSITIVE_INFINITY, maxY = Number.NEGATIVE_INFINITY;
    
    for( var i = 0; i < V; ++i )
    {
      minX = Math.min( minX, vs[i].x-70 );
      maxX = Math.max( maxX, vs[i].x+70 );
      minY = Math.min( minY, vs[i].y-70 );
      maxY = Math.max( maxY, vs[i].y+110 );
    }

    torat = Math.min( w/(maxX-minX), h/(maxY-minY) );
    toosX = (w-(maxX-minX))/2-minX;
    toosY = (h-(maxY-minY))/2-minY;
  }

  osX = morph( osX, toosX, 10 );
  osY = morph( osY, toosY, 10 );
  if( torat < 1 )
    rat = morph( rat, torat, 10 );
  else
    rat = 1;

  frat = Math.max( rat, 0.2 );

  var used = [], usedP = [];
  
  for( var i = 0; i < V; ++i ) for( var j = 0; j < G[i].length; ++j )
    usedP.push( i.toString()+","+G[i][j].to.toString() );

  for( var i = 0; i < V; ++i ) for( var j = 0; j < G[i].length; ++j )
  {
    var tag = Math.min(i,G[i][j].to).toString()+","+Math.max(i,G[i][j].to).toString();

    if( undir && used.indexOf(tag) != -1 )
      continue;

    var fx = (vs[i].x+osX-w/2)*rat+w/2, fy = (vs[i].y+osY-h/2)*rat+h/2;
    var tx = (vs[G[i][j].to].x+osX-w/2)*rat+w/2, ty = (vs[G[i][j].to].y+osY-h/2)*rat+h/2;
    var norm = Math.sqrt((tx-fx)**2+(ty-fy)**2);

    ctx.fillStyle = "rgb(40,40,40)";
    ctx.font = "normal "+Math.floor(30*rat)+"px 'Yu Gothic'";
    ctx.textAlign = 'center';
    var prvBaseLine = ctx.textBaseline;
    ctx.textBaseline = "middle";
    ctx.fillText( G[i][j].cost.toString(), (fx+tx)/2-(ty-fy)/norm*30*rat, (fy+ty)/2+(tx-fx)/norm*30*rat );
    ctx.textBaseline = prvBaseLine;

    if( !undir )
    {
      ctx.beginPath();
      ctx.strokeStyle = "rgb(40,40,40)";
      if( state != undefined && state.type != "focus" && ( i == state.v || undir && G[i][j].to == state.v ) )
        ctx.strokeStyle = "rgb(229,107,45)";
      var arrX = tx-(tx-fx)/norm*50*frat, arrY = ty-(ty-fy)/norm*50*frat;
      var vecX = (fx-tx)/norm*10*Math.max(rat,0.8), vecY = (fy-ty)/norm*10*Math.max(rat,0.8);
      ctx.moveTo( arrX, arrY );
      ctx.lineTo( arrX+(vecX*Math.cos(Math.PI/6)-vecY*Math.sin(Math.PI/6)), arrY+(vecY*Math.cos(Math.PI/6)+vecX*Math.sin(Math.PI/6)) );
      ctx.moveTo( arrX, arrY );
      ctx.lineTo( arrX+(vecX*Math.cos(-Math.PI/6)-vecY*Math.sin(-Math.PI/6)), arrY+(vecY*Math.cos(-Math.PI/6)+vecX*Math.sin(-Math.PI/6)) );
      ctx.stroke();
      ctx.closePath();
    }

    if( used.indexOf(tag) == -1 )
    {
      ctx.beginPath();
      ctx.lineWidth = 2;
      ctx.strokeStyle = "rgb(40,40,40)";
      if( state != undefined && state.type != "focus" && ( ( i == state.v || undir && G[i][j].to == state.v ) || ( !undir && usedP.indexOf(G[i][j].to.toString()+","+i.toString()) != -1 && G[i][j].to == state.v ) ) )
        ctx.strokeStyle = "rgb(229,107,45)";
      
      ctx.moveTo( fx, fy );
      ctx.lineTo( tx, ty );
      ctx.stroke();
      ctx.closePath();
    }

    used.push( tag );
  }

  for( var i = 0; i < V; ++i )
  {
    var v = vs[i];
    ctx.beginPath();
    ctx.fillStyle = "rgb(40,40,40)";
    if( state != undefined && ( i == state.v || state.type == "upd" && state.to == i ) )
      ctx.fillStyle = "rgb(229,107,45)";
    ctx.arc( (v.x+osX-w/2)*rat+w/2, (v.y+osY-h/2)*rat+h/2, 50*frat, 0, 2*Math.PI, false );
    ctx.fill();
    ctx.fillStyle = "rgb(255,255,255)";
    ctx.font = "normal "+Math.floor(40*frat)+"px 'Yu Gothic'";
    ctx.textAlign = 'center';
    ctx.fillText( i.toString(), (v.x+osX-w/2)*rat+w/2, (v.y+osY-h/2)*rat+h/2+16*frat );
    ctx.fillStyle = "rgb(40,40,40)";

    if( state != undefined && ( i == state.v || state.type == "upd" && state.to == i ) )
      ctx.fillStyle = "rgb(229,107,45)";

    ctx.font = "normal "+Math.floor(30*frat)+"px 'Yu Gothic'";
    ctx.fillText( "d="+(d[i]==INF?"∞":d[i].toString()), (v.x+osX-w/2)*rat+w/2, (v.y+osY-h/2)*rat+h/2+80*frat ); 
  }

  ctx.font = "normal 40px 'Yu Gothic'";
  ctx.fillStyle = "rgb(40,40,40)";
  ctx.textAlign = 'left';
  //ctx.fillText( "E = "+E.toString(), 20, 60 );
  ctx.fillText( (pStates+1).toString()+" / "+states.length.toString()+" steps", 20, 60 );
  ctx.fillText( "Undirected: "+(undirN?"true":"false"), 20, 115 );

  if( auto )
    ctx.fillText( "auto", 20, 160 );
  //if( E > prvE )
    //fl = false;

  if( clickN != -1 )
  {
    vs[clickN].x = vs[clickN].tox = (mX-w/2)/rat-(osX-w/2);
    vs[clickN].y = vs[clickN].toy = (mY-h/2)/rat-(osY-h/2); 
  }

  prvE = E;
}

setInterval( render, 1000/60 );