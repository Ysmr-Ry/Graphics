var renderer, scene, cam, cvsFrame;
var trackball;
var pointLight, lighthelper, spotLight, ambientLight;
var axis, arrows, cube, plane, tri;
var faceNormalsHelper;
var earth;

window.onload = () => {
  cvsFrame = document.getElementById( 'canvas-frame' );
  renderer = new THREE.WebGLRenderer( { alpha: true, antialias: true } );
  renderer.setSize( window.innerWidth, window.innerHeight );
  cvsFrame.appendChild( renderer.domElement );
  renderer.setClearColor( 0x282828, 1.0 );
  renderer.shadowMap.enabled = true;
  scene = new THREE.Scene();

  cam = new THREE.PerspectiveCamera( 45, window.innerWidth / window.innerHeight, 1, 10000 );
  //cam.position.set( 200, 150, 100 );
  cam.position.set( 50, 200, 0 );
  cam.up.set( 1, 0, 0 );
  cam.lookAt( { x: 0, y: 0, z: 0 } );

  trackball = new THREE.TrackballControls( cam, cvsFrame );
  trackball.noRotate = false;
  trackball.rotateSpeed = 2.0;
  trackball.noZoom = false;
  trackball.zoomSpeed = 0.1;
  trackball.noPan = false;
  trackball.panSpeed = 0.1;
  trackball.target = new THREE.Vector3( 0, 0, 10 );
  trackball.staticMoving = false;
  trackball.dynamicDampingFactor = 0.1;

  /*pointLight = new THREE.PointLight( 0xffffff, 1 );
  pointLight.position.set( 100, 50, 0 );
  scene.add( pointLight );*/

  const lNum = 12;
  for( let i = 0; i < lNum; ++i )
  {
    spotLight = new THREE.SpotLight( 0xffffff, 1.0, 0, Math.PI/3, 1, 0 );
    spotLight.position.set( 0, 100*Math.cos(2*Math.PI/lNum*i), 100*Math.sin(2*Math.PI/lNum*i) );
    scene.add( spotLight );
    spotLight.castShadow = true;
    lighthelper = new THREE.PointLightHelper( spotLight, 5 );
    scene.add( lighthelper );
  }

  /*spotLight = new THREE.SpotLight( 0xffffff, 1.0, 0, Math.PI/6, 1, 0 );
  spotLight.position.set( 200, 0, 0 );
  scene.add( spotLight );
  spotLight.castShadow = true;
  lighthelper = new THREE.PointLightHelper( spotLight, 5 );
  scene.add( lighthelper );
  ambientLight = new THREE.AmbientLight( 0x222222 );
  scene.add( ambientLight );*/

  /*axis = new THREE.AxisHelper( 100 );
  scene.add( axis );
  axis.position.set( 0, 0, 0 );*/

  arrows = new THREE.Group();

  arrows.add(
    new THREE.ArrowHelper(
      new THREE.Vector3( 1, 0, 0 ),
      new THREE.Vector3( 0, 0, 0 ),
      100,
      0xff0000
    )
  );

  arrows.add(
    new THREE.ArrowHelper(
      new THREE.Vector3( 0, 1, 0 ),
      new THREE.Vector3( 0, 0, 0 ),
      100,
      0x00ff00
    )
  );

  arrows.add(
    new THREE.ArrowHelper(
      new THREE.Vector3( 0, 0, 1 ),
      new THREE.Vector3( 0, 0, 0 ),
      100,
      0x0000ff
    )
  );

  scene.add( arrows );

  var geometry = new THREE.PlaneGeometry( 300, 300 );
  var material = new THREE.MeshPhongMaterial( { color: 0xffff00, specular: 0x333333, shininess: 200 } ); //new THREE.MeshNormalMaterial( { wireframe: false, wireframeLinewidth: 3 } );
  plane = new THREE.Mesh( geometry, material );
  scene.add( plane );
  plane.position.setX( -25 );
  plane.quaternion.setFromAxisAngle( new THREE.Vector3( 0, 1, 0 ), Math.PI/2 );
  plane.receiveShadow = true;

  //var loader = new THREE.TextureLoader();
  //var texture = loader.load( './ゆーたす.jpg' );

  var geometry = new THREE.BoxGeometry( 50, 50, 50 );
  var material = new THREE.MeshPhongMaterial( { color: 0xff0000, specular: 0x333333, shininess: 200 } ); //new THREE.MeshNormalMaterial( { wireframe: false, wireframeLinewidth: 3 } );

  cube = new THREE.Mesh( geometry, material );
  scene.add( cube );
  cube.castShadow = true;

  /*var geometry = new THREE.Geometry();
  geometry.vertices[0] = new THREE.Vector3( 50, 0, 0 );
  geometry.vertices[1] = new THREE.Vector3( 0, 50, 0 );
  geometry.vertices[2] = new THREE.Vector3( 0, 0, 50 );

  var colors = new Array();
  colors[0] = new THREE.Color( 0xff0000 );
  colors[1] = new THREE.Color( 0x00ff00 );
  colors[2] = new THREE.Color( 0x0000ff );

  geometry.faces[0] = new THREE.Face3( 0, 1, 2, null, colors );

  var material = new THREE.MeshBasicMaterial( { color: 0xffffff, vertexColors: THREE.VertexColors } );

  tri = new THREE.Mesh( geometry, material );
  scene.add( tri );*/

  //faceNormalsHelper = new THREE.FaceNormalsHelper( cube, 50 );
  //scene.add( faceNormalsHelper );

  /*var urls = [
    'posx.jpg', 'negx.jpg',
    'posy.jpg', 'negy.jpg',
    'posz.jpg', 'negz.jpg'
  ];
  var loader = new THREE.CubeTextureLoader();
  var textureCube = loader.load( urls );
  //textureCube.mapping = THREE.ReflectionMapping;
  textureCube.mapping = THREE.RefractionMapping;*/
  /*earth = new THREE.Mesh( geometry, material );
  scene.add( earth );*/

  /*var textureloader = new THREE.TextureLoader();
  textureloader.load( 'earth_atmos_2048.jpg', ( texture ) => {
    earth.material.map = texture;
    earth.material.needsUpdate = true;
  });
  textureloader.load( 'earth_normal_2048.jpg', ( texture ) => {
    earth.material.normalMap = texture;
    earth.material.needsUpdate = true;
  });
  textureloader.load( 'earth_specular_2048.jpg', ( texture ) => {
    earth.material.specularMap = texture;
    earth.material.needsUpdate = true;
  });

  var materialClouds = new THREE.MeshLambertMaterial( { color: 0xffffff, transparent: true } );
  cloud = new THREE.Mesh( geometry, materialClouds );
  cloud.scale.set( 1.005, 1.005, 1.005 );
  scene.add( cloud );

  textureloader.load( 'earth_clouds_1024.png', ( texture ) => {
    cloud.material.map = texture;
    cloud.material.needsUpdate = true;
  });*/

  timeStep();
}

var tim = 0;

function timeStep()
{
  ++tim;

  renderer.setSize( window.innerWidth, window.innerHeight );
  cam.aspect = window.innerWidth/window.innerHeight;
  cam.position.applyAxisAngle( new THREE.Vector3( 1, 0, 0 ).normalize(), Math.PI/1000 );
  cam.lookAt( { x: 0, y: 0, z: 0 } );
  cam.updateProjectionMatrix();

  trackball.update();

  //cloud.rotation.z = tim/1000+1;

  renderer.render( scene, cam );

  requestAnimationFrame( timeStep );
};