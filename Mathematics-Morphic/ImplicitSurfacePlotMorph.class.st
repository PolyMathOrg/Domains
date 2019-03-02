Class {
	#name : #ImplicitSurfacePlotMorph,
	#superclass : #Morph,
	#instVars : [
		'polynomial',
		'rotation',
		'scaling',
		'surface',
		'scene',
		'camera',
		'image',
		'resolutionRatio',
		'lastMousePosition'
	],
	#category : #'Mathematics-Morphic'
}

{ #category : #accessing }
ImplicitSurfacePlotMorph >> color: aColor [
	super color: aColor.
	surface color: aColor
]

{ #category : #drawing }
ImplicitSurfacePlotMorph >> drawOn: aCanvas [
	image isNil ifTrue: [^ super drawOn: aCanvas].
	aCanvas image: (image magnifyBy: resolutionRatio) at: 0@0
]

{ #category : #private }
ImplicitSurfacePlotMorph >> fastResolutionRatio [
	^ 8
]

{ #category : #'event handling testing' }
ImplicitSurfacePlotMorph >> handlesMouseDown: aMouseButtonEvent [
	"Do I want to receive mouseDown events (mouseDown:, mouseMove:, mouseUp:)?"
	^true
]

{ #category : #initialization }
ImplicitSurfacePlotMorph >> initialize [
	super initialize.
	self morphExtent: 300@300.
	resolutionRatio := self normalResolutionRatio.
	self polynomial: AffineVariety clebschCubic asHypersurface polynomial
]

{ #category : #accessing }
ImplicitSurfacePlotMorph >> interiorColor: aColor [
	surface interiorColor: aColor
]

{ #category : #geometry }
ImplicitSurfacePlotMorph >> morphExtent: aPoint [
	image := nil.
	super morphExtent: aPoint
]

{ #category : #events }
ImplicitSurfacePlotMorph >> mouseButton1Down: aMouseButtonEvent localPosition: localEventPosition [
	super mouseButton1Down: aMouseButtonEvent localPosition: localEventPosition.
	lastMousePosition := localEventPosition
]

{ #category : #events }
ImplicitSurfacePlotMorph >> mouseButton1Up: aMouseButtonEvent localPosition: localEventPosition [
	super mouseButton1Up: aMouseButtonEvent localPosition: localEventPosition.
	resolutionRatio := self normalResolutionRatio.
	self render
]

{ #category : #events }
ImplicitSurfacePlotMorph >> mouseMove: aMouseMoveEvent localPosition: localEventPosition [
	lastMousePosition isNil
		ifFalse:
			[aMouseMoveEvent shiftPressed
				ifTrue:
					[| bounds d |
					bounds := self morphLocalBounds.
					d := (localEventPosition dist: lastMousePosition) / (bounds width min: bounds height) * 2.0.
					localEventPosition y >= lastMousePosition y ifTrue: [d := d negated].
					resolutionRatio := self fastResolutionRatio.
					self scaleSurfaceBy: (2 raisedTo: d)]
				ifFalse: [resolutionRatio := self fastResolutionRatio.
					self rotateSurfaceBy: localEventPosition - lastMousePosition]].
	lastMousePosition := localEventPosition
]

{ #category : #private }
ImplicitSurfacePlotMorph >> normalResolutionRatio [
	^ 2
]

{ #category : #accessing }
ImplicitSurfacePlotMorph >> polynomial: aPolynomial [
	polynomial := aPolynomial.
	rotation := Float64Quaternion identity.
	scaling := 1.0.
	surface := ImplicitSurface new polynomial: aPolynomial.
	surface color: color.
	camera := Camera new
				location: 0 @ 0 @ -2.5;
				direction: 0 @ 0 @ 1;
				up: 0 @ 1 @ 0;
				right: 1 @ 0 @ 0.
	scene := Scene new
				addLightSource: (LightSource new
							location: 15 @ 5 @ -20;
							color: Color lightYellow muchLighter);
"				addLightSource: (LightSource new
							location: -15 @ -5 @ 0;
							color: Color cyan);"
				addObject: surface;
"				addObject: (Plane new
							normal: 0 @ 1 @ 0;
							offset: 1;
							texture: (TextureWithFinish new
										pigment: (CheckerBoardPigment new
													center: 0 @ 0.1 @ 0;
													color1: Color gray;
													color2: Color white;
													squareSize: 1);
										finish: (CompoundFinish new
													addFinish: (PhongLightingModelFinish new
																ambient: 0.2;
																specular: 0;
																specularPower: 10);
													addFinish: (ReflectionFinish new reflection: 0.3))));
"				yourself.
	self render
]

{ #category : #private }
ImplicitSurfacePlotMorph >> render [
	camera imageSize: extent // resolutionRatio.
	image := camera renderScene: scene.
	self redrawNeeded
]

{ #category : #private }
ImplicitSurfacePlotMorph >> renderBest [
	resolutionRatio := 1.
	self render
]

{ #category : #'surface geometry' }
ImplicitSurfacePlotMorph >> rotateSurfaceBy: aPoint [
	| xSpeed ySpeed |
	xSpeed := Float pi / self morphLocalBounds width.
	ySpeed := Float pi / self morphLocalBounds height.
	rotation := ((Float64Quaternion radiansAngle: aPoint x * xSpeed axis: 0@1@0) * (Float64Quaternion radiansAngle: aPoint y * ySpeed axis: 1@0@0)) * rotation.
	self updateTransformation
]

{ #category : #'surface geometry' }
ImplicitSurfacePlotMorph >> scaleSurfaceBy: aNumber [
	scaling := scaling * aNumber.
	self updateTransformation
]

{ #category : #private }
ImplicitSurfacePlotMorph >> setCameraBack: distance [
	camera
		location: 0 @ 0 @ distance negated;
		direction: 0 @ 0 @ 1;
		up: 0 @ 1 @ 0;
		right: 1 @ 0 @ 0.
	self render
]

{ #category : #private }
ImplicitSurfacePlotMorph >> setCameraLocation: aPoint [
	camera location: aPoint.
	self render
]

{ #category : #private }
ImplicitSurfacePlotMorph >> setCameraRight: distance [
	camera
		location: distance @ 0 @ 0;
		direction: -1 @ 0 @ 0;
		up: 0 @ 1 @ 0;
		right: 0 @ 0 @ 1.
	self render
]

{ #category : #private }
ImplicitSurfacePlotMorph >> setCameraTop: distance [
	camera
		location: 0 @ distance @ 0;
		direction: 0 @ -1 @ 0;
		up: 0 @ 0 @ 1;
		right: 1 @ 0 @ 0.
	self render
]

{ #category : #private }
ImplicitSurfacePlotMorph >> setLightSourceAt: aPoint [
	scene lightSources first location: aPoint.
	self render
]

{ #category : #private }
ImplicitSurfacePlotMorph >> setRadius: aNumber [
	surface radius: aNumber.
	self render
]

{ #category : #'surface geometry' }
ImplicitSurfacePlotMorph >> updateTransformation [
	| M v |
	M := rotation asMatrix3x3.
	v := polynomial parent generate: [:x :y :z|
		{x * M a11 + (y * M a12) + (z * M a13) * scaling.
		x * M a21 + (y * M a22) + (z * M a23) * scaling.
		x * M a31 + (y * M a32) + (z * M a33) * scaling}].
	surface polynomial: (polynomial value: v).
	self render
]
