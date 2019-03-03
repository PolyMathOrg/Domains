Class {
	#name : #ImplicitSurface,
	#superclass : #Object,
	#instVars : [
		'polynomial',
		'gradient',
		'radiusSquared',
		'interiorTexture'
	],
	#category : #'Mathematics-Morphic'
}

{ #category : #examples }
ImplicitSurface class >> example1 [
	^ self new
		polynomial:
			((RR polynomialsIn: #(x y z)) generate: [:x :y :z| (x raisedTo: 2) + (y raisedTo: 2) + (z raisedTo: 3) + (x*y*z*2) - 1]);
		radius: 1.0
]

{ #category : #examples }
ImplicitSurface class >> example2 [
	^ self new
			polynomial: ((RR polynomialsIn: #(x y z)) generate: [:x :y :z| (x raisedTo: 2) - ((y raisedTo: 2)*(z raisedTo: 2))]);
			radius: 5.0
]

{ #category : #accessing }
ImplicitSurface >> color: aColor [
	self texture: (self defaultTextureForColor: aColor)
]

{ #category : #private }
ImplicitSurface >> defaultTextureForColor: aColor [
	^ TextureWithFinish new
			pigment: (FlatColorPigment new color: aColor);
			finish: (PhongLightingModelFinish new
					ambient: 0.35;
					specular: 0.8;
					specularPower: 20)

"			finish: (CompoundFinish new
				addFinish: (PhongLightingModelFinish new
					ambient: 0.35;
					specular: 0.8;
					specularPower: 20);
				addFinish: (ReflectionFinish new reflection: 1);
				yourself)"
]

{ #category : #initializing }
ImplicitSurface >> initialize [
"	self polynomial: (RR polynomialsIn: #(x y z) :: generate: [:x :y :z| x**2 + (y**2) + (z**2) - 2])"
"	self polynomial: (RR polynomialsIn: #(x y z) :: generate: [:x :y :z| x**2 + (z**2) - (y**2)])."
	self polynomial: AffineVariety clebschCubic asHypersurface polynomial.
"	self polynomial: (QQ polynomialsIn: #(x y z) :: generate: [:x :y :z| x squared + y squared - ((1 - z) * (z**4))])."
	self radius: 1.0
]

{ #category : #accessing }
ImplicitSurface >> interiorColor: aColor [
	self interiorTexture: (self defaultTextureForColor: aColor)
]

{ #category : #accessing }
ImplicitSurface >> interiorTexture [
	^ interiorTexture ifNil: [texture]
]

{ #category : #accessing }
ImplicitSurface >> interiorTexture: aTexture [
	interiorTexture := aTexture
]

{ #category : #'tracing-private' }
ImplicitSurface >> intersectionWithSphere: aRay [
	| a b c determinant t1 t2 |
	a := aRay directionLengthSquared.
	b := (aRay origin dot: aRay direction) * 2.0.
	c := (aRay origin dot: aRay origin) - radiusSquared.
	determinant := b * b - (4.0 * a * c).
	determinant < 0.0 ifTrue: [^ nil].
	determinant := determinant sqrt.
	a := a * 2.0.
	t1 := (determinant - b) / a.
	t2 := (determinant negated - b) / a.
	t1 negative ifTrue: [^ t2 positive ifTrue: [t2]].
	t2 negative ifTrue: [^ t1 positive ifTrue: [t1]].
	^ t1 min: t2
]

{ #category : #tracing }
ImplicitSurface >> normalAt: aPoint [
	^ (Float32Vector3 x: ((gradient at: 1) value: aPoint) y: ((gradient at: 2) value: aPoint) z: ((gradient at: 3) value: aPoint)) normalize
]

{ #category : #accessing }
ImplicitSurface >> polynomial [
	^ polynomial
]

{ #category : #accessing }
ImplicitSurface >> polynomial: aPolynomial [
	polynomial := aPolynomial.
	gradient := polynomial gradient
]

{ #category : #accessing }
ImplicitSurface >> radius [
	^ radiusSquared sqrt
]

{ #category : #accessing }
ImplicitSurface >> radius: aNumber [
	radiusSquared := aNumber squared
]

{ #category : #'tracing-private' }
ImplicitSurface >> signChanges: a [
	| lastSign count |
	lastSign := a at: 1.
	count := 0.
	2 to: a size do: [:i| | ai sign | (ai := a at: i) abs < Float epsilon ifFalse: [(sign := ai sign) == lastSign ifFalse: [count := count + 1. lastSign := sign]]].
	^ count
]

{ #category : #'tracing-private' }
ImplicitSurface >> solve: f max: max [
	| left right n a b c r0 r1 count |
	f isConstant ifTrue: [^ nil].
"	(f independentCoefficient < Float epsilon) ifTrue: [^ 0.0]."
	a := f coefficients asArray reversed collect: [:each| each asFloat].
	n := a size.
"	(self signChanges: a) > 0 ifFalse: [^ nil]." "no positive roots"
	b := Array new: n.
	c := Array new: n-1.
	left := 0.000001.
	[right := left + 0.1. (f value: left) * (f value: right) <= 0.0] whileFalse: [left := right. left > max ifTrue: [^ nil]].
	r0 := left.
	b at: 1 put: (a at: 1).
	c at: 1 put: (b at: 1).
	count := 1.
	[2 to: n do: [:i|
		b at: i put: (a at: i) + (r0 * (b at: i-1)).
		i < n ifTrue: [c at: i put: (b at: i) + (r0 * (c at: i-1))]].
	r1 := r0 - ((b at: n) / (c at: n-1)).
	(r1 - r0) abs < 10.0e-6 ifTrue: [^ r1].
	r0 := r1.
	(count := count + 1) > 100 ifTrue: [^ nil]] repeat
]

{ #category : #tracing }
ImplicitSurface >> writeIntersectionsWith: aRay into: aCollection [
	| t0 origin ox oy oz direction dx dy dz t f root intersection p |
	(t0 := self intersectionWithSphere: aRay) ifNil: [^ self].
	origin := aRay pointAtDistance: t0.
	ox := origin x.
	oy := origin y.
	oz := origin z.
	direction := aRay direction.
	dx := direction x.
	dy := direction y.
	dz := direction z.
	t := RR polynomials x.
	f := polynomial value: {t*dx + ox. t*dy + oy. t*dz + oz}.
	(root := self solve: f max: radiusSquared sqrt*2) ifNil: [^ self].
	intersection := Intersection for: self ray: aRay distance: root+t0.
	p := intersection intersectionPoint. "this is expensive, can we do without computing this intersection point?"
	(p dot: p) < (radiusSquared - 0.00001) ifTrue: [aCollection add: intersection]
]
