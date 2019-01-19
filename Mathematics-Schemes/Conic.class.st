"
Projective plane curves of genus 0 and degree 2. They are defined by quadratic polynomials.

Conics, together with rational curves (see RationalCurve), are the only curves of genus 0.

As any genus 0 curve, a conic either has no rational points, or it has infinitely many.
"
Class {
	#name : #Conic,
	#superclass : #ProjectivePlaneCurve,
	#category : #'Mathematics-Schemes-Projective'
}

{ #category : #'instance creation' }
Conic class >> coefficients: aTuple [
	| R x y z |
	R := aTuple scalars polynomialsIn: #(x y z).
	x := R x.
	y := R y.
	z := R z.
	'aTuple size = 3
			ifTrue: [^ self polynomial: x^2 * (aTuple at: 1) + (y^2 * (aTuple at: 2)) + (z^2 * (aTuple at: 3))]'.
	'aTuple size = 6
			ifTrue: [^ self polynomial: x^2*(aTuple at: 1) + (x*y*(aTuple at: 2)) + (x*z*(aTuple at: 3)) + (y^2*(aTuple at: 4)) + (y*z*(aTuple at: 5)) + (z^2*(aTuple at: 6))]'.
	^ self error: '3 or 6 coefficients expected'
]

{ #category : #accessing }
Conic >> coefficients [
	^ self propertyAt: #coefficients ifAbsentPut:
		[| f |
		f := self polynomial orderedBy: #lex.
		(f parent gradingAt: 2) coordinatesOf: f]
]

{ #category : #accessing }
Conic >> determinant [
	^ self matrix determinant
]

{ #category : #accessing }
Conic >> genus [
	"Answer the geometric genus of the receiver."
	^ 0
]

{ #category : #testing }
Conic >> isDiagonal [
	"Answer true if the reciever is in diagonal form, i.e. it is defined by a polynomial of the form ax^2 + by^2 + cz^2."
	| coefficients |
	coefficients := self coefficients.
	^ (coefficients at: 2) isZero and: [(coefficients at: 3) isZero and: [(coefficients at: 5) isZero]]
]

{ #category : #testing }
Conic >> isIrreducible [
	"In characteristic not 2, this is equivalent to the diagonal form having coefficients a,b,c all not 0."
	^ super isIrreducible
]

{ #category : #testing }
Conic >> isSmooth [
	"Answer true if the receiver is nonsingular."
	| coefficients p |
	self scalars characteristic = 2 ifFalse: [^ self determinant isZero not].
	coefficients := self coefficients.
	p := #(5 3 2) collect: [:i| coefficients at: i].
	(p allSatisfy: [:each| each isZero]) ifTrue: [^ false].
	^ (self polynomial value: p) isZero not
]

{ #category : #accessing }
Conic >> matrix [
	"Answer the matrix M such that the defining polynomial of this conic is (x,y,z)*M*(x,y,z)^t. The matrix is upper-triangular over characteristic 2, and symmetric otherwise."
	self scalars characteristic = 2
		ifTrue: [^ self upperTriangularMatrix].
	^ self symmetricMatrix
]

{ #category : #accessing }
Conic >> parametrization [
	"Answer a parametrization of the receiver as a regular map from the projective line."
	| point P1 |
	self scalars isField ifFalse: [^ self error: 'not over a field'].
	self isSmooth ifFalse: [^ self error: 'the conic is not smooth'].
	point := self anyPoint.
	P1 := ProjectiveLine over: self scalars.
	"..."
]

{ #category : #points }
Conic >> pointAtRandom: aRandom [
	"Answer randomly a point of the receiver. Assume the scalars are a finite field."
	| f |
	f := self parametrization.
	^ f value: (f domain pointAtRandom: aRandom)
]

{ #category : #points }
Conic >> pointsCountOver: aRing [
	"The number of Z/pZ-rational points of a curve of genus 0 is always p + 1."
	(aRing isKindOf: PrimeField) ifTrue: [^ aRing characteristic + 1].
	^ super pointsCountOver: aRing
]

{ #category : #private }
Conic >> solve: d n: n [
	(d < 0 and: [n < 0]) ifTrue: [^ nil].
	d abs > n abs ifTrue: [^ self solve: n n: d].
	d = 1 ifTrue: [^ #(1 1 0)].
	n = 1 ifTrue: [^ #(1 0 1)].
	d = n negated ifTrue: [^ #(0 1 1)].
	d = n ifTrue: [^ (self solve: -1 n: d) ifNotNil: [:xyz| [:x :y :z| {d*z. x. y}] valueWithArguments: xyz]].
	(d isQuadraticResidueModulo: n) ifFalse: [^ nil].
	"... last two steps"
]

{ #category : #private }
Conic >> symmetricMatrix [
	| T |
	self scalars characteristic = 2
		ifTrue:
			[self isDiagonal ifFalse: [self error: 'not symmetric matrix defined for non-diagonal conic over field of characteristic 2'].
			^ self upperTriangularMatrix].
	T := self upperTriangularMatrix.
	^ T + T transposed / 2
]

{ #category : #morphisms }
Conic >> toDiagonal [
	"Answer an isomorphism between the receiver and its diagonal form."
	self notYetImplemented
]

{ #category : #private }
Conic >> upperTriangularMatrix [
	| stream |
	stream := self coefficients readStream.
	^ self scalars matrix: 3 evaluating: [:i :j| i > j ifTrue: [self scalars zero] ifFalse: [stream next]]
]
