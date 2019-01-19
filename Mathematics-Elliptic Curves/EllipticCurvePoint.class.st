"
K-rational points on an elliptic curve E, seen as morphisms Spec(K) -> E. These objects implement the group law (with additive notation). The identity element (zero, or the point at infinity) is [0:1:0].

Following conventions, a point [a:b:1] is printed '(a,b)', and the point at infinity [0:1:0] is printed 'O'.

See also EllipticCurve.
"
Class {
	#name : #EllipticCurvePoint,
	#superclass : #ProjectivePoint,
	#category : #'Mathematics-Elliptic Curves'
}

{ #category : #arithmetic }
EllipticCurvePoint >> * anInteger [
	anInteger isInteger ifFalse: [^ DomainError signal: 'argument must be integer'].
	anInteger = 1 ifTrue: [^ self].
	anInteger = 0 ifTrue: [^ self zero].
	anInteger < 0 ifTrue: [^ (self * anInteger negated) negated].
	^ anInteger even
		ifTrue: [self doubled * (anInteger // 2)]
		ifFalse: [self doubled * (anInteger // 2) + self]
]

{ #category : #arithmetic }
EllipticCurvePoint >> + aPoint [
	"Answer the sum of the receiver and the argument.
	Reference: Henri Cohen, 'A Course In Computational Algebraic Number Theory', Proposition 7.1.7."
	| W x1 y1 x2 y2 m x3 y3 |
	aPoint isZero ifTrue: [^ self].
	self isZero ifTrue: [^ aPoint].
	W := self codomain equation.
	x1 := self x. y1 := self y.
	x2 := aPoint x. y2 := aPoint y.
	(x1 = x2 and: [y1 = (y2 negated - (W a1 * x2) - W a3)]) "self = aPoint negated"
		ifTrue: [^ self zero].
	m := (x1 = x2 and: [y1 = y2]) "self = aPoint"
		ifTrue: [x1 squared * 3 + (W a2 * x1 * 2) + W a4 - (W a1 * y1) / (y1 * 2 + (W a1 * x1) + W a3)]
		ifFalse: [y1 - y2 / (x1 - x2)].
	x3 := x1 negated - x2 - W a2 + (m*(m + W a1)).
	y3 := y1 negated - W a3 - (W a1 * x3) + (m*(x1 - x3)).
	^ self shallowCopy coordinates: (self scalars tuple: {x3. y3. self scalars one})
]

{ #category : #arithmetic }
EllipticCurvePoint >> - aPoint [
	^ self + aPoint negated
]

{ #category : #converting }
EllipticCurvePoint >> adaptToInteger: anInteger andSend: selector [
	selector = #* ifTrue: [^ self * anInteger].
	self error: 'undefined operation'
]

{ #category : #arithmetic }
EllipticCurvePoint >> doubled [
	"Answer the receiver times 2, i.e. self + self.
	Reference: Henri Cohen, 'A Course In Computational Algebraic Number Theory', Proposition 7.1.7."
	| W x1 y1 m x3 y3 |
	self isZero ifTrue: [^ self].
	W := self codomain equation.
	x1 := self x. y1 := self y.
	m := x1 squared * 3 + (W a2 * x1 * 2) + W a4 - (W a1 * y1) / (y1 * 2 + (W a1 * x1) + W a3).
	x3 := x1*(-2) - W a2 + (m*(m + W a1)).
	y3 := y1 negated - W a3 - (W a1 * x3) + (m*(x1 - x3)).
	^ self shallowCopy coordinates: (self scalars tuple: {x3. y3. self scalars one})
]

{ #category : #testing }
EllipticCurvePoint >> isZero [
	^ (self coordinates at: 1) isZero and: [(self coordinates at: 3) isZero]
]

{ #category : #arithmetic }
EllipticCurvePoint >> negated [
	| W x |
	self isZero ifTrue: [^ self].
	W := self codomain equation.
	x := self x.
	^ self shallowCopy coordinates: (self scalars tuple: {x. self y negated + (W a1 * x) - W a3. self scalars one})
]

{ #category : #printing }
EllipticCurvePoint >> printOn: aStream [
	self isZero
		ifTrue: [aStream nextPutAll: 'O' italic]
		ifFalse: [aStream nextPut: $(; print: self x; nextPut: $,; print: self y; nextPut: $)]
]

{ #category : #accessing }
EllipticCurvePoint >> x [
	^ self coordinates at: 1
]

{ #category : #accessing }
EllipticCurvePoint >> y [
	^ self coordinates at: 2
]

{ #category : #arithmetic }
EllipticCurvePoint >> zero [
	| R |
	R := self scalars.
	^ self shallowCopy coordinates: (R tuple: {R zero. R one. R zero})
]
