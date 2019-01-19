Extension { #name : #Fraction }

{ #category : #'*mathematics' }
Fraction >> % anInteger [
	| R |
	R := ZZ % anInteger.
	^ (R project: numerator) / (R project: denominator)
]

{ #category : #'*mathematics' }
Fraction >> adaptToAlgebraic: rcvr andSend: selector [
	^ rcvr perform: selector with: (ComplexAlgebraicNumber fromRational: self)
]

{ #category : #'*mathematics' }
Fraction >> adaptToRealAlgebraic: rcvr andSend: selector [
	^ rcvr perform: selector with: (RealAlgebraicNumber fromRational: self)
]

{ #category : #'*mathematics' }
Fraction >> bitSize [
	^ numerator bitSize + denominator bitSize
]

{ #category : #'*mathematics' }
Fraction >> height [
	^ numerator abs max: denominator
]

{ #category : #'*mathematics' }
Fraction >> isFractional [
	"Answer true if this is an element of a localization, i.e. if it is some kind of fraction and understands #numerator and #denominator."
	^ true
]

{ #category : #'*mathematics' }
Fraction >> isRational [
	^ true
]

{ #category : #'*mathematics' }
Fraction >> minimalPolynomial [
	^ QQ polynomials x - self
]

{ #category : #'*mathematics' }
Fraction >> parent [
	^ QQ
]

{ #category : #'*mathematics' }
Fraction >> squareRoot [
	self positive ifTrue: [^ RealAlgebraicNumber sqrt: self].
	^ ComplexAlgebraicNumber sqrt: self
]
