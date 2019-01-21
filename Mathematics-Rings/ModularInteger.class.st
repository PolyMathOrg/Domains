"
Residue classes of integers modulo an integer m, i.e. elements of the quotient ring Z/mZ (see ModularIntegers).
"
Class {
	#name : #ModularInteger,
	#superclass : #ResidueClass,
	#category : #'Mathematics-Rings-Finite'
}

{ #category : #operations }
ModularInteger >> + aModularInteger [
	| modulus r |
	aModularInteger isInteger ifTrue: [^ parent project: representative + aModularInteger].
	modulus := self modulus.
	r := representative + aModularInteger representative.
	r >= modulus ifTrue: [r := r - modulus].
	^ self class in: parent representative: r
]

{ #category : #copying }
ModularInteger >> , aTuple [
	^ (self modulus = 2
		ifTrue: [BitTuple new: 1 fromInteger: representative]
		ifFalse: [(ModularTuple new: 1 over: parent) at: 1 put: self; yourself]), aTuple
]

{ #category : #operations }
ModularInteger >> - aModularInteger [
	| modulus r |
	aModularInteger isInteger ifTrue: [^ parent project: representative - aModularInteger].
	modulus := self modulus.
	r := representative + modulus - aModularInteger representative.
	r >= modulus ifTrue: [r := r - modulus].
	^ self class in: parent representative: r
]

{ #category : #operations }
ModularInteger >> / aModularInteger [
	aModularInteger isInteger ifTrue: [^ self * (parent inverseOfRepresentative: aModularInteger)].
	^ self * aModularInteger reciprocal
]

{ #category : #comparing }
ModularInteger >> = aModularInteger [
	self class == aModularInteger class ifFalse: [^ false].
	self == aModularInteger ifTrue: [^ true].
	^ representative = aModularInteger representative and: [parent = aModularInteger parent]
]

{ #category : #operations }
ModularInteger >> additiveOrder [
	| modulus |
	modulus := self modulus.
	^ modulus // (representative gcd: modulus)
]

{ #category : #converting }
ModularInteger >> asRational [
	"Answer the rational reconstruction of the receiver, or nil if it doesn't exist."
	| N |
	N := (self modulus // 2) sqrtFloor.
	^ self asRationalMaxNumerator: N maxDenominator: N
]

{ #category : #converting }
ModularInteger >> asRational: T [
	"Answer the rational reconstruction of the receiver, or nil if not found.
	This is the MQRR (Maximal Quotient Rational Reconstruction) algorithm.
	The parameter T > 0 bounds the size of the possible outputs. If u is the representative of the receiver and m is the modulus, the algorithm returns a rational n/d = u mod m, d > 0, gcd(n,d) = 1 and T*|n|*d < m, or fails.
	The algorithm is almost optimal in the sense that requires that the modulus be only a modest number bits longer than 2*|n|*d. The time complexity is O(log^2 m).
	Reference: 'Maximal Quotient Rational Reconstruction: An Almost Optimal Algorithm for Rational Reconstructoin', Michael Monagan."
	| T2 n d t0 r0 t1 r1 temp answer |
	representative == 0 ifTrue: [^ self modulus > T ifTrue: [0]].
	n := 0. d := 0.
	t0 := 0. r0 := self modulus.
	t1 := 1. r1 := representative.
	T2 := T.
	[r1 ~~ 0 and: [r0 > T2]]
		whileTrue:
			[| q |
			(q := r0 // r1) > T2
				ifTrue: [n := r1. d := t1. T2 := q].
			temp := r0 - (q * r1). r0 := r1. r1 := temp.
			temp := t0 - (q * t1). t0 := t1. t1 := temp].
	^ (d ~~ 0 and: [(answer := n/d) numerator abs = n abs]) ifTrue: [answer]
]

{ #category : #converting }
ModularInteger >> asRationalMaxNumerator: N maxDenominator: D [
	"Answer the rational reconstruction of the receiver, or nil if it doesn't exist."
	| n d t0 r0 t1 r1 temp answer |
	representative == 0 ifTrue: [^ 0].
	t0 := 0. r0 := self modulus.
	t1 := 1. r1 := representative.
	[r1 > N]
		whileTrue:
			[| q |
			q := r0 // r1.
			temp := r0 - (q * r1). r0 := r1. r1 := temp.
			temp := t0 - (q * t1). t0 := t1. t1 := temp].
	n := r1. d := t1.
	d <= 0 ifTrue: [n := n negated. d := d negated].
	^ (d <= D and: [(answer := n/d) numerator abs = n abs]) ifTrue: [answer]
]

{ #category : #accessing }
ModularInteger >> bitSize [
	^ representative bitSize
]

{ #category : #comparing }
ModularInteger >> hash [
	^ representative hash
]

{ #category : #testing }
ModularInteger >> isQuadraticResidue [
	(representative kronecker: self modulus) ~= 1 ifTrue: [^ false].
	(parent isKindOf: PrimeField) ifTrue: [^ true].
	^ self notYetImplemented
]

{ #category : #testing }
ModularInteger >> isZero [
	^ representative == 0
]

{ #category : #accessing }
ModularInteger >> lift [
	| m |
	m := self modulus.
	^ representative <= (m >> 1) ifTrue: [representative] ifFalse: [representative - m].
]

{ #category : #operations }
ModularInteger >> log: aModularInteger [
	"Answer the logarithm of the receiver with base aModularInteger."
	| m g answer x |
	representative = 0 ifTrue: [^ nil].
	representative = 1 ifTrue: [^ 0].
	m := parent modulus.
	g := aModularInteger representative.
	answer := 1.
	x := g.
	[x = representative] whileFalse: [x = 0 ifTrue: [^ nil]. x := x * g \\ m. answer := answer + 1].
	^ answer
]

{ #category : #operations }
ModularInteger >> multiplicativeOrder [
	^ parent units orderOf: self
]

{ #category : #operations }
ModularInteger >> negated [
	representative = 0 ifTrue: [^ self].
	^ self class in: parent representative: self modulus - representative
]

{ #category : #printing }
ModularInteger >> printOn: aStream [
	aStream print: representative
]

{ #category : #operations }
ModularInteger >> raiseTo: anInteger [ "^ "
	^ self class in: parent representative: (representative raisedTo: anInteger modulo: self modulus)
"	anInteger = 1 ifTrue: [^ self].
	anInteger = 0 ifTrue: [^ self one].
	anInteger < 0 ifTrue: [^ self reciprocal ^ anInteger negated].
	^ (self * self ^ (anInteger // 2)) * (self ^ (anInteger \\ 2))"
]

{ #category : #operations }
ModularInteger >> raisedTo: anInteger [

	^ self class
		in: parent
		representative: (representative raisedTo: anInteger modulo: self modulus)
	"	anInteger = 1 ifTrue: [^ self].
	anInteger = 0 ifTrue: [^ self one].
	anInteger < 0 ifTrue: [^ self reciprocal ^ anInteger negated].
	^ (self * self ^ (anInteger // 2)) * (self ^ (anInteger \\ 2))"
]

{ #category : #operations }
ModularInteger >> reciprocal [
	representative == 1 ifTrue: [^ self].
	^ parent inverseOf: self
]

{ #category : #accessing }
ModularInteger >> representative [
	^ representative
]

{ #category : #'accessing-private' }
ModularInteger >> representative: anInteger [
	representative := anInteger
]

{ #category : #operations }
ModularInteger >> squareRoot [
	"Assuming the receiver is a quadratic residue, answer a square root."
	| p |
	representative == 0 ifTrue: [^ self].
	p := self modulus.
	p == 2 ifTrue: [^ self].
	(p bitAnd: 3) == 3 ifTrue: [^ self raiseTo: (p + 1 // 4)].
	^ self parent squareRootOf: self
]
