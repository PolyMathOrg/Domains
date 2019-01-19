Extension { #name : #Integer }

{ #category : #'*mathematics' }
Integer >> % anInteger [
	^ ZZ % anInteger project: self
]

{ #category : #'*mathematics' }
Integer >> /// anInteger [
	"Answer the exact division of the receiver by the argument."
	^ self // anInteger
]

{ #category : #'*mathematics' }
Integer >> Stirling: anInteger [
	"Answer the Stirling number of the second kind S(n,k).
	Stirling numbers of the second kind count the ways to partition a set of n things into k nonempty subsets."
	(anInteger > self or: [self < 0]) ifTrue: [^ DomainError signal].
	self = anInteger ifTrue: [^ 1].
	anInteger = 0 ifTrue: [^ 0].
	self+1 = anInteger ifTrue: [^ self choose: 2].
	anInteger = 2 ifTrue: [^ 2 raisedTo: (self-1) - 1].
	^ anInteger*(self - 1 Stirling: anInteger) + (self - 1 Stirling: anInteger - 1)
]

{ #category : #'*mathematics' }
Integer >> adaptToAlgebraic: rcvr andSend: selector [
	^ rcvr perform: selector with: (ComplexAlgebraicNumber fromRational: self)
]

{ #category : #'*mathematics' }
Integer >> adaptToRealAlgebraic: rcvr andSend: selector [
	^ rcvr perform: selector with: (RealAlgebraicNumber fromRational: self)
]

{ #category : #'*mathematics' }
Integer >> additiveOrder [
	^ self == 0 ifTrue: [1] ifFalse: [Infinity positive]
]

{ #category : #'*mathematics' }
Integer >> bitCount [
	"Answer the number of bits that are set, i.e. the number of 1s in the binary representation."
	| n |
	self = 0 ifTrue: [^ 0].
	self = 1 ifTrue: [^ 1].
	n := self digitLength * 8. "this will always be >= 32, because SmallInteger implements bitCount"
	n := n // 2.
	^ (self bitShift: n negated) bitCount + (self bitAnd: (1 bitShift: n) - 1) bitCount
]

{ #category : #'*mathematics' }
Integer >> bitParity [
	"Answer 1 if there are an odd number of bits set, 0 otherwise."
	| n |
	self = 0 ifTrue: [^ 0].
	self = 1 ifTrue: [^ 1].
	n := self digitLength * 8. "this will always be >= 32, because SmallInteger implements bitParity"
	n := n // 2.
	^ ((self bitShift: n negated) bitXor: (self bitAnd: (1 bitShift: n) - 1)) bitParity
]

{ #category : #'*mathematics' }
Integer >> bitParity2 [
	"Answer 1 if there are an odd number of bits set, 0 otherwise."
	| i n |
	self = 0 ifTrue: [^ 0].
	self = 1 ifTrue: [^ 1].
	i := self digitLength * 8. "this will always be >= 32, because SmallInteger implements bitParity"
	n := self.
	[i := i bitShift: -1.
	i > 30] whileTrue:
		[n := n bitXor: (n bitShift: i negated)].
	^ (n bitAnd: (1 bitShift: i) - 1) bitParity
]

{ #category : #'*mathematics' }
Integer >> bitSize [
	self negative ifTrue: [^ self negated highBit + 1].
	^ self highBit
]

{ #category : #'*mathematics' }
Integer >> choose: anInteger [
	"Answer the binomial coefficient (self anInteger)"
	" 6 choose: 3  "

	(anInteger < 0 or: [anInteger > self]) ifTrue: [^0].
	^(self - anInteger + 1 productTo: self) // anInteger factorial
]

{ #category : #'*mathematics' }
Integer >> choose: anInteger q: q [
	"Answer the q-binomial coefficient of self with anInteger.
	This counts the number of 'anInteger'-dimensional subspaces of a vector space of dimension 'self' over a finite field of order 'q' (power of a prime)."

	(anInteger < 0 or: [anInteger > self]) ifTrue: [^0].
	^ ((0 to: anInteger - 1) inject: 1 into: [:x :i| 1 - (q raisedTo:(self-i)) * x]) / ((1 to: anInteger) inject: 1 into: [:x :i| 1 - (q raisedTo:i) * x])
]

{ #category : #'*mathematics' }
Integer >> count: aBlock [
	| answer |
	answer := 0.
	self timesRepeat: [aBlock value ifTrue: [answer := answer + 1]].
	^ answer
]

{ #category : #'*mathematics' }
Integer >> denominator [
	^ 1
]

{ #category : #'*mathematics' }
Integer >> divisors [
	"Answer the collection of positive divisors of the receiver including 1 and self."
	^ Iterator on: self performing: #divisorsDo:
]

{ #category : #'*mathematics' }
Integer >> divisorsDo: aBlock [
	"Iterate over the positive divisors of the receiver, including 1 and self."
	| n sqrt |
	n := self abs.
	sqrt := n sqrtFloor.
	1 to: sqrt - 1
		do: [:k| n \\ k = 0 ifTrue: [aBlock value: k; value: n // k]].
	n \\ sqrt = 0
		ifTrue:
			[aBlock value: sqrt.
			sqrt * sqrt = n ifFalse: [aBlock value: n // sqrt]]
]

{ #category : #'*mathematics' }
Integer >> factorizationDo: aBlock [
	| n times |
	n := self abs.
	n <= 1 ifTrue: [^ self].
	n even ifTrue:
		[aBlock value: 2 value: (times := n lowBit - 1).
		n := n bitShift: times negated].
	Integer primesUpTo: n sqrtFloor + 1 do: [:p| "tests again 2, but who cares"
		n == 1 ifTrue: [^ self].
		times := 0.
		[n \\ p == 0] whileTrue: [times := times + 1. n := n // p].
		times > 0 ifTrue: [aBlock value: p value: times]].
	n == 1 ifFalse: [aBlock value: n value: 1]
]

{ #category : #'*mathematics' }
Integer >> factors [
	"Answer a collection with the prime factors of the receiver (with multiplicity)."
	| answer |
	answer := Bag new.
	self factorizationDo: [:p :e| answer add: p withOccurrences: e].
	^ answer
]

{ #category : #'*mathematics' }
Integer >> height [
	self = 0 ifTrue: [^ 1].
	^ self abs
]

{ #category : #'*mathematics' }
Integer >> isFundamentalDiscriminant [
	| m r |
	r := self \\ 4.
	r == 1 ifTrue: [^ self isSquareFree].
	r == 0 ifFalse: [^ false].
	m := self // 4.
	r := m \\ 4.
	^ (r == 2 or: [r == 3]) and: [m isSquareFree]
]

{ #category : #'*mathematics' }
Integer >> isPerfectSquare [
	^ self sqrtFloor squared = self
]

{ #category : #'*mathematics' }
Integer >> isRational [
	^ true
]

{ #category : #'*mathematics' }
Integer >> isSquareFree [
	"Answer true if the factorization of the receiver is squarefree."
	self factorizationDo: [:p :e| e > 1 ifTrue: [^ false]].
	^ true

"
The limit of the density of squarefree positive integers < n is 6 / pi^2 ~ 0.6079271:
(1000 count: [100000 atRandom isSquareFree]) / 1000.0
"
]

{ #category : #'*mathematics' }
Integer >> isZero [
	^ self == 0
]

{ #category : #'*mathematics' }
Integer >> jacobi: m [
	"Answer the Jacobi symbol of the receiver and the positive odd integer m.
	This is a generalization of the Legendre symbol that allows a composite argument m."

	^ self kronecker: m
]

{ #category : #'*mathematics' }
Integer >> jacobiNew: m [
	"Answer the Jacobi symbol of the receiver and the positive odd integer m.
	This is a generalization of the Legendre symbol that allows a composite argument m."

	"this is broken, it should satisfy: (3 jacobiNew: 11) = 1"
	| x y z answer |
	m odd ifFalse: [^ self error: 'the argument must by an odd positive integer'].
	(self gcd: m) = 1 ifFalse: [^ 0].
	x := self \\ m.
	y := m.
	answer := 1.
	[x > 1] whileTrue:
		[[x \\ 4 = 0] whileTrue: [x := x // 4].
		x \\ 2 = 0
			ifTrue:
				[x := x // 2.
				y + 2 \\ 8 > 4 ifTrue: [answer := answer negated]].
		z := y \\ x.
		y := x.
		x := z].
	^ answer
]

{ #category : #'*mathematics' }
Integer >> jacobiOld: n [
	"Answer the Jacoby symbol of the receiver and the argument."

	| a minusOne |
"	n odd ifFalse: [^ self error: 'the argument must by an odd positive integer']."
	a := self \\ n.
	a = 2 ifTrue: [^ (n squared - 1) lowBit > 3 ifTrue: [1] ifFalse: [-1]].
	minusOne := n - 1.
	a = minusOne ifTrue: [^ minusOne lowBit > 1 ifTrue: [1] ifFalse: [-1]].
	^ (a - 1 * minusOne) lowBit > 2
		ifTrue: [n jacobiOld: a] ifFalse: [(n jacobiOld: a) negated]
]

{ #category : #'*mathematics' }
Integer >> kronecker: anInteger [
	"Answer the Kronecker symbol (a | b) for a, b integers. This is the Legendre symbol when b is an odd prime.
	Reference: Henri Cohen, 'A Course in Computatational Algebraic Number Theory', Algorithm 1.4.10."
	| a b v k r |
	a := self.
	b := anInteger.
	"1. Test b = 0"
	b == 0 ifTrue: [^ a abs == 1 ifTrue: [1] ifFalse: [0]].
	"2. Remove 2's from b"
	(a even and: [b even]) ifTrue: [^ 0].
	v := b lowBit - 1.
	b := b bitShift: v negated.
	"v even ifTrue: [k := 1] ifFalse: [k := (-1) ^ (a squared - 1 / 8)]."
	v even ifTrue: [k := 1] ifFalse: [k := #(0 1 0 -1 0 -1 0 1) at: (a bitAnd: 7) + 1].
	b < 0 ifTrue: [b := b negated. a < 0 ifTrue: [k := k negated]].
	"3. Finished?"
	[a == 0 ifTrue: [^ b == 1 "b is odd and > 0" ifTrue: [k] ifFalse: [0]].
	v := a lowBit - 1.
	a := a bitShift: v negated.
	"v odd ifTrue: [k := (-1) ^ (b squared - 1 / 8) * k]."
	v odd ifTrue: [k := (#(0 1 0 -1 0 -1 0 1) at: (b bitAnd: 7) + 1) * k].
	"4. Apply reciprocity"
	"k := (-1) ^ ((a - 1)*(b - 1)/4) * k."
	((a bitAnd: b) bitAnd: 2) == 0 ifFalse: [k := k negated].
	r := a abs.
	a := b \\ r.
	b := r] repeat
]

{ #category : #'*mathematics' }
Integer >> legendre: p [
	"Answer the Legendre symbol (a | p) where p is an odd prime. This is:
		1 if a is a quadratic residue modulo p and a is not 0 modulo p;
		-1 if a is a quadratic non-residue modulo p;
		0 if a is 0 modulo p.
	See also >>jacobi: and >>kronecker:."
	| answer |
	answer := self raisedToInteger: p - 1 // 2 modulo: p.
	answer > 1 ifTrue: [answer := answer - p].
	^ answer
]

{ #category : #'*mathematics' }
Integer >> minimalPolynomial [
	^ QQ polynomials x - self
]

{ #category : #'*mathematics' }
Integer >> moebius [
	"Answer the Moebius function mu of the receiver."
	| factors |
	factors := self factors.
	factors asSet size = factors size ifFalse: [^ 0].
	^ factors size even ifTrue: [1] ifFalse: [-1]
]

{ #category : #'*mathematics' }
Integer >> multiplicativeOrder [
	^ self == 1 ifTrue: [1] ifFalse: [self == -1 ifTrue: [2] ifFalse: [Infinity positive]]
]

{ #category : #'*mathematics' }
Integer >> numberOfDivisors [
	^ self primeSignature inject: 1 into: [:x :each| x * (each + 1)]
]

{ #category : #'*mathematics' }
Integer >> numerator [
	^ self
]

{ #category : #'*mathematics' }
Integer >> parent [
	^ ZZ
]

{ #category : #'*mathematics' }
Integer >> partitions [
	^ Iterator on: self performing: #partitionsDo:
]

{ #category : #'*mathematics' }
Integer >> partitionsDo: aBlock [
	self < 0 ifTrue: [^ DomainError signal: 'negative number'].
	self = 0 ifTrue: [^ aBlock value: #()].
	self - 1 partitionsDo: [:each|
		aBlock value: #(1), each.
		(each size > 0 and: [each size < 2 or: [(each at: 2) > (each at: 1)]])
			ifTrue: [aBlock value: (each copy at: 1 put: (each at: 1) + 1; yourself)]]
]

{ #category : #'*mathematics' }
Integer >> phi [
	"Answer Euler's totient function phi of the receiver."
	^ (1 to: self) count: [:each| (self gcd: each) = 1]
]

{ #category : #'*mathematics' }
Integer >> pollard [
	"Answer a non trivial factor of the receiver.
	Pollard's p-1 algorithm is used. This works well to find a prime factor p such that p - 1 is smooth."

	| N a x y p count |
	N := self abs.
	a := N atRandom.
	x := N atRandom.
	y := x.
	count := 1.
	[x := x squared + a \\ self.
	y := (y squared + a \\ self) squared + a \\ self.
	(p := y - x gcd: self) = 1
		ifFalse: [^ Array with: p with: count].
	count := count + 1] repeat
]

{ #category : #'*mathematics' }
Integer >> pollard: L [
	"Answer a nontrivial factor of the receiver, or nil if fail.
	This is Pollard's p-1 algorithm. It works well with numbers divisible by a prime p such that p - 1 is smooth with some small factor q^k where k*q <= L."
	| N A F |
	N := self abs.
	A := (2 to: N-1) atRandom.
	1 to: L do: [:i|
		A := A raisedTo: i modulo: N.
		(F := A - 1 gcd: N) = 1
			ifFalse: [^ F]].
	^ nil
]

{ #category : #'*mathematics' }
Integer >> primeSignature [
	| factors |
	factors := self factors.
	^ (factors asSet asSortedCollection collect: [:each| factors occurrencesOf: each]) asArray
]

{ #category : #'*mathematics' }
Integer >> radical [
	"Answer the product of the prime divisors of the receiver."
	| answer |
	answer := self sign.
	self factorizationDo: [:p :e| answer := answer * p].
	^ answer
]

{ #category : #'*mathematics' }
Integer >> reciprocalModulo2: n [
	"Answer an integer x such that self * x \\ n = 1, with 0 < x < n, or nil if it doesn't exist."
	| xgcd |
	self == 0 ifTrue: [^ nil].
	self == 1 ifTrue: [^ 1].
	xgcd := self xgcd: n.
	^ (xgcd at: 1) == 1 ifTrue: [^ (xgcd at: 2) \\ n]
]

{ #category : #'*mathematics' }
Integer >> reciprocalModulo: mod [
	"Answer an integer x such that self * x \\ n = 1, with 0 < x < n, or nil if x does not exist.
	The algorithm is a non extended euclidean modular inversion called NINV.
	It is described in this article:
		'Using an RSA Accelerator for Modular Inversion'
	by Martin Seysen. See http://www.iacr.org/archive/ches2005/017.pdf"

	| receiver u v f fPlusN b result result2 |
	mod > 1 ifFalse: [^nil].
	receiver := (self >= mod or: [self < 0])
		ifTrue: [self \\ mod] ifFalse: [self].
	b := mod highBit + 1.
	f := 1 bitShift: b.
	v := (receiver bitShift: b) + 1.
	u := mod bitShift: b.
	fPlusN := f + mod.
	[v >= fPlusN] whileTrue:
		[v := u \\\ (u := v)].
	result := v - f.
	result2 := result + mod.
	result2 > 0 ifFalse: [^nil].
	^result positive
		ifTrue: [result]
		ifFalse: [result2]
]

{ #category : #'*mathematics' }
Integer >> squareFree [
	"Answer the unique integer z such that the receiver equals z * y^2 with z squarefree and y^2 a perfect square."
	| answer |
	answer := self sign.
	self factorizationDo: [:p :e| e even ifFalse: [answer := answer * p]].
	^ answer
]

{ #category : #'*mathematics' }
Integer >> squareRoot [
	self positive ifTrue: [^ RealAlgebraicNumber sqrt: self].
	^ ComplexAlgebraicNumber sqrt: self
]

{ #category : #'*mathematics' }
Integer >> stirling: anInteger [
	"Answer the Stirling number of the first kind s(n,k).
	Stirling numbers of the first kind count the ways to arrange n objects into k cycles."
	(anInteger > self or: [self < 0]) ifTrue: [^ DomainError signal].
	anInteger = 1 ifTrue: [^ (self - 1) factorial].
	self = anInteger ifTrue: [^ self Stirling: anInteger].
	self+1 = anInteger ifTrue: [^ self choose: 2].
	^ (self-1) * (self-1 stirling: anInteger) + (self-1 stirling: anInteger-1)
]

{ #category : #'*mathematics' }
Integer >> xgcd: anInteger [
	"Extended Euclidean algorithm.
	Answer an array {x. u. v} where self * u + (anInteger * v) = x, and x = (self gcd: anInteger)."
	| a b s1 t1 s t r1 r |
	a := self. b := anInteger.
	s1 := 0. s := 1.
	t1 := 1. t := 0.
	r1 := a abs. r := b abs.
	[r1 == 0]
		whileFalse:
			[ | q temp |
			q := r // r1.
			temp := r1. r1 := r - (q * r1). r := temp.
			temp := s1. s1 := s - (q * s1). s := temp.
			temp := t1. t1 := t - (q * t1). t := temp].
	s := s * b sign. t := t * a sign.
	^ {r. t. s}
]

{ #category : #'*mathematics' }
Integer >> | anInteger [
	"Answer true if the receiver divides anInteger."
	^ self ~= 0 and: [anInteger \\ self = 0]
]
