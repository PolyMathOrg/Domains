"
Sequences are functions with domain the natural numbers {1,2,...}. They can be evaluated at an index (#value: and #at:), and can also be iterated over like Smalltalk collections (#do:, #collect:, #select, etc).

Example (the Fibonacci sequence):
	Sequence initialValues: #(0 1) recurrence: [:f :n| (f at: n-1) + (f at: n-2)].

Example (the harmonic numbers):
	Sequence to: QQ evaluating: [:n| (1 to: n) sum: [:k| 1/k]].

Each sequence has an associated generating series, which is the formal power series with coefficients given by the sequence (see PowerSeries):
	Sequence fibonacci generatingSeries
and Dirichlet series (see DirichletSeries):
	Sequence fibonacci dirichletSeries

"
Class {
	#name : #Sequence,
	#superclass : #Function,
	#category : #'Mathematics-Sequences'
}

{ #category : #examples }
Sequence class >> Omega [
	"Number of prime divisors of n counted with multiplicity. A001222."
	
	^ Sequence evaluating: [ :n | n factors size ]
]

{ #category : #examples }
Sequence class >> aliquot [
	"This is the aliquot function a(n) or s(n).
	It is the sum of the proper divisors of n (aliquot parts of n).
	If a(n) = n, n is a perfect number. If a(n) = n - 1, it is almost perfect. If a(n) > n, it is an abundant number."

	^ Sequence evaluating: [ :n | n divisors sum - n ]
]

{ #category : #examples }
Sequence class >> bbs: s p: p q: q [
	"Answer the Blum Blum Shub sequence for the given parameters."

	| lambda m |
	lambda := p - 1 lcm: q - 1.
	m := p * q.
	^ self
		evaluating: [ :i | s raisedTo: (2 raisedTo: i modulo: lambda) modulo: m ]
]

{ #category : #examples }
Sequence class >> bellNumbers [
	"The Bell numbers."
	^ (Sequence
		evaluating: [ :n | (0 to: n) sum: [ :k | n Stirling: k ] ])
		startIndex: 0
]

{ #category : #examples }
Sequence class >> bernoulli [
	"This is the sequence of Bernoulli numbers (starting at 1), computed via a recurrence."
	
	^ Sequence
		to: QQ
		initialValues: #(1)
		recurrence: [ :f :n | 
			(n > 4 and: [ n even ])
				ifTrue: [ 0 ]
				ifFalse: [ ((0 to: n - 2) sum: [ :k | (n choose: k) * (f at: k + 1) ])
						/ n negated ] ]
]

{ #category : #examples }
Sequence class >> calkinWilf [
	"The Calkin-Wilf sequence.
	It enumerates the positive rational numbers by a breadth-first traversal of the Calkin-Wilf tree."

	^ Sequence
		to: QQ
		evaluating: [ :n | 
			| q |
			q := 1.
			n - 1 timesRepeat: [ q := 1 / (2 * q floor - q + 1) ].
			q ]
]

{ #category : #examples }
Sequence class >> catalanNumbers [
	"The Catalan numbers."
	^ Sequence evaluating: [:n| (2*(n-1) choose: n-1) / n]
]

{ #category : #'intance creation' }
Sequence class >> constant: anInteger [
	anInteger isInteger
		ifFalse: [ ^ DomainError signal: 'argument is not integer' ].
	^ self to: ZZ constant: anInteger
]

{ #category : #'intance creation' }
Sequence class >> dynamic: aBlock [
	^ self to: ZZ dynamic: aBlock
]

{ #category : #'intance creation' }
Sequence class >> evaluating: aBlock [
	^ self to: ZZ evaluating: aBlock
]

{ #category : #examples }
Sequence class >> fibonacci [
	"The Fibonacci sequence defined as a recurrence."
	
	^ Sequence
		initialValues: #(0 1)
		recurrence: [ :f :n | (f at: n - 1) + (f at: n - 2) ]
]

{ #category : #examples }
Sequence class >> harmonicNumbers [
	"The harmonic numbers."
	^ Sequence to: QQ evaluating: [:n| (1 to: n) sum: [:k| 1/k]]
]

{ #category : #examples }
Sequence class >> hensel: aPolynomial at: anIntegerRoot mod: p [
	"Answer the p-adic expansion by Hensel lemma."
	| x |
	x := aPolynomial species x.
	^ 'self recurrence:
			[:f :n|
			n = 1
				ifTrue: [anIntegerRoot]
				ifFalse:
					[| g a |
					g := (f at: n-1) + (p^(n-1) * x).
					a := (aPolynomial value: g % (p^n)) roots anyOne representative.
					(g value: a) \\ (p^n)]]'
]

{ #category : #examples }
Sequence class >> highlyCompositeNumbers [
	"The sequence of highly composite numbers."
	^ Sequence recurrence: [:f :n| | i max |
		n = 1
			ifTrue: [1]
			ifFalse:
				[i := f at: n-1.
				max := i numberOfDivisors.
				[(i := i + 1) numberOfDivisors > max] whileFalse. i]]
]

{ #category : #examples }
Sequence class >> id [
	"The identity sequence."
	^ Sequence evaluating: [:n| n]
]

{ #category : #'intance creation' }
Sequence class >> initialValues: anArray recurrence: aBinaryBlock [
	^ self to: ZZ initialValues: anArray recurrence: aBinaryBlock
]

{ #category : #examples }
Sequence class >> liouville [
	"The Liouville function."
	| Omega |
	Omega := Sequence Omega.
	^ 'Sequence evaluating: [:n| (-1) ^ (Omega at: n)]'
]

{ #category : #examples }
Sequence class >> mangoldt [
	"The von Mangoldt function (float)."
	^ Sequence evaluating: [:n| | factors | factors := n factors. factors asSet size = 1 ifTrue: [factors anyOne ln] ifFalse: [0]]
]

{ #category : #examples }
Sequence class >> mangoldt2 [
	"The log2 von Mangoldt function."
	^ Sequence evaluating: [:n| | factors | factors := n factors. factors asSet size = 1 ifTrue: [factors anyOne highBit] ifFalse: [0]]
]

{ #category : #examples }
Sequence class >> moebius [
	"The Moebius function mu(n).
	This is 0 if n is squarefree, and (-1)^k otherwise (where k is the number of prime factors counted with multiplicity)."
	^ Sequence evaluating: [:n| n moebius]
]

{ #category : #examples }
Sequence class >> omega [
	"Number of distinct primes dividing n. A001221."
	^ Sequence evaluating: [:n| n factors asSet size]
]

{ #category : #examples }
Sequence class >> one [
	"The constant sequence that is always 1."
	^ Sequence constant: 1
]

{ #category : #examples }
Sequence class >> partitions [
	"The partition function p(n) = number of partition of n. OEIS A000041."
	^ Sequence evaluating: [:n| n partitions size]
]

{ #category : #examples }
Sequence class >> phi [
	"Euler's totient function."
	^ Sequence evaluating: [:n| n phi]
]

{ #category : #examples }
Sequence class >> primeGaps [
	"The sequence of prime gaps.
	This is p(n+1) - p(n), the difference between concecutive primes."
	| p |
	p := 2.
	^ Sequence streamming: [p negated + (p := p nextPrime)]
"	^ Sequence primes difference"
]

{ #category : #examples }
Sequence class >> primes [
	"The sequence of primes."
	^ Sequence initialValues: #(2) recurrence: [:f :i| (f at: i-1) nextPrime]
"	^ Sequence evaluating: [:i|
		| n count |
		n := 2.
		count := 1.
		[count = i] whileFalse: [n := n nextPrime. count := count + 1].
		n]"
]

{ #category : #'intance creation' }
Sequence class >> recurrence: aBinaryBlock [
	^ self initialValues: #() recurrence: aBinaryBlock
]

{ #category : #examples }
Sequence class >> sigma [
	"The sigma(n) function, defined as the sum of the positive divisors of n.
	The number n is said to be a perfect number iff sigma(n) = 2*n."
	^ Sequence evaluating: [:n| n divisors sum]
]

{ #category : #examples }
Sequence class >> sigma: x [
	"Answer the sigma(x,n) function."
	^ Sequence evaluating: [:n| n divisors sum: [:d| d raiseTo: x]]
]

{ #category : #'intance creation' }
Sequence class >> streamming: aBlock [
	^ self to: ZZ streamming: aBlock
]

{ #category : #examples }
Sequence class >> tau [
	"Number of divisors of n, also called d(n) and sigma_O(n). A000005."
	^ Sequence evaluating: [:n| n divisors size]
]

{ #category : #'intance creation' }
Sequence class >> to: aDomain constant: anObject [
	^ self to: aDomain evaluating: [:n| anObject]
]

{ #category : #'intance creation' }
Sequence class >> to: aDomain dynamic: aBlock [
	^ self to: aDomain evaluating:
			[:n| | x |
			x := 0.
			n timesRepeat: [x := aBlock value: x].
			x]
]

{ #category : #'intance creation' }
Sequence class >> to: aDomain evaluating: aBlock [
	^ self from: NN to: aDomain evaluating: aBlock
]

{ #category : #'intance creation' }
Sequence class >> to: aDomain initialValues: anArray recurrence: aBlock [
	| cache |
	cache := OrderedCollection withAll: anArray.
	^ self to: aDomain evaluating:
			[:n|
			"(n isInteger and: [n > 0]) ifFalse: [DomainError signal]."
			[cache size < n] whileTrue: [cache add: (aBlock value: cache value: cache size + 1)].
			cache at: n]
]

{ #category : #'intance creation' }
Sequence class >> to: aDomain recurrence: aBlock [
	^ self to: aDomain initialValues: #() recurrence: aBlock
]

{ #category : #'intance creation' }
Sequence class >> to: aDomain streamming: aBlock [
	| cache |
	cache := OrderedCollection new.
	^ self to: aDomain evaluating:
			[:n|
			"(n isInteger and: [n > 0]) ifFalse: [DomainError signal]."
			[cache size < n] whileTrue: [cache add: aBlock value].
			cache at: n]
]

{ #category : #operations }
Sequence >> << anInteger [
	^ self shift: anInteger negated
]

{ #category : #operations }
Sequence >> >> anInteger [
	^ self shift: anInteger
]

{ #category : #converting }
Sequence >> asStream [
	^ ReadStream on: self
]

{ #category : #accessing }
Sequence >> at: anInteger [
	^ anInteger >= 0 ifTrue: [super value: anInteger]
]

{ #category : #operations }
Sequence >> average [
	^ self species to: self codomain evaluating: [:N| ((1 to: N) sum: [:n| self at: n]) / N]
]

{ #category : #comparing }
Sequence >> beginsWith: aSequenceableCollection [
	1 to: aSequenceableCollection size do: [:i| (self at: i) = (aSequenceableCollection at: i) ifFalse: [^ false]].
	^ true
]

{ #category : #series }
Sequence >> bellSeries: p [
	^ 'PowerSeries coefficients: (self species to: self codomain evaluating: [:n| self at: p^(n-1)])'
]

{ #category : #operations }
Sequence >> binomialTransform [
	"The binomial transform is its own inverse, it's an involution."
	^ 'self species to: self codomain evaluating: [:n| (0 to: n) sum: [:k| (-1)^(n-k) * (n choose: k) * (self at: k)]]'
]

{ #category : #operations }
Sequence >> binomialTransform2 [
	^ self species to: self codomain evaluating: [:n| (0 to: n) sum: [:k| (n choose: k) * (self at: k)]]
]

{ #category : #accessing }
Sequence >> codomain [
	^ self propertyAt: #codomain ifAbsent: [ZZ]
]

{ #category : #enumerating }
Sequence >> collect: aBlock [
	^ self species evaluating: [:i| aBlock value: (self at: i)]
]

{ #category : #operations }
Sequence >> convolution: aSequence [
	^ self species to: self codomain evaluating: [:n| (0 to: n-1) sum: [:i| (self at: self startIndex + i) * (aSequence at: aSequence startIndex+n-1-i)]]
]

{ #category : #copying }
Sequence >> copyFrom: start to: end [
	end isInfinite
		ifTrue: [^ self shift: 1 - start].
	^ (start to: end) collect: [:i| self at: i]
]

{ #category : #enumerating }
Sequence >> count: aBlock [
	^ (self collect: [:each| (aBlock value: each) ifTrue: [1] ifFalse: [0]]) sum
]

{ #category : #operations }
Sequence >> difference [
	"Answer the 'difference' sequence of the receiver, or delta, or discrete derivative."
	^ (self shift: -1) - self
]

{ #category : #operations }
Sequence >> dirichlet: aSequence [
	"Answer the Dirichlet convolution of the receiver with the argument, assuming both are arithmetic functions (i.e. functions from the natural numbers to the complex numbers).
	The set of arithmetic functions form a commutative ring (the Dirichlet ring) under pointwise addition and Dirichlet convolution."
	^ self species to: self codomain evaluating: [:n| n divisors sum: [:d| (self at: d) * (aSequence at: n/d)]]
]

{ #category : #series }
Sequence >> dirichletSeries [
	"Answer the Dirichlet series generating function of the receiver."
	^ DirichletSeries coefficients: self
]

{ #category : #enumerating }
Sequence >> do: aBlock [
	1 to: self size do: [:each| aBlock value: (self at: each)]
]

{ #category : #accessing }
Sequence >> domain [
	^ self propertyAt: #domain ifAbsent: [NN]
]

{ #category : #comparing }
Sequence >> equals: aSequence upTo: n [
	^ self beginsWith: (aSequence copyFrom: 1 to: n)
]

{ #category : #series }
Sequence >> exponentialSeries [
	"Answer the exponential generating function of the receiver."
	^ PowerSeries coefficients: (self species to: self codomain evaluating: [:n| (self at: n) / (n-1) factorial])
]

{ #category : #copying }
Sequence >> first: n [
	^ self copyFrom: 1 to: n
]

{ #category : #series }
Sequence >> generatingSeries [
	"Answer the ordinary generating function of the receiver."
	^ self ordinaryGeneratingSeries
]

{ #category : #operations }
Sequence >> hadamard: aSequence [
	"Answer the entrywise product with the argument, also called Hadamard product."
	^ self class evaluating: [:i| (self at: i) * (aSequence at: i)]
]

{ #category : #comparing }
Sequence >> hash [
	^ (self at: 1) hash + (self at: 3) hash + (self at: 5) hash
]

{ #category : #printing }
Sequence >> lookup [
	^ OEIS default lookup: self
]

{ #category : #operations }
Sequence >> moebiusInverse [
	"This is equivalent to the Dirichlet convolution of the Moebius arithmetic function with the receiver.
	If f(n) and g(n) are two arithmetic functions satisfying g = f * 1 (Dirichlet convolution of f with the constant function 1), then the Moebius inversion formula can be used to retrieve f as f = mu * g. It is said that f and g and Moebius transforms of each other."
	^ self species to: self codomain evaluating: [:n| n divisors sum: [:d| d moebius * (self at: n/d)]]
]

{ #category : #series }
Sequence >> ordinaryGeneratingSeries [
	"Answer the ordinary generating function of the receiver."
	^ PowerSeries coefficients: self
]

{ #category : #printing }
Sequence >> printLimit [
	^ self propertyAt: #printLimit ifAbsent: [17]
]

{ #category : #printing }
Sequence >> printLimit: anInteger [
	self propertyAt: #printLimit put: anInteger
]

{ #category : #printing }
Sequence >> printOn: aStream [
	(self startIndex to: self printLimit) do: [:i| aStream print: (self at: i)] separatedBy: [aStream nextPutAll:', ' ].
	aStream nextPutAll: '...'
]

{ #category : #printing }
Sequence >> printOn: aStream base: base [
	(1 to: self printLimit) do: [:i| (self at: i) printOn: aStream base: base] separatedBy: [aStream nextPutAll:', ' ].
	aStream nextPutAll: '...'
]

{ #category : #printing }
Sequence >> printStringBase: base [
	^ String streamContents:
		[:aStream| self printOn: aStream base: base]
]

{ #category : #operations }
Sequence >> product [
	"Answer the indefinite product of the receiver."
	^ self species to: self codomain evaluating: [:i| (1 to: i) collect: [:k| self at: k] andFold: [:a :b| a*b]]
]

{ #category : #enumerating }
Sequence >> select: aBlock [
	^ self species evaluating: [:i|
		| k j value |
		k := 1.
		j := 1.
		[[aBlock value: (value := self at: k)] whileFalse: [k := k + 1]. j < i] whileTrue: [j := j + 1. k := k + 1].
		value]
]

{ #category : #operations }
Sequence >> shift: anInteger [
	^ self species to: self codomain evaluating: [:i| self at: i-anInteger]
]

{ #category : #accessing }
Sequence >> size [
	^ self propertyAt: #size ifAbsent: [Aleph new]
]

{ #category : #private }
Sequence >> species [
	^ Sequence
]

{ #category : #accessing }
Sequence >> startIndex [
	^ self propertyAt: #startIndex ifAbsent: [1]
]

{ #category : #private }
Sequence >> startIndex: anInteger [
	self propertyAt: #startIndex put: anInteger
]

{ #category : #operations }
Sequence >> stirlingInverseTransform [
	^ self species to: self codomain evaluating: [:n| (1 to: n) sum: [:k| (n stirling: k) * (self at: k)]]
]

{ #category : #operations }
Sequence >> stirlingTransform [
	^ self species to: self codomain evaluating: [:n| (1 to: n) sum: [:k| (n Stirling: k) * (self at: k)]]
]

{ #category : #operations }
Sequence >> sum [
	"Answer the indefinite sum of the receiver."
	^ self species to: self codomain evaluating: [:i| (1 to: i) sum: [:k| self at: k]]
]

{ #category : #operations }
Sequence >> value: aNumber [
	^ self at: aNumber asInteger
]

{ #category : #enumerating }
Sequence >> withIndexDo: aBlock [
	| i |
	i := 1.
	self do: [:each| aBlock value: each value: i. i := i + 1]
]
