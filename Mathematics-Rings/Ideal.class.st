"
Finitely-generated ideals of a commutative ring.

For an arbitrary ring R, a subset I <= R is called a (two-sided) ideal of R if it's a subgroup of R (as group under addition) and ""absorbs multiplication by elements of R"", i.e. I * R = I and R * I = I.

Equivalently, an ideal of R is a R-submodule of R.

Ideals are the ring theory analog of normal subgroups from group theory. They are 'normal subobjects' that are in one-to-one correspondence with certain congruences, and this allows to quotient by them. Given a ring R and an ideal I, the quotient R/I can be constructed (see QuotientRing). Ideals are the kernels of ring homomorphisms.

References:
	https://en.wikipedia.org/wiki/Ideal_(ring_theory)
"
Class {
	#name : #Ideal,
	#superclass : #Module,
	#category : #'Mathematics-Rings'
}

{ #category : #examples }
Ideal class >> example1 [
	"Creating an ideal of Z:"
	^ ZZ * {12. 18. 60}
]

{ #category : #examples }
Ideal class >> example2 [
	"Creating an ideal in Z/3Z[x,y,z]:"
	| R x y z |
	R := ZZ/3 polynomialsIn: #(x y z).
	x := R x.
	y := R y.
	z := R z.
	^ 'R * {x^2 + (y^2). x*y + (y^2) + (y*z). y^2 + (z^2) + z}'
]

{ #category : #'instance creation' }
Ideal class >> over: aRing generators: aCollection [
	^ self new scalars: aRing; generators: aCollection
]

{ #category : #operations }
Ideal >> * anElementOrIdeal [
	"The product is included in the intersection: I*J <= I /\ J.
	When the ideals are comaximal, the equality holds."
	| newGenerators |
	(self scalars includes: anElementOrIdeal) ifTrue: [^ self class over: self scalars generators: (self generators collect: [:each| each * anElementOrIdeal])].
	anElementOrIdeal scalars = self scalars ifFalse: [^ DomainError signal: 'ideal from different rings'].
	newGenerators := Set new.
	self generators do: [:a| anElementOrIdeal generators do: [:b| newGenerators add: a*b]].
	^ self scalars * newGenerators
]

{ #category : #operations }
Ideal >> + anIdeal [
	anIdeal scalars = self scalars ifFalse: [^ DomainError signal: 'ideals from different rings'].
	^ self scalars * (self generators asSet copy addAll: anIdeal generators; yourself)
]

{ #category : #operations }
Ideal >> / anIdeal [
	"If the receiver is an ideal I in a ring R, and the argument is an ideal J in R, answer the projection of I to the quotient ring R/J."
	| Q |
	((anIdeal isKindOf: Ideal) and: [self scalars = anIdeal scalars]) ifFalse: [^ super / anIdeal].
	Q := self scalars / anIdeal.
	^ Q * (self generators collect: [:each| Q project: each])
]

{ #category : #operations }
Ideal >> /\ anIdeal [
	"Meet."
	^ self ï anIdeal
]

{ #category : #comparing }
Ideal >> < anIdeal [
	"Answer true if the receiver is strictly included in the argument."
	^ self ~= anIdeal and: [self <= anIdeal]
]

{ #category : #comparing }
Ideal >> <= anIdeal [
	"Answer true if the receiver is included in the argument."
	self == anIdeal ifTrue: [^ true].
	self generators do: [:each| (anIdeal includes: each) ifFalse: [^ false]].
	^ true
]

{ #category : #comparing }
Ideal >> = anIdeal [
	self == anIdeal ifTrue: [^ true].
	(anIdeal isKindOf: Ideal) ifFalse: [^ false].
	self scalars = anIdeal scalars ifFalse: [^ false].
	self generators = anIdeal generators ifTrue: [^ true].
	^ self <= anIdeal and: [anIdeal <= self]
]

{ #category : #operations }
Ideal >> \/ anIdeal [
	"Join."
	^ self + anIdeal
]

{ #category : #accessing }
Ideal >> ambient [
	^ self scalars asSelfModule
]

{ #category : #operations }
Ideal >> annihilator [
	^ 'self scalars zeroIdeal ˜ self'
]

{ #category : #morphisms }
Ideal >> apply: aMorphism [
	"Apply a ring homomorphism phi to the receiver, sending each generator g to phi(g)."
	aMorphism isBlock
		ifTrue: [^ self scalars * (self generators collect: aMorphism)].
	aMorphism domain = self scalars
		ifTrue: [^ aMorphism codomain * (self generators collect: aMorphism)].
	^ super apply: aMorphism
]

{ #category : #converting }
Ideal >> asIdeal [
	^ self
]

{ #category : #random }
Ideal >> atRandom: aRandom bits: bitSize [
	self isZero ifTrue: [^ self scalars zero].
	^ self generators sum: [:each| each * (self scalars atRandom: aRandom bits: bitSize / self generators size)]
]

{ #category : #accessing }
Ideal >> codimension [
	"Answer the Krull codimension of the receiver."
	^ self quotientRing codimension
]

{ #category : #testing }
Ideal >> contains: anObject [
	self isZero ifTrue: [^ anObject isZero].
	^ (self reduce: anObject) isZero
]

{ #category : #copying }
Ideal >> copy [
	"Answer a copy of the receiver."
	^ self class over: self scalars generators: self generators copy
]

{ #category : #accessing }
Ideal >> denominator [
	^ self scalars one
]

{ #category : #accessing }
Ideal >> dimension [
	"Answer the Krull dimension of the quotient ring of the base ring by the receiver."
	^ self quotientRing dimension
]

{ #category : #enumerating }
Ideal >> do: aBlock [
	self scalars isCommutative
		ifTrue:
			[self scalars do: [:each| self generators do: [:g| aBlock value: each * g]]]
		ifFalse:
			[self scalars do: [:each| self generators do: [:g| aBlock value: each * g; value: g * each]]]
]

{ #category : #operations }
Ideal >> dot: anIdeal [ "ï "
	"Answer the intersection of the receiver and the argument."
	^ self scalars * (self generator lcm: anIdeal generator)
]

{ #category : #accessing }
Ideal >> generator [
	| generator |
	self generators size = 1 ifTrue: [^ self generators anyOne].
	self generators size = 0 ifTrue: [^ self scalars zero].
	self scalars isPID ifFalse: [^ self error: 'not a principal ideal domain'].
	self generators do: [:each| generator := generator isNil ifTrue: [each] ifFalse: [generator gcd: each]].
	self generators: {generator}.
	^ generator
]

{ #category : #'accessing-private' }
Ideal >> generators: aCollection [
	| generators |
	generators := aCollection asSet reject: [:each| each isZero].
"	generators size = aCollection size ifTrue: [generators := aCollection]." "keep order if possible"
	(generators size > 1 and: [[self scalars isPID] ifError: [false]])
		ifTrue:
			[| generator |
			generators do: [:each| generator := generator isNil ifTrue: [each] ifFalse: [generator gcd: each]].
			generators := {generator}].
	super generators: generators
]

{ #category : #comparing }
Ideal >> hash [
	^ self scalars hash
]

{ #category : #accessing }
Ideal >> height [
	"Answer the height (or codimension, or rank) of the receiver."
	^ (self scalars localizationAt: self) dimension
]

{ #category : #testing }
Ideal >> includes: anElement [
	^ (self scalars includes: anElement) and: [self contains: anElement]
]

{ #category : #'operations-elements' }
Ideal >> inverseOf: anElement [
	"This works only for ideals of an euclidean domain given by one generator."
	| euclid |
	self scalars isEuclideanDomain ifFalse: [^ nil].
	euclid := ExtendedEuclid on: {anElement. self generator}.
	euclid gcd = self scalars one ifFalse: [^ nil].
	^ euclid bezout first
]

{ #category : #testing }
Ideal >> isComaximalWith: anIdeal [
	^ (self + anIdeal) isOne
]

{ #category : #testing }
Ideal >> isIntegral [
	"This is an integral ideal (not a fractional ideal)."
	^ true
]

{ #category : #testing }
Ideal >> isMaximal [
	"An ideal I of R is called 'maximal' if it is not contained in any other ideal but R itself.
	I is maximal iff R/I is a field."
	self scalars isPID ifFalse: [^ self propertyAt: #isMaximal].
	(self scalars isField not and: [self isZero]) ifTrue: [^ false].
	^ self isPrime
]

{ #category : #testing }
Ideal >> isNilIdeal [
	"An ideal is called nil-ideal if all its elements are nilpotent."
	^ self generators allSatisfy: [:each| self ambient isNilpotent: each]
]

{ #category : #testing }
Ideal >> isNilpotent [
	"An ideal I is called nilpotent if there is an integer n >= 1 such that I^n = 0."
	^ self notYetImplemented
]

{ #category : #testing }
Ideal >> isOne [
	"Answer true if the receiver is the unit ideal <1> that equals the whole ambient ring."
	^ self includes: self scalars one
]

{ #category : #testing }
Ideal >> isPrime [
	"An ideal I of R is prime iff R/I is an integral domain.
	This method only works for zero ideals or ideals given by one generator. Subclasses should reimplement."
	(self scalars isIntegralDomain and: [self isZero]) ifTrue: [^ true].
	(self scalars isUFD and: [self isPrincipal]) ifTrue: [^ self scalars isIrreducible: self generator].
	^ self subclassResponsibility
]

{ #category : #testing }
Ideal >> isPrincipal [
	"Answer true if the receiver is generated by a single element."
	self generators size <= 1 ifTrue: [^ true].
	self scalars isPID ifTrue: [^ true].
	^ self propertyAt: #isPrincipal
]

{ #category : #testing }
Ideal >> isProper [
	^ self isZero not and: [self isOne not]
]

{ #category : #testing }
Ideal >> isRadical [
	^ self = self radical
]

{ #category : #testing }
Ideal >> isSaturated [
	^ self = self saturation
]

{ #category : #testing }
Ideal >> isSquareFree [
	^ self = self squareFree
]

{ #category : #testing }
Ideal >> isZero [
	"Answer true if the receiver is the zero ideal {0}."
	^ self generators allSatisfy: [:each| each isZero]
]

{ #category : #accessing }
Ideal >> numerator [
	^ self
]

{ #category : #converting }
Ideal >> over: aRing [
	^ (self scalars over: aRing) ! self
]

{ #category : #printing }
Ideal >> printOn: aStream [
	self isZero ifTrue: [aStream nextPut: ${; print: self scalars zero; nextPut: $}. ^ self].
	aStream nextPut: $<.
	(self generators asSortedCollection: [:a :b| a printString <= b printString])
		do: [:each| aStream print: each] separatedBy: [aStream nextPutAll: ', '].
	aStream nextPut: $>
]

{ #category : #operations }
Ideal >> quot: anIdeal [ "˜ "
	"Answer the colon quotient I:J of the receiver I with the argument J."
	self subclassResponsibility
]

{ #category : #operations }
Ideal >> quotientRing [
	"Answer the quotient ring of the base ring by the receiver."
	"is this ok? this is actually isomorphic to the quotient we mean, but maybe is ok, we have some quotient defined by relations and we just add more relations, also makes sense"
"	self flag: #fix.
	self ring isQuotient
		ifTrue: [^ self ring base / (self ring ideal generators, (self generators collect: [:each| each representative]))]."
	^ QuotientRing mod: self
]

{ #category : #operations }
Ideal >> radical [
	^ self subclassResponsibility
]

{ #category : #operations }
Ideal >> raisedTo: anInteger [
	"Answer the receiver raised to the power anInteger."

	anInteger <= 0
		ifTrue: [ self error: 'exponent is not positive' ].
	anInteger = 1
		ifTrue: [ ^ self ].
	"	anInteger = 0 ifTrue: [^ self ring oneIdeal].
		anInteger < 0 ifTrue: [^ (self ^ anInteger negated) reciprocal]."
	^ ((self squared) raisedTo: (anInteger // 2)) * (self raisedTo: (anInteger \\ 2))
]

{ #category : #'operations-elements' }
Ideal >> reduce: anElement [
	"Answer the normal form of anElement with respect to the receiver.
	It is required that:
		(I reduce: x) = (I reduce: y) <=> x-y is in I, and
		x - (I reduce: x) is in I for all x, y in I.
	Subclasses should override."
	self isZero ifTrue: [^ anElement].
	^ anElement \\ self generator
]

{ #category : #operations }
Ideal >> saturation [
	"Answer the saturation ideal I:I^infinity of the receiver I."
	^ self saturation: self
]

{ #category : #accessing }
Ideal >> scalars [
	^ self propertyAt: #scalars
]

{ #category : #operations }
Ideal >> squareFree [
	^ self scalars
		* (self generators collect: [ :each | each squareFree ])
]

{ #category : #testing }
Ideal >> | anIdeal [
	"Answer true if the receiver divides anIdeal."
	^ self >= anIdeal
]
