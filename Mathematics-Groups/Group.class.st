"
Groups consist of a set with an associative binary operation, an inverse map (every element has an inverse), and an identity element.

Small groups can be represented explicitly (and naively) as a set of elements, plus a distinguished 'identity' element, group operation and inverse map. Groups can be also defined and represented more compactly by a set of generators.

Some specific groups (such as permutation groups and matrix groups) can be represented in more efficient ways, and operate with more efficient algorithms. See subclasses.

References:
	https://en.wikipedia.org/wiki/Group_(mathematics)
"
Class {
	#name : #Group,
	#superclass : #Monoid,
	#category : #'Mathematics-Groups'
}

{ #category : #examples }
Group class >> alternating: aCollection [
	"Answer the group of alternate permutations of aCollection."
	^ ((self symmetric: aCollection) select: [:each| each even]) name: 'Alt(', aCollection printString, ')'
]

{ #category : #examples }
Group class >> integersMod: anInteger [
	"Answer the cyclic group of integers modulo anInteger."
	^ AbelianGroup new elements: ((0 to: anInteger-1) collect: [:x| x % anInteger]) asSet
]

{ #category : #examples }
Group class >> quaternions [
	"Answer the quaternionic group.
	https://en.wikipedia.org/wiki/Quaternion_group"

	^ Group new
		generators:
			{Quaternion i.
			Quaternion j}
]

{ #category : #examples }
Group class >> schnorr: q [
	"Answer a Schnorr group of the given prime order q.
	This is a subgroup of the  group of (units of) integers modulo p
	for some prime p (with order p-1)."
	| p r h g |
	r := 1.
	[(p := q*r + 1) isPrime] whileFalse: [r := r + 1].
	[h := (1 to: p) atRandom.
	(g := h raisedTo: r modulo: p) = 1] whileTrue.
	^ Group new generator: g % p
]

{ #category : #examples }
Group class >> symmetric: aCollection [
	"Answer the group of permutations of aCollection."
	| generators X |
	generators := OrderedCollection new.
	X := aCollection isInteger ifTrue: [1 to: aCollection] ifFalse: [aCollection asArray].
	1 to: X size do: [:i| | xi |
		xi := X at: i.
		i+1 to: X size do: [:j|
			generators add: (Permutation transposing: xi with: (X at: j))]].
	^ TransformationGroup new generators: generators; name: 'Sym(', aCollection asString, ')'
]

{ #category : #operations }
Group >> * anElementOrGroup [
	(anElementOrGroup isKindOf: Group) ifTrue: [^ self freeProduct: anElementOrGroup].
	^ RightCoset on: self representative: anElementOrGroup
]

{ #category : #operations }
Group >> / aSubgroup [
	"Answer the quotient group (or factor group) of the receiver by the argument.
	Assume aSubgroup is normal in the receiver, otherwise this is just the set of left cosets."
	^ QuotientGroup on: self by: aSubgroup

	"Answer the left factor group (or left quotient group) of the receiver by the argument.
	If aSubgroup is not normal in the receiver, this is just the set of left cosets."
"	^ self collect: [:each| LeftCoset on: aSubgroup representative: each]"
]

{ #category : #operations }
Group >> // aSubgroup [
	"Answer the set of left cosets of the receiver by aSubgroup."
	| answer |
	answer := Set new.
	self do: [:each| answer add: (LeftCoset on: aSubgroup representative: each)].
	^ answer
]

{ #category : #operations }
Group >> \ aSubgroup [
	"Answer the right factor group (or right quotient group) of the receiver by the argument. If aGroup is not normal in the receiver, this is just the set of right cosets."
	^ self collect: [:each| RightCoset on: aSubgroup representative: each]
]

{ #category : #operations }
Group >> \\ aSubgroup [
	"Answer the set of right cosets of the receiver by aSubgroup."
	| answer |
	answer := Set new.
	self do: [:each| answer add: (RightCoset on: aSubgroup representative: each)].
	^ answer
]

{ #category : #operations }
Group >> abelianization [
	"Answer the receiver 'made abelian'."
	^ (self / self commutator)
		propertyAt: #isCommutative put: true;
		yourself
]

{ #category : #private }
Group >> additiveInverseMap [
	^ (self to: self evaluating: [:each| each negated]) name: '-id'
]

{ #category : #private }
Group >> additiveOperation [
	^ (GroupAction from: (self, self) to: self evaluatingWithArguments: [:x :y| x + y]) name: '+'
]

{ #category : #morphisms }
Group >> adjointAction [
	^ GroupAction
		from: self , self
		to: self
		evaluatingWithArguments: [ :x :y | 
			self operation
				value:
					{(self operation
						value:
							{x.
							y}).
					(self inverseMap value: x)} ]
]

{ #category : #random }
Group >> atRandom: aRandom bits: bitSize [
	self propertyAt: #elements ifPresent: [:aCollection| ^ aCollection atRandom: aRandom bits: bitSize].
	self generators notNil ifTrue: [^ (GroupRandomGenerator on: self random: aRandom) bits: bitSize; next].
	^ self subclassResponsibility
]

{ #category : #graphs }
Group >> cayleyGraph: generators [
	"Answer the 'colored' Cayley graph of the receiver for the given set of generators.
	The set of generators is usually assumed to be symmetric (contains all inverses too) and to not contain the identity."
	| op G |
	self isFinite ifFalse: [^ self error: 'not a finite group'].
	op := self operation.
	G := Digraph unorderedLabeled.
	self do: [:g|
		generators do: [:x|
			G addEdgeFrom: g to: (op value: {g.x}) label: x]].
	^ G
]

{ #category : #graphs }
Group >> cayleyGraphMorph [
	^ self cayleyGraphMorph: self generators
]

{ #category : #graphs }
Group >> cayleyGraphMorph: generators [
	"Answer the colored Cayley graph of the receiver for the given set of generators.
	The set of generators is usually assumed to be symmetric (contains all inverses too) and to not contain the identity."
	| G answer colors |
	G := self cayleyGraph: generators.
	answer := G asMorph.
	colors := AutomaticPalette new.
	answer nodesDo: [:each| each color: Color transparent; radius: 0].
	generators do: [:each| colors at: each].
	generators do: [:each| (answer nodeAt: each) color: (colors at: each); radius: 10].
	answer edgesAndLabelsDo: [:each :label| each hideLabel; color: (colors at: label)].
	(answer nodeAt: self identity) color: Color white; shape: #square; radius: 10.
	^ answer
]

{ #category : #operations }
Group >> center [
	^ self centralizerOf: self
]

{ #category : #operations }
Group >> centralizerOf: aCollection [
	| op |
	op := self operation.
	^ self select: [:x| aCollection allSatisfy: [:y| (op value: {x. y}) = (op value: {y. x})]]
]

{ #category : #enumerating }
Group >> collect: aBlock [
	"Answer the subgroup resulting of mapping the elements of the receiver by aBlock."
	| elements |
	elements := Set new.
	self do: [:each| elements add: (aBlock value: each)].
	^ self copyEmpty elements: elements
]

{ #category : #operations }
Group >> commutator [
	"Answer the commutator group [G,G] of the receiver G, also called the derived group and noted G'.
	This is the smallest normal subgroup of G such that the quotient G / [G,G] is commutative."
	^ self commutator: self
]

{ #category : #operations }
Group >> commutator2: aGroup [
	"Answer the commutator group [G,H] of the receiver G with the argument H."
	| op inverseMap generators |
	generators := Set new.
	op := self operation.
	inverseMap := self inverseMap.
	self generators do: [:x|
		aGroup generators do: [:y|
			| xInv yInv |
			xInv := inverseMap value: x.
			yInv := inverseMap value: y.
"			answer add: x * y * x reciprocal * y reciprocal]]."
			generators add: (op value: {op value: {op value: {x.y}. xInv}. yInv})]].
	^ (self copyEmpty generators: self generators, aGroup generators) normalClosureOf: generators
]

{ #category : #operations }
Group >> commutator: aSubgroup [
	"Answer the commutator group [G,H] of the receiver G with the argument H."
	| op inverseMap elements |
	elements := Set new.
	op := self operation.
	inverseMap := self inverseMap.
	self do: [:x|
		aSubgroup do: [:y|
			| xInv yInv |
			xInv := inverseMap value: x.
			yInv := inverseMap value: y.
"			answer add: x * y * x reciprocal * y reciprocal]]."
			elements add: (op value: {op value: {op value: {x.y}. xInv}. yInv})]].
	^ self copyEmpty elements: elements
]

{ #category : #private }
Group >> compositiveInverseMap [
	^ (self to: self evaluating: [:each| each inverse]) name: 'inverse'
]

{ #category : #private }
Group >> compositiveOperation [
	^ (GroupAction from: (self, self) to: self evaluatingWithArguments: [:x :y| x compose: y]) name: 'î'
]

{ #category : #private }
Group >> computeExponent [
	| answer |
	answer := 1.
	self do: [:each| answer := answer lcm: (self orderOf: each)].
	^ answer
]

{ #category : #private }
Group >> computeGenerators [
	"The receiver is a finite group represented explicitly as a set of its elements. This method computes a set of generators."
	| n op generators elements |
	(self hasProperty: #elements) ifFalse: [^ nil].
	n := self size.
	n isInfinite ifTrue: [^ nil].
	op := self operation.
	generators := OrderedCollection new.
	elements := Set with: self identity.
	self elements do: [:g|
		elements size = n ifTrue: [^ generators].
		(elements includes: g)
			ifFalse:
				[| previous |
				generators add: g.
				[(previous := elements copy) do: [:x|
					generators do: [:y|
						| xy |
						xy := op value: {x. y}.
						elements add: xy]].
				previous size = elements size] whileFalse]].
	^ generators
]

{ #category : #operations }
Group >> conjugacyClassOf: anElement [
	^ self conjugation orbitOf: anElement
]

{ #category : #operations }
Group >> conjugacyClasses [
	^ self conjugation orbits
]

{ #category : #private }
Group >> conjugate: g by: x [
	"Answer the conjugate of g by x: x*g*x^-1."
	| op |
	op := self operation.
	^ op value: {x. op value: {g. self inverseMap value: x}}
]

{ #category : #morphisms }
Group >> conjugation [
	^ GroupAction from: (self, self) to: self evaluatingWithArguments: [:x :y| self conjugate: y by: x]
]

{ #category : #copying }
Group >> copyEmpty [
	^ super copyEmpty inverseMap: self inverseMap
]

{ #category : #graphs }
Group >> cycleGraph [
	| op G elements id |
	self isFinite ifFalse: [^ self error: 'not a finite group'].
	G := Graph unordered.
	op := self operation.
	id := self identity.
	elements := self elements asSet copyWithout: id.
	[elements isEmpty]
		whileFalse:
			[| e g |
			e := elements anyOne.
			g := id.
			[| g2 |
			g2 := op value: {g. e}.
			(G hasEdgeFrom: g to: g2) ifFalse: [G addEdgeFrom: g to: g2].
			(g := g2) = id] whileFalse: [elements remove: g ifAbsent: []]].
	^ G
]

{ #category : #graphs }
Group >> cycleGraph2 [
	| op G elements id |
	self flag: #fix. "incorrect, test dihedral 4, 5.."
	self isFinite ifFalse: [^ self error: 'not a finite group'].
	G := Graph unordered.
	op := self operation.
	id := self identity.
	elements := self elements asSet copyWithout: id.
	[elements isEmpty]
		whileFalse:
			[| e g |
			e := elements remove: elements anyOne.
			g := id.
			[| g2 |
			g2 := op value: {g. e}.
			G addEdgeFrom: g to: g2.
			(g := g2) = id] whileFalse].
	^ G
]

{ #category : #graphs }
Group >> cycleGraphMorph [
	| answer |
	answer := self cycleGraph asMorph.
	"	answer hideLabels."
	(answer nodeAt: self identity)
		color: Color white;
		shape: #square.
	^ answer
]

{ #category : #private }
Group >> defaultInverseMap [
	^ self multiplicativeInverseMap
"	self do: [:each|
		(each isKindOf: Function) ifTrue: [^ self compositiveInverseMap].
		(each class canUnderstand: #reciprocal) ifTrue: [^ self multiplicativeInverseMap].
		(each class canUnderstand: #negated) ifTrue: [^ self additiveInverseMap].
		^ self error: 'unable to determine group operation']"
]

{ #category : #private }
Group >> defaultOperation [
	^ self multiplicativeOperation
"	self do: [:each|
		(each isKindOf: Function) ifTrue: [^ self compositiveOperation].
		(each class canUnderstand: #reciprocal) ifTrue: [^ self multiplicativeOperation].
		(each class canUnderstand: #negated) ifTrue: [^ self additiveOperation].
		^ self error: 'unable to determine group operation']"
]

{ #category : #series }
Group >> derivedSeriesDo: aBlock [
	"For finite groups the derived series terminates in a perfect group (called the perfect core), which may or may not be trivial."
	| G H |
	G := self.
	[H := G commutator.
	aBlock value: H.
	G order = H order ifTrue: [^ self].
	G := H] repeat
]

{ #category : #operations }
Group >> directProduct: aGroupOrAction [
	"◊ "

	(aGroupOrAction isKindOf: GroupAction)
		ifTrue: [ ^ SemidirectProductGroup
				left: self
				right: aGroupOrAction group
				action: aGroupOrAction ].
	^ DirectProductGroup
		components:
			{self.
			aGroupOrAction}
]

{ #category : #operations }
Group >> directSum: aGroup [
	"Answer the direct sum of the receiver and the argument."
	^ 'self ◊ aGroup' "finite direct sums of groups are the same as direct products"
]

{ #category : #enumerating }
Group >> do: aBlock [
	| generators current previous op |
	self propertyAt: #elements ifPresent: [:aCollection| aCollection do: aBlock. ^ self].
	"iterate all elements from the generators:"
	self flag: #fix. "this is too expensive"
	op := self operation.
	generators := self generators.
	current := generators asSet.
	current do: aBlock.
	current add: self identity ifAbsent: [aBlock value: self identity].
	[previous := current.
	current := current copy.
	previous do: [:x|
		generators do: [:y|
			| xy |
			xy := op value: {x. y}.
			current add: xy ifAbsent: [aBlock value: xy]]].
	previous size < current size] whileTrue.
	self propertyAt: #elements put: current
]

{ #category : #operations }
Group >> dot: aGroup [
	"Answer the intersection of the receiver and the argument."
	self ambient = aGroup ambient ifFalse: [^ DomainError signal: 'groups in different ambients'].
	^ self select: [:each| aGroup includes: each]
]

{ #category : #accessing }
Group >> exponent [
	"Answer the exponent of the receiver, i.e. the maximum order of an element."
	^ self propertyAt: #exponent ifAbsentPut: [self computeExponent]
]

{ #category : #accessing }
Group >> generators [
	self propertyAt: #generators ifPresent: [:aCollection| ^ aCollection].
	^ self propertyAt: #generators put: (self computeGenerators ifNil: [^ nil])
]

{ #category : #operations }
Group >> groupRing [
	^ self groupRingOver: ZZ
]

{ #category : #operations }
Group >> groupRingOver: aRing [
	^ GroupRing on: self over: aRing
]

{ #category : #operations }
Group >> hypoabelianization [
	^ self / self perfectCore
]

{ #category : #accessing }
Group >> identity [
	"Answer the identity element of the receiver."
	^ self propertyAt: #identity ifAbsent: [self do: [:each| ^ self propertyAt: #identity put: (self operation value: {each. self inverseMap value: each})]]
]

{ #category : #operations }
Group >> index [
	"Answer the index of the receiver in its ambient group."
	^ self ambient indexOf: self
]

{ #category : #operations }
Group >> indexOf: aSubgroup [
	^ (self / aSubgroup) size
]

{ #category : #morphisms }
Group >> innerAutomorphisms [
	^ TransformationGroup new elements: (self elements collect: [:a| Conjugation by: a in: self])
]

{ #category : #accessing }
Group >> inverseMap [
	^ self propertyAt: #inverseMap ifAbsentPut: [self defaultInverseMap]
]

{ #category : #'accessing-private' }
Group >> inverseMap: aFunction [
	self propertyAt: #inverseMap put: (self hom: self) ! aFunction
]

{ #category : #testing }
Group >> isAdditive [
	^ self operation name = '+'
]

{ #category : #testing }
Group >> isCompositive [
	^ self operation name = '@'
]

{ #category : #testing }
Group >> isCyclic [
	"Answer true if the receiver is generated by one element."
	self do: [:each| (self span: {each}) size = self size ifTrue: [^ true]].
	^ false
]

{ #category : #testing }
Group >> isGroup [
	^ true
]

{ #category : #testing }
Group >> isHypoabelian [
	^ self perfectCore isTrivial
]

{ #category : #testing }
Group >> isInitial [
	^ self isTrivial
]

{ #category : #testing }
Group >> isMultiplicative [
	^ self operation name = '*'
]

{ #category : #testing }
Group >> isNilpotent [
	| termination |
	self lowerCentralSeriesDo: [:each| termination := each].
	^ termination isTrivial
]

{ #category : #testing }
Group >> isNormal [
	"Answer true if the receiver is normal in its ambient overgroup."
	^ self isNormalIn: self ambient
]

{ #category : #testing }
Group >> isNormalIn: anOvergroup [
	"Answer true if the receiver is normal as subgroup of aGroup, i.e. if it is a subgroup invariant under conjugation."
	| inverseMap op X Y |
	op := self operation.
	inverseMap := self inverseMap.
	X := self generators ifNil: [self].
	Y := anOvergroup generators ifNil: [anOvergroup].
	X do: [:x|
		Y do: [:y|
			| yInv |
			yInv := inverseMap value: y.
"			(self includes: other * each * other reciprocal)"
			(self includes: (op value: {op value: {y.x}. yInv}))
				ifFalse: [^ false]]].
	^ true
]

{ #category : #testing }
Group >> isPerfect [
	^ self isTrivial not and: [self = self commutator]
]

{ #category : #testing }
Group >> isSolvable [
	^ self perfectCore isTrivial

"
alternative implementations:
	| G G' |
	G := self.
	[G isCyclic ifTrue: [^ true].
	G isTrivial ifTrue: [^ false].
	G' := G commutator.
	G' order = G order ifTrue: [^ false].
	G := G'] repeat

or:
	| G G' |
	G := self.
	[G isTrivial ifTrue: [^ true].
	G' := G commutator.
	G' order = G order ifTrue: [^ false].
	G := G'] repeat"

]

{ #category : #testing }
Group >> isTerminal [
	^ self isTrivial
]

{ #category : #testing }
Group >> isTrivial [
	"Answer true if the receiver is the trivial group {id}."
	| generators id |
	self propertyAt: #elements ifPresent: [:aCollection| ^ aCollection size = 1].
	generators := self generators ifNil: [^ self size = 1].
	id := self identity.
	^ generators allSatisfy: [:each| each = id]
]

{ #category : #morphisms }
Group >> leftAction [
	self flag: #fix. "check this, is this right?"
	^ self operation
	"^ GroupAction from: (self, self) to: self evaluating: [:each| self operation value: {each first. each second}]"
]

{ #category : #series }
Group >> lowerCentralSeriesDo: aBlock [
	| G H |
	G := self.
	[H := G commutator: self.
	aBlock value: H.
	G order = H order ifTrue: [^ self].
	G := H] repeat
]

{ #category : #operations }
Group >> mult:aGroupOrAction [ "◊ "
	(aGroupOrAction isKindOf: GroupAction)
		ifTrue: [^ SemidirectProductGroup left: self right: aGroupOrAction group action: aGroupOrAction].
	^ DirectProductGroup components: {self. aGroupOrAction}
]

{ #category : #private }
Group >> multiplicativeInverseMap [
	^ (self to: self evaluating: [:each| each reciprocal]) name: 'x^-1'
]

{ #category : #private }
Group >> multiplicativeOperation [
	^ (GroupAction from: (self, self) to: self evaluatingWithArguments: [:x :y| x * y]) name: '*'
]

{ #category : #operations }
Group >> normalClosureOf: aSubset [
	"From Handbook of Computational Group Theory (Holt) 74p.
	The normal closure of A <= G in G (denoted A^G) is the smallest normal subgroup of G that contains A, i.e. the intersection of all normal subgroups that contain A. Equivalently, it is the set A^G := {g^-1 * a * g | g in G, a in A}."
	| X Y Z random N |
	self flag: #fix. "test and fix, replace >>normalizerOf:?"
	X := self generators.
	Y := aSubset.
	Z := Y.
	random := self random.
	N := self copyEmpty generators: Z.
	["test whether <Z> = <Y>^<X>"
	X allSatisfy: [:g| Z allSatisfy: [:h| N includes: (self conjugate: h by: g)]]]
		whileFalse:
			["add some new random conjugates to Z"
			| random2 |
			random2 := N random.
			10 timesRepeat:
				[| h g hg |
				g := random next.
				h := random2 next.
				hg := self conjugate: h with: g. "h^g"
				(N includes: hg) ifFalse: [Z add: hg. N := self copyEmpty generators: Z. random2 := N random]]].
	^ N
]

{ #category : #operations }
Group >> normalizerOf: aCollection [
	"Answer the normal closure of aCollection in the receiver, i.e. the smallest normal subgroup that contains aCollection."
	| inverseMap op |
	op := self operation.
	inverseMap := self inverseMap.
	^ self select: [:x| (aCollection collect: [:y| op value: {op value: {x.y}. inverseMap value: x}]) = aCollection]
]

{ #category : #accessing }
Group >> null [
	"Answer the trivial subgroup."
	^ self span: #()
]

{ #category : #accessing }
Group >> operation [
	^ self propertyAt: #operation ifAbsentPut: [self defaultOperation]
]

{ #category : #accessing }
Group >> order [
	"The order of a group is its cardinality, i.e., the number of elements in its set."
	^ self size
]

{ #category : #operations }
Group >> orderOf: anElement [
	"Answer the order of the argument in the receiver, i.e. the minimum e such that g^e = 1.
	COHEN Algorithm 1.4.3 (Order of an Element)."

	| h factors id e g1 |
	h := self size.
	factors := h factors.
	e := h.
	id := self identity.
	factors asSet
		do: [ :p | 
			e := e / (p raisedTo: (factors occurrencesOf: p)).
			g1 := self raise: anElement to: e.
			[ g1 = id ]
				whileFalse: [ g1 := self raise: g1 to: p.
					e := e * p ] ].
	^ e
]

{ #category : #operations }
Group >> orderOf: anElement boundedBy: n [
	"Alternative to orderOf:, from Handbook of Computational Group Theory (Holt), 73p. Runs in time at most O(log(n)^3)."
	| id |
	n = 1 ifTrue: [^ 1].
	id := self identity.
	n factors asSet do: [:p| (self raise: anElement to: n/p) = id ifTrue: [^ self orderOf: anElement boundedBy: n/p]].
	^ n
]

{ #category : #morphisms }
Group >> outerAutomorphisms [
	^ self automorphisms / self innerAutomorphisms 
]

{ #category : #operations }
Group >> perfectCore [
	| answer |
	self derivedSeriesDo: [ :each | answer := each ].
	^ answer
]

{ #category : #accessing }
Group >> presentation [
	^ self propertyAt: #presentation
]

{ #category : #printing }
Group >> printOn: aStream [
	| generators |
	((self hasProperty: #name) or: [(generators := self generators) isNil])
		ifTrue: [^ super printOn: aStream].
	"use the original printOn for wrapped objects:"
	self propertyAt: #elements ifPresent: [:elements| (elements isKindOf: Domain) ifTrue: [aStream print: elements. ^ self]].
	generators isEmpty
		ifTrue: [aStream nextPut: ${; print: self identity; nextPut: $}. ^ self].
	aStream nextPut: $<.
	generators do: [:each| aStream print: each] separatedBy: [aStream nextPutAll: '; '].
	aStream nextPut: $>
]

{ #category : #private }
Group >> raise: anElement to: anInteger [
	| op |
	anInteger = 1 ifTrue: [^ anElement].
	anInteger = 0 ifTrue: [^ self identity].
	anInteger < 0 ifTrue: [^ self raise: (self inverseMap value: anElement) to: anInteger negated].
	op := self operation.
	^ op value:
		{self raise: (op value: {anElement. anElement}) to: anInteger // 2.
		self raise: anElement to: anInteger \\ 2}
]

{ #category : #random }
Group >> random [
	^ GroupRandomGenerator on: self
]

{ #category : #morphisms }
Group >> rightAction [
	^ GroupAction
		from: self , self
		to: self
		evaluatingWithArguments: [ :x :y |
			self operation
				value:
					{y.
					(self inverseMap value: x)} ]
]

{ #category : #morphisms }
Group >> rightCosetAction [
	self flag: #fix."nil"
	^ GroupAction from: (self, nil "set of subgroups?") to: nil "set of right cosets" evaluating: [:each| each first * each second]
]

{ #category : #morphisms }
Group >> rightRegularAction [
	self flag: #fix. "is this right?"
	^ GroupAction from: (self, self) to: self evaluatingWithArguments: [:x :y| x * y]
]

{ #category : #enumerating }
Group >> select: aBlock [
	"Answer the subgroup resulting of the selection by aBlock."
	| elements |
	elements := Set new.
	self do: [:each| (aBlock value: each) ifTrue: [elements add: each]].
	^ self copyEmpty elements: elements
]

{ #category : #operations }
Group >> span: aCollection [
	"Answer the subgroup generated by the argument."
	^ self copyEmpty generators: aCollection
]

{ #category : #private }
Group >> species [
	^ Group
]

{ #category : #morphisms }
Group >> to: aCodomain [
	(self isTrivial and: [aCodomain isGroup]) ifTrue: [^ self to: aCodomain evaluating: [:x| aCodomain identity]].
	^ super to: aCodomain
]

{ #category : #morphisms }
Group >> to: aGroup evaluating: aBlock [
	aGroup isGroup ifFalse: [^ super to: aGroup evaluating: aBlock].
	^ GroupMap from: self to: aGroup evaluating: aBlock
]

{ #category : #accessing }
Group >> trivial [
	"Answer the trivial subgroup."

	^ self null
]

{ #category : #series }
Group >> upperCentralSeriesDo: aBlock [
	| Z inverseMap op |
	op := self operation.
	inverseMap := self inverseMap.
	Z := self trivial.
	[Z := self select: [:x| self allSatisfy: [:y| Z includes: (op value: {op value: {x.y}. inverseMap value: x})]].
	aBlock value: Z.
	Z order = self order] whileFalse
]

{ #category : #series }
Group >> upperCentralSeriesQuotientsDo: aBlock [
	| Z1 |
	Z1 := self trivial.
	self upperCentralSeriesDo: [:Z| aBlock value: Z / Z1. Z1 := Z]
]
