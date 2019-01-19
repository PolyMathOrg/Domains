"
'Objects' of some category (such as Groups, Rings, Modules, Schemes, etc) connected by the corresponding Morphisms. In many practical situations, domains can be seen as sets of elements, and their morphisms as some kind of Functions.

Domains with an underlying set can have finite or infinite cardinality, and whenever makes sense they implement some *Collection* protocol (such as #do:, #size, #asSet, #atRandom:, etc).

Domains can be derived from other domains, for example by taking products or coproducts (cartesian products, direct products, direct sums), quotients, extensions, localizations, completions, duals, etc. These operations are functors, and are mostly implemented as Smalltalk messages.

Domains can have subobjects: groups have subgroups, vector spaces have subspaces, rings have subrings and ideals, schemes have subschemes, etc. In general, there is an #ambient overobject, and there is a protocol for inclusion testing with #<, #<=, #>=, #> and membership testing witih #includes: and #contains:.

Given two domains A and B in the same category, the set Hom(A,B) of morphisms between them is obtained by sending the message 'A hom: B' (see HomSet). The #hom: message is the Hom(A,-) functor. The identity morphism is returned by the message #id. And a morphism from A to B can be constructed by sending 'A to: B evaluating: [:x| ...]'.

Domains often come equipped with cannonical morphisms. For example, field extensions and localizations have canonical embeddings (monomorphisms), and implement #embed: (the embedding implemented as a message) and #embedding (which returns the embedding morphism as an instance of some subclass of Morphism). Quotient objects have canonical projections (epimorphisms) and implement #project: and #projection. N-ary products and coproducts implement #projection: for the i-th projection map (and coproducts also implement #embedding: for the i-th coprojection).

More generally, canonical morphisms that are uniquely determined by their domain and codomain can be retrieved by sending the message #. This can be used for automatic coercion of elements between domains. For example, for any ring R, 'ZZ  R' returns the canonical ring homomorphism that sends an integer 'n' to 'n times the unit of R'. In order for this mechanism to work, subclasses must sometimes reimplement the messages #to: and #from: to answer canonical morphisms when such morphisms are known, and call super otherwise.

There's also a very simple coercion mechanism that allows to convert elements from one domain to another via the message #!. For example, the coercion of an integer 'n' to an element of any ring R can be performed simply as 'R ! n'. Subclasses must sometimes reimplement the message #! to convert the argument when possible, and call super otherwise.

References:
	https://en.wikipedia.org/wiki/Algebraic_structure
	https://en.wikipedia.org/wiki/Category_theory
	https://en.wikipedia.org/wiki/Subobject
	https://en.wikipedia.org/wiki/Product_(category_theory)
	https://en.wikipedia.org/wiki/Coproduct

"
Class {
	#name : #Domain,
	#superclass : #Object,
	#instVars : [
		'properties'
	],
	#category : #'Mathematics-Kernel'
}

{ #category : #examples }
Domain class >> example1asSet [
	"The ring Z/5Z as a Smalltalk Set.
	This is possible because the ring is finite."
	^ (ZZ/5) asSet
]

{ #category : #examples }
Domain class >> example1atRandom [
	"Taking an element at random from the Z-module of 3x3 matrices.
	Use 50 bits to generate this element. Essentially, this can return
	at most 2^50 different matrices, and their bitsize doesn't exceed 50
	bits (where bitsize is losely defined, in this case it's the sum
	of bitsize of the coefficients of the matrix)."
	^ 'ZZ^(3@3) atRandom: (Random seed: 12345) bits: 50'
]

{ #category : #examples }
Domain class >> example21VectorSpace [
	"The vector space of 3-tuples with rational coefficients."
	^ 'QQ ^ 3'
]

{ #category : #examples }
Domain class >> example21VectorSpace2 [
	"The vector space of 3x3 matrices with complex coefficients."
	^ 'CC ^ (3@3)'
]

{ #category : #examples }
Domain class >> example2ModuleDirectSum [
	"The direct sum of the module of 3x3 matrices
	with coefficients in Z/6Z plus the rank 1 module
	of Z/6Z scalars."
	^ 'ZZ/6 ^ (3@3) ê (ZZ/6) asSelfModule'
]

{ #category : #examples }
Domain class >> example3DirectProductOfGroups [
	"The direct product of the group of permutations of
	the symbols {#a, #b, #c} by the group of alternating
	permutations of {1,2,3,4}."
	^ '(SymmetricGroup on: #(a b c)) ◊ (AlternatingGroup new: 4)'
]

{ #category : #examples }
Domain class >> example41Polynomials [
	"Polynomials in two variables with integer coefficients."
	^ ZZ polynomialsIn: #(a b)
]

{ #category : #examples }
Domain class >> example42AffineRing [
	"The quotient of a polynomial ring by an ideal.
	This is an affine ring, in particular it is the coordinate ring of the twisted cubic."
	| R x y z I |
	R := CC polynomialsIn: #(x y z).
	x := R x: 1.
	y := R x: 2.
	z := R x: 3.
	I := 'R * {(x^2) - y. (x^3) - z}'.
	^ R / I
]

{ #category : #examples }
Domain class >> example43AffineVariety [
	"This is the twisted cubic affine variety, parameterized by (x, x^2, x^3) in C^3."
	| R x y z I |
	R := CC polynomialsIn: #(x y z).
	x := R x: 1.
	y := R x: 2.
	z := R x: 3.
	I := 'R * {(x^2) - y. (x^3) - z}'.
	^ (R / I) spec
]

{ #category : #examples }
Domain class >> example5GL [
	"The group GL(Q^3) of invertible linear maps
	on the vector space of 3-tuples with rational coefficients.
	This is the automorphisms group of the vector space, and
	its elements are linear maps, not matrices."
	^ '(QQ ^ 3) automorphisms'
]

{ #category : #examples }
Domain class >> example5GLAsMatrixGroup [
	"The matrix group GL(3,Q) of 3x3 matrices with rational coefficients."
	^ GeneralLinearMatrixGroup new: 3 over: QQ
]

{ #category : #'instance creation' }
Domain class >> newFrom: anObject [
	^ self new elements: anObject
]

{ #category : #elements }
Domain >> ! anObject [
	"Coerce anObject to an element of the receiver. Subclasses should extend."
	(self includes: anObject) ifTrue: [^ anObject].
	(self isQuotient and: [self base includes: anObject]) ifTrue: [^ self project: anObject].
	self isEmbedded ifTrue: [| element | element := self ambient ! anObject. (self contains: element) ifTrue: [^ element]].
	^ DomainError signal: 'coercion failed'
]

{ #category : #operations }
Domain >> + aDomain [
	"This is a convenience method for doing coproducts. Subclasses can reimplement it to mean something different from the coproduct in order to match customary notation."
	^ self ê aDomain
]

{ #category : #operations }
Domain >> , aDomain [
	"Answer the cartesian set product of the receiver with the argument."
	^ CartesianProduct components: {self. aDomain}
]

{ #category : #operations }
Domain >> / anEquivalenceRelation [
	"Answer the categorical quotient of the receiver by an equivalence relation."
	| relation |
	relation := anEquivalenceRelation isBlock ifTrue: [EquivalenceRelation on: self evaluating: anEquivalenceRelation] ifFalse: [anEquivalenceRelation].
	^ QuotientSet mod: relation
]

{ #category : #comparing }
Domain >> < aDomain [
	"Answer true if the receiver is a proper subobject of aDomain (strict inclusion)."
	aDomain isFinite ifTrue: [^ self size < aDomain size and: [self elements allSatisfy: [:each| aDomain includes: each]]].
	self isFinite ifTrue: [self do: [:each| (aDomain includes: each) ifFalse: [^ false]]. ^ true].
	^ aDomain > self
]

{ #category : #comparing }
Domain >> <= aDomain [
	"Answer true if the receiver is a subobject of aDomain (inclusion)."
	^ self = aDomain or: [self < aDomain]
]

{ #category : #comparing }
Domain >> = aDomain [
	self == aDomain ifTrue: [^ true].
	self size = aDomain size ifFalse: [^ false].
	self isFinite ifTrue: [^ self asSet = aDomain asSet].
	self propertyAt: #elements ifPresent: [:aCollectionOrDomain| ^ aDomain = aCollectionOrDomain].
	aDomain propertyAt: #elements ifPresent: [:aCollectionOrDomain| ^ self = aCollectionOrDomain].
	^ super = aDomain
]

{ #category : #comparing }
Domain >> > aDomain [
	"Answer true if aDomain is a proper subobject of the receiver (strict inclusion)."
	^ aDomain < self
]

{ #category : #comparing }
Domain >> >= aDomain [
	"Answer true if aDomain is a subobject of the receiver (inclusion)."
	^ aDomain <= self
]

{ #category : #enumerating }
Domain >> allSatisfy: aBlock [
	self do: [:each| (aBlock value: each) ifFalse: [^ false]].
	^ true
]

{ #category : #accessing }
Domain >> ambient [
	"Domains can be subobjects of other domains, for example subspeces are subobjects of vector spaces.
	Answer the ambient domain of which the receiver is a subobject."
	^ self propertyAt: #ambient ifAbsent: [self]
]

{ #category : #'accessing-private' }
Domain >> ambient: aDomain [
	self propertyAt: #ambient put: aDomain
]

{ #category : #enumerating }
Domain >> anySatisfy: aBlock [
	self do: [:each| (aBlock value: each) ifTrue: [^ true]].
	^ false
]

{ #category : #morphisms }
Domain >> apply: aMorphism [
	"Answer the pushforward of the receiver by aMorphism."
	^ self collect: aMorphism
]

{ #category : #converting }
Domain >> asArray [
	self propertyAt: #elements ifPresent: [:aCollectionOrDomain| ^ aCollectionOrDomain asArray].
	^ (Iterator on: self performing: #do:) asArray
]

{ #category : #converting }
Domain >> asSet [
	self propertyAt: #elements ifPresent: [:aCollectionOrDomain| ^ aCollectionOrDomain asSet].
	^ Set accumulate: [:aBlock| self do: aBlock]
]

{ #category : #random }
Domain >> atRandom [
	"Answer an element in the receiver choosen at random. This will fail if the receiver is not finite."
	^ Random withDefaultDo: [:aRandom| self atRandom: aRandom]
]

{ #category : #random }
Domain >> atRandom: aRandom [
	"Answer an element in the receiver choosen at random. This will fail if the receiver is not finite."
	self propertyAt: #elements ifPresent: [:aCollection| aCollection atRandom: aRandom].
	^ self atRandom: aRandom bits: Infinity positive
]

{ #category : #random }
Domain >> atRandom: aRandom bits: bitSize [
	"Answer an element of the receiver of at most n bits (as measured by #bitSize). The total number of elements that could be returned shouldn't exceed 2^n."
	self propertyAt: #elements ifPresent: [:aCollection| ^ aCollection atRandom: aRandom bits: bitSize].
	^ self subclassResponsibility
]

{ #category : #random }
Domain >> atRandomBits: bitSize [
	"Answer an element of the receiver of at most n bits (as measured by #bitSize). The total number of elements that could be returned shouldn't exceed 2^n."
	^ Random withDefaultDo: [:aRandom| self atRandom: aRandom bits: bitSize]
]

{ #category : #morphisms }
Domain >> automorphisms [
	self flag: #fix. "this shouldn't be here for all subclasses to inherit, maybe Domain should be abstract, and we could consider Collections as finite sets and implement these things in Collection; same with #to:evaluating:, etc."
	^ SymmetricGroup on: self
]

{ #category : #operations }
Domain >> catProduct1: aDomain [
	"Answer the categorical product of the receiver with the argument."
	"The product in the category of sets is the cartesian product."
	^ self, aDomain
]

{ #category : #operations }
Domain >> catProduct: aDomain [
	"This is a convenience method for doing categorical products. Subclasses can reimplement it to mean something different from the categorical product in order to match customary notation."
	^ 'self ◊ aDomain'
]

{ #category : #operations }
Domain >> categSum: aDomain [
	"Answer the categorical sum (or coproduct) of the receiver with the argument."
	"The coproduct in the category of sets is the disjoint union."
	^ 'self species newFrom: ((self elements collect: [:each| {each. 0}]) ñ (aDomain elements collect: [:each| {each. 1}]))'
]

{ #category : #operations }
Domain >> catprod: aDomain [
	"This is a convenience method for doing categorical products. Subclasses can reimplement it to mean something different from the categorical product in order to match customary notation."
	^ 'self ◊ aDomain'
]

{ #category : #enumerating }
Domain >> collect: aBlock [
	| elements |
	elements := Set new.
	self do: [:each| elements add: (aBlock value: each)].
	^ elements as: Domain
]

{ #category : #testing }
Domain >> contains: anElement [
	"Answer true if the receiver contains the given element of its ambient.
	This is similar to >>includes: but less checks are needed, because the element is not an arbitrary object."
	self isEmbedded ifFalse: [^ true].
	^ self elements includes: anElement
]

{ #category : #testing }
Domain >> containsAllOf: aCollection [ 
	"Answer whether all the elements of aCollection are in the receiver."
	aCollection do: [:each| (self contains: each) ifFalse: [^ false]].
	^ true
]

{ #category : #copying }
Domain >> copyEmpty [
	^ self species new
]

{ #category : #enumerating }
Domain >> count: aBlock [
	| answer |
	answer := 0.
	self do: [:each| (aBlock value: each) ifTrue: [answer := answer + 1]].
	^ answer
]

{ #category : #enumerating }
Domain >> detect: aBlock [
	"Evaluate aBlock with each of the receiver's elements as the argument. 
	Answer the first element for which aBlock evaluates to true."

	^ self detect: aBlock ifNone: [self error: 'Element is not in the domain']
]

{ #category : #enumerating }
Domain >> detect: aBlock ifNone: exceptionBlock [
	"Evaluate aBlock with each of the receiver's elements as the argument. 
	Answer the first element for which aBlock evaluates to true. If none 
	evaluate to true, then evaluate the argument, exceptionBlock."

	self do: [:each | (aBlock value: each) ifTrue: [^each]].
	^ exceptionBlock value
]

{ #category : #enumerating }
Domain >> do: aBlock [
	(self propertyAt: #elements ifAbsent: [self subclassResponsibility]) do: aBlock
]

{ #category : #enumerating }
Domain >> do: elementBlock separatedBy: separatorBlock [
	| beforeFirst | 
	"Evaluate the elementBlock for all elements in the receiver,
	and evaluate the separatorBlock between."

	beforeFirst := true.
	self do: [ :element |
		beforeFirst
			ifTrue: [beforeFirst := false]
			ifFalse: [separatorBlock value].
		elementBlock value: element]
]

{ #category : #accessing }
Domain >> elements [
	self propertyAt: #elements ifPresent: [:aCollectionOrDomain| ^ aCollectionOrDomain].
	^ Iterator on: self performing: #do:
]

{ #category : #'accessing-private' }
Domain >> elements: aCollection [
	self propertyAt: #elements put: aCollection
]

{ #category : #morphisms }
Domain >> endomorphisms [
	^ self hom: self
]

{ #category : #morphisms }
Domain >> from: aDomain [
	"Answer the canonical morphism from aDomain to the receiver."
	self = aDomain ifTrue: [^ self id].
	self >= aDomain ifTrue: [^ aDomain id restrictedTo: self].
	self isQuotient
		ifTrue: ['aDomain  self base ifNotNil: [:aMorphism| ^ self projection î aMorphism]'].
	self isCoproduct
		ifTrue: [(1 to: self arity) do: [:i| 'aDomain  (self at: i) ifNotNil: [:aMorphism| ^ (self embedding: i) î aMorphism]']].
	^ nil
]

{ #category : #elements }
Domain >> generate: aBlock [
	"Answer the result of evaluating aBlock on the generators of the receiver."
	^ aBlock valueWithArguments: self generators asArray
]

{ #category : #accessing }
Domain >> generator [
	self generators size = 1 ifFalse: [self error: 'more than one generator'].
	^ self generators anyOne
]

{ #category : #accessing }
Domain >> generator: anElement [
	self generators: {anElement}
]

{ #category : #accessing }
Domain >> generators [
	"Subclases can use this or reimplement it when it makes sense."
	^ self propertyAt: #generators ifAbsent: []
]

{ #category : #accessing }
Domain >> generators: aCollection [
	"Subclases can use this or reimplement it when it makes sense."
	self propertyAt: #generators put: aCollection asArray
]

{ #category : #properties }
Domain >> hasProperty: aSymbol [
	^ (properties ifNil: [^ false]) includesKey: aSymbol
]

{ #category : #comparing }
Domain >> hash [
	^ self isFinite ifTrue: [self size hash] ifFalse: [super hash]
]

{ #category : #morphisms }
Domain >> hom: aCodomain [
	"Answer the morphisms that go from the receiver A to the argument B: Hom(A,B)."
	^ HomSet from: self to: aCodomain
]

{ #category : #morphisms }
Domain >> id [
	"Answer the identity morphism."
	| answer |
	self propertyAt: #id ifPresent: [:aMorphism| ^ aMorphism].
	answer := self to: self evaluating: [:x| x].
	answer properties
		at: #isIdentity put: true;
		at: #leftInverse put: answer;
		at: #rightInverse put: answer;
"		at: #kernel put: self null;"
		at: #image put: self.
	^ self propertyAt: #id put: answer
]

{ #category : #testing }
Domain >> includes: anElement [
	^ self elements includes: anElement
]

{ #category : #testing }
Domain >> includesAllOf: aCollection [ 
	"Answer whether all the elements of aCollection are in the receiver."
	aCollection do: [:each| (self includes: each) ifFalse: [^ false]].
	^ true
]

{ #category : #morphisms }
Domain >> inclusion [
	"Answer the inclusion monomorphism from the receiver into its ambient object."
	^ self ambient id restrictedTo: self
]

{ #category : #operations }
Domain >> intersection: aCollection [
	"Answer the intersection of the receiver and the argument."
	^ self select: [:each| aCollection includes: each]
]

{ #category : #morphisms }
Domain >> into: aCodomain evaluating: aBlock [
	"Answer an embedding (an injective morphism) into the specified codomain (in the same category), evaluating as the given block."
	^ self to: aCodomain evaluating: aBlock
]

{ #category : #testing }
Domain >> is: aSymbol [
	^ aSymbol == #Set or: [aSymbol == #Domain or: [super is: aSymbol]]
]

{ #category : #'testing-category' }
Domain >> isAbelianGroup [
	^ false
]

{ #category : #'testing-category' }
Domain >> isAlgebra [
	^ false
]

{ #category : #'testing-category' }
Domain >> isCommutativeRing [
	^ self isRing and: [self isCommutative]
]

{ #category : #'testing-category' }
Domain >> isComplex [
	^ false
]

{ #category : #testing }
Domain >> isCoproduct [
	"Answer true if the receiver is some kind of categorical coproduct, such as direct sum of vector spaces or of other abelian groups. Coproducts are equipped with canonical embeddings from their components (they must implement >>embedding:)."
	^ false
]

{ #category : #testing }
Domain >> isEmbedded [
	"Answer true if the receiver is a subobject; for example a submodule of R^n, a subgroup of Sym(n), a subvariety of affine or projective space, etc."
	^ self ambient ~~ self
]

{ #category : #testing }
Domain >> isEmpty [
	^ self size = 0
]

{ #category : #'testing-category' }
Domain >> isField [
	^ false
]

{ #category : #testing }
Domain >> isFinite [
	^ self propertyAt: #isFinite ifAbsent: [self size isInfinite not]
]

{ #category : #'testing-category' }
Domain >> isFractionRing [
	^ false
]

{ #category : #'testing-category' }
Domain >> isFreeModule [
	^ self isVectorSpace
]

{ #category : #'testing-category' }
Domain >> isGroup [
	^ false
]

{ #category : #testing }
Domain >> isInfinite [
	^ self isFinite not
]

{ #category : #testing }
Domain >> isInitial [
	"Answer true if the receiver is an initial object.
	The empty set is the initial object in the category of sets. Subclasses can override."
	^ self propertyAt: #isInitial ifAbsent: [self isEmpty]
]

{ #category : #'testing-category' }
Domain >> isModule [
	^ self isFreeModule
]

{ #category : #'testing-category' }
Domain >> isMonoid [
	^ self isGroup
]

{ #category : #testing }
Domain >> isProduct [
	"Answer true if the receiver is some kind of categorical product, such as cartesian product of sets, direct product of groups, etc. Products are equipped with canonical projections to their components (they must implement >>projection:)."
	^ false
]

{ #category : #testing }
Domain >> isQuotient [
	"Answer true if the receiver is some kind of quotient object, such as a quotient of sets, gropus, vector spaces, etc. Quotients are equipped with a canonical embedding from their base object (they must implement >>embedding)."
	^ false
]

{ #category : #'testing-category' }
Domain >> isReal [
	^ false
]

{ #category : #'testing-category' }
Domain >> isRing [
	^ false
]

{ #category : #'testing-category' }
Domain >> isSemigroup [
	^ self isMonoid
]

{ #category : #testing }
Domain >> isTerminal [
	"Answer true if the receiver is a terminal object.
	In the category of sets, the singletons (sets with one element) are the terminal objects. Subclasses can override."
	^ self propertyAt: #isTerminal ifAbsent: [self size = 1]
]

{ #category : #'testing-category' }
Domain >> isVectorSpace [
	^ false
]

{ #category : #enumerating }
Domain >> max: aBlock [
	^ self elements max: aBlock
]

{ #category : #enumerating }
Domain >> min: aBlock [
	^ self elements min: aBlock
]

{ #category : #morphisms }
Domain >> morphism: aCodomain [
	"Answer the canonical morphism from the receiver to aCodomain.
	If the argument is a morphism, answer the composition with the canonical morphism to its domain. See also Morphism>>."
	'(aCodomain isKindOf: Morphism)
			ifTrue: [^ self  aCodomain domain ifNotNil: [:aMorphism| aCodomain î aMorphism]]'.
	(self to: aCodomain) ifNotNil: [:aMorphism| ^ aMorphism].
"	self propertyAt: #canonicalMaps ifPresent: [:aDictionary| aDictionary at: aCodomain ifPresent: [:aMorphism| ^ aMorphism]]."
	^ aCodomain from: self
]

{ #category : #accessing }
Domain >> name [
	^ self propertyAt: #name ifAbsent: [self printString]
]

{ #category : #accessing }
Domain >> name: aString [
	self propertyAt: #name put: aString
]

{ #category : #elements }
Domain >> newFrom: anObject [
	"Coerce anObject to an element of the receiver. Implemented in order to be able to use >>as: consistently. Subclasses should reimplement >>!."
	^ self ! anObject
]

{ #category : #enumerating }
Domain >> noneSatisfy: aBlock [
	self do: [:each| (aBlock value: each) ifTrue: [^ false]].
	^ true
]

{ #category : #accessing }
Domain >> null [
	"Answer the null or zero object in the category of the receiver, i.e. an object that is both intial and terminal. For example {id} in the case of groups (the trivial group)."
	"The null object in the category of sets is the empty set."
	^ self propertyAt: #null ifAbsent: [self class newFrom: (Set new: 0)]
]

{ #category : #morphisms }
Domain >> onto: aCodomain evaluating: aBlock [
	"Answer a projection (a surjective morphism) onto the specified codomain (in the same category), evaluating as the given block."
	^ self to: aCodomain evaluating: aBlock
]

{ #category : #copying }
Domain >> postCopy [
	super postCopy.
	properties := properties copy
]

{ #category : #printing }
Domain >> printOn: aStream [
	"Subclasses should reimplement defaultPrintOn: instead of this method."
	self propertyAt: #name ifPresent: [:aString| aStream nextPutAll: aString italic. ^ self].
	self propertyAt: #elements ifPresent: [:aCollection|
		(aCollection isKindOf: Domain) ifTrue: [aStream print: aCollection. ^ self].
		aStream nextPut: ${. "Wildberger notation for unordered sets: elements separated by spaces"
		aCollection asSet do: [:each| aStream print: each] separatedBy: [aStream nextPutAll: ' '].
		aStream nextPut: $}.
		^ self].
	^ super printOn: aStream
]

{ #category : #enumerating }
Domain >> product: aBlock [
	^ self elements product: aBlock
]

{ #category : #properties }
Domain >> properties [
	^ properties ifNil: [properties := IdentityDictionary new]
]

{ #category : #properties }
Domain >> propertyAt: aSymbol [
	^ self propertyAt: aSymbol ifAbsent: [self error: 'no such property']
]

{ #category : #properties }
Domain >> propertyAt: aSymbol ifAbsent: exceptionBlock [
	^ (properties ifNil: [^ exceptionBlock value]) at: aSymbol ifAbsent: exceptionBlock
]

{ #category : #properties }
Domain >> propertyAt: aSymbol ifAbsentPut: aBlock [
	^ self properties at: aSymbol ifAbsentPut: aBlock
]

{ #category : #properties }
Domain >> propertyAt: aSymbol ifPresent: aBlock [
	^ (properties ifNil: [^ nil]) at: aSymbol ifPresent: aBlock
]

{ #category : #properties }
Domain >> propertyAt: aSymbol put: anObject [
	^ self properties at: aSymbol put: anObject
]

{ #category : #operations }
Domain >> raisedTo: anInteger [
	| components |
	components := Array new: anInteger.
	components atAllPut: self.
	^ CartesianProduct components: components
]

{ #category : #enumerating }
Domain >> select: aBlock [
	| elements |
	elements := Set new.
	self do: [:each| (aBlock value: each) ifTrue: [elements add: each]].
	^ elements as: Domain
]

{ #category : #accessing }
Domain >> size [
	^ self propertyAt: #size ifAbsentPut: [self elements size]
]

{ #category : #private }
Domain >> species [
	"Answer a class appropiate for the subobjects of the receiver."
	^ self class
]

{ #category : #enumerating }
Domain >> sum: aBlock [
	^ self elements sum: aBlock
]

{ #category : #morphisms }
Domain >> to: aCodomain [
	"Answer the canonical morphism from the receiver to aCodomain."
	self = aCodomain ifTrue: [^ self id].
	self <= aCodomain ifTrue: [^ aCodomain id restrictedTo: self].
	self isProduct ifTrue: [(1 to: self arity) do: [:i| '(self at: i)  aCodomain ifNotNil: [:aMorphism| ^ aMorphism î (self projection: i)]']].
	^ nil
]

{ #category : #morphisms }
Domain >> to: aCodomain evaluating: aBlock [
	"Answer a morphism to the specified codomain (in the same category), evaluating as the given block.
	Example: ZZ to: ZZ evaluating: [:x| x squared]."
	^ Function from: self to: aCodomain evaluating: aBlock
]

{ #category : #morphisms }
Domain >> to: aCodomain evaluatingWithArguments: aBlock [
	"When the receiver is N-ary, this method allows to define morphisms by N-ary blocks.
	Example: ZZ ◊ ZZ to: ZZ evaluatingWithArguments: [:a :b| a * b]."
	^ self to: aCodomain evaluating: [:each| aBlock valueWithArguments: each asArray]
]

{ #category : #enumerating }
Domain >> upTo: maximumNumberOfElements [
	| answer |
	answer := OrderedCollection new.
	self do: [:each|
		answer size >= maximumNumberOfElements ifTrue: [^ answer].
		answer add: each].
	^ answer
]

{ #category : #enumerating }
Domain >> upTo: max do: aBlock [
	"Iterate over the elements of the receiver, just like #do:, but stop after max elements."
	| k |
	k := 1.
	self do: [:each|
		k > max ifTrue: [^ self].
		aBlock value: each.
		k := k+1]
]

{ #category : #morphisms }
Domain >> | aMorphism [
	"See also Morphism>>|."
	^ aMorphism restrictedTo: self
]

{ #category : #comparing }
Domain >> ~ aDomain [
	"Answer true if the receiver is isomorphic to the argument."
	^ self = aDomain "not much more we can test at this abstract level, subclasses should reimplement"
]
