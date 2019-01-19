"
Standard bases of polynomial ideals. A standard basis is nothing but a special set of generators with the property that the leading monomials generate the leading ideal.

When the choosen monomial ordering is global (a well-ordering), these are Groebner bases and are computed with Buchberger's algorithm. For arbitrary monomial orderings, they are computed using Mora's normal form.

See also Buchberger and ExtendedBuchberger.
"
Class {
	#name : #StandardBasis,
	#superclass : #SequenceableCollection,
	#instVars : [
		'elements'
	],
	#category : #'Mathematics-Polynomials-Algorithms'
}

{ #category : #accessing }
StandardBasis >> add: aPolynomial [
	^ elements add: aPolynomial
]

{ #category : #accessing }
StandardBasis >> addAll: aCollection [
	^ elements addAll: aCollection
]

{ #category : #enumerating }
StandardBasis >> apply: aMorphism [
	| answer |
	answer := self copyEmpty.
	self do: [:each| answer add: (aMorphism value: each)].
	^ answer
]

{ #category : #accessing }
StandardBasis >> at: anInteger [
	^ elements at: anInteger
]

{ #category : #copying }
StandardBasis >> copy [
	"Answer a copy of the reciever."
	^ self class new elements: elements copy
]

{ #category : #copying }
StandardBasis >> copyEmpty [
	^ self class new
]

{ #category : #copying }
StandardBasis >> copyWithout: aPolynomial [
	^ self class new elements: (elements copyWithout: aPolynomial)
]

{ #category : #enumerating }
StandardBasis >> do: aBlock [
	elements do: aBlock
]

{ #category : #operations }
StandardBasis >> elementAt: aTuple [
	^ (1 to: aTuple size) sum: [:i| (self at: i) * (aTuple at: i)]
]

{ #category : #'accessing-private' }
StandardBasis >> elements: aCollection [
	elements := aCollection
]

{ #category : #accessing }
StandardBasis >> first [
	^ self at: 1
]

{ #category : #accessing }
StandardBasis >> indeterminates [
	^ self anyOne parent indeterminates
]

{ #category : #initialization }
StandardBasis >> initialize [
"	elements := SortedCollection sortBlock: [:a :b| a degree <= b degree]."
"	elements := SortedCollection sortBlock: [:a :b| a leadingMonomial <= b leadingMonomial]."
	elements := OrderedCollection new
]

{ #category : #testing }
StandardBasis >> isMinimal [
	"A Groebner basis G of an ideal I is called 'minimal' if the lead terms of the elements in G minimally generate in(I); or equivalently, if for all p in G:
	- LC(p) = 1, and
	- LT(p) is not in <G-{p}> (i.e., leading-term-minimal).
	Note that any leading-term-minimal Groebner basis is also cardinality-minimal."
	| one |
	one := self first scalars one.
	self do: [:g| g leadingCoefficient ~= one ifTrue: [^ false]].
	self do: [:g|
		self do: [:f|
			(f ~~ g and: [f leadingMonomial | g leadingMonomial]) ifTrue: [^ false]]].
	^ true
]

{ #category : #testing }
StandardBasis >> isMinimal2 [
	"A Groebner basis G is minimal when for all p in G:
	1. LC(p) = 1;
	2. LT(p) is not in <G-{p}>."
	| one |
	one := self first scalars one.
	"Check all polynomials are monic:"
	self do: [:each| each leadingCoefficient ~= one ifTrue: [^ false]].
	self do: [:each| "Check if the basis without it still generates its leading term:"
		((self copyWithout: each) reduces: each leadingTerm)
				ifTrue: [^ false]].
	^ true
]

{ #category : #testing }
StandardBasis >> isReduced [
	"A Groebner basis G is called 'reduced' (or 'auto-reduced') if for all p in G:
	- LC(p) = 1, and
	- no monomial of p is in <G-{p}>.
	In particular, a reduced Groebner basis is leading-term-minimal (no leading term of any generator divides any other generator's leading term), and a leading-term-minimal basis is also cardinality-minimal."
	| one |
	one := self first scalars one.
	self do: [:g| g leadingCoefficient ~= one ifTrue: [^ false]].
	self do: [:g|
		g monomials do: [:gi|
			self do: [:f|
				(f ~~ g and: [f leadingMonomial | gi]) ifTrue: [^ false]]]].
	^ true
]

{ #category : #testing }
StandardBasis >> isReduced2 [
	"A Groebner basis G is reduced when for all p in G:
	1. LC(p) = 1;
	2. No monomial of p is contained in <G-{p}>."
	| one subBasis |
	one := self first scalars one.
	"Check all polynomials are monic:"
	self do: [:each| each leadingCoefficient ~= one ifTrue: [^ false]].
	self do: [:each| "Check if the basis without it still generates its monomials:"
		subBasis := self copyWithout: each.
		(each terms allSatisfy: [:other| subBasis reduces: other]) ifTrue: [^ false]].
	^ true
]

{ #category : #testing }
StandardBasis >> isTrivial [
	"Answer true if the basis is {1}."
	^ elements size = 1 and: [elements first isConstant and: [elements first isMonic]]
"	^ elements anySatisfy: [:f| f isConstant]"
]

{ #category : #operations }
StandardBasis >> leadingTerms [
	"Answer the standard basis made of all leading monomials of polynomials in the receiver."
	| answer |
	answer := self class new.
	self do: [:each| | lt | lt := each leadingTerm. (answer reduces: lt) ifFalse: [answer add: lt]].
	^ answer
]

{ #category : #operations }
StandardBasis >> macaulayMatrix [
	| monomials |
	monomials := Set new.
	self do: [:each| monomials addAll: each monomials].
	monomials := monomials asSortedCollection: [:a :b| a >= b].
	^ self anyOne parent scalars matrix: self size @ monomials size evaluating: [:i :j| (self at: i) coefficientAt: (monomials at: j)]
]

{ #category : #operations }
StandardBasis >> minimal [
	"Answer the minimal Groebner basis of the receiver."
	| heads goods answer |
	self isMinimal ifTrue: [^ self].
	heads := elements collect: [:each| each leadingMonomial].
	goods := (1 to: heads size) asSet.
	heads withIndexDo: [:head :i|
		(goods anySatisfy: [:one| i ~= one and: [(heads at: one) | head]])
			ifTrue: [goods remove: i]].
	answer := self class new.
	(goods asSortedCollection: [:a :b| "make it triangular for lex" (elements at: a) leadingMonomial >= (elements at: b) leadingMonomial])
		do: [:i| answer add: (elements at: i) monic].
	^ answer
]

{ #category : #accessing }
StandardBasis >> ordering [
	"Answer the monomial ordering of the receiver."
	^ self anyOne parent ordering
]

{ #category : #printing }
StandardBasis >> printOn: aStream [
	aStream nextPut: ${.
	elements do: [:each| aStream print: each] separatedBy: [aStream nextPutAll: ', '].
	aStream nextPut: $}
]

{ #category : #operations }
StandardBasis >> reduce1: aPolynomial [ 
	"Answer Mora's normal form of aPolynomial with respect to the receiver)."
	| h L M |
	h := aPolynomial.
	L := OrderedCollection withAll: self.
	([h isZero or: [(M := L select: [:g| g leadingMonomial | h leadingMonomial]) isEmpty]])
		whileFalse:
			[| g |
			g := M argmin: [:each| each ecart].
			g ecart > h ecart ifTrue: [L add: h].
			h := h - (g * (h leadingMonomial / g leadingMonomial) * (h leadingCoefficient / g leadingCoefficient))].
	^ h
]

{ #category : #operations }
StandardBasis >> reduce: aPolynomial [ 
	"Answer Mora's normal form of aPolynomial with respect to the receiver."
	| h L lmh g ecartg |
	h := aPolynomial.
	L := OrderedCollection withAll: self.
	[h isZero ifTrue: [^ h].
	lmh := h leadingMonomial.
	g := nil.
	ecartg := -1.
	L do: [:each|
		| ecart |
		(each leadingMonomial | lmh and: [ecart := each ecart. g isNil or: [ecart < ecartg]])
			ifTrue: [g := each. ecartg := ecart]].
	g isNil ifTrue: [^ h].
	ecartg > h ecart ifTrue: [L add: h].
	h := h - (g * (lmh / g leadingMonomial) * (h leadingCoefficient / g leadingCoefficient))] repeat
]

{ #category : #operations }
StandardBasis >> reduceFull: aPolynomial [
	"In the general case of standard bases, this is the same as >>reduce:.
	It is reimplemented in GroebnerBasis."
	^ self reduce: aPolynomial
]

{ #category : #operations }
StandardBasis >> reduceFull: aPolynomial startingAt: startIndex [
	"In the general case of standard bases, this is the same as >>reduce:.
	It is reimplemented in GroebnerBasis."
	^ self reduce: aPolynomial
]

{ #category : #operations }
StandardBasis >> reduced [
	"Answer a reduced basis for the ideal generated by the receivr.
	Becker, Weispfenning, 'Groebner Bases', algorithm REDGROEBNER (p. 216) and REDUCTION (p. 203)."
	| G H |
	H := OrderedCollection new.
	1 to: self size do: [:i| | fi lm |
		fi := self at: i.
		lm := fi leadingMonomial.
		(((i+1 to: self size) noneSatisfy: [:j| (self at: j) leadingMonomial | lm])
			and: [H noneSatisfy: [:h| h leadingMonomial | lm]])
				ifTrue: [H add: fi]].
	H := H asArray.
	G := self class new.
	1 to: H size do: [:i| | hi r |
		hi := H at: i.
		(r := hi \\ (H copyWithoutIndex: i)) isZero ifFalse: [G add: r monic]].
	G sort: [:a :b| a leadingMonomial >= b leadingMonomial]. "make it triangular for lex"
	^ G
]

{ #category : #testing }
StandardBasis >> reduces: aPolynomial [
	^ (self reduce: aPolynomial) isZero
]

{ #category : #accessing }
StandardBasis >> size [
	^ elements size
]

{ #category : #sorting }
StandardBasis >> sort: aBlock [
	elements sort: aBlock
]

{ #category : #private }
StandardBasis >> species [
	^ Array
]

{ #category : #private }
StandardBasis >> verify [
	1 to: self size do: [:i| | fi |
		fi := self at: i.
		i+1 to: self size do: [:j| | fj |
			fj := self at: j.
			(self reduces: (fi s: fj))
				ifFalse: [^ false]]].
	^ true
]
