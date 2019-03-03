Class {
	#name : #GroupTest,
	#superclass : #TestCase,
	#category : #'Mathematics-Tests'
}

{ #category : #'as yet unclassified' }
GroupTest >> smallGroupAtRandom [
	^ {[ SymmetricGroup new: 3 ].
	[ AlternatingGroup new: 3 ].
	[ PermutationGroup klein ].
	[ MatrixGroup klein ].
	[ Group quaternions ]} atRandom value
]

{ #category : #tests }
GroupTest >> testActionOrbitOf [
	| g |
	g := PermutationGroup
		on: (1 to: 8)
		generators:
			{#(#(1 3 2) #(4 6 5)).
			#(#(1 2 3) #(4 5 6)).
			#(#(7 8))}.
	self assert: (g action orbitOf: 1) equals: #(1 2 3) asSet.
	self assert: (g action orbitOf: 4) equals: #(4 6 5) asSet.
	self assert: (g action orbitOf: 7) equals: #(7 8) asSet
]

{ #category : #tests }
GroupTest >> testActionStabilizerOf [
	| G g1 g2 g3 id H |
	G := SymmetricGroup new: 8.
	g1 := G ! #(#(1 3 2) #(4 6 5)).
	g2 := G ! #(#(1 2 3) #(4 5 6)).
	g3 := G ! #(#(7 8)).
	id := G identity.
	H := G
		span:
			{g1.
			g2.
			g3}.
	self
		assert: (H action stabilizerOf: 1) asSet
		equals:
			{id.
			g3} asSet.
	self
		assert: (H action stabilizerOf: 7) asSet
		equals:
			{id.
			g1.
			g2} asSet
]

{ #category : #tests }
GroupTest >> testAlternatingIsSymmetricCommutator [
	| S A |
	S := Group symmetric: (1 to: 3).
	A := Group alternating: (1 to: 3).
	self assert: A = S commutator.
	self assert: (S indexOf: A) = 2
]

{ #category : #tests }
GroupTest >> testAlternatingOrder [
	| A |
	A := Group alternating: (1 to: 3).
	self assert: A order equals: 3 factorial / 2
]

{ #category : #tests }
GroupTest >> testBigOrder1 [
	"Test fast computation of group order with Schreier-Sims algorithm. This is Sym(10), with order 10!."

	| G |
	G := PermutationGroup
		new: 10
		generators:
			{#(#(1 2)).
			#(10 1 2 3 4 5 6 7 8 9)}.
	self assert: G order equals: 10 factorial
]

{ #category : #tests }
GroupTest >> testBigOrder2 [
	"Test fast computation of group order with Schreier-Sims algorithm.
	This is the Mathieu group on 12 points, the second smallest of the 26 sporadic simple groups, with order 95040."

	self assert: PermutationGroup M12 order equals: 95040
]

{ #category : #tests }
GroupTest >> testCauchyFrobeniusLemma [
	"Also called Brunside's lemma, Burnside counting theorem, or orbit-counting theorem."

	| X G phi sum |
	X := 1 to: 3.
	G := Group alternating: X.
	phi := GroupAction
		from: G , X
		to: X
		evaluatingWithArguments: [ :f :x | f value: x ].
	sum := G elements sum: [ :g | (phi fixedPointsOf: g) size ].
	self assert: phi orbits size * G order equals: sum
]

{ #category : #tests }
GroupTest >> testConjugacyClasses [
	"From wikipedia article on conjugacy classes.
	https://en.wikipedia.org/wiki/Conjugacy_class"

	self assert: (SymmetricGroup new: 3) conjugacyClasses size equals: 3.
	self assert: (SymmetricGroup new: 4) conjugacyClasses size equals: 5
]

{ #category : #tests }
GroupTest >> testD3 [
	| D S A |
	D := PermutationGroup dihedral: 2 * 3.
	self testGroup: D.
	S := SymmetricGroup new: 3.
	self assert: D equals: S.
	A := AlternatingGroup new: 3.
	self assert: D commutator equals: A.
	self assert: D center isTrivial
]

{ #category : #tests }
GroupTest >> testDirectProduct [
	| S A G g |
	S := self smallGroupAtRandom.
	A := self smallGroupAtRandom.
	G := S directProduct: A.
	g := G atRandom.
	self
		assert:
			(G operation
				value:
					{g.
					(G inverseMap value: g)})
		equals: G identity.
	self testGroup: G.
	self testGroupHomomorphism: (G projection: 1).
	self testGroupHomomorphism: (G projection: 2)
]

{ #category : #tests }
GroupTest >> testGroup: G [
	| op inv e a b c |
	e := G identity.
	op := G operation.
	inv := G inverseMap.
	a := G atRandomBits: 100.
	b := G atRandomBits: 100.
	c := G atRandomBits: 100.
	self
		assert:
			(op
				value:
					{e.
					a})
		equals: a.
	self
		assert:
			(op
				value:
					{a.
					e})
		equals: a.
	self
		assert:
			(op
				value:
					{a.
					(inv value: a)})
		equals: e.
	self
		assert:
			(op
				value:
					{(inv value: a).
					a})
		equals: e.
	self
		assert:
			(op
				value:
					{(op
						value:
							{a.
							b}).
					c})
		equals:
			(op
				value:
					{a.
					(op
						value:
							{b.
							c})})
]

{ #category : #tests }
GroupTest >> testGroupAction: phi [
	| G X e g h x |
	G := phi group.
	X := phi space.
	e := G identity.
	g := G atRandomBits: 100.
	h := G atRandomBits: 100.
	x := X atRandomBits: 100.
	self
		assert:
			(phi
				value:
					{e.
					x})
		equals: x.
	self
		assert:
			(phi
				value:
					{g.
					(phi
						value:
							{h.
							x})})
		equals:
			(phi
				value:
					{(G operation
						value:
							{g.
							h}).
					x})
]

{ #category : #tests }
GroupTest >> testGroupHomomorphism: phi [
	| G H a b |
	G := phi domain.
	H := phi codomain.
	a := G atRandomBits: 100.
	b := G atRandomBits: 100.
	self assert: (phi value: G identity) = H identity.
	self assert: (phi value: (G operation value: {a. b})) = (H operation value: {phi value: a. phi value: b})
]

{ #category : #tests }
GroupTest >> testGroupRing [
	| G R a b c xa xb xc |
	G := self smallGroupAtRandom.
	R := G groupRing.
	a := G atRandom.
	b := G atRandom.
	c := G atRandom.
	xa := R embed: a.
	xb := R embed: b.
	xc := R embed: c.
	self assert: xa * xb equals: (R embed: a * b).
	self
		assert: (xa * 2 + xb) * xc - (xa * xc) - (xb * xc)
		equals: (R embed: a * c).
	self
		assert: (xa + xb) * (xa - xb)
		equals: (xa raisedTo: 2) - (xb raisedTo: 2) + (xb * xa) - (xa * xb)
]

{ #category : #tests }
GroupTest >> testGroupRingIsARing [
	| G R a a2 b b2 c c2 e e2 |
	G := self smallGroupAtRandom.
	R := G groupRing.
	e := G identity.
	a := G atRandom.
	b := G atRandom.
	c := G atRandom.
	e2 := R embed: e.
	a2 := R embed: a.
	b2 := R embed: b.
	c2 := R embed: c.
	self assert: e2 equals: R one.
	self assert: e2 * a2 equals: a2.
	self assert: a2 * e2 equals: a2.
	self assert: a2 * b2 * c2 equals: a2 * (b2 * c2).
	G isCommutative
		ifTrue: [ self assert: a2 * b2 equals: b2 * a2 ]
]

{ #category : #tests }
GroupTest >> testHessian [
	| H |
	H := PermutationGroup hessian.
	self assert: H elements size equals: 216.
	self testGroup: H
]

{ #category : #tests }
GroupTest >> testIsSolvable [
	| G |
	G := Group symmetric: (1 to: 3).
	self assert: G isSolvable
]

{ #category : #tests }
GroupTest >> testIsSolvableNot [
	| G |
	G := Group alternating: (1 to: 5).
	self assert: G isSolvable not
]

{ #category : #tests }
GroupTest >> testKleinFour [
	| V S A |
	V := PermutationGroup klein.
	self testGroup: V.
	S := SymmetricGroup new: 4.
	self assert: (V isNormalIn: S).
	A := AlternatingGroup new: 4.
	self assert: (V isNormalIn: A)
]

{ #category : #tests }
GroupTest >> testLagrangeTheorem [
	"G finite group, H subgroup of G, then |H| divides |G|."
	| G H |
	G := self smallGroupAtRandom.
	H := G span: (G random next: 3 atRandom) asSet.
	self assert: H order | G order
]

{ #category : #tests }
GroupTest >> testModularIntegersUnits [
	| m R U |
	m := (2 to: 100) atRandom.
	R := ZZ / m.
	U := R units.
	self assert: U size equals: (Sequence phi value: m)
]

{ #category : #tests }
GroupTest >> testOrbitStabilizerTheorem [
	| X G phi p |
	X := 1 to: 4.
	G := Group alternating: X.
	phi := GroupAction from: (G, X) to: X evaluatingWithArguments: [:f :x| f value: x].
	p := X atRandom.
	self assert: (phi stabilizerOf: p) order * (phi orbitOf: p) size = G order
]

{ #category : #tests }
GroupTest >> testPermutationGroupAction [
	self testGroupAction: (SymmetricGroup new: 10) action.
	self testGroupAction: (PermutationGroup cyclic: 15) action
]

{ #category : #tests }
GroupTest >> testPermutationGroupHomomorphism [
	"Magma Handbook, Example H57E2."

	| C15 h im |
	C15 := PermutationGroup cyclic: 15.
	h := C15 to: C15 evaluating: [ :g | g raisedTo: 3 ].
	im := h image.
	self assert: im space size equals: 15.
	self assert: im size equals: 5.
	self assert: im isCyclic
]

{ #category : #tests }
GroupTest >> testQuotientGroup [
	| G N Q pi h |
	G := Group integersMod: 6.
	N := G span: {(3 % 6)}.
	Q := G / N.
	self assert: Q size equals: 3.
	self testGroup: Q.
	pi := Q projection.
	self assert: (Q includes: (pi value: G atRandom)).
	h := Q atRandom.
	self assert: (pi value: (pi section value: h)) equals: h.
	self testGroupHomomorphism: pi
]

{ #category : #tests }
GroupTest >> testSymmetricOrder [
	| G |
	G := Group symmetric: (1 to: 4).
	self assert: G order equals: 4 factorial
]

{ #category : #tests }
GroupTest >> testTrivial [
	| G |
	G := PermutationGroup new: 4 generators: #().
	self assert: G size equals: 1.
	self assert: G isTrivial
]
