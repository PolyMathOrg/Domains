Class {
	#name : #MonomialTest,
	#superclass : #TestCase,
	#category : #'Mathematics-Tests'
}

{ #category : #tests }
MonomialTest >> testAntigradedLexOrdering [
	"Example from 'Using Algebraic Geometry', Cox, Little, O'Shea, Ch. 4, 3.2."
	| M x y |
	M := FreeAbelianMonoid new: 2 ordering: #lglex. "antigraded lex order"
	x := M x: 1.
	y := M x: 2.
	self assert: M identity > x.
	self assert: x > y.
	'self assert: x^2 > (x*y).
		self assert: x*y > (y raiseTo: 2).
		self assert: (y^2) > (x raiseTo: 3)'
]

{ #category : #tests }
MonomialTest >> testAntigradedRevlexOrdering [
	"Example from 'Using Algebraic Geometry', Cox, Little, O'Shea, Ch. 4, 3.3."
	| M x y z ordering |
	"The antigraded revlex order:"
	ordering := LocalGradedReverseLexicographicOrdering indeterminates: #(3 2 1).
	M := FreeAbelianMonoid new: 3 ordering: ordering.
	x := M x: 1.
	y := M x: 2.
	z := M x: 3.
	self assert: M identity > x.
	self assert: x > y.
	self assert: y > z.
'	self assert: x^2 > (x*y).
	self assert: x*y > (y^2).
	self assert: (x*z) > (y*z).
	self assert: (y*z) > (z^2)'
]

{ #category : #tests }
MonomialTest >> testHash [
	| m1 m2 |
	m1 := Monomial exponents: #(1 2 0).
	m2 := Monomial exponents: #(1 2 0 0 0 0 0).
	self assert: m1 hash equals: m2 hash
]

{ #category : #tests }
MonomialTest >> testLocalMonomialOrderings [
	"Examples from Magma handbook."

	| f |
	'f := ZZ polynomialsIn: #(x y z) ordering: #llex :: generate: [:x :y :z| 1 + x + y + z + (x^7) + (x^8*(y^7)) + (y^5) + (z^10)]'.
		self
		assert: f printString
		equals: '1 + x + x^7 + y + y^5 + x^8y^7 + z + z^{10}'.
	self
		assert: (f orderedBy: #lgrevlex) printString
		equals: '1 + z + y + x + y^5 + x^7 + z^{10} + x^8y^7'
]

{ #category : #tests }
MonomialTest >> testMonomialDivision [
	| M x y |
	M := FreeAbelianMonoid new: 2.
	x := M x: 1.
	self assert: x*x = (M x: 1 to: 2).
	y := M x: 2.
	self assert: x*x*y / (x*y) = x.
	self assert: x*y*x / x = (x*y).
	self assert: x*y*x*y / (x*y) = (x*y)
]

{ #category : #tests }
MonomialTest >> testMonomialGCD [
	| M x y a b |
	M := FreeAbelianMonoid new: 2.
	x := M x: 1.
	y := M x: 2.
	a := x*x*y*y*y.
	b := x*x*x*y*y.
	self assert: (a gcd: b) = (x*x*y*y)
]

{ #category : #tests }
MonomialTest >> testMonomialLCM [
	| M x y a b |
	M := FreeAbelianMonoid new: 2.
	x := M x: 1.
	y := M x: 2.
	a := x*x.
	b := x*y*y.
	self assert: (a lcm: b) = (x*x*y*y)
]

{ #category : #tests }
MonomialTest >> testMonomialOrderings [
	| P x y z f lex glex grevlex |
	P := ZZ polynomialsIn: 3.
	x := P x.
	y := P y.
	z := P z.
	f := 10 * x - (7 * (y raisedTo: 4)) + (11 * (y raisedTo: 3) * z).
	lex := MonomialOrdering lex: 3.
	glex := MonomialOrdering glex: 3.
	grevlex := MonomialOrdering grevlex: 3.
	self assert: (f orderedBy: lex) leadingCoefficient equals: 10.
	self assert: (f orderedBy: glex) leadingCoefficient equals: -7.
	self assert: (f orderedBy: grevlex) leadingCoefficient equals: -7	"this matches the definition in Singular"
]

{ #category : #tests }
MonomialTest >> testMonomialOrderings2 [
	"Examples from Macaulay2 documentation."

	| R a b c d f |
	R := ZZ polynomialsIn: #(a b c d).
	a := R x: 1.
	b := R x: 2.
	c := R x: 3.
	d := R x: 4.
	f := a + (b raisedTo: 100) + (c*d).
	self assert: (f orderedBy: #lex) printString = 'a + b^{100} + cd'.
	self assert: (f orderedBy: #grevlex) printString = 'b^{100} + cd + a'.
	self assert: (f orderedBy: #glex) printString = 'b^{100} + cd + a'
]

{ #category : #tests }
MonomialTest >> testMonomialOrderings3 [
	"Examples from Derksen, Kemper 'Computational Invariant Theory' 1.1.1."
	| P x1 x2 x3 x4 f |
	P := ZZ polynomialsIn: 4.
	x1 := P x: 1.
	x2 := P x: 2.
	x3 := P x: 3.
	x4 := P x: 4.
	f := x1 + (x2*x4) + (x3 raisedTo: 2).
	self assert: (f orderedBy: #lex) leadingTerm = x1.
	self assert: (f orderedBy: #glex) leadingTerm = (x2*x4).
	self assert: (f orderedBy: #grevlex) leadingTerm = (x3 raisedTo: 2)
]

{ #category : #tests }
MonomialTest >> testMonomialOrderings4 [
	"Examples from en.wikipedia.org/wiki/Monomial_order to illustrate the difference between graded lexicographic and graded reverse lexicographic."
	| M S |
	M := FreeAbelianMonoid new: 3 ordering: #glex.
	S := Set new.
	1 to: 3 do: [:i| i to: 3 do: [:j| S add: (M x: i) * (M x: j)]].
	self assert: (S sorted: [:a :b| a > b]) printString = '({x1}^2, {x1}{x2}, {x1}{x3}, {x2}^2, {x2}{x3}, {x3}^2)'.
	M := M orderedBy: #grevlex.
	S := S collect: [:each| M ! each].
	self assert: (S sorted: [:a :b| a > b]) printString = '({x1}^2, {x1}{x2}, {x2}^2, {x1}{x3}, {x2}{x3}, {x3}^2)'
]

{ #category : #tests }
MonomialTest >> testMonomialOrderingsExample [
	| a b lex glex grevlex |
	a := Monomial exponents: #(3 2 8).
	b := Monomial exponents: #(2 9 2).
	lex := FreeAbelianMonoid new: 3 ordering: #lex.
	glex := FreeAbelianMonoid new: 3 ordering: #glex.
	grevlex := FreeAbelianMonoid new: 3 ordering: #grevlex.
	self assert: (a as: lex) > (b as: lex).
	self assert: (a as: glex) > (b as: glex).
	self assert: (a as: grevlex) < (b as: grevlex)
]

{ #category : #tests }
MonomialTest >> testMonomialOrderingsExample2 [
	| a b lex glex |
	a := Monomial exponents: #(0 2 9).
	b := Monomial exponents: #(0 5 3).
	lex := FreeAbelianMonoid new: 3 ordering: #lex.
	glex := FreeAbelianMonoid new: 3 ordering: #glex.
	"	grevlex := FreeAbelianMonoid new: 3 ordering: #grevlex."
	self assert: (b as: lex) > (a as: lex).
	self assert: (a as: glex) > (b as: glex)
	"	self assert: (a as: grevlex) < (b as: grevlex)"
]

{ #category : #tests }
MonomialTest >> testMonomialOrderingsExample3 [
	| a b lex glex grevlex |
	a := Monomial exponents: #(2 1 2).
	b := Monomial exponents: #(1 3 1).
	lex := FreeAbelianMonoid new: 3 ordering: #lex.
	glex := FreeAbelianMonoid new: 3 ordering: #glex.
	grevlex := FreeAbelianMonoid new: 3 ordering: #grevlex.
	self assert: (a as: lex) > (b as: lex).
	self assert: (a as: glex) > (b as: glex).
	self assert: (a as: grevlex) < (b as: grevlex)
]

{ #category : #tests }
MonomialTest >> testMonomialOrderingsOfIndeterminates [
	| M x y z |
	M := FreeAbelianMonoid new: 3.
	x := M x: 1.
	y := M x: 2.
	z := M x: 3.
	{(MonomialOrdering lex: 3).
	(MonomialOrdering llex: 3).
	(MonomialOrdering glex: 3).
	(MonomialOrdering grevlex: 3)}
		do: [ :ordering | 
			self assert: (x orderedBy: ordering) > (y orderedBy: ordering).
			self assert: (y orderedBy: ordering) > (z orderedBy: ordering) ]
]

{ #category : #tests }
MonomialTest >> testMonomialOrderingsOfIndeterminatesReordered [
	| M x y z |
	M := FreeAbelianMonoid
		new: 3
		ordering: (MonomialOrdering lex: #(2 1 3)).
	x := M x: 1.
	y := M x: 2.
	z := M x: 3.
	self assert: y > x.
	self assert: x > z
]

{ #category : #tests }
MonomialTest >> testMonomialOrderingsSingularExample [
	"'A Singular Introduction to Commutative Algebra', Example 1.2.13 (monomial orderings)."

	| f |
	f := (QQ polynomialsIn: #(x y z)) ! [:x :y :z| (x raisedTo: 3)*y*z + (x raisedTo: 3) + (x*(y raisedTo: 2)) + (y raisedTo: 5) + (z raisedTo: 4)].
	"Global orderings:"
	self
		assert: (f orderedBy: #lex) printString
		equals: 'x^3yz + x^3 + xy^2 + y^5 + z^4'.
	self
		assert: (f orderedBy: #grevlex) printString
		equals: 'y^5 + x^3yz + z^4 + x^3 + xy^2'.
	self
		assert: (f orderedBy: #glex) printString
		equals: 'x^3yz + y^5 + z^4 + x^3 + xy^2'
	"TODO: weighted total lexicographic ordering"
	"Local orderings don't match because we implemented them with Magma conventions."
]

{ #category : #tests }
MonomialTest >> testMonomialProduct [
	| M x y |
	M := FreeAbelianMonoid new: 2.
	x := M x: 1.
	self assert: x * x equals: (M x: 1 to: 2).
	y := M x: 2.
	self assert: x * y equals: y * x.
	self assert: x * y * y equals: x * (y * y).
	self assert: (x * y * y at: 2) equals: 2.
	self assert: (x * y * x * x * y) degree equals: 5
]

{ #category : #tests }
MonomialTest >> testWeightedMonomialOrderings [
	| P x y z f lex glex grevlex revlex |
	P := ZZ polynomialsIn: 3.
	x := P x.
	y := P y.
	z := P z.
	f := 10*x - (7*(y raisedTo: 4)) + (11*(y raisedTo: 3)*z).
	lex := WeightedMonomialOrdering lex: (1 to: 3).
	glex := WeightedMonomialOrdering glex: (1 to: 3).
	grevlex := WeightedMonomialOrdering grevlex: (1 to: 3).
	revlex := WeightedMonomialOrdering grevlex: (1 to: 3).
	self assert: (f orderedBy: lex) leadingCoefficient equals: 10.
	self assert: (f orderedBy: glex) leadingCoefficient equals: -7.
	self assert: (f orderedBy: grevlex) leadingCoefficient equals: 11.
	self assert: (f orderedBy: revlex) leadingCoefficient equals: 11
]

{ #category : #tests }
MonomialTest >> testWeightedMonomialOrderingsConsistency [
	| P x y z f lex glex grevlex revlex |
	P := ZZ polynomialsIn: 3.
	x := P x.
	y := P y.
	z := P z.
	f := 10 * x - (7 * (y raisedTo: 4)) + (11 * (y raisedTo: 3) * z).
	lex := WeightedMonomialOrdering lex: (1 to: 3).
	glex := WeightedMonomialOrdering glex: (1 to: 3).
	grevlex := WeightedMonomialOrdering grevlex: (1 to: 3).
	revlex := WeightedMonomialOrdering grevlex: (1 to: 3).
	self
		assert: (f orderedBy: lex) monomials asArray
		equals: (f orderedBy: #lex) monomials asArray.
	self
		assert: (f orderedBy: glex) monomials asArray
		equals: (f orderedBy: #glex) monomials asArray.
	self
		assert: (f orderedBy: grevlex) monomials asArray
		equals: (f orderedBy: #grevlex) monomials asArray.
	self
		assert: (f orderedBy: revlex) monomials asArray
		equals: (f orderedBy: #revlex) monomials asArray
]
