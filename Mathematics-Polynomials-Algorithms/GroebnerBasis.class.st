"
Groebner bases are a special case of standard bases.

For a fixed global monomial ordering, a subset G = {g1,...,gm} of an ideal I = <f1,...,fm> of a polynomial ring is called a Groebner basis for I if every polynomial f in I is reducible by G, i.e. there exists g in G such that its leading monomial LM(g) divides LM(f).

When all generators {f1,...,fm} are linear, a Groebner basis corresponds to ""row echelon form"" or ""triangular system""; when they are univariate, then a Groebner basis corresponds to gcd(f1,...,fm). In general, a Groebner basis for an ideal I consists of all the ""smallest polynomials"" in I under the given monomial ordering.

See also Buchberger and ExtendedBuchberger.
"
Class {
	#name : #GroebnerBasis,
	#superclass : #StandardBasis,
	#category : #'Mathematics-Polynomials-Algorithms'
}

{ #category : #operations }
GroebnerBasis >> coordinatesOf: aPolynomial [
	^ (MultivariatePolynomialDivision divide: aPolynomial by: self) quotients
]

{ #category : #operations }
GroebnerBasis >> reduce2: aPolynomial [ 
	"Answer the remainder of the argument when divided by the receiver (i.e. the normal form with respect to the receiver)."
	| division |
	division := MultivariatePolynomialDivision divide: aPolynomial by: self.
"	division verify ifFalse: [self halt]."
	^ division remainder
]

{ #category : #operations }
GroebnerBasis >> reduce: aPolynomial [
	"Answer a top-reduced normal form of aPolynomial with respect to the receiver (i.e. without doing tail reduction)."
	| h |
	h := aPolynomial.
	[h isZero]
		whileFalse:
			[| lmh lmg g |
			lmh := h leadingMonomial.
			g := elements detect: [:one| (lmg := one leadingMonomial) | lmh] ifNone: [^ h].
			h := h - (g * (lmh / lmg) * (h leadingCoefficient / g leadingCoefficient))].
	^ h
]

{ #category : #operations }
GroebnerBasis >> reduce: aPolynomial startingAt: startIndex [
	"Answer a top-reduced normal form of aPolynomial with respect to the receiver (.e. without doing tail reduction)."
	| h |
	h := aPolynomial.
	[h isZero]
		whileFalse:
			[| lmh lmg g |
			lmh := h leadingMonomial.
			(startIndex to: elements size) detect: [:one| (lmg := (g := elements at: one) leadingMonomial) | lmh] ifNone: [^ h].
			h := h - (g * (lmh / lmg) * (h leadingCoefficient / g leadingCoefficient))].
	^ h
]

{ #category : #operations }
GroebnerBasis >> reduceFull: aPolynomial [
	"Answer the tail-reduced normal form of aPolynomial with respect to the receiver (doing full tail reduction)."
	| g h |
	g := aPolynomial.
	h := g zero.
	[g isZero]
		whileFalse:
			[g := self reduce: g.
			g isZero ifFalse: [h := h + g leadingTerm. g := g tail]].
	^ h / h leadingCoefficient
]

{ #category : #operations }
GroebnerBasis >> reduceFull: aPolynomial startingAt: startIndex [
	"Answer the tail-reduced normal form of aPolynomial with respect to the receiver (doing full tail reduction)."

	| g h |
	g := aPolynomial.
	h := g zero.
	[ g isZero ]
		whileFalse: [ g := self reduce: g startingAt: startIndex.
			g isZero
				ifFalse: [ h := h + g leadingTerm.
					g := g tail ] ].
	^ h / h leadingCoefficient
]
