"
This is the extended Buchberger algorithm. It keeps track of how the polynomials in the Groebner basis arise as linear combinations of the original generators of the ideal, and produces a matrix that maps the original generators to the Groebner basis (or equivalently a 'change of coordinates' module endomorphism of the corresponding ideal).

Input: a polynomial ideal given by generators, with a choice of *global* monomial ordering;
Output: a Groebner basis, and a 'change of basis' matrix that maps the original generators to the Groebner basis.

See Buchberger for a more general algorithm that works with both global and local monomial orderings.
"
Class {
	#name : #ExtendedBuchberger,
	#superclass : #Buchberger,
	#instVars : [
		'matrix'
	],
	#category : #'Mathematics-Polynomials-Algorithms'
}

{ #category : #'as yet unclassified' }
ExtendedBuchberger >> matrix [
	matrix ifNil: [self run].
	^ matrix
]

{ #category : #'as yet unclassified' }
ExtendedBuchberger >> run [
	"Extended Buchberger algorithm.
	Compute a standard basis from the input polynomials with the specified ordering."
	| R M S combinations division i0 |
	ideal ordering isGlobal ifFalse: [DomainError signal: 'not a global ordering'].
	basis := GroebnerBasis new.
	combinations := OrderedCollection new.
	R := ideal scalars.
	R scalars isField ifFalse: [^ DomainError signal: 'not over a field'].
	M := FormalSumsModule on: ideal generators over: R.
	S := ideal generators withIndexCollect: [:each :i| each -> (M e: i)].
	S := S asSortedCollection: [:a :b| a key leadingMonomial <= b key leadingMonomial].
	[i0 := basis size + 1.
	S do: [:f| (basis reduce: f key) isZero ifFalse: [basis add: f key. combinations add: f value]].
	S removeAll.
	1 to: basis size do: [:i| | fi hi ci ai |
		fi := basis at: i.
		hi := fi leadingMonomial.
		ci := fi coefficientAt: hi.
		ai := combinations at: i.
		(i+1 max: i0) to: basis size do: [:k| | fk hk ck lcm r f ak |
			fk := basis at: k.
			hk := fk leadingMonomial.
			lcm := hi lcm: hk.
			"Buchberger criterium 1 and 2:"
			(lcm ~= (hi * hk) and: [((1 to: i-1) noneSatisfy: [:j| (basis at: j) leadingMonomial | lcm])])
				ifTrue:
					[ck := fk coefficientAt: hk.
					ak := combinations at: k.
					f := fi * (lcm / hi) / ci - (fk * (lcm / hk) / ck).
					division := MultivariatePolynomialDivision divide: f by: basis.
					r := division remainder.
					r isZero
"						ifTrue: [Display fill: (i@k*4 extent: 3@3) fillColor: Color red]"
						ifFalse:
							["Display fill: (i@k*4 extent: 3@3) fillColor: Color green."
							S add: r -> ((ai * (R one * (lcm / hi) / ci) - (ak * (R one * (lcm / hk) / ck))) - (combinations * division quotients) sum)]]]].
	S isEmpty] whileFalse.
	matrix := R matrix: combinations size @ ideal generators size evaluating: [:i :j| (combinations at: i) at: (ideal generators at: j)]
]

{ #category : #'as yet unclassified' }
ExtendedBuchberger >> verify [
	| S G |
	S := ideal scalars tuple: ideal generators.
	G := ideal scalars tuple: self basis.
	^ matrix * S = G
]
