"
This is the Buchberger's algorithm.

Input: a polynomial ideal given by generators, with a choice of monomial ordering;
Output: a standard basis or a Groebner basis.

When the monomial ordering is global, the algorithm outputs a Groebner basis. In case of a local monomial ordering, the algorithm uses Mora's normal form and outputs a standard basis.

"
Class {
	#name : #Buchberger,
	#superclass : #Object,
	#instVars : [
		'ideal',
		'basis'
	],
	#category : #'Mathematics-Polynomials-Algorithms'
}

{ #category : #'instance creation' }
Buchberger class >> on: anIdeal [
	^ self new ideal: anIdeal
]

{ #category : #'as yet unclassified' }
Buchberger >> basis [
	basis ifNil: [self run].
	^ basis
]

{ #category : #'as yet unclassified' }
Buchberger >> ideal: anIdeal [
	ideal := anIdeal
]

{ #category : #'as yet unclassified' }
Buchberger >> run [
	"Buchberger's algorithm.
	Compute a standard basis from the input polynomials with the specified ordering."
	| S i0 |
	basis := ideal ordering isGlobal ifTrue: [GroebnerBasis new] ifFalse: [StandardBasis new].
	ideal isZero ifTrue: [^ basis].
	ideal scalars scalars isField ifFalse: [^ DomainError signal: 'not over a field'].
	S := ideal generators copy.
	[i0 := basis size + 1.
	S := S asSortedCollection: [:a :b| a leadingMonomial <= b leadingMonomial].
	"Full reduction in this step produces a reduced basis:"
	S do: [:f| | r | (r := basis reduceFull: f) isZero ifFalse: [basis add: r]].
	S := OrderedCollection new.
	1 to: basis size do: [:i| | fi hi ci |
		fi := basis at: i.
		hi := fi leadingMonomial.
		ci := fi leadingCoefficient.
		(i+1 max: i0) to: basis size do: [:j| | fj hj cj lcm r |
			fj := basis at: j.
			hj := fj leadingMonomial.
			lcm := hi lcm: hj.
			"Buchberger criterium 1 and 2:"
			(lcm ~= (hi * hj) and: [((1 to: i-1) noneSatisfy: [:k| (basis at: k) leadingMonomial | lcm])])
				ifTrue:
					[cj := fj leadingCoefficient.
					"Perform only top-reduction here (do full-reduction just before adding to the basis):"
					r := basis reduce: fi * (lcm / hi) / ci - (fj * (lcm / hj) / cj).
					r isZero
						"ifTrue: [Display fill: (i@k*4 extent: 3@3) fillColor: Color red]"
						ifFalse: [
							"Display fill: (i@k*4 extent: 3@3) fillColor: Color green."
							S add: r]]]].
	S isEmpty] whileFalse
]
