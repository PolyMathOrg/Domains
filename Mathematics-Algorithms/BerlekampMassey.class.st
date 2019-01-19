"
This is the Berlekamp-Massey algorithm. The initial purpose of this algorithm was to evaluate Binary BCH codes, but it has found many uses, including inverting matrices of constant diagonal, solving linear recurrences (synthesizing LFSRs with a specified output sequence), etc.

Input: a_1..a_{2n} the first 2n coefficients of a linear recursive sequence over a field K of order at most n (the minimal polynomial has degree bound n);
Output: the minimal polynomial of the sequence.

The algorithm performs O(n^2/2) multiplications; more precisely, at most 2 floor(n^2/4) - n + 1 multiplications.
"
Class {
	#name : #BerlekampMassey,
	#superclass : #Object,
	#category : #'Mathematics-Algorithms'
}

{ #category : #'as yet unclassified' }
BerlekampMassey >> run [
	| F Fx x C L N m B d b s |
	x := Fx x.
	C := Fx one.
	L := 0. "current number of errors"
	N := 100. "total number of syndromes"
	B := C.
	b := F one. "copy of the last discrepancy d"
	m := 1. "number of iterations since last update"
	0 to: N do: [:n|
		"calculate discrepancy:"
		d := (s coefficientAtDegree: n) + ((1 to: L) sum: [:i| (C coefficientAtDegree: i) * (s coefficientAtDegree: n-i)]).
		d = 0
			ifTrue: [m := m + 1]
			ifFalse: [2*L <= n
				ifTrue:
					[|t|
					t := C.
					C := C - ((x raiseTo: m)*(d/b)*B).
					B := t.
					L := n + 1 - L.
					b := d.
					m := 1]
				ifFalse:
					[C := C - ((x raiseTo: m)*(d/b)*B).
					m := m + 1]]].
	^ L
]
