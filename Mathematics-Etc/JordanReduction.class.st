Class {
	#name : #JordanReduction,
	#superclass : #Object,
	#instVars : [
		'matrix',
		'blocks'
	],
	#category : #'Mathematics-Etc'
}

{ #category : #'as yet unclassified' }
JordanReduction >> block: eigenvalue size: n [
	| K one zero |
	K := matrix scalars.
	one := K one.
	zero := K zero.
	^ K matrix: n@n evaluating: [:i :j| i=j ifTrue: [eigenvalue] ifFalse: [j-1=i ifTrue: [one] ifFalse: [zero]]]
]

{ #category : #'as yet unclassified' }
JordanReduction >> blocks [
	blocks isNil ifTrue: [self run].
	^ blocks
]

{ #category : #'as yet unclassified' }
JordanReduction >> matrix: aMatrix [
	matrix := aMatrix
]

{ #category : #'as yet unclassified' }
JordanReduction >> run [
	| spectrum |
	spectrum := matrix spectrum.
	spectrum size = matrix height ifFalse: [^ self error: 'the characteristic polynomial doesn''t split'].
"	I := matrix species identity."
	blocks := Bag new.
	spectrum asSet do: [:eigenvalue|
		| multiplicity dimensions X T count |
		multiplicity := spectrum occurrencesOf: eigenvalue.
		dimensions := OrderedCollection new.
		X := matrix - (matrix scalars matrix: matrix dimension scalar: eigenvalue).
		T := X.
		[(dimensions add: T nullity) < multiplicity] whileTrue: [T := T * X].
		count := 0.
		dimensions size to: 1 by: -1 do: [:i| | k |
			k := (dimensions at: i) - (dimensions at: i-1 ifAbsent: [0]).
			blocks add: (self block: eigenvalue size: i) withOccurrences: k - count.
			count := count + k]]
]
