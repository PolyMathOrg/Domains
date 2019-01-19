"
TODO:
- Div^d(E) := subgroup of Div(E) of divisors of degree d
- Princ(E) := subgroup of Div^0(E) of principal divisors
- Pic^0(E) := Div^0(E) / Princ(E)
- Abel-Jacobi map Pic^0(E) -> E(K)
- equality: D1 = D2 iff D1 - D2 is a principal divisor
- a divisors of degree zero is principal iff the Abel-Jacobi map sends it to the zero point in the curve
- divisor reduction: red(D) := (AJ([D])) - (0)
- Miller's algorithm
"
Class {
	#name : #DivisorsGroup,
	#superclass : #FreeModule,
	#instVars : [
		'scheme',
		'scalars'
	],
	#category : #'Mathematics-Schemes-Divisors'
}

{ #category : #'instance creation' }
DivisorsGroup class >> on: aScheme [
	^ self on: aScheme over: ZZ
]

{ #category : #'instance creation' }
DivisorsGroup class >> on: aScheme over: aRing [
	^ self new scheme: aScheme; scalars: aRing
]

{ #category : #printing }
DivisorsGroup >> printOn: aStream [
	aStream nextPutAll: 'Div'.
"	(rationals = scheme ambient scalars) ifFalse: [aStream nextPutAll: rationals printText sub].
"	aStream nextPut: $(; print: scheme; nextPut: $)
]

{ #category : #accessing }
DivisorsGroup >> scalars [
	^ scalars
]

{ #category : #accessing }
DivisorsGroup >> scheme [
	^ scheme
]

{ #category : #'accessing-private' }
DivisorsGroup >> scheme: aScheme [
	scheme := aScheme
]
