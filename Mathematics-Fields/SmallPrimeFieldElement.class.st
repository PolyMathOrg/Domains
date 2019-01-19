Class {
	#name : #SmallPrimeFieldElement,
	#superclass : #ModularInteger,
	#category : #'Mathematics-Fields-Finite'
}

{ #category : #operations }
SmallPrimeFieldElement >> * aModularInteger [
	| b i p |
	aModularInteger class == self class ifFalse: [^ super * aModularInteger].
	b := aModularInteger representative.
	(representative = 0 or: [b = 1]) ifTrue: [^ self].
	(representative = 1 or: [b = 0]) ifTrue: [^ aModularInteger].
	i := (parent logTable at: representative) + (parent logTable at: b).
	i >= (p := parent modulus) ifTrue: [i := i - p + 1].
	^ parent representative: (parent expTable at: i)
]

{ #category : #operations }
SmallPrimeFieldElement >> / aModularInteger [
	| b i |
	aModularInteger class == self class ifFalse: [^ super / aModularInteger].
	b := aModularInteger representative.
	(representative = 0 or: [b = 1]) ifTrue: [^ self].
	b = 0 ifTrue: [^ (ZeroDivide dividend: aModularInteger) signal].
	i := (parent logTable at: representative) - (parent logTable at: b).
	i <= 0 ifTrue: [i := i + parent modulus - 1].
	^ parent representative: (parent expTable at: i)
]
