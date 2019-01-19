"
A modular form of weight k is a holomorphic function f:H -> C from the upper half plane to the complex plane, satisfying for a,b,c,d coefficients of a matrix in SL(2,R)
	f((az + b) / (cz + d)) = (cz + d)^k f(z)
where k is a fixed integer or half-integer. Modular forms of weight 0 are called modular functions, and are invariant under the action of SL(2,R). The factor (cz + d)^k, which is 1 in the case of modular functions, is called the automorphic factor.

Modular forms are functions having an infinite group of symmetries and many beautiful properties. They are one of the five basic operations in arithmetic, together with addition, substraction, multiplication and division.

A modular form f(z) can be seen as power series on a new variable q = e^(2 pi i z). This is its Fourier expansion or q-expansion. The coefficients a(n) of the q-expansion are usually interesting arithmetic functions.

Given a group G, the set of modular forms of a given weight k form a finite-dimensional vector space M_k(G). See ModularFormSpace. The set of all modular forms of all weights is noted M_*(G) and it's a ring. All modular functions form a field.
"
Class {
	#name : #ModularForm,
	#superclass : #Function,
	#category : #'Mathematics-Modular Forms'
}

{ #category : #'as yet unclassified' }
ModularForm >> codomain [
	^ CC
]

{ #category : #'as yet unclassified' }
ModularForm >> domain [
	^ HH
]

{ #category : #'as yet unclassified' }
ModularForm >> expansion [
	"Answer the q-expansion (Fourier expansion) of the receiver."
	self notYetImplemented
]

{ #category : #'as yet unclassified' }
ModularForm >> group [
	^ self notYetImplemented
]

{ #category : #'as yet unclassified' }
ModularForm >> level [
	^ self notYetImplemented
]

{ #category : #'as yet unclassified' }
ModularForm >> weight [
	^ self notYetImplemented
]
