Class {
	#name : #SymmetricPolynomialRing,
	#superclass : #Ring,
	#instVars : [
		'polynomials'
	],
	#category : #'Mathematics-Etc'
}

{ #category : #'as yet unclassified' }
SymmetricPolynomialRing >> generators [
	^ (1 to: self rank) collect: [:i| polynomials symmetric: i]
]
