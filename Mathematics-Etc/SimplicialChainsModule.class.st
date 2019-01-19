"
My instances are free modules of simplicial k-chains in a simplicial complex. See SimplicialChain.
"
Class {
	#name : #SimplicialChainsModule,
	#superclass : #FormalSumsModule,
	#category : #'Mathematics-Etc'
}

{ #category : #elements }
SimplicialChainsModule >> coefficients: aDictionary [
	^ (SimplicialChain coefficients: aDictionary) parent: self
]

{ #category : #basis }
SimplicialChainsModule >> e: anInteger [
	^ SimplicialChain new parent: self; at: (self symbols at: anInteger) put: self scalars one; yourself
]
