"
A simplicial k-chain is a formal linear combination of k-simplices.
"
Class {
	#name : #SimplicialChain,
	#superclass : #FormalSum,
	#category : #'Mathematics-Etc'
}

{ #category : #operations }
SimplicialChain >> boundary [
	"The boundary of a chain is the linear combination of the boundary of the simplices in the chain. The boundary of a k-chain is a (k-1)-chain."
	| answer |
	self dimension <= 0 ifTrue: [^ self zero].
	answer := self class over: self scalars.
	self keysAndValuesDo: [:key :value|
		| V minusValue |
		V := key vertices asArray.
		minusValue := value negated.
		1 to: V size do: [:i| | F |
			"F is the facet opposite the i-th vertex:"
			F := Simplex vertices: (V copyWithoutIndex: i).
			answer at: F add: (i odd ifTrue: [value] ifFalse: [minusValue])]].
	^ answer
]

{ #category : #accessing }
SimplicialChain >> dimension [
	self keysDo: [:any| ^ any dimension].
	^ -1
]

{ #category : #testing }
SimplicialChain >> isCycle [
	^ self boundary isZero
]
