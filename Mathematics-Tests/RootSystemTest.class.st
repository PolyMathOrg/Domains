Class {
	#name : #RootSystemTest,
	#superclass : #TestCase,
	#category : #'Mathematics-Tests'
}

{ #category : #'as yet unclassified' }
RootSystemTest >> rootSystem1 [
	| V roots |
	V := QQ raisedTo: 3.
	roots := Set new.
	1 to: 3 do: [ :i | 
		1 to: i - 1 do: [ :j | 
			| r |
			roots
				add: (r := (V e: i) - (V e: j));
				add: r negated ] ].
	^ RootSystem on: V roots: roots
]

{ #category : #'as yet unclassified' }
RootSystemTest >> rootSystem2 [
	| V roots |
	V := QQ raisedTo: 3.
	roots := Set new.
	1 to: 3 do: [ :i | 
		1 to: i - 1 do: [ :j | 
			roots
				add: (V e: i) - (V e: j);
				add: (V e: j) - (V e: i);
				add: (V e: i) + (V e: j);
				add: ((V e: i) + (V e: j)) negated ] ].
	^ RootSystem on: V roots: roots
]

{ #category : #'as yet unclassified' }
RootSystemTest >> testBaseSignCondition [
	| R |
	R := self rootSystem1.
	'R roots do: [:each| | coordinates |
			coordinates := R simpleRoots coordinatesOf: each :: asArray.
			self assert: (coordinates allSatisfy: [:xi| xi >= 0]) | (coordinates allSatisfy: [:xi| xi <= 0])]'
]

{ #category : #'as yet unclassified' }
RootSystemTest >> testPositiveRoots [
	| V R |
	R := self rootSystem1.
	V := R ambient.
	R positiveRoots
		do: [ :each | 
			"the point must be in the positive Weyl chamber"
			self
				assert:
					(V innerProduct
						value:
							{each.
							(1 , 1 , 1)}) > 0 ]
]

{ #category : #accessing }
RootSystemTest >> testWeylGroup [
	| R W |
	R := self rootSystem1.
	W := R weylGroup.
	"The Weyl group of this root system is isomorphic to Sym(3), so we test some properties of Sym(3):"
	self assert: W order equals: 6.
	self assert: W center isTrivial.
	self assert: W isSolvable.
	self assert: W isCyclic not
]

{ #category : #'as yet unclassified' }
RootSystemTest >> testWeylGroup2 [
	| R W |
	R := self rootSystem2.
	W := R weylGroup. "this is an index 2 subgroup of the hyperoctahedral group"
	self assert: W order = 24
]

{ #category : #'as yet unclassified' }
RootSystemTest >> testWeylGroupAndSimpleRoots [
	"For every root, there exists an transformation in the Weyl group that makes it a simple root."
	| R W |
	R := self rootSystem1.
	W := R weylGroup.
	R roots do: [:r| self assert: (W anySatisfy: [:w| R simpleRoots includes: (w value: r)])]
]
