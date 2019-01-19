"
Monomial orderings defined by weight tuples.

For monomials in n variables, there are n! (n factorial) orderings. In certain applications such as Groebner bases it's desirable to easily construct new monomial orderings.

ideterminates 		an array with the indeterminates (variables) in order;
weights 				n-tuples with real coefficients.

Suppose you have two monomials:
	a = x1^a1 x2^a2 ... xn^an
	b = x1^b1 x2^b2 ... xn^bn
where some of the ai or bi may be 0. And suppose the variables are ordered x1 < x2 < ... < xn. If we are asked for the truth of a < b, we enumerate the weights and for each one, (w1, w2, ..., wn) we do:
	aSum = a1 w1 + a2 w2 + ... + an wn,
	bSum = b1 w1 + b2 w2 + ... + bn wn;
if aSum < bSum, then a < b; if aSum > bSum, then a > b; if aSum = bSum, we continue with the next weight, until there are no more weights (then, a should equal b...).

Theorem: For any monomial ordering in a finite number of variables, there is a collection of weights that models the ordering. So, with this idea we can contruct any ordering.

"
Class {
	#name : #WeightedMonomialOrdering,
	#superclass : #MonomialOrdering,
	#instVars : [
		'weights'
	],
	#category : #'Mathematics-Monomials-Orderings'
}

{ #category : #'instance creation' }
WeightedMonomialOrdering class >> glex: aCollection [
	"Answer the total (or graded) lexicographic ordering with the indeterminates of aCollection."
	| weights |
	weights := OrderedCollection new.
	weights add: (QQ tuple: aCollection size evaluating: [:each| 1]).
	weights addAll: (self lex: aCollection) weights.
	^ self new: aCollection size weights: weights
]

{ #category : #'instance creation' }
WeightedMonomialOrdering class >> grevlex: aCollection [
	"Answer the total (or graded) reverse lexicographic ordering with the indeterminates of aCollection."
	| weights |
	weights := OrderedCollection new.
	weights add: (QQ tuple: aCollection size evaluating: [:each| 1]).
	weights addAll: (self revlex: aCollection) weights.
	^ self new: aCollection size weights: weights
]

{ #category : #'instance creation' }
WeightedMonomialOrdering class >> indeterminates: indeterminates weights: weights [
	weights isSequenceable ifFalse: [self error: 'the indeterminates are unordered'].
	^ self new: indeterminates size weights: (weights collect: [:each| each withIndexCollect: [:x :i| each at: (indeterminates indexOf: i)]])
]

{ #category : #'instance creation' }
WeightedMonomialOrdering class >> lex: aCollection [
	"Answer the lexicographic order with the indeterminates of aCollection."
	| weighs n |
	n := aCollection size.
	weighs := (1 to: n) collect: [:i| QQ tuple: n evaluating: [:k| k==i ifTrue:[1] ifFalse: [0]]].
	^ self indeterminates: aCollection weights: weighs
]

{ #category : #'instance creation' }
WeightedMonomialOrdering class >> new: anInteger weights: anArray [
	^ (self new: anInteger) weights: anArray
]

{ #category : #'instance creation' }
WeightedMonomialOrdering class >> revlex: aCollection [
	"Answer the reverse lexicographic ordering with the indeterminates of aCollection."
	^ (self lex: aCollection) reverse
]

{ #category : #arithmetic }
WeightedMonomialOrdering >> * aMonomialOrdering [
	| newWeights zero |
	newWeights := OrderedCollection new.
	zero := aMonomialOrdering weights first zero.
	weights do: [:each| newWeights add: each, zero].
	zero := weights first zero.
	aMonomialOrdering weights do: [:each| newWeights add: zero, each].
	^ self class
		new: self rank + aMonomialOrdering rank
		weights: newWeights
]

{ #category : #arithmetic }
WeightedMonomialOrdering >> , aMonomialOrdering [
	"Answer the concatenation of the recever and the argument."

	self rank = aMonomialOrdering rank ifFalse: [^ self error: 'cannot concatenate monomial orderings of different rank'].
	^ self class
		new: self rank
		weights: (self weights copy addAll: aMonomialOrdering weights; yourself)
]

{ #category : #ordering }
WeightedMonomialOrdering >> compare: aMonomial with: anotherMonomial [
	| t1 t2 |
	t1 := FloatArray new: indeterminates size.
	t2 := t1 copy.
	1 to: indeterminates size do: [:i| | xi |
		t1 at: i put: (aMonomial at: (xi := indeterminates at: i)).
		t2 at: i put: (anotherMonomial at: xi)].
	self weights do: [:w|
		| a b |
		a := w dot: t1.
		b := w dot: t2.
		a = b ifFalse: [^ a > b ifTrue: [1] ifFalse: [-1]]].
	^ 0
]

{ #category : #copying }
WeightedMonomialOrdering >> copyWithout: anIndeterminate [
	^ (super copyWithout: anIndeterminate) weights: (weights copyWithoutIndex: anIndeterminate)
]

{ #category : #arithmetic }
WeightedMonomialOrdering >> inverse [
	^ self class
		new: self rank
		weights: (self weights collect: [:each| each reversed])
]

{ #category : #ordering }
WeightedMonomialOrdering >> leadingMonomialOf: aPolynomial [
	"Answer the head monomial of aPolynomial according to this ordering."
	| head headTuple |
	headTuple := FloatArray new: indeterminates size.
	aPolynomial monomialsDo: [:each|
		| t a b |
		t := FloatArray new: indeterminates size.
		1 to: indeterminates size do: [:i| t at: i put: (each at: (indeterminates at: i))].
		'head isNil
					ifTrue: [head := each. headTuple := t]
					ifFalse: [self weights anySatisfy: [:w|
						a := w dot: t.
						b := w dot: headTuple. "could be precomputed up to some extent"
						a ~= b] :: ifTrue: [a > b ifTrue: [head := each. headTuple := t]]]'].
	^ head
]

{ #category : #printing }
WeightedMonomialOrdering >> printOn: aStream [
	super printOn: aStream.
	aStream space.
	self weights do: [:each| aStream print: each] separatedBy: [aStream space]
]

{ #category : #arithmetic }
WeightedMonomialOrdering >> reverse [
	^ self class
		new: self rank
		weights: (self weights collect: [:each| each negated])
]

{ #category : #accessing }
WeightedMonomialOrdering >> weights [
	^ weights
]

{ #category : #'accessing-private' }
WeightedMonomialOrdering >> weights: aCollectionOfTuples [
	weights := aCollectionOfTuples collect: [:each| each as: FloatArray]
]
