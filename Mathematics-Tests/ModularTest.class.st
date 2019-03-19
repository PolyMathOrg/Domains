Class {
	#name : #ModularTest,
	#superclass : #TestCase,
	#category : #'Mathematics-Tests'
}

{ #category : #tests }
ModularTest >> testGamma0Index [
	self assert: ((1 to: 19) collect: [:each| (Gamma0CongruenceSubgroup new: each) index]) = #(1 3 4 6 6 12 8 12 12 18 12 24 14 24 24 24 18 36 20).
	self
		assert: (Gamma0CongruenceSubgroup new: 32041) index
		equals: 32220
]

{ #category : #tests }
ModularTest >> testGamma0NumberOfCusps [
	| p |
	'self assert: (1 to: 19 :: collect: [:each| Gamma0CongruenceSubgroup new: each :: numberOfCusps]) =  #(1 2 2 3 2 4 2 4 4 4 2 6 2 4 4 6 2 8 2)'.
	p := 1.
	100 timesRepeat: [self assert: (Gamma0CongruenceSubgroup new: (p := p nextPrime)) numberOfCusps = 2]
]

{ #category : #tests }
ModularTest >> testGammaIndex [
	self assert: ((1 to: 19) collect: [:each| (PrincipalCongruenceSubgroup new: each) index]) =  #(1 6 24 48 120 144 336 384 648 720 1320 1152 2184 2016 2880 3072 4896 3888 6840)
]

{ #category : #tests }
ModularTest >> testIndexOf [
	| G H |
	G := PrincipalCongruenceSubgroup new: 2.
	H := PrincipalCongruenceSubgroup new: 8.
	self assert: (G indexOf: H) equals: 32	"according to GAP manual chap. 2, Gamma(2) has index 12"
]
