"
Farey symbols give information about finite index subgroups of the modular group (such as index, generators, etc) and about the associated modular curve (such as genus and rank of the fundamental group).

References
	R. S. Kulkarni, ""An arithmetic-geometric method in the study of the subgroups of the modular group"", American Journal of Mathematics 113 (1991), no. 6, 1053-1133.
	Chris A. Kurth, Ling Long, ""Computations with finite index subgroups of PSL(2,Z) using Farey symbols"".
	John Voight, ""Computational methods for modular and Shimura curves"", lecture videos in youtube.
"
Class {
	#name : #FareySymbol,
	#superclass : #Object,
	#instVars : [
		'group',
		'fractions',
		'pairings'
	],
	#category : #'Mathematics-Modular Group'
}

{ #category : #'as yet unclassified' }
FareySymbol >> cusps [
	^ self notYetImplemented
]

{ #category : #'as yet unclassified' }
FareySymbol >> denominatorAt: i [
	i == 0 ifTrue: [^ 0].
	i == (fractions size + 1) ifTrue: [^ 0].
	^ (fractions at: i) denominator
]

{ #category : #'as yet unclassified' }
FareySymbol >> e2 [
	"Answer the number of inequivalent order-2 elliptic points."
	^ pairings count: [:each| each == #even]
]

{ #category : #'as yet unclassified' }
FareySymbol >> e3 [
	"Answer the number of inequivalent order-3 elliptic points."
	^ pairings count: [:each| each == #odd]
]

{ #category : #'as yet unclassified' }
FareySymbol >> example [
	group := PrincipalCongruenceSubgroup new: 2.
	fractions := {0. 1. 2}.
	pairings := {1. 2. 2. 1}
]

{ #category : #'as yet unclassified' }
FareySymbol >> generators [
	^ (1 to: fractions size) collect: [:i| self pairingMapAt: i]
]

{ #category : #'as yet unclassified' }
FareySymbol >> genus [
	^ self rank - self numberOfCusps / 2
]

{ #category : #'as yet unclassified' }
FareySymbol >> index [
	"Answer the index of the group of the receiver as subgroup of the modular group."
	^ (self size - 1) * 3 + self e3
]

{ #category : #'as yet unclassified' }
FareySymbol >> numeratorAt: i [
	i == 0 ifTrue: [^ -1].
	i == (fractions size + 1) ifTrue: [^ 1].
	^ (fractions at: i) numerator
]

{ #category : #'as yet unclassified' }
FareySymbol >> pairingAt: i [
	"Answer the pairing between i-1 and i. Each pairing is either a positive integer (a free pairing), #even or #odd."
	^ pairings at: i
]

{ #category : #'as yet unclassified' }
FareySymbol >> pairingMapAt: i [
	| a b a1 b1 k ak bk ak1 bk1 |
	a := self numeratorAt: i-1.
	b := self denominatorAt: i-1.
	a1 := self numeratorAt: i.
	b1 := self denominatorAt: i.
	k := self pairingAt: i.
	k == #even ifTrue: [^ ModularMap a: a1*b1 + (a*b) b: a*a negated - (a1*a1) c: b*b + (b1*b1) d: a1*b1 negated - (a*b)].
	k == #odd ifTrue: [^ ModularMap a: a1*b1 + (a*b1) + (a*b) b: a*a negated - (a*a1) - (a1*a1) c: b*b + (b*b1) + (b1*b1) d: a1*b1 negated - (a1*b) - (a*b)].
	ak := self numeratorAt: k.
	bk := self denominatorAt: k.
	ak1 := self numeratorAt: k+1.
	bk1 := self denominatorAt: k+1.
	^ ModularMap a: ak1*b1 + (ak*b) b: ak*ak negated - (ak1*a1) c: bk*b + (bk1*b1) d: a1*bk1 negated - (a*bk)
]

{ #category : #'as yet unclassified' }
FareySymbol >> printOn: aStream [
	| n |
	n := self size.
	aStream print: Infinity negative.
	1 to: n do: [:i|
		aStream nextPutAll: ' (', (self pairingAt: i) asString, ') '; print: (self numeratorAt: i); nextPut: $/; print: (self denominatorAt: i)].
	aStream nextPutAll: ' (', (self pairingAt: n+1) asString, ') '; print: Infinity positive
]

{ #category : #'as yet unclassified' }
FareySymbol >> r [
	"Answer the rank of the fundamental group of the uncompactified modular curve G\H, where G denotes de group of the receiver and H is the upper half plane."
	^ pairings count: [:each| each isInteger]
]

{ #category : #'as yet unclassified' }
FareySymbol >> size [
	^ fractions size
]
