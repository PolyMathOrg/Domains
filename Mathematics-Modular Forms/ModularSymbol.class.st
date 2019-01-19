Class {
	#name : #ModularSymbol,
	#superclass : #Object,
	#instVars : [
		'alpha',
		'beta'
	],
	#category : #'Mathematics-Modular Forms'
}

{ #category : #'as yet unclassified' }
ModularSymbol >> apply: aMorphism [
	^ self class alpha: (aMorphism value: alpha) beta: (aMorphism value: beta)
]
