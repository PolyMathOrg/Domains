Class {
	#name : #SyzygyModule,
	#superclass : #FreeModule,
	#instVars : [
		'polynomials'
	],
	#category : #'Mathematics-Etc'
}

{ #category : #'as yet unclassified' }
SyzygyModule >> printOn: aStream [
	aStream nextPutAll: 'Syz('.
	polynomials do: [:each| aStream print: each] separatedBy: [aStream nextPutAll: ', '].
	aStream nextPut: $)
]
