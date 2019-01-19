Class {
	#name : #Maxel,
	#superclass : #Object,
	#instVars : [
		'pixels'
	],
	#category : #'Mathematics-Etc'
}

{ #category : #'as yet unclassified' }
Maxel class >> pixels: aCollection [
	^ self new pixels: aCollection
]

{ #category : #'as yet unclassified' }
Maxel >> * anInteger [
	^ self notYetImplemented
]

{ #category : #'as yet unclassified' }
Maxel >> + aMaxel [
	^ self class pixels: (pixels ñ aMaxel pixels)
]

{ #category : #'as yet unclassified' }
Maxel >> dot: aMaxel [ "ï "
	^ self notYetImplemented
]

{ #category : #'as yet unclassified' }
Maxel >> extent [
	^ Pixel row: (pixels max: [:each| each row]) column: (pixels max: [:each| each column])
]

{ #category : #'as yet unclassified' }
Maxel >> isDiagonal [
	^ pixels allSatisfy: [:each| each isDiagonal]
]

{ #category : #'as yet unclassified' }
Maxel >> isEmpty [
	^ self size = 0
]

{ #category : #'as yet unclassified' }
Maxel >> isSymmetric [
	^ self transposed = self
]

{ #category : #'as yet unclassified' }
Maxel >> minus: aMaxel [ "ñ"
	^ self notYetImplemented
]

{ #category : #'as yet unclassified' }
Maxel >> size [
	^ pixels size
]

{ #category : #'as yet unclassified' }
Maxel >> trasposed [
	^ self class pixels: (pixels collect: [:each| each transposed])
]
