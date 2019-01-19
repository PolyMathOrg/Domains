"
A Loop is a Quasigrop with an identity element.
"
Class {
	#name : #Loop,
	#superclass : #Quasigroup,
	#category : #'Mathematics-Abstract'
}

{ #category : #accessing }
Loop >> identity [
	^ self propertyAt: #identity
]

{ #category : #'accessing-private' }
Loop >> identity: anElement [
	self propertyAt: #identity put: anElement
]
