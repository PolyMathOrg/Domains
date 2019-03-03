"
self new run

test1000Factorial	5,620 per second. (spur 32 bits)

test1000Factorial	1,250 per second.

"
Class {
	#name : #IntegersBenchmark,
	#superclass : #Benchmark,
	#category : #'Mathematics-Tests'
}

{ #category : #'as yet unclassified' }
IntegersBenchmark >> test1000Factorial [
	1000 factorial
]
