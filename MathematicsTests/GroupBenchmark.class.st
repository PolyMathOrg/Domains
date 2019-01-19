"
GroupBenchmark new run

testJ1Order	3.95 per second. (spur 32 bits)
testM12Order	86.7 per second.

testJ1Order	2.39 per second.
testM12Order	57.4 per second.

testJ1Order	2.51 per second.
testM12Order	56.9 per second.

"
Class {
	#name : #GroupBenchmark,
	#superclass : #Benchmark,
	#category : #MathematicsTests
}

{ #category : #'as yet unclassified' }
GroupBenchmark >> testJ1Order [
	PermutationGroup J1 size
]

{ #category : #'as yet unclassified' }
GroupBenchmark >> testM12Order [
	PermutationGroup M12 size
]
