Class {
	#name : #SpringNodeMorph,
	#superclass : #GraphNodeMorph,
	#category : #'Mathematics-Graphs-Morphic'
}

{ #category : #'event handling testing' }
SpringNodeMorph >> aboutToBeGrabbedBy: aHand [ 
	super aboutToBeGrabbedBy: aHand.
	(owner isKindOf: GraphMorph) ifTrue: ["owner focusOn: node; stopStepping"]
]

{ #category : #moving }
SpringNodeMorph >> approachPoint: aPoint [
	| dxNew x1 x2 diff |
	dxNew := dx - dx. "0@0."
	x1 := x.
	x2 := aPoint.
	x1 = x2 ifTrue: [^ self].
	diff := x1 - x2.
	dxNew := dxNew + (diff / diff norm2).
	dxNew isZero ifFalse: [dx := dx + (dxNew / dxNew norm * 2)]
]

{ #category : #'event handling testing' }
SpringNodeMorph >> handlesMouseDown: evt [ 
	evt shiftPressed
		ifFalse: [^ super handlesMouseDown: evt]
		ifTrue: [^ true]
]

{ #category : #private }
SpringNodeMorph >> nearbyNodesDo: aBlock [
	| count |
	count := 0.
	node markDo: [:each |
		count := count + 1.
		count > 40 ifTrue: [^ self].
		aBlock value: (owner nodeAt: each)]
]

{ #category : #moving }
SpringNodeMorph >> separateFromAllNodes [
	| dxNew x1 x2 |
	(owner isKindOf: SpringGraphMorph) ifFalse: [^ self].
	dxNew := dx - dx. "0@0"
	x1 := x.
	owner nodesDo: [:each|
		x2 := each x + each dx.
		self == each
			ifFalse:
				[x1 = x2
					ifTrue: [dxNew := dxNew + self perturbation]
					ifFalse:
						[| diff |
						diff := x1 - x2.
						dxNew := dxNew + (diff / diff norm2)]]].
	dxNew isZero ifFalse: [dx := dx + (dxNew / dxNew norm * 2)]
]

{ #category : #'event handling testing' }
SpringNodeMorph >> wantsToBeDroppedInto: aMorph [
	^ aMorph isKindOf: SpringGraphMorph
]
