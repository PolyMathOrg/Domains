Extension { #name : #Class }

{ #category : #'*mathematics' }
Class >> newSubclass [
	"Answer a new subclass of the receiver. The new subclass will be unnamed and uncategorized, and if no instances exist it can be subject of garbage collection."
	| newMetaclass |
	newMetaclass := Metaclass new.
	newMetaclass
		superclass: self class
		methodDictionary: MethodDictionary new
		format: self class format.
	^ newMetaclass new
		superclass: self
		methodDictionary: MethodDictionary new
		format: self format
]
