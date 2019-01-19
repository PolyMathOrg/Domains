"
I am the Gaussian Elimination algorithm.

Given a matrix M with coefficients in a field, my instances perform Gaussian reduction on the matrix to compute linear dependency of the columns, rank, determinant, inverse matrix, etc.
"
Class {
	#name : #GaussianElimination2,
	#superclass : #Object,
	#instVars : [
		'matrix',
		'extension',
		'subreducer',
		'pivots',
		'columns',
		'inverse',
		'determinant'
	],
	#category : #'Mathematics-Etc'
}

{ #category : #examples }
GaussianElimination2 class >> examples [
	" MatrixReducer examples "

'

	vandermonde :=
			''1  1   1
			 3  5	7
			 9  25 49'' asMatrix.
	reducer := MatrixReducer input: vandermonde copy.
	reducer reduce.
	reducer rank.
	reducer det.
	inverse := reducer leftInverse.
	inverse * vandermonde.
	vandermonde scalars.
	vandermonde columnAmbient.

	extReducer := MatrixReducer input: vandermonde copy extension: (1, -1, 17).
	extReducer reduce.
	extReducer extension.
	extReducer subextension.
	extReducer extensionDependentColumns.
	extReducer extensionIndependentColumns.
	extReducer extensionIsDependent.
	extReducer extension.
	coordinates := extReducer extension column: 1.

	columns := vandermonde columnIndexes
		inject: OrderedCollection new
		into: [:result :j | result add: (vandermonde column: j); yourself].
	basis := LinearBasis generators: columns ambient: (vandermonde columnAmbient).
	basis coordinatesOf: (1, -1, 17)

' edit
			
]

{ #category : #'instance creation' }
GaussianElimination2 class >> on: aMatrix [
	^ self on: aMatrix extension: nil
]

{ #category : #'instance creation' }
GaussianElimination2 class >> on: aMatrix extension: extMatrix [
	^ self new setMatrix: aMatrix extension: extMatrix
]

{ #category : #inquiries }
GaussianElimination2 >> dependentColumns [
	| independent |
	independent := self independentColumns.
	^ (1 to: matrix numberOfColumns) reject: [:j | independent includes: j]
]

{ #category : #inquiries }
GaussianElimination2 >> determinant [
	matrix isSquare ifFalse: [^ nil].
	^ self rank = matrix height
		ifTrue: [determinant]
		ifFalse: [matrix scalars zero]
]

{ #category : #accessing }
GaussianElimination2 >> extension [
	^ extension
]

{ #category : #'extension inquiries' }
GaussianElimination2 >> extensionDependentColumns [
	extension isNil ifTrue: [^ nil].
	^ subreducer dependentColumns
]

{ #category : #'extension inquiries' }
GaussianElimination2 >> extensionIndependentColumns [
	extension isNil ifTrue: [^ nil].
	^ subreducer independentColumns
]

{ #category : #'extension inquiries' }
GaussianElimination2 >> extensionIsDependent [
	^ self extensionDependentColumns isEmpty not

]

{ #category : #inquiries }
GaussianElimination2 >> independentColumns [
	^ pivots collect: [:each | each y]
]

{ #category : #computing }
GaussianElimination2 >> killColumn [
	| piv |
	piv := pivots last.
	1 to: piv x - 1 do: [:i | self killRow: i].
	piv x + 1 to: matrix numberOfRows do: [:i | self killRow: i]

]

{ #category : #computing }
GaussianElimination2 >> killRow: i [
	| piv r coef pos  j a |
	piv := pivots last.
	(coef := (matrix at: i @ piv y) negated) isZero ifTrue: [^ self].
	r := piv x.

	"Kill the element"
	matrix at: i @ piv y put: matrix scalars zero.

	"Repeat the computation on the row"
	pos := columns position.
	[columns atEnd]
		whileFalse:
			[j := columns next.
			a := matrix at: i @ j.
			matrix at: i @ j put: (matrix at: r @ j) * coef + a].
	columns position: pos.

	"Do the same on the inverse"
	inverse addRow: r by: coef toRow: i.

	"Do the same on the extension, if any"
	extension notNil ifTrue: [extension addRow: r by: coef toRow: i]
]

{ #category : #inquiries }
GaussianElimination2 >> leftInverse [
	^ inverse
]

{ #category : #computing }
GaussianElimination2 >> nextColumn [
	^ columns atEnd ifFalse: [columns next]
]

{ #category : #computing }
GaussianElimination2 >> nextPivot [
	| col n r k |
	n := matrix height.
	r := self rowNumber + 1.
	[col := self nextColumn ifNil: [^ nil].
	(k := (r to: n)
		detect: [:i| (matrix at: i @ col) isZero not]
		ifNone: []) isNil] whileTrue.
	^ k @ col
]

{ #category : #computing }
GaussianElimination2 >> normalize [
	| piv factor coef index |
	matrix scalars isField ifFalse: [ ^ self ].
	piv := pivots last.
	index := piv x.
	coef := matrix at: index @ piv y.
	coef = self scalars one ifTrue: [^ self].
	factor := coef reciprocal.
	matrix multiplyRow: index by: factor.
	inverse multiplyRow: index by: factor.
	extension notNil ifTrue: [extension multiplyRow: index by: factor].
	determinant := determinant * coef "or multiply by factor?!!!"
]

{ #category : #inquiries }
GaussianElimination2 >> rank [
	^ pivots size
]

{ #category : #processing }
GaussianElimination2 >> reduce [
	| i piv |
	i := 0.
	[(piv := self nextPivot) isNil]
		whileFalse:
			[i := i + 1.
			pivots add: i @ piv y.
			self
				swap: piv x;
				normalize;
				killColumn].
	extension notNil
		ifTrue:
			[subreducer := self class on: self subextension].
"	matrix scalars isField
		ifFalse:
			[1 to: (matrix numberOfRows min: matrix numberOfColumns)
				do: [ :k | determinant := determinant * (matrix at: k at: k) ]]"
]

{ #category : #inquiries }
GaussianElimination2 >> reduced [
	^ matrix
]

{ #category : #inquiries }
GaussianElimination2 >> rowIndexOfPivotAtColumn: j [
	^ (pivots detect: [:one | one y = j]) x
]

{ #category : #computing }
GaussianElimination2 >> rowNumber [
	^ pivots isEmpty ifTrue: [0] ifFalse: [pivots last x]
]

{ #category : #accessing }
GaussianElimination2 >> scalars [
	^ matrix scalars
]

{ #category : #initialization }
GaussianElimination2 >> setMatrix: aMatrix extension: extMatrix [
	aMatrix scalars isField ifFalse: [^ DomainError signal: 'scalars are not a field'].
	matrix := aMatrix.
	extension := (extMatrix isKindOf: Tuple)
		ifTrue: [matrix species columns: {extMatrix}]
		ifFalse: [extMatrix].
	columns := ReadStream on: (1 to: aMatrix numberOfColumns) asArray.
	inverse := aMatrix species identity.
	pivots := OrderedCollection new.
	determinant := aMatrix scalars one.
	self reduce
]

{ #category : #'extension inquiries' }
GaussianElimination2 >> subextension [
	^ extension submatrix: self rowNumber + 1 by: 1 to: matrix height by: extension width
]

{ #category : #'extension inquiries' }
GaussianElimination2 >> subreducer [
	^ subreducer
]

{ #category : #computing }
GaussianElimination2 >> swap: i [
	| r |
	r := self rowNumber.
	i = r ifTrue: [ ^ self ].
	matrix swapRow: i with: r.
	inverse swapRow: i with: r.
	extension notNil ifTrue: [extension swapRow: i with: r].
	determinant := determinant negated
]
