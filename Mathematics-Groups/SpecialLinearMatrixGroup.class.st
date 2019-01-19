"
SL(n,R), the Special Linear Group of the R-module of n-tuples. This is the group of matrices of determinant 1.
"
Class {
	#name : #SpecialLinearMatrixGroup,
	#superclass : #MatrixGroup,
	#category : #'Mathematics-Groups-Matrix'
}

{ #category : #operations }
SpecialLinearMatrixGroup >> asAlgebraicVariety [
	| n P det |
	n := self degree.
	P := self scalars polynomialsIn: n squared.
	det := (P matrix: n@n evaluating: [:i :j| P x: i - 1 * n + j]) determinant.
	^ 'P * (det - self scalars one) :: variety'
]

{ #category : #operations }
SpecialLinearMatrixGroup >> center [
	^ SpecialScalarMatrixGroup new: self degree over: self scalars
]

{ #category : #testing }
SpecialLinearMatrixGroup >> contains: aMatrix [
	"Answer true if the receiver contains the given element of its ambient."
	^ aMatrix determinant = self scalars one
]

{ #category : #printing }
SpecialLinearMatrixGroup >> shortName [
	^ 'SL'
]
