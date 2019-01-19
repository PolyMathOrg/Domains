"
Affine plane algebraic curves, i.e. schemes of dimension 1 over an affine plane.
"
Class {
	#name : #AffinePlaneCurve,
	#superclass : #AffineHypersurface,
	#category : #'Mathematics-Schemes-Affine'
}

{ #category : #examples }
AffinePlaneCurve class >> descartesFolium [
	"This is the 'Descartes folium'."
	^ 'AffinePlaneCurve polynomial: (QQ polynomialsIn: #(x y)) ! [:x :y| x^3 + (y^3) - (3*x*y)]'
]

{ #category : #examples }
AffinePlaneCurve class >> iminus [
	^ 'AffinePlaneCurve polynomial: (QQ polynomialsIn: #(x y)) ! [:x :y| x^3 + (y^3) - x - (2*y) - 1]'
]

{ #category : #morphic }
AffinePlaneCurve >> plot [
	^ self plot: (-5@-5 extent: 10@10)
]

{ #category : #morphic }
AffinePlaneCurve >> plot: aRectangle [
	^ ImplicitFunctionPlotMorph new function: self polynomial; box: aRectangle
]

{ #category : #operations }
AffinePlaneCurve >> tangentsAt: aTuple [
	| f r derivatives |
	f := (self - aTuple) polynomial.
	r := f order. "multiplicity at the point"
	derivatives := (0 to: r) collect: [:k| (f derivative: k in: 1) derivative: r-k in: 2].
	^ (self ambient subscheme: ((0 to: r) sum: [:k| (r choose: k) * (derivatives at: k+1) * (f parent x: 1 to: k) * (f parent x: 2 to: r-k)])) + aTuple
]
