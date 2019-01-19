"
A chain map between two chain complexes defined by differentials d(k):C(k)->C(k-1) and d'(k):C'(k)->C'(k-1) is a sequence of homomorphisms f(k):C(k)->C'(k) that commutes with the differentials in the two complexes: d'(k) o f(k) = f(k-1) o d(k). They send cycles to cycles and boundaries to boundaries, and this descends to a map in homology f(k)* : H(k) -> H'(k).

Chain maps are morphisms in the category of chain complexes. See ChainComplex.
"
Class {
	#name : #ChainMap,
	#superclass : #Function,
	#category : #'Mathematics-Homology'
}
