"
Permutation groups, i.e. subgroups of the symmetric group Sym(X) of permutations on the elements of a set X (see SymmetricGroup).

The set X is refered to as the 'space' of the group, elements of the X are 'points', while the word 'element' is used for elements of the group itself (permutations). The group acts naturally on the space X by the action p^x |-> p(x).
"
Class {
	#name : #PermutationGroup,
	#superclass : #TransformationGroup,
	#category : #'Mathematics-Groups-Permutations'
}

{ #category : #examples }
PermutationGroup class >> Co3 [
	"Conway group Co3. This group has order 495766656000."
	
	| x y |
	x := #(245 42 112 15 131 7 188 75 132 10 11 187 186 265 22 159 256 43 101 123 134 4 32 209 238 35 45 235 126 5 19 60 66 80 154 251 117 206 71 118 93 87 167 271 221 261 182 155 47 230 172 236 109 191 76 156 73 116 147 23 127 231 38 53 122 210 24 68 86 255 196 139 149 21 111 203 252 72 262 114 214 9 181 174 85 95 2 250 257 243 90 158 170 148 69 105 249 263 16 54 31 115 51 104 125 219 92 46 64 204 8 266 225 34 175 145 161 180 237 241 224 169 269 12 96 129 189 190 29 17 30 82 143 74 168 13 227 217 78 258 220 178 228 146 58 254 273 215 57 106 77 110 50 26 248 260 274 107 99 253 37 25 272 44 52 119 18 201 65 41 233 103 246 200 102 160 198 207 157 40 223 49 267 79 1 136 124 6 61 268 100 70 98 171 121 39 62 211 208 84 135 97 55 152 141 63 142 259 67 33 177 173 14 242 94 113 240 264 150 205 27 183 83 195 216 163 247 133 36 153 197 140 194 120 270 165 166 162 218 138 234 81 91 89 185 212 137 48 202 276 229 151 176 144 192 130 244 232 199 56 108 184 193 239 213 3 222 128 20 28 164 226 59 179 275 88).
	y := #(204 203 33 236 5 172 77 76 47 146 133 224 229 53 84 16 223 228 130 131 252 190 13 263 242 10 32 196 199 65 246 209 40 99 241 198 269 251 75 118 176 271 183 116 197 238 22 29 178 26 174 129 2 153 272 257 41 12 59 20 27 175 106 159 218 259 137 258 261 164 262 189 45 177 260 85 25 15 226 96 24 1 274 148 264 132 48 117 36 60 171 201 101 253 95 120 142 213 165 51 115 44 103 167 243 66 141 108 88 97 276 30 139 222 166 173 231 3 73 239 56 170 82 162 163 207 145 128 52 104 90 216 220 155 74 237 28 4 113 273 230 270 248 180 206 50 250 78 127 150 54 232 217 121 69 156 6 125 210 86 89 46 184 211 265 93 19 138 23 126 43 188 102 244 219 192 256 83 58 144 181 187 91 158 205 235 147 157 114 9 152 57 39 64 143 67 119 161 87 200 111 79 14 123 21 149 122 191 61 194 266 225 31 81 62 160 151 112 215 254 234 72 17 179 105 267 227 18 169 249 109 208 275 68 233 168 55 124 80 240 35 7 212 100 245 98 195 247 107 182 42 185 94 11 255 135 154 221 63 193 134 71 214 8 34 70 202 268 37 110 38 136 140 49 186 92).
	^ PermutationGroup
		new: 276
		generators:
			{x.
			y}
]

{ #category : #examples }
PermutationGroup class >> J1 [
	"Janko group J1. This group has order 175560."
	| x y |
	x := #(262 107 21 213 191 22 133 234 232 151 139 176 202 253 222 16 195 206 68 55 3 6 179 217 216 256 87 70 131 44 105 170 77 104 198 137 243 56 124 223 134 42 174 30 45 51 128 94 250 264 46 183 231 115 20 38 85 233 261 95 235 177 249 91 247 155 67 19 219 28 237 211 84 192 130 251 33 78 260 112 193 156 242 73 57 238 27 143 168 148 64 119 212 48 60 150 199 140 189 180 147 111 159 34 31 162 2 194 166 200 102 80 120 141 54 182 181 225 92 113 254 125 146 39 122 208 221 47 210 75 29 255 7 41 135 175 36 207 11 98 114 240 88 172 185 123 101 90 224 96 10 169 241 190 66 82 214 161 103 236 158 106 239 229 230 109 188 89 152 32 258 144 186 43 136 12 62 245 23 100 117 116 52 205 145 173 228 167 99 154 5 74 81 108 17 196 203 35 97 110 252 13 197 204 184 18 138 126 248 129 72 93 4 157 259 25 24 246 69 227 127 15 40 149 118 226 220 187 164 165 53 9 58 8 61 160 71 86 163 142 153 83 37 244 178 218 65 209 63 49 76 201 14 121 132 26 263 171 215 79 59 1 257 50 266 265).
	y := #(146 132 3 156 242 107 125 245 174 241 264 248 36 116 47 178 170 197 233 121 1 228 48 201 15 136 212 6 175 77 237 30 226 31 129 44 161 232 219 78 139 9 211 13 222 97 25 173 70 153 186 29 203 35 169 140 260 91 199 108 208 206 11 55 103 65 95 73 151 131 41 221 225 18 143 7 32 159 217 93 181 2 258 163 154 182 38 133 117 33 243 191 122 27 205 20 135 98 229 138 61 194 66 104 149 62 28 164 123 17 137 16 69 37 238 128 247 57 167 134 96 80 193 185 76 83 218 14 54 8 49 82 215 189 46 190 183 188 71 230 231 239 202 224 158 21 119 214 184 250 113 72 200 213 22 166 102 220 40 92 114 257 177 60 179 4 147 168 64 110 171 148 23 42 52 195 84 112 246 19 252 196 111 105 265 209 24 100 120 26 160 39 109 157 266 86 74 204 227 50 187 75 216 207 67 106 198 101 51 141 251 94 85 172 88 53 254 261 192 145 152 240 262 249 68 90 59 155 263 56 210 87 180 12 115 142 34 235 236 45 244 253 58 10 130 165 89 234 144 259 43 81 5 79 223 162 256 126 150 118 127 255 99 63 124 176).
	^ PermutationGroup new: 266 generators: {x. y}
]

{ #category : #examples }
PermutationGroup class >> M11 [
	"The Mathieu group on 11 points. With order 7920, this is the smallest of the 26 sporadic simple groups."

	"ALTERNATIVELY: #((1 2 3 4 5 6 7 8 9 10 11)), #((3 7 11 8) (4 10 5 6))."

	^ self
		new: 11
		generators:
			{#(#(1 10) #(2 8) #(3 11) #(5 7)).
			#(#(1 4 7 6) #(2 11 10 9))}
]

{ #category : #examples }
PermutationGroup class >> M12 [
"The Mathieu group on 12 points, the second smallest of the 26 sporadic simple groups, with order 95040."
	^ self
		new: 12
		generators:
			{#(#(1 2 3 4 5 6 7 8 9 10 11)).
			#(#(3 7 11 8) #(4 10 5 6)).
			#(#(1 12) #(2 11) #(3 6) #(4 8) #(5 9) #(7 10))}
]

{ #category : #examples }
PermutationGroup class >> McL [
	"McLaughlin group. This group has order 898128000."
	| x y |
	x := #(191 182 3 81 55 60 7 66 272 177 192 163 13 242 133 107 17 267 108 218 198 185 211 82 204 195 132 253 207 59 179 154 264 152 92 189 217 197 85 156 41 184 102 50 216 99 181 48 199 44 111 52 158 236 5 210 57 103 30 6 263 62 119 138 127 8 105 137 69 125 144 219 261 74 175 76 269 237 268 80 4 24 232 256 39 104 95 88 234 233 140 35 93 149 87 96 173 160 46 112 123 43 58 86 67 221 16 19 131 176 51 100 262 257 201 116 260 238 63 275 214 225 101 246 70 170 65 128 141 130 109 27 15 196 167 136 68 64 139 91 129 235 224 71 205 249 147 226 94 243 151 34 193 32 228 40 157 53 159 98 231 162 12 215 180 166 135 222 270 126 241 259 97 212 75 110 10 188 31 165 47 2 266 42 22 203 187 178 36 250 1 11 153 194 26 134 38 21 49 200 115 247 186 25 145 206 29 255 251 56 23 174 252 121 164 45 37 20 72 220 106 168 271 143 122 148 274 155 229 240 161 83 90 89 142 54 78 118 254 230 171 14 150 244 258 124 202 248 146 190 209 213 28 239 208 84 114 245 172 117 73 113 61 33 273 183 18 79 77 169 223 9 265 227 120).
	y := #(24 28 67 168 118 274 98 209 266 271 247 13 71 7 218 170 100 26 223 128 264 116 179 204 40 198 64 272 56 132 255 148 61 241 89 239 54 20 126 177 35 248 139 172 234 214 140 55 134 213 22 107 101 99 113 135 221 57 252 84 163 47 94 162 171 192 142 195 167 145 10 152 14 206 73 91 17 2 245 203 63 205 38 188 191 215 115 52 82 227 180 155 169 173 181 265 250 75 249 4 51 207 156 70 267 273 262 256 97 66 117 76 220 49 158 53 105 19 44 144 269 127 141 185 119 189 102 159 58 50 225 42 164 32 68 230 79 121 193 268 259 31 106 96 9 30 184 114 143 103 150 197 125 186 1 160 147 178 83 151 120 21 90 196 78 59 190 77 110 182 16 153 210 62 200 37 85 240 244 238 34 65 36 108 18 219 251 208 136 46 25 93 8 236 29 15 217 124 111 123 60 130 23 92 41 154 246 201 43 81 5 45 224 69 231 166 254 133 74 235 261 232 211 202 86 88 33 237 228 39 131 212 95 222 48 187 253 112 275 87 233 149 263 80 6 122 138 146 176 243 258 260 270 72 3 157 183 194 175 216 129 226 109 27 161 104 199 174 11 229 12 165 242 137 257).
	^ PermutationGroup new: 275 generators: {x. y}
]

{ #category : #examples }
PermutationGroup class >> cyclic: n [
	"Answer the cyclic group of order n as a permutation group."
	^ 'self new: n generators: {{(1 to: n)}} :: name: ''C'', n printString sub'
]

{ #category : #examples }
PermutationGroup class >> dihedral: order [
	"Answer the Dihedral group of order n as a permutation group."
	| n G s r |
	order even ifFalse: [self error: 'order should be even'].
	n := order // 2.
	G := SymmetricGroup new: n.
	r := G ! {(1 to: n)}.
	s := G ! [:i| n - i + 1].
	^ (G span: {s. r}) name: 'Dih', order printString sub
]

{ #category : #examples }
PermutationGroup class >> hessian [
	"The Hessian group, a finite group of order 216 introduced by Jordan and named after Otto Hesse."
	^ self new: 9 generators: {#((1 2 4) (5 6 8) (3 9 7)). #((4 5 6) (7 9 8))}
]

{ #category : #examples }
PermutationGroup class >> klein [
	"The Klein four-group (or Vierergruppe) as a permutation group."
	^ self new: 4 generators: {#(2 1 4 3). #(3 4 1 2) ". #(4 3 2 1)"}
]

{ #category : #'instance creation' }
PermutationGroup class >> new: n generators: aCollection [
	^ (SymmetricGroup new: n) span: aCollection
]

{ #category : #'instance creation' }
PermutationGroup class >> on: aCollection generators: anotherCollection [
	^ (SymmetricGroup on: aCollection) span: anotherCollection
]

{ #category : #comparing }
PermutationGroup >> = anObject [
	self == anObject ifTrue: [^ true].
	(anObject isKindOf: self species)
		ifFalse: [^ super = anObject].
	self generators ifNotNil: [:g1| anObject generators ifNotNil: [:g2| g1 asSet = g2 asSet ifTrue: [^ true]]].
	self size = anObject size ifFalse: [^ false].
	anObject generators ifNotNil: [:generators| ^ self containsAllOf: generators].
	self generators ifNotNil: [:generators| ^ anObject containsAllOf: generators].
	^ super = anObject
]

{ #category : #accessing }
PermutationGroup >> action [
	"Answer the natural action that sends (s, x) to s(x)."
	
	^ GroupAction
		from: self , self space
		to: self space
		evaluatingWithArguments: [ :s :x | s value: x ]
]

{ #category : #converting }
PermutationGroup >> asLinearGroupOver: aRing [
	"Return a linear group over aRing isomorphic to the receiver.
	Assume the space of the receiver is an interval (1 to: n)."
	
	| n V |
	n := self degree.
	V := aRing raisedTo: n.
	^ LinearGroup
		on: V
		generators:
			(self generators
				collect: [ :g | 
					V
						to: V
						evaluating: [ :x | x withIndexCollect: [ :xi :i | x at: (g value: i) ] ] ])
]

{ #category : #converting }
PermutationGroup >> asMatrixGroup [
	"Return a matrix group isomorphic to the receiver.
	Assume the space of the receiver is an interval (1 to: n)."
	| n generators |
	n := self degree.
	generators := self generators collect: [:g| QQ matrix: n@n evaluating: [:i :j| (g at: i) = j ifTrue: [1] ifFalse: [0]]].
	^ MatrixGroup generators: generators
]

{ #category : #private }
PermutationGroup >> computeSize [
	"Schreier-Sims algorithm."
	| G answer |
	G := self.
	answer := 1.
	self space do: [:b| | tree |
		G isTrivial ifTrue: [^ answer].
		tree := SchreierTree root: b generators: G generators action: G action.
		answer := answer * tree orbit size.
		G := tree stabilizer].
	self error: 'what?'.
	^ answer
]

{ #category : #copying }
PermutationGroup >> copyEmpty [
	^ PermutationGroup new ambient: self ambient
]

{ #category : #accessing }
PermutationGroup >> degree [
	^ self space size
]

{ #category : #private }
PermutationGroup >> generators: aCollection [
	super generators: (aCollection asSet reject: [:each| each isIdentity])
]

{ #category : #accessing }
PermutationGroup >> identity [
	self ambient == self ifTrue: [^ self halt].
	^ self ambient identity
]

{ #category : #testing }
PermutationGroup >> includes: aPermutation [
	^ (self ambient includes: aPermutation) and: [self contains: aPermutation]
]

{ #category : #testing }
PermutationGroup >> isStandard [
	"Answer true if the domain of the receiver is an interval [1..n]."
	^ self ambient isStandard
]

{ #category : #testing }
PermutationGroup >> isSubgroupOfAn [
	"Monte Carlo test."
	| random |
	self flag: #fix.
	self isTransitive ifFalse: [^ false].
	random := self random.
	20 timesRepeat:
		[random next isPurple ifTrue: [^ true]].
	^ false
]

{ #category : #accessing }
PermutationGroup >> polynomialActionOn: aPolynomialRing [
	"Answer the action that permutes the indeterminates."
	^ GroupAction from: (self, aPolynomialRing) to: aPolynomialRing evaluatingWithArguments: [:s :f| f permutedBy: s]
]

{ #category : #accessing }
PermutationGroup >> polynomialActionOver: aRing [
	"Answer the action that permutes the indeterminates on a polynomial ring."
	| R |
	R := aRing polynomialsIn: self degree.
	^ GroupAction from: (self, R) to: R evaluatingWithArguments: [:s :f| f permutedBy: s]
]

{ #category : #accessing }
PermutationGroup >> size [
	self propertyAt: #elements ifPresent: [:aCollection| ^ aCollection size].
	^ self propertyAt: #size ifAbsentPut: [self computeSize]
]

{ #category : #accessing }
PermutationGroup >> space [
	^ self ambient space
]

{ #category : #operations }
PermutationGroup >> span: aCollection [
	^ self ambient span: aCollection
]

{ #category : #private }
PermutationGroup >> species [
	^ PermutationGroup
]
