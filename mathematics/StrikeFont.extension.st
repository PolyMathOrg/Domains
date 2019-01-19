Extension { #name : #StrikeFont }

{ #category : #'*mathematics-character shapes' }
StrikeFont class >> buildMathFont [
	"
	StrikeFont buildMathFont
	"
	#(5 6 7 8 9 10 11 12 13 14 17 22) do: [:pointSize| self buildMathFont: pointSize]
]

{ #category : #'*mathematics-character shapes' }
StrikeFont class >> buildMathFont: pointSize [
	| font normal larger muchLarger |
	font := AbstractFont familyName: 'DejaVu Sans Mono' pointSize: pointSize.
	font characterToGlyphMap at: 96 put: 28. "use left arrow instead of underscore"
	normal := AbstractFont familyName: 'DejaVu' pointSize: pointSize.
"	#(1 0) detect: [:one| (slightlyLarger := (AbstractFont familyName: 'DejaVu' pointSize: pointSize+one)) notNil]."
	#(2 1 3 0) detect: [:one| (larger := (AbstractFont familyName: 'DejaVu' pointSize: pointSize+one)) notNil].
	#(4 3 2 1 0) detect: [:one| (muchLarger := (AbstractFont familyName: 'DejaVu' pointSize: pointSize+one)) notNil].
	"replace some math glyphs with their normal counterpart, because the monospaced glyphs are far too small (and some are missing):"
	'ÄÅÇÉÖÜáàâäãåçéèêëíìîïñóòôöõúùû' do: [:each|
		font takeAllGlyphFor: each from: each in: normal].
"	'ÄÉÑÖÜâäãåçéè' do: [:each|
		font takeAllGlyphFor: each from: each in: slightlyLarger].
"	'Äêëíìîïñóòôöõú' do: [:each|
		font takeAllGlyphFor: each from: each in: larger].
	'Ä' do: [:each|
		font takeAllGlyphFor: each from: each in: muchLarger].
	"make arrows bigger"
	'' do: [:each|
		font takeAllGlyphFor: each from: each in: larger]
]

{ #category : #'*mathematics-character shapes' }
StrikeFont class >> installMathFonts [
"
StrikeFont installMathFonts
"
	| family codeFamily |
	StrikeFont install: 'DejaVu'.
	StrikeFont install: 'DejaVu Sans Mono'.
	StrikeFont buildMathFont.
	Character initialize.
	family := 'DejaVu Sans Mono'.
	codeFamily := 'DejaVu Sans Mono'.
	Preferences setDefaultFonts: {
		{#setSystemFontTo:. family. 10}.
		{#setListFontTo:. family. 10}.
		{#setMenuFontTo:. family. 9}.
		{#setWindowTitleFontTo:. family. 10}.
		{#setCodeFontTo:. codeFamily. 10}.
		{#setButtonFontTo:. family. 9}}.
	DisplayScreen runningWorld ifNotNil: [ :world | world fontPreferenceChanged ].

]
