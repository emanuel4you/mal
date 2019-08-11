Red [
	Title: "Step 1: read/print"
	File:  %step1_read_print.red
	Tabs:  4
]

#include %types.red
#include %reader.red
#include %printer.red

mal.read: func [
	str [string!]
][
	read-str str
]

mal.eval: func [
	val
][
	val
]

mal.print: func [
	val
	return: [string!]
][
	_pr_str :val true
]

rep: func [
	str     [string!]
	return: [string!]
][
	mal.print mal.eval mal.read str
]

forever [
	either not none? ui: ask "user> " [
		if ui = "" [continue]
		
		print read-str ui
	][
		quit/return 0
	]
]