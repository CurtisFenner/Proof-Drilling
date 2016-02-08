// Curtis Fenner
// cwfenner@umich.edu
// 4 February 2016
"use strict";

// Compare two expressions
function Same(a, b) {
	// TODO: Allow normalization for associativity and commutativity
	return a.compare(b, Same);
}

///////////////////////////////////////////////////////////////////////////////

// List of Axioms -- options in the "Justification" dropdown.
var axioms = [];

// name: Name of axiom (listed in dropdown)
// args: List of arguments for axiom. Names are listed above inputs.
//       The first character is either
//       @ signifying the input is a statement number
//       $ signifying the input is an expression
// test: A function taking (student statement, [argument expressions])
//       It throws in the event the student statement does not follow
//       and otherwise returns anything truthy
// fun:  A function given all of the arguments to the justification
//       returning what it expects the student answer to be.
//       The table reports whether or not the result is different from
//       what the student entered.


// Define Universal Instantiation
axioms.push({
	name: "universal instantiation := b(y)",
	args: ["@for all x, b(x)"],
	test: function(exp, args) {
		var forall = Match( Bin("all", "x", "predicate") , args[0], Same);
		if (!forall) {
			throw "Statement is not a for-all";
		}
		var pattern = Substitute(forall.x, "x", forall.predicate);
		var f = Match( pattern, exp, Same );
		if (f && f.x) {
			return true;
		} else {
			throw "Not a valid instantiation of " + forall.predicate;
		}
	}
});

// Define Commutativity of Addition
// Allows
// x + y = y + x
// style-statements
axioms.push({
	name: "commutativity of '+' := u + v = v + u",
	args: [],
	test: function(exp) {
		var t = Match( Bin("=", Bin("+", "u", "v"), Bin("+", "v", "u") ), exp, Same );
		if (!t) {
			throw "Not of the form u + v = v + u";
		}
	},
	fun: function(args) {
		return new Bin("=", new Bin("+", args[0], args[1]), new Bin("+", args[1], args[0]));
	}
});

// Define transitivity of equality
axioms.push({
	name: "transitivity of '=' := x = z",
	args: ["@x = y", "@y = z"],
	fun: function(args) {
		var fail = false;

		if (args[0].args.length !== 2 || args[1].args.length !== 2) {
			fail = true;
		}
		else if (args[0].operator !== "=" || args[1].operator !== "=") {
			fail = true;
		}
		else if (!Same(args[0].args[1], args[1].args[0])) {
			fail = true;
		}
		if (fail) {
			throw "Does not fit pattern x=y, y=z";
		}
		return new Bin("=", args[0].args[0], args[1].args[1]);
	}
});

// Define symmetry of equality
axioms.push({
	name: "symmetry of '=' := y = x",
	args: ["@x = y"],
	fun: function(args) {
		var t = Match( new Bin("=", "x", "y"), args[0], Same );
		if (!t) {
			throw "Does not fit pattern a = b"
		}
		return new Bin("=", t.y, t.x);
	}
});

///////////////////////////////////////////////////////////////////////////////


// Hypothesis (givens)
var hypotheses = [];
hypotheses.push( Parse("all x a + x = x") );
hypotheses.push( Parse("all x b + x = x") );

// Add hypotheses lines to proof:
var lines = [];
for (var i = 0; i < hypotheses.length; i++) {
	lines[i] = { expression: hypotheses[i], text: "x", reason: "hypothesis", args: ["", "", ""] };
}

// Add empty lines to proof:
for (var i = 0; i < 13; i++) {
	lines.push( {expression: new Atom("x"), text: "", reason: "", args: ["", "", ""] });
}
