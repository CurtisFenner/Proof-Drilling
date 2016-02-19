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

////////////////////////////////////////////////////////////////////////////////

// Define Universal Instantiation
axioms.push({
	name: "Universal Elimination",
	args: ["@for all x, b(x)"],
	test: function(exp, args) {
		var forall = Match(Parse("all @x @predicate"), args[0], Same);
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

axioms.push({
	name: "Universal Introduction",
	args: ["@predicate"],
	opens: true, // Creates a subproof and assumption.
	test: function(exp, args, history) {
		var forall = Match(Parse("all @x @predicate"), exp, Same);
		if (!forall) {
			throw "Must conclude a for-all";
		}
		var pattern = Substitute(forall.x, "x", forall.predicate);
		var f = Match(pattern, args[0], Same);
		if (!f || !f.x) {
			throw "Not of the right form";
		}
		if (!(f.x instanceof Atom)) {
			throw "Instance must be a constant; '" + f.x + "' is not a constant";
		}
		for (var i = 0; i < history.length; i++) {
			var d = {};
			d[f.x.name] = true;
			if (history[i].assumption && history[i].invalid(d) ) {
				throw "'" + f.x + "' must not appear in any assumptions";
			}
		}
	}
});


axioms.push({
	name: "Modus Ponens",
	args: ["@implication", "@base"],
	test: function(exp, args) {
		var implication = Match(Parse("@x -> @y"), args[0], Same);
		if (!implication) {
			throw "'implication' must be an implication";
		}
		if (!Same(implication.x, args[1])) {
			throw "'" + implication.x + "' and '" + args[1] + "' don't match, so modus ponens can't be applied";
		}
		if (!Same(implication.y, exp)) {
			throw "Expected conclusion to be '" + implication.y + "' but got '" + exp + "'";
		}
	}
});


axioms.push({
	name: "Existential Introduction",
	args: ["@statement"],
	test: function(exp, args) {
		var exists = Match(Parse("exist @x, @predicate"), exp, Same);
		if (!exists) {
			throw "Must conclude a there-exists";
		}
		var pattern = Substitute(exists.x, "x", exists.predicate);
		var match = Match(pattern, args[0], Same);
		if (!match) {
			throw "'" + exists.predicate + "' does not match '" + args[0] + "'";
		}
	}
});

axioms.push({
	name: "Conjunction",
	args: ["@a", "@b"],
	test: function(exp, args) {
		var and = Match(Parse("@a and @b"), exp, Same);
		if (!and) {
			throw "Expected an 'and'";
		}
		if (Same(and.a, args[0]) && Same(and.b, args[1])) {
			return;
		}
		throw "Does not match.";
	},
});

// Existential Elimination.
// Opens a sub-proof that allows conclusion of "there exists"
axioms.push({
	
});

////////////////////////////////////////////////////////////////////////////////

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

/*

// Define Existential Instantiation
axioms.push({
	name: "Existential Instantiation",
	args: ["@there exists"],
	test: function(exp, args, history) {
		var exists = Match(Parse("exist @x @predicate"), args[0], Same);
		if (!exists) {
			throw "Statement is not a there-exists";
		}
		// Test whether or not this is a real instantiation:
		var pattern = Substitute(exists.x, "x", exists.predicate);
		var f = Match(pattern, exp, Same);
		if (f && f.x) {
			// Check that it was instantiated with a name:
			if (f.x instanceof Atom) {
				// Check that this name is new:
				console.log(history);
				for (var i = 0; i < history.length; i++) {
					console.log(history[i].latex(), "???", f.x.name);
					if (history[i].uses(f.x.name)) {
						throw "You cannot instantiate with a name that has been used before.";
					}
				}
				// This is a valid instantiation
				return true;
			} else {
				throw "You can only instantiate a there-exists statement with a variable, not an expression like " + f.x;
			}
		} else {
			throw "Not a valid instantiation of " + exists.predicate;
		}
	},
})


// Define Universal Instantiation
axioms.push({
	name: "universal instantiation := b(y)",
	args: ["@for all x, b(x)"],
	test: function(exp, args) {
		var forall = Match(Parse("all @x @predicate"), args[0], Same);
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
		var t = Match( Parse("@u + @v = @v + @u"), exp, Same );
		if (!t) {
			throw "Not of the form u + v = v + u";
		}
	}
});

// Define transitivity of equality
axioms.push({
	name: "transitivity of '=' := x = z",
	args: ["@x = y", "@y = z"],
	test: function(exp, args) {
		var M = Match(
			[Parse("@x = @y"), Parse("@y = @z"), Parse("@x = @z")],
			[args[0], args[1], exp],
			Same);
		if (!M) {
			throw "Does not fit pattern x=y, y=z => x=z";
		}
	}
});

// Define symmetry of equality
axioms.push({
	name: "symmetry of '=' := y = x",
	args: ["@x = y"],
	test: function(exp, args) {
		if (!Match([Parse("@x = @y"), Parse("@y = @x")], [exp, args[0]], Same)) {
			throw "Does not fit pattern x = y"
		}
	}
});


///////////////////////////////////////////////////////////////////////////////

// Natural proof axioms:

axioms.push({
	name: "Suppose",
	args: [],
	test: function(exp, args) {
		return true; // Everything is okay.
	},
	opens: true,
});


axioms.push({
	name: "Conclude",
	args: [],
	test: function(exp, args) {
		// TODO: Check appropriately
	},
	closes: true,
});

*/

///////////////////////////////////////////////////////////////////////////////


// Hypothesis (givens)
var hypotheses = [];
(function(){
//hypotheses.push( ("(all x)(a + x = x)") );
//hypotheses.push( ("(all x)(b + x = x)") );

// (1)
//hypotheses.push( ("all x, F(x)") );

// (2)
//hypotheses.push( ("all x, all y, H(x, y)") );
//hypotheses.push( ("H(a, b) -> K(g)"));

// (3)
hypotheses = [
	"all x, A(x)",
	"(exist y, A(y)) -> (all w, B(w))"
];

// (4)
hypotheses = [
	"all y, H(y,y)",
	"exist z, B(z)",
];

})();
// Add hypotheses lines to proof:
hypotheses = hypotheses.map(Parse);
var lines = [];
for (var i = 0; i < hypotheses.length; i++) {
	lines[i] = { expression: hypotheses[i], text: "x", reason: "hypothesis", args: ["", "", ""] };
}

// Add empty lines to proof:
for (var i = 0; i < 13; i++) {
	lines.push( {expression: new Atom("x"), text: "", reason: "", args: ["", "", ""] });
}
