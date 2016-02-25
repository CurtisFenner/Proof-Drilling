// Curtis Fenner
// cwfenner@umich.edu
// 4 February 2016
"use strict";

var implicitSort = {};
var implicitFlat = {};
// Compare two expressions
function Same(a, b) {
	// TODO: Allow normalization for associativity and commutativity
	var parameter = {sort: implicitSort, flat: implicitFlat};
	return a.normalize(parameter).compare(b.normalize(parameter), Same);
}

function UseEqualityProperty(axioms, op, name) {
	axioms.push({
		name: name + " property of equality",
		args: ["@equality"],
		test: function(exp, args) {
			var eq = Match(Parse("@a = @b"), args[0], Same);
			if (!eq) {
				throw "Expression " + args[0] + " is not of the form a = b";
			}
			var left = Bin(op, eq.a, "x");
			var right = Bin(op, eq.b, "x");
			var pattern = Bin(op, left, right); ""
			var px = Parse("@x " + op + " @a = @x " + op + " @b");
			var py = Parse("@a " + op + " @x = @b " + op + " @x");
			if (Match(px, exp, Same, {a: eq.a, b: eq.b}) || Match(py, exp, Same, {a: eq.a, b: eq.b})) {
				return;
			} else {
				throw exp + " is not of the form " + px;
			}
		}
	});
}

function UseTransitivity(axioms, op, name) {
	axioms.push({
		name: "Transitivity of " + op,
		args: ["@a", "@b"],
		test: function(exp, args) {
			var m0 = Match( Parse("@a = @b"), args[0], Same );
			if (!m0) { throw args[0] + " should be in the form a=b";}
			var m1 = Match( Parse("@b = @c"), args[1], Same, {a:m0.a,b:m0.b} );
			var m2 = Match( Parse("@c = @b"), args[1], Same, {a:m0.a,b:m0.b} );
			var m = m1 || m2;
			if (m) {
				var a = Match( Parse("@a = @c"), exp, Same, m );
				var b = Match( Parse("@c = @a"), exp, Same, m );
				if (a || b) {
					return;
				}
			}
			//
			var m0 = Match( Parse("@b = @a"), args[0], Same );
			if (!m0) { throw args[0] + " should be in the form a=b";}
			var m1 = Match( Parse("@b = @c"), args[1], Same, {a:m0.a,b:m0.b} );
			var m2 = Match( Parse("@c = @b"), args[1], Same, {a:m0.a,b:m0.b} );
			var m = m1 || m2;
			if (m) {
				var a = Match( Parse("@a = @c"), exp, Same, m );
				var b = Match( Parse("@c = @a"), exp, Same, m );
				if (a || b) {
					return;
				}
			}
			throw "Invalid.";
		}
	});
}

// Add Reflexicity and Additive Property of Equality for an operation (usually =)
function UseReflexive(axioms, op) {
	op = op || "=";
	axioms.push({
		name: "Reflexivity of " + op,
		args: [],
		test: function(exp) {
			if (Match(Parse("@a " + op + " @a"), exp, Same)) {
				return false;
			}
			throw exp + " is not of the form a " + op + " a";
		}
	});
}

function UseSymmetry(axioms, op) {
	op = op || "=";
	axioms.push({
		name: "Symmetry of " + op,
		args: ["@flipped"],
		test: function(exp, args) {
			var m = Match(Parse("@a " + op + " @b"), exp, Same);
			if (!m) {
				throw exp + " is not of the form a " + op + " b";
			}
			if (Match(Parse("@b " + op + " @a"),args[0], m)) {
				return;
			}
			throw "Invalid";
		}
	});
}

// Add a rule for the associativity of an operation
function UseAssociativity(axioms, op) {
	if (!op) {
		throw "Must say operand in UseAssociativity";
	}
	axioms.push({
		name: "Associativity of " + op,
		args: [],
		test: function(exp) {
			var pattern = "(@a" + op + " @b) " + op + " @c=@a " + op + " (@b " + op + " @c)";
			if (Match(Parse(pattern), exp, Same)) {
				return false;
			}
			throw exp + " is not of the form (a+b)+c=a+(b+c)".replace(/\+/g, op);
		}
	});
}

// Add a rule for the commutativity of an operation
function UseCommutativity(axioms, op) {
	if (!op) {
		throw "Must say operand in UseCommutativity";
	}
	axioms.push({
		name: "Commutativity of " + op,
		args: [],
		test: function(exp) {
			var pattern = "@a " + op + " @b = @b " + op + " @a";
			if (Match(Parse(pattern), exp, Same)) {
				return false;
			}
			throw exp + " is not of the form a+b=b+a".replace(/\+/g, op);
		}
	});
}

function UseDistributivity(axioms, times, plus) {
	axioms.push({
		name: "[left] Distributivity of " + times + " over " + plus,
		args: [],
		test: function(exp) {
			if (Match(Parse("@a*(@b+@c)=@a*@b+@a*@c"), exp, Same)) {
				return;
			}
			throw "Not valid a*(b+c) = a*b + a*c";
		}
	});
	axioms.push({
		name: "[right] Distributivity of " + times + " over " + plus,
		args: [],
		test: function(exp) {
			if (Match(Parse("(@b+@c)*@a=@b*@a+@c*@a"), exp, Same)) {
				return;
			}
			throw "Not valid (b+c)*a = b*a + c*a";
		}
	});
}

function UseRing(axioms, plus, times) {
	// Closure is implicit ?
	plus = plus || "+";
	times = times || "*";
	// Commutativity, associativity, distributivity
	UseReflexive(axioms, "=");
	UseTransitivity(axioms, "=");
	UseEqualityProperty(axioms, "+", "Additive");
	UseEqualityProperty(axioms, "*", "Multiplicative");
	UseAssociativity(axioms, plus);
	UseCommutativity(axioms, plus);
	UseAssociativity(axioms, times);
	UseDistributivity(axioms, times, plus);
	// Additive inverse
	axioms.push({
		name: "Additive Identity (0)",
		args: [],
		test: function(exp) {
			if (Match(Parse("@a " + plus + " 0 = @a"), exp, Same)) {
				return;
			}
			throw "Expected a + 0 = a";
		}
	});
	axioms.push({
		name: "Additive Inverse",
		args: [],
		test: function(exp) {
			if (Match(Parse("@a " + plus + " -@a = 0"), exp, Same)) {
				return;
			}
			throw "Expected a + -a = 0";
		}
	});
}

////////////////////////////////////////////////////////////////////////////////
function UseNaturalDeduction(axioms) {
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
				if (history[i].assumption && history[i].uses(f.x.name)) {
					throw "'" + f.x +
						"' must not appear in any assumptions, but appears in statement " +
						(i+1);
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
				throw "'" + implication.x + "' and '" + args[1] +
					"' don't match, so modus ponens can't be applied";
			}
			if (!Same(implication.y, exp)) {
				throw "Expected conclusion to be '" + implication.y +
					"' but got '" + exp + "'";
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
		name: "Existential Elimination (Begin)",
		args: ["@exists"],
		opens: true,
		test: function(exp, args, history) {
			var exists = Match(Parse("exist @x, @predicate"), args[0], Same);
			if (!exists) {
				throw "Expected a there-exists statement";
			}
			var pattern = Substitute(exists.x, "x", exists.predicate);
			var v = Match(pattern, exp, Same);
			if (!v || !v.x) {
				throw "Did not match expected pattern " + pattern;
			}
			if (!(v.x instanceof Atom)) {
				throw "Expected a constant name but got '" + v.x + "'";
			}
			// Check that 'v' is not used anywhere in the history
			for (var i = 0; i < history.length; i++) {
				if (history[i].uses(v.x.name)) {
					throw "Statement " + (i+1) + " uses variable '" + v.x.name +
						"', so it cannot be used as the name of a constant.";
				}
			}
			exp.supposed = v.x.name;
		},
		concludes: function concludeExistentialElimination(exp, args, history, scope) {
			if (!Same(exp, scope[scope.length-1])) {
				throw "Must conclude the previous statement";
			}
			if (exp.uses(scope[0].supposed)) {
				throw "Must not contain the constant '" + scope[0].supposed + "'";
			}
		}
	});

	axioms.push({
		name: "Conclude (End)",
		closes: true,
		args: [],
		test: function(exp, args, history, scope) {
			return scope.concludes(exp, args, history, scope);
		}
	});

}

////////////////////////////////////////////////////////////////////////////////

// name: Name of axiom (listed in dropdown)
// args: List of arguments for axiom. Names are listed above inputs.
//       The first character is either
//       @ signifying the input is a statement number
//       $ signifying the input is an expression
// test: A function taking (student statement, [argument expressions])
//       It throws in the event the student statement does not follow
//       and otherwise returns anything truthy
// opens:
// closes: DO NOT USE except for single 'Conclude' for safety
