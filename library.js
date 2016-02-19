// Curtis Fenner
// cwfenner@umich.edu
// 4 February 2016
"use strict";

// Compare two expressions
function Same(a, b) {
	// TODO: Allow normalization for associativity and commutativity
	return a.compare(b, Same);
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
			if (!(v.x instanceof Atom)) {
				throw "Expected a constant name but got '" + v.x + "'";
			}
			// Check that 'v' is not used anywhere in the history
			for (var i = 0; i < history.length; i++) {
				if (history[i].uses(v.x.name)) {
					throw "Statement " + (i+1) + " uses variable '" + v.x.name + "', so it cannot be used as the name of a constant.";
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
