// Curtis Fenner
// cwfenner@umich.edu
// 4 February 2016
"use strict";


// Represents an expression
// `op` is an operator (string)
// `as` is a list of operands (Expressions)
function Expression(op, as) {
	this.operator = op;
	// Break up bound quantifiers: all_x( p(x) ) --> all(x, p(x))
	if (this.operator.indexOf("_") >= 0) {
		var d = this.operator.split("_");
		return new Expression( d[0], [new Atom(d[1])].concat(as) );
	}
	this.args = as.slice(0);
}
// Produce a string of LaTeX code representing this expression
Expression.prototype.latex = function(parent) {
	var latexMap = {
		"and": "\\wedge",
		"or": "\\vee",
	}
	var me = getPrecedence(this.operator);
	var s;
	if (this.operator === "all") {
		s = "(\\forall " + this.args[0].latex(me) + ") (" + this.args[1].latex(me) + ")";
	} else if (this.operator === "exist") {
		s = "(\\exists " + this.args[0].latex(me) + ") (" + this.args[1].latex(me) + ")";
	} else if (this.operator === "~") {
		s = "\\neg " + this.args[0].latex(me);
	} else if (this.operator === ".") {
		return this.args[0].latex(-1) + "(" + this.args[1].latex(-1) + ")";
	} else {
		s = this.args[0].latex(me) + " " + (latexMap[this.operator] || this.operator) + " " + this.args[1].latex(me);
	}
	if (me < parent) {
		return "(" + s + ")";
	} else {
		return s;
	}
};
// Produce a human-readable string representing this expression
Expression.prototype.toString = function() {
	if (this.operator === "all" || this.operator === "exist") {
		return "(" + this.operator + " " + this.args[0] + ")" + this.args[1];
	} else if (this.args.length === 1) {
		return this.operator + this.args[0];
	} else {
		return "(" + this.args.join(" " + this.operator + " ") + ")";
	}
};
// Compare this expression precisely to `other`.
// Operator and all operands must be equal.
Expression.prototype.compare = function(other) {
	if (this.operator !== other.operator || this.args.length !== other.args.length) {
		return false;
	}
	for (var i = 0; i < this.args.length; i++) {
		if (!this.args[i].compare(other.args[i])) {
			return false;
		}
	}
	return true;
};

// Sugar for creating Binary expressions
function Bin(op, x, y) {
	return new Expression(op, [x, y]);
}
// Sugar for creating unary expressions
function Un(op, x) {
	return new Expression(op, [x]);
}

// Atom class (numbers and bound variables)
function Atom(n) {
	this.type = "atom";
	this.name = n;
}
Atom.prototype.toString = function(x) {
	return x ? "@" + this.name : this.name;
}
Atom.prototype.compare = function(other) {
	return other.name === this.name;
}
Atom.prototype.latex = function() {
	return this.name;
};

// Match an expression against an expression pattern
// eq: a (transitive) function comparing expressions for precise equality
// Returns false if not a successful match
// Returns a dictionary of assignments to variables in pattern otherwise
function Match(pattern, object, eq, assignments) {
	if (!assignments) {
		assignments = {};
	}
	if ("string" === typeof pattern) {
		if (assignments[pattern]) {
			if (!eq( assignments[pattern] , object)) {
				return false;
			}
		} else {
			assignments[pattern] = object;
		}
		return assignments;
	}
	if (pattern instanceof Atom) {
		if (eq(pattern, object)) {
			return assignments;
		}
		return false;
	}
	if (pattern instanceof Expression) {
		if (pattern.operator != object.operator) {
			return false;
		}
		if (pattern.args.length != object.args.length) {
			return false;
		}
		for (var i = 0; i < pattern.args.length; i++) {
			var m = Match(pattern.args[i], object.args[i], eq, assignments);
			if (!m) {
				return m;
			}
		}
		return assignments;
	} else {
		throw "Unknown pattern type.";
	}
}

// Substitute an expression for another expression
function Substitute(pattern, replacement, object) {
	if (Same(pattern, object)) {
		return replacement;
	} else {
		if (object instanceof Expression) {
			var u = [];
			for (var i = 0; i < object.args.length; i++) {
				u[i] = Substitute(pattern, replacement, object.args[i]);
			}
			return new Expression(object.operator, u);
		} else {
			return object;
		}
	}
}

///////////////////////////////////////////////////////////////////////////////

function isSpace(c) {
	return c.trim() === "";
}

function isDigit(c) {
	return c * 1 == c * 1 && 0 <= c;
}

function isLetter(c) {
	return c.replace(/[@a-zA-Z]/, "") === "";
}

// Classifies character c for the purposes of joining adjacent
// characters into tokens (see `joined` and `Tokens`)
function classify(c) {
	if (c === ".") {
		return "dot";
	} else if (isSpace(c)) {
		return "space";
	} else if (isDigit(c)) {
		return "digit";
	} else if (isLetter(c)) {
		return "letter";
	}
	return "op";
}

// Returns whether character classes a and b (from `classify`)
// are part of the same token when adjacent (see `Tokens`)
function joined(a, b) {
	if (a === "space" || b === "space") {
		return false;
	}
	if (a === "dot") {
		return b === "digit";
	}
	if (a === "letter") {
		return b === "letter";
	}
	if (a === "digit") {
		return b === "digit" || b === "dot";
	}
	if (a === "op") {
		return b === "op";
	}
	throw "unclassified pair " + a + ", " + b;
}

// Splits a string into tokens.
// Adjacent characters are joined based on `joined` and `classify`
function Tokens(text) {
	text += " ";
	var last = "space";
	var a = [];
	var w = "";
	for (var i = 0; i < text.length; i++) {
		var c = classify( text[i] );
		if (joined(last, c)) {
			w += text[i];
		} else {
			if (w.trim()) {
				a.push(w);
			}
			w = text[i];
		}
		last = c;
	}
	return a;
}

// Defines the order of precedence for operators
var operatorPrecedence = {
	".": 100,
	"~": 90,
	"*": 75,
	"/": 75,
	"+": 50,
	"-": 50,
	"=": 30,
	"and": 20,
	"or": 10,
	"all": 5, // all, exist not actually used.
	"exist": 5,
	",": 1,
};

// Defines the arity of non-binary operators
var operatorArity = {
	"~": 1
};

// Defines whether operators are right-associative
// (otherwise left associative)
var operatorRightAssociative = {
	"^": true
};

// Returns whether operator 'a' is lower precedence than
// operator 'b' for use in the shunting-yard-algorithm.
// If a and b are equal, it returns whether the operator
// is left-associative.
function lower(a, b) {
	if (operatorPrecedence[a] == operatorPrecedence[b]) {
		return !operatorRightAssociative[a];
	} else {
		return operatorPrecedence[a] < operatorPrecedence[b];
	}
}

// Returns whether or not an operator is a quantifier.
function isQuantifier(t) {
	return t === "all" || t === "exist";
}

// Adjusts an array of tokens to allow some extra syntax:
// 1) adds an explicit "." as a function-application-operator
// 2) adjusts quantifiers to be unary operators that are
//    bound with their variables (stripping parens and
//    commmas around them)s
function FixTokens(x) {
	var r = [];
	// Bind quantifiers
	// Add application operators
	for (var i = 0; i < x.length; i++) {
		if (isQuantifier(x[i-1])) {
			// ["all", "x"] --> ["all_x"]
			// ["all", "x", ","] --> ["all_x"]
			r[r.length-1] += "_" + x[i];
			if (x[i+1] === ",") {
				i++;
			}
		} else {
			// ["name", "("] --> ["name", ".", "("]
			if (x[i] === "(" && x[i-1] && isLetter(x[i-1][0]) ) {
				r.push(".");
			}
			r.push(x[i]);
		}
	}
	// Removes parenthesis around bound quantifiers
	// ["(", "quant_x", ")"] --> ["quant_x"]
	for (var i = 1; i+1 < r.length; i++) {
		if (r[i-1] === "(" && r[i+1] === ")" && r[i].indexOf("_") >= 0) {
			r = r.slice(0, i - 1).concat([ r[i] ]).concat(r.slice(i + 2));
		}
	}
	return r;
}

// Returns the precedence (as a number) of an operator
function getPrecedence(op) {
	if (op.indexOf("_") >= 0) {
		// bound quantifiers are precedence 5
		// (and not in lookup table)
		return 5;
	}
	return operatorPrecedence[op];
}

// Returns the arity of an operator (usually 2 for infix binary)
function getArity(op) {
	if (op.indexOf("_") >= 0) {
		return 1;
	}
	return operatorArity[op];
}

// Given a list of tokens (strings), produces a RPN sequence of
// tokens to be interpretted by the arity of operators.
function ParseShunting(tokens) {
	tokens = FixTokens(tokens);
	//
	var output = [];
	var stack = [];
	for (var i = 0; i < tokens.length; i++) {
		var token = tokens[i];
		if (token === ")") {
			while (stack[stack.length - 1] != "(") {
				output.push(stack.pop());
				if (!stack.length) {
					throw "unmatched paren";
				}
			}
			stack.pop();
		} else if ( getPrecedence(token) ) {
			while (stack.length && lower(token, stack[stack.length-1])) {
				output.push( stack.pop() );
			}
			stack.push( token );
		} else if (token === "(") {
			stack.push(token);
		} else {
			output.push( token );
		}
	}
	while (stack.length) {
		output.push( stack.pop() );
	}
	return output;
}

// Returns an Expression by parsing `text`
// Throws on invalid input
function Parse(text) {
	var x = ParseShunting( Tokens(text) );
	for (var i = 0; i < x.length; i++) {
		var t = x[i];
		if (getPrecedence(t)) {
			var a = getArity(t) || 2;
			var before = x.slice(0, i - a);
			var args = x.slice(i - a, i);
			var after = x.slice(i + 1);
			if (a === 1) {
				var obj = new Un(t, args[0]);
			} else if (a === 2) {
				var obj = new Bin(t, args[0], args[1]);
			} else {
				throw "invalid arity";
			}
			x = before.concat([obj]).concat(after);
			i -= a;
		} else {
			x[i] = new Atom(t);
		}
	}
	if (x.length != 1) {
		throw "Could not parse near '" + x[1] + "'";
	}
	return x[0];
}

