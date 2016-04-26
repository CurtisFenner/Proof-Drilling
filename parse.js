// Parse expressions
"use strict";

// This file parses strings into Expression objects.
// It is a shunting-yard-algorithm, with some extra cleanup to support human-
// friendly quantifier syntax, and an explicit functiona-application operator.

// Parse(String input) -> Expression

////////////////////////////////////////////////////////////////////////////////

function isSpace(c) {
	return c.trim() === "";
}

function isDigit(c) {
	return c * 1 == c * 1 && 0 <= c;
}

function isLetter(c) {
	return c.replace(/[@a-zA-Z]/, "") === "";
}

function isBracket(c) {
	return c === "(" || c === ")";
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
	} else if (isBracket(c)) {
		return "bracket";
	}
	return "op";
}

// Returns whether character classes a and b (from `classify`)
// are part of the same token when adjacent (see `Tokens`)
function joined(a, b) {
	if (a === "space" || b === "space" || a == "bracket" || b == "bracket") {
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
	"-u": 90,
	"*": 75,
	"/": 75,
	"+": 50,
	"-": 50,
	"=": 30,
	"and": 20,
	"or": 10,
	"->": 9,
	"all": 5, // all, exist not actually used.
	"exist": 5,
	",": 1,
};

// Defines the arity of non-binary operators
var operatorArity = {
	"~": 1,
	"-u": 1,
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
	if (getPrecedence(a) == getPrecedence(b)) {
		return !operatorRightAssociative[a] && a.indexOf("_") < 0;
	} else {
		return getPrecedence(a) < getPrecedence(b);
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
			r.splice(i+1, 1);
			r.splice(i-1, 1);
			//r = r.slice(0, i - 1).concat([ r[i] ]).concat(r.slice(i + 2));
		}
	}
	for (var i = 0; i < r.length; i++) {
		if (i === 0 || getPrecedence(r[i-1]) || r[i-1] === "(") {
			if (r[i] === "-") {
				r[i] = "-u";
			}
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
			if (i - a < 0) {
				throw "Could not parse near '" + t + "'; expected more";
			}
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
			if (t[0] == "@") { // Bare strings. Useful for patterns in `Match`
				x[i] = t.substr(1);
			} else {
				x[i] = new Atom(t);
			}
		}
	}
	if (x.length != 1) {
		throw "Could not parse near '" + x[1] + "'";
	}
	return x[0];
}

