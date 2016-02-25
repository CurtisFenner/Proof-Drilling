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
		if (d[1][0] === '@') {
			return new Expression( d[0], [d[1].substr(1)].concat(as) );
		}
		return new Expression( d[0], [new Atom(d[1])].concat(as) );
	}
	this.args = as.slice(0);
}
// Produce a string of LaTeX code representing this expression
Expression.prototype.latex = function(parent) {
	var latexMap = {
		"and": "\\wedge",
		"or": "\\vee",
		"->": "\\Rightarrow"
	}
	var me = getPrecedence(this.operator);
	var s;
	if (this.operator === "all") {
		s = "(\\forall " + this.args[0].latex(me) + ") (" + this.args[1].latex(me) + ")";
	} else if (this.operator === "exist") {
		s = "(\\exists " + this.args[0].latex(me) + ") (" + this.args[1].latex(me) + ")";
	} else if (this.operator === "~") {
		s = "\\neg " + this.args[0].latex(me);
	} else if (this.operator === "-u") {
		s = "-" + this.args[0].latex(me);
	} else if (this.operator === ".") {
		return this.args[0].latex(-1) + "(" + this.args[1].latex(-1) + ")";
	} else {
		s = this.args
			.map(function(arg){return arg.latex(me);})
			.join(" " + (latexMap[this.operator] || this.operator) + " ");
	}
	if (me < parent) {
		return "(" + s + ")";
	} else {
		return s;
	}
};
// Produce a human-readable string representing this expression
Expression.prototype.toString = function() {
	if (this.operator === ".") {
		return this.args[0] + "(" + this.args[1] + ")";
	}
	if (this.operator === ",") {
		return this.args.join(", ");
	}
	if (this.operator === "all" || this.operator === "exist") {
		return "(" + this.operator + " " + this.args[0] + ")(" + this.args[1] + ")";
	} else if (this.args.length === 1) {
		var o = this.operator.substr(-1)=="u" ? this.operator.substr(0,this.operator.length-1) : this.operator;
		return this.operator + this.args[0];
	} else {
		return "(" + this.args.join(" " + this.operator + " ") + ")";
	}
};
// Compare this expression precisely to `other`.
// Operator and all operands must be equal.
Expression.prototype.compare = function(other) {
	if (!other) {
		return false;
	}
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

// Returns whether or not the first parameter of this is a variable scoped to this operation
Expression.prototype.introducesVariable = function() {
	return this.operator === "exist" || this.operator === "all";
};

// Returns whether or not a given expression is notationally invalid.
Expression.prototype.invalid = function invalid(data) {
	if (!data) {
		data = {};
	}
	// Redeclaring a variable is invalid. e.g., "forall x, forall x, p(x)" since "x" becomes ambiguous
	if (this.introducesVariable()) {
		var name = this.args[0].name;
		if (data[name]) {
			return "variable '" + name + "' cannot be re-introduced";
		}
		data[name] = true;
		for (var i = 1; i < this.args.length; i++) {
			var reason = this.args[i].invalid(data);
			if (reason) {
				return reason;
			}
		}
		data[name] = false;
		return false;
	}
	// An expression is valid if its sub expressions are valid
	for (var i = 0; i < this.args.length; i++) {
		var reason = this.args[i].invalid(data);
		if (reason) {
			return reason;
		}
	}
	return false;
};

// "Normalizes" this expression (sorts commutative, re-groups associative)
Expression.prototype.normalize = function normalizeExpression(p) {
	var as = this.args.map(function(x){return x.normalize(p);});
	var x = [];
	for (var i = 0; i < as.length; i++) {
		if (p.flat[this.operator] && as[i].operator === this.operator) {
			x = x.concat(as[i].args);
		} else {
			x.push(as[i]);
		}
	}
	if (p.sort[this.operator]) {
		x = x.sort();
	}
	return new Expression(this.operator, x);
}

Expression.prototype.uses = function(name) {
	for (var i = 0; i < this.args.length; i++) {
		if (this.args[i].uses(name)) {
			return true;
		}
	}
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
Atom.prototype.invalid = function(data) {
	// TODO: Validate based on usage & name (a -- o for constants, p -- z for scoped varibles)
	return false;
};
Atom.prototype.uses = function(name) {
	return this.name === name;
};
Atom.prototype.normalize = function() {
	return new Atom(this.name);
};

// Match an expression against an expression pattern
// eq: a (transitive) function comparing expressions for precise equality
// Returns false if not a successful match
// Returns a dictionary of assignments to variables in pattern otherwise
function Match(pattern, object, eq, assignments) {
	if (!assignments) {
		assignments = {};
	}
	// pattern is an array. match each corresponding element.
	if (pattern instanceof Array) {
		if(!(object instanceof Array) || pattern.length !== object.length) {
			return false;
		}
		for (var i = 0; i < pattern.length; i++) {
			if (!Match(pattern[i], object[i], eq, assignments)) {
				return false;
			}
		}
		return assignments;
	}
	// pattern is a string -- a variable. it may be free,
	// or already bound to an expression
	if ("string" === typeof pattern) {
		if (pattern.indexOf("@") >= 0) {
			throw "Warning: bad pattern used with '" + pattern + "'";
		}
		if (assignments[pattern]) {
			if (!eq( assignments[pattern] , object)) {
				return false;
			}
		} else {
			assignments[pattern] = object;
		}
		return assignments;
	}
	// pattern is an atom. match exactly
	if (pattern instanceof Atom) {
		if (eq(pattern, object)) {
			return assignments;
		}
		return false;
	}
	// pattern is an expression. match its operator and operands
	if (pattern instanceof Expression) {
		if (pattern.operator != object.operator) {
			return false;
		}
		return Match(pattern.args, object.args, eq, assignments);
	}
	throw "Unknown pattern type.";
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

