// Curtis Fenner
// cwfenner@umich.edu
// 4 February 2016
"use strict";

// A convenience method for creating a DOM object of
// type `e` and adding it to `parent`
function make(e, parent) {
	var x = document.createElement(e);
	if (parent) {
		parent.appendChild(x);
	}
	return x;
}

// Render a single line of the table (creating a <tr>)
function RenderLine(proof, i) {
	var line = make("tr", problem);
	var equation = make("td", line);
	var num = make("td", line);
	var box = make("td", line);
	var reason = make("td", line);
	var argCells = [];
	var argLabels = [];
	var argInputs = [];
	// Set up the arguments fields and attach labels
	for (var j = 0; j < 2; j++) {
		var cell = make("td", line);
		argCells.push( cell );
		var label = make("span", cell);
		label.className = "little";
		argLabels.push( label );
		var input = make("input", cell);
		input.required = true;
		input.value = proof[i].args[j];
		argInputs.push( input );
	}
	var errors = make("td", line);
	// This function updates the labels of the arguments
	var updateLabels = function() {
		var ax = axioms[s.value];
		for (var j = 0; j < argLabels.length; j++) {
			argLabels[j].textContent = "";
			argInputs[j].disabled = true;
		}
		if (!ax) {
			for (var j = 0; j < argInputs.length; j++) {
				argInputs[j].disabled = true;
			}
			return;
		}
		for (var j = 0; j < ax.args.length; j++) {
			argLabels[j].textContent = ax.args[j].substr(1);
			argInputs[j].disabled = false;
			if (ax.args[j][0] === "@") {
				argInputs[j].type = "number";
				argInputs[j].min = 1;
				argInputs[j].max = i;
			} else {
				argInputs[j].type = "text";
			}
		}
	}
	// Label the current statement number
	num.textContent = i + 1 + ".";
	//
	var e = make("input", box);
	e.disabled = i < hypotheses.length;
	e.value = proof[i].text;
	e.oninput = function() {
		proof[i].text = e.value;
	};
	// Create the justification drop down
	var s = make("select", reason);
	if (e.disabled) {
		var x = make("option", s);
		x.textContent = "given";
		s.disabled = true;
		e.value = proof[i].expression.toString().replace(/@/g, "");
		katex.render( proof[i].expression.latex(), equation );
	} else {
		for (var j = 0; j < axioms.length; j++) {
			var o = make("option", s);
			o.value = j;
			o.textContent = axioms[j].name;
		}
		s.value = proof[i].reason;
		//
		proof[i].expression = null;
		try {
			// Verify the statement.
			if (!proof[i].text) {
				// Require the student enters a statement to check
				throw "";
			}
			// Parse and render the expression (throws on failure)
			proof[i].expression = Parse(proof[i].text);
			katex.render( proof[i].expression.latex(), equation );
			if (proof[i].reason === "") {
				// Require the student enter a justification for their statement
				throw "Must enter justification";
			}
			// Get the definition of the justification they picked.
			var ax = axioms[ s.value ];
			var args = [];
			if (ax) {
				// If the justification field isn't blank...
				// Consider all of the arguments the axiom requires.
				// They may be previous statements, or expressions.
				// Pull the Expressions either represents into `args`
				for (var j = 0; j < ax.args.length; j++) {
					if (ax.args[j][0] === "@") {
						var m = parseInt( proof[i].args[j] ) - 1;
						// Verify the statement number is before this one (and positive, etc)
						if (isFinite(m) && m === m << 0 && m >= 0) {
							if (m >= i) {
								throw "Statement must come before this";
							}
						} else {
							throw "Statement number '" + proof[i].args[j] + "' is not a number";
						}
						args[j] = proof[m].expression;
					} else {
						var m = Parse( proof[i].args[j] );
						args[j] = m;
					}
				}
				// `ax.test` is a friendlier function which infers expressions.
				// If it's provided for this axiom, use it!
				if (ax.test) {
					var okay = ax.test(proof[i].expression, args);
					// throws on failure
				} else {
					// Otherwise, compute (given arguments, but NOT student statement)
					// what you expect, and check that they match.
					var predicted = ax.fun(args);
					if (!Same(proof[i].expression, predicted)) {
						throw "This statement does not follow.\nExpected: " + predicted;
					}
				}
			}
		} catch (error) {
			// Show why this line is wrong
			errors.textContent = error;
		}
	}
	// Update all the labels when the justification changes
	s.onchange = function() {
		proof[i].reason = s.value;
		updateLabels();
	}
	// Update the labels now so that they match the initial state of the proof
	updateLabels();
	// On any change to any argument, save the value.
	for (var j = 0; j < argInputs.length; j++) {
		argInputs.value = proof[i].args[j];
		(function(u){
			argInputs[u].oninput = function() {
				proof[i].args[u] = argInputs[u].value;
			};
		})(j);
	}
	//
}

// Render all of the lines of the current proof
function Render(proof) {
	while (problem.firstChild) {
		problem.removeChild(problem.firstChild);
	}
	for (var i = 0; i < proof.length; i++) {
		RenderLine(proof, i);
	}
}

// Show the initial state of the table with hypotheses
// (hypotheses loaded in "problem.js")
Render(lines);

// Recheck answers when the 'recheck' button is pressed
recheck.onclick = function() {
	Render(lines);
};


