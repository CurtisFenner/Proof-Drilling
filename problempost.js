// This file defines 'DONE()' which should be the last line of every problem
// definition script.

// DONE() builds the proof table and shows and enables it.

////////////////////////////////////////////////////////////////////////////////

function DONE(){
	solution = Parse(solution);

	if (!description) {
		if (hypotheses.length === 0) {
			description += "    /PROBLEM DID NOT SPECIFY ANY GIVENS/";
		}
	}
	if (axioms.length === 0) {
		description += "    /PROBLEM DID NOT SPECIFY ANY AXIOMS/"
	}

	hypotheses = hypotheses.map(Parse);
	problemdescription.textContent = description || ("Prove $" + solution + "$ given $" + hypotheses.join("$, $") + "$.");

	// Add hypotheses lines to proof:
	var lines = hypotheses.map(function(e) {
		return {expression: e, text: "x", reason: "given", args: ["","",""]};
	});

	// Add empty lines to proof:
	for (var i = 0; i < 13; i++) {
		lines.push( {expression: new Atom("x"), text: "", reason: "", args: ["", "", ""] });
	}
	Setup(lines);
}
