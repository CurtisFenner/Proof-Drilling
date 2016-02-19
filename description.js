
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
