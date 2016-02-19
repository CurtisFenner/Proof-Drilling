// (4)
hypotheses = [
	"all y, H(y,y)",
	"exist z, B(z)",
];

UseNaturalDeduction(axioms);

solution = "exist x, B(x) and H(x, x)";
description = "Prove $" + solution + "$ given $" + hypotheses.join("$, $") + "$.";
