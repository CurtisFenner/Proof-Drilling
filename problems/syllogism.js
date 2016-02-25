//     All squirrels are fuzzy. (MaP)
//     Some wildlife are squirrels. (SiM)
//  |= Some wildlife are fuzzy. (SiP)

hypotheses = [
	"all x, Squirrel(x) -> Fuzzy(x)",
	"exist y, Wildlife(y) and Squirrel(y)",
];

UseNaturalDeduction(axioms);

solution = "exist z, Wildlife(z) and Fuzzy(z)";

DONE();
