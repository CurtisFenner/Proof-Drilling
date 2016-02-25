// Prove that the additive identity is the annihilator for multiplication

UseRing(axioms);

UseNaturalDeduction(axioms);

solution = "all x, 0*x = 0";

description = "Prove that $all x, 0*x = 0$ given only that 0 is the additive identity";

implicitSort.push("=");
implicitSort.push("+");
implicitFlat.push("+");
implicitFlat.push("*");
