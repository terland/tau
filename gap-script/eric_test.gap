LoadPackage("qpa");
Q := Quiver(3, [[1,2,"a"],[1,2,"b"],[2,3,"c"]]);
KQ := PathAlgebra(GF(2),Q);


AssignGeneratorVariables(KQ);
KQ := KQ/[a*c];

inj := IndecInjectiveModules(KQ);
Display(IsTauRigidModule(inj[3])); #Gives false

Display(DTr(inj[3]));
Display(HomOverAlgebra(inj[3],DTr(inj[3]))); # Has 1 basis element
