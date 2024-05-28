fof(inters_in_genopens,conjecture,unions(fB)=fX).
fof(topological_basis,axiom,![XB,XX]:(topological_basis(XB,XX)<=>(unions(XB)=XX&![XU,XV,Xx]:((elem(XU,XB)&elem(XV,XB)&elem(Xx,XU)&elem(Xx,XV))=>?[XW]:(elem(XW,XB)&elem(Xx,XW)&subseteq(XW,XU)&subseteq(XW,XV)))))).
fof(inters_in_genopens1,axiom,elem(fx,fVprimeprime)&subseteq(fVprimeprime,fC)&elem(fVprimeprime,fB)).
fof(inters_in_genopens2,axiom,elem(fx,fVprime)&subseteq(fVprime,fA)&elem(fVprime,fB)).
fof(inters_in_genopens3,axiom,elem(fx,inter(fA,fC))).
fof(inters_in_genopens4,axiom,topological_basis(fB,fX)).
