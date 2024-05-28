% It doesn't make sense for me that this task takes so long. It taks on my computer nearly 50-60 secounds.

fof(inters_in_genopens,conjecture,?[XW]:(elem(XW,fB)&elem(fx,XW)&subseteq(XW,fvprime)&subseteq(XW,fVprimeprime))).
%fof(topological_basis,axiom,![XB,XX]:(topological_basis(XB,XX)<=>(unions(XB)=XX&![XU,XV,Xx]:((elem(XU,XB)&elem(XV,XB)&elem(Xx,XU)&elem(Xx,XV))=>?[XW]:(elem(XW,XB)&elem(Xx,XW)&subseteq(XW,XU)&subseteq(XW,XV)))))).
fof(inters_in_genopens1,axiom,elem(fx,fVprimeprime)&subseteq(fVprimeprime,fC)&elem(fVprimeprime,fB)).
fof(inters_in_genopens2,axiom,elem(fx,fVprime)&subseteq(fVprime,fA)&elem(fVprime,fB)).
fof(inters_in_genopens3,axiom,elem(fx,inter(fA,fC))).
fof(inters_in_genopens4,axiom,topological_basis(fB,fX)).

fof(topological_basis1,axiom,![XU,XV,Xx]:((elem(XU,fB)&elem(XV,fB)&elem(Xx,XU)&elem(Xx,XV))=>?[XW]:(elem(XW,fB)&elem(Xx,XW)&subseteq(XW,XU)&subseteq(XW,XV)))).

fof(inters_in_genopens10,axiom,subseteq(fVprime,fA)).
fof(inters_in_genopens11,axiom,subseteq(fVprimeprime,fC)).
fof(inters_in_genopens12,axiom,elem(fx,fVprime)).
fof(inters_in_genopens13,axiom,elem(fx,fVprimeprime)).


% the task (unions(fB)=fX) takes only 0.2 secounds
% but if it is stated as an axiom it doesn't effect any proof time.


% with this axiom it takes 27 secounds so it improve the overall time, 
% but this axiom is just a "and" more and combines axiom 1 and 2
% fof(inters_in_genopens5,axiom,elem(fVprimeprime,fB)&elem(fVprimeprime,fB)&elem(fx,fVprime)&elem(fx,fVprimeprime)).

% fof(topological_basis1,axiom,![XU,XV,Xx]:((elem(XU,fB)&elem(XV,fB)&elem(Xx,XU)&elem(Xx,XV))=>?[XW]:(elem(XW,fB)&elem(Xx,XW)&subseteq(XW,XU)&subseteq(XW,XV)))).