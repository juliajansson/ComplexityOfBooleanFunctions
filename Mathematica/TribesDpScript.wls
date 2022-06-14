#!/usr/bin/env wolframscript
(* ::Package:: *)

<<MaTeX`
fsum[p_, k_, m_] := Sum[p^(j-1),{j,1,k}]*Sum[(1-p^k)^(i-1),{i,1,m}]
k = 4
m = 9
f = fsum[p,k,m]
Expand[f]
u=D[f,p]
proot = p/.FindRoot[u==0,{p,0,1}]
maxval = fsum[proot,k,m]
plot1 = Plot[f,{p,0,1},Frame -> True,FrameLabel->{MaTeX@"p", MaTeX@"D_p(f)"},LabelStyle->{Black,Medium} ,PlotRange->{{0,1},{0,maxval+2}}]
plot2 = Show[plot1, Graphics[{PointSize[0.025], Point[{proot, maxval}]}]]
filenameTemplate = StringTemplate["/home/julia/git/ComplexityOfBooleanFunctions/plots/tribes`m``k`.eps"];
filename = filenameTemplate[<|"m" -> m,"k" -> k|>]
Export[filename,plot2]



























