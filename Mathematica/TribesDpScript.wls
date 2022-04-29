#!/usr/bin/env wolframscript
(* ::Package:: *)

fsum[p_, k_, m_] := Sum[p^(j-1),{j,1,k}]*Sum[(1-p^k)^(i-1),{i,1,m}]
k = 30
m = 20
f = fsum[p,k,m]
plot1 = Plot[f,{p,0,1}]
u=D[f,p]
proot = p/.FindRoot[u==0,{p,0,1}]
fsum[proot,2,2]
plot2 = Show[plot1, Graphics[{PointSize[0.025], Point[{proot, fsum[proot,k,m]}]}]]
filenameTemplate = StringTemplate["/home/julia/git/ComplexityOfBooleanFunctions/plots/tribes`m``k`.eps"];
filename = filenameTemplate[<|"m" -> m,"k" -> k|>]
Export[filename,plot2]















