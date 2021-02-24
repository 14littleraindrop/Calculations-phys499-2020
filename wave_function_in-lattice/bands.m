(* ::Package:: *)

BeginPackage["Bands`"];

BandEnergy::usage = "BandEnergy[u, q, (n:0)]";
BandGap::usage = "BandGap[u, (n:0)]";
MathieuPotentialWaveFunction::usage = "MathieuPotentialWaveFunction[r, q, z]";
CreateTwoBandPropagator::usage = "CreateTwoBandPropagator[u, k, (n:0)]";
CreateThreeBandPropagator::usage = "CreateThreeBandPropagator[u, k, (n:0)]";
CreateTwoBandEfficiencyFunction::usage = "CreateTwoBandEfficiencyFunction[u, nbo, (band:0, mode: \"Default\")]";
CreateThreeBandEfficiencyFunction::usage = "CreateThreeBandEfficiencyFunction[u, nbo, (band:0, mode: \"Default\")]";
CreateThreeBandEfficiencyFunctionMiddle::usage = "CreateThreeBandEfficiencyFunctionMiddle[u, nbo, (band:0, mode: \"Default\")]";
TranslateQuasimomentum::usage = "TranslateQuasimomentum[q, n]";
LandauZener::usage = "LandauZener[u, \[Tau], (n:0)]";
Options[LandauZener] ={BandGapGiven -> False};
Options[LandauZenerGamma] ={BandGapGiven -> False};
BandGapGiven::usage = "Option for LandauZener and LandauZenerGamms";
StokesPhase::usage = "StokesPhase[\[Gamma]]";
StueckelbergPhaseIntegral::usage = "StueckelbergPhaseIntegral[u, {n:0, m:1}]";
MathieuPotentialWaveFunction::usage = "MathieuPotentialWaveFunction[r, q, z]";

Begin["`Private`"];
bovera[r_,q_]:=I*(Exp[I*Pi*r]*MathieuC[MathieuCharacteristicA[r, q], q, 0] 
					- MathieuC[MathieuCharacteristicA[r, q], q, Pi]) / (
						Exp[I*Pi*r]*MathieuS[MathieuCharacteristicB[r, q], q, 0] 
						- MathieuS[MathieuCharacteristicB[r, q], q, Pi]);
(*exq[q_, n_] := q+If[q!=0, Sign[q], 1]*(-1)^n*Quotient[n+1,2]*2;*)
TranslateQuasimomentum[q_, n_] := Module[{delta = 0.000001},
	qmod = If[q == 1, q-delta, If[q == -1, q+delta, If[Abs[q] <= delta, delta, q]]]; 
	qmod+Sign[qmod]*(-1)^n*Quotient[n+1,2]*2];

MathieuPotentialWaveFunction[r_, q_, z_] :=Quiet[
	MathieuC[MathieuCharacteristicA[r, q], q, Pi*z] 
		+ I * bovera[r, q]*MathieuS[MathieuCharacteristicB[r, q], q, Pi*z]];
BandEnergy[u_, q_, n_:0] := N[MathieuCharacteristicA[TranslateQuasimomentum[q, n] ,u/4]];
StueckelbergPhaseIntegral[u_, n_:0, m_:1]:=NIntegrate[BandEnergy[u, q, n+m]-BandEnergy[u, q, n], {q, -1, 1}];
BandGap[u_, n_:0] := Min[BandEnergy[u, 1, n+1]-BandEnergy[u, 1, n], BandEnergy[u, 0, n+1]-BandEnergy[u, 0, n]];

LandauZenerGamma[u_, \[Tau]_, n_:0, opts:OptionsPattern[]] := (\[Pi]*If[OptionValue[BandGapGiven], u, BandGap[u, n]]^2*\[Tau])/(16*(n+1))
LandauZener[u_, \[Tau]_, n_:0, opts:OptionsPattern[]] := Exp[-2*\[Pi]*LandauZenerGamma[u, \[Tau], n, BandGapGiven -> OptionValue[BandGapGiven]]];

StokesPhase[\[Gamma]_] := Pi/4 + \[Gamma]*(Log[\[Gamma]] - 1) + Arg[Gamma[1 - I*\[Gamma]]];
StueckelbergPhase[u_,\[Tau]_, n_:0] := Pi * \[Tau] * StueckelbergPhaseIntegral[u, n];

CreateTwoBandPropagator[u_, k_, n_:0] := Module[
	{\[Iota] = StueckelbergPhaseIntegral[u, n],
	m1, m2, m3},
	m1[\[Tau]_]={
		{1, 0}, 
		{0, Sqrt[1-LandauZener[u, \[Tau], n+1]]*Exp[-I*(Pi*\[Tau]*\[Iota]/2+StokesPhase[LandauZenerGamma[u, \[Tau], n+1]])]}
	};
	m2[\[Tau]_, c1_, c2_]={
		{Sqrt[1-c2*LandauZener[u, \[Tau]*c1, n]]*Exp[-I*StokesPhase[LandauZenerGamma[u, \[Tau], n]]],
			-Sqrt[c2*LandauZener[u, \[Tau]*c1, n]]},
		{Sqrt[c2*LandauZener[u, \[Tau]*c1, n]],
			Sqrt[1-c2*LandauZener[u, \[Tau]*c1, n]]*Exp[I*StokesPhase[LandauZenerGamma[u, \[Tau], n]]]}
	};
	m3[\[Tau]_]={
		{1, 0},
		{0, Exp[-I*Pi*\[Tau]*\[Iota]/2]}
	};
	Function[{\[Tau], c1, c2}, Evaluate[MatrixPower[m3[\[Tau]].m2[\[Tau], c1, c2].m1[\[Tau]],k]]]
];

CreateThreeBandPropagator[u_, k_, n_:0] := Module[
	{\[Iota]1 = StueckelbergPhaseIntegral[u, n],
	 \[Iota]2 = StueckelbergPhaseIntegral[u, n, 2],
	 m1, m2, m3},
	d1[\[Tau]_]={
		{1, 0, 0}, 
		{0, Sqrt[1-LandauZener[u, \[Tau], n+1]]*Exp[-I*StokesPhase[LandauZenerGamma[u, \[Tau], n+1]]],
			-Sqrt[LandauZener[u, \[Tau], n+1]]},
		{0, Sqrt[LandauZener[u, \[Tau], n+1]],
			Sqrt[1-LandauZener[u, \[Tau], n+1]]*Exp[I*StokesPhase[LandauZenerGamma[u, \[Tau], n+1]]]}
	};
	m[\[Tau]_]={
		{1, 0, 0},
		{0, Exp[-I*Pi*\[Tau]*\[Iota]1/2], 0},
		{0, 0, Exp[-I*Pi*\[Tau]*\[Iota]2/2]}
	};

	d2[\[Tau]_, c1_, c2_]={
		{Sqrt[1-c2 + 0*LandauZener[u, \[Tau]*c1, n]]*Exp[-I*StokesPhase[LandauZenerGamma[u, \[Tau], n]]],
			-Sqrt[c2 + 0*LandauZener[u, \[Tau]*c1, n]], 0},
		{Sqrt[c2 + 0*LandauZener[u, \[Tau]*c1, n]],
			Sqrt[1-c2 + 0 *LandauZener[u, \[Tau]*c1, n]]*Exp[I*StokesPhase[LandauZenerGamma[u, \[Tau], n]]], 0},
		{0, 0, Sqrt[1-LandauZener[u, \[Tau], n+2]]*Exp[-I*StokesPhase[LandauZenerGamma[u, \[Tau], n+2]]]}
	};
	Function[{\[Tau], c1, c2}, Evaluate[MatrixPower[m[\[Tau]].d2[\[Tau], c1, c2].m[\[Tau]].d1[\[Tau]], k]]]
];

CreateTwoBandEfficiencyFunction[u_, k_, n_:0, mode_: "Default"] := Module[
	{prop = CreateTwoBandPropagator[u, k, n], m = If[mode == "Full", 1, k]},
	Function[{\[Tau], c1, c2}, Evaluate[Norm[(prop[\[Tau], c1, c2].{1, 0})[[1]]]^(2/m)]]];

CreateThreeBandEfficiencyFunction[u_, k_, n_:0, mode_: "Default"] := Module[
	{prop = CreateThreeBandPropagator[u, k, n], m = If[mode == "Full", 1, k]},
	Function[{\[Tau], c1, c2}, Evaluate[Norm[(prop[\[Tau], c1, c2].{1, 0, 0})[[1]]]^(2/m)]]];

CreateThreeBandEfficiencyFunctionMiddle[u_, k_, n_:0, mode_: "Default"] := Module[
	{prop = CreateThreeBandPropagator[u, k, n], m = If[mode == "Full", 1, k]},
	Function[{\[Tau], c1, c2}, Evaluate[Norm[(prop[\[Tau], c1, c2].{0, 1, 0})[[2]]]^(2/m)]]];
End[]; (* `Private` *)
EndPackage[]; (* Bands` *)
