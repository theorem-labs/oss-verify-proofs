(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit AsanNodesWJoin BothStartup StartupPlanBoth StartupHSBoth StartupPlan2Both StartupHS2Both.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanCertDefs () := "C6ARocqVerifyHarness?AgentSubmission2AS=AsanPlanSound3APSDmk_itab_ranges_soundC5ARocqVerifyHarness?AgentSubmission2AS>BothPlanImages5ASEGSC5ARocqVerifyHarness?AgentSubmission2AS?StartupPlanBothEstartup_plan_ranges_0C5ARocqVerifyHarness?AgentSubmission2AS?StartupPlanBothEstartup_plan_ranges_AK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Peano2le00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP3NX0c5ARocqVerifyHarness?AgentSubmission2AS<BothCertDefs3NXBC5ARocqVerifyHarness?AgentSubmission2AS?StartupPlanBothEstartup_plan_ranges_Bc5ARocqVerifyHarness?AgentSubmission2AS<BothCertDefs3NXCC5ARocqVerifyHarness?AgentSubmission2AS?StartupPlanBothEstartup_plan_ranges_Cc5ARocqVerifyHarness?AgentSubmission2AS<BothCertDefs3NXDC5ARocqVerifyHarness?AgentSubmission2AS@StartupPlan2BothDstartup2_plan_rangesc5ARocqVerifyHarness?AgentSubmission2AS<BothCertDefs4NXS2".
Unset Lia Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.
(* [comment removed for export] *)
Definition IT0 : itab := mk_itab_ranges ASEGS startup_plan_ranges_0.
Lemma IT0_ok : itab_sound ASEGS IT0.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCertDefs ()) [] "p;2g0000j20Tg001>g002:'0o"). Qed.
Definition startup_shape : shape := SHole 10.

(* [comment removed for export] *)
Definition ITB : itab := mk_itab_ranges ASEGS startup_plan_ranges_A.
Lemma ITB_ok : itab_sound ASEGS ITB.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCertDefs ()) [] "p;2g0000j20Tg001>g003G'0o"). Qed.
(* [comment removed for export] *)
Definition NXB : nat := 207%nat.
Lemma NXB_ge : (NX0 <= NXB)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCertDefs ()) [] "h07__arithh14__ffh28__varmaph35__witp;1p;2p;4p;7p;3p;<g004Tj10Tg0053R0j26Tg005Mj14Tg0062j11Tg006Wj17Tg0075R1j2;Tg007Qj23Tg007kj1:Tg008Kj1ITg008kj1HTg009Ij1GTg009gj1CTg00:Rj25Tg00;5j4BTg00;`j7?Tg00<Dj2@Tg00<fj2ATg00=Rj3=Tg00=lj3DTg00>Kj4ETg00?=j4<Tg00?hl<FTf0R2#0#0p=J%02#0#0#0#0#0#0#0p=>%02#0#0#0p=8%02#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=2g00@Mg00@lR3P0g00AJP1g00Ajf5f4f3f2R1f1R0P2M<Fp=9g00BL#0#J#>R4%84#2#2#2#2#2#2R5'6g00BkR6#4#1#1#7R7%16#4#4#1#1#1#1#7R6';R8P4P71337P5P61336E9g00CPR5#:%I5%H3%G3%C3R5g00D<g00D[R4P4g00E;R4P31537g00E[1536CBg00FBF?1@54P2P1g00FbR4g00GBR5'31A21==45dg00Gb=D30CEb1b2b3P8P2b0C<g00H@g00I7'6eo"). Qed.
Definition startup_shapeB : shape := SHole 11.

(* [comment removed for export] *)
Definition ITC : itab := mk_itab_ranges ASEGS startup_plan_ranges_B.
Lemma ITC_ok : itab_sound ASEGS ITC.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCertDefs ()) [] "p;2g0000j20Tg001>g00Io'0o"). Qed.
(* [comment removed for export] *)
Definition NXC : nat := 344%nat.
Lemma NXC_ge : (NX0 <= NXC)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCertDefs ()) [] "h07__arithh14__ffh28__varmaph35__witp;1p;2p;4p;7p;3p;<g004Tj10Tg0053R0j26Tg005Mj12Tg0062j13Tg006Wj18Tg0075R1j2<Tg007Qj24Tg007kj19Tg008Kj1ITg008kj1HTg009Ij1GTg009gj1DTg00:Rj25Tg00;5j4CTg00;`j7@Tg00<Dj2ATg00<fj2BTg00=Rj3?Tg00=lj3>Tg00>Kj4ETg00?=j4=Tg00?hl<FTf0R2#0#0p=J%02#0#0#0#0#0#0#0p=7%02#0#0#0p=;%02#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00@Mg00@lR3P0g00AJP1g00Ajf5f4f3f2R1f1R0P2M<Fp=:g00BL#0#J#7R4%04#;#7#1#1#1#1#1#1#1#1#1#1R5'6g00Bk#2#3R6#3#8R7%26#3#3#2#2#2#8R6'<R8P4P71437P5P61436E:g00CPR5#9%I5%H3%G3%D3R5g00D<g00D[R4P4g00E;R4P31537g00E[1536CCg00FBF@1A54P2P1g00FbR4g00GBR5'41B21=?45dg00Gb=>30CEb1b2b3P8P2b0C=g00H@g00K<'6eo"). Qed.
Definition startup_shapeC : shape := SCase (EVar 6) 10 (SCase e_atr8 17592186044384 (SHole 12) (SCase e_atr8 17592186044385 (SHole 12) (SCase e_atr8 17592186044386 (SHole 12) (SCase e_atr8 17592186044387 (SHole 12) (SCase e_atr8 17592186044388 (SHole 12) (SCase e_atr8 17592186044389 (SHole 12) (SCase e_atr8 17592186044390 (SHole 12) (SHole 12)))))))) (SCase e_atr8 17592186044384 (SHole 12) (SCase e_atr8 17592186044385 (SHole 12) (SCase e_atr8 17592186044386 (SHole 12) (SCase e_atr8 17592186044387 (SHole 12) (SCase e_atr8 17592186044388 (SHole 12) (SCase e_atr8 17592186044389 (SHole 12) (SCase e_atr8 17592186044390 (SHole 12) (SHole 12)))))))).

(* [comment removed for export] *)
Definition ITD : itab := mk_itab_ranges ASEGS startup_plan_ranges_C.
Lemma ITD_ok : itab_sound ASEGS ITD.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCertDefs ()) [] "p;2g0000j20Tg001>g00L4'0o"). Qed.
(* [comment removed for export] *)
Definition NXD : nat := 394%nat.
Lemma NXD_ge : (NX0 <= NXD)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCertDefs ()) [] "h07__arithh14__ffh28__varmaph35__witp;1p;2p;4p;7p;3p;<g004Tj10Tg0053R0j26Tg005Mj12Tg0062j13Tg006Wj15Tg0075R1j2;Tg007Qj24Tg007kj1JTg008Kj1ITg008kj1HTg009Ij1DTg009gj1CTg00:Rj27Tg00;5j4@Tg00;`j7ATg00<Dj2BTg00<fj2?Tg00=Rj3>Tg00=lj3ETg00>Kj4=Tg00?=j4FTg00?hl<GTf0R2#0#0p=9%02#0#0#0#0#0#0#0p=8%02#0#0#0p=<%02#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=K%02#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00@Mg00@lR3P0g00AJP1g00Ajf5f4f3f2R1f1R0P2M<Gp=:g00BL#0#9#8R4%04#9#<#8#K#1#1#1#1#1#1#1#1#1#1#1R5'6g00BkR6#2#3#3#5R7%36#2#2#2#3#2#3#2#5R6';R8P4P71437P5P61436E:g00CPR5#J%I5%H3%D3%C3R5g00D<g00D[R4P4g00E;R4P31737g00E[1736C@g00FBFA1B54P2P1g00FbR4g00GBR5'41?21=>45dg00Gb=E30C=b1b2b3P8P2b0CFg00H@g00MA'6eo"). Qed.
Definition startup_shapeD : shape := SCase (EVar 5) 524277 (SHole 0) (SHole 0).

(* [comment removed for export] *)
Definition IT2 : itab := mk_itab_ranges ASEGS startup2_plan_ranges.
Lemma IT2_ok : itab_sound ASEGS IT2.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCertDefs ()) [] "p;2g0000j20Tg001>g00N9'0o"). Qed.
Definition NXS2 : nat := 453%nat.
Lemma NXS2_ge : (NX0 <= NXS2)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanCertDefs ()) [] "h07__arithh14__ffh28__varmaph35__witp;1p;2p;4p;7p;3p;<g004Tj10Tg0053R0j27Tg005Mj13Tg0062j12Tg006Wj18Tg0075R1j2=Tg007Qj24Tg007kj1:Tg008Kj1JTg008kj1ITg009Ij1HTg009gj1FTg00:Rj26Tg00;5j4ETg00;`j7CTg00<Dj2BTg00<fj2ATg00=Rj3@Tg00=lj3?Tg00>Kj4DTg00?=j4>Tg00?hl<GTf0R2#0#0p=9%02#0#0#0#0#0#0#0p=5%02#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=<%02#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00@Mg00@lR3P0g00AJP1g00Ajf5f4f3f2R1f1R0P2M<Gp=;g00BL#0#9#5R4%94#5#<#1#1#1#1#1#1#1#1#1#1#1#1#1R5'7g00BkR6#3#2#2#8R7%26#2#3#3#3#2#3#2#8R6'=R8P4P71437P5P61436E;g00CPR5#:%J5%I3%H3%F3R5g00D<g00D[R4P4g00E;R4P31637g00E[1636CEg00FBFC1B54P2P1g00FbR4g00GBR5'41A21=@45dg00Gb=?30CDb1b2b3P8P2b0C>g00H@g00OF'7eo"). Qed.
(* [comment removed for export] *)
Definition startup2_shape : shape := SCase (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 344))) 3935) 4030 (SHole 1) (SHole 2).

From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
