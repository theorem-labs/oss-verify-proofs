(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require ZeroObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require MuslWLA DrvGlueB.

(* [comment removed for export] *)
Module Icpt_region_proof.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "pow"; "modulo"; "sub"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "holds"; "eval"; "rw"; "ss_facts"; "valuation"; "SLit"; "SVar"; "sprop_below"; "ss_next"; "SPAlign"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub_id_below"; "wsub"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "cur"; "add"; "F_E"; "F_P"; "F_W"; "g8"; "s_Eb"; "s_Ee"; "s_Pb"; "s_Pe"; "s_Wb"; "s_We"; "C0"; "E_Eb"; "E_Ee"; "CE_0"; "CP_0"; "CW_0"; "E_Pb"; "E_Pe"; "E_Wb"; "E_We"; "F_ab"; "F_ae"; "P_ret"; "base_facts"; "g_facts"; "gd"; "gu"; "pab"; "shp"; "vB"; "vL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "cons"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "SHB"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof"; "Posts_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof.Z"; "baseZ"; "gZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue MuslWL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgGlueA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import RegionAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Local Notation "'UU' rho e" := (bv_unsigned (eval rho e)) (at level 10, rho at level 9, e at level 9).

Lemma U_var : ltac2:(tb__ "0|1|
S13SdS9ScS0Q40M0S10R2S15R1A1A2A2S0G0S11R2R1A2A2A3Fv;Frho;").
Proof. reflexivity. Qed.

Lemma U_g8 : ltac2:(tb__ "0|1|
S13SdS4S0Q40M0S11R2R1A2A2S6Z2Z3dA2A2S9ScS0G0S10R3S23S15R2A1A1A2A2S5Z8S0G0S11R3R2A2A2A2A3F_;Fv;Frho;").
Proof.
  intros rho v Hv. unfold g8. cbn [eval]. rewrite sll_val. change (3 mod 64) with 3.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (urange (rw rho v)). rewrite Z.mod_small by lia. lia.
Qed.

Lemma U_shp : ltac2:(tb__ "0|1|
S13SdS4S0Q40M0S11R2R1A2A2S6Z2Z3eA2A2S9ScS0G0S10R3S3cS15R2A1A1A2A2S3S0G0S11R3R2A2A2S49A2A3F_;Fv;Frho;").
Proof.
  intros rho v Hv. unfold shp, add, shb. pose proof (urange (rw rho v)).
  apply (U_addc rho (SVar v) SHB); [reflexivity | unfold SHB; lia | unfold SHB; lia].
Qed.

Ltac have_fact H HF f := pose proof (proj1 (Forall_forall _ _) HF f ltac:(cbn; tauto)) as H; cbn [holds] in H.

Section Z.
Variable rho : valuation.
Let B := bv_unsigned (rw rho 15). Let L := bv_unsigned (rw rho 16). Let O := bv_unsigned (rw rho 17). Let N := bv_unsigned (rw rho 18).
Let gu := bv_unsigned (rw rho 120). Let gd := bv_unsigned (rw rho 121).

Definition baseZ : Prop := ltac2:(tb__ "0|1|
SaS2S3VO;VN;A2VL;A2SaS2VL;S6Z2M0Z28A2A2SaS2Z1VN;A2SaS2Z1000VB;A2S2S3VB;VL;A2S8S6G0Z2fA2Z8A2A2A2A2A2A2").
Definition gZ : Prop := ltac2:(tb__ "0|3|
SaS2VB;S5Z8M0Vgu;A2A2SaS2VB;S5G0Vgd;A2M1A2SaS2G1S3VB;VL;A2A2SaS4Vgu;S6Z2Z3dA2M2A2SaS4Vgd;G2A2S2G1S3S3VB;VO;A2VN;A2A2A2A2A2A2A2").

Lemma base_facts_Z : ltac2:(tb__ "0|1|
S19SeSfVrho;A1M0S38A3S19SeG0S37A3SaS51S52A2F_;F_;").
Proof.
  intros HG HB.
  pose proof (urange (rw rho 15)) as R15. pose proof (urange (rw rho 16)) as R16. pose proof (urange (rw rho 17)) as R17.
  pose proof (urange (rw rho 18)) as R18. pose proof (urange (rw rho 120)) as R52. pose proof (urange (rw rho 121)) as R53.
  have_fact A1 HB (SPUle (add vO vN) vL). have_fact A2 HB (SPUle vL (SLit (2 ^ 40))). have_fact A3 HB (SPUle (SLit 1) vN).
  have_fact A4 HB (SPUle (SLit 4096) vB). have_fact A5 HB (SPUle (add vB vL) (SLit (2 ^ 47 - 8))).
  have_fact A6 HB (SPUle vO vL). have_fact A7 HB (SPUle vN vL). have_fact A8 HB (SPUle vB (SLit (2 ^ 47 - 8))).
  have_fact G1 HG (SPUle vB (g8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gu)). have_fact G2 HG (SPUle vB (g8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gd)). have_fact G3 HG (SPUle (g8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gd) (add vB vL)).
  have_fact G4 HG (SPUle OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gu (SLit (2 ^ 61 - 1))). have_fact G5 HG (SPUle OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gd (SLit (2 ^ 61 - 1))).
  have_fact G6 HG (SPUle (g8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gd) endd).
  unfold vB, vL, vO, vN, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gu, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gd, add in *.

  rewrite (U_lit64 rho (2 ^ 40)) in A2 by lia. rewrite (U_lit64 rho 1) in A3 by lia.
  rewrite (U_lit64 rho 4096) in A4 by lia.
  pose proof (U_lit64 rho (2 ^ 47 - 8) ltac:(lia)) as T47. rewrite T47 in A5. rewrite T47 in A8.
  rewrite (U_lit64 rho (2 ^ 61 - 1)) in G4, G5 by lia.
  cbn [eval] in A2, A3, A4, A6, A7, A8, G4, G5. unfold HSE, ACEIL in *.

  assert (B1718 : 0 <= bv_unsigned (rw rho 17) + bv_unsigned (rw rho 18) < 2 ^ 64) by lia.
  assert (B52 : bv_unsigned (rw rho 120) < 2 ^ 61) by lia. assert (B53 : bv_unsigned (rw rho 121) < 2 ^ 61) by lia.
  rewrite (U_add2 rho (SVar 17) (SVar 18) (bv_unsigned (rw rho 17)) (bv_unsigned (rw rho 18)) eq_refl eq_refl B1718) in A1.
  rewrite (U_g8 rho 120 B52) in G1. rewrite (U_g8 rho 121 B53) in G2, G3, G6.
  cbn [eval] in A1, G1, G2.
  assert (B1516 : 0 <= bv_unsigned (rw rho 15) + bv_unsigned (rw rho 16) < 2 ^ 64) by (clear -R15 R16 A2 A8; lia).
  rewrite (U_add2 rho (SVar 15) (SVar 16) (bv_unsigned (rw rho 15)) (bv_unsigned (rw rho 16)) eq_refl eq_refl B1516) in A5, G3.
  assert (EE : bv_unsigned (eval rho endd) = bv_unsigned (rw rho 18) + (bv_unsigned (rw rho 15) + bv_unsigned (rw rho 17))).
  { unfold endd, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.beg, add, vB, vO, vN.
    apply U_add2; [reflexivity | | lia]. apply U_add2; [reflexivity | reflexivity | lia]. }
  rewrite EE in G6.
  unfold baseZ, gZ. subst B L O N gu gd. unfold HSE, ACEIL. repeat split; lia.
Qed.
End Z.

Lemma rw_sub : ltac2:(tb__ "0|0|
S13S1cSdS9S1Q40A1S11S1aR3R2A2R1A2S10R3S1dR2R1A2A2A3Fi;Fs;Frho;").
Proof. reflexivity. Qed.

Ltac zz := cbn [holds eval cur pab pae cnt OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gu OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gd vB vL vO vN].
Ltac zzh H := cbn [holds eval cur pab pae cnt OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gu OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gd vB vL vO vN] in H.

Section Intro.
Variable rho' : valuation.
Variables B L gu gd p c r : Z.
Hypothesis E15 : ltac2:(tb__ "0|0|
S9ScS0Q40S11Vrho';PfA2A2VB;A3").
Hypothesis E16 : ltac2:(tb__ "0|0|
S9ScS0Q40S11Vrho';P10A2A2VL;A3").
Hypothesis E52 : ltac2:(tb__ "0|0|
S9ScS0Q40S11Vrho';P78A2A2Vgu;A3").
Hypothesis E53 : ltac2:(tb__ "0|0|
S9ScS0Q40S11Vrho';P79A2A2Vgd;A3").
Hypothesis E103 : ltac2:(tb__ "0|0|
S9ScS0Q40S11Vrho';P8eA2A2Vc;A3").
Hypothesis HBL : ltac2:(tb__ "0|0|
S4S3VB;VL;A2S6Z2Z3fA2A2").
Hypothesis Hc : c < 2 ^ 61.

Lemma Ug8c : ltac2:(tb__ "0|0|
S9ScS0Q40S10Vrho';S23S1eA1A2A2S5Z8Vc;A2A3").
Proof using E103 Hc. unfold cur. rewrite U_g8; [lia|]. rewrite E103. exact Hc. Qed.
Lemma Ug8ck : ltac2:(tb__ "0|1|
ScS2Z0R1A2S4S3S5Z8Vc;A2M0R2A2S6Z2Z40A2A2S9ScS0Q40S10Vrho';S1fS23S1eA1S14R3A1A2A2A2S3G0R3A2A3F_;F_;Fk;").
Proof using E103 Hc. intros k Hk Hk'. unfold add. pose proof (urange (rw rho' 142)). apply (U_addc rho' (g8 cur) k (8 * c) Ug8c); lia. Qed.
Lemma UBL : ltac2:(tb__ "0|0|
S9ScS0Q40S10Vrho';S1fS3dS3eA2A2A2S3VB;VL;A2A3").
Proof using E15 E16 HBL. unfold add, vB, vL. pose proof (urange (rw rho' 15)). pose proof (urange (rw rho' 16)).
  apply U_add2; [exact E15 | exact E16 | lia]. Qed.

Lemma F_P_intro : ltac2:(tb__ "0|2|
S9ScS0Q40S11Vrho';P8cA2A2Vp;A3S2VB;S5Z8M0Vc;A2M1A2S2S3G1G0A2S3VB;VL;A2A2S2Vgu;Vc;A2S4Vc;Vp;A2S4Vc;Vgd;A2S19SeSfVrho';A1S21A3F_;F_;F_;F_;F_;F_;").
Proof using E15 E16 E52 E53 E103 HBL Hc.
  intros E101 H1 H2 H3 H4 H5. unfold F_P.
  constructor. { cbn [holds]. rewrite Ug8c. change (eval rho' vB) with (rw rho' 15). lia. }
  constructor. { cbn [holds]. rewrite (Ug8ck 8) by lia. rewrite UBL. lia. }
  constructor. { cbn [holds]. reflexivity. }
  constructor. { cbn [holds]. rewrite (U_lit64 rho' (2 ^ 61 - 1)) by lia. change (eval rho' cur) with (rw rho' 142). lia. }
  constructor. { zz. lia. }
  constructor. { zz. lia. }
  constructor. { zz. lia. }
  constructor.
Qed.

Lemma F_W_intro : ltac2:(tb__ "0|2|
S9ScS0Q40S11Vrho';P8dA2A2Vp;A3S2VB;S5Z8M0Vc;A2M1A2S2S3G1Z40A2S3VB;VL;A2A2S2Vgu;Vc;A2S4Vc;Vp;A2S9ScS7Vc;G0A2Z0A3S4Vc;Vgd;A2S19SeSfVrho';A1S22A3F_;F_;F_;F_;F_;F_;F_;").
Proof using E15 E16 E52 E53 E103 HBL Hc.
  intros E102 H1 H2 H3 H4 H5 H6. unfold F_W.
  constructor. { cbn [holds]. rewrite Ug8c. change (eval rho' vB) with (rw rho' 15). lia. }
  constructor. { cbn [holds]. rewrite (Ug8ck 64) by lia. rewrite UBL. lia. }
  constructor. { cbn [holds]. reflexivity. }
  constructor. { cbn [holds]. rewrite (U_lit64 rho' (2 ^ 61 - 1)) by lia. change (eval rho' cur) with (rw rho' 142). lia. }
  constructor. { zz. lia. }
  constructor. { zz. lia. }
  constructor. { cbn [holds]. split; [lia|]. change (2 ^ 3) with 8. rewrite E103. exact H5. }
  constructor. { zz. lia. }
  constructor.
Qed.

Lemma F_E_intro : ltac2:(tb__ "0|2|
S9ScS0Q40S11Vrho';P8fA2A2Vr;A3S2VB;S5Z8M0Vc;A2M1A2S2S3G1G0A2S3VB;VL;A2A2S9ScS3Vc;Vr;A2Vgd;A3S2Z1Vr;A2S2Vr;Z7A2S19SeSfVrho';A1S20A3F_;F_;F_;F_;F_;F_;").
Proof using E15 E16 E52 E53 E103 HBL Hc.
  intros E104 H1 H2 H3 H4 H5. unfold F_E.
  assert (Ucr : bv_unsigned (eval rho' (add cur cnt)) = c + r).
  { unfold add, cur, cnt. pose proof (urange (rw rho' 142)). apply U_add2; [exact E103 | exact E104 | lia]. }
  constructor. { cbn [holds]. rewrite Ug8c. change (eval rho' vB) with (rw rho' 15). lia. }
  constructor. { cbn [holds]. rewrite (Ug8ck 8) by lia. rewrite UBL. lia. }
  constructor. { cbn [holds]. reflexivity. }
  constructor. { cbn [holds]. rewrite (U_lit64 rho' (2 ^ 61 - 1)) by lia. change (eval rho' cur) with (rw rho' 142). lia. }
  constructor. { cbn [holds]. rewrite Ucr. change (eval rho' OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gd) with (rw rho' 121). lia. }
  constructor. { cbn [holds]. rewrite Ucr. change (eval rho' OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gd) with (rw rho' 121). lia. }
  constructor. { cbn [holds]. rewrite (U_lit64 rho' 1) by lia. change (eval rho' cnt) with (rw rho' 143). lia. }
  constructor. { cbn [holds]. rewrite (U_lit64 rho' 7) by lia. change (eval rho' cnt) with (rw rho' 143). lia. }
  constructor. { zz. lia. }
  constructor.
Qed.
End Intro.

Lemma align8_of : ltac2:(tb__ "0|0|
S13SdSfR2S18R1Z3A2A2SbScScS9ScS0Q40S11R4R3A2A2S5Z8R1A2A3Lk;A2F_;Fv;Frho;").
Proof.
  intros rho v [_ H]. change (2 ^ 3) with 8 in H. exists (bv_unsigned (rw rho v) / 8).
  pose proof (Z.div_mod (bv_unsigned (rw rho v)) 8 ltac:(lia)). lia.
Qed.

Ltac split_facts HF HX HG HB :=
  cbn [ax_S ss_facts miz_state mkA] in HF;
  apply Forall_app in HF as [HX HF]; apply Forall_app in HF as [HG HB].

Section Glue.
Variable rho : valuation.
Let B := bv_unsigned (rw rho 15). Let L := bv_unsigned (rw rho 16). Let O := bv_unsigned (rw rho 17). Let N := bv_unsigned (rw rho 18).
Let gu := bv_unsigned (rw rho 120). Let gd := bv_unsigned (rw rho 121).
Let pab := bv_unsigned (rw rho 140). Let pae := bv_unsigned (rw rho 141).
Let c := bv_unsigned (rw rho 142). Let r := bv_unsigned (rw rho 143).

Lemma F_ab_Z : ltac2:(tb__ "0|0|
S4Vgu;S6Z2Z3dA2A2S19SeSfVrho;A1S34A3SaS2Vpab;S3Vgu;Z7A2A2SaS2Vgu;Vpab;A2SbScScS9ScVpab;S5Z8R1A2A3Lk;A2A2A2F_;F_;").
Proof.
  intros Hgu HF. pose proof (urange (rw rho 140)) as R101. pose proof (urange (rw rho 120)) as R52.
  have_fact A1 HF (SPUle OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.pab (add OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gu (SLit 7))).
  have_fact A2 HF (SPUle (add OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gu (SLit 7)) (add OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.pab (SLit 7))).
  have_fact A3 HF (SPAlign 140 3).
  unfold add in A1, A2.
  pose proof (U_addc rho OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gu 7 (bv_unsigned (rw rho 120)) eq_refl ltac:(lia) ltac:(lia)) as T1. rewrite T1 in A1, A2.
  change (eval rho OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.pab) with (rw rho 140) in A1.
  pose proof (U_addc rho OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.pab 7 (bv_unsigned (rw rho 140)) eq_refl ltac:(subst; lia) ltac:(lia)) as T2. rewrite T2 in A2.
  destruct (align8_of rho 140 A3) as [k Hk]. subst pab gu. split; [lia|]. split; [lia|]. exists k. exact Hk.
Qed.

Lemma F_ae_Z : ltac2:(tb__ "0|0|
S4Vgd;S6Z2Z3dA2A2S19SeSfVrho;A1S35A3SaS2Vpae;Vgd;A2SaS2Vgd;S3Vpae;Z7A2A2SbScScS9ScVpae;S5Z8R1A2A3Lk;A2A2A2F_;F_;").
Proof.
  intros Hgd HF. pose proof (urange (rw rho 141)) as R102. pose proof (urange (rw rho 121)) as R53.
  have_fact A1 HF (SPUle OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.pae OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gd).
  have_fact A2 HF (SPUle OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gd (add OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.pae (SLit 7))).
  have_fact A3 HF (SPAlign 141 3).
  change (eval rho OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.pae) with (rw rho 141) in A1. change (eval rho OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gd) with (rw rho 121) in A1, A2.
  unfold add in A2. pose proof (U_addc rho OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.pae 7 (bv_unsigned (rw rho 141)) eq_refl ltac:(lia) ltac:(lia)) as T1. rewrite T1 in A2.
  destruct (align8_of rho 141 A3) as [k Hk]. subst pae gd. split; [lia|]. split; [lia|]. exists k. exact Hk.
Qed.

Lemma glue_Pe : ltac2:(tb__ "0|0|
S19SeSfVrho;A1S12S3fS31A1A1A3S19SeSfS1aVrho;S27A2A1S21A3F_;").
Proof.
  intros HF. unfold E_Pe in HF. split_facts HF HX HG HB.
  destruct (base_facts_Z rho HG HB) as [(Z1 & Z2 & Z3 & Z4 & Z5) (Y1 & Y2 & Y3 & Y4 & Y5 & Y6)].
  apply Forall_app in HX as [HAB HX]. apply Forall_app in HX as [HAE HX].
  destruct (F_ab_Z Y4 HAB) as (P1 & P2 & _).
  have_fact X1 HX (SPUlt OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gu OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gd). have_fact X2 HX (SPUlt OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gu OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.pab). zzh X1. zzh X2.
  assert (W103 : wsub_get s_Pe 142 = SVar 120) by (pose proof s_Pe_vals as V; cbn [map] in V; congruence).
  assert (W101 : wsub_get s_Pe 140 = SVar 140) by (pose proof s_Pe_vals as V; cbn [map] in V; congruence).
  assert (W120 : wsub_get s_Pe 120 = SVar 120) by (pose proof s_Pe_vals as V; cbn [map] in V; congruence).
  assert (W121 : wsub_get s_Pe 121 = SVar 121) by (pose proof s_Pe_vals as V; cbn [map] in V; congruence).
  pose proof (proj1 (s_glob 15 eq_refl)) as W15. pose proof (proj1 (s_glob 16 eq_refl)) as W16.
  apply (F_P_intro (rho_sub rho s_Pe) B L gu gd pab gu);
    [ rewrite rw_sub, W15; reflexivity | rewrite rw_sub, W16; reflexivity | rewrite rw_sub, W120; reflexivity
    | rewrite rw_sub, W121; reflexivity | rewrite rw_sub, W103; reflexivity | | | rewrite rw_sub, W101; reflexivity | idtac ..];
    unfold ACEIL in *; subst; lia.
Qed.

Lemma glue_Pb : ltac2:(tb__ "0|0|
S19SeSfVrho;A1S12S3fS30A1A1A3S19SeSfS1aVrho;S26A2A1S21A3F_;").
Proof.
  intros HF. unfold E_Pb in HF. split_facts HF HX HG HB.
  destruct (base_facts_Z rho HG HB) as [(Z1 & Z2 & Z3 & Z4 & Z5) (Y1 & Y2 & Y3 & Y4 & Y5 & Y6)].
  apply Forall_app in HX as [HP HX]. apply Forall_app in HX as [HAB HX]. apply Forall_app in HX as [HAE HX].
  destruct (F_ab_Z Y4 HAB) as (P1 & P2 & _). destruct (F_ae_Z Y5 HAE) as (Q1 & Q2 & _).
  pose proof (urange (rw rho 142)) as R103. pose proof (urange (rw rho 140)) as R101.
  have_fact Hf1 HP (SPUle vB (g8 cur)). have_fact Hf3 HP (SPUle OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gu cur).
  have_fact Hf4 HP (SPUlt cur OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.pab). have_fact Hf5 HP (SPUlt cur OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gd). zzh Hf3. zzh Hf4. zzh Hf5.
  assert (Hc : bv_unsigned (rw rho 142) < 2 ^ 61) by lia.
  unfold cur in Hf1. rewrite (U_g8 rho 142 Hc) in Hf1. change (eval rho vB) with (rw rho 15) in Hf1.
  have_fact X1 HX (SPUlt (add cur (SLit 1)) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.pab). have_fact X2 HX (SPUlt (add cur (SLit 1)) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gd).
  unfold add in X1, X2. pose proof (U_addc rho cur 1 (bv_unsigned (rw rho 142)) eq_refl ltac:(lia) ltac:(lia)) as T1. rewrite T1 in X1, X2. zzh X1. zzh X2.
  apply (F_P_intro (rho_sub rho s_Pb) B L gu gd pab (c + 1)); try (rewrite rw_sub; reflexivity); unfold ACEIL in *.
  - rewrite rw_sub. cbn [wsub_get s_Pb Pos.eqb]. unfold add. subst c. apply (U_addc rho cur 1 (bv_unsigned (rw rho 142)) eq_refl); lia.
  - subst; lia. - subst; lia. - subst; lia. - subst; lia. - subst; lia. - subst; lia. - subst; lia.
Qed.

Lemma glue_We : ltac2:(tb__ "0|0|
S19SeSfVrho;A1S12S3fS33A1A1A3S19SeSfS1aVrho;S29A2A1S22A3F_;").
Proof.
  intros HF. unfold E_We in HF. split_facts HF HX HG HB.
  destruct (base_facts_Z rho HG HB) as [(Z1 & Z2 & Z3 & Z4 & Z5) (Y1 & Y2 & Y3 & Y4 & Y5 & Y6)].
  apply Forall_app in HX as [HAB HX]. apply Forall_app in HX as [HAE HX].
  destruct (F_ab_Z Y4 HAB) as (P1 & P2 & [k Hk]). destruct (F_ae_Z Y5 HAE) as (Q1 & Q2 & [k' Hk']).
  have_fact X1 HX (SPUlt OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.pab OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.pae). zzh X1.
  assert (W103 : wsub_get s_We 142 = SVar 140) by (pose proof s_We_vals as V; cbn [map] in V; congruence).
  assert (W102 : wsub_get s_We 141 = SVar 141) by (pose proof s_We_vals as V; cbn [map] in V; congruence).
  assert (W120 : wsub_get s_We 120 = SVar 120) by (pose proof s_We_vals as V; cbn [map] in V; congruence).
  assert (W121 : wsub_get s_We 121 = SVar 121) by (pose proof s_We_vals as V; cbn [map] in V; congruence).
  pose proof (proj1 (proj2 (s_glob 15 eq_refl))) as W15. pose proof (proj1 (proj2 (s_glob 16 eq_refl))) as W16.
  apply (F_W_intro (rho_sub rho s_We) B L gu gd pae pab);
    [ rewrite rw_sub, W15; reflexivity | rewrite rw_sub, W16; reflexivity | rewrite rw_sub, W120; reflexivity
    | rewrite rw_sub, W121; reflexivity | rewrite rw_sub, W103; reflexivity | | | rewrite rw_sub, W102; reflexivity | idtac ..];
    unfold ACEIL in *; subst; first [lia | rewrite Z.mul_comm; apply Z_mod_mult].
Qed.

Lemma glue_Wb : ltac2:(tb__ "0|0|
S19SeSfVrho;A1S12S3fS32A1A1A3S19SeSfS1aVrho;S28A2A1S22A3F_;").
Proof.
  intros HF. unfold E_Wb in HF. split_facts HF HX HG HB.
  destruct (base_facts_Z rho HG HB) as [(Z1 & Z2 & Z3 & Z4 & Z5) (Y1 & Y2 & Y3 & Y4 & Y5 & Y6)].
  apply Forall_app in HX as [HW HX]. apply Forall_app in HX as [HAB HX]. apply Forall_app in HX as [HAE HX].
  destruct (F_ae_Z Y5 HAE) as (Q1 & Q2 & [k' Hk']).
  pose proof (urange (rw rho 142)) as R103. pose proof (urange (rw rho 141)) as R102.
  have_fact Hf1 HW (SPUle vB (g8 cur)). have_fact Hf3 HW (SPUle OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gu cur).
  have_fact Hf4 HW (SPUlt cur OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.pae). have_fact Hf5 HW (SPAlign 142 3). zzh Hf3. zzh Hf4.
  destruct (align8_of rho 142 Hf5) as [k Hk].
  assert (Hc : bv_unsigned (rw rho 142) < 2 ^ 61) by lia.
  unfold cur in Hf1. rewrite (U_g8 rho 142 Hc) in Hf1. change (eval rho vB) with (rw rho 15) in Hf1.
  have_fact X1 HX (SPUlt (add cur (SLit 8)) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.pae).
  unfold add in X1. pose proof (U_addc rho cur 8 (bv_unsigned (rw rho 142)) eq_refl ltac:(lia) ltac:(lia)) as T1. rewrite T1 in X1. zzh X1.
  apply (F_W_intro (rho_sub rho s_Wb) B L gu gd pae (c + 8)); try (rewrite rw_sub; reflexivity); unfold ACEIL in *.
  1:{ rewrite rw_sub. cbn [wsub_get s_Wb Pos.eqb]. unfold add. subst c. apply (U_addc rho cur 8 (bv_unsigned (rw rho 142)) eq_refl); lia. }
  all: (subst; lia).
Qed.

Lemma glue_Ee : ltac2:(tb__ "0|0|
S19SeSfVrho;A1S12S3fS2cA1A1A3S19SeSfS1aVrho;S25A2A1S20A3F_;").
Proof.
  intros HF. unfold E_Ee in HF. split_facts HF HX HG HB.
  destruct (base_facts_Z rho HG HB) as [(Z1 & Z2 & Z3 & Z4 & Z5) (Y1 & Y2 & Y3 & Y4 & Y5 & Y6)].
  apply Forall_app in HX as [HAE HX].
  destruct (F_ae_Z Y5 HAE) as (Q1 & Q2 & _).
  pose proof (urange (rw rho 141)) as R102.
  have_fact X1 HX (SPUlt OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.pae OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gd). have_fact X2 HX (SPUle OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gu OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.pae). zzh X1. zzh X2.
  assert (W103 : wsub_get s_Ee 142 = SVar 141) by (pose proof s_Ee_vals as V; cbn [map] in V; congruence).
  assert (W104 : wsub_get s_Ee 143 = SAlu ALU_SUB (shp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gd) (shp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.pae)) by (pose proof s_Ee_vals as V; cbn [map] in V; congruence).
  assert (W102 : wsub_get s_Ee 141 = SVar 141) by (pose proof s_Ee_vals as V; cbn [map] in V; congruence).
  assert (W120 : wsub_get s_Ee 120 = SVar 120) by (pose proof s_Ee_vals as V; cbn [map] in V; congruence).
  assert (W121 : wsub_get s_Ee 121 = SVar 121) by (pose proof s_Ee_vals as V; cbn [map] in V; congruence).
  pose proof (proj2 (proj2 (s_glob 15 eq_refl))) as W15. pose proof (proj2 (proj2 (s_glob 16 eq_refl))) as W16.
  apply (F_E_intro (rho_sub rho s_Ee) B L gu gd pae (gd - pae));
    [ rewrite rw_sub, W15; reflexivity | rewrite rw_sub, W16; reflexivity | rewrite rw_sub, W120; reflexivity
    | rewrite rw_sub, W121; reflexivity | rewrite rw_sub, W103; reflexivity | idtac ..]; unfold ACEIL in *.
  - subst; lia. - subst; lia.
  - rewrite rw_sub, W104. subst gd pae. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gd, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.pae.
    pose proof (U_sub2 rho (shp (SVar 121)) (shp (SVar 141)) (bv_unsigned (rw rho 121) + SHB) (bv_unsigned (rw rho 141) + SHB)
                  (U_shp rho 121 ltac:(lia)) (U_shp rho 141 ltac:(lia)) ltac:(lia)) as T3.
    rewrite T3. lia.
  - subst; lia. - subst; lia. - subst; lia. - subst; lia. - subst; lia.
Qed.

Lemma glue_Eb : ltac2:(tb__ "0|0|
S19SeSfVrho;A1S12S3fS2bA1A1A3S19SeSfS1aVrho;S24A2A1S20A3F_;").
Proof.
  intros HF. unfold E_Eb in HF. split_facts HF HX HG HB.
  destruct (base_facts_Z rho HG HB) as [(Z1 & Z2 & Z3 & Z4 & Z5) (Y1 & Y2 & Y3 & Y4 & Y5 & Y6)].
  apply Forall_app in HX as [HE HX]. apply Forall_app in HX as [HAE HX].
  pose proof (urange (rw rho 142)) as R103. pose proof (urange (rw rho 143)) as R104.
  have_fact Hf1 HE (SPUle vB (g8 cur)). have_fact Hf5 HE (SPUle (add cur cnt) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gd). have_fact Hf6 HE (SPUle OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gd (add cur cnt)).
  have_fact Hf7 HE (SPUle (SLit 1) cnt). have_fact Hf8 HE (SPUle cnt (SLit 7)). have_fact Hf9 HE (SPUlt cur OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gd).
  rewrite (U_lit64 rho 1) in Hf7 by lia. rewrite (U_lit64 rho 7) in Hf8 by lia. zzh Hf7. zzh Hf8. zzh Hf9.
  assert (Hc : bv_unsigned (rw rho 142) < 2 ^ 61) by lia.
  unfold cur in Hf1. rewrite (U_g8 rho 142 Hc) in Hf1. change (eval rho vB) with (rw rho 15) in Hf1.
  unfold add in Hf5, Hf6. pose proof (U_add2 rho cur cnt (bv_unsigned (rw rho 142)) (bv_unsigned (rw rho 143)) eq_refl eq_refl ltac:(lia)) as T1. rewrite T1 in Hf5, Hf6.
  change (eval rho OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gd) with (rw rho 121) in Hf5, Hf6.
  have_fact X1 HX (SPBranch BC_NE (add cnt (SLit (-1))) (SLit 0)).
  cbn [holds branch_taken] in X1. unfold bv_eqb in X1. apply negb_true_iff in X1. apply Z.eqb_neq in X1.
  unfold add in X1. pose proof (U_addc rho cnt (-1) (bv_unsigned (rw rho 143)) eq_refl ltac:(lia) ltac:(lia)) as T2. rewrite T2 in X1.
  rewrite (U_lit64 rho 0) in X1 by lia.
  apply (F_E_intro (rho_sub rho s_Eb) B L gu gd (c + 1) (r - 1)); try (rewrite rw_sub; reflexivity); unfold ACEIL in *.
  - rewrite rw_sub. cbn [wsub_get s_Eb Pos.eqb]. unfold add. subst c. apply (U_addc rho cur 1 (bv_unsigned (rw rho 142)) eq_refl); lia.
  - subst; lia. - subst; lia.
  - rewrite rw_sub. cbn [wsub_get s_Eb Pos.eqb]. unfold add. subst r. apply (U_addc rho cnt (-1) (bv_unsigned (rw rho 143)) eq_refl); lia.
  - subst; lia. - subst; lia. - subst; lia. - subst; lia. - subst; lia.
Qed.
End Glue.

Definition Posts_rip : list leafA := ltac2:(tb__ "0|0|
S46S40S41S36S56A2S47S40A1A3").

Lemma F_P_below : ltac2:(tb__ "0|0|
S9S43S4aSeS16S17S3fS2eA1A1A1S21A3S44A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F_W_below : ltac2:(tb__ "0|0|
S9S43S4aSeS16S17S3fS2fA1A1A1S22A3S44A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F_E_below : ltac2:(tb__ "0|0|
S9S43S4aSeS16S17S3fS2dA1A1A1S20A3S44A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma ids_rip6 : ltac2:(tb__ "0|0|
SaS9S43S1bS27S42A2S44A3SaS9S43S1bS26S42A2S44A3SaS9S43S1bS29S42A2S44A3SaS9S43S1bS28S42A2S44A3SaS9S43S1bS25S42A2S44A3S9S43S1bS24S42A2S44A3A2A2A2A2A2").
Proof.
  pose proof ids_rip as H.
  apply andb_prop in H as [H I6]. apply andb_prop in H as [H I5]. apply andb_prop in H as [H I4].
  apply andb_prop in H as [H I3]. apply andb_prop in H as [I1 I2].
  exact (conj I1 (conj I2 (conj I3 (conj I4 (conj I5 I6))))).
Qed.

Theorem region_B_sum : ltac2:(tb__ "0|0|
S55OF_;S4eS13S45S1Q40A1A1S50S48R4R3A3S4fS48S42R4A3S54S48R6S4dS48R5S2aR4R3A5S4cS48R5S42R4R3S4bA6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  destruct ids_rip6 as (I1 & I2 & I3 & I4 & I5 & I6).
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF C0 rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUEL cutpcs_rip NF cuts_rip exits_rip (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_rip) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - exact HstG.
  - exact check_rip.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]].
    + apply exit_postA. in_nth 0.
    + apply (exit_reenterA segs ok _ NF cuts_rip _ E_Pe CP_0 F_P s_Pe tp);
        [in_nth 1 | exact ent_Pe | exact I1 | exact HstG | exact F_P_below | intros r tp' tr md _ HF; exact (glue_Pe r HF)].
    + apply (exit_reenterA segs ok _ NF cuts_rip _ E_Pb CP_0 F_P s_Pb tp);
        [in_nth 1 | exact ent_Pb | exact I2 | exact HstG | exact F_P_below | intros r tp' tr md _ HF; exact (glue_Pb r HF)].
    + apply (exit_reenterA segs ok _ NF cuts_rip _ E_We CW_0 F_W s_We tp);
        [in_nth 2 | exact ent_We | exact I3 | exact HstG | exact F_W_below | intros r tp' tr md _ HF; exact (glue_We r HF)].
    + apply (exit_reenterA segs ok _ NF cuts_rip _ E_Wb CW_0 F_W s_Wb tp);
        [in_nth 2 | exact ent_Wb | exact I4 | exact HstG | exact F_W_below | intros r tp' tr md _ HF; exact (glue_Wb r HF)].
    + apply (exit_reenterA segs ok _ NF cuts_rip _ E_Ee CE_0 F_E s_Ee tp);
        [in_nth 3 | exact ent_Ee | exact I5 | exact HstG | exact F_E_below | intros r tp' tr md _ HF; exact (glue_Ee r HF)].
    + apply (exit_reenterA segs ok _ NF cuts_rip _ E_Eb CE_0 F_E s_Eb tp);
        [in_nth 3 | exact ent_Eb | exact I6 | exact HstG | exact F_E_below | intros r tp' tr md _ HF; exact (glue_Eb r HF)].
  - left; reflexivity.
Qed.

Section GlueMeas.
Variable rho : valuation.

Lemma meas_Pe : ltac2:(tb__ "0|1|
S2S0Q40M0S10Vrho;S3aA2A2S0G0S10S1aVrho;S27A2S1eA2A2A2").
Proof.
  assert (W103 : wsub_get s_Pe 142 = SVar 120) by (pose proof s_Pe_vals as V; cbn [map] in V; congruence).
  unfold cur. cbn [eval]. rewrite rw_sub, W103. cbn [eval]. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gu. cbn [eval]. lia.
Qed.
Lemma meas_Pb : ltac2:(tb__ "0|1|
S2S0Q40M0S10Vrho;S1fS1eS14Z1A1A2A2A2S0G0S10S1aVrho;S26A2S1eA2A2A2").
Proof. unfold cur at 2. cbn [eval]. rewrite rw_sub. cbn [wsub_get s_Pb Pos.eqb]. lia. Qed.
Lemma meas_We : ltac2:(tb__ "0|1|
S2S0Q40M0S10Vrho;S3bA2A2S0G0S10S1aVrho;S29A2S1eA2A2A2").
Proof.
  assert (W103 : wsub_get s_We 142 = SVar 140) by (pose proof s_We_vals as V; cbn [map] in V; congruence).
  unfold cur. cbn [eval]. rewrite rw_sub, W103. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.pab. lia.
Qed.
Lemma meas_Wb : ltac2:(tb__ "0|1|
S2S0Q40M0S10Vrho;S1fS1eS14Z8A1A2A2A2S0G0S10S1aVrho;S28A2S1eA2A2A2").
Proof. unfold cur at 2. cbn [eval]. rewrite rw_sub. cbn [wsub_get s_Wb Pos.eqb]. lia. Qed.
Lemma meas_Ee : ltac2:(tb__ "0|1|
S19SeSfVrho;A1S12S3fS2cA1A1A3S2S0Q40M0S10Vrho;S39A2A2S0G0S10S1aVrho;S25A2S1fS1eS14Z8A1A2A2A2A2F_;").
Proof.
  intros HF. unfold E_Ee in HF. split_facts HF HX HG HB.
  destruct (base_facts_Z rho HG HB) as [(Z1 & Z2 & Z3 & Z4 & Z5) (Y1 & Y2 & Y3 & Y4 & Y5 & Y6)].
  apply Forall_app in HX as [HAE HX]. destruct (F_ae_Z rho Y5 HAE) as (Q1 & Q2 & _).
  pose proof (urange (rw rho 141)) as R102.
  assert (W103 : wsub_get s_Ee 142 = SVar 141) by (pose proof s_Ee_vals as V; cbn [map] in V; congruence).
  unfold add, cur. cbn [eval]. rewrite rw_sub, W103. cbn [eval]. rewrite add_val, (u64_lit 8) by lia.
  rewrite Z.mod_small by lia. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gd. cbn [eval]. lia.
Qed.
Lemma meas_Eb : ltac2:(tb__ "0|1|
S19SeSfVrho;A1S12S3fS2bA1A1A3S2S0Q40M0S10Vrho;S1fS1eS14Z9A1A2A2A2S0G0S10S1aVrho;S24A2S1fS1eS14Z8A1A2A2A2A2F_;").
Proof.
  intros HF. unfold E_Eb in HF. split_facts HF HX HG HB.
  destruct (base_facts_Z rho HG HB) as [(Z1 & Z2 & Z3 & Z4 & Z5) (Y1 & Y2 & Y3 & Y4 & Y5 & Y6)].
  apply Forall_app in HX as [HE HX]. have_fact Hf9 HE (SPUlt cur OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.gd). zzh Hf9.
  pose proof (urange (rw rho 142)) as R103.
  unfold add. rewrite (U_addc rho cur 9 (bv_unsigned (rw rho 142)) eq_refl) by lia.
  cbn [eval]. unfold cur. cbn [eval]. rewrite rw_sub. cbn [wsub_get s_Eb Pos.eqb].
  rewrite add_val, (u64_lit 8) by lia.
  unfold add, cur. rewrite (U_addc rho (SVar 142) 1 (bv_unsigned (rw rho 142)) eq_refl) by lia. rewrite Z.mod_small by lia. lia.
Qed.
End GlueMeas.

Theorem region_B_sum_ex : ltac2:(tb__ "0|0|
S4eS13S45S1Q40A1A1S4fS48S42R3A3S53S48S4dS48R4S2aR3R2A5S4cS48R4S42R3R2S4bA6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  destruct ids_rip6 as (I1 & I2 & I3 & I4 & I5 & I6).
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF C0 rho tp w Hw) | intros w Hw; exact Hw |].
  change C0 with (vna_state (mkVNA C0 50 (SLit 0))).
  apply (cfg_complete_autoIA segs FUEL cutpcs_rip NF vcuts_rip vexits_rip (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_rip) tp).
  - exact HstG.
  - intros n Hin. unfold vcuts_rip in Hin. repeat (destruct Hin as [<-|Hin]; [cbv; congruence|]). destruct Hin.
  - exact echeck_rip.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]].
    + apply (eexit_post_IA0 segs J NF rho vcuts_rip Posts_rip (mkVNA P_ret 0 (SLit (2 ^ 64 - 1)))). in_nth 0.
    + apply (eexit_reenter_IA segs _ NF vcuts_rip _ (mkVNA E_Pe 31 gu) (mkVNA CP 30 cur) F_P CP_0 s_Pe tp);
        [in_nth 1 | reflexivity | exact ent_Pe | exact I1 | exact HstG | exact F_P_below
        | intros r tp' tr md _ HF; split; [exact (glue_Pe r HF) | right; split; [exact (meas_Pe r) | cbn; lia]] | cbn; lia | cbn; lia].
    + apply (eexit_reenter_IA segs _ NF vcuts_rip _ (mkVNA E_Pb 31 (add cur (SLit 1))) (mkVNA CP 30 cur) F_P CP_0 s_Pb tp);
        [in_nth 1 | reflexivity | exact ent_Pb | exact I2 | exact HstG | exact F_P_below
        | intros r tp' tr md _ HF; split; [exact (glue_Pb r HF) | right; split; [exact (meas_Pb r) | cbn; lia]] | cbn; lia | cbn; lia].
    + apply (eexit_reenter_IA segs _ NF vcuts_rip _ (mkVNA E_We 21 pab) (mkVNA CW 20 cur) F_W CW_0 s_We tp);
        [in_nth 2 | reflexivity | exact ent_We | exact I3 | exact HstG | exact F_W_below
        | intros r tp' tr md _ HF; split; [exact (glue_We r HF) | right; split; [exact (meas_We r) | cbn; lia]] | cbn; lia | cbn; lia].
    + apply (eexit_reenter_IA segs _ NF vcuts_rip _ (mkVNA E_Wb 21 (add cur (SLit 8))) (mkVNA CW 20 cur) F_W CW_0 s_Wb tp);
        [in_nth 2 | reflexivity | exact ent_Wb | exact I4 | exact HstG | exact F_W_below
        | intros r tp' tr md _ HF; split; [exact (glue_Wb r HF) | right; split; [exact (meas_Wb r) | cbn; lia]] | cbn; lia | cbn; lia].
    + apply (eexit_reenter_IA segs _ NF vcuts_rip _ (mkVNA E_Ee 11 gd) (mkVNA CE 10 (add cur (SLit 8))) F_E CE_0 s_Ee tp);
        [in_nth 3 | reflexivity | exact ent_Ee | exact I5 | exact HstG | exact F_E_below
        | intros r tp' tr md _ HF; split; [exact (glue_Ee r HF) | right; split; [exact (meas_Ee r HF) | cbn; lia]] | cbn; lia | cbn; lia].
    + apply (eexit_reenter_IA segs _ NF vcuts_rip _ (mkVNA E_Eb 11 (add cur (SLit 9))) (mkVNA CE 10 (add cur (SLit 8))) F_E CE_0 s_Eb tp);
        [in_nth 3 | reflexivity | exact ent_Eb | exact I6 | exact HstG | exact F_E_below
        | intros r tp' tr md _ HF; split; [exact (glue_Eb r HF) | right; split; [exact (meas_Eb r HF) | cbn; lia]] | cbn; lia | cbn; lia].
  - left; reflexivity.
Qed.
End Icpt_region_proof.

(* [comment removed for export] *)
Module DrvFwIface.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "nat"; "cons"; "nil"; "andb"; "bool"; "false"; "prod"; "pair"; "true"; "None"; "fst"; "option"; "snd"; "length"; "list"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "sobj"; "cell"; "mkObj"; "sprop"; "DImage"; "FcsrFrm0"; "SPUle"; "mkSS"; "swf"; "DUnknown"; "SPAlign"; "mkCell"; "ob_base"; "ob_hi"; "ob_lo"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "add"; "pow"; "div"; "mul"; "opp"; "sub"; "eqb"; "ltb"; "of_nat"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface"; "FERR"; "fc"; "EBUF"; "P_fw"; "O_fwstk"; "O_realfw"; "facts_fw"; "fregs_fw"; "fw_msgs"; "D_FW"; "MSGB"; "NPOST_FW"; "O_ferr0"; "O_ferr1"; "Pre_fw"; "fw_entry"; "fw_ret"; "obj_farW"; "objs_fw"; "objs_fw'"; "post_regs_fw"; "reg_fw"; "regs_fw"; "xblk"; "@Corelib.Init.Logic"; "eq"; "and"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "add"; "eqb"; "@Corelib.Init.Nat"; "add"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "O_got"; "O_rtc"; "SHB"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf"; "O_rtc3w"; "O_ssp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axwf"; "leafA"; "mkAX"; "mkLeafA"; "@Stdlib.Lists.List"; "In"; "forallb"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "image_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition fw_entry : Z := 0x4d2d0.
Definition fw_ret : Z := 0x4f328.
Definition FERR : Z := 0xe8ef0.
Definition EBUF : Z := 0x641980.
Definition D_FW : Z := 2400.

Definition fw_msgs : list (Z * Z) := ltac2:(tb__ "0|2|
S1S6S22S22A2M0S7S22S22Z21447Z1fM1A4S1G0S7S22S22Z160cdG1A4S1G0S7S22S22Z14d9dZ13A4S2G0A1A3A3A3").

Definition MSGB (msg len : Z) : list byte := ltac2:(tb__ "0|2|
SbSeS5dQ8A1M0A1M1A1G1Lx;S61S53Vmsg;S2fVlen;A1A3G1R1Lbs;S2G0A1Xbx2").

Definition xblk (msg len : Z) : sv * sv := ltac2:(tb__ "0|1|
S29S28Vmsg;Z40M0A2G0A2S22S7S10S10S11R1A1S11S2bS29S28S26S26Vmsg;Vlen;A2Z3fA2G0A2G0A2R1A2A1A4Tb;").

Definition O_fwstk : sobj := ltac2:(tb__ "0|0|
S15S12PaA1S11S2aS39A1A1S11Z0A1S2S14A1S1cA5").
Definition O_ferr0 : sobj := ltac2:(tb__ "0|0|
S15S11Z0A1S11S30A1S11S26S30Ze8A2A1S2S14A1S17A5").
Definition fc (off w v : Z) : cell := ltac2:(tb__ "0|0|
S1eS11S26S30Voff;A2A1Vw;S11Vv;A1A3").

Definition O_ferr1 : sobj := ltac2:(tb__ "0|2|
S15S11Z0M0A1S11S30A1S11S26S30Ze8A2A1S1S14S31Z38Z8M1S32A3S1S14S31Z28G1S32A3S1S14S31Z20G1S32A3S1S14S31Z10G1G0A3S1S14S31G1G1G0A3S1S14S31Z88Z4S2bS27Z2Z40A2Z1A2A3S2S14A1A3A3A3A3A3A3S17A5").
Definition O_realfw : sobj := ltac2:(tb__ "0|0|
S15S11Z0A1S11Ze6650A1S11Ze6658A1S2S14A1S17A5").
Definition objs_fw : list sobj := ltac2:(tb__ "0|0|
S1S13S34S1S13S3cS1S13S54S1S13S55S1S13S35S1S13S50S1S13S51S2S13A1A3A3A3A3A3A3A3").
Definition objs_fw' : list sobj := ltac2:(tb__ "0|0|
S1S13S34S1S13S3dS1S13S54S1S13S55S1S13S35S1S13S50S1S13S51S2S13A1A3A3A3A3A3A3A3").
Definition facts_fw : list sprop := ltac2:(tb__ "0|2|
S1S16S1dPaM0Z4A2S1S16S19S11Z7fff7ff01000A1S12G0A1M1A2S1S16S19G1S11S27Z2Z2fA2A1A2S2S16A1A3A3A3").

Definition obj_farW (lo0 hi0 : Z) (o : sobj) : bool := ltac2:(tb__ "0|e|
S10S4Lx;M0S1fVo;A1S22G0S21Vo;A1M1S22G0S20Vo;A1M2S22S3S3S3S3S2cR3Z0M3A2S25G3R2A2A2S25R2R1A2M4A2S2dR1S27Z2M5Z3eA2A2A2SfS25R1Vlo0;A2S25Vhi0;R2A2A2A2Lh;S23S5Li;M6S5eS10S10S5Lb;La;M7Lop;M8G8S5fG7Lop;M9G9S4S24S10S5La;Lw;Lsgn;MaS23S10S22S5Lk;Li;MbLl0;McX10x8Ll;G6G8G8G9G9GaS23GbLl;MdX10x8Lbz;S23G0G1S22G0G2S22S3S3S3S4cR3PaA2S25S2aS27G5Z28A2A1R2A2A2G4A2S25R1G3A2A2Lh;G6G8G8G9G9GaGcX10x8Ll;G6G8G8G9G9GaGdX10x8Lv;G8G8G9G9GaGdX10x8").
Definition objs_farW (lo0 hi0 : Z) (objs : list sobj) : bool := ltac2:(tb__ "0|0|
S3S3S25Z0Vlo0;A2S25Vhi0;S27Z2Z20A2A2A2S5cS13S41Vlo0;Vhi0;A2Vobjs;A3A2").

Definition reg_fw (msg len : Z) (r : nat) : sv := ltac2:(tb__ "0|1|
S0S10Lr;Vr;S11Z0A1S0S0S10Ln;R1S12PbA1S0S0S10Ln0;R1S12PaA1S0S0S10Ln1;R1S11Z10800A1S0S0S10Ln2;R1S11Z621278A1S0S0S10Ln3;R1S12S4aS4dU3cVr;A2A1A1M0S0S0S10Ln4;R1G0S0S0S10Ln5;R1G0S0S0S10Ln6;R1G0S0S0S10Ln7;R1G0S0S0S10Ln8;R1S11Vmsg;A1S0S0S10Ln9;R1S11Vlen;A1S0S0S10Ln10;R1S11Z1A1S0S0S10Ln11;R1S11S30A1S0G0Ln12;X0x2Ln11;X0x2Ln10;X0x2Ln9;X0x2Ln8;X0x2Ln7;X0x2Ln6;X0x2Ln5;X0x2Ln4;X0x2Ln3;X0x2Ln2;X0x2Ln1;X0x2Ln0;X0x2Ln;X0x2").
Definition regs_fw (msg len : Z) : list sv := ltac2:(tb__ "0|0|
S4eS0S10S45Vmsg;Vlen;A2S4fU0U20A2A4").
Definition fregs_fw : list sv := ltac2:(tb__ "0|0|
S4eS0S10S0S12S4aS4dU14R1A2A1A1Lr;S4fU0U20A2A4").
Definition NPOST_FW : positive := 132.
Definition post_reg_fw (r : nat) : sv := ltac2:(tb__ "0|1|
S0S10Lr;Vr;S11Z0A1S0S0S10Ln;R1S12PbA1S0S0S10Ln0;R1S12PaA1S0S0S10Ln1;R1S11Z10800A1S0S0S10Ln2;R1S11Z621278A1S0S0S10Ln3;R1S12S4bP64S4aVr;A1A2A1M0S0S0S10Ln4;R1G0S0S0S10Ln5;R1G0S0S0S10Ln6;R1S12P44A1S0S0S10Ln7;R1S12P45A1S0S0S10Ln8;R1S11Z1A1S0S0S10Ln9;R1G0S0S0S10Ln10;R1G0S0S0S10Ln11;R1G0S0S0S10Ln12;R1G0S0S0S10Ln13;R1G0S0S0S10Ln14;R1G0S0S0S10Ln15;R1G0S0S0S10Ln16;R1S12P4eA1S0S0S10Ln17;R1S12P4fA1S0S0S10Ln18;R1S12P50A1S0S0S10Ln19;R1S12P51A1S0S0S10Ln20;R1S12P52A1S0S0S10Ln21;R1S12P53A1S0S0S10Ln22;R1S12P54A1S0S0S10Ln23;R1S12P55A1S0S0S10Ln24;R1S12P56A1S0S0S10Ln25;R1S12P57A1S0G0Ln26;X0x2Ln25;X0x2Ln24;X0x2Ln23;X0x2Ln22;X0x2Ln21;X0x2Ln20;X0x2Ln19;X0x2Ln18;X0x2Ln17;X0x2Ln16;X0x2Ln15;X0x2Ln14;X0x2Ln13;X0x2Ln12;X0x2Ln11;X0x2Ln10;X0x2Ln9;X0x2Ln8;X0x2Ln7;X0x2Ln6;X0x2Ln5;X0x2Ln4;X0x2Ln3;X0x2Ln2;X0x2Ln1;X0x2Ln0;X0x2Ln;X0x2").
Definition post_regs_fw : list sv := map post_reg_fw (seq 0 32).

Definition Pre_fw (msg len : Z) : axst := ltac2:(tb__ "0|1|
S59S1aS3fS46Vmsg;Vlen;A2S37S18S9S10A1S42S36S62S5A9S1S6S10S10A2M0S47Vmsg;Vlen;A2S2G0A1A3S11S52A1A3").
Definition P_fw : axst := ltac2:(tb__ "0|0|
S59S1aS40S44S37S18S9S10A1S43S36S3bS5A9S2S6S10S10A2A1S11S52A1A3").
Definition Posts_fw : list leafA := ltac2:(tb__ "0|0|
S1S58S5aS33S60A2S2S58A1A3").

Lemma fw_wf : ltac2:(tb__ "0|2|
S6S22S22A2M0S5bG0R1S38A3S49S48S4S57S3eSaS22S22R2A3ScS22S22R2A3A2M1A1S8A3S48S4S1bS56G1A1A1S8A3A2F_;Fml;").
Proof. intros ml H. repeat (destruct H as [<-|H]; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2|]). destruct H. Qed.
Lemma P_fw_wf : ltac2:(tb__ "0|0|
S49S48S4S57S33A1S8A3S48S4S1bS56S33A1A1S8A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma MSGB_len : ltac2:(tb__ "0|2|
S6S22S22A2M0S5bG0R1S38A3S48S22S2eSdS5dQ8A1S3aSaS22S22R2A3ScS22S22R2A3M1A2A2A1G1A3F_;Fml;").
Proof. intros ml H. repeat (destruct H as [<-|H]; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]). destruct H. Qed.
End DrvFwIface.

(* [comment removed for export] *)
Module StartMemsetZ.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "valuation"; "sstate"; "sprop"; "SVar"; "rw"; "SAlu"; "ss_next"; "agree_below"; "cell"; "mkObj"; "ss_lenient"; "sv_eqb"; "eval"; "mkSS"; "swf"; "FcsrFrm0"; "SPUle"; "DUnknown"; "DZero"; "ss_facts"; "ss_pc"; "ss_objs"; "holds"; "mkCell"; "obj_range"; "ss_regs"; "SAluW"; "ob_base"; "ob_hi"; "ob_lo"; "sprop_below"; "ss_fcsr"; "ss_fregs"; "ss_resv"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "prod"; "option"; "false"; "andb"; "pair"; "nat"; "list"; "nil"; "true"; "None"; "Some"; "fst"; "snd"; "app"; "negb"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "False"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "sub"; "opp"; "modulo"; "eqb"; "mul"; "of_nat"; "lt"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "la_state"; "axst"; "ax_setS"; "ax_base"; "entailsA"; "ax_X"; "la_reason"; "sym_runA"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "pre_regs"; "setregs"; "NPOST"; "two62"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "@Stdlib.Lists.List"; "In"; "forallb"; "flat_map"; "nth_error"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ"; "u_range"; "zvC"; "CZ"; "run1"; "zvN"; "P_msz"; "addl"; "Posts_mszA"; "is_cut"; "setreg"; "zvD"; "ZBODY"; "noX"; "restate_okb"; "Pre_mszA"; "PC_K"; "PC_T"; "ex_okb"; "factsCZ"; "factsZ"; "fin_okb"; "is_ret"; "it_okb"; "lit_okb"; "r_range"; "s_en"; "zfold_at"; "KX"; "L1_MAX"; "L2_MIN"; "P_lit"; "T4X"; "ZRET"; "diff_isb"; "eT"; "en_okb"; "kut_range"; "lit_range"; "s_it"; "ur_range"; "NAk"; "NXk"; "O_du"; "O_dz"; "PC_N"; "POSTR"; "Pre_big"; "Pre_lit"; "ZB"; "eX"; "factsN"; "guard"; "regsCZ"; "remC"; "tail_cells"; "CZX"; "CZi"; "M4"; "Pre_msz"; "pair_inb"; "stage2"; "stage3"; "xdiffs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub"; "rho_sub"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "list_set"; "set_objs"; "RsSymJump"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "seq"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue"; "M64v"; "@Stdlib.PArith.BinPos.Pos"; "le"; "eqb"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueZ"; "zero_covered"; "zobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ZeroObj"; "zero_obj"; "zero_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "N14"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymObj SymEntail SymCFG SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueZ SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv MuslMemset CursorGlue ZeroObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA MuslWLA DrvGlueB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ZB : Z := memset_entryA.
Definition ZRET : Z := memset_entryA + 0xf4.
Definition O_du (hi : sv) : sobj := ltac2:(tb__ "0|0|
SeS8PcA1S3Z0A1Vhi;S30SdA1S16A5").
Definition O_dz (hi : sv) : sobj := ltac2:(tb__ "0|0|
SeS8PcA1S3Z0A1Vhi;S30SdA1S17A5").
Definition factsZ : list sprop := [N14].

Definition POSTR : list sv := ltac2:(tb__ "0|1|
S56S55S28S29S2eS2A2M0S2dS2eS2UaS8PcA1A4S28G0S2dS2eS2UbS8P6fA1A4S28G0S2dS2eS2UcS8P70A1A4S28G0S2dS2eS2UdS8P71A1A4S28G0S2dS2eS2UeS8P72A1A4S28G0S2dS2eS2UfS8P73A1A4S28G0S2dS2eS2U10S8P74A1A4S30G0A1A3A3A3A3A3A3A3A2").

Definition Pre_msz : sstate := ltac2:(tb__ "0|1|
S12S93S56S55S28S29S2eS2A2M0S2dS2eS2UbS3Z0A1A4S30G0A1A3A2S54S14S32S2A1S28S4S8dS8PeA1A1S30S4A1A3S76S53S2bA9").

Definition P_msz : sstate := ltac2:(tb__ "0|0|
S12S83S90S54S14S32S2A1S28S4S8eS8PeA1A1S30S4A1A3S76S57S2bA9").
Definition Pre_mszA : axst := liftA Pre_msz.
Definition Posts_mszA : list leafA := ltac2:(tb__ "0|0|
S28S47S51S62S68A1Sb2A2S30S47A1A3").

Definition KX : sv := ltac2:(tb__ "0|0|
SaSa7S1fSa8S3Z0A1S8PcA1A3S3Z3A1A3").
Definition M4 : Z := 18446744073709551612.
Definition NXk (k : Z) : sv := ltac2:(tb__ "0|2|
S27S2L_;S42Vk;Z0A2SaSa7S8PeA1M0S3S9cA1M1A3SaSa7SaSa6G0S3S40Vk;A1A1A3G1A3X27x2").
Definition NAk (k u : Z) : sv := ltac2:(tb__ "0|2|
S27S2L_;S42S3eVk;Vu;A2M0Z0A2S8PeA1M1SaSa6G1S3S40G0A1A1A3X27x2").
Definition T4X (k : Z) : sv := ltac2:(tb__ "0|2|
S27S2L_;S42Vk;Z0A2SaSa7S8PcA1M0S3Z4A1M1A3SaSa7SaSa6G0S3Vk;A1A3G1A3X27x2").
Definition PC_K : Z := ZB + 0x50.
Definition PC_N : Z := ZB + 0x64.
Definition PC_T : Z := ZB + 0xa4.
Definition ZBODY : Z := ZB + 0xd8.

Definition setreg (A : axst) (r : nat) (e : sv) : axst := ltac2:(tb__ "0|0|
S48VA;A1S6S4bVA;S12S19R1A1Sb0S2S1eR1A1Vr;Ve;A4S25R1A1S24R1A1S26R1A1S1aR1A1S18R1A1SbR1A1SfR1A1A9A2TS;").

Definition run1 (fuel : nat) (cuts : list Z) (A : axst) : option leafA := ltac2:(tb__ "0|3|
S2aS2fS47A1M0A1S2aS47A1M1Lx;S50S52Vfuel;Vcuts;VA;S31A5G0G0G1Ll;R1S32S47A1M2S47G0G0G1Ll0;R1S33S47R2A2S47G0G2Ll2;Ll1;X2fx2Ll0;LL;X2fx2Ll;G2X2ax2").

Definition restate_okb (A : axst) (r : nat) (e e' : sv) : bool := ltac2:(tb__ "0|6|
S2cS2cS10Sb6S2Vr;S1eS48VA;A1M0A1S3Z0A1A4Ve;A2S13S48S6cVA;Vr;Ve';A3A1M1A1A2S2aS29S2fS29S2S2A2M2A1M3S2fS7A1M4A2M5A1S27Lx;SadG0G1A2G5G5S27Lp;R1G3G4G4S27Ll;R1S5eG2G2S2cS10S34S2S2R1A3Ve;A2S10S35S2S2R1A3Ve';A2A2Lp;R2A3S7G4S2bLl0;Ls;X2fx2Ll;Ld;X29x1Lp;S2bX2ax2A2").
Definition is_ret (L : leafA) : bool := ltac2:(tb__ "0|0|
S2cS42S19S48S49VL;A1A1A1S83A2SafS27Lx;S4fVL;A1S2bS2bS2bS2bS31S2bS2bXafx7A2").
Definition is_cut (L : leafA) (pc : Z) : bool := ltac2:(tb__ "0|1|
S2cS2cS2cS42S19S48S49VL;A1A1M0A1Vpc;A2SafS27Lx;S4fVL;A1S2bS31S2bS2bS2bS2bS2bXafx7A2S37SfG0A1A1A2SbcS53SbG0A1A2A2").
Definition noX (A : axst) : bool := ltac2:(tb__ "0|2|
S2cS2fS29S2S2A2M0A1M1S27Lx;S4eVA;A1S31G0G1S2bLl;Lp;X2fx2S10S4cVA;A1S4cS62S68A1A1A2A2").
Definition diff_isb (a b : sv) (d : list (sv * sv)) : bool := ltac2:(tb__ "0|1|
S5eS29S2S2A2M0G0S2cS10S34S2S2R1A3Va;A2S10S35S2S2R1A3Vb;A2A2Lp;Vd;A3").

Definition Pre_lit (n : Z) : sstate := ltac2:(tb__ "0|2|
S12S93S56S55S28S29S2eS2A2M0S2dS2eS2UbS3Z0A1A4S28G0S2dS2eS2UcS3Vn;A1M1A4S30G0A1A3A3A2S54S14S32S2A1S28S4S8dG1A1S30S4A1A3S76S53S2bA9").
Definition P_lit (n : Z) : sstate := ltac2:(tb__ "0|0|
S12S83S90S54S14S32S2A1S28S4S8eS3Vn;A1A1S30S4A1A3S76S57S2bA9").

Definition fin_okb (n : Z) (L : leafA) : bool := ltac2:(tb__ "0|3|
S2cS2cS78VL;A1S6fS49VL;A1M0A1A2S2aS6A1S27Lx;Sc1S48G0A1M1U0A2S6SbdS53R1S81Vn;A1M2A3SaaS2cS2cSaeG1R2A2S4dS62R2A1S62G2A1R1A3A2Sa9R1S53A2A2Ts;LSz;S2bX2ax2A2").
Definition stage3 (fuel : nat) (n k t4 : Z) (E2 : axst) : bool := ltac2:(tb__ "0|2|
S2cS70VE2;UfM0S82Vk;A1S3Vt4;A1M1A4S2aS47A1S27Lx;S66Vfuel;S30S0A1S6cVE2;G0G1A3A3S47S77Vn;R1A2LL;S2bX2ax2A2").
Definition stage2 (fuel : nat) (n k t4 : Z) (E1 : axst) : bool := ltac2:(tb__ "0|2|
S2cS70VE1;UdM0S7eS3Vk;A1M1A4S2aS47A1S27Lx;S66Vfuel;S28S0S73S30S0A1A3S6cVE1;G0G1A3A3S47S27S27L_;S78R1A1S77Vn;R1A2S2cS6bR1S73A2Sa0Vfuel;Vn;Vk;Vt4;S49R1A1A5A2X27x2LL;S2bX2ax2A2").
Definition lit_okb (fuel : nat) (c : Z * Z * Z) : bool := ltac2:(tb__ "0|8|
S29S29S0S0A2M0S0A2S27Lc;Vc;G0S0G0S27Lp;R2S0S0S2aS29S2fS29S2S2A2A1M1S2fS7A1M2A2M3A1S27Lx;M4SadS9dS92R2A1A2G3G3S27Lp;R1G1G2G2S27Ll;R1G4SadS81R5A1S68A2G3G3S27Lp0;R1G1G2G2S27Ll0;R1S2cS2cS2cS2cS84S8PeA1M5S3R8A1M6R5A3S84G6G5R2A3A2S13S92R8A1M7A1A2S13S68A1A2S2aS47A1S27Lx;S66Vfuel;S28S0S72S30S0A1A3S62G7A1A3S47S27S27L_;S78R1A1S77R9R1A2S2cS6bR1S72A2S9fVfuel;R9R8RaS49R1A1A5A2X27x2LL;S2bX2ax2A2S7G2S2bLl1;Ls;X2fx2Ll0;Ld2;X29x1Lp0;S2bX2ax2S7G2S2bLl0;Ls;X2fx2Ll;Ld1;X29x1Lp;S2bX2ax2Lk;Ln;X29x1Lt4;Lp;X29x1").

Definition L1_MAX : Z := 103.
Definition lit_range : list (Z * Z * Z) := ltac2:(tb__ "0|4|
S5fS2eS29S29S0S0A2M0S0A2M1S2eS5fS2eG1S2eS28G1S2dG0S0S2dS0S0S44R2A1S44R1A1A4M2Z0A4S28G1S2dG0S0G2Z4A4S30G1A1A3A3Lk;Sb5U0M3U4A2A4Ln;Sb5G3S46S3eS7fZ1A2A1A2A4").
Lemma lit_allb : ltac2:(tb__ "0|0|
S38S27S5eS29S29S0S0A2S0A2S7aU190A1S88A3S31A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma lit_range_in : ltac2:(tb__ "0|3|
S0S0S0S39S3dZ0M0R3A2M1S3dR3S7fA2A2S39G1S3dR3Z3A2A2S3aS38S0R3G0A3S38S0R3Z4A3A2S5dS29S29S0S0A2M2S0A2S2dG2S0S2dS0S0R6R5A4R4A4S88A3F_;F_;F_;Ft4;Fk;Fn;").
Proof.
  intros n k t4 Hn Hk Ht. unfold lit_range. apply in_flat_map. exists (Z.to_nat n). split; [apply in_seq; unfold L1_MAX in *; lia|].
  apply in_flat_map. exists (Z.to_nat k). split; [apply in_seq; lia|]. rewrite !Z2Nat.id by lia.
  destruct Ht as [-> | ->]; [left; reflexivity | right; left; reflexivity].
Qed.
Lemma lit_ok : ltac2:(tb__ "0|2|
S0S0S0S39S3dZ0M0R3A2M1S3dR3S7fA2A2S39G1S3dR3Z3A2A2S3aS38S0R3G0A3S38S0R3Z4A3A2S38S27S7aU190S2dS29S0S0A2S0S2dS0S0R6R5A4R4A4A2S31A3F_;F_;F_;Ft4;Fk;Fn;").
Proof. intros n k t4 Hn Hk Ht. exact (proj1 (forallb_forall _ _) lit_allb _ (lit_range_in n k t4 Hn Hk Ht)). Qed.

Definition L2_MIN : Z := 104.
Definition zvD : sv := SVar 12.
Definition zvN : sv := SVar 14.
Definition zvC : sv := SVar 100.
Definition addl (a : sv) (z : Z) : sv := ltac2:(tb__ "0|0|
SaSa6Va;S3Vz;A1A3").
Definition eT : sv := addl zvN (-32).
Definition factsN : list sprop := ltac2:(tb__ "0|0|
S28S7Sc3S28S7S15S3S80A1S67A2S30S7A1A3A3").
Definition tail_cells (u : Z) : list cell := ltac2:(tb__ "0|6|
S36SdSb3S0SdS0S1cS69S67S3fS40Vu;A1S43Z4M0R1A2A2A2G0S3Z0A1M1A3Lj;S28S0Z1M2S28S0Z2M3S28S0Z3M4S28S0G0S28S0Z5S28S0Z6S28S0Z7S30S0A1M5A3A3A3A3A3A3A3A4Sb3S0SdS0S1cS69S67S40R1A1A2G2G1A3Lj;S28S0G2S28S0G3S28S0G4S28S0G0G5A3A3A3A3A4A3").
Definition regsCZ (cur rem a5 : sv) : list sv := ltac2:(tb__ "0|1|
S56S55S28S29S2eS2A2M0S2dS2eS2UbSaSa6S6dVcur;A3A4S28G0S2dS2eS2UcS3Z0A1A4S28G0S2dS2eS2UdS3Z1fA1A4S28G0S2dS2eS2UeVrem;A4S28G0S2dS2eS2UfVa5;A4S28G0S2dS2eS2U10S3Z20A1A4S30G0A1A3A3A3A3A3A3A2").
Definition remC (u : Z) : sv := ltac2:(tb__ "0|0|
SaSa8S69S67S40Vu;A1A2S64A3").
Definition factsCZ (u : Z) : list sprop := ltac2:(tb__ "0|0|
S36S7S95S28S7S15S64S67A2S28S7S15S69S64S3eZ20Vu;A2A2S67A2S28S7S15S3Z18A1S64A2S30S7A1A3A3A3A3").

Definition CZ (u : Z) : sstate := ltac2:(tb__ "0|1|
S12S6eS97S64S98Vu;A1S8P65A1A3S54S14S32S2A1S28S4SeS6dS3Z0A1S64S30SdA1M0S17A5S28S4SeS6dS64S85G0S16A5S28S4SeS6dS85S67S99Vu;A1S16A5S30S4A1A3A3A3S75Vu;A1P66S2bA9").

Definition CZi (u : Z) : axst := ltac2:(tb__ "0|0|
Sc2S62S65Vu;A1A1S28S7S15S69S64S3eZ40Vu;A2A2S67A2S75Vu;A1A3A2").

Definition eX (u r : Z) : sv := ltac2:(tb__ "0|0|
S69S67S40S3eS3eVu;Z20A2Vr;A2A1A2").
Definition CZX (u r : Z) : sstate := ltac2:(tb__ "0|1|
S12S6eS97S94Vu;Vr;A2M0S3S3eZ20Vr;A2A1S8P65A1A3S54S14S32S2A1S28S4SeS6dS3Z0A1G0S30SdA1S17A5S28S4SeS6dG0S67S99Vu;A1S16A5S30S4A1A3A3S95P66S2bA9").
Definition xdiffs (u r : Z) : list (sv * sv) := ltac2:(tb__ "0|2|
S28S29S2S2A2M0S2dS2S2SaSa6S6dS64A3SaSa6S6dS94Vu;Vr;A2M1A3A4S28G0S2dS2S2S98Vu;A1S3S3eZ20Vr;A2A1A4S28G0S2dS2S2S64G1A4S30G0A1A3A3A3").
Definition pair_inb (l : list (sv * sv)) (p : sv * sv) : bool := ltac2:(tb__ "0|1|
S61S29S2S2A2M0G0S2cS10S34S2S2Vp;A3S34S2S2R1A3A2S10S35S2S2Vp;A3S35S2S2R1A3A2A2Lq;Vl;A3").

Definition s_it : wsub := ltac2:(tb__ "0|2|
S28S29S1S2A2M0S2dS1S2P64S69S64Z20A2A4S28G0S2dS1S2P65M1S8G1A1A4S30G0A1A3A3").
Definition s_en (k t4 : Z) : wsub := ltac2:(tb__ "0|1|
S28S29S1S2A2M0S2dS1S2P64S3S3eS3eVk;Z38A2Vt4;A2A1A4S28G0S2dS1S2P65S3S3eZ18Vt4;A2A1A4S30G0A1A3A3").

Definition guard {T} (fuel : nat) (x : option T) : option T := match fuel with O => None | S _ => x end.
Lemma guard_Some : forall {T} fuel (x : option T) y, guard fuel x = Some y -> x = Some y.
Proof. intros T [|f] x y H; [discriminate H | exact H]. Qed.

Definition zfold_at (S : sstate) (i : nat) : option sstate := ltac2:(tb__ "0|3|
S2aS4A1S2aS6A1M0Lx;S60S4S1aVS;A1M1Vi;A3S4S27G0L_;SbeS18VS;A1R1A2S33S6Sb1VS;Sb0S4G1Vi;SbfR1A1A4A2A2S32S6A1M2X27x2Lo;G2X2ax2").

Definition it_okb (fuel : nat) (u : Z) : bool := ltac2:(tb__ "0|3|
S2cS5eS7S23P66A1S28S7S15S69S64S3eZ40Vu;A2A2S67A2S75Vu;A1A3A3S2aS47A1S27Lx;S66Vfuel;S28S0S6eS30S0A1A3S9bVu;A1A3S47S2cS2cS6bR1S6eA2S6fS49R1A1M0A1A2S2aS6A1S27Lx;M1Sb8S48G0A1U1M2S69S64Z20A2A3S6G1S7dR1G2A2S6G1Sb7R1U0A2S6S4dS4bS49R4A1R1A2S62S65Vu;A1A1S89A3LS3;S2bX2ax2LS2;S2bX2ax2LS1;S2bX2ax2A2LL;S2bX2ax2A2").

Definition ex_okb (fuel : nat) (ur : Z * Z) : bool := ltac2:(tb__ "0|8|
S29S0S0A2S27Lur;Vur;S0S0S2aS6A1S27Lx;M0S96S6Vfuel;Sb7S65R2A1U1M1A2A3S6S2cS2cS2cSbbSbR1A1P66A2S13S9aR3R2A2M2A1A2S2aS29S2fS29S2S2A2M3A1M4S2fS7A1M5A2M6A1S27Lx;SadR1G2A2G6G6S27Lp;R1G4G5G5S27Ll;R1S5eG3S9eSa1R6R5A2A1R2A3S7G5S2bLl0;Ls;X2fx2Ll;Ld;X29x1Lp;S2bX2ax2A2S2aS47A1S27Lx;S66Vfuel;S30S0A1S62G2A1A3S47S2cS2cS78R1A1S6fS49R1A1M7A1A2G0S7dS48G7A1G1A2S6G0Sb7R1U0A2S6SbdS53R1S68A3SaaS2cS4dS4bS49R4A1R2A2S62S68A1R1A3Sa9R1S53A2A2Ts;LS3;S2bX2ax2LS2;S2bX2ax2A2LL;S2bX2ax2A2LSm;S2bX2ax2Lr;Lu;X29x1").

Definition Pre_big : axst := ax_with_facts Pre_mszA factsN.
Definition en_okb (fuel : nat) (c : Z * Z * Z) : bool := ltac2:(tb__ "0|e|
S29S29S0S0A2M0S0A2S27Lc;Vc;G0S0G0S27Lp;R2S0S0S2aS6A1S27Lx;M1S96S6Vfuel;Sb8S48S91A1U0M2S85A3A3S6S2cS2cSbbSbR1A1S53A2S37SfR1A1A1A2S2aS47A1S27Lx;M3S66Vfuel;S28S0S72S30S0A1M4A3S4bS91R1A2A3S47S2cS2cS6bR1S72A2S70S49R1A1M5UdM6S7eS3R4A1M7A4A2G3S66Vfuel;S28S0S8fG4A3S6cG5G6G7A3A3S47S2cS2cS6bR1S8fA2S70G5UeM8S8cR5A1S8bR5R4A2M9A4A2G3S66Vfuel;S28S0S73G4A3S6cG5G8G9A3A3S47S2cS2cS6bR1S73A2S70G5UfMaS82R6A1S3R7A1MbA4A2G3S66Vfuel;S28S0S6eG4A3McS6cG5GaGbA3A3S47S2cS6bR1S6eA2MdG3S66Vfuel;GcG5A3S47S2cS2cGdS6fG5A1A2G1Sb8S48G5A1G2S3S3eS3eR8Z38A2R9A2A1A3S6G1S7dR1G2A2S6S4dS4bS49R3A1R1A2S62S65R9A1A1S7cRaRbA2A3LS6;S2bX2ax2LS5;S2bX2ax2A2LL5;S2bX2ax2A2LL4;S2bX2ax2A2LL3;S2bX2ax2A2LL2;S2bX2ax2A2LL1;S2bX2ax2A2LS0;S2bX2ax2Lu;Lk;X29x1Lt4;Lp;X29x1").

Definition u_range : list Z := ltac2:(tb__ "0|0|
S28S0Z0S28S0Z1S28S0Z2S28S0Z3S30S0A1A3A3A3A3").
Definition r_range : list Z := ltac2:(tb__ "0|0|
S28S0Z0S28S0Z4S28S0Z8S28S0ZcS28S0Z10S28S0Z14S28S0Z18S28S0Z1cS30S0A1A3A3A3A3A3A3A3A3").
Definition ur_range : list (Z * Z) := ltac2:(tb__ "0|1|
S5fS0S29S0S0A2M0S0Sb3S0G0S0S2dS0S0R2R1A4Lr;S7bA4Lu;S63A4").
Definition kut_range : list (Z * Z * Z) := ltac2:(tb__ "0|3|
S5fS0S29S29S0S0A2M0S0A2M1S0S5fS0G1S0S28G1S2dG0S0S2dS0S0R2R1A4M2Z0A4S28G1S2dG0S0G2Z4A4S30G1A1A3A3Lu;S63A4Lk;S63A4").

Lemma it_allb : ltac2:(tb__ "0|0|
S38S27S5eS0S79U28A1S63A3S31A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ex_allb : ltac2:(tb__ "0|0|
S38S27S5eS29S0S0A2S74U28A1S8aA3S31A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma en_allb : ltac2:(tb__ "0|0|
S38S27S5eS29S29S0S0A2S0A2S86U78A1S87A3S31A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma swf_CZ : ltac2:(tb__ "0|0|
S38S27S5eS0S0S2cS2cS13S65R1A1A1Sa9S89S53A2A2S5eS0S0S2cSa9S7cR1Z0A2S53A2Sa9S7cR1Z4A2S53A2A2Lk;S63A3A2Lu;S63A3S31A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Local Notation "'U' rho i" := (bv_unsigned (rw rho i)) (at level 10, rho at level 9, i at level 9).

Lemma U_KX_range : ltac2:(tb__ "0|1|
S5S39S3dZ0S59Q40S11R1S7eA2A2M0A2S3dG0Z3A2A2Frho;").
Proof.
  intros rho. unfold KX. cbn [eval]. rewrite and_val, lit_unsigned. change (3 mod 2 ^ 64) with (Z.ones 2).
  rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (bv_unsigned (sext 64 (alu32 ALU_SUB (low32 (Z_to_bv 64 0)) (low32 (rw rho 12))))) (2 ^ 2) ltac:(lia)). lia.
Qed.
Lemma U_T4X_cases : ltac2:(tb__ "0|1|
S5S0S3aS38S0S59Q40S11R2S82R1A1A2A2M0Z0A3S38S0G0Z4A3A2Fk;Frho;").
Proof.
  intros rho k.
  assert (G : forall x : word, Z.land (bv_unsigned x) 4 = 0 \/ Z.land (bv_unsigned x) 4 = 4).
  { intros x. destruct (Z.testbit (bv_unsigned x) 2) eqn:B.
    - right. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
      destruct (Z.eq_dec i 2) as [->|Hne]; [rewrite B; reflexivity|].
      replace (Z.testbit 4 i) with false; [rewrite andb_false_r; reflexivity|].
      symmetry. change 4 with (2 ^ 2). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
    - left. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
      destruct (Z.eq_dec i 2) as [->|Hne]; [rewrite B; reflexivity|].
      replace (Z.testbit 4 i) with false; [rewrite andb_false_r; reflexivity|].
      symmetry. change 4 with (2 ^ 2). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia. }
  unfold T4X. destruct (k =? 0); cbn [eval]; rewrite and_val, lit_unsigned; change (4 mod 2 ^ 64) with 4; apply G.
Qed.

Lemma add_neg_lit : ltac2:(tb__ "0|0|
S0S0S39S3dZ0R1A2S3dR1R2A2A2S45R3Sb9A2S38S0S41S3eR4S41S40R3A1Sb9A2A2Sb9A2S3fR4R3A2A3F_;F_;Fc;Fx;").
Proof.
  intros x c Hc Hx. rewrite Z.add_mod_idemp_r by (cbv; discriminate).
  rewrite Z.mod_small; unfold M64v in *; lia.
Qed.
Lemma U_NX : ltac2:(tb__ "0|2|
S5S0S39S3dZ0R1A2S3dR1Z3A2A2S3dR2S59Q40M0S9R3PeM1A2A2A2S38S5aG0A1S11R4S8cR3A1A2S11R4S8bR3S41S3fS59G0S9R4G1A2A2R3A2Z4A2A2A2A3F_;F_;Fk;Frho;").
Proof.
  intros rho k Hk Hle. pose proof (urange (rw rho 14)) as Hr. rewrite M64v_eq in Hr.
  pose proof (Z.mod_pos_bound (U rho 14 - k) 4 ltac:(lia)) as Hm.
  pose proof (Z_div_mod_eq_full (U rho 14 - k) 4) as Hdm.
  assert (HM4 : forall x, 0 <= x < M64v -> Z.land x M4 = x - x mod 4).
  { intros x Hx. unfold M4. apply land_m4. rewrite M64v_eq. exact Hx. }
  apply bv_eq. unfold NXk, NAk.
  destruct (Z.eqb_spec k 0) as [->|Hk0].
  - rewrite Z.sub_0_r in *. cbn [eval]. rewrite and_val. change (bv_unsigned (Z_to_bv 64 M4)) with M4.
    rewrite HM4 by lia.
    destruct (Z.eqb_spec (0 + U rho 14 mod 4) 0) as [E0|NE].
    + cbn [eval]. lia.
    + change (bv_unsigned (eval rho (SAlu ALU_ADD (SVar 14) (SLit (- (0 + U rho 14 mod 4))))))
        with (bv_unsigned (eval rho (SAlu ALU_ADD (SVar 14) (SLit (- (0 + U rho 14 mod 4)))))).
      rewrite U_add, U_lit. cbn [eval]. rewrite add_neg_lit; lia.
  - cbn [eval]. rewrite and_val. change (bv_unsigned (Z_to_bv 64 M4)) with M4.
    rewrite add_val, lit_unsigned, M64v_eq, add_neg_lit by lia.
    rewrite HM4 by lia.
    destruct (Z.eqb_spec (k + (U rho 14 - k) mod 4) 0) as [E0|NE]; [lia|].
    change (bv_unsigned (eval rho (SAlu ALU_ADD (SVar 14) (SLit (- (k + (U rho 14 - k) mod 4))))))
      with (bv_unsigned (eval rho (SAlu ALU_ADD (SVar 14) (SLit (- (k + (U rho 14 - k) mod 4)))))).
    rewrite U_add, U_lit. cbn [eval]. rewrite add_neg_lit; lia.
Qed.

Lemma restate_keeps : ltac2:(tb__ "0|2|
S4aS2eS2S39S38S1SbS48S6cR3R2R1A3A1M0A1SbS48R3A1M1A1A3S38S27SfG0A1SfG1A1A3A2Fe;Fr;FA;").
Proof. intros. split; reflexivity. Qed.
Lemma is_cut_sound : ltac2:(tb__ "0|1|
S47S0S38S27S6bR2R1A2S31A3S39S38S0S19S48S49R3A1A1M0A1R2A3S39S38S27SfG0A1S2bA3SbaS53SbG0A1A2A2A2F_;Fpc;FL;").
Proof.
  intros L pc H. unfold is_cut in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H1 _].
  apply Z.eqb_eq in H1. apply Pos.leb_le in H3. destruct (ss_lenient (ax_S (la_state L))); [discriminate|]. auto.
Qed.
Lemma noX_sound : ltac2:(tb__ "0|1|
S4aS38S27S6fR1A1S31A3S39S38S2fS29S2S2A2M0A1S4eR2A1S30G0A1A3S38S2S4cR2A1S4cS62S68A1A1A3A2F_;FA;").
Proof.
  intros A H. unfold noX in H. apply andb_prop in H as [H1 H2]. apply sv_eqb_sound in H2.
  destruct (ax_X A); [auto | discriminate].
Qed.
Lemma noX_lift : ltac2:(tb__ "0|0|
S4aS6S38S27S6fR2A1S31A3S38S4aS4bR3R2A2S62R2A1A3F_;FS;FA;").
Proof. intros [SA XA bA] S H. destruct (noX_sound _ H) as [H1 H2]. cbn in H1, H2 |- *. subst. reflexivity. Qed.
Lemma zfold_at_spec : ltac2:(tb__ "0|1|
S6S2eS6S38S2aS6A1S7dR3R2A2S33S6R1A2A3S3cS4S4S39S38S2aS4A1S60S4S1aR5A1M0R4A3S33S4R1A2A3S39S38S27SbeS18R5A1R1A2S31A3S38S6R3Sb1R5Sb0S4G0R4SbfR1A1A4A2A3A2A2Lo;A2F_;FS';Fi;FS;").
Proof.
  intros S i S' H. unfold zfold_at in H. destruct (nth_error (ss_objs S) i) as [o|]; [|discriminate].
  destruct (zero_covered (ss_facts S) o) eqn:Z0; [|discriminate]. injection H as <-. exists o. auto.
Qed.
Lemma rw_rho_sub : ltac2:(tb__ "0|0|
S5SaaS1S38S5aQ40A1S9SabR3R2A2R1A2S11R3SacR2R1A2A2A3Fv;Fs;Frho;").
Proof. intros. reflexivity. Qed.

Lemma in_u_range : ltac2:(tb__ "0|0|
S0S39S3dZ0R1A2S3dR1Z3A2A2S5dS0R2S63A3F_;Fu;").
Proof. intros u Hu. unfold u_range. assert (u = 0 \/ u = 1 \/ u = 2 \/ u = 3) as [-> | [-> | [-> | ->]]] by lia; cbn; tauto. Qed.
Lemma in_ur_range : ltac2:(tb__ "0|0|
S0S0S5dS0R2S63A3S5dS0R2S7bA3S5dS29S0S0A2S2dS0S0R4R3A4S8aA3F_;F_;Fr;Fu;").
Proof. intros u r Hu Hr. unfold ur_range. apply in_flat_map. exists u. split; [exact Hu|]. apply in_map_iff. exists r. auto. Qed.
Lemma in_r_range : ltac2:(tb__ "0|0|
S0S39S3dZ0R1A2S3dR1Z7A2A2S5dS0S43Z4R2A2S7bA3F_;Fm;").
Proof.
  intros m Hm. unfold r_range.
  assert (m = 0 \/ m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5 \/ m = 6 \/ m = 7) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]] by lia; cbn; tauto.
Qed.
Lemma in_kut_range : ltac2:(tb__ "0|3|
S0S0S0S39S3dZ0M0R3A2S3dR3Z3A2A2M1G1S3aS38S0R3G0A3S38S0R3Z4A3A2S5dS29S29S0S0A2M2S0A2S2dG2S0S2dS0S0R6R5A4R4A4S87A3F_;F_;F_;Ft4;Fu;Fk;").
Proof.
  intros k u t4 Hk Hu Ht. unfold kut_range. apply in_flat_map. exists k. split; [apply in_u_range; lia|].
  apply in_flat_map. exists u. split; [apply in_u_range; lia|]. destruct Ht as [-> | ->]; cbn; tauto.
Qed.
Lemma u_range_bound : ltac2:(tb__ "0|0|
S0S5dS0R1S63A3S39S3dZ0R2A2S3dR2Z3A2A2F_;Fu;").
Proof. intros u Hu. unfold u_range in Hu. cbn in Hu. lia. Qed.

Lemma swf_CZ_u : ltac2:(tb__ "0|0|
S0S5dS0R1S63A3S38S27S13S65R2A1A1S31A3F_;Fu;").
Proof.
  intros u Hu. pose proof (proj1 (forallb_forall _ _) swf_CZ u Hu) as X. cbn beta in X.
  apply andb_prop in X as [X _]. apply andb_prop in X as [X _]. exact X.
Qed.
Lemma s_it_id : ltac2:(tb__ "0|0|
S38S27Sa9S89S53A2S31A3").
Proof. reflexivity. Qed.
Lemma s_en_id : ltac2:(tb__ "0|0|
S0S0S38S27Sa9S7cR2R1A2S53A2S31A3Ft4;Fk;").
Proof. reflexivity. Qed.

Lemma factsCZ_num : ltac2:(tb__ "0|2|
S0S5Sb4S7S1bR1A1S75R2A1A3S39S3dS59Q40M0S9R2PeA2A2M1S58A2S39S3dS80G1A2S3dS59G0S9R2P64A2A2G1A2A2A2F_;Frho;Fu;").
Proof.
  intros u rho HF. unfold factsCZ, factsN in HF. cbn [app] in HF.
  apply Forall_cons_iff in HF as [H1 HF]. apply Forall_cons_iff in HF as [H2 HF]. apply Forall_cons_iff in HF as [H3 _].
  cbn [holds eval zvN zvC N14] in H1, H2, H3. rewrite lit_unsigned in H1, H2.
  change (two62 mod 2 ^ 64) with two62 in H1. change (L2_MIN mod 2 ^ 64) with L2_MIN in H2. auto.
Qed.

Lemma mod4_entry : ltac2:(tb__ "0|2|
S0S0S0S3aS38S0R1Z0M0A3S38S0R1Z4M1A3A2S38S0S41S3fS3fR4S41S3fR4R3A2G1A2A2S3eS3eR3Z38A2R2A2A2G1A2G0A3F_;Ft4;Fk;Fn;").
Proof.
  intros n k t4 Ht. pose proof (Z_div_mod_eq_full (n - k) 4) as E.
  destruct Ht as [-> | ->].
  - replace (n - (n - k) mod 4 - (k + 56 + 0)) with (((n - k) / 4 - 14) * 4) by lia. apply Z_mod_mult.
  - replace (n - (n - k) mod 4 - (k + 56 + 4)) with (((n - k) / 4 - 15) * 4) by lia. apply Z_mod_mult.
Qed.

Section Sound.
Variable J : jpredA.
Hypothesis Hst : stableA segs NF J.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
Sa2Sa2Sa2Sa3R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_run : ltac2:(tb__ "0|1|
S2eS2fS0A1S4aS2fS47A1M0S5S2fS5aQ40A1A1Sa2S38S2aG0A1S50S52R7R6R5S31A5S33G0R4A2A3S38S27SfS48R6A1A1S2bA3SbaS53SbS48R7A1A1A2S47S5S5dS47R2R9A3ScSbS48RbA1A1R9R2A3VTR;S5bS52VJ;S49R4A1R3R9A5R8A2F_;F_;Frho';FL;VTR;S5bS52VJ;R9R7R6A5R5A2F_;F_;F_;F_;FQ;Ftp;Frho;Fleaves;FA;Fcuts;Ffuel;").
Hypothesis TR_refl : ltac2:(tb__ "0|0|
Sa2VTR;R1R1A2FP;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S4aS5S2fS5aQ40A1A1Sa2Sb4S7S1bR3A1S18S48R4A1A1A3VTR;S5bS52VJ;R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FA;").

Lemma run1_TR : ltac2:(tb__ "0|0|
S2eS2fS0A1S4aS47S5S2fS5aQ40A1A1Sa2S38S2aS47A1S66R7R6R5A3S33S47R4A2A3S38S27SfS48R6A1A1S2bA3SbaS53SbS48R7A1A1A2S5ScSbS48R9A1A1R7R1A3VTR;S5bS52VJ;S49R9A1R2R7A5R6A2F_;Frho';VTR;S5bS52VJ;R9R7R6A5R5A2F_;F_;F_;F_;FQ;Ftp;Frho;FL;FA;Fcuts;Ffuel;").
Proof using TR_run.
  intros fuel cuts A L rho tp Q H Hl Hn HQ. unfold run1 in H.
  destruct (sym_runA segs fuel cuts A true) as [[|L' [|]]|] eqn:E; try discriminate H. injection H as ->.
  eapply (TR_run fuel cuts A [L] rho tp Q E Hl Hn). intros L0 rho' [<-|[]] Hag. exact (HQ rho' Hag).
Qed.

Lemma SPA_setreg : ltac2:(tb__ "0|1|
S4aS2eS2S2S5S2fS5aQ40A1M0A1Sa3S38S27S70R7R6R5R4A4S31A3S38G0S11R4R6A2S11R4R5A2A3S5bS52VJ;R9R5R4R3A6S5bS52VJ;S6cRaR9R7A3R6R5R4A6F_;F_;F_;Fw;Ftp;Frho;Fe';Fe;Fr;FA;").
Proof using .
  intros A r e e' rho tp w H He HS. unfold restate_okb in H. apply andb_prop in H as [H Hd]. apply andb_prop in H as [_ Hwf].
  destruct (state_diff (ax_S A) (ax_S (setreg A r e'))) as [[d [|]]|] eqn:E; try discriminate Hd.
  unfold setreg. apply (SPA_restate segs J rho A _ tp w d [] Hwf E); [reflexivity | | constructor | exact HS].
  unfold diffs_ok. apply Forall_forall. intros [a b] Hin. pose proof (proj1 (forallb_forall _ _) Hd _ Hin) as X. cbn [fst snd] in X |- *.
  apply andb_prop in X as [X1 X2]. apply sv_eqb_sound in X1. apply sv_eqb_sound in X2. subst a b. exact He.
Qed.

Lemma TR_post : ltac2:(tb__ "0|0|
S5S5S2fS5aQ40A1A1ScS53R3R2A3VTR;S5bS52VJ;S62S68A1R3R2A5S5cS52VJ;S53R4R2S6aA6A2F_;Ftp;Frho;Frho0;").
Proof using TR_pre TR_refl.
  intros rho0 rho tp Hag. eapply TR_pre; [|apply TR_refl]. intros w Hw.
  apply (LQA_intro segs J NF rho0 tp (mkLeafA (liftA P_msz) RsSymJump) Posts_mszA rho w); [left; reflexivity | exact Hag | exact Hw].
Qed.

Lemma zero_obj_shape : ltac2:(tb__ "0|0|
S4S4S38S2aS4A1Sc0R2A1S33S4R1A2A3S38S4R2SeS20R3A1S22R3A1S21R3A1S30SdA1S17A5A3F_;Fo';Fo;").
Proof.
  intros o o' H. unfold zero_obj in H.
  destruct (ob_lo o) eqn:El; try discriminate H. destruct (ob_hi o) eqn:Eh; try discriminate H. destruct (ob_dflt o); try discriminate H.
  destruct (zcover_from _ _ _); [|discriminate H]. injection H as <-. reflexivity.
Qed.
Lemma zero_obj_range : ltac2:(tb__ "0|0|
S5S4S4S38S2aS4A1Sc0R2A1S33S4R1A2A3S38S29S0S0A2S1dR4R2A2S1dR4R3A2A3F_;Fo';Fo;Frho;").
Proof. intros rho o o' H. rewrite (zero_obj_shape o o' H). unfold obj_range, obj_lo_of, obj_hi_of. reflexivity. Qed.

Lemma fin_sound : ltac2:(tb__ "0|5|
S0S47S5S5S2fS5aQ40M0A1A1S38S27S77R5R4A2S31A3S2aS29S2fS29S2S2A2A1M1S2fS7A1M2A2M3A1OLx;SadS81R6A1S68A2G3G3OLp;R1G1G2G2OLl;R1S38S27S84S3R9A1S8PeM4A1R2A3S31A3S7G2S3bLl0;Ls;X2fx2Ll;Ld2;X29x1Lp;S3bX2ax2S38S27S13S68A1S31A3S38S0S59G0S9R6G4A2A2R8A3ScS53R7R6A3VTR;S5bS52VJ;S49R9A1R7R6A5S5cS52VJ;S53R8R6S6aA6A2F_;F_;F_;F_;F_;Ftp;Frho;Frho0;FL;Fn;").
Proof using Hst TR_pre TR_refl.
  intros n L rho0 rho tp H Hd2 Hwf2 Hn Hag.
  unfold fin_okb in H. apply andb_prop in H as [H Hz]. apply andb_prop in H as [Hret HX].
  destruct (zero_obj_at (ax_S (la_state L)) 0) as [Sz|] eqn:EZ; [|discriminate Hz].
  apply andb_prop in Hz as [Hz Hid]. apply andb_prop in Hz as [Hsame He].
  set (rho2 := rho_sub rho (infer_sub NF Sz (P_lit n))).
  assert (Hag2 : agree_below NF rho rho2) by (apply rho_sub_agree; exact Hid).
  apply (TR_pre (SPA segs J (liftA P_msz) rho2 tp)); [|apply TR_post; eapply agree_below_trans; [exact Hag | exact Hag2]].
  intros w [Hsm HJ].

  assert (HS1 : SPA segs J (liftA Sz) rho tp w).
  { unfold zero_obj_at in EZ. destruct (nth_error (ss_objs (ax_S (la_state L))) 0) as [o|] eqn:En; [|discriminate EZ].
    destruct (zero_obj o) as [o'|] eqn:Eo; [|discriminate EZ].
    assert (ESz : Sz = replace_obj_at (ax_S (la_state L)) 0 o') by (injection EZ as <-; reflexivity).
    assert (HS0 : SPA segs J (ax_setS (la_state L) Sz) rho tp w).
    { rewrite ESz. apply (SPA_replace_obj segs J rho (la_state L) 0 o o' tp w En).
      - exact (zero_obj_range rho o o' Eo).
      - intros ms _ Ho. exact (zero_obj_holds segs rho ms o o' Eo Ho).
      - rewrite <- ESz. exact Hsame.
      - split; [exact Hsm | exact HJ]. }
    rewrite (noX_lift _ _ HX) in HS0. exact HS0. }

  pose proof (SPA_entails segs J NF (liftA Sz) (liftA (P_lit n)) _ rho tp w He Hid Hst HS1) as HS2. fold rho2 in HS2.

  destruct (state_diff (P_lit n) P_msz) as [[d2 [|]]|] eqn:E2; try contradiction.
  change (liftA P_msz) with (ax_setS (liftA (P_lit n)) P_msz).
  apply (SPA_restate segs J rho2 (liftA (P_lit n)) P_msz tp w d2 [] Hwf2 E2); [reflexivity | | constructor | exact HS2].
  unfold diffs_ok. apply Forall_forall. intros [a b] Hin. pose proof (proj1 (forallb_forall _ _) Hd2 _ Hin) as X. cbn [fst snd] in X |- *.
  apply andb_prop in X as [X1 X2]. apply sv_eqb_sound in X1. apply sv_eqb_sound in X2. subst a b. cbn [eval].
  destruct Hag2 as (Hv & _ & _). rewrite <- (Hv 14%positive ltac:(cbv; reflexivity)).
  destruct Hag as (Hv0 & _ & _). rewrite <- (Hv0 14%positive ltac:(cbv; reflexivity)). apply bv_eq. rewrite Z_to_bv_unsigned, Hn.
  pose proof (urange (rw rho0 14)). rewrite bv_wrap_small; [reflexivity|]. rewrite two64. lia.
Qed.

Theorem memsetZ_small : ltac2:(tb__ "0|2|
S2eS5S2fS5aQ40M0A1A1S0S0S39S3dZ0M1R2A2S3dR2Z3A2A2S3aS38S0R2G1A3S38S0R2Z4A3A2S38S27S7aR7S2dS29S0S0A2S0S2dS0S0S59G0S9R6PeA2A2R4A4R3A4A2S31A3F_;F_;Ft4;Fk;VTR;S5bS52VJ;S71R3R2A5S5cS52VJ;S53R3R2S6aA6A2F_;Ftp;Frho;FfuelL;").
Proof using Hst TR_pre TR_refl TR_run.
  intros fuelL rho tp HLn. pose proof (urange (rw rho 14)) as Hr. set (n := U rho 14) in *.
  assert (C0 : lit_okb fuelL (n, 0, 0) = true) by (apply HLn; lia).
  unfold lit_okb in C0.
  destruct (state_diff Pre_msz (Pre_lit n)) as [[d1 [|]]|] eqn:E1; try discriminate C0.
  destruct (state_diff (P_lit n) P_msz) as [[d2 [|]]|] eqn:E2; try discriminate C0.
  apply andb_prop in C0 as [C0 R1]. apply andb_prop in C0 as [C0 W2]. apply andb_prop in C0 as [C0 W1]. apply andb_prop in C0 as [D1 D2].
  assert (HD2 : match state_diff (P_lit n) P_msz with Some (d0, []) => diff_isb (SLit n) (SVar 14) d0 = true | _ => False end) by (rewrite E2; exact D2).

  apply (TR_pre (SPA segs J (liftA (Pre_lit n)) rho tp)).
  { intros w HS. change (liftA (Pre_lit n)) with (ax_setS Pre_mszA (Pre_lit n)).
    apply (SPA_restate segs J rho Pre_mszA (Pre_lit n) tp w d1 [] W1 E1); [reflexivity | | constructor | exact HS].
    unfold diffs_ok. apply Forall_forall. intros [a b] Hin. pose proof (proj1 (forallb_forall _ _) D1 _ Hin) as X. cbn [fst snd] in X |- *.
    apply andb_prop in X as [X1 X2]. apply sv_eqb_sound in X1. apply sv_eqb_sound in X2. subst a b. cbn [eval].
    apply bv_eq. rewrite Z_to_bv_unsigned. subst n. rewrite bv_wrap_small; [reflexivity | rewrite two64; lia]. }

  destruct (run1 fuelL [PC_K] (liftA (Pre_lit n))) as [L1|] eqn:RUN1; [|discriminate R1].
  apply (run1_TR fuelL [PC_K] (liftA (Pre_lit n)) L1 rho tp _ RUN1 eq_refl (Pos.le_refl _)).
  intros rho1 Hag1. cbn [ax_S liftA mkA ss_next] in Hag1.
  destruct (is_ret L1) eqn:RET1.
  { apply (fin_sound n L1 rho rho1 tp R1 HD2 W2 eq_refl Hag1). }
  apply andb_prop in R1 as [CUT1 _]. destruct (is_cut_sound L1 PC_K CUT1) as (_ & Hl1 & Hn1).
  set (k := bv_unsigned (eval rho1 KX)). pose proof (U_KX_range rho1) as Hk. fold k in Hk.
  assert (C1 : lit_okb fuelL (n, k, 0) = true) by (apply HLn; lia).
  unfold lit_okb in C1. rewrite E1, E2, RUN1, RET1 in C1.
  apply andb_prop in C1 as [_ C1]. apply andb_prop in C1 as [_ S2]. unfold stage2 in S2. apply andb_prop in S2 as [RS1 S2].
  apply (TR_pre (SPA segs J (setreg (la_state L1) 13 (SLit k)) rho1 tp)).
  { intros w HS. apply (SPA_setreg (la_state L1) 13 KX (SLit k) rho1 tp w RS1); [|exact HS]. cbn [eval]. apply bv_eq. rewrite Z_to_bv_unsigned. subst k.
    pose proof (urange (eval rho1 KX)). rewrite bv_wrap_small; [reflexivity | rewrite two64; lia]. }
  destruct (run1 fuelL [PC_T] (setreg (la_state L1) 13 (SLit k))) as [L2|] eqn:RUN2; [|discriminate S2].
  destruct (restate_keeps (la_state L1) 13 (SLit k)) as [Kn Kl].
  apply (run1_TR fuelL [PC_T] _ L2 rho1 tp _ RUN2 ltac:(rewrite Kl; exact Hl1) ltac:(rewrite Kn; exact Hn1)).
  intros rho2 Hag2. rewrite Kn in Hag2.
  assert (Hag02 : agree_below NF rho rho2) by (eapply agree_below_trans; [exact Hag1 | eapply agree_below_le; [exact Hn1 | exact Hag2]]).
  destruct (is_ret L2) eqn:RET2.
  { apply (fin_sound n L2 rho rho2 tp S2 HD2 W2 eq_refl Hag02). }
  apply andb_prop in S2 as [CUT2 _]. destruct (is_cut_sound L2 PC_T CUT2) as (_ & Hl2 & Hn2).
  set (t4 := bv_unsigned (eval rho2 (T4X k))). pose proof (U_T4X_cases rho2 k) as Ht. fold t4 in Ht.
  assert (C2 : lit_okb fuelL (n, k, t4) = true) by (apply HLn; lia).
  unfold lit_okb in C2. rewrite E1, E2, RUN1, RET1 in C2.
  apply andb_prop in C2 as [_ C2]. apply andb_prop in C2 as [_ S3]. unfold stage2 in S3. apply andb_prop in S3 as [_ S3].
  rewrite RUN2, RET2 in S3. apply andb_prop in S3 as [_ S3]. unfold stage3 in S3. apply andb_prop in S3 as [RS2 S3].
  apply (TR_pre (SPA segs J (setreg (la_state L2) 15 (SLit t4)) rho2 tp)).
  { intros w HS. apply (SPA_setreg (la_state L2) 15 (T4X k) (SLit t4) rho2 tp w RS2); [|exact HS]. cbn [eval]. apply bv_eq. rewrite Z_to_bv_unsigned. subst t4.
    pose proof (urange (eval rho2 (T4X k))). rewrite bv_wrap_small; [reflexivity | rewrite two64; lia]. }
  destruct (run1 fuelL [] (setreg (la_state L2) 15 (SLit t4))) as [L3|] eqn:RUN3; [|discriminate S3].
  destruct (restate_keeps (la_state L2) 15 (SLit t4)) as [Kn2 Kl2].
  apply (run1_TR fuelL [] _ L3 rho2 tp _ RUN3 ltac:(rewrite Kl2; exact Hl2) ltac:(rewrite Kn2; exact Hn2)).
  intros rho3 Hag3. rewrite Kn2 in Hag3.
  assert (Hag03 : agree_below NF rho rho3) by (eapply agree_below_trans; [exact Hag02 | eapply agree_below_le; [exact Hn2 | exact Hag3]]).
  apply (fin_sound n L3 rho rho3 tp S3 HD2 W2 eq_refl Hag03).
Qed.

Lemma it_TR : ltac2:(tb__ "0|2|
S2eS0S5S2fS5aQ40M0A1A1Sa2S5dS0R4S63A3S38S27S79R6R5A2S31A3S3dS3eS3eS59G0S9R5P64M1A2A2Z40A2R6A2S59G0S9R5PeA2A2A2S5ScS53R7R1A3S38S0S59G0S9R2G1A2A2S3eS59G0S9R8G1A2A2Z20A2A3VTR;S5bS52VJ;S62S65RaA1A1R3R8A5R7A2F_;F_;Frho';VTR;S5bS52VJ;S62S65R8A1A1R7R6A5R5A2F_;F_;F_;F_;FQ;Ftp;Frho;Fu;FfuelI;").
Proof using Hst TR_pre TR_run TR_facts.
  intros fuelI u rho tp Q Hu C HR HK. pose proof (u_range_bound u Hu) as Hub. unfold it_okb in C.
  apply andb_prop in C as [FB C].
  destruct (run1 fuelI [ZBODY] (CZi u)) as [L|] eqn:RUN; [|discriminate C].
  apply andb_prop in C as [C1 C]. apply andb_prop in C1 as [CUT NX].
  destruct (split_obj_at (ax_S (la_state L)) 1 (addl zvC 32)) as [S1|] eqn:SP; [|discriminate C].
  destruct (zfold_at S1 1) as [S2|] eqn:ZF; [|discriminate C].
  destruct (merge_objs_at S2 0) as [S3|] eqn:MG; [|discriminate C].
  apply TR_facts. intros HF. cbn [ax_S liftA mkA ss_facts CZ] in HF. destruct (factsCZ_num u rho HF) as (B1 & B2 & B3).
  pose proof (urange (rw rho 100)) as H100. unfold two62 in B1.

  apply (TR_pre (SPA segs J (CZi u) rho tp)).
  { intros w HS. unfold CZi. apply (SPA_refacts segs J rho (liftA (CZ u)) _ tp w HS FB).
    intros HF0. constructor; [|exact HF0]. cbn [holds eval zvN zvC addl]. rewrite add_val, lit_unsigned.
    rewrite (Z.mod_small (64 + u)) by lia. rewrite Z.mod_small; lia. }
  apply (run1_TR fuelI [ZBODY] (CZi u) L rho tp Q RUN eq_refl ltac:(apply Pos.leb_le; reflexivity)).
  intros rho1 Hag1. cbn [CZi ax_with_facts ax_S ax_setS liftA mkA with_facts ss_next CZ] in Hag1.
  destruct (is_cut_sound L ZBODY CUT) as (_ & Hl & Hn).
  destruct (zfold_at_spec S1 1 S2 ZF) as (o & Ho & Hz & ->).
  apply (TR_pre (SPA segs J (liftA (CZ u)) (rho_sub rho1 s_it) tp)).
  { intros w HS.
    pose proof (SPA_split segs J rho1 (la_state L) 1 (addl zvC 32) S1 tp w SP HS) as HS1.
    pose proof (SPA_zero_fold segs J rho1 (ax_setS (la_state L) S1) tp w 1 o Ho Hz HS1) as HS2.
    pose proof (SPA_merge segs J rho1 (ax_setS (la_state L) (set_objs S1 (list_set (ss_objs S1) 1 (zobj o)))) 0 S3 tp w MG HS2) as HS3.
    exact (SPA_entails segs J NF _ _ s_it rho1 tp w C s_it_id Hst HS3). }
  apply HK.
  - eapply agree_below_trans; [eapply agree_below_le; [|exact Hag1]; apply Pos.leb_le; reflexivity | apply rho_sub_agree; exact s_it_id].
  - rewrite rw_rho_sub. change (wsub_get s_it 100) with (SAlu ALU_ADD (SVar 100) (SLit 32)). rewrite U_add, U_lit. cbn [eval].
    destruct Hag1 as (Hv & _ & _). rewrite <- (Hv 100%positive ltac:(cbv; reflexivity)).
    change (32 mod M64v) with 32. rewrite Z.mod_small; [reflexivity|]. unfold M64v. lia.
Qed.

Lemma ex_TR : ltac2:(tb__ "0|1|
S2eS0S0S5S5S2fS5aQ40M0A1A1S5dS0R5S63A3S38S27S74R7S2dS0S0R6R5A4A2S31A3S3dZ0R6A2ScS53R6R5A3S38S0S3fS3fS59G0S9R6PeA2A2R9A2S59G0S9R6P64A2A2A2S3eZ20R8A2A3VTR;S5bS52VJ;S62S65RaA1A1R7R6A5S5cS52VJ;S53R8R6S6aA6A2F_;F_;F_;F_;F_;Ftp;Frho;Frho0;Fr;Fu;FfuelX;").
Proof using Hst TR_pre TR_run TR_facts TR_refl.
  intros fuelX u r rho0 rho tp Hu C Hr Hag0 HR. pose proof (u_range_bound u Hu) as Hub. unfold ex_okb in C.
  destruct (guard fuelX (merge_objs_at (CZ u) 1)) as [Sm|] eqn:MG1; [|discriminate C]. apply guard_Some in MG1.
  apply andb_prop in C as [C RN]. apply andb_prop in C as [WF DF]. apply andb_prop in WF as [NXM WF]. apply Pos.eqb_eq in NXM.
  destruct (state_diff Sm (CZX u r)) as [[d [|]]|] eqn:SD; try discriminate DF.
  destruct (run1 fuelX [] (liftA (CZX u r))) as [L|] eqn:RUN; [|discriminate RN].
  apply andb_prop in RN as [C1 RN]. apply andb_prop in C1 as [RET NX].
  destruct (zfold_at (ax_S (la_state L)) 1) as [S2|] eqn:ZF; [|discriminate RN].
  destruct (merge_objs_at S2 0) as [S3|] eqn:MG; [|discriminate RN].
  apply andb_prop in RN as [EN ID].
  apply TR_facts. intros HF. cbn [ax_S liftA mkA ss_facts CZ] in HF. destruct (factsCZ_num u rho HF) as (B1 & B2 & B3).
  pose proof (urange (rw rho 100)) as H100. unfold two62 in B1.

  apply (TR_pre (SPA segs J (liftA (CZX u r)) rho tp)).
  { intros w HS.
    pose proof (SPA_merge segs J rho (liftA (CZ u)) 1 Sm tp w MG1 HS) as HS1.
    change (liftA (CZX u r)) with (ax_setS (ax_setS (liftA (CZ u)) Sm) (CZX u r)).
    apply (SPA_restate segs J rho (ax_setS (liftA (CZ u)) Sm) (CZX u r) tp w d [] WF SD); [ | | constructor | exact HS1].
    -
      cbn [ax_S ax_setS]. rewrite NXM. reflexivity.
    - unfold diffs_ok. apply Forall_forall. intros [a b] Hin.
      pose proof (proj1 (forallb_forall _ _) DF _ Hin) as X. unfold pair_inb, xdiffs in X. cbn [existsb fst snd] in X.
      assert (E3 : eval rho zvC = eval rho (eX u r)).
      { apply bv_eq. unfold eX, addl, zvC, zvN. rewrite U_add, U_lit. cbn [eval]. rewrite add_neg_lit; unfold M64v in *; lia. }
      rewrite !Bool.orb_false_r in X.
      apply Bool.orb_prop in X as [X|X]; [|apply Bool.orb_prop in X as [X|X]];
        apply andb_prop in X as [X1 X2]; apply sv_eqb_sound in X1; apply sv_eqb_sound in X2; subst a b; cbn [fst snd].
      + cbn [eval]. rewrite E3. reflexivity.
      + apply bv_eq. unfold remC, addl, zvN, zvC. rewrite U_sub, U_add, !U_lit. cbn [eval].
        rewrite (add_neg_lit (U rho 14) u) by (unfold M64v in *; lia). rewrite !Z.mod_small; unfold M64v in *; lia.
      + exact E3. }
  apply (run1_TR fuelX [] (liftA (CZX u r)) L rho tp _ RUN eq_refl ltac:(apply Pos.leb_le; reflexivity)).
  intros rho1 Hag1. cbn [ax_S liftA mkA ss_next CZX] in Hag1.
  destruct (zfold_at_spec _ 1 S2 ZF) as (o & Ho & Hz & ->).
  set (s := infer_sub NF S3 P_msz) in *.
  apply (TR_pre (SPA segs J (liftA P_msz) (rho_sub rho1 s) tp)).
  { intros w HS.
    pose proof (SPA_zero_fold segs J rho1 (la_state L) tp w 1 o Ho Hz HS) as HS2.
    pose proof (SPA_merge segs J rho1 (ax_setS (la_state L) (set_objs (ax_S (la_state L)) (list_set (ss_objs (ax_S (la_state L))) 1 (zobj o)))) 0 S3 tp w MG HS2) as HS3.
    exact (SPA_entails segs J NF _ _ s rho1 tp w EN ID Hst HS3). }
  apply TR_post. eapply agree_below_trans; [exact Hag0|].
  eapply agree_below_trans; [eapply agree_below_le; [|exact Hag1]; apply Pos.leb_le; reflexivity | apply rho_sub_agree; exact ID].
Qed.

Lemma loop_TR : ltac2:(tb__ "0|1|
S2eS2eS0S5dS0R1S63A3S38S27S79R4R2A2S31A3S0S5dS0R1S7bA3S38S27S74R6S2dS0S0R5R2A4A2S31A3F_;Fr;S2eS0S5S5S2fS5aQ40M0A1A1S3dZ0R4A2S45R5S43Z8S44R6A1A2A2ScS53R5R4A3S38S0S3fS3fS59G0S9R5PeA2A2RcA2S59G0S9R5P64A2A2A2S3eZ20S43Z4R7A2A2A3VTR;S5bS52VJ;S62S65RdA1A1R6R5A5S5cS52VJ;S53R7R5S6aA6A2F_;F_;F_;F_;Ftp;Frho;Frho0;Fm;Fc;F_;F_;F_;Fu;FfuelX;FfuelI;").
Proof using Hst TR_pre TR_run TR_facts TR_refl.
  intros fuelI fuelX u Hu HIu HXu c. induction c as [|c IH]; intros m rho0 rho tp Hm Hc Hag HR; [lia|].
  pose proof (u_range_bound u Hu) as Hub.
  destruct (Z.le_gt_cases 8 m) as [Hbig|Hsmall].
  - apply (it_TR fuelI u rho tp _ Hu HIu); [lia|]. intros rho' Hag' H100.
    assert (E14 : U rho' 14 = U rho 14) by (destruct Hag' as (Hv & _ & _); rewrite <- (Hv 14%positive ltac:(cbv; reflexivity)); reflexivity).
    apply (IH (m - 8) rho0 rho' tp); [lia | lia | eapply agree_below_trans; [exact Hag | exact Hag'] | rewrite E14, H100; lia].
  - apply (ex_TR fuelX u (4 * m) rho0 rho tp Hu); [apply HXu; apply in_r_range; lia | lia | exact Hag | lia].
Qed.

Lemma en_TR : ltac2:(tb__ "0|7|
S2eS5S2fS5aQ40M0A1A1Sa2S0S0S0S39S3dZ0M1R3A2S3dR3Z3A2A2M2G2S3aS38S0R3G1A3S38S0R3Z4M3A3A2S38S27S86RaS2dS29S0S0A2S0S2dS0S0R6R5A4R4A4A2S31A3F_;F_;F_;Ft4;Fu;Fk;S3dS80S59G0S9R4PeM4A2A2M5A2S0S5S5dS0R2S63A3ScS53R8R2A3S38S0S41S3fS3fS59G0S9R3G4A2A2R4A2S59G0S9R3P64M6A2A2A2G3A2G1A3S3dZ20S3fS3fG5R5A2S59G0S9R4G6A2A2A2A2VTR;S5bS52VJ;S62S65R6A1A1R5RaA5R9A2F_;F_;F_;F_;Frho';Fu;VTR;S5bS52VJ;S71R6R5A5R4A2F_;F_;F_;FQ;Ftp;Frho;FfuelE;").
Proof using Hst TR_pre TR_run TR_facts.
  intros fuelE rho tp Q HEf Hn HK. pose proof (urange (rw rho 14)) as Hr.
  apply TR_facts. intros HF0. cbn [ax_S Pre_mszA liftA mkA ss_facts Pre_msz] in HF0.
  assert (B62 : U rho 14 <= two62).
  { apply Forall_cons_iff in HF0 as [H1 _]. cbn [holds eval N14] in H1. rewrite lit_unsigned in H1. change (two62 mod 2 ^ 64) with two62 in H1. exact H1. }
  unfold two62 in B62.

  pose proof (HEf 0 0 0 ltac:(lia) ltac:(lia) ltac:(lia)) as C0. unfold en_okb in C0.
  destruct (guard fuelE (split_obj_at (ax_S Pre_big) 0 eT)) as [S0|] eqn:SP0; [|discriminate C0].
  pose proof (guard_Some _ _ _ SP0) as SP0'.
  apply andb_prop in C0 as [NS0 C0]. apply andb_prop in NS0 as [NXT0 LEN0]. apply Pos.eqb_eq in NXT0.
  assert (LEN0' : ss_lenient S0 = false) by (destruct (ss_lenient S0); [discriminate LEN0 | reflexivity]). clear LEN0. rename LEN0' into LEN0.
  destruct (run1 fuelE [PC_K] (ax_setS Pre_big S0)) as [L1|] eqn:RUN1; [|discriminate C0].
  apply andb_prop in C0 as [C0 _]. apply andb_prop in C0 as [CUT1 _]. destruct (is_cut_sound L1 PC_K CUT1) as (_ & Hl1 & Hn1).

  apply (TR_pre (SPA segs J (ax_setS Pre_big S0) rho tp)).
  { intros w HS. apply (SPA_split segs J rho Pre_big 0 eT S0 tp w SP0').
    unfold Pre_big. apply (SPA_refacts segs J rho Pre_mszA factsN tp w HS ltac:(reflexivity)).
    intros HF. constructor; [apply Forall_cons_iff in HF as [H1 _]; exact H1|]. constructor; [|constructor].
    cbn [holds eval zvN]. rewrite lit_unsigned. change (L2_MIN mod 2 ^ 64) with L2_MIN. exact Hn. }
  apply (run1_TR fuelE [PC_K] (ax_setS Pre_big S0) L1 rho tp Q RUN1 LEN0 ltac:(cbn [ax_S ax_setS]; rewrite NXT0; apply Pos.le_refl)).
  intros rho1 Hag1. cbn [ax_S ax_setS] in Hag1. rewrite NXT0 in Hag1.
  assert (E14a : U rho1 14 = U rho 14) by (destruct Hag1 as (Hv & _ & _); rewrite <- (Hv 14%positive ltac:(cbv; reflexivity)); reflexivity).

  set (k := bv_unsigned (eval rho1 KX)). pose proof (U_KX_range rho1) as Hk. fold k in Hk.
  set (u := (U rho 14 - k) mod 4). pose proof (Z.mod_pos_bound (U rho 14 - k) 4 ltac:(lia)) as Hu. fold u in Hu.
  pose proof (HEf k u 0 ltac:(lia) ltac:(lia) ltac:(lia)) as C1. unfold en_okb in C1.
  rewrite SP0, RUN1 in C1. apply andb_prop in C1 as [_ C1]. apply andb_prop in C1 as [C1a C1]. apply andb_prop in C1a as [_ RS1].
  apply (TR_pre (SPA segs J (setreg (la_state L1) 13 (SLit k)) rho1 tp)).
  { intros w HS. apply (SPA_setreg (la_state L1) 13 KX (SLit k) rho1 tp w RS1); [|exact HS]. cbn [eval]. apply bv_eq. rewrite Z_to_bv_unsigned. subst k.
    pose proof (urange (eval rho1 KX)). rewrite bv_wrap_small; [reflexivity | rewrite two64; lia]. }
  destruct (run1 fuelE [PC_N] (setreg (la_state L1) 13 (SLit k))) as [L2|] eqn:RUN2; [|discriminate C1].
  destruct (restate_keeps (la_state L1) 13 (SLit k)) as [Kn1 Kl1].
  apply (run1_TR fuelE [PC_N] _ L2 rho1 tp _ RUN2 ltac:(rewrite Kl1; exact Hl1) ltac:(rewrite Kn1; exact Hn1)).
  intros rho2 Hag2. rewrite Kn1 in Hag2.
  assert (Hag02 : agree_below NF rho rho2) by (eapply agree_below_trans; [exact Hag1 | eapply agree_below_le; [exact Hn1 | exact Hag2]]).
  assert (E14b : U rho2 14 = U rho 14) by (destruct Hag02 as (Hv & _ & _); rewrite <- (Hv 14%positive ltac:(cbv; reflexivity)); reflexivity).
  apply andb_prop in C1 as [C1a C1]. apply andb_prop in C1a as [CUT2 RS2]. destruct (is_cut_sound L2 PC_N CUT2) as (_ & Hl2 & Hn2).
  apply (TR_pre (SPA segs J (setreg (la_state L2) 14 (NAk k u)) rho2 tp)).
  { intros w HS. apply (SPA_setreg (la_state L2) 14 (NXk k) (NAk k u) rho2 tp w RS2); [|exact HS].
    subst u. rewrite <- E14b. apply U_NX; [lia|]. rewrite E14b. unfold L2_MIN in Hn. lia. }
  destruct (run1 fuelE [PC_T] (setreg (la_state L2) 14 (NAk k u))) as [L3|] eqn:RUN3; [|discriminate C1].
  destruct (restate_keeps (la_state L2) 14 (NAk k u)) as [Kn2 Kl2].
  apply (run1_TR fuelE [PC_T] _ L3 rho2 tp _ RUN3 ltac:(rewrite Kl2; exact Hl2) ltac:(rewrite Kn2; exact Hn2)).
  intros rho3 Hag3. rewrite Kn2 in Hag3.
  assert (Hag03 : agree_below NF rho rho3) by (eapply agree_below_trans; [exact Hag02 | eapply agree_below_le; [exact Hn2 | exact Hag3]]).
  apply andb_prop in C1 as [C1a _]. apply andb_prop in C1a as [CUT3 _]. destruct (is_cut_sound L3 PC_T CUT3) as (_ & Hl3 & Hn3).

  set (t4 := bv_unsigned (eval rho3 (T4X k))). pose proof (U_T4X_cases rho3 k) as Ht. fold t4 in Ht.
  pose proof (HEf k u t4 ltac:(lia) ltac:(lia) ltac:(lia)) as C2. unfold en_okb in C2.
  rewrite SP0, RUN1, RUN2, RUN3 in C2.
  apply andb_prop in C2 as [_ C2]. apply andb_prop in C2 as [_ C2]. apply andb_prop in C2 as [_ C2]. apply andb_prop in C2 as [C2a C2]. apply andb_prop in C2a as [_ RS3].
  apply (TR_pre (SPA segs J (setreg (la_state L3) 15 (SLit t4)) rho3 tp)).
  { intros w HS. apply (SPA_setreg (la_state L3) 15 (T4X k) (SLit t4) rho3 tp w RS3); [|exact HS]. cbn [eval]. apply bv_eq. rewrite Z_to_bv_unsigned. subst t4.
    pose proof (urange (eval rho3 (T4X k))). rewrite bv_wrap_small; [reflexivity | rewrite two64; lia]. }
  destruct (run1 fuelE [ZBODY] (setreg (la_state L3) 15 (SLit t4))) as [L4|] eqn:RUN4; [|discriminate C2].
  destruct (restate_keeps (la_state L3) 15 (SLit t4)) as [Kn3 Kl3].
  apply (run1_TR fuelE [ZBODY] _ L4 rho3 tp _ RUN4 ltac:(rewrite Kl3; exact Hl3) ltac:(rewrite Kn3; exact Hn3)).
  intros rho4 Hag4. rewrite Kn3 in Hag4.
  assert (Hag04 : agree_below NF rho rho4) by (eapply agree_below_trans; [exact Hag03 | eapply agree_below_le; [exact Hn3 | exact Hag4]]).
  apply andb_prop in C2 as [CUT4 C2]. destruct (is_cut_sound L4 ZBODY CUT4) as (_ & Hl4 & Hn4).
  destruct (run1 fuelE [ZBODY] (la_state L4)) as [L5|] eqn:RUN5; [|discriminate C2].
  apply (run1_TR fuelE [ZBODY] _ L5 rho4 tp _ RUN5 Hl4 Hn4).
  intros rho5 Hag5.
  assert (Hag05 : agree_below NF rho rho5) by (eapply agree_below_trans; [exact Hag04 | eapply agree_below_le; [exact Hn4 | exact Hag5]]).
  apply andb_prop in C2 as [C2a C2]. apply andb_prop in C2a as [CUT5 NX5].
  destruct (split_obj_at (ax_S (la_state L5)) 0 (SLit (k + 56 + t4))) as [S5|] eqn:SP5; [|discriminate C2].
  destruct (zfold_at S5 0) as [S6|] eqn:ZF; [|discriminate C2].
  destruct (zfold_at_spec S5 0 S6 ZF) as (o & Ho & Hz & ->).
  apply (TR_pre (SPA segs J (liftA (CZ u)) (rho_sub rho5 (s_en k t4)) tp)).
  { intros w HS.
    pose proof (SPA_split segs J rho5 (la_state L5) 0 _ S5 tp w SP5 HS) as HS1.
    pose proof (SPA_zero_fold segs J rho5 (ax_setS (la_state L5) S5) tp w 0 o Ho Hz HS1) as HS2.
    exact (SPA_entails segs J NF _ _ (s_en k t4) rho5 tp w C2 (s_en_id k t4) Hst HS2). }
  assert (E14c : U (rho_sub rho5 (s_en k t4)) 14 = U rho 14).
  { rewrite rw_rho_sub. cbn [wsub_get s_en Pos.eqb eval]. destruct Hag05 as (Hv & _ & _). rewrite <- (Hv 14%positive ltac:(cbv; reflexivity)). reflexivity. }
  assert (E100 : U (rho_sub rho5 (s_en k t4)) 100 = k + 56 + t4).
  { rewrite rw_rho_sub. cbn [wsub_get s_en Pos.eqb eval]. rewrite lit_unsigned. apply Z.mod_small. lia. }
  apply (HK u); [apply in_u_range; lia | | |].
  - eapply agree_below_trans; [exact Hag05 | apply rho_sub_agree; apply s_en_id].
  - rewrite E14c, E100. subst u. apply mod4_entry. exact Ht.
  - rewrite E14c, E100. unfold L2_MIN in Hn. lia.
Qed.

Theorem memsetZ_TR : ltac2:(tb__ "0|2|
S2eS2eS2eS2eS29S29S0S0A2M0S0A2M1S5dG1R1S88A3S38S27S7aR6R2A2S31A3F_;Fc;S0S5dS0R1S63A3S38S27S79R6R2A2S31A3F_;Fu;G0S5dG0R1S8aA3S38S27S74R6R2A2S31A3F_;Fur;G1S5dG1R1S87A3S38S27S86R6R2A2S31A3F_;Fc;S5S2fS5aQ40A1A1VTR;S5bS52VJ;S71R2R1A5S5cS52VJ;S53R2R1S6aA6A2Ftp;Frho;F_;F_;F_;F_;FfuelE;FfuelX;FfuelI;FfuelL;").
Proof using Hst TR_pre TR_run TR_facts TR_refl.
  intros fuelL fuelI fuelX fuelE HL HI HX HE rho tp.
  destruct (Z.le_gt_cases (U rho 14) L1_MAX) as [Hs|Hb].
  { apply (memsetZ_small fuelL). intros k t4 Hk Ht. apply HL. apply lit_range_in; [pose proof (urange (rw rho 14)); lia | exact Hk | exact Ht]. }
  apply (en_TR fuelE); [intros k u t4 Hk Hu Ht; apply HE; apply in_kut_range; [exact Hk | exact Hu | exact Ht] | unfold L1_MAX, L2_MIN in *; lia|].
  intros u rho' Hu Hag Hmod Hge.
  pose proof (Z_div_mod_eq_full (U rho' 14 - u - U rho' 100 - 32) 4) as Hdm.
  pose proof (Z.mod_pos_bound (U rho' 14 - u - U rho' 100 - 32) 4 ltac:(lia)) as Hmb.
  set (m := (U rho' 14 - u - U rho' 100 - 32) / 4) in *.
  assert (Hm4 : (U rho' 14 - u - U rho' 100 - 32) mod 4 = 0).
  { rewrite Zminus_mod, Hmod. reflexivity. }
  apply (loop_TR fuelI fuelX u Hu (HI u Hu) ltac:(intros r Hr; apply HX; apply in_ur_range; [exact Hu | exact Hr]) (S (Z.to_nat m)) m rho rho' tp);
    [lia | rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia | exact Hag | lia].
Qed.
End Sound.

Section Inst.
Variable ok : assn.
Variable J : jpredA.
Hypothesis Hok : ok_frameA segs ok J.
Hypothesis Hst : stableA segs NF J.

Theorem memsetZ_sumA : ltac2:(tb__ "0|0|
S5S2fS5aQ40A1A1Sa5S52Vok;S5bS52VJ;S71R2R1A5S5cS52VJ;S53R2R1S6aA6A4Ftp;Frho;").
Proof.
  eapply (memsetZ_TR J Hst (triple segs ok)).
  - intros P P' Q HP HT. eapply triple_conseq; [exact HP | intros w Hw; exact Hw | exact HT].
  - intros fuel cuts A leaves rho tp Q Hrun Hl Hn HQ. eapply (runA_tr segs ok fuel cuts A leaves J rho tp Q Hrun Hl Hok (stableA_mono segs _ _ _ Hn Hst)). exact HQ.
  - apply triple_refl.
  - intros A rho tp Q H. apply triple_factsA. exact H.
  - exact (proj1 (forallb_forall _ _) lit_allb).
  - exact (proj1 (forallb_forall _ _) it_allb).
  - exact (proj1 (forallb_forall _ _) ex_allb).
  - exact (proj1 (forallb_forall _ _) en_allb).
Qed.
End Inst.

Section InstEx.
Variable J : jpredA.
Hypothesis Hst : stableA segs NF J.
Theorem memsetZ_sumA_ex : ltac2:(tb__ "0|0|
S5S2fS5aQ40A1A1Sa4S52S5bS52VJ;S71R2R1A5S5cS52VJ;S53R2R1S6aA6A3Ftp;Frho;").
Proof.
  eapply (memsetZ_TR J Hst (etriple segs)).
  - intros P P' Q HP HT. eapply etriple_conseq; [exact HP | intros w Hw; exact Hw | exact HT].
  - intros fuel cuts A leaves rho tp Q Hrun Hl Hn HQ. eapply (erunA_tr segs fuel cuts A leaves J rho tp Q Hrun Hl (stableA_mono segs _ _ _ Hn Hst)). exact HQ.
  - apply etriple_refl.
  - intros A rho tp Q H. apply etriple_factsA. exact H.
  - exact (proj1 (forallb_forall _ _) lit_allb).
  - exact (proj1 (forallb_forall _ _) it_allb).
  - exact (proj1 (forallb_forall _ _) ex_allb).
  - exact (proj1 (forallb_forall _ _) en_allb).
Qed.
End InstEx.
End StartMemsetZ.

