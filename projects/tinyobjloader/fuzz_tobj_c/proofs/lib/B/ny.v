(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9 np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAF.

(* [comment removed for export] *)
Module Lib_builder_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "valuation"; "SPUle"; "sobj"; "holds"; "SAlu"; "SVar"; "obj_range"; "rw"; "ss_facts"; "sv_eqb"; "ob_base"; "ob_hi"; "ob_lo"; "soff"; "sprop_eqb"; "DUnknown"; "SPEq"; "cell"; "ss_objs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "prod"; "cons"; "bool"; "true"; "pair"; "fst"; "snd"; "None"; "nat"; "nil"; "option"; "andb"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "True"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "pow"; "div"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "vb"; "vAL"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "pclMA"; "FFx"; "xrs_okL"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf"; "baseF"; "extraO"; "basez"; "extraX"; "frameF"; "in_callers"; "vb184"; "P0_builder"; "base_facts"; "extra_tab"; "frame_facts"; "framez"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double.ScanDoubleAddr"; "pow10_tab"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double"; "vB"; "vL"; "two26"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T_ok"; "tvd"; "tvz"; "remove_nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "TPA"; "frinA"; "tvinA"; "fbinA"; "ffinA"; "ANone"; "NDA"; "PTrue"; "frozen"; "nd_below"; "ndesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "axst"; "g8"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "is_shadowZ"; "payA"; "robjs_okA"; "site_okA"; "xrs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "robjs_checkF"; "xrs_checkL"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT"; "robjs_checkP"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "robjs_okF"; "xrs_ok47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "alloc_lawsA"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_scan_double_ex.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_vec_reserve_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma uval_add_litZ : ltac2:(tb__ "0|0|
S3S0S16S29Z0R1A2S2aS2bS2fR4R3A2R2A2S2cZ2Z40A2A2S26S16S2fR5S7S3aR4S2R3A1A3A2S2bS2fR5R4A2R3A2A3F_;F_;Fk;Fa;Frho;").
Proof. intros rho a k Hk H. pose proof (uval_range rho a). rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity. Qed.

Lemma obj_rangeZ : ltac2:(tb__ "0|2|
S3S5S16S16S16S25S29S1eS16S16S9R5R4A2M0A3R3A2S2aR3S1fS16S16G0A3A2A2S26S16S10R6SfR5A1A2R3A3S26S16S10R7SeR6A1A2R3A3S25S29S2bS2fR8SdR7A1A2M1R5A2R6A2S2aR6S2bG1R4A2A2A2F_;F_;F_;Fhi;Flo;Fa;Fo;Frho;").
Proof. intros rho o a lo hi Hr <- <-. unfold obj_range, obj_lo_of, obj_hi_of in Hr. unfold uval. exact Hr. Qed.

Definition P0_builder (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S25S16S25S29S51Q40M0SaVr;PfA2A2M1R1A2S2aR1S2bG1S51G0SaVr;P12A2A2A2A2A2S37VCST;Vr;VFB;VFF;R2A5F_;Fa;S25S57VFF;S51G0SaVr;PcA2A2Z518A3S57VFF;S51G0SaVr;P3aA2A2Z30A3A2A2").

Lemma pclMA_mono : ltac2:(tb__ "0|2|
S18S19S16S16A2M0A1M1S3G1S18S19G0S16A2A1S3S18S19S0S0A2A1S18S19S19S0S16A2S0A2A1S16S37R8R7R6R5R1A5S37R9R8S52R7R5R4A3S38R6R5R3A3R2A5F_;Fa;Ffrs;Fkept;Frho;FFF;FFB;Frho0;FCST;").
Proof.
  intros CST rho0 FB FF rho kept frs a [H|[H|[(b & n & Hin & Hr)|(f & s & fl & Hin & Hr)]]]; [left; exact H | right; left; exact H | |].
  - right; right; left. exists b, n. split; [apply In_FBx; left; exact Hin | exact Hr].
  - right; right; right. exists f, s, fl. split; [apply In_FFx; left; exact Hin | exact Hr].
Qed.

Definition base_facts (DW : Z) : list sprop := ltac2:(tb__ "0|4|
S1aS1S4S8PaA1M0S2S76A1M1A2S1aS1S4S7S3aS8P1eA1M2S2VDW;A1A3G0A2S1aS1S4S2S4fA1M3S33A2S1aS1S4S7S3aS33S2Z518A1A3G2A2S1aS1S4S33G1A2S1aS1S4G3S34A2S1aS1S4S7S3aS34S2Z30A1A3G2A2S1aS1S4S34G1A2S1aS1S4S4dS2S4eA1A2S1aS1S4S4cG1A2S1aS1S4S2Z7fff7f800000A1G2A2S1aS1S4G2S2Z7fffff800000A1A2S22S1A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition baseF (DW : Z) (F : list sprop) : bool := ltac2:(tb__ "0|0|
S69S1S1S68S1S11R1A1VF;A3Lp;S43VDW;A1A3").
Record basez (DW : Z) (rho : valuation) : Prop := BZ {
  bz_sp : aceil + DW <= uval rho (SVar 10) <= 2 ^ 47;
  bz_b : IMG_HI <= uval rho vb /\ uval rho vb + 1304 <= bv_unsigned (rw rho V_TOP);
  bz_al : IMG_HI <= uval rho vAL /\ uval rho vAL + 48 <= bv_unsigned (rw rho V_TOP);
  bz_L : uval rho vL <= 2 ^ 26;
  bz_B : uval rho vB <= 2 ^ 47;
  bz_top : bv_unsigned (rw rho V_TOP) + DW <= uval rho (SVar 10) /\ 140735332483072 <= bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Lemma basez_of : ltac2:(tb__ "0|0|
S16S3S18S1A1S25S29Z0R3A2S2aR3S2cZ2Z28A2A2A2S35S1S6R3A1R2A3S26S1bS3bR5R3A2S1cA3S3dR6R5A2F_;F_;F_;FF;Frho;FDW;").
Proof.
  intros DW rho F HDW HF HB. unfold baseF in HB.
  assert (G : forall p, In p (base_facts DW) -> holds rho p).
  { intros p Hp. apply (holds_mem rho F p HF). exact (proj1 (forallb_forall _ _) HB p Hp). }
  cbn [base_facts] in G.
  pose proof (G _ ltac:(left; reflexivity)) as F1. pose proof (G _ ltac:(do 1 right; left; reflexivity)) as F2.
  pose proof (G _ ltac:(do 2 right; left; reflexivity)) as F3. pose proof (G _ ltac:(do 3 right; left; reflexivity)) as F4.
  pose proof (G _ ltac:(do 4 right; left; reflexivity)) as F5. pose proof (G _ ltac:(do 5 right; left; reflexivity)) as F6.
  pose proof (G _ ltac:(do 6 right; left; reflexivity)) as F7. pose proof (G _ ltac:(do 7 right; left; reflexivity)) as F8.
  pose proof (G _ ltac:(do 8 right; left; reflexivity)) as F9. pose proof (G _ ltac:(do 9 right; left; reflexivity)) as F10.
  pose proof (G _ ltac:(do 10 right; left; reflexivity)) as F11. pose proof (G _ ltac:(do 11 right; left; reflexivity)) as F12.
  rewrite h_ule in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12.
  unfold two47, two26, RA.two47 in *. unfold IMG_HI in *.
  rewrite !uval_lit in * by lia. pose proof (uval_range rho (SVar 30)) as R30. rewrite uval_add_litZ in F2 by lia.
  change (uval rho (SVar 30)) with (bv_unsigned (rw rho V_TOP)) in *.
  pose proof (uval_range rho vb) as Rb. pose proof (uval_range rho vAL) as Ral.
  rewrite uval_add_litZ in F4 by lia. rewrite uval_add_litZ in F7 by lia.
  constructor; rewrite ?aceil_val; unfold IMG_HI in *; lia.
Qed.

Definition frame_facts (g pR : positive) (sz : Z) : list sprop := ltac2:(tb__ "0|3|
S1aS1S13S67Vg;A1S8VpR;A1M0A2S1aS1S4S8Vg;A1S2S2eS2cZ2M1Z3dA2Z1A2A1A2S1aS1S4S2S4fA1G0A2S1aS1S4S7S3aG0S2Vsz;A1A3S8P1eA1M2A2S1aS1S4G0S2S2cG1Z2fA2A1A2S1aS1S4G2S2Z7fffff800000A1A2S22S1A1A3A3A3A3A3A3").
Definition frameF (g pR : positive) (sz : Z) (F : list sprop) : bool := ltac2:(tb__ "0|0|
S69S1S1S68S1S11R1A1VF;A3Lp;S45Vg;VpR;Vsz;A3A3").
Record framez (g pR : positive) (sz : Z) (rho : valuation) : Prop := FZ {
  fz_g : uval rho (SVar g) = uval rho (SVar pR) / 8;
  fz_g8 : uval rho (SVar pR) mod 8 = 0;
  fz_f : IMG_HI <= uval rho (SVar pR) /\ uval rho (SVar pR) + sz <= bv_unsigned (rw rho V_TOP) /\ bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Lemma framez_of : ltac2:(tb__ "0|0|
S17S17S16S3S18S1A1S25S29Z0R3A2S2aR3S2cZ2Z28A2A2A2S35S1S6R3A1R2A3S26S1bS3fR7R6R5R3A4S1cA3S46R8R7R6R5A4F_;F_;F_;FF;Frho;Fsz;FpR;Fg;").
Proof.
  intros g pR sz rho F Hsz HF HB. unfold frameF in HB.
  assert (G : forall p, In p (frame_facts g pR sz) -> holds rho p).
  { intros p Hp. apply (holds_mem rho F p HF). exact (proj1 (forallb_forall _ _) HB p Hp). }
  cbn [frame_facts] in G.
  pose proof (G _ ltac:(left; reflexivity)) as F1. pose proof (G _ ltac:(do 1 right; left; reflexivity)) as F2.
  pose proof (G _ ltac:(do 2 right; left; reflexivity)) as F3. pose proof (G _ ltac:(do 3 right; left; reflexivity)) as F4.
  pose proof (G _ ltac:(do 4 right; left; reflexivity)) as F5. pose proof (G _ ltac:(do 5 right; left; reflexivity)) as F6.
  rewrite h_ule in F2, F3, F4, F5, F6. cbn [holds] in F1. change (uval rho (SVar 30)) with (bv_unsigned (rw rho V_TOP)) in *. unfold IMG_HI in *.
  rewrite !uval_lit in * by lia. pose proof (uval_range rho (SVar pR)) as Rf. pose proof (uval_range rho (SVar g)) as Rg.
  rewrite uval_add_litZ in F4 by lia.
  assert (E8 : uval rho (g8 g) = (uval rho (SVar g) * 8) mod 2 ^ 64).
  { unfold uval, g8. rewrite U_sll_lit. change (2 ^ (3 mod 64)) with 8. reflexivity. }
  apply (f_equal bv_unsigned) in F1. change (uval rho (g8 g) = uval rho (SVar pR)) in F1. rewrite E8 in F1.
  rewrite Z.mod_small in F1 by lia.
  constructor; [rewrite <- F1; rewrite Z.div_mul by lia; reflexivity | rewrite <- F1; apply Z_mod_mult | unfold IMG_HI; lia].
Qed.

Lemma shobj_range_hse : ltac2:(tb__ "0|2|
S17S17S16S16S16S3S18S1A1S16S25S29Z0R6A2M0S2aR6S2cZ2Z28A2A2A2G0S25S29R7R6A2S29R6S2dR8Z8A2A2A2S35S1S6R6A1R5A3S26S1bS3fRcRbRaR6A4S1cA3S25S29S1eS16S16S9R8S73RdRaR9S22S14A1S12A5A2M1A3R6A2S2aR6S1fS16S16G1A3A2A2S6cR7A1F_;F_;F_;F_;F_;F_;Fa;FF;Frho;Fk2;Fk1;Fsz;FpR;Fg;").
Proof.
  intros g pR sz k1 k2 rho F a Hsz Hk1 Hk2 HF HFR Hr. pose proof (framez_of g pR sz rho F Hsz HF HFR) as [G1 G2 G3]. unfold is_shadowZ, IMG_HI in *.
  unfold shobj, obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  pose proof (Z.div_le_mono sz (2 ^ 40) 8 ltac:(lia) ltac:(lia)) as D8. change (2 ^ 40 / 8) with 137438953472 in D8.
  unfold SHADOW_OFF, HIGH_SHADOW_END in *. rewrite !soff_lit_small in Hr by lia.
  change (bv_unsigned (eval rho (SVar g))) with (uval rho (SVar g)) in Hr. rewrite G1 in Hr.
  pose proof (uval_range rho (SVar pR)). lia.
Qed.

Lemma frame_off_rng : ltac2:(tb__ "0|2|
S17S17S16S16S3S18S1A1S25S29Z0R4A2M0S2aR4S2cZ2Z28A2A2A2S25G0S29R4R5A2A2S35S1S6R4A1R3A3S26S1bS3fR9R8R7R4A4S1cA3S26S16S2fR6S7S3aS8R9A1M1S2R7A1A3A2S2bS2fR6G1A2R7A2A3F_;F_;F_;F_;FF;Frho;Foff;Fsz;FpR;Fg;").
Proof.
  intros g pR sz off rho F Hsz Hoff HF HFR. pose proof (framez_of g pR sz rho F Hsz HF HFR) as [_ _ G3]. unfold IMG_HI in G3.
  pose proof (uval_range rho (SVar pR)). apply uval_add_litZ; lia.
Qed.

Definition vb184 : sv := SAlu ALU_ADD vb (SLit 184).
Definition extra_tab : list (sv * sv * sv) := ltac2:(tb__ "0|3|
S1aS19S19S0S0A2M0S0A2M1S1dG0S0S1dS0S0S33S2Z0A1M2A4S2Z8A1A4S1aG1S1dG0S0S1dS0S0S33S2Z60A1A4S2Z78A1A4S1aG1S1dG0S0S1dS0S0S33S2Zb8A1A4S2Zd8A1A4S1aG1S1dG0S0S1dS0S0S41G2A4S2Z20A1A4S1aG1S1dG0S0S1dS0S0S34G2A4S2Z30A1A4S1aG1S1dG0S0S1dS0S0S4cG2A4S4dA4S22G1A1A3A3A3A3A3A3").
Definition extraO (o : sobj) : bool := ltac2:(tb__ "0|3|
S68S19S19S0S0A2M0S0A2M1G1S24S24ScSdVo;A1S1eS0S0S1eG0S0R1A3M2A3A2ScSfVo;A1S1fS0S0G2A3A2A2ScSeVo;A1S1fG0S0R1A3A2A2Lt;S44A3").
Definition extraX_tab : list (sv * sv) := ltac2:(tb__ "0|1|
S1aS19S0S0A2M0S1dS0S0S33S2Z518A1A4S1aG0S1dS0S0S34S2Z30A1A4S1aG0S1dS0S0S4cS4dA4S1aG0S1dS0S0S41S2Z20A1A4S1aG0S1dS0S0S2S4bA1S2Zb8A1A4S22G0A1A3A3A3A3A3").
Definition extraX (r : sv * sv) : bool := existsb (xr_eqb r) extraX_tab.
Definition in_callers (rho : valuation) (a : Z) : Prop := ltac2:(tb__ "0|3|
S27S25S29S2fVrho;S33A2M0Va;A2S2aVa;S2bG0Z518A2A2A2S27S25S29S2fVrho;S34A2M1Va;A2S2aVa;S2bG1Z30A2A2A2S27S25S29S2fVrho;S4cA2M2Va;A2S2aVa;S2bG2S2fVrho;S4dA2A2A2A2S25S29S4bVa;A2S2aVa;S2bS4bZb8A2A2A2A2A2A2").

Lemma extraO_sound : ltac2:(tb__ "0|1|
S16S3S5S16S3dR4R3A2S26S1bS3cR3A1S1cA3S25S29S1eS16S16S9R5R4A2M0A3R3A2S2aR3S1fS16S16G0A3A2A2S40R6R4A2F_;F_;F_;Fa;Fo;Frho;FDW;").
Proof.
  intros DW rho o a [Bsp Bb Bal BL BB Btop] HE Hr. rewrite aceil_val in *. unfold IMG_HI in *.
  assert (E184 : uval rho vb184 = uval rho vb + 184) by (unfold vb184; apply uval_add_litZ; lia).
  unfold extraO in HE. apply existsb_exists in HE as (t & Hin & Heq).
  apply andb_prop in Heq as [Heq Hh]. apply andb_prop in Heq as [Hb Hl]. apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  unfold in_callers. cbn [extra_tab In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd] in Hb, Hl, Hh;
    (eapply obj_rangeZ in Hr; [| rewrite Hl; first [apply soff_lit_small; lia | apply soff_smallu; lia] | rewrite Hh; first [apply soff_lit_small; lia | apply soff_smallu; lia]]);
    rewrite Hb in Hr; rewrite ?E184 in Hr; lia.
Qed.

Lemma extraX_sound : ltac2:(tb__ "0|1|
S16S3S19S0S0A2S16S3dR4R3A2S26S1bS3eR3A1S1cA3S25S29S2fR5S1eS0S0R4A3A2M0R3A2S2aR3S2bG0S2fR5S1fS0S0R4A3A2A2A2A2S40R6R4A2F_;F_;F_;Fa;Fr;Frho;FDW;").
Proof.
  intros DW rho r a [Bsp Bb Bal BL BB Btop] HE Hr. rewrite aceil_val in *. unfold IMG_HI in *.
  assert (E184 : uval rho vb184 = uval rho vb + 184) by (unfold vb184; apply uval_add_litZ; lia).
  unfold extraX in HE. apply existsb_exists in HE as (t & Hin & Heq). apply xr_eqb_sound in Heq. subst t.
  unfold in_callers. cbn [extraX_tab In] in Hin. unfold pow10_tab in *.
  destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; destruct r as [b l]; injection E as <- <-; cbn [fst snd] in Hr;
    rewrite ?uval_lit in Hr by lia; rewrite ?E184 in Hr; lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S47S3S18S50Q40A1A1S4aOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S7bS6bVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S16S63VCST;R1A2S25S29Z0R2A2S2aR2S4fA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S16S63VXGL;R1A2S25S29Z0R2A2S2aR2S4fA2A2F_;Fa;").

Hypothesis HXpow : ltac2:(tb__ "0|0|
S16S25S29S4bR1A2S2aR1S2bS4bZb8A2A2A2S63VXGL;R2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S18S19S19S16S16A2S16A2A1").
Variable BX : bxt.
Variable rho0 : valuation.

Variable P0f : valuation -> Prop.
Hypothesis HP0b : ltac2:(tb__ "0|0|
S3VP0f;R1A1S42VCST;VFB;VFF;R2A4F_;Fr;").
Variable DW : Z.
Hypothesis HDW : 0 <= DW < 2 ^ 40.

Lemma P0b_now : ltac2:(tb__ "0|1|
S3S36S32Vrho0;R1A3VP0f;Vrho0;A1S25S16S25S29S2fR4S4cA2M0R1A2S2aR1S2bG0S2fR4S4dA2A2A2A2S37VCST;Vrho0;VFB;VFF;R2A5F_;Fa;S25S57VFF;S2fR3S33A2Z518A3S57VFF;S2fR3S34A2Z30A3A2A2F_;F_;Frho;").
Proof.
  intros rho Hav HP. destruct (HP0b _ HP) as (A & B & C). unfold uval, vL, vB, vb, vAL. cbn [eval].
  rewrite <- (proj1 Hav 12%positive eq_refl), <- (proj1 Hav 15%positive eq_refl), <- (proj1 Hav 18%positive eq_refl), <- (proj1 Hav 58%positive eq_refl).
  repeat (split; [assumption|]). assumption.
Qed.

Lemma in_callers_ok : ltac2:(tb__ "0|0|
S3S16S18S19S0S0A2A1S18S19S19S0S16A2S0A2A1S36S32Vrho0;R4A3VP0f;Vrho0;A1S40R6R5A2S27S37VCST;Vrho0;S52VFB;R7R5A3S38VFF;R7R4A3R6A5S63VXGL;R6A2A2F_;F_;F_;Ffrs;Fkept;Fa;Frho;").
Proof.
  intros rho a kept frs Hav HP0 H. destruct (P0b_now rho Hav HP0) as (HT & Hb & Hal).
  destruct H as [H|[H|[H|H]]].
  - destruct Hb as (f & sz & fl & Hin & H1 & H2). left. right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hin | lia].
  - destruct Hal as (f & sz & fl & Hin & H1 & H2). left. right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hin | lia].
  - left. apply pclMA_mono. apply HT. exact H.
  - right. exact (HXpow a H).
Qed.
Lemma extraO_client : ltac2:(tb__ "0|1|
S3S5S16S18S19S0S0A2A1S18S19S19S0S16A2S0A2A1S3dVDW;R5A2S36S32Vrho0;R6A3VP0f;Vrho0;A1S26S1bS3cR7A1S1cA3S25S29S1eS16S16S9R9R8A2M0A3R7A2S2aR7S1fS16S16G0A3A2A2S37VCST;Vrho0;S52VFB;RaR7A3S38VFF;RaR6A3R8A5F_;F_;F_;F_;F_;Ffrs;Fkept;Fa;Fo;Frho;").
Proof.
  intros rho o a kept frs BZ Hav HP0 HE Hr. destruct (P0b_now rho Hav HP0) as (HT & Hb & Hal).
  pose proof BZ as [Bsp Bb Bal BL BB Btop]. rewrite aceil_val in *. unfold IMG_HI in *.
  assert (E184 : uval rho vb184 = uval rho vb + 184) by (unfold vb184; apply uval_add_litZ; lia).
  unfold extraO in HE. apply existsb_exists in HE as (t & Hin & Heq).
  apply andb_prop in Heq as [Heq Hh]. apply andb_prop in Heq as [Hb0 Hl]. apply sv_eqb_sound in Hb0. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  cbn [extra_tab In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd] in Hb0, Hl, Hh;
    (eapply obj_rangeZ in Hr; [| rewrite Hl; first [apply soff_lit_small; lia | apply soff_smallu; lia] | rewrite Hh; first [apply soff_lit_small; lia | apply soff_smallu; lia]]);
    rewrite Hb0 in Hr; rewrite ?E184 in Hr.
  1-4: destruct Hb as (f & sz & fl & Hin & H1 & H2); right; right; right; exists f, sz, fl; split; [apply In_FFx; left; exact Hin | lia].
  - destruct Hal as (f & sz & fl & Hin & H1 & H2). right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hin | lia].
  - apply pclMA_mono. apply HT. lia.
Qed.

Lemma siteP : ltac2:(tb__ "0|0|
S47S3S18S1A1S18S19S0S0A2A1S18S19S19S0S16A2S0A2A1S23S21A1S18S5A1S3S18S50Q40A1A1S4aVAInv;RaR3R2R1A4S35S1S6RaA1R9A3S26S1bS3bVDW;RaA2S1cA3S36S32Vrho0;RcA3VP0f;Vrho0;A1S58Vrho0;RfA2S53RfS49S48R10A1A1A2S5bVFB;R11A2S5cVFF;R12A2S5aVFB;R13R12R10A4S54R13R11A2S55R14R12A2S59VFF;R16R15R12A4S26S1bS74R15R14R13R12S3cR11A6S1cA3S6eVCST;R18S20S16A1R17R12A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr skip R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR Hchk.
  eapply (robjsP_okA segs AInv CST ALA rho0 FB FF Ai rho facts tv fr skip extraO R rho1 tp1 md1 HM HF HT HTK HBf HFF HN HD HZ HFR Hchk).
  intros o a Ho HE Hr. exact (extraO_client rho o a _ _ (basez_of DW rho facts HDW HF HB) Hav HP0 HE Hr).
Qed.
Lemma siteF : ltac2:(tb__ "0|0|
S47S3S18S1A1S18S19S0S0A2A1S18S19S19S0S16A2S0A2A1S18S5A1S3S18S50Q40A1A1S4aVAInv;R9R3R2R1A4S35S1S6R9A1R8A3S26S1bS3bVDW;R9A2S1cA3S36S32Vrho0;RbA3VP0f;Vrho0;A1S58Vrho0;ReA2S53ReS49S48RfA1A1A2S5aVFB;R10RfRdA4S54R10ReA2S55R11RfA2S59VFF;R13R12RfA4S26S1bS71R12R11R10S20S21A1S3cRfA6S1cA3S79VCST;Vrho0;VFB;VFF;R14R12R11R10A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR Hchk.
  eapply (robjsP_okF segs AInv CST ALA rho0 FB FF Ai rho facts tv fr extraO R rho1 tp1 md1 HM HF HT HTK HN HD HZ HFR Hchk).
  intros o a Ho HE Hr. exact (extraO_client rho o a _ _ (basez_of DW rho facts HDW HF HB) Hav HP0 HE Hr).
Qed.
Lemma siteH : ltac2:(tb__ "0|1|
S47S3S18S1A1S18S19S0S0A2A1S18S19S19S0S16A2S0A2A1S18S5A1S3S18S50Q40A1A1S4aVAInv;R9R3R2R1A4S35S1S6R9A1R8A3S26S1bS3bVDW;R9A2S1cA3S36S32Vrho0;RbA3VP0f;Vrho0;A1S58Vrho0;ReA2S53ReS49S48RfA1A1A2S5aVFB;R10RfRdA4S54R10ReA2S55R11RfA2S59VFF;R13R12RfA4S26S1bS71R12R11R10S20S21A1S3cRfA6S1cA3S5S16S6aS5R2R12A3S25S29S1eS16S16S9R17R3A2M0A3R2A2S2aR2S1fS16S16G0A3A2A2S27S37VCST;Vrho0;S52VFB;R18R16A3S38VFF;R18R15A3R3A5S27S25S29Z0R3A2S2aR3S4fA2A2S6cR3A1A2A2F_;F_;Fa;Fo;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR Hchk.
  eapply (robjsP_hse segs AInv CST ALA rho0 FB FF Ai rho facts tv fr extraO R rho1 tp1 md1 HM HF HT HTK HN HD HZ HFR Hchk).
  intros o a Ho HE Hr. exact (extraO_client rho o a _ _ (basez_of DW rho facts HDW HF HB) Hav HP0 HE Hr).
Qed.
Lemma siteX : ltac2:(tb__ "0|4|
S47S3S18S1A1S18S19S0S0A2A1M0S18S19S19S0S16A2S0A2M1A1M2S23S21A1M3S18S5A1G0S3S18S50Q40A1A1S4aVAInv;RbR3R2R1A4S35S1S6RbA1RaA3S26S1bS3bVDW;RbA2S1cA3S36S32Vrho0;RdA3VP0f;Vrho0;A1S58Vrho0;R10A2S53R10S49S48R11A1A1A2S5bVFB;R12A2S5cVFF;R13A2S5aVFB;R14R13R11A4S54R14R12A2S55R15R13A2S59VFF;R17R16R13A4S26S1bS72VXGL;R16R15R14R13R12S3eR11A8S1cA3S25S39VCST;VXGL;Vrho0;VFB;VFF;R18R16G3G2Lskip;R14S21S56G1R1R16A3Li;R15X23x2R12A9S25S70VCST;VXGL;R19S20S16A1R18R12A6S7aR18R12A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Fobjs;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr skip objs X rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR Hchk.
  assert (HEX : forall r a, In r X -> extraX r = true -> uval rho (fst r) <= a < uval rho (fst r) + uval rho (snd r) ->
            pclMA CST rho0 (FBx FB rho tv) (FFx FF rho (match skip with Some i => remove_nth i fr | None => fr end)) a \/ RtCells.in_rangesZ XGL a).
  { intros r a Hr HE Ha. apply (in_callers_ok rho a _ _ Hav HP0). exact (extraX_sound DW rho r a (basez_of DW rho facts HDW HF HB) HE Ha). }
  split; [exact (xrs_checkL_sound segs AInv CST XGL ALA rho0 FB FF Ai rho facts tv fr skip objs extraX X rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HT HTK) HN HD HZ HFR Hchk HEX)|].
  exact (xrs_checkL_okA segs AInv CST XGL ALA HCST HXGL rho0 FB FF Ai rho facts tv fr skip objs extraX X rho1 tp1 md1 HM HF HT HTK HBf HFF HN HD HZ HFR Hchk HEX).
Qed.

Lemma site_pure : ltac2:(tb__ "0|2|
S66S77S18S5A1S3S18S19S0S0A2A1S18S19S19S0S16A2S0A2A1S18S30A1S26S1bS3bVDW;SbS64R7A1A1A2S1cA3S26S1bS74SbS64R8A1A1R4R3S20S21A1M0S3cR6A6S1cA3S26S1bS72VXGL;SbS64R9A1M1A1R5R4G0S15G1A1S3eS65R9A1A8S1cA3S6fVAInv;VCST;VXGL;S32Vrho0;VP0f;VFB;VFF;RaR9R8R7S5eR6R5R4S5dA4S20S16A1S47S75S28L_;L_;AfF_;F_;F_;Fbd;Ffr;Ftv;Frho;FR;Fs;FE;").
Proof.
  intros E s R rho tv fr bd HB HR HX Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. cbn [nd_tv nd_fr] in HN, HD, HZ, HFR.
  split; [exact (siteP Ai rho _ tv fr None R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HR)|].
  split; [exact (proj1 (proj2 (siteX Ai rho _ tv fr None _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HX))) | exact I].
Qed.

Lemma frozen_stableA' : ltac2:(tb__ "0|0|
S17S17S62S3S7cS32R3A2S26S1bS61R4R3A2S1cA3S78S6bR6S60VAInv;VCST;VXGL;S32VKc;Vrho0;VP0f;VFB;VFF;VBX;S5fR4R3AdA3F_;F_;Frho;Fnd;Fm;Fn;").
Proof.
  intros n m nd rho Hm Hb r r' tp tr md md' _ Hme (Ai & kc & HJ). exists Ai, kc.
  eapply (JAi_stable segs AInv CST XGL NF Kc rho0 P0f FB FF BX PTrue HKc ALA m nd Ai kc rho rho tp tr md md'); [exact Hm | exact Hb | apply agree_below_refl | exact Hme | exact HJ].
Qed.

Lemma payA_same : ltac2:(tb__ "0|1|
S18S1A1S18S30A1S26S1bS31R1A1S1cA3S6dS32Vrho0;VP0f;R3S2Z0M0A1G0R2R2A8F_;Fbd;Ffacts;").
Proof.
  intros facts bd Hw. split; [exact Hw|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia.
  split; [lia|]. split; [lia | exact Hn].
Qed.
End Sum.
End Lib_builder_pf.

(* [comment removed for export] *)
Module Lib_realloc_rom.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "list"; "prod"; "app"; "None"; "false"; "bool"; "fst"; "option"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "SLit"; "SPUle"; "SVar"; "cell"; "SAlu"; "SPBranch"; "FcsrFrm0"; "mkSS"; "DUnknown"; "SPAlign"; "mkObj"; "ss_regs"; "valuation"; "ss_next"; "SMd"; "SPNot"; "rm"; "rw"; "ss_facts"; "ss_fregs"; "ss_objs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_realloc_rom"; "kb16"; "VQ"; "vK"; "vKn"; "ndR"; "vP"; "vQ"; "vA"; "z0"; "c8"; "pN"; "vD"; "X_cp0"; "O_D"; "O_F"; "O_al"; "q1"; "ra_facts"; "tv0"; "vPn"; "B32"; "bd1"; "fs_facts"; "two47"; "E_m"; "FUEL_rr"; "Pre_rr"; "X_step"; "bd0"; "cutpcs_rr"; "eoff"; "ok_facts"; "spm"; "tv1"; "tv2"; "C_0"; "D_1"; "D_10"; "D_11"; "D_12"; "D_13"; "D_14"; "D_15"; "D_2"; "D_3"; "D_4"; "D_5"; "D_6"; "D_7"; "D_8"; "D_9"; "E_free"; "E_freeT"; "O_fs"; "P0_ra"; "P_fail"; "P_okX"; "P_ok_S"; "PhisV"; "Pre_f"; "Pre_m"; "T_free"; "T_mnull"; "T_mok"; "Vs"; "X_a2"; "X_cp0f"; "cp_regs"; "cutsE"; "exitsE"; "leafA_at"; "pls"; "pre_regs_ra"; "q_facts"; "two40"; "vF0"; "vF1"; "vUD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "tv_factsA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "BC_LTU"; "BC_GE"; "BC_EQ"; "M_MUL"; "aluop"; "mulop"; "@Corelib.Lists.ListDef"; "nth"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "uval"; "BIc"; "BIs"; "KU"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "True"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "A_globals"; "leavesA_at"; "mkA"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "post_regs"; "pre_regs"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "opp"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_realloc_rom.RRAddr"; "ra_L"; "ra_ret"; "free_pc"; "malloc_pc"; "ra_entry"; "thunk_alloc"; "thunk_calloc"; "thunk_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "ejcertAF"; "efnode"; "ent_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Lib_byteloops"; "bl_prune"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "NPOSTM"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV CellTile ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import TobjJAR TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Lib_byteloops.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Module RRAddr. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Lib_realloc.ReallocAddr. End RRAddr.
Import RRAddr.

Definition FUEL_rr : nat := 400%nat.
Definition two40 : Z := 2 ^ 40.
Definition two47 : Z := 2 ^ 47.
Definition B32 : Z := 4294967295.

Definition vA : sv := SVar 12. Definition vP : sv := SVar 13. Definition vK : sv := SVar 14. Definition vKn : sv := SVar 33.
Definition vD : sv := SVar 19. Definition vUD : sv := SVar 52.
Definition spm (k : Z) : sv := ltac2:(tb__ "0|0|
S14S7bS12PaA1S10S9bVk;A1A1A3").
Definition kb16 (k : sv) : sv := SMd M_MUL (SLit 16) k.

Definition c8 (o : Z) (v : sv) : cell := mkCell (SLit o) 8 v.
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1aS12PaA1S10N60A1S10Z0A1Vcells;S18A5").
Definition O_D : sobj := ltac2:(tb__ "0|0|
S1aS4bZ60A1S36S10Z0A1S3S13A1S18A5").
Definition O_al : sobj := ltac2:(tb__ "0|2|
S1aS32S10Z0M0A1M1S10Z30A1S0S13S34G0S10Sa2A1A2S0S13S34Z8S10Sa3A1A2S0S13S34Z10G1A2S0S13S34Z18S10Sa4A1A2S0S13S34Z20G1A2S0S13S34Z28S78A2S3S13A1A3A3A3A3A3A3S18A5").

Definition O_fs (d c k : sv) : sobj := ltac2:(tb__ "0|0|
S1aS14S7bVd;S2bVc;A1A3S10Z0A1S2bS14S7cVk;Vc;A3A1S3S13A1S18A5").

Definition ra_facts : list sprop := ltac2:(tb__ "0|9|
S0SeS19PaM0Z4M1A2S0SeS11S12G0A1M2S10S42A1M3A2S0SeS11S12P1eA1M4S14S7bS4bZ60A1M5S36A3A2S0SeS11G4G5A2S0SeS11G4G2A2S0SeS15S7eS10N1000A1S36A3S0SeS15S7eS36S10S9bS75A1A1A3S0SeS19PcZ3A2S0SeS11S10Z1000A1M6S32A2S0SeS11S14S7bS32S10Z30A1A3G4A2S0SeS11S32G3A2S0SeS19PdG1A2S0SeS11G6S30A2S0SeS11S14S7bS30S2bS2dA1A3G4A2S0SeS11S30G3A2S0SeS11S10Z1A1S2dA2S0SeS15S7dS2dS2eA3S0SeS11S2bS2eA1S10S3fA1M7A2S0SeS11S2eG7A2S0SeS11S10Z7fff7f800000A1M8G4A2S0SeS11G4S10Z7fffff800000A1A2S0SeS11G8G2A2S3SeA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition pre_regs_ra : list sv := ltac2:(tb__ "0|1|
S95S97S0S5S2SdA2M0S1S2SdUcS2bS2dA1A4S0G0S1S2SdUdS2bS2eA1A4S0G0S1S2SdUeS10Z10A1A4S3G0A1A3A3A3A2").
Definition X_ra : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5SdSdA2M0S1SdSdS32S10Z30A1A4S0G0S1SdSdS30S2bS2dA1A4S3G0A1A3A3").
Definition Pre_rr_S : sstate := ltac2:(tb__ "0|0|
S17Sa1S73S94S16S7SdA1S6SfS0SfS39S3S13A1A1S0SfS38S0SfS3aS3SfA1A3A3A3S8fA3S3cS93S8A9").
Definition Pre_rr : axst := mkA Pre_rr_S X_ra.

Definition cutpcs_rr : list Z := ltac2:(tb__ "0|0|
S0S25S9dS0S25Sa0S0S25S9fS3S25A1A3A3A3").
Definition optA (x : option axst) : axst := match x with Some s => s | None => Pre_rr end.
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_rr_S end.
Definition leafA_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S83S28Vk;S90S44S48VS;Vpc;A4S45A4").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition E_m : axst := Eval vm_compute in leafA_at Pre_rr malloc_pc 0.
Definition Pre_m : axst := Pre_malloc AE_A [] UStopLe.
Definition s_m : wsub := ltac2:(tb__ "0|0|
S0S5S26SdA2S1S26SdPfS36A4Sa8PaS29S43A1S29S67A1A3A3").
Definition R_m : list sobj := Eval vm_compute in optR (entails_frA E_m Pre_m s_m).
Definition pN : positive := pos_add_nat (ss_next (ax_S E_m)) 10.
Definition T_mnull : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_null AE_A [] UStopLe).
Definition T_mok0 : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_ok AE_A [] UStopLe).
Definition mok_facts : list sprop := ltac2:(tb__ "0|0|
S7aS1SdSdS12S35A1S2bS2eA1A4A1").
Definition T_mok : axst := ax_add_facts mok_facts T_mok0.

Definition X_cp0 : axst := Eval vm_compute in leafA_at T_mok ra_L 0.

Definition vQ : sv := SVar 172.  Definition vF0 : sv := SVar 173.  Definition vF1 : sv := SVar 174.
Definition eoff (j : Z) : sv := ltac2:(tb__ "0|0|
S14S7bS2bS31A1S10Vj;A1A3").
Definition pls (b : sv) (o : sv) : sv := SAlu ALU_ADD b o.
Definition q1 : sv := SAlu ALU_ADD vQ (SLit 1).
Definition cp_regs : list sv := ltac2:(tb__ "0|12|
S4SdA1M0G0Lx;S1bS29S37A1A1S3SdA1M1SdG0G0G0Ll;R1S0SdR2G1A3M2SdG0G0G0Ll0;R1S0SdR4G2A3M3SdG0G0G0Ll1;R1S0SdR6G3A3M4SdG0G0G0Ll2;R1S0SdR8G4A3M5SdG0G0G0Ll3;R1S0SdRaG5A3M6SdG0G0G0Ll4;R1S0SdRcG6A3M7SdG0G0G0Ll5;R1S0SdReG7A3M8SdG0G0G0Ll6;R1S0SdR10G8A3M9SdG0G0G0Ll7;R1S0SdR12G9A3MaSdG0G0G0Ll8;R1S0SdR14GaA3MbSdG0G0G0Ll9;R1S0SdR16GbA3McSdG0G0G0Ll10;R1S0SdR18GcA3MdSdG0G0G0Ll11;R1S0SdR1aGdA3MeSdG0G0G0Ll12;R1S0SdR1cGeA3MfSdG0G0G0Ll13;R1S0SdR1eGfA3M10SdG0G0G0Ll14;R1S0SdR20G10A3M11SdG0G0G0Ll15;R1S0SdR22G11A3SdG0S0SdR24S0SdR22S0SdR20S0SdR1eS0SdR1cS0SdR1aS0SdR18S0SdS12Pb0A1S0SdR14S0SdR12S0SdR10S0SdReS0SdRcS0SdRaS0SdS12PafA1S0SdS12Pb1A1S0SdR4S0SdS2bS31A1R1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Lrest;Lr17;X4x2Ll15;Lr16;X4x2Ll14;Lr15;X4x2Ll13;Lr14;X4x2Ll12;Lr13;X4x2Ll11;Lr12;X4x2Ll10;Lr11;X4x2Ll9;Lr10;X4x2Ll8;Lr9;X4x2Ll7;Lr8;X4x2Ll6;Lr7;X4x2Ll5;Lr6;X4x2Ll4;Lr5;X4x2Ll3;Lr4;X4x2Ll2;Lr3;X4x2Ll1;Lr2;X4x2Ll0;Lr1;X4x2Ll;Lr0;X4x2").

Definition fs_facts (q : sv) : list sprop := ltac2:(tb__ "0|1|
S0SeS11S10Z10A1S2bS14S7cS2eVq;A3A1M0A2S0SeS11G0S10S3fA1A2S3SeA1A3A3").
Definition q_facts : list sprop := ltac2:(tb__ "0|1|
S6SeS0SeS15S7dS31S2dA3S0SeS11S49Z10A1M0S2bS2dA1A2S0SeS11G0S2bS2eA1A2S0SeS11S31S10S3fA1A2S3SeA1A3A3A3A3S41S31A1A3").
Definition C_0c : axst := ltac2:(tb__ "0|7|
S2aS37S17S9dS6eS23S29S37A1M0A1S16S7SdA1S4SfA1M1G1Lx;S24G0A1S3SfA1M2SfG1G1G1Ll;R1S0SfR2G2A3M3SfG1G1G1Ll0;R1S0SfR4G3A3M4SfG1G1G1Ll1;R1S0SfR6G4A3M5SfG1G1G1Ll2;R1S0SfR8G5A3M6SfG1G1G1Ll3;R1S0SfRaG6A3SfG1G1G1Ll4;R1S0SfRcS0SfS60S12S35A1S31S2eA3S0SfR8S0SfR6S0SfR4S0SfR2S0SfSa7S72S30S2bS31A1A2PadA2G2A3A3A3A3A3A3A3SfG1S0SfReS0SfRcS0SfRaS0SfR8S0SfR6S0SfR4S0SfR2R1A3A3A3A3A3A3A3Ll5;Ls;X4x2Ll4;Lo5;X4x2Ll3;Lo4;X4x2Ll2;Lo3;X4x2Ll1;Lo2;X4x2Ll0;Lo1;X4x2Ll;Lo0;X4x2S6SeS74S22G0A1A3Pb2S8A9A2").
Definition C_0 : axst := Eval vm_compute in C_0c.

Definition stepD (S : axst) : axst := ltac2:(tb__ "0|0|
SabPb2S71VS;S9dU0A3A2").
Definition D_1 : axst := Eval vm_compute in stepD C_0.
Definition D_2 : axst := Eval vm_compute in stepD D_1.
Definition D_3 : axst := Eval vm_compute in stepD D_2.
Definition D_4 : axst := Eval vm_compute in stepD D_3.
Definition D_5 : axst := Eval vm_compute in stepD D_4.
Definition D_6 : axst := Eval vm_compute in stepD D_5.
Definition D_7 : axst := Eval vm_compute in stepD D_6.
Definition D_8 : axst := Eval vm_compute in stepD D_7.
Definition D_9 : axst := Eval vm_compute in stepD D_8.
Definition D_10 : axst := Eval vm_compute in stepD D_9.
Definition D_11 : axst := Eval vm_compute in stepD D_10.
Definition D_12 : axst := Eval vm_compute in stepD D_11.
Definition D_13 : axst := Eval vm_compute in stepD D_12.
Definition D_14 : axst := Eval vm_compute in stepD D_13.
Definition D_15 : axst := Eval vm_compute in stepD D_14.

Definition X_step : axst := Eval vm_compute in stepD D_15.
Definition E_free : axst := Eval vm_compute in leafA_at D_15 free_pc 0.

Definition tiles2 : list (nat * sv * Z * sv) := ltac2:(tb__ "0|5|
S0S5S5S5S2SdA2M0S25A2M1SdA2M2S1G1SdS1G0S25S1S2SdU1M3S10Z0A1A4Z8M4A4S76A4S0G2S1G1SdS1G0S25S1S2SdG3S10G4A1A4G4A4S77A4S3G2A1A3A3").

Definition sel8 : list nat := ltac2:(tb__ "0|0|
S0S2U0S0S2U2S0S2U3S0S2U4S0S2U5S0S2U6S0S2U7S0S2U1S3S2A1A3A3A3A3A3A3A3A3").

Definition step_facts : list sprop := ltac2:(tb__ "0|1|
S6SeS0SeS15S7dS3bS2dA3S0SeS11S49Z20A1M0S2bS2dA1A2S0SeS11G0S2bS2eA1A2S3SeA1A3A3A3S41S3bA1A3").
Definition X_t : axst := Eval vm_compute in ax_setS X_step (optS (tiles_at (ax_S X_step) tiles2)).
Definition X_f : axst := ax_add_facts step_facts X_t.
Definition X_s : axst := Eval vm_compute in optA (apply_axforms X_f [AXSplit 1 (SLit 16)]).
Definition X_r : axst := Eval vm_compute in ax_setS X_s (reshape_obj_at (ax_S X_s) 2 (O_fs (SVar pN) q1 vKn)).
Definition X_p : axst := Eval vm_compute in optA (apply_axforms X_r [AXSelect sel8]).

Definition X_a1 : axst := Eval vm_compute in drop_lastA X_p (removelast (ss_objs (ax_S X_p))).
Definition X_a2 : axst := Eval vm_compute in drop_lastA X_a1 (removelast (ss_objs (ax_S X_a1))).
Definition X_c : axst := Eval vm_compute in carve_ent_stateA X_a2 (pls vP (kb16 q1)).
Definition s_step : wsub := ltac2:(tb__ "0|4|
S0S5S26SdA2M0S1S26SdPacS3bA4S0G0S1S26SdPadS12S1dS29S6cA1A1M1A1A4S0G0S1S26SdPaeS12Sa9G1A1A1A4S0G0S1S26SdPafS83SdUeS1bS29S46A1A1M2S10Z0A1M3A4A4S0G0S1S26SdPb0S83SdU7G2G3A4A4S0G0S1S26SdPb1S83SdUfG2G3A4A4S3G0A1A3A3A3A3A3A3").

Definition cp0_facts : list sprop := ltac2:(tb__ "0|2|
S6SeS0SeS15S7dS10Z0A1M0S2dA3S0SeS11S10Z10A1M1S2bS2dA1A2S0SeS11G1S2bS2eA1A2S3SeA1A3A3A3S41G0A1A3").
Definition X_cp0f : axst := ax_add_facts cp0_facts X_cp0.
Definition X_cp0c : axst := Eval vm_compute in carve_ent_stateA X_cp0f (pls vP (kb16 (SLit 0))).
Definition s_cp0 : wsub := ltac2:(tb__ "0|4|
S0S5S26SdA2M0S1S26SdPacS10Z0A1M1A4S0G0S1S26SdPadS12S1dS29S6dA1A1M2A1A4S0G0S1S26SdPaeS12Sa9G2A1A1A4S0G0S1S26SdPafS83SdUeS1bS29S37A1A1M3G1A4A4S0G0S1S26SdPb0S83SdU7G3G1A4A4S0G0S1S26SdPb1S83SdUfG3G1A4A4S3G0A1A3A3A3A3A3A3").

Definition free_facts : list sprop := ltac2:(tb__ "0|0|
S0SeS11S2dS3bA2S3SeA1A3").
Definition sel7 : list nat := ltac2:(tb__ "0|0|
S0S2U0S0S2U2S0S2U3S0S2U4S0S2U5S0S2U6S0S2U1S3S2A1A3A3A3A3A3A3A3").
Definition E_ft : axst := Eval vm_compute in ax_setS E_free (optS (tiles_at (ax_S E_free) tiles2)).
Definition E_ff : axst := ax_add_facts free_facts E_ft.
Definition E_fp : axst := Eval vm_compute in optA (apply_axforms E_ff [AXSelect sel7]).
Definition E_fa1 : axst := Eval vm_compute in drop_lastA E_fp (removelast (ss_objs (ax_S E_fp))).
Definition E_fa2 : axst := Eval vm_compute in drop_lastA E_fa1 (removelast (ss_objs (ax_S E_fa1))).
Definition E_fc : axst := Eval vm_compute in carve_stateA E_fa2 vP (kb16 vK).
Definition X_rrT : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5SdSdA2M0S1SdSdS32S10Z30A1A4S0G0S1SdSdS12S35A1S2bS2eA1A4S3G0A1A3A3").
Definition E_freeT : axst := Eval vm_compute in mkAX (ax_S E_fc) X_rrT shb.

Definition Pre_f : axst := Pre_free AE_A [] UStopLe.
Definition s_f : wsub := ltac2:(tb__ "0|1|
S0S5S26SdA2M0S1S26SdPfS36A4S0G0S1S26SdPdS2bS2dA1A4Sa8PaS29S5fA1S29S66A1A3A3A3").
Definition R_f : list sobj := Eval vm_compute in optR (entails_frA E_freeT Pre_f s_f).
Definition T_free : axst := Eval vm_compute in T_afterA Pre_f E_freeT s_f R_f (L_free AE_A [] UStopLe).

Definition vPn : sv := SVar 140.
Definition P_fail_S : sstate := ltac2:(tb__ "0|1|
S17S9eS95S96S93A1S0S5S2SdA2M0S1S2SdUaS10Z0A1A4S3G0A1A3A2S94S16S7SdA1S6SfS0SfS39S3S13A1A1S0SfS38S0SfS3aS3SfA1A3A3A3S8fA3S3cSadS8A9").
Definition P_fail : axst := mkA P_fail_S X_ra.
Definition ok_facts (p : sv) : list sprop := ltac2:(tb__ "0|4|
S0SeS19SdS26Lp;Vp;S25P8cM0Lz;S26R1Lv;S81SdSdG0Lb;La;M1Lop;M2G2S82G1Lop;M3G3S9S27SdG0La;Lw;Lsgn;S26SdS25G0Lk;Li;Ll;Xdx8Z4A2S0SeS1fS15S7fVp;S10Z0A1A3A1S0SeS11S10Z1000A1Vp;A2S0SeS11S14S7bVp;S2bS2eA1A3S12P1eA1A2S0SeS11Vp;S10S42A1A2S0SeS11S10SacA1Vp;A2S3SeA1A3A3A3A3A3A3").
Definition P_ok_S : sstate := ltac2:(tb__ "0|1|
S17S9eS95S96S93A1S0S5S2SdA2M0S1S2SdUaS3eA4S3G0A1A3A2S94S16S7SdA1S6SfS0SfS39S3S13A1A1S0SfS38S0SfS3aS3SfA1A3A3A3S8fA3S6SeS4aS3eA1S3cA3P8dS8A9").
Definition P_ok : axst := ltac2:(tb__ "0|1|
S91S64S0S5SdSdA2M0S1SdSdS32S10Z30A1A4S0G0S1SdSdS3eS2bS2eA1A4S3G0A1A3A3A2").

Definition P_okX_S : sstate := ltac2:(tb__ "0|2|
S17S9eS95S96Pc8A1S0S5S2SdA2M0S1S2SdUaS12S35A1M1A4S3G0A1A3A2S94S16S7SdA1S6SfS0SfS39S3S13A1A1S0SfS38S0SfS3aS3SfA1A3A3A3S8fA3S6SeS4aG1A1S3cA3Pe8S8A9").
Definition P_okX : axst := mkA P_okX_S X_rrT.
Definition s_post : wsub := Eval vm_compute in infer_sub NF (ax_S P_okX) (ax_S P_ok).

Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5SdSdA2M0S1SdSdS30S2bS2dA1A4S3G0A1A3").
Definition tv1 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5SdSdA2M0S1SdSdS12S35A1S2bS2eA1A4S0G0S1SdSdS30S2bS2dA1A4S3G0A1A3A3").
Definition tv2 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5SdSdA2M0S1SdSdS12S35A1S2bS2eA1A4S3G0A1A3").
Definition tvP : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5SdSdA2M0S1SdSdS3eS2bS2eA1A4S3G0A1A3").
Definition bd0 : list bitem := ltac2:(tb__ "0|2|
S0S85S88Z1M0Z0M1S2bS2eA1A3S0S85S87G1S9aZ2S89A2G0A3S3S85A1A3A3").
Definition bd1 : list bitem := [BIc 0 KU 1].
Definition ndR (tv : list (sv * sv)) (bd : list bitem) : ndesc := ND tv [] bd.

Definition z0 : sv := SLit 0.

Definition VQ (c : Z) : sv := ltac2:(tb__ "0|0|
S14S7cS1eS80S10Z20A1S14S7cS14S7bS10S98S42Z1A2A1S2dA3S31A3A3S10Vc;A1A3").

Definition Vs : list (list positive) := ltac2:(tb__ "0|3|
S0S4S26A1M0S3S26A1M1S0G0S0S26P6fM2S0S26PacS0S26PadS0S26PaeG1A3A3A3A3S0G0S0S26G2G1A3S3G0A1A3A3A3").
Definition cutsE : list efnode := ltac2:(tb__ "0|9|
S0S5S5S5S28S79A2M0S2A2M1S5S25SdA2M2A2M3S1G1G2S1G0S2S1S28S79S45S2fS3dS47A2A4U0M4A4S1S25SdZ64S33A4A4S0G3S1G1G2S1G0S2S1S28S79S69S2fS3dS40A2A4G4A4S1S25SdZ50S33A4M5A4S0G3S1G1G2S1G0S2S1S28S79S6aS2fS4cS40A2M6A4G4A4G5A4S0G3S1G1G2S1G0S2S1S28S79S4eG6A4U1M7A4S1S25SdZ46M8S2cZ0A1A4A4S0G3S1G1G2S1G0S2S1S28S79S4fG6A4G7A4S1S25SdG8S2cZ1A1A4A4S0G3S1G1G2S1G0S2S1S28S79S56G6A4G7A4S1S25SdG8S2cZ3A1A4A4S0G3S1G1G2S1G0S2S1S28S79S57G6A4G7A4S1S25SdG8S2cZ5A1A4A4S0G3S1G1G2S1G0S2S1S28S79S58G6A4G7A4S1S25SdG8S2cZ7A1A4A4S0G3S1G1G2S1G0S2S1S28S79S59G6A4G7A4S1S25SdG8S2cZ9A1A4A4S0G3S1G1G2S1G0S2S1S28S79S5aG6A4G7A4S1S25SdG8S2cZbA1A4A4S0G3S1G1G2S1G0S2S1S28S79S5bG6A4G7A4S1S25SdG8S2cZdA1A4A4S0G3S1G1G2S1G0S2S1S28S79S5cG6A4G7A4S1S25SdG8S2cZfA1A4A4S0G3S1G1G2S1G0S2S1S28S79S5dG6A4G7A4S1S25SdG8S2cZ11A1A4A4S0G3S1G1G2S1G0S2S1S28S79S50G6A4G7A4S1S25SdG8S2cZ13A1A4A4S0G3S1G1G2S1G0S2S1S28S79S51G6A4G7A4S1S25SdG8S2cZ15A1A4A4S0G3S1G1G2S1G0S2S1S28S79S52G6A4G7A4S1S25SdG8S2cZ17A1A4A4S0G3S1G1G2S1G0S2S1S28S79S53G6A4G7A4S1S25SdG8S2cZ19A1A4A4S0G3S1G1G2S1G0S2S1S28S79S54G6A4G7A4S1S25SdG8S2cZ1bA1A4A4S0G3S1G1G2S1G0S2S1S28S79S55G6A4G7A4S1S25SdG8S2cZ1dA1A4A4S0G3S1G1G2S1G0S2S1S28S79S68S2fS4dS3S85A1A2A4U2A4S1S25SdZ3cS33A4A4S3G3A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsE : list efnode := ltac2:(tb__ "0|9|
S0S5S5S5S28S79A2M0S2A2M1S5S25SdA2M2A2M3S1G1G2S1G0S2S1S28S79S43S2fS3dS47A2A4U0M4A4S1S25SdZ5aS33A4A4S0G3S1G1G2S1G0S2S1S28S79S37S2fS4cS40A2M5A4G4A4S1S25SdZ4bS33A4A4S0G3S1G1G2S1G0S2S1S28S79S46G5A4U1M6A4S1S25SdZ46S2cZ1fA1A4A4S0G3S1G1G2S1G0S2S1S28S79S5eG5A4G6A4S1S25SdZ41S33A4A4S0G3S1G1G2S1G0S2S1S28S79S62S2fS3dS3S85A1M7A2A4G4A4S1S25SdZ0S33A4M8A4S0G3S1G1G2S1G0S2S1S28S79S63S2fS4dG7A2A4U2A4G8A4S3G3A1A3A3A3A3A3A3").

Definition PhisV : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|2|
S84S4S26A1M0S5G0S1cOF_;M1A2G0S1G0G1R1S1cS8dL_;A4LV;S6bA4").

Definition P0_ra (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S8cS25S25S8cS25S25S8cS25S25S8aSaeS5S5S25S25A2M0S25A2S1G0S25S1S25S25R3R2A4R1A4VFF;A3S8aS99R3Sb1Q40S21Vr;PcA2A2M1A2S99S98G1Z30A2S98R3R2A2A2A2A2Lfl;A2Ls;A2Lf;A2").
Definition P0_rr (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S8aS61VFB;VFF;Vr;A3S25S8aS99S86Vr;S30A2M0R1A2S9cR1S98G0S9aZ10S86Vr;S2dA2A2A2A2A2S8eS8bSbSb0Q8A1M1A1S20Vr;SafQ40R2A2A2S7G1A1A3A1F_;Fz;A2").

Goal entailsA X_c C_0 s_step = true /\ entailsA X_cp0c C_0 s_cp0 = true /\ entailsA E_fc E_freeT [] = true
     /\ entailsA P_okX P_ok s_post = true
     /\ call_checkPA E_freeT Pre_f s_f R_f [L_free AE_A [] UStopLe] = true /\ length R_f = 2%nat
     /\ call_checkPA E_m Pre_m s_m R_m [L_malloc_null AE_A [] UStopLe; L_malloc_ok AE_A [] UStopLe] = true /\ length R_m = 2%nat.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma ejcertAF_ok0 : ltac2:(tb__ "0|0|
S8bS9Sa5S92S93S65S44S48P64S6fS70A8ScA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma ejcertAF_V : ltac2:(tb__ "0|6|
S4SaaA1S26S4S5S4S26A1M0S1cOF_;M1A2M2A1M3G3S2S4S25A1S26S4Sa6A1M4G4S8bS4G0A1S84G2G0SaG0G1A2M5R7A4S84G2G0G5R6A4A3S8bS9Sa5RaR9R8R6R5R4R3R2A8Sa5RaR9R7R6R5R4R3R2A8A3F_;Fexits;Fcuts;Fg;Fcps;Ffuel;FPhis';FPhis;Fnp;Fsg;").
Proof.
  intros sg np Phis Phis' fuel cps g cuts exits H. unfold ejcertAF, eecheckJAF_pf, echeckJAF_pf, VK. rewrite H. reflexivity.
Qed.
End Lib_realloc_rom.

