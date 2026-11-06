(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "SAlu"; "cell"; "SPUle"; "sobj"; "valuation"; "soff"; "holds"; "SPBranch"; "enc_bytes"; "sv"; "SVar"; "eval"; "ob_cells"; "SPEq"; "c_off"; "c_val"; "c_width"; "covered"; "mkCell"; "obj_holds"; "obj_wf"; "smatch"; "ss_facts"; "ss_next"; "ss_objs"; "mkObj"; "ob_base"; "ob_dflt"; "ob_hi"; "ob_lo"; "sstate"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "modulo"; "pow"; "sub"; "lt"; "opp"; "mul"; "of_nat"; "to_nat"; "@Corelib.Init.Datatypes"; "cons"; "list"; "nat"; "Some"; "bool"; "option"; "true"; "nil"; "prod"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "vDp"; "spm"; "two47"; "vTOPfz"; "two40"; "fz_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue"; "Zsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_glue.Recell"; "cell_weq"; "recell_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "aceil"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_glue"; "WIN"; "hS"; "DNt"; "G10t"; "al_facts"; "vDN"; "vG10"; "vH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@Stdlib.Lists.List"; "Forall2"; "nth_error"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface.FZAddr"; "D_FZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase CursorGlue TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_fuzz_iface2.
Import ListNotations.
Import FZAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Recell.
Variable segs : list Segment.

Definition cell_weq (rho : valuation) (c c' : cell) : Prop := ltac2:(tb__ "0|2|
S2S1S10S15Vc';A1S15Vc;A1A3S2S1S0S17Vc';A1S17Vc;A1M0A3S1S31S55Q8A1A1SfS2fG0A1M1S12Vrho;S16Vc';A1A2A2SfG1S12Vrho;S16Vc;A1A2A2A3A2A2").

Definition recell_obj (o : sobj) (cells' : list cell) : sobj := ltac2:(tb__ "0|0|
S20S21Vo;A1S24Vo;A1S23Vo;A1Vcells';S22Vo;A1A5").

Lemma covered_weq : ltac2:(tb__ "0|1|
SbS31S8A1M0G0S0S53S8S8S44R4A1R3R2A5S4S18R5R3R2A3S18R5R4R2A3A2F_;Foff;Fcells';Fcells;Frho;").
Proof.
  intros rho cells cells' off H. unfold covered. induction H as [|c c' l l' (E1 & E2 & _) _ IH].
  - split; intros X; inversion X.
  - rewrite !Exists_cons, IH. unfold in_cell. rewrite E1, E2. tauto.
Qed.

Lemma obj_holds_recell : ltac2:(tb__ "0|0|
SbS5bSaS31S8A1S53S8S8S44R4A1S13R2A1R1A5S1aVsegs;R5R4R3A4S1aVsegs;R6R5S45R4R3A2A4F_;F_;Fcells';Fo;Fms;Frho;").
Proof.
  intros rho ms o cells' HW (Hb & Hw & Hc & Hd & Hi). unfold obj_holds, recell_obj, obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  split; [exact Hb|]. split; [exact Hw|]. split; [|split; [|exact Hi]].
  - clear Hd. induction HW as [|c c' l l' (E1 & E2 & E3) _ IH]; [constructor|].
    apply Forall_cons_iff in Hc as [Hc0 Hc]. constructor; [|exact (IH Hc)].
    unfold cell_holds in *. rewrite E1, E2, E3. exact Hc0.
  - intros off Ho Hnc. apply Hd; [exact Ho|]. intros X. apply Hnc. apply (covered_weq rho _ _ off HW). exact X.
Qed.

Theorem smatch_recell : ltac2:(tb__ "0|0|
SbS25S32SaS31S8A1S38S31S5dA1S5cA2S1S35SaA1S54SaS1fR5A1R4A3S33SaR3A2A3S1S34S1bS1eR6A1S45R4R3A2A2S36A3S47S5SdR8A1S1dR7A1A3S53S8S8S44R9A1S13R6A1R5A5F_;S1cVsegs;R9R8R4A4S1cVsegs;RaS5aR9R8S45R7R6A2A3R5A4F_;F_;F_;F_;Fw;Fcells';Fo;Fi;FS;Frho;").
Proof.
  intros rho S i o cells' [tr [ms md]] Hn Hwfo' HW Hsm.
  pose proof (smatch_swf segs _ _ _ Hsm) as Hwf.
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof (HW Hfacts) as HW'.
  pose proof (nth_error_split3 _ _ _ Hn) as EQ.
  assert (Hoh : obj_holds segs rho ms o).
  { destruct Hmem as (Hall & _ & _). rewrite EQ in Hall. apply Forall_app in Hall as [_ Hall]. inversion Hall; auto. }
  assert (Hrange : obj_range rho (recell_obj o cells') = obj_range rho o) by reflexivity.
  unfold smatch, reshape_obj_at. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split.
  { change (firstn i (ss_objs S) ++ recell_obj o cells' :: skipn (Datatypes.S i) (ss_objs S)) with (firstn i (ss_objs S) ++ [recell_obj o cells'] ++ skipn (Datatypes.S i) (ss_objs S)).
    eapply swf_objs_replace; [exact Hwf | exact EQ |]. cbn. rewrite Hwfo'. reflexivity. }
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hresv|].
  split; [|exact Hfacts].
  rewrite EQ in Hmem.
  change (firstn i (ss_objs S) ++ recell_obj o cells' :: skipn (Datatypes.S i) (ss_objs S)) with (firstn i (ss_objs S) ++ [recell_obj o cells'] ++ skipn (Datatypes.S i) (ss_objs S)).
  apply mem_match_replace with (o := o).
  - exact Hmem.
  - constructor; [exact (obj_holds_recell rho ms o cells' HW' Hoh)|]. constructor.
  - destruct Hmem as (_ & Hpd & _). apply pairwise_disjoint_pdr in Hpd.
    rewrite !map_app in Hpd |- *. cbn [map app] in Hpd |- *. rewrite Hrange. exact Hpd.
  - intros x. split.
    + intros Hx. exists (recell_obj o cells'). split; [cbn; auto|]. rewrite Hrange. exact Hx.
    + intros (o'' & Hin'' & Hx). destruct Hin'' as [<-|[]]. rewrite Hrange in Hx. exact Hx.
Qed.

Lemma SPA_recell : ltac2:(tb__ "0|0|
S59SbS52S32SaS31S8A1S31S55Q40A1A1S5eS1S35SaA1S54SaS1fS50R6A1A1R5A3S33SaR4A2A3S1S34S1bS1eS50R7A1A1S45R5R4A2A2S36A3S47S5SdR9A1S1dS50R8A1A1A3S53S8S8S44RaA1S13R7A1R6A5F_;S58Vsegs;RbR9RaR5R4A6S58Vsegs;RcS51RaS5aS50RaA1R9S45R8R7A2A3A2RbR6R5A6F_;F_;F_;F_;Fw;Ftp;Fcells';Fo;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i o cells' tp [tr [ms md]] Hn Hwf HW [(Hsm & HMI & Hwf' & Hsh & Hhz) Hk]. split; [|exact Hk].
  pose proof (smatch_recell rho (ax_S A) i o cells' _ Hn Hwf HW Hsm) as Hsm'.
  assert (Hin_o : In o (ss_objs (ax_S A))) by (eapply nth_error_In; exact Hn).
  split; [exact Hsm'|]. split; [exact HMI|]. split; [unfold axwf in Hwf' |- *; cbn; exact Hwf'|]. split; [|exact Hhz].
  apply shadow_ok_reobjs; [exact Hsh|]. apply xshadow_outside_cover; [exact Hsh|].
  unfold reshape_obj_at. cbn [set_objs ss_objs]. intros o2 x Ho2 Hx. apply in_app_or in Ho2 as [Ho2|[<-|Ho2]].
  - exists o2. split; [eapply In_firstn_In; exact Ho2 | exact Hx].
  - exists o. split; [exact Hin_o | exact Hx].
  - exists o2. split; [eapply In_skipn_In; exact Ho2 | exact Hx].
Qed.

Lemma enc_bytes_mod_eq : ltac2:(tb__ "0|3|
S32S55Q40M0A1M1G1S1S0S28S56G0R2A2S29Z2S2dZ8S2eR3A1A2A2M2A2S28S56G0R1A2G2A2A3S1S31S55Q8A1A1SfR4R3A2SfR4R2A2A3F_;Fb;Fa;Fk;").
Proof.
  intros k a b H. unfold enc_bytes. rewrite <- (SymSoundM.Z_to_le_bytes_mod k (bv_unsigned a)), <- (SymSoundM.Z_to_le_bytes_mod k (bv_unsigned b)), H. reflexivity.
Qed.
Lemma cell_weq_refl : ltac2:(tb__ "0|0|
SbS8S44R2R1R1A3Fc;Frho;").
Proof. intros rho c. repeat split. Qed.
Lemma cell_weq_lit : ltac2:(tb__ "0|3|
SbS10S0S0S0S1S0S28S28R1S29Z2M0Z40A2M1A2S29G0S2dZ8S2eS2fR3A1A1A2A2M2A2S28S28R2G1A2G2A2A3S44R6S19R5R4S6R3A1A3S19R5R4S6R2A1A3A3F_;Fz';Fz;Fw;Foff;Frho;").
Proof.
  intros rho off w z z' H. split; [reflexivity|]. split; [reflexivity|]. cbn [c_width c_val eval]. apply enc_bytes_mod_eq. rewrite !SymSoundV.lit_unsigned. exact H.
Qed.
End Recell.

Definition hS : sv := SAlu ALU_AND (spm 288) (SLit 18446744073709551584).

Definition vH : sv := SVar 100.  Definition vDN : sv := SVar 101.  Definition vG10 : sv := SVar 102.
Definition WIN : Z := 32752.

Definition DNt : sv := ltac2:(tb__ "0|0|
S7S3bS7S39S3eZ120A1S3dA3S49A3").
Definition G10t : sv := ltac2:(tb__ "0|0|
S7S3bS7S39S49S6Ze0A1A3S11PaA1A3").
Definition al_facts (h dn g : sv) : list sprop := ltac2:(tb__ "0|4|
S30S5S14S7S39Vh;Vdn;A3M0S7S39S3eZ120M1A1S3dA3A2S30S5S14S7S39S11PaA1M2Vg;A3M3S7S39Vh;S6Ze0A1A3A2S30S5SeS3aS6S2cS48A1A1Vdn;A3S30S5SeS3aVdn;S6S2cS41A1A1A3S30S5SeS3aS6N40A1Vg;A3S30S5SeS3aVg;S6N50A1A3S30S5S9S7S39Vh;S6G1A1A3G2A2S30S5S9G2S7S39Vh;S6Z130A1A3A2S30S5S9S6S46A1G0A2S30S5S9S40G0A2S30S5S9S6S26S46S48A2A1Vh;A2S30S5S9S7S39S40S6S48A1A3Vh;A2S30S5S9Vh;S6S2aS3fZ200A2A1A2S30S5S9S40G3A2S30S5S9S40S3eS57A1A2S37S5A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Lemma mod16_32 : ltac2:(tb__ "0|3|
S0S27Z0M0R1A2S1S0S28R2Z10M1A2G0A3S3S1S0S28R3Z20A2M2G0A3S1S0G2G1A3A2F_;F_;Fx;").
Proof.
  intros x Hx H. pose proof (Z.div_mod x 32 ltac:(lia)) as E. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as B.
  pose proof (Z.div_mod x 16 ltac:(lia)) as E16. rewrite H in E16.
  assert (E2 : x mod 32 = 16 * (x / 16 - 2 * (x / 32))) by lia. lia.
Qed.

Section Realign.
Variable rho : valuation.
Hypothesis HF : Forall (holds rho) fz_facts.
Let S := uval rho (SVar 10).
Let T := uval rho vTOPfz.
Let Du := uval rho vDp.

Lemma fz_S : ltac2:(tb__ "0|0|
S2S1S0S28VS;Z10A2Z0A3S2S27S26S46S57A2VS;A2S27VS;S2aS3fZe0A2A2A2A2").
Proof.
  fact HF (SPAlign 10 4) A1. fact HF (SPUle (SVar 10) (SLit (two47 - 224))) A2. fact HF (SPUle (SLit (aceil + D_FZ)) (SVar 10)) A3.
  cbn [holds] in A1. apply (proj1 (h_ule _ _ _)) in A2. apply (proj1 (h_ule _ _ _)) in A3. rewrite uval_lit in A2, A3 by (vm_compute; split; [discriminate | reflexivity]).
  unfold S, uval. cbn [eval]. change (2 ^ 4) with 16 in A1. split; [exact (proj2 A1) | split; [exact A3 | exact A2]].
Qed.

Lemma fz_D : ltac2:(tb__ "0|1|
S2S27S2cS41A1S43VDu;A1M0A2S27G0N8000A2A2").
Proof.
  fact HF (SPBranch BC_GE (SLit (- FZ_DEPTH)) vDp) A1. fact HF (SPBranch BC_GE vDp (SLit (- two40))) A2.
  apply (proj1 (holds_bge _ _ _)) in A1. apply (proj1 (holds_bge _ _ _)) in A2. rewrite U_lit in A1, A2. fold (uval rho vDp) in A1, A2. fold Du in A1, A2.
  change (Zsigned (- FZ_DEPTH mod M64v)) with (-32768) in A1. change (Zsigned (- two40 mod M64v)) with (- two40) in A2. lia.
Qed.
Lemma fz_T : aceil <= T <= 140737479966720.
Proof.
  fact HF (SPUle (SLit aceil) vTOPfz) A1. fact HF (SPUle vTOPfz (SLit 140737479966720)) A2.
  apply (proj1 (h_ule _ _ _)) in A1. apply (proj1 (h_ule _ _ _)) in A2. rewrite uval_lit in A1, A2 by (vm_compute; split; [discriminate | reflexivity]). fold T in A1, A2. lia.
Qed.
End Realign.

Lemma uval_addk : ltac2:(tb__ "0|1|
SbS10S0S2S27Z0S26S3cR3R2A2R1A2M0A2S2bG0S29Z2Z40A2A2A2S1S0S3cR4S7S39R3S6R2A1A3A2S26S3cR4R3A2R2A2A3F_;Fk;Fa;Frho;").
Proof.
  intros rho a k H. unfold uval in *. rewrite U_add, U_lit. unfold M64v. rewrite Zplus_mod_idemp_r. apply Z.mod_small. exact H.
Qed.

Lemma rl_consts : ltac2:(tb__ "0|0|
S2S1S0S46Z7fff7f800000A3S2S1S0S57Z8120A3S2S1S0S3fZ800000000000A3S2S1S0S41Z10000000000A3S2S1S0S48Z7ff0A3S1S0S29Z2Z40A2Z10000000000000000A3A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Lemma Zsigned_neg : ltac2:(tb__ "0|1|
S0S2S27S2cS29Z2M0Z3fA2A1R1A2S2bR1Z0A2A2S1S0S43S26R2S29G0Z40A2A2A1R2A3F_;Fz;").
Proof. intros z Hz. destruct (Zsigned_spec (z + 2 ^ 64)) as [[A E]|[A E]]; lia. Qed.
Lemma Zsigned_lit : ltac2:(tb__ "0|0|
SbS0S2S27S2cS29Z2Z3fA2A1R1A2S2bR1Z0A2A2S1S0S43S56Q40S12R3S6R2A1A2A2A1R2A3F_;Fk;Frho0;").
Proof.
  intros rho0 k Hk. rewrite U_lit. unfold M64v. replace (k mod 18446744073709551616) with (k + 2 ^ 64).
  - apply Zsigned_neg. exact Hk.
  - symmetry. replace k with (k + 2 ^ 64 + (-1) * 18446744073709551616) at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Section Realign2.
Variable rho : valuation.
Hypothesis HF : Forall (holds rho) fz_facts.
Let S := uval rho (SVar 10).
Let T := uval rho vTOPfz.
Let D : ltac2:(tb__ "0|0|
S0") := ltac2:(tb__ "0|0|
S43S3cVrho;S3dA2A1").
Let hv := uval rho hS.
Let dl := S - 288 - hv.
Let M := 2 ^ 64.

Lemma U_spm : ltac2:(tb__ "0|0|
S0S2S27Z0R1A2S27R1Z9c40A2A2S1S0S3cVrho;S3eR2A1A2S2aVS;R2A2A3F_;Fk;").
Proof.
  intros k Hk. pose proof (fz_S rho HF) as (_ & A & B). pose proof rl_consts as (C1 & C2 & C3 & _). fold S in A, B. unfold spm. rewrite uval_addk; fold S; lia.
Qed.
Lemma U_Du : ltac2:(tb__ "0|0|
S1S0S3cVrho;S3dA2S26VD;VM;A2A3").
Proof.
  pose proof (fz_D rho HF) as A. fold D in A. pose proof rl_consts as (_ & _ & _ & C4 & _). pose proof (uval_range rho vDp) as R.
  unfold D in *. destruct (Zsigned_spec (uval rho vDp)) as [[_ E]|[_ E]]; unfold M; lia.
Qed.
Lemma U_win : ltac2:(tb__ "0|2|
S2S1S0S3cVrho;S7S39S3eZ120M0A1S3dA3A2S26S2aVS;G0A2VD;A2M1A3S2S27S46G1A2S27VT;G1A2A2A2").
Proof.
  pose proof (fz_S rho HF) as (_ & A & B). pose proof (fz_D rho HF) as AD. fold S in A, B. fold D in AD. pose proof rl_consts as (C1 & C2 & C3 & C4 & _ & C6).
  assert (E : uval rho (SAlu ALU_ADD (spm 288) vDp) = S - 288 + D).
  { unfold uval. rewrite U_add. fold (uval rho (spm 288)). fold (uval rho vDp). rewrite (U_spm 288) by lia. rewrite U_Du. unfold M64v. fold M.
    replace (S - 288 + (D + M)) with (S - 288 + D + 1 * M) by lia. rewrite Z.mod_add by (unfold M; lia). apply Z.mod_small. unfold M. lia. }
  split; [exact E|].
  fact HF (SPUle (SLit aceil) (SAlu ALU_ADD (spm fz_frame) vDp)) A1. fact HF (SPUle vTOPfz (SAlu ALU_ADD (spm fz_frame) vDp)) A2.
  apply (proj1 (h_ule _ _ _)) in A1. apply (proj1 (h_ule _ _ _)) in A2. change fz_frame with 288 in A1, A2. rewrite E in A1, A2.
  rewrite uval_lit in A1 by (vm_compute; split; [discriminate | reflexivity]). fold T in A2. lia.
Qed.
Lemma hv_val : ltac2:(tb__ "0|0|
S2S1S0Vhv;S2aS2aVS;Z120A2Vdl;A2A3S3S1S0Vdl;Z0A3S1S0Vdl;Z10A3A2A2").
Proof.
  pose proof (fz_S rho HF) as (A0 & A & B). fold S in A0, A, B. pose proof rl_consts as (C1 & C2 & C3 & _).
  assert (E : hv = (S - 288) - (S - 288) mod 32).
  { unfold hv, hS, uval. cbn [eval]. rewrite and_val. fold (uval rho (spm 288)). rewrite (U_spm 288) by lia.
    rewrite lit_unsigned. change (18446744073709551584 mod 2 ^ 64) with (2 ^ 64 - 2 ^ 5). rewrite land_high_mask by lia. reflexivity. }
  split; [unfold dl; lia|]. unfold dl. rewrite E.
  assert (H16 : (S - 288) mod 16 = 0).
  { replace (S - 288) with (S + (-18) * 16) by lia. rewrite Z.mod_add by lia. exact A0. }
  destruct (mod16_32 (S - 288) ltac:(lia) H16) as [H|H]; rewrite H; lia.
Qed.
Lemma U_DNt : ltac2:(tb__ "0|0|
S1S0S3cVrho;S4aA2S26S26VD;Vdl;A2VM;A2A3").
Proof.
  pose proof U_win as (E & A1 & _). pose proof hv_val as (Eh & Hd). pose proof (fz_D rho HF) as AD. fold D in AD. pose proof rl_consts as (C1 & C2 & C3 & C4 & _ & C6).
  unfold DNt, uval. rewrite U_sub. fold (uval rho (SAlu ALU_ADD (spm 288) vDp)). fold (uval rho hS). fold hv. rewrite E, Eh. unfold M64v. fold M.
  replace (S - 288 + D - (S - 288 - dl)) with (D + dl + M + (-1) * M) by lia. rewrite Z.mod_add by (unfold M; lia). apply Z.mod_small. unfold M. lia.
Qed.
Lemma U_G10t : ltac2:(tb__ "0|0|
S1S0S3cVrho;S4bA2S26S2aN40Vdl;A2VM;A2A3").
Proof.
  pose proof hv_val as (Eh & Hd). pose proof (fz_S rho HF) as (_ & A & B). fold S in A, B. pose proof rl_consts as (C1 & C2 & C3 & C4 & _ & C6).
  unfold G10t, uval. rewrite U_sub. fold (uval rho (SAlu ALU_ADD hS (SLit 224))). fold (uval rho (SVar 10)). fold S.
  rewrite uval_addk by (fold hv; rewrite Eh; lia). fold hv. rewrite Eh. unfold M64v. fold M.
  replace (S - 288 - dl + 224 - S) with (-64 - dl + M + (-1) * M) by lia. rewrite Z.mod_add by (unfold M; lia). apply Z.mod_small. unfold M. lia.
Qed.

Theorem al_facts_hold : ltac2:(tb__ "0|0|
S47S5SdVrho;A1S4cS49S4aS4bA3A3").
Proof.
  pose proof U_win as (EW & AW & TW). pose proof hv_val as (Eh & Hd). pose proof U_DNt as EDN. pose proof U_G10t as EG.
  pose proof (fz_S rho HF) as (_ & AS & BS). fold S in AS, BS. pose proof (fz_D rho HF) as AD. fold D in AD. pose proof (fz_T rho HF) as AT. fold T in AT.
  pose proof rl_consts as (C1 & C2 & C3 & C4 & C5 & C6).
  assert (EHD : uval rho (SAlu ALU_ADD hS DNt) = S - 288 + D).
  { unfold uval. rewrite U_add. fold (uval rho hS). fold (uval rho DNt). fold hv. rewrite EDN, Eh. unfold M64v. fold M.
    replace (S - 288 - dl + (D + dl + M)) with (S - 288 + D + 1 * M) by lia. rewrite Z.mod_add by (unfold M; lia). apply Z.mod_small. unfold M. lia. }
  assert (EHG : uval rho (SAlu ALU_ADD (SVar 10) G10t) = hv + 224).
  { unfold uval. rewrite U_add. fold (uval rho (SVar 10)). fold (uval rho G10t). fold S. rewrite EG, Eh. unfold M64v. fold M.
    replace (S + (-64 - dl + M)) with (S - 288 - dl + 224 + 1 * M) by lia. rewrite Z.mod_add by (unfold M; lia). apply Z.mod_small. unfold M. lia. }
  assert (EH280 : uval rho (SAlu ALU_ADD hS (SLit 224)) = hv + 224) by (rewrite uval_addk; fold hv; [reflexivity | rewrite Eh; lia]).
  unfold al_facts. repeat (apply Forall_cons); [ | | | | | | | | | | | | | | | apply Forall_nil].
  - cbn [holds]. apply bv_eq. fold (uval rho (SAlu ALU_ADD hS DNt)). fold (uval rho (SAlu ALU_ADD (spm 288) vDp)). rewrite EHD, EW. reflexivity.
  - cbn [holds]. apply bv_eq. fold (uval rho (SAlu ALU_ADD (SVar 10) G10t)). fold (uval rho (SAlu ALU_ADD hS (SLit 224))). rewrite EHG, EH280. reflexivity.
  - apply (proj2 (holds_bge _ _ _)). fold (uval rho DNt). rewrite EDN. rewrite Zsigned_lit by (unfold WIN; lia). unfold M. rewrite Zsigned_neg by lia. lia.
  - apply (proj2 (holds_bge _ _ _)). fold (uval rho DNt). rewrite EDN. rewrite Zsigned_lit by (rewrite C4; lia). unfold M. rewrite Zsigned_neg by lia. lia.
  - apply (proj2 (holds_bge _ _ _)). fold (uval rho G10t). rewrite EG. rewrite Zsigned_lit by lia. unfold M. rewrite Zsigned_neg by lia. lia.
  - apply (proj2 (holds_bge _ _ _)). fold (uval rho G10t). rewrite EG. rewrite Zsigned_lit by lia. unfold M. rewrite Zsigned_neg by lia. lia.
  - apply (proj2 (h_ule _ _ _)). rewrite uval_addk; fold hv; fold S; rewrite Eh; lia.
  - apply (proj2 (h_ule _ _ _)). rewrite uval_addk; fold hv; fold S; rewrite Eh; lia.
  - apply (proj2 (h_ule _ _ _)). rewrite EHD. rewrite uval_lit by lia. lia.
  - apply (proj2 (h_ule _ _ _)). rewrite EHD. fold T. lia.
  - apply (proj2 (h_ule _ _ _)). rewrite uval_lit by lia. fold hv. rewrite Eh. lia.
  - apply (proj2 (h_ule _ _ _)). rewrite uval_addk by (fold T; lia). fold T. fold hv. rewrite Eh. lia.
  - apply (proj2 (h_ule _ _ _)). rewrite uval_lit by lia. fold hv. rewrite Eh. lia.
  - apply (proj2 (h_ule _ _ _)). rewrite EHG. fold T. rewrite Eh. lia.
  - apply (proj2 (h_ule _ _ _)). rewrite (U_spm D_FZ) by lia. fold T. lia.
Qed.
End Realign2.

Section Reshape.
Variable rho : valuation.
Hypothesis HF : Forall (holds rho) fz_facts.
Hypothesis HA : ltac2:(tb__ "0|0|
S47S5SdVrho;A1S4cS4fS4dS4eA3A3").
Let S := uval rho (SVar 10).
Let D : ltac2:(tb__ "0|0|
S0") := ltac2:(tb__ "0|0|
S43S3cVrho;S3dA2A1").
Let Hh := uval rho vH.
Let M := 2 ^ 64.

Lemma soff_U : ltac2:(tb__ "0|0|
S10S1S0ScVrho;R1A2S43S3cVrho;R1A2A1A3Fe;").
Proof. intros e. unfold soff, uval. apply bv_signed_U. Qed.
Lemma Zsigned_unneg : ltac2:(tb__ "0|2|
S0S2S27Z0M0R1A2S2bR1S29Z2Z40A2M1A2A2S2bS43R2A1G0A2S1S0R3S26S43R3A1G1A2A3F_;F_;Fu;").
Proof. intros u Hu Hn. destruct (Zsigned_spec u) as [[A E]|[A E]]; lia. Qed.

Lemma al_H : ltac2:(tb__ "0|0|
S2S27S26S46S48A2VHh;A2S27VHh;S2aS3fZ200A2A2A2").
Proof.
  fact HA (SPUle (SLit (aceil + WIN)) vH) A1. fact HA (SPUle vH (SLit (two47 - 512))) A2.
  apply (proj1 (h_ule _ _ _)) in A1. apply (proj1 (h_ule _ _ _)) in A2. rewrite uval_lit in A1, A2 by (vm_compute; split; [discriminate | reflexivity]). fold Hh in A1, A2. lia.
Qed.
Lemma soff_DpOff : ltac2:(tb__ "0|0|
S1S0ScVrho;S7S39S3dS6N120A1A3A2S2aVD;Z120A2A3").
Proof.
  pose proof (fz_D rho HF) as AD. fold D in AD. pose proof rl_consts as (C1 & C2 & C3 & C4 & C5 & C6).
  rewrite soff_U. unfold uval. rewrite U_add, U_lit. fold (uval rho vDp). rewrite (U_Du rho HF). fold D. unfold M64v.
  change (-288 mod 18446744073709551616) with (18446744073709551616 - 288).
  replace (D + 2 ^ 64 + (18446744073709551616 - 288)) with (D - 288 + 2 ^ 64 + 1 * 18446744073709551616) by lia. rewrite Z.mod_add by lia.
  rewrite Z.mod_small by lia. apply Zsigned_neg. lia.
Qed.
Lemma al_lo : ltac2:(tb__ "0|0|
S1S0S26VHh;ScVrho;S4dA2A2S26VS;ScVrho;S7S39S3dS6N120A1A3A2A2A3").
Proof.
  pose proof (U_win rho HF) as (EW & AW & _). pose proof al_H as AH. pose proof (fz_D rho HF) as AD. fold D in AD, EW, AW. fold S in EW, AW.
  pose proof rl_consts as (C1 & C2 & C3 & C4 & C5 & C6).
  fact HA (SPEq (SAlu ALU_ADD vH vDN) (SAlu ALU_ADD (spm 288) vDp)) E1. fact HA (SPBranch BC_GE (SLit (- WIN)) vDN) B1. fact HA (SPBranch BC_GE vDN (SLit (- two40))) B2.
  cbn [holds] in E1. apply (f_equal bv_unsigned) in E1. fold (uval rho (SAlu ALU_ADD vH vDN)) in E1. fold (uval rho (SAlu ALU_ADD (spm 288) vDp)) in E1. rewrite EW in E1.
  apply (proj1 (holds_bge _ _ _)) in B1. apply (proj1 (holds_bge _ _ _)) in B2. rewrite Zsigned_lit in B1 by (unfold WIN; lia). rewrite Zsigned_lit in B2 by (rewrite C4; lia).
  fold (uval rho vDN) in B1, B2. rewrite soff_DpOff, soff_U.
  pose proof (uval_range rho vDN) as RD. pose proof (Zsigned_unneg (uval rho vDN) RD ltac:(lia)) as EU.
  unfold uval in E1 at 1. rewrite U_add in E1. fold (uval rho vH) in E1. fold (uval rho vDN) in E1. fold Hh in E1. rewrite EU in E1. unfold M64v in E1.
  replace (Hh + (Zsigned (uval rho vDN) + 2 ^ 64)) with (Hh + Zsigned (uval rho vDN) + 1 * 18446744073709551616) in E1 by lia. rewrite Z.mod_add in E1 by lia.
  rewrite Z.mod_small in E1 by lia. lia.
Qed.
Lemma al_hi : ltac2:(tb__ "0|0|
S1S0S26VHh;Ze0A2S26VS;ScVrho;S4eA2A2A3").
Proof.
  pose proof al_H as AH. pose proof (fz_S rho HF) as (_ & AS & BS). fold S in AS, BS. pose proof rl_consts as (C1 & C2 & C3 & C4 & C5 & C6).
  fact HA (SPEq (SAlu ALU_ADD (SVar 10) vG10) (SAlu ALU_ADD vH (SLit 224))) E1. fact HA (SPBranch BC_GE (SLit (-64)) vG10) B1. fact HA (SPBranch BC_GE vG10 (SLit (-80))) B2.
  cbn [holds] in E1. apply (f_equal bv_unsigned) in E1. fold (uval rho (SAlu ALU_ADD (SVar 10) vG10)) in E1. fold (uval rho (SAlu ALU_ADD vH (SLit 224))) in E1.
  rewrite (uval_addk rho vH 224) in E1 by (fold Hh; lia). fold Hh in E1.
  apply (proj1 (holds_bge _ _ _)) in B1. apply (proj1 (holds_bge _ _ _)) in B2. rewrite Zsigned_lit in B1, B2 by lia. fold (uval rho vG10) in B1, B2. rewrite soff_U.
  pose proof (uval_range rho vG10) as RG. pose proof (Zsigned_unneg (uval rho vG10) RG ltac:(lia)) as EU.
  unfold uval in E1 at 1. rewrite U_add in E1. fold (uval rho (SVar 10)) in E1. fold (uval rho vG10) in E1. fold S in E1. rewrite EU in E1. unfold M64v in E1.
  replace (S + (Zsigned (uval rho vG10) + 2 ^ 64)) with (S + Zsigned (uval rho vG10) + 1 * 18446744073709551616) in E1 by lia. rewrite Z.mod_add in E1 by lia.
  rewrite Z.mod_small in E1 by lia. lia.
Qed.
End Reshape.

Lemma al_w : ltac2:(tb__ "0|3|
SbS47S5SdR1A1S42A3S2S1S0S26S3cR2S3eZ120A1A2M0ScR2S3dA2A2S26S3cR2S11PaA1A2M1ScR2S7S39S3dS6N120M2A1A3A2A2A3S1S0S26G0Z0A2S26G1G2A2A3A2F_;Frho;").
Proof.
  intros rho HF. rewrite (soff_DpOff rho HF), (U_spm rho HF 288) by lia. rewrite soff_U. lia.
Qed.
