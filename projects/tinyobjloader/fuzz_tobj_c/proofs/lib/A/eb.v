(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_fuzz_iface2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.

(* [comment removed for export] *)
Module Lib_fuzz_one_glue.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "SAlu"; "cell"; "SPUle"; "sobj"; "valuation"; "soff"; "holds"; "SPBranch"; "enc_bytes"; "sv"; "SVar"; "eval"; "ob_cells"; "SPEq"; "c_off"; "c_val"; "c_width"; "covered"; "mkCell"; "obj_holds"; "obj_wf"; "smatch"; "ss_facts"; "ss_next"; "ss_objs"; "mkObj"; "ob_base"; "ob_dflt"; "ob_hi"; "ob_lo"; "sstate"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "modulo"; "pow"; "sub"; "lt"; "opp"; "mul"; "of_nat"; "to_nat"; "@Corelib.Init.Datatypes"; "cons"; "list"; "nat"; "Some"; "bool"; "option"; "true"; "nil"; "prod"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "vDp"; "spm"; "two47"; "vTOPfz"; "two40"; "fz_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue"; "Zsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_fuzz_one_glue.Recell"; "cell_weq"; "recell_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "aceil"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_fuzz_one_glue"; "WIN"; "hS"; "DNt"; "G10t"; "al_facts"; "vDN"; "vG10"; "vH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@Stdlib.Lists.List"; "Forall2"; "nth_error"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface.FZAddr"; "D_FZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_fuzz_iface2.
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

Definition hS : sv := SAlu ALU_AND (spm 384) (SLit 18446744073709551584).

Definition vH : sv := SVar 100.  Definition vDN : sv := SVar 101.  Definition vG10 : sv := SVar 102.
Definition WIN : Z := 32752.

Definition DNt : sv := ltac2:(tb__ "0|0|
S7S3bS7S39S3eZ180A1S3dA3S49A3").
Definition G10t : sv := ltac2:(tb__ "0|0|
S7S3bS7S39S49S6Z118A1A3S11PaA1A3").
Definition al_facts (h dn g : sv) : list sprop := ltac2:(tb__ "0|4|
S30S5S14S7S39Vh;Vdn;A3M0S7S39S3eZ180M1A1S3dA3A2S30S5S14S7S39S11PaA1M2Vg;A3M3S7S39Vh;S6Z118A1A3A2S30S5SeS3aS6S2cS48A1A1Vdn;A3S30S5SeS3aVdn;S6S2cS41A1A1A3S30S5SeS3aS6N68A1Vg;A3S30S5SeS3aVg;S6N78A1A3S30S5S9S7S39Vh;S6G1A1A3G2A2S30S5S9G2S7S39Vh;S6Z190A1A3A2S30S5S9S6S46A1G0A2S30S5S9S40G0A2S30S5S9S6S26S46S48A2A1Vh;A2S30S5S9S7S39S40S6S48A1A3Vh;A2S30S5S9Vh;S6S2aS3fZ260A2A1A2S30S5S9S40G3A2S30S5S9S40S3eS57A1A2S37S5A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

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
S2S1S0S46Z7fff7f800000A3S2S1S0S57Z8180A3S2S1S0S3fZ800000000000A3S2S1S0S41Z10000000000A3S2S1S0S48Z7ff0A3S1S0S29Z2Z40A2Z10000000000000000A3A2A2A2A2A2").
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
Let dl := S - 384 - hv.
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
S2S1S0S3cVrho;S7S39S3eZ180M0A1S3dA3A2S26S2aVS;G0A2VD;A2M1A3S2S27S46G1A2S27VT;G1A2A2A2").
Proof.
  pose proof (fz_S rho HF) as (_ & A & B). pose proof (fz_D rho HF) as AD. fold S in A, B. fold D in AD. pose proof rl_consts as (C1 & C2 & C3 & C4 & _ & C6).
  assert (E : uval rho (SAlu ALU_ADD (spm 384) vDp) = S - 384 + D).
  { unfold uval. rewrite U_add. fold (uval rho (spm 384)). fold (uval rho vDp). rewrite (U_spm 384) by lia. rewrite U_Du. unfold M64v. fold M.
    replace (S - 384 + (D + M)) with (S - 384 + D + 1 * M) by lia. rewrite Z.mod_add by (unfold M; lia). apply Z.mod_small. unfold M. lia. }
  split; [exact E|].
  fact HF (SPUle (SLit aceil) (SAlu ALU_ADD (spm fz_frame) vDp)) A1. fact HF (SPUle vTOPfz (SAlu ALU_ADD (spm fz_frame) vDp)) A2.
  apply (proj1 (h_ule _ _ _)) in A1. apply (proj1 (h_ule _ _ _)) in A2. change fz_frame with 384 in A1, A2. rewrite E in A1, A2.
  rewrite uval_lit in A1 by (vm_compute; split; [discriminate | reflexivity]). fold T in A2. lia.
Qed.
Lemma hv_val : ltac2:(tb__ "0|0|
S2S1S0Vhv;S2aS2aVS;Z180A2Vdl;A2A3S3S1S0Vdl;Z0A3S1S0Vdl;Z10A3A2A2").
Proof.
  pose proof (fz_S rho HF) as (A0 & A & B). fold S in A0, A, B. pose proof rl_consts as (C1 & C2 & C3 & _).
  assert (E : hv = (S - 384) - (S - 384) mod 32).
  { unfold hv, hS, uval. cbn [eval]. rewrite and_val. fold (uval rho (spm 384)). rewrite (U_spm 384) by lia.
    rewrite lit_unsigned. change (18446744073709551584 mod 2 ^ 64) with (2 ^ 64 - 2 ^ 5). rewrite land_high_mask by lia. reflexivity. }
  split; [unfold dl; lia|]. unfold dl. rewrite E.
  assert (H16 : (S - 384) mod 16 = 0).
  { replace (S - 384) with (S + (-24) * 16) by lia. rewrite Z.mod_add by lia. exact A0. }
  destruct (mod16_32 (S - 384) ltac:(lia) H16) as [H|H]; rewrite H; lia.
Qed.
Lemma U_DNt : ltac2:(tb__ "0|0|
S1S0S3cVrho;S4aA2S26S26VD;Vdl;A2VM;A2A3").
Proof.
  pose proof U_win as (E & A1 & _). pose proof hv_val as (Eh & Hd). pose proof (fz_D rho HF) as AD. fold D in AD. pose proof rl_consts as (C1 & C2 & C3 & C4 & _ & C6).
  unfold DNt, uval. rewrite U_sub. fold (uval rho (SAlu ALU_ADD (spm 384) vDp)). fold (uval rho hS). fold hv. rewrite E, Eh. unfold M64v. fold M.
  replace (S - 384 + D - (S - 384 - dl)) with (D + dl + M + (-1) * M) by lia. rewrite Z.mod_add by (unfold M; lia). apply Z.mod_small. unfold M. lia.
Qed.
Lemma U_G10t : ltac2:(tb__ "0|0|
S1S0S3cVrho;S4bA2S26S2aN68Vdl;A2VM;A2A3").
Proof.
  pose proof hv_val as (Eh & Hd). pose proof (fz_S rho HF) as (_ & A & B). fold S in A, B. pose proof rl_consts as (C1 & C2 & C3 & C4 & _ & C6).
  unfold G10t, uval. rewrite U_sub. fold (uval rho (SAlu ALU_ADD hS (SLit 280))). fold (uval rho (SVar 10)). fold S.
  rewrite uval_addk by (fold hv; rewrite Eh; lia). fold hv. rewrite Eh. unfold M64v. fold M.
  replace (S - 384 - dl + 280 - S) with (-104 - dl + M + (-1) * M) by lia. rewrite Z.mod_add by (unfold M; lia). apply Z.mod_small. unfold M. lia.
Qed.

Theorem al_facts_hold : ltac2:(tb__ "0|0|
S47S5SdVrho;A1S4cS49S4aS4bA3A3").
Proof.
  pose proof U_win as (EW & AW & TW). pose proof hv_val as (Eh & Hd). pose proof U_DNt as EDN. pose proof U_G10t as EG.
  pose proof (fz_S rho HF) as (_ & AS & BS). fold S in AS, BS. pose proof (fz_D rho HF) as AD. fold D in AD. pose proof (fz_T rho HF) as AT. fold T in AT.
  pose proof rl_consts as (C1 & C2 & C3 & C4 & C5 & C6).
  assert (EHD : uval rho (SAlu ALU_ADD hS DNt) = S - 384 + D).
  { unfold uval. rewrite U_add. fold (uval rho hS). fold (uval rho DNt). fold hv. rewrite EDN, Eh. unfold M64v. fold M.
    replace (S - 384 - dl + (D + dl + M)) with (S - 384 + D + 1 * M) by lia. rewrite Z.mod_add by (unfold M; lia). apply Z.mod_small. unfold M. lia. }
  assert (EHG : uval rho (SAlu ALU_ADD (SVar 10) G10t) = hv + 280).
  { unfold uval. rewrite U_add. fold (uval rho (SVar 10)). fold (uval rho G10t). fold S. rewrite EG, Eh. unfold M64v. fold M.
    replace (S + (-104 - dl + M)) with (S - 384 - dl + 280 + 1 * M) by lia. rewrite Z.mod_add by (unfold M; lia). apply Z.mod_small. unfold M. lia. }
  assert (EH280 : uval rho (SAlu ALU_ADD hS (SLit 280)) = hv + 280) by (rewrite uval_addk; fold hv; [reflexivity | rewrite Eh; lia]).
  unfold al_facts. repeat (apply Forall_cons); [ | | | | | | | | | | | | | | | apply Forall_nil].
  - cbn [holds]. apply bv_eq. fold (uval rho (SAlu ALU_ADD hS DNt)). fold (uval rho (SAlu ALU_ADD (spm 384) vDp)). rewrite EHD, EW. reflexivity.
  - cbn [holds]. apply bv_eq. fold (uval rho (SAlu ALU_ADD (SVar 10) G10t)). fold (uval rho (SAlu ALU_ADD hS (SLit 280))). rewrite EHG, EH280. reflexivity.
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
S2S27S26S46S48A2VHh;A2S27VHh;S2aS3fZ260A2A2A2").
Proof.
  fact HA (SPUle (SLit (aceil + WIN)) vH) A1. fact HA (SPUle vH (SLit (two47 - 608))) A2.
  apply (proj1 (h_ule _ _ _)) in A1. apply (proj1 (h_ule _ _ _)) in A2. rewrite uval_lit in A1, A2 by (vm_compute; split; [discriminate | reflexivity]). fold Hh in A1, A2. lia.
Qed.
Lemma soff_DpOff : ltac2:(tb__ "0|0|
S1S0ScVrho;S7S39S3dS6N180A1A3A2S2aVD;Z180A2A3").
Proof.
  pose proof (fz_D rho HF) as AD. fold D in AD. pose proof rl_consts as (C1 & C2 & C3 & C4 & C5 & C6).
  rewrite soff_U. unfold uval. rewrite U_add, U_lit. fold (uval rho vDp). rewrite (U_Du rho HF). fold D. unfold M64v.
  change (-384 mod 18446744073709551616) with (18446744073709551616 - 384).
  replace (D + 2 ^ 64 + (18446744073709551616 - 384)) with (D - 384 + 2 ^ 64 + 1 * 18446744073709551616) by lia. rewrite Z.mod_add by lia.
  rewrite Z.mod_small by lia. apply Zsigned_neg. lia.
Qed.
Lemma al_lo : ltac2:(tb__ "0|0|
S1S0S26VHh;ScVrho;S4dA2A2S26VS;ScVrho;S7S39S3dS6N180A1A3A2A2A3").
Proof.
  pose proof (U_win rho HF) as (EW & AW & _). pose proof al_H as AH. pose proof (fz_D rho HF) as AD. fold D in AD, EW, AW. fold S in EW, AW.
  pose proof rl_consts as (C1 & C2 & C3 & C4 & C5 & C6).
  fact HA (SPEq (SAlu ALU_ADD vH vDN) (SAlu ALU_ADD (spm 384) vDp)) E1. fact HA (SPBranch BC_GE (SLit (- WIN)) vDN) B1. fact HA (SPBranch BC_GE vDN (SLit (- two40))) B2.
  cbn [holds] in E1. apply (f_equal bv_unsigned) in E1. fold (uval rho (SAlu ALU_ADD vH vDN)) in E1. fold (uval rho (SAlu ALU_ADD (spm 384) vDp)) in E1. rewrite EW in E1.
  apply (proj1 (holds_bge _ _ _)) in B1. apply (proj1 (holds_bge _ _ _)) in B2. rewrite Zsigned_lit in B1 by (unfold WIN; lia). rewrite Zsigned_lit in B2 by (rewrite C4; lia).
  fold (uval rho vDN) in B1, B2. rewrite soff_DpOff, soff_U.
  pose proof (uval_range rho vDN) as RD. pose proof (Zsigned_unneg (uval rho vDN) RD ltac:(lia)) as EU.
  unfold uval in E1 at 1. rewrite U_add in E1. fold (uval rho vH) in E1. fold (uval rho vDN) in E1. fold Hh in E1. rewrite EU in E1. unfold M64v in E1.
  replace (Hh + (Zsigned (uval rho vDN) + 2 ^ 64)) with (Hh + Zsigned (uval rho vDN) + 1 * 18446744073709551616) in E1 by lia. rewrite Z.mod_add in E1 by lia.
  rewrite Z.mod_small in E1 by lia. lia.
Qed.
Lemma al_hi : ltac2:(tb__ "0|0|
S1S0S26VHh;Z118A2S26VS;ScVrho;S4eA2A2A3").
Proof.
  pose proof al_H as AH. pose proof (fz_S rho HF) as (_ & AS & BS). fold S in AS, BS. pose proof rl_consts as (C1 & C2 & C3 & C4 & C5 & C6).
  fact HA (SPEq (SAlu ALU_ADD (SVar 10) vG10) (SAlu ALU_ADD vH (SLit 280))) E1. fact HA (SPBranch BC_GE (SLit (-104)) vG10) B1. fact HA (SPBranch BC_GE vG10 (SLit (-120))) B2.
  cbn [holds] in E1. apply (f_equal bv_unsigned) in E1. fold (uval rho (SAlu ALU_ADD (SVar 10) vG10)) in E1. fold (uval rho (SAlu ALU_ADD vH (SLit 280))) in E1.
  rewrite (uval_addk rho vH 280) in E1 by (fold Hh; lia). fold Hh in E1.
  apply (proj1 (holds_bge _ _ _)) in B1. apply (proj1 (holds_bge _ _ _)) in B2. rewrite Zsigned_lit in B1, B2 by lia. fold (uval rho vG10) in B1, B2. rewrite soff_U.
  pose proof (uval_range rho vG10) as RG. pose proof (Zsigned_unneg (uval rho vG10) RG ltac:(lia)) as EU.
  unfold uval in E1 at 1. rewrite U_add in E1. fold (uval rho (SVar 10)) in E1. fold (uval rho vG10) in E1. fold S in E1. rewrite EU in E1. unfold M64v in E1.
  replace (S + (Zsigned (uval rho vG10) + 2 ^ 64)) with (S + Zsigned (uval rho vG10) + 1 * 18446744073709551616) in E1 by lia. rewrite Z.mod_add in E1 by lia.
  rewrite Z.mod_small in E1 by lia. lia.
Qed.
End Reshape.

Lemma al_w : ltac2:(tb__ "0|3|
SbS47S5SdR1A1S42A3S2S1S0S26S3cR2S3eZ180A1A2M0ScR2S3dA2A2S26S3cR2S11PaA1A2M1ScR2S7S39S3dS6N180M2A1A3A2A2A3S1S0S26G0Z0A2S26G1G2A2A3A2F_;Frho;").
Proof.
  intros rho HF. rewrite (soff_DpOff rho HF), (U_spm rho HF 384) by lia. rewrite soff_U. lia.
Qed.
End Lib_fuzz_one_glue.

(* [comment removed for export] *)
Module Lib_arena_alloc.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "prod"; "nat"; "None"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "SVar"; "SPUle"; "cell"; "sobj"; "SAlu"; "DUnknown"; "mkObj"; "FcsrFrm0"; "SPAlign"; "mkSS"; "SPBranch"; "ss_objs"; "ss_regs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "NDA"; "AK0"; "AOpen"; "AV0"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc"; "c8"; "z0"; "SZ"; "tv0"; "vAR"; "vHD"; "p_fit"; "vDp"; "X_nohead"; "am_np"; "ndO"; "C_slow"; "O_F"; "O_W"; "O_ar"; "P_ok"; "X_aa"; "aa_facts"; "nd0"; "E_m"; "Pre_aa"; "base_fit"; "bd_m"; "ndMok"; "ndS"; "pN"; "spm"; "vCAP"; "vU"; "AL"; "CH"; "C_open"; "FUEL_aa"; "O_hdr"; "O_slot"; "P_fail"; "Pre_m"; "T_mnull"; "T_mok"; "X_fit"; "X_fit3"; "X_nofit"; "X_nofit2"; "X_nofitO"; "X_open"; "X_sret"; "X_sret3"; "ahd"; "am_ok"; "am_open"; "ar_cells"; "bd_ok"; "bd_open"; "bd_slow"; "cutpcs_aa"; "gh0"; "ndF"; "ndK"; "ndM"; "ok_facts"; "pad_fit"; "pre_regs_aa"; "slow_facts"; "slow_regs"; "tv_m"; "two40"; "two47"; "vNX"; "vUD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "BIc"; "KU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "pre_fregs"; "setregs"; "NF"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "A_globals"; "mkA"; "leavesA_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "e32"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.AAAddr"; "aa_ret"; "aa_slow"; "aa_entry"; "aa_open"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "add"; "opp"; "pow"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.RA.ReallocAddr"; "malloc_pc"; "thunk_alloc"; "thunk_calloc"; "thunk_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "NPOSTM"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
Module RA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Lib_realloc. End RA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma HTOP_ok : InitState.segs_top segs <= IMG_HI.
Proof. vm_compute. discriminate. Qed.

Module AAAddr.
  Definition aa_entry : Z := 0x9d8c8.
  Definition aa_open : Z := 0x9d918.
  Definition aa_slow : Z := 0x9d978.
  Definition aa_join : Z := 0x9daa4.
  Definition aa_ret : Z := 0x9dac8.
End AAAddr.
Import AAAddr.
Import RA.ReallocAddr.
Definition c8 := RA.c8. Definition spm := RA.spm. Definition vUD := RA.vUD. Definition two47 := RA.two47. Definition two40 := RA.two40.

Definition FUEL_aa : nat := 400%nat.
Definition SZ : Z := 72. Definition AL : Z := 16.
Definition vAR : sv := SVar 12. Definition vHD : sv := SVar 15. Definition vDp : sv := SVar 19.

Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S11SbPaA1S9N40A1S9Z0A1Vcells;S10A5").
Definition O_W : sobj := ltac2:(tb__ "0|0|
S11S3dZ40A1S2aS9Z0A1S2SdA1S10A5").
Definition ar_cells (hd : sv) : list cell := ltac2:(tb__ "0|2|
S0SdS23Z0M0S9S7fA1A2S0SdS23Z8S9S80A1A2S0SdS23Z10S9G0A1M1A2S0SdS23Z18S9S81A1A2S0SdS23Z20G1A2S0SdS23Z28S67A2S0SdS23Z30Vhd;A2S0SdS23Z38S9Z10000A1A2S2SdA1A3A3A3A3A3A3A3A3").
Definition O_ar (hd : sv) : sobj := ltac2:(tb__ "0|0|
S11S27S9Z0A1S9Z40A1S55Vhd;A1S10A5").
Definition O_hdr (hd nx cap u : sv) : sobj := ltac2:(tb__ "0|1|
S11Vhd;S9Z0M0A1S9Z18A1S0SdS23G0Vnx;A2S0SdS23Z8Vcap;A2S0SdS23Z10Vu;A2S2SdA1A3A3A3S10A5").
Definition O_slot (p : sv) : sobj := ltac2:(tb__ "0|0|
S11Vp;S9Z0A1S9S25A1S2SdA1S10A5").

Definition aa_facts : list sprop := ltac2:(tb__ "0|8|
S0SaS13PaM0Z4M1A2S0SaScSbG0A1M2S9S65A1M3A2S0SaScSbP1eA1M4SfS21S3dZ40M5A1M6S2aA3A2S0SaScG4G6A2S0SaScG4G2A2S0SaS15S22S9N1000A1S2aA3S0SaS15S22S2aS9S7bS64A1A1A3S0SaS13PcG1A2S0SaScS9Z1000A1S27A2S0SaScSfS21S27S9G5A1A3G4A2S0SaScS27G3A2S0SaScS28G4A2S0SaScS9Z7fff7f800000A1M7G4A2S0SaScG4S9Z7fffff800000A1A2S0SaScG7G2A2S2SaA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition pre_regs_aa : list sv := ltac2:(tb__ "0|1|
S6dS70S0S3S4S8A2M0S1S4S8UbS9S25A1A4S0G0S1S4S8UcS9S40A1A4S2G0A1A3A3A2").
Definition X_aa : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S8S8A2M0S1S8S8S27S9Z40A1A4S2G0A1A3").
Definition Pre_aa_S : sstate := ltac2:(tb__ "0|0|
S14S77S60S6cS12S5S8A1S6SeS0SeS2fS2SdA1A1S0SeS30S0SeS31S28A1S2SeA1A3A3A3S71A3S34S6eS7A9").
Definition Pre_aa : axst := mkA Pre_aa_S X_aa.
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S8S8A2M0S1S8S8S27S9Z40A1A4S2G0A1A3").
Definition CH : list bitem := ltac2:(tb__ "0|2|
S0S68S69Z1M0Z0M1Zf0A3S0S68S69G1G0Z160A3S2S68A1A3A3").

Definition cutpcs_aa : list Z := ltac2:(tb__ "0|0|
S0S18S78S0S18S76S0S18S7eS2S18A1A3A3A3").
Definition leafA_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S7dS1aVk;S73S43S59VS;Vpc;A4S37A4").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition X_open : axst := Eval vm_compute in leafA_at Pre_aa aa_open 0.
Definition nO : positive := ss_next (ax_S X_open).
Definition C_open : axst := Eval vm_compute in open_stateA X_open vHD.

Definition vNX : sv := Eval vm_compute in SVar nO.
Definition vCAP : sv := Eval vm_compute in SVar (nO + 1).
Definition vU : sv := Eval vm_compute in SVar (nO + 2).
Definition am_open : amode := ltac2:(tb__ "0|0|
S1fS28S66S3eS2S3S8S8A2A1A4").
Definition bd_open : list bitem := CH ++ POT vU.

Definition X_nohead : axst := Eval vm_compute in leafA_at Pre_aa aa_slow 0.

Definition X_nofitO : axst := Eval vm_compute in leafA_at C_open aa_slow 0.
Definition X_nofit : axst := Eval vm_compute in leafA_at C_open aa_slow 1.
Definition X_fit : axst := Eval vm_compute in leafA_at C_open aa_ret 0.

Definition E0 : list bitem := ltac2:(tb__ "0|2|
S0S68S69Z1M0Z0M1S20A3S0S68S69G1G0S1eA3S2S68A1A3A3").
Definition slow_regs : list sv := ltac2:(tb__ "0|1|
S6dS17S1bS2bA1A1S0S3S4S8A2M0S1S4S8UbSbP65A1A4S0G0S1S4S8UdSbP66A1A4S0G0S1S4S8UeSbP67A1A4S0G0S1S4S8UfSbP68A1A4S0G0S1S4S8U10SbP69A1A4S0G0S1S4S8U11SbP6aA1A4S0G0S1S4S8U5SbP6bA1A4S2G0A1A3A3A3A3A3A3A3A2").

Definition slow_facts : list sprop :=
  Eval vm_compute in List.filter (fun f => negb (sprop_eqb f (SPBranch BC_EQ vHD (SLit 0)))) (ss_facts (ax_S X_nohead)).

Definition gh0 : sprop := SPEq (SVar 108) (SLit 0).
Definition C_slow : axst := ltac2:(tb__ "0|0|
S72S14S76S62S6cS12S5S8A1S16S1bS2bA1A1S0SaS5aS61A3P6dS7A9S33A2").
Definition bd_slow : list bitem := CH ++ E0.
Definition am_np : amode := AHead vHD false.

Definition E_m : axst := Eval vm_compute in leafA_at C_slow malloc_pc 0.
Definition Pre_m : axst := Pre_malloc AE_A [] UStopLe.
Definition s_m : wsub := ltac2:(tb__ "0|0|
S0S3S19S8A2S1S19S8PfS2aA4S6bPaS1bS36A1S1bS47A1A3A3").
Definition R_m : list sobj := Eval vm_compute in optR (entails_frA E_m Pre_m s_m).
Definition pN : positive := Eval vm_compute in pos_add_nat (ss_next (ax_S E_m)) 10.
Definition blkN : sv * sv := ltac2:(tb__ "0|0|
S1S8S8SbS3cA1S9Z10020A1A4").
Definition T_mnull : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_null AE_A [] UStopLe).
Definition T_mok0 : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_ok AE_A [] UStopLe).
Definition mok_facts : list sprop := tv_factsA blkN.
Definition T_mok : axst := ax_add_facts mok_facts T_mok0.

Definition bd_m : list bitem := ltac2:(tb__ "0|2|
S0S68S69Z1M0Z0M1Zf0A3S0S68S69G1G0S79S7aS1eZ160A2S6aA2A3S2S68A1A3A3").
Definition tv_m : list (sv * sv) := blkN :: tv0.

Definition X_sret : axst := Eval vm_compute in leafA_at T_mok aa_ret 0.
Definition optAp (x : option axst) : axst := match x with Some a => a | None => Pre_aa end.

Fixpoint find_idxb {T} (f : T -> bool) (l : list T) (k : nat) : nat :=
  match l with [] => k | x :: r => if f x then k else find_idxb f r (S k) end.
Definition iN : nat := Eval vm_compute in find_idxb (fun o => sv_eqb (ob_base o) (SVar pN)) (ss_objs (ax_S X_sret)) 0%nat.
Definition sel_sret : list nat := Eval vm_compute in (List.filter (fun j => negb (Nat.eqb j iN)) (seq 0 (length (ss_objs (ax_S X_sret))))) ++ [iN].
Definition X_sret1 : axst := Eval vm_compute in optAp (apply_axforms X_sret [AXSelect sel_sret; AXSplit (length sel_sret - 1) (SLit 24)]).
Definition X_sret2 : axst := Eval vm_compute in drop_lastA X_sret1 (removelast (ss_objs (ax_S X_sret1))).
Definition p_new : sv := ltac2:(tb__ "0|0|
SfS21SbS3cA1S9Z20A1A3").
Definition X_sret3 : axst := Eval vm_compute in carve_stateA X_sret2 p_new (SLit SZ).
Definition new_facts : list sprop := ltac2:(tb__ "0|0|
S0SaScS9Z18A1S9Z20A1A2S2SaA1A3").

Definition p_fit : sv := Eval vm_compute in nth 10 (ss_regs (ax_S X_fit)) (SLit 0).
Definition u_fit : sv := Eval vm_compute in
  match find (fun o => sv_eqb (ob_base o) vHD) (ss_objs (ax_S X_fit)) with
  | Some o => match find (fun c => sv_eqb (c_off c) (SLit 16)) (ob_cells o) with Some c => c_val c | None => SLit 0 end
  | None => SLit 0 end.
Definition base_fit : sv := ltac2:(tb__ "0|0|
SfS21SfS21S28S9Z20A1A3S3fA3").
Definition pad_fit : sv := SAlu ALU_SUB p_fit base_fit.
Definition need_fit : sv := ltac2:(tb__ "0|0|
SfS21SfS21S3fS9S25A1A3S5fA3").

Definition nofit_fact : sprop := SPUle (SLit 65449) vU.
Definition X_nofit1 : axst := Eval vm_compute in drop_lastA X_nofit (removelast (ss_objs (ax_S X_nofit))).
Definition X_nofit2 : axst := Eval vm_compute in ax_with_facts X_nofit1 (nofit_fact :: ss_facts (ax_S X_nofit1)).
Definition fit_facts : list sprop := ltac2:(tb__ "0|0|
S0SaScS38S29A2S0SaScS29SfS21S38S9ZfA1A3A2S0SaScS9Z1000A1S29A2S0SaScS29SbP1eA1A2S0SaScSfS21S29S9S25A1A3SfS21S28S74S3eA1A3A2S2SaA1A3A3A3A3A3").
Definition X_fit3 : axst := Eval vm_compute in ax_with_facts (carve_stateA X_fit p_fit (SLit SZ)) (fit_facts ++ ss_facts (ax_S X_fit)).

Definition P_fail : axst := ltac2:(tb__ "0|1|
S72S14S75S6dS6fS6eA1S0S3S4S8A2M0S1S4S8UaS9Z0A1A4S2G0A1A3A2S6cS12S5S8A1S6SeS0SeS2fS2SdA1A1S0SeS30S0SeS31S28A1S2SeA1A3A3A3S71A3S34S82S7A9S33A2").
Definition ok_facts : list sprop := ltac2:(tb__ "0|8|
S0SaScSbP90A1SbP8fA1M0A2S0SaScS9Z10000A1G0A2S0SaScG0S9S79S7cZ2Z28A2Z21A2A1A2S0SaScSfS21SbP8dM1A1M2S74G0A1A3M3SbP1eA1M4A2S0SaScG2G4A2S0SaScS9Z1000A1G2A2S0SaS13G1Z4M5A2S0SaScSfS21G2S9Z18A1A3SbP8cM6A1M7A2S0SaScSfS21G7S9S25A1A3G3A2S0SaS13G6G5A2S2SaA1A3A3A3A3A3A3A3A3A3A3").
Definition P_ok : axst := ltac2:(tb__ "0|4|
S72S14S75S6dS6fS6eA1S0S3S4S8A2M0S1S4S8UaSbP8cA1M1A4S2G0A1A3A2S6cS12S5S8A1S6SeS0SeS2fS2SdA1A1S0SeS30S0SeS31SbP8dA1M2A1S0SeS44G2SbP8eA1SbP8fA1M3SbP90A1A4S0SeS45G1A1S2SeA1A3A3A3A3A3S71A3S6SaS5eS34A3P91S7A9S0S3S8S8A2S1S8S8G2S74G3A1A4S33A3A2").
Definition am_ok : amode := ltac2:(tb__ "0|1|
S1fSbP8dA1SbP8eA1SbP8fA1S0S3S8S8A2M0S1S8S8SbP8cA1S9S25A1A4S2G0A1A3A4").
Definition bd_ok : list bitem := POT (SVar 144).

Definition s_fit : wsub := ltac2:(tb__ "0|0|
S6bP64S1bS4bA1S1bS32A1A3").
Definition s_sret : wsub := ltac2:(tb__ "0|0|
S6bP64S1bS51A1S1bS32A1A3").
Definition s_nofit : wsub := ltac2:(tb__ "0|0|
S0S3S19S8A2S1S19S8P6cS9Z0A1A4S6bP64S1bS4dA1S1bS2eA1A3A3").
Definition s_nohead : wsub := ltac2:(tb__ "0|0|
S0S3S19S8A2S1S19S8P6cS9Z0A1A4S6bP64S1bS2bA1S1bS2eA1A3A3").

Definition ahd : amode := AHead vHD true.
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S1dS26S2S3S3S8S18A2S8A2A1S41S52A4").
Definition ndO : ndesc := ltac2:(tb__ "0|0|
S1dS26S2S3S3S8S18A2S8A2A1S57S54A4").
Definition ndS : ndesc := ltac2:(tb__ "0|0|
S1dS26S2S3S3S8S18A2S8A2A1S58S2cA4").
Definition ndM : ndesc := ltac2:(tb__ "0|0|
S1dS26S2S3S3S8S18A2S8A2A1S39S2cA4").
Definition ndMok : ndesc := ltac2:(tb__ "0|0|
S1dS63S2S3S3S8S18A2S8A2A1S39S2cA4").
Definition ndF : ndesc := ltac2:(tb__ "0|0|
S1dS26S2S3S3S8S18A2S8A2A1S2S68A1S2cA4").
Definition ndK : ndesc := ltac2:(tb__ "0|0|
S1dS26S2S3S3S8S18A2S8A2A1S56S53A4").
Definition z0 : sv := SLit 0.
Definition cutsE : list edescA := ltac2:(tb__ "0|4|
S0S3S3S1aS1cA2M0S3S18S8A2M1A2M2S1G0G1S1S1aS1cS37S35A4S1S18S8Z64S24A4A4S0G2S1G0G1S1S1aS1cS42S2dA4S1S18S8Z5aS24A4A4S0G2S1G0G1S1S1aS1cS2eS3bA4S1S18S8Z50S24A4A4S0G2S1G0G1S1S1aS1cS48S5dA4S1S18S8Z41S24A4M3A4S0G2S1G0G1S1S1aS1cS49S3aA4G3A4S2G2A1A3A3A3A3A3").
Definition exitsE : list edescA := ltac2:(tb__ "0|6|
S0S3S3S1aS1cA2M0S3S18S8A2M1A2M2S1G0G1S1S1aS1cS4fS35A4S1S18S8Z5fS24A4M3A4S0G2S1G0G1S1S1aS1cS2bS35A4G3A4S0G2S1G0G1S1S1aS1cS4eS2dA4S1S18S8Z55S24A4M4A4S0G2S1G0G1S1S1aS1cS4cS2dA4G4A4S0G2S1G0G1S1S1aS1cS4aS2dA4G4A4S0G2S1G0G1S1S1aS1cS36S3bA4S1S18S8Z46S24A4A4S0G2S1G0G1S1S1aS1cS50S3aA4S1S18S8Z3cS24A4A4S0G2S1G0G1S1S1aS1cS46S5bA4S1S18S8Z0S24A4M5A4S0G2S1G0G1S1S1aS1cS32S5cA4G5A4S2G2A1A3A3A3A3A3A3A3A3A3").
End Lib_arena_alloc.

(* [comment removed for export] *)
Module Lib_vec_reserve_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "ss_facts"; "SVar"; "SLit"; "@Corelib.Init.Datatypes"; "Some"; "app"; "option"; "nil"; "pair"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "E_r15f"; "E_rW1f"; "E_c8"; "E_cW0"; "Pre_c"; "Xk_r"; "inj"; "kbytes"; "s_c"; "s_r"; "vW"; "xf_rback"; "E_r15x"; "E_rW1x"; "R_c8"; "R_cW0"; "R_r15"; "R_rW1"; "T_r15f0"; "T_r15ok0"; "T_r15okB"; "T_rW1f0"; "T_rW1ok0"; "T_rW1okB"; "X15"; "X8"; "XW0"; "XW1"; "kn15"; "tvf0"; "xf_rcall"; "E_r15"; "E_rW1"; "FUEL_vr"; "N15"; "N8"; "NW0"; "NW1"; "T_c8n0"; "T_c8ok"; "T_c8ok0"; "T_c8ok2"; "T_cW0n0"; "T_cW0ok"; "T_cW0ok0"; "T_cW0ok2"; "T_r15f"; "T_r15ok"; "T_rW1f"; "T_rW1ok"; "cutpcs_vr"; "cutsE"; "exitsE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve.RA"; "Pre_ra"; "P_fail"; "P_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "tv_factsA"; "ejcertA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "UStopLe"; "ulink"; "L_calloc_null"; "L_calloc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRAddr RA.ReallocAddr.

Lemma ejcertA_ok : ltac2:(tb__ "0|0|
S2SdS4bS53S54S32S43P64S44S45A7SeA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma E_r15x_eq : ltac2:(tb__ "0|0|
S2SaS0A1S10S30S2fA2S8S0S1dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_rW1x_eq : ltac2:(tb__ "0|0|
S2SaS0A1S10S31S2fA2S8S0S1eA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_r15f_eq : ltac2:(tb__ "0|0|
S2S0SfS1dS9S4S2eS5S1S1dA1A1A3A2S11A3"). Proof. reflexivity. Qed.
Lemma E_rW1f_eq : ltac2:(tb__ "0|0|
S2S0SfS1eS9S4S2eS5S1S1eA1A1A3A2S12A3"). Proof. reflexivity. Qed.
Lemma T_r15f0_eq : ltac2:(tb__ "0|0|
S2S0S4cS46S11S1aS11A1S21S47S16A6S23A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_r15ok0_eq : ltac2:(tb__ "0|0|
S2S0S4cS46S11S1aS11A1S21S48S16A6S24A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1f0_eq : ltac2:(tb__ "0|0|
S2S0S4cS46S12S1aS12A1S22S47S16A6S26A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1ok0_eq : ltac2:(tb__ "0|0|
S2S0S4cS46S12S1aS12A1S22S48S16A6S27A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_r15f_eq : ltac2:(tb__ "0|0|
S2SaS0A1S10S23S1cA2S8S0S3fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1f_eq : ltac2:(tb__ "0|0|
S2SaS0A1S10S26S1cA2S8S0S41A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_r15okB_eq : ltac2:(tb__ "0|0|
S2SaS0A1S10S24S1cA2S8S0S25A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1okB_eq : ltac2:(tb__ "0|0|
S2SaS0A1S10S27S1cA2S8S0S28A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_r15ok_eq : ltac2:(tb__ "0|0|
S2S0S49S4aScS3S3S6P8dA1S18S2dA1A4A1S25A2S40A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1ok_eq : ltac2:(tb__ "0|0|
S2S0S49S4aScS3S3S6P8dA1S18S1bA1A4A1S28A2S42A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_cW0n0_eq : ltac2:(tb__ "0|0|
S2S0S4dS15S14S19S14A1S20S51S4eSbS50A1S4fA3A5S3bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_cW0ok0_eq : ltac2:(tb__ "0|0|
S2S0S4dS15S14S19S14A1S20S52S4eSbS50A1S4fA3A5S3dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_c8n0_eq : ltac2:(tb__ "0|0|
S2S0S4dS15S13S19S13A1S1fS51S4eSbS50A1S4fA3A5S37A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_c8ok0_eq : ltac2:(tb__ "0|0|
S2S0S4dS15S13S19S13A1S1fS52S4eSbS50A1S4fA3A5S39A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_cW0ok_eq : ltac2:(tb__ "0|0|
S2S0S49S4aScS3S3S6P70A1S18S1bA1A4A1S3eA2S3cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_c8ok_eq : ltac2:(tb__ "0|0|
S2S0S49S4aScS3S3S6P70A1S18S7Z8A1A1A4A1S3aA2S38A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma N15_eq : ltac2:(tb__ "0|0|
S2S0SfS29S9S4S17S2dA1S5S1S29A1A1A3A2S33A3"). Proof. reflexivity. Qed.
Lemma NW1_eq : ltac2:(tb__ "0|0|
S2S0SfS2cS9S4S17S1bA1S5S1S2cA1A1A3A2S36A3"). Proof. reflexivity. Qed.
Lemma NW0_eq : ltac2:(tb__ "0|0|
S2S0SfS2bS9S4S17S1bA1S5S1S2bA1A1A3A2S35A3"). Proof. reflexivity. Qed.
Lemma N8_eq : ltac2:(tb__ "0|0|
S2S0SfS2aS9S4S17S7Z8A1A1S5S1S2aA1A1A3A2S34A3"). Proof. reflexivity. Qed.
End Lib_vec_reserve_eqs.

(* [comment removed for export] *)
Module Lib_vec_reserve_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "zlog15"; "KU"; "bitem"; "bd_nn"; "bsumK"; "bsumV"; "bd_below"; "BIc"; "BIs"; "BXok_d"; "ZK"; "bd_subst"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "ss_facts"; "sobj"; "SLit"; "sprop_eqb"; "ss_next"; "SVar"; "SPUle"; "holds"; "SPBranch"; "SPNot"; "mkObj"; "rw"; "DUnknown"; "ob_cells"; "sprop_below"; "eval"; "ss_objs"; "DZero"; "cell"; "obj_range"; "obj_wf"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "xr_below"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "prod"; "pair"; "nil"; "cons"; "app"; "Some"; "None"; "option"; "fst"; "snd"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "pow"; "add"; "lt"; "sub"; "div"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "vK"; "vW"; "kbytes"; "bdP"; "nd0"; "s_r"; "vDt"; "vE"; "cutsE"; "vAl"; "E_c8'"; "E_cW0'"; "O_data"; "Pre_c"; "Xk_r"; "inj"; "kn15"; "s_c"; "vV"; "O_W"; "O_vec"; "tv0"; "vC"; "B32"; "PD_ra"; "z0"; "E_r15f"; "E_rW1f"; "Pre_vr"; "R_c8"; "R_cW0"; "X15"; "X8"; "XW0"; "XW1"; "X_vr"; "ndG"; "ndN"; "spm"; "tvf0"; "B_EW"; "E_c8"; "E_cW0"; "E_r15"; "E_rW1"; "O_alv"; "P_fail"; "P_grown"; "P_keep"; "exitsE"; "tvP"; "two47"; "two48"; "vKn"; "xf_rback"; "xf_rcall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.Lists.List"; "existsb"; "In"; "forallb"; "hd"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "tv_factsA"; "JA_pre"; "ND"; "emeasA"; "ffinA"; "nd_below"; "JA"; "JLA"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_vec_reserve_pf"; "P0_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_vec_reserve_pf.Sum"; "baseF"; "basez"; "s_rbd"; "JL"; "Posts_vr"; "injF"; "injz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkPA"; "entails_frA"; "import_subA"; "J_ofPA"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve.RA"; "Pre_ra"; "P0_ra"; "tv0"; "P_fail"; "P_ok"; "bd0"; "ndR"; "tvP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "csz"; "payA"; "site_okA"; "T_afterA"; "call_checkTA"; "robjs_okA"; "xrs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "ulink"; "unwind_stopJ"; "J_alloc_pre"; "L_calloc_null"; "L_calloc_ok"; "Posts_calloc"; "Pre_calloc"; "V_RES"; "V_TOP"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "calloc_size";
"@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "BC_NE"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "pos_add_nat"; "call_linkP"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "FBx"; "T0"; "T_ok"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "drop_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "robjs_okF"; "xrs_okF"; "FFx"; "PostsC"; "pd_okA"; "pdescA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_vec_reserve_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRAddr RA.ReallocAddr.

Lemma uval_kn15 : ltac2:(tb__ "0|1|
S12S3eS3R1S46A2S5dA2S0S2fS3R2S56A2S41S3R2S46A2M0S44G0Z2A2A2A3F_;Frho;").
Proof.
  intros rho HK. unfold kn15. pose proof (uval_range rho vK).
  assert (E1 : uval rho (SAlu ALU_SRL vK (SLit 1)) = uval rho vK / 2).
  { unfold uval. rewrite U_srl_lit. change (2 ^ (1 mod 64)) with 2. reflexivity. }
  unfold B32 in HK. rewrite uval_add_small; rewrite E1; [lia|]. pose proof (Z.div_le_upper_bound (uval rho vK) 2). lia.
Qed.

Definition P0_vr (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S1S2S0S2fS83Q40M0S1fVr;P11A2A2Z0M1A3A1S2S0S2fS83G0S1fVr;PfA2A2G1A3A1F_;S1S9dVFF;S83G0S1fVr;PcA2A2Z20A3S9dVFF;S83G0S1fVr;PeA2A2Z30A3A2A2").

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
ScdS12S33S82Q40A1A1Sd3OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
ScaS45VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S2fSefVCST;R1A2S1S3eZ0R2A2S42R2SeeA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S2fSefVXGL;R1A2S1S3eZ0R2A2S42R2SeeA2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S33S34S34S2fS2fA2S2fA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 3 BX.
Variable rho0 : valuation.

Definition JL (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S92VAInv;VCST;VXGL;VKc;S95VFB;VFF;A2VFB;VFF;VBX;S8aVnd;Aa").
Definition Posts_vr : list (axst * jpostA) := ltac2:(tb__ "0|2|
S37S34S2aSa2A2M0S35S2aSa2S76S99S4aA1A4S37G0S35S2aSa2S74S99S8dS5bS36S34S34S11S2fA2S11A2A1M1S36S6A1A3A1A4S37G0S35S2aSa2S75S99S8dS78G1S49S47S7bA2A3A1A4S36G0A1A3A3A3").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S91VAInv;VCST;VXGL;S7eVKc;Vrho0;S95VFB;VFF;A2VFB;VFF;VBX;S8aVnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S34S2aS89A2SdcFn;") := ltac2:(tb__ "0|0|
S93VAInv;VCST;VXGL;S7eVKc;Vrho0;S95VFB;VFF;A2VFB;VFF;VBX;S8aAb").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
Sa3S45S7eVrho0;Vtp0;S9aA5").

Lemma range_data : ltac2:(tb__ "0|2|
S12S11S11S2fS42S3R4S48R2A1A2S40Z2Z3fA2A2S1S3eS3cS2fS2fS27R5S52R4S48R3A1A2A2M0A3R2A2S42R2S3dS2fS2fG0A3A2A2S1S3eS3R6R5A2M1R3A2S42R3S41G1S3R6S48R4A1A2A2A2A2F_;F_;Fa;Fk;Fd;Frho;").
Proof.
  intros rho d k a Hk Hr. unfold obj_range, obj_lo_of, obj_hi_of, O_data in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. rewrite (soff_smallu rho (kbytes k) Hk) in Hr. unfold uval in *. lia.
Qed.

Definition baseF (F : list sprop) : Prop := ltac2:(tb__ "0|3|
S1S0S31S84S13S17S1aS19P1eA1M0S6cZ40A1A2A1VF;A3S32A3S1S0S31S84S13S17S1aG0S19PaA1M1A2A1VF;A3S32A3S1S0S31S84S13S17S1aG1S16S79A1A2A1VF;A3S32A3S1S0S31S84S13S17S1aS16Z1A1S4dA2A1VF;A3S32A3S1S0S31S84S13S17S1aS4dS16Z1000A1A2A1VF;A3S32A3S1S0S31S84S13S17S1aS47S16S7aA1A2A1VF;A3S32A3S1S0S31S84S13S17S1aS46S16S5dA1M2A2A1VF;A3S32A3S1S0S31S84S13S17S1aS48S47A1S16S6eA1A2A1VF;A3S32A3S1S0S31S84S13S17S1aS48S46A1G2A2A1VF;A3S32A3S1S0S31S84S13S17S1aS16Z7fff7f800000A1G0A2A1VF;A3S32A3S0S31S84S13S17S1aG0S16Z7fffff800000A1A2A1VF;A3S32A3A2A2A2A2A2A2A2A2A2A2").
Record basez (rho : valuation) : Prop := BZ {
  bz_sp : aceil + 64 <= uval rho (SVar 10) <= 2 ^ 47;
  bz_e : 1 <= uval rho vE <= 4096;
  bz_w : uval rho vW <= 2 ^ 48;
  bz_k : uval rho vK <= B32;
  bz_ew : uval rho (kbytes vW) = uval rho vE * uval rho vW /\ uval rho (kbytes vW) <= B_EW;
  bz_ek : uval rho (kbytes vK) = uval rho vE * uval rho vK /\ uval rho (kbytes vK) <= B32;

  bz_top : bv_unsigned (rw rho V_TOP) + 64 <= uval rho (SVar 10) /\ 140735332483072 <= bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Lemma uval_spm : ltac2:(tb__ "0|1|
S12S2fS1S3eZ0R1A2S3eR1S3R2S19PaA1M0A2A2A2S0S2fS3R3S6cR2A1A2S43S3R3G0A2R2A2A3F_;Fk;Frho;").
Proof.
  intros rho k Hk. unfold spm, RA.spm, uval in *. rewrite U_add, U_lit. pose proof (U_range (eval rho (SVar 10))) as R. unfold M64v in *.
  set (x := bv_unsigned (eval rho (SVar 10))) in *.
  rewrite Zplus_mod_idemp_r. replace (x + - k) with (x - k) by lia. apply Z.mod_small. lia.
Qed.
Lemma basez_of : ltac2:(tb__ "0|0|
S12S33S13A1Sa8S13S1bR2A1R1A3S96R2A1S97R4A1F_;F_;FF;Frho;").
Proof.
  intros rho F HF (B1 & B1' & B2 & B3 & B4 & B5 & B6 & B7 & B8 & BT1 & BT2).
  pose proof (holds_mem _ _ _ HF B1) as H1. pose proof (holds_mem _ _ _ HF B1') as H1'. pose proof (holds_mem _ _ _ HF B2) as H2. pose proof (holds_mem _ _ _ HF B3) as H3.
  pose proof (holds_mem _ _ _ HF B4) as H4. pose proof (holds_mem _ _ _ HF B5) as H5. pose proof (holds_mem _ _ _ HF B6) as H6.
  pose proof (holds_mem _ _ _ HF B7) as H7. pose proof (holds_mem _ _ _ HF B8) as H8.
  pose proof (holds_mem _ _ _ HF BT1) as HT1. pose proof (holds_mem _ _ _ HF BT2) as HT2.
  zf H1. zf H1'. zf H2. zf H3. zf H4. zf H5. zf H6. zf H7. zf H8. zf HT1. zf HT2.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  assert (E30 : uval rho (SVar 30) = bv_unsigned (rw rho V_TOP)) by reflexivity. rewrite E30 in *.
  unfold aceil, two47, RA.two47, two48, B_EW, B32 in *.
  rewrite !uval_lit in H2, H3, H4, H5, H6, H7, H8, HT1, HT2 by lia.
  rewrite uval_spm in H1 by lia.
  assert (EW : uval rho (kbytes vW) = uval rho vE * uval rho vW) by (unfold kbytes; apply uval_mul_small; nia).
  assert (EK : uval rho (kbytes vK) = uval rho vE * uval rho vK) by (unfold kbytes; apply uval_mul_small; nia).
  constructor; unfold aceil, B_EW, B32; lia.
Qed.

Lemma robjs_r : ltac2:(tb__ "0|1|
S12S33S15A1M0S0G0R1S37S15S1eS19PaA1S16N40A1S16Z0A1S21S87S15S59R1A3A1S20A5S37S15S5aS4cS5cS46S4dA4S36S15A1A3A3A3S97R3A1S0S2fSe1Vrho0;A1S83Q40S1fR4Sc7A2A2A3S9dVFF;S3R5S58A2Z20A3Se7VCST;Vrho0;VFB;VFF;R6S36S34S11S11A2A1S36S34S34S11S2fA2S11A2A1R5A8F_;F_;F_;F_;FR;Frho;").
Proof.
  intros rho R -> BZ ET HV o a Ho Hr. cbn in Ho. destruct Ho as [<-|[<-|[]]].
  - left. apply range_lit' in Hr; [|lia|lia]. destruct BZ. lia.
  - unfold O_vec in Hr. apply range_lit' in Hr; [|lia|lia]. eapply (infrFF_pclMA CST rho0 FF); [exact HV | lia].
Qed.
Lemma xrs_r : ltac2:(tb__ "0|0|
S12S9dVFF;S3R1S58A2Z20A3S9dVFF;S3R2S4fA2Z30A3Se8VCST;VXGL;Vrho0;VFB;VFF;R3S36S34S11S11A2A1S36S34S34S11S2fA2S11A2A1S54A9F_;F_;Frho;").
Proof.
  intros rho HV HA r a Hr Ha. cbn in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in Ha; left.
  - rewrite uval_lit in Ha by lia. eapply (infrFF_pclMA CST rho0 FF); [exact HV | lia].
  - rewrite uval_lit in Ha by lia. eapply (infrFF_pclMA CST rho0 FF); [exact HA | lia].
Qed.

Lemma P0_now : ltac2:(tb__ "0|1|
S12Sd7S7eVrho0;R1A3S95VFB;VFF;Vrho0;A3S1S2S0S2fS3R3S46A2Z0M0A3A1S2S0S2fS3R4S4cA2G0A3A1F_;S1S9dVFF;S3R3S58A2Z20A3S9dVFF;S3R3S4fA2Z30A3A2A2F_;F_;Frho;").
Proof.
  intros rho Hav (A & B & C). unfold uval, vK, vDt, vV, vAl. cbn [eval].
  rewrite <- (proj1 Hav 17%positive eq_refl), <- (proj1 Hav 15%positive eq_refl), <- (proj1 Hav 12%positive eq_refl), <- (proj1 Hav 14%positive eq_refl).
  auto.
Qed.

Lemma HIN_r : ltac2:(tb__ "0|3|
S2aS33S15A1M0S12SccS0G0R3S37S15S1eS19PaA1S16N40A1S16Z0A1S21S87S15S59R3A3A1S20A5S37S15S5aS4cS5cS46S4dA4S36S15A1A3A3A3S96S14S2bR5A1A1A1S0S11SaaS4bR6A1PcA2S4fA3Sa8S13S1bR5A1S14S2bR7A1A1A3S95VFB;VFF;Vrho0;A3Sd7S7eVrho0;R7A3S1Se7VCST;Vrho0;VFB;VFF;R8S36S34S11S11A2A1M1S36S34S34S11S2fA2S11A2A1M2R9A8S1Se8VCST;VXGL;Vrho0;VFB;VFF;R8G1G2S54A9SafSe0VFB;R8G1A3Se9VFF;R8G2A3SacSabR8R9R7A3S4bRaA1A2A3A2A2F_;F_;F_;F_;F_;F_;Fms;Frho;FR;FE;").
Proof.
  intros E R rho ms HR HB Hs12 HF HP0 Hav. destruct (P0_now rho Hav HP0) as (_ & HV & HA).
  pose proof (basez_of rho _ HF HB) as BZ. pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET.
  split; [exact (robjs_r rho R HR BZ ET HV)|]. split; [exact (xrs_r rho HV HA)|].
  unfold RA.P0_ra. rewrite rw_call', Hs12. destruct HA as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl.
  split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin|]. unfold uval in H1, H2. lia.
Qed.

Lemma robjs_c : ltac2:(tb__ "0|2|
S12ScdS33S15A1M0S0G0R1S37S15S1eS19PaA1S16N40A1S16Z0M1A1S21S87S15S59R1A3A1S20A5S37S15S5aS4cS5cS46S4dA4S37S15S73S37S15S52S4cS48S46A1A2S36S15A1A3A3A3A3A3S97R4A1Se2R5ScfSceR4A1A1A2S0S2fS3R6S46A2G1A3S8fVFF;R6A2S9dVFF;S3R8S58A2Z20A3S9dVFF;S3R9S4fA2Z30A3SbbVCST;R9S3aS2fA1RaR8A5F_;F_;F_;F_;F_;F_;F_;FR;FAi;Frho;").
Proof.
  intros rho Ai R -> BZ HTK HK0 HFF HV HA o a Ho Hr. cbn in Ho. apply T_ok_rw in HTK. destruct Ho as [<-|[<-|[<-|[<-|[]]]]].
  - left. apply range_lit' in Hr; [|lia|lia]. destruct BZ. lia.
  - unfold O_vec in Hr. apply range_lit' in Hr; [|lia|lia]. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact HV | lia].
  - unfold O_alv in Hr. apply range_lit' in Hr; [|lia|lia]. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact HA | lia].
  - exfalso. destruct BZ as [_ _ _ _ _ [EK _] _]. apply range_data in Hr; [|rewrite EK, HK0; lia]. rewrite EK, HK0 in Hr. lia.
Qed.
Lemma xrs_c : ltac2:(tb__ "0|1|
S12ScdS33S34S11S11A2A1M0S0G0R1S69S4cS46A2A3S97R4A1S0S2fS3R5S46A2Z0A3S8fVFF;R5A2S9dVFF;S3R7S58A2Z20A3S9dVFF;S3R8S4fA2Z30A3SbcVCST;VXGL;R8S3aS2fA1R9R7A6F_;F_;F_;F_;F_;F_;FX;FAi;Frho;").
Proof.
  intros rho Ai X -> BZ HK0 HFF HV HA r a Hr Ha. cbn in Hr. destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Ha; left.
  - rewrite uval_lit in Ha by lia. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact HV | lia].
  - rewrite uval_lit in Ha by lia. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact HA | lia].
  - exfalso. destruct BZ as [_ _ _ _ _ [EK _] _]. rewrite EK, HK0 in Ha. lia.
Qed.

Lemma baseF_E_cW0' : ltac2:(tb__ "0|0|
S96S14S2bS51A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_E_c8' : ltac2:(tb__ "0|0|
S96S14S2bS50A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_E_r15f : ltac2:(tb__ "0|0|
S96S14S2bS60A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_E_rW1f : ltac2:(tb__ "0|0|
S96S14S2bS61A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_X15 : ltac2:(tb__ "0|0|
S96S14S2bS65A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_XW1 : ltac2:(tb__ "0|0|
S96S14S2bS68A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_XW0 : ltac2:(tb__ "0|0|
S96S14S2bS67A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_X8 : ltac2:(tb__ "0|0|
S96S14S2bS66A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma site_cW0 : ltac2:(tb__ "0|2|
S12Sb8VAInv;VCST;VXGL;S7eVrho0;S95VFB;VFF;A2VFB;VFF;S51S57S51A1M0S64R1S4aS3aS2fA1ScdSccS1S1S3eZ1S3R3Sb6G0A1A2M1A2S42G1S40Z2Z27A2A2A2S1S0S2fS3fS3R3SaaG0PcA2A2S3R3SaaG0PdA2A2A2G1A3Sc0S36SbfA1SbdSacSabR3S64R1A3G0A2A3A2A2Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HB HFF HN HD HZ HFR HM HT HTK. destruct (P0_now rho Hav HP0) as (_ & HV & HA).
  pose proof (basez_of rho _ HF baseF_E_cW0') as BZ.
  factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) HK0. rewrite uval_lit in HK0 by lia.
  factz HF (SPBranch BC_GEU vW (SLit 8)) HW8. rewrite uval_lit in HW8 by lia.
  split; [apply (robjs_c rho Ai); [reflexivity | exact BZ | exact HTK | exact HK0 | exact HFF | exact HV | exact HA]|].
  split; [apply (xrs_c rho Ai); [reflexivity | exact BZ | exact HK0 | exact HFF | exact HV | exact HA]|].
  change (csz (s_c E_cW0')) with (SMd M_MUL vW vE). change (wsub_get (s_c E_cW0') 12) with vW. change (wsub_get (s_c E_cW0') 13) with vE.
  destruct BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK] Btop]. rewrite uval_mul_comm. fold (kbytes vW). rewrite EW. unfold B_EW in BEW.
  split; [nia|]. split; [lia | exact I].
Qed.
Lemma site_c8 : ltac2:(tb__ "0|2|
S12Sb8VAInv;VCST;VXGL;S7eVrho0;S95VFB;VFF;A2VFB;VFF;S50S57S50A1M0S63R1S4aS3aS2fA1ScdSccS1S1S3eZ1S3R3Sb6G0A1A2M1A2S42G1S40Z2Z27A2A2A2S1S0S2fS3fS3R3SaaG0PcA2A2S3R3SaaG0PdA2A2A2G1A3Sc0S36SbfA1SbdSacSabR3S63R1A3G0A2A3A2A2Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HB HFF HN HD HZ HFR HM HT HTK. destruct (P0_now rho Hav HP0) as (_ & HV & HA).
  pose proof (basez_of rho _ HF baseF_E_c8') as BZ.
  factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) HK0. rewrite uval_lit in HK0 by lia.
  split; [apply (robjs_c rho Ai); [reflexivity | exact BZ | exact HTK | exact HK0 | exact HFF | exact HV | exact HA]|].
  split; [apply (xrs_c rho Ai); [reflexivity | exact BZ | exact HK0 | exact HFF | exact HV | exact HA]|].
  change (csz (s_c E_c8')) with (SMd M_MUL (SLit 8) vE). change (wsub_get (s_c E_c8') 12) with (SLit 8). change (wsub_get (s_c E_c8') 13) with vE.
  destruct BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK] Btop]. rewrite uval_mul_lit by lia. rewrite uval_lit by lia.
  split; [lia|]. split; [lia | exact I].
Qed.

Definition s_rbd (kn : sv) : list bitem := ltac2:(tb__ "0|2|
S38S6S37S6ScZ1M0Z0M1S48Vkn;A1A3S37S6SbG1S3fZ2S5A2G0A3S36S6A1A3A3S49S47Vkn;A2A3").

Lemma sums_bdP : ltac2:(tb__ "0|1|
S12S11S11S1S0S2fS9S49R2R1A2M0R3A2S41S43S3fZ6S3R3S48R2A1A2A2S3fZ4S3R3S48R1A1A2A2A2S3fZ20S3R3S4dA2A2A2A3S0S2fS8G0R3A2S3fS3fZ2S5A2S43SeS4S3R3R1A2A1A2A2A3A2Fk;Fw;Frho;").
Proof. intros. unfold bdP, PHI, KLG. cbn [bsumV bsumK]. unfold BudA.bival. cbn [lfval aval bi_v bi_k bi_f bi_c]. split; lia. Qed.
Lemma sums_s_rbd : ltac2:(tb__ "0|2|
S12S11S1S0S2fS9S98R1A1M0R2A2S41S3R2S48R1A1A2S9S49S47R1A2M1R2A2A2A3S0S2fS8G0R2A2S41S3fZ2S5A2S8G1R2A2A2A3A2Fkn;Frho;").
Proof. intros. unfold s_rbd, BIs, BIc. cbn [bsumV bsumK app]. unfold BudA.bival. cbn [lfval aval bi_v bi_k bi_f bi_c]. split; lia. Qed.
Lemma bd_nn_bdP : ltac2:(tb__ "0|1|
S12S11S11S3eS3fZ4S3R3S48R1A1A2A2S41S3fZ6S3R3S48R2A1A2A2S3fZ20M0S3R3S4dA2A2A2A2S3eS3R4R2A2S40Z2G0A2A2S7S49R4R3A2R5A2F_;F_;Fk;Fw;Frho;").
Proof.
  intros rho w k H1 H2. unfold bd_nn, bdP, PHI, KLG. repeat constructor; unfold BudA.bival; cbn [lfval aval bi_f bi_c]; [lia|].
  pose proof (zlog15_ZK _ H2). lia.
Qed.
Lemma bd_nn_s_rbd : ltac2:(tb__ "0|0|
S12S11S7S49S47R1A2R2A2S7S98R2A1R3A2F_;Fkn;Frho;").
Proof.
  intros rho kn H. unfold s_rbd. apply bd_nn_app. split; [|exact H]. unfold bd_nn, BIs, BIc. repeat constructor; unfold BudA.bival; cbn [lfval aval bi_f bi_c].
  - pose proof (uval_range rho (kbytes kn)). lia.
  - lia.
Qed.

Record injz (rho : valuation) (kn : sv) : Prop := IJ {
  ij_b : 4 * uval rho (kbytes vK) <= 3 * uval rho (kbytes kn);
  ij_a : 4 * uval rho (kbytes kn) <= 6 * uval rho (kbytes vW) + 32 * uval rho vE;
  ij_c : 1 <= uval rho (kbytes kn) <= B32;
  ij_e : uval rho (kbytes kn) = uval rho vE * uval rho kn }.
Definition injF (kn : sv) (F : list sprop) : Prop := ltac2:(tb__ "0|0|
S0S31S86S13S13S84S13S17R1A1VF;A3Lf;S55Vkn;A1A3S32A3").
Lemma injz_of : ltac2:(tb__ "0|0|
S12S11S33S13A1Sa8S13S1bR3A1R1A3S97R4A1S9bR4R3A2S3eS3R6R5A2S40Z2Z31A2A2S9cR7R6A2F_;F_;F_;F_;FF;Fkn;Frho;").
Proof.
  intros rho kn F HF BZ H Hkn. unfold injF, inj in H. cbn [forallb] in H.
  apply andb_prop in H as [H1 H]. apply andb_prop in H as [H2 H]. apply andb_prop in H as [H3 H]. apply andb_prop in H as [H4 _].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3. pose proof (holds_mem _ _ _ HF H4) as F4.
  zf F1. zf F2. zf F3. zf F4. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  destruct BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK] Btop]. unfold B_EW, B32 in *.
  pose proof (uval_range rho kn) as Rkn.
  assert (EKn : uval rho (kbytes kn) = uval rho vE * uval rho kn) by (unfold kbytes; apply uval_mul_small; nia).
  rewrite !uval_lit in F3, F4 by lia.
  rewrite !uval_mul_lit in F1 by (rewrite ?EKn; lia). rewrite uval_add_small in F2 by (rewrite !uval_mul_lit by lia; lia).
  rewrite !uval_mul_lit in F2 by lia.
  constructor; unfold B32; lia.
Qed.

Lemma grow15 : ltac2:(tb__ "0|0|
S12S97R1A1S2S0S2fS3R2S46A2Z0A3A1S42S3R3S46A2S3R3S47A2A2S42S3R4S47A2S3R4S56A2A2S3eS41S4S3R5S46A2A1Z1A2S4S3R5S56A2A1A2F_;F_;F_;F_;Frho;").
Proof.
  intros rho BZ H0 H1 H2. destruct BZ as [Bsp Be Bw Bk _ _ _]. pose proof (uval_kn15 rho Bk) as E. rewrite E in H2 |- *.
  pose proof (uval_range rho vK). pose proof (zlog15_grow (uval rho vK) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma growW1 : ltac2:(tb__ "0|0|
S12S97R1A1S2S0S2fS3R2S46A2Z0A3A1S42S3R3S46A2S3R3S47A2A2S3eS3R4S56A2S3R4S47A2A2S3eS41S4S3R5S46A2A1Z1A2S4S3R5S47A2A1A2F_;F_;F_;F_;Frho;").
Proof.
  intros rho BZ H0 H1 H2. destruct BZ as [Bsp Be Bw Bk _ _ _]. pose proof (uval_kn15 rho Bk) as E. rewrite E in H2.
  pose proof (uval_range rho vK).
  destruct (Z_lt_ge_dec (uval rho vK) 2).
  - assert (E1 : uval rho vK = 1) by lia. rewrite E1, zlog15_1. pose proof (zlog15_ge1 (uval rho vW) ltac:(lia)). lia.
  - pose proof (zlog15_grow (uval rho vK) ltac:(lia) ltac:(lia)). pose proof (zlog15_mono (uval rho vK + uval rho vK / 2) (uval rho vW) ltac:(lia)). lia.
Qed.
Lemma grow0 : ltac2:(tb__ "0|0|
S12S11S0S2fS3R2S46A2Z0A3S3eZ8S3R3R2A2A2S3eS41S4S3R4S46A2A1Z1A2S4S3R4R3A2A1A2F_;F_;Fkn;Frho;").
Proof. intros rho kn -> H. rewrite zlog15_0. pose proof (zlog15_ge1 (uval rho kn) ltac:(lia)). lia. Qed.

Lemma pay_r : ltac2:(tb__ "0|3|
S2aS11S96S14S2bR2A1A1A1S9bR2S14S2bR3A1A1A2S12Sa8S13S1bR1A1S14S2bR5A1A1M0A3S97R2A1S1S3eS3R3R6A2M1S40Z2Z31A2A2S3eS41S4S3R3S46A2A1Z1A2S4G1A1A2A2F_;F_;Frho;Sb7S7eVrho0;S95VFB;VFF;A2G0S16Z0M2A1G2S49S47S46A2S98R4A1A8F_;F_;F_;Fkn;FE;").
Proof.
  intros E kn HB HI HG. split; [reflexivity|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem.
  pose proof (basez_of rho _ HF HB) as BZ. destruct (HG rho HF BZ) as [Hkn HL]. pose proof (injz_of rho kn _ HF BZ HI Hkn) as [I1 I2 I3 I4].
  destruct BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK] Btop]. unfold B32 in I3.
  assert (NN : bd_nn (bdP vW kn) rho) by (apply bd_nn_bdP; nia).
  split; [|split; [|apply bd_nn_s_rbd; exact NN]].
  - rewrite uval_lit by lia. destruct (sums_s_rbd rho kn) as [-> _]. destruct (sums_bdP rho vW kn) as [-> _]. destruct (sums_bdP rho vW vK) as [-> _]. lia.
  - destruct (sums_s_rbd rho kn) as [_ ->]. destruct (sums_bdP rho vW kn) as [_ ->]. destruct (sums_bdP rho vW vK) as [_ ->]. unfold KU. nia.
Qed.
Lemma pay_r15 : ltac2:(tb__ "0|1|
Sb7S7eVrho0;S95VFB;VFF;A2S14S2bS60A1A1S16Z0M0A1G0S49S47S46A2S98S56A1A8").
Proof.
  apply pay_r; [exact baseF_E_r15f | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros rho HF BZ.
  factz HF (SPBranch BC_NE vK (SLit 0)) HK0. factz HF (SPNot (SPBranch BC_GEU vK vW)) HKW. factz HF (SPBranch BC_LTU vW kn15) HWn.
  rewrite uval_lit in HK0 by lia.
  split; [| exact (grow15 rho BZ HK0 HKW HWn)].
  destruct BZ as [Bsp Be Bw Bk _ _ _]. rewrite (uval_kn15 rho Bk). pose proof (uval_range rho vK). lia.
Qed.
Lemma pay_rW1 : ltac2:(tb__ "0|1|
Sb7S7eVrho0;S95VFB;VFF;A2S14S2bS61A1A1S16Z0M0A1G0S49S47S46A2S98S47A1A8").
Proof.
  apply pay_r; [exact baseF_E_rW1f | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros rho HF BZ.
  factz HF (SPBranch BC_NE vK (SLit 0)) HK0. factz HF (SPNot (SPBranch BC_GEU vK vW)) HKW. factz HF (SPNot (SPBranch BC_LTU vW kn15)) HWn.
  rewrite uval_lit in HK0 by lia.
  split; [| exact (growW1 rho BZ HK0 HKW HWn)]. destruct BZ; lia.
Qed.

Lemma pay_c : ltac2:(tb__ "0|2|
S2aS11S11S96S14S2bR3A1A1A1S9bR3S14S2bR4A1A1A2S12Sa8S13S1bR1A1S14S2bR6A1A1M0A3S97R2A1S1S3eS3R3R7A2M1S40Z2Z31A2A2S1S0S2fS3R3S46A2Z0A3S1S3eZ8G1A2S0S2fS3R3R6A2S3R3S48R7A1A2A3A2A2A2F_;F_;Frho;Sb7S7eVrho0;S95VFB;VFF;A2G0R4S5S49S47S46A2S49S47R5A2A8F_;F_;F_;Fcst;Fkn;FE;").
Proof.
  intros E kn cst HB HI HG. split; [reflexivity|]. split; [unfold KU; lia|]. intros rho HF _ _ Hn. unfold pay_sem.
  pose proof (basez_of rho _ HF HB) as BZ. destruct (HG rho HF BZ) as (Hkn & HK0 & H8 & ->). pose proof (injz_of rho kn _ HF BZ HI Hkn) as [I1 I2 I3 I4].
  pose proof (grow0 rho kn HK0 H8) as HL.
  destruct BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK] Btop]. unfold B32 in I3.
  assert (NN : bd_nn (bdP vW kn) rho) by (apply bd_nn_bdP; nia).
  split; [|split; [|exact NN]].
  - destruct (sums_bdP rho vW kn) as [-> _]. destruct (sums_bdP rho vW vK) as [-> _]. rewrite EK, HK0. lia.
  - destruct (sums_bdP rho vW kn) as [_ ->]. destruct (sums_bdP rho vW vK) as [_ ->]. unfold KU. nia.
Qed.
Lemma pay_cW0 : ltac2:(tb__ "0|0|
Sb7S7eVrho0;S95VFB;VFF;A2S14S2bS51A1A1Sb6S57S51A1A1S5S49S47S46A2S49S47S47A2A8").
Proof.
  apply pay_c; [exact baseF_E_cW0' | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros rho HF BZ.
  factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) HK0. factz HF (SPBranch BC_GEU vW (SLit 8)) HW8.
  rewrite uval_lit in HK0 by lia. rewrite uval_lit in HW8 by lia.
  change (csz (s_c E_cW0')) with (SMd M_MUL vW vE). rewrite uval_mul_comm. fold (kbytes vW).
  destruct BZ; repeat split; lia.
Qed.
Lemma pay_c8 : ltac2:(tb__ "0|0|
Sb7S7eVrho0;S95VFB;VFF;A2S14S2bS50A1A1Sb6S57S50A1A1S5S49S47S46A2S49S47S16Z8A1A2A8").
Proof.
  apply pay_c; [exact baseF_E_c8' | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros rho HF BZ.
  factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) HK0. rewrite uval_lit in HK0 by lia.
  change (csz (s_c E_c8')) with (SMd M_MUL (SLit 8) vE). rewrite uval_mul_comm. fold (kbytes (SLit 8)).
  rewrite uval_lit by lia. destruct BZ; repeat split; lia.
Qed.

Lemma inj_holds : ltac2:(tb__ "0|4|
S12S11S97R2A1S3eS3R3R2A2S40Z2Z31A2A2S3eS3fZ4M0S3fS3R4S4dA2M1S3R4S46A2A2A2S3fZ3S3fG1S3R4R3A2A2A2A2S3eS3fG0S3fS3R5S4dA2M2S3R5R4A2A2A2S41S3fZ6S3fG2S3R5S47A2A2A2S3fZ20G2A2A2A2S1S3eZ1S3fS3R6S4dA2S3R6R5A2A2M3A2S3eG3S5dA2A2Sa8S13S1bR7A1S55R6A1A3F_;F_;F_;F_;F_;Fkn;Frho;").
Proof.
  intros rho kn BZ Hkn H1 H2 H3. destruct BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK] Btop]. unfold B_EW, B32 in *.
  assert (Hkn32 : uval rho kn <= 4294967295) by nia.
  pose proof (uval_range rho kn).
  assert (EKn : uval rho (kbytes kn) = uval rho vE * uval rho kn) by (unfold kbytes; apply uval_mul_small; nia).
  unfold inj, B32. repeat constructor; apply (proj2 (holds_ule _ _ _)); repeat change (bv_unsigned (eval ?r ?e)) with (uval r e).
  - rewrite !uval_mul_lit by (rewrite ?EK, ?EKn; lia). rewrite EK, EKn. lia.
  - rewrite uval_add_small by (rewrite !uval_mul_lit by (rewrite ?EW; lia); rewrite EW; lia).
    rewrite !uval_mul_lit by (rewrite ?EW, ?EKn; lia). rewrite EW, EKn. lia.
  - rewrite uval_lit by lia. rewrite EKn. lia.
  - rewrite uval_lit by lia. rewrite EKn. lia.
  - rewrite uval_lit by lia. exact Hkn32.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S2fS33S82Q40A1A1S9eF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S80S2aS12S33S82Q40A1A1S9eSa8S13S1bR3A1S14S2bR4A1A1A3VTR;S7fS45R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S9eS9eS9eS9fR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_false : ltac2:(tb__ "0|0|
S9eS9eS9fS2R3R1A1A1Fw;VTR;R3R2A2F_;FQ;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S80S80S2aS2aSadS33S15A1M0S33S34S2aSa2A2M1A1S33S34S11S11A2M2A1S9eS12S33S82Q40A1A1M3G2S85G2R1R5A3S85G2R2S2cRbA1A3F_;Fr;S0S3bG0A1Sa5RaR9R8A3S39G0R7A2A3S0S31Sa4RbRaR9R8Sa9G1S2aS3cS2aSa2A2R7A4A5S32A3S12G3VTR;S7fS45RfRdR2R1A5Sa3S45S18S2bRdA1A1R2R1RaA5A2Ftp1;Frho1;S33Sd4A1M4SccSd3S81S45R9R8R10S35G4Sd5R3Sd6R2R1A2A4A5R13RaR9R4R2A4R13SacSabRbRfSd0R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S2aSa2G4SccSd3S12G3G4SccSd3S85G1S35S2aSa2RaR9A4R14A3S81S45R12R11R19S35G4Sd5R9Sd6R8R7A2A4A5R1cR13R12RaR8A4Sd7S18S2bR1aA1A1SacSabR14R18Sd0R9R13RaA3A3R19A2R8A3S81S45R9R8ReS35G4Sd5R7Sd6R6R5A2A4A5ReSacSabR16R1aSd0RbR15RcA3A3R1bA2R15RaR9R8R6A6S1Sf2R17Sd0RcR16RdA3R1bR1cR1dR10R1eR19RbA9S12Sd9R18Sd0RdR17ReA3R1cR1dS2bR1eA1S2bR1fA1S2bR11A1R1RcA9VTR;S7fS45Sa7R11SacSabR19R1dSd0ReR18RfA3A3R1eA2R18RdRcA5Sf3R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S7fS45R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CCALLOC : ltac2:(tb__ "0|1|
ScdS12S33S82Q40A1A1VTR;S7fS45Sc1VAInv;S36SbfA1M0SbdR3VKc;ScbA6Sc5SbeG0SbdA3R2R1A5Sa3S45S7eR2R1Sc4SbeVAInv;VCST;VXGL;G0SbdR3VKc;A8A5A2Ftp1;Frho1;FAi;").
Hypothesis CREALLOC : ltac2:(tb__ "0|1|
S33S34S2fS2fA2M0A1S33S34G0S2fA2A1S10S12S33S82Q40A1A1SdZ2R3A2VTR;S7fS45S8cVAInv;VCST;VXGL;VKc;SafR6R5A2R6R5R4S8aSb4Sb0Sb3A2AaSaeR3R2A5Sa3S45S7eR3R2SeaVAInv;VCST;VXGL;VKc;SafS8aS5eR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Hypothesis REENTER : ltac2:(tb__ "0|4|
S2aS89S34S2fS11A2M0S12S33S82Q40A1A1M1S2fG1S85S34S34S2aS89A2M2G0A2S35G2G0S35S2aS89R7R6A4R5A4S4eA3S1S3eZ0S8eS35G2G0S35S2aS89R8R7A4R6A4R5A2M3A2S42G3R3A2A2VTR;S7fS45VJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S2aS89S12S33S82Q40A1A1M0S2fG0S85S34S2aSa2A2S35S2aSa2R6S99R5A1A4S9aA3VTR;S7fS45VJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd z0 eval]; rewrite lit_unsigned; cbn; lia.
Tactic Notation "innth" integer(n) := cbn [In cutsE exitsE Posts_vr PD_ra]; do n right; left; reflexivity.

Lemma X_N : ltac2:(tb__ "0|4|
S2aS2aS11S2fS12S33S82Q40A1A1M0S2fG0S0S2aSddR8S38S13S55R6A1S14S2bR8A1A1A3A2R7A3S85S34S34S2aS89A2M1S34S2fS11A2M2A2S35G1G2S35S2aS89R8S4aA4S35S2fS11R6S5fA4A4S4eA3S3eS3fS41R7Z1A2S40Z2Z40A2A2R4A2S3eZ0R8A2S0S31S86S13S22S18S2bRcA1M3A1A1S38S13S55RaA1S14G3A1A3A3S32A3S12Sa8S13S1bR1A1S14S2bReA1A1A3Sa8S13S1bR2A1S55RdA1A3F_;Frho;VTR;S7fS45VJAv;S4aA1ReRaR9A5VFAM;R8R7A2A2F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fr;Fkn;FNs;FXs;").
Proof.
  intros Xs Ns kn r rho tp b tp0 HN Hin Hb Hr Hbelow Hinj.
  eapply TR_pre; [|apply (REENTER Ns nd0 (r, z0)); [exact Hin | meas]].
  intros w Hw. rewrite <- HN. apply (SPA_refacts_JA segs); [exact Hw | exact Hbelow |].
  intros tr md _ HF. apply Forall_app. split; [exact (Hinj _ HF) | exact HF].
Qed.

Lemma X_X15 : ltac2:(tb__ "0|1|
S12S33S82Q40A1A1M0S2fG0S3eS3fZ5aS40Z2Z40A2A2R2A2VTR;S7fS45VJAv;S4aA1S65R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_N X15 N15 kn15 80 rho tp b tp0 N15_eq); [innth 1 | lia | lia | reflexivity |].
  intros r HF. pose proof (basez_of r _ HF baseF_X15) as BZ.
  factz HF (SPBranch BC_NE vK (SLit 0)) HK0. factz HF (SPNot (SPBranch BC_GEU vK vW)) HKW. factz HF (SPBranch BC_LTU vW kn15) HWn.
  rewrite uval_lit in HK0 by lia. pose proof BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK]]. unfold B_EW, B32 in *.
  rewrite (uval_kn15 r Bk) in HWn. pose proof (uval_range r vK).
  pose proof (Z.div_mod (uval r vK) 2 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (uval r vK) 2 ltac:(lia)) as MB.
  apply (inj_holds r kn15 BZ); rewrite ?(uval_kn15 r Bk); unfold B32; try nia.
Qed.
Lemma X_XW1 : ltac2:(tb__ "0|1|
S12S33S82Q40A1A1M0S2fG0S3eS3fZ5aS40Z2Z40A2A2R2A2VTR;S7fS45VJAv;S4aA1S68R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_N XW1 NW1 vW 80 rho tp b tp0 NW1_eq); [innth 2 | lia | lia | reflexivity |].
  intros r HF. pose proof (basez_of r _ HF baseF_XW1) as BZ.
  factz HF (SPBranch BC_NE vK (SLit 0)) HK0. factz HF (SPNot (SPBranch BC_GEU vK vW)) HKW. factz HF (SPNot (SPBranch BC_LTU vW kn15)) HWn.
  rewrite uval_lit in HK0 by lia. pose proof BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK]]. unfold B_EW, B32 in *.
  rewrite (uval_kn15 r Bk) in HWn. pose proof (uval_range r vK).
  pose proof (Z.div_mod (uval r vK) 2 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (uval r vK) 2 ltac:(lia)) as MB.
  apply (inj_holds r vW BZ); unfold B32; try nia.
Qed.
Lemma X_XW0 : ltac2:(tb__ "0|1|
S12S33S82Q40A1A1M0S2fG0S3eS3fZ5aS40Z2Z40A2A2R2A2VTR;S7fS45VJAv;S4aA1S67R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_N XW0 NW0 vW 80 rho tp b tp0 NW0_eq); [innth 3 | lia | lia | reflexivity |].
  intros r HF. pose proof (basez_of r _ HF baseF_XW0) as BZ.
  factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) HK0. factz HF (SPBranch BC_GEU vW (SLit 8)) HW8.
  rewrite uval_lit in HK0 by lia. rewrite uval_lit in HW8 by lia. pose proof BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK]]. unfold B_EW, B32 in *.
  apply (inj_holds r vW BZ); unfold B32; try nia.
Qed.
Lemma X_X8 : ltac2:(tb__ "0|1|
S12S33S82Q40A1A1M0S2fG0S3eS3fZ5aS40Z2Z40A2A2R2A2VTR;S7fS45VJAv;S4aA1S66R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_N X8 N8 (SLit 8) 80 rho tp b tp0 N8_eq); [innth 4 | lia | lia | reflexivity |].
  intros r HF. pose proof (basez_of r _ HF baseF_X8) as BZ.
  factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) HK0. factz HF (SPNot (SPBranch BC_GEU vW (SLit 8))) HW8.
  rewrite uval_lit in HK0 by lia. rewrite uval_lit in HW8 by lia. pose proof BZ as [Bsp Be Bw Bk [EW BEW] [EK BEK]]. unfold B_EW, B32 in *.
  pose proof (uval_range r vW).
  apply (inj_holds r (SLit 8) BZ); rewrite ?uval_lit by lia; unfold B32; try nia.
Qed.

Lemma C_calloc_contra : ltac2:(tb__ "0|1|
S2aS12S33S82Q40A1A1S9eS0S31S84S13S17S1cSd2S46S16Z0A1M0A3A1S14S2bR4A1A1A3S32A3S0S31S84S13S17S1cSd1S4cG0A3A1S14S2bR5A1A1A3S32A3VTR;S7fS45VJAv;S4aA1R6R5R4A5R3A2F_;F_;FQx;Ftp;Frho;FC;").
Proof.
  intros C rho tp Qx H1 H2. apply TR_facts. intros HF. apply TR_false. intros w [_ (Ai & kc & HJ)].
  pose proof HJ as (Hav & _ & _ & _ & _ & _ & _ & _ & _ & HP0 & _).
  destruct (P0_now rho Hav HP0) as (HKD & _ & _).
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. zf F1. zf F2.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. rewrite uval_lit in F1, F2 by lia. exact (HKD F1 F2).
Qed.
Lemma C_realloc_contra : ltac2:(tb__ "0|1|
S2aS12S33S82Q40A1A1S9eS0S31S84S13S17S1dS1cSd2S46S16Z0A1M0A3A1A1S14S2bR4A1A1A3S32A3S0S31S84S13S17S1dS1cSd1S4cG0A3A1A1S14S2bR5A1A1A3S32A3S96S14S2bR6A1A1A1VTR;S7fS45VJAv;S4aA1R7R6R5A5R4A2F_;F_;F_;FQx;Ftp;Frho;FC;").
Proof.
  intros C rho tp Qx H1 H2 HB. apply TR_facts. intros HF. apply TR_false. intros w [_ (Ai & kc & HJ)].
  pose proof HJ as (Hav & _ & _ & _ & _ & _ & (HN & _ & _) & _).
  pose proof (basez_of rho _ HF HB) as [_ _ _ _ _ [EK _] _].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2.
  pose proof (tnz_of_fact rho vDt (kbytes vK) F2) as Hnz. zf F1.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. rewrite uval_lit in F1 by lia.
  cbn [nd_tv nd0] in HN. destruct (proj1 (Forall_forall _ _) HN (vDt, kbytes vK) ltac:(left; reflexivity) Hnz) as (Hpos & _).
  unfold tvv in Hpos. cbn [snd] in Hpos. change (bv_unsigned (eval rho (kbytes vK))) with (uval rho (kbytes vK)) in Hpos.
  rewrite EK, F1 in Hpos. lia.
Qed.

Lemma X_E_r : ltac2:(tb__ "0|10|
S2aS2aS2aS2aS2aS2aS2aS2aS33S15A1M0S11S30S12S33S82Q40A1A1M1S2fG1S0S3bS2aA1M2Se4RfS7dA2S39S2aReA2A3S0S2aSddRfS38S13S6dS14S2bRfA1A1A3A2ReA3S0S31S84S13S17S1dS1cSd1S4cS16Z0M3A1M4A3A1A1S14S2bR10A1A1A3S32A3S0G0RaS37S15S1eS19PaA1S16N40A1G4S21S87S15S59RaA3A1S20A5S37S15S5aS4cS5cS46S4dA4S36S15A1A3A3A3S96S14S2bR11A1A1A1S0S11SaaS4bR12A1PcA2S4fA3S0S31SedS54S2cR13A1A2S32A3S0S3bG0A1Sa5R14SaeS4bR14A1A3S39G0ReA2A3S0S31Sa4R15SaeS4bR15A1RfSa9S34S2aS89A2M5S2aS3cS2aS89A2S5eA4A5S32A3S0S31SbaS7eS4bR16A1A2S32A3S0S31SdaS4bR17A1S7eA2S32A3S0S31Sf0S7eS18S2bR18A1A1A2S32A3S0S31S90S18S2bR19A1A1S8dS38S34S11S11A2M6S36G6A1M7S5bA3S36S34S34S11S2fA2S11A2A1S49S47S46A2M8A3A2S32A3S0S31SaS18S2bR1aA1A1S49S47R13A2A2S32A3S0S31Se3S4bR1bA1S5bSb0A3S32A3Sb7S7eVrho0;S95VFB;VFF;A2S14S2bR1cA1A1G4G3G8S38S6SfS4bR1cA1Sb3A2S49S47R15A2A3A8S0S31S86SecSebSaeS7eS4bR1dA1S18S2bR1dA1A1A4S5eA3S32A3S0S2aSe6SaeR1eS4bR1eA1R18Sb1S54A6R1dA3S0G2Se4R1eS7cA2S39S2aR1dA2A3M9S0S2aSe6SaeR20S4bR20A1R1aSb2S54A6R1dA3G9S0S2aSdbS8bS35S11S11S19R1aA1S48R1bA1A4A1R1eA2R1dA3S0S33G6A1MaSdfSa6S4bR23A1SaeSb2R23A4Sb5A2S37G6S35S11S11S19R1bA1S48R1cA1A4G7A3A3S0GaSdfSa6S4bR24A1SaeSb1R24A4Sb0A2S5bA3S0S31S84S13S17S1dS1cSd1S19R1dA1G4A3A1A1S14S2bR21A1A1A3S32A3S0S31S86S13S22S18S2bR22A1MbA1A1S38S13S8bS35S11S11S19R1eA1S48R1fA1A4A1S14GbA1A3A3S32A3S0S31S86S13S22S18S2bR28A1McA1A1S38S13S6dS14GcA1A3A3S32A3S85S34G5S34S2fS11A2MdA2MeS35G5GdS35S2aS89R26S6bR21A1A4S35S2fS11Z3cS5fA4MfA4S4eA3S85GeS35G5GdS35S2aS89R24S6aS19R21A1R22A2A4GfA4S4eA3S3eS3fZ46S40Z2Z40A2A2R1fA2VTR;S7fS45VJAv;S4aA1R2dR22R21A5VFAM;R20R1fA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FpN;Fkn;FR;FTok;FTokB;FTok0;FTf;FTf0;FEf;FEx;FE;").
Proof.
  intros E Ex Ef Tf0 Tf Tok0 TokB Tok R kn pN rho tp b tp0 HEx HEf HD HR HB Hs12 HXk He Hchk Htp Hdom Hnf Hnb Hbr Hpass HPAY Hpd HTf0 HTf HTok0 HTokB HTok Htvok Htvf HpN Hbelow HbelowE HinF HinOK Hb.

  eapply TR_pre with (P := SPA segs (JAv nd0) Ef rho tp).
  { intros w Hw. pose proof (SPA_axforms segs _ xf_rcall rho E Ex tp w HEx Hw) as Hw1.
    rewrite <- HEf. apply (SPA_refacts_JA segs); [exact Hw1 | exact HbelowE | ].
    intros tr md HJ HF. apply Forall_app. split; [|exact HF].
    eapply (JA_tv_facts segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue ALA); [ | exact HJ | left; reflexivity |]; [reflexivity|].
    apply tnz_of_fact. exact (holds_mem _ _ _ HF HD). }
  apply TR_facts. intros HF.
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue HKc HBX RA.P0_ra PTrue (fun _ H => H) (fun _ _ _ H => H) RA.Pre_ra (RA.ndR RA.tv0 RA.bd0) PD_ra NF
           eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CREALLOC eq_refl
           Ef (s_r Ef) R Xk_r rho tp [] tv0 [] (bdP vW vK) (bdP vW kn) ANone (FAM b tp0) HXk He Hchk Htp Hdom Hnf Hnb Hbr Hpass eq_refl HPAY Hpd).
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD' HZ HFR HM HT HTK. apply (HIN_r Ef R rho ms HR HB Hs12 HF' HP0 Hav).
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_ra In] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <-; cbn [fst snd nd_tv nd_bd nd_am RA.ndR ND am_subst app].
    + rewrite HTf0, Htvf. change (bd_subst _ []) with (@nil bitem). cbn [app].
      eapply TR_pre; [|apply (REENTER Tf (ndN kn) (60, z0)); [exact HinF | meas]].
      intros w Hw. exact (SPA_axforms segs _ xf_rback rho' Tf0 Tf tp' w HTf Hw).
    + rewrite HTok0, Htvok. change (bd_subst _ []) with (@nil bitem). cbn [app].
      eapply TR_pre; [|apply (REENTER Tok (ndG (SVar pN) kn) (60, z0)); [exact HinOK | meas]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_rback rho' Tok0 TokB tp' w HTokB Hw) as Hw1.
      rewrite <- HTok. unfold ax_add_facts.
      change (ax_setS TokB (add_facts (tv_factsA (SVar pN, kbytes kn)) (ax_S TokB))) with (ax_with_facts TokB (tv_factsA (SVar pN, kbytes kn) ++ ss_facts (ax_S TokB))).
      apply (SPA_refacts_JA segs); [exact Hw1 | exact Hbelow |].
      intros tr md HJ HF2. apply Forall_app. split; [|exact HF2].
      eapply (JA_tv_facts segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue ALA); [ | exact HJ | left; reflexivity |]; [reflexivity|].
      apply tnz_of_fact. exact (holds_mem _ _ _ HF2 HpN).
Qed.
Lemma X_E_r15 : ltac2:(tb__ "0|1|
S12S33S82Q40A1A1M0S2fG0S3eS3fZ46S40Z2Z40A2A2R2A2VTR;S7fS45VJAv;S4aA1S71R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_E_r E_r15 E_r15x E_r15f T_r15f0 T_r15f T_r15ok0 T_r15okB T_r15ok R_r15 kn15 141%positive rho tp b tp0 E_r15x_eq E_r15f_eq).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact baseF_E_r15f.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - pose proof pay_r15 as P. unfold s_rbd in P. match goal with |- payA _ _ _ _ _ _ _ ?x => replace x with ([BIs 1 0 (kbytes kn15); BIc 0 (2 * KU) 1] ++ bdP vW kn15) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) end. exact P.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact T_r15f0_eq.
  - exact T_r15f_eq.
  - exact T_r15ok0_eq.
  - exact T_r15okB_eq.
  - exact T_r15ok_eq.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - innth 5.
  - innth 6.
  - exact Hb.
Qed.
Lemma X_E_rW1 : ltac2:(tb__ "0|1|
S12S33S82Q40A1A1M0S2fG0S3eS3fZ46S40Z2Z40A2A2R2A2VTR;S7fS45VJAv;S4aA1S72R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_E_r E_rW1 E_rW1x E_rW1f T_rW1f0 T_rW1f T_rW1ok0 T_rW1okB T_rW1ok R_rW1 vW 141%positive rho tp b tp0 E_rW1x_eq E_rW1f_eq).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact baseF_E_rW1f.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - pose proof pay_rW1 as P. unfold s_rbd in P. match goal with |- payA _ _ _ _ _ _ _ ?x => replace x with ([BIs 1 0 (kbytes vW); BIc 0 (2 * KU) 1] ++ bdP vW vW) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) end. exact P.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact T_rW1f0_eq.
  - exact T_rW1f_eq.
  - exact T_rW1ok0_eq.
  - exact T_rW1okB_eq.
  - exact T_rW1ok_eq.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - innth 7.
  - innth 8.
  - exact Hb.
Qed.

Lemma X_E_c : ltac2:(tb__ "0|19|
S2aS2aS2aS2aS2aSadS33S15A1M0S11S11S12S33S82Q40A1M1A1M2S2fG2S0SadR8S57RdA1A3S0S3bG0A1Sa5ReS53R9A3S39G0R8A2A3S0S31Sa4RfS53RaR9S37S2aSc2SbeS36SbfA1M3SbdA3M4S37S2aSc3SbeG3SbdA3M5S36S2aA1A3A3A5S32A3S0S31SbaS7eRbA2S32A3S0S31Sf0S7eS18S2bR11A1A1A2S32A3S0S31S90S18S2bR12A1A1S4aA2S32A3S0S31SaS18S2bR13A1A1S49S47RcA2A2S32A3S0S31S29S18S2bR14A1A1Sb6RfA1A2S32A3S0S11SaaSa6R10S53G5R15A4Sc6A2S19Sd8S18S2bR15A1A1UaM6A2A1A3S0S11S19Sd8S18S2bR16A1A1G6A2A1S19P70A1M7A3Sb7S7eVrho0;S95VFB;VFF;A2M8S14S2bR17A1A1Sb6R12A1S5S49S47S46A2S49S47R10A2A8Sb8VAInv;VCST;VXGL;S7eVrho0;G8VFB;VFF;R18R13R12RfS4aS3aS2fA1ScdSccS1S1S3eZ1S3R11Sb6R15A1A2M9A2S42G9S40Z2MaZ27A2A2A2S1S0S2fS3fS3R11SaaR15PcA2A2S3R11SaaR15PdA2A2A2G9A3Sc0G3SbdSacSabR11R14R1A3R15A2A3A2A2Lms;LAi;AfS0S2aSb9S53R19R14R13G4A5R18A3S0S2aSb9S53R1aR15R14G5A5R18A3S12S0G1S23R1R14A2S23R1S48R15A1A2A3Fr;S0S11Sb6R17A1R14A3S0S3bS15A1MbS88S15S24S2bR1bA1A1U1McA3S39S15S1eG7S16Z0A1MdR15S36S26A1S25A5A2A3S0S33S34S11S11A2MeA1S2cR1cA1S38GeS69S4cS46A2MfS37GeS35S11S11G7R16A4S36GeA1M10A3A3A3S0S2aSdeS2dR1dSf1S2bR1dA1GcS52G7S48R18A1M11A2A3A2S38GeGfS37GeS35S11S11G7G11A4G10A3A3A2R1cA3S0S31S28S18S2bR1eA1A1S52G7S48R19A1A2A2S32A3S0S31S86GeS2eS18S2bR1fA1M12A1A1S38GeGfS37GeS35S11S11G7S48R1aA1A4G10A3A3A3S32A3S0GbS88S15S24G12A1U7M13A3S39S15S52S4cS48S46A1A2A2A3S0S31S84S13S17S1dS1cSd2S46GdA3A1A1S14S2bR20A1A1A3S32A3S96S14S2bR21A1A1A1S0S2aSdbS8bS35S11S11G7S48R1eA1A4A1S2dR22Se5S2bR22A1G13A2A2A2R21A3S0S31S84S13S17S1dS1cSd1G7GdA3A1A1S14S2bR23A1A1A3S32A3S0S31S86S13S22S18S2bR24A1M14A1A1S38S13S8bS35S11S11G7S48R20A1A4A1S14G14A1A3A3S32A3S85S34S34S2aS89A2M15S34S2fS11A2M16A2M17S35G15G16S35S2aS89R27S6bR21A1A4S35S2fS11Z3cS5fA4M18A4S4eA3S85G17S35G15G16S35S2aS89R25S6aG7R22A2A4G18A4S4eA3S3eS3fZ46S40GaZ40A2A2R1fA2VTR;S7fS45VJAv;S4aA1R2bR22R21A5VFAM;R20R1fA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fcst;Fkn;FR;Fs;FTok;FTokA;FTok0;FTn;FE;").
Proof.
  intros E Tn Tok0 TokA Tok s R kn cst rho tp b tp0 Hs He Hchk Htp Hnf Hnb Hbr Hcsz Hres H112 HPAY HSITE
         HTn HTok0 Hev Hcst Hblk HX HTokA Hwf HXb Hold HK0 HB HTok Hp0 Hbelow HinN HinOK Hb.
  subst s. unfold Pre_c in *.
  apply (calloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue HKc HBX TR TR_facts TR_ex TR_pre TR_callP
           [] UStopLe E (s_c E) R rho tp nd0 (bdP vW kn) (FAM b tp0) CCALLOC He Hchk Htp Hnf Hnb Hbr Hcsz Hres HPAY (fun _ _ _ _ => I) HSITE).
  -   intros rho' tp'. rewrite HTn. cbn [nd_tv nd_fr nd0]. apply (REENTER Tn (ndN kn) (60, z0)); [exact HinN | meas].
  -   intros rho' tp'. rewrite HTok0, H112, Hcst. cbn [nd_tv nd_fr nd0].
    eapply TR_pre; [|apply (REENTER Tok (ndG (SVar 112) kn) (60, z0)); [exact HinOK | meas]].
    intros w Hw.

    apply (SPA_JA_tv_ext segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue ((SVar 112, cst) :: tv0) ((SVar 112, kbytes kn) :: tv0)) in Hw.
    2: { intros _. split; [cbn [map]; unfold tvv; cbn [fst snd]; rewrite (Hev rho'); reflexivity|].
         intros [|k] t t' Ht Ht'; cbn [nth_error] in Ht, Ht'; [injection Ht as <-; injection Ht' as <-; unfold tnz; cbn [fst]; tauto|].
         rewrite Ht in Ht'. injection Ht' as <-. tauto. }
    apply (SPA_JA_drop_tv segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue _ [] (bdP vW kn) 1) in Hw.
    2: {
         intros HF0 t Ht. unfold tv0 in Ht. cbn [nth_error] in Ht. injection Ht as <-. right.
         assert (EF : ss_facts (ax_S TokA) = ss_facts (ax_S Tok0)) by (rewrite <- HTokA; reflexivity).
         pose proof HB as HB0. pose proof HK0 as HK00. rewrite EF in HB0, HK00.
         pose proof (basez_of rho' _ HF0 HB0) as [_ _ _ _ _ [EK _] _].
         pose proof (holds_mem _ _ _ HF0 HK00) as F0. zf F0. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
         rewrite uval_lit in F0 by lia. unfold tvv. cbn [snd]. change (bv_unsigned (eval rho' (kbytes vK))) with (uval rho' (kbytes vK)). rewrite EK, F0. lia. }
    cbn [remove_nth] in Hw.
    change (ND [(SVar 112, kbytes kn)] [] (bdP vW kn)) with (ndG (SVar 112) kn) in Hw.

    assert (Hw1 : SPA segs (JAv (ndG (SVar 112) kn)) TokA rho' tp' w).
    { rewrite <- HTokA. apply (SPA_x_requiv segs).
      - cbn [ax_X ax_setS]. rewrite HX. unfold X_vr. repeat constructor; cbn [fst snd]; try reflexivity. symmetry. apply Hev.
      - cbn [ax_S ax_setS]. unfold reshape_obj_at. cbn [ss_next set_objs]. exact HXb.
      - apply (SPA_reshape segs _ rho' Tok0 1 _ _ tp' w Hblk); [reflexivity | reflexivity | reflexivity | exact Hwf | | exact Hw].
        intros _. unfold obj_lo_of, obj_hi_of, O_data. cbn [ob_base ob_lo ob_hi]. unfold soff. rewrite (Hev rho'). split; reflexivity. }
    assert (Hw3 : SPA segs (JAv (ndG (SVar 112) kn)) (ax_setS TokA (drop_obj_at (ax_S TokA) 7)) rho' tp' w).
    { apply (SPA_drop_empty segs _ rho' TokA 7 _ tp' w Hold); [|exact Hw1].
      intros HF. pose proof (basez_of rho' _ HF HB) as [_ _ _ _ _ [EK _] _].
      pose proof (holds_mem _ _ _ HF HK0) as F0. zf F0. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
      rewrite uval_lit in F0 by lia.
      unfold obj_hi_of, obj_lo_of, O_data. cbn [ob_lo ob_hi]. rewrite soff_lit_small by lia.
      rewrite (soff_smallu rho' (kbytes vK)) by (rewrite EK, F0; lia). rewrite EK, F0. lia. }
    rewrite <- HTok. unfold ax_add_facts.
    change (ax_setS (ax_setS TokA (drop_obj_at (ax_S TokA) 7)) (add_facts (tv_factsA (SVar 112, kbytes kn)) (ax_S (ax_setS TokA (drop_obj_at (ax_S TokA) 7)))))
      with (ax_with_facts (ax_setS TokA (drop_obj_at (ax_S TokA) 7)) (tv_factsA (SVar 112, kbytes kn) ++ ss_facts (ax_S (ax_setS TokA (drop_obj_at (ax_S TokA) 7))))).
    apply (SPA_refacts_JA segs); [exact Hw3 | exact Hbelow |].
    intros tr md HJ HF2. apply Forall_app. split; [|exact HF2].
    eapply (JA_tv_facts segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue ALA); [ | exact HJ | left; reflexivity |]; [reflexivity|].
    apply tnz_of_fact. exact (holds_mem _ _ _ HF2 Hp0).
Qed.
Lemma X_E_cW0 : ltac2:(tb__ "0|1|
S12S33S82Q40A1A1M0S2fG0S3eS3fZ46S40Z2Z40A2A2R2A2VTR;S7fS45VJAv;S4aA1S70R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_E_c E_cW0 T_cW0n0 T_cW0ok0 T_cW0okA T_cW0ok (s_c E_cW0) R_cW0 vW (SMd M_MUL vW vE) rho tp b tp0 eq_refl).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact pay_cW0.
  - exact (site_cW0 rho).
  - exact T_cW0n0_eq.
  - exact T_cW0ok0_eq.
  - intros r. apply eval_mul_comm.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact T_cW0ok_eq.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - innth 9.
  - innth 10.
  - exact Hb.
Qed.
Lemma X_E_c8 : ltac2:(tb__ "0|1|
S12S33S82Q40A1A1M0S2fG0S3eS3fZ46S40Z2Z40A2A2R2A2VTR;S7fS45VJAv;S4aA1S6fR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_E_c E_c8 T_c8n0 T_c8ok0 T_c8okA T_c8ok (s_c E_c8) R_c8 (SLit 8) (SMd M_MUL (SLit 8) vE) rho tp b tp0 eq_refl).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact pay_c8.
  - exact (site_c8 rho).
  - exact T_c8n0_eq.
  - exact T_c8ok0_eq.
  - intros r. apply eval_mul_comm.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact T_c8ok_eq.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - innth 11.
  - innth 12.
  - exact Hb.
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S2aS89S34S2fS11A2M0S12S33S82Q40A1A1M1G1S85S34S34S2aS89A2M2G0A2S35G2G0S35S2aS89R6R5A4R4A4S77A3VTR;S7fS45VJAv;R6A1R7R4R3A5VFAM;S8eS35G2G0S35S2aS89R7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsE] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]]]]; injection H as <- <- <-.
  - apply X_X15. meas.
  - apply X_XW1. meas.
  - apply X_XW0. meas.
  - apply X_X8. meas.
  - apply X_E_r15. meas.
  - apply X_E_rW1. meas.
  - apply C_calloc_contra; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - apply C_calloc_contra; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - apply X_E_cW0. meas.
  - apply X_E_c8. meas.
  - apply C_realloc_contra; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply C_realloc_contra; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply POST. innth 0.
  - apply POST. innth 1.
  - apply POST. innth 2.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S94S45VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
Sc8S45SbeVAInv;VCST;VXGL;A5").

Theorem vec_reserve_sum : ltac2:(tb__ "0|0|
S33S82Q40A1A1Sa1S45Vok;S7fS45S8cVAInv;VCST;VXGL;VKc;S95VFB;VFF;A2VFB;VFF;VBX;S8aS4aAaS62Vrho0;R1A5Sa3S45S7eVrho0;R1S9aA5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue HKc ALA FUEL_vr cutpcs_vr 100
                (map edropA cutsE) (map edropA exitsE) ok (Q tp0) Hok (ejcertA_jcertA segs NF _ _ _ _ _ ejcertA_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsE)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_false segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros Ai rho1 tp1. apply (aca_calloc _ _ _ _ _ AC); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
       - intros FBc FFc BXc rho1 tp1 HBc. apply (RA.realloc_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HBc rho1 ok Hok AC tp1).
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue ok (map edropA cutsE) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NF Kc (P0_vr FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_vr P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
Sc9S45SbeVAInv;VCST;VXGL;A5").

Theorem vec_reserve_sum_ex : ltac2:(tb__ "0|0|
S33S82Q40A1A1Sa0S45S7fS45S8cVAInv;VCST;VXGL;VKc;S95VFB;VFF;A2VFB;VFF;VBX;S8aS4aAaS62Vrho0;R1A5Sa3S45S7eVrho0;R1S9aA5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue HKc ALA FUEL_vr cutpcs_vr 100 cutsE exitsE (Q tp0) ejcertA_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue) cutsE) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_false segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros Ai rho1 tp1. apply (acx_calloc _ _ _ _ _ ACX); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc].
       - intros FBc FFc BXc rho1 tp1 HBc. apply (RA.realloc_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HBc rho1 ACX tp1).
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_vr FB FF) FB FF BX PTrue cutsE T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NF Kc (P0_vr FB FF) FB FF BX PTrue rho0 tp0 nd Posts_vr P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_vec_reserve_pf.

(* [comment removed for export] *)
Module Lib_load_obj_epiS_kit.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "BIc"; "BUD"; "BXnn"; "@Corelib.Init.Datatypes"; "list"; "prod"; "cons"; "app"; "nil"; "false"; "pair"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "AHead"; "AK0"; "AV0"; "NDA"; "JA"; "JAi"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "and"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section PotIn.
Variable segs : list Segment.
Variable AInv : ltac2:(tb__ "0|0|
S1cSeS5S17Q40A1A1S19OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Variable NP' : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S5S6S6S0S0A2S0A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.

Lemma BUD_pot_in : ltac2:(tb__ "0|3|
S5S1A1S0S0S0S0S0S0S0S0SeS3S8S1RaS7S1S2Z1M0Z0M1S13A3S7S1S2G1G0S12A3S9S1A1A3A3A3SbS0S0SfR9G1A2SfSfR8G1A2R7A2A4R4R3R2R1A6S10G1RaA2M2G2G2S18G2S10RaS13A2A2S18G2S10RaS12A2A2S3R10SbS0S0SfRfRcA2SfSfReRbA2RdA2A4RaR9R8R7A6F_;F_;F_;F_;F_;F_;Frho;FKf;FKm;FV;Fpk;Fpv;Fkc;Fx2;Fx1;Fb;").
Proof.
  intros b x1 x2 kc pv pk V Km Kf rho H H1 H2 Hkc Hpv Hpk.
  pose proof H as (A1 & A2 & A3 & A4 & A5 & Hw & Hn & B1 & B2). cbn [fst snd] in *.
  rewrite bsumV_app in B1. rewrite bsumK_app in B2. rewrite bd_wpos_app in Hw. apply andb_prop in Hw as [Hw _].
  unfold BIc in B1, B2. cbn [bsumV bsumK bi_v bi_k] in B1, B2. unfold bival in B1, B2. cbn [lfval bi_f bi_c] in B1, B2.
  apply bd_nn_app in Hn as [Hn _].
  unfold BUD. cbn [fst snd]. repeat (split; [first [assumption | lia]|]). lia.
Qed.

Lemma JAi_pot_in : ltac2:(tb__ "0|2|
S5S6SdSdA2A1S5S6S6SdS0A2SdA2A1S5S1A1SdS1cS0SeS5S17Q40A1A1S5S1aA1S19S4VBX;A1S16VAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S14RbRaS8S1R9S7S1S2Z1M0Z0M1S13A3S7S1S2G1G0S12A3S9S1A1A3A3A3S11R8SaA2A4R7R6R5R4R3R2A12S16VAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S14RcRbRaS11R9ScA2A4R8R7R6R5R4R3A12F_;F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fhd;Fbd;Ffr;Ftv;").
Proof.
  intros tv fr bd hd Ai kc rho tp tr md [HX1 HX2] HJ.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & HNDZ & HFR & HK0 & HP0 & HXA & HBU & HPA & HCK & HCN).
  cbn [nd_tv nd_fr nd_bd nd_am] in HNDZ, HFR, HXA, HBU |- *.
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HNDZ|]. split; [exact HFR|]. split; [exact HK0|]. split; [exact HP0|]. split; [exact HXA|].
  split; [|split; [exact HPA | split; [exact HCK | exact HCN]]].
  pose proof (apot_range (AHead hd true) rho) as [R1 R2].
  unfold apot in HBU. cbn [am_eval apotz] in HBU. unfold bxa in HBU |- *. cbn [fst snd] in HBU |- *.
  apply (BUD_pot_in bd (fst (bx2 BX)) (snd (bx2 BX)) kc _ _ _ _ _ rho HBU HX1 HX2 (XA_kc_nonneg _ _ _ _ _ _ HXA) R1 R2).
Qed.

Lemma SPA_JA_pot_in : ltac2:(tb__ "0|2|
S5S6SdSdA2A1S5S6S6SdS0A2SdA2A1S5S1A1SdS1eSeS5S17Q40A1A1S1dS4VBX;A1S1bVsegs;S15VAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S14R9R8S8S1R7S7S1S2Z1M0Z0M1S13A3S7S1S2G1G0S12A3S9S1A1A3A3A3S11R6SaA2A4AcR5R4R3R2A6S1bVsegs;S15VAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S14RaR9R8S11R7ScA2A4AcR6R5R4R3A6F_;F_;Fw;Ftp;Frho;FA;Fhd;Fbd;Ffr;Ftv;").
Proof.
  intros tv fr bd hd A rho tp [tr [ms md]] HX [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, kc. exact (JAi_pot_in tv fr bd hd Ai kc rho tp tr md HX HJ).
Qed.
End PotIn.
End Lib_load_obj_epiS_kit.

