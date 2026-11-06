(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nj.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_l_s2.

(* [comment removed for export] *)
Module FpsC_a4.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nat"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsC_st"; "T7s"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail"; "FPA"; "FQA"; "PRE_C"; "SUF_NL"; "T8"; "tailA_n"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "factsS"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsC_st.
Import ListNotations.
Open Scope Z_scope.

Lemma okA_4 : ltac2:(tb__ "0|0|
S7S2S11S0S0SfSaR1S6A2S0SbR2R1S6A3Lr;ScSdR1S12Z12R1A2S0SeZ11R2R1S10S6A5Lr;S1S0Z0S1S0Z1S1S0Z2S1S0Z3S4S0A1A3A3A3A3A8Ln;S8S3S0S13S9U20U8A2A4A3S5A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End FpsC_a4.

(* [comment removed for export] *)
Module Fps_tailA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@Corelib.Init.Datatypes"; "list"; "length"; "bool"; "nat"; "Some"; "true"; "option"; "nil"; "app"; "false"; "cons"; "pair"; "prod"; "S"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "rl"; "sprop"; "ss_next"; "sstate"; "holds"; "sv"; "SLit"; "agree_below"; "ss_objs"; "rw"; "sprop_below"; "cell"; "ob_cells"; "ob_dflt"; "rm"; "ss_lenient"; "ss_pc"; "swf"; "DList"; "dflt_writable"; "is_arr"; "ob_hi"; "ob_lo"; "odefault"; "sprop_eqb"; "ss_facts"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "Forall"; "nth"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.TailA"; "Kf"; "MSGb"; "Kwr"; "EVS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "obj_ext"; "ax_base"; "ax_setS"; "entailsA"; "mkLeafA"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre"; "facts_fps"; "BASEF"; "fs_ok"; "CUTS_FPS"; "FUEL_T"; "runp"; "set_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "beval"; "BLit"; "BSrc"; "cells_bytes"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "FdEntry"; "FdChannel"; "WriteEv"; "fd_lookup"; "m_fds"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "@Stdlib.ZArith.BinInt.Z"; "of_nat"; "add"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail"; "tailA_out"; "Posts_fps"; "blA"; "P_fps"; "bexps_eqb"; "seg"; "splitsA"; "tailA_post"; "XQ1"; "XQ2"; "XW"; "bexp_eqb"; "dropL"; "post_sub"; "subA"; "tailA"; "x_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.TailA.Post"; "Jp"; "rho_wl"; "WLF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Musl_wl_err.WLerrS"; "Pre_wl2"; "D"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rl"; "state_has_rl"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvFw"; "ch2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Musl_wl_err.WLerr"; "Kw"; "MSG"; "Posts_wl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@Corelib.Init.Peano"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.DrvFpStates"; "O_b2e"; "finish_fp"; "unlist_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.TailA.Post.Inst"; "rho_fin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_get"; "rho_absorb"; "rho_sub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj"; "obj_to_list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "apply_xforms";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ListCommitA"; "exts_rl_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFpIface"; "fp_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFwStates"; "axc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "mat_equiv"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundV SymSoundM SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymBytes SymObj SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ListObj DrvGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform ListCommitA SysA MuslWLA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import SpecConsts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Musl_wl_err.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvFw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Musl_wl_err OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFwStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvFw OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFpIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.DrvFpStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.DrvFp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nc.Str_strnlenA_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Icpt_strnlen_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_istrlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_run OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma seg_run : ltac2:(tb__ "0|1|
S7S3fS33S3fS0SaS3fA1S6aR4R3R2A3S8S3fR1A2A3S1S0SaS4S41A1M0A1S47S15R5S50R4S9A5S8G0SeS41S46R2S9cA2SbS41A1A3A2A3S0S33S29S40R2A1A1R3A3A2F_;FW;Fpc;FA;Ffuel;").
Proof.
  intros fuel A pc W H. unfold seg in H.
  destruct (sym_runA segs fuel CUTS_FPS A true) as [ls|]; [|discriminate]. destruct ls as [|L ls']; [discriminate|]. destruct ls' as [|L2 ls'']; [|discriminate].
  destruct L as [S r]. cbn [la_reason la_state] in H. destruct r; try discriminate.
  destruct (Z.eqb_spec (ss_pc (ax_S S)) pc); [|discriminate]. injection H as <-. split; [reflexivity | assumption].
Qed.

Lemma splitsA_SPA : ltac2:(tb__ "0|0|
S4aS33S3fS1cS18S4S12Q40A1A1S87S0SaS1cA1S6bR6S40R5A1A2S8S1cR4A2A3S48S15R8R6R4R3R2A6S48S15R9S44R7R6A2R5R4R3A6F_;F_;Fw;Ftp;Frho;FS6;FA;Fe;FJ;").
Proof.
  intros J e A S6 rho tp w H Hsp. unfold splitsA, obindW in H.
  destruct (split_obj_at (ax_S A) 0 (SLit (-584))) as [S1|] eqn:E1; [|discriminate].
  destruct (split_obj_at S1 1 (SLit (-552))) as [S2|] eqn:E2; [|discriminate].
  destruct (split_obj_at S2 2 (SLit (-464))) as [S3|] eqn:E3; [|discriminate].
  destruct (split_obj_at S3 3 (SLit e)) as [S4|] eqn:E4; [|discriminate].
  destruct (split_obj_at S4 5 (SLit (FERR + 120))) as [S5|] eqn:E5; [|discriminate].
  pose proof (SPA_split segs J rho A 0 (SLit (-584)) S1 tp w E1 Hsp) as H1.
  pose proof (SPA_split segs J rho (ax_setS A S1) 1 (SLit (-552)) S2 tp w E2 H1) as H2.
  pose proof (SPA_split segs J rho (ax_setS (ax_setS A S1) S2) 2 (SLit (-464)) S3 tp w E3 H2) as H3.
  pose proof (SPA_split segs J rho (ax_setS (ax_setS (ax_setS A S1) S2) S3) 3 (SLit e) S4 tp w E4 H3) as H4.
  pose proof (SPA_split segs J rho (ax_setS (ax_setS (ax_setS (ax_setS A S1) S2) S3) S4) 5 (SLit (FERR + 120)) S5 tp w E5 H4) as H5.
  pose proof (SPA_split segs J rho (ax_setS (ax_setS (ax_setS (ax_setS (ax_setS A S1) S2) S3) S4) S5) 6 (SLit (FERR + 124)) S6 tp w H H5) as H6.
  rewrite !ax_setS_setS in H6. exact H6.
Qed.

Lemma bexp_eqb_sound : ltac2:(tb__ "0|0|
S54S54S0S6S70R2R1A2S9A3S0S54R3R2A3F_;Fb;Fa;").
Proof.
  intros [x|l i] [y|l' i'] H; cbn in H; try discriminate.
  - apply Z.eqb_eq in H. subst. reflexivity.
  - apply andb_prop in H as [H1 H2]. apply Pos.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.
Lemma bexps_eqb_sound : ltac2:(tb__ "0|1|
S4S54A1M0G0S0S6S69R2R1A2S9A3S0G0R3R2A3F_;Fb;Fa;").
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. f_equal; [apply bexp_eqb_sound; exact H1 | apply IH; exact H2].
Qed.
Lemma map_beval_lit : ltac2:(tb__ "0|2|
S18S4S33A1S0S4S12Q8M0A1M1A1S36S54G1S55R2A1S36S33S54S56R1A4A4S36S33G1S13G0A1R1A4A3Fl;Fr;").
Proof. intros r l. rewrite map_map. reflexivity. Qed.
Lemma firstn_S_snoc : ltac2:(tb__ "0|2|
S4S12Q8A1M0A1M1S7G0S89R2S5G0R3A2A2S0G1S37G0S11R3A1R4A3ScG0S37G0R3R4A3SeG0S39G0R3R4R2A4SbG0A1A3A3A3F_;Fd;Fk;FL;").
Proof.
  induction L as [|x L IH]; intros k d Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [firstn nth app]. rewrite (IH k d) by lia. reflexivity.
Qed.
Lemma map_nth_seq : ltac2:(tb__ "0|2|
S4S12Q8A1M0A1M1G0S7S88R1S5G0R3A2A2S0G1S36S7G0S7S39G0R1R5R4A4Li;S3aU0R2A2A4S37G0R2R4A3A3F_;Fk;Fd;FL;").
Proof.
  intros L d k. induction k as [|k IH]; intros Hk; [reflexivity|].
  rewrite seq_S, map_app, IH by lia. cbn [map Nat.add]. rewrite (firstn_S_snoc L k d) by lia. reflexivity.
Qed.
Lemma map_beval_src : ltac2:(tb__ "0|3|
S18S4S12Q8A1M0A1M1S7S0G1S37G0S5G0R2A2S19R3P3M2A2A3R2A3S88R2S5G0R3A2A2S0G1S36S54G0S55R5A1S36S7S54S7S57G2S62R1A1A2Li;S3aU0R3A2A4A4S37G0R3R4A3A3F_;F_;Fk;Fstr;Fr;").
Proof.
  intros r str k Hstr Hk. rewrite map_map. cbn [beval].
  transitivity (map (fun i => nth i (rl r 3) (Z_to_bv 8 0)) (seq 0 k)); [apply map_ext; intros i; rewrite Nat2Z.id; reflexivity|].
  assert (HL : (length str <= length (rl r 3))%nat) by (rewrite <- Hstr at 1; rewrite length_firstn; lia).
  rewrite (map_nth_seq (rl r 3) _ k) by lia. rewrite <- Hstr, firstn_firstn. f_equal. lia.
Qed.
Lemma blA_val : ltac2:(tb__ "0|5|
S18S4S33A1M0S4S12Q8M1A1M2A1M3G0S0G3S37G2S5G2R2A2S19R4P3A2A3R2A3S0G3S36S54G2S55R5A1S67R4S62S5G2R3A2A1R2A3A4ScG2S36S33G2S13G1A1M4R4A4ScG2R3S36S33G2G4R2A4A3A3A3F_;Fsuf;Fstr;Fpre;Fr;").
Proof.
  intros r pre str suf Hstr. unfold blA. rewrite !map_app, !map_beval_lit, Nat2Z.id.
  rewrite (map_beval_src r str (length str) Hstr ltac:(lia)), firstn_all. reflexivity.
Qed.

Section TailA.
Variable ok : world -> Prop.
Variable J0 : jpredA.
Variables pre suf : list Z.
Variable str : list byte.
Definition MSGb : list byte := ltac2:(tb__ "0|3|
ScS12Q8M0A1M1S36S33G1S13G0A1M2Vpre;A4ScG1Vstr;S36S33G1G2Vsuf;A4A3A3").
Definition EVS (k : nat) : list event := ltac2:(tb__ "0|1|
S36S12Q8A1M0S5aS5dS81A1S37G0Vk;S3cA3A4").
Definition Kwr (k : nat) : jpredA := ltac2:(tb__ "0|1|
S18S4S12Q40A1A1S4S5aA1M0S59S2G0G0S1VJ0;R5R4R1R2A4S0G0R3ScS5aR1S3eVk;A1A3A3A2Ltr0;A2Lmd;Ltr;Lt;Lr;").
Hypothesis Hst0 : stableA segs NF J0.
Hypothesis Hfd2 : ltac2:(tb__ "0|0|
S18S4S12Q40A1A1S4S5aA1S59VJ0;R4R3R2R1A4S0SaS5bA1S5eS5fR2A1S81A2S8S5bS5cS81A1A2A3F_;Fmd;Ftr;Ft;Fr;").
Hypothesis HokK : ltac2:(tb__ "0|0|
S7S4bS15Vok;S3dR1A1A3Fk;").
Hypothesis HokP : ltac2:(tb__ "0|0|
S7S96S15Vok;S3dR1A1A3Fk;").
Variable rho : valuation.
Variable tp : list word.
Hypothesis Hstr : ltac2:(tb__ "0|1|
S0S4S12Q8A1M0A1S37G0S5G0Vstr;A2S19Vrho;P3A2A3Vstr;A3").

Definition Kf (k : nat) : jpredA := ltac2:(tb__ "0|1|
S18S4S12Q40A1A1M0S4S5aA1S59S1S0G0R3Vtp;A3S3dVk;Vrho;R3R2R1A5A2Lmd;Ltr;Lt;L_;").
Lemma J0_mat : ltac2:(tb__ "0|0|
S18S4S12Q40A1A1S4S5aA1S59S59Sa0S15R4R2R1A4VJ0;R6R5R4R3A4VJ0;R7R6R5R3A4F_;F_;Fmd';Fmd;Ftr;Ft;Fr;").
Proof. intros r t tr md md' Hme HJ. eapply Hst0; [apply agree_below_refl | exact Hme | exact HJ]. Qed.
Lemma Kf_stable : ltac2:(tb__ "0|0|
S7S34S4cS15R1S3bR2A1A3Flvl;Fk;").
Proof.
  intros k lvl r r' t tr md md' Hag Hme [Ht (tr0 & HJ & Htr)]. split; [exact Ht|].
  exists tr0. split; [eapply J0_mat; eauto | exact Htr].
Qed.
Lemma Kf_okK : ltac2:(tb__ "0|0|
S7S4bS15Vok;S3bR1A1A3Fk;").
Proof. intros k r t tr ms md msv' [_ HK]. exact (HokK k rho t tr ms md msv' HK). Qed.
Lemma Kf_okP : ltac2:(tb__ "0|0|
S7S96S15Vok;S3bR1A1A3Fk;").
Proof. intros k r t tr ms md x8 [_ HK]. exact (HokP k rho t tr ms md x8 HK). Qed.
Lemma Kf_inv : ltac2:(tb__ "0|0|
S7S18S18S4S12Q40A1A1S4S5aA1S59S3bR6R5R3R2R1A5S3bR7R5R4R3R2A5F_;Fmd;Ftr;Ft;Fr';Fr;Fk;").
Proof. intros k r r' t tr md H. exact H. Qed.
Lemma MSGb_len : ltac2:(tb__ "0|1|
S0S7S5S12Q8A1M0S3cA2S7bS7bS5S33Vpre;A2S5G0Vstr;A2A2S5S33Vsuf;A2A2A3").
Proof. unfold MSGb. rewrite !length_app, !length_map. lia. Qed.

Section Post.
Variable k0 : nat.
Variables M1 M2 : list byte.
Variable len2 : Z.
Variables pre2 suf2 : list Z.
Variable n2 : Z.
Hypothesis HM : ltac2:(tb__ "0|1|
S0S4S12Q8A1M0A1S3cScG0VM1;VM2;A3A3").
Hypothesis Hk0 : k0 = length M1.
Hypothesis Hlen2 : ltac2:(tb__ "0|0|
S0S33Vlen2;S62S5S12Q8A1VM2;A2A1A3").
Hypothesis Hlen2r : 1 <= len2 <= 80.
Hypothesis Hbl2 : ltac2:(tb__ "0|3|
S18S0S4S12Q8A1M0A1M1S19R1P3M2A2S19Vrho;G2A2A3S0G1S36S54G0S55R2A1S67Vpre2;Vn2;Vsuf2;A3A4VM2;A3F_;Fr;").

Lemma Lk : ltac2:(tb__ "0|1|
S0S7S7bVk0;S5S12Q8A1M0VM2;A2A2S5G0S3cA2A3").
Proof. rewrite HM, Hk0, length_app. reflexivity. Qed.

Definition rho_wl (r : valuation) : valuation := ltac2:(tb__ "0|0|
S7cS7cVr;P6SbS12Q8A1A1A3P5VM2;A3").
Definition WLF (r : valuation) : Prop := ltac2:(tb__ "0|3|
S1S0S4S12Q8A1M0A1M1S19Vr;P5A2VM2;A3S1S0G1S19Vr;P6A2SbG0A1A3S1S0S33S14Q40M2S22Vr;PdA2A2Vlen2;A3S0S33S14G2S22Vr;PfA2A2Z0A3A2A2A2").
Definition Jp : jpredA := ltac2:(tb__ "0|0|
S18S4S12Q40A1A1S4S5aA1S59S1S78R4A1S3bVk0;R4R3R2R1A5A2Lmd;Ltr;Lt;Lr;").
Lemma Jp_stable : stableA segs 92 Jp.
Proof.
  intros r r' t tr md md' Hag Hme [(A5 & A6 & A13 & A15) HK].
  split; [| eapply (Kf_stable k0 92%positive); [exact Hag | exact Hme | exact HK]].
  destruct Hag as (Hw & Hl & _). unfold WLF.
  rewrite <- (Hl 5%positive), <- (Hl 6%positive), <- (Hw 13%positive ltac:(lia)), <- (Hw 15%positive ltac:(lia)).
  repeat split; assumption.
Qed.
Lemma Kw_Jp_Kf : ltac2:(tb__ "0|0|
S7S18S4S12Q40A1A1S4S5aA1S59S82S76VM2;SbS12Q8A1A1R5R4R3R2R1A8S3bS7bVk0;R6A2R5R4R3R2A5F_;Fmd;Ftr;Ft;Fr;Fk;").
Proof.
  intros k r t tr md (tr0 & [_ [Ht (tr00 & HJ & ->)]] & ->). split; [exact Ht|].
  exists tr00. split; [exact HJ|]. unfold WLerr.TRk, WLerr.MSG, EVS. rewrite app_nil_r, <- app_assoc, <- map_app. f_equal. f_equal.
  rewrite HM, Hk0, firstn_app_2. f_equal. rewrite firstn_app, firstn_all2, Nat.sub_diag by lia. cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.
Lemma wl_MSG_len : ltac2:(tb__ "0|1|
S0S7S5S12Q8A1M0S83VM2;SbG0A1A2A2S5G0VM2;A2A3").
Proof. unfold WLerr.MSG. rewrite app_nil_r. reflexivity. Qed.
Lemma wl_call : ltac2:(tb__ "0|2|
S18S4S12Q40A1A1S86S15Vok;S48S15S76S79R2R1A5S49S15S82S76VM2;SbS12Q8A1M0A1M1S5G0S83VM2;G1A2A2A4P5cR2R1S84A6A4Ftp2;Frho2;").
Proof.
  intros rho2 tp2.
  apply triple_SPA_pure. intros tr md [(A5 & A6 & A13 & A15) _].
  apply (triple_SPA_conseq_J segs ok _ Jp); [intros t md0 (HJ & _ & _); exact HJ|].
  apply (WLerr.wl2_sum ok Jp rho2 tp2 M2 [] A5 A6).
  - rewrite A13, Hlen2. reflexivity.
  - rewrite A15. reflexivity.
  - rewrite wl_MSG_len. unfold max_write_total. lia.
  - apply Jp_stable.
  - intros k r t tr0 ms md0 msv' HK HMI Hh Hp Hstep. exact (Kf_okK (k0 + k) r t tr0 ms md0 msv' (Kw_Jp_Kf k r t tr0 md0 HK) HMI Hh Hp Hstep).
  - intros k r t tr0 ms md0 x8 HK Hp Ho. exact (Kf_okP (k0 + k) r t tr0 ms md0 x8 (Kw_Jp_Kf k r t tr0 md0 HK) Hp Ho).
  - intros r t tr0 md0 [_ [_ (tr00 & HJ & _)]]. exact (Hfd2 _ _ _ _ HJ).
  - lia.
Qed.
Lemma wl_call_ex : ltac2:(tb__ "0|2|
S18S4S12Q40A1A1S85S15S48S15S76S79R2R1A5S49S15S82S76VM2;SbS12Q8A1M0A1M1S5G0S83VM2;G1A2A2A4P5cR2R1S84A6A3Ftp2;Frho2;").
Proof.
  intros rho2 tp2 w Hw. pose proof Hw as [Hsm [(A5 & A6 & A13 & A15) HK]].
  apply (WLerr.wl2_sum_ex Jp rho2 tp2 M2 [] A5 A6).
  - rewrite A13, Hlen2. reflexivity.
  - rewrite A15. reflexivity.
  - rewrite wl_MSG_len. unfold max_write_total. lia.
  - apply Jp_stable.
  - intros r t tr0 md0 [_ [_ (tr00 & HJ & _)]]. exact (Hfd2 _ _ _ _ HJ).
  - lia.
  - exact Hw.
Qed.

Local Opaque FUEL_T.
Section Inst.
Variables T8 W0 : axst.
Variable o : tailA_out.
Hypothesis Hcert : ltac2:(tb__ "0|0|
S0SaS65A1S6cVpre2;Vsuf2;Vn2;Vlen2;VT8;VW0;A6S8S65Vo;A2A3").
Hypothesis HnT8 : ltac2:(tb__ "0|0|
S60S35S1bS40VT8;A1A1A2").

Let W := ta_W o. Let S6 := ta_S6 o. Let Cs := ta_Cs o. Let s := ta_s o. Let R := ta_R o. Let T := ta_T o.
Let F0 := ta_F o. Let G1 := ta_G1 o. Let G2 := ta_G2 o. Let G2u := ta_G2u o. Let G3 := ta_G3 o. Let sp := ta_sp o.
Let C : axst := ax_setS W Cs.
Let Tf : axst := ax_add_facts BASEF T.
Let F : axst := ax_add_facts facts_fps F0.

Lemma cert : ltac2:(tb__ "0|17|
S2S17S17S2S4S54A1M0G0S2S17S17S1S1S0S33S29S40VW0;A1M1A1Zd6760A3S60S1bS40VT8;A1A1M2S1bG1A1A2A2S1S0SaS3fA1M3Sa2S53VW0;S4dA2S6fA2S8S3fVW;A2A3S1S0S6S7eS1aS1aS80S1aS31R1A1S32S40VW;A1M4A1A3Lf;S4dA3S9A3S1S60G2S1bG4A1M5A2S1S0SaS1cA1M6S6bS63N1d0M7Vlen2;A2M8G4A2S8S1cVS6;A2A3S1S0SaS17A1M9S7fS17S21VS6;A1MaU3MbA3S8S17R3A2A3S1S0SaG0A1S58S25R3A1S1fG7A1McZ0MdS64Vlen2;A1A4S8G0R2A2A3S1S0S6S69R2S67Vpre2;Vn2;Vsuf2;A3A2S9A3S1S0S6S7dP5MeVS6;A2SdA3S1S0S6S7dP6MfVS6;A2SdA3S1S0S6S2cS26R3A1M10A1S9A3S1S0S6S2dG10A1SdA3S1S0S1eS2fR3A1GcA3S1S0S1eS2eR3A1S1fG8A1A3S1S0S6S99GeGaA2S9A3S1S0S6S99GfGaA2S9A3S1S0S1cVCs;S8eVS6;A1A3S1S0S91Vs;S73Vlen2;VCs;A2A3S1S0S6S75VW;S1bVCs;A1M11A2S9A3S1S0SaS4S17A1M12A1S9eVC;S79Vs;A3S8G12VR;A2A3S1S0S6S9dVC;S79Vs;VR;SeS3fS7aSbS3fA1A3A5S9A3S1S0S6S2aVCs;A1S9A3S1S0S1eS92Vs;PdA2S1fVlen2;A1A3S1S0S1eS92Vs;PfA2S1fGdA1A3S1S0S34G11G5A3S1S0S34S1bS97VS6;GbGeA3A1G5A3S1S0S34S1bVS6;A1G5A3S1S0S3fVT;S9fVs;S79S7aVC;VR;A5A3S1S0S6S28S40VTf;A1A1SdA3S1S60S35S1bS40VT;A1A1A2S1S0G3S6aS51VTf;S9aA3S8S3fVF0;A2A3S1S0G6S98S40VF;A1M13S6dA2S8S1cVG1;A2A3S1S0G9S7fS17S21VG1;A1M14U14A3S8S17S8dA2A3S1S0S7S5S17G14A2U15A3S1S0S1cVG2;S71VG1;A1A3S1S0G9S7fS17S21VG2;A1U1M15A3S8S17R1A2A3S1S0S30S26R1A1S2bGeA1A3S1S0S4S24A1S25R1A1SbS24A1A3S1S0S1cVG2u;S8fVG2;G15A2A3S1S0S6S2aVG2u;A1S9A3S1S0G6S98VG2u;S6eA2S8S1cVG3;A2A3S1S0S91Vsp;S72VG3;A1A3S1S0S6S45S9bVG3;A1S68Vsp;A3S9A3S1S0S6S95Vsp;S35A2S9A3S1S0S6S7dGeVG3;A2SdA3S1S0S6S7dGfVG3;A2SdA3S1S0S1eS43VF;A1S1fS16A1A3S1S60S35S1bG13A1M16A2S1S0S34S1bVG1;A1G16A3S1S0S34S1bVG2u;A1G16A3S0S34S1bVG3;A1G16A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2Lob1;A2Lbl;A2Lo8;A2").
Proof.
  pose proof Hcert as H. unfold tailA_post in H.
  destruct ((ss_pc (ax_S W0) =? 0xd6760) && (ss_next (ax_S T8) <=? ss_next (ax_S W0))%positive) eqn:BP; [|discriminate]. cbn [negb] in H.
  apply andb_prop in BP as [BP BnW0]. apply Z.eqb_eq in BP. apply Pos.leb_le in BnW0.
  destruct (apply_axforms (set_facts W0 facts_fps) XW) as [W'|] eqn:EW; [|discriminate].
  destruct (forallb (fun f => existsb (sprop_eqb f) (ss_facts (ax_S W'))) facts_fps && (ss_next (ax_S T8) <=? ss_next (ax_S W'))%positive) eqn:Bf; [|discriminate]. cbn [negb] in H.
  apply andb_prop in Bf as [Bf BnW]. apply Pos.leb_le in BnW.
  destruct (splitsA (-464 + len2) (ax_S W')) as [S6'|] eqn:ES6; [|discriminate].
  destruct (nth_error (ss_objs S6') 3) as [o8|] eqn:Eo8; [|discriminate].
  destruct (cells_bytes (ob_cells o8) (SLit (-464)) 0 (Z.to_nat len2)) as [bl|] eqn:Ebl; [|discriminate].
  destruct (bexps_eqb bl (blA pre2 n2 suf2) && negb (state_has_rl 5 S6') && negb (state_has_rl 6 S6') && dflt_writable (ob_dflt o8) && negb (is_arr (ob_dflt o8))
            && sv_eqb (ob_lo o8) (SLit (-464)) && sv_eqb (ob_hi o8) (SLit (-464 + len2)) && exts_rl_free 5 (ss_objs S6') && exts_rl_free 6 (ss_objs S6')) eqn:B1; [|discriminate]. cbn [negb] in H.
  destruct (x_ok W' (ss_next (finish_fp S6'))) eqn:Bx; [|discriminate]. cbn [negb] in H.
  destruct (entails_frA (ax_setS W' (finish_fp S6')) WLerrS.Pre_wl2 (subA len2 (finish_fp S6'))) as [R'|] eqn:ER; [|discriminate].
  destruct (call_checkA (ax_setS W' (finish_fp S6')) WLerrS.Pre_wl2 (subA len2 (finish_fp S6')) R' [WLerrS.D] && swf (finish_fp S6')
            && sv_eqb (wsub_get (subA len2 (finish_fp S6')) 13) (SLit len2) && sv_eqb (wsub_get (subA len2 (finish_fp S6')) 15) (SLit 0)
            && (ss_next (finish_fp S6') =? ss_next (ax_S W'))%positive && (ss_next (obj_to_list S6' 3 5) =? ss_next (ax_S W'))%positive
            && (ss_next S6' =? ss_next (ax_S W'))%positive) eqn:B2; [|discriminate]. cbn [negb] in H.
  destruct (ss_lenient (ax_S (ax_add_facts BASEF (import_postA (subA len2 (finish_fp S6')) WLerrS.Pre_wl2 WLerrS.D (ax_setS W' (finish_fp S6')) R'))) || negb (NF <=? ss_next (ax_S (import_postA (subA len2 (finish_fp S6')) WLerrS.Pre_wl2 WLerrS.D (ax_setS W' (finish_fp S6')) R')))%positive) eqn:B3; [discriminate|].
  destruct (seg FUEL_T (ax_add_facts BASEF (import_postA (subA len2 (finish_fp S6')) WLerrS.Pre_wl2 WLerrS.D (ax_setS W' (finish_fp S6')) R')) fp_ret) as [F'|] eqn:EF; [|discriminate]. cbn zeta in H.
  destruct (apply_xforms (ax_S (ax_add_facts facts_fps F')) XQ1) as [G1'|] eqn:EG1; [|discriminate].
  destruct (nth_error (ss_objs G1') 20) as [ob2|] eqn:Eob2; [|discriminate].
  destruct (sobj_eqb ob2 O_b2e && (length (ss_objs G1') =? 21)%nat) eqn:B4; [|discriminate]. cbn [negb] in H.
  destruct (nth_error (ss_objs (dropL G1')) 1) as [ob1|] eqn:Eob1; [|discriminate].
  destruct (dflt_eqb (ob_dflt ob1) (DList 5) && (length (ob_cells ob1) =? 0)%nat) eqn:B5; [|discriminate]. cbn [negb] in H.
  destruct (swf (unlist_at (dropL G1') 1)) eqn:B6; [|discriminate]. cbn [negb] in H.
  destruct (apply_xforms (unlist_at (dropL G1') 1) XQ2) as [G3'|] eqn:EG3; [|discriminate].
  destruct (entailsA (axc G3') P_fps (post_sub G3') && wsub_id_below (post_sub G3') NF && negb (state_has_rl 5 G3') && negb (state_has_rl 6 G3')
            && sv_eqb (ax_base (ax_add_facts facts_fps F')) (SLit SHB) && (NF <=? ss_next (ax_S (ax_add_facts facts_fps F')))%positive
            && (ss_next G1' =? ss_next (ax_S (ax_add_facts facts_fps F')))%positive && (ss_next (unlist_at (dropL G1') 1) =? ss_next (ax_S (ax_add_facts facts_fps F')))%positive
            && (ss_next G3' =? ss_next (ax_S (ax_add_facts facts_fps F')))%positive) eqn:B7; [|discriminate].
  injection H as Eo. subst o. subst W S6 Cs s R T F0 F G1 G2 G2u G3 sp C Tf. cbn [ta_W ta_S6 ta_Cs ta_s ta_R ta_T ta_F ta_G1 ta_G2 ta_G2u ta_G3 ta_sp] in *.
  apply andb_prop in B1 as [B1 B1i]. apply andb_prop in B1 as [B1 B1h].
  apply andb_prop in B1 as [B1 B1g]. apply andb_prop in B1 as [B1 B1f]. apply andb_prop in B1 as [B1 B1e]. apply andb_prop in B1 as [B1 B1d].
  apply andb_prop in B1 as [B1 B1c]. apply andb_prop in B1 as [B1a B1b].
  apply andb_prop in B2 as [B2 B2g]. apply andb_prop in B2 as [B2 B2f]. apply andb_prop in B2 as [B2 B2e]. apply andb_prop in B2 as [B2 B2d].
  apply andb_prop in B2 as [B2 B2c]. apply andb_prop in B2 as [B2a B2b].
  apply Bool.orb_false_iff in B3 as [B3a B3b].
  apply andb_prop in B4 as [B4a B4b]. apply andb_prop in B5 as [B5a B5b].
  apply andb_prop in B7 as [B7 B7i]. apply andb_prop in B7 as [B7 B7h]. apply andb_prop in B7 as [B7 B7g]. apply andb_prop in B7 as [B7 B7f].
  apply andb_prop in B7 as [B7 B7e]. apply andb_prop in B7 as [B7 B7d]. apply andb_prop in B7 as [B7 B7c]. apply andb_prop in B7 as [B7a B7b].
  apply sv_eqb_sound in B1f. apply sv_eqb_sound in B1g. apply sv_eqb_sound in B2c. apply sv_eqb_sound in B2d. apply sv_eqb_sound in B7e.
  apply Pos.eqb_eq in B2e. apply Pos.eqb_eq in B2f. apply Pos.eqb_eq in B2g. apply Pos.leb_le in B7f. apply Pos.eqb_eq in B7g. apply Pos.eqb_eq in B7h. apply Pos.eqb_eq in B7i.
  apply Nat.eqb_eq in B4b. apply Nat.eqb_eq in B5b. apply sobj_eqb_sound in B4a. subst ob2. apply dflt_eqb_sound in B5a.
  apply Bool.negb_true_iff in B1b. apply Bool.negb_true_iff in B1c. apply Bool.negb_true_iff in B1e. apply Bool.negb_true_iff in B7c. apply Bool.negb_true_iff in B7d.
  apply Bool.negb_false_iff in B3b. apply Pos.leb_le in B3b.
  assert (Hc1 : ob_cells ob1 = []) by (destruct (ob_cells ob1); [reflexivity | cbn in B5b; lia]).
  exists o8, bl, ob1. repeat split; try assumption; try reflexivity.
Qed.

Lemma fb_facts : ltac2:(tb__ "0|0|
S0S6S7eS1aS23S35A1S4dA3S9A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fb_facts_le : ltac2:(tb__ "0|0|
S34S60S35R1A2S0S6S7eS1aS23R2A1S4dA3S9A3F_;Fm;").
Proof.
  intros m Hm. apply forallb_forall. intros p Hp. apply (sprop_below_mono NF); [exact Hm | exact (proj1 (forallb_forall _ _) fb_facts p Hp)].
Qed.
Lemma basef_holds : ltac2:(tb__ "0|0|
S18S38S1aS1dR1A1S4dA3S38S1aS1dR2A1S4eA3F_;Fr;").
Proof. intros r H. unfold facts_fps in H. exact (proj1 (proj1 (Forall_app _ _ _) H)). Qed.
Lemma fb_basef_le : ltac2:(tb__ "0|0|
S34S60S35R1A2S0S6S7eS1aS23R2A1S4eA3S9A3F_;Fm;").
Proof.
  intros m Hm. apply forallb_forall. intros p Hp. apply (proj1 (forallb_forall _ _) (fb_facts_le m Hm)). unfold facts_fps. apply in_app_iff. left. exact Hp.
Qed.

Lemma obj_to_list_ext : ltac2:(tb__ "0|1|
S1cS7S34S0S4S10S10S1eS1eA2S1eA2M0A1S36S17G0S42S21S97R3R2R1A3A1A4S36S17G0S42S21R3A1A4A3Fl;Fi;FS;").
Proof.
  intros S i l. unfold obj_to_list. destruct (nth_error (ss_objs S) i) as [ob|] eqn:Hnth; [|reflexivity].
  cbn [ss_objs set_objs].
  transitivity (map obj_ext (firstn i (ss_objs S) ++ ob :: skipn (Datatypes.S i) (ss_objs S))); [rewrite !map_app; reflexivity|].
  rewrite <- (nth_error_split3 _ _ _ Hnth). reflexivity.
Qed.

Lemma facts_rho_wl : ltac2:(tb__ "0|0|
S18S38S1aS1dR1A1S4dA3S38S1aS1dS77R2A1A1S4dA3F_;Fr;").
Proof.
  intros r H. apply Forall_forall. intros p Hp. pose proof (proj1 (Forall_forall _ _) H p Hp) as X.
  unfold facts_fps, str_facts in Hp. cbn [app] in Hp.
  repeat (destruct Hp as [<-|Hp]; [exact X|]). destruct Hp.
Qed.

Lemma W_facts : ltac2:(tb__ "0|0|
S4aS18S87S48S15R3VW;R2Vtp;R1A6S38S1aS1dR3A1S4dA3F_;Fw;FrhoW;FJ;").
Proof.
  intros J rhoW w Hsp. destruct cert as (o8 & bl & ob1 & _ & _ & Bf & _ & _).
  pose proof (SPA_facts_hold segs J rhoW W tp w Hsp) as HF.
  apply Forall_forall. intros p Hp. pose proof (proj1 (forallb_forall _ _) Bf p Hp) as E. cbn beta in E.
  apply existsb_exists in E as (q & Hq & Eq). apply sprop_eqb_sound in Eq. subst q. exact (proj1 (Forall_forall _ _) HF _ Hq).
Qed.

Lemma reshape : ltac2:(tb__ "0|1|
S7S18S87S0S4S12Q8A1A1S19R2P3M0A2S19Vrho;G0A2A3S48S15S3bR4A1VW;R3Vtp;R2A6S48S15S3bR5A1VC;S77R4A1Vtp;R3A6F_;F_;Fw;FrhoW;Fk;").
Proof.
  intros k rhoW w Hrl3 Hsp.
  destruct cert as (o8 & bl & ob1 & _ & _ & _ & _ & ES6 & Eo8 & Ebl & Bbl & Hrl5 & Hrl6 & Hw8 & Ha8 & Hlo & Hhi & Hx5 & Hx6 & ECs & _ & Hxok & _ & _ & HswfC & _ & _ & HnC & HnL & Hn6 & _).
  pose proof (splitsA_SPA _ _ W S6 rhoW tp w ES6 Hsp) as H6.
  unfold C. rewrite <- (ax_setS_twice W S6 Cs).
  unfold x_ok in Hxok. apply andb_prop in Hxok as [Hxok Hbase]. apply andb_prop in Hxok as [Hnorl Hxb]. apply sv_eqb_sound in Hbase.
  assert (Hbl : map (beval (rho_set_rl rhoW 6 [])) bl = M2).
  { apply bexps_eqb_sound in Bbl. rewrite Bbl. apply Hbl2. cbn [rl rho_set_rl]. exact Hrl3. }
  assert (Hlen0 : 0 <= len2) by lia.
  eapply (SPA_morphX (Kf k) (Kf k) (ax_setS W S6) Cs rhoW (rho_wl rhoW) tp w).
  - cbn [ax_X ax_base ax_setS]. rewrite Hxb, Hbase. reflexivity.
  - cbn [ax_base ax_setS]. rewrite Hbase. reflexivity.
  - cbn [ax_X ax_setS]. intros r Hr. pose proof (proj1 (forallb_forall _ _) Hnorl r Hr) as X0. unfold xr_norl in X0.
    apply Bool.negb_true_iff in X0. apply Bool.orb_false_iff in X0 as [X0 X4]. apply Bool.orb_false_iff in X0 as [X0 X3]. apply Bool.orb_false_iff in X0 as [X1 X2].
    unfold rho_wl. split; rewrite !SymCall.eval_set_rl by assumption; reflexivity.
  - cbn [ax_S ax_setS]. intros x Hout Hrm. split; [|reflexivity].
    rewrite ECs. unfold finish_fp. cbn [ss_objs app_obj]. apply outside_all_app_iff. split.
    + unfold rho_wl. apply (outside_all_exts_rl _ 5 M2 (ss_objs S6)); [apply obj_to_list_ext | exact Hx5 |].
      apply (outside_all_exts_rl rhoW 6 [] (ss_objs S6)); [reflexivity | exact Hx6 | exact Hout].
    + unfold outside_all. constructor; [|constructor]. cbn zeta. unfold obj_range, obj_lo_of, obj_hi_of, O_b2e; cbn [ob_base ob_lo ob_hi eval fst snd].
      rewrite !soff_lit_small by lia. lia.
  - intros Hsm. rewrite ECs. unfold finish_fp.
    pose proof (SymCall.smatch_set_rl segs rhoW 6 [] S6 (virt tp w) Hrl6 Hsm) as H5.
    pose proof (smatch_obj_to_list segs _ S6 (virt tp w) 3 5 o8 (-464) (-464 + len2) bl H5 Eo8 Hlo Hhi
                  ltac:(lia) ltac:(lia) Hw8 Ha8 ltac:(replace (Z.to_nat (-464 + len2 - -464)) with (Z.to_nat len2) by lia; exact Ebl) Hrl5) as H7.
    rewrite Hbl in H7. change (rho_set_rl (rho_set_rl rhoW 6 []) 5 M2) with (rho_wl rhoW) in H7.
    unfold app_obj, O_b2e.
    apply (smatch_carve_rom segs (rho_wl rhoW) (obj_to_list S6 3 5) (virt tp w) 0 0 6 (ss_next (obj_to_list S6 3 5)) H7).
    + rewrite ECs in HswfC. unfold finish_fp, app_obj, O_b2e in HswfC. exact HswfC.
    + lia. + lia. + lia.
    + reflexivity.
    + intros j Hj. exfalso. lia.
    + apply Forall_forall. intros ob _. unfold ranges_disjoint. cbn [fst snd]. lia.
  - intros HK. exact HK.
  - exact H6.
Qed.

Definition rho_fin (rho3 : valuation) (ms : machine_state) (md : Model) : valuation := ltac2:(tb__ "0|2|
S94S7cS7cS93Vrho3;SeS17S8dSbS17A1A3Sa1Vmd;Vtp;Vms;A3A3P5M0S19Vrho;G0A2A3P6M1S19Vrho;G1A2A3Vsp;A2").

Lemma split_last : ltac2:(tb__ "0|2|
S4S17A1M0S17S0S7S5S17R2A2U15A3S0SaS17A1S7fS17R3U14M1A3S8S17R2A2A3S0G0R4ScS17S37S17G1R4A3SeS17R3SbS17A1A3A3A3F_;F_;Fx;Fl;").
Proof.
  intros l x Hl Hnth. rewrite (nth_error_split3 l 20 x Hnth) at 1.
  replace (skipn 21 l) with (@nil sobj); [reflexivity|].
  symmetry. apply skipn_all2. lia.
Qed.

Lemma cleanup : ltac2:(tb__ "0|1|
S7S18S4S5aA1M0S8aS59S38S1aS1dR4A1S4dA3S48S15S3bR6A1VF0;R5Vtp;SfG0S8bR4S8cR3R2A2A4A6S48S15S3bR7A1S68S90R6R4R3A3Vtp;SfG0S8bR5S8cR4R3A2A4A6F_;F_;Fmd;Fms;Ftr;Frho3;Fk;").
Proof.
  intros k rho3 tr ms md HF3 Hsp0.
  destruct cert as (o8 & bl & ob1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                    & _ & EG1 & HG1b2 & HG1len & EG2 & Eob1 & Hob1d & Hob1c & EG2u & HswfG2u & EG3 & Esp & Hent & Hspid & Hg5 & Hg6 & HbF & HnF & HnG1 & HnG2u & HnG3).
  assert (EnF : ss_next (ax_S F) = ss_next (ax_S F0)) by (unfold F, ax_add_facts, add_facts, ax_setS; destruct F0 as [S0 X0 b0]; reflexivity).
  assert (Hsp : SPA segs (Kf k) F rho3 tp (tr, mkCfg ms md)).
  { destruct Hsp0 as [Hsm0 HK0]. split; [|exact HK0]. unfold F. apply smatchA_add_facts; [exact Hsm0 | exact HF3 | apply fb_facts_le; rewrite <- EnF; exact HnF]. }
  pose proof (SPA_x_sub segs (Kf k) rho3 F [] tp _ ltac:(intros r Hr; destruct Hr) Hsp) as H0.
  assert (E0 : ax_setX F [] = axc (ax_S F)) by (unfold ax_setX, axc; rewrite HbF; reflexivity). rewrite E0 in H0.
  assert (H1 : SPA segs (Kf k) (axc G1) rho3 tp (tr, mkCfg ms md)).
  { apply (SPA_morph (Kf k) (Kf k) (axc (ax_S F)) G1 rho3 rho3 tp _ eq_refl); [cbn [ax_base axc]; reflexivity | | intros HK; exact HK | exact H0].
    intros Hsm. exact (smatch_xforms segs XQ1 rho3 (ax_S F) G1 _ EG1 Hsm). }
  pose proof (SPA_unobj segs (Kf k) rho3 (axc G1) (firstn 20 (ss_objs G1)) [O_b2e] tp tr ms md
                (split_last _ _ HG1len HG1b2) H1 ltac:(intros HK; exact HK)) as H2.
  cbn zeta in H2. cbn [ax_S axc] in H2.
  assert (EG2' : set_objs G1 (firstn 20 (ss_objs G1)) = G2) by (rewrite EG2; unfold dropL; rewrite HG1len; reflexivity).
  rewrite EG2' in H2.
  set (rho4 := rho_absorb rho3 [O_b2e] (vms md tp ms)) in H2.
  change (ax_setS (axc G1) G2) with (axc G2) in H2.
  assert (H2u : SPA segs (Kf k) (axc G2u) rho4 tp (tr, mkCfg ms md)).
  { apply (SPA_morph (Kf k) (Kf k) (axc G2) G2u rho4 rho4 tp _ eq_refl); [cbn [ax_base axc]; reflexivity | | intros HK; exact HK | exact H2].
    intros Hsm. rewrite EG2u. eapply (smatch_unlist_at rho4 G2 1 ob1 5 _ Eob1 Hob1d Hob1c); [rewrite <- EG2u; exact HswfG2u | exact Hsm]. }
  assert (H3 : SPA segs (Kf k) (axc G3) rho4 tp (tr, mkCfg ms md)).
  { apply (SPA_morph (Kf k) (Kf k) (axc G2u) G3 rho4 rho4 tp _ eq_refl); [cbn [ax_base axc]; reflexivity | | intros HK; exact HK | exact H2u].
    intros Hsm. exact (smatch_xforms segs XQ2 rho4 G2u G3 _ EG3 Hsm). }
  set (rho5 := rho_set_rl (rho_set_rl rho4 5 (rl rho 5)) 6 (rl rho 6)).
  assert (H4 : SPA segs (Kf k) (axc G3) rho5 tp (tr, mkCfg ms md)).
  { apply (SPA_morph (Kf k) (Kf k) (axc G3) G3 rho4 rho5 tp _ eq_refl); [cbn [ax_base axc]; reflexivity | | intros HK; exact HK | exact H3].
    intros Hsm. unfold rho5. apply SymCall.smatch_set_rl; [exact Hg6|]. apply SymCall.smatch_set_rl; [exact Hg5|]. exact Hsm. }
  unfold rho_fin. fold rho4. fold rho5. destruct H4 as [Hsm4 HK4]. split; [| exact HK4].
  rewrite Esp. eapply smatchA_entails; [rewrite <- Esp; exact Hent | exact Hsm4].
Qed.

Lemma rho_fin_agree : ltac2:(tb__ "0|2|
S18S8aS59S34S61R1S35A2S0S12Q40A1M0S22R5R2A2S22Vrho;R2A2A3F_;Fi;S34S3S0S34R1P5A3A1S3S0S34R2P6A3A1S0S4S12Q8A1M1A1S19R7R3A2S19Vrho;R3A2A3F_;F_;Fl;G0S0SaG1A1S27R6R1A2S27Vrho;R1A2A3Fa;S20S35Vrho;S90R6R5R4A3A3F_;F_;F_;Fmd;Fms;Frho3;").
Proof.
  intros rho3 ms md Hrw Hrl Hrm.
  destruct cert as (o8 & bl & ob1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                    & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hspid & _).
  unfold rho_fin. split; [|split].
  - intros i Hi. cbn [rw rho_sub rho_set_rl rho_absorb]. rewrite (wsub_get_id sp NF i Hspid Hi). cbn. symmetry. apply Hrw. exact Hi.
  - intros l. cbn [rl rho_sub rho_set_rl rho_absorb].
    destruct (Pos.eqb_spec l 6) as [->|N6]; [reflexivity|]. destruct (Pos.eqb_spec l 5) as [->|N5]; [reflexivity|].
    symmetry. apply Hrl; assumption.
  - intros a. cbn [rm rho_sub rho_set_rl rho_absorb].
    destruct (in_ranges_dec rho3 [O_b2e] a) as [Hin|Hnin]; [| symmetry; apply Hrm].
    exfalso. destruct Hin as (ob & [<-|[]] & Hr). unfold obj_range, obj_lo_of, obj_hi_of, O_b2e in Hr. cbn [ob_base ob_lo ob_hi eval fst snd] in Hr.
    rewrite !soff_lit_small in Hr by lia. lia.
Qed.

Theorem post_sound : ltac2:(tb__ "0|0|
S18S20S35Vrho;R1A3S38S1aS1dR2A1S4dA3S86S15Vok;S48S15S3bVk0;A1VW0;R3Vtp;A5S49S15S3dS5S12Q8A1S3cA2A1S35Vrho;Vtp;S66A6A4F_;F_;FrhoW;").
Proof.
  intros rhoW HagW HFW.
  destruct cert as (o8 & bl & ob1 & EW0 & EW & _ & HnW & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Es & _ & Hefr & Hchk & _ & S13 & S15 & HnC & _ & _
                    & ET & HlTf & HnT & EF & _).
  destruct EW0 as (HpcW & HnW0). destruct (seg_run _ _ _ _ EF) as [HrunF HpcF].
  assert (HbW0 : forallb (sprop_below (ss_next (ax_S W0))) facts_fps = true) by (apply fb_facts_le; exact (Pos.le_trans _ _ _ HnT8 HnW0)).
  eapply triple_conseq with (P := SPA segs (Kf k0) W rhoW tp); [intros w Hw; exact (SPA_axforms segs _ XW rhoW (set_facts W0 facts_fps) W tp w EW (SPA_set_facts (Kf k0) W0 facts_fps rhoW tp w HFW HbW0 Hw)) | intros w Hw; exact Hw |].
  apply (triple_pre ok _ (Forall (holds rhoW) facts_fps)); [intros w Hw; exact (W_facts _ rhoW w Hw) | intros HF1].
  assert (Hrl3 : rl rhoW 3 = rl rho 3) by (destruct HagW as (_ & LW & _); rewrite <- (LW 3%positive); reflexivity).
  eapply triple_conseq with (P := SPA segs (Kf k0) C (rho_wl rhoW) tp); [intros w Hw; exact (reshape k0 rhoW w Hrl3 Hw) | intros w Hw; exact Hw |].
  apply (call_soundA segs ok (Kf k0) Jp (WLerr.Kw Jp M2 [] (length (WLerr.MSG M2 []))) (Kf (length MSGb)) C WLerrS.Pre_wl2 s R WLerr.Posts_wl _ (rho_wl rhoW) tp Hefr Hchk).
  - intros rho2 tp2. apply wl_call.
  - intros tr ms md Hsm [_ HK]. split; [| split; [reflexivity | exact HK]].
    unfold WLF. cbn [rl rw rho_sub rho_absorb]. rewrite S13, S15. cbn [eval rl rho_wl rho_set_rl].
    rewrite !lit_unsigned. rewrite !Z.mod_small by lia. repeat split; reflexivity.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HK'. apply Kw_Jp_Kf in HK'. rewrite wl_MSG_len, Lk in HK'. exact HK'.
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite <- ET.
    apply triple_SPA_pure. intros tr md [Et _]. subst tpL.
    apply (triple_SPA_conseq_J segs ok _ (Kf (length MSGb))); [intros t md0 (HJ & _ & _); exact HJ|].
    assert (HF' : Forall (holds rho') facts_fps).
    { apply Forall_forall. intros p Hp.
      apply (proj1 (holds_agree (ss_next (ax_S C)) (rho_wl rhoW) rho' p Hag'
               ltac:(unfold C; cbn [ax_S ax_setS]; rewrite HnC; apply (sprop_below_mono NF);
                       [unfold NF in *; lia | exact (proj1 (forallb_forall _ _) fb_facts p Hp)]))).
      exact (proj1 (Forall_forall _ _) (facts_rho_wl rhoW HF1) p Hp). }
    eapply triple_conseq with (P := SPA segs (Kf (length MSGb)) Tf rho' tp); [ | intros w Hw; exact Hw |].
    { intros w [Hsm HJ]. split; [|exact HJ]. unfold Tf. apply smatchA_add_facts; [exact Hsm | exact (basef_holds _ HF') | exact (fb_basef_le _ HnT)]. }
    eapply (runA_tr segs ok FUEL_T CUTS_FPS Tf _ (Kf (length MSGb)) rho' tp); [exact HrunF | exact HlTf | apply Kf_okK | apply Kf_stable |].
    intros L2 rho3 [<-|[]] Hag3. cbn [la_state].
    assert (Hn3 : ss_next (ax_S Tf) = ss_next (ax_S T)) by (unfold Tf, ax_add_facts, add_facts; destruct T as [ST XT bT]; reflexivity).
    rewrite Hn3 in Hag3.
    intros m Hg w [Hsm3 HK3]. destruct w as [tr3 [ms3 md3]].
    assert (HF3 : Forall (holds rho3) facts_fps).
    { apply Forall_forall. intros p Hp.
      apply (proj1 (holds_agree (ss_next (ax_S T)) rho' rho3 p Hag3 ltac:(apply (sprop_below_mono NF); [exact HnT | exact (proj1 (forallb_forall _ _) fb_facts p Hp)]))).
      exact (proj1 (Forall_forall _ _) HF' p Hp). }
    pose proof (cleanup (length MSGb) rho3 tr3 ms3 md3 HF3 (conj Hsm3 HK3)) as [HsmP HKP].
    assert (HagF : agree_below NF rho (rho_fin rho3 ms3 md3)).
    { destruct HagW as (AW & LW & MW). destruct Hag' as (A' & L' & M'). destruct Hag3 as (A3 & L3 & M3).
      unfold C in A'. cbn [ax_S ax_setS] in A'. rewrite HnC in A'.
      apply rho_fin_agree.
      - intros i Hi. rewrite <- (A3 i) by (unfold NF in *; lia). rewrite <- (A' i) by (unfold NF in *; lia).
        cbn [rw rho_wl rho_set_rl]. rewrite <- (AW i Hi). reflexivity.
      - intros l N5 N6. rewrite <- (L3 l), <- (L' l). cbn [rl rho_wl rho_set_rl].
        destruct (Pos.eqb_spec l 5) as [->|_]; [congruence|]. destruct (Pos.eqb_spec l 6) as [->|_]; [congruence|].
        rewrite <- (LW l). reflexivity.
      - intros a. rewrite <- (M3 a), <- (M' a). cbn [rm rho_wl rho_set_rl]. rewrite <- (MW a). reflexivity. }
    apply Hg.
    exists (mkLeafA P_fps RsCut), (rho_fin rho3 ms3 md3). split; [left; reflexivity|]. split; [exact HagF|].
    split; [exact HsmP|]. cbn [la_state w_tr w_cfg cfg_model]. destruct HKP as [_ (tr0 & HJ0 & ->)].
    exists tr0. split; [|reflexivity].
    eapply Hst0; [exact HagF | apply mat_equiv_refl | exact HJ0].
Qed.

Theorem post_sound_ex : ltac2:(tb__ "0|0|
S18S20S35Vrho;R1A3S38S1aS1dR2A1S4dA3S85S15S48S15S3bVk0;A1VW0;R3Vtp;A5S49S15S3dS5S12Q8A1S3cA2A1S35Vrho;Vtp;S66A6A3F_;F_;FrhoW;").
Proof.
  intros rhoW HagW HFW.
  destruct cert as (o8 & bl & ob1 & EW0 & EW & _ & HnW & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Es & _ & Hefr & Hchk & _ & S13 & S15 & HnC & _ & _
                    & ET & HlTf & HnT & EF & _).
  destruct EW0 as (HpcW & HnW0). destruct (seg_run _ _ _ _ EF) as [HrunF HpcF].
  assert (HbW0 : forallb (sprop_below (ss_next (ax_S W0))) facts_fps = true) by (apply fb_facts_le; exact (Pos.le_trans _ _ _ HnT8 HnW0)).
  eapply etriple_conseq with (P := SPA segs (Kf k0) W rhoW tp); [intros w Hw; exact (SPA_axforms segs _ XW rhoW (set_facts W0 facts_fps) W tp w EW (SPA_set_facts (Kf k0) W0 facts_fps rhoW tp w HFW HbW0 Hw)) | intros w Hw; exact Hw |].
  apply (etriple_pre _ (Forall (holds rhoW) facts_fps)); [intros w Hw; exact (W_facts _ rhoW w Hw) | intros HF1].
  assert (Hrl3 : rl rhoW 3 = rl rho 3) by (destruct HagW as (_ & LW & _); rewrite <- (LW 3%positive); reflexivity).
  eapply etriple_conseq with (P := SPA segs (Kf k0) C (rho_wl rhoW) tp); [intros w Hw; exact (reshape k0 rhoW w Hrl3 Hw) | intros w Hw; exact Hw |].
  apply (call_completeA segs (Kf k0) Jp (WLerr.Kw Jp M2 [] (length (WLerr.MSG M2 []))) (Kf (length MSGb)) C WLerrS.Pre_wl2 s R WLerr.Posts_wl _ (rho_wl rhoW) tp Hefr Hchk).
  - intros rho2 tp2. apply wl_call_ex.
  - intros tr ms md Hsm [_ HK]. split; [| split; [reflexivity | exact HK]].
    unfold WLF. cbn [rl rw rho_sub rho_absorb]. rewrite S13, S15. cbn [eval rl rho_wl rho_set_rl].
    rewrite !lit_unsigned. rewrite !Z.mod_small by lia. repeat split; reflexivity.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HK'. apply Kw_Jp_Kf in HK'. rewrite wl_MSG_len, Lk in HK'. exact HK'.
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite <- ET.
    intros w0 [Hsm0 [Et HK0]]. subst tpL. revert w0 Hsm0 HK0.
    assert (HF' : Forall (holds rho') facts_fps).
    { apply Forall_forall. intros p Hp.
      apply (proj1 (holds_agree (ss_next (ax_S C)) (rho_wl rhoW) rho' p Hag'
               ltac:(unfold C; cbn [ax_S ax_setS]; rewrite HnC; apply (sprop_below_mono NF);
                       [unfold NF in *; lia | exact (proj1 (forallb_forall _ _) fb_facts p Hp)]))).
      exact (proj1 (Forall_forall _ _) (facts_rho_wl rhoW HF1) p Hp). }
    assert (HE : etriple segs (SPA segs (Kf (length MSGb)) Tf rho' tp) (LQA segs (Kwr (length MSGb)) NF rho tp Posts_fps)).
    { eapply (erunA_tr segs FUEL_T CUTS_FPS Tf _ (Kf (length MSGb)) rho' tp); [exact HrunF | exact HlTf | apply Kf_stable |].
      intros L2 rho3 [<-|[]] Hag3. cbn [la_state].
      assert (Hn3 : ss_next (ax_S Tf) = ss_next (ax_S T)) by (unfold Tf, ax_add_facts, add_facts; destruct T as [ST XT bT]; reflexivity).
      rewrite Hn3 in Hag3.
      intros w [Hsm3 HK3]. destruct w as [tr3 [ms3 md3]]. exists (tr3, mkCfg ms3 md3). split; [apply wsteps_refl|].
      assert (HF3 : Forall (holds rho3) facts_fps).
      { apply Forall_forall. intros p Hp.
        apply (proj1 (holds_agree (ss_next (ax_S T)) rho' rho3 p Hag3 ltac:(apply (sprop_below_mono NF); [exact HnT | exact (proj1 (forallb_forall _ _) fb_facts p Hp)]))).
        exact (proj1 (Forall_forall _ _) HF' p Hp). }
      pose proof (cleanup (length MSGb) rho3 tr3 ms3 md3 HF3 (conj Hsm3 HK3)) as [HsmP HKP].
      assert (HagF : agree_below NF rho (rho_fin rho3 ms3 md3)).
      { destruct HagW as (AW & LW & MW). destruct Hag' as (A' & L' & M'). destruct Hag3 as (A3 & L3 & M3).
        unfold C in A'. cbn [ax_S ax_setS] in A'. rewrite HnC in A'.
        apply rho_fin_agree.
        - intros i Hi. rewrite <- (A3 i) by (unfold NF in *; lia). rewrite <- (A' i) by (unfold NF in *; lia).
          cbn [rw rho_wl rho_set_rl]. rewrite <- (AW i Hi). reflexivity.
        - intros l N5 N6. rewrite <- (L3 l), <- (L' l). cbn [rl rho_wl rho_set_rl].
          destruct (Pos.eqb_spec l 5) as [->|_]; [congruence|]. destruct (Pos.eqb_spec l 6) as [->|_]; [congruence|].
          rewrite <- (LW l). reflexivity.
        - intros a. rewrite <- (M3 a), <- (M' a). cbn [rm rho_wl rho_set_rl]. rewrite <- (MW a). reflexivity. }
      exists (mkLeafA P_fps RsCut), (rho_fin rho3 ms3 md3). split; [left; reflexivity|]. split; [exact HagF|].
      split; [exact HsmP|]. cbn [la_state w_tr w_cfg cfg_model]. destruct HKP as [_ (tr0 & HJ0 & ->)].
      exists tr0. split; [|reflexivity].
      eapply Hst0; [exact HagF | apply mat_equiv_refl | exact HJ0]. }
    intros w0 Hsm0 HK0. apply HE. split; [| split; [reflexivity | exact HK0]].
    unfold Tf. apply smatchA_add_facts; [exact Hsm0 | exact (basef_holds _ HF') | exact (fb_basef_le _ HnT)].
Qed.
End Inst.
End Post.

Section InstA.
Variables n len : Z.
Hypothesis Hn : ltac2:(tb__ "0|0|
S0S33Vn;S62S5S12Q8A1Vstr;A2A1A3").
Hypothesis Hlen_eq : ltac2:(tb__ "0|0|
S0S33Vlen;S63S63S62S5S33Vpre;A2A1Vn;A2S62S5S33Vsuf;A2A1A2A3").
Hypothesis Hlen : len <= 80.
Hypothesis Hpre1 : (1 <= length pre)%nat.
Variable LFs : list (list sprop).
Variable T8 : axst.
Variable o : tailA_out.
Hypothesis Hcert : ltac2:(tb__ "0|0|
S0SaS65A1S74VLFs;Vpre;Vsuf;Vn;Vlen;VT8;A6S8S65Vo;A2A3").
Hypothesis HlT8 : ltac2:(tb__ "0|0|
S0S6S28S40VT8;A1A1SdA3").
Hypothesis HnT8 : ltac2:(tb__ "0|0|
S60S35S1bS40VT8;A1A1A2").

Lemma certA : ltac2:(tb__ "0|2|
S2S3fS3fS1S0S6S4fVLFs;S40VT8;A1M0A2S9A3S1S0S6S4fSeS4S1aA1M1S4dSbG1A1A3G0A2S9A3S1S0SaS3fA1S52VLFs;VT8;A2S8S3fR1A2A3S0SaS65A1S6cVpre;Vsuf;Vn;Vlen;VT8;R1A6S8S65Vo;A2A3A2A2A2LW0;A2").
Proof.
  pose proof Hcert as H. unfold tailA in H.
  destruct (len =? Z.of_nat (length pre) + n + Z.of_nat (length suf)) eqn:B0; [|discriminate]. cbn [negb] in H.
  destruct (fs_ok LFs (ax_S T8) && fs_ok [facts_fps] (ax_S T8)) eqn:BL; [|discriminate]. cbn [negb] in H. apply andb_prop in BL as [BL BL2].
  destruct (runp LFs T8) as [W0|] eqn:EW0; [|discriminate].
  exists W0. repeat split; try assumption.
Qed.
Lemma HM0 : ltac2:(tb__ "0|1|
S0S4S12Q8A1M0A1S3cScG0SbG0A1S3cA3A3"). Proof. reflexivity. Qed.
Lemma HlenM : ltac2:(tb__ "0|0|
S0S33Vlen;S62S5S12Q8A1S3cA2A1A3"). Proof. rewrite MSGb_len, Hlen_eq, Hn. lia. Qed.
Lemma Hlen80 : 1 <= len <= 80. Proof. pose proof Hlen. rewrite Hlen_eq, Hn in *. lia. Qed.
Lemma Hbl0 : ltac2:(tb__ "0|3|
S18S0S4S12Q8A1M0A1M1S19R1P3M2A2S19Vrho;G2A2A3S0G1S36S54G0S55R2A1S67Vpre;Vn;Vsuf;A3A4S3cA3F_;Fr;").
Proof. intros r Hr3. rewrite Hn. unfold MSGb. apply blA_val. rewrite Hr3. exact Hstr. Qed.

Theorem tailA_sound : ltac2:(tb__ "0|0|
S18S20S35Vrho;R1A3S86S15Vok;S48S15S3bU0A1VT8;R2Vtp;A5S49S15S3dS5S12Q8A1S3cA2A1S35Vrho;Vtp;S66A6A4F_;Frho7;").
Proof.
  intros rho7 Hag7. destruct certA as (W0 & HLok & HLf & EW0 & HP).
  apply (triple_pre ok _ (FsHold rho7 LFs /\ FsBelow (ss_next (ax_S T8)) LFs = true)); [intros w Hw; exact (fs_ok_sound _ LFs T8 rho7 tp w HLok Hw) | intros [HF0 HLb]].
  apply (triple_pre ok _ (FsHold rho7 [facts_fps] /\ FsBelow (ss_next (ax_S T8)) [facts_fps] = true)); [intros w Hw; exact (fs_ok_sound _ [facts_fps] T8 rho7 tp w HLf Hw) | intros [HFf0 HLfb]].
  eapply (runp_tr ok (Kf 0) (Kf_stable 0) LFs T8 W0 rho7 tp); [exact EW0 | exact HlT8 | apply Kf_okK | exact HF0 | exact HLb |].
  intros rhoW HagW.
  assert (HFW : Forall (holds rhoW) facts_fps) by (exact (Forall_inv (FsHold_agree _ rho7 rhoW [facts_fps] HagW HLfb HFf0))).
  apply (post_sound 0 [] MSGb len pre suf n HM0 eq_refl HlenM Hlen80 Hbl0 T8 W0 o HP HnT8 rhoW); [|exact HFW].
  eapply agree_below_trans; [exact Hag7 | exact (agree_below_le _ _ _ _ HnT8 HagW)].
Qed.

Theorem tailA_sound_ex : ltac2:(tb__ "0|0|
S18S20S35Vrho;R1A3S85S15S48S15S3bU0A1VT8;R2Vtp;A5S49S15S3dS5S12Q8A1S3cA2A1S35Vrho;Vtp;S66A6A3F_;Frho7;").
Proof.
  intros rho7 Hag7. destruct certA as (W0 & HLok & HLf & EW0 & HP).
  apply (etriple_pre _ (FsHold rho7 LFs /\ FsBelow (ss_next (ax_S T8)) LFs = true)); [intros w Hw; exact (fs_ok_sound _ LFs T8 rho7 tp w HLok Hw) | intros [HF0 HLb]].
  apply (etriple_pre _ (FsHold rho7 [facts_fps] /\ FsBelow (ss_next (ax_S T8)) [facts_fps] = true)); [intros w Hw; exact (fs_ok_sound _ [facts_fps] T8 rho7 tp w HLf Hw) | intros [HFf0 HLfb]].
  eapply (runp_etr (Kf 0) (Kf_stable 0) LFs T8 W0 rho7 tp); [exact EW0 | exact HlT8 | exact HF0 | exact HLb |].
  intros rhoW HagW.
  assert (HFW : Forall (holds rhoW) facts_fps) by (exact (Forall_inv (FsHold_agree _ rho7 rhoW [facts_fps] HagW HLfb HFf0))).
  apply (post_sound_ex 0 [] MSGb len pre suf n HM0 eq_refl HlenM Hlen80 Hbl0 T8 W0 o HP HnT8 rhoW); [|exact HFW].
  eapply agree_below_trans; [exact Hag7 | exact (agree_below_le _ _ _ _ HnT8 HagW)].
Qed.
End InstA.
End TailA.

End Fps_tailA.

(* [comment removed for export] *)
Module FpsC_a5.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nat"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsC_st"; "T7s"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail"; "FPA"; "FQA"; "PRE_C"; "SUF_NL"; "T8"; "tailA_n"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "factsS"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsC_st.
Import ListNotations.
Open Scope Z_scope.

Lemma okA_5 : ltac2:(tb__ "0|0|
S7S2S11S0S0SfSaR1S6A2S0SbR2R1S6A3Lr;ScSdR1S12Z12R1A2S0SeZ11R2R1S10S6A5Lr;S1S0Z0S1S0Z1S1S0Z2S1S0Z3S4S0A1A3A3A3A3A8Ln;S8S3S0S13S9U28U8A2A4A3S5A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End FpsC_a5.

(* [comment removed for export] *)
Module FpsC_a6.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nat"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsC_st"; "T7s"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail"; "FPA"; "FQA"; "PRE_C"; "SUF_NL"; "T8"; "tailA_n"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "factsS"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsC_st.
Import ListNotations.
Open Scope Z_scope.

Lemma okA_6 : ltac2:(tb__ "0|0|
S7S2S11S0S0SfSaR1S6A2S0SbR2R1S6A3Lr;ScSdR1S12Z12R1A2S0SeZ11R2R1S10S6A5Lr;S1S0Z0S1S0Z1S1S0Z2S1S0Z3S4S0A1A3A3A3A3A8Ln;S8S3S0S13S9U30U8A2A4A3S5A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End FpsC_a6.

(* [comment removed for export] *)
Module FpsC_a7.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nat"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsC_st"; "T7s"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail"; "FPA"; "FQA"; "PRE_C"; "SUF_NL"; "T8"; "tailA_n"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "factsS"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.FpsC_st.
Import ListNotations.
Open Scope Z_scope.

Lemma okA_7 : ltac2:(tb__ "0|0|
S7S2S11S0S0SfSaR1S6A2S0SbR2R1S6A3Lr;ScSdR1S12Z12R1A2S0SeZ11R2R1S10S6A5Lr;S1S0Z0S1S0Z1S1S0Z2S1S0Z3S4S0A1A3A3A3A3A8Ln;S8S3S0S13S9U38U7A2A4A3S5A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End FpsC_a7.

(* [comment removed for export] *)
Module Lib_handle_l_chk0.

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SummaryA EntailA CFGA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.JcertCutA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_l Lib_handle_l_s2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import HLAddr.

Abbreviation TG := (etargets cutsL exitsL).
Abbreviation PE := (eecheckJA NPH (cutsL ++ exitsL)).
Abbreviation CC i T := (cut_okE segs FUEL_hl cutpcs_hl NPH PE i T TG).
End Lib_handle_l_chk0.

