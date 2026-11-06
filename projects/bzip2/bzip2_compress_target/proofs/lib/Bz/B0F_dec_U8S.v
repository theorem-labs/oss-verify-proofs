(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts DecCut DecTac DecTac2 DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU8 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU8 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFB DecTacFB DecTacFRB B0F_decV B0F_decRet B0F_decCutsM B0F_decCuts8 B0F_dec_U8A B0F_dec_U8B B0F_dec_U8C.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCutsM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts8 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_dec_U8A OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_dec_U8B OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_dec_U8C.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast FLiaA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= FLiaA.lia_f.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecTac2.
Local Ltac AsanKit.a_norm ::= DecTac2.lit_store_fix.

Section ACeilS1. Context {ACEIL__ : ACeil}.
(* [comment removed for export] *)
Lemma dinv_HRUN_start : forall L d, dinv_SYM L d -> (sv_nextSym L <= 1)%Z -> dinv_HRUN (sv_set_N (sv_set_es L (-1)) 1) d.
Proof.
  intros L d [ML NS] H. unfold dinv_HRUN. split; [| Lsplit L; split; [lia | apply run_okF_init]].
  apply (dinv_ML_keep L _ d d ML); [destruct L; unfold Lkeep; cbn; repeat split; reflexivity|].
  destruct d; unfold dkeep; cbn; repeat split; try reflexivity.
  destruct ML as [AL _]. unfold alpha_ok in AL. cbn in AL. lia.
Qed.
Lemma dinv_HLIT_start : forall L d, dinv_SYM L d -> sv_nextSym L <> sv_EOB L -> (1 < sv_nextSym L)%Z -> dinv_HLIT L d.
Proof.
  intros L d [ML NS] H1 H2. pose proof (dinv_ML_alpha L d ML) as [AL EOB]. unfold dinv_HLIT. split; [exact ML| lia].
Qed.
Lemma dinv_HEOB_start : forall L d, dinv_SYM L d -> sv_nextSym L = sv_EOB L -> dinv_HEOB L d.
Proof. intros L d [ML NS] H. split; [exact ML | exact H]. Qed.

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok BIHI0 A.
  Hypothesis ASH : act_sh DI_B0 A.
  Variable Q : dres -> machine_state -> Prop.
  Variable F : nat.
  Hypothesis HEOB : B0F_cut_HEOB A Q F.
  Hypothesis HLIT : B0F_cut_HLIT A Q F.
  Hypothesis HRUN : B0F_cut_HRUN A Q F.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Lemma B0F_dec_U8S' : B0F_cut_SYM A Q F.
  Proof.
    unfold B0F_cut_SYM. intros until w752. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    pose proof DI as DI'. destruct DI' as [ML NS]. pose proof (dinv_ML_alpha _ _ ML) as [AL15 EOB15].
    pose proof ML as X; cps_destruct X as (ALK & GRP & TABS & MTF & BLKF & CUR). pose proof (proj1 BLKF) as NB15.
    unfold grp_okF in GRP; unfold alpha_ok in ALK. pose proof (dpureF_n _ _ _ _ _ _ DP) as BN.
    open_dmemF DM. b0img. kq_intro.
    unfold r_of in DR. dr_open. hide_all_but_atF [a_P A; a_P A + 344]%Z.
    pose proof (munch_refl [(a_P A + 344, a_P A + 760)]%Z m) as MUL. pose proof (wmono_refl b0segs m) as WML.
    (* [comment removed for export] *)
    brun; if_cases KE; zify_cond_z KE.
    { rewrite (K_SYM_eob F L d s) in KQ by lia.
      revive_all MUL WML AOK. enter_sameF HEOB DP. apply dinv_HEOB_start; [exact DI | lia]. }
    (* [comment removed for export] *)
    brun; if_cases KL; zify_cond_z KL.
    { rewrite (K_SYM_lit F L d s) in KQ by lia.
      revive_all MUL WML AOK. enter_sameF HLIT DP. apply dinv_HLIT_start; [exact DI | lia | lia]. }
    (* [comment removed for export] *)
    brun_to 0xb4aac%Z.
    rewrite (K_SYM_run F L d s) in KQ by lia.
    revive_all MUL WML AOK. enter_sameF HRUN DP. apply dinv_HRUN_start; [exact DI | lia].
  Qed.
End R.

(* [comment removed for export] *)
Lemma B0F_dec_U8 : forall A, act_ok BIHI0 A -> act_sh DI_B0 A -> forall Q, B0F_RET_OK A Q -> B0F_RET A Q -> forall F,
  (forall F', (F' < F)%nat -> B0F_cut_SYM A Q F') ->
  (forall F', (F' < F)%nat -> B0F_cut_HRUN A Q F') ->
  (forall F', (F' < F)%nat -> B0F_cut_HRUNEND A Q F') ->
  B0F_cut_HEOB A Q F ->
  (B0F_cut_HMTFC A Q F -> B0F_cut_HLIT A Q F) ->
  (B0F_cut_HMTFB A Q F -> B0F_cut_HRUN A Q F) ->
  (B0F_cut_SYM A Q F -> B0F_cut_HRUNEND A Q F) ->
  B0F_cut_HMTFC A Q F /\ B0F_cut_HLIT A Q F /\ B0F_cut_HMTFB A Q F /\ B0F_cut_HRUN A Q F /\
  B0F_cut_SYM A Q F /\ B0F_cut_HRUNEND A Q F /\ B0F_cut_HMTF1 A Q F.
Proof.
  intros A AOK ASH Q HOK HP2 F HS HR HN HE U10 U9a U9b.
  pose proof (B0F_dec_U8C.B0F_dec_U8C A AOK ASH Q HOK HP2 F HS) as C. pose proof (U10 C) as L.
  pose proof (B0F_dec_U8B.B0F_dec_U8B A AOK ASH Q HOK HP2 F HR HN) as B. pose proof (U9a B) as R.
  pose proof (B0F_dec_U8S' A AOK ASH Q F HE L R) as Y. pose proof (U9b Y) as N.
  pose proof (B0F_dec_U8A.B0F_dec_U8A A AOK ASH Q HOK HP2 F HS) as M1.
  repeat split; assumption.
Qed.
End ACeilS1.
