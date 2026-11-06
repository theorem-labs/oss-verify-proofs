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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU6 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFB DecTacFB DecTacFRB B0F_decV B0F_decRet B0F_decCuts5 B0F_decCuts6 B0F_gb_D B0F_gb_E.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_gb_D OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_gb_E.
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

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac.DecAuxB.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok BIHI0 A.
  Hypothesis ASH : act_sh DI_B0 A.
  Variable Q : dres -> machine_state -> Prop.
  Hypothesis HRETOK : B0F_RET_OK A Q.
  Hypothesis HRETD : B0F_RET_DATA A Q.
  Variable F : nat.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  (* [comment removed for export] *)
  Lemma B0F_U6_W :
    (forall F', (F' < F)%nat -> B0F_cut_L6W A Q F') -> (forall F', (F' < F)%nat -> B0F_cut_HCOD A Q F') ->
    B0F_cut_L6W A Q F.
  Proof.
    intros HW HT. unfold B0F_cut_L6W. intros until w752. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    cps_destruct DI as (SEL & Ht & Hi & Hc & LOK). pose proof SEL as SEL'. cps_destruct SEL' as ((AL & NBL) & NG & NSC & SOK).
    pose proof AL as AL'. cps_destruct AL' as (_ & _ & _ & _ & _ & NS2).
    open_dmemF DM. b0img. kq_intro.
    unfold r_of in DR. dr_open. hide_all_but_atF [S; a_P A; a_P A + 344]%Z.
    pose proof (munch_refl [(a_P A + 344, a_P A + 760)]%Z m) as MUL. pose proof (wmono_refl b0segs m) as WML.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    brun; if_cases KC; zify_cond KC.
    2: { assert (HC' : (sv_curr L < 1 \/ 20 < sv_curr L)%Z).
      { destruct (Z_lt_le_dec (sv_curr L + -21) 0) as [Lc|Lc].
        - rewrite (land64_neg (sv_curr L + -21)) in KC by lia. lia.
        - rewrite (land64_small (sv_curr L + -21)) in KC by lia. lia. }
      rewrite K_L6W_ret in KQ by exact HC'.
      (* [comment removed for export] *)
      brun_to 0xafb8c%Z.
      revive_all MUL WML AOK.
      kq_fold. enter_cutF (HRETD _ _ _ JK_) DP; [ ret_nb | apply dpost14_ne; exact NS2 ]. }
    assert (HC' : (1 <= sv_curr L <= 20)%Z).
    { destruct (Z_lt_le_dec (sv_curr L + -21) 0) as [Lc|Lc].
      - rewrite (land64_neg (sv_curr L + -21)) in KC by lia. lia.
      - rewrite (land64_small (sv_curr L + -21)) in KC by lia. lia. }
    clear KC. rewrite K_L6W_go in KQ by exact HC'.
    (* [comment removed for export] *)
    brun_to 0xb1de4%Z.
    gbF_call (B0F_gb_b1b20 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU.
    gbF_nextA [S; S + 43888; a_P A; a_P A + 344]%Z [(S, S + 68); (S + 43888, S + 45436); (a_P A + 344, a_P A + 760)]%Z.
    dr_open. hide_all_but_atF [S; S + 43888; a_P A; a_P A + 344]%Z.
    arun_lwbuf. arun_gbv 1%Z ub.
    (* [comment removed for export] *)
    brun; if_cases Kbit; zify_cond_z Kbit.
    - (* [comment removed for export] *)
      rewrite (edge_34_0 _ ub) in KQ by (unset_Z; lia). kq_norm.
      brun_to 0xb22a0%Z.
      lazymatch goal with H : u8arr _ _ (S + 43888)%Z _ |- _ =>
        zb8_sb H (258 * sv_t L + sv_i L)%Z; try rewrite (Z.mod_small (sv_curr L) 256) in H by lia end.
      assert (Ht0 : (0 <= sv_t L)%Z) by lia. assert (Ha : (sv_alphaSize L <= 258)%Z) by lia.
      pose proof (lenp_ok_upd _ _ _ _ _ Ht0 Hi Ha HC' LOK) as LOK'.
      (* [comment removed for export] *)
      brun; if_cases KI; zify_cond_z KI.
      + (* [comment removed for export] *)
        rewrite (@if_trueP _ (_ <? sv_alphaSize L)%Z) in KQ by blia.
        revive_all MUL WML AOK. enter_nextF HW DP.
        unfold dinv_L6W, sel_okF, alpha_ok in *. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try (unset_Z; lia).
        exact SOK. exact LOK'.
      + (* [comment removed for export] *)
        rewrite (@if_falseP _ (_ <? sv_alphaSize L)%Z) in KQ by blia.
        brun_to 0xb0f3c%Z.
        revive_all MUL WML AOK. enter_nextF HT DP.
        unfold dinv_HCOD, alpha_ok in *. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try (unset_Z; lia).
        exact SOK.
        intros t' i' Ht' Hi'. apply (LOK' t' i'); lia.
    - (* [comment removed for export] *)
      rewrite (edge_34_1 _ ub) in KQ by (unset_Z; lia).
      gbF_call (B0F_gb_b1b8c A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU.
      gbF_nextA [S; a_P A; a_P A + 344]%Z [(S, S + 68)]%Z.
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      arun_lwbuf. arun_gbv 1%Z ub2.
      rewrite edge_35 in KQ.
      brun; if_cases Kb2; zify_cond_z Kb2.
      + (* [comment removed for export] *)
        rewrite (@if_trueP _ (ub2 =? 0)%Z) in KQ by blia.
        brun_to 0xb1dd0%Z.
        revive_all MUL WML AOK. enter_nextF HW DP.
        unfold dinv_L6W, sel_okF, alpha_ok in *. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try (unset_Z; lia).
        exact SOK. exact LOK.
      + (* [comment removed for export] *)
        rewrite (@if_falseP _ (ub2 =? 0)%Z) in KQ by blia.
        brun_to 0xb1dd0%Z.
        revive_all MUL WML AOK. enter_nextF HW DP.
        unfold dinv_L6W, sel_okF, alpha_ok in *. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try (unset_Z; lia).
        exact SOK. exact LOK.
  Qed.

  (* [comment removed for export] *)
  Lemma B0F_U6_T : (forall F', (F' < F)%nat -> B0F_cut_L6W A Q F') -> B0F_cut_HHB A Q F -> B0F_cut_HCOD A Q F.
  Proof.
    intros HW HHB. unfold B0F_cut_HCOD. intros until w752. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    pose proof DI as DI'. cps_destruct DI' as ((AL & NBL) & NG & NSC & SOK & Ht & LOK).
    open_dmemF DM. b0img. kq_intro.
    unfold r_of in DR. dr_open. hide_all_but_atF [S; a_P A; a_P A + 344]%Z.
    pose proof (munch_refl [(a_P A + 344, a_P A + 760)]%Z m) as MUL. pose proof (wmono_refl b0segs m) as WML.
    destruct (Z_lt_le_dec (sv_t L) (sv_nGroups L)) as [LT|GE].
    - rewrite K_HCOD_go in KQ by exact LT.
      (* [comment removed for export] *)
      brun. if_cases KX; zify_cond_z KX; [exfalso; lia|].
      brun_to 0xb0f4c%Z.
      gbF_call (B0F_gb_b0c88 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU.
      gbF_nextA [S; a_P A; a_P A + 344]%Z [(S, S + 68); (a_P A + 344, a_P A + 760)]%Z.   (* [comment removed for export] *)
      arun_lwbuf. arun_gbv 5%Z curr.
      rewrite edge_33 in KQ.
      (* [comment removed for export] *)
      brun. if_cases KA; zify_cond_z KA; [|exfalso; unfold alpha_ok in AL; lia].
      revive_all MUL WML AOK. enter_nextF HW DP.
      unfold dinv_L6W, sel_okF, alpha_ok in *. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try (unset_Z; lia).
      exact SOK. apply lenp_ok_of_rows. intros t' i' Ht' Hi'. apply LOK; lia.
    - rewrite K_HCOD_exit in KQ by exact GE.
      brun. if_cases KX; zify_cond_z KX; [|exfalso; lia].
      revive_all MUL WML AOK.
      enter_sameF HHB DP.
      unfold dinv_HHB, sel_okF, alpha_ok in *. repeat match goal with |- _ /\ _ => split end; try lia.
      exact SOK. intros t' i' Ht' Hi'. apply LOK; lia.
  Qed.
End R.
End ACeilS1.
