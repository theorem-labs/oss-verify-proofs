(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzContracts BzContracts0 DecCut DecTac DecTac2 DecAux.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_dec_U13.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAux OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac.DecAuxB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_dec_U13.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU6. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR S0F_decRet S0F_decCuts S0F_decCuts6.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require U0_gbF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require U0_gbF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU6 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts6 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.U0_gbF.S0F_gb_J OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.U0_gbF.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecFast DecFastT.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacFR BzImg0Tac.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Lemma pm1_bit : forall r,
  Z.lor (Z.land (bv_signed (Z_to_bv 64 (Z.land r 18446744073709551615 * 9223372036854775808)) / 9223372036854775808)
                18446744073709551615) 1
  = (if (Z.land (Z.land r 18446744073709551615) 1 =? 0)%Z then 1%Z else 18446744073709551615%Z).
Proof.
  intros r.
  set (u := Z.land r 18446744073709551615).
  assert (Hu : (0 <= u < 18446744073709551616)%Z).
  { subst u. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  change 1%Z with (Z.ones 1) at 2. rewrite (Z.land_ones u 1) by lia. change (2 ^ 1)%Z with 2%Z.
  rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64 `div` 2)%Z with 9223372036854775808%Z. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  destruct (Z.Even_or_Odd u) as [[k ->]|[k ->]].
  - replace (2 * k * 9223372036854775808 + 9223372036854775808)%Z with (9223372036854775808 + k * 18446744073709551616)%Z by lia.
    rewrite Z_mod_plus_full. rewrite Z.mod_small by lia.
    replace ((2 * k) mod 2)%Z with 0%Z by (symmetry; rewrite Z.mul_comm; apply Z_mod_mult). reflexivity.
  - replace ((2 * k + 1) * 9223372036854775808 + 9223372036854775808)%Z with (0 + (k + 1) * 18446744073709551616)%Z by lia.
    rewrite Z_mod_plus_full. rewrite Z.mod_0_l by lia.
    replace ((2 * k + 1) mod 2)%Z with 1%Z; [reflexivity|].
    symmetry. rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full. reflexivity.
Qed.

Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Ltac prep DM MU :=
    unfold W14, D14, DSTATE_SIZE in MU; cbn [app blk_ivls b_s b_strm] in MU; open_dmemF DM; s2img.

  (* [comment removed for export] *)
  Lemma S0F_U6_W :
    (forall F', (F' < F)%nat -> S0F_cut_L6W A F') -> (forall F', (F' < F)%nat -> S0F_cut_L6T A F') ->
    S0F_cut_L6W A F.
  Proof.
    intros HW HT. unfold S0F_cut_L6W. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    cps_destruct DI as (SEL & Ht & Hi & Hc & LOK). pose proof SEL as SEL'. cps_destruct SEL' as ((AL & NBL) & NG & NSC & SOK).
    pose proof AL as AL'. cps_destruct AL' as (_ & _ & _ & _ & _ & NS2).
    prep DM MU. kq_intro.
    hide_all_but_at [S; usp + -336]%Z.
    pose proof (munch_refl [(usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    (* [comment removed for export] *)
    wstepl. wstepl. wstepl.
    wstepl; if_cases KC; zify_cond KC.
    { assert (HC' : (sv_curr L < 1 \/ 20 < sv_curr L)%Z).
      { destruct (Z_lt_le_dec (sv_curr L + -21) 0) as [Lc|Lc].
        - rewrite (land64_neg (sv_curr L + -21)) in KC by lia. lia.
        - rewrite (land64_small (sv_curr L + -21)) in KC by lia. lia. }
      rewrite K_L6W_ret in KQ by exact HC'.
      revive_all MUL WML AOK. kq_fold. enter_cutF (S0F_dec_ret_data A AOK _ _ _ JK_) DP; [ ret_nb | apply dpost14_ne; exact NS2 ]. }
    assert (HC' : (1 <= sv_curr L <= 20)%Z).
    { destruct (Z_lt_le_dec (sv_curr L + -21) 0) as [Lc|Lc].
      - rewrite (land64_neg (sv_curr L + -21)) in KC by lia. lia.
      - rewrite (land64_small (sv_curr L + -21)) in KC by lia. lia. }
    clear KC. rewrite K_L6W_go in KQ by exact HC'.
    (* [comment removed for export] *)
    gbF_call (S0F_gb_1e014 A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MUL WML AOK DP FU.
    gbF_next [S; S + 43888; usp + -336]%Z [(S, S + 68); (S + 43888, S + 45436); (usp + -336, usp)]%Z.
    dr_open. hide_all_but_at [S; S + 43888; usp + -336]%Z.
    (* [comment removed for export] *)
    wstepl. wstepl. gbv 11%Z 1%Z ub. wstepl.
    wstepl; if_cases Kbit; zify_cond_z Kbit.
    - (* [comment removed for export] *)
      rewrite (edge_34_0 _ ub) in KQ by (unset_Z; lia). kq_norm.
      wstepl. wstepl. wstepl. notrap.
      wstepl. wstepl. wstepl. wstepl. wstepl. wstepl. wstepl. wstepl. notrap.
      wstepl. wstepl. notrap.
      wstepl. wstepl. wstepl. notrap.
      wstepl. wstepl. wstepl. wstepl. wstepl. wstepl.
      lazymatch goal with H : u8arr _ _ (S + 43888)%Z _ |- _ =>
        zb8_sb H (258 * sv_t L + sv_i L)%Z; try rewrite (Z.mod_small (sv_curr L) 256) in H by lia end.
      assert (Ht0 : (0 <= sv_t L)%Z) by lia. assert (Ha : (sv_alphaSize L <= 258)%Z) by lia.
      pose proof (lenp_ok_upd _ _ _ _ _ Ht0 Hi Ha HC' LOK) as LOK'.
      (* [comment removed for export] *)
      wstepl.
      wstepl; if_cases KI; zify_cond_z KI.
      + (* [comment removed for export] *)
        rewrite (@if_trueP _ (_ <? sv_alphaSize L)%Z) in KQ by blia.
        revive_all MUL WML AOK. enter_nextF HW DP.
        unfold dinv_L6W, sel_okF, alpha_ok in *. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try (unset_Z; lia).
        exact SOK. exact LOK'.
      + (* [comment removed for export] *)
        rewrite (@if_falseP _ (_ <? sv_alphaSize L)%Z) in KQ by blia.
        wstepl. wstepl. wstepl. wstepl. notrap.
        revive_all MUL WML AOK. enter_nextF HT DP.
        unfold dinv_HCOD, alpha_ok in *. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try (unset_Z; lia).
        exact SOK.
        intros t' i' Ht' Hi'. apply (LOK' t' i'); lia.
    - (* [comment removed for export] *)
      rewrite (edge_34_1 _ ub) in KQ by (unset_Z; lia).
      revive_all MUL WML AOK.
      gbF_call (S0F_gb_1df6c A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MUL WML AOK DP FU.
      gbF_next [S; usp + -336]%Z [(S, S + 68)]%Z.
      (* [comment removed for export] *)
      wstepl. wstepl. gbv 11%Z 1%Z ub2. wstepl.
      rewrite edge_35 in KQ.
      wstepl; if_cases Kb2; zify_cond_z Kb2.
      + (* [comment removed for export] *)
        rewrite (@if_trueP _ (ub2 =? 0)%Z) in KQ by blia.
        wstepl. wstepl. wstepl. notrap. wstepl. wstepl.
        revive_all MUL WML AOK. enter_nextF HW DP.
        unfold dinv_L6W, sel_okF, alpha_ok in *. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try (unset_Z; lia).
        exact SOK. exact LOK.
      + (* [comment removed for export] *)
        rewrite (@if_falseP _ (ub2 =? 0)%Z) in KQ by blia.
        wstepl. wstepl. wstepl. notrap. wstepl. wstepl.
        revive_all MUL WML AOK. enter_nextF HW DP.
        unfold dinv_L6W, sel_okF, alpha_ok in *. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try (unset_Z; lia).
        exact SOK. exact LOK.
  Qed.

  (* [comment removed for export] *)
  Lemma S0F_U6_T : (forall F', (F' < F)%nat -> S0F_cut_L6W A F') -> S0F_cut_HHB A F -> S0F_cut_L6T A F.
  Proof.
    intros HW HHB. unfold S0F_cut_L6T. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof DI as DI'. cps_destruct DI' as ((AL & NBL) & NG & NSC & SOK & Ht & LOK).
    prep DM MU. kq_intro.
    hide_all_but_at [S; usp + -336]%Z.
    pose proof (munch_refl [(usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    destruct (Z_lt_le_dec (sv_t L) (sv_nGroups L)) as [LT|GE].
    - rewrite K_HCOD_go in KQ by exact LT.
      (* [comment removed for export] *)
      wstepl. wstepl. if_false_z.
      gbF_call (S0F_gb_1dae8 A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MUL WML AOK DP FU.
      gbF_next [S]%Z [(S, S + 68)]%Z.
      (* [comment removed for export] *)
      wstepl. wstepl. wstepl. gbv 11%Z 5%Z curr.
      rewrite edge_33 in KQ.
      (* [comment removed for export] *)
      wstepl. if_false_z. wstepl.
      revive_all MUL WML AOK. enter_nextF HW DP.
      unfold dinv_L6W, sel_okF, alpha_ok in *. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try (unset_Z; lia).
      exact SOK. apply lenp_ok_of_rows. intros t' i' Ht' Hi'. apply LOK; lia.
    - rewrite K_HCOD_exit in KQ by exact GE.
      wstepl. wstepl. if_true_z.
      revive_all MUL WML AOK. enter_sameF HHB DP.
      unfold dinv_HHB, sel_okF, alpha_ok in *. repeat match goal with |- _ /\ _ => split end; try lia.
      exact SOK. intros t' i' Ht' Hi'. apply LOK; lia.
  Qed.
End R.
End ACeilS1.
