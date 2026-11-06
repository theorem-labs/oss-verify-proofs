(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts DecCut DecTac DecTac2 DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU6 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFA DecTacFA DecTacFRA A0F_decV A0F_decRet A0F_decCuts5 A0F_decCuts6 A0F_gb_D A0F_gb_E.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCuts5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCuts6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_gb_D OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_gb_E.
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
  Hypothesis AOK : act_ok AIHI0 A.
  Hypothesis ASH : act_sh DI_A0 A.
  Variable Q : dres -> machine_state -> Prop.
  Hypothesis HRETOK : A0F_RET_OK A Q.
  Hypothesis HRETD : A0F_RET_DATA A Q.
  Variable F : nat.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  (* [comment removed for export] *)
  Lemma A0F_U6_W :
    (forall F', (F' < F)%nat -> A0F_cut_L6W A Q F') -> (forall F', (F' < F)%nat -> A0F_cut_HCOD A Q F') ->
    A0F_cut_L6W A Q F.
  Proof.
    intros HW HT. unfold A0F_cut_L6W. intros until w720. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    cps_destruct DI as (SEL & Ht & Hi & Hc & LOK). pose proof SEL as SEL'. cps_destruct SEL' as ((AL & NBL) & NG & NSC & SOK).
    pose proof AL as AL'. cps_destruct AL' as (_ & _ & _ & _ & _ & NS2).
    open_dmemF DM. a0img. kq_intro.
    unfold r_of in DR. dr_open. hide_all_but_atF [S; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(a_P A + 496, a_P A + 728)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    (* [comment removed for export] *)
    arun; if_cases KC; zify_cond KC.
    { assert (HC' : (sv_curr L < 1 \/ 20 < sv_curr L)%Z).
      { destruct (Z_lt_le_dec (sv_curr L + -21) 0) as [Lc|Lc].
        - rewrite (land64_neg (sv_curr L + -21)) in KC by lia. lia.
        - rewrite (land64_small (sv_curr L + -21)) in KC by lia. lia. }
      rewrite K_L6W_ret in KQ by exact HC'.
      (* [comment removed for export] *)
      arun_to 0xa3d6c%Z.
      revive_all MUL WML AOK.
      kq_fold. enter_cutF (HRETD _ _ _ JK_) DP; [ ret_nb | apply dpost14_ne; exact NS2 ]. }
    assert (HC' : (1 <= sv_curr L <= 20)%Z).
    { destruct (Z_lt_le_dec (sv_curr L + -21) 0) as [Lc|Lc].
      - rewrite (land64_neg (sv_curr L + -21)) in KC by lia. lia.
      - rewrite (land64_small (sv_curr L + -21)) in KC by lia. lia. }
    clear KC. rewrite K_L6W_go in KQ by exact HC'.
    (* [comment removed for export] *)
    arun_to 0xa56dc%Z.
    gbF_call (A0F_gb_a53c0 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU.
    gbF_nextA [S; S + 43888; a_P A; a_P A + 496]%Z [(S, S + 68); (S + 43888, S + 45436); (a_P A + 496, a_P A + 728)]%Z.
    dr_open. hide_all_but_atF [S; S + 43888; a_P A; a_P A + 496]%Z.
    arun_lwbuf. arun_gbv 1%Z ub.
    (* [comment removed for export] *)
    arun; if_cases Kbit; zify_cond_z Kbit.
    - (* [comment removed for export] *)
      rewrite (edge_34_0 _ ub) in KQ by (unset_Z; lia). kq_norm.
      arun_to 0xa5ad0%Z.
      lazymatch goal with H : u8arr _ _ (S + 43888)%Z _ |- _ =>
        zb8_sb H (258 * sv_t L + sv_i L)%Z; try rewrite (Z.mod_small (sv_curr L) 256) in H by lia end.
      assert (Ht0 : (0 <= sv_t L)%Z) by lia. assert (Ha : (sv_alphaSize L <= 258)%Z) by lia.
      pose proof (lenp_ok_upd _ _ _ _ _ Ht0 Hi Ha HC' LOK) as LOK'.
      (* [comment removed for export] *)
      arun; if_cases KI; zify_cond_z KI.
      + (* [comment removed for export] *)
        rewrite (@if_trueP _ (_ <? sv_alphaSize L)%Z) in KQ by blia.
        revive_all MUL WML AOK. enter_nextF HW DP.
        unfold dinv_L6W, sel_okF, alpha_ok in *. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try (unset_Z; lia).
        exact SOK. exact LOK'.
      + (* [comment removed for export] *)
        rewrite (@if_falseP _ (_ <? sv_alphaSize L)%Z) in KQ by blia.
        arun_to 0xa4e2c%Z.
        revive_all MUL WML AOK. enter_nextF HT DP.
        unfold dinv_HCOD, alpha_ok in *. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try (unset_Z; lia).
        exact SOK.
        intros t' i' Ht' Hi'. apply (LOK' t' i'); lia.
    - (* [comment removed for export] *)
      rewrite (edge_34_1 _ ub) in KQ by (unset_Z; lia).
      gbF_call (A0F_gb_a5428 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU.
      gbF_nextA [S; a_P A; a_P A + 496]%Z [(S, S + 68)]%Z.
      (* [comment removed for export] *)
      arun_lwbuf. arun_to 0xa56c8%Z.
      lazymatch goal with |- context [Z_to_bv 64 (Z.lor (Z.land (bv_signed (Z_to_bv 64 (Z.land ?r 18446744073709551615 * 9223372036854775808)) / 9223372036854775808) 18446744073709551615) 1 + _)] =>
        rewrite (pm1_bit r);
        match goal with
        | WB : (bv_unsigned ?w mod 4294967296 = ?bbx)%Z, RL : (_ <= ?blx <= 32)%Z |- _ =>
            replace (Z.land (Z.land r 18446744073709551615) 1) with (gbval bbx blx 1)
              by (symmetry; change 1%Z with (2^1 - 1)%Z at 2; apply (gbval_of_srlw64 _ _ _ _ _ WB RL); lia);
            pose proof (gbval_range bbx blx 1 ltac:(lia)) as Rub2; change (2^1)%Z with 2%Z in Rub2;
            set (ub2 := gbval bbx blx 1) in *
        end
      end.
      rewrite edge_35 in KQ.
      destruct (Z.eqb_spec ub2 0) as [Eb|Eb].
      + (* [comment removed for export] *)
        revive_all MUL WML AOK. enter_nextF HW DP.
        unfold dinv_L6W, sel_okF, alpha_ok in *. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try (unset_Z; lia).
        exact SOK. exact LOK.
      + (* [comment removed for export] *)
        rewrite (zb64_addM (sv_curr L)).
        revive_all MUL WML AOK. enter_nextF HW DP.
        unfold dinv_L6W, sel_okF, alpha_ok in *. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try (unset_Z; lia).
        exact SOK. exact LOK.
  Qed.

  (* [comment removed for export] *)
  Lemma A0F_U6_T : (forall F', (F' < F)%nat -> A0F_cut_L6W A Q F') -> A0F_cut_HHB A Q F -> A0F_cut_HCOD A Q F.
  Proof.
    intros HW HHB. unfold A0F_cut_HCOD. intros until w720. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    pose proof DI as DI'. cps_destruct DI' as ((AL & NBL) & NG & NSC & SOK & Ht & LOK).
    open_dmemF DM. a0img. kq_intro.
    unfold r_of in DR. dr_open. hide_all_but_atF [S; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(a_P A + 496, a_P A + 728)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    destruct (Z_lt_le_dec (sv_t L) (sv_nGroups L)) as [LT|GE].
    - rewrite K_HCOD_go in KQ by exact LT.
      (* [comment removed for export] *)
      arun. if_cases KX; zify_cond_z KX; [exfalso; lia|].
      arun_to 0xa4e3c%Z.
      gbF_call (A0F_gb_a4b20 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU.
      gbF_nextA [S; a_P A; a_P A + 496]%Z [(S, S + 68)]%Z.
      arun_lwbuf. arun_gbv 5%Z curr.
      rewrite edge_33 in KQ.
      (* [comment removed for export] *)
      arun. if_cases KA; zify_cond_z KA; [|exfalso; unfold alpha_ok in AL; lia].
      revive_all MUL WML AOK. enter_nextF HW DP.
      unfold dinv_L6W, sel_okF, alpha_ok in *. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try (unset_Z; lia).
      exact SOK. apply lenp_ok_of_rows. intros t' i' Ht' Hi'. apply LOK; lia.
    - rewrite K_HCOD_exit in KQ by exact GE.
      arun. if_cases KX; zify_cond_z KX; [|exfalso; lia].
      revive_all MUL WML AOK.
      enter_sameF HHB DP.
      unfold dinv_HHB, sel_okF, alpha_ok in *. repeat match goal with |- _ /\ _ => split end; try lia.
      exact SOK. intros t' i' Ht' Hi'. apply LOK; lia.
  Qed.
End R.
End ACeilS1.
