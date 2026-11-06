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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU6 BzDU7 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU7 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFB DecTacFB DecTacFRB B0F_decV B0F_decRet B0F_decCuts6 B0F_decCuts7 B0F_dec_U7B.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts7.
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
Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok BIHI0 A.
  Hypothesis ASH : act_sh DI_B0 A.
  Variable Q : dres -> machine_state -> Prop.
  Variable F : nat.
  (* [comment removed for export] *)
  Variable t : Z.
  Hypothesis HL7C : forall mn mx, B0F_cut_L7C A Q F t mn mx.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  (* [comment removed for export] *)
  Lemma B0F_U7_I : forall i mn mx, (forall mn' mx', B0F_cut_L7I A Q F t (i + 1) mn' mx') -> B0F_cut_L7I A Q F t i mn mx.
  Proof.
    intros i mn mx NXI. unfold B0F_cut_L7I. intros until w752. intros DM FRL FRH AF ST MU WM MI DP [DI Hia] FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    pose proof DI as DI'. cps_destruct DI' as (COM & Ht & Hi & Hmn & Hmx & SCAN & SC0 & TU).
    pose proof COM as COM'. destruct COM' as [SEL LALL]. pose proof SEL as SEL'. cps_destruct SEL' as ((AL & NBL) & NG & NSC & SOK).
    assert (Ha : (1 <= sv_alphaSize L <= 258)%Z) by (unfold alpha_ok in AL; lia).
    open_dmemF DM. b0img. kq_intro.
    unfold r_of in DR. dr_open. hide_all_but_atF [S + 43888; a_P A; a_P A + 344]%Z.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MUL. pose proof (wmono_refl b0segs m) as WML.
    (* [comment removed for export] *)
    pose proof (LALL t i ltac:(lia) ltac:(lia)) as Bb.
    brun_to 0xb127c%Z.
    lazymatch goal with H : u8arr _ ?mm (S + 43888)%Z (zb8 ?a ?n) |- _ =>
      pose proof (zb8_read1 b0segs mm (S + 43888) a n (258 * t + i)%Z _ H ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    astep. clear RD. rewrite zxb_lit8 by lia.
    set (b := zget (d_len d) (258 * t + i)) in *.
    rewrite (K_L7I_step F L d s t i mn mx) in KQ by lia. fold b in KQ.
    Ltac fin_scan NXI HL7C MUL WML DP AOK b mn mx :=
      (* [comment removed for export] *)
      let K := fresh "K" in
      brun; if_cases K; zify_cond_z K;
      [ revive_all MUL WML AOK; enter_sameF (NXI (Z.min mn b) (Z.max mx b)) DP
      | astep;
        match goal with KQ : kq _ _ |- _ => rewrite K_L7I_exit in KQ by (unset_Z; lia) end;
        revive_all MUL WML AOK; enter_sameF (HL7C (Z.min mn b) (Z.max mx b)) DP ].
    replace (if (b <? mn)%Z then b else mn) with (Z.min mn b) in KQ by (destruct (Z.ltb_spec b mn); lia).
    replace (if (mx <? b)%Z then b else mx) with (Z.max mx b) in KQ by (destruct (Z.ltb_spec mx b); lia).
    assert (SCAN' : forall j, (0 <= j < i + 1)%Z -> (Z.min mn b <= zget (d_len d) (258 * t + j) <= Z.max mx b)%Z).
    { intros j Hj. destruct (Z.eq_dec j i) as [->|NE]; [unset_Z; lia|]. specialize (SCAN j ltac:(lia)). lia. }
    Ltac fin_inv SCAN' :=
      unfold dinv_L7I, dinv_L7C; repeat match goal with |- _ /\ _ => split end; try assumption; try (unset_Z; lia);
      try (intros j Hj; apply SCAN'; unset_Z; lia).
    (* [comment removed for export] *)
    brun; if_cases K1; zify_cond_z K1.
    - brun; if_cases K2; zify_cond_z K2.
      + replace (Z_to_bv 64 mx) with (Z_to_bv 64 (Z.max mx b)) by (f_equal; lia).
        replace (Z_to_bv 64 mn) with (Z_to_bv 64 (Z.min mn b)) by (f_equal; lia).
        fin_scan NXI HL7C MUL WML DP AOK b mn mx; fin_inv SCAN'.
      + astep.
        replace (Z_to_bv 64 mx) with (Z_to_bv 64 (Z.max mx b)) by (f_equal; lia).
        replace (Z_to_bv 64 b) with (Z_to_bv 64 (Z.min mn b)) by (f_equal; lia).
        fin_scan NXI HL7C MUL WML DP AOK b mn mx; fin_inv SCAN'.
    - astep.
      brun; if_cases K2; zify_cond_z K2.
      + replace (Z_to_bv 64 b) with (Z_to_bv 64 (Z.max mx b)) by (f_equal; lia).
        replace (Z_to_bv 64 mn) with (Z_to_bv 64 (Z.min mn b)) by (f_equal; lia).
        fin_scan NXI HL7C MUL WML DP AOK b mn mx; fin_inv SCAN'.
      + astep.
        replace (Z_to_bv 64 b) with (Z_to_bv 64 (Z.max mx b)) by (f_equal; lia).
        fin_scan NXI HL7C MUL WML DP AOK b mn mx; fin_inv SCAN'.
  Qed.

  Lemma B0F_U7_I_all : forall k : nat, forall i mn mx, (258 - Z.of_nat k <= i)%Z -> B0F_cut_L7I A Q F t i mn mx.
  Proof.
    induction k as [|k IH]; intros i mn mx Hi.
    - (* [comment removed for export] *)
      unfold B0F_cut_L7I. intros until w752. intros DM FRL FRH AF ST MU WM MI DP [DI Hia] FU. exfalso.
      destruct DI as (((AL & _) & _) & _). unfold alpha_ok in AL. cbn in Hi. lia.
    - apply B0F_U7_I. intros mn' mx'. apply IH. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma B0F_U7_T : B0F_cut_L7T A Q F t.
  Proof.
    unfold B0F_cut_L7T. intros until w752. intros DM FRL FRH AF ST MU WM MI DP [DI LT] FU.
    pose proof DI as DI'. cps_destruct DI' as (COM & Ht & TU).
    pose proof COM as COM'. destruct COM' as [SEL LALL]. pose proof SEL as SEL'. cps_destruct SEL' as ((AL & NBL) & NG & NSC & SOK).
    assert (Ha : (3 <= sv_alphaSize L <= 258)%Z) by (unfold alpha_ok in AL; lia).
    kq_intro. rewrite K_L7T_scan in KQ by exact LT.
    brun. if_cases KA; zify_cond_z KA; [exfalso; lia|].
    (* [comment removed for export] *)
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN.
    assert (Ht6 : (0 <= t < 6)%Z) by lia.
    brun_to 0xb1258%Z.
    kq_fold. eapply evt_eq; [ | eapply (B0F_U7_I_all 258%nat 0 32 0 ltac:(cbn; lia) L d s J) ]; [ st_eq | eassumption .. | | eassumption ].
    split; [| lia]. unfold dinv_L7I. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
  Qed.
End R.

Section R2.
  Variable A : act14.
  Hypothesis AOK : act_ok BIHI0 A.
  Hypothesis ASH : act_sh DI_B0 A.
  Variable Q : dres -> machine_state -> Prop.
  Variable F : nat.
  Hypothesis HH7M : B0F_cut_H7M A Q F.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  (* [comment removed for export] *)
  Lemma B0F_U7_D : forall t, B0F_cut_L7T A Q F (t + 1) -> B0F_cut_L7D A Q F t.
  Proof.
    intros t NXT. unfold B0F_cut_L7D. intros until w752. intros DM FRL FRH AF ST MU WM MI DP [DI Ht] FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    pose proof DI as DI'. cps_destruct DI' as (COM & Ht1 & TU).
    pose proof COM as COM'. destruct COM' as [SEL LALL]. pose proof SEL as SEL'. cps_destruct SEL' as ((AL & NBL) & NG & NSC & SOK).
    open_dmemF DM. b0img. kq_intro.
    unfold r_of in DR. dr_open. hide_all_but_atF [a_P A; a_P A + 344]%Z.
    pose proof (munch_refl [(a_P A + 344, a_P A + 760)]%Z m) as MUL. pose proof (wmono_refl b0segs m) as WML.
    brun; if_cases KC; zify_cond_z KC.
    - revive_all MUL WML AOK. enter_sameF NXT DP. split; [exact DI| lia].
    - brun_to 0xb1370%Z.
      rewrite (K_L7T_exit F L d s (t + 1)) in KQ by lia.
      revive_all MUL WML AOK. enter_sameF HH7M DP.
      unfold dinv_H7M. split; [exact COM|]. replace (sv_nGroups L) with (t + 1)%Z by lia. exact TU.
  Qed.

  (* [comment removed for export] *)
  Lemma B0F_U7_pro : B0F_cut_L7T A Q F 0 -> B0F_cut_HHB A Q F.
  Proof.
    intros NX. unfold B0F_cut_HHB. intros until w752. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    pose proof DI as DI'. cps_destruct DI' as (SEL & HtG & LALL). pose proof SEL as SEL'. cps_destruct SEL' as ((AL & NBL) & NG & NSC & SOK).
    assert (Ha : (3 <= sv_alphaSize L <= 258)%Z) by (unfold alpha_ok in AL; lia).
    open_dmemF DM. b0img. kq_intro. rewrite K_HHB_L7T in KQ.
    unfold r_of in DR. dr_open. hide_all_but_atF [a_P A; a_P A + 344]%Z.
    pose proof (munch_refl [(a_P A, a_P A + 128); (a_P A + 344, a_P A + 760)]%Z m) as MUL   (* [comment removed for export] *). pose proof (wmono_refl b0segs m) as WML.
    brun. if_cases KG; zify_cond_z KG; [exfalso; lia|].
    brun_to 0xb1220%Z.
    (* [comment removed for export] *)
    rewrite ?(Z.div_mul (sv_alphaSize L) 4294967296) in * by lia.
    (* [comment removed for export] *)
    replace (Z.land 18446744073709551615 (sv_nGroups L)) with (sv_nGroups L) in * by (rewrite Z.land_comm; symmetry; apply land64_small; lia).
    revive_all MUL WML AOK. enter_sameF NX DP.
    split; [| lia]. unfold dinv_L7T, u7com. split; [split; [exact SEL| exact LALL]|]. split; [lia| apply tabs_upto_0].
  Qed.
End R2.

(* [comment removed for export] *)
(* [comment removed for export] *)
End ACeilS1.
