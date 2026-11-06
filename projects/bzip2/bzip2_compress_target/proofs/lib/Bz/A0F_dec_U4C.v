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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU2 BzDU4 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFA DecTacFA DecTacFRA A0F_decV A0F_decRet A0F_decCutsA A0F_decCuts4 A0F_decCuts5.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCuts4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCuts5.
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

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok AIHI0 A.
  Hypothesis ASH : act_sh DI_A0 A.
  Variable Q : dres -> machine_state -> Prop.
  Hypothesis HRETD : A0F_RET_DATA A Q.
  Variable F : nat.
  Hypothesis HSEL : A0F_cut_HSEL A Q F.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  (* [comment removed for export] *)
  Lemma A0F_U4_L4M_body : forall i, (0 <= i <= 255)%Z -> ((i < 255)%Z -> A0F_cut_L4M A Q F (i + 1)) -> A0F_cut_L4M A Q F i.
  Proof.
    intros i Hi NXT. unfold A0F_cut_L4M. intros until w720. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    cps_destruct DI as (NB & HDR & IU & _ & Hn & NS2). unfold nb_ok in NB.
    pose proof (dpureF_rep _ _ _ _ _ _ DP) as REP. unfold drep in REP. cps_destruct REP as (_ & _ & _ & RS2U & _).
    open_dmemF DM. a0img. unfold r_of in DR. dr_open. kq_intro.
    hide_all_but_atF [S + 3152; S + 3196; S + 3468; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(S + 3152, S + 3196); (S + 3468, S + 3724); (a_P A + 496, a_P A + 728)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    (* [comment removed for export] *)
    arun_to 0xa411c%Z.
    lazymatch goal with H : u8arr _ ?mm (S + 3196)%Z (zb8 ?a ?n) |- _ =>
      pose proof (zb8_read1 a0segs mm (S + 3196) a n i _ H ltac:(lia) eq_refl) as RD end.
    pose proof (IU i ltac:(lia)) as Bi.
    astep. clear RD. rewrite zxb_lit8 by lia.
    (* [comment removed for export] *)
    Ltac fin_lia := repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
    Ltac tail i NXT HSEL HRETD MUL WML DP NS2 AOK :=
      let KL := fresh "KL" in
      arun; if_cases KL; zify_cond_z KL;
      [ (* [comment removed for export] *)
        revive_all MUL WML AOK; kq_fold;
        enter_cutF (NXT ltac:(lia) _ _ _ JK_) DP
      | (* [comment removed for export] *)
        match goal with KQ : kq _ _ |- _ =>
          replace (i + 1)%Z with 256%Z in KQ by lia end;
        let KZ := fresh "KZ" in
        arun; if_cases KZ; zify_cond_z KZ;
        [ match goal with KQ : kq _ _ |- _ => rewrite K_L4M_exit_ret in KQ by (dmodel_cbn; unset_Z; lia) end;
          revive_all MUL WML AOK; kq_fold; enter_cutF (HRETD _ _ _ JK_) DP;
          [ ret_nb | apply dpost14_ne; dmodel_cbn; exact NS2 ]
        | match goal with KQ : kq _ _ |- _ => rewrite K_L4M_exit_go in KQ by (dmodel_cbn; unset_Z; lia) end;
          arun_to 0xa419c%Z; revive_all MUL WML AOK; enter_sameF HSEL DP ] ].
    arun; if_cases Kb; zify_cond_z Kb.
    - (* [comment removed for export] *)
      rewrite K_L4M_skip in KQ by lia.
      tail i NXT HSEL HRETD MUL WML DP NS2 AOK.
      + unfold dinv_L4M, nb_ok. split; [lia|]. split; [apply (hdr_ok_frame _ _ HDR); dmodel_cbn; reflexivity|]. split; [exact IU|]. split; [lia|]. split; [lia| exact NS2].
      + unfold dinv_HSEL, alpha_ok, hdr_ok in *. dmodel_cbn. unset_Z. fin_lia.
    - (* [comment removed for export] *)
      rewrite K_L4M_set in KQ by lia.
      arun_to 0xa4144%Z.
      lazymatch goal with H : u8arr _ _ (S + 3468)%Z _ |- _ => zb8_sb H (d_nInUse d) end.
      arun_to 0xa4154%Z.
      (* [comment removed for export] *)
      assert (RS2U' : forall k, (0 <= zget (zset (d_s2u d) (d_nInUse d) i) k < 256)%Z).
      { intros k. rewrite zget_zset. destruct (Z.eqb_spec k (d_nInUse d)); [lia| apply RS2U]. }
      tail i NXT HSEL HRETD MUL WML DP NS2 AOK.
      + unfold dinv_L4M, nb_ok. dmodel_cbn. split; [lia|]. split; [apply (hdr_ok_frame _ _ HDR); dmodel_cbn; reflexivity|]. split; [apply inUse_ok_frame_s2u; exact IU|]. split; [lia|]. split; [lia| exact NS2].
      + unfold dinv_HSEL, alpha_ok, hdr_ok in *. dmodel_cbn. unset_Z. fin_lia.
  Qed.

  Lemma A0F_dec_U4C : A0F_cut_HMK A Q F.
  Proof.
    assert (G : forall k : nat, (k <= 255)%nat -> A0F_cut_L4M A Q F (255 - Z.of_nat k)%Z).
    { induction k as [|k IH]; intros Hk.
      - apply A0F_U4_L4M_body; [lia | intros; exfalso; lia].
      - apply A0F_U4_L4M_body; [lia | intros _].
        replace (255 - Z.of_nat (Datatypes.S k) + 1)%Z with (255 - Z.of_nat k)%Z by lia. apply IH. lia. }
    pose proof (G 255%nat ltac:(lia)) as G0. change (255 - Z.of_nat 255)%Z with 0%Z in G0. unfold A0F_cut_L4M in G0.
    unfold A0F_cut_HMK. intros until w720. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    cps_destruct DI as (NB & HDR & IU & NS2). unfold nb_ok in NB.
    open_dmemF DM. a0img. kq_intro. rewrite K_HMK_L4M in KQ.
    unfold r_of in DR. dr_open. hide_all_but_atF [S + 3152; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(S + 3152, S + 3196)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    (* [comment removed for export] *)
    arun_to 0xa4104%Z. sh_norm.
    revive_all MUL WML AOK. enter_sameF G0 DP.
    unfold dinv_L4M, nb_ok. dmodel_cbn. split; [lia|]. split; [apply (hdr_ok_frame _ _ HDR); dmodel_cbn; reflexivity|]. split; [exact IU|]. split; [lia|]. split; [lia| exact NS2].
  Qed.
End R.
End ACeilS1.
