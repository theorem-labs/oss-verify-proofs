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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU6 BzDUM BzDU7 DecCutF DecTacF DecTacFR DecTacFR2.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU7 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFA DecTacFA DecTacFRA A0F_decV A0F_decRet A0F_decCuts7.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCuts7.
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
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR2.
(* [comment removed for export] *)
Lemma addiw_m1 : forall x, (-1 <= x <= 2147483646)%Z ->
  bv_swrap 32 (Z.land x 18446744073709551615 + 1) = (x + 1)%Z.
Proof.
  intros x Hx. destruct (Z.eq_dec x (-1)) as [->|NE].
  - vm_compute. reflexivity.
  - rewrite (land64_small x) by lia. rewrite swrap32_small by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Ltac zw32_store_done ARR i v :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?mm ?ga (le4 ?x)) _) =>
      lazymatch type of ARR with u32arr _ _ ?A (zw32 ?a ?n) =>
        let H := fresh "ARR" in
        pose proof (zw32_write segs mm A a n i x v ARR ltac:(lia)
                      ltac:(first [ reflexivity | rewrite unsigned_lit by lia; reflexivity | rewrite unsigned_lit_wrap, <- Znumtheory.Zmod_div_mod by lia; reflexivity ])) as H;
        let ga' := lazymatch ga with wa _ => ga | Z_to_bv 64 ?X => constr:(wa X) | _ => ga end in
        replace (wa (A + 4 * i)%Z) with ga' in H by (cbv delta [wa]; first [reflexivity | f_equal; lia | apply f_equal; lia]);
        clear ARR; store_done; rename H into ARR
      end
  end.

Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok AIHI0 A.
  Hypothesis ASH : act_sh DI_A0 A.
  Variable Q : dres -> machine_state -> Prop.
  Variable F : nat.
  Hypothesis HL7G : A0F_cut_L7G A Q F.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Ltac prepA DM DP MU :=
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN; pose proof rnums_words_length as RNL; lin_natZ RNL;
    unfold_W14 MU; open_ash ASH AOK;
    lazymatch goal with H : sanchor (b_s _) (a_shs _) |- _ => pose proof (proj2 H : saddr (b_s (a_cx A)) (a_shs A)) as ANS0 end;
    open_dmemF DM; a0img.

  Lemma A0F_U7_K : forall ii, A0F_cut_L7J A Q F ii 0 -> A0F_cut_L7K A Q F ii.
  Proof.
    intros ii NX. unfold A0F_cut_L7K. intros until w720. intros DM FRL FRH AF ST MU WM MI DP [DI Hii] FU.
    pose proof DI as DI'. cps_destruct DI' as (SEL & TABS & U0 & Hii' & MB & MA).
    kq_intro. rewrite K_L7K_in in KQ by lia.
    (* [comment removed for export] *)
    arun_to 0xa5210%Z.
    kq_fold. eapply evt_eq; [ | eapply (NX L d s J) ]; [ st_eq | eassumption .. | | eassumption ].
    split; [| lia]. unfold dinv_L7J. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
    intros k Hk. apply MA. lia.
  Qed.

  Lemma A0F_U7_J : forall ii dd, A0F_cut_L7J A Q F ii (dd + 1) -> A0F_cut_L7K A Q F (ii - 1) -> A0F_cut_L7J A Q F ii dd.
  Proof.
    intros ii dd NXJ NXK. unfold A0F_cut_L7J. intros until w720. intros DM FRL FRH AF ST MU WM MI DP [DI Hdd] FU.
    pose proof DI as DI'. cps_destruct DI' as (SEL & TABS & U0 & Hii & Hdd' & MB & MA).
    pose proof SEL as SEL'. cps_destruct SEL' as ((AL & NBL) & NG & NSC & SOK).
    prepA DM DP MU. kq_intro. rewrite K_L7J_step in KQ by lia.
    replace (ii * 16 + (15 - dd))%Z with (16 * ii + 15 - dd)%Z in KQ by lia.
    unfold r_of in DR. dr_open. hide_all_but_atF [S + 3724; S + 7820; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(S + 3724, S + 7820); (S + 7820, S + 7884)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    (* [comment removed for export] *)
    arun_to 0xa5220%Z.
    lazymatch goal with H : u8arr _ _ (S + 3724)%Z _ |- _ =>
      zb8_sb H (3855 + 16 * ii - dd)%Z; try rewrite (Z.mod_small (16 * ii + 15 - dd) 256) in H by lia end.
    (* [comment removed for export] *)
    astep. astep. try rewrite (addiw_m1 (dd - 1)) by lia.
    arun; if_cases KC; zify_cond_z KC.
    - revive_all MUL WML AOK. enter_sameF NXJ DP.
      split; [| lia]. unfold dinv_L7J. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
      all: try (apply (tabs_okF_frame d); [exact TABS| | | |]; dmodel_cbn; reflexivity).
      intros k Hk. rewrite zget_zset. destruct (Z.eqb_spec k (3855 + 16 * ii - dd)); [lia|]. apply MA. lia.
    - (* [comment removed for export] *)
      arun_to 0xa526c%Z.
      replace (3855 + 16 * ii - (dd - 1 + 1))%Z with (3840 + 16 * ii)%Z by lia.
      lazymatch goal with H : u32arr _ ?mm (S + 7820)%Z ?ws |- _ =>
        pose proof (u32arr_store_ok a0segs mm (S + 7820) ws ii _ H ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO;
        wstepl; zw32_store_done H ii (3840 + 16 * ii)%Z end.
      try clear SO.
      (* [comment removed for export] *)
      arun; if_cases K2; zify_cond_z K2.
      + replace (dd + 1)%Z with 16%Z in KQ by lia. rewrite K_L7J_exit in KQ by lia.
        revive_all MUL WML AOK. enter_sameF NXK DP.
        split; [| lia]. unfold dinv_L7K. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
        all: try (apply (tabs_okF_frame d); [exact TABS| | | |]; dmodel_cbn; reflexivity).
        all: try (intros l Hl; rewrite zget_zset; destruct (Z.eqb_spec l ii); [lia|]; apply MB; lia).
        all: intros k Hk; rewrite zget_zset; destruct (Z.eqb_spec k (3855 + 16 * ii - dd)); [lia|]; apply MA; lia.
      + (* [comment removed for export] *)
        astep.
        replace (dd + 1)%Z with 16%Z in KQ by lia. subst ii. rewrite K_L7J_last in KQ.
        revive_all MUL WML AOK. enter_sameF HL7G DP.
        unfold dinv_L7G, mtf_okF, mtfb. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try assumption.
        all: try (apply (tabs_okF_frame d); [exact TABS| | | |]; dmodel_cbn; reflexivity).
        all: try (apply (mtf_inv_ext (fun l => 3840 + 16 * l)%Z); [| exact mtf_inv_home];
                  intros l Hl; rewrite zget_zset; destruct (Z.eqb_spec l 0); [lia|]; rewrite MB by lia; reflexivity).
        all: try lia.
        (* [comment removed for export] *)
        all: intros k Hk; rewrite zget_zset; destruct (Z.eqb_spec k (3855 + 16 * 0 - dd)); [lia|];
          destruct (Z_lt_le_dec k (3855 + 16 * 0 - dd));
          [ pose proof (dpureF_rep _ _ _ _ _ _ DP) as RP; unfold drep in RP; dmodel_cbn_in RP;
            cps_destruct RP as (_ & _ & _ & _ & _ & MTFA); apply MTFA; lia
          | apply MA; lia ].
  Qed.

  (* [comment removed for export] *)
  Lemma A0F_U7_M1 : A0F_call_MSU A Q F -> A0F_cut_H7M A Q F.
  Proof.
    intros HCALL. unfold A0F_cut_H7M. intros until w720. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    pose proof DI as DI'. destruct DI' as [COM TABS]. pose proof COM as COM'. destruct COM' as [SEL LALL].
    pose proof SEL as SEL'. cps_destruct SEL' as ((AL & NBL) & NG & NSC & SOK).
    pose proof AL as AL'. unfold alpha_ok in AL'. cps_destruct AL' as (EA & NIU & _).
    pose proof DM as DM0. prepA DM DP MU.
    arun_to 0x52ea0%Z.
    eapply evt_eq; [ | eapply (HCALL L d s J) ]; [ st_eq | exact DM0 | eassumption .. ].
  Qed.

  (* [comment removed for export] *)
  Lemma A0F_U7_M2 : A0F_cut_L7K A Q F 15 -> A0F_cut_MSUR A Q F.
  Proof.
    intros NX. unfold A0F_cut_MSUR. intros until w720. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    pose proof DI as DI'. destruct DI' as [COM TABS]. pose proof COM as COM'. destruct COM' as [SEL LALL].
    pose proof SEL as SEL'. cps_destruct SEL' as ((AL & NBL) & NG & NSC & SOK).
    prepA DM DP MU. kq_intro. rewrite K_H7M_memset in KQ.
    unfold r_of in DR. dr_open. hide_all_but_atF [a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(a_P A + 496, a_P A + 728)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    arun_to 0xa51f8%Z.
    revive_all MUL WML AOK. enter_sameF NX DP.
    split; [| lia]. unfold dinv_L7K. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
    all: try (apply (tabs_okF_frame d); [exact TABS| | | |]; dmodel_cbn; reflexivity).
    all: try apply unz0_clear.
    all: intros; exfalso; lia.
  Qed.
End R.

(* [comment removed for export] *)
Lemma A0F_U7_mtf : forall A, act_ok AIHI0 A -> act_sh DI_A0 A -> forall Q F, A0F_cut_L7G A Q F -> A0F_cut_L7K A Q F 15.
Proof.
  intros A AOK ASH Q F HL7G.
  assert (J : forall ii, A0F_cut_L7K A Q F (ii - 1) -> forall k : nat, forall dd, (15 - Z.of_nat k <= dd)%Z -> A0F_cut_L7J A Q F ii dd).
  { intros ii NXK. induction k as [|k IH]; intros dd Hdd.
    - (* [comment removed for export] *)
      apply (A0F_U7_J A AOK ASH Q F HL7G); [| exact NXK].
      unfold A0F_cut_L7J. intros until w720. intros DM FRL FRH AF ST MU WM MI DP [DI Hdd2] FU. exfalso. cbn in Hdd. lia.
    - apply (A0F_U7_J A AOK ASH Q F HL7G); [| exact NXK]. apply IH. lia. }
  assert (K : forall k : nat, forall ii, (ii <= Z.of_nat k - 1)%Z -> A0F_cut_L7K A Q F ii).
  { induction k as [|k IH]; intros ii Hii.
    - unfold A0F_cut_L7K. intros until w720. intros DM FRL FRH AF ST MU WM MI DP [DI Hii2] FU. exfalso. cbn in Hii. lia.
    - apply (A0F_U7_K A Q F). apply (J ii ltac:(apply IH; lia) 16%nat). cbn; lia. }
  apply (K 16%nat). cbn; lia.
Qed.
End ACeilS1.
