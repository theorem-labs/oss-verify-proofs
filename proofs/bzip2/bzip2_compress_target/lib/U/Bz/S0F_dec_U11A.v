(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 DecCut DecTac DecTac2 DecAux. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import
     BzLemmasT BzLemmasT2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzWalkArith BzWalkArith3 S0_dec_U13 S0_decCuts S0_decCutsE.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU9 BzDU11. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR S0F_decRet S0F_decCuts S0F_decCutsM S0F_decCutsE.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsE.
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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia.
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
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.
  Hypothesis HFAST : S0F_cut_HFAST A F.
  Hypothesis HSMALL : S0F_cut_HSMALL A F.
  (* [comment removed for export] *)
  Variables (L : dsv) (s : dstrm) (J : jk).

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation L21cF := (L21cF A F L s J). Notation L22cF := (L22cF A F L s J). Notation L23cF := (L23cF A F L s J).
  Notation L24cF := (L24cF A F L s J). Notation L25cF := (L25cF A F L s J). Notation TcF := (TcF A F L s J).

  (* [comment removed for export] *)
  Ltac zw32_sw ARR i v tacv :=
    lazymatch goal with |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of ARR with u32arr _ _ ?A (zw32 ?a ?n) =>
      let SO := fresh "SO" in
      pose proof (u32arr_store_ok sg mm A (zw32 a n) i _ ARR ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO;
      step;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?ga (le4 ?x)) _) =>
        let H := fresh "ARR" in
        pose proof (zw32_write sg mm A a n i x v ARR ltac:(lia) ltac:(tacv)) as H;
        let ga' := lazymatch ga with wa _ => ga | Z_to_bv 64 ?X => constr:(wa X) | _ => ga end in
        replace (wa (A + 4 * i)%Z) with ga' in H by (cbv delta [wa]; first [reflexivity | f_equal; lia | apply f_equal; lia]);
        clear ARR; store_done; rename H into ARR
      end; try clear SO; zsimp; bz32l
    end end.

  Ltac prep DM MU DP :=
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN; pose proof rnums_words_length as RNL; lin_natZ RNL;
    unfold W14, D14, DSTATE_SIZE in MU; cbn [app blk_ivls b_s b_strm] in MU; open_dmemF DM; s2img.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma U11F_T : TcF.
  Proof.
    unfold S0F_decCutsE.TcF. intros until pb. intros DM FR ST MU WM MI DP FU DI.
    prep DM MU DP. cps_destruct DI as (EOB & ORIG & CFP).
    pose proof (dpureF_small _ _ _ _ _ _ DP) as SMALL. pose proof (dpureF_verb _ _ _ _ _ _ DP) as VERB.
    hide_all_but_at [S; S + 3152; usp + -336]%Z.
    pose proof (munch_refl [(S, S + 68); (S + 3152, S + 3196); (usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro.
    wstepl. wstepl. wstepl. wstepl. (* [comment removed for export] *)
    wstepl. wstepl. (* [comment removed for export] *)
    sb_step. (* [comment removed for export] *)
    wstepl. (* [comment removed for export] *)
    wstepl. (* [comment removed for export] *)
    rewrite VERB. wstepl; if_cases Kv; [ zify_cond_z Kv; exfalso; lia | ].
    wstepl. (* [comment removed for export] *)
    wstepl; if_cases Ksm; zify_cond_z Ksm.
    - (* [comment removed for export] *)
      assert (SM0 : d_small d = 0%Z).
      { rewrite SMALL in Ksm |- *. assert (B01 : b_small cx = 0%Z \/ b_small cx = 1%Z) by (lin_unbox LIN; clear - LIN; decompose [and] LIN; assumption). clear - Ksm B01.
        destruct B01 as [E|E]; rewrite E in Ksm |- *; [reflexivity| cbv in Ksm; discriminate]. }
      rewrite (K_T_fast F L d s SM0) in KQ. unfold dT in KQ.
      cell_mod32 MIDc 32%nat. change ((-1) mod 2 ^ 32)%Z with crc_init in MIDc.
      revive_all MUL WML AOK. enter_sameF HFAST DP.
      apply dinv_HFAST_T; [exact EOB | exact ORIG | exact CFP | exact SM0].
    - (* [comment removed for export] *)
      assert (SM1 : d_small d = 1%Z).
      { rewrite SMALL in Ksm |- *. assert (B01 : b_small cx = 0%Z \/ b_small cx = 1%Z) by (lin_unbox LIN; clear - LIN; decompose [and] LIN; assumption). clear - Ksm B01.
        destruct B01 as [E|E]; rewrite E in Ksm |- *; [cbv in Ksm; exfalso; apply Ksm; reflexivity| reflexivity]. }
      rewrite (K_T_small F L d s) in KQ by (rewrite SM1; discriminate). unfold dT in KQ.
      cell_mod32 MIDc 32%nat. change ((-1) mod 2 ^ 32)%Z with crc_init in MIDc.
      revive_all MUL WML AOK. enter_sameF HSMALL DP.
      apply dinv_HSMALL_T; [exact EOB | exact ORIG | exact CFP | exact SM1].
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma U11F_L25 : forall i, (1 <= i <= 256)%Z -> ((i < 256)%Z -> L25cF (i + 1)) -> L25cF i.
  Proof.
    intros i Hi NXT. unfold S0F_decCutsE.L25cF. intros until pb. intros DM FR ST MU WM MI DP FU DI.
    prep DM MU DP. cps_destruct DI as (EOB & ORIG & _ & CFP). cps_pose EOB as (NBR & NB9 & SYMB & HIST & HDR).
    pose proof (eobF_psum_range L d (i - 1) EOB ltac:(lia)) as PS0. pose proof (eobF_psum_range L d i EOB ltac:(lia)) as PS1.
    pose proof (psum_step_le (bsym d) (zget (d_unzftab d)) (Z.to_nat (sv_nblock L)) HIST (i - 1) ltac:(lia)) as MONO.
    replace (i - 1 + 1)%Z with i in MONO by lia.
    pose proof (CFP i ltac:(lia)) as CFi.
    hide_all_but_at [S + 1096; usp + -336]%Z.
    pose proof (munch_refl [(usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro.
    wstepl. notrap. (* [comment removed for export] *)
    pose proof (zw32_read s0segs m (S + 1096) (d_cftab d) 257 i _ CF ltac:(lia) eq_refl) as RD.
    wstepl. clear RD. (* [comment removed for export] *) rewrite CFi.
    wstepl; if_cases K1; [ zify_cond_z K1; exfalso; lia | ].
    wstepl. wstepl. wstepl. wstepl. wstepl. (* [comment removed for export] *)
    wstepl; if_cases K2; zify_cond_z K2.
    - rewrite (K_L25_pass F L d s i) in KQ by first [lia | rewrite !CFP by lia; exact MONO].
      pose proof (NXT ltac:(lia)) as NX. unfold S0F_decCutsE.L25cF in NX. revive_all MUL WML AOK.
      kq_fold. enter_cutF NX DP; [ f_equal; lia | ]. split; [exact EOB | split; [exact ORIG | split; [lia | exact CFP]]].
    - rewrite (K_L25_pass F L d s i) in KQ by first [lia | rewrite !CFP by lia; exact MONO].
      rewrite (K_L25_exit F L d s) in KQ || (replace (i + 1)%Z with 257%Z in KQ by lia; rewrite (K_L25_exit F L d s) in KQ).
      revive_all MUL WML AOK. kq_fold. enter_cutF U11F_T DP. split; [exact EOB | split; [exact ORIG | exact CFP]].
  Time Qed.
  Lemma U11F_L25_all : L25cF 1.
  Proof.
    assert (G : forall k : nat, (k <= 255)%nat -> L25cF (256 - Z.of_nat k)%Z).
    { induction k as [|k IH]; intros Hk.
      - apply U11F_L25; [lia| intros; exfalso; lia].
      - apply U11F_L25; [lia| intros _]. replace (256 - Z.of_nat (Datatypes.S k) + 1)%Z with (256 - Z.of_nat k)%Z by lia. apply IH. lia. }
    exact (G 255%nat ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma U11F_L24 : forall i, (0 <= i <= 256)%Z -> ((i < 256)%Z -> L24cF (i + 1)) -> L24cF i.
  Proof.
    intros i Hi NXT. unfold S0F_decCutsE.L24cF. intros until pb. intros DM FR ST MU WM MI DP FU DI.
    prep DM MU DP. cps_destruct DI as (EOB & ORIG & _ & CFP). cps_pose EOB as (NBR & NB9 & SYMB & HIST & HDR).
    pose proof (eobF_psum_range L d i EOB ltac:(lia)) as PS1. pose proof (CFP i ltac:(lia)) as CFi.
    hide_all_but_at [S + 1096; usp + -336]%Z.
    pose proof (munch_refl [(usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro.
    wstepl. notrap. wstepl.
    pose proof (zw32_read s0segs m (S + 1096) (d_cftab d) 257 i _ CF ltac:(lia) eq_refl) as RD.
    wstepl. clear RD. (* [comment removed for export] *) rewrite CFi.
    wstepl; if_cases K1; [ zify_cond_z K1; exfalso; lia | ].
    wstepl; if_cases K1'; [ zify_cond_z K1'; exfalso; lia | ].
    wstepl. wstepl. (* [comment removed for export] *)
    rewrite (K_L24_pass F L d s i) in KQ by first [lia | rewrite CFi; lia].
    wstepl; if_cases K2; zify_cond_z K2.
    - pose proof (NXT ltac:(lia)) as NX. unfold S0F_decCutsE.L24cF in NX. revive_all MUL WML AOK.
      kq_fold. enter_cutF NX DP. split; [exact EOB | split; [exact ORIG | split; [lia | exact CFP]]].
    - wstepl. wstepl. wstepl. wstepl. wstepl. (* [comment removed for export] *)
      replace (i + 1)%Z with 257%Z in KQ by lia. rewrite (K_L24_exit F L d s) in KQ.
      revive_all MUL WML AOK. kq_fold.
      change (Z_to_bv 64 0) with (Z_to_bv 64 (psum (zget (d_unzftab d)) (1 - 1))) at 1.
      enter_cutF U11F_L25_all DP. split; [exact EOB | split; [exact ORIG | split; [lia | exact CFP]]].
  Time Qed.
  Lemma U11F_L24_all : L24cF 0.
  Proof.
    assert (G : forall k : nat, (k <= 256)%nat -> L24cF (256 - Z.of_nat k)%Z).
    { induction k as [|k IH]; intros Hk.
      - apply U11F_L24; [lia| intros; exfalso; lia].
      - apply U11F_L24; [lia| intros _]. replace (256 - Z.of_nat (Datatypes.S k) + 1)%Z with (256 - Z.of_nat k)%Z by lia. apply IH. lia. }
    exact (G 256%nat ltac:(lia)).
  Qed.

End R.
End ACeilS1.
