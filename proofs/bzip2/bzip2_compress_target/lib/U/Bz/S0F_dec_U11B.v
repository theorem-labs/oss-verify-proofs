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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU9 BzDU11. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR S0F_decRet S0F_decCuts S0F_decCutsM S0F_decCutsE S0F_dec_U11A.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsE OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U11A.
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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF.
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
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
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
  Lemma U11F_L23 : forall k, (0 <= k <= 255)%Z -> ((k < 255)%Z -> L23cF (k + 1)) -> L23cF k.
  Proof.
    intros k Hk NXT. unfold S0F_decCutsE.L23cF. intros until pb. intros DM FR ST MU WM MI DP FU DI.
    prep DM MU DP. cps_destruct DI as (EOB & ORIG & _ & CS). cps_pose EOB as (NBR & NB9 & SYMB & HIST & HDR).
    pose proof (eobF_psum_range L d k EOB ltac:(lia)) as PS0. pose proof (eobF_psum_range L d (k + 1) EOB ltac:(lia)) as PS1.
    pose proof (eobF_unz_range L d k EOB ltac:(lia)) as UZk.
    pose proof (cf_summed_val _ _ (k + 1) ltac:(lia) CS) as VAL. replace (k + 1 - 1)%Z with k in VAL by lia.
    pose proof (proj2 CS (k + 1)%Z ltac:(lia)) as CFk1. replace (k + 1 - 1)%Z with k in CFk1 by lia.
    pose proof (proj1 CS k ltac:(lia)) as CFk.
    rewrite psum_succ in PS1 by lia.
    hide_all_but_at [S + 1096; usp + -336]%Z.
    pose proof (munch_refl [(S + 1096, S + 2124); (usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro.
    wstepl. notrap.
    pose proof (zw32_read s0segs m (S + 1096) (d_cftab d) 257 (k + 1) _ CF ltac:(lia) eq_refl) as RD.
    wstepl. clear RD. (* [comment removed for export] *) rewrite CFk1.
    wstepl. wstepl. wstepl. (* [comment removed for export] *)
    wstepl. notrap.
    zw32_sw CF (k + 1)%Z (zget (d_cftab d) (k + 1) + zget (d_cftab d) k)%Z
      ltac:(rewrite CFk1, CFk; rewrite unsigned_lit by lia; reflexivity).
    rewrite (K_L23_step F L d s (k + 1)) in KQ by lia. replace (k + 1 - 1)%Z with k in KQ by lia.
    wstepl. wstepl. wstepl. (* [comment removed for export] *)
    wstepl; if_cases K2; zify_cond_z K2.
    - pose proof (NXT ltac:(lia)) as NX. unfold S0F_decCutsE.L23cF in NX. revive_all MUL WML AOK.
      kq_fold. enter_cutF NX DP.
      split; [apply eobF_set_cftab; exact EOB | split; [cbn; exact ORIG | split; [lia |]]].
      dmodel_cbn. apply (cf_summed_step' _ _ (k + 1)); [lia | exact CS | f_equal; f_equal; lia].
    - wstepl. wstepl. wstepl. (* [comment removed for export] *)
      replace (k + 1 + 1)%Z with 257%Z in KQ by lia. rewrite (K_L23_exit F L) in KQ.
      revive_all MUL WML AOK. kq_fold.
      enter_cutF (S0F_dec_U11A.U11F_L24_all A AOK F HFAST HSMALL L s J) DP.
      split; [apply eobF_set_cftab; exact EOB | split; [cbn; exact ORIG | split; [lia |]]].
      unfold cfps. dmodel_cbn. apply cf_summed_exit. replace 257%Z with (k + 1 + 1)%Z by lia. apply (cf_summed_step' _ _ (k + 1)); [lia | exact CS | f_equal; f_equal; lia].
  Time Qed.
  Lemma U11F_L23_all : L23cF 0.
  Proof.
    assert (G : forall k : nat, (k <= 255)%nat -> L23cF (255 - Z.of_nat k)%Z).
    { induction k as [|k IH]; intros Hk.
      - apply U11F_L23; [lia| intros; exfalso; lia].
      - apply U11F_L23; [lia| intros _]. replace (255 - Z.of_nat (Datatypes.S k) + 1)%Z with (255 - Z.of_nat k)%Z by lia. apply IH. lia. }
    exact (G 255%nat ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma U11F_L22 : forall k, (0 <= k <= 255)%Z -> ((k < 255)%Z -> L22cF (k + 1)) -> L22cF k.
  Proof.
    intros k Hk NXT. unfold S0F_decCutsE.L22cF. intros until pb. intros DM FR ST MU WM MI DP FU DI.
    prep DM MU DP. cps_destruct DI as (EOB & ORIG & _ & CC). cps_pose EOB as (NBR & NB9 & SYMB & HIST & HDR).
    pose proof (eobF_unz_range L d k EOB ltac:(lia)) as UZk.
    unfold r_of in DR. dr_open.
    hide_all_but_at [S + 68; S + 1096; usp + -336]%Z.
    pose proof (munch_refl [(S + 1096, S + 2124); (usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro.
    wstepl. notrap. wstepl. notrap.
    pose proof (zw32_read s0segs m (S + 68) (d_unzftab d) 256 k _ DRunz ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    wstepl. clear RD. (* [comment removed for export] *)
    wstepl. wstepl.
    zw32_sw CF (k + 1)%Z (zget (d_unzftab d) (k + 1 - 1))%Z
      ltac:(replace (k + 1 - 1)%Z with k by lia; rewrite unsigned_lit by lia; reflexivity).
    rewrite (K_L22_step F L d s (k + 1)) in KQ by lia.
    wstepl. (* [comment removed for export] *)
    wstepl; if_cases K2; zify_cond_z K2.
    - pose proof (NXT ltac:(lia)) as NX. unfold S0F_decCutsE.L22cF in NX. revive_all MUL WML AOK.
      kq_fold. enter_cutF NX DP.
      split; [apply eobF_set_cftab; exact EOB | split; [cbn; exact ORIG | split; [lia |]]].
      dmodel_cbn. apply (cf_copied_step' _ _ (k + 1)); [lia | exact CC | reflexivity].
    - wstepl. wstepl. wstepl. wstepl. (* [comment removed for export] *)
      replace (k + 1 + 1)%Z with 257%Z in KQ by lia. rewrite (K_L22_exit F L) in KQ.
      revive_all MUL WML AOK. kq_fold.
      enter_cutF U11F_L23_all DP.
      split; [apply eobF_set_cftab; exact EOB | split; [cbn; exact ORIG | split; [lia |]]].
      dmodel_cbn. apply cf_summed_1. replace 257%Z with (k + 1 + 1)%Z by lia. apply (cf_copied_step' _ _ (k + 1)); [lia | exact CC | reflexivity].
  Time Qed.
  Lemma U11F_L22_all : L22cF 0.
  Proof.
    assert (G : forall k : nat, (k <= 255)%nat -> L22cF (255 - Z.of_nat k)%Z).
    { induction k as [|k IH]; intros Hk.
      - apply U11F_L22; [lia| intros; exfalso; lia].
      - apply U11F_L22; [lia| intros _]. replace (255 - Z.of_nat (Datatypes.S k) + 1)%Z with (255 - Z.of_nat k)%Z by lia. apply IH. lia. }
    exact (G 255%nat ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma U11F_L21 : forall i, (0 <= i <= 255)%Z -> ((i < 255)%Z -> L21cF (i + 1)) -> L21cF i.
  Proof.
    intros i Hi NXT. unfold S0F_decCutsE.L21cF. intros until pb. intros DM FR ST MU WM MI DP FU DI.
    prep DM MU DP. cps_destruct DI as (EOB & ORIG & _). cps_pose EOB as (NBR & NB9 & SYMB & HIST & HDR).
    pose proof (eobF_unz_range L d i EOB ltac:(lia)) as UZi.
    unfold r_of in DR. dr_open.
    hide_all_but_at [S + 68; S + 1096; usp + -336]%Z.
    pose proof (munch_refl [(S + 1096, S + 2124); (usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro.
    wstepl. notrap. wstepl.
    pose proof (zw32_read s0segs m (S + 68) (d_unzftab d) 256 i _ DRunz ltac:(lia) eq_refl) as RD.
    wstepl. clear RD. (* [comment removed for export] *)
    wstepl; if_cases K1; [ zify_cond_z K1; exfalso; lia | ].
    wstepl; if_cases K1'; [ zify_cond_z K1'; exfalso; lia | ].
    wstepl. wstepl. (* [comment removed for export] *)
    rewrite (K_L21_pass F L d s i) in KQ by lia.
    wstepl; if_cases K2; zify_cond_z K2.
    - pose proof (NXT ltac:(lia)) as NX. unfold S0F_decCutsE.L21cF in NX. revive_all MUL WML AOK.
      kq_fold. enter_cutF NX DP.
      split; [exact EOB | split; [exact ORIG | lia]].
    - wstepl. wstepl. (* [comment removed for export] *)
      zw32_sw CF 0%Z 0%Z ltac:(reflexivity).
      wstepl. wstepl. wstepl. wstepl. wstepl. (* [comment removed for export] *)
      replace (i + 1)%Z with 256%Z in KQ by lia. rewrite (K_L21_exit F L d s) in KQ.
      revive_all MUL WML AOK. kq_fold.
      enter_cutF U11F_L22_all DP.
      split; [apply eobF_set_cftab; exact EOB | split; [cbn; exact ORIG | split; [lia |]]].
      dmodel_cbn. apply cf_copied_1.
  Time Qed.
  Lemma U11F_L21_all : L21cF 0.
  Proof.
    assert (G : forall k : nat, (k <= 255)%nat -> L21cF (255 - Z.of_nat k)%Z).
    { induction k as [|k IH]; intros Hk.
      - apply U11F_L21; [lia| intros; exfalso; lia].
      - apply U11F_L21; [lia| intros _]. replace (255 - Z.of_nat (Datatypes.S k) + 1)%Z with (255 - Z.of_nat k)%Z by lia. apply IH. lia. }
    exact (G 255%nat ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma U11F_entry : L21cF 0 ->
    forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte)
           (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 (S + 2047)) f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192
         (Z_to_bv 64 (S + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (usp + -336) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    dinv_HEOB L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_HEOB F L d s))
      (MS (mkR x1 (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x27910) (a_fc A) None m (seg_rom s0segs)).
  Proof.
    intros NXT. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    prep DM MU DP. destruct DI as [ML EOBsym]. pose proof (eobF_of_ML L d ML) as EOB. cps_pose EOB as (NBR & NB9 & SYMB & HIST & HDR).
    pose proof (alpha_ok_state L d (proj1 ML)) as NST.
    cps_pose HDR as (_ & _ & OPR).
    hide_all_but_at [S; usp + -336]%Z.
    pose proof (munch_refl [(usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro. unfold K_HEOB in KQ. rewrite (K_HEOB_eq F L d s) in KQ.
    wstepl. wstepl. (* [comment removed for export] *)
    wstepl; if_cases K1; [ zify_cond_z K1; exfalso; lia | ]. zify_cond_z K1.
    wstepl; if_cases K2; zify_cond_z K2.
    - (* [comment removed for export] *)
      rewrite if_trueP in KQ by blia.
      wstepl. wstepl. wstepl. wstepl. wstepl. wstepl. revive_all MUL WML AOK.
      kq_fold. enter_cutF (S0F_dec_retc A AOK _ _ _ _ JK_) DP; [ ret_nb | apply dpost14_ne; dmodel_cbn; exact NST ].
    - rewrite if_falseP in KQ by blia.
      wstepl. wstepl. wstepl. wstepl. wstepl. (* [comment removed for export] *)
      revive_all MUL WML AOK. kq_fold. unfold S0F_decCutsE.L21cF in NXT.
      enter_cutF NXT DP. split; [exact EOB | split; [lia | lia]].
  Time Qed.
End R.

(* [comment removed for export] *)
Lemma S0F_dec_U11 : forall A, act_ok 320 A -> forall F, S0F_cut_HFAST A F -> S0F_cut_HSMALL A F -> S0F_cut_HEOB A F.
Proof.
  intros A AOK F HF HS. unfold S0F_cut_HEOB. intros L d s J. intros until pb. intros DM FR ST MU WM MI DP DI FU.
  eapply (U11F_entry A AOK F L s J); first [ exact DM | exact FR | eassumption | eapply (U11F_L21_all A AOK F HF HS L s J) ].
Qed.
End ACeilS1.
