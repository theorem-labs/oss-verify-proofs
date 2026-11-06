(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts BzContracts0 DecCut DecTac DecTac2 DecTacM DecAux DecAuxM S0_dec_U13 S0_dec_U7D.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Musl Require Import S0_memset.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU4 BzDU6 BzDUM BzDU7 DecCutF DecTacF DecTacFR DecTacFR2 S0F_decRet S0F_decCuts7.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU7 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCuts7.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit DecFast DecFastT.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzImg0TacFR BzImg0Tac.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast RelLiaA SasFastF RelLia.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Lemma zw32_clear256 : forall a, zw32 (clear256 256 0 a) 256 = repeat (Z_to_bv 64 0) (Z.to_nat 256).
Proof.
  intros a. apply nth_error_ext. intros k.
  destruct (Nat.lt_ge_cases k (Z.to_nat 256)) as [Hk|Hk].
  - rewrite nth_error_repeat by exact Hk. replace k with (Z.to_nat (Z.of_nat k)) by lia.
    rewrite zw32_nth by lia. rewrite zget_clear256_in by lia. reflexivity.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite zw32_length_nat; lia).
    rewrite (proj2 (nth_error_None _ _)) by (rewrite repeat_length; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Ltac zw32_store_done ARR i v :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?mm ?ga (le4 ?x)) _) =>
      lazymatch type of ARR with u32arr _ _ ?A (zw32 ?a ?n) =>
        let H := fresh "ARR" in
        pose proof (zw32_write segs mm A a n i x v ARR ltac:(lia)
                      ltac:(first [ reflexivity | rewrite unsigned_lit by lia; first [ reflexivity | f_equal; lia ] ])) as H;
        let ga' := lazymatch ga with wa _ => ga | Z_to_bv 64 ?X => constr:(wa X) | _ => ga end in
        replace (wa (A + 4 * i)%Z) with ga' in H by (cbv delta [wa]; first [reflexivity | f_equal; lia | apply f_equal; lia]);
        clear ARR; store_done; rename H into ARR
      end
  end.

Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.
  Hypothesis HL7G : S0F_cut_L7G A F.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Ltac prep DM MU :=
    unfold W14, D14, DSTATE_SIZE in MU; cbn [app blk_ivls b_s b_strm] in MU; open_dmemF DM; s2img.

  (* [comment removed for export] *)
  Notation KFR m j0 f8 f16 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 pb L :=
    (S0FR A m j0 f8 f16 (Z_to_bv 64 (sv_nSelectors L)) f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb) (only parsing).

  (* [comment removed for export] *)
  Definition L7K (ii : Z) : Prop :=
    forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x9 x16 x18 x20 x21 x24 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (j0 : list byte) (f8 f16 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    KFR m j0 f8 f16 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 pb L ->
    stk s0segs m (a_lo A) (usp + -320) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (dinv_L7K L d ii /\ 0 <= ii)%Z ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_L7K F L d s ii))
      (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A) x5 x6 (Z_to_bv 64 (100000 * d_bs100k d)) (Z_to_bv 64 (S + 64036)) x9
              (Z_to_bv 64 (S + 3724)) (Z_to_bv 64 15) (Z_to_bv 64 (16 * ii + 15)) (Z_to_bv 64 (S + 7820)) (Z_to_bv 64 (3855 + 16 * ii))
              (Z_to_bv 64 (3855 + 16 * ii)) x16 (Z_to_bv 64 ii) x18 (Z_to_bv 64 S) x20 x21
              (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (sv_alphaSize L)) x24 (Z_to_bv 64 (sv_nSelectors L)) (Z_to_bv 64 (sv_alphaSize L - 2)) x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1de34) (a_fc A) None m (seg_rom s0segs)).

  (* [comment removed for export] *)
  Definition L7J (ii dd : Z) : Prop :=
    forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x9 x18 x20 x21 x24 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte)
           (j0 : list byte) (f8 f16 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    KFR m j0 f8 f16 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 pb L ->
    stk s0segs m (a_lo A) (usp + -320) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    (dinv_L7J L d ii dd /\ dd <= 15)%Z ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_L7J F L d s ii dd))
      (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A)
              (Z_to_bv 64 (S + 3724 + 3855 + 16 * ii - dd)) (Z_to_bv 64 (16 * ii + 15 - dd)) (Z_to_bv 64 (100000 * d_bs100k d))
              (Z_to_bv 64 (S + 64036)) x9
              (Z_to_bv 64 (S + 3724)) (Z_to_bv 64 15) (Z_to_bv 64 (16 * ii + 15)) (Z_to_bv 64 (S + 7820)) (Z_to_bv 64 (3855 + 16 * ii - dd))
              (Z_to_bv 64 (3855 + 16 * ii)) (Z_to_bv 64 ii) (Z_to_bv 64 (dd - 1)) x18 (Z_to_bv 64 S) x20 x21
              (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 (sv_alphaSize L)) x24 (Z_to_bv 64 (sv_nSelectors L)) (Z_to_bv 64 (sv_alphaSize L - 2)) x27 x28 x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1de44) (a_fc A) None m (seg_rom s0segs)).

  Lemma S0F_U7_K : forall ii, L7J ii 0 -> L7K ii.
  Proof.
    intros ii NX. unfold L7K. intros until pb. intros DM FR ST MU WM MI DP [DI Hii] FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof DI as DI'. cps_destruct DI' as (SEL & TABS & U0 & Hii' & MB & MA).
    pose proof SEL as SEL'. cps_destruct SEL' as ((AL & NBL) & NG & NSC & SOK).
    prep DM MU. kq_intro. rewrite K_L7K_in in KQ by lia.
    (* [comment removed for export] *)
    wstepl. wstepl. wstepl. wstepl.
    enter_sameF NX DP.
    split; [| lia]. unfold dinv_L7J. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
    intros k Hk. apply MA. lia.
  Qed.

  Lemma S0F_U7_J : forall ii dd, L7J ii (dd + 1) -> L7K (ii - 1) -> L7J ii dd.
  Proof.
    intros ii dd NXJ NXK. unfold L7J. intros until pb. intros DM FR ST MU WM MI DP [DI Hdd] FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof DI as DI'. cps_destruct DI' as (SEL & TABS & U0 & Hii & Hdd' & MB & MA).
    pose proof SEL as SEL'. cps_destruct SEL' as ((AL & NBL) & NG & NSC & SOK).
    prep DM MU. kq_intro. rewrite K_L7J_step in KQ by lia.
    replace (ii * 16 + (15 - dd))%Z with (16 * ii + 15 - dd)%Z in KQ by lia.
    unfold r_of in DR. dr_open. hide_all_but_at [S + 3724; S + 7820]%Z.
    pose proof (munch_refl [(S + 3724, S + 7820); (S + 7820, S + 7884)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    (* [comment removed for export] *)
    lazymatch goal with H : u8arr _ _ (S + 3724)%Z _ |- _ =>
      zb8_sb H (3855 + 16 * ii - dd)%Z; try rewrite (Z.mod_small (16 * ii + 15 - dd) 256) in H by lia end.
    (* [comment removed for export] *)
    wstepl. wstepl. try rewrite (addiw_m1 (dd - 1)) by lia. wstepl. wstepl.
    wstepl; if_cases KC; zify_cond_z KC.
    - revive_all_fs MUL WML AOK ltac:(clear - AOK LIN RNL). enter_sameF NXJ DP.
      split; [| lia]. unfold dinv_L7J. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
      all: try (apply (tabs_okF_frame d); [exact TABS| | | |]; dmodel_cbn; reflexivity).
      intros k Hk. rewrite zget_zset. destruct (Z.eqb_spec k (3855 + 16 * ii - dd)); [lia|]. apply MA. lia.
    - (* [comment removed for export] *)
      wstepl. wstepl. wstepl.
      lazymatch goal with H : u32arr _ ?mm (S + 7820)%Z ?ws |- _ =>
        pose proof (u32arr_store_ok s0segs mm (S + 7820) ws ii _ H ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO;
        wstepl; zw32_store_done H ii (3840 + 16 * ii)%Z end.
      try clear SO.
      (* [comment removed for export] *)
      wstepl. wstepl. wstepl.
      wstepl; if_cases K2; zify_cond_z K2.
      + replace (dd + 1)%Z with 16%Z in KQ by lia. rewrite K_L7J_exit in KQ by lia.
        revive_all_fs MUL WML AOK ltac:(clear - AOK LIN RNL). enter_sameF NXK DP.
        split; [| lia]. unfold dinv_L7K. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
        all: try (apply (tabs_okF_frame d); [exact TABS| | | |]; dmodel_cbn; reflexivity).
        all: try (intros l Hl; rewrite zget_zset; destruct (Z.eqb_spec l ii); [lia|]; apply MB; lia).
        all: intros k Hk; rewrite zget_zset; destruct (Z.eqb_spec k (3855 + 16 * ii - dd)); [lia|]; apply MA; lia.
      + (* [comment removed for export] *)
        replace (dd + 1)%Z with 16%Z in KQ by lia. subst ii. rewrite K_L7J_last in KQ.
        revive_all_fs MUL WML AOK ltac:(clear - AOK LIN RNL). enter_sameF HL7G DP.
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
  Lemma S0F_U7_M : L7K 15 -> S0F_cut_H7M A F.
  Proof.
    intros NX. unfold S0F_cut_H7M. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof DI as DI'. destruct DI' as [COM TABS]. pose proof COM as COM'. destruct COM' as [SEL LALL].
    pose proof SEL as SEL'. cps_destruct SEL' as ((AL & NBL) & NG & NSC & SOK).
    prep DM MU. kq_intro. rewrite K_H7M_memset in KQ.
    unfold r_of in DR. dr_open.
    (* [comment removed for export] *)
    wstepl. wstepl. wstepl. wstepl. wstepl.
    hide_all_but_at [S + 68; usp + -320]%Z.
    pose proof (munch_refl ([(S + 68, S + 68 + 1024)] ++ [(usp + -320, usp)])%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    (* [comment removed for export] *)
    wstepl.
    lazymatch goal with H : u32arr _ _ (S + 68)%Z ?ws |- _ =>
      apply u32arr_to_CB in H; replace (4 * length ws)%nat with (Z.to_nat 1024) in H by (rewrite zw32_length_nat; lia);
      rename H into UNZcb end.
    eapply evt_cut.
    { eapply (S0_memset_specZ (S + 68) 1024 0); [ exact UNZcb | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia ]. }
    intros ms' PO. unfold S0_memsetZ_post in PO.
    cps_destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & Ems & MUc & WMc & MIc & UNZ').
    subst ms'.
    replace (ret_pc (Z_to_bv 64 122356)) with (Z_to_bv 64 122356) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    lazymatch type of MUL with munch ?Wq _ _ =>
      pose proof (munch_weaken _ Wq m m' (sub_fp_app_l _ _) MUc) as MULn end.
    clear MUL. rename MULn into MUL. cbn [app] in MUL.
    lazymatch type of MU with munch ?W14 ?m0 _ =>
    lazymatch type of MUc with munch ?Wc _ _ =>
      assert (SUB14 : sub_fp Wc W14) by (lin_unbox LIN; clear - LIN; sub_fp_solve);
      apply (munch_trans W14 m0 m m') in MU; [ | exact (munch_weaken Wc W14 m m' SUB14 MUc) ]; clear SUB14 end end.
    apply (wmono_trans s0segs _ m m') in WM; [ | exact WMc ].
    clear WML. pose proof WMc as WML.
    lazymatch type of MUc with munch ?Wc _ _ =>
      apply (rw_cells_transport s0segs Wc m m') in FR; [ | exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; lia ];
      apply (stk_transport_disjoint s0segs Wc m m') in ST; [ | exact MUc | exact WMc | cbn [disjoint_from]; lia ] end.
    clear UNZcb MI MUc WMc.
    change (Z.to_nat 1024) with (4 * 256)%nat in UNZ'. rewrite <- (u32s_repeat_zero 256) in UNZ'. apply u32arr_of_CB in UNZ'.
    change 256%nat with (Z.to_nat 256) in UNZ'. rewrite <- (zw32_clear256 (d_unzftab d)) in UNZ'.
    (* [comment removed for export] *)
    do 16 wstepl.
    revive_all_fs MUL WML AOK ltac:(clear - AOK LIN RNL). enter_sameF NX DP.
    split; [| lia]. unfold dinv_L7K. dmodel_cbn. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
    all: try (apply (tabs_okF_frame d); [exact TABS| | | |]; dmodel_cbn; reflexivity).
    all: try apply unz0_clear.
    all: intros; exfalso; lia.
  Qed.
End R.

Lemma S0F_U7_mtf : forall A, act_ok 320 A -> forall F, S0F_cut_L7G A F -> S0F_cut_H7M A F.
Proof.
  intros A AOK F HL7G. apply (S0F_U7_M A AOK F).
  assert (J : forall ii, L7K A F (ii - 1) -> forall k : nat, forall dd, (15 - Z.of_nat k <= dd)%Z -> L7J A F ii dd).
  { intros ii NXK. induction k as [|k IH]; intros dd Hdd.
    - (* [comment removed for export] *)
      apply (S0F_U7_J A AOK F HL7G); [| exact NXK].
      unfold L7J. intros until pb. intros DM FR ST MU WM MI DP [DI Hdd2] FU. exfalso. cbn in Hdd. lia.
    - apply (S0F_U7_J A AOK F HL7G); [| exact NXK]. apply IH. lia. }
  assert (K : forall k : nat, forall ii, (ii <= Z.of_nat k - 1)%Z -> L7K A F ii).
  { induction k as [|k IH]; intros ii Hii.
    - unfold L7K. intros until pb. intros DM FR ST MU WM MI DP [DI Hii2] FU. exfalso. cbn in Hii. lia.
    - apply (S0F_U7_K A AOK F). apply (J ii ltac:(apply IH; lia) 16%nat). cbn; lia. }
  apply (K 16%nat). cbn; lia.
Qed.

End ACeilS1.
