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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts BzContracts0 DecCut DecTac DecTac2 DecAux S0_dec_U13.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU2 BzDU4 DecCutF DecTacF DecTacFR S0F_decRet S0F_decCuts S0F_decCuts4.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCuts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCuts4.
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
Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.
  Hypothesis HSEL : S0F_cut_HSEL A F.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  (* [comment removed for export] *)
  Definition L4Mcut (i : Z) : Prop :=
    forall (L : dsv) (d : dst) (s : dstrm) (J : jk)
           (x1 x5 x6 x7 x9 x15 x16 x17 x18 x20 x21 x23 x24 x25 x26 x27 x29 x30 x31 : word)
           (m : word -> option byte)
           (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f136 f144 f152 f160 f168 f176 f184 f192 f200 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
         (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 7820))
         f136 f144 f152 f160 f168 f176 f184 f192 f200 pb ->
    stk s0segs m (a_lo A) (usp + -320) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    dinv_L4M L d i ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_L4M F L d s i))
      (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A) x5 x6 x7 (Z_to_bv 64 (S + 64036)) x9
              (Z_to_bv 64 (d_nInUse d)) (Z_to_bv 64 i) (Z_to_bv 64 (S + 3196)) (Z_to_bv 64 (S + 3468)) (Z_to_bv 64 256) x15 x16 x17
              x18 (Z_to_bv 64 S) x20 x21
              (Z_to_bv 64 (S + 2047)) x23 x24 x25 x26 x27 (Z_to_bv 64 (sv_nblock L)) x29 x30 x31)
          (a_F A) (Z_to_bv 64 0x1d878) (a_fc A) None m (seg_rom s0segs)).

  (* [comment removed for export] *)
  Lemma S0F_U4_L4M_body : forall i, (0 <= i <= 255)%Z -> ((i < 255)%Z -> L4Mcut (i + 1)) -> L4Mcut i.
  Proof.
    intros i Hi NXT. unfold L4Mcut. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold W14, D14, DSTATE_SIZE in MU. cbn [app blk_ivls b_s b_strm] in MU.
    cps_destruct DI as (NB & HDR & IU & _ & Hn & NS2). unfold nb_ok in NB.
    pose proof (dpureF_rep _ _ _ _ _ _ DP) as REP. unfold drep in REP. cps_destruct REP as (_ & _ & _ & RS2U & _).
    open_dmemF DM. s2img. unfold r_of in DR. dr_open. kq_intro.
    hide_all_but_at [S + 3152; S + 3196; S + 3468]%Z.
    pose proof (munch_refl [(S + 3152, S + 3196); (S + 3468, S + 3724)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    (* [comment removed for export] *)
    wstepl.
    lazymatch goal with H : u8arr _ ?mm (S + 3196)%Z (zb8 ?a ?n) |- _ =>
      pose proof (zb8_read1 s0segs mm (S + 3196) a n i _ H ltac:(lia) eq_refl) as RD end.
    pose proof (IU i ltac:(lia)) as Bi.
    wstepl. clear RD. rewrite zxb_lit8 by lia.
    (* [comment removed for export] *)
    Ltac tail i NXT HSEL MUL WML DP NS2 :=
      wstepl;
      let KL := fresh "KL" in
      wstepl; if_cases KL; zify_cond_z KL;
      [ (* [comment removed for export] *)
        revive_all MUL WML AOK; kq_fold;
        enter_cutF (NXT ltac:(lia) _ _ _ JK_) DP
      | (* [comment removed for export] *)
        match goal with KQ : kq _ _ |- _ =>
          replace (i + 1)%Z with 256%Z in KQ by lia end;
        let KZ := fresh "KZ" in
        wstepl; if_cases KZ; zify_cond_z KZ;
        [ match goal with KQ : kq _ _ |- _ => rewrite K_L4M_exit_ret in KQ by (dmodel_cbn; unset_Z; lia) end;
          revive_all MUL WML AOK; kq_fold; enter_cutF (S0F_dec_ret_data A AOK _ _ _ JK_) DP;
          [ ret_nb | apply dpost14_ne; dmodel_cbn; exact NS2 ]
        | match goal with KQ : kq _ _ |- _ => rewrite K_L4M_exit_go in KQ by (dmodel_cbn; unset_Z; lia) end;
          wstepl; revive_all MUL WML AOK; enter_sameF HSEL DP ] ].
    wstepl; if_cases Kb; zify_cond_z Kb.
    - (* [comment removed for export] *)
      rewrite K_L4M_skip in KQ by lia.
      tail i NXT HSEL MUL WML DP NS2.
      + unfold dinv_L4M, nb_ok. split; [lia|]. split; [apply (hdr_ok_frame _ _ HDR); dmodel_cbn; reflexivity|]. split; [exact IU|]. split; [lia|]. split; [lia| exact NS2].
      + unfold dinv_HSEL, alpha_ok, hdr_ok in *. dmodel_cbn. unset_Z. lia.
    - (* [comment removed for export] *)
      rewrite K_L4M_set in KQ by lia.
      wstepl.
      lazymatch goal with H : u8arr _ _ (S + 3468)%Z _ |- _ => zb8_sb H (d_nInUse d) end.
      wstepl. wstepl. wstepl.
      (* [comment removed for export] *)
      assert (RS2U' : forall k, (0 <= zget (zset (d_s2u d) (d_nInUse d) i) k < 256)%Z).
      { intros k. rewrite zget_zset. destruct (Z.eqb_spec k (d_nInUse d)); [lia| apply RS2U]. }
      tail i NXT HSEL MUL WML DP NS2.
      + unfold dinv_L4M, nb_ok. dmodel_cbn. split; [lia|]. split; [apply (hdr_ok_frame _ _ HDR); dmodel_cbn; reflexivity|]. split; [apply inUse_ok_frame_s2u; exact IU|]. split; [lia|]. split; [lia| exact NS2].
      + unfold dinv_HSEL, alpha_ok, hdr_ok in *. dmodel_cbn. unset_Z. lia.
  Qed.

  Lemma S0F_dec_U4C : S0F_cut_HMK A F.
  Proof.
    assert (G : forall k : nat, (k <= 255)%nat -> L4Mcut (255 - Z.of_nat k)%Z).
    { induction k as [|k IH]; intros Hk.
      - apply S0F_U4_L4M_body; [lia | intros; exfalso; lia].
      - apply S0F_U4_L4M_body; [lia | intros _].
        replace (255 - Z.of_nat (Datatypes.S k) + 1)%Z with (255 - Z.of_nat k)%Z by lia. apply IH. lia. }
    pose proof (G 255%nat ltac:(lia)) as G0. change (255 - Z.of_nat 255)%Z with 0%Z in G0. unfold L4Mcut in G0.
    unfold S0F_cut_HMK. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold W14, D14, DSTATE_SIZE in MU. cbn [app blk_ivls b_s b_strm] in MU.
    cps_destruct DI as (NB & HDR & IU & NS2). unfold nb_ok in NB.
    open_dmemF DM. s2img. kq_intro. rewrite K_HMK_L4M in KQ.
    hide_all_but_at [S + 3152]%Z.
    pose proof (munch_refl [(S + 3152, S + 3196)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    (* [comment removed for export] *)
    wstepl. wstepl. wstepl. wstepl. wstepl. wstepl.
    revive_all MUL WML AOK. enter_sameF G0 DP.
    unfold dinv_L4M, nb_ok. dmodel_cbn. split; [lia|]. split; [apply (hdr_ok_frame _ _ HDR); dmodel_cbn; reflexivity|]. split; [exact IU|]. split; [lia|]. split; [lia| exact NS2].
  Qed.
End R.
End ACeilS1.
