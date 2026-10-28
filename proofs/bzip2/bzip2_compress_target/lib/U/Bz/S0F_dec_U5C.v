(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 DecCut DecTac DecTac2 DecAux S0_dec_U13 S2_dec_U5C.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR S0F_decRet S0F_decCuts.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts.
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
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition pos_ag (pb : list byte) (pos : zarr) (n : Z) : Prop :=
  length pb = 8%nat /\ forall k, (0 <= k < n)%Z -> nth_error pb (Z.to_nat (2 + k)) = Some (Z_to_bv 8 (zget pos k)).
(* [comment removed for export] *)
Definition pos_okz (pos : zarr) (ng : Z) : Prop := forall k, (0 <= k < ng)%Z -> (0 <= zget pos k < ng)%Z.

Lemma pos_ag_set : forall pb pos n k x n', pos_ag pb pos n -> (0 <= k < 6)%Z -> (n' <= 6)%Z ->
  (forall j, 0 <= j < n' -> j <> k -> j < n)%Z ->
  pos_ag (upd pb (Z.to_nat (2 + k)) (Z_to_bv 8 x)) (zset pos k x) n'.
Proof.
  intros pb pos n k x n' [L P] Hk Hn' Hj. split; [rewrite upd_length; exact L|].
  intros j Hjr. rewrite zget_zset. destruct (Z.eqb_spec j k) as [->|NE].
  - apply nth_error_upd_same. rewrite L. lia.
  - rewrite nth_error_upd_other by lia. apply P. specialize (Hj j Hjr NE). lia.
Qed.
(* [comment removed for export] *)

Lemma pos_okz_init : forall pos v, (forall k, 0 <= k < v -> zget pos k = k)%Z -> pos_okz pos v.
Proof. intros pos v H k Hk. rewrite H by lia. lia. Qed.
Lemma pos_okz_set : forall pos ng k x, pos_okz pos ng -> (0 <= x < ng)%Z -> pos_okz (zset pos k x) ng.
Proof. intros pos ng k x P Hx j Hj. rewrite zget_zset. destruct (Z.eqb_spec j k); [lia| apply P; lia]. Qed.
Lemma pos_ag_nil : forall pb pos, length pb = 8%nat -> pos_ag pb pos 0.
Proof. intros pb pos L. split; [exact L|]. intros k Hk. exfalso. lia. Qed.

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.
  Hypothesis HCOD : S0F_cut_HCOD A F.
  (* [comment removed for export] *)
  Variables (L : dsv) (s : dstrm) (J : jk).
  Notation ng := (sv_nGroups L).
  Notation ns := (sv_nSelectors L).
  Notation nsc := (Z.min (sv_nSelectors L) 18002).
  Hypothesis NG : (2 <= sv_nGroups L <= 6)%Z.
  Hypothesis NS : (1 <= sv_nSelectors L < 32768)%Z.
  Hypothesis NBL : (0 <= sv_nblock L <= 900000)%Z.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  (* [comment removed for export] *)
  Notation FRA mm j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 :=
    (rw_cells s0segs mm (bv_unsigned (a_sp A) + -336)
      [CB 8 j0; C8 f8; C8 f16; C8 f24; C8 f32; C8 f40; C8 f48; C8 f56; C8 f64; C8 f72; C8 f80; C8 (Z_to_bv 64 (b_s (a_cx A) + 2047));
       C8 f96; C8 f104; C8 f112; C8 f120; C8 f128; C8 f136; C8 f144; C8 f152; C8 f160; C8 f168; C8 f176; C8 f184; C8 f192;
       C8 (Z_to_bv 64 (b_s (a_cx A) + 7820)); C8 f208; C8 f216]) (only parsing).
  Notation FRC mm :=
    (rw_cells s0segs mm (bv_unsigned (a_sp A) + -104)
      [C8 (a_s11 A); C8 (a_s10 A); C8 (a_s9 A); C8 (a_s8 A); C8 (a_s7 A); C8 (a_s6 A); C8 (a_s5 A);
       C8 (a_s4 A); C8 (a_s3 A); C8 (a_s2 A); C8 (a_s1 A); C8 (a_s0 A); C8 (a_ra A)]) (only parsing).

  (* [comment removed for export] *)
  Notation COMMONF mm dd pb K :=
    (dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) mm (dvF cx J dd s) ->
     u8arr s0segs mm (usp + -112) pb ->
     FRC mm ->
     stk s0segs mm (a_lo A) (usp + -336) ->
     munch (W14 DI_S0 cx usp) (a_m0 A) mm -> wmono s0segs (a_m0 A) mm -> mem_inv s0segs mm ->
     dpureF cx (a_b0 A) (a_payload A) J dd s ->
     fuel_ok F dd s ->
     alpha_ok L dd -> belown (d_selMtf dd) nsc ng -> K) (only parsing).

  (* [comment removed for export] *)
  Definition LP1cutF (v : Z) (pos : zarr) : Prop :=
    forall (x5 x6 x7 x8 x9 x14 x15 x16 x17 x19 x21 x24 x25 x27 x28 x29 x31 : word)
           (d : dst) (m : word -> option byte)
           (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    FRA m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 ->
    COMMONF m d pb (
    (0 <= v <= ng)%Z -> pos_ag pb pos v -> (forall k, 0 <= k < v -> zget pos k = k)%Z ->
    evt s0segs (QF A (K_LP1 F L d s nsc v pos))
      (MS (mkR (Z_to_bv 64 ng) (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9
              (Z_to_bv 64 ns) (Z_to_bv 64 v) (Z_to_bv 64 6) (Z_to_bv 64 (usp + -110)) x14 x15 x16 x17
              (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (sv_alphaSize L))
              x24 x25 (Z_to_bv 64 nsc) x27 x28 x29 (Z_to_bv 64 (S + 7884)) x31)
          (a_F A) (Z_to_bv 64 0x26738) (a_fc A) None m (seg_rom s0segs))).

  (* [comment removed for export] *)
  Definition LP2cutF (i : Z) (pos : zarr) : Prop :=
    forall (x5 x6 x7 x8 x9 x19 x21 x24 x25 x27 x28 x29 x31 : word)
           (d : dst) (m : word -> option byte)
           (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    FRA m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 ->
    COMMONF m d pb (
    pos_ag pb pos ng -> pos_okz pos ng -> (0 <= i <= nsc)%Z -> belown (d_sel d) i ng ->
    evt s0segs (QF A (K_LP2 F L d s nsc i pos))
      (MS (mkR (Z_to_bv 64 ng) (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9
              (Z_to_bv 64 i) (Z_to_bv 64 5) (Z_to_bv 64 4294967295) (Z_to_bv 64 (S + 25886)) (Z_to_bv 64 (S + 7884))
              (Z_to_bv 64 (18446744073709551615 - (S + 25886))) (Z_to_bv 64 (18446744073709551615 - (S + 7884))) (Z_to_bv 64 (usp + -110))
              (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (sv_alphaSize L))
              x24 x25 (Z_to_bv 64 nsc) x27 x28 x29 (Z_to_bv 64 (S + 7884)) x31)
          (a_F A) (Z_to_bv 64 0x26788) (a_fc A) None m (seg_rom s0segs))).

  (* [comment removed for export] *)
  Definition X8cutF (pos : zarr) : Prop :=
    forall (x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x19 x21 x24 x25 x27 x28 x29 x31 : word)
           (d : dst) (m : word -> option byte)
           (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    FRA m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 ->
    COMMONF m d pb (
    pos_ag pb pos ng -> pos_okz pos ng -> belown (d_sel d) 0 ng ->
    evt s0segs (QF A (K_LP2 F L d s nsc 0 pos))
      (MS (mkR (Z_to_bv 64 ng) (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9
              (Z_to_bv 64 ns) x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (sv_alphaSize L))
              x24 x25 (Z_to_bv 64 nsc) x27 x28 x29 (Z_to_bv 64 (S + 7884)) x31)
          (a_F A) (Z_to_bv 64 0x26750) (a_fc A) None m (seg_rom s0segs))).

  (* [comment removed for export] *)
  Definition LP3cutF (i : Z) (pos : zarr) (tmp w : Z) : Prop :=
    forall (x7 x8 x9 x19 x21 x24 x25 x27 x28 x29 x31 : word)
           (d : dst) (m : word -> option byte)
           (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    FRA m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 ->
    COMMONF m d pb (
    pos_ag pb pos ng -> pos_okz pos ng -> (0 <= i < nsc)%Z -> belown (d_sel d) i ng -> (0 <= tmp < ng)%Z -> (1 <= w < ng)%Z ->
    evt s0segs (QF A (K_LP3 F L d s nsc i pos tmp w))
      (MS (mkR (Z_to_bv 64 ng) (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) (Z_to_bv 64 tmp) (Z_to_bv 64 w) x7 x8 x9
              (Z_to_bv 64 i) (Z_to_bv 64 5) (Z_to_bv 64 4294967295) (Z_to_bv 64 (S + 25886)) (Z_to_bv 64 (S + 7884))
              (Z_to_bv 64 (18446744073709551615 - (S + 25886))) (Z_to_bv 64 (18446744073709551615 - (S + 7884))) (Z_to_bv 64 (usp + -110))
              (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (sv_alphaSize L))
              x24 x25 (Z_to_bv 64 nsc) x27 x28 x29 (Z_to_bv 64 (S + 7884)) x31)
          (a_F A) (Z_to_bv 64 0x267ac) (a_fc A) None m (seg_rom s0segs))).

  (* [comment removed for export] *)
  Definition X78cutF (i : Z) (pos : zarr) (tmp : Z) : Prop :=
    forall (x6 x7 x8 x9 x19 x21 x24 x25 x27 x28 x29 x31 : word)
           (d : dst) (m : word -> option byte)
           (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    FRA m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 ->
    COMMONF m d pb (
    pos_ag pb pos ng -> pos_okz pos ng -> (0 <= i < nsc)%Z -> belown (d_sel d) i ng -> (0 <= tmp < ng)%Z ->
    evt s0segs (QF A (K_X78 F L d s nsc i pos tmp))
      (MS (mkR (Z_to_bv 64 ng) (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) (Z_to_bv 64 tmp) x6 x7 x8 x9
              (Z_to_bv 64 i) (Z_to_bv 64 5) (Z_to_bv 64 4294967295) (Z_to_bv 64 (S + 25886)) (Z_to_bv 64 (S + 7884))
              (Z_to_bv 64 (18446744073709551615 - (S + 25886))) (Z_to_bv 64 (18446744073709551615 - (S + 7884))) (Z_to_bv 64 (usp + -110))
              (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (sv_alphaSize L))
              x24 x25 (Z_to_bv 64 nsc) x27 x28 x29 (Z_to_bv 64 (S + 7884)) x31)
          (a_F A) (Z_to_bv 64 0x267dc) (a_fc A) None m (seg_rom s0segs))).

  Ltac prep DM MU :=
    unfold W14, D14, DSTATE_SIZE in MU; cbn [app blk_ivls b_s b_strm] in MU; open_dmemF DM; s2img.

  (* [comment removed for export] *)
  Ltac enter_cutP NXT DP :=
    eapply evt_eq; [ | eapply NXT ]; only 1: unify_memF; try cut_sideF DP; only 1: (dvF_cbn; dmodel_cbn; st_eq);
    try match goal with H : u8arr _ ?mm ?a _ |- u8arr _ ?mm ?a _ => exact H end;
    try match goal with H : rw_cells _ ?mm ?a _ |- rw_cells _ ?mm ?a _ => exact H end;
    try assumption; try (dmodel_cbn; assumption); try (cbn; lia).

  (* [comment removed for export] *)
  Ltac u8st ARR A i :=
    lazymatch goal with |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of ARR with u8arr _ _ _ ?bs =>
      pose proof (u8arr_store_ok sg mm A bs i _ ARR ltac:(lia) eq_refl) as SO;
      step; u8_store_doneA ARR i; try clear SO; zsimp; bz32l
    end end.

  Lemma S0F_U5_LP1 : forall v pos, (0 <= v < ng)%Z ->
    ((v + 1 < ng)%Z -> LP1cutF (v + 1) (zset pos v v)) -> X8cutF (zset pos v v) -> LP1cutF v pos.
  Proof.
    intros v pos Hv NXT X8. unfold LP1cutF. intros until pb. intros FRa DM POS FRc ST MU WM MI DP FU AL SOK Hv' PAG PK.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL. prep DM MU.
    hide_all_but_at [usp + -112]%Z.
    pose proof (munch_refl [(usp + -112, usp + -104)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    destruct PAG as [LPB PAG].
    (* [comment removed for export] *)
    wstepl. notrap. wstepl.
    u8st POS (usp + -112)%Z (2 + v)%Z.
    rewrite unsigned_lit in POS by lia. rewrite (Z.mod_small v 256) in POS by lia.
    assert (PAG' : pos_ag (upd pb (Z.to_nat (2 + v)) (Z_to_bv 8 v)) (zset pos v v) (v + 1))
      by (apply (pos_ag_set pb pos v); [split; [exact LPB| exact PAG] | lia | lia | intros; lia]).
    assert (PK' : forall k, (0 <= k < v + 1 -> zget (zset pos v v) k = k)%Z)
      by (intros k Hk; rewrite zget_zset; destruct (Z.eqb_spec k v); [lia| apply PK; lia]).
    rewrite K_LP1_step by lia.
    (* [comment removed for export] *)
    wstepl. wstepl; if_cases K; zify_cond_z K.
    - pose proof (NXT ltac:(lia)) as NX. unfold LP1cutF in NX. revive_all MUL WML AOK.
      enter_cutP NX DP.
    - unfold X8cutF in X8. revive_all MUL WML AOK.
      rewrite K_LP1_exit by lia.
      enter_cutP X8 DP.
      + replace ng with (v + 1)%Z by lia. exact PAG'.
      + apply pos_okz_init. replace ng with (v + 1)%Z by lia. exact PK'.
      + apply belown_0.
  Qed.

  Lemma S0F_U5_X8 : forall pos, LP2cutF 0 pos -> X8cutF pos.
  Proof.
    intros pos NXT. unfold X8cutF. intros until pb. intros FRa DM POS FRc ST MU WM MI DP FU AL SOK PAG POK SEL.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL. prep DM MU.
    (* [comment removed for export] *)
    wstepl. if_false_z. do 13 wstepl.
    unfold LP2cutF in NXT. enter_cutP NXT DP.
  Qed.

  Lemma S0F_U5_X78 : forall i pos tmp, (0 <= i < nsc)%Z ->
    ((i + 1 < nsc)%Z -> LP2cutF (i + 1) (zset pos 0 tmp)) -> X78cutF i pos tmp.
  Proof using ACEIL__ A AOK F HCOD L s J NG NS NBL.
    intros i pos tmp Hi NXT. unfold X78cutF. intros until pb. intros FRa DM POS FRc ST MU WM MI DP FU AL SOK PAG POK Hi' SEL TMP.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL. prep DM MU.
    unfold r_of in DR. dr_open. hide_all_but_at [usp + -112; S + 7884]%Z.
    pose proof (munch_refl [(usp + -112, usp + -104); (S + 7884, S + 25886)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    destruct PAG as [LPB PAG].
    (* [comment removed for export] *)
    u8st POS (usp + -112)%Z 2%Z.
    rewrite unsigned_lit in POS by lia. rewrite (Z.mod_small tmp 256) in POS by lia.
    assert (PAG' : pos_ag (upd pb (Z.to_nat 2) (Z_to_bv 8 tmp)) (zset pos 0 tmp) ng).
    { replace (Z.to_nat 2) with (Z.to_nat (2 + 0)) by lia.
      apply (pos_ag_set pb pos ng); [split; [exact LPB| exact PAG] | lia | lia | intros; lia]. }
    assert (POK' : pos_okz (zset pos 0 tmp) ng) by (apply pos_okz_set; [exact POK| lia]).
    (* [comment removed for export] *)
    wstepl. notrap. wstepl. wstepl.
    lazymatch goal with H : u8arr _ _ (S + 7884)%Z _ |- _ =>
      zb8_sb H i; try rewrite (Z.mod_small tmp 256) in H by lia end.
    unfold K_X78.
    (* [comment removed for export] *)
    wstepl; if_cases K; zify_cond_z K.
    - pose proof (NXT ltac:(lia)) as NX. unfold LP2cutF in NX. revive_all MUL WML AOK.
      enter_cutP NX DP.
      dmodel_cbn. apply belown_set; [exact SEL| lia].
    - (* [comment removed for export] *)
      wstepl. wstepl. wstepl.
      revive_all MUL WML AOK.
      rewrite K_LP2_exit_HCOD by lia.
      lazymatch goal with H : u8arr _ _ (usp + -112)%Z ?bs |- _ =>
        apply rw_cells_of_u8arr in H; rewrite upd_length, LPB in H; rename H into FRm end.
      rw_join3 FRa FRm FRc.
      unfold S0F_cut_HCOD in HCOD. enter_cutF (HCOD _ _ _ JK_) DP.
      pose proof AL as AL'. unfold alpha_ok in AL'.
      unfold dinv_HCOD, L_cod, alpha_ok. dmodel_cbn.
      repeat match goal with |- _ /\ _ => split end; try lia.
      replace (Z.min ns 18002) with (i + 1)%Z by lia. apply belown_set; [exact SEL| lia].
  Qed.

  Lemma S0F_U5_LP3 : forall i pos tmp w, (0 <= i < nsc)%Z -> (1 <= w < ng)%Z ->
    ((1 <= w - 1)%Z -> LP3cutF i (zset pos w (zget pos (w - 1))) tmp (w - 1)) ->
    X78cutF i (zset pos w (zget pos (w - 1))) tmp -> LP3cutF i pos tmp w.
  Proof.
    intros i pos tmp w Hi Hw NXT X78. unfold LP3cutF. intros until pb.
    intros FRa DM POS FRc ST MU WM MI DP FU AL SOK PAG POK Hi' SEL TMP Hw'.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL. prep DM MU.
    hide_all_but_at [usp + -112]%Z.
    pose proof (munch_refl [(usp + -112, usp + -104)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    destruct PAG as [LPB PAG].
    (* [comment removed for export] *)
    wstepl. rewrite (land255_small w) by lia. wstepl. wstepl. rewrite (land_w32 w) by lia. wstepl. notrap. wstepl.
    pose proof (POK (w - 1)%Z ltac:(lia)) as Bb.
    pose proof (u8arr_read s0segs _ (usp + -112) pb (2 + (w - 1))%Z (Z_to_bv 8 (zget pos (w - 1))) _ POS (PAG (w - 1)%Z ltac:(lia)) ltac:(lia) eq_refl) as RD.
    wstepl. clear RD. rewrite zxb_lit8 by lia.
    (* [comment removed for export] *)
    wstepl. wstepl. wstepl. rewrite (land255_small (w + -1)) by lia.
    u8st POS (usp + -112)%Z (2 + w)%Z.
    rewrite unsigned_lit in POS by lia. rewrite (Z.mod_small (zget pos (w - 1)) 256) in POS by lia.
    assert (PAG' : pos_ag (upd pb (Z.to_nat (2 + w)) (Z_to_bv 8 (zget pos (w - 1)))) (zset pos w (zget pos (w - 1))) ng)
      by (apply (pos_ag_set pb pos ng); [split; [exact LPB| exact PAG] | lia | lia | intros; lia]).
    assert (POK' : pos_okz (zset pos w (zget pos (w - 1))) ng) by (apply pos_okz_set; [exact POK| lia]).
    rewrite K_LP3_step by lia.
    (* [comment removed for export] *)
    wstepl; if_cases K; zify_cond_z K.
    - pose proof (NXT ltac:(lia)) as NX. unfold LP3cutF in NX. revive_all MUL WML AOK.
      rewrite if_trueP by blia.
      enter_cutP NX DP.
    - unfold X78cutF in X78. revive_all MUL WML AOK.
      rewrite if_falseP by blia.
      enter_cutP X78 DP.
  Qed.

  Lemma S0F_U5_LP2 : forall i pos, (0 <= i < nsc)%Z ->
    (forall tmp w, (0 <= tmp < ng)%Z -> (1 <= w < ng)%Z -> LP3cutF i pos tmp w) ->
    (forall tmp, (0 <= tmp < ng)%Z -> X78cutF i pos tmp) -> LP2cutF i pos.
  Proof.
    intros i pos Hi LP3 X78. unfold LP2cutF. intros until pb. intros FRa DM POS FRc ST MU WM MI DP FU AL SOK PAG POK Hi' SEL.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL. prep DM MU.
    unfold r_of in DR. dr_open. hide_all_but_at [usp + -112; S + 25886; S + 7884]%Z.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    pose proof PAG as PAG0. destruct PAG as [LPB PAG].
    pose proof (SOK i ltac:(lia)) as Bv. set (v := zget (d_selMtf d) i) in Bv.
    (* [comment removed for export] *)
    wstepl. notrap. wstepl.
    lazymatch goal with H : u8arr _ ?mm (S + 25886)%Z (zb8 ?a ?n) |- _ =>
      pose proof (zb8_read1 s0segs mm (S + 25886) a n i _ H ltac:(lia) eq_refl) as RD end.
    wstepl. clear RD. fold v. rewrite zxb_lit8 by lia.
    (* [comment removed for export] *)
    wstepl. notrap. wstepl.
    pose proof (POK v ltac:(lia)) as Bt.
    pose proof (u8arr_read s0segs _ (usp + -112) pb (2 + v)%Z (Z_to_bv 8 (zget pos v)) _ POS (PAG v ltac:(lia)) ltac:(lia) eq_refl) as RD.
    wstepl. clear RD. rewrite zxb_lit8 by lia.
    rewrite (K_LP2_step F L d s nsc i pos) by lia. fold v.
    (* [comment removed for export] *)
    wstepl; if_cases Kv0; zify_cond Kv0.
    - (* [comment removed for export] *)
      rewrite if_falseP by blia.
      pose proof (X78 (zget pos v) Bt) as NX. unfold X78cutF in NX. revive_all MUL WML AOK.
      enter_cutP NX DP.
    - (* [comment removed for export] *)
      rewrite if_trueP by blia.
      pose proof (LP3 (zget pos v) v Bt ltac:(lia)) as NX. unfold LP3cutF in NX. revive_all MUL WML AOK.
      enter_cutP NX DP.
  Qed.

  (* [comment removed for export] *)
  Lemma S0F_U5_entry : LP1cutF 0 znew ->
    forall (x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x19 x21 x24 x25 x26 x27 x28 x29 x31 : word)
           (d : dst) (m : word -> option byte)
           (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192 f208 f216 : word) (pb : list byte),
    dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
    S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 (Z_to_bv 64 (S + 2047)) f96 f104 f112 f120 f128 f136 f144 f152 f160 f168 f176 f184 f192
         (Z_to_bv 64 (S + 7820)) f208 f216 pb ->
    stk s0segs m (a_lo A) (usp + -336) ->
    munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
    dpureF cx (a_b0 A) (a_payload A) J d s ->
    dinv_HUND L d ->
    fuel_ok F d s ->
    evt s0segs (QF A (K_HUND F L d s))
      (MS (mkR (Z_to_bv 64 ng) (Z_to_bv 64 (usp + -336)) (a_gp A) (a_tp A) x5 x6 x7 x8 x9
              (Z_to_bv 64 ns) x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 S) x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 (sv_nblock L)) (Z_to_bv 64 (sv_alphaSize L))
              x24 x25 x26 x27 x28 x29 (Z_to_bv 64 (S + 7884)) x31)
          (a_F A) (Z_to_bv 64 0x26714) (a_fc A) None m (seg_rom s0segs)).
  Proof.
    intros NXT. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL. prep DM MU.
    destruct DI as [AL [_ [_ SOK]]].
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ ?cs =>
      assert (LPB : length pb = 8%nat)
        by (eapply (rw_cells_CB_length s0segs m _ (firstn 28 cs) 8 pb (skipn 29 cs)); cbn [firstn skipn app]; exact FR) end.
    rewrite K_HUND_LP1, nsel_clamp_eq.
    (* [comment removed for export] *)
    wstepl. wstepl. wstepl.
    wstepl; if_cases K; zify_cond_z K.
    - (* [comment removed for export] *) wstepl. if_false_z. wstepl. wstepl. wstepl.
      rw_split3 FR 28%nat FRm FRc.
      lazymatch type of FRm with rw_cells _ _ ?a _ => replace a with (usp + -112)%Z in FRm by lia end.
      lazymatch type of FRc with rw_cells _ _ ?a _ => replace a with (usp + -104)%Z in FRc by lia end.
      apply u8arr_of_rw_cells in FRm.
      unfold LP1cutF in NXT. enter_cutP NXT DP.
      all: try (apply pos_ag_nil; exact LPB). all: intros k Hk; exfalso; lia.
    - wstepl. wstepl. if_false_z. wstepl. wstepl. wstepl.
      rw_split3 FR 28%nat FRm FRc.
      lazymatch type of FRm with rw_cells _ _ ?a _ => replace a with (usp + -112)%Z in FRm by lia end.
      lazymatch type of FRc with rw_cells _ _ ?a _ => replace a with (usp + -104)%Z in FRc by lia end.
      apply u8arr_of_rw_cells in FRm.
      unfold LP1cutF in NXT. enter_cutP NXT DP.
      all: try (apply pos_ag_nil; exact LPB). all: intros k Hk; exfalso; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma S0F_U5_all : LP1cutF 0 znew.
  Proof.
    assert (STEP : forall i, (0 <= i < nsc)%Z -> ((i + 1 < nsc)%Z -> forall pos, LP2cutF (i + 1) pos) -> forall pos, LP2cutF i pos).
    { intros i Hi NX pos.
      assert (X78s : forall pos' tmp, (0 <= tmp < ng)%Z -> X78cutF i pos' tmp)
        by (intros pos' tmp Bt; apply S0F_U5_X78; [lia | intros Hlt; apply NX; exact Hlt]).
      apply S0F_U5_LP2; [lia | | intros tmp Bt; apply X78s; exact Bt].
      intros tmp w Bt Hw.
      assert (G : forall k : nat, (1 <= Z.of_nat k < ng)%Z -> forall pos', LP3cutF i pos' tmp (Z.of_nat k)).
      { induction k as [|k IH]; intros Hk pos'; [exfalso; lia|].
        apply S0F_U5_LP3; [lia | lia | | apply X78s; exact Bt].
        intros Hk1. replace (Z.of_nat (Datatypes.S k) - 1)%Z with (Z.of_nat k) by lia. apply IH. lia. }
      replace w with (Z.of_nat (Z.to_nat w)) by lia. apply G. lia. }
    assert (ALL : forall k : nat, (Z.of_nat k < nsc)%Z -> forall pos, LP2cutF (nsc - 1 - Z.of_nat k)%Z pos).
    { induction k as [|k IH]; intros Hk.
      - apply STEP; [lia | intros; exfalso; lia].
      - apply STEP; [lia | intros _].
        replace (nsc - 1 - Z.of_nat (Datatypes.S k) + 1)%Z with (nsc - 1 - Z.of_nat k)%Z by lia. apply IH. lia. }
    assert (L2 : forall pos, LP2cutF 0 pos).
    { pose proof (ALL (Z.to_nat (nsc - 1)) ltac:(lia)) as X.
      replace (nsc - 1 - Z.of_nat (Z.to_nat (nsc - 1)))%Z with 0%Z in X by lia. exact X. }
    assert (X8 : forall pos, X8cutF pos) by (intros pos; apply S0F_U5_X8; apply L2).
    assert (L1 : forall k : nat, (Z.of_nat k < ng)%Z -> forall pos, LP1cutF (ng - 1 - Z.of_nat k)%Z pos).
    { induction k as [|k IH]; intros Hk pos.
      - apply S0F_U5_LP1; [lia | intros; exfalso; lia | apply X8].
      - apply S0F_U5_LP1; [lia | intros _ | apply X8].
        replace (ng - 1 - Z.of_nat (Datatypes.S k) + 1)%Z with (ng - 1 - Z.of_nat k)%Z by lia. apply IH. lia. }
    pose proof (L1 (Z.to_nat (ng - 1)) ltac:(lia) znew) as X.
    replace (ng - 1 - Z.of_nat (Z.to_nat (ng - 1)))%Z with 0%Z in X by lia. exact X.
  Qed.
End R.

(* [comment removed for export] *)
Lemma S0F_dec_U5C : forall A, act_ok 320 A -> forall F, S0F_cut_HCOD A F -> S0F_cut_HUND A F.
Proof.
  intros A AOK F HC. unfold S0F_cut_HUND. intros L d s J. intros until pb. intros DM FR ST MU WM MI DP DI FU.
  pose proof DI as DI'. destruct DI' as [[_ NBL] [NG [NS _]]].
  eapply (S0F_U5_entry A AOK F L s J); first [ exact DM | exact FR | eassumption | eapply (S0F_U5_all A AOK F HC); eassumption ].
Qed.

End ACeilS1.
