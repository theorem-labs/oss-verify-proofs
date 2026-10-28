(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim SjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_defsA Atp_kitA Pj_rtkA Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_os_defsA El_ins_ifaceA Atp_arrlA El_dump_kitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Ltac ls := lstep; try sb_fix.

Local Ltac prep D :=
  destruct D as [X E f1 L sp0 cr m0 gp xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 jj]; cbn [d_X d_E d_f1 d_gp d_j d_s0 d_s1 d_s2 d_s3 d_s4 d_s5 d_s6 d_s7 d_s8 d_s9 d_s10 d_s11] in *;
  destruct X as [usp S1 Fr lo]; cbn [lf_usp lf_S1 lf_F lf_lo] in *;
  unfold LSTA, dfrL, dsaves, J, fa_saved, MASK56, shad, SHB in *; cbn [d_j d_f1 d_X d_E d_gp d_s0 d_s1 d_s2 d_s3 d_s4 d_s5 d_s6 d_s7 d_s8 d_s9 d_s10 d_s11 lf_usp lf_S1 lf_F lf_lo app nth] in *.

Lemma b_w1 : forall (D : dctx) (i : Z) (sv1 sv2 : list byte) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) F fc (m : mem),
  0 <= dq D -> dq D + 256 < 2^63 -> rw_cells asegs m (dq D) (dfrL D sv1 sv2) -> mem_inv asegs m ->
  evt asegs (fun ms => ms = LSTA D EL_OSPUT i (wz 0xb7520) x5 x6 x7 (wz (dF D + 368)) (wz 0x23860) (wz 3) x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m)
    (LSTA D 0xb7514 i x1 x5 x6 x7 (wz (dF D + 368)) x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F   fc m).
Proof.
  intros until m. intros Q0 QH FR MI. prep D.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EQ : bv_unsigned (wz (S1 - 288)) = S1 - 288) by (apply unsigned_lit; lia).
  zstep. step. zstep. apply evt_done. atp_st_eq_goal.
Qed.

Lemma b_w2 : forall (D : dctx) (i : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) F fc (m : mem),
  aenvA_ok (d_E D) -> ae_DOC (d_E D) = dDOC D -> 1 <= i < ae_n (d_E D) -> 0 <= ae_T (d_E D) i < 2^64 ->
  AINV_A (d_E D) m -> shz m (ae_TAPE (d_E D)) (8 * ae_n (d_E D)) -> mem_inv asegs m ->
  evt asegs (fun ms => exists x11' x12', ms = LSTA D 0xb7550 i x1 x5 x6 x7 (wz 0) x11' x12' (wz (ttype (ae_T (d_E D) i))) x14 x15 x16 x17 x24 (wz (ae_T (d_E D) i)) x28 x29 x30 x31 F fc m)
    (LSTA D 0xb7520 i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros OK EDOC IR TR AI SHZT MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR]. unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
  pose proof (shz_doc _ _ OK AI) as SHZD.
  pose proof AI as (TAPEB & _ & _ & DOCC & _). rewrite EDOC in SHZD, DOCC, D8, DF, DL.
  prep D.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RDT.
  shz_pose SHZD (Fr + 120). zstep. shz_norm. step. if_false.
  step. astep. astep.
  chk0 SHZT (ae_TAPE E + 8 * i). step. if_false.
  step. astep. change (ae_T E i / 2 ^ 56) with (ttype (ae_T E i)). zstep.
  apply evt_done. do 2 eexists. atp_st_eq_goal.
Qed.

Lemma b_join : forall (D : dctx) (i : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) F fc (m : mem),
  0 <= i -> i + 1 < ae_n (d_E D) -> ae_n (d_E D) < 2^32 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = LSTA D 0xb7508 (i + 1) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m)
    (LSTA D 0xb78e4 i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros I0 IN NR MI. prep D.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  astep. step. if_cases KB; zify_cond KB; [apply evt_done; atp_st_eq_goal| exfalso; rewrite ?unsigned_lit in KB by lia; lia].
Qed.

Definition atom_lit (t : Z) : Z := if t =? 116 then 0x239e0 else if t =? 102 then 0x23a00 else 0x239c0.
Definition atom_len (t : Z) : Z := if t =? 110 then 5 else if t =? 116 then 5 else 6.
Lemma b_atom : forall (D : dctx) (i : Z) (sv1 sv2 : list byte) (x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x24 x28 x29 x30 x31 : word) F fc (m : mem),
  0 <= dq D -> dq D + 256 < 2^63 -> rw_cells asegs m (dq D) (dfrL D sv1 sv2) -> mem_inv asegs m ->
  (ttype (ae_T (d_E D) i) = 116 \/ ttype (ae_T (d_E D) i) = 102 \/ ttype (ae_T (d_E D) i) = 110) ->
  evt asegs (fun ms => ms = LSTA D EL_OSPUT i (wz 0xb78e4) x5 x6 x7 (wz (dF D + 368)) (wz (atom_lit (ttype (ae_T (d_E D) i)))) (wz (atom_len (ttype (ae_T (d_E D) i))))
                                               (wz (ttype (ae_T (d_E D) i))) x14 x15 x16 x17 x24 (wz (ae_T (d_E D) i)) x28 x29 x30 x31 F fc m)
    (LSTA D 0xb7550 i x1 x5 x6 x7 (wz 0) x11 x12 (wz (ttype (ae_T (d_E D) i))) x14 x15 x16 x17 x24 (wz (ae_T (d_E D) i)) x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros Q0 QH FR MI TY. prep D.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EQ : bv_unsigned (wz (S1 - 288)) = S1 - 288) by (apply unsigned_lit; lia).
  destruct TY as [TY|[TY|TY]]; rewrite TY; unfold atom_lit, atom_len; cbn [Z.eqb Pos.eqb].
  -
    step. step. if_true. step. step. if_false. step. step. if_false. step. step. step. if_false. step. step. if_false.
    zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done. atp_st_eq_goal.
  -
    step. step. if_false. step. step. if_true. step. step. if_false. step. step. if_false. step. step. if_false.
    zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done. atp_st_eq_goal.
  -
    step. step. if_true. step. step. if_false. step. step. if_false. step. step. step. if_true.
    zstep. step. zstep. zstep. apply evt_done. atp_st_eq_goal.
Qed.

Definition num_lit (t : Z) : Z := if t =? 108 then 0x23920 else 0x23960.
Definition num_len (t : Z) : Z := if t =? 108 then 8 else 17.
Definition num_ret1 (t : Z) : Z := if t =? 108 then 0xb787c else 0xb790c.
Lemma b_num1 : forall (D : dctx) (i : Z) (x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x24 x28 x29 x30 x31 : word) F fc (m : mem),
  0 <= i -> i + 1 < ae_n (d_E D) -> ae_n (d_E D) < 2^32 -> mem_inv asegs m ->
  (ttype (ae_T (d_E D) i) = 108 \/ ttype (ae_T (d_E D) i) = 117) ->
  evt asegs (fun ms => exists x10', ms = LSTA D EL_OSPUT (i + 1) (wz (num_ret1 (ttype (ae_T (d_E D) i)))) x5 x6 x7 (wz (dF D + 368)) (wz (num_lit (ttype (ae_T (d_E D) i)))) (wz (num_len (ttype (ae_T (d_E D) i))))
                                               (wz (ttype (ae_T (d_E D) i))) x14 x15 x16 x17 x24 (wz (ae_T (d_E D) i)) x28 x29 x30 x31 F fc m /\ x10' = x5)
    (LSTA D 0xb7550 i x1 x5 x6 x7 (wz 0) x11 x12 (wz (ttype (ae_T (d_E D) i))) x14 x15 x16 x17 x24 (wz (ae_T (d_E D) i)) x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros I0 IN NR MI TY. prep D.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct TY as [TY|TY]; rewrite TY; unfold num_lit, num_len, num_ret1; cbn [Z.eqb Pos.eqb].
  -
    step. step. if_true. step. step. if_false. step. step. if_true.
    astep. step. if_cases KB; zify_cond KB; [exfalso; rewrite ?unsigned_lit in KB by lia; lia|].
    zstep. zstep. zstep. zstep. zstep. apply evt_done. eexists. split; [atp_st_eq_goal| reflexivity].
  -
    step. step. if_true. step. step. if_true. step. step. if_true.
    astep. step. if_cases KB; zify_cond KB; [exfalso; rewrite ?unsigned_lit in KB by lia; lia|].
    zstep. zstep. zstep. zstep. zstep. apply evt_done. eexists. split; [atp_st_eq_goal| reflexivity].
Qed.

Definition num_ins (t : Z) : Z := if t =? 108 then EL_INS_L else EL_INS_UL.
Definition num_tix (t : Z) : Z := if t =? 108 then 0xb7890 else 0xb7920.
Definition num_ret2 (t : Z) : Z := if t =? 108 then 0xb78a8 else 0xb7938.
Lemma b_num2a : forall (D : dctx) (i t : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) F fc (m : mem),
  aenvA_ok (d_E D) -> ae_DOC (d_E D) = dDOC D -> 0 <= i -> i + 1 < ae_n (d_E D) -> (t = 108 \/ t = 117) -> AINV_A (d_E D) m -> mem_inv asegs m ->
  evt asegs (fun ms => exists x12', ms = LSTA D (num_tix t) (i + 1) x1 x5 x6 x7 (wz (dF D + 368)) (wz (ae_TAPE (d_E D) + 8 * (i + 1))) x12' x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m)
    (LSTA D (num_ret1 t) (i + 1) x1 x5 x6 x7 (wz (dF D + 368)) x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros OK EDOC I0 IN TY AI MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR]. unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
  pose proof (shz_doc _ _ OK AI) as SHZD.
  pose proof AI as (_ & _ & _ & DOCC & _). rewrite EDOC in SHZD, DOCC, D8, DF, DL.
  prep D.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct TY as [-> | ->]; unfold num_ret1, num_tix; cbn [Z.eqb Pos.eqb];
    (shz_pose SHZD (Fr + 120); zstep; shz_norm; step; if_false; step; astep; astep; apply evt_done; eexists; atp_st_eq_goal).
Qed.

Lemma b_num2b : forall (D : dctx) (i t : Z) (x1 x5 x6 x7 xa2 xa3 xa4 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) F fc (m : mem),
  aenvA_ok (d_E D) -> 1 <= i -> i + 1 < ae_n (d_E D) -> (t = 108 \/ t = 117) ->
  AINV_A (d_E D) m -> shz m (ae_TAPE (d_E D)) (8 * ae_n (d_E D)) -> mem_inv asegs m ->
  evt asegs (fun ms => ms = LSTA D (num_ins t) (i + 1) (wz (num_ret2 t)) x5 x6 x7 (wz (dF D + 368)) (wz (ae_T (d_E D) (i + 1))) (wz 0) xa3 xa4 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m)
    (LSTA D (num_tix t) (i + 1) x1 x5 x6 x7 (wz (dF D + 368)) (wz (ae_TAPE (d_E D) + 8 * (i + 1))) xa2 xa3 xa4 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros OK I1 IN TY AI SHZT MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR]. unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
  pose proof AI as (TAPEB & _ & _ & DOCC & _).
  prep D.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) (i + 1) TAPEB ltac:(lia)) as RDT.
  destruct TY as [-> | ->]; unfold num_ins, num_tix, num_ret2; cbn [Z.eqb Pos.eqb];
    (chk0 SHZT (ae_TAPE E + 8 * (i + 1)); step; if_false; step; zstep; apply evt_done; atp_st_eq_goal).
Qed.

Definition num_ret3 (t : Z) : Z := if t =? 108 then 0xb78b8 else 0xb7948.
Lemma b_num3 : forall (D : dctx) (i t : Z) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) F fc (m : mem),
  (t = 108 \/ t = 117) -> mem_inv asegs m ->
  evt asegs (fun ms => ms = LSTA D EL_OSPUT i (wz (num_ret3 t)) x5 x6 x7 (wz (dF D + 368)) (wz 0x23940) (wz 1) x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m)
    (LSTA D (num_ret2 t) i (wz (num_ret2 t)) x5 x6 x7 (wz (dF D + 368)) x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros TY MI. prep D.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct TY as [-> | ->]; unfold num_ret2, num_ret3; cbn [Z.eqb Pos.eqb]; (zstep; zstep; zstep; zstep; apply evt_done; atp_st_eq_goal).
Qed.

Lemma b_d1 : forall (D : dctx) (i : Z) (sv1 sv2 : list byte) (x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x24 x28 x29 x30 x31 : word) F fc (m : mem),
  0 <= dq D -> dq D + 256 < 2^63 -> rw_cells asegs m (dq D) (dfrL D sv1 sv2) -> mem_inv asegs m ->
  ttype (ae_T (d_E D) i) = 100 ->
  evt asegs (fun ms => ms = LSTA D EL_OSPUT i (wz 0xb7720) x5 x6 x7 (wz (dF D + 368)) (wz 0x239a0) (wz 6) (wz 100) x14 x15 x16 x17 x24 (wz (ae_T (d_E D) i)) x28 x29 x30 x31 F fc m)
    (LSTA D 0xb7550 i x1 x5 x6 x7 (wz 0) x11 x12 (wz (ttype (ae_T (d_E D) i))) x14 x15 x16 x17 x24 (wz (ae_T (d_E D) i)) x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros Q0 QH FR MI TY. prep D. rewrite TY.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EQ : bv_unsigned (wz (S1 - 288)) = S1 - 288) by (apply unsigned_lit; lia).

  step. step. if_false. step. step. if_true. step. step. if_false. step. step. if_true.
  zstep. zstep. step. zstep. apply evt_done. atp_st_eq_goal.
Qed.

Lemma b_d2a : forall (D : dctx) (i : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) F fc (m : mem),
  aenvA_ok (d_E D) -> ae_DOC (d_E D) = dDOC D -> 0 <= i -> i + 1 < ae_n (d_E D) -> ae_n (d_E D) < 2^32 -> AINV_A (d_E D) m -> mem_inv asegs m ->
  evt asegs (fun ms => exists x11', ms = LSTA D 0xb773c (i + 1) x1 x5 x6 x7 (wz (ae_TAPE (d_E D) + 8 * (i + 1))) x11' x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m)
    (LSTA D 0xb7720 i x1 x5 x6 x7 (wz (dF D + 368)) x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros OK EDOC I0 IN NR AI MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
  pose proof (shz_doc _ _ OK AI) as SHZD.
  pose proof AI as (_ & _ & _ & DOCC & _). rewrite EDOC in SHZD, DOCC, D8, DF, DL.
  prep D.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  astep. step. if_cases KB; zify_cond KB; [exfalso; rewrite ?unsigned_lit in KB by lia; lia|].
  shz_pose SHZD (Fr + 120). zstep. shz_norm. step. if_false.
  step. astep. astep. apply evt_done. eexists. atp_st_eq_goal.
Qed.

Lemma b_d2b : forall (D : dctx) (i : Z) (x1 x5 x6 x7 xa1 x12 xa3 xa4 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) F fc (m : mem),
  aenvA_ok (d_E D) -> 1 <= i -> i + 1 < ae_n (d_E D) ->
  AINV_A (d_E D) m -> shz m (ae_TAPE (d_E D)) (8 * ae_n (d_E D)) -> mem_inv asegs m ->
  evt asegs (fun ms => exists x11' F', ms = LSTA D EL_INS_D (i + 1) (wz 0xb7758) x5 x6 x7 (wz (dF D + 368)) x11' x12 xa3 xa4 x15 x16 x17 x24 x25 x28 x29 x30 x31 F' fc m)
    (LSTA D 0xb773c (i + 1) x1 x5 x6 x7 (wz (ae_TAPE (d_E D) + 8 * (i + 1))) xa1 x12 xa3 xa4 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros OK I1 IN AI SHZT MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR]. unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
  pose proof AI as (TAPEB & _ & _ & DOCC & _).
  prep D.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) (i + 1) TAPEB ltac:(lia)) as RDT.
  chk0 SHZT (ae_TAPE E + 8 * (i + 1)). step. if_false.
  step. zstep. zstep. apply evt_done. do 2 eexists. atp_st_eq_goal.
Qed.

Lemma b_d3 : forall (D : dctx) (i : Z) (sv1 sv2 : list byte) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) (jc js : list byte) F fc (m : mem),
  0 <= dq D -> dq D + 256 < 2^63 -> 0 < d_f1 D -> d_f1 D + 128 < 2^63 -> shad (d_f1 D) + 16 < 2^63 -> (d_f1 D + 128 <= shad (d_f1 D) \/ shad (d_f1 D) + 16 <= d_f1 D) ->
  d_f1 D + 128 <= dq D -> shad (d_f1 D) + 16 <= dq D ->
  rw_cells asegs m (dq D) (dfrL D sv1 sv2) ->
  rw_cells asegs m (d_f1 D + 64) [CB 1 jc] -> rw_cells asegs m (shad (d_f1 D) + 8) [CB 1 js] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = LSTA D EL_OSPUT i (wz 0xb7774) x5 x6 x7 (wz (dF D + 368)) (wz (d_f1 D + 64)) (wz 1) x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m1
      /\ munch [(d_f1 D + 64, d_f1 D + 65); (shad (d_f1 D) + 8, shad (d_f1 D) + 9)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (d_f1 D + 64) [C1 (Z_to_bv 8 10)] /\ rw_cells asegs m1 (shad (d_f1 D) + 8) [C1 (Z_to_bv 8 1)])
    (LSTA D 0xb7758 i (wz 0xb7758) x5 x6 x7 (wz (dF D + 368)) x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros Q0 QH F0 FH SHH SAP FQ SQ FR FC FS MI. prep D.
  lazymatch goal with |- context [munch ?W0 m _] => pose proof (munch_refl W0 m) as MU end. pose proof (wmono_refl asegs m) as WM.
  assert (EQ : bv_unsigned (wz (S1 - 288)) = S1 - 288) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (wz f1) = f1) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (wz (f1 / 8 + 2147450880)) = f1 / 8 + 2147450880) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  replace (f1 / 8 + 2147450880 + 8) with (f1 / 8 + 2147450888) in FS by lia.
  zstep. ls. step. zstep. ls. zstep. zstep.
  apply evt_done. eexists. split; [atp_st_eq_goal|]. split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia|].
  split; [exact WM|]. split; [assumption|]. replace (f1 / 8 + 2147450880 + 8) with (f1 / 8 + 2147450888) by lia. split; [exact FC| exact FS].
Qed.

Lemma b_d4 : forall (D : dctx) (i : Z) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) (js : list byte) F fc (m : mem),
  0 < d_f1 D -> shad (d_f1 D) + 16 < 2^63 ->
  rw_cells asegs m (shad (d_f1 D) + 8) [CB 1 js] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = LSTA D 0xb78e4 i (wz 0xb7774) x5 x6 x7 (wz (-8)) x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m1
      /\ munch [(shad (d_f1 D) + 8, shad (d_f1 D) + 9)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1)
    (LSTA D 0xb7774 i (wz 0xb7774) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros F0 SHH FS MI. prep D.
  lazymatch goal with |- context [munch ?W0 m _] => pose proof (munch_refl W0 m) as MU end. pose proof (wmono_refl asegs m) as WM.
  assert (ES : bv_unsigned (wz (f1 / 8 + 2147450880)) = f1 / 8 + 2147450880) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  replace (f1 / 8 + 2147450880 + 8) with (f1 / 8 + 2147450888) in FS by lia.
  zstep. ls. zstep.
  apply evt_done. eexists. split; [atp_st_eq_goal|]. split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia|].
  split; [exact WM| assumption].
Qed.

Section Body.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Variable D : dctx.
Hypothesis DOK : dctx_ok D.
Hypothesis PUT : os_put_cpsA RT PMc.
Hypothesis IUL : ins_ul_cpsA RT PMc.
Hypothesis IU : ins_u_cpsA RT PMc.
Hypothesis IL : ins_l_cpsA RT PMc.
Hypothesis INSD : ins_d_cpsA RT PMc.
Hypothesis CRB : EL_DUMP_C0 - 2 + EL_DUMP_CW * ae_n (d_E D) + EL_DUMP_CSB * ae_sn (d_E D) <= d_cr D.

Local Ltac ul := unfold EL_DUMP_STACK_A, EL_PUT_STACK_A, EL_INS_STACK_A, EL_INSD_STACK_A, FUZZ_STACK, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.
Notation GI := (GINVA RT (d_G D) 0x1002 0 FILLOK).
Notation n := (ae_n (d_E D)).
Notation T := (ae_T (d_E D)).
Notation KLOOP := (KLOOPA RT PMc D).

Local Ltac facts DOK :=
  pose proof DOK as (GOK & GE & LK & AI0 & IOS0 & WFS & LJ & _);
  pose proof GOK as [(Q32 & FS0 & QT & LQ) (LO1 & LO2) (SP1 & SP2) (E0 & E64 & ESEG & ELO & EIN & ESH & ESHL & EHI) (F0 & F64 & FSEG & FLO & FSR & FHI & SHLO & SHAP) FFR FFL RFR LL];
  cbn [d_G g_q g_fsz g_lo g_F g_ff g_ffk g_rfr g_L g_sp0 g_cr g_m0] in *; change (fs_size 1) with 128 in *; change (128 / 8) with 16 in *;
  pose proof GE as (OKE & ELOE & EDOC & EFD & EKD & INT & INS & INP & QHI); cbn [d_G g_lo g_F g_L] in ELOE, EDOC, EFD, INT, INS, INP;
  pose proof WFS as (NR & SNR & TR0 & _).

Lemma dump_headA : forall (K : config -> Prop) (i : Z) (Σ : rts RT) (m : mem) (k : Z) (sv1 sv2 : list byte)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
  GI (dfrL D sv1 sv2) k Σ m -> frm0 fc -> 1 <= i < n -> 0 <= T i < 2^64 -> 0 <= k -> k + 3 <= 59 + 24 * n + 4 * ae_sn (d_E D) ->
  (forall (Σ' : rts RT) (m' : mem) (x1' x5' x6' x7' x11' x12' x14' x15' x16' x17' x28' x29' x30' x31' : word) (F' : bvmap 5 word) (fc' : bv 32),
     GI (dfrL D sv1 sv2) (k + 3) Σ' m' -> frm0 fc' ->
     aevt RT PMc Σ' K (LSTA D 0xb7550 i x1' x5' x6' x7' (wz 0) x11' x12' (wz (ttype (T i))) x14' x15' x16' x17' x24 (wz (T i)) x28' x29' x30' x31' F' fc' m')) ->
  aevt RT PMc Σ K (LSTA D 0xb7508 i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m).
Proof using AF FDO MST DOK PUT IUL CRB.
  intros until fc. intros GI0 FRM IR TIR K0 KB HK. facts DOK.
  assert (Q0 : 0 <= dq D) by (clear - LQ LO1; ul). assert (QH : dq D + 256 < 2^63) by (clear - QT; ul).
  assert (FA : forall f, FILLOK f -> FILLOK (fill_after f)) by (intros f Hf; destruct (FILLOK_after f Hf) as [e|e]; rewrite e; [right; left| right; right]; reflexivity).
  assert (LOQ : forall d, d <= 12800 + RT_STACK -> lf_lo (d_X D) + d <= dq D) by (intros d Hd; clear - Hd LQ; lia).
  assert (CRB' : 62 + 24 * n + 4 * ae_sn (d_E D) <= d_cr D) by (clear - CRB; unfold EL_DUMP_C0, EL_DUMP_CW, EL_DUMP_CSB in CRB; lia).

  unfold LSTA. apply (aevt_evt RT AF PMc MST). zstep. zstep. zstep. apply evt_done.
  eapply (g_ins RT AF PMc FDO MST (d_G D) GOK EL_INS_UL (fun v => 0 <= v < 2^64) 0x1002 0 FILLOK FILLOK FILLOK EL_INS_STACK_A _ k Σ K i);
    [exact IUL| exact GI0| exact IOS0| intros f Hf; exact Hf| exact FA| clear - IR NR; lia| exact FRM| apply LOQ; clear; ul
    | (cbn [d_G g_rfr length]; unfold FRAMES_TOT; clear; lia)| (cbn [d_G g_cr]; clear - CRB' KB K0; lia)|].
  clear m GI0. intros Σ1 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F1 fc1 m GI1 FRM1. cbn [d_G g_q g_F] in GI1 |- *. rewrite (ret_pc_even 0xb7514) by (clear; lia).

  pose proof GI1 as (_ & MI1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR1 & _) & _). cbn [d_G g_q] in FR1.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (b_w1 D i sv1 sv2 _ u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 x24 x25 u3 u4 u5 u6 F1 fc1 m Q0 QH FR1 MI1)|].
  cbv beta. intros ms2 ->. apply evt_done. unfold LSTA.
  eapply (g_put_lit RT AF PMc FDO MST (d_G D) GOK FILLOK FILLOK _ (k + 1) Σ1 K 0x23860 3 4 4%nat);
    [exact PUT| exact GI1| intros f Hf; exact Hf| exact FA| clear; cbn [In ACC_LITS]; repeat (first [left; reflexivity | right])| vm_compute; reflexivity| vm_compute; reflexivity
    | clear; lia| clear; lia| clear; lia| clear; unfold SEGTOP_A; lia| apply LOQ; clear; ul
    | (cbn [d_G g_rfr length]; unfold FRAMES_TOT; clear; lia)| (cbn [d_G g_cr]; clear - CRB' KB K0; lia)|].
  clear m MI1 GI1 FR1 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6. intros Σ2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 m GI2. cbn [d_G g_q g_F] in GI2 |- *. rewrite (ret_pc_even 0xb7520) by (clear; lia).
  replace (k + 1 + 2) with (k + 3) in GI2 by (clear; lia).

  pose proof GI2 as (_ & MI2 & _).
  pose proof (GINVA_ainv RT AF (d_G D) GOK (d_E D) _ _ _ _ _ _ _ GE AI0 GI2) as AI2.
  pose proof (GINVA_shz RT AF (d_G D) GOK (d_E D) _ _ _ _ _ _ _ GE AI0 GI2) as (SZT2 & _ & _).
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (b_w2 D i _ u0 u1 u2 _ b1 b2 b3 b4 b5 b6 b7 x24 x25 u3 u4 u5 u6 F2 fc1 m OKE EDOC IR TIR AI2 SZT2 MI2)|].
  cbv beta. intros ms3 (x11' & x12' & ->). apply evt_done.
  exact (HK Σ2 m _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc1 GI2 FRM1).
Qed.

Lemma dump_joinA : forall (K : config -> Prop) (i c : Z) (Σ : rts RT) (m : mem) (k : Z) (sv1 sv2 : list byte)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
  GI (dfrL D sv1 sv2) k Σ m -> frm0 fc -> 0 <= i -> i + 1 < n -> KLOOP K (i + 1) c -> 0 <= k ->
  k <= DKH + EL_DUMP_CW * i + EL_DUMP_CSB * c ->
  aevt RT PMc Σ K (LSTA D 0xb78e4 i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m).
Proof using AF MST DOK.
  intros until fc. intros GI0 FRM I0 IN HK K0 KB. facts DOK. pose proof GI0 as (_ & MI0 & _).
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (b_join D i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m I0 IN ltac:(clear - NR; lia) MI0)|].
  cbv beta. intros ms1 ->. apply evt_done. eapply HK; [exact GI0| exact FRM| exact K0| clear - KB; lia].
Qed.

Lemma dump_atomA : forall (K : config -> Prop) (i c : Z) (Σ : rts RT) (m : mem) (k : Z) (sv1 sv2 : list byte)
    (x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x24 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
  GI (dfrL D sv1 sv2) k Σ m -> frm0 fc -> 1 <= i -> i + 1 < n ->
  (T i = tword t_true 0 \/ T i = tword t_false 0 \/ T i = tword t_null 0) -> KLOOP K (i + 1) c -> 0 <= k -> k + 2 <= DKH + EL_DUMP_CW * i + EL_DUMP_CSB * c -> 0 <= c <= ae_sn (d_E D) ->
  aevt RT PMc Σ K (LSTA D 0xb7550 i x1 x5 x6 x7 (wz 0) x11 x12 (wz (ttype (T i))) x14 x15 x16 x17 x24 (wz (T i)) x28 x29 x30 x31 F fc m).
Proof using AF FDO MST DOK PUT CRB.
  intros until fc. intros GI0 FRM I1 IN TY HK K0 KB CB. facts DOK.
  assert (Q0 : 0 <= dq D) by (clear - LQ LO1; ul). assert (QH : dq D + 256 < 2^63) by (clear - QT; ul).
  assert (FA : forall f, FILLOK f -> FILLOK (fill_after f)) by (intros f Hf; destruct (FILLOK_after f Hf) as [e|e]; rewrite e; [right; left| right; right]; reflexivity).
  assert (LOQ : forall d, d <= 12800 + RT_STACK -> lf_lo (d_X D) + d <= dq D) by (intros d Hd; clear - Hd LQ; lia).
  assert (CRB' : 62 + 24 * n + 4 * ae_sn (d_E D) <= d_cr D) by (clear - CRB; unfold EL_DUMP_C0, EL_DUMP_CW, EL_DUMP_CSB in CRB; lia).
  assert (F64x : d_f1 D mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
  pose proof (FFR _ _ ltac:(left; reflexivity)) as (A1 & A2 & A3). change (fs_size 4) with 1024 in A1, A2, A3.
  pose proof GI0 as (_ & MI0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR0 & _) & _). cbn [d_G g_q] in FR0.
  assert (TY' : ttype (T i) = 116 \/ ttype (T i) = 102 \/ ttype (T i) = 110)
    by (destruct TY as [E|[E|E]]; rewrite E, ttype_tword by lia; unfold t_true, t_false, t_null; [left| right; left| right; right]; reflexivity).
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (b_atom D i sv1 sv2 x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x24 x28 x29 x30 x31 F fc m Q0 QH FR0 MI0 TY')|].
  cbv beta. intros ms1 ->. apply evt_done. unfold LSTA.
  assert (PUTL : forall (BUF N CAPL : Z) (nb : nat), In (BUF, CAPL) ACC_LITS -> ro_bytes_b asegs BUF (lit BUF nb) = true -> length (lit BUF nb) = nb -> Z.of_nat nb <= CAPL ->
            0 <= N <= Z.of_nat nb -> 0x10000 <= BUF -> BUF + CAPL <= SEGTOP_A ->
            wz (atom_lit (ttype (T i))) = wz BUF -> wz (atom_len (ttype (T i))) = wz N ->
            aevt RT PMc Σ K (MS (mkR (wz 0xb78e4) (wz (dq D)) (d_gp D) (wz TPV_A) x5 x6 x7 (wz (lf_S1 (d_X D))) (wz (dq D)) (wz (dF D + 368)) (wz (atom_lit (ttype (T i)))) (wz (atom_len (ttype (T i))))
                                     (wz (ttype (T i))) x14 x15 x16 x17 (wz (d_f1 D)) (wz (dF D + 368)) (wz (dDOC D)) (wz n) (wz (shad (dDOC D))) (wz (shad (d_f1 D))) x24 (wz (T i)) (wz SHB) (wz i) x28 x29 x30 x31)
                                F (wz EL_OSPUT) fc None m (seg_rom asegs))).
  { intros BUF N CAPL nb INL RB LLn NBC NRG BLO BHI -> ->.
    eapply (g_put_lit RT AF PMc FDO MST (d_G D) GOK FILLOK FILLOK _ k Σ K BUF N CAPL nb);
      [exact PUT| exact GI0| intros f Hf; exact Hf| exact FA| exact INL| exact RB| exact LLn| exact NBC| exact NRG| exact BLO| exact BHI| apply LOQ; clear; ul
      | (cbn [d_G g_rfr length]; unfold FRAMES_TOT; clear; lia)| (cbn [d_G g_cr]; unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB; clear - CRB' KB K0 CB IN I1; lia)|].
    clear m MI0 GI0 FR0. intros Σ2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 m GI2. cbn [d_G g_q g_F] in GI2 |- *. rewrite (ret_pc_even 0xb78e4) by (clear; lia).
    eapply (dump_joinA K i c Σ2 m (k + 2) sv1 sv2); [exact GI2| exact FRM| clear - I1; lia| exact IN| exact HK| clear - K0; lia| exact KB]. }
  destruct TY' as [E|[E|E]]; rewrite E in PUTL |- *; unfold atom_lit, atom_len in PUTL |- *; cbn [Z.eqb Pos.eqb] in PUTL |- *.
  - apply (PUTL 0x239e0 5 6 6%nat); [clear; cbn [In ACC_LITS]; repeat (first [left; reflexivity | right])| vm_compute; reflexivity| vm_compute; reflexivity| clear; lia| clear; lia| clear; lia| clear; unfold SEGTOP_A; lia| reflexivity| reflexivity].
  - apply (PUTL 0x23a00 6 7 7%nat); [clear; cbn [In ACC_LITS]; repeat (first [left; reflexivity | right])| vm_compute; reflexivity| vm_compute; reflexivity| clear; lia| clear; lia| clear; lia| clear; unfold SEGTOP_A; lia| reflexivity| reflexivity].
  - apply (PUTL 0x239c0 5 6 6%nat); [clear; cbn [In ACC_LITS]; repeat (first [left; reflexivity | right])| vm_compute; reflexivity| vm_compute; reflexivity| clear; lia| clear; lia| clear; lia| clear; unfold SEGTOP_A; lia| reflexivity| reflexivity].
Qed.

Lemma dump_numA : forall (K : config -> Prop) (i c : Z) (Σ : rts RT) (m : mem) (k : Z) (sv1 sv2 : list byte)
    (x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x24 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
  GI (dfrL D sv1 sv2) k Σ m -> frm0 fc -> 1 <= i -> i + 2 < n ->
  (T i = tword t_i64 0 \/ T i = tword t_u64 0) -> KLOOP K (i + 2) c -> 0 <= k -> k + 5 <= DKH + EL_DUMP_CW * (i + 1) + EL_DUMP_CSB * c -> 0 <= c <= ae_sn (d_E D) ->
  aevt RT PMc Σ K (LSTA D 0xb7550 i x1 x5 x6 x7 (wz 0) x11 x12 (wz (ttype (T i))) x14 x15 x16 x17 x24 (wz (T i)) x28 x29 x30 x31 F fc m).
Proof using AF FDO MST DOK PUT IUL IL CRB.
  intros until fc. intros GI0 FRM I1 IN TY HK K0 KB CB. facts DOK.
  assert (Q0 : 0 <= dq D) by (clear - LQ LO1; ul). assert (QH : dq D + 256 < 2^63) by (clear - QT; ul).
  assert (FA : forall f, FILLOK f -> FILLOK (fill_after f)) by (intros f Hf; destruct (FILLOK_after f Hf) as [e|e]; rewrite e; [right; left| right; right]; reflexivity).
  assert (LOQ : forall d, d <= 12800 + RT_STACK -> lf_lo (d_X D) + d <= dq D) by (intros d Hd; clear - Hd LQ; lia).
  assert (CRB' : 62 + 24 * n + 4 * ae_sn (d_E D) <= d_cr D) by (clear - CRB; unfold EL_DUMP_C0, EL_DUMP_CW, EL_DUMP_CSB in CRB; lia).
  assert (F64x : d_f1 D mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
  pose proof (FFR _ _ ltac:(left; reflexivity)) as (A1 & A2 & A3). change (fs_size 4) with 1024 in A1, A2, A3.
  pose proof GI0 as (_ & MI0 & _).
  assert (TY' : ttype (T i) = 108 \/ ttype (T i) = 117)
    by (destruct TY as [E|E]; rewrite E, ttype_tword by lia; unfold t_i64, t_u64; [left| right]; reflexivity).
  set (t := ttype (T i)) in *.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (b_num1 D i x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x24 x28 x29 x30 x31 F fc m ltac:(clear - I1; lia) ltac:(clear - IN; lia) ltac:(clear - NR; lia) MI0 TY')|].
  cbv beta. intros ms1 (x10' & -> & _). apply evt_done. unfold LSTA. fold t.
  assert (STEP2 : forall (Σ2 : rts RT) (m2 : mem) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 (F2 : bvmap 5 word),
    GI (dfrL D sv1 sv2) (k + 2) Σ2 m2 ->
    aevt RT PMc Σ2 K (MS (mkR (wz (num_ret1 t)) (wz (dq D)) (d_gp D) (wz TPV_A) u0 u1 u2 (wz (lf_S1 (d_X D))) (wz (dq D)) (wz (dF D + 368)) b1 b2 b3 b4 b5 b6 b7
                             (wz (d_f1 D)) (wz (dF D + 368)) (wz (dDOC D)) (wz n) (wz (shad (dDOC D))) (wz (shad (d_f1 D))) x24 (wz (T i)) (wz SHB) (wz (i + 1)) u3 u4 u5 u6)
                        F2 (ret_pc (wz (num_ret1 t))) fc None m2 (seg_rom asegs))).
  { intros Σ2 m2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 GI2.
    pose proof GI2 as (_ & MI2 & _).
    pose proof (GINVA_ainv RT AF (d_G D) GOK (d_E D) _ _ _ _ _ _ _ GE AI0 GI2) as AI2.
    pose proof (GINVA_shz RT AF (d_G D) GOK (d_E D) _ _ _ _ _ _ _ GE AI0 GI2) as (SZT2 & _ & _).
    replace (ret_pc (wz (num_ret1 t))) with (wz (num_ret1 t)) by (subst t; destruct TY' as [E|E]; (rewrite E; unfold num_ret1; cbn [Z.eqb Pos.eqb]; symmetry; apply ret_pc_even; [clear; lia| reflexivity])).

    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (b_num2a D i t _ u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 x24 (wz (T i)) u3 u4 u5 u6 F2 fc m2 OKE EDOC ltac:(clear - I1; lia) ltac:(clear - IN; lia) TY' AI2 MI2)|].
    cbv beta. intros ms2 (xa2 & ->).
    eapply evt_cut; [eapply (b_num2b D i t _ u0 u1 u2 xa2 b3 b4 b5 b6 b7 x24 (wz (T i)) u3 u4 u5 u6 F2 fc m2 OKE I1 ltac:(clear - IN; lia) TY' AI2 SZT2 MI2)|].
    cbv beta. intros ms3 ->. apply evt_done. unfold LSTA.
    assert (STEP3 : forall (Σ4 : rts RT) (m4 : mem) v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 (F4 : bvmap 5 word) (fc4 : bv 32),
      GI (dfrL D sv1 sv2) (k + 3) Σ4 m4 -> frm0 fc4 ->
      aevt RT PMc Σ4 K (MS (mkR (wz (num_ret2 t)) (wz (dq D)) (d_gp D) (wz TPV_A) v0 v1 v2 (wz (lf_S1 (d_X D))) (wz (dq D)) (wz (dF D + 368)) c1 c2 c3 c4 c5 c6 c7
                               (wz (d_f1 D)) (wz (dF D + 368)) (wz (dDOC D)) (wz n) (wz (shad (dDOC D))) (wz (shad (d_f1 D))) x24 (wz (T i)) (wz SHB) (wz (i + 1)) v3 v4 v5 v6)
                          F4 (ret_pc (wz (num_ret2 t))) fc4 None m4 (seg_rom asegs))).
    { intros Σ4 m4 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F4 fc4 GI4 FRM4. pose proof GI4 as (_ & MI4 & _).
      replace (ret_pc (wz (num_ret2 t))) with (wz (num_ret2 t)) by (subst t; destruct TY' as [E|E]; (rewrite E; unfold num_ret2; cbn [Z.eqb Pos.eqb]; symmetry; apply ret_pc_even; [clear; lia| reflexivity])).
      apply (aevt_evt RT AF PMc MST).
      eapply evt_cut; [eapply (b_num3 D (i + 1) t v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 x24 (wz (T i)) v3 v4 v5 v6 F4 fc4 m4 TY' MI4)|].
      cbv beta. intros ms5 ->. apply evt_done. unfold LSTA.
      eapply (g_put_lit RT AF PMc FDO MST (d_G D) GOK FILLOK FILLOK _ (k + 3) Σ4 K 0x23940 1 2 2%nat);
        [exact PUT| exact GI4| intros f Hf; exact Hf| exact FA| clear; cbn [In ACC_LITS]; repeat (first [left; reflexivity | right])| vm_compute; reflexivity| vm_compute; reflexivity
        | clear; lia| clear; lia| clear; lia| clear; unfold SEGTOP_A; lia| apply LOQ; clear; ul
        | (cbn [d_G g_rfr length]; unfold FRAMES_TOT; clear; lia)| (cbn [d_G g_cr]; unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB; clear - CRB' KB K0 CB IN I1; lia)|].
      clear m4 MI4 GI4. intros Σ6 w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F6 m6 GI6. cbn [d_G g_q g_F] in GI6 |- *. replace (k + 3 + 2) with (k + 5) in GI6 by (clear; lia).
      replace (ret_pc (wz (num_ret3 t))) with (wz (num_ret3 t)) by (subst t; destruct TY' as [E|E]; (rewrite E; unfold num_ret3; cbn [Z.eqb Pos.eqb]; symmetry; apply ret_pc_even; [clear; lia| reflexivity])).
      pose proof GI6 as (_ & MI6 & _). pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.

      apply (aevt_evt RT AF PMc MST). subst t. destruct TY' as [E|E]; rewrite E; unfold num_ret3; cbn [Z.eqb Pos.eqb]; zstep; apply evt_done;
        (eapply (dump_joinA K (i + 1) c Σ6 m6 (k + 5) sv1 sv2); [exact GI6| exact FRM4| clear - I1; lia| clear - IN; lia| replace (i + 1 + 1) with (i + 2) by lia; exact HK| clear - K0; lia| clear - KB; lia]). }
    subst t. destruct TY' as [E|E]; rewrite E in STEP3 |- *; unfold num_ins, num_ret2 in STEP3 |- *; cbn [Z.eqb Pos.eqb] in STEP3 |- *.
    -
      pose proof (Z.mod_pos_bound (T (i + 1)) (2^64) ltac:(clear; lia)) as WR.
      replace (Z_to_bv 64 (T (i + 1))) with (Z_to_bv 64 ((T (i + 1)) mod 2 ^ 64)) by (apply Z_to_bv64_eqm; rewrite Z.mod_mod by (clear; lia); reflexivity).
      destruct (Z_lt_le_dec (T (i + 1) mod 2^64) (2^63)) as [SM|BG].
      + eapply (g_ins RT AF PMc FDO MST (d_G D) GOK EL_INS_L (fun v => -2^63 <= v < 2^63) 0x1002 0 FILLOK FILLOK FILLOK EL_INS_STACK_A _ (k + 2) Σ2 K (T (i + 1) mod 2^64));
          [exact IL| exact GI2| exact IOS0| intros f Hf; exact Hf| exact FA| clear - SM WR; lia| exact FRM| apply LOQ; clear; ul
          | (cbn [d_G g_rfr length]; unfold FRAMES_TOT; clear; lia)| (cbn [d_G g_cr]; unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB; clear - CRB' KB K0 CB IN I1; lia)|].
        intros Σ4 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F4 fc4 m4 GI4 FRM4. cbn [d_G g_q g_F] in GI4 |- *. replace (k + 2 + 1) with (k + 3) in GI4 by (clear; lia). exact (STEP3 Σ4 m4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc4 GI4 FRM4).
      + rewrite <- (Z_to_bv_minus_mod (T (i + 1) mod 2^64)).
        eapply (g_ins RT AF PMc FDO MST (d_G D) GOK EL_INS_L (fun v => -2^63 <= v < 2^63) 0x1002 0 FILLOK FILLOK FILLOK EL_INS_STACK_A _ (k + 2) Σ2 K (T (i + 1) mod 2^64 - 2^64));
          [exact IL| exact GI2| exact IOS0| intros f Hf; exact Hf| exact FA| clear - BG WR; lia| exact FRM| apply LOQ; clear; ul
          | (cbn [d_G g_rfr length]; unfold FRAMES_TOT; clear; lia)| (cbn [d_G g_cr]; unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB; clear - CRB' KB K0 CB IN I1; lia)|].
        intros Σ4 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F4 fc4 m4 GI4 FRM4. cbn [d_G g_q g_F] in GI4 |- *. replace (k + 2 + 1) with (k + 3) in GI4 by (clear; lia). exact (STEP3 Σ4 m4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc4 GI4 FRM4).
    - pose proof (Z.mod_pos_bound (T (i + 1)) (2^64) ltac:(clear; lia)) as WR.
      replace (Z_to_bv 64 (T (i + 1))) with (Z_to_bv 64 ((T (i + 1)) mod 2 ^ 64)) by (apply Z_to_bv64_eqm; rewrite Z.mod_mod by (clear; lia); reflexivity).
      eapply (g_ins RT AF PMc FDO MST (d_G D) GOK EL_INS_UL (fun v => 0 <= v < 2^64) 0x1002 0 FILLOK FILLOK FILLOK EL_INS_STACK_A _ (k + 2) Σ2 K (T (i + 1) mod 2^64));
        [exact IUL| exact GI2| exact IOS0| intros f Hf; exact Hf| exact FA| exact WR| exact FRM| apply LOQ; clear; ul
        | (cbn [d_G g_rfr length]; unfold FRAMES_TOT; clear; lia)| (cbn [d_G g_cr]; unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB; clear - CRB' KB K0 CB IN I1; lia)|].
      intros Σ4 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F4 fc4 m4 GI4 FRM4. cbn [d_G g_q g_F] in GI4 |- *. replace (k + 2 + 1) with (k + 3) in GI4 by (clear; lia). exact (STEP3 Σ4 m4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc4 GI4 FRM4). }
  subst t. destruct TY' as [E|E]; rewrite E in STEP2 |- *; unfold num_lit, num_len, num_ret1 in STEP2 |- *; cbn [Z.eqb Pos.eqb] in STEP2 |- *.
  - eapply (g_put_lit RT AF PMc FDO MST (d_G D) GOK FILLOK FILLOK _ k Σ K 0x23920 8 9 9%nat);
      [exact PUT| exact GI0| intros f Hf; exact Hf| exact FA| clear; cbn [In ACC_LITS]; repeat (first [left; reflexivity | right])| vm_compute; reflexivity| vm_compute; reflexivity
      | clear; lia| clear; lia| clear; lia| clear; unfold SEGTOP_A; lia| apply LOQ; clear; ul
      | (cbn [d_G g_rfr length]; unfold FRAMES_TOT; clear; lia)| (cbn [d_G g_cr]; unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB; clear - CRB' KB K0 CB IN I1; lia)|].
    clear m MI0 GI0. intros Σ2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 m GI2. cbn [d_G g_q g_F] in GI2 |- *. exact (STEP2 Σ2 m _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 GI2).
  - eapply (g_put_lit RT AF PMc FDO MST (d_G D) GOK FILLOK FILLOK _ k Σ K 0x23960 17 18 18%nat);
      [exact PUT| exact GI0| intros f Hf; exact Hf| exact FA| clear; cbn [In ACC_LITS]; repeat (first [left; reflexivity | right])| vm_compute; reflexivity| vm_compute; reflexivity
      | clear; lia| clear; lia| clear; lia| clear; unfold SEGTOP_A; lia| apply LOQ; clear; ul
      | (cbn [d_G g_rfr length]; unfold FRAMES_TOT; clear; lia)| (cbn [d_G g_cr]; unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB; clear - CRB' KB K0 CB IN I1; lia)|].
    clear m MI0 GI0. intros Σ2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 m GI2. cbn [d_G g_q g_F] in GI2 |- *. exact (STEP2 Σ2 m _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 GI2).
Qed.

Lemma dump_numdA : forall (K : config -> Prop) (i c : Z) (Σ : rts RT) (m : mem) (k : Z) (sv1 sv2 : list byte)
    (x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x24 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
  GI (dfrL D sv1 sv2) k Σ m -> frm0 fc -> 1 <= i -> i + 2 < n ->
  T i = tword t_dbl 0 -> KLOOP K (i + 2) c -> 0 <= k -> k + 5 <= DKH + EL_DUMP_CW * (i + 1) + EL_DUMP_CSB * c -> 0 <= c <= ae_sn (d_E D) ->
  aevt RT PMc Σ K (LSTA D 0xb7550 i x1 x5 x6 x7 (wz 0) x11 x12 (wz (ttype (T i))) x14 x15 x16 x17 x24 (wz (T i)) x28 x29 x30 x31 F fc m).
Proof using AF FDO MST DOK PUT INSD CRB.
  intros until fc. intros GI0 FRM I1 IN TY HK K0 KB CB. facts DOK.
  assert (Q0 : 0 <= dq D) by (clear - LQ LO1; ul). assert (QH : dq D + 256 < 2^63) by (clear - QT; ul).
  assert (FA : forall f, FILLOK f -> FILLOK (fill_after f)) by (intros f Hf; destruct (FILLOK_after f Hf) as [e|e]; rewrite e; [right; left| right; right]; reflexivity).
  assert (LOQ : forall d, d <= 12800 + RT_STACK -> lf_lo (d_X D) + d <= dq D) by (intros d Hd; clear - Hd LQ; lia).
  assert (CRB' : 62 + 24 * n + 4 * ae_sn (d_E D) <= d_cr D) by (clear - CRB; unfold EL_DUMP_C0, EL_DUMP_CW, EL_DUMP_CSB in CRB; lia).
  assert (F64x : d_f1 D mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
  pose proof (FFR _ _ ltac:(left; reflexivity)) as (A1 & A2 & A3). change (fs_size 4) with 1024 in A1, A2, A3.
  pose proof GI0 as (_ & MI0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR0 & _) & _). cbn [d_G g_q] in FR0.
  assert (TY' : ttype (T i) = 100) by (rewrite TY, ttype_tword by lia; reflexivity).
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (b_d1 D i sv1 sv2 x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x24 x28 x29 x30 x31 F fc m Q0 QH FR0 MI0 TY')|].
  cbv beta. intros ms1 ->. apply evt_done. unfold LSTA.
  eapply (g_put_lit RT AF PMc FDO MST (d_G D) GOK FILLOK FILLOK _ k Σ K 0x239a0 6 7 7%nat);
    [exact PUT| exact GI0| intros f Hf; exact Hf| exact FA| clear; cbn [In ACC_LITS]; repeat (first [left; reflexivity | right])| vm_compute; reflexivity| vm_compute; reflexivity
    | clear; lia| clear; lia| clear; lia| clear; unfold SEGTOP_A; lia| apply LOQ; clear; ul
    | (cbn [d_G g_rfr length]; unfold FRAMES_TOT; clear; lia)| (cbn [d_G g_cr]; unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB; clear - CRB' KB K0 CB IN I1; lia)|].
  clear m MI0 GI0 FR0. intros Σ2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 m GI2. cbn [d_G g_q g_F] in GI2 |- *. rewrite (ret_pc_even 0xb7720) by (clear; lia).

  pose proof GI2 as (_ & MI2 & _).
  pose proof (GINVA_ainv RT AF (d_G D) GOK (d_E D) _ _ _ _ _ _ _ GE AI0 GI2) as AI2.
  pose proof (GINVA_shz RT AF (d_G D) GOK (d_E D) _ _ _ _ _ _ _ GE AI0 GI2) as (SZT2 & _ & _).
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (b_d2a D i _ u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 x24 (wz (T i)) u3 u4 u5 u6 F2 fc m OKE EDOC ltac:(clear - I1; lia) ltac:(clear - IN; lia) ltac:(clear - NR; lia) AI2 MI2)|].
  cbv beta. intros ms2 (xa1 & ->).
  eapply evt_cut; [eapply (b_d2b D i _ u0 u1 u2 xa1 b2 b3 b4 b5 b6 b7 x24 (wz (T i)) u3 u4 u5 u6 F2 fc m OKE I1 ltac:(clear - IN; lia) AI2 SZT2 MI2)|].
  cbv beta. intros ms3 (x11' & F3 & ->). apply evt_done. unfold LSTA.
  eapply (g_insd RT AF PMc FDO MST (d_G D) GOK FILLOK FILLOK _ (k + 2) Σ2 K);
    [exact INSD| exact GI2| exact IOS0| intros f Hf; exact Hf| exact FA| exact FRM| apply LOQ; clear; ul
    | (cbn [d_G g_rfr length]; unfold FRAMES_TOT; clear; lia)| (cbn [d_G g_cr]; unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB; clear - CRB' KB K0 CB IN I1; lia)|].
  clear m MI2 GI2 AI2 SZT2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 F3 xa1 x11'. intros Σ4 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F4 fc4 m GI4 FRM4. cbn [d_G g_q g_F g_ff] in GI4 |- *. replace (k + 2 + 1) with (k + 3) in GI4 by (clear; lia).
  rewrite (ret_pc_even 0xb7758) by (clear; lia).

  pose proof GI4 as (_ & MI4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR4 & _) & WF4 & WS4 & _). cbn [d_G g_ff g_FS g_ffk g_q] in WF4, WS4, FR4. change (fs_size 1) with 128 in WF4, WS4.
  replace (128 - 8) with 120 in WF4 by reflexivity. change (128 / 8) with 16 in WS4.
  destruct (wr_at_cell m _ 120 64 1 WF4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [jc FC4].
  destruct (wr_at_cell m _ 16 8 1 WS4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [js FS4].
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (b_d3 D (i + 1) sv1 sv2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 x24 (wz (T i)) u3 u4 u5 u6 jc js F4 fc4 m Q0 QH F0);
    [clear - FLO LQ QT; ul| clear - SHLO LQ QT; ul| exact SHAP| clear - FLO LQ; ul| clear - SHLO LQ; ul| exact FR4| exact FC4| exact FS4| exact MI4]|].
  cbv beta. intros ms5 (m5 & -> & MU5 & WM5 & MI5 & FC5 & FS5). apply evt_done. unfold LSTA.
  assert (GI5 : GI (dfrL D sv1 sv2) (k + 3) Σ4 m5).
  { eapply (GINVA_cw RT AF (d_G D) GOK _ _ _ _ _ _ Σ4 m m5 _ GI4 MU5 WM5 MI5); [(intros ?; unfold own; cbn [outside d_G g_q g_fsz g_ff g_ffk]; change (fs_size 1) with 128; change (128 / 8) with 16; clear - A1; lia)| | reflexivity].
    cbn [d_G g_q]. apply (rw_cells_agree_nw asegs m m5 _ _ FR4). apply (agree_of_munch _ _ _ _ MU5). intros x Hx. cbn [d_G g_q] in Hx. rewrite (dfrL_size D sv1 sv2) in Hx.
    cbn [outside]. repeat split; try exact I; clear - Hx FLO LQ SHLO; ul. }
  clear GI4 MI4 FR4 WF4 WS4 FC4 FS4 MU5 WM5.
  eapply (g_put_ownc RT AF PMc FDO MST (d_G D) GOK FILLOK FILLOK _ (k + 3) Σ4 K 64 (Z_to_bv 8 10));
    [exact PUT| exact GI5| intros f Hf; exact Hf| exact FA| exact FC5| exact FS5| reflexivity| clear; lia| cbn [d_G g_ffk]; change (fs_size 1) with 128; clear; lia
    | apply LOQ; clear; ul| (cbn [d_G g_rfr length]; unfold FRAMES_TOT; clear; lia)| (cbn [d_G g_cr]; unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB; clear - CRB' KB K0 CB IN I1; lia)|].
  clear m m5 MI5 GI5 FC5 FS5 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F4. intros Σ6 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F6 m GI6. cbn [d_G g_q g_F g_ff] in GI6 |- *. replace (k + 3 + 2) with (k + 5) in GI6 by (clear; lia).
  rewrite (ret_pc_even 0xb7774) by (clear; lia).

  pose proof GI6 as (_ & MI6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR6 & _) & _ & WS6 & _). cbn [d_G g_ff g_FS g_ffk g_q] in WS6, FR6. change (fs_size 1) with 128 in WS6. change (128 / 8) with 16 in WS6.
  destruct (wr_at_cell m _ 16 8 1 WS6 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [js6 FS6].
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (b_d4 D (i + 1) u0 u1 u2 _ b1 b2 b3 b4 b5 b6 b7 x24 (wz (T i)) u3 u4 u5 u6 js6 F6 fc4 m F0); [clear - SHLO LQ QT; ul| exact FS6| exact MI6]|].
  cbv beta. intros ms7 (m7 & -> & MU7 & WM7 & MI7). apply evt_done.
  assert (GI7 : GI (dfrL D sv1 sv2) (k + 5) Σ6 m7).
  { eapply (GINVA_cw RT AF (d_G D) GOK _ _ _ _ _ _ Σ6 m m7 _ GI6 MU7 WM7 MI7); [(intros ?; unfold own; cbn [outside d_G g_q g_fsz g_ff g_ffk]; change (fs_size 1) with 128; change (128 / 8) with 16; clear - A1; lia)| | reflexivity].
    cbn [d_G g_q]. apply (rw_cells_agree_nw asegs m m7 _ _ FR6). apply (agree_of_munch _ _ _ _ MU7). intros x Hx. cbn [d_G g_q] in Hx. rewrite (dfrL_size D sv1 sv2) in Hx.
    cbn [outside]. repeat split; try exact I; clear - Hx FLO LQ SHLO; ul. }
  eapply (dump_joinA K (i + 1) c Σ6 m7 (k + 5) sv1 sv2); [exact GI7| exact FRM4| clear - I1; lia| clear - IN; lia| replace (i + 1 + 1) with (i + 2) by lia; exact HK| clear - K0; lia| clear - KB; lia].
Qed.
End Body.
