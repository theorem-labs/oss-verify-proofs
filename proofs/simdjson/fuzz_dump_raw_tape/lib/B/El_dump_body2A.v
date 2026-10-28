(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim SjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_fzwA Atp_defsA Atp_kitA Atp_objwA Atp_objnA Pj_rtkA Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_os_defsA El_ins_ifaceA El_esc_ifaceA El_dump_kitA El_dump_body1A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Ltac ls := lstep; try sb_fix.

Local Ltac prep D :=
  destruct D as [X E f1 L sp0 cr m0 gp xs6 xs9 xs10 xs11 jj]; cbn [d_X d_E d_f1 d_gp d_j d_s6 d_s9 d_s10 d_s11] in *;
  destruct X as [usp S1 Fr lo]; cbn [lf_usp lf_S1 lf_F lf_lo] in *;
  unfold LSTA, dfrL, dsaves, J, fa_saved, MASK56, shad, SHB in *; cbn [d_j d_f1 d_X d_E d_gp d_s6 d_s9 d_s10 d_s11 lf_usp lf_S1 lf_F lf_lo app nth] in *.
Local Ltac mu0 m := pose proof (munch_refl ([] : list (Z * Z)) m) as MU; pose proof (wmono_refl bsegs m) as WM.

Definition open_lit (t : Z) : Z := if t =? 123 then 0x237e0 else 0x23960.
Lemma o_w1 : forall (D : dctx) (i : Z) (sv1 sv2 : list byte) (x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x24 x28 x29 x30 x31 : word) F fc (m : mem),
  0 <= dq D -> dq D + 256 < 2^63 -> rw_cells bsegs m (dq D) (dfrL D sv1 sv2) -> mem_inv bsegs m ->
  0 <= ae_T (d_E D) i < 2^64 -> (ttype (ae_T (d_E D) i) = 123 \/ ttype (ae_T (d_E D) i) = 91) ->
  evt bsegs (fun ms => exists x24', ms = LSTA D EL_OSPUT i (wz 0xb080c) x5 x6 x7 (wz (dF D + 272)) (wz (open_lit (ttype (ae_T (d_E D) i)))) (wz 36)
                                               (wz (ttype (ae_T (d_E D) i))) x14 x15 x16 x17 x24' (wz (ae_T (d_E D) i)) x28 x29 x30 x31 F fc m)
    (LSTA D 0xb0748 i x1 x5 x6 x7 (wz 0) x11 x12 (wz (ttype (ae_T (d_E D) i))) x14 x15 x16 x17 x24 (wz (ae_T (d_E D) i)) x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros Q0 QH FR MI TR TY. prep D. mu0 m.
  assert (EQ : bv_unsigned (wz (S1 - 256)) = S1 - 256) by (apply unsigned_lit; lia).
  destruct TY as [TY|TY]; rewrite TY; unfold open_lit; cbn [Z.eqb Pos.eqb].
  -
    step. step. if_true. step. step. if_true. step. step. if_false. step. step. step. if_true.
    zstep. zstep. zstep. apply evt_done. eexists. atp_st_eq_goal.
  -
    step. step. if_false. step. step. if_false. step. zstep. step. step. if_false. step. step. if_false. step. step. if_false.
    step. zstep. zstep. zstep. zstep. apply evt_done. eexists. atp_st_eq_goal.
Qed.

Lemma o_w2 : forall (D : dctx) (i : Z) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) F fc (m : mem),
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists a1', ms = LSTA D EL_INS_U i (wz 0xb0814) x5 x6 x7 (wz (dF D + 272)) a1' x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m)
    (LSTA D 0xb080c i (wz 0xb080c) x5 x6 x7 (wz (dF D + 272)) x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m).
Proof. intros until m. intros MI. prep D. mu0 m. step. zstep. apply evt_done. eexists. atp_st_eq_goal. Qed.
Lemma o_w3 : forall (D : dctx) (i : Z) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) F fc (m : mem),
  mem_inv bsegs m ->
  evt bsegs (fun ms => ms = LSTA D EL_OSPUT i (wz 0xb0824) x5 x6 x7 (wz (dF D + 272)) (wz 0x23840) (wz 31) x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m)
    (LSTA D 0xb0814 i (wz 0xb0814) x5 x6 x7 (wz (dF D + 272)) x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m).
Proof. intros until m. intros MI. prep D. mu0 m. zstep. zstep. zstep. zstep. apply evt_done. atp_st_eq_goal. Qed.
Lemma o_w4 : forall (D : dctx) (i : Z) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) F fc (m : mem),
  mem_inv bsegs m ->
  evt bsegs (fun ms => ms = LSTA D EL_OSPUT i (wz 0xb0834) x5 x6 x7 (wz (dF D + 272)) (wz 0x23880) (wz 17) x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m)
    (LSTA D 0xb0824 i (wz 0xb0824) x5 x6 x7 (wz (dF D + 272)) x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m).
Proof. intros until m. intros MI. prep D. mu0 m. zstep. zstep. zstep. zstep. apply evt_done. atp_st_eq_goal. Qed.
Lemma o_w5 : forall (D : dctx) (i : Z) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) F fc (m : mem),
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists a1', ms = LSTA D EL_INS_UL i (wz 0xb0840) x5 x6 x7 (wz (dF D + 272)) a1' x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m)
    (LSTA D 0xb0834 i (wz 0xb0834) x5 x6 x7 (wz (dF D + 272)) x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m).
Proof. intros until m. intros MI. prep D. mu0 m. zstep. zstep. zstep. apply evt_done. eexists. atp_st_eq_goal. Qed.
Lemma o_w6 : forall (D : dctx) (i : Z) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) F fc (m : mem),
  mem_inv bsegs m ->
  evt bsegs (fun ms => ms = LSTA D EL_OSPUT i (wz 0xb0b1c) x5 x6 x7 (wz (dF D + 272)) (wz 0x23700) (wz 1) x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m)
    (LSTA D 0xb0840 i (wz 0xb0840) x5 x6 x7 (wz (dF D + 272)) x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m).
Proof. intros until m. intros MI. prep D. mu0 m. zstep. zstep. zstep. zstep. zstep. apply evt_done. atp_st_eq_goal. Qed.

Definition close_lit (t : Z) : Z := if t =? 125 then 0x238c0 else 0x239c0.
Lemma c_w1 : forall (D : dctx) (i : Z) (sv1 sv2 : list byte) (x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x24 x28 x29 x30 x31 : word) F fc (m : mem),
  0 <= dq D -> dq D + 256 < 2^63 -> rw_cells bsegs m (dq D) (dfrL D sv1 sv2) -> mem_inv bsegs m ->
  (ttype (ae_T (d_E D) i) = 125 \/ ttype (ae_T (d_E D) i) = 93) ->
  evt bsegs (fun ms => exists x12', ms = LSTA D EL_OSPUT i (wz 0xb0b04) x5 x6 x7 (wz (dF D + 272)) (wz (close_lit (ttype (ae_T (d_E D) i)))) (wz 40)
                                               (wz (ttype (ae_T (d_E D) i))) x14 x15 x16 x17 x24 (wz (ae_T (d_E D) i)) x28 x29 x30 x31 F fc m /\ x12' = x12)
    (LSTA D 0xb0748 i x1 x5 x6 x7 (wz 0) x11 x12 (wz (ttype (ae_T (d_E D) i))) x14 x15 x16 x17 x24 (wz (ae_T (d_E D) i)) x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros Q0 QH FR MI TY. prep D. mu0 m.
  assert (EQ : bv_unsigned (wz (S1 - 256)) = S1 - 256) by (apply unsigned_lit; lia).
  destruct TY as [TY|TY]; rewrite TY; unfold close_lit; cbn [Z.eqb Pos.eqb].
  -
    step. step. if_true. step. step. if_true. step. step. if_false. step. step. step. if_false. step. step. step. if_false.
    zstep. zstep. zstep. zstep. apply evt_done. eexists. split; [atp_st_eq_goal| reflexivity].
  -
    step. step. if_false. step. step. if_true. step. step. if_true.
    zstep. zstep. zstep. zstep. zstep. apply evt_done. eexists. split; [atp_st_eq_goal| reflexivity].
Qed.
Lemma c_w2 : forall (D : dctx) (i : Z) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) F fc (m : mem),
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists a1', ms = LSTA D EL_INS_U i (wz 0xb0b0c) x5 x6 x7 (wz (dF D + 272)) a1' x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m)
    (LSTA D 0xb0b04 i (wz 0xb0b04) x5 x6 x7 (wz (dF D + 272)) x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m).
Proof. intros until m. intros MI. prep D. mu0 m. step. zstep. apply evt_done. eexists. atp_st_eq_goal. Qed.
Lemma c_w3 : forall (D : dctx) (i : Z) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) F fc (m : mem),
  mem_inv bsegs m ->
  evt bsegs (fun ms => ms = LSTA D EL_OSPUT i (wz 0xb0b1c) x5 x6 x7 (wz (dF D + 272)) (wz 0x23920) (wz 22) x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m)
    (LSTA D 0xb0b0c i (wz 0xb0b0c) x5 x6 x7 (wz (dF D + 272)) x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m).
Proof. intros until m. intros MI. prep D. mu0 m. zstep. zstep. zstep. zstep. apply evt_done. atp_st_eq_goal. Qed.

Section SbufB.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Lemma sbs_byteA : forall o, 0 <= o < ae_sn E -> 0 <= ae_S E o < 256.
  Proof using OK.
    intros o Ho. destruct OK as [_ SBS _ _ _ _ _ _ _ _ _]. unfold Tf. apply Forall_nth_Z; [exact SBS| lia].
  Qed.

  Definition sbuf_bytesA (o l : Z) : list byte := firstn (Z.to_nat l) (skipn (Z.to_nat (o + 4)) (map (Z_to_bv 8) (ae_sbs E))).
  Lemma sbuf_bytesA_at : forall m o l, bytes_at bsegs m (ae_SBUF E) (map (Z_to_bv 8) (ae_sbs E)) -> 0 <= o -> 0 <= l -> o + 4 + l < ae_sn E ->
    bytes_at bsegs m (ae_SBUF E + o + 4) (sbuf_bytesA o l) /\ length (sbuf_bytesA o l) = Z.to_nat l.
  Proof.
    intros m o l HB Ho Hl Hol. unfold sbuf_bytesA. split.
    - replace (ae_SBUF E + o + 4) with (ae_SBUF E + Z.of_nat (Z.to_nat (o + 4))) by lia.
      apply bytes_at_firstn. apply bytes_at_skipn; [exact HB|]. rewrite length_map. lia.
    - rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn, length_map. lia.
  Qed.
End SbufB.

Lemma s_w1 : forall (D : dctx) (i : Z) (sv1 sv2 : list byte) (x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x24 x28 x29 x30 x31 : word) F fc (m : mem),
  0 <= dq D -> dq D + 256 < 2^63 -> rw_cells bsegs m (dq D) (dfrL D sv1 sv2) -> mem_inv bsegs m ->
  0 <= ae_T (d_E D) i < 2^64 -> ttype (ae_T (d_E D) i) = 34 ->
  evt bsegs (fun ms => ms = LSTA D EL_OSPUT i (wz 0xb09a4) x5 x6 x7 (wz (dF D + 272)) (wz 0x236c0) (wz 8) (wz 34) x14 x15 x16 x17 (wz (tval (ae_T (d_E D) i))) (wz (ae_T (d_E D) i)) x28 x29 x30 x31 F fc m)
    (LSTA D 0xb0748 i x1 x5 x6 x7 (wz 0) x11 x12 (wz (ttype (ae_T (d_E D) i))) x14 x15 x16 x17 x24 (wz (ae_T (d_E D) i)) x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros Q0 QH FR MI TR TY. prep D. mu0 m. rewrite TY.
  assert (EQ : bv_unsigned (wz (S1 - 256)) = S1 - 256) by (apply unsigned_lit; lia).

  step. step. if_false. step. step. if_false. step. zstep. rewrite ?land64_mod, (land_mask56 (ae_T E i)) by lia. step. step. if_true.
  zstep. zstep. step. zstep. apply evt_done. atp_st_eq_goal.
Qed.

Lemma s_w2 : forall (D : dctx) (i o l : Z) (sv1 sv2 : list byte) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word) F fc (m : mem),
  0 <= dq D -> dq D + 256 < 2^63 -> rw_cells bsegs m (dq D) (dfrL D sv1 sv2) ->
  aenvA_ok (d_E D) -> ae_DOC (d_E D) = dDOC D -> str_at (ae_S (d_E D)) (ae_sn (d_E D)) o l ->
  AINV_A (d_E D) m -> shz m (ae_SBUF (d_E D)) (ae_NS (d_E D)) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) a2' a3' a4',
      ms = LSTA D 0xb0da0 i (wz 0xb0a40) x5 x6 x7 (wz (dF D + 272)) (wz (dq D + 136)) a2' a3' a4' x15 x16 x17 (wz o) x25 x28 x29 x30 x31 F fc m1
      /\ munch [(dq D + 136, dq D + 152)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (dq D) (dfrL D (le8 (wz (ae_SBUF (d_E D) + o + 4))) (le8 (wz l))) /\ rw_cells bsegs m1 (dq D + 136) [C8 (wz (ae_SBUF (d_E D) + o + 4)); C8 (wz l)])
    (LSTA D 0xb09a4 i (wz 0xb09a4) x5 x6 x7 (wz (dF D + 272)) x11 x12 x13 x14 x15 x16 x17 (wz o) x25 x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros Q0 QH FR OK EDOC SA AI SHZS MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SN & SS & SL) _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *. assert (HSN : ae_sn (d_E D) < 2^56) by (destruct WF as (_ & ? & _); lia).
  pose proof (str_at_bounds _ _ HSN _ _ SA) as (O0 & L0 & OL & LE & O56).
  pose proof AI as (_ & SBUFB & _ & DOCC & DSH). rewrite EDOC in DOCC, DSH.
  prep D. replace (Fr + 56 + 8) with (Fr + 64) in * by lia.
  lazymatch goal with |- context [munch ?W0 m _] => pose proof (munch_refl W0 m) as MU end. pose proof (wmono_refl bsegs m) as WM.
  assert (EQ : bv_unsigned (wz (S1 - 256)) = S1 - 256) by (apply unsigned_lit; lia).

  pose proof (proj2 (proj1 (rw_cells_app bsegs m (Fr + 56) [_] [_]) DOCC)) as DOC2. cbn [cells_size csize Nat.add] in DOC2. replace (Fr + 56 + Z.of_nat 8) with (Fr + 64) in DOC2 by lia.
  pose proof (shz_of_zero_run m (Fr + 56) 2 ltac:(rewrite EDOC in D8; exact D8) ltac:(lia) DSH) as SHZD. change (8 * Z.of_nat 2) with 16 in SHZD.
  step. shz_pose SHZD (Fr + 64). zstep. shz_norm. zstep. if_false.
  step. step. astep.

  step. if_dead1 by O0 OL SS SL. astep. astep.
  replace (0 <? ae_SBUF E) with true by (symmetry; apply Z.ltb_lt; lia). replace (o + ae_SBUF E <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  astep. step. if_false. replace (o + ae_SBUF E) with (ae_SBUF E + o) by lia.
  chk0 SHZS (ae_SBUF E + o). step. if_false. astep. chk0 SHZS (ae_SBUF E + o + 3). step. if_false.

  step. if_dead1 by SS. zstep. step. replace (Z_to_bv 64 (-5)) with (Z_to_bv 64 18446744073709551611) by (apply Z_to_bv64_eqm; reflexivity).
  if_cases KB; zify_cond KB; [exfalso; clear - KB O0 OL SN SL HL HT L0; lia| clear KB].
  pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) o SBUFB ltac:(lia)) as RB0.
  pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (o + 1) SBUFB ltac:(lia)) as RB1.
  pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (o + 2) SBUFB ltac:(lia)) as RB2.
  pose proof (sbuf_read1 m (ae_SBUF E) (ae_sbs E) (o + 3) SBUFB ltac:(lia)) as RB3.
  pose proof (sbs_byteA E OK o ltac:(lia)) as Y0. pose proof (sbs_byteA E OK (o + 1) ltac:(lia)) as Y1.
  pose proof (sbs_byteA E OK (o + 2) ltac:(lia)) as Y2. pose proof (sbs_byteA E OK (o + 3) ltac:(lia)) as Y3.
  hide SBUFB. clear SHRD SHRD0 SHRD1.

  do 11 zstep.
  rewrite ?(a_u8_small (ae_S E o)), ?(a_u8_small (ae_S E (o + 1))), ?(a_u8_small (ae_S E (o + 2))), ?(a_u8_small (ae_S E (o + 3))) by (clear - Y0 Y1 Y2 Y3; lia).
  rewrite ?land64_mod. rewrite ?shl_mod_smallA by (clear - Y0 Y1 Y2 Y3; lia). rewrite le32_of_lbu4A by (clear - Y0 Y1 Y2 Y3; lia).
  change (ae_S E o + 2 ^ 8 * ae_S E (o + 1) + 2 ^ 16 * ae_S E (o + 2) + 2 ^ 24 * ae_S E (o + 3)) with (le32 (ae_S E) o). rewrite LE.
  clear RB0 RB1 RB2 RB3.

  lstep. lstep. zstep. zstep. zstep.
  apply evt_done. do 4 eexists. split; [atp_st_eq_goal|]. split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia|].
  split; [exact WM|]. split; [assumption|]. split.
  - apply (rw_cells_forget_C8 bsegs _ _ [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _] _ _).
    apply (rw_cells_forget_C8 bsegs _ _ [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _] _ _). exact FR.
  - pose proof FR as X. lazymatch type of X with rw_cells _ _ _ ?l => rewrite <- (firstn_skipn 17 l) in X end. cbn [firstn skipn] in X.
    apply rw_cells_app in X. destruct X as [_ X]. cbn [cells_size csize Nat.add] in X.
    lazymatch type of X with rw_cells _ _ _ ?l => rewrite <- (firstn_skipn 2 l) in X end. cbn [firstn skipn] in X.
    apply rw_cells_app in X. destruct X as [X _]. replace (S1 - 256 + Z.of_nat 136) with (S1 - 256 + 136) in X by lia. exact X.
Qed.

Lemma s_w3 : forall (D : dctx) (i : Z) (sv1 sv2 : list byte) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) (jc js : list byte) F fc (m : mem),
  0 <= dq D -> dq D + 256 < 2^63 -> 0 < d_f1 D -> d_f1 D + 128 < 2^63 -> shad (d_f1 D) + 16 < 2^63 -> (d_f1 D + 128 <= shad (d_f1 D) \/ shad (d_f1 D) + 16 <= d_f1 D) ->
  d_f1 D + 128 <= dq D -> shad (d_f1 D) + 16 <= dq D -> rw_cells bsegs m (dq D) (dfrL D sv1 sv2) ->
  rw_cells bsegs m (d_f1 D + 96) [CB 1 jc] -> rw_cells bsegs m (shad (d_f1 D) + 12) [CB 1 js] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = LSTA D EL_OSPUT i (wz 0xb0a60) x5 x6 x7 (wz (dF D + 272)) (wz (d_f1 D + 96)) (wz 1) x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m1
      /\ munch [(d_f1 D + 96, d_f1 D + 97); (shad (d_f1 D) + 12, shad (d_f1 D) + 13)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (d_f1 D + 96) [C1 (Z_to_bv 8 34)] /\ rw_cells bsegs m1 (shad (d_f1 D) + 12) [C1 (Z_to_bv 8 1)])
    (LSTA D 0xb0a40 i (wz 0xb0a40) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros Q0 QH F0 FH SHH SAP FQ SQ FR FC FS MI. prep D.
  lazymatch goal with |- context [munch ?W0 m _] => pose proof (munch_refl W0 m) as MU end. pose proof (wmono_refl bsegs m) as WM.
  assert (EQ : bv_unsigned (wz (S1 - 256)) = S1 - 256) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (wz f1) = f1) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (wz (f1 / 8 + 2147450880)) = f1 / 8 + 2147450880) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  replace (f1 / 8 + 2147450880 + 12) with (f1 / 8 + 2147450892) in FS by lia.
  zstep. ls. step. zstep. ls. zstep. zstep. zstep.
  apply evt_done. eexists. split; [atp_st_eq_goal|]. split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia|].
  split; [exact WM|]. split; [assumption|]. replace (f1 / 8 + 2147450880 + 12) with (f1 / 8 + 2147450892) by lia. split; [exact FC| exact FS].
Qed.

Lemma s_w4 : forall (D : dctx) (i : Z) (sv1 sv2 : list byte) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) (jc js js2 : list byte) F fc (m : mem),
  0 <= dq D -> dq D + 256 < 2^63 -> 0 < d_f1 D -> d_f1 D + 128 < 2^63 -> shad (d_f1 D) + 16 < 2^63 -> (d_f1 D + 128 <= shad (d_f1 D) \/ shad (d_f1 D) + 16 <= d_f1 D) ->
  d_f1 D + 128 <= dq D -> shad (d_f1 D) + 16 <= dq D -> rw_cells bsegs m (dq D) (dfrL D sv1 sv2) ->
  rw_cells bsegs m (d_f1 D + 80) [CB 1 jc] -> rw_cells bsegs m (shad (d_f1 D) + 10) [CB 1 js] -> rw_cells bsegs m (shad (d_f1 D) + 12) [CB 1 js2] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = LSTA D EL_OSPUT i (wz 0xb0a88) x5 x6 x7 (wz (dF D + 272)) (wz (d_f1 D + 80)) (wz 1) x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m1
      /\ munch [(d_f1 D + 80, d_f1 D + 81); (shad (d_f1 D) + 10, shad (d_f1 D) + 11); (shad (d_f1 D) + 12, shad (d_f1 D) + 13)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (d_f1 D + 80) [C1 (Z_to_bv 8 10)] /\ rw_cells bsegs m1 (shad (d_f1 D) + 10) [C1 (Z_to_bv 8 1)])
    (LSTA D 0xb0a60 i (wz 0xb0a60) x5 x6 x7 (wz (dF D + 272)) x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros Q0 QH F0 FH SHH SAP FQ SQ FR FC FS FS2 MI. prep D.
  lazymatch goal with |- context [munch ?W0 m _] => pose proof (munch_refl W0 m) as MU end. pose proof (wmono_refl bsegs m) as WM.
  assert (EQ : bv_unsigned (wz (S1 - 256)) = S1 - 256) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (wz f1) = f1) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (wz (f1 / 8 + 2147450880)) = f1 / 8 + 2147450880) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  replace (f1 / 8 + 2147450880 + 10) with (f1 / 8 + 2147450890) in FS by lia. replace (f1 / 8 + 2147450880 + 12) with (f1 / 8 + 2147450892) in FS2 by lia.
  zstep. ls. zstep. ls. step. zstep. ls. zstep. zstep. zstep.
  apply evt_done. eexists. split; [atp_st_eq_goal|]. split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia|].
  split; [exact WM|]. split; [assumption|]. replace (f1 / 8 + 2147450880 + 10) with (f1 / 8 + 2147450890) by lia. split; [exact FC| exact FS].
Qed.

Lemma s_w5 : forall (D : dctx) (i : Z) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) (js : list byte) F fc (m : mem),
  0 < d_f1 D -> shad (d_f1 D) + 16 < 2^63 ->
  rw_cells bsegs m (shad (d_f1 D) + 10) [CB 1 js] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = LSTA D 0xb0b1c i (wz 0xb0a88) x5 x6 x7 (wz (-8)) x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m1
      /\ munch [(shad (d_f1 D) + 10, shad (d_f1 D) + 11)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1)
    (LSTA D 0xb0a88 i (wz 0xb0a88) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros F0 SHH FS MI. prep D.
  lazymatch goal with |- context [munch ?W0 m _] => pose proof (munch_refl W0 m) as MU end. pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (wz (f1 / 8 + 2147450880)) = f1 / 8 + 2147450880) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  replace (f1 / 8 + 2147450880 + 10) with (f1 / 8 + 2147450890) in FS by lia.
  zstep. ls. zstep.
  apply evt_done. eexists. split; [atp_st_eq_goal|]. split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia|].
  split; [exact WM| assumption].
Qed.

Lemma x_w1 : forall (D : dctx) (i : Z) (x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x24 x28 x29 x30 x31 : word) F fc (m : mem),
  mem_inv bsegs m -> ttype (ae_T (d_E D) i) = 114 ->
  evt bsegs (fun ms => exists x11' x12', ms = LSTA D 0xb0c58 i x1 x5 x6 x7 (wz 0) x11' x12' (wz 114) x14 x15 x16 x17 x24 (wz (ae_T (d_E D) i)) x28 x29 x30 x31 F fc m)
    (LSTA D 0xb0748 i x1 x5 x6 x7 (wz 0) x11 x12 (wz (ttype (ae_T (d_E D) i))) x14 x15 x16 x17 x24 (wz (ae_T (d_E D) i)) x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros MI TY. prep D. mu0 m. rewrite TY.

  step. step. if_true. step. step. if_false. step. step. if_false. step. step. step. if_false. step. step. if_true.
  apply evt_done. do 2 eexists. atp_st_eq_goal.
Qed.

Lemma x_w2 : forall (D : dctx) (i : Z) (sv1 sv2 jm jsh : list byte) (x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) F fc (m : mem),
  0 <= dq D -> dq D + 256 < 2^63 -> 0 < d_f1 D -> d_f1 D + 128 < 2^63 -> shad (d_f1 D) + 16 < 2^63 -> (d_f1 D + 128 <= shad (d_f1 D) \/ shad (d_f1 D) + 16 <= d_f1 D) ->
  d_f1 D + 128 <= dq D -> shad (d_f1 D) + 16 <= dq D ->
  rw_cells bsegs m (dq D) (dfrL D sv1 sv2) -> rw_cells bsegs m (d_f1 D) [CB 8 jm] -> rw_cells bsegs m (shad (d_f1 D)) [CB 16 jsh] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = LSTA D 0xb0cb0 i x1 x5 x6 x7 (wz 0) (wz (-11)) (wz (d_f1 D)) (wz 114) x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m1
      /\ munch [(d_f1 D, d_f1 D + 8); (shad (d_f1 D), shad (d_f1 D) + 16)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1)
    (LSTA D 0xb0c58 i x1 x5 x6 x7 (wz 0) x11 x12 (wz 114) x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros Q0 QH F0 FH SHH SAP FQ SQ FR FM FS MI. prep D.
  lazymatch goal with |- context [munch ?W0 m _] => pose proof (munch_refl W0 m) as MU end. pose proof (wmono_refl bsegs m) as WM.
  assert (EQ : bv_unsigned (wz (S1 - 256)) = S1 - 256) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (wz f1) = f1) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (wz (f1 / 8 + 2147450880)) = f1 / 8 + 2147450880) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] (repeat 1%nat 16)) in FS; [| reflexivity]. cbn [repeat mk_CB_cells app] in FS.
  zstep. zstep. lstep. step. zstep. if_false. zstep. do 16 ls.
  apply evt_done. eexists. split; [atp_st_eq_goal|]. split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia|].
  split; [exact WM| assumption].
Qed.

Lemma x_w3 : forall (D : dctx) (i fl : Z) (sv1 sv2 : list byte) (x1 x5 x6 x7 x11 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) F fc (m : mem),
  0 <= dq D -> dq D + 256 < 2^63 -> 0 < fl -> fl + 1 < 2^63 -> fl + 1 <= lf_lo (d_X D) -> lf_lo (d_X D) <= dq D -> 0 < d_f1 D -> d_f1 D + 128 <= dq D ->
  stk bsegs m (lf_lo (d_X D)) (dq D) -> rw_cells bsegs m (dq D) (dfrL D sv1 sv2) -> rw_cells bsegs m fl [C1 (Z_to_bv 8 1)] -> ro_cells bsegs m (d_f1 D + 120) [C8 (wz fl)] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz EL_DUMPRET_A) (wz (lf_S1 (d_X D))) (d_gp D) (wz TPV_A) x5 x6 x7 (wz (lf_usp (d_X D))) (wz (lf_S1 (d_X D))) (wz 0) (wz fl) (wz (d_f1 D)) (wz 114) x14 x15 x16 x17
                   (wz (dF D)) (wz (shad (dF D))) (wz (dF D + 32)) (wz (dF D + 144)) (d_s6 D) (wz (dF D + 272)) (wz (dF D)) (d_s9 D) (d_s10 D) (d_s11 D) x28 x29 x30 x31)
              F (ret_pc (wz EL_DUMPRET_A)) fc None m1 (seg_rom bsegs)
      /\ munch [(fl, fl + 1)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ rw_cells bsegs m1 fl [C1 (Z_to_bv 8 0)] /\ stk bsegs m1 (lf_lo (d_X D)) (lf_S1 (d_X D)))
    (LSTA D 0xb0cb0 i x1 x5 x6 x7 (wz 0) x11 (wz (d_f1 D)) (wz 114) x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros Q0 QH FL0 FLH FLO LOQ F0 FQ ST FR FC FW MI. prep D.
  lazymatch goal with |- context [munch ?W0 m _] => pose proof (munch_refl W0 m) as MU end. pose proof (wmono_refl bsegs m) as WM.
  assert (EQ : bv_unsigned (wz (S1 - 256)) = S1 - 256) by (apply unsigned_lit; lia).
  assert (EU : bv_unsigned (wz S1) = S1) by (apply unsigned_lit; lia).
  assert (EFL : bv_unsigned (wz fl) = fl) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (wz f1) = f1) by (apply unsigned_lit; lia).
  step. ls. zstep. zstep. replace (S1 + -256) with (S1 - 256) by (clear; lia). do 13 step. zstep. release_frame FR ST S1. step.
  apply evt_done. eexists. split; [atp_st_eq_goal|]. split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia|].
  split; [exact WM|]. split; [assumption|]. split; [exact FC| exact ST].
Qed.

Section Body2.
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
Hypothesis ESC : esc_cpsA RT PMc.
Hypothesis CRB : EL_DUMP_C0 - 2 + EL_DUMP_CW * ae_n (d_E D) + EL_DUMP_CSB * ae_sn (d_E D) <= d_cr D.

Local Ltac ul := unfold EL_DUMP_STACK_A, EL_PUT_STACK_A, EL_INS_STACK_A, EL_INSD_STACK_A, EL_ESC_STACK_A, FUZZ_STACK, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.
Notation GI := (GINVA RT (d_G D) 0x1002 0 FILLOK).
Notation n := (ae_n (d_E D)).
Notation T := (ae_T (d_E D)).
Notation KLOOP := (KLOOPA RT PMc D).
Local Ltac facts DOK :=
  pose proof DOK as (GOK & GE & LK & AI0 & IOS0 & WFS & LJ & NEED);
  pose proof GOK as [(Q32 & FS0 & QT & LQ) (LO1 & LO2) (SP1 & SP2) (E0 & E64 & ESEG & ELO & EIN & ESH & ESHL & EHI) (F0 & F64 & FSEG & FLO & FSR & FHI & SHLO & SHAP) FFR FFL RFR LL];
  cbn [d_G g_q g_fsz g_lo g_F g_ff g_ffk g_rfr g_L g_sp0 g_cr g_m0] in *; change (fs_size 1) with 128 in *; change (128 / 8) with 16 in *;
  pose proof GE as (OKE & ELOE & EDOC & EFD & EKD & INT & INS & INP & QHI); cbn [d_G g_lo g_F g_L] in ELOE, EDOC, EFD, INT, INS, INP;
  pose proof WFS as (NR & SNR & TR0 & _).

Local Ltac putlit GIx BUF N CAPL nb kx Σx LOQ FA CRB' KB K0 CB IN I1 :=
  eapply (g_put_lit RT AF PMc FDO MST (d_G D) ltac:(exact (proj1 DOK)) FILLOK FILLOK _ kx Σx _ BUF N CAPL nb);
    [exact PUT| exact GIx| intros f Hf; exact Hf| exact FA| clear; cbn [In ACC_LITS]; repeat (first [left; reflexivity | right])| vm_compute; reflexivity| vm_compute; reflexivity
    | clear; lia| clear; lia| clear; lia| clear; unfold SEGTOP_A; lia| apply LOQ; clear; ul
    | (cbn [d_G g_rfr length]; unfold FRAMES_TOT; clear; lia)| (cbn [d_G g_cr]; unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB; clear - CRB' KB K0 CB IN I1; lia)|].

Lemma dump_openA : forall (K : config -> Prop) (i c : Z) (Σ : rts RT) (m : mem) (k : Z) (sv1 sv2 : list byte)
    (x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x24 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
  GI (dfrL D sv1 sv2) k Σ m -> frm0 fc -> 1 <= i -> i + 1 < n -> 0 <= T i < 2^64 ->
  (ttype (T i) = 123 \/ ttype (T i) = 91) -> KLOOP K (i + 1) c -> 0 <= k -> k + 10 <= DKH + EL_DUMP_CW * i + EL_DUMP_CSB * c -> 0 <= c <= ae_sn (d_E D) ->
  aevt RT PMc Σ K (LSTA D 0xb0748 i x1 x5 x6 x7 (wz 0) x11 x12 (wz (ttype (T i))) x14 x15 x16 x17 x24 (wz (T i)) x28 x29 x30 x31 F fc m).
Proof using AF FDO MST DOK PUT IUL IU CRB.
  intros until fc. intros GI0 FRM I1 IN TIR TY HK K0 KB CB. facts DOK.
  assert (Q0 : 0 <= dq D) by (clear - LQ LO1; ul). assert (QH : dq D + 256 < 2^63) by (clear - QT; ul).
  assert (FA : forall f, FILLOK f -> FILLOK (fill_after f)) by (intros f Hf; destruct (FILLOK_after f Hf) as [e|e]; rewrite e; [right; left| right; right]; reflexivity).
  assert (LOQ : forall d, d <= 12800 + RT_STACK -> lf_lo (d_X D) + d <= dq D) by (intros d Hd; clear - Hd LQ; lia).
  assert (CRB' : 62 + 24 * n + 4 * ae_sn (d_E D) <= d_cr D) by (clear - CRB; unfold EL_DUMP_C0, EL_DUMP_CW, EL_DUMP_CSB in CRB; lia).
  assert (F64x : d_f1 D mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
  pose proof (FFR _ _ ltac:(left; reflexivity)) as (A1 & A2 & A3). change (fs_size 3) with 512 in A1, A2, A3.
  pose proof GI0 as (_ & MI0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR0 & _) & _). cbn [d_G g_q] in FR0.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (o_w1 D i sv1 sv2 x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x24 x28 x29 x30 x31 F fc m Q0 QH FR0 MI0 TIR TY)|].
  cbv beta. intros ms1 (x24' & ->). apply evt_done. unfold LSTA.
  assert (STEP2 : forall (Σ2 : rts RT) (m2 : mem) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 (F2 : bvmap 5 word),
    GI (dfrL D sv1 sv2) (k + 2) Σ2 m2 ->
    aevt RT PMc Σ2 K (MS (mkR (wz 0xb080c) (wz (dq D)) (d_gp D) (wz TPV_A) u0 u1 u2 (wz (lf_S1 (d_X D))) (wz (dq D)) (wz (dF D + 272)) b1 b2 b3 b4 b5 b6 b7
                             (wz (d_f1 D)) (wz (dF D + 272)) (wz (dDOC D)) (wz n) (wz SHB) (wz (T i)) (wz 0x23620) (wz (shad (d_f1 D))) x24' (wz i) u3 u4 u5 u6)
                        F2 (ret_pc (wz 0xb080c)) fc None m2 (seg_rom bsegs))).
  2:{ destruct TY as [E|E]; rewrite E; unfold open_lit; cbn [Z.eqb Pos.eqb].
      - putlit GI0 0x237e0 36 37 37%nat k Σ LOQ FA CRB' KB K0 CB IN I1.
        clear m MI0 GI0 FR0. intros Σ2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 m GI2. cbn [d_G g_q g_F] in GI2 |- *. exact (STEP2 Σ2 m _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 GI2).
      - putlit GI0 0x23960 36 37 37%nat k Σ LOQ FA CRB' KB K0 CB IN I1.
        clear m MI0 GI0 FR0. intros Σ2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 m GI2. cbn [d_G g_q g_F] in GI2 |- *. exact (STEP2 Σ2 m _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 GI2). }
  intros Σ2 m2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 GI2. pose proof GI2 as (_ & MI2 & _).
  rewrite (ret_pc_even 0xb080c) by (clear; lia). apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (o_w2 D i u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 x24' (wz (T i)) u3 u4 u5 u6 F2 fc m2 MI2)|].
  cbv beta. intros ms3 (a1w & ->). apply evt_done. unfold LSTA. rewrite <- (Z_to_bv_bv_unsigned a1w).
  pose proof (bv_unsigned_in_range 64 a1w) as A1R. unfold bv_modulus in A1R. change (2 ^ Z.of_N 64) with (2^64) in A1R.
  eapply (g_ins RT AF PMc FDO MST (d_G D) GOK EL_INS_U (fun v => 0 <= v < 2^64) 0x1002 0 FILLOK FILLOK FILLOK EL_INS_STACK_A _ (k + 2) Σ2 K (bv_unsigned a1w));
    [exact IU| exact GI2| exact IOS0| intros f Hf; exact Hf| exact FA| exact A1R| exact FRM| apply LOQ; clear; ul
    | (cbn [d_G g_rfr length]; unfold FRAMES_TOT; clear; lia)| (cbn [d_G g_cr]; unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB; clear - CRB' KB K0 CB IN I1; lia)|].
  clear m2 MI2 GI2 A1R u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2. intros Σ3 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F3 fc3 m3 GI3 FRM3. cbn [d_G g_q g_F] in GI3 |- *.
  replace (k + 2 + 1) with (k + 3) in GI3 by (clear; lia). pose proof GI3 as (_ & MI3 & _).
  rewrite (ret_pc_even 0xb0814) by (clear; lia). apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (o_w3 D i u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 x24' (wz (T i)) u3 u4 u5 u6 F3 fc3 m3 MI3)|].
  cbv beta. intros ms4 ->. apply evt_done. unfold LSTA.
  putlit GI3 0x23840 31 32 32%nat (k + 3) Σ3 LOQ FA CRB' KB K0 CB IN I1.
  clear m3 MI3 GI3 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F3. intros Σ4 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F4 m4 GI4. cbn [d_G g_q g_F] in GI4 |- *.
  replace (k + 3 + 2) with (k + 5) in GI4 by (clear; lia). pose proof GI4 as (_ & MI4 & _).
  rewrite (ret_pc_even 0xb0824) by (clear; lia). apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (o_w4 D i u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 x24' (wz (T i)) u3 u4 u5 u6 F4 fc3 m4 MI4)|].
  cbv beta. intros ms5 ->. apply evt_done. unfold LSTA.
  putlit GI4 0x23880 17 18 18%nat (k + 5) Σ4 LOQ FA CRB' KB K0 CB IN I1.
  clear m4 MI4 GI4 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F4. intros Σ5 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F5 m5 GI5. cbn [d_G g_q g_F] in GI5 |- *.
  replace (k + 5 + 2) with (k + 7) in GI5 by (clear; lia). pose proof GI5 as (_ & MI5 & _).
  rewrite (ret_pc_even 0xb0834) by (clear; lia). apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (o_w5 D i u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 x24' (wz (T i)) u3 u4 u5 u6 F5 fc3 m5 MI5)|].
  cbv beta. intros ms6 (a1v & ->). apply evt_done. unfold LSTA. rewrite <- (Z_to_bv_bv_unsigned a1v).
  pose proof (bv_unsigned_in_range 64 a1v) as A2R. unfold bv_modulus in A2R. change (2 ^ Z.of_N 64) with (2^64) in A2R.
  eapply (g_ins RT AF PMc FDO MST (d_G D) GOK EL_INS_UL (fun v => 0 <= v < 2^64) 0x1002 0 FILLOK FILLOK FILLOK EL_INS_STACK_A _ (k + 7) Σ5 K (bv_unsigned a1v));
    [exact IUL| exact GI5| exact IOS0| intros f Hf; exact Hf| exact FA| exact A2R| exact FRM3| apply LOQ; clear; ul
    | (cbn [d_G g_rfr length]; unfold FRAMES_TOT; clear; lia)| (cbn [d_G g_cr]; unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB; clear - CRB' KB K0 CB IN I1; lia)|].
  clear m5 MI5 GI5 A2R u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F5. intros Σ6 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F6 fc6 m6 GI6 FRM6. cbn [d_G g_q g_F] in GI6 |- *.
  replace (k + 7 + 1) with (k + 8) in GI6 by (clear; lia). pose proof GI6 as (_ & MI6 & _).
  rewrite (ret_pc_even 0xb0840) by (clear; lia). apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (o_w6 D i u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 x24' (wz (T i)) u3 u4 u5 u6 F6 fc6 m6 MI6)|].
  cbv beta. intros ms7 ->. apply evt_done. unfold LSTA.
  putlit GI6 0x23700 1 2 2%nat (k + 8) Σ6 LOQ FA CRB' KB K0 CB IN I1.
  clear m6 MI6 GI6 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F6. intros Σ7 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F7 m7 GI7. cbn [d_G g_q g_F] in GI7 |- *.
  rewrite (ret_pc_even 0xb0b1c) by (clear; lia).
  eapply (dump_joinA RT AF PMc MST D DOK K i c Σ7 m7 (k + 8 + 2) sv1 sv2); [exact GI7| exact FRM6| clear - I1; lia| exact IN| exact HK| clear - K0; lia| clear - KB; lia].
Qed.

Lemma dump_closeA : forall (K : config -> Prop) (i c : Z) (Σ : rts RT) (m : mem) (k : Z) (sv1 sv2 : list byte)
    (x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x24 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
  GI (dfrL D sv1 sv2) k Σ m -> frm0 fc -> 1 <= i -> i + 1 < n ->
  (ttype (T i) = 125 \/ ttype (T i) = 93) -> KLOOP K (i + 1) c -> 0 <= k -> k + 5 <= DKH + EL_DUMP_CW * i + EL_DUMP_CSB * c -> 0 <= c <= ae_sn (d_E D) ->
  aevt RT PMc Σ K (LSTA D 0xb0748 i x1 x5 x6 x7 (wz 0) x11 x12 (wz (ttype (T i))) x14 x15 x16 x17 x24 (wz (T i)) x28 x29 x30 x31 F fc m).
Proof using AF FDO MST DOK PUT IU CRB.
  intros until fc. intros GI0 FRM I1 IN TY HK K0 KB CB. facts DOK.
  assert (Q0 : 0 <= dq D) by (clear - LQ LO1; ul). assert (QH : dq D + 256 < 2^63) by (clear - QT; ul).
  assert (FA : forall f, FILLOK f -> FILLOK (fill_after f)) by (intros f Hf; destruct (FILLOK_after f Hf) as [e|e]; rewrite e; [right; left| right; right]; reflexivity).
  assert (LOQ : forall d, d <= 12800 + RT_STACK -> lf_lo (d_X D) + d <= dq D) by (intros d Hd; clear - Hd LQ; lia).
  assert (CRB' : 62 + 24 * n + 4 * ae_sn (d_E D) <= d_cr D) by (clear - CRB; unfold EL_DUMP_C0, EL_DUMP_CW, EL_DUMP_CSB in CRB; lia).
  assert (F64x : d_f1 D mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
  pose proof (FFR _ _ ltac:(left; reflexivity)) as (A1 & A2 & A3). change (fs_size 3) with 512 in A1, A2, A3.
  pose proof GI0 as (_ & MI0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR0 & _) & _). cbn [d_G g_q] in FR0.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (c_w1 D i sv1 sv2 x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x24 x28 x29 x30 x31 F fc m Q0 QH FR0 MI0 TY)|].
  cbv beta. intros ms1 (x12' & -> & _). apply evt_done. unfold LSTA.
  assert (STEP2 : forall (Σ2 : rts RT) (m2 : mem) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 (F2 : bvmap 5 word),
    GI (dfrL D sv1 sv2) (k + 2) Σ2 m2 ->
    aevt RT PMc Σ2 K (MS (mkR (wz 0xb0b04) (wz (dq D)) (d_gp D) (wz TPV_A) u0 u1 u2 (wz (lf_S1 (d_X D))) (wz (dq D)) (wz (dF D + 272)) b1 b2 b3 b4 b5 b6 b7
                             (wz (d_f1 D)) (wz (dF D + 272)) (wz (dDOC D)) (wz n) (wz SHB) (wz (T i)) (wz 0x23620) (wz (shad (d_f1 D))) x24 (wz i) u3 u4 u5 u6)
                        F2 (ret_pc (wz 0xb0b04)) fc None m2 (seg_rom bsegs))).
  2:{ destruct TY as [E|E]; rewrite E; unfold close_lit; cbn [Z.eqb Pos.eqb].
      - putlit GI0 0x238c0 40 41 41%nat k Σ LOQ FA CRB' KB K0 CB IN I1.
        clear m MI0 GI0 FR0. intros Σ2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 m GI2. cbn [d_G g_q g_F] in GI2 |- *. exact (STEP2 Σ2 m _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 GI2).
      - putlit GI0 0x239c0 40 41 41%nat k Σ LOQ FA CRB' KB K0 CB IN I1.
        clear m MI0 GI0 FR0. intros Σ2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 m GI2. cbn [d_G g_q g_F] in GI2 |- *. exact (STEP2 Σ2 m _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 GI2). }
  intros Σ2 m2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 GI2. pose proof GI2 as (_ & MI2 & _).
  rewrite (ret_pc_even 0xb0b04) by (clear; lia). apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (c_w2 D i u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 x24 (wz (T i)) u3 u4 u5 u6 F2 fc m2 MI2)|].
  cbv beta. intros ms3 (a1w & ->). apply evt_done. unfold LSTA. rewrite <- (Z_to_bv_bv_unsigned a1w).
  pose proof (bv_unsigned_in_range 64 a1w) as A1R. unfold bv_modulus in A1R. change (2 ^ Z.of_N 64) with (2^64) in A1R.
  eapply (g_ins RT AF PMc FDO MST (d_G D) GOK EL_INS_U (fun v => 0 <= v < 2^64) 0x1002 0 FILLOK FILLOK FILLOK EL_INS_STACK_A _ (k + 2) Σ2 K (bv_unsigned a1w));
    [exact IU| exact GI2| exact IOS0| intros f Hf; exact Hf| exact FA| exact A1R| exact FRM| apply LOQ; clear; ul
    | (cbn [d_G g_rfr length]; unfold FRAMES_TOT; clear; lia)| (cbn [d_G g_cr]; unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB; clear - CRB' KB K0 CB IN I1; lia)|].
  clear m2 MI2 GI2 A1R u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2. intros Σ3 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F3 fc3 m3 GI3 FRM3. cbn [d_G g_q g_F] in GI3 |- *.
  replace (k + 2 + 1) with (k + 3) in GI3 by (clear; lia). pose proof GI3 as (_ & MI3 & _).
  rewrite (ret_pc_even 0xb0b0c) by (clear; lia). apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (c_w3 D i u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 x24 (wz (T i)) u3 u4 u5 u6 F3 fc3 m3 MI3)|].
  cbv beta. intros ms4 ->. apply evt_done. unfold LSTA.
  putlit GI3 0x23920 22 23 23%nat (k + 3) Σ3 LOQ FA CRB' KB K0 CB IN I1.
  clear m3 MI3 GI3 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F3. intros Σ4 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F4 m4 GI4. cbn [d_G g_q g_F] in GI4 |- *.
  rewrite (ret_pc_even 0xb0b1c) by (clear; lia).
  eapply (dump_joinA RT AF PMc MST D DOK K i c Σ4 m4 (k + 3 + 2) sv1 sv2); [exact GI4| exact FRM3| clear - I1; lia| exact IN| exact HK| clear - K0; lia| clear - KB; lia].
Qed.

Lemma dump_strA : forall (K : config -> Prop) (i o l : Z) (Σ : rts RT) (m : mem) (k : Z) (sv1 sv2 : list byte)
    (x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x24 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
  GI (dfrL D sv1 sv2) k Σ m -> frm0 fc -> 1 <= i -> i + 1 < n ->
  T i = tword t_str o -> str_at (ae_S (d_E D)) (ae_sn (d_E D)) o l -> KLOOP K (i + 1) (o + l + 5) -> 0 <= k -> k <= DKH + EL_DUMP_CW * (i - 1) + EL_DUMP_CSB * o + 3 ->
  aevt RT PMc Σ K (LSTA D 0xb0748 i x1 x5 x6 x7 (wz 0) x11 x12 (wz (ttype (T i))) x14 x15 x16 x17 x24 (wz (T i)) x28 x29 x30 x31 F fc m).
Proof using AF FDO MST DOK PUT ESC CRB.
  intros until fc. intros GI0 FRM I1 IN TI SA HK K0 KB. facts DOK.
  assert (Q0 : 0 <= dq D) by (clear - LQ LO1; ul). assert (QH : dq D + 256 < 2^63) by (clear - QT; ul).
  assert (FA : forall f, FILLOK f -> FILLOK (fill_after f)) by (intros f Hf; destruct (FILLOK_after f Hf) as [e|e]; rewrite e; [right; left| right; right]; reflexivity).
  assert (LOQ : forall d, d <= 12800 + RT_STACK -> lf_lo (d_X D) + d <= dq D) by (intros d Hd; clear - Hd LQ; lia).
  assert (CRB' : 62 + 24 * n + 4 * ae_sn (d_E D) <= d_cr D) by (clear - CRB; unfold EL_DUMP_C0, EL_DUMP_CW, EL_DUMP_CSB in CRB; lia).
  assert (F64x : d_f1 D mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
  pose proof (FFR _ _ ltac:(left; reflexivity)) as (A1 & A2 & A3). change (fs_size 3) with 512 in A1, A2, A3.
  assert (HSN : ae_sn (d_E D) < 2^56) by (clear - SNR; lia).
  pose proof (str_at_bounds _ _ HSN _ _ SA) as (O0 & L0 & OL & LE & O56).
  assert (TIR : 0 <= T i < 2^64) by (rewrite TI; apply tword_range; unfold t_str; clear - O56 O0; lia).
  assert (TY : ttype (T i) = 34) by (rewrite TI, ttype_tword by (clear - O56 O0; lia); reflexivity).
  assert (TV : tval (T i) = o) by (rewrite TI, tval_tword by (clear - O56 O0; lia); reflexivity).
  assert (CB : 0 <= o /\ 0 <= l /\ o + l + 5 <= ae_sn (d_E D)) by (clear - O0 L0 OL; lia).
  pose proof (Atp_defsA.ok_sbuf (d_E D) OKE) as (S16 & NS8 & SN & SS & SL).
  pose proof GI0 as (_ & MI0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR0 & _) & _). cbn [d_G g_q] in FR0.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (s_w1 D i sv1 sv2 x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x24 x28 x29 x30 x31 F fc m Q0 QH FR0 MI0 TIR TY)|].
  cbv beta. intros ms1 ->. apply evt_done. unfold LSTA. rewrite TV.
  putlit GI0 0x236c0 8 9 9%nat k Σ LOQ FA CRB' KB K0 CB IN I1.
  clear m MI0 GI0 FR0. intros Σ2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 m GI2. cbn [d_G g_q g_F] in GI2 |- *.
  rewrite (ret_pc_even 0xb09a4) by (clear; lia).

  pose proof (GINVA_wfacts RT AF (d_G D) GOK (d_E D) _ _ _ _ _ _ _ GE AI0 GI2 [] m (munch_refl [] m) (wmono_refl bsegs m) ltac:(intros a; left; exact I)) as (_ & AI2 & _ & SZS2 & _).
  pose proof GI2 as (_ & MI2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR2 & _) & _). cbn [d_G g_q] in FR2.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (s_w2 D i o l sv1 sv2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 (wz (T i)) u3 u4 u5 u6 F2 fc m Q0 QH FR2 OKE EDOC SA AI2 SZS2 MI2)|].
  cbv beta. intros ms3 (m3 & a2' & a3' & a4' & -> & MU3 & WM3 & MI3 & FR3 & SV3). apply evt_done. unfold LSTA.
  assert (GI3 : GI (dfrL D (le8 (wz (ae_SBUF (d_E D) + o + 4))) (le8 (wz l))) (k + 2) Σ2 m3).
  { eapply (GINVA_cw RT AF (d_G D) GOK _ _ _ _ _ _ Σ2 m m3 _ GI2 MU3 WM3 MI3); [(intros ?; unfold own; cbn [outside d_G g_q g_fsz g_ff g_ffk]; change (fs_size 1) with 128; change (128 / 8) with 16; clear - A1; lia)| exact FR3| rewrite !dfrL_size; reflexivity]. }
  pose proof (GINVA_wfacts RT AF (d_G D) GOK (d_E D) _ _ _ _ _ _ _ GE AI0 GI3 [] m3 (munch_refl [] m3) (wmono_refl bsegs m3) ltac:(intros a; left; exact I)) as (_ & AI3 & _).
  pose proof AI3 as (_ & SBUFB3 & _).
  destruct (sbuf_bytesA_at (d_E D) m3 o l SBUFB3 ltac:(clear - O0; lia) ltac:(clear - L0; lia) ltac:(clear - OL; lia)) as [SB3 SBL].
  pose proof GI3 as (HA3 & _ & FRS3 & LV3 & SP3 & CR3 & ST3 & (fill3 & OX3 & FOK3) & SHO3 & TPL3 & LB3 & _).
  cbn [d_G g_q g_F g_ff g_ffk g_rfr g_L g_sp0 g_cr g_lo] in HA3, FRS3, LV3, SP3, CR3, ST3, OX3, SHO3.
  clear GI2 MI2 FR2 AI2 SZS2 MU3 WM3 FR3.

  eapply (ESC Σ2 K (dF D) (dq D) (lf_lo (d_X D)) (dq D + 136) (ae_SBUF (d_E D) + o + 4) l fill3 (ae_SBUF (d_E D)) (ae_NS (d_E D)) (sbuf_bytesA (d_E D) o l)
            _ (d_gp D) u0 u1 u2 _ _ a2' a3' a4' b5 b6 b7 _ _ _ _ _ _ _ _ _ _ u3 u4 u5 u6 F2 fc m3 FDO MST);
    [rewrite FRS3; right; exact EIN| apply (proj2 (OSX_W m3 _ fill3)); exact OX3| exact FOK3| exact SHO3| exact LB3| exact TPL3
    | exact (GINVA_iossp RT AF (d_G D) GOK _ _ _ _ _ _ _ IOS0 GI3)| exact FRM| exact SV3| clear; lia| clear - QT; ul| clear - Q32; Z.div_mod_to_equations; lia
    | exact SB3| rewrite SBL; clear - L0; lia| exact L0
    | rewrite LV3; exact INS| clear - S16; Z.div_mod_to_equations; lia| exact NS8| clear - O0; lia| clear - OL SN; lia
    | exact HA3| exact MI3| exact ST3| rewrite SP3; exact LO2| exact LO1| clear - NEED; ul| clear - QT; ul| exact Q32
    | rewrite FRS3; cbn [length]; unfold FRAMES_MAX; clear; lia
    | unfold esc_costA; unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB; clear - CR3 CRB' KB K0 CB IN I1 OL; lia |].
  intros Σ4 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F4 fc4 m4 HA4 MI4 ST4 OX4 SHO4 LB4 TPL4 FRM4 LV4 FRS4 SP4 CR4 PRES4.
  assert (GI4 : GI (dfrL D (le8 (wz (ae_SBUF (d_E D) + o + 4))) (le8 (wz l))) (k + 3 + 4 * l) Σ4 m4).
  { eapply (GINVA_after RT AF (d_G D) GOK 0x1002 0 FILLOK 0x1002 0 FILLOK _ (k + 2) (k + 3 + 4 * l) Σ2 Σ4 m3 m4 (ESC_W (dF D)) GI3 HA4 MI4 ST4);
      [destruct OX4 as (f4 & O4 & F4'); exists f4; split; [apply (proj1 (OSX_W m4 _ f4)); exact O4| exact F4']| exact TPL4| exact LB4| exact LV4| exact FRS4| exact SP4
      | cbn [d_G g_cr]; unfold esc_costA in CR4; clear - CR4 CR3; lia| exact PRES4| intros a Ha; exact Ha]. }
  clear HA3 FRS3 LV3 SP3 CR3 ST3 OX3 SHO3 TPL3 LB3 SB3 AI3 SBUFB3 GI3 HA4 MI4 ST4 OX4 SHO4 LB4 TPL4 LV4 FRS4 SP4 CR4 PRES4 SV3 FOK3 m3 MI3.
  rewrite (ret_pc_even 0xb0a40) by (clear; lia).

  pose proof GI4 as (_ & MI4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR4 & _) & WF4 & WS4 & _). cbn [d_G g_ff g_FS g_ffk g_q] in WF4, WS4, FR4. change (fs_size 1) with 128 in WF4, WS4.
  replace (128 - 8) with 120 in WF4 by reflexivity. change (128 / 8) with 16 in WS4.
  destruct (wr_at_cell m4 _ 120 96 1 WF4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [jc FC4].
  destruct (wr_at_cell m4 _ 16 12 1 WS4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [js FS4].
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (s_w3 D i _ _ v0 v1 v2 _ c1 c2 c3 c4 c5 c6 c7 (wz o) (wz (T i)) v3 v4 v5 v6 jc js F4 fc4 m4 Q0 QH F0);
    [clear - FLO LQ QT; ul| clear - SHLO LQ QT; ul| exact SHAP| clear - FLO LQ; ul| clear - SHLO LQ; ul| exact FR4| exact FC4| exact FS4| exact MI4]|].
  cbv beta. intros ms5 (m5 & -> & MU5 & WM5 & MI5 & FC5 & FS5). apply evt_done. unfold LSTA.
  assert (GI5 : GI (dfrL D (le8 (wz (ae_SBUF (d_E D) + o + 4))) (le8 (wz l))) (k + 3 + 4 * l) Σ4 m5).
  { eapply (GINVA_cw RT AF (d_G D) GOK _ _ _ _ _ _ Σ4 m4 m5 _ GI4 MU5 WM5 MI5); [(intros ?; unfold own; cbn [outside d_G g_q g_fsz g_ff g_ffk]; change (fs_size 1) with 128; change (128 / 8) with 16; clear - A1; lia)| | reflexivity].
    cbn [d_G g_q]. apply (rw_cells_agree_nw bsegs m4 m5 _ _ FR4). apply (agree_of_munch _ _ _ _ MU5). intros x Hx. cbn [d_G g_q] in Hx. rewrite dfrL_size in Hx.
    cbn [outside]. repeat split; try exact I; clear - Hx FLO LQ SHLO; ul. }
  clear GI4 MI4 FR4 WF4 WS4 FC4 FS4 MU5 WM5.
  eapply (g_put_ownc RT AF PMc FDO MST (d_G D) GOK FILLOK FILLOK _ (k + 3 + 4 * l) Σ4 K 96 (Z_to_bv 8 34));
    [exact PUT| exact GI5| intros f Hf; exact Hf| exact FA| exact FC5| exact FS5| reflexivity| clear; lia| cbn [d_G g_ffk]; change (fs_size 1) with 128; clear; lia
    | apply LOQ; clear; ul| (cbn [d_G g_rfr length]; unfold FRAMES_TOT; clear; lia)| (cbn [d_G g_cr]; unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB; clear - CRB' KB K0 CB IN I1 OL L0; lia)|].
  clear m4 m5 MI5 GI5 FC5 FS5 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F4. intros Σ6 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F6 m6 GI6. cbn [d_G g_q g_F g_ff] in GI6 |- *.
  rewrite (ret_pc_even 0xb0a60) by (clear; lia).

  pose proof GI6 as (_ & MI6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR6 & _) & WF6 & WS6 & _). cbn [d_G g_ff g_FS g_ffk g_q] in WF6, WS6, FR6. change (fs_size 1) with 128 in WF6, WS6.
  replace (128 - 8) with 120 in WF6 by reflexivity. change (128 / 8) with 16 in WS6.
  destruct (wr_at_cell m6 _ 120 80 1 WF6 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [jc6 FC6].
  destruct (wr_at_cell m6 _ 16 10 1 WS6 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [js6 FS6].
  destruct (wr_at_cell m6 _ 16 12 1 WS6 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [js7 FS7].
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (s_w4 D i _ _ v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 (wz o) (wz (T i)) v3 v4 v5 v6 jc6 js6 js7 F6 fc4 m6 Q0 QH F0);
    [clear - FLO LQ QT; ul| clear - SHLO LQ QT; ul| exact SHAP| clear - FLO LQ; ul| clear - SHLO LQ; ul| exact FR6| exact FC6| exact FS6| exact FS7| exact MI6]|].
  cbv beta. intros ms7 (m7 & -> & MU7 & WM7 & MI7 & FC7 & FS8). apply evt_done. unfold LSTA.
  assert (GI7 : GI (dfrL D (le8 (wz (ae_SBUF (d_E D) + o + 4))) (le8 (wz l))) (k + 5 + 4 * l) Σ6 m7).
  { replace (k + 5 + 4 * l) with (k + 3 + 4 * l + 2) by (clear; lia).
    eapply (GINVA_cw RT AF (d_G D) GOK _ _ _ _ _ _ Σ6 m6 m7 _ GI6 MU7 WM7 MI7); [(intros ?; unfold own; cbn [outside d_G g_q g_fsz g_ff g_ffk]; change (fs_size 1) with 128; change (128 / 8) with 16; clear - A1; lia)| | reflexivity].
    cbn [d_G g_q]. apply (rw_cells_agree_nw bsegs m6 m7 _ _ FR6). apply (agree_of_munch _ _ _ _ MU7). intros x Hx. cbn [d_G g_q] in Hx. rewrite dfrL_size in Hx.
    cbn [outside]. repeat split; try exact I; clear - Hx FLO LQ SHLO; ul. }
  clear GI6 MI6 FR6 WF6 WS6 FC6 FS6 FS7 MU7 WM7.
  eapply (g_put_ownc RT AF PMc FDO MST (d_G D) GOK FILLOK FILLOK _ (k + 5 + 4 * l) Σ6 K 80 (Z_to_bv 8 10));
    [exact PUT| exact GI7| intros f Hf; exact Hf| exact FA| exact FC7| exact FS8| reflexivity| clear; lia| cbn [d_G g_ffk]; change (fs_size 1) with 128; clear; lia
    | apply LOQ; clear; ul| (cbn [d_G g_rfr length]; unfold FRAMES_TOT; clear; lia)| (cbn [d_G g_cr]; unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB; clear - CRB' KB K0 CB IN I1 OL L0; lia)|].
  clear m6 m7 MI7 GI7 FC7 FS8 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F6. intros Σ8 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F8 m8 GI8. cbn [d_G g_q g_F g_ff] in GI8 |- *.
  rewrite (ret_pc_even 0xb0a88) by (clear; lia).

  pose proof GI8 as (_ & MI8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR8 & _) & _ & WS8 & _). cbn [d_G g_ff g_FS g_ffk g_q] in WS8, FR8. change (fs_size 1) with 128 in WS8. change (128 / 8) with 16 in WS8.
  destruct (wr_at_cell m8 _ 16 10 1 WS8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [js8 FS9].
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (s_w5 D i v0 v1 v2 _ c1 c2 c3 c4 c5 c6 c7 (wz o) (wz (T i)) v3 v4 v5 v6 js8 F8 fc4 m8 F0); [clear - SHLO LQ QT; ul| exact FS9| exact MI8]|].
  cbv beta. intros ms9 (m9 & -> & MU9 & WM9 & MI9). apply evt_done.
  assert (GI9 : GI (dfrL D (le8 (wz (ae_SBUF (d_E D) + o + 4))) (le8 (wz l))) (k + 7 + 4 * l) Σ8 m9).
  { replace (k + 7 + 4 * l) with (k + 5 + 4 * l + 2) by (clear; lia).
    eapply (GINVA_cw RT AF (d_G D) GOK _ _ _ _ _ _ Σ8 m8 m9 _ GI8 MU9 WM9 MI9); [(intros ?; unfold own; cbn [outside d_G g_q g_fsz g_ff g_ffk]; change (fs_size 1) with 128; change (128 / 8) with 16; clear - A1; lia)| | reflexivity].
    cbn [d_G g_q]. apply (rw_cells_agree_nw bsegs m8 m9 _ _ FR8). apply (agree_of_munch _ _ _ _ MU9). intros x Hx. cbn [d_G g_q] in Hx. rewrite dfrL_size in Hx.
    cbn [outside]. repeat split; try exact I; clear - Hx FLO LQ SHLO; ul. }
  eapply (dump_joinA RT AF PMc MST D DOK K i (o + l + 5) Σ8 m9 (k + 7 + 4 * l)); [exact GI9| exact FRM4| clear - I1; lia| exact IN| exact HK| clear - K0 L0; lia| unfold DKH, EL_DUMP_CW, EL_DUMP_CSB in KB |- *; clear - KB L0 O0 I1; lia].
Qed.
End Body2.
