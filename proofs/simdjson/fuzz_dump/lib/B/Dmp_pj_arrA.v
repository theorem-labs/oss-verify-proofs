(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA Atp_defsA Atp_objwA Atp_objnA Pj_defsA El_defsA Dmp_hdefsA Dmp_pj_ifaceA Dmp_pj_kitA Dmp_pj_leafA Pj_ser_trefA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition DMP_LIT_COMMA_A : Z := 0x23540.
Definition DMP_PJ_ATEST_A : Z := 0xaf538.
Definition DMP_PJ_ASTEP_A : Z := 0xaf4c0.

Definition pjRL (E : aenvA) (q f osp e : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s5 t0 t1 t2 t3 t4 t5 t6 : word) : bvmap 5 word :=
  mkR ra (Z_to_bv 64 (q - 256)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 256)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 SHB) (Z_to_bv 64 0x100000001) (Z_to_bv 64 e) (Z_to_bv 64 (ae_DOC E)) s5 (Z_to_bv 64 DMP_LIT_COMMA_A) (Z_to_bv 64 32)
      (Z_to_bv 64 osp) (Z_to_bv 64 0x4020200) (Z_to_bv 64 (shad f)) t3 t4 t5 t6.

Lemma low32_cwordA : forall t nxt cv, 0 <= t < 256 -> 0 <= nxt < 2^32 -> 0 <= cv <= CNT_MAX ->
  Z.land (Z.land (cword t nxt cv) 18446744073709551615) 4294967295 = nxt.
Proof.
  intros t nxt cv Ht Hn Hc. assert (R : 0 <= cword t nxt cv < 2^64) by (unfold cword, tword, CNT_MAX in *; lia).
  change 18446744073709551615 with (Z.ones 64). change 4294967295 with (Z.ones 32).
  rewrite !Z.land_ones by lia. rewrite (Z.mod_small _ (2^64)) by lia.
  pose proof (tnext_cword t nxt cv Hn) as E. unfold tnext in E. exact E.
Qed.
Lemma low32_cwordA' : forall t nxt cv, 0 <= t < 256 -> 0 <= nxt < 2^32 -> 0 <= cv <= CNT_MAX ->
  Z.land (cword t nxt cv) 4294967295 = nxt.
Proof.
  intros t nxt cv Ht Hn Hc. pose proof (low32_cwordA t nxt cv Ht Hn Hc) as E.
  change 18446744073709551615 with (Z.ones 64) in E. rewrite Z.land_ones in E by (unfold cword, tword, CNT_MAX in *; lia).
  rewrite Z.mod_small in E by (unfold cword, tword, CNT_MAX in *; lia). exact E.
Qed.

Definition pj_kindA (T S : Z -> Z) (sn it j : Z) : Prop :=
  (j = it + 1 /\ (T it = tword t_true 0 \/ T it = tword t_false 0 \/ T it = tword t_null 0))
  \/ (j = it + 2 /\ (T it = tword t_i64 0 \/ T it = tword t_u64 0 \/ T it = tword t_dbl 0))
  \/ (j = it + 1 /\ is_str T S sn it)
  \/ (exists cv, 0 <= cv <= CNT_MAX /\ (T it = cword t_arr j cv \/ T it = cword t_obj j cv)).

Lemma pj_le8_nth7 : forall v, (0 <= v < 2^64)%Z -> nth 7 (le8 (Z_to_bv 64 v)) (Z_to_bv 8 0) = Z_to_bv 8 (ttype v).
Proof.
  intros v Hv. unfold le8, word_to_le_bytes. rewrite a_u64_small by lia.
  cbn [Z_to_le_bytes nth]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ]. rewrite a_shr56. reflexivity.
Qed.
Lemma pj_u64s_read7 : forall (ws : list word) (i : nat), (i < length ws)%nat ->
  firstn 1 (skipn (8 * i + 7) (u64s ws)) = [nth 7 (le8 (nth i ws (Z_to_bv 64 0))) (Z_to_bv 8 0)].
Proof.
  induction ws as [|w ws IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i].
  - cbn [Nat.mul Nat.add u64s nth]. rewrite skipn_app, length_le8. replace (7 - 8)%nat with 0%nat by lia. cbn [skipn].
    pose proof (length_le8 w) as L. remember (le8 w) as l eqn:El. clear El.
    destruct l as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 r]]]]]]]]]; cbn [length] in L; try lia. reflexivity.
  - replace (8 * S i + 7)%nat with (8 + (8 * i + 7))%nat by lia. cbn [u64s nth]. rewrite skipn_app, length_le8.
    replace (8 + (8 * i + 7) - 8)%nat with (8 * i + 7)%nat by lia. rewrite skipn_all2 by (rewrite length_le8; lia). cbn [app].
    apply IH. lia.
Qed.

Lemma tape_read_typeA : forall m TAPE (tws : list Z) (i : Z),
  bytes_at bsegs m TAPE (u64s (map (Z_to_bv 64) tws)) -> 0 <= i < Z.of_nat (length tws) -> 0 <= Tf tws i < 2^64 ->
  ov_read_bytes bsegs m (wa (TAPE + 8 * i + 7)) 1 = Some [Z_to_bv 8 (ttype (Tf tws i))].
Proof.
  intros m TAPE tws i HB Hi HT.
  replace (TAPE + 8 * i + 7) with (TAPE + (8 * i + 7)) by lia.
  rewrite (bytes_at_read bsegs m TAPE _ (8 * i + 7) 1 HB); [| lia| rewrite u64s_length, length_map; lia].
  f_equal. replace (Z.to_nat (8 * i + 7)) with (8 * Z.to_nat i + 7)%nat by lia.
  rewrite pj_u64s_read7 by (rewrite length_map; lia).
  rewrite <- pj_le8_nth7 by exact HT. do 3 f_equal.
  unfold Tf. rewrite (map_nth (Z_to_bv 64)). reflexivity.
Qed.

Lemma tape_read4A : forall m TAPE (tws : list Z) (i : Z),
  bytes_at bsegs m TAPE (u64s (map (Z_to_bv 64) tws)) -> 0 <= i < Z.of_nat (length tws) ->
  ov_read_bytes bsegs m (wa (TAPE + 8 * i)) 4 = Some (le4 (Z_to_bv 64 (Tf tws i))).
Proof.
  intros m TAPE tws i HB Hi.
  assert (Hn : nth_error (map (Z_to_bv 64) tws) (Z.to_nat i) = Some (Z_to_bv 64 (Tf tws i))).
  { unfold Tf. rewrite nth_error_map. rewrite (nth_error_nth' tws 0) by lia. reflexivity. }
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i) with (Z.of_nat (8 * Z.to_nat i)) by lia.
  rewrite (bytes_at_ov_read bsegs m TAPE _ (8 * Z.to_nat i) 4 HB).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app. rewrite length_le8. change (4 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r.
  reflexivity.
Qed.

Lemma zx32_cwordA : forall t nxt cv, 0 <= t < 256 -> 0 <= nxt < 2^32 -> 0 <= cv <= CNT_MAX ->
  bv_unsigned (zx32 (Z_to_bv 64 (cword t nxt cv))) = nxt.
Proof.
  intros t nxt cv Ht Hn Hc. assert (R : 0 <= cword t nxt cv < 2^64) by (unfold cword, tword, CNT_MAX in *; lia).
  unfold zx32. rewrite (unsigned_lit (cword t nxt cv)) by lia.
  rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (cword t nxt cv) (2^32) ltac:(lia)); lia).
  rewrite <- Z.land_ones by lia. exact (low32_cwordA' t nxt cv Ht Hn Hc).
Qed.

Lemma mask_allA : forall x, 0 <= x < 2^64 -> Z.land (Z.land (Z.b2z (0 <? 0) + -1) 18446744073709551615) x = x.
Proof. intros x Hx. change (Z.land (Z.b2z (0 <? 0) + -1) 18446744073709551615) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma pj_astep3 : forall (E : aenvA) (q f osp e it i : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> 0 <= it -> it < ae_n E -> ae_n E < 2^32 -> 0x6d5000 <= q - 256 -> q < 2^63 ->
  rw_cells bsegs m (q - 256 + 136) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] -> mem_inv bsegs m ->
  evt bsegs (fun ms =>
      ms = MS (pjRL E q f osp e gp (Z_to_bv 64 0xaf4cc) (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 it) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 it) t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 PJ_TREF_A) fc None m (seg_rom bsegs))
    (MS (pjRL E q f osp e gp ra a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 it) t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 DMP_PJ_ASTEP_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros OK I0 IN N32 QLO QH FD MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
  unfold pjRL, DMP_PJ_ASTEP_A, SHB, shad in *.
  assert (EQ : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ae_DOC E)) = ae_DOC E) by (apply unsigned_lit; lia).
  pj_run PJ_TREF_A. apply evt_done. reflexivity.
Qed.

Lemma pj_astep4 : forall (E : aenvA) (q f osp e it j : Z) (gp ra a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> 0 <= it -> it < j -> j <= ae_n E -> ae_n E < 2^32 -> pj_kindA (ae_T E) (ae_S E) (ae_sn E) it j ->
  0x6d5000 <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 -> 0 <= e < 2^64 -> 0 < f -> shad f + 32 < 2^63 ->
  AINV_A E m -> shz m (ae_TAPE E) (8 * ae_n E) -> shz m (ae_DOC E) 16 -> mem_inv bsegs m ->
  evt bsegs (fun ms =>
      (exists (a0x a1x a2x a3x : word),
         ms = MS (pjRL E q f osp e gp ra a0x a1x a2x a3x a4 a5 a6 a7 (Z_to_bv 64 j) t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 DMP_PJ_ATEST_A) fc None m (seg_rom bsegs))
      \/ ((exists cv, 0 <= cv <= CNT_MAX /\ (ae_T E it = cword t_arr j cv \/ ae_T E it = cword t_obj j cv))
          /\ ms = MS (pjRL E q f osp e gp (Z_to_bv 64 0xaf514) (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 it) (Z_to_bv 64 (ae_TAPE E)) (Z_to_bv 64 (2^60))
                         a4 a5 a6 a7 (Z_to_bv 64 it) t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 PJ_TREF_A) fc None m (seg_rom bsegs)))
    (MS (pjRL E q f osp e gp ra (Z_to_bv 64 (ae_TAPE E + 8 * it)) (Z_to_bv 64 0) (Z_to_bv 64 (ae_TAPE E)) (Z_to_bv 64 (2^60)) a4 a5 a6 a7 (Z_to_bv 64 it)
             t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 0xaf4cc) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros OK I0 IJ JN N32 KIND QLO QH OR ER F0 SFH AI SHZT SHZD MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *. assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
  assert (FS0 : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  pose proof AI as (TAPEB & _ & _ & DOCC & DSH).
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) it TAPEB ltac:(lia)) as RDT.
  pose proof (tape_read4A m (ae_TAPE E) (ae_tws E) it TAPEB ltac:(lia)) as RD4.
  unfold pjRL, DMP_PJ_ATEST_A, SHB, shad in *.
  assert (EQ : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ae_DOC E)) = ae_DOC E) by (apply unsigned_lit; lia).
  assert (ET : bv_unsigned (Z_to_bv 64 (ae_TAPE E + 8 * it)) = ae_TAPE E + 8 * it) by (apply unsigned_lit; lia).
  shz_pose SHZT (ae_TAPE E + 8 * it). shz_pose SHZD (ae_DOC E).
  destruct KIND as [[-> TY]|[[-> TY]|[[-> STRI]|(cv & CV & CO)]]].
  - destruct TY as [E'|[E'|E']];
      (assert (TIR : 0 <= ae_T E it < 2^64) by (rewrite E'; unfold tword, t_true, t_false, t_null; lia));
      pose proof (tape_read_typeA m (ae_TAPE E) (ae_tws E) it TAPEB ltac:(lia) TIR) as RTY;
      rewrite E' in RTY, RDT, RD4; rewrite ttype_tword in RTY by lia; unfold t_true, t_false, t_null in RTY;
      pj_run DMP_PJ_ATEST_A; apply evt_done; left; do 4 eexists; reflexivity.
  - destruct TY as [E'|[E'|E']];
      (assert (TIR : 0 <= ae_T E it < 2^64) by (rewrite E'; unfold tword, t_i64, t_u64, t_dbl; lia));
      pose proof (tape_read_typeA m (ae_TAPE E) (ae_tws E) it TAPEB ltac:(lia) TIR) as RTY;
      rewrite E' in RTY, RDT, RD4; rewrite ttype_tword in RTY by lia; unfold t_i64, t_u64, t_dbl in RTY;
      pj_run DMP_PJ_ATEST_A; apply evt_done; left; do 4 eexists; reflexivity.
  - pose proof (key_word_rangeA _ _ _ _ STRI HSN) as (TIR & _ & KT).
    pose proof (tape_read_typeA m (ae_TAPE E) (ae_tws E) it TAPEB ltac:(lia) TIR) as RTY.
    rewrite KT in RTY. unfold t_str in RTY.
    pj_run DMP_PJ_ATEST_A. apply evt_done. left. do 4 eexists. reflexivity.
  - unfold CNT_MAX in CV.
    destruct CO as [E'|E'];
      (assert (TIR : 0 <= ae_T E it < 2^64) by (rewrite E'; unfold cword, tword, t_arr, t_obj; lia));
      pose proof (tape_read_typeA m (ae_TAPE E) (ae_tws E) it TAPEB ltac:(lia) TIR) as RTY;
      rewrite E' in RTY; rewrite ttype_cword in RTY by (unfold CNT_MAX; lia); unfold t_arr, t_obj in RTY;
      pj_run PJ_TREF_A; apply evt_done; right; (split; [exists cv; split; [unfold CNT_MAX; lia| first [left; exact E' | right; exact E']]| reflexivity]).
Qed.

Lemma pj_astep5 : forall (E : aenvA) (q f osp e it j cv : Z) (gp ra a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> 0 <= it -> it < j -> j <= ae_n E -> ae_n E < 2^32 -> 0 <= cv <= CNT_MAX ->
  (ae_T E it = cword t_arr j cv \/ ae_T E it = cword t_obj j cv) ->
  0x6d5000 <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 -> 0 <= e < 2^64 -> 0 < f -> shad f + 32 < 2^63 ->
  AINV_A E m -> shz m (ae_TAPE E) (8 * ae_n E) -> shz m (ae_DOC E) 16 ->
  rw_cells bsegs m (q - 256 + 72) [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (a0x a1x a2x a3x : word),
         ms = MS (pjRL E q f osp e gp ra a0x a1x a2x a3x a4 a5 a6 a7 (Z_to_bv 64 j) t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 DMP_PJ_ATEST_A) fc None m (seg_rom bsegs))
    (MS (pjRL E q f osp e gp ra (Z_to_bv 64 (ae_TAPE E + 8 * it)) (Z_to_bv 64 0) (Z_to_bv 64 (ae_TAPE E)) (Z_to_bv 64 (2^60)) a4 a5 a6 a7 (Z_to_bv 64 it)
             t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 0xaf514) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros OK I0 IJ JN N32 CV CO QLO QH OR ER F0 SFH AI SHZT SHZD F72 MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *. assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
  assert (FS0 : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  pose proof AI as (TAPEB & _ & _ & DOCC & DSH).
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) it TAPEB ltac:(lia)) as RDT.
  pose proof (tape_read4A m (ae_TAPE E) (ae_tws E) it TAPEB ltac:(lia)) as RD4.
  unfold pjRL, DMP_PJ_ATEST_A, SHB, shad in *.
  assert (EQ : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ae_DOC E)) = ae_DOC E) by (apply unsigned_lit; lia).
  assert (ET : bv_unsigned (Z_to_bv 64 (ae_TAPE E + 8 * it)) = ae_TAPE E + 8 * it) by (apply unsigned_lit; lia).
  shz_pose SHZT (ae_TAPE E + 8 * it). shz_pose SHZD (ae_DOC E).
  unfold CNT_MAX in CV.
  destruct CO as [E'|E'];
    (assert (TIR : 0 <= ae_T E it < 2^64) by (rewrite E'; unfold cword, tword, t_arr, t_obj; lia));
    pose proof (tape_read_typeA m (ae_TAPE E) (ae_tws E) it TAPEB ltac:(lia) TIR) as RTY;
    rewrite E' in RTY, RDT, RD4; rewrite ttype_cword in RTY by (unfold CNT_MAX; lia); unfold t_arr, t_obj in RTY;
    pj_run DMP_PJ_ATEST_A; rewrite low32_cwordA' by (unfold t_arr, t_obj, CNT_MAX; lia);
    apply evt_done; do 4 eexists; reflexivity.
Qed.

Definition DMP_LIT_RBRK_A : Z := 0x23560.
Definition DMP_PJ_AHEAD_A : Z := 0xaf13c.
Definition DMP_PJ_AH1RET_A : Z := 0xaf154.
Definition DMP_PJ_AH2RET_A : Z := 0xaf36c.
Definition DMP_PJ_AH3RET_A : Z := 0xaf43c.

Lemma pj_ahead1 : forall (E : aenvA) (q f osp i e cv : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> 0 <= i -> i < e -> e + 1 <= ae_n E -> ae_n E < 2^32 -> 0 <= cv <= CNT_MAX -> ae_T E i = cword t_arr (e + 1) cv ->
  0x6d5000 <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 -> 0 < f -> f + 256 < 2^63 -> shad f + 32 < 2^63 ->
  AINV_A E m -> shz m (ae_TAPE E) (8 * ae_n E) -> shz m (ae_DOC E) 16 ->
  rw_cells bsegs m (q - 256 + 136) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => ms = MS (pjR q f gp (Z_to_bv 64 DMP_PJ_AH1RET_A) (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7
                                    (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
                               F (Z_to_bv 64 PJ_TREF_A) fc None m (seg_rom bsegs))
    (MS (pjR q f gp ra a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_AHEAD_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros OK I0 IE EN N32 CV TW QLO QH OR F0 FH SFH AI SHZT SHZD FD MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
  unfold pjR, DMP_PJ_AHEAD_A, DMP_PJ_AH1RET_A, SHB, shad in *.
  assert (EQ : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ae_DOC E)) = ae_DOC E) by (apply unsigned_lit; lia).
  pj_run PJ_TREF_A.
  apply evt_done. reflexivity.
Qed.

Lemma pj_ahead2 : forall (E : aenvA) (q f osp i e cv : Z) (gp ra a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> 0 <= i -> i < e -> e + 1 <= ae_n E -> ae_n E < 2^32 -> 0 <= cv <= CNT_MAX -> ae_T E i = cword t_arr (e + 1) cv ->
  0x6d5000 <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 -> 0 < f -> f + 256 < 2^63 -> shad f + 32 < 2^63 ->
  AINV_A E m -> shz m (ae_TAPE E) (8 * ae_n E) -> shz m (ae_DOC E) 16 ->
  rw_cells bsegs m (q - 256 + 136) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => ms = MS (pjR q f gp (Z_to_bv 64 DMP_PJ_AH2RET_A) (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) (Z_to_bv 64 (ae_TAPE E)) (Z_to_bv 64 (2^60))
                                    a4 a5 a6 a7 (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
                               F (Z_to_bv 64 PJ_TREF_A) fc None m (seg_rom bsegs))
    (MS (pjR q f gp ra (Z_to_bv 64 (ae_TAPE E + 8 * i)) (Z_to_bv 64 0) (Z_to_bv 64 (ae_TAPE E)) (Z_to_bv 64 (2^60)) a4 a5 a6 a7
             (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_AH1RET_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros OK I0 IE EN N32 CV TW QLO QH OR F0 FH SFH AI SHZT SHZD FD MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
  assert (FS0 : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  unfold CNT_MAX in CV.
  pose proof AI as (TAPEB & _ & _ & DOCC & DSH).
  assert (TIR : 0 <= ae_T E i < 2^64) by (rewrite TW; unfold cword, tword, t_arr; lia).
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RDT.
  pose proof (tape_read_typeA m (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia) TIR) as RTY.
  rewrite TW in RTY. rewrite ttype_cword in RTY by (unfold CNT_MAX; lia). unfold t_arr in RTY.
  unfold pjR, DMP_PJ_AH1RET_A, DMP_PJ_AH2RET_A, SHB, shad in *.
  assert (EQ : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ae_DOC E)) = ae_DOC E) by (apply unsigned_lit; lia).
  assert (ET : bv_unsigned (Z_to_bv 64 (ae_TAPE E + 8 * i)) = ae_TAPE E + 8 * i) by (apply unsigned_lit; lia).
  shz_pose SHZT (ae_TAPE E + 8 * i). shz_pose SHZD (ae_DOC E).
  pj_run PJ_TREF_A.
  apply evt_done. reflexivity.
Qed.

Lemma pj_ahead3 : forall (E : aenvA) (q f osp i e cv : Z) (gp ra a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> 0 <= i -> i < e -> e + 1 <= ae_n E -> ae_n E < 2^32 -> 0 <= cv <= CNT_MAX -> ae_T E i = cword t_arr (e + 1) cv ->
  0x6d5000 <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 -> 0 < f -> f + 256 < 2^63 -> shad f + 32 < 2^63 ->
  AINV_A E m -> shz m (ae_TAPE E) (8 * ae_n E) -> shz m (ae_DOC E) 16 ->
  rw_cells bsegs m (q - 256 + 136) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => ms = MS (pjR q f gp (Z_to_bv 64 DMP_PJ_AH3RET_A) (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) (Z_to_bv 64 32) (Z_to_bv 64 (2^60))
                                    a4 a5 a6 a7 (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) (Z_to_bv 64 (i + 1)) s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
                               F (Z_to_bv 64 PJ_TREF_A) fc None m (seg_rom bsegs))
    (MS (pjR q f gp ra (Z_to_bv 64 (ae_TAPE E + 8 * i)) (Z_to_bv 64 0) (Z_to_bv 64 (ae_TAPE E)) (Z_to_bv 64 (2^60)) a4 a5 a6 a7
             (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_AH2RET_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros OK I0 IE EN N32 CV TW QLO QH OR F0 FH SFH AI SHZT SHZD FD MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
  assert (FS0 : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  unfold CNT_MAX in CV.
  pose proof AI as (TAPEB & _ & _ & DOCC & DSH).
  assert (TIR : 0 <= ae_T E i < 2^64) by (rewrite TW; unfold cword, tword, t_arr; lia).
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RDT.
  pose proof (tape_read_typeA m (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia) TIR) as RTY.
  rewrite TW in RTY. rewrite ttype_cword in RTY by (unfold CNT_MAX; lia). unfold t_arr in RTY.
  unfold pjR, DMP_PJ_AH2RET_A, DMP_PJ_AH3RET_A, SHB, shad in *.
  assert (EQ : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ae_DOC E)) = ae_DOC E) by (apply unsigned_lit; lia).
  assert (ET : bv_unsigned (Z_to_bv 64 (ae_TAPE E + 8 * i)) = ae_TAPE E + 8 * i) by (apply unsigned_lit; lia).
  shz_pose SHZT (ae_TAPE E + 8 * i). shz_pose SHZD (ae_DOC E).
  pj_run PJ_TREF_A.
  apply evt_done. reflexivity.
Qed.

Lemma pj_ahead4 : forall (E : aenvA) (q f osp i e cv : Z) (gp ra a4 a5 a6 a7 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (j0 j8 j16 j72 : list byte) F fc (m : mem),
  aenvA_ok E -> 0 <= i -> i < e -> e + 1 <= ae_n E -> ae_n E < 2^32 -> 0 <= cv <= CNT_MAX -> ae_T E i = cword t_arr (e + 1) cv ->
  0x6d5000 <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 -> 0 < f -> f + 256 < 2^63 -> shad f + 32 < 2^63 ->
  AINV_A E m -> shz m (ae_TAPE E) (8 * ae_n E) -> shz m (ae_DOC E) 16 ->
  rw_cells bsegs m (q - 256 + 136) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] ->
  rw_cells bsegs m (q - 256) [CB 8 j0; CB 8 j8; CB 8 j16] ->
  rw_cells bsegs m (q - 256 + 72) [CB 8 j72; C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms =>
      (i + 1 = e /\ exists (a0x a2x a3x : word),
         ms = MS (pjR q f gp ra a0x (Z_to_bv 64 DMP_LIT_RBRK_A) a2x a3x a4 a5 a6 a7 (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 e) (Z_to_bv 64 (i + 1))
                      s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 DMP_PJ_CLOSE_A) fc None m (seg_rom bsegs))
      \/ (i + 1 <> e /\ exists (m' : mem) (a0x a1x a2x a3x : word),
         ms = MS (pjRL E q f osp e gp ra a0x a1x a2x a3x a4 a5 a6 a7 (Z_to_bv 64 (i + 1)) t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 DMP_PJ_ALOOP_A) fc None m' (seg_rom bsegs)
         /\ munch [(q - 256, q - 232); (q - 184, q - 176)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
         /\ rw_cells bsegs m' (q - 256) [C8 (Z_to_bv 64 DMP_LIT_RBRK_A); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f)]
         /\ rw_cells bsegs m' (q - 256 + 72) [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp)]))
    (MS (pjR q f gp ra (Z_to_bv 64 (ae_TAPE E + 8 * i)) (Z_to_bv 64 0) (Z_to_bv 64 (ae_TAPE E)) (Z_to_bv 64 (2^60)) a4 a5 a6 a7
             (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) (Z_to_bv 64 (i + 1)) s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_AH3RET_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros OK I0 IE EN N32 CV TW QLO QH OR F0 FH SFH AI SHZT SHZD FD F0C F72 MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
  assert (FS0 : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  pose proof AI as (TAPEB & _ & _ & DOCC & DSH).
  assert (TIR : 0 <= ae_T E i < 2^64) by (rewrite TW; unfold cword, tword, t_arr, CNT_MAX in *; lia).
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RDT.
  pose proof (tape_read4A m (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RD4.
  pose proof (tape_read_typeA m (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia) TIR) as RTY.
  rewrite TW in RTY. rewrite ttype_cword in RTY by (unfold CNT_MAX in *; lia). unfold t_arr in RTY.
  rewrite TW in RD4.
  unfold pjR, pjRL, DMP_PJ_AH3RET_A, DMP_PJ_CLOSE_A, DMP_PJ_ALOOP_A, DMP_LIT_RBRK_A, DMP_LIT_COMMA_A, SHB, shad in *.
  lazymatch goal with |- evt _ (fun _ => _ \/ (_ /\ (exists _ _ _ _ _, _ /\ (munch ?W _ _ /\ _)))) _ => pose proof (munch_refl W m) as MU end.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EQ : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ae_DOC E)) = ae_DOC E) by (apply unsigned_lit; lia).
  assert (ET : bv_unsigned (Z_to_bv 64 (ae_TAPE E + 8 * i)) = ae_TAPE E + 8 * i) by (apply unsigned_lit; lia).
  shz_pose SHZT (ae_TAPE E + 8 * i). shz_pose SHZD (ae_DOC E).
  pj_run DMP_PJ_CLOSE_A.
  rewrite (zx32_cwordA t_arr (e + 1) cv) by (unfold t_arr, CNT_MAX in *; lia).
  if_cases KE; zify_cond KE; rewrite ?unsigned_lit in KE by lia.
  - apply evt_done. left. split; [lia|]. replace (e + 1 + -1) with e by lia. do 3 eexists. reflexivity.
  - pj_run DMP_PJ_ALOOP_A.
    apply evt_done. right. split; [lia|]. do 5 eexists. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
    split; eassumption.
Qed.

Lemma pj_aloop1 : forall (E : aenvA) (q f osp e it : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  mem_inv bsegs m ->
  evt bsegs (fun ms =>
      ms = MS (pjRL E q f osp e gp (Z_to_bv 64 0xaf4b0) (Z_to_bv 64 osp) (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 it) a3 a4 a5 a6 a7 (Z_to_bv 64 it) t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_PJ_A) fc None m (seg_rom bsegs))
    (MS (pjRL E q f osp e gp ra a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 it) t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 DMP_PJ_ALOOP_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros MI. unfold pjRL, DMP_PJ_ALOOP_A, DMP_PJ_A.
  pj_run DMP_PJ_A. apply evt_done. reflexivity.
Qed.

Lemma pj_aloop2 : forall (E : aenvA) (q f osp e it : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  mem_inv bsegs m ->
  evt bsegs (fun ms =>
      ms = MS (pjRL E q f osp e gp (Z_to_bv 64 DMP_PJ_ASTEP_A) (Z_to_bv 64 osp) (Z_to_bv 64 DMP_LIT_COMMA_A) (Z_to_bv 64 1) a3 a4 a5 a6 a7 (Z_to_bv 64 it) t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_PJ_PUT_A) fc None m (seg_rom bsegs))
    (MS (pjRL E q f osp e gp ra a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 it) t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 0xaf4b0) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros MI. unfold pjRL, DMP_PJ_ASTEP_A, DMP_PJ_PUT_A, DMP_LIT_COMMA_A.
  pj_run DMP_PJ_PUT_A. apply evt_done. reflexivity.
Qed.

Lemma pj_atest : forall (E : aenvA) (q f osp e j : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= j < 2^63 -> 0 <= e < 2^63 -> mem_inv bsegs m ->
  evt bsegs (fun ms =>
      ms = MS (pjRL E q f osp e gp ra a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 j) t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 (if j =? e then DMP_PJ_LOOPX_A else DMP_PJ_ALOOP_A)) fc None m (seg_rom bsegs))
    (MS (pjRL E q f osp e gp ra a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 j) t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 DMP_PJ_ATEST_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros JR ER MI. unfold pjRL, DMP_PJ_ATEST_A, DMP_PJ_LOOPX_A, DMP_PJ_ALOOP_A.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  step. if_cases KJ; zify_cond KJ; rewrite ?unsigned_lit in KJ by lia.
  - replace (j =? e) with false by (symmetry; apply Z.eqb_neq; lia). apply evt_done. atp_st_eq_goal.
  - replace (j =? e) with true by (symmetry; apply Z.eqb_eq; lia). apply evt_done. atp_st_eq_goal.
Qed.
