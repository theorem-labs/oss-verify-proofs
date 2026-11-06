(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, addresses and numbers changed; 158 of its 230 lines of code are new or changed and 674 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_no_overread_blocks.v, with its module paths, module names and addresses changed; 271 of its 312 lines of code are new or changed and 189 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.


Lemma cn_sx32 : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma cn_signed : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit_wrap.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 63) with 9223372036854775808 in *.
  destruct (Z.ltb_spec (z mod 18446744073709551616) 9223372036854775808); cbv iota;
    Z.div_mod_to_equations; lia.
Qed.

Lemma cn_swrap : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648.
  change (bv_modulus 32) with 4294967296. change (2 ^ 31) with 2147483648 in Hz. Z.div_mod_to_equations. lia.
Qed.

Lemma cn_zxb : forall g, 0 <= g < 256 -> zxb (Z_to_bv 8 g) = Z_to_bv 64 g.
Proof.
  intros g Hg. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 8) with 256. lia.
Qed.

Lemma cn_eqb : forall a b : word, bv_eqb a b = true -> a = b.
Proof. intros a b H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Lemma cn_wr_at_app : forall segs m A n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at segs m A (n1 + n2) <-> wr_at segs m A n1 /\ wr_at segs m (A + n1) n2.
Proof.
  intros segs m A n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hn & H). split; (split; [lia| split; [lia|]]).
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (A + n1 + i) with (A + (n1 + i)) by lia. apply H. lia.
  - intros [(Ha & Hn & Ha') (Hb & Hm & Hb')]. split; [lia| split; [lia|]].
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply Ha'. lia.
    + replace (A + i) with (A + n1 + (i - n1)) by lia. apply Hb'. lia.
Qed.

Lemma cn_cells_app_l : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) ->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2 [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1.
  rewrite cells_size_app, Nat2Z.inj_add in Hw. apply cn_wr_at_app in Hw; [|lia|lia]. destruct Hw as [H1 H2].
  exact (conj (conj (conj W1 B1) H1) (conj (conj W2 B2) H2)).
Qed.

Lemma cn_cb_split : forall segs m A (n1 n2 : nat) bs,
  rw_cells segs m A [CB (n1 + n2) bs] -> rw_cells segs m A [CB n1 (firstn n1 bs); CB n2 (skipn n1 bs)].
Proof.
  intros segs m A n1 n2 bs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  split; [split|].
  - cbn [cells_wf cell_wf]. rewrite length_firstn, length_skipn. repeat split; lia.
  - cbn [cells_bytes cbytes] in *. rewrite app_nil_r in Hb. rewrite app_nil_r, firstn_skipn. exact Hb.
  - cbn [cells_size csize] in *. replace (Z.of_nat (n1 + (n2 + 0))) with (Z.of_nat (n1 + n2 + 0)) by lia. exact Hw.
Qed.

Lemma cn_frame_split : forall m B (jk : list byte) (w5 w4 w3 w2 w1 w0 wr : word),
  rw_cells rsegs m B [CB 24 jk; C8 w5; C8 w4; C8 w3; C8 w2; C8 w1; C8 w0; C8 wr] ->
  exists j0 j1 j2, rw_cells rsegs m B [CB 8 j0] /\ rw_cells rsegs m (B + 8) [CB 8 j1] /\
    rw_cells rsegs m (B + 16) [CB 8 j2] /\
    rw_cells rsegs m (B + 24) [C8 w5; C8 w4; C8 w3; C8 w2; C8 w1; C8 w0; C8 wr].
Proof.
  intros m B jk w5 w4 w3 w2 w1 w0 wr H.
  destruct (cn_cells_app_l rsegs m B [CB 24 jk] [C8 w5; C8 w4; C8 w3; C8 w2; C8 w1; C8 w0; C8 wr] H) as [H1 H2].
  pose proof (cn_cb_split rsegs m B 8 16 jk H1) as H3.
  destruct (cn_cells_app_l rsegs m B [CB 8 (firstn 8 jk)] [CB 16 (skipn 8 jk)] H3) as [H4 H5].
  change (Z.of_nat (cells_size [CB 8 (firstn 8 jk)])) with 8 in H5.
  pose proof (cn_cb_split rsegs m (B + 8) 8 8 (skipn 8 jk) H5) as H6.
  destruct (cn_cells_app_l rsegs m (B + 8) [CB 8 (firstn 8 (skipn 8 jk))] [CB 8 (skipn 8 (skipn 8 jk))] H6)
    as [H7 H8].
  change (Z.of_nat (cells_size [CB 8 (firstn 8 (skipn 8 jk))])) with 8 in H8.
  change (Z.of_nat (cells_size [CB 24 jk])) with 24 in H2.
  replace (B + 8 + 8) with (B + 16) in H8 by lia.
  exists (firstn 8 jk), (firstn 8 (skipn 8 jk)), (skipn 8 (skipn 8 jk)).
  split; [exact H4|]. split; [exact H7|]. split; [exact H8|]. exact H2.
Qed.

Lemma cn_gm_gone : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 0x147b0) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1480c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x147ac) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  step. apply evt_done. reflexivity.
Qed.

Lemma cn_epi : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (rav s0v s1v s2v s3v s4v s5v : word),
  rw_cells rsegs m (bv_unsigned sp + 24) [C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  evt rsegs (fun ms' =>
      ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 80)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7
                    s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x147e4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m rav s0v s1v s2v s3v s4v s5v HC.
  do 9 step. apply evt_done. reflexivity.
Qed.

Lemma cn_free : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (V N CAP q L0 : Z),
  rw_cells rsegs m (bv_unsigned s0 + 64) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)] ->
  ro_cells rsegs m V [C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 L0)] ->
  evt rsegs (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 0x147bc) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x15664) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x147b0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m V N CAP q L0 HC RC.
  do 3 step. apply evt_done. reflexivity.
Qed.

Lemma cn_mm : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (V N CAP : Z),
  rw_cells rsegs m (bv_unsigned s0 + 64) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)] ->
  0 < N < 2 ^ 31 ->
  evt rsegs (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 0x147d4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 (V + 16))
                    (Z_to_bv 64 (16 * (N - 1))) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1d200) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x147bc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m V N CAP HC HN.
  do 6 step.
  rewrite (cn_sx32 N) by lia. rewrite (unsigned_lit N) by lia. rewrite (cn_swrap (N + -1)) by lia.
  rewrite (unsigned_lit (N + -1)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  replace ((N + -1) * 2 ^ 4) with (16 * (N - 1)) by lia.
  apply evt_done. reflexivity.
Qed.

Lemma cn_gm : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' =>
      (a0 <> Z_to_bv 64 0 /\
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x14808) fc None m (seg_rom rsegs)) \/
      (a0 = Z_to_bv 64 0 /\
       ms' = MS (mkR (Z_to_bv 64 0x147b0) sp gp tp t0 t1 t2 s0 s1 s0 s3 s2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1480c) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1479c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  step. if_cases Q.
  - apply Bool.negb_true_iff in Q.
    assert (NZ : a0 <> Z_to_bv 64 0) by (intro E; rewrite E, bv_eqb_refl in Q; discriminate).
    apply evt_done. left. split; [exact NZ | reflexivity].
  - apply Bool.negb_false_iff in Q. apply cn_eqb in Q.
    do 4 step. apply evt_done. right. split; [exact Q | reflexivity].
Qed.

Lemma cn_head : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (gone V N CAP q L0 : Z),
  s4 = Z_to_bv 64 0x31740 ->
  bytes_at rsegs m 0x30fc8 [Z_to_bv 8 gone] -> 0 <= gone < 256 ->
  rw_cells rsegs m (bv_unsigned s0 + 64) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)] ->
  ro_cells rsegs m V [C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 L0)] ->
  evt rsegs (fun ms' =>
      (gone <> 0 /\
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 s0 (Z_to_bv 64 q) (Z_to_bv 64 L0) a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x147ac) fc None m (seg_rom rsegs)) \/
      (gone = 0 /\
       ms' = MS (mkR (Z_to_bv 64 0x14774) sp gp tp t0 t1 t2 s0 s1 s1 (Z_to_bv 64 (bv_unsigned sp + 16))
                     (Z_to_bv 64 (bv_unsigned sp + 8)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x14958) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14748) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m gone V N CAP q L0 -> HG Hg HC RC.
  assert (RD : ov_read_bytes rsegs m (wa 0x30fc8) 1 = Some [Z_to_bv 8 gone]).
  { replace (wa 0x30fc8) with (wa (0x30fc8 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m 0x30fc8 [Z_to_bv 8 gone] 0 1 HG ltac:(lia)) by (cbn; lia). reflexivity. }
  step. rewrite (cn_zxb gone) by lia. step. if_cases Q.
  - unfold bv_eqb in Q. rewrite (unsigned_lit gone) in Q by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0 in Q.
    apply Z.eqb_eq in Q. subst gone.
    do 4 step. apply evt_done. right. split; reflexivity.
  - unfold bv_eqb in Q. rewrite (unsigned_lit gone) in Q by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0 in Q.
    apply Z.eqb_neq in Q.
    do 5 step. apply evt_done. left. split; [exact Q | reflexivity].
Qed.

Lemma cn_cmp : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (V N CAP q L0 LEN LP : Z),
  rw_cells rsegs m (bv_unsigned s0 + 64) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)] ->
  ro_cells rsegs m V [C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 L0)] ->
  0 <= L0 < 2 ^ 64 -> 0 <= LEN < 2 ^ 64 ->
  (a0 <> Z_to_bv 64 0 ->
   rw_cells rsegs m (bv_unsigned sp + 8) [C8 (Z_to_bv 64 LEN)] /\
   rw_cells rsegs m (bv_unsigned sp + 16) [C8 (Z_to_bv 64 LP)]) ->
  evt rsegs (fun ms' =>
      (a0 = Z_to_bv 64 0 /\
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x14808) fc None m (seg_rom rsegs)) \/
      (a0 <> Z_to_bv 64 0 /\ LEN <> L0 /\
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 L0) a2 a3 a4 a5 a6 a7
                     (Z_to_bv 64 LEN) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x14808) fc None m (seg_rom rsegs)) \/
      (a0 <> Z_to_bv 64 0 /\ LEN = L0 /\
       ms' = MS (mkR (Z_to_bv 64 0x1479c) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LP) (Z_to_bv 64 q) (Z_to_bv 64 LEN)
                     a3 a4 a5 a6 a7 (Z_to_bv 64 LEN) (Z_to_bv 64 LP) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1ccfc) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14774) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m V N CAP q L0 LEN LP HC RC HL0 HLEN HF.
  step. if_cases Q.
  - apply cn_eqb in Q. apply evt_done. left. split; [exact Q | reflexivity].
  - assert (NZ : a0 <> Z_to_bv 64 0) by (intro E; rewrite E, bv_eqb_refl in Q; discriminate).
    destruct (HF NZ) as [HN HP].
    do 4 step. if_cases Q2.
    + apply Bool.negb_true_iff in Q2. unfold bv_eqb in Q2. rewrite !unsigned_lit in Q2 by lia.
      apply Z.eqb_neq in Q2.
      apply evt_done. right. left. split; [exact NZ|]. split; [exact Q2 | reflexivity].
    + apply Bool.negb_false_iff in Q2. unfold bv_eqb in Q2. rewrite !unsigned_lit in Q2 by lia.
      apply Z.eqb_eq in Q2. subst L0.
      do 5 step. apply evt_done. right. right. split; [exact NZ|]. split; reflexivity.
Qed.

Lemma cn_dec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (V N CAP : Z),
  s5 = Z_to_bv 64 1 ->
  rw_cells rsegs m (bv_unsigned s0 + 64) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)] ->
  0 < N < 2 ^ 31 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
      munch [(bv_unsigned s0 + 72, bv_unsigned s0 + 76)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (bv_unsigned s0 + 64) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 (N - 1)); C4 (Z_to_bv 64 CAP)] /\
      ((1 < N /\
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 N) (Z_to_bv 64 (N - 1)) a2 a3 a4 a5 a6 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x14748) fc None m' (seg_rom rsegs)) \/
       (N = 1 /\
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 N) (Z_to_bv 64 (N - 1)) a2 a3 a4 a5 a6 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x147e4) fc None m' (seg_rom rsegs))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x147d4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m V N CAP -> HC HN MI.
  pose proof (zr_word s0) as R0. unfold inr64 in R0.
  pose proof (munch_refl [(bv_unsigned s0 + 72, bv_unsigned s0 + 76)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite (cn_sx32 N) by lia. step. try rewrite (unsigned_lit N) by lia. step.
  replace (N + -1) with (N - 1) in * by lia.
  step. if_cases Q.
  - unfold bv_lts in Q. rewrite (cn_signed 1), (cn_signed N) in Q by lia. apply Z.ltb_lt in Q.
    apply evt_done. eexists. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. left. split; [exact Q | reflexivity].
  - unfold bv_lts in Q. rewrite (cn_signed 1), (cn_signed N) in Q by lia. apply Z.ltb_ge in Q.
    apply evt_done. eexists. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. right. split; [lia | reflexivity].
Qed.

Lemma cn_pro : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo V N CAP : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 80 <= bv_unsigned sp -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned a0 + 64) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)] ->
  bv_unsigned a0 + 80 <= bv_unsigned sp - 80 -> 0 <= N < 2 ^ 31 ->
  evt rsegs (fun ms' => exists (j0 j1 j2 : list byte) m',
      munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      stk rsegs m' lo (bv_unsigned sp - 80) /\
      rw_cells rsegs m' (bv_unsigned sp - 80) [CB 8 j0] /\
      rw_cells rsegs m' (bv_unsigned sp - 72) [CB 8 j1] /\
      rw_cells rsegs m' (bv_unsigned sp - 64) [CB 8 j2] /\
      rw_cells rsegs m' (bv_unsigned sp - 56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
      rw_cells rsegs m' (bv_unsigned a0 + 64) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)] /\
      ((N = 0 /\
        ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0 t1 t2 a0 s1 (Z_to_bv 64 N) a1 a2 a3 a4 a5 a6 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x147e4) fc None m' (seg_rom rsegs)) \/
       (0 < N /\
        ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0 t1 t2 a0 a1 (Z_to_bv 64 N) a1 a2 a3 a4 a5 a6 a7
                      s2 s3 (Z_to_bv 64 0x31740) (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x14748) fc None m' (seg_rom rsegs))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14710) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo V N CAP ST LO MI HC HD HN.
  pose proof (zr_word sp) as Rsp. pose proof (zr_word a0) as Ra0. unfold inr64 in *.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 80%nat ST.
  do 10 step.
  rewrite (cn_sx32 N) by lia.
  destruct (cn_frame_split _ _ _ _ _ _ _ _ _ _ FR) as (j0 & j1 & j2 & F0 & F1 & F2 & F3).
  replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp - 72) in F1 by lia.
  replace (bv_unsigned sp + -80 + 16) with (bv_unsigned sp - 64) in F2 by lia.
  replace (bv_unsigned sp + -80 + 24) with (bv_unsigned sp - 56) in F3 by lia.
  step. if_cases Q.
  - apply Bool.negb_true_iff in Q. unfold bv_lts in Q. rewrite (cn_signed 0), (cn_signed N) in Q by lia.
    apply Z.ltb_ge in Q.
    apply evt_done. do 4 eexists.
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. left. split; [lia | reflexivity].
  - apply Bool.negb_false_iff in Q. unfold bv_lts in Q. rewrite (cn_signed 0), (cn_signed N) in Q by lia.
    apply Z.ltb_lt in Q.
    do 3 step.
    apply evt_done. do 4 eexists.
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. right. split; [lia | reflexivity].
Qed.

