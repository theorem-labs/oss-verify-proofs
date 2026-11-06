(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout RT_iface D_defs D_kit I_read.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act L2StmtD.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzDefs BzInv BzContracts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecTac2 BzDState BzDBlock BzDOut BzDOK S0_bzd_loop1 A0F_bzdV A0F_bzd_skV.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_bzd_loop1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_bzdV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_bzd_skV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

Section BZDK.
Context {ACEIL__ : ACeil}.

Lemma bz_rw_C8_inj : forall (m : mem) a w w', rw_cells a0segs m a [C8 w] -> rw_cells a0segs m a [C8 w'] -> w = w'.
Proof.
  intros m a w w' [[_ B1] _] [[_ B2] _]. cbn [cells_bytes cbytes app] in B1, B2. rewrite app_nil_r in B1, B2.
  destruct B1 as (_ & _ & R1). destruct B2 as (_ & _ & R2). rewrite length_le8 in R1, R2.
  rewrite <- (le_bytes_to_word_le8 w), <- (le_bytes_to_word_le8 w'). f_equal.
  apply nth_error_ext. intros i. destruct (Nat.lt_ge_cases i 8) as [L|L].
  - rewrite <- (R1 i L). exact (R2 i L).
  - rewrite (proj2 (nth_error_None (le8 w) i)) by (rewrite length_le8; exact L).
    rewrite (proj2 (nth_error_None (le8 w') i)) by (rewrite length_le8; exact L). reflexivity.
Qed.

Lemma bz_strm_tail : forall (m m' : mem) (STRM : Z) (b b' : bzs),
  rw_cells a0segs m STRM (STRM_CELLS b) -> rw_cells a0segs m' STRM (STRM_CELLS b') ->
  agree_on (fun x => STRM + 44 <= x < STRM + 80) m m' ->
  bs_bzalloc b' = bs_bzalloc b /\ bs_bzfree b' = bs_bzfree b /\ bs_opaque b' = bs_opaque b.
Proof.
  intros m m' STRM b b' H H' AG.
  change (STRM_CELLS b) with ([C8 (Z_to_bv 64 (bs_src b + (bs_len b - bs_ai b))); C4 (Z_to_bv 64 (bs_ai b)); C4 (bs_til b); C4 (bs_tih b); CB 4 (bs_q1 b);
     C8 (Z_to_bv 64 (bs_dst b + (bs_dlen b - bs_av b))); C4 (Z_to_bv 64 (bs_av b)); C4 (bs_tol b); C4 (bs_toh b); CB 4 (bs_q2 b); C8 (Z_to_bv 64 (bs_S b))]
     ++ ([C8 (bs_bzalloc b)] ++ [C8 (bs_bzfree b)] ++ [C8 (bs_opaque b)])) in H.
  change (STRM_CELLS b') with ([C8 (Z_to_bv 64 (bs_src b' + (bs_len b' - bs_ai b'))); C4 (Z_to_bv 64 (bs_ai b')); C4 (bs_til b'); C4 (bs_tih b'); CB 4 (bs_q1 b');
     C8 (Z_to_bv 64 (bs_dst b' + (bs_dlen b' - bs_av b'))); C4 (Z_to_bv 64 (bs_av b')); C4 (bs_tol b'); C4 (bs_toh b'); CB 4 (bs_q2 b'); C8 (Z_to_bv 64 (bs_S b'))]
     ++ ([C8 (bs_bzalloc b')] ++ [C8 (bs_bzfree b')] ++ [C8 (bs_opaque b')])) in H'.
  apply (proj1 (DecTac2.rw_cells_app_iff a0segs m _ _ _)) in H. destruct H as [_ T]. cbn [cells_size csize Nat.add] in T.
  apply (proj1 (DecTac2.rw_cells_app_iff a0segs m' _ _ _)) in H'. destruct H' as [_ T']. cbn [cells_size csize Nat.add] in T'.
  assert (T2 : rw_cells a0segs m' (STRM + Z.of_nat 56) ([C8 (bs_bzalloc b)] ++ [C8 (bs_bzfree b)] ++ [C8 (bs_opaque b)])).
  { apply (n_rw_cells_agree a0segs m m' _ _ T). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. cbn [cells_size csize Nat.add app] in Hx. lia. }
  apply (proj1 (DecTac2.rw_cells_app_iff a0segs m' _ _ _)) in T2. destruct T2 as [A1 T2]. apply (proj1 (DecTac2.rw_cells_app_iff a0segs m' _ _ _)) in T2. destruct T2 as [A2 A3].
  apply (proj1 (DecTac2.rw_cells_app_iff a0segs m' _ _ _)) in T'. destruct T' as [B1 T']. apply (proj1 (DecTac2.rw_cells_app_iff a0segs m' _ _ _)) in T'. destruct T' as [B2 B3].
  split; [exact (bz_rw_C8_inj m' _ _ _ B1 A1)|]. split; [exact (bz_rw_C8_inj m' _ _ _ B2 A2)| exact (bz_rw_C8_inj m' _ _ _ B3 A3)].
Qed.

(* [comment removed for export] *)
Lemma bz_model : forall d0 s0, d_state d0 = BZ_X_MAGIC_1 -> bzDecompress d0 s0 = K_L (Datatypes.S (length (s_in s0))) (decompress d0 s0).
Proof. intros d0 s0 H. rewrite bzDecompress_eq. rewrite (bzd_loop_10 _ d0 s0 H). reflexivity. Qed.

(* [comment removed for export] *)
Lemma bz_ctx_ok : forall (RT : rt_sig) (AF : art_facts RT) Σ (m : mem) (z : bzdctx) (SHS zp zn op on fS : Z) (kS : nat),
  let cx := z_cx z in
  ART RT Σ m -> alloc_ceiling = rt_sp0 RT Σ - STACK_WIN ->
  In (fS, kS) (rt_frames RT Σ) -> fS <= b_strm cx -> b_strm cx + 80 <= fS + fs_size kS - 8 -> b_strm cx mod 8 = 0 ->
  In (b_s cx, 64144) (rt_live RT Σ) ->
  In (zp, zn) (rt_live RT Σ) -> zp <= b_src cx -> b_src cx + b_len cx <= zp + zn ->
  In (op, on) (rt_live RT Σ) -> op <= b_dst cx -> b_dst cx + b_dlen cx <= op + on ->
  (b_tt cx <> 0 -> In (b_tt cx, 400000 * b_n cx) (rt_live RT Σ)) ->
  (b_ll16 cx <> 0 -> In (b_ll16 cx, 200000 * b_n cx) (rt_live RT Σ)) ->
  (b_ll4 cx <> 0 -> In (b_ll4 cx, 50000 * b_n cx) (rt_live RT Σ)) ->
  dpureA cx -> sanchor (b_s cx) SHS ->
  alloc_ceiling <= z_lo z -> z_lo z + 400 <= bv_unsigned (z_sp z) ->
  bv_unsigned (z_spi z) = bv_unsigned (z_sp z) - 400 -> Z_to_bv 64 (bv_unsigned (z_spi z) + 400) = z_sp z ->
  Z.of_nat (length (z_payload z)) = b_len cx ->
  bzdctx_okA z SHS.
Proof.
  intros RT AF Σ m z SHS zp zn op on fS kS cx ART0 CEQ FSIN FSLO FSHI T8 SLIV ZLIV ZLO ZHI OLIV OLO OHI TLIV L16LIV L4LIV PURE ANS CL LU EU EZ PL. subst cx.
  destruct PURE as (LEN0 & DLEN0 & SM01 & NR & S16 & TT16 & L1616 & L416 & SEP).
  destruct SEP as (D1 & D2 & D3 & D4 & D5 & D6 & DTT & DL16 & DL4 & DLL). cbv zeta in D1, D2, D3, D4, D5, D6, DTT, DL16, DL4, DLL.
  pose proof (af_live_range RT AF Σ m _ _ ART0 SLIV) as (SL0 & SL1 & SLI). pose proof (af_live_range RT AF Σ m _ _ ART0 ZLIV) as (ZL0 & ZL1 & _).
  pose proof (af_live_range RT AF Σ m _ _ ART0 OLIV) as (OL0 & OL1 & OLI).
  pose proof (af_frames_range RT AF Σ m _ _ ART0 FSIN) as (FS0 & FS1 & _). pose proof (af_frames_align RT AF Σ m _ _ ART0 FSIN) as (_ & FSSEG).
  pose proof (bv_unsigned_in_range 64 (z_sp z)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  rewrite <- CEQ in *. unfold SEGTOP_A in *.
  assert (BLK : forall p n, In (p, n) (rt_live RT Σ) -> (0 < p /\ p + n <= alloc_ceiling) /\ bzd_img_apart 6414336 p n).
  { intros p n IN. pose proof (af_live_range RT AF Σ m _ _ ART0 IN) as (A0 & A1 & A2). rewrite <- CEQ in A1. unfold SEGTOP_A in A2. split; [split; [exact A0| exact A1]| exact A2]. }
  unfold bzdctx_okA.
  split. { repeat split; try assumption; try (clear - SL0 SL1 ZL0 ZL1 ZLO ZHI OL0 OL1 OLO OHI FS0 FS1 FSLO FSHI LEN0 DLEN0 NR SPR; lia). }
  split; [exact ANS|].
  split. { split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split; [exact D5|]. split; [exact D6|].
           unfold bzd_img_apart. split; [exact SLI|]. split; [right; clear - FSSEG FSLO; lia| clear - OLI OLO OHI DLEN0; lia]. }
  split. { intros E. destruct (DTT E) as (B1 & B2 & _ & B4). destruct (BLK _ _ (TLIV E)) as (R & IA). repeat split; try assumption; exact (proj1 R) || exact (proj2 R). }
  split. { intros E. destruct (DL16 E) as (B1 & B2 & _ & B4). destruct (BLK _ _ (L16LIV E)) as (R & IA). repeat split; try assumption; exact (proj1 R) || exact (proj2 R). }
  split. { intros E. destruct (DL4 E) as (B1 & B2 & _ & B4). destruct (BLK _ _ (L4LIV E)) as (R & IA). repeat split; try assumption; exact (proj1 R) || exact (proj2 R). }
  exact DLL.
Qed.

End BZDK.
