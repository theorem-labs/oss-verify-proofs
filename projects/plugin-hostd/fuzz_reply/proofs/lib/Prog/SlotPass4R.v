From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import check_no_loss_read_c check_shape_done_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma p4_sx32 : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma p4_signed : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit_wrap.
  change (2^64) with 18446744073709551616. change (2^63) with 9223372036854775808 in *.
  destruct (Z.ltb_spec (z mod 18446744073709551616) 9223372036854775808); cbv iota;
    Z.div_mod_to_equations; lia.
Qed.

Lemma p4_beq : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma p4_rd4 : forall m a (v : word) e, bytes_at rsegs m a (le4 v) -> e = a ->
  ov_read_bytes rsegs m (Z_to_bv 64 e) 4 = Some (le4 v).
Proof.
  intros m a v e H ->. change (Z_to_bv 64 a) with (wa a).
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a (le4 v) 0 4 H ltac:(lia)) by (rewrite length_le4; lia).
  reflexivity.
Qed.

Lemma p4_rd8 : forall m a (v : word) e, bytes_at rsegs m a (le8 v) -> e = a ->
  ov_read_bytes rsegs m (Z_to_bv 64 e) 8 = Some (le8 v).
Proof.
  intros m a v e H ->. change (Z_to_bv 64 a) with (wa a).
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a (le8 v) 0 8 H ltac:(lia)) by (rewrite length_le8; lia).
  reflexivity.
Qed.

Lemma p4_loop : forall (d : nat) (N FD EOF G q j : Z) (fs : list Z)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  d = Z.to_nat (q - j) -> 0 <= j <= q -> q < N -> N < 2 ^ 31 -> 0 <= FD < 2 ^ 31 -> 0 <= EOF < 2 ^ 31 ->
  0 <= G -> G + 56 * N < 2 ^ 63 ->
  (forall i, j <= i <= q -> 0 <= nth (Z.to_nat i) fs 0 < 2 ^ 31 /\
     ov_read_bytes rsegs m (Z_to_bv 64 (G + 56 * i)) 4 = Some (le4 (Z_to_bv 64 (nth (Z.to_nat i) fs 0)))) ->
  (forall i, j <= i < q -> nth (Z.to_nat i) fs 0 <> FD) -> nth (Z.to_nat q) fs 0 = FD ->
  ov_read_bytes rsegs m (Z_to_bv 64 (G + 56 * q + 4)) 4 = Some (le4 (Z_to_bv 64 EOF)) ->
  evt rsegs (fun ms => exists a1 a2 a3 : word,
      ms = MS (mkR (Z_to_bv 64 0x13fcc) x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 FD) a1 a2 a3 x14 x15 x16 x17
                   (Z_to_bv 64 EOF) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x13a58) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 FD) (Z_to_bv 64 (N - j)) (Z_to_bv 64 (G + 4 + 56 * j)) x13 x14
             x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13d74) fc None m ro).
Proof.
  induction d as [|d IH];
    intros N FD EOF G q j fs x1 x2 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
      x28 x29 x30 x31 F fc m ro Hd Hj HqN HN HFD HEOF HG HGN RB NE HQ RE.
  - assert (EJ : j = q) by lia. subst j.
    destruct (RB q ltac:(lia)) as [R0 RD]. rewrite HQ in R0, RD.
    step. rewrite (p4_sx32 FD) by lia.
    step. if_cases HC; [|exfalso; zify_cond HC; lia].
    step. rewrite (p4_sx32 EOF) by lia.
    step. apply evt_done. do 3 eexists. reflexivity.
  - destruct (RB j ltac:(lia)) as [R0 RD].
    assert (NJ : nth (Z.to_nat j) fs 0 <> FD) by (apply NE; lia).
    step. rewrite (p4_sx32 (nth (Z.to_nat j) fs 0)) by lia.
    step. if_cases HC; [exfalso; zify_cond HC; lia|].
    step. step. step. if_cases HB; [|exfalso; zify_cond HB; lia].
    replace (N - j + -1) with (N - (j + 1)) by lia.
    replace (G + 4 + 56 * j + 56) with (G + 4 + 56 * (j + 1)) by lia.
    apply (IH N FD EOF G q (j + 1) fs); try lia; try assumption.
    + intros i Hi. apply RB. lia.
    + intros i Hi. apply NE. lia.
Qed.

Lemma p4_head : forall (SP S N FD EOF G q : Z) (fs : list Z)
    (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m1 ro : word -> option byte),
  store_ok rsegs m (Z_to_bv 64 (SP + 40)) 8 = true ->
  m1 = write_to_mem m (Z_to_bv 64 (SP + 40)) (le8 (Z_to_bv 64 0)) ->
  ov_read_bytes rsegs m1 (Z_to_bv 64 0x30fd8) 4 = Some (le4 (Z_to_bv 64 N)) ->
  ov_read_bytes rsegs m1 (Z_to_bv 64 S) 4 = Some (le4 (Z_to_bv 64 FD)) ->
  ov_read_bytes rsegs m1 (Z_to_bv 64 0x30ff0) 8 = Some (le8 (Z_to_bv 64 G)) ->
  0 <= q < N -> N < 2 ^ 31 -> 0 <= FD < 2 ^ 31 -> 0 <= EOF < 2 ^ 31 -> 0 <= G -> G + 56 * N < 2 ^ 63 ->
  (forall i, 0 <= i <= q -> 0 <= nth (Z.to_nat i) fs 0 < 2 ^ 31 /\
     ov_read_bytes rsegs m1 (Z_to_bv 64 (G + 56 * i)) 4 = Some (le4 (Z_to_bv 64 (nth (Z.to_nat i) fs 0)))) ->
  (forall i, 0 <= i < q -> nth (Z.to_nat i) fs 0 <> FD) -> nth (Z.to_nat q) fs 0 = FD ->
  ov_read_bytes rsegs m1 (Z_to_bv 64 (G + 56 * q + 4)) 4 = Some (le4 (Z_to_bv 64 EOF)) ->
  evt rsegs (fun ms => exists a1 a2 a3 : word,
      ms = MS (mkR (Z_to_bv 64 0x13fcc) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) (Z_to_bv 64 FD) a1 a2 a3
                   x14 x15 x16 x17 (Z_to_bv 64 EOF) x19 (Z_to_bv 64 0x30fc0) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
                   x31) F (Z_to_bv 64 0x13a58) fc None m1 ro)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
             (Z_to_bv 64 0x30fc0) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13d5c) fc None m ro).
Proof.
  intros SP S N FD EOF G q fs x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m m1 ro SOK EM RN RF RG HqN HN HFD HEOF HG HGN RB NE HQ RE.
  step. rewrite <- EM.
  step. rewrite (p4_sx32 N) by lia.
  step. rewrite (p4_sx32 FD) by lia.
  step. if_cases HC; [exfalso; zify_cond HC; lia|].
  step. step.
  replace (G + 4) with (G + 4 + 56 * 0) by lia. replace (Z_to_bv 64 N) with (Z_to_bv 64 (N - 0)) by (f_equal; lia).
  apply (p4_loop (Z.to_nat (q - 0)) N FD EOF G q 0 fs); solve [lia | assumption | intros i Hi; apply RB; lia |
    intros i Hi; apply NE; lia].
Qed.

Lemma p4_mid : check_no_loss_read_contract -> forall (SP S EOF : Z)
    (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  (EOF = 0 \/ EOF = 1) -> 0 <= S < 2 ^ 64 -> 0 <= SP + 40 < 2 ^ 64 ->
  (EOF = 0 -> bytes_at rsegs m (S + 24) (le4 (Z_to_bv 64 0))) ->
  evt rsegs (fun ms =>
      ms = MS (mkR (Z_to_bv 64 0x13fe4) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) (Z_to_bv 64 S)
                   (Z_to_bv 64 (SP + 40)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 EOF) x19 x20 x21 x22 x23 x24 x25 x26 x27
                   x28 x29 x30 x31) F (Z_to_bv 64 0x14710) fc None m (seg_rom rsegs))
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 EOF) x19
             x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13fcc) fc None m (seg_rom rsegs)).
Proof.
  intros CNLR SP S EOF x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m HE HS HSP HB.
  destruct HE as [-> | ->].
  - step. if_false.
    step. step.
    eapply evt_cut.
    { eapply (CNLR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 S)) with (n := 0); [lia|].
      rewrite unsigned_lit by lia. exact (HB eq_refl). }
    intros ms (a0' & ->). rewrite ret_pc_even by lia.
    step. step. step. apply evt_done. reflexivity.
  - step. if_true.
    step. step. step. apply evt_done. reflexivity.
Qed.

Lemma p4_ends : forall (SP S : Z)
    (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  evt rsegs (fun ms =>
      ms = MS (mkR (Z_to_bv 64 0x13ff8) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) (Z_to_bv 64 S)
                   (Z_to_bv 64 0x102e9) (Z_to_bv 64 (SP + 40)) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
                   x27 x28 x29 x30 x31) F (Z_to_bv 64 0x143c0) fc None m ro)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
             x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13fe4) fc None m ro).
Proof.
  intros. step. step. step. step. step. apply evt_done. reflexivity.
Qed.

Lemma p4_done : check_shape_done_contract -> forall (SP S : Z) (AT : word)
    (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  ov_read_bytes rsegs m (Z_to_bv 64 (SP + 40)) 8 = Some (le8 AT) ->
  bytes_at rsegs m check_shape_done_c.G_NOUT (le8 AT) ->
  evt rsegs (fun ms => exists a1 : word,
      ms = MS (mkR (Z_to_bv 64 0x14008) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) (Z_to_bv 64 S) a1
                   x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x145fc) fc None m (seg_rom rsegs))
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
             x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13ff8) fc None m (seg_rom rsegs)).
Proof.
  intros CSD SP S AT x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m RA HN.
  step. step.
  eapply evt_cut; [eapply CSD; exact HN|].
  intros ms (a1' & ->). rewrite ret_pc_even by lia.
  step. step. apply evt_done. eexists. reflexivity.
Qed.

Lemma p4_jump : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  evt rsegs (fun ms =>
      ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
                   x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13d38) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
             x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14008) fc None m ro).
Proof.
  intros. step. apply evt_done. reflexivity.
Qed.
