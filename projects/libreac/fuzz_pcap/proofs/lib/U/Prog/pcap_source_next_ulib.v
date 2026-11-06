From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel pcap_source_struct pcap_source_struct_next
  pcap_source_next_lib rd_u32_c.
Import ListNotations.
Open Scope Z_scope.

Ltac closed_vm :=
  lazymatch goal with
  | |- ?g => tryif (match g with context [?x] => is_var x end) then fail "open goal" else (vm_compute; reflexivity)
  end.

Lemma Z_to_bv8_mod : forall a b, a mod 2 ^ 8 = b mod 2 ^ 8 -> Z_to_bv 8 a = Z_to_bv 8 b.
Proof. intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod. exact H. Qed.

Lemma shr_mod8 : forall X Y k, 0 <= k -> k + 8 <= 32 -> X mod 2 ^ 32 = Y mod 2 ^ 32 ->
  Z.shiftr X k mod 2 ^ 8 = Z.shiftr Y k mod 2 ^ 8.
Proof.
  intros X Y k Hk Hk8 H. apply Z.bits_inj'. intros i Hi. destruct (Z.lt_ge_cases i 8) as [Hl|Hg].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
    rewrite <- (Z.mod_pow2_bits_low X 32 (i + k)) by lia. rewrite <- (Z.mod_pow2_bits_low Y 32 (i + k)) by lia.
    rewrite H. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma le4_mod : forall x y : word, bv_unsigned x mod 2 ^ 32 = bv_unsigned y mod 2 ^ 32 -> le4 x = le4 y.
Proof.
  intros x y H. unfold le4. cbn [Z_to_le_bytes]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add].
  f_equal; [|f_equal; [|f_equal; [|f_equal]]]; apply Z_to_bv8_mod.
  - rewrite <- (Z.shiftr_0_r (bv_unsigned x)), <- (Z.shiftr_0_r (bv_unsigned y)). apply shr_mod8; lia.
  - apply shr_mod8; lia.
  - apply shr_mod8; lia.
  - apply shr_mod8; lia.
Qed.

Lemma ps_olen_mod : forall m A (f sw x y vt vid : word) pad,
  rw_cells rsegs m A [C8 f; C4 sw; C4 x; C4 vt; C2 vid; CB 2 pad] -> bv_unsigned x mod 2 ^ 32 = bv_unsigned y mod 2 ^ 32 ->
  rw_cells rsegs m A [C8 f; C4 sw; C4 y; C4 vt; C2 vid; CB 2 pad].
Proof.
  intros m A f sw x y vt vid pad [[W B] R] E. split; [split; [exact W|]|exact R].
  cbn [cells_bytes cbytes] in *. rewrite <- (le4_mod x y E). exact B.
Qed.

Lemma hdr4 : forall m A (F : list byte) q j,
  bytes_at rsegs m A (firstn 16 (skipn (Z.to_nat q) F)) -> 0 <= q -> q + 16 <= Z.of_nat (length F) -> 0 <= j <= 12 ->
  bytes_at rsegs m (A + j)
    [nth (Z.to_nat (q + j)) F (Z_to_bv 8 0); nth (Z.to_nat (q + j + 1)) F (Z_to_bv 8 0);
     nth (Z.to_nat (q + j + 2)) F (Z_to_bv 8 0); nth (Z.to_nat (q + j + 3)) F (Z_to_bv 8 0)].
Proof.
  intros m A F q j (H0 & H1 & H) Hq Hl Hj. rewrite length_firstn, length_skipn in H1.
  split; [lia|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi.
  replace (A + j + Z.of_nat i) with (A + Z.of_nat (Z.to_nat j + i)) by lia.
  rewrite H by (rewrite length_firstn, length_skipn; lia).
  rewrite (nth_error_nth' _ (Z_to_bv 8 0)) by (rewrite length_firstn, length_skipn; lia).
  rewrite nth_firstn_lt by lia. rewrite nth_skipn_add.
  destruct i as [|[|[|[|i]]]]; try lia; cbn [nth_error]; do 2 f_equal; lia.
Qed.

Lemma rd_hw : forall swz F q j, (swz = 0 \/ swz = 1) ->
  rd_val (wz swz) (nth (Z.to_nat (q + j)) F (Z_to_bv 8 0)) (nth (Z.to_nat (q + j + 1)) F (Z_to_bv 8 0))
    (nth (Z.to_nat (q + j + 2)) F (Z_to_bv 8 0)) (nth (Z.to_nat (q + j + 3)) F (Z_to_bv 8 0)) = hw (swz =? 1) F q j.
Proof.
  intros swz F q j [-> | ->]; unfold rd_val, rd_le, hw, w32le, fb.
  - change (bv_eqb (wz 0) (Z_to_bv 64 0)) with true. change (0 =? 1) with false. cbv iota. reflexivity.
  - change (bv_eqb (wz 1) (Z_to_bv 64 0)) with false. change (1 =? 1) with true. cbv iota. lia.
Qed.

Lemma rd_range : forall w c0 c1 c2 c3, 0 <= rd_val w c0 c1 c2 c3 < 2 ^ 32.
Proof.
  intros w c0 c1 c2 c3. pose proof (byte_range c0). pose proof (byte_range c1). pose proof (byte_range c2).
  pose proof (byte_range c3). unfold rd_val, rd_le. destruct (bv_eqb w (Z_to_bv 64 0)); lia.
Qed.
