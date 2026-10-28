From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import HufPure_HufX1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXBridge HufWalkKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec Mem Bytes.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
Import ListNotations.
Open Scope Z_scope.

Definition x4k2_bne_stmt : Prop :=
  forall x : word, bv_unsigned x <> 0 -> branch_taken BC_NE x (Z_to_bv 64 0) = true.

Definition x4k2_sll5_nz_stmt : Prop :=
  forall b y1 y2 y3 y4 y5 : word,
    bv_unsigned b mod 512 <> 0 ->
    bv_unsigned y1 mod 64 <= 11 -> bv_unsigned y2 mod 64 <= 11 -> bv_unsigned y3 mod 64 <= 11 ->
    bv_unsigned y4 mod 64 <= 11 -> bv_unsigned y5 mod 64 <= 11 ->
    bv_unsigned (alu64 ALU_SLL (alu64 ALU_SLL (alu64 ALU_SLL (alu64 ALU_SLL (alu64 ALU_SLL b y1) y2) y3) y4) y5) <> 0.

Definition x4k2_ip_nz_stmt : Prop :=
  forall p r : word, 8 <= bv_unsigned p -> bv_unsigned r <= 63 ->
    bv_unsigned (alu64 ALU_XOR (Z_to_bv 64 1)
                   (alu64 ALU_SLTU (alu64 ALU_XOR p (alu64 ALU_SRL r (Z_to_bv 64 3))) (Z_to_bv 64 1))) <> 0.

Definition x4k2_reload_nz_stmt : Prop :=
  forall x y : word, bv_unsigned y mod 64 <= 7 ->
    bv_unsigned (alu64 ALU_SLL (alu64 ALU_OR x (Z_to_bv 64 1)) y) mod 512 <> 0.

Definition x4k2_amt_stmt : Prop :=
  forall (m : word -> option byte) (DT4 : Z) (tbl : list byte) (cells : list deltX1) (A : Z),
    bytes_at usegs m DT4 tbl -> length tbl = 4096%nat -> x1_table_ok cells 11 -> tbl = firstn 4096 (x1_bytes' cells) ->
    (A - DT4) mod 2 = 0 -> 0 <= A - DT4 < 4096 ->
    bv_unsigned (rdval usegs m (wa A) 2 false) mod 64 <= 11.

Lemma x4k2_bit_nz : forall z i, Z.testbit z i = true -> z <> 0.
Proof. intros z i Hb E. subst z. rewrite Z.bits_0 in Hb. discriminate Hb. Qed.

Lemma x4k2_bit_mod_nz : forall z i k, 0 <= i < k -> Z.testbit z i = true -> z mod 2 ^ k <> 0.
Proof.
  intros z i k Hi Hb. apply (x4k2_bit_nz _ i). rewrite Z.mod_pow2_bits_low by lia. exact Hb.
Qed.

Lemma x4k2_shl_bit : forall i s z, 0 <= s -> i + s < 64 -> Z.testbit z i = true ->
  Z.testbit ((z * 2 ^ s) mod 2 ^ 64) (i + s) = true.
Proof.
  intros i s z Hs Hl Hb. rewrite Z.mod_pow2_bits_low by lia. rewrite Z.mul_pow2_bits by lia.
  replace (i + s - s) with i by lia. exact Hb.
Qed.

Lemma x4k2_low9 : forall z, z mod 512 <> 0 -> exists i, 0 <= i <= 8 /\ Z.testbit z i = true.
Proof.
  intros z Hz. change 512 with (2 ^ 9) in Hz.
  assert (P : 0 < 2 ^ 9) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mod_pos_bound z (2 ^ 9) P) as R.
  remember (z mod 2 ^ 9) as r eqn:Er.
  assert (Hr : 0 < r) by lia.
  assert (HL : Z.log2 r < 9) by (apply Z.log2_lt_pow2; lia).
  exists (Z.log2 r). split; [split; [apply Z.log2_nonneg | lia]|].
  rewrite <- (Z.mod_pow2_bits_low z 9 (Z.log2 r)) by lia. rewrite <- Er. apply Z.bit_log2. lia.
Qed.

Lemma x4k2_bne : x4k2_bne_stmt.
Proof.
  unfold x4k2_bne_stmt. intros x H. unfold branch_taken, bv_eqb.
  change (bv_unsigned (Z_to_bv 64 0)) with 0.
  destruct (Z.eqb_spec (bv_unsigned x) 0) as [E|E]; [contradiction | reflexivity].
Qed.

Lemma x4k2_sll5_nz : x4k2_sll5_nz_stmt.
Proof.
  unfold x4k2_sll5_nz_stmt. intros b y1 y2 y3 y4 y5 Hb H1 H2 H3 H4 H5.
  destruct (x4k2_low9 _ Hb) as (i & Hi & B0).
  pose proof (Z.mod_pos_bound (bv_unsigned y1) 64 ltac:(lia)) as R1.
  pose proof (Z.mod_pos_bound (bv_unsigned y2) 64 ltac:(lia)) as R2.
  pose proof (Z.mod_pos_bound (bv_unsigned y3) 64 ltac:(lia)) as R3.
  pose proof (Z.mod_pos_bound (bv_unsigned y4) 64 ltac:(lia)) as R4.
  pose proof (Z.mod_pos_bound (bv_unsigned y5) 64 ltac:(lia)) as R5.
  rewrite !KXS.u_sll64.
  set (s1 := bv_unsigned y1 mod 64) in *. set (s2 := bv_unsigned y2 mod 64) in *.
  set (s3 := bv_unsigned y3 mod 64) in *. set (s4 := bv_unsigned y4 mod 64) in *.
  set (s5 := bv_unsigned y5 mod 64) in *.
  pose proof (x4k2_shl_bit i s1 _ (proj1 R1) ltac:(lia) B0) as B1.
  pose proof (x4k2_shl_bit (i + s1) s2 _ (proj1 R2) ltac:(lia) B1) as B2.
  pose proof (x4k2_shl_bit (i + s1 + s2) s3 _ (proj1 R3) ltac:(lia) B2) as B3.
  pose proof (x4k2_shl_bit (i + s1 + s2 + s3) s4 _ (proj1 R4) ltac:(lia) B3) as B4.
  pose proof (x4k2_shl_bit (i + s1 + s2 + s3 + s4) s5 _ (proj1 R5) ltac:(lia) B4) as B5.
  exact (x4k2_bit_nz _ _ B5).
Qed.

Lemma x4k2_ip_nz : x4k2_ip_nz_stmt.
Proof.
  unfold x4k2_ip_nz_stmt. intros p r Hp Hr.
  rewrite KXS.u_xor64, KXS.u_sltu64, KXS.u_xor64, KXS.u_srl64.
  change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 3)) with 3.
  change (2 ^ (3 mod 64)) with 8.
  pose proof (bv_unsigned_in_range 64 r) as RR.
  assert (Q : 0 <= bv_unsigned r / 8 <= 7) by (Z.div_mod_to_equations; lia).
  set (P := bv_unsigned p) in *. set (W := bv_unsigned r / 8) in *.
  assert (NZ : Z.lxor P W <> 0) by (rewrite Z.lxor_eq_0_iff; lia).
  assert (NN : 0 <= Z.lxor P W) by (apply Z.lxor_nonneg; split; intros; lia).
  destruct (Z.ltb_spec (Z.lxor P W) 1) as [L|L]; [lia|].
  intro E. vm_compute in E. discriminate E.
Qed.

Lemma x4k2_reload_nz : x4k2_reload_nz_stmt.
Proof.
  unfold x4k2_reload_nz_stmt. intros x y Hy.
  rewrite KXS.u_sll64, KXS.u_or64.
  change (bv_unsigned (Z_to_bv 64 1)) with 1.
  pose proof (Z.mod_pos_bound (bv_unsigned y) 64 ltac:(lia)) as R.
  set (s := bv_unsigned y mod 64) in *.
  assert (B0 : Z.testbit (Z.lor (bv_unsigned x) 1) 0 = true).
  { rewrite Z.lor_spec. replace (Z.testbit 1 0) with true by reflexivity. apply Bool.orb_true_r. }
  pose proof (x4k2_shl_bit 0 s _ (proj1 R) ltac:(lia) B0) as B.
  change 512 with (2 ^ 9).
  exact (x4k2_bit_mod_nz _ (0 + s) 9 ltac:(lia) B).
Qed.

Lemma x4k2_amt : x4k2_amt_stmt.
Proof.
  unfold x4k2_amt_stmt. intros m DT4 tbl cells A HB HL HT ET EV RG.
  unfold x1_table_ok in HT. destruct HT as (_ & HZ & HC).
  unfold FseNCount.Zlength in HZ. change (2 ^ 11) with 2048 in HZ.
  set (X := (A - DT4) / 2).
  assert (HX : A = DT4 + 2 * X /\ 0 <= X < 2048) by (subst X; Z.div_mod_to_equations; lia).
  destruct HX as [EA XB].
  assert (VL : (Z.to_nat X < length cells)%nat) by lia.
  pose proof (HC X ltac:(change (2 ^ 11) with 2048; lia)) as CC.
  unfold x1_cell_ok in CC. destruct CC as [CB _].
  replace (wa A) with (wa (DT4 + Z.of_nat (2 * Z.to_nat X)%nat)) by (f_equal; lia).
  unfold rdval.
  rewrite (bytes_at_rdn usegs m DT4 tbl (2 * Z.to_nat X)%nat 2%nat HB) by lia.
  unfold KXS.extz. cbv beta iota.
  rewrite ET, skipn_firstn_comm, firstn_firstn, Nat.min_l by lia.
  rewrite (x1_bytes'_skipn cells (Z.to_nat X) VL).
  unfold x1_cellbytes. cbn [app firstn].
  rewrite bytes_le_to_Z_le_val. cbn [map le_val].
  set (c := nth (Z.to_nat X) cells x1_default) in *.
  pose proof (bv_unsigned_in_range 8 (Z_to_bv 8 (x1_byte c))) as R2.
  unfold bv_modulus in R2. change (2 ^ Z.of_N 8) with 256 in R2.
  assert (U1 : bv_unsigned (Z_to_bv 8 (x1_nbBits c)) = x1_nbBits c)
    by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; lia).
  rewrite U1. revert R2. generalize (bv_unsigned (Z_to_bv 8 (x1_byte c))). intros w R2.
  rewrite firstn_O. cbn [map le_val].
  rewrite KXS.u_small by lia.
  Z.div_mod_to_equations. lia.
Qed.
