(** Braid lookup loads and signed-word arithmetic for actual CRC instructions. *)
From Stdlib Require Import ZArith NArith List Lia Bool Btauto.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import Tac Bytes.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import
  CrcLib CrcWord CrcLinearBasis CrcBraidModel CrcBraidIndices CrcTables CrcLoads Img0.
Open Scope Z_scope.
Opaque csteps.
Definition braid_power (j : nat) : nat := match j with O=>160%nat|S O=>152%nat|S(S O)=>144%nat|_=>136%nat end.
Definition braid_byte (a : Z) (j : nat) := (Z.shiftr (a mod 2^32) (8*Z.of_nat j)) mod 256.
Definition braid_part (a : Z) (j : nat) := csteps (braid_power j) (braid_byte a j).
Lemma braid_byte_range : forall a j, 0 <= braid_byte a j < 256.
Proof. intros. unfold braid_byte. apply Z.mod_pos_bound. lia. Qed.
Lemma braid_part_range : forall a j, 0 <= braid_part a j < 2^32.
Proof. intros. apply csteps_range. pose proof (braid_byte_range a j). lia. Qed.
Lemma signed_xor4 : forall a b c d,
  0 <= a < 2^32 -> 0 <= b < 2^32 -> 0 <= c < 2^32 -> 0 <= d < 2^32 ->
  Z.lxor (Z.lxor (SX c) (SX d)) (Z.lxor (SX a) (SX b)) =
  SX (Z.lxor (Z.lxor c d) (Z.lxor a b)).
Proof.
  intros a b c d Ha Hb Hc Hd. rewrite (lxor_SX c d Hc Hd),(lxor_SX a b Ha Hb).
  apply lxor_SX;apply lxor_bound;lia.
Qed.
Theorem braid_signed_value : forall a,
  Z.lxor (Z.lxor (SX (braid_part a 3)) (SX (braid_part a 2)))
    (Z.lxor (SX (braid_part a 0)) (SX (braid_part a 1))) = SX (csteps 160 (a mod 2^32)).
Proof.
  intros a. rewrite signed_xor4 by apply braid_part_range.
  rewrite <- (braid_word_value (a mod 2^32) ltac:(apply Z.mod_pos_bound;lia)).
  f_equal. unfold braid_part,braid_byte,braid_power,braid_word.
  change (Z.lxor (Z.lxor (csteps 136 ((Z.shiftr (a mod 2^32) 24) mod 256)) (csteps 144 ((Z.shiftr (a mod 2^32) 16) mod 256))) (Z.lxor (csteps 160 ((a mod 2^32) mod 256)) (csteps 152 ((Z.shiftr (a mod 2^32) 8) mod 256))) = Z.lxor (csteps 160 ((a mod 2^32) mod 256)) (Z.lxor (csteps 152 ((Z.shiftr (a mod 2^32) 8) mod 256)) (Z.lxor (csteps 144 ((Z.shiftr (a mod 2^32) 16) mod 256)) (csteps 136 ((Z.shiftr (a mod 2^32) 24) mod 256))))).
  apply Z.bits_inj'. intros k Hk. rewrite !Z.lxor_spec. btauto.
Qed.
Lemma srliw24_raw : forall a,
  bv_swrap 32 (Z.shiftr (bv_wrap 32 a) 24) = Z.shiftr (a mod 2^32) 24.
Proof.
  intros a. unfold bv_wrap. change (bv_modulus 32) with (2^32).
  pose proof (Z.mod_pos_bound a (2^32) ltac:(lia)) as Hq.
  assert (HQ : 0 <= Z.shiftr (a mod 2^32) 24 < 256).
  { rewrite Z.shiftr_div_pow2 by lia. change (0 <= (a mod 2^32)/16777216 < 256).
    split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia]. }
  apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia.
Qed.
Lemma sx32_of_small : forall v, 0 <= v < 2^32 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 (SX v).
Proof.
  intros v Hv. apply sx32_SX;[|exact Hv]. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 64) with (2^64). lia.
Qed.
Lemma bword4_unsigned_range : forall bs k, 0 <= bv_unsigned (bword4 bs k) < 2^32.
Proof.
  intros bs k. unfold bword4,le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_nonneg (firstn 4 (skipn (Z.to_nat k) bs))) as H0.
  pose proof (bytes_le_to_Z_bound (firstn 4 (skipn (Z.to_nat k) bs))) as H1.
  assert (HN : (length (firstn 4 (skipn (Z.to_nat k) bs)) <= 4)%nat) by (rewrite firstn_length;lia).
  assert (HM : 256 ^ Z.of_nat (length (firstn 4 (skipn (Z.to_nat k) bs))) <= 2^32).
  { change (2^32) with (256^4). apply Z.pow_le_mono_r;lia. }
  rewrite bv_wrap_small;[lia|]. change (bv_modulus 64) with (2^64). lia.
Qed.
Lemma crc_table_at_offset : forall m (t : nat) i,
  bytes_at rsegs m CRC_TABS crc_table_bytes -> (t < 5)%nat -> 0 <= i < 256 ->
  ov_read_bytes rsegs m (wa (CRC_TABS+1024*Z.of_nat t+4*i)) 4 =
  Some (le4 (Z_to_bv 64 (csteps (crc_table_power t) i))).
Proof.
  intros m t i HT Ht Hi.
  replace (CRC_TABS+1024*Z.of_nat t+4*i) with (CRC_TABS+Z.of_nat (4*(256*t+Z.to_nat i))).
  - rewrite crc_table_word_at by (try assumption;lia). rewrite Z2Nat.id by lia. reflexivity.
  - repeat (rewrite Nat2Z.inj_mul || rewrite Nat2Z.inj_add).
    change (CRC_TABS+4*(256*Z.of_nat t+Z.of_nat (Z.to_nat i))=CRC_TABS+1024*Z.of_nat t+4*i).
    rewrite Z2Nat.id by lia. ring.
Qed.
Theorem crc_braid_table_read : forall m j a,
  bytes_at rsegs m CRC_TABS crc_table_bytes -> (j < 4)%nat -> 0 <= a < 2^64 ->
  ov_read_bytes rsegs m (wa (CRC_TABS+1024*Z.of_nat (S j)+braid_index_machine j a)) 4 =
  Some (le4 (Z_to_bv 64 (braid_part a j))).
Proof.
  intros m j a HT Hj Ha. rewrite braid_index_correct by assumption.
  unfold braid_index_expected. rewrite Z.shiftl_mul_pow2 by lia.
  replace (Z.land (Z.shiftr (a mod 2^32) (8*Z.of_nat j)) 255 * 2^2)
    with (4*Z.land (Z.shiftr (a mod 2^32) (8*Z.of_nat j)) 255) by ring.
  rewrite crc_table_at_offset by (try exact HT;try lia;pose proof (land255_range (Z.shiftr (a mod 2^32) (8*Z.of_nat j)));lia).
  rewrite land255_mod. unfold braid_part,braid_byte.
  assert (HP : crc_table_power (S j) = braid_power j).
  { destruct j as [|[|[|[|j]]]];[reflexivity|reflexivity|reflexivity|reflexivity|lia]. }
  rewrite HP. reflexivity.
Qed.
