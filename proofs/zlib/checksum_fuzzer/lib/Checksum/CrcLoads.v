(** Exact effective reads from the fixed binary's CRC lookup tables. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import Tac Bytes.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import
  CrcLib CrcLinearBasis CrcTables Img0.
Open Scope Z_scope.
Opaque csteps.
Lemma crc_table_word_at : forall m t i,
  bytes_at rsegs m CRC_TABS crc_table_bytes -> (t < 5)%nat -> (i < 256)%nat ->
  ov_read_bytes rsegs m (wa (CRC_TABS + Z.of_nat (4*(256*t+i)))) 4 =
  Some (le4 (Z_to_bv 64 (csteps (crc_table_power t) (Z.of_nat i)))).
Proof.
  intros m t i HT Ht Hi.
  rewrite (rd4_at rsegs m CRC_TABS crc_table_bytes
    (Z.of_nat (4*(256*t+i))) _ HT).
  - change (Some (le4 (crc_table_word t i)) =
      Some (le4 (Z_to_bv 64 (csteps (crc_table_power t) (Z.of_nat i))))).
    rewrite <- (Z_to_bv_bv_unsigned (crc_table_word t i)),crc_table_word_correct by assumption.
    reflexivity.
  - lia.
  - rewrite crc_table_bytes_length.
    repeat (rewrite Nat2Z.inj_mul || rewrite Nat2Z.inj_add).
    change (4*(256*Z.of_nat t+Z.of_nat i)+4 <= 5120). lia.
  - reflexivity.
Qed.
Lemma crc_byte_table_at : forall m i,
  bytes_at rsegs m CRC_TABS crc_table_bytes -> 0 <= i < 256 ->
  ov_read_bytes rsegs m (wa (CRC_TABS + 4*i)) 4 =
  Some (le4 (Z_to_bv 64 (csteps 8 i))).
Proof.
  intros m i HT Hi.
  replace (CRC_TABS+4*i) with (CRC_TABS+Z.of_nat (4*(256*0+Z.to_nat i))).
  - rewrite crc_table_word_at by (try exact HT;lia).
    cbn [crc_table_power List.nth]. rewrite Z2Nat.id by lia. reflexivity.
  - rewrite Nat2Z.inj_mul. cbn. rewrite Z2Nat.id by lia. reflexivity.
Qed.
