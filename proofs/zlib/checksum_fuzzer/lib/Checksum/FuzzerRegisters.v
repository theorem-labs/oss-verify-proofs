From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import PropExec Exec MState Mem Frame Regs6ss.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcLib CrcTables AdlerModel Img0 RegisterBridge ChecksumRegisters FuzzerFull FuzzerReturn.
Open Scope Z_scope.
Theorem fuzzer_valid_registers : forall (R F : bvmap 5 word) (fc : bv 32) (lo B : Z) (inp : list byte) (m : word -> option byte),
  reg_get R 10 = Z_to_bv 64 B -> reg_get R 11 = Z_to_bv 64 (Z.of_nat (length inp)) ->
  bytes_at rsegs m B inp -> bytes_at rsegs m CRC_TABS crc_table_bytes ->
  bytes_at rsegs m X2N_TAB x2n_bytes -> bytes_at rsegs m 0x119e0 (le8 (Z_to_bv 64 ADLER_MAGIC)) ->
  0 < B -> B+Z.of_nat (length inp) < 2^64 -> 1 <= Z.of_nat (length inp) <= 1048576 ->
  stk rsegs m lo (bv_unsigned (reg_get R 2)) -> lo+192 <= bv_unsigned (reg_get R 2) ->
  (B+Z.of_nat (length inp) <= bv_unsigned (reg_get R 2)-192 \/ bv_unsigned (reg_get R 2) <= B) ->
  (CRC_TABS+5120 <= bv_unsigned (reg_get R 2)-192 \/ bv_unsigned (reg_get R 2) <= CRC_TABS) ->
  (X2N_TAB+128 <= bv_unsigned (reg_get R 2)-192 \/ bv_unsigned (reg_get R 2) <= X2N_TAB) ->
  (0x119e0+8 <= bv_unsigned (reg_get R 2)-192 \/ bv_unsigned (reg_get R 2) <= 0x119e0) ->
  evt rsegs (checksum_register_post 192 0 R F fc lo m)
    (MS R F (Z_to_bv 64 0x141f0) fc None m (seg_rom rsegs)).
Proof.
  intros R F fc lo B inp m H0 H1 INP TABLE XTABLE MAGIC HBUF TOP SIZE ST LO DI DT DX DM.
  unfold checksum_register_post. eapply canonical_contract_transport.
  unfold canonical_register_state, MS. cbn. unfold mkR_of. cbn. rewrite H0,H1.
  apply fuzzer_valid_spec;assumption.
Qed.
