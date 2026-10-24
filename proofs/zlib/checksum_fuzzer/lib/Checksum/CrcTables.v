(** Exact values of the five CRC lookup tables in the fixed zlib ELF image. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import Tac Bytes Image.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcAlgebra CrcLib CrcLinearBasis Img0.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP09 YO0d YL0g YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib Require ChecksumBridge.
Import ListNotations.
Open Scope Z_scope.
Module CM := OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Mem.
Definition CRC_TABS : Z := 0x10554.
Definition crc_table_bytes : list byte := Eval vm_compute in
  match image_bytes rsegs CRC_TABS 5120 with Some bs => bs | None => [] end.
Lemma crc_table_bytes_length : List.length crc_table_bytes = 5120%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma crc_table_empty_image : CM.bytes_at rsegs (fun _ => None) CRC_TABS crc_table_bytes.
Proof.
  apply (ro_table_at rsegs (fun _ => None));
    [intros a b H;discriminate|vm_compute;reflexivity|unfold CRC_TABS;lia|].
  rewrite crc_table_bytes_length. change (0x10554 + 5120 <= 2^64). lia.
Qed.
Lemma crc_table_in_ro : forall a, CRC_TABS <= a < CRC_TABS + 5120 -> in_ro_img src0_msyms a.
Proof.
  intros a Ha. split.
  - exists ChecksumBridge.first_segment. split; [exact ChecksumBridge.first_segment_in|].
    split; [vm_compute;reflexivity|]. change (65536 <= a < 65536+12288). unfold CRC_TABS in Ha. lia.
  - unfold static_owned,ms_lock,ms_libc,ms_got_guard,ms_guard,ms_debruijn,ms_size_classes,ms_small_cnt,ms_med_cnt.
    cbn [src0_msyms].
    cbv delta [YH03.src0_D_malloc_lock YH03.src0_D_libc YH03.src0_D_got_stack_chk_guard
      YH03.src0_D_stack_chk_guard YH03.src0_D_debruijn32 YH03.src0_D_size_classes
      YH03.src0_D_small_cnt_tab YH03.src0_D_med_cnt_tab].
    cbn. unfold CRC_TABS in Ha. lia.
Qed.
Lemma driver_has_crc_tables : forall mem,
  rodata_ok src0_msyms mem -> CM.bytes_at rsegs mem CRC_TABS crc_table_bytes.
Proof.
  intros mem HRO. destruct crc_table_empty_image as [HA [HL HR]].
  split;[exact HA|]. split;[exact HL|]. intros i Hi.
  rewrite ChecksumBridge.checksum_effective_byte,HRO.
  - exact (HR i Hi).
  - apply crc_table_in_ro. apply Nat2Z.inj_lt in Hi.
    rewrite crc_table_bytes_length in Hi. change (Z.of_nat i < 5120) in Hi. lia.
Qed.
Definition crc_table_power (t : nat) : nat := nth t [8%nat;160%nat;152%nat;144%nat;136%nat] 0%nat.
Definition crc_table_word (t i : nat) : word := bword4 crc_table_bytes (Z.of_nat (4*(256*t+i))).
Definition crc_tables_check : bool := forallb (fun t => forallb (fun i =>
  bv_unsigned (crc_table_word t i) =? csteps (crc_table_power t) (Z.of_nat i)) (seq 0 256)) (seq 0 5).
Lemma crc_tables_checked : crc_tables_check = true.
Proof. vm_compute. reflexivity. Qed.
Theorem crc_table_word_correct : forall t i, (t < 5)%nat -> (i < 256)%nat ->
  bv_unsigned (crc_table_word t i) = csteps (crc_table_power t) (Z.of_nat i).
Proof.
  intros t i Ht Hi. apply Z.eqb_eq.
  exact (forallb_seq _ 0 256 i (forallb_seq _ 0 5 t crc_tables_checked ltac:(lia)) ltac:(lia)).
Qed.
