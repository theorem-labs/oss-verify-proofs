(** Derive the Adler reciprocal constant from the unchanged driver ROM premise. *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import Mem Bytes.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcLib AdlerModel.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
  YK11 YK0i YK15 YP09 YO0d YL0g YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib Require Import ZImage ChecksumBridge.
Import ListNotations.
Open Scope Z_scope.
Lemma adler_magic_address_in_ro : forall a,
  0x119e0 <= a < 0x119e0+8 -> in_ro_img src0_msyms a.
Proof.
  intros a Ha. split.
  - exists first_segment. split; [exact first_segment_in|].
    split; [vm_compute;reflexivity|].
    change (65536 <= a < 65536 + 12288). lia.
  - unfold static_owned, ms_lock, ms_libc, ms_got_guard, ms_guard, ms_debruijn, ms_size_classes, ms_small_cnt, ms_med_cnt. cbn [src0_msyms].
    cbv delta [YH03.src0_D_malloc_lock YH03.src0_D_libc YH03.src0_D_got_stack_chk_guard
      YH03.src0_D_stack_chk_guard YH03.src0_D_debruijn32 YH03.src0_D_size_classes
      YH03.src0_D_small_cnt_tab YH03.src0_D_med_cnt_tab].
    cbn. lia.
Qed.
Lemma driver_has_adler_magic : forall mem,
  rodata_ok src0_msyms mem ->
  CM.bytes_at zsegs mem 0x119e0 (le8 (Z_to_bv 64 ADLER_MAGIC)).
Proof.
  intros mem HRO.
  assert (HE : CM.mem_inv zsegs (fun _ => None)).
  { intros a b H. discriminate. }
  assert (REF : CM.bytes_at zsegs (fun _ => None) 0x119e0 (le8 (Z_to_bv 64 ADLER_MAGIC))).
  { apply (ro_table_at zsegs); [exact HE|vm_compute;reflexivity|lia|].
    change (0x119e0+8 <= 2^64). lia. }
  destruct REF as [HA [HL HR]]. split; [exact HA|]. split; [exact HL|].
  intros i Hi. rewrite checksum_effective_byte. rewrite HRO.
  - specialize (HR i Hi). exact HR.
  - apply adler_magic_address_in_ro. change (i < 8)%nat in Hi. lia.
Qed.
Lemma driver_reads_adler_magic : forall mem,
  rodata_ok src0_msyms mem ->
  ov_read_bytes zsegs mem (CM.wa 0x119e0) 8 = Some (le8 (Z_to_bv 64 ADLER_MAGIC)).
Proof.
  intros mem HRO. pose proof (driver_has_adler_magic mem HRO) as H.
  replace (CM.wa 0x119e0) with (CM.wa (0x119e0+Z.of_nat 0)) by reflexivity.
  rewrite (CM.bytes_at_ov_read zsegs mem 0x119e0 _ 0 8 H) by (vm_compute;lia).
  reflexivity.
Qed.
