(** Checked checksum APIs for arbitrary driver register maps, including their frame effects. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import
  PropExec Exec MState Mem Frame Regs6ss.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import
  CrcLib CrcModel CrcTables Crc32 AdlerModel Adler32 Img0 RegisterBridge.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YO0d.
Import ListNotations.
Open Scope Z_scope.
Definition checksum_raw_post (frame answer : Z) (R F : bvmap 5 word) (fc : bv 32) (lo : Z)
  (m : word -> option byte) (final : machine_state) : Prop :=
  exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    final = MS (mkR (reg_get R 1) (reg_get R 2) (reg_get R 3) (reg_get R 4) t0 t1 t2 (reg_get R 8) (reg_get R 9) (Z_to_bv 64 answer) a1 a2 a3 a4 a5 a6 a7 (reg_get R 18) (reg_get R 19) (reg_get R 20) (reg_get R 21) (reg_get R 22) (reg_get R 23) (reg_get R 24) (reg_get R 25) (reg_get R 26) (reg_get R 27) t3 t4 t5 t6) F (ret_pc (reg_get R 1)) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned (reg_get R 2)-frame,bv_unsigned (reg_get R 2))] m m' /\
    wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned (reg_get R 2)).
Definition checksum_register_post frame answer R F fc lo m actual : Prop :=
  exists canonical, checksum_raw_post frame answer R F fc lo m canonical /\ ms_eqv canonical actual.
Theorem crc32_z_registers : forall (R F : bvmap 5 word) (fc : bv 32) (lo B : Z) (inp : list byte) (m : word -> option byte),
  reg_get R 11 = Z_to_bv 64 B -> reg_get R 12 = Z_to_bv 64 (Z.of_nat (length inp)) ->
  bytes_at rsegs m B inp -> bytes_at rsegs m CRC_TABS crc_table_bytes ->
  0 < B -> B+Z.of_nat (length inp) < 2^64 -> Z.of_nat (length inp) <= 1048576 ->
  stk rsegs m lo (bv_unsigned (reg_get R 2)) -> lo+80 <= bv_unsigned (reg_get R 2) ->
  (B+Z.of_nat (length inp) <= bv_unsigned (reg_get R 2)-80 \/ bv_unsigned (reg_get R 2) <= B) ->
  (CRC_TABS+5120 <= bv_unsigned (reg_get R 2)-80 \/ bv_unsigned (reg_get R 2) <= CRC_TABS) ->
  evt rsegs (checksum_register_post 80 (crc_model (bv_unsigned (reg_get R 10) mod 2^32) inp) R F fc lo m)
    (MS R F (Z_to_bv 64 0x14580) fc None m (seg_rom rsegs)).
Proof.
  intros R F fc lo B inp m HP HN INP TABLE HBUF TOP SIZE ST LO DI DT. unfold checksum_register_post.
  eapply canonical_contract_transport.
  unfold canonical_register_state. unfold MS. cbn. unfold mkR_of. cbn.
  rewrite HP,HN.
  apply crc32_z_nonnull_spec;assumption.
Qed.
Theorem crc32_registers : forall (R F : bvmap 5 word) (fc : bv 32) (lo B : Z) (inp : list byte) (m : word -> option byte),
  reg_get R 11 = Z_to_bv 64 B -> reg_get R 12 = Z_to_bv 64 (Z.of_nat (length inp)) ->
  bytes_at rsegs m B inp -> bytes_at rsegs m CRC_TABS crc_table_bytes ->
  0 < B -> B+Z.of_nat (length inp) < 2^64 -> Z.of_nat (length inp) <= 1048576 ->
  stk rsegs m lo (bv_unsigned (reg_get R 2)) -> lo+80 <= bv_unsigned (reg_get R 2) ->
  (B+Z.of_nat (length inp) <= bv_unsigned (reg_get R 2)-80 \/ bv_unsigned (reg_get R 2) <= B) ->
  (CRC_TABS+5120 <= bv_unsigned (reg_get R 2)-80 \/ bv_unsigned (reg_get R 2) <= CRC_TABS) ->
  evt rsegs (checksum_register_post 80 (crc_model (bv_unsigned (reg_get R 10) mod 2^32) inp) R F fc lo m)
    (MS R F (Z_to_bv 64 0x14be4) fc None m (seg_rom rsegs)).
Proof.
  intros R F fc lo B inp m HP HN INP TABLE HBUF TOP SIZE ST LO DI DT. unfold checksum_register_post.
  eapply canonical_contract_transport.
  unfold canonical_register_state. unfold MS. cbn. unfold mkR_of. cbn.
  rewrite HP,HN.
  apply crc32_nonnull_spec;assumption.
Qed.
Theorem adler32_z_registers : forall (R F : bvmap 5 word) (fc : bv 32) (lo B : Z) (inp : list byte) (m : word -> option byte) (a b : Z),
  reg_get R 10 = Z_to_bv 64 (adler_pack a b) -> 0 <= a < ADLER_BASE -> 0 <= b < ADLER_BASE ->
  reg_get R 11 = Z_to_bv 64 B -> reg_get R 12 = Z_to_bv 64 (Z.of_nat (length inp)) ->
  bytes_at rsegs m B inp -> bytes_at rsegs m 0x119e0 (le8 (Z_to_bv 64 ADLER_MAGIC)) ->
  0 < B -> B+Z.of_nat (length inp) < 2^64 -> Z.of_nat (length inp) <= 1048576 ->
  stk rsegs m lo (bv_unsigned (reg_get R 2)) -> lo+32 <= bv_unsigned (reg_get R 2) ->
  (B+Z.of_nat (length inp) <= bv_unsigned (reg_get R 2)-32 \/ bv_unsigned (reg_get R 2) <= B) ->
  (0x119e0+8 <= bv_unsigned (reg_get R 2)-32 \/ bv_unsigned (reg_get R 2) <= 0x119e0) ->
  evt rsegs (checksum_register_post 32 (adler_output inp a b) R F fc lo m)
    (MS R F (Z_to_bv 64 0x14dc8) fc None m (seg_rom rsegs)).
Proof.
  intros R F fc lo B inp m a b HS HA HB HP HN INP TABLE HBUF TOP SIZE ST LO DI DT. unfold checksum_register_post.
  eapply canonical_contract_transport.
  unfold canonical_register_state. unfold MS. cbn. unfold mkR_of. cbn.
  rewrite HS,HP,HN.
  apply adler32_z_nonnull_spec;assumption.
Qed.
Theorem adler32_registers : forall (R F : bvmap 5 word) (fc : bv 32) (lo B : Z) (inp : list byte) (m : word -> option byte) (a b : Z),
  reg_get R 10 = Z_to_bv 64 (adler_pack a b) -> 0 <= a < ADLER_BASE -> 0 <= b < ADLER_BASE ->
  reg_get R 11 = Z_to_bv 64 B -> reg_get R 12 = Z_to_bv 64 (Z.of_nat (length inp)) ->
  bytes_at rsegs m B inp -> bytes_at rsegs m 0x119e0 (le8 (Z_to_bv 64 ADLER_MAGIC)) ->
  0 < B -> B+Z.of_nat (length inp) < 2^64 -> Z.of_nat (length inp) <= 1048576 ->
  stk rsegs m lo (bv_unsigned (reg_get R 2)) -> lo+32 <= bv_unsigned (reg_get R 2) ->
  (B+Z.of_nat (length inp) <= bv_unsigned (reg_get R 2)-32 \/ bv_unsigned (reg_get R 2) <= B) ->
  (0x119e0+8 <= bv_unsigned (reg_get R 2)-32 \/ bv_unsigned (reg_get R 2) <= 0x119e0) ->
  evt rsegs (checksum_register_post 32 (adler_output inp a b) R F fc lo m)
    (MS R F (Z_to_bv 64 0x1518c) fc None m (seg_rom rsegs)).
Proof.
  intros R F fc lo B inp m a b HS HA HB HP HN INP TABLE HBUF TOP SIZE ST LO DI DT. unfold checksum_register_post.
  eapply canonical_contract_transport.
  unfold canonical_register_state. unfold MS. cbn. unfold mkR_of. cbn.
  rewrite HS,HP,HN.
  apply adler32_nonnull_spec;assumption.
Qed.
Theorem crc32_z_null_registers : forall R F fc lo m,
  reg_get R 11 = Z_to_bv 64 0 -> stk rsegs m lo (bv_unsigned (reg_get R 2)) ->
  evt rsegs (checksum_register_post 80 0 R F fc lo m)
    (MS R F (Z_to_bv 64 0x14580) fc None m (seg_rom rsegs)).
Proof.
  intros R F fc lo m HP ST. unfold checksum_register_post.
  eapply canonical_contract_transport.
  unfold canonical_register_state. unfold MS. cbn. unfold mkR_of. cbn.
  rewrite HP. apply crc32_z_null_spec. exact ST.
Qed.
Theorem crc32_null_registers : forall R F fc lo m,
  reg_get R 11 = Z_to_bv 64 0 -> stk rsegs m lo (bv_unsigned (reg_get R 2)) ->
  evt rsegs (checksum_register_post 80 0 R F fc lo m)
    (MS R F (Z_to_bv 64 0x14be4) fc None m (seg_rom rsegs)).
Proof.
  intros R F fc lo m HP ST. unfold checksum_register_post.
  eapply canonical_contract_transport.
  unfold canonical_register_state. unfold MS. cbn. unfold mkR_of. cbn.
  rewrite HP. apply crc32_null_spec. exact ST.
Qed.
Theorem adler32_z_null0_registers : forall R F fc lo m,
  reg_get R 11 = Z_to_bv 64 0 -> reg_get R 12 = Z_to_bv 64 0 -> stk rsegs m lo (bv_unsigned (reg_get R 2)) ->
  evt rsegs (checksum_register_post 32 1 R F fc lo m)
    (MS R F (Z_to_bv 64 0x14dc8) fc None m (seg_rom rsegs)).
Proof.
  intros R F fc lo m HP HN ST. unfold checksum_register_post.
  eapply canonical_contract_transport.
  unfold canonical_register_state. unfold MS. cbn. unfold mkR_of. cbn.
  rewrite HP,HN. apply adler32_z_null0_spec. exact ST.
Qed.
Theorem adler32_null0_registers : forall R F fc lo m,
  reg_get R 11 = Z_to_bv 64 0 -> reg_get R 12 = Z_to_bv 64 0 -> stk rsegs m lo (bv_unsigned (reg_get R 2)) ->
  evt rsegs (checksum_register_post 32 1 R F fc lo m)
    (MS R F (Z_to_bv 64 0x1518c) fc None m (seg_rom rsegs)).
Proof.
  intros R F fc lo m HP HN ST. unfold checksum_register_post.
  eapply canonical_contract_transport.
  unfold canonical_register_state. unfold MS. cbn. unfold mkR_of. cbn.
  rewrite HP,HN. apply adler32_null0_spec. exact ST.
Qed.
Lemma checksum_register_post_value : forall frame answer R F fc lo m actual,
  checksum_register_post frame answer R F fc lo m actual -> ms_reg actual 10 = Z_to_bv 64 answer.
Proof.
  intros frame answer R F fc lo m actual [canonical [HP HE]].
  destruct HP as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m1 & HS & MU & WM & ST). subst canonical.
  pose proof (ms_reg_eqv _ _ 10 HE) as V.
  change (Z_to_bv 64 answer = ms_reg actual 10) in V. symmetry. exact V.
Qed.
Lemma checksum_register_post_fields : forall frame answer R F fc lo m actual,
  checksum_register_post frame answer R F fc lo m actual ->
  ms_pc_val actual = ret_pc (reg_get R 1) /\ ms_fregs actual = F /\
  ms_svc_pending actual = None /\ ms_resv actual = None /\ ms_fcsr actual = fc /\ ms_rom actual = seg_rom rsegs.
Proof.
  intros frame answer R F fc lo m actual [canonical [HP HE]].
  destruct HP as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m1 & HS & MU & WM & ST). subst canonical.
  destruct HE as (_ & HF & HPC & HV & HR & HC & HM & HO).
  change (F = ms_fregs actual) in HF.
  change (ret_pc (reg_get R 1) = ms_pc_val actual) in HPC.
  change (None = ms_svc_pending actual) in HV. change (None = ms_resv actual) in HR.
  change (fc = ms_fcsr actual) in HC. change (seg_rom rsegs = ms_rom actual) in HO.
  repeat split;symmetry;assumption.
Qed.
Lemma checksum_register_post_resources : forall frame answer R F fc lo m actual,
  checksum_register_post frame answer R F fc lo m actual ->
  munch [(bv_unsigned (reg_get R 2)-frame,bv_unsigned (reg_get R 2))] m (ms_mem actual) /\
  wmono rsegs m (ms_mem actual) /\ stk rsegs (ms_mem actual) lo (bv_unsigned (reg_get R 2)).
Proof.
  intros frame answer R F fc lo m actual [canonical [HP HE]].
  destruct HP as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m1 & HS & MU & WM & ST). subst canonical.
  destruct HE as (_ & _ & _ & _ & _ & _ & HM & _).
  change (m1 = ms_mem actual) in HM. rewrite <- HM. split; [exact MU|]. split; [exact WM|exact ST].
Qed.
Lemma checksum_register_post_saved : forall frame answer R F fc lo m actual,
  checksum_register_post frame answer R F fc lo m actual -> forall r,
  YO0d.callee_saved r -> ms_reg actual (Z_to_bv 5 r) = reg_get R (Z_to_bv 5 r).
Proof.
  intros frame answer R F fc lo m actual [canonical [HP HE]] r HR.
  destruct HP as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m1 & HS & MU & WM & ST). subst canonical.
  rewrite <- (ms_reg_eqv _ _ (Z_to_bv 5 r) HE). unfold YO0d.callee_saved in HR.
  assert (E : (r=2 \/ r=3 \/ r=4 \/ r=8 \/ r=9 \/ r=18 \/ r=19 \/ r=20 \/ r=21 \/ r=22 \/ r=23 \/ r=24 \/ r=25 \/ r=26 \/ r=27)%Z) by lia.
  repeat destruct E as [E|E];subst r;reflexivity.
Qed.
