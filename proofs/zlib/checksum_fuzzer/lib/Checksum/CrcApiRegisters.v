(** The three completed combine API proofs for arbitrary driver register maps. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import
  PropExec Exec MState Mem Regs6ss.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import
  CrcLib CrcGenModel CrcGen CrcOp CrcCombine Img0 RegisterBridge.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YO0d.
Open Scope bv_scope.

Definition crc_api_post (answer : Z) (R F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (actual : machine_state) : Prop :=
  exists canonical,
    crc_return_post answer
      (reg_get R 1) (reg_get R 2) (reg_get R 3) (reg_get R 4)
      (reg_get R 8) (reg_get R 9)
      (reg_get R 18) (reg_get R 19) (reg_get R 20) (reg_get R 21)
      (reg_get R 22) (reg_get R 23) (reg_get R 24) (reg_get R 25)
      (reg_get R 26) (reg_get R 27) F fc m canonical /\ ms_eqv canonical actual.

Theorem crc_gen_arbitrary_registers : forall R F fc m,
  bytes_at rsegs m X2N_TAB x2n_bytes -> (bv_unsigned (reg_get R 10) <= 1048576)%Z ->
  evt rsegs (crc_api_post (combine_gen_model (bv_unsigned (reg_get R 10))) R F fc m)
    (MS R F (Z_to_bv 64 0x14ccc) fc None m (seg_rom rsegs)).
Proof.
  intros R F fc m HT Hn. unfold crc_api_post.
  eapply canonical_contract_transport.
  unfold canonical_register_state. cbn [MS]. unfold mkR_of.
  apply crc32_combine_gen_table_spec;assumption.
Qed.
Theorem crc_op_arbitrary_registers : forall R F fc m,
  (bv_unsigned (reg_get R 10) < 2^32)%Z ->
  (bv_unsigned (reg_get R 11) < 2^32)%Z ->
  (0 < bv_unsigned (reg_get R 12) < 2^32)%Z ->
  evt rsegs (crc_api_post
    (combine_op_model (bv_unsigned (reg_get R 10)) (bv_unsigned (reg_get R 11))
      (bv_unsigned (reg_get R 12))) R F fc m)
    (MS R F (Z_to_bv 64 0x14d6c) fc None m (seg_rom rsegs)).
Proof.
  intros R F fc m H0 H1 H2. unfold crc_api_post.
  eapply canonical_contract_transport.
  unfold canonical_register_state. cbn [MS]. unfold mkR_of.
  apply crc32_combine_op_any_memory_spec;assumption.
Qed.
Theorem crc_combine_arbitrary_registers : forall R F fc m,
  bytes_at rsegs m X2N_TAB x2n_bytes ->
  (bv_unsigned (reg_get R 10) < 2^32)%Z ->
  (bv_unsigned (reg_get R 11) < 2^32)%Z ->
  (bv_unsigned (reg_get R 12) <= 1048576)%Z ->
  evt rsegs (crc_api_post
    (combine_op_model (bv_unsigned (reg_get R 10)) (bv_unsigned (reg_get R 11))
      (combine_gen_model (bv_unsigned (reg_get R 12)))) R F fc m)
    (MS R F (Z_to_bv 64 0x14bf0) fc None m (seg_rom rsegs)).
Proof.
  intros R F fc m HT H0 H1 Hn. unfold crc_api_post.
  eapply canonical_contract_transport.
  unfold canonical_register_state. cbn [MS]. unfold mkR_of.
  apply crc32_combine_spec;assumption.
Qed.

Lemma crc_api_post_value : forall answer R F fc m actual,
  crc_api_post answer R F fc m actual -> ms_reg actual 10 = Z_to_bv 64 answer.
Proof.
  intros answer R F fc m actual [canonical [HC HE]].
  destruct HC as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & HS & _).
  subst canonical. pose proof (ms_reg_eqv _ _ 10 HE) as V.
  change (Z_to_bv 64 answer = ms_reg actual 10) in V. symmetry. exact V.
Qed.
Lemma crc_api_post_fields : forall answer R F fc m actual,
  crc_api_post answer R F fc m actual ->
  ms_pc_val actual = ret_pc (reg_get R 1) /\ ms_fregs actual = F /\
  ms_svc_pending actual = None /\ ms_resv actual = None /\ ms_fcsr actual = fc /\
  ms_mem actual = m /\ ms_rom actual = seg_rom rsegs.
Proof.
  intros answer R F fc m actual [canonical [HC HE]].
  destruct HC as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & HS & _).
  subst canonical. destruct HE as (_ & HF & HP & HV & HR & HC & HM & HO).
  change (F = ms_fregs actual) in HF.
  change (ret_pc (reg_get R 1) = ms_pc_val actual) in HP.
  change (None = ms_svc_pending actual) in HV.
  change (None = ms_resv actual) in HR.
  change (fc = ms_fcsr actual) in HC.
  change (m = ms_mem actual) in HM.
  change (seg_rom rsegs = ms_rom actual) in HO.
  repeat split;symmetry;assumption.
Qed.
Lemma crc_api_post_saved : forall answer R F fc m actual,
  crc_api_post answer R F fc m actual -> forall r,
  YO0d.callee_saved r -> ms_reg actual (Z_to_bv 5 r) = reg_get R (Z_to_bv 5 r).
Proof.
  intros answer R F fc m actual [canonical [HC HE]] r HR.
  destruct HC as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & HS & _).
  subst canonical. rewrite <- (ms_reg_eqv _ _ (Z_to_bv 5 r) HE).
  unfold YO0d.callee_saved in HR.
  assert (E : (r=2 \/ r=3 \/ r=4 \/ r=8 \/ r=9 \/ r=18 \/ r=19 \/ r=20 \/
    r=21 \/ r=22 \/ r=23 \/ r=24 \/ r=25 \/ r=26 \/ r=27)%Z) by lia.
  repeat destruct E as [E|E];subst r;reflexivity.
Qed.
