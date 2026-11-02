(** Glue from the driver proof's memory/execution predicates to the checksum
    arithmetic proof framework, without strengthening any target premise. *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Mem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Exec.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require CrcLib.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require CrcGen.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Img0.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail Require Import ZImage.
Import ListNotations.
Open Scope Z_scope.
Module CM := OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Mem.
Module CE := OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Exec.
Lemma checksum_effective_byte : forall segs mem a,
  CM.mrd segs mem (CM.wa a) = YP09.mbyte segs mem a.
Proof. reflexivity. Qed.
Lemma checksum_msteps_to_driver : forall segs ms final,
  CE.msteps segs ms final -> YK0i.msteps segs ms final.
Proof.
  intros segs ms final H. induction H as [ms|ms mid final [HS HV] HT IH].
  - constructor.
  - econstructor; eassumption.
Qed.
Lemma checksum_evt_realizes : forall segs ms Q md T,
  CE.evt segs Q ms -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall final, Q final -> YK15.realizes segs (mkCfg final md) T) ->
  YK15.realizes segs (mkCfg ms md) T.
Proof.
  intros segs ms Q md T [final [Hsteps HQ]] Hhalt Hlazy K.
  eapply YK15.rz_msteps; [exact Hhalt|exact Hlazy|apply checksum_msteps_to_driver;exact Hsteps|].
  exact (K final HQ).
Qed.

Definition first_segment : Segment :=
  hd {| seg_base := 0%N; seg_size := 0%N; seg_perms := String.EmptyString;
        seg_bytes := [] |} zsegs.
Lemma first_segment_in : In first_segment zsegs.
Proof.
  unfold first_segment. assert (HNE : zsegs <> []) by (vm_compute; discriminate).
  destruct zsegs as [|s rest]; [contradiction|left;reflexivity].
Qed.
Lemma table_address_in_ro : forall a,
  0x11954 <= a < 0x119d4 -> in_ro_img src0_msyms a.
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
Lemma driver_has_x2n_table : forall mem,
  rodata_ok src0_msyms mem ->
  CM.bytes_at zsegs mem CrcLib.X2N_TAB CrcLib.x2n_bytes.
Proof.
  intros mem HRO.
  assert (HE : Mem.mem_inv zsegs (fun _ => None)).
  { intros a b H. discriminate. }
  destruct (CrcGen.x2n_tab_at (fun _ => None) HE) as [HA [HL HR]].
  split; [exact HA|]. split; [exact HL|].
  intros i Hi. rewrite checksum_effective_byte.
  rewrite HRO.
  - specialize (HR i Hi). exact HR.
  - apply table_address_in_ro. rewrite CrcLib.x2n_bytes_length in Hi.
    unfold CrcLib.X2N_TAB. lia.
Qed.
