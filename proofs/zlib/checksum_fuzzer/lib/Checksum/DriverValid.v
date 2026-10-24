(* SPDX-License-Identifier: MIT *)
(** The complete valid-input driver contract, obtained from the actual fuzzer certificate using only the original buffer, ROM, stack and allocator premises. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
  YK11 YK0i YK0o YK15 YP0m YP09 YP0l YP02 YP03
  YM05 YO0i YO0f YO0d YO0o YO05 YO09 YN03 YH02 YI16 YI14 YI5b YI5c
  YL01 YL0g YL0i YL0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib Require Import
  ZImage ZFuzzerBounds ZTraceSpec.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem Fpu.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib Require Import ZAllocator ZValidChecksum ChecksumBridge AdlerBridge ChecksumPost.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require FuzzerRegisters ChecksumRegisters CrcTables Img0.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Frame Regs6ss.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YL0k.
Module FC := OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.FuzzerRegisters.
Module CR := OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.ChecksumRegisters.
Module CF := OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Frame.
Lemma driver_segs_top : forallb (fun s => Z.of_N (seg_base s)+Z.of_N (seg_size s) <=? 0x60000) zsegs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma driver_writable_read : forall m a,
  0x60000 <= a < 2^64 -> writable_at zsegs m a -> exists b, CM.mrd zsegs m (CM.wa a) = Some b.
Proof.
  intros m a HA H. unfold writable_at,wview in H. unfold CM.mrd, CM.wa.
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:E;[exists b;reflexivity|].
  rewrite Z_to_bv_unsigned in H. change (bv_wrap 64 a) with (a mod 2^64) in H.
  rewrite Z.mod_small in H by lia.
  rewrite (find_segment_above zsegs 0x60000 a 1 driver_segs_top ltac:(lia) ltac:(lia)) in H. contradiction.
Qed.
Section DriverValid.
Context {rc : RunCeil} {fx : FPState}.
Theorem checksum_valid_contract : @valid_checksum_contract rc fx.
Proof.
  intros L A regs mem md p n pl b K HP SIZE Hfrm HK.
  pose proof HP as [HP0 [HLEN [HD _]]].
  destruct HP0 as [HM [HW [HB [Hid [Hra [Hal [Hsp [HspHi [HWstack [Htp [HWerrno
    [Hptr [Hsize [Hlive Hro]]]]]]]]]]]]]].
  assert (BUF : 4096 <= p /\ p+n <= alloc_ceiling).
  { destruct Hlive as [[HZ _]|[HN [q [HQ EQ]]]];[lia|].
    pose proof (mr_blocks_range _ _ (aa_laws zlib_API) _ _ _ _ q n HM HQ) as H. rewrite EQ in H. exact H. }
  assert (ST : CF.stk zsegs mem (spZ regs-LIB_STACK) (spZ regs)).
  { unfold CF.stk. split;[pose proof alloc_ceiling_val;lia|]. split;[lia|].
    intros a HA. split;[apply HWstack;exact HA|].
    apply driver_writable_read;[pose proof alloc_ceiling_val;lia|apply HWstack;exact HA]. }
  assert (INPUT : CM.bytes_at zsegs mem p pl).
  { split;[lia|]. split;[rewrite <- HLEN;pose proof alloc_ceiling_lt;lia|].
    intros i HI. rewrite checksum_effective_byte,HD by lia. rewrite Nat2Z.id. reflexivity. }
  pose proof (CrcTables.driver_has_crc_tables mem Hro) as CRC.
  pose proof (driver_has_x2n_table mem Hro) as X2N.
  pose proof (driver_has_adler_magic mem Hro) as MAGIC.
  pose proof (FC.fuzzer_valid_registers regs fp_regs fp_csr (spZ regs-LIB_STACK) p pl mem) as EV.
  change (bv_unsigned (reg_get regs 2)) with (spZ regs) in EV.
  assert (RUN : OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Exec.evt zsegs
    (CR.checksum_register_post 192 0 regs fp_regs fp_csr (spZ regs-LIB_STACK) mem)
    (mkst regs (Z_to_bv 64 LIBPC) mem (seg_rom zsegs))).
  { apply EV;
    [exact Hptr|rewrite <- HLEN;exact Hsize|exact INPUT|exact CRC|exact X2N|exact MAGIC|lia|
     rewrite <- HLEN;pose proof alloc_ceiling_lt;lia|rewrite <- HLEN;exact SIZE|exact ST|
     unfold LIB_STACK;lia|left;rewrite <- HLEN;unfold LIB_STACK in Hsp;lia|
     left;unfold CrcTables.CRC_TABS;unfold LIB_STACK in Hsp;pose proof alloc_ceiling_val;lia|
     left;unfold CrcLib.X2N_TAB;unfold LIB_STACK in Hsp;pose proof alloc_ceiling_val;lia|
     left;unfold LIB_STACK in Hsp;pose proof alloc_ceiling_val;lia]. }
  destruct (mr_model _ _ (aa_laws zlib_API) _ _ _ _ HM) as [Hhalt [Hlazy Hmat]].
  change (realizes zsegs (mkCfg (mkst regs (Z_to_bv 64 LIBPC) mem (seg_rom zsegs)) md) (K (LL 0 (m_fs md) []))).
  eapply checksum_evt_realizes;[exact RUN|exact Hhalt|exact Hlazy|].
  intros final POST.
  pose proof (CR.checksum_register_post_fields _ _ _ _ _ _ _ _ POST) as FIELDS.
  pose proof (CR.checksum_register_post_resources _ _ _ _ _ _ _ _ POST) as [MU [WM STFINAL]].
  pose proof (CR.checksum_register_post_value _ _ _ _ _ _ _ _ POST) as VALUE.
  destruct FIELDS as (HPC & HF & HSVC & HRES & HFCSR & HROM).
  change (reg_get regs 1 = Z_to_bv 64 RA_LIB) in Hra. rewrite Hra in HPC.
  replace (OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.MState.ret_pc (Z_to_bv 64 RA_LIB)) with (Z_to_bv 64 RA_LIB) in HPC by (apply bv_eq;vm_compute;reflexivity).
  assert (SHAPE : final = @mkst fx (ms_regs final) (Z_to_bv 64 RA_LIB) (ms_mem final) (seg_rom zsegs)).
  { destruct final. cbn in HPC,HF,HSVC,HRES,HFCSR,HROM |- *. subst. reflexivity. }
  apply HK. exists fx,L,A,(ms_regs final),(ms_mem final),md.
  split;[f_equal;exact SHAPE|]. split;[exact Hfrm|].
  eapply checksum192_checksum_post with (API:=zlib_API);
    [exact HP| | |exact MU|].
  - change (ms_reg final 10 = Z_to_bv 64 0). exact VALUE.
  - intros r HR.
    assert (RANGE : 0 < r < 32) by (unfold callee_saved in HR;lia).
    assert (NZ : bv_eqb (Z_to_bv 5 r) 0 = false).
    { apply bv_eqb_neq. intro E. apply (f_equal bv_unsigned) in E.
      rewrite Z_to_bv_unsigned in E. change (bv_wrap 5 r = 0) in E.
      change (r mod 32 = 0) in E. rewrite Z.mod_small in E by lia. lia. }
    unfold getr. rewrite NZ.
    pose proof (CR.checksum_register_post_saved _ _ _ _ _ _ _ _ POST r HR) as SAVED.
    unfold ms_reg in SAVED. rewrite NZ in SAVED. exact SAVED.
  - intros a [HA|HA];unfold writable_at;apply WM.
    + exact (HWstack a HA).
    + exact (HWerrno a HA).
Qed.
End DriverValid.
