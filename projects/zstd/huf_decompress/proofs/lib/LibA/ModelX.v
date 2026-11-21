(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (9 recorded proofs replaced by written proofs (same_but_mat_MX, same_but_mat_MX_eq, MX_mat and 6 more); adds m_channel_reader_MX; drops m_stdin_MX). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import AcctCore.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ModelX () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyc59OSSVerify5KrLib4LibA6ModelX2MXC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC4ELinuxProcessSemantics?LinuxProcessSem5State?with_vm_backingK47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4LibA8AcctCore<same_but_matC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K4ELinuxProcessSemantics?LinuxProcessSem5State5Model01I47Corelib4Init9Datatypes4prod00K4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsI4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsI47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State7m_stdinI4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00C59OSSVerify5KrLib4LibA8AcctCore=nonlazy_bytesC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00c59OSSVerify5KrLib4LibA6ModelX5stripC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC4ELinuxProcessSemantics?LinuxProcessSem5State8with_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State8with_tidC4ELinuxProcessSemantics?LinuxProcessSem5State;with_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State:with_stdinC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_add_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_forget_rangeC4ELinuxProcessSemantics?LinuxProcessSem5StateBpage_outside_rangeC46Stdlib5Lists4List6filterK47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option01".
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition strip (m : Model) : Model := with_tid (Z_to_bv 64 1) (with_vm_backing [] [] m).

(* [comment removed for export] *)
Definition MX (m : Model) (mat : list word) : Model := with_vm_backing (m_vm_lazy m) mat m.

Lemma same_but_mat_MX : forall m mat, same_but_mat m (MX m mat).
Proof. intros m mat. reflexivity. Qed.

Lemma same_but_mat_MX_eq : forall m m', same_but_mat m m' -> m' = MX m (m_vm_materialized m').
Proof. intros m m' H. exact H. Qed.

Lemma MX_mat : forall m, MX m (m_vm_materialized m) = m.
Proof. intros [fd [mp lz mt] io fs pr lm tm]. reflexivity. Qed.

Lemma MX_MX : forall m a b, MX (MX m a) b = MX m b.
Proof. intros. reflexivity. Qed.

Lemma m_vm_materialized_MX : forall m mat, m_vm_materialized (MX m mat) = mat.
Proof. reflexivity. Qed.
Lemma m_vm_lazy_MX : forall m mat, m_vm_lazy (MX m mat) = m_vm_lazy m.
Proof. reflexivity. Qed.
Lemma m_vmmaps_MX : forall m mat, m_vmmaps (MX m mat) = m_vmmaps m.
Proof. reflexivity. Qed.
Lemma m_fds_MX : forall m mat, m_fds (MX m mat) = m_fds m.
Proof.
ltac2:(KReplay.run1 (kr_t_ModelX ()) [] "h01mh13matp;1p;2g0000j10Tg000Uj16Tg0013j12Tg001Vj11Tg009cj25Tg00C6j14Tg005_j23Tg0069g006o#0#0#0#0#0#0#6#2R0#1g00Cj,50#1f1#4'3W1W0o"). Qed.
Lemma m_fs_MX : forall m mat, m_fs (MX m mat) = m_fs m.
Proof.
ltac2:(KReplay.run1 (kr_t_ModelX ()) [] "h01mh13matp;1p;2g0000j10Tg000Uj15Tg0013j12Tg001Vj11Tg00Dbj14Tg005_j23Tg0069g006o#0#0#0#0#0#0#5#2#1g00EUf1#4'3W1W0o"). Qed.
Lemma m_tid_MX : forall m mat, m_tid (MX m mat) = m_tid m.
Proof.
ltac2:(KReplay.run1 (kr_t_ModelX ()) [] "h01mh13matp;1p;2g0000j10Tg000Uj16Tg0013j12Tg001Vj11Tg00FCj15Tg00Fej14Tg005_j23Tg0069g006o#0#0#0#0#0#0#6#2R0#1%50f1#4'3W1W0o"). Qed.
Lemma m_halted_MX : forall m mat, m_halted (MX m mat) = m_halted m.
Proof.
ltac2:(KReplay.run1 (kr_t_ModelX ()) [] "h01mh13matp;1p;2g0000j10Tg000Uj16Tg0013j12Tg001Vj11Tg00FCj15Tg00GYj14Tg005_j23Tg0069g006o#0#0#0#0#0#0#6#2R0#1%50f1#4'3W1W0o"). Qed.
Lemma m_channel_reader_MX : forall m mat, m_channel_reader (MX m mat) = m_channel_reader m. Proof. reflexivity. Qed.

Lemma m_stdin_MX : forall m mat, m_stdin (MX m mat) = m_stdin m.
Proof.
ltac2:(KReplay.run1 (kr_t_ModelX ()) [] "h01mh13matp;1p;2g0000j10Tg000Uj15Tg0013j12Tg001Vj11Tg00HPj14Tg005_j23Tg0069g006o#0#0#0#0#0#0#5#2#1g00IFf1#4'3W1W0o"). Qed.
Lemma nonlazy_bytes_MX : forall m mat, nonlazy_bytes (MX m mat) = nonlazy_bytes m.
Proof.
ltac2:(KReplay.run1 (kr_t_ModelX ()) [] "h01mh13matp;1p;2g0000j10Tg000Uj15Tg0013j12Tg001Vj11Tg00JBj14Tg005_j23Tg0069g006o#0#0#0#0#0#0#5#2#1g00KBf1#4'3W1W0o"). Qed.
Lemma strip_MX : forall m mat, strip (MX m mat) = strip m.
Proof.
ltac2:(KReplay.run1 (kr_t_ModelX ()) [] "h01mh13matp;1p;2g0000j10Tg000Uj15Tg0013j12Tg001Vj11Tg00K`j14Tg005_j23Tg0069R0g006o#0#0#0#0#0#0#5#2#1f1#4,30W1W0o"). Qed.

Lemma vm_backing_used_MX : forall m mat,
  vm_backing_used (MX m mat) = nonlazy_bytes m + Z.of_nat (length mat) * page_size.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma with_fds_MX : forall x m mat, with_fds x (MX m mat) = MX (with_fds x m) mat.
Proof.
ltac2:(KReplay.run1 (kr_t_ModelX ()) [] "h01mh13math21xp;1p;2g0000j10Tg000Uj17Tg0013j13Tg009cj22Tg001Vj11Tg00OHj26Tg002nj25Tg005_j24Tg006o#0#0#0#0#0#0#7#3R0g00Cj'2#1g0069R1%10f2f1'6f0'5,41W1W0W2o"). Qed.
Lemma with_tid_MX : forall x m mat, with_tid x (MX m mat) = MX (with_tid x m) mat.
Proof.
ltac2:(KReplay.run1 (kr_t_ModelX ()) [] "h01mh13math21xp;1p;2g0000j10Tg000Uj16Tg0013j12Tg001Vj11Tg00P?j25Tg002nj24Tg005_j23Tg006o#0#0#0#0#0#0#6#2R0g0069R1%10f2f1'5f0'4,31W1W0W2o"). Qed.
Lemma with_halted_MX : forall x m mat, with_halted x (MX m mat) = MX (with_halted x m) mat.
Proof.
ltac2:(KReplay.run1 (kr_t_ModelX ()) [] "h01mh13math21xp;1p;2g0000j10Tg000Uj16Tg0013j12Tg001Vj11Tg00Q6j25Tg002nj24Tg005_j23Tg006o#0#0#0#0#0#0#6#2R0g0069R1%10f2f1'5f0'4,31W1W0W2o"). Qed.
Lemma with_stdin_MX : forall x m mat, with_stdin x (MX m mat) = MX (with_stdin x m) mat.
Proof.
ltac2:(KReplay.run1 (kr_t_ModelX ()) [] "h01mh13math21xp;1p;2g0000j10Tg000Uj16Tg0013j12Tg001Vj11Tg00R0j25Tg002nj24Tg005_j23Tg00IFg0069R0g006o#0#0#0#0#0#0#6#2#1f2f1'5f0'4,30W1W0W2o"). Qed.
Lemma with_vmmaps_MX : forall h m mat, with_vmmaps h (MX m mat) = MX (with_vmmaps h m) mat.
Proof.
ltac2:(KReplay.run1 (kr_t_ModelX ()) [] "h01hh11mh23matp;1p;2g0000j10Tg000Uj16Tg0013j12Tg001Vj11Tg00Rij25Tg002nj24Tg005_j23Tg00AHg0069R0g006o#0#0#0#0#0#0#6#2#1f2f1'5f0'4,30W2W1W0o"). Qed.
Lemma vm_add_lazy_MX : forall a n m mat, vm_add_lazy a n (MX m mat) = MX (vm_add_lazy a n m) mat.
Proof.
ltac2:(KReplay.run1 (kr_t_ModelX ()) [] "h01ah11mh23math31np;1p;3p;2g0000j10Tg000Uj16Tg0013j12Tg001Vj11Tg00Scj35Tg002nj24Tg005_j23Tg006o#0#0#0#0#0#0#6#2R0g0069R1%10f3f2f135f0'4,31W2W1X30W0o"). Qed.
Lemma vm_forget_range_MX : forall lo hi m mat,
  vm_forget_range lo hi (MX m mat) = MX (vm_forget_range lo hi m) (List.filter (page_outside_range lo hi) mat).
Proof. reflexivity. Qed.

Lemma strip_with_fds : forall x m, strip (with_fds x m) = with_fds x (strip m).
Proof.
ltac2:(KReplay.run1 (kr_t_ModelX ()) [] "h01mh11xp;1p;2g0000j10Tg000Uj17Tg0013j12Tg009cj21Tg001Vj16Tg00K`j15Tg00OHj23Tg005_j24Tg006o#0#0#0#0#0#0#7#2g00Cj'1#6g0069R0f1f0#5'3,40W0W1o"). Qed.
Lemma strip_with_tid : forall x m, strip (with_tid x m) = strip m.
Proof.
ltac2:(KReplay.run1 (kr_t_ModelX ()) [] "h01mh11xp;1p;2g0000j10Tg000Uj14Tg0013j12Tg00K`j11Tg005_j23Tg006o#0#0#0#0#0#0#4#2g0069R0f0#1,30W0W1o"). Qed.
Lemma strip_with_halted : forall x m, strip (with_halted x m) = with_halted x (strip m).
Proof.
ltac2:(KReplay.run1 (kr_t_ModelX ()) [] "h01mh11xp;1p;2g0000j10Tg000Uj15Tg0013j12Tg00K`j11Tg00Q6j24Tg005_j23Tg006o#0#0#0#0#0#0#5#2g0069R0f1f0#1'4,30W0W1o"). Qed.
Lemma m_fds_strip : forall m, m_fds (strip m) = m_fds m.
Proof.
ltac2:(KReplay.run1 (kr_t_ModelX ()) [] "h01mp;1p;2g0000j10Tg000Uj16Tg0013j12Tg009cj21Tg001Vj15Tg00C6j14Tg005_j23Tg0069g006o#0#0#0#0#0#0#6#2g00Cj'1#5f0#4'3W0o"). Qed.
Lemma m_fs_strip : forall m, m_fs (strip m) = m_fs m.
Proof.
ltac2:(KReplay.run1 (kr_t_ModelX ()) [] "h01mp;1p;2g00Dbj11Tg005_j20Tg0069g00EUf0#1'0W0o"). Qed.
Lemma m_tid_strip : forall m, m_tid (strip m) = Some (Z_to_bv 64 1).
Proof.
ltac2:(KReplay.run1 (kr_t_ModelX ()) [] "h01mp;1p;2g0000j10Tg000Uj17Tg0013j12Tg00FCj11Tg00W7j16Tg00WUj25Tg00X;j23Tg005_j24Tg0069g006oR0#0#0#0#0#0#0#7R1#2R2#1%60,51,32'4W0o"). Qed.
Lemma m_halted_strip : forall m, m_halted (strip m) = m_halted m.
Proof.
ltac2:(KReplay.run1 (kr_t_ModelX ()) [] "h01mp;1p;2g0000j10Tg000Uj15Tg0013j12Tg00FCj11Tg00GYj14Tg005_j23Tg0069g006o#0#0#0#0#0#0#5#2#1f0#4'3W0o"). Qed.

