(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "with_vmmaps"; "VmMaps"; "event"; "m_vm_lazy"; "vm_forget_range"; "with_vm_backing"; "m_fds"; "m_fs"; "m_halted"; "m_stdin"; "m_tid"; "m_vmmaps"; "vm_add_lazy"; "FdEntry"; "InputStream"; "m_vm_materialized"; "vm_backing_used"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA"; "erase_mat"; "KxA"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "list"; "nil"; "prod"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "with_mmap_backing"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "stableA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition erase_mat (md : Model) : Model := ltac2:(tb__ "0|0|
S6S4Vmd;A1S17S1cQ40A1A1Vmd;A3").

Lemma erase_mat_with_vm_backing : ltac2:(tb__ "0|1|
S16S18S1cQ40A1M0G0A2A1S16G0A1S0S14S0S12S6R3R2R1A3A1S12S6R3S17G0A1R1A3A1A3Fmd;Fp;Fl;").
Proof. intros l p md. unfold erase_mat. autorewrite with model. reflexivity. Qed.

Definition KxA (m : Model) (B : Z) : jpredA := ltac2:(tb__ "0|1|
S1dS16S1cQ40A1A1S16S3A1M0S0S15S14G0R2S17S3A1A3S15S14S0S12R1A1S12Vm;A1A3S20S1fR1R3A2VB;A2A2A2Lmd;Ltr;Ltp;L_;").

Lemma stableA_KxA : ltac2:(tb__ "0|0|
S16S22A1S1bS0S1aS23R4R3S13R2R1A2A3FB;Fm;Fn;Fsegs;").
Proof.
  intros segs n m B.
  apply (stableA_of_proj segs n erase_mat (fun _ tp tr b z => tr = [] /\ b = erase_mat m /\ z <= B)).
  - intros md l p. apply erase_mat_with_vm_backing.
  - intros; assumption.
Qed.

Lemma KxA_nil : ltac2:(tb__ "0|1|
S0S1aS1dS16S1cQ40A1A1S16S3A1M0S0S13R6R5R4R3R2R1A6S14G0R3S17S3A1A3F_;Fmd;Ftr;Ftp;Frho;FB;Fm;").
Proof. intros m B rho tp tr md (H & _). exact H. Qed.

Lemma KxA_mono : ltac2:(tb__ "0|0|
S0S1aS1aS1dS16S1cQ40A1A1S16S3A1S0S20R6R5A2S13R8R7R5R4R3R2A6S13R9R7R6R5R4R3A6F_;F_;Fmd;Ftr;Ftp;Frho;FB';FB;Fm;").
Proof. intros m B B' rho tp tr md HB (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. lia. Qed.

Lemma erase_mat_eq_fields : ltac2:(tb__ "0|2|
S0S0S14S0S12R2A1S12R1A1A3S15S14S2ScR3A1ScR2A1A3S15S14S16S18S1cQ40A1M0G0A2A1S4R3A1S4R2A1A3S15S14S16S18G0SeA2A1S7R3A1S7R2A1A3S15S14S19G0A1M1S9R3A1S9R2A1A3S15S14G1SbR3A1SbR2A1A3S15S14S21S8R3A1S8R2A1A3S14SfSaR3A1SaR2A1A3A2A2A2A2A2A2F_;Fm;Fmd;").
Proof.
  intros md m H. unfold erase_mat in H.
  repeat split.
  - apply (f_equal m_vmmaps) in H. autorewrite with model in H. exact H.
  - apply (f_equal m_vm_lazy) in H. autorewrite with model in H. exact H.
  - apply (f_equal m_fds) in H. autorewrite with model in H. exact H.
  - apply (f_equal m_halted) in H. autorewrite with model in H. exact H.
  - apply (f_equal m_tid) in H. autorewrite with model in H. exact H.
  - apply (f_equal m_fs) in H. autorewrite with model in H. exact H.
  - apply (f_equal m_stdin) in H. autorewrite with model in H. exact H.
Qed.

Lemma erase_mat_shape : ltac2:(tb__ "0|0|
S0S0S14S0S12R2A1S12R1A1A3S14S0R3S6S4R2A1S10R3A1R2A3A3F_;Fm;Fmd;").
Proof.
  intros md m H. unfold erase_mat in H.
  destruct md as [fd [maps lz mat] io fs proc lim tm].
  destruct m as [fd' [maps' lz' mat'] io' fs' proc' lim' tm'].
  unfold with_vm_backing, m_vmmaps, m_vm_lazy, m_vm_materialized in *. cbn in *.
  injection H as -> -> -> -> -> -> -> ->. reflexivity.
Qed.

Lemma erase_mat_cong_lazy : ltac2:(tb__ "0|1|
S0S0S2S1cQ40A1M0G0S14S0S12R5A1S12R4A1A3S14S0S12SdR3R2S1R4R6A2A3A1S12SdR3R2S1R4R5A2A3A1A3F_;Fn;Fa;Fh;Fm;Fmd;").
Proof.
  intros md m h a n H. rewrite (erase_mat_shape md m H).
  destruct m as [fd' [maps' lz' mat'] io' fs' proc' lim' tm']. reflexivity.
Qed.
Lemma erase_mat_cong_vmmaps : ltac2:(tb__ "0|0|
S0S0S2S14S0S12R3A1S12R2A1A3S14S0S12S1R2R4A2A1S12S1R2R3A2A1A3F_;Fh;Fm;Fmd;").
Proof.
  intros md m h H. rewrite (erase_mat_shape md m H).
  destruct m as [fd' [maps' lz' mat'] io' fs' proc' lim' tm']. reflexivity.
Qed.
Lemma erase_mat_cong_backing : ltac2:(tb__ "0|1|
S0S0S1cQ40A1M0S2G0G0S14S0S12R6A1S12R5A1A3S14S0S12S1eR5R3R2S1R4R7A2A4A1S12S1eR5R3R2S1R4R6A2A4A1A3F_;Fn;Fa;Fh;Fflags;Fm;Fmd;").
Proof.
  intros md m flags h a n H. unfold with_mmap_backing. destruct (mmap_noreserve_b flags).
  - apply erase_mat_cong_lazy. exact H.
  - apply erase_mat_cong_vmmaps. exact H.
Qed.
Lemma erase_mat_cong_forget : ltac2:(tb__ "0|0|
S0S0S2S1aS1aS14S0S12R5A1S12R4A1A3S14S0S12S5R3R2S1R4R6A2A3A1S12S5R3R2S1R4R5A2A3A1A3F_;Fhi;Flo;Fh;Fm;Fmd;").
Proof.
  intros md m h lo hi H. rewrite (erase_mat_shape md m H).
  destruct m as [fd' [maps' lz' mat'] io' fs' proc' lim' tm']. reflexivity.
Qed.
Lemma erase_mat_cong_forget0 : ltac2:(tb__ "0|0|
S0S0S1aS1aS14S0S12R4A1S12R3A1A3S14S0S12S5R3R2R5A3A1S12S5R3R2R4A3A1A3F_;Fhi;Flo;Fm;Fmd;").
Proof.
  intros md m lo hi H. rewrite (erase_mat_shape md m H).
  destruct m as [fd' [maps' lz' mat'] io' fs' proc' lim' tm']. reflexivity.
Qed.
Lemma paid_nil_used : ltac2:(tb__ "0|0|
S0S14S1aS1fR1S17S1cQ40A1A1A2S11R1A1A3Fmd;").
Proof. intros md. unfold paid, unpaid. cbn. lia. Qed.

Lemma erase_mat_idem : ltac2:(tb__ "0|1|
S0S14S0S12S12R1A1M0A1G0A3Fmd;").
Proof. intros md. unfold erase_mat. autorewrite with model. reflexivity. Qed.

Lemma wx_segs_nowrap_A : wx_segs_nowrap segsA.
Proof.
  intros seg Hin Hwx. unfold segsA in Hin. cbn in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hwx |- *; try discriminate; lia.
Qed.
