(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "pair"; "option"; "Some"; "prod"; "nat"; "nil"; "bool"; "None"; "true"; "cons"; "app"; "snd"; "fst"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "SyscallEffect"; "m_halted"; "materialize_model_accesses"; "ExitEv"; "m_fs"; "SyscallInput"; "m_vm_lazy"; "m_vm_materialized"; "m_vmmaps"; "syscall_effect_accesses"; "vm_backing_used"; "FdEntry"; "MemCopy"; "VmMaps"; "mkEffectU"; "with_fds"; "with_halted"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "False"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "sys_input"; "cfg_model"; "SError"; "advance_past_svc"; "apply_effect"; "cfg_ms"; "sstep"; "unmodeled_at"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_svc_pending"; "ms_read_byte"; "MachineOk"; "machine_result"; "ms_gpr"; "ms_pc"; "step"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "ss_next"; "ss_pc"; "sv"; "reg_sv"; "eval"; "ss_objs"; "obj_range"; "sobj"; "dflt_writable"; "holds"; "mem_match"; "ob_dflt"; "regs_match"; "sprop"; "ss_facts"; "sv_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "axwf"; "shadow_ok"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA.SC"; "smatch_pendingA"; "vm_same"; "only_okA"; "SPpA"; "ok_pframeA"; "A_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "wstep"; "etriple"; "tcons"; "triple1"; "assn"; "ok_src"; "ok_tgt"; "w_tr"; "triple"; "w_cfg"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "jpredA"; "SPA"; "stableA"; "smatchA"; "ok_frameA"; "hidz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "MI"; "hid"; "mat_equiv"; "headroom"; "paid"; "md_after"; "virt"; "vmd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "after_sys"; "exit_code"; "exited"; "only_ok"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Restrict"; "ranges_avoid"; "range_avoids"; "@LinuxProcessSemantics.LinuxProcessSem.Specs"; "syscall_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "pending_of"; "smatch_pending"; "S_after"; "@LinuxProcessSemantics.LinuxProcessSem.Monad"; "Ok"; "Unmodeled"; "outcome"; "@Corelib.Init.Peano"; "lt"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit"; "ok_halted"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymComplete SymCall SymExit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Section SC.
Variable segs : list Segment.

Local Notation wstep := (wstep segs).

Definition smatch_pendingA (rho : valuation) (tp : list word) (A : axst) (w : list event * config) : Prop := ltac2:(tb__ "0|2|
S22S84Vsegs;Vrho;S4fVA;A1S75Vtp;Vw;A2A4S22S6fVsegs;S2dScS0SfA1S2aVw;A3M0A1M1Vtp;A3S22S21S7S51VA;A1S9A3S22S52Vrho;VA;A2S6dG1Vtp;S31G0A1A3A2A2A2A2").

Definition SPpA (J : jpredA) (A : axst) (rho : valuation) (tp : list word) : assn := ltac2:(tb__ "0|0|
S5aS22S54Vrho;Vtp;VA;R1A4VJ;Vrho;Vtp;S62R1A1S2dS64R1A1A1A4A2Lw;").

Lemma smatch_pendingA_sp : ltac2:(tb__ "0|1|
S3cS0S27Q40A1A1S50S0SfA1M0S34SeS54R6R5R4S1G0S2aR3S2bR2R1A2A4A4S84Vsegs;R7S4fR5A1S1G0S2aR4S2bS6eR2R6R3A3S76R2A1A2A4A4F_;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using . intros rho tp A tr ms md [H _]. rewrite virt_unfold in H. exact H. Qed.

Lemma smatch_pendingA_MI : ltac2:(tb__ "0|1|
S3cS0S27Q40A1A1S50S0SfA1M0S34SeS54R6R5R4S1G0S2aR3S2bR2R1A2A4A4S6fVsegs;R2R6A3F_;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using . intros rho tp A tr ms md (_ & H & _). exact H. Qed.

Lemma smatch_pendingA_axwf : ltac2:(tb__ "0|0|
S3cS0S27Q40A1A1S50S4S0SfA1S2aA2S54R4R3R2R1A4S21S7S51R3A1S9A3F_;Fw;FA;Ftp;Frho;").
Proof using . intros rho tp A w (_ & _ & H & _). exact H. Qed.

Lemma smatch_pendingA_shadow : ltac2:(tb__ "0|0|
S3cS0S27Q40A1A1S50S4S0SfA1S2aA2S54R4R3R2R1A4S52R5R3A2F_;Fw;FA;Ftp;Frho;").
Proof using . intros rho tp A w (_ & _ & _ & H & _). exact H. Qed.

Lemma smatch_pendingA_hidz : ltac2:(tb__ "0|1|
S3cS0S27Q40A1A1S50S0SfA1M0S34SeS54R6R5R4S1G0S2aR3S2bR2R1A2A4A4S6dR2R6R3A3F_;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using . intros rho tp A tr ms md (_ & _ & _ & _ & H). exact H. Qed.

Lemma smatch_pendingA_swf : ltac2:(tb__ "0|0|
S3cS0S27Q40A1A1S50S4S0SfA1S2aA2S54R4R3R2R1A4S21S7S4eS4fR3A1A1S9A3F_;Fw;FA;Ftp;Frho;").
Proof using . intros rho tp A [tr [ms md]] H. exact (smatch_pending_swf segs _ _ _ _ _ (smatch_pendingA_sp _ _ _ _ _ _ H)). Qed.

Lemma smatch_pendingA_pending : ltac2:(tb__ "0|2|
S3cS0S27Q40A1M0A1S50S0SfA1M1S34SeS54R6R5R4S1G1S2aR3S2bR2R1A2A4A4S21S2G0A1S35R3A1S3G0S42R7S41S4fR5A1Z11A2A2A2A3F_;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md H. pose proof (smatch_pending_pending segs _ _ _ _ _ (smatch_pendingA_sp _ _ _ _ _ _ H)) as X.
  rewrite vms_svc_pending in X. exact X.
Qed.

Lemma smatch_pendingA_halted : ltac2:(tb__ "0|2|
S3cS0S27Q40A1M0A1S50S0SfA1M1S34SeS54R6R5R4S1G1S2aR3S2bR2R1A2A4A4S21S2G0A1S11R2A1S8G0A1A3F_;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md H. pose proof (smatch_pending_halted segs _ _ _ _ _ (smatch_pendingA_sp _ _ _ _ _ _ H)) as X.
  apply (proj1 (model_idle_vmd md)). exact X.
Qed.

Lemma smatch_pendingA_gpr : ltac2:(tb__ "0|2|
S3cS0S27Q40A1M0A1S50S0SfA1M1S34SeS5S54R7R6R5S1G1S2aR4S2bR3R2A2A4A4S89R2U6A2S21G0S39R5R3A2S42R9S41S4fR7A1S7eZaS7fR3A1A2A2A2A3F_;F_;Fi;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md i H Hi. rewrite <- (vms_gpr md tp). eapply smatch_pending_gpr; [exact (smatch_pendingA_sp _ _ _ _ _ _ H) | exact Hi].
Qed.

Lemma smatch_pendingA_regs : ltac2:(tb__ "0|1|
S3cS0S27Q40A1A1S50S0SfA1M0S34SeS54R6R5R4S1G0S2aR3S2bR2R1A2A4A4S4aR7S4fR5A1R3A3F_;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md H. pose proof (smatch_pending_regs segs _ _ _ _ _ (smatch_pendingA_sp _ _ _ _ _ _ H)) as X.
  unfold regs_match in X |- *. rewrite vms_regs in X. exact X.
Qed.

Lemma smatch_pendingA_pc : ltac2:(tb__ "0|3|
S3cS0S27Q40M0A1M1A1S50S0SfA1M2S34SeS54R6R5R4S1G2S2aR3S2bR2R1A2A4A4S21G1S3aR3A1S28G0S3fS4fR5A1A1A2A3F_;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md H. pose proof (smatch_pendingA_sp _ _ _ _ _ _ H) as (_ & Hpc & _). cbn [fst snd cfg_ms cfg_model] in Hpc.
  rewrite vms_pc in Hpc. exact Hpc.
Qed.

Lemma smatch_pendingA_facts : ltac2:(tb__ "0|0|
S3cS0S27Q40A1A1S50S4S0SfA1S2aA2S54R4R3R2R1A4S8aS4bS47R5A1S4cS4fR3A1A1A3F_;Fw;FA;Ftp;Frho;").
Proof using . intros rho tp A [tr [ms md]] H. exact (smatch_pending_facts segs _ _ _ _ _ (smatch_pendingA_sp _ _ _ _ _ _ H)). Qed.

Lemma smatch_pendingA_mem : ltac2:(tb__ "0|1|
S3cS0S27Q40A1A1S50S0SfA1M0S34SeS54R6R5R4S1G0S2aR3S2bR2R1A2A4A4S48Vsegs;R7S43S4fR5A1A1S6eR2R6R3A3A4F_;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using . intros rho tp A tr ms md H. exact (smatch_pending_mem segs _ _ _ _ _ (smatch_pendingA_sp _ _ _ _ _ _ H)). Qed.

Lemma vms_read_byte_someA : ltac2:(tb__ "0|4|
S3cS0S27Q40A1M0A1S50S0SfA1M1S34SeG0S27Q8A1M2S54R8R7R6S1G1S2aR5S2bR4R3A2A4A4S21S2G2A1M3S36S6eR4R8R5A3R3A2S3G2R2A2A3S21G3S36R6R4A2S3G2R3A2A3F_;F_;Fb;Fa;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md a b HspA H. pose proof (smatch_pendingA_sp _ _ _ _ _ _ HspA) as Hsp. pose proof (smatch_pendingA_MI _ _ _ _ _ _ HspA) as HMI.
  pose proof (smatch_pending_rom segs _ _ _ _ _ Hsp) as Hrom.
  unfold ms_read_byte in H |- *. rewrite vms_mem in H.
  destruct (hid md tp a) eqn:Hh; [|rewrite vms_rom in H; exact H].

  exfalso. pose proof (Hrom a) as R. rewrite R in H. unfold image_byte in H.
  pose proof (hid_off_segments segs md tp (MI_lazy_clear segs md tp HMI) a Hh) as Hoff.
  unfold memory_read in H. replace (Z.of_N 1) with 1 in H by reflexivity.
  rewrite Hoff in H. discriminate.
Qed.

Lemma vms_pending_of : ltac2:(tb__ "0|0|
SeS0S27Q40A1A1S34S21S34S6eR3R2S83R1A1A3S83S6eR3R2R1A3A1A3Fms;Ftp;Fmd;").
Proof using . intros. reflexivity. Qed.

Lemma ecall_succA : ltac2:(tb__ "0|4|
S3cS0S27Q40A1A1S50S0SfA1M0S34SeS6bVsegs;R6R5R4S1G0S2aR3S2bR2R1A2M1A4A5S21S2S65A1S77Vsegs;S3fS4fR5A1A1A2S3S65S66A2A3S23S34S34S23SeSeS22S5bVsegs;S1G0S2aR7S2bR6R5A2A4S1G0S2aR7G1A4M2A3S22S5aS5bVsegs;S1G0S2aR8S2bR7R6A2A4R1A3S21S5aR2S1G0S2aR9S2bR4R3A2A4A3F_;Fw';S22S71Vsegs;R9R5R1A4S22S54RaR9R8G2A4S21S38S34A1S3bVsegs;S6eR5R9R6A3M3A2S37S34S83G3A1A2A3A2A2A2A2Lmd';A2Lms';A2F_;F_;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md HsmA Hi. pose proof HsmA as (Hsm & HMI & Hwf & Hsh & Hhz).
  pose proof (ecall_step segs rho (ax_S A) tr (vms md tp ms) (vmd md) Hsm Hi) as Hstep.
  pose proof (smatchA_halted segs _ _ _ _ _ _ HsmA) as Hh.
  pose proof (smatchA_pending segs _ _ _ _ _ _ HsmA) as Hp.
  destruct (wstepA_of_step segs tr ms md tp _ HMI Hh Hp Hstep) as (ms' & md' & Hacc & Hw & Hv & Hme & Hhs).
  exists ms', md'. split; [exact Hw|]. split.
  { intros w' Hw'. exact (wstepA_step_inv segs tr ms md ms' md' w' Hh Hp Hacc Hw'). }
  split; [exact Hme|]. split; [|exact Hstep].
  split; [|split; [exact (proj2 (proj2 Hme) HMI) | split; [exact Hwf | split; [exact Hsh|]]]].
  - unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg].
    rewrite (mat_equiv_vmd segs tp md md' Hme), Hv. apply smatch_pending_of. exact Hsm.
  - cbn. intros a Ha. rewrite (mat_equiv_hid segs tp md md' Hme) in Ha. rewrite (Hhs a Ha), (mat_equiv_vmmaps segs tp md md' Hme). exact (Hhz a Ha).
Qed.

Lemma triple1_ecallA : ltac2:(tb__ "0|0|
S5aOF_;S68S50S3cS0S27Q40A1A1S6cVsegs;R5R4A3S6aVsegs;S3eS4fR4A1A1R5A3S21S2S65A1S77Vsegs;S3fS4fR5A1A1A2S3S65S66A2A3S5eVsegs;R8S69Vsegs;R7R6R5R4A5S57R7R6R5R4A4A4F_;F_;F_;Ftp;Frho;FA;FJ;Fok;").
Proof using .
  intros ok J A rho tp Hok Hst Hi. apply triple1_step.
  intros [tr [ms md]] [HsmA Hk]. cbn [w_tr w_cfg fst snd cfg_model] in Hk.
  destruct (ecall_succA rho tp A tr ms md HsmA Hi) as (ms' & md' & Hw & Huniq & Hme & Hsp' & Hstep).
  split.
  - eapply Hok; [exact Hk | eapply smatchA_MI; exact HsmA | eapply smatchA_halted; exact HsmA | eapply smatchA_pending; exact HsmA | exact Hstep].
  - intros w' Hw'. rewrite (Huniq w' Hw'). split; [exact Hsp'|]. cbn. eapply Hst; [apply agree_below_refl | exact Hme | exact Hk].
Qed.

Lemma etriple_ecallA : ltac2:(tb__ "0|0|
S68S50S3cS0S27Q40A1A1S6aVsegs;S3eS4fR3A1A1R4A3S21S2S65A1S77Vsegs;S3fS4fR4A1A1A2S3S65S66A2A3S5cVsegs;S69Vsegs;R6R5R4R3A5S57R6R5R4R3A4A3F_;F_;Ftp;Frho;FA;FJ;").
Proof using .
  intros J A rho tp Hst Hi. apply etriple_step.
  intros [tr [ms md]] [HsmA Hk]. cbn [w_tr w_cfg fst snd cfg_model] in Hk.
  destruct (ecall_succA rho tp A tr ms md HsmA Hi) as (ms' & md' & Hw & Huniq & Hme & Hsp' & Hstep).
  exists (tr, mkCfg ms' md'). split; [exact Hw|]. split; [exact Hsp'|]. cbn.
  eapply Hst; [apply agree_below_refl | exact Hme | exact Hk].
Qed.

Lemma triple1_pendingA : ltac2:(tb__ "0|1|
S4S0SfA1M0S2aA2OFx;S68S50S3cS0S27Q40A1A1S5fG0S34SeS54R6R5R7S1G0S2aR3S2bR2R1A2A4A4R9R7R6R4R2A4S22RbS1G0S2aR5S2bR4R3A2A4A1S5aS5bVsegs;S1G0S2aR6S2bR5R4A2A4R1A3R8R2A1F_;Fw';A2F_;F_;Fmd;Fms;Ftr;S5eVsegs;R7S57R6R5R4R3A4R2A4F_;FQ;Ftp;Frho;FA;FJ;Fok;").
Proof using .
  intros ok J A rho tp Q H. apply triple1_step.
  intros [tr [ms md]] [Hsp Hk]. cbn [w_tr w_cfg fst snd cfg_model] in Hk. exact (H tr ms md Hsp Hk).
Qed.

Lemma etriple_pendingA : ltac2:(tb__ "0|1|
S68S50S3cS0S27Q40A1A1S5aOF_;S0SfA1M0S34SeS54R6R5R7S1G0S2aR3S2bR2R1A2A4A4R9R7R6R4R2A4S23S5aS5aS22S5bVsegs;S1G0S2aR6S2bR5R4A2A4R1A3R7R1A1A2Lw';A2F_;F_;Fmd;Fms;Ftr;S5cVsegs;S57R6R5R4R3A4R2A3F_;FQ;Ftp;Frho;FA;FJ;").
Proof using .
  intros J A rho tp Q H. apply etriple_step.
  intros [tr [ms md]] [Hsp Hk]. cbn [w_tr w_cfg fst snd cfg_model] in Hk. exact (H tr ms md Hsp Hk).
Qed.

Lemma triple1_ecall_detA : ltac2:(tb__ "0|1|
S5aOF_;S68S50S3cS0S27Q40A1A1S5fS6cVsegs;R6R5A3S6aVsegs;S3eS4fR5A1A1R6A3S21S2S65A1S77Vsegs;S3fS4fR6A1A1A2S3S65S66A2A3S0SfA1M0S34SeS54R9R8RaS1G0S2aR3S2bR2R1A2A4A4RcRaR9R4R2A4S22ReS1G0S2aR5S2bR4R3A2A4A1S5aS5bVsegs;S1G0S2aR6S2bR5R4A2A4R1A3RbR2A1F_;Fw';A2F_;F_;Fmd;Fms;Ftr;S5eVsegs;RaS69Vsegs;R9R8R7R6A5R5A4F_;F_;F_;F_;FQ;Ftp;Frho;FA;FJ;Fok;").
Proof using .
  intros ok J A rho tp Q Hok Hst Hi H.
  eapply triple1_seq_l; [apply triple1_ecallA; [exact Hok | exact Hst | exact Hi]|].
  apply triple1_triple. apply triple1_pendingA. exact H.
Qed.

Lemma etriple_ecall_detA : ltac2:(tb__ "0|1|
S68S50S3cS0S27Q40A1A1S5aOF_;S6aVsegs;S3eS4fR4A1A1R5A3S21S2S65A1S77Vsegs;S3fS4fR5A1A1A2S3S65S66A2A3S0SfA1M0S34SeS54R8R7R9S1G0S2aR3S2bR2R1A2A4A4RbR9R8R4R2A4S23S5aS5aS22S5bVsegs;S1G0S2aR6S2bR5R4A2A4R1A3R9R1A1A2Lw';A2F_;F_;Fmd;Fms;Ftr;S5cVsegs;S69Vsegs;R8R7R6R5A5R4A3F_;F_;F_;FQ;Ftp;Frho;FA;FJ;").
Proof using .
  intros J A rho tp Q Hst Hi H.
  eapply etriple_seq; [apply etriple_ecallA; [exact Hst | exact Hi]|]. apply etriple_pendingA. exact H.
Qed.

Definition only_okA (i : SyscallInput) (m : Model) : Prop := ltac2:(tb__ "0|1|
S22S24S82Vi;Vm;S87S10A1A3A1S10SeS0SfA1S82Vi;Vm;S86S10R3R2R1A4A3S21S2S27Q40A1M0A1S11R3A1S8G0A1A3S24S21S2SeA1S12R4S19R5A1A2S8SeA1A3A1F_;F_;Fevs;Fm';Feff;A2").

Lemma only_okA_of_inv : ltac2:(tb__ "0|2|
S15SeS88S10A1M0OF_;G0S82R4R3R1A3R3R2A1F_;FR;S24R2S87S10A1A1A1S10SeS0SfA1R6S86S10R3R2R1A4A1S21S2S27Q40A1M1A1S11R3A1S8G1A1A3S24S21S2SeA1S12R4S19R5A1A2S8SeA1A3A1F_;F_;Fevs;Fm';Feff;S56R6R5A2F_;F_;F_;FP;Fm;Fi;").
Proof using .
  intros i m P Hinv Hn Hm. split.
  - intros Hs. exact (Hn (Hinv _ Hs)).
  - intros eff m' evs Hs Hh. exact (Hm _ _ _ (Hinv _ Hs) Hh).
Qed.

Lemma only_okA_of_only_ok : ltac2:(tb__ "0|0|
S15SeS7bR2R1A2S56R3R2A2F_;Fm;Fi;").
Proof using .
  intros i m [Hn Hl]. split; [exact Hn|]. intros eff m' evs Hs Hh.
  rewrite (materialize_model_accesses_no_lazy m' _ (Hl _ _ _ Hs Hh)). discriminate.
Qed.

Lemma pending_no_errorA : ltac2:(tb__ "0|1|
S34SeS27Q40A1M0S0SfA1S21S2G0A1S35R4A1S3G0R2A2A3S56S2cVsegs;R5R3A3R4A2S24S32Vsegs;S2bR6R5A2R3S2eA4A1F_;F_;Fevs;Fx8;Fm;Fms;").
Proof using .
  intros ms m x8 evs Hp [Hok Hm] Hs. inversion Hs; subst; try congruence;
    match goal with H : ms_svc_pending ms = Some ?y |- _ => rewrite Hp in H; inversion H; subst end;
    first [ eapply Hm; eauto | exact (Hok ltac:(assumption)) ].
Qed.

Lemma pending_not_unmodeled_atA : ltac2:(tb__ "0|1|
S34SeS27Q40A1M0S21S2G0A1S35R3A1S3G0R1A2A3S56S2cVsegs;R4R2A3R3A2S24S33Vsegs;S2bR5R4A2A2A1F_;F_;Fx8;Fm;Fms;").
Proof using .
  intros ms m x8 Hp [Hok _] [_ [[Hn _] | (x & Hx & Hs)]]; cbn in *; [congruence|].
  rewrite Hp in Hx. inversion Hx; subst. exact (Hok Hs).
Qed.

Lemma ok_tgt_pendingA : ltac2:(tb__ "0|2|
S0SfA1M0OF_;G0S34SeS27Q40A1M1S5dR5R4A2S21S2G1A1S35R4A1S3G1R2A2A3S56S2cVsegs;R5R3A3R4A2S61Vsegs;R8S1G0S2aR7S2bR6R5A2A4A3F_;F_;F_;Fx8;Fm;Fms;Ftr;FSpec;").
Proof using .
  intros Spec tr ms m x8 Ht Hp Hok. split; [exact Ht|]. cbn. intros evs.
  exact (pending_no_errorA ms m x8 evs Hp Hok).
Qed.

Lemma ok_src_pendingA : ltac2:(tb__ "0|2|
S0SfA1M0OF_;G0S34SeS27Q40A1M1S5dR5R4A2S21S2G1A1S35R4A1S3G1R2A2A3S56S2cVsegs;R5R3A3R4A2S60Vsegs;R8S1G0S2aR7S2bR6R5A2A4A3F_;F_;F_;Fx8;Fm;Fms;Ftr;FSpec;").
Proof using .
  intros Spec tr ms m x8 Ht Hp Hok. split; [exact Ht|]. cbn. exact (pending_not_unmodeled_atA ms m x8 Hp Hok).
Qed.

Definition ok_pframeA (ok : world -> Prop) (J : jpredA) : Prop := ltac2:(tb__ "0|2|
S3cS0S27Q40A1M0A1S0SfA1M1S34SeG0VJ;R6R5R4R2A4S21S2G0A1S35R4A1S3G0R2A2A3S56S2cVsegs;R5R3A3R4A2Vok;S1G1S2aR7S2bR6R5A2A4A1F_;F_;F_;Fx8;Fmd;Fms;Ftr;Ftp;Frho;").

Lemma ok_pframeA_tgt : ltac2:(tb__ "0|1|
S0SfA1M0OF_;S68S3cS0S27Q40A1A1G0SeR5R4R3R2R1A4S5dR7R3A2F_;Fmd;Ftr;Ftp;Frho;S58S61Vsegs;R3A2R2A2F_;FJ;FSpec;").
Proof using . intros Spec J HJ rho tp tr ms md x8 Hk Hp Hok. eapply ok_tgt_pendingA; eauto. Qed.

Lemma ok_pframeA_src : ltac2:(tb__ "0|1|
S0SfA1M0OF_;S68S3cS0S27Q40A1A1G0SeR5R4R3R2R1A4S5dR7R3A2F_;Fmd;Ftr;Ftp;Frho;S58S60Vsegs;R3A2R2A2F_;FJ;FSpec;").
Proof using . intros Spec J HJ rho tp tr ms md x8 Hk Hp Hok. eapply ok_src_pendingA; eauto. Qed.

Lemma materialize_nil : ltac2:(tb__ "0|0|
SeS21S2SeA1S12R1S6S4S27Q40A1S5A2A1A2S3SeR1A2A3Fm;").
Proof using .
  intros m. unfold materialize_model_accesses, materialize_accesses. cbn.
  rewrite with_vm_backing_id. reflexivity.
Qed.

Lemma materialize_prepaid : ltac2:(tb__ "0|2|
SeS0S27Q40A1M0A1S0S4G0S5A2A1S6fVsegs;R3R2A3S80S70R4R3A2R2A2S22S21S2SeA1S12R5R3A2S3SeS74R5R3A2M1A2A3S22S71Vsegs;R4R5G1A4S6fVsegs;G1R4A3A2A2F_;F_;Faccs;Ftp;Fm;").
Proof using .
  intros m tp accs HMI Hav. split; [eapply materialize_model_accesses_prepaid; eassumption|].
  split; [eapply mat_equiv_after; eassumption | eapply MI_after; eassumption].
Qed.

Lemma range_in_obj_avoidsA : ltac2:(tb__ "0|3|
S3cS0S27Q40M0A1M1A1S50S0SfA1M2S34SeS45G1S5S54R9R8R7S1G2S2aR6S2bR5R4A2A4A4S8cS45R4S43S4fR8A1A1A3S21S7S46S49R5A1A1S9A3S7cSdS67S67S44RcR6A2A3S29G0R5A2A2S7cS7eS29G0R6A2S7fR5A1A2ScS67S67S44RdR7A2A3A2S81S70R9RdA2R7R6A3F_;F_;F_;F_;F_;Fn;Fa;Fo;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md o a n HspA Hin Hdw Hlo Hhi k Hk.
  pose proof (smatch_pendingA_mem _ _ _ _ _ _ HspA) as (Hall & _ & _).
  pose proof (smatch_pendingA_MI _ _ _ _ _ _ HspA) as HMI.
  pose proof (proj1 (Forall_forall _ _) Hall o Hin) as (HB & Hw & _).
  unfold obj_range in Hlo, Hhi. cbn [fst snd] in Hlo, Hhi.
  set (b := bv_unsigned (eval rho (ob_base o))) in *.
  pose proof (urange a) as Ra.
  specialize (Hw (bv_unsigned a + Z.of_nat k - b) ltac:(lia) Hdw).
  replace (Z_to_bv 64 (b + (bv_unsigned a + Z.of_nat k - b))) with (woff a k) in Hw.
  2:{ unfold woff. f_equal. lia. }
  unfold wview in Hw. rewrite vms_mem in Hw.
  destruct (hid md tp (woff a k)) eqn:E; [|reflexivity]. exfalso.
  apply Hw. rewrite (hid_off_segments segs md tp (MI_lazy_clear segs md tp HMI) _ E). reflexivity.
Qed.

Lemma ranges_avoid_cons : ltac2:(tb__ "0|2|
S27Q40A1M0S7F_;G0S5S0S4G0S5A2M1A1S81R4R3R2A3S80R5R2A2S80R6SaG1S1G0S5R5R4A4R3A3A2F_;F_;Fl;Fn;Fa;FH;").
Proof using .
  intros H a n l Ha Hl a' n' [E|Hin]; [injection E as <- <-; exact Ha | exact (Hl a' n' Hin)].
Qed.

Lemma ranges_avoid_nil : ltac2:(tb__ "0|1|
S27Q40A1M0S7F_;S80R1S6S4G0S5A2A1A2FH;").
Proof using . intros H a n []. Qed.

Definition vm_same (md md' : Model) : Prop := ltac2:(tb__ "0|1|
S22S21S1dS18Vmd';A1S18Vmd;A1A3S22S21S0S4S27Q40A1M0G0A2A1S16Vmd';A1S16Vmd;A1A3S21S0G0A1S17Vmd';A1S17Vmd;A1A3A2A2").

Lemma vm_same_refl : ltac2:(tb__ "0|0|
SeS55R1R1A2Fmd;").
Proof using . intros md. repeat split; reflexivity. Qed.

Lemma vm_same_hid : ltac2:(tb__ "0|1|
SeSeS0S27Q40A1M0A1S55R3R2A2S21G0S7Fa;S70R3R2A2S70R4R2A2A3F_;Ftp;Fmd';Fmd;").
Proof using . intros md md' tp (_ & Hl & _). unfold hid. rewrite Hl. reflexivity. Qed.

Lemma vm_same_vms : ltac2:(tb__ "0|0|
SeSeS0S27Q40A1A1S34S55R4R3A2S21S34S6eR4R3R2A3S6eR5R3R2A3A3F_;Fms;Ftp;Fmd';Fmd;").
Proof using . intros md md' tp ms H. unfold vms. rewrite (vm_same_hid md md' tp H). reflexivity. Qed.

Lemma vm_same_used : ltac2:(tb__ "0|0|
SeSeS55R2R1A2S21S67S1aR2A1S1aR3A1A3F_;Fmd';Fmd;").
Proof using . intros md md' (Hm & Hl & Hp). unfold vm_backing_used. rewrite Hm, Hl, Hp. reflexivity. Qed.

Lemma vm_same_paid : ltac2:(tb__ "0|0|
SeSeS0S27Q40A1A1S55R3R2A2S21S67S73R3R2A2S73R4R2A2A3F_;Ftp;Fmd';Fmd;").
Proof using .
  intros md md' tp H. pose proof H as (Hm & Hl & Hp). unfold paid, unpaid. rewrite (vm_same_used md md' H), Hl, Hp. reflexivity.
Qed.

Lemma vm_same_headroom : ltac2:(tb__ "0|0|
SeSeS0S27Q40A1A1S55R3R2A2S21S67S72R3R2A2S72R4R2A2A3F_;Ftp;Fmd';Fmd;").
Proof using . intros md md' tp H. unfold headroom. rewrite (vm_same_paid md md' tp H), (proj1 H). reflexivity. Qed.

Lemma vm_same_MI : ltac2:(tb__ "0|0|
SeSeS0S27Q40A1A1S55R3R2A2S6fVsegs;R4R2A3S6fVsegs;R4R3A3F_;F_;Ftp;Fmd';Fmd;").
Proof using .
  intros md md' tp H (HW & HT & Hmat & Hsub & Hpaid & Hlc & Hivs & Hlm & Htm). pose proof H as (Hm & Hl & Hp).
  unfold MI. rewrite Hp, Hl, Hm, (vm_same_paid md md' tp H).
  split; [exact HW|]. split; [exact HT|]. split; [exact Hmat|]. split; [exact Hsub|]. split; [exact Hpaid|]. split; [exact Hlc|].
  split; [|split].
  - unfold BackingAlgebra.model_ivs_wf in Hivs |- *. rewrite Hm, Hl. exact Hivs.
  - unfold lazy_in_maps in Hlm |- *. rewrite Hm, Hl. exact Hlm.
  - unfold tp_in_maps in Htm |- *. rewrite Hm. exact Htm.
Qed.

Lemma vm_same_with_fds : ltac2:(tb__ "0|0|
SeS0S4S27Q40A1S1bA2A1S55R2S1fR1R2A2A2Ff;Fmd;").
Proof using . intros. repeat split; reflexivity. Qed.
Lemma vm_same_with_halted : ltac2:(tb__ "0|0|
SeS27Q40A1S55R2S20R1R2A2A2Fh;Fmd;").
Proof using . intros. repeat split; reflexivity. Qed.

Lemma smatchA_mat_equiv : ltac2:(tb__ "0|1|
S3cS0S27Q40A1A1S50S0SfA1M0S34SeSeS71Vsegs;R6R2R1A4S6bVsegs;R8R7R6S1G0S2aR5S2bR4R3A2A4A5S6bVsegs;R9R8R7S1G0S2aR6S2bR5R3A2A4A5F_;F_;Fmd';Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md md' Hme (Hsm & HMI & Hwf & Hsh & Hhz).
  split; [|split; [exact (proj2 (proj2 Hme) HMI) | split; [exact Hwf | split; [exact Hsh|]]]].
  - unfold virt in Hsm |- *. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm |- *.
    rewrite (mat_equiv_vmd segs tp md md' Hme), (mat_equiv_vms segs tp md md' ms Hme). exact Hsm.
  - cbn in Hhz |- *. intros a Ha. rewrite (mat_equiv_hid segs tp md md' Hme) in Ha. rewrite (mat_equiv_vmmaps segs tp md md' Hme). exact (Hhz a Ha).
Qed.

Definition A_after (A : axst) (e : sv) : axst := ltac2:(tb__ "0|1|
S53VA;S85S4fVA;A1M0Ve;S43G0A1S3eG0A1A4A2").

Lemma vms_after_sys : ltac2:(tb__ "0|1|
SeS0S27Q40A1M0A1S34G0S21S34S6eR4R3S78R2R1A2A3S78S6eR4R3R2A3R1A2A3Fr;Fms;Ftp;Fmd;").
Proof using . intros. reflexivity. Qed.

Lemma smatchA_after_ret_lit : ltac2:(tb__ "0|3|
S3cS0S27Q40M0A1M1A1S50S0SfA1M2S34SeG2SeG1S54R9R8R7S1G2S2aR6S2bR5R4A2A4A4S21S2G1A1S11R3A1S8G1A1A3S55R6R4A2S6bVsegs;RcRbS59RaS3dS29G0R4A2A1A2S1G2S2aR6S2bS78R8R4A2R5A2A4A5F_;F_;F_;Fr;Fmd';Ftr';Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md tr' md' r HspA Hh' Hvs. pose proof HspA as (Hsp & HMI & Hwf & Hsh & Hhz).
  split; [|split; [eapply vm_same_MI; eauto | split; [unfold axwf in Hwf |- *; cbn; exact Hwf | split; [|]]]].
  - unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg A_after ax_S ax_setS].
    rewrite (vm_same_vms md md' tp _ Hvs), vms_after_sys.
    apply (smatch_after_ret_lit segs rho (ax_S A) tr (vms md tp ms) (vmd md)); [exact Hsp|].
    apply model_idle_vmd. exact Hh'.
  - unfold shadow_ok in Hsh |- *. cbn. exact Hsh.
  - cbn. intros a Ha. rewrite (vm_same_hid md md' tp Hvs) in Ha. cbn. rewrite (proj1 Hvs). exact (Hhz a Ha).
Qed.

Lemma smatchA_after_ret_expr : ltac2:(tb__ "0|2|
S3cS0S27Q40A1M0A1S50S0SfA1M1S34SeG1SeG0S40S54RaR9R8S1G1S2aR7S2bR6R5A2A4A4S21S2G0A1S11R4A1S8G0A1A3S55R7R5A2S21S7S4dS3eS4fRbA1A1R4A2S9A3S21G0S42ReR5A2R6A3S6bVsegs;RfReS59RdR6A2S1G1S2aR9S2bS78RbR7A2R8A2A4A5F_;F_;F_;F_;F_;Fe;Fr;Fmd';Ftr';Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md tr' md' r e HspA Hh' Hvs He Hev. pose proof HspA as (Hsp & HMI & Hwf & Hsh & Hhz).
  split; [|split; [eapply vm_same_MI; eauto | split; [unfold axwf in Hwf |- *; cbn; exact Hwf | split; [|]]]].
  - unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg A_after ax_S ax_setS].
    rewrite (vm_same_vms md md' tp _ Hvs), vms_after_sys.
    apply (smatch_after_ret_expr segs rho (ax_S A) tr (vms md tp ms) (vmd md)); [exact Hsp| |exact He|exact Hev].
    apply model_idle_vmd. exact Hh'.
  - unfold shadow_ok in Hsh |- *. cbn. exact Hsh.
  - cbn. intros a Ha. rewrite (vm_same_hid md md' tp Hvs) in Ha. cbn. rewrite (proj1 Hvs). exact (Hhz a Ha).
Qed.

Lemma apply_effect_ret_only : ltac2:(tb__ "0|2|
S34S27Q40A1M0S21S34S2fS30R2S1eR1S6S4G0S0S27Q8A1A1A2A1S6S4G0G0A2A1M1G1S6S1cA1S6S4G0S5A2A1A6A2A1S78R2R1A2A3Fr;Fms;").
Proof using . intros ms r. apply advance_apply_ret. Qed.

Definition exited_worldA (J : jpredA) (A : axst) (rho : valuation) (tp : list word) : assn := ltac2:(tb__ "0|1|
S5aS23S0SfA1M0G0S23S34S34S23SeSeS22VJ;Vrho;Vtp;R3R1A4S22S54Vrho;Vtp;VA;S1G0S2aR3S2bR2R1A2A4A4S21S5aR4S1G0S2aSbSfR3SaSfS13S79R2A1S14R1A1A2S6SfA1A3A3S2bR2S7aR2R1A2A2A4A3A2A2Lmd;A2Lms;A2Ltr;A2Lw';").

Lemma exit_code_litA : ltac2:(tb__ "0|3|
S3cS0S27Q40M0A1M1A1S50S0SfA1M2S34SeS67S54R7R6R5S1G2S2aR4S2bR3R2A2A4A4S21S40S41S4fR6A1ZaA2S3dR2A1A3S22S7cZ0R3A2S7dR3Z100A2A2S21G1S79R6A1S28G0R4A2A3F_;F_;F_;Fc;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md c HspA H10 Hc.
  pose proof (exit_code_lit segs rho (ax_S A) tr (vms md tp ms) (vmd md) c (smatch_pendingA_sp _ _ _ _ _ _ HspA) H10 Hc) as X.
  unfold exit_code in X |- *. rewrite vms_gpr in X. exact X.
Qed.

Lemma triple_exitA : ltac2:(tb__ "0|3|
S5aOF_;S0SfA1M0OF_;S68S50S3cS0S27Q40M1A1A1S67S6cVsegs;R7R5A3S58R8R6A2S8bR9R8A2S6aVsegs;S3eS4fR7A1A1R8A3S21S2S65A1S77Vsegs;S3fS4fR8A1A1A2S3S65S66A2A3S25S21S40S41S4fR9A1Z11A2M2S3dZ5eA1A3S21S40G2S3dZ5dA1A3A2S21S40S41S4fRaA1ZaA2S3dR7A1A3S22S7cZ0R8A2S7dR8Z100A2A2G0SeRfRdRcR2R1A4R11SbSfR3SaSfS13S28G1RcA2S14R2A1A2S6SfA1A3A3A1F_;Fmd;Ftr;S63Vsegs;R10S69Vsegs;ReRdRcRbA5S5aS26L_;A4F_;F_;F_;F_;F_;F_;F_;F_;F_;Fc;Ftp;Frho;FA;FJ;FSpec;Fok;").
Proof using .
  intros ok Spec J A rho tp c Hokf Hokp Hokh Hst Hi H17 H10 Hc Hspec.
  apply (@triple_seq segs ok _ (exited_worldA J A rho tp)).
  - apply triple1_triple. eapply triple1_ecall_detA; [exact Hokf | exact Hst | exact Hi |].
    intros tr ms md Hsp Hk.
    pose proof (smatch_pendingA_pending _ _ _ _ _ _ Hsp) as Hp.
    pose proof (smatch_pendingA_halted _ _ _ _ _ _ Hsp) as Hh.
    assert (Hno : bv_unsigned (eval rho (reg_sv (ax_S A) 17)) = 93 \/ bv_unsigned (eval rho (reg_sv (ax_S A) 17)) = 94).
    { destruct H17 as [-> | ->]; cbn; [right | left]; reflexivity. }
    split.
    + eapply Hokp; [exact Hk | exact Hp |]. apply only_okA_of_only_ok. apply exit_only_ok. exact Hno.
    + intros w' Hw. rewrite (wstep_exit_inv Hp Hh Hno Hw).
      exists tr, ms, md. split; [exact Hk|]. split; [exact Hsp | reflexivity].
  - apply triple_halt. intros w' (tr & ms & md & Hk & Hsp & ->).
    split.
    + eapply Hokh; [|apply exited_halted].
      exists (tr ++ [ExitEv (Z_to_bv 64 c) (m_fs md)]). split; [exact (Hspec tr md Hk)|].
      rewrite (exit_code_litA rho tp A tr ms md c Hsp H10 Hc). apply is_prefix_refl.
    + intros w'' Hw'. exact (wstep_exited_none Hw').
Qed.

Lemma etriple_exitA : ltac2:(tb__ "0|3|
S68S50S3cS0S27Q40M0A1A1S67S6aVsegs;S3eS4fR4A1A1R5A3S21S2S65A1S77Vsegs;S3fS4fR5A1A1A2S3S65S66A2A3S25S21S40S41S4fR6A1Z11A2M1S3dZ5eA1A3S21S40G1S3dZ5dA1A3A2S21S40S41S4fR7A1ZaA2S3dR4A1A3S22S7cZ0R5A2S7dR5Z100A2A2S5cVsegs;S69Vsegs;RaR9R8R7A5S5aS23S0SfA1M2G2S23SeSeS22RdRbRaR2R1A4S21G2S62R3A1SbSfR2SaSfS13S28G0R9A2S14R1A1A2S6SfA1A3A3A3A2Lmd;A2Ltr;A2Lw';A3F_;F_;F_;F_;F_;Fc;Ftp;Frho;FA;FJ;").
Proof using .
  intros J A rho tp c Hst Hi H17 H10 Hc.
  eapply etriple_ecall_detA; [exact Hst | exact Hi|].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending _ _ _ _ _ _ Hsp) as Hp.
  pose proof (smatch_pendingA_halted _ _ _ _ _ _ Hsp) as Hh.
  assert (Hno : bv_unsigned (eval rho (reg_sv (ax_S A) 17)) = 93 \/ bv_unsigned (eval rho (reg_sv (ax_S A) 17)) = 94).
  { destruct H17 as [-> | ->]; cbn; [right | left]; reflexivity. }
  eexists. split; [exact (@wstep_exit_intro segs tr ms md _ Hp Hh Hno)|].
  exists tr, md. split; [exact Hk|]. cbn. rewrite (exit_code_litA rho tp A tr ms md c Hsp H10 Hc). reflexivity.
Qed.

End SC.
