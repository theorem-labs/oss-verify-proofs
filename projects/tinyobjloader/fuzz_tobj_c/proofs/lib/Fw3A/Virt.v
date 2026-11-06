(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "prod"; "option"; "nat"; "bool"; "pair"; "length"; "None"; "Some"; "andb"; "app"; "true"; "false"; "negb"; "nil"; "orb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "with_vm_backing"; "m_vm_lazy"; "m_halted"; "m_vmmaps"; "page_mem"; "m_vm_materialized"; "page_size"; "event"; "page_base_of"; "page_in_ranges"; "vm_backing_used"; "vm_limit"; "accesses_pages"; "page_base"; "VmMaps"; "access_pages_acc"; "m_clock"; "m_conn_ix"; "m_creds"; "m_fd"; "m_fds"; "m_fs"; "m_fsys"; "m_io"; "m_lim"; "m_net"; "m_nofile"; "m_pipes"; "m_proc"; "m_rlimit_core"; "m_stdin"; "m_tid"; "m_time"; "page_insert"; "vm_maps"; "Creds"; "FdEntry"; "FdState"; "FsState"; "InputStream"; "IoState"; "LimState"; "NetQueue"; "PipeBuf"; "ProcState"; "TimeState"; "materialize_accesses"; "materialize_model_accesses"; "newly_materialized_pages"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "iff"; "not"; "or"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "MachineOk"; "machine_result"; "ms_svc_pending"; "step"; "ms_fcsr"; "ms_fregs"; "ms_gpr"; "ms_pc"; "ms_reg"; "ms_regs"; "ms_resv"; "ms_rom"; "find_segment"; "@Stdlib.Lists.List"; "In"; "NoDup"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "hid"; "vmd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt.WithImage"; "MI"; "mat_equiv"; "paid"; "unpaid"; "headroom"; "lazy_clear"; "lazy_in_maps"; "tp_in_maps"; "virt"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "of_nat"; "lt"; "mul"; "modulo"; "sub"; "pow"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "mkCfg"; "config"; "mi_account_step"; "SError"; "cfg_model"; "cfg_ms"; "sstep"; "unmodeled_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt.WithImage.Accounting"; "md_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "wstep"; "model_idle"; "w_cfg"; "w_tr"; "@Corelib.Init.Nat"; "add"; "@Corelib.Init.Peano"; "lt"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@LinuxProcessSemantics.Riscv.Prelude"; "bvmap"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "model_ivs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Restrict"; "wx_segs_nowrap"; "H_off_segments"; "ranges_avoid"; "restrict"; "woff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt.WithImage.Sim"; "hid_same"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra.
Import ListNotations.
Open Scope Z_scope.

Lemma filter_ext_in {A} : ltac2:(tb__ "0|2|
VA;S4F_;M0G0S0VA;A1M1VA;S59VA;R1R2A3S44S4R5R2A1R4R2A1A3F_;Fx;S44G1S5bVA;R4R2A3S5bVA;R3R2A3A3F_;Fl;Fg;Ff;").
Proof.
  intros f g l H. induction l as [|x l IH]; [reflexivity|]. cbn.
  rewrite (H x (or_introl eq_refl)). rewrite IH; [reflexivity|]. intros y Hy; apply H; right; exact Hy.
Qed.

Lemma filter_length_split {A} : ltac2:(tb__ "0|3|
VA;S4F_;M0G0S0VA;A1S44S3S7fS6VA;S5bVA;VA;S9R4R1A1M1R3R1A1M2A2Lx;R1A3A2S6VA;S5bVA;VA;S9G1SdG2A1A2Lx;R1A3A2A2S6VA;S5bVA;R3R1A3A2A3Fl;Fg;Ff;").
Proof.
  intros f g l. induction l as [|x l IH]; [reflexivity|]. cbn.
  destruct (f x), (g x); cbn; lia.
Qed.

Lemma NoDup_same_length {A} : ltac2:(tb__ "0|2|
S0VA;A1M0G0S5aVA;R2A2M1G1VA;S47S59VA;R1R5A3S59VA;R1R4A3A2Fx;S44S3S6VA;R5A2S6VA;R4A2A3F_;F_;F_;Fl2;Fl1;").
Proof.
  intros l1 l2 H1 H2 H.
  pose proof (List.NoDup_incl_length H1 (fun x Hx => proj1 (H x) Hx)).
  pose proof (List.NoDup_incl_length H2 (fun x Hx => proj2 (H x) Hx)). lia.
Qed.

Lemma NoDup_app_intro {A} : ltac2:(tb__ "0|2|
S0VA;A1M0G0S5aVA;R2A2M1G1VA;S59VA;R1R5A3S48S59VA;R2R5A3A1F_;Fx;S5aVA;SaVA;R5R4A3A2F_;F_;F_;Fl2;Fl1;").
Proof.
  intros l1 l2 H1 H2 Hd. induction H1 as [|x l Hx Hl IH]; [exact H2|]. cbn.
  constructor.
  - intros Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (Hx Hin)|]. exact (Hd x (or_introl eq_refl) Hin).
  - apply IH. intros y Hy. apply Hd. right. exact Hy.
Qed.

Lemma page_size_pos : 0 < page_size.
Proof. unfold page_size. lia. Qed.

Lemma page_mem_In : ltac2:(tb__ "0|1|
S10Q40A1M0S0G0A1S47S44S4S17R2R1A2SbA3S59G0R2R1A3A2Fl;Fp;").
Proof.
  intros p l. unfold page_mem. rewrite existsb_exists. split.
  - intros (q & Hin & Heq). apply bv_eqb_eq in Heq. subst q. exact Hin.
  - intros Hin. exists p. split; [exact Hin|]. apply bv_eqb_eq. reflexivity.
Qed.

Lemma page_mem_false : ltac2:(tb__ "0|1|
S10Q40A1M0S0G0A1S47S44S4S17R2R1A2ScA3S48S59G0R2R1A3A1A2Fl;Fp;").
Proof.
  intros p l. rewrite <- page_mem_In. destruct (page_mem p l); split; congruence.
Qed.

Lemma page_mem_app : ltac2:(tb__ "0|2|
S10Q40A1M0S0G0A1M1G1S44S4S17R3SaG0R2R1A3A2SfS17R3R2A2S17R3R1A2A2A3Fl2;Fl1;Fp;").
Proof. intros. unfold page_mem. apply existsb_app. Qed.

Lemma page_base_of_mod : ltac2:(tb__ "0|0|
S70S69Z0R1A2S44S10Q40A1S1bS6dR2S6fZ2Z40A2A2A1S1bR2A1A3F_;Fz;").
Proof.
  intros z Hz. unfold page_base_of. apply bv_eq. rewrite !Z_to_bv_unsigned.
  change (bv_wrap 64 (z mod 2 ^ 64 / page_size * page_size)) with ((z mod 2 ^ 64 / page_size * page_size) mod bv_modulus 64).
  change (bv_wrap 64 (z / page_size * page_size)) with ((z / page_size * page_size) mod bv_modulus 64).
  change (bv_modulus 64) with (2 ^ 64).
  assert (E1 : z / page_size * page_size = z - z mod page_size).
  { pose proof (Z.div_mod z page_size ltac:(unfold page_size; lia)). lia. }
  assert (E2 : z mod 2 ^ 64 / page_size * page_size = z mod 2 ^ 64 - (z mod 2 ^ 64) mod page_size).
  { pose proof (Z.div_mod (z mod 2 ^ 64) page_size ltac:(unfold page_size; lia)). lia. }
  rewrite E1, E2.
  assert (E4 : z mod 2 ^ 64 = z - 2 ^ 64 * (z / 2 ^ 64)).
  { pose proof (Z.div_mod z (2 ^ 64) ltac:(lia)). lia. }
  assert (E3 : (z mod 2 ^ 64) mod page_size = z mod page_size).
  { rewrite E4. replace (z - 2 ^ 64 * (z / 2 ^ 64)) with (z + (- (2 ^ 52) * (z / 2 ^ 64)) * page_size) by (unfold page_size; lia).
    apply Z.mod_add. unfold page_size; lia. }
  rewrite E3. rewrite E4.
  replace (z - 2 ^ 64 * (z / 2 ^ 64) - z mod page_size) with ((z - z mod page_size) + (- (z / 2 ^ 64)) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma page_base_woff : ltac2:(tb__ "0|2|
S10Q40M0A1M1S3S44G1S20S89R2R1A2A1S1bS68S11G0R2A2S6aR1A1A2A1A3Fk;Fa;").
Proof.
  intros a k. unfold page_base. rewrite woff_unsigned. apply page_base_of_mod.
  pose proof (bv_unsigned_in_range 64 a). lia.
Qed.

Lemma page_insert_in : ltac2:(tb__ "0|1|
S10Q40A1M0G0S0G0A1S59G0R3S34R2R1A2A3S49S44G0R4R3A3S59G0R4R2A3A2F_;Fpages;Fq;Fp;").
Proof.
  intros p q pages H. unfold page_insert in H.
  destruct (page_mem q pages); [right; exact H|].
  destruct H as [Hqp | H]; [left; symmetry; exact Hqp | right; exact H].
Qed.

Lemma page_insert_NoDup : ltac2:(tb__ "0|1|
S10Q40A1M0S0G0A1S5aG0R1A2S5aG0S34R3R2A2A2F_;Fpages;Fq;").
Proof.
  intros q pages H. unfold page_insert. destruct (page_mem q pages) eqn:E; [exact H|].
  constructor; [|exact H]. apply page_mem_false. exact E.
Qed.

Lemma access_pages_acc_in : ltac2:(tb__ "0|1|
S3S70S0S10Q40A1M0A1G0S59G0R1S22R3R4R2A3A3S49S59G0R2R3A3S46S3S3S45S80R1R6A2S44G0R3S1bS68R5S6aR1A1A2A1A3A2Lk;A2A2F_;Fp;Fpages;Fbase;Fn;").
Proof.
  induction n as [|n IH]; cbn [access_pages_acc]; intros base pages p H.
  - left; exact H.
  - destruct (IH (base + 1) _ p H) as [Hin | (k & Hk & ->)].
    + destruct (page_insert_in _ _ _ Hin) as [-> | Hin'].
      * right. exists 0%nat. split; [lia|]. f_equal. lia.
      * left; exact Hin'.
    + right. exists (S k). split; [lia|]. f_equal. lia.
Qed.

Lemma access_pages_acc_NoDup : ltac2:(tb__ "0|1|
S3S70S0S10Q40A1M0A1S5aG0R1A2S5aG0S22R3R4R2A3A2F_;Fpages;Fbase;Fn;").
Proof.
  induction n as [|n IH]; cbn [access_pages_acc]; intros base pages H; [exact H|].
  apply IH. apply page_insert_NoDup. exact H.
Qed.

Lemma accesses_pages_in : ltac2:(tb__ "0|3|
S0S1S10Q40M0A1M1S3A2M2A1S0G1A1G1S59G1R1S1fR3R2A2A3S49S59G1R2R3A3S46G1G1S46S3S3S46S3S3S45S59G2S5G1S3R3R2A4R7A3S45S80R1R2A2S44G1R5S1bS68S11G0R3A2S6aR1A1A2A1A3A2A2Lk;A2Ln;A2La;A2A2F_;Fp;Fpages;Faccs;").
Proof.
  induction accs as [|[a n] accs IH]; cbn [accesses_pages]; intros pages p H.
  - left; exact H.
  - destruct (IH _ p H) as [Hin | (a' & n' & k & Hin & Hk & Hp)].
    + destruct (access_pages_acc_in n (bv_unsigned a) pages p Hin) as [Hp | (k & Hk & Hp)].
      * left; exact Hp.
      * right. exists a, n, k. split; [left; reflexivity | split; assumption].
    + right. exists a', n', k. split; [right; exact Hin | split; assumption].
Qed.

Lemma accesses_pages_NoDup : ltac2:(tb__ "0|1|
S0S1S10Q40A1M0S3A2A1S0G0A1S5aG0R1A2S5aG0S1fR3R2A2A2F_;Fpages;Faccs;").
Proof.
  induction accs as [|[a n] accs IH]; cbn [accesses_pages]; intros pages H; [exact H|].
  apply IH. apply access_pages_acc_NoDup. exact H.
Qed.

Definition hid (md : Model) (tp : list word) (a : word) : bool := ltac2:(tb__ "0|1|
S9S1cS20Va;A1M0S14Vmd;A1A2SdS17G0Vtp;A2A1A2").

Definition vms (md : Model) (tp : list word) (ms : machine_state) : machine_state := ltac2:(tb__ "0|0|
S88S5dVmd;Vtp;A2Vms;A2").
Definition vmd (md : Model) : Model := with_vm_backing [] [] md.

Lemma m_vmmaps_with_vm_backing : ltac2:(tb__ "0|1|
S0S1S10Q40A1M0G0A2A1S0G0A1S12S44S21S16S13R3R2R1A3A1S16R1A1A3Fm;Fp;Fl;").
Proof. reflexivity. Qed.
Lemma m_vm_lazy_with_vm_backing : ltac2:(tb__ "0|2|
S0S1S10Q40A1M0G0A2A1M1S0G0A1S12S44G1S14S13R3R2R1A3A1R3A3Fm;Fp;Fl;").
Proof. reflexivity. Qed.
Lemma m_vm_materialized_with_vm_backing : ltac2:(tb__ "0|2|
S0S1S10Q40A1M0G0A2A1S0G0A1M1S12S44G1S18S13R3R2R1A3A1R2A3Fm;Fp;Fl;").
Proof. reflexivity. Qed.
Lemma m_fds_with_vm_backing : ltac2:(tb__ "0|1|
S0S1S10Q40A1M0G0A2A1S0G0A1S12S44S0S1G0S37A2A1S27S13R3R2R1A3A1S27R1A1A3Fm;Fp;Fl;").
Proof. reflexivity. Qed.
Lemma m_pipes_with_vm_backing : ltac2:(tb__ "0|1|
S0S1S10Q40A1M0G0A2A1S0G0A1S12S44S0S1G0S3eA2A1S2eS13R3R2R1A3A1S2eR1A1A3Fm;Fp;Fl;").
Proof. reflexivity. Qed.
Lemma m_stdin_with_vm_backing : ltac2:(tb__ "0|1|
S0S1S10Q40A1M0G0A2A1S0G0A1S12S44S3aS31S13R3R2R1A3A1S31R1A1A3Fm;Fp;Fl;").
Proof. reflexivity. Qed.
Lemma m_fs_with_vm_backing : ltac2:(tb__ "0|1|
S0S1S10Q40A1M0G0A2A1S0G0A1S12S44S8bS28S13R3R2R1A3A1S28R1A1A3Fm;Fp;Fl;").
Proof. reflexivity. Qed.
Lemma m_halted_with_vm_backing : ltac2:(tb__ "0|1|
S0S1S10Q40A1M0G0A2A1S0G0A1S12S44S2G0A1S15S13R3R2R1A3A1S15R1A1A3Fm;Fp;Fl;").
Proof. reflexivity. Qed.
Lemma m_tid_with_vm_backing : ltac2:(tb__ "0|1|
S0S1S10Q40A1M0G0A2A1S0G0A1S12S44S2G0A1S32S13R3R2R1A3A1S32R1A1A3Fm;Fp;Fl;").
Proof. reflexivity. Qed.
Lemma m_rlimit_core_with_vm_backing : ltac2:(tb__ "0|1|
S0S1S10Q40A1M0G0A2A1S0G0A1S12S44S2S0S10Q8A1A1A1S30S13R3R2R1A3A1S30R1A1A3Fm;Fp;Fl;").
Proof. reflexivity. Qed.
Lemma m_clock_with_vm_backing : ltac2:(tb__ "0|1|
S0S1S10Q40A1M0G0A2A1S0G0A1S12S44G0S23S13R3R2R1A3A1S23R1A1A3Fm;Fp;Fl;").
Proof. reflexivity. Qed.
Lemma m_creds_with_vm_backing : ltac2:(tb__ "0|1|
S0S1S10Q40A1M0G0A2A1S0G0A1S12S44S36S25S13R3R2R1A3A1S25R1A1A3Fm;Fp;Fl;").
Proof. reflexivity. Qed.
Lemma m_net_with_vm_backing : ltac2:(tb__ "0|1|
S0S1S10Q40A1M0G0A2A1S0G0A1S12S44S3dS2cS13R3R2R1A3A1S2cR1A1A3Fm;Fp;Fl;").
Proof. reflexivity. Qed.
Lemma m_conn_ix_with_vm_backing : ltac2:(tb__ "0|1|
S0S1S10Q40A1M0G0A2A1S0G0A1S12S44G0S24S13R3R2R1A3A1S24R1A1A3Fm;Fp;Fl;").
Proof. reflexivity. Qed.
Lemma m_fd_with_vm_backing : ltac2:(tb__ "0|1|
S0S1S10Q40A1M0G0A2A1S0G0A1S12S44S38S26S13R3R2R1A3A1S26R1A1A3Fm;Fp;Fl;").
Proof. reflexivity. Qed.
Lemma m_io_with_vm_backing : ltac2:(tb__ "0|1|
S0S1S10Q40A1M0G0A2A1S0G0A1S12S44S3bS2aS13R3R2R1A3A1S2aR1A1A3Fm;Fp;Fl;").
Proof. reflexivity. Qed.
Lemma m_fsys_with_vm_backing : ltac2:(tb__ "0|1|
S0S1S10Q40A1M0G0A2A1S0G0A1S12S44S39S29S13R3R2R1A3A1S29R1A1A3Fm;Fp;Fl;").
Proof. reflexivity. Qed.
Lemma m_proc_with_vm_backing : ltac2:(tb__ "0|1|
S0S1S10Q40A1M0G0A2A1S0G0A1S12S44S3fS2fS13R3R2R1A3A1S2fR1A1A3Fm;Fp;Fl;").
Proof. reflexivity. Qed.
Lemma m_lim_with_vm_backing : ltac2:(tb__ "0|1|
S0S1S10Q40A1M0G0A2A1S0G0A1S12S44S3cS2bS13R3R2R1A3A1S2bR1A1A3Fm;Fp;Fl;").
Proof. reflexivity. Qed.
Lemma m_time_with_vm_backing : ltac2:(tb__ "0|1|
S0S1S10Q40A1M0G0A2A1S0G0A1S12S44S40S33S13R3R2R1A3A1S33R1A1A3Fm;Fp;Fl;").
Proof. reflexivity. Qed.

Lemma m_nofile_with_vm_backing : ltac2:(tb__ "0|1|
S0S1S10Q40A1M0G0A2A1S0G0A1S12S44G0S2dS13R3R2R1A3A1S2dR1A1A3Fm;Fp;Fl;").
Proof. reflexivity. Qed.

Lemma with_vm_backing_twice : ltac2:(tb__ "0|3|
S0S1S10Q40A1M0G0A2A1M1S0G0A1M2G1G2S12S44S12S13R5R4S13R3R2R1A3A3S13R5R4R1A3A3Fm;Fp';Fl';Fp;Fl;").
Proof. reflexivity. Qed.

Lemma with_vm_backing_id : ltac2:(tb__ "0|0|
S12S44S12S13S14R1A1S18R1A1R1A3R1A3Fm;").
Proof. intros m. destruct m as [fd [maps lz mat] io fs proc lim tm]. reflexivity. Qed.

#[export] Hint Rewrite m_vmmaps_with_vm_backing m_vm_lazy_with_vm_backing m_vm_materialized_with_vm_backing
  m_fds_with_vm_backing m_pipes_with_vm_backing m_stdin_with_vm_backing m_fs_with_vm_backing
  m_halted_with_vm_backing m_tid_with_vm_backing m_rlimit_core_with_vm_backing m_clock_with_vm_backing
  m_creds_with_vm_backing m_net_with_vm_backing m_conn_ix_with_vm_backing
  m_fd_with_vm_backing m_io_with_vm_backing m_fsys_with_vm_backing m_proc_with_vm_backing m_lim_with_vm_backing
  m_time_with_vm_backing m_nofile_with_vm_backing with_vm_backing_twice : model.

Lemma vmd_halted : ltac2:(tb__ "0|0|
S12S44S2S10Q40A1A1S15S5eR1A1A1S15R1A1A3Fmd;").
Proof. reflexivity. Qed.
Lemma vmd_lazy : ltac2:(tb__ "0|2|
S12S44S0S1S10Q40A1M0G0A2M1A1S14S5eR1A1A1SeG1A1A3Fmd;").
Proof. reflexivity. Qed.
Lemma vmd_with_vm_backing : ltac2:(tb__ "0|1|
S0S1S10Q40A1M0G0A2A1S0G0A1S12S44S12S5eS13R3R2R1A3A1S5eR1A1A3Fmd;Fp;Fl;").
Proof. reflexivity. Qed.
Lemma model_idle_vmd : ltac2:(tb__ "0|1|
S12S47S7cS5eR1A1A1S44S2S10Q40A1M0A1S15R1A1S7G0A1A3A2Fmd;").
Proof. intros md. unfold model_idle. rewrite vmd_halted, vmd_lazy. tauto. Qed.

Lemma hid_with_vm_backing : ltac2:(tb__ "0|2|
S12S0S10Q40A1M0A1M1G1S44G0S4Fa;S5dS13S14R3A1R2R3A3R1A2S5dR3R1A2A3Ftp;Fp;Fmd;").
Proof. reflexivity. Qed.

Lemma vms_with_vm_backing : ltac2:(tb__ "0|1|
S12S0S10Q40A1A1M0G0S4aS44S4aS5cS13S14R4A1R3R4A3R2R1A3S5cR4R2R1A3A3Fms;Ftp;Fp;Fmd;").
Proof. reflexivity. Qed.

Section WithImage.
Variable segs : list Segment.

Definition virt (tp : list word) (w : world) : world := ltac2:(tb__ "0|2|
S5S0S1aA1S72S7eVw;A1S71S5cS75S7dVw;A1M0A1M1Vtp;S76G0A1A3S5eG1A1A2A4").

Definition unpaid (md : Model) (tp : list word) : list word := ltac2:(tb__ "0|1|
S5bS10Q40A1M0G0S9S1cR1S14Vmd;A1A2SdS17R1S18Vmd;A1A2A1A2Lp;Vtp;A3").

Definition paid (md : Model) (tp : list word) : Z := ltac2:(tb__ "0|0|
S68S1dVmd;A1S6cS19S6aS6S10Q40A1S62Vmd;Vtp;A2A2A1A2A2").

Definition headroom (md : Model) (tp : list word) : Z := ltac2:(tb__ "0|0|
S6eS1eS16Vmd;A1A1S61Vmd;Vtp;A2A2").

Definition lazy_clear (lz : list (word * word)) : Prop := ltac2:(tb__ "0|3|
S10Q40M0A1M1G1S70S59S1G1G1A2S5G1G1R3R2A4Vlz;A3S45S69S11G0R4A2M2R2A2S6bR2S68G2S11G0R3A2A2A2A2S44S2S82A1S58Vsegs;R3Z1A3S7S82A1A3F_;F_;Fz;Fsz;Flo;").

Definition lazy_in_maps (md : Model) : Prop := ltac2:(tb__ "0|6|
S10Q40M0A1M1G1S59S1G1G1A2M2S5G1G1R2R1A4M3S14Vmd;A1A3S6bZ0S11G0R2A2M4A2S46G1G1S46G1G1S45S59G2G3S35S16Vmd;A1A1A3S45S69G4S11G0R6A2M5A2S69S68G5S11G0R5A2A2S68G4S11G0R1A2A2A2A2A2Ls;A2Lb;A2F_;F_;Fsz;Flo;").

Definition tp_in_maps (md : Model) (tp : list word) : Prop := ltac2:(tb__ "0|4|
S10Q40M0A1M1S59G1R1Vtp;A3S45S44S70S6dS11G0R2A2M2S19A2Z0A3S46G1G1S46G1G1S45S59S1G1G1A2S5G1G1R2R1A4S35S16Vmd;A1A1A3S45S69G2S11G0R4A2M3A2S69S68G3S19A2S68G2S11G0R1A2A2A2A2A2Ls;A2Lb;A2A2F_;Fp;").

Definition MI (md : Model) (tp : list word) : Prop := ltac2:(tb__ "0|2|
S45S85Vsegs;A1S45S5aS10Q40A1M0Vtp;A2S45S5aG0S18Vmd;A1M1A2S45G0S59G0R1G1A3S59G0R2Vtp;A3F_;Fp;S45S69S61Vmd;Vtp;A2S1eS16Vmd;A1A1A2S45S64S14Vmd;A1A1S45S84Vmd;A1S45S65Vmd;A1S66Vmd;Vtp;A2A2A2A2A2A2A2A2A2").

Lemma MI_wx : ltac2:(tb__ "0|0|
S12S0S10Q40A1A1S5fR2R1A2S85Vsegs;A1F_;Ftp;Fmd;").
Proof. intros md tp H. exact (proj1 H). Qed.
Lemma MI_nodupT : ltac2:(tb__ "0|1|
S12S0S10Q40A1M0A1S5fR2R1A2S5aG0R2A2F_;Ftp;Fmd;").
Proof. intros md tp H. exact (proj1 (proj2 H)). Qed.
Lemma MI_nodup_mat : ltac2:(tb__ "0|1|
S12S0S10Q40A1M0A1S5fR2R1A2S5aG0S18R3A1A2F_;Ftp;Fmd;").
Proof. intros md tp H. exact (proj1 (proj2 (proj2 H))). Qed.
Lemma MI_mat_T : ltac2:(tb__ "0|1|
S12S0S10Q40A1M0A1G0S5fR3R2A2S59G0R2S18R4A1A3S59G0R3R4A3F_;F_;Fp;Ftp;Fmd;").
Proof. intros md tp p H. exact (proj1 (proj2 (proj2 (proj2 H))) p). Qed.
Lemma MI_paid : ltac2:(tb__ "0|0|
S12S0S10Q40A1A1S5fR2R1A2S69S61R3R2A2S1eS16R3A1A1A2F_;Ftp;Fmd;").
Proof. intros md tp H. exact (proj1 (proj2 (proj2 (proj2 (proj2 H))))). Qed.
Lemma MI_ivs_wf : ltac2:(tb__ "0|0|
S12S0S10Q40A1A1S5fR2R1A2S84R3A1F_;Ftp;Fmd;").
Proof. intros md tp H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))). Qed.

Lemma MI_lazy_in_maps : ltac2:(tb__ "0|0|
S12S0S10Q40A1A1S5fR2R1A2S65R3A1F_;Ftp;Fmd;").
Proof. intros md tp H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))). Qed.

Lemma MI_tp_in_maps : ltac2:(tb__ "0|0|
S12S0S10Q40A1A1S5fR2R1A2S66R3R2A2F_;Ftp;Fmd;").
Proof. intros md tp H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))). Qed.

Lemma MI_lazy_clear : ltac2:(tb__ "0|0|
S12S0S10Q40A1A1S5fR2R1A2S64S14R3A1A1F_;Ftp;Fmd;").
Proof. intros md tp H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))). Qed.
Lemma MI_headroom : ltac2:(tb__ "0|0|
S12S0S10Q40A1A1S5fR2R1A2S69Z0S63R3R2A2A2F_;Ftp;Fmd;").
Proof. intros md tp H. pose proof (MI_paid md tp H). unfold headroom. lia. Qed.

Definition mat_equiv (tp : list word) (md md' : Model) : Prop := ltac2:(tb__ "0|1|
S45S46S0S10Q40A1A1M0G0S44S12Vmd';S13S14Vmd;A1R1Vmd;A3A3Lmat';A2S45S44S70S61Vmd';Vtp;A2S61Vmd;Vtp;A2A3S5fVmd;Vtp;A2S5fVmd';Vtp;A2F_;A2A2").

Lemma vm_backing_used_with_mat : ltac2:(tb__ "0|1|
S12S0S10Q40A1M0A1S44S70S1dS13S14R2A1R1R2A3A1S68S6eS1dR2A1S6cS19S6aS6G0S18R2A1A2A1A2A2S6cS19S6aS6G0R1A2A1A2A2A3Fmat';Fmd;").
Proof.
  intros md mat'. unfold vm_backing_used.
  rewrite m_vmmaps_with_vm_backing, m_vm_lazy_with_vm_backing, m_vm_materialized_with_vm_backing. lia.
Qed.

Lemma page_base_range : ltac2:(tb__ "0|3|
S10Q40M0A1S45S69S11G0S20R1A1A2M1S11G0R1A2M2A2S6bG2S68G1S19A2A2A2Fa;").
Proof.
  intros a. unfold page_base, page_base_of.
  pose proof (bv_unsigned_in_range 64 a) as Ha. change (bv_modulus 64) with (2 ^ 64) in Ha.
  rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 (bv_unsigned a / page_size * page_size)) with ((bv_unsigned a / page_size * page_size) mod bv_modulus 64).
  change (bv_modulus 64) with (2 ^ 64).
  pose proof (Z.div_mod (bv_unsigned a) page_size ltac:(unfold page_size; lia)) as Hd.
  pose proof (Z.mod_pos_bound (bv_unsigned a) page_size ltac:(unfold page_size; lia)) as Hm.
  rewrite Z.mod_small; [lia|].
  split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos; unfold page_size in *; lia | unfold page_size; lia] | lia].
Qed.

Lemma hid_off_segments : ltac2:(tb__ "0|0|
S12S0S10Q40A1A1S64S14R2A1A1S86Vsegs;S5dR3R2A2A2F_;Ftp;Fmd;").
Proof.
  intros md tp Hlc a Ha. unfold hid in Ha. apply andb_prop in Ha as [Hin _].
  unfold page_in_ranges in Hin. apply existsb_exists in Hin as ([lo sz] & Hin & Hr). cbn [fst snd] in Hr.
  apply andb_prop in Hr as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (page_base_range a). eapply Hlc; [exact Hin|]. lia.
Qed.

Section Accounting.
Variable md : Model.
Variable tp : list word.
Variable accs : list (word * nat).
Hypothesis HMI : MI md tp.
Hypothesis Hav : ltac2:(tb__ "0|0|
S87S5dVmd;Vtp;A2Vaccs;A2").

Let lz := m_vm_lazy md.
Let mat := m_vm_materialized md.
Let new : ltac2:(tb__ "0|0|
S0S10Q40A1A1") := ltac2:(tb__ "0|0|
S43Vlz;Vmat;Vaccs;A3").

Lemma touched_lazy_page_prepaid : ltac2:(tb__ "0|1|
S10Q40A1M0S59G0R1S1fVaccs;SeG0A1A2A3S44S4S1cR2Vlz;A2SbA3S59G0R3Vtp;A3F_;F_;Fp;").
Proof using Hav.
  intros p Hp Hl. destruct (accesses_pages_in accs [] p Hp) as [[] | (a & n & k & Hin & Hk & ->)].
  pose proof (Hav a n Hin k Hk) as Hh. unfold hid in Hh. rewrite page_base_woff in Hh. fold lz in Hh.
  rewrite Hl in Hh. cbn in Hh. apply negb_false_iff in Hh. apply page_mem_In. exact Hh.
Qed.

Lemma new_spec : ltac2:(tb__ "0|1|
S10Q40A1M0S59G0R1Vnew;A3S45S59G0R2Vtp;A3S45S44S4S1cR2Vlz;A2SbA3S44S4S17R2Vmat;A2ScA3A2A2F_;Fp;").
Proof using Hav.
  intros p Hp. unfold new, newly_materialized_pages in Hp. apply filter_In in Hp as [Hp Hb].
  apply andb_prop in Hb as [Hl Hm]. apply negb_true_iff in Hm.
  split; [exact (touched_lazy_page_prepaid p Hp Hl)|]. split; assumption.
Qed.

Lemma new_NoDup : List.NoDup new.
Proof using .
  unfold new, newly_materialized_pages. apply List.NoDup_filter. apply accesses_pages_NoDup. constructor.
Qed.

Lemma new_in_unpaid : ltac2:(tb__ "0|1|
S10Q40A1M0S59G0R1Vnew;A3S59G0R2S62Vmd;Vtp;A2A3F_;Fp;").
Proof using Hav.
  intros p Hp. destruct (new_spec p Hp) as (HT & Hl & Hm). unfold unpaid. apply filter_In.
  split; [exact HT|]. fold lz mat. rewrite Hl, Hm. reflexivity.
Qed.

Lemma new_length_le : ltac2:(tb__ "0|1|
S81S6S10Q40A1M0Vnew;A2S6G0S62Vmd;Vtp;A2A2A2").
Proof using Hav.
  apply List.NoDup_incl_length; [apply new_NoDup|]. intros p Hp. apply new_in_unpaid. exact Hp.
Qed.

Lemma materialize_accesses_prepaid : ltac2:(tb__ "0|2|
S44S2S0S10Q40A1M0A1M1A1S41Vlz;Vmat;S1dVmd;A1S1eS16Vmd;A1A1Vaccs;A5S8G1SaG0Vnew;Vmat;A3A2A3").
Proof using HMI Hav.
  unfold materialize_accesses. fold new. destruct new as [|p rest] eqn:En; [reflexivity|].
  pose proof (MI_paid md tp HMI) as Hpaid. unfold paid in Hpaid.
  pose proof new_length_le as Hlen. rewrite En in Hlen.
  match goal with |- (if ?c then _ else _) = _ => replace c with true; [reflexivity|] end.
  symmetry. apply Z.leb_le. pose proof page_size_pos. nia.
Qed.

Definition md_after : Model := ltac2:(tb__ "0|0|
S13Vlz;SaS10Q40A1Vnew;Vmat;A3Vmd;A3").

Lemma materialize_model_accesses_prepaid : ltac2:(tb__ "0|0|
S44S2S12A1S42Vmd;Vaccs;A2S8S12S79A2A3").
Proof using HMI Hav.
  unfold materialize_model_accesses. fold lz mat. rewrite materialize_accesses_prepaid. reflexivity.
Qed.

Lemma unpaid_after_length : ltac2:(tb__ "0|1|
S44S3S7fS6S10Q40A1M0S62S79Vtp;A2A2S6G0Vnew;A2A2S6G0S62Vmd;Vtp;A2A2A3").
Proof using HMI Hav.
  unfold unpaid, md_after. rewrite m_vm_lazy_with_vm_backing, m_vm_materialized_with_vm_backing. fold lz mat.
  transitivity (length (List.filter (fun p => (page_in_ranges p lz && negb (page_mem p mat)) && negb (page_mem p new)) tp)
                + length (List.filter (fun p => (page_in_ranges p lz && negb (page_mem p mat)) && page_mem p new) tp))%nat.
  - f_equal.
    + f_equal. apply filter_ext_in. intros p _. rewrite page_mem_app. destruct (page_in_ranges p lz), (page_mem p new), (page_mem p mat); reflexivity.
    + rewrite (filter_ext_in (fun p => page_in_ranges p lz && negb (page_mem p mat) && page_mem p new) (fun p => page_mem p new) tp).
      * symmetry. apply NoDup_same_length.
        -- apply List.NoDup_filter. exact (MI_nodupT md tp HMI).
        -- apply new_NoDup.
        -- intros p. rewrite filter_In, page_mem_In. split; [tauto|]. intros Hp. split; [exact (proj1 (new_spec p Hp)) | exact Hp].
      * intros p _. destruct (page_mem p new) eqn:E; [|now rewrite andb_false_r].
        apply page_mem_In in E. destruct (new_spec p E) as (_ & -> & ->). reflexivity.
  - rewrite Nat.add_comm. apply filter_length_split.
Qed.

Lemma paid_after : ltac2:(tb__ "0|0|
S44S70S61S79Vtp;A2S61Vmd;Vtp;A2A3").
Proof using HMI Hav.
  unfold paid. pose proof unpaid_after_length as Hl.
  unfold md_after in *. unfold lz, mat in Hl |- *. rewrite vm_backing_used_with_mat. rewrite length_app. lia.
Qed.

Lemma MI_after : MI md_after tp.
Proof using HMI Hav.
  pose proof paid_after as HP. destruct HMI as (HW & HT & Hmat & Hsub & Hpaid & Hlc & Hivs & Hlm & Htm).
  unfold MI, md_after in *. unfold lz, mat in HP |- *.
  rewrite m_vm_materialized_with_vm_backing, m_vmmaps_with_vm_backing, m_vm_lazy_with_vm_backing.
  split; [exact HW|]. split; [exact HT|]. split.
  { apply NoDup_app_intro; [apply new_NoDup | exact Hmat |].
    intros p Hp Hm. destruct (new_spec p Hp) as (_ & _ & Hf). apply page_mem_false in Hf. exact (Hf Hm). }
  split.
  { intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (proj1 (new_spec p Hp)) | exact (Hsub p Hp)]. }
  split; [rewrite HP; exact Hpaid |]. split; [exact Hlc|]. split; [exact Hivs |]. split; [exact Hlm | exact Htm].
Qed.

Lemma mat_equiv_after : ltac2:(tb__ "0|0|
S60Vtp;Vmd;S79A3").
Proof using HMI Hav.
  split; [exists (new ++ mat); reflexivity|]. split; [apply paid_after | intros _; apply MI_after].
Qed.

End Accounting.

Lemma mat_equiv_refl : ltac2:(tb__ "0|0|
S0S10Q40A1A1S12S60R2R1R1A3Fmd;Ftp;").
Proof.
  intros tp md. split; [exists (m_vm_materialized md); symmetry; apply with_vm_backing_id|]. split; [reflexivity | tauto].
Qed.

Lemma mat_equiv_trans : ltac2:(tb__ "0|0|
S0S10Q40A1A1S12S12S12S60R4R3R2A3S60R5R3R2A3S60R6R5R3A3F_;F_;Fmd3;Fmd2;Fmd1;Ftp;").
Proof.
  intros tp md1 md2 md3 ((p2 & ->) & P2 & M2) ((p3 & ->) & P3 & M3).
  split; [exists p3; reflexivity|]. split; [|tauto].
  rewrite <- P2, <- P3. reflexivity.
Qed.

Lemma mat_equiv_vmd : ltac2:(tb__ "0|0|
S0S10Q40A1A1S12S12S60R3R2R1A3S44S12S5eR2A1S5eR3A1A3F_;Fmd';Fmd;Ftp;").
Proof. intros tp md md' ((p & ->) & _). reflexivity. Qed.

Lemma mat_equiv_hid : ltac2:(tb__ "0|1|
S0S10Q40A1M0A1S12S12S60R3R2R1A3S44G0S4Fa;S5dR2R4A2S5dR3R4A2A3F_;Fmd';Fmd;Ftp;").
Proof. intros tp md md' ((p & ->) & _). reflexivity. Qed.

Lemma mat_equiv_vms : ltac2:(tb__ "0|0|
S0S10Q40A1A1S12S12S4aS60R4R3R2A3S44S4aS5cR3R5R2A3S5cR4R5R2A3A3F_;Fms;Fmd';Fmd;Ftp;").
Proof. intros tp md md' ms ((p & ->) & _). reflexivity. Qed.

Lemma mat_equiv_halted : ltac2:(tb__ "0|1|
S0S10Q40A1M0A1S12S12S60R3R2R1A3S44S2G0A1S15R2A1S15R3A1A3F_;Fmd';Fmd;Ftp;").
Proof. intros tp md md' ((p & ->) & _). reflexivity. Qed.

Lemma mat_equiv_vmmaps : ltac2:(tb__ "0|0|
S0S10Q40A1A1S12S12S60R3R2R1A3S44S21S16R2A1S16R3A1A3F_;Fmd';Fmd;Ftp;").
Proof. intros tp md md' ((p & ->) & _). reflexivity. Qed.

Lemma mat_equiv_lazy : ltac2:(tb__ "0|1|
S0S10Q40A1M0A1S12S12S60R3R2R1A3S44S0S1G0G0A2A1S14R2A1S14R3A1A3F_;Fmd';Fmd;Ftp;").
Proof. intros tp md md' ((p & ->) & _). reflexivity. Qed.

Lemma mat_equiv_headroom : ltac2:(tb__ "0|0|
S0S10Q40A1A1S12S12S60R3R2R1A3S44S70S63R2R4A2S63R3R4A2A3F_;Fmd';Fmd;Ftp;").
Proof. intros tp md md' ((p & ->) & P & _). unfold headroom. rewrite P. reflexivity. Qed.

Section Sim.

Definition hid_same (md : Model) (tp : list word) (ms ms' : machine_state) : Prop := ltac2:(tb__ "0|0|
S10Q40A1S44S4S5dVmd;Vtp;R1A3SbA3S44S2S10Q8A1A1S4bVms';R2A2S4bVms;R2A2A3F_;Fa;").

Theorem stepA_sim : ltac2:(tb__ "0|1|
S12S0S10Q40A1A1S4aS4aS5fR4R3A2S44S4dS4aA1S4fVsegs;S5cR5R4R3A3A2S4cS4aR2A2A3S46S4aS4aS46S12S12S45S44S4dS1S4aS12A2M0A1S73Vsegs;R6R8A3S4cG0S5S4aS12R2R1A4A2A3S45S44S4aS5cR1R7R2A3R5A3S45S60R7R8R1A3S8aR8R7R6R2A4A2A2A2Lmd';A2Lms';A2F_;F_;Fmsv';Fms;Ftp;Fmd;").
Proof.
  intros md tp ms msv' HMI Hstep.
  pose proof (hid_off_segments md tp (MI_lazy_clear md tp HMI)) as HH.
  destruct (step_restrict_sound segs (hid md tp) HH (MI_wx md tp HMI) ms msv' Hstep) as (rep & Hsa & Hv & Hrs & Hcl & Hrr).
  destruct rep as [ms' rs]. cbn [access_value accessed_ranges] in Hv, Hrs, Hrr. subst ms'.
  exists (unrestrict (hid md tp) (ms_mem ms) msv'), (md_after md rs).
  split.
  - unfold mi_account_step. rewrite Hsa. cbn [accessed_ranges access_value].
    rewrite (materialize_model_accesses_prepaid md tp rs HMI Hrs). reflexivity.
  - split; [|split; [apply (mat_equiv_after md tp rs HMI Hrs)|]].
    + unfold vms, md_after. rewrite hid_with_vm_backing. exact Hrr.
    + intros a Ha. rewrite unrestrict_mem. unfold munrestrict. rewrite Ha. reflexivity.
Qed.

Lemma wstepA_of_step : ltac2:(tb__ "0|5|
S0S1aA1M0S4aS12S0S10Q40A1M1A1S4aS5fR3R2A2S44S2G1A1M2S15R4A1S7G1A1M3A3S44G2S4eR6A1G3A3S44S4dS4aA1S4fVsegs;S5cR6R5R7A3A2S4cS4aR4A2A3S46S4aS4aS46S12S12S45S44S4dS1S4aS12A2M4A1S73Vsegs;RaR9A3S4cG4S5S4aS12R2R1A4A2A3S45S7bVsegs;S5G0S72RbS71RaR9A2A4S5G0S72RbS71R2R1A2A4A3S45S44S4aS5cR1R8R2A3R7A3S45S60R8R9R1A3S8aR9R8RaR2A4A2A2A2A2Lmd';A2Lms';A2F_;F_;F_;F_;Fmsv';Ftp;Fmd;Fms;Ftr;").
Proof.
  intros tr ms md tp msv' HMI Hh Hp Hs.
  destruct (stepA_sim md tp ms msv' HMI Hs) as (ms' & md' & Hacc & Hv & Heq & Hhz).
  exists ms', md'. split; [exact Hacc|]. split; [|split; [exact Hv | split; assumption]].
  exists []. split; [|cbn; rewrite app_nil_r; reflexivity]. cbn. apply sstep_cfg_instr; assumption.
Qed.

Lemma wstepA_step_inv : ltac2:(tb__ "0|5|
S0S1aA1M0S4aS12S4aS12S7aS44S2S10Q40A1M1A1M2S15R4A1S7G1A1M3A3S44G2S4eR6A1G3A3S44S4dS1S4aS12A2M4A1S73Vsegs;R7R6A3S4cG4S5S4aS12R5R4A4A2A3S7bVsegs;S5G0S72R9S71R8R7A2A4R4A3S44S7aR5S5G0S72RaS71R7R6A2A4A3F_;F_;F_;F_;Fw';Fmd';Fms';Fmd;Fms;Ftr;").
Proof.
  intros tr ms md ms' md' [tr' c'] Hh Hp Hacc Hw. destruct Hw as [evs [Hst Heq]]. cbn in Hst, Heq.
  inversion Hst; subst; try congruence.
  match goal with H : mi_account_step segs ms md = MachineOk (?x, ?y) |- _ => rewrite Hacc in H; injection H as <- <- end.
  rewrite app_nil_r. reflexivity.
Qed.

Lemma sstepA_no_error : ltac2:(tb__ "0|3|
S4aS12S0S10Q40A1M0A1S4aS0S1aA1S5fR4R3A2S44S2G0A1M1S15R5A1S7G0A1M2A3S44G1S4eR7A1G2A3S44S4dS4aA1S4fVsegs;S5cR7R6R8A3A2S4cS4aR5A2A3S48S77Vsegs;S71R9R8A2R5S74A4A1F_;F_;F_;F_;Fevs;Fmsv';Ftp;Fmd;Fms;").
Proof.
  intros ms md tp msv' evs HMI Hh Hp Hs Hst.
  destruct (stepA_sim md tp ms msv' HMI Hs) as (ms' & md' & Hacc & _).
  inversion Hst; subst; try congruence.
Qed.

Lemma unmodeledA_not : ltac2:(tb__ "0|1|
S4aS12S0S10Q40A1M0A1S4aS5fR3R2A2S44S2G0A1S4eR5A1S7G0A1A3S44S4dS4aA1S4fVsegs;S5cR5R4R6A3A2S4cS4aR3A2A3S48S78Vsegs;S71R7R6A2A2A1F_;F_;F_;Fmsv';Ftp;Fmd;Fms;").
Proof.
  intros ms md tp msv' HMI Hp Hs [_ [[_ Hu] | [x8 [Hp' _]]]]; cbn in *; [|congruence].
  destruct (stepA_sim md tp ms msv' HMI Hs) as (ms' & md' & Hacc & _). rewrite Hacc in Hu. discriminate.
Qed.

End Sim.

Lemma vms_pc : ltac2:(tb__ "0|1|
S12S0S10Q40A1M0A1S4aS44G0S53S5cR3R2R1A3A1S53R1A1A3Fms;Ftp;Fmd;").
Proof. reflexivity. Qed.
Lemma vms_regs : ltac2:(tb__ "0|1|
S12S0S10Q40A1M0A1S4aS44S83Q5G0A2S55S5cR3R2R1A3A1S55R1A1A3Fms;Ftp;Fmd;").
Proof. reflexivity. Qed.
Lemma vms_fregs : ltac2:(tb__ "0|1|
S12S0S10Q40A1M0A1S4aS44S83Q5G0A2S51S5cR3R2R1A3A1S51R1A1A3Fms;Ftp;Fmd;").
Proof. reflexivity. Qed.
Lemma vms_gpr : ltac2:(tb__ "0|1|
S12S0S10Q40A1M0A1S4aS3S44G0S52S5cR4R3R2A3R1A2S52R2R1A2A3Fi;Fms;Ftp;Fmd;").
Proof. reflexivity. Qed.
Lemma vms_reg : ltac2:(tb__ "0|1|
S12S0S10Q40A1M0A1S4aS10Q5A1S44G0S54S5cR4R3R2A3R1A2S54R2R1A2A3Fr;Fms;Ftp;Fmd;").
Proof. reflexivity. Qed.
Lemma vms_svc_pending : ltac2:(tb__ "0|1|
S12S0S10Q40A1M0A1S4aS44S2G0A1S4eS5cR3R2R1A3A1S4eR1A1A3Fms;Ftp;Fmd;").
Proof. reflexivity. Qed.
Lemma vms_rom : ltac2:(tb__ "0|1|
S12S0S10Q40A1M0A1S4aS44G0S2S10Q8A1A1F_;S57S5cR3R2R1A3A1S57R1A1A3Fms;Ftp;Fmd;").
Proof. reflexivity. Qed.
Lemma vms_fcsr : ltac2:(tb__ "0|0|
S12S0S10Q40A1A1S4aS44S10Q20A1S50S5cR3R2R1A3A1S50R1A1A3Fms;Ftp;Fmd;").
Proof. reflexivity. Qed.
Lemma vms_resv : ltac2:(tb__ "0|1|
S12S0S10Q40A1M0A1S4aS44S2G0A1S56S5cR3R2R1A3A1S56R1A1A3Fms;Ftp;Fmd;").
Proof. reflexivity. Qed.
Lemma vms_mem : ltac2:(tb__ "0|3|
S12S0S10Q40A1M0A1S4aG0S44S2S10Q8A1M1A1M2S4bS5cR4R3R2A3R1A2S4G2L_;S5dR4R3R1A3S7G1A1S4bR2R1A2X4x2A3Fa;Fms;Ftp;Fmd;").
Proof. reflexivity. Qed.
Lemma vms_mem_visible : ltac2:(tb__ "0|1|
S12S0S10Q40A1M0A1S4aG0S44S4S5dR4R3R1A3ScA3S44S2S10Q8A1A1S4bS5cR5R4R3A3R2A2S4bR3R2A2A3F_;Fa;Fms;Ftp;Fmd;").
Proof. intros md tp ms a H. rewrite vms_mem, H. reflexivity. Qed.
Lemma vms_mem_some : ltac2:(tb__ "0|3|
S12S0S10Q40A1M0A1S4aG0S10Q8A1M1S44S2G1A1M2S4bS5cR5R4R3A3R2A2S8G1R1A2A3S44G2S4bR4R3A2S8G1R2A2A3F_;Fb;Fa;Fms;Ftp;Fmd;").
Proof. intros md tp ms a b H. rewrite vms_mem in H. destruct (hid md tp a); [discriminate | exact H]. Qed.

Lemma virt_unfold : ltac2:(tb__ "0|1|
S0S10Q40A1A1S0S1aA1M0S4aS12S44S7aS67R4S5G0S72R3S71R2R1A2A4A2S5G0S72R3S71S5cR1R4R2A3S5eR1A1A2A4A3Fmd;Fms;Ftr;Ftp;").
Proof. reflexivity. Qed.

End WithImage.

Arguments vms : simpl never.
Arguments vmd : simpl never.
Arguments hid : simpl never.
