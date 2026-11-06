(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StreamSim__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require FileSim__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Mprotect.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require MmapSim AllocSim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require Footprint__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefNodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module NodesFs.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StreamSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require FileSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.StreamExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StreamSim__Common.StreamSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.FileSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.ShapeNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Local Instance nodesfs_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u64_lit : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. exact Hz. Qed.

Lemma fd32_id : forall fd : word, (bv_unsigned fd < 2 ^ 32)%Z -> fd32 fd = fd.
Proof. intros fd H. apply fd32_small. exact H. Qed.

Section WithSegs.
Variable segs : list Segment.

Local Notation ROM := (seg_rom segs) (only parsing).

(* [comment removed for export] *)
#[using="Type"] Lemma si_gpr0 : forall regs pc mem, ms_gpr (ecall_st regs pc mem ROM) 0 = getr regs 10.
Proof. intros. apply ecall_st_gpr0. Qed.
#[using="Type"] Lemma si_gpr1 : forall regs pc mem, ms_gpr (ecall_st regs pc mem ROM) 1 = getr regs 11.
Proof. intros. apply ecall_st_gpr1. Qed.
#[using="Type"] Lemma si_gpr2 : forall regs pc mem, ms_gpr (ecall_st regs pc mem ROM) 2 = getr regs 12.
Proof. intros. apply ecall_st_gpr2. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma estep_instr : forall ms model ms',
  m_halted model = None -> m_vm_lazy model = [] -> ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  star_cfg segs CFG (mkCfg ms model) [] (mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hl Hs Hst. apply star_cfg_one.
  exact (proj1 (node_instr segs ms model ms' Hh Hl Hs Hst) tt).
Qed.

#[using="Type"] Lemma estep_msteps : forall ms ms' model,
  m_halted model = None -> m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  star_cfg segs CFG (mkCfg ms model) [] (mkCfg ms' model).
Proof.
  intros ms ms' model Hh Hl Hms.
  induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH].
  - apply star_cfg_refl.
  - change ([] : list event) with (([] : list event) ++ []).
    eapply star_cfg_trans; [| exact IH].
    eapply estep_instr; eassumption.
Qed.

#[using="Type"] Lemma estep_of_check : forall regs pc mem model w eff m',
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  alloc_no (bv_unsigned (getr regs 17)) = false ->
  check_syscall (sys_input segs (ecall_st regs pc mem ROM) (getr regs 17)) eff model = CheckOk m' [] ->
  m_halted m' = None -> m_vm_lazy m' = [] ->
  star_cfg segs CFG (mkCfg (mkst regs pc mem ROM) model) []
            (mkCfg (advance_past_svc (apply_effect (ecall_st regs pc mem ROM) eff)) m').
Proof.
  intros regs pc mem model w eff m' HF HE Hh Hl Hu Hc Hh' Hl'.
  change ([] : list event) with (([] : list event) ++ []).
  eapply star_cfg_trans.
  - eapply estep_instr; [exact Hh | exact Hl | reflexivity | eapply step_ecall_st; eassumption].
  - apply star_cfg_one. apply sstep_cfg_of_unfiltered; [eapply unfiltered_sysno; [reflexivity | exact Hu]|].
    apply (sstep_of_check segs (ecall_st regs pc mem ROM) model (getr regs 17) eff m' []);
      [exact Hh | reflexivity | exact Hc | exact Hh' | exact Hl'].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma close_check : forall regs pc mem model fd e,
  getr regs 17 = Z_to_bv 64 57 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some e ->
  forall eff, check_syscall (sys_input segs (ecall_st regs pc mem ROM) (getr regs 17)) eff model
              = check_ret_only eff (Z_to_bv 64 0) (with_fds (fd_remove (m_fds model) fd) model) [].
Proof.
  intros regs pc mem model fd e H17 Hfd Hfd32 Hlk eff.
  rewrite (check_syscall_57 segs) by (rewrite H17; apply u64_lit; lia).
  unfold check_close. rewrite ecall_st_gpr0, Hfd, (fd32_id fd Hfd32), Hlk. reflexivity.
Qed.

#[using="Type"] Lemma rz_close_at : forall regs (pc : word) mem model w fd e K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 57 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some e ->
  realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem ROM)
                       (with_fds (fd_remove (m_fds model) fd) model)) K ->
  realizes segs (mkCfg (mkst regs pc mem ROM) model) K.
Proof.
  intros regs pc mem model w fd e K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hc.
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply rz_ret_chk_silent; [exact Hh | reflexivity | rewrite H17; reflexivity | eapply close_check; eassumption
    | cbn; exact Hh | cbn; exact Hlazy | rewrite adv_ret_st; exact Hc].
Qed.

#[using="Type"] Lemma estep_close_at : forall regs (pc : word) mem model w fd e,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 57 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some e ->
  star_cfg segs CFG (mkCfg (mkst regs pc mem ROM) model) []
            (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem ROM)
                   (with_fds (fd_remove (m_fds model) fd) model)).
Proof.
  intros regs pc mem model w fd e HF HE Hh Hlazy H17 Hfd Hfd32 Hlk.
  rewrite <- (adv_ret_st regs pc mem ROM (Z_to_bv 64 0)).
  eapply estep_of_check; [exact HF | exact HE | exact Hh | exact Hlazy | rewrite H17; reflexivity | | cbn; exact Hh | cbn; exact Hlazy].
  rewrite (close_check regs pc mem model fd e H17 Hfd Hfd32 Hlk). apply check_ret_only_ok_iff. auto.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma read_dir_check : forall regs pc mem model fd,
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  access_okb (getr regs 11) (bv_unsigned (getr regs 12)) = true ->
  forall eff, check_syscall (sys_input segs (ecall_st regs pc mem ROM) (getr regs 17)) eff model
              = check_ret_only eff (errno_ret EISDIR) model [].
Proof.
  intros regs pc mem model fd H17 Hfd Hfd32 Hlk Hok eff.
  rewrite (check_syscall_63 segs) by (rewrite H17; apply u64_lit; lia).
  unfold check_read. rewrite ecall_st_gpr0, ecall_st_gpr1, ecall_st_gpr2, Hfd, (fd32_id fd Hfd32), Hlk, Hok.
  reflexivity.
Qed.

#[using="Type"] Lemma rz_read_dir_at : forall regs (pc : word) mem model w fd K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  access_okb (getr regs 11) (bv_unsigned (getr regs 12)) = true ->
  realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem ROM) model) K ->
  realizes segs (mkCfg (mkst regs pc mem ROM) model) K.
Proof.
  intros regs pc mem model w fd K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hok Hc.
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply rz_ret_chk_silent; [exact Hh | reflexivity | rewrite H17; reflexivity | eapply read_dir_check; eassumption
    | exact Hh | exact Hlazy | rewrite adv_ret_st; exact Hc].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rd_bytes (data : list byte) (off cnt : word) : list byte := file_read data off cnt.

#[using="Type"] Lemma read_file_reduce : forall regs pc mem model fd p off data cnt wit,
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdFile p off) ->
  fs_lookup (m_fs model) p = Some data ->
  getr regs 12 = cnt ->
  (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  access_okb (getr regs 11) (bv_unsigned cnt) = true ->
  read_bytes_map (wview segs mem) (getr regs 11) cnt = Some wit ->
  forall eff,
    check_syscall (sys_input segs (ecall_st regs pc mem ROM) (getr regs 17)) eff model =
    let bs := rd_bytes data off cnt in
    let m' := with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model in
    match bs, eff with
    | [], _ => check_ret_only eff (Z_to_bv 64 0) m' []
    | _ :: _, mkEffectU ret [(a, bs')] [] [] [] [] =>
        if bv_eqb a (getr regs 11) && listN_eqb bs' bs && bv_eqb ret (len_word bs) then CheckOk m' [] else CheckReject
    | _, _ => CheckReject
    end.
Proof.
  intros regs pc mem model fd p off data cnt wit H17 Hfd Hfd32 Hlk Hfs H12 Hcnt Hok Hw eff.
  assert (HL : (bv_unsigned (len_word (file_read data off cnt)) <= bv_unsigned cnt)%Z).
  { unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
    pose proof (u64_range cnt) as Hc.
    rewrite length_file_read, Nat2Z.inj_min. unfold word_to_nat. rewrite Z.mod_small; lia. }
  rewrite (check_syscall_63 segs) by (rewrite H17; apply u64_lit; lia).
  unfold check_read. rewrite ecall_st_gpr0, ecall_st_gpr1, ecall_st_gpr2, Hfd, (fd32_id fd Hfd32), Hlk, H12.
  rewrite Hok. cbn [negb]. cbv beta iota.
  rewrite (rw_count_clamp_of_rw _ (proj2 Hcnt)), Z_to_bv_bv_unsigned.
  rewrite Hfs. cbv beta iota zeta.
  rewrite in_wmem_si, ecall_st_writable.
  rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw). cbv beta iota.
  unfold rd_bytes. reflexivity.
Qed.

#[using="Type"] Lemma read_file_chk_facts : forall regs pc mem model fd p off data cnt wit,
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdFile p off) ->
  fs_lookup (m_fs model) p = Some data ->
  getr regs 12 = cnt ->
  (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  access_okb (getr regs 11) (bv_unsigned cnt) = true ->
  read_bytes_map (wview segs mem) (getr regs 11) cnt = Some wit ->
  let chk := fun eff => check_syscall (sys_input segs (ecall_st regs pc mem ROM) (getr regs 17)) eff model in
  let bs := rd_bytes data off cnt in
  let m' := with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model in
  let E := mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) [] in
  chk E = CheckOk m' []
  /\ (forall eff m2 evs2, chk eff = CheckOk m2 evs2 -> eff = E /\ m2 = m' /\ evs2 = [])
  /\ (forall eff, chk eff <> CheckUnmodeled).
Proof.
  intros regs pc mem model fd p off data cnt wit H17 Hfd Hfd32 Hlk Hfs H12 Hcnt Hok Hw.
  cbv zeta.
  pose proof (read_file_reduce regs pc mem model fd p off data cnt wit H17 Hfd Hfd32 Hlk Hfs H12 Hcnt Hok Hw) as R.
  cbv zeta in R.
  split; [| split].
  - rewrite R. destruct (rd_bytes data off cnt) as [|b bsr] eqn:Hbs.
    + apply check_ret_only_ok_iff. cbn [delivered_writes]. unfold len_word. cbn [length Z.of_nat]. auto.
    + cbn [delivered_writes]. rewrite bv_eqb_refl, (proj2 (listN_eqb_eq _ _) eq_refl), bv_eqb_refl. reflexivity.
  - intros eff m2 evs2 Hc. rewrite R in Hc. destruct (rd_bytes data off cnt) as [|b bsr] eqn:Hbs.
    + apply check_ret_only_ok_iff in Hc. destruct Hc as (-> & -> & ->).
      cbn [delivered_writes]. unfold len_word. cbn [length]. auto.
    + destruct eff as [ret ws zs us cs copyins].
      destruct ws as [|[a bs'] [|? ?]]; try discriminate.
      destruct zs as [|? ?]; [|discriminate].
      destruct us as [|? ?]; [|discriminate].
      destruct cs as [|? ?]; [|discriminate].
      destruct copyins as [|? ?]; [|discriminate].
      destruct (bv_eqb a (getr regs 11) && listN_eqb bs' (b :: bsr) && bv_eqb ret (len_word (b :: bsr))) eqn:Hb;
        [|discriminate].
      apply andb_true_iff in Hb as [Hb Hr]. apply andb_true_iff in Hb as [Ha Hbs'].
      apply bv_eqb_eq in Ha. apply bv_eqb_eq in Hr. apply listN_eqb_eq in Hbs'.
      injection Hc as <- <-. subst. cbn [delivered_writes]. auto.
  - intros eff Hc. rewrite R in Hc. destruct (rd_bytes data off cnt) as [|b bsr].
    + exact (check_ret_only_no_unmodeled _ _ _ _ Hc).
    + destruct eff as [ret ws zs us cs copyins].
      destruct ws as [|[a bs'] [|? ?]]; try discriminate.
      destruct zs as [|? ?]; [|discriminate].
      destruct us as [|? ?]; [|discriminate].
      destruct cs as [|? ?]; [|discriminate].
      destruct copyins as [|? ?]; [|discriminate].
      destruct (bv_eqb a (getr regs 11) && listN_eqb bs' (b :: bsr) && bv_eqb ret (len_word (b :: bsr)));
        discriminate.
Qed.

#[using="Type"] Lemma rz_read_file_at : forall regs (pc : word) mem model w fd p off data cnt wit K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdFile p off) ->
  fs_lookup (m_fs model) p = Some data ->
  getr regs 12 = cnt ->
  (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  access_okb (getr regs 11) (bv_unsigned cnt) = true ->
  read_bytes_map (wview segs mem) (getr regs 11) cnt = Some wit ->
  realizes segs (mkCfg (mkst (regupd regs 10 (len_word (rd_bytes data off cnt))) (v_addi pc 4)
                             (wbytes mem (getr regs 11) (rd_bytes data off cnt)) ROM)
                       (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word (rd_bytes data off cnt)))) model)) K ->
  realizes segs (mkCfg (mkst regs pc mem ROM) model) K.
Proof.
  intros regs pc mem model w fd p off data cnt wit K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hfs H12 Hcnt Hok Hw Hc.
  destruct (read_file_chk_facts regs pc mem model fd p off data cnt wit H17 Hfd Hfd32 Hlk Hfs H12 Hcnt Hok Hw)
    as (Hok1 & Hinv & Hnu).
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply (rz_sys_chk_const segs (ecall_st regs pc mem ROM) model (getr regs 17) _ unit
            (fun _ => _) (fun _ => _) K tt);
    [exact Hh | reflexivity | rewrite H17; reflexivity | intros eff; reflexivity
    | intros []; exact Hok1
    | intros eff m2 evs2 Hck; destruct (Hinv eff m2 evs2 Hck) as (-> & -> & ->); exists tt; auto
    | exact Hnu
    | intros []; cbn; exact Hh
    | intros []; cbn; exact Hlazy
    | intros []; rewrite adv_delivered_st, write_to_mem_wbytes; exact Hc ].
Qed.

#[using="Type"] Lemma estep_read_file_at : forall regs (pc : word) mem model w fd p off data cnt wit,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdFile p off) ->
  fs_lookup (m_fs model) p = Some data ->
  getr regs 12 = cnt ->
  (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  access_okb (getr regs 11) (bv_unsigned cnt) = true ->
  read_bytes_map (wview segs mem) (getr regs 11) cnt = Some wit ->
  star_cfg segs CFG (mkCfg (mkst regs pc mem ROM) model) []
       (mkCfg (mkst (regupd regs 10 (len_word (rd_bytes data off cnt))) (v_addi pc 4)
                    (wbytes mem (getr regs 11) (rd_bytes data off cnt)) ROM)
              (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word (rd_bytes data off cnt)))) model)).
Proof.
  intros regs pc mem model w fd p off data cnt wit HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hfs H12 Hcnt Hok Hw.
  destruct (read_file_chk_facts regs pc mem model fd p off data cnt wit H17 Hfd Hfd32 Hlk Hfs H12 Hcnt Hok Hw)
    as (Hok1 & _ & _).
  rewrite <- write_to_mem_wbytes, <- adv_delivered_st.
  eapply estep_of_check; [exact HF | exact HE | exact Hh | exact Hlazy | rewrite H17; reflexivity | exact Hok1 | cbn; exact Hh | cbn; exact Hlazy].
Qed.

#[using="Type"] Lemma estep_read_dir_at : forall regs (pc : word) mem model w fd,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  access_okb (getr regs 11) (bv_unsigned (getr regs 12)) = true ->
  star_cfg segs CFG (mkCfg (mkst regs pc mem ROM) model) []
       (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem ROM) model).
Proof.
  intros regs pc mem model w fd HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hok.
  rewrite <- (adv_ret_st regs pc mem ROM (errno_ret EISDIR)).
  eapply estep_of_check; [exact HF | exact HE | exact Hh | exact Hlazy | rewrite H17; reflexivity | | exact Hh | exact Hlazy].
  rewrite (read_dir_check regs pc mem model fd H17 Hfd Hfd32 Hlk Hok). apply check_ret_only_ok_iff. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Notation "'path_at' mem a" := (read_cstr (mrb segs mem) a) (at level 10, mem at level 9, a at level 9, only parsing).

(* [comment removed for export] *)
#[using="Type"] Lemma openat_toolong_check' : forall regs pc mem model,
  getr regs 17 = Z_to_bv 64 56 ->
  modeled_open_flags (getr regs 12) = true ->
  path_at mem (getr regs 11) = CstrTooLong ->
  forall eff, check_syscall (sys_input segs (ecall_st regs pc mem ROM) (getr regs 17)) eff model
              = check_ret_only_copyins (open_copyins (ecall_st regs pc mem ROM)) eff (errno_ret ENAMETOOLONG) model [].
Proof.
  intros regs pc mem model H17 Hfl Hp eff.
  apply openat_toolong_check; [rewrite H17; apply u64_lit; lia | rewrite ecall_st_gpr2; exact Hfl |].
  rewrite ecall_st_read_byte, ecall_st_gpr1. exact Hp.
Qed.

#[using="Type"] Lemma rz_openat_toolong_at : forall regs (pc : word) mem model w K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 56 ->
  modeled_open_flags (getr regs 12) = true ->
  path_at mem (getr regs 11) = CstrTooLong ->
  realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENAMETOOLONG)) (v_addi pc 4) mem ROM) model) K ->
  realizes segs (mkCfg (mkst regs pc mem ROM) model) K.
Proof.
  intros regs pc mem model w K HF HE Hh Hlazy H17 Hfl Hp Hc.
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply rz_ret_only_copyins_silent; [exact Hh | reflexivity | rewrite H17; reflexivity | eapply openat_toolong_check'; eassumption
    | exact Hh | exact Hlazy | rewrite adv_setgpr0_st; exact Hc].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma openat_enoent_check : forall regs pc mem model p,
  getr regs 17 = Z_to_bv 64 56 ->
  getr regs 10 = AT_FDCWD ->
  path_at mem (getr regs 11) = CstrOk p ->
  Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
  (path_eqb p [] = true \/ (openat_plain_name p = true /\ fs_lookup (m_fs model) p = None)) ->
  forall eff, check_syscall (sys_input segs (ecall_st regs pc mem ROM) (getr regs 17)) eff model
              = check_ret_only_copyins (open_copyins (ecall_st regs pc mem ROM)) eff (errno_ret ENOENT) model [].
Proof.
  intros regs pc mem model p H17 Hdirfd Hp Hfl Hcase eff.
  rewrite (check_syscall_56 segs) by (rewrite H17; apply u64_lit; lia).
  unfold check_openat.
  rewrite ecall_st_gpr2, (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota.
  unfold Prelude.check_copyins_after, Open.check_openat_body.
  rewrite in_mem_si, ecall_st_read_byte, ecall_st_gpr1. rewrite Hp. cbv beta iota zeta.
  destruct Hcase as [Hpe | [Hplain Hfs]].
  - rewrite Hpe. cbv beta iota. apply check_copyins_after_ret_only.
  - destruct (path_eqb p []) eqn:Hpe; cbv beta iota; [apply check_copyins_after_ret_only|].
    rewrite ecall_st_gpr0, Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
    unfold Open.check_openat_resolved.
    rewrite (openat_plain_name_noslash _ Hplain). cbv beta iota.
    rewrite Hfl, Z.eqb_refl. cbv beta iota.
    unfold Open.check_openat_read. rewrite (openat_plain_name_nodirref _ Hplain), Hfs.
    apply check_copyins_after_ret_only.
Qed.

#[using="Type"] Lemma rz_openat_enoent_at : forall regs (pc : word) mem model w p K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 56 ->
  getr regs 10 = AT_FDCWD ->
  path_at mem (getr regs 11) = CstrOk p ->
  Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
  (path_eqb p [] = true \/ (openat_plain_name p = true /\ fs_lookup (m_fs model) p = None)) ->
  realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4) mem ROM) model) K ->
  realizes segs (mkCfg (mkst regs pc mem ROM) model) K.
Proof.
  intros regs pc mem model w p K HF HE Hh Hlazy H17 Hdirfd Hp Hfl Hcase Hc.
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply rz_ret_only_copyins_silent; [exact Hh | reflexivity | rewrite H17; reflexivity | eapply openat_enoent_check; eassumption
    | exact Hh | exact Hlazy | rewrite adv_setgpr0_st; exact Hc].
Qed.

(* [comment removed for export] *)
Definition open_file_model (model : Model) (p : path) (fd : word) : Model :=
  with_fds (fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model.

#[using="Type"] Lemma openat_file_check : forall regs pc mem model p d,
  getr regs 17 = Z_to_bv 64 56 ->
  getr regs 10 = AT_FDCWD ->
  path_at mem (getr regs 11) = CstrOk p ->
  path_eqb p [] = false ->
  Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
  openat_plain_name p = true ->
  fs_lookup (m_fs model) p = Some d ->
  forall eff, check_syscall (sys_input segs (ecall_st regs pc mem ROM) (getr regs 17)) eff model
              = check_open_result_copyins (open_copyins (ecall_st regs pc mem ROM)) eff model (open_file_model model p).
Proof.
  intros regs pc mem model p d H17 Hdirfd Hp Hpe Hfl Hplain Hfs eff.
  unfold open_file_model.
  apply (openat_rd_check segs (ecall_st regs pc mem ROM) (getr regs 17) model p d).
  - rewrite H17; apply u64_lit; lia.
  - rewrite ecall_st_gpr0; exact Hdirfd.
  - rewrite ecall_st_read_byte, ecall_st_gpr1. exact Hp.
  - exact Hpe.
  - rewrite ecall_st_gpr2. exact Hfl.
  - exact Hplain.
  - exact Hfs.
Qed.

#[using="Type"] Lemma rz_openat_file_at : forall regs (pc : word) mem model w p d A B,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 56 ->
  getr regs 10 = AT_FDCWD ->
  path_at mem (getr regs 11) = CstrOk p ->
  path_eqb p [] = false ->
  Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
  openat_plain_name p = true ->
  fs_lookup (m_fs model) p = Some d ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  (forall e, In e openat_errnos ->
     realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem ROM) model) A) ->
  realizes segs (mkCfg (mkst (regupd regs 10 (alloc_fd (m_fds model))) (v_addi pc 4) mem ROM)
                       (open_file_model model p (alloc_fd (m_fds model)))) B ->
  realizes segs (mkCfg (mkst regs pc mem ROM) model) (t_alt2 A B).
Proof.
  intros regs pc mem model w p d A B HF HE Hh Hlazy H17 Hdirfd Hp Hpe Hfl Hplain Hfs Hfree HA HB.
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply (rz_open segs (ecall_st regs pc mem ROM) model (getr regs 17) _ (open_file_model model p));
    [exact Hh | exact Hlazy | reflexivity | rewrite H17; reflexivity | eapply openat_file_check; eassumption
    | intros fd; cbn; exact Hh | intros fd; cbn; exact Hlazy | exact Hfree
    | intros e He; rewrite adv_setgpr0_st; apply HA; exact He
    | rewrite adv_setgpr0_st; exact HB ].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma estep_openat_file_at : forall regs (pc : word) mem model w p d,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 56 ->
  getr regs 10 = AT_FDCWD ->
  path_at mem (getr regs 11) = CstrOk p ->
  path_eqb p [] = false ->
  Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
  openat_plain_name p = true ->
  fs_lookup (m_fs model) p = Some d ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  star_cfg segs CFG (mkCfg (mkst regs pc mem ROM) model) []
       (mkCfg (mkst (regupd regs 10 (alloc_fd (m_fds model))) (v_addi pc 4) mem ROM)
              (open_file_model model p (alloc_fd (m_fds model)))).
Proof.
  intros regs pc mem model w p d HF HE Hh Hlazy H17 Hdirfd Hp Hpe Hfl Hplain Hfs Hfree.
  pose proof (node_open segs (ecall_st regs pc mem ROM) model (getr regs 17) _ (open_file_model model p)
                Hh Hlazy eq_refl (openat_file_check regs pc mem model p d H17 Hdirfd Hp Hpe Hfl Hplain Hfs)
                (fun fd => Hh) (fun fd => Hlazy) Hfree) as [Hcomp _].
  change ([] : list event) with (([] : list event) ++ []).
  eapply star_cfg_trans.
  - eapply estep_instr; [exact Hh | exact Hlazy | reflexivity | eapply step_ecall_st; eassumption].
  - apply star_cfg_one. apply sstep_cfg_of_unfiltered; [eapply unfiltered_sysno; [reflexivity | rewrite H17; reflexivity]|].
    specialize (Hcomp (inr tt)). cbn [open_nx] in Hcomp.
    rewrite adv_setgpr0_st in Hcomp. exact Hcomp.
Qed.

(* [comment removed for export] *)
Definition open_dir_model (model : Model) (fd : word) : Model :=
  with_fds (fd_insert (m_fds model) fd FdDir) model.

#[using="Type"] Lemma openat_dir_check : forall regs pc mem model p,
  getr regs 17 = Z_to_bv 64 56 ->
  getr regs 10 = AT_FDCWD ->
  path_at mem (getr regs 11) = CstrOk p ->
  Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
  path_is_dirref p = true ->
  forall eff, check_syscall (sys_input segs (ecall_st regs pc mem ROM) (getr regs 17)) eff model
              = check_open_result_copyins (open_copyins (ecall_st regs pc mem ROM)) eff model (open_dir_model model).
Proof.
  intros regs pc mem model p H17 Hdirfd Hp Hfl Hdir eff.
  assert (Hpe : path_eqb p [] = false).
  { unfold path_is_dirref in Hdir. destruct p; [cbn in Hdir; discriminate | reflexivity]. }
  rewrite (check_syscall_56 segs) by (rewrite H17; apply u64_lit; lia).
  unfold check_openat.
  rewrite ecall_st_gpr2, (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota.
  unfold Prelude.check_copyins_after, Open.check_openat_body.
  rewrite in_mem_si, ecall_st_read_byte, ecall_st_gpr1. rewrite Hp. cbv beta iota zeta.
  rewrite Hpe. cbv beta iota.
  rewrite ecall_st_gpr0, Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
  unfold Open.check_openat_resolved.
  rewrite (path_is_dirref_no_slash _ Hdir). cbv beta iota.
  rewrite Hfl, Z.eqb_refl. cbv beta iota.
  unfold Open.check_openat_read. rewrite Hdir.
  unfold check_open_result_copyins, open_copyins, open_dir_model.
  destruct (check_open_result (clear_copyins eff) model
              (fun fd : word => with_fds (fd_insert (m_fds model) fd FdDir) model)) eqn:Hr;
    [reflexivity | reflexivity | exfalso; now apply check_open_result_never_unmodeled in Hr].
Qed.

#[using="Type"] Lemma rz_openat_dir_at : forall regs (pc : word) mem model w p A B,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 56 ->
  getr regs 10 = AT_FDCWD ->
  path_at mem (getr regs 11) = CstrOk p ->
  Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
  path_is_dirref p = true ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  (forall e, In e openat_errnos ->
     realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem ROM) model) A) ->
  realizes segs (mkCfg (mkst (regupd regs 10 (alloc_fd (m_fds model))) (v_addi pc 4) mem ROM)
                       (open_dir_model model (alloc_fd (m_fds model)))) B ->
  realizes segs (mkCfg (mkst regs pc mem ROM) model) (t_alt2 A B).
Proof.
  intros regs pc mem model w p A B HF HE Hh Hlazy H17 Hdirfd Hp Hfl Hdir Hfree HA HB.
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply (rz_open segs (ecall_st regs pc mem ROM) model (getr regs 17) _ (open_dir_model model));
    [exact Hh | exact Hlazy | reflexivity | rewrite H17; reflexivity | eapply openat_dir_check; eassumption
    | intros fd; cbn; exact Hh | intros fd; cbn; exact Hlazy | exact Hfree
    | intros e He; rewrite adv_setgpr0_st; apply HA; exact He
    | rewrite adv_setgpr0_st; exact HB ].
Qed.


(* [comment removed for export] *)

End WithSegs.
End NodesFs.

(* [comment removed for export] *)
Module NodesMm.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require MmapSim AllocSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require FileSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require Footprint__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefNodes. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.StreamExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.FileSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.FileSim__Common.AgentNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.Footprint__Common.SpecConsts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefNodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.ErrEscape.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance nodesmm_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition t_if_adm (adm : bool) (KA KB : TSet) : TSet :=
  if adm then KB else KA.

Lemma t_if_adm_absorb : forall adm K, t_eq (t_if_adm adm K K) K.
Proof. intros [|] K tr; unfold t_if_adm; tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_errnos_is_ENOMEM : forall e, In e mmap_errnos -> e = ENOMEM.
Proof. intros e [<-|[]]. reflexivity. Qed.

Lemma mprotect_errnos_is_ENOMEM : forall e, In e mprotect_errnos -> e = ENOMEM.
Proof. intros e [<-|[]]. reflexivity. Qed.

Lemma a1_len_facts : forall regs pc mem rom (len : Z),
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  bv_unsigned (ms_gpr (epend regs pc mem rom (getr regs 17)) 1) = len
  /\ ms_gpr (epend regs pc mem rom (getr regs 17)) 1 <> Z_to_bv 64 0.
Proof.
  intros regs pc mem rom len H11 Hlen. rewrite ms_gpr_epend1, H11. split.
  - apply u64_lit. lia.
  - intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia.
Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma brk_refusal_b_eq : forall ms x8 model r,
  bv_unsigned x8 = 214%Z ->
  refusal_b (sys_input segs ms x8) model r = brk_refusal_b model (ms_gpr ms 0) r.
Proof.
  intros ms x8 model r Hno. unfold refusal_b. rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.

#[using="Type"] Lemma mprotect_refusal_b : forall ms x8 model r,
  bv_unsigned x8 = 226%Z ->
  refusal_b (sys_input segs ms x8) model r = errno_ret_in mprotect_errnos r.
Proof.
  intros ms x8 model r Hno. unfold refusal_b. rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_alloc_keep : forall ms model x8 (I : Type) (effs : I -> SyscallEffect) (ms' : I -> Model)
                             (keep : I -> bool) (i0 : I) K,
  ms_svc_pending ms = Some x8 -> alloc_no (bv_unsigned x8) = true ->
  node_ok segs (mkCfg ms model) I (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) ->
  (forall i, keep i = true -> refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false) ->
  (forall i, keep i = false -> refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = true) ->
  keep i0 = true ->
  (forall i, keep i = true ->
     realizes segs (mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) K) ->
  realizes segs (mkCfg ms model) K.
Proof.
  intros ms model x8 I effs ms' keep i0 K Hsvc Ha Hnode Hk Hd Hi0 HK.
  eapply (rz_silent segs _ {i : I | keep i = true} _ (exist _ i0 Hi0)).
  - exact (cnode_prune segs ms model x8 I (fun _ => []) effs ms' keep i0 Hsvc Ha Hnode Hk Hd Hi0).
  - intros [i Hki]. cbn [proj1_sig]. apply HK. exact Hki.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma star_cfg_succ_nr : forall ms model x8 eff m',
  ms_svc_pending ms = Some x8 ->
  sstep segs (mkCfg ms model) [] (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')) ->
  refusal_b (sys_input segs ms x8) model (eff_ret eff) = false ->
  star_cfg segs CFG (mkCfg ms model) [] (mkCfg (advance_past_svc (apply_effect ms eff)) m').
Proof.
  intros ms model x8 eff m' Hsvc Hss Hnr. apply star_cfg_one.
  apply (sstep_cfg_of_sstep_succ segs ms model x8); [exact Hsvc | exact Hss |].
  intros eff' m'' E. rewrite <- (svc_succ_ret ms eff eff' m' m'' (f_equal SNext E)). exact Hnr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma rz_set_tid : forall regs (pc : word) mem rom model K w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     realizes segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model K w HF HE Hh Hlazy H17 Htid Hk.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  assert (Hno : bv_unsigned (getr regs 17) = 96%Z) by (rewrite H17; apply u64_lit; lia).
  apply (rz_conseq segs _ (t_alt (fun _ : tid_I => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ (Z_to_bv 64 1) one_tid_ok); exact Ht]].
  eapply rz_cases; [exact (exist _ (Z_to_bv 64 1) one_tid_ok)
                   | apply cnode_lift; [eapply unfiltered_sysno; [apply epend_svc | rewrite Hno; reflexivity]
                                       | eapply node_set_tid; [exact Hh | exact Hlazy | reflexivity | exact Hno | exact Htid]] |].
  intros [t Ht]. cbn [proj1_sig]. rewrite adv_set_epend. apply Hk. exact Ht.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma rz_brk_query : forall regs (pc : word) mem rom model w K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 214 ->
  getr regs 10 = Z_to_bv 64 0 ->
  realizes segs (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem rom)
                       model) K ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w K HF HE Hh Hlazy H17 H10 Hc.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = vm_brk (m_vmmaps model)).
  { intros r. rewrite H0. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
    unfold w_is0. rewrite bv_eqb_refl. cbn [orb]. apply bv_eqb_eq. }
  assert (Hq : brk_resolution_ok model (ms_gpr ms 0) (vm_brk (m_vmmaps model))) by (apply Hcases; reflexivity).
  apply (rz_conseq segs _ (t_alt (fun _ : {r : word | brk_resolution_ok model (ms_gpr ms 0) r} => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ _ Hq); exact Ht]].
  eapply rz_cases; [exact (exist _ _ Hq) | |].
  { apply cnode_lift_nr; [| eapply node_brk; [exact Hh | exact Hlazy | reflexivity | exact Hno]].
    intros y eff m' evs Hy _. cbn in Hy |- *. injection Hy as <-.
    rewrite (brk_refusal_b_eq ms _ model _ Hno), H0. unfold brk_refusal_b, w_is0. rewrite bv_eqb_refl. reflexivity. }
  intros [r Hr]. cbn [proj1_sig].
  pose proof (proj1 (Hcases r) Hr) as Er. subst r.
  rewrite H0, brk_zeros_query, brk_unmaps_keep.
  rewrite (brk_model_query _ model eq_refl), vmmaps_eta, with_vmmaps_eta.
  unfold ms. rewrite adv_ret_epend. exact Hc.
Qed.

(* [comment removed for export] *)
Definition brk_grown_model (d : Z) (m : Model) : Model :=
  let h := m_vmmaps m in
  with_vmmaps (mkVmMapsFull (vm_reserved h) ((vm_brk h, Z_to_bv 64 d) :: vm_maps h)
                 (vm_noaccess h) (vm_start_brk h)
                 (Z_to_bv 64 (bv_unsigned (vm_brk h) + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m.

#[using="Type"] Lemma brk_grown_model_halted : forall d m, m_halted (brk_grown_model d m) = m_halted m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma brk_grown_model_lazy : forall d m, m_vm_lazy (brk_grown_model d m) = m_vm_lazy m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma brk_grown_model_mat : forall d m, m_vm_materialized (brk_grown_model d m) = m_vm_materialized m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma brk_grown_model_fs : forall d m, m_fs (brk_grown_model d m) = m_fs m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma brk_grown_model_fds : forall d m, m_fds (brk_grown_model d m) = m_fds m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma brk_grown_model_tid : forall d m, m_tid (brk_grown_model d m) = m_tid m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma brk_grown_model_vm : forall d m,
  m_vmmaps (brk_grown_model d m)
  = mkVmMapsFull (vm_reserved (m_vmmaps m)) ((vm_brk (m_vmmaps m), Z_to_bv 64 d) :: vm_maps (m_vmmaps m))
      (vm_noaccess (m_vmmaps m)) (vm_start_brk (m_vmmaps m))
      (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps m)) + d)) (vm_limit (m_vmmaps m))
      (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition brk_grow_adm (d : Z) (m : Model) : bool :=
  Mmap.brk_grow_ok m (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps m)) + d))
                     (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps m)) + d)).

#[using="Type"] Lemma rz_brk_grow : forall regs (pc : word) mem rom model w (d : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->
  brk_grow_adm d model = true ->
  (* [comment removed for export] *)
  realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                             (zfill b (Z_to_bv 64 d) mem) rom)
                       (brk_grown_model d model)) KB ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w d KB HF HE Hh Hlazy H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm HB.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> (r = b \/ (r = req /\ Mmap.brk_grow_ok model req req = true))).
  { intros r. rewrite H0. apply brk_r_ok_grow_cases; fold h; fold b; rewrite ?Hureq; lia. }
  assert (Hgrow : brk_resolution_ok model (ms_gpr ms 0) req)
    by (apply Hcases; right; split; [reflexivity | exact Hadm]).
  assert (Hneq : req <> b).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E. unfold b in E. lia. }
  (* [comment removed for export] *)
  assert (Hrb : forall r, refusal_b (sys_input segs ms (getr regs 17)) model r = bv_eqb r b).
  { intros r. rewrite (brk_refusal_b_eq ms _ model r Hno), H0. unfold brk_refusal_b. fold h. fold b.
    unfold w_is0. rewrite (bv_eqb_neq _ _ Hneq).
    replace (bv_eqb req (Z_to_bv 64 0)) with false
      by (symmetry; apply bv_eqb_neq; intros E; apply (f_equal bv_unsigned) in E; rewrite Hureq in E;
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E; lia).
    unfold min_brk. fold h. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
  set (I := {r : word | brk_resolution_ok model (ms_gpr ms 0) r}).
  set (keep := fun i : I => negb (bv_eqb (proj1_sig i) b)).
  assert (Hk0 : keep (exist _ req Hgrow) = true) by (unfold keep; cbn [proj1_sig]; rewrite (bv_eqb_neq _ _ Hneq); reflexivity).
  pose proof (cnode_prune segs ms model (getr regs 17) I (fun _ => [])
                (fun i => mkEffectU (proj1_sig i) [] (brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
                                    (brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])
                (fun i => brk_model (ms_gpr ms 0) (proj1_sig i) model) keep (exist _ req Hgrow)
                (epend_svc _ _ _ _ _) ltac:(rewrite Hno; reflexivity)
                (node_brk segs ms model (getr regs 17) Hh Hlazy (epend_svc _ _ _ _ _) Hno)) as Hc.
  eapply (rz_silent segs _ {i : I | keep i = true} _ (exist _ (exist _ req Hgrow) Hk0)).
  - apply Hc.
    + intros [r Hr] Hk. cbn [proj1_sig eff_ret] in *. rewrite Hrb. unfold keep in Hk. cbn [proj1_sig] in Hk.
      destruct (bv_eqb r b); [discriminate Hk | reflexivity].
    + intros [r Hr] Hk. cbn [proj1_sig eff_ret] in *. rewrite Hrb. unfold keep in Hk. cbn [proj1_sig] in Hk.
      destruct (bv_eqb r b); [reflexivity | discriminate Hk].
    + exact Hk0.
  - intros [[r Hr] Hk]. cbn [proj1_sig]. fold h.
    destruct (proj1 (Hcases r) Hr) as [-> | [-> Hg]].
    + exfalso. unfold keep in Hk. cbn [proj1_sig] in Hk. rewrite bv_eqb_refl in Hk. discriminate Hk.
    + assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
      assert (Hreq0 : req <> Z_to_bv 64 0).
      { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
        change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
      rewrite H0. fold b. rewrite (brk_zeros_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
      unfold brk_page_range.
      rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
      rewrite (page_round_up_Z_aligned (bv_unsigned req))
        by (rewrite Hureq; first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
      rewrite (proj2 (Z.ltb_lt _ _) Hlt).
      replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
      rewrite Hureq. replace (bv_unsigned b + d - bv_unsigned b)%Z with d by lia.
      unfold req, b, h. rewrite (brk_model_grow_eq model d) by assumption.
      unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.
#[using="Type"] Lemma rz_brk_grow_blocked : forall regs (pc : word) mem rom model w (req : word) KA,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  getr regs 10 = req ->
  (0 < bv_unsigned req)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
  (bv_unsigned b <= bv_unsigned req)%Z ->
  Mmap.brk_grow_ok model req req = false ->
  realizes segs (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem rom) model) KA ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) KA.
Proof.
  intros regs pc mem rom model w req KA HF HE Hh Hlazy H17 h b H10 Hpos Hs Hb Hblk HA.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = b).
  { intros r. rewrite H0, (brk_r_ok_grow_cases model req r Hpos Hs Hb). fold h. fold b. split.
    - intros [-> | [-> Hg]]; [reflexivity | rewrite Hblk in Hg; discriminate].
    - intros ->. left. reflexivity. }
  assert (Hkeep : brk_resolution_ok model (ms_gpr ms 0) b) by (apply Hcases; reflexivity).
  apply (rz_conseq segs _ (t_alt (fun _ : {r : word | brk_resolution_ok model (ms_gpr ms 0) r} => KA)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ _ Hkeep); exact Ht]].
  eapply rz_cases; [exact (exist _ b Hkeep) | |].
  { (* [comment removed for export] *)
    destruct (bv_eqb req b) eqn:Ereq.
    - apply bv_eqb_eq in Ereq.
      apply cnode_lift_nr; [| eapply node_brk; [exact Hh | exact Hlazy | apply epend_svc | exact Hno]].
      intros y eff m' evs Hy _. cbn in Hy |- *. injection Hy as <-.
      rewrite (brk_refusal_b_eq ms _ model _ Hno), H0, Ereq. unfold brk_refusal_b. fold h. fold b.
      rewrite bv_eqb_refl. cbn [negb]. rewrite !Bool.andb_false_r. reflexivity.
    - assert (Hneq : req <> b) by (intros E; rewrite E, bv_eqb_refl in Ereq; discriminate Ereq).
      apply cnode_lift_forced; [| eapply node_brk; [exact Hh | exact Hlazy | apply epend_svc | exact Hno]].
      intros y eff m' evs Hy Hspec. cbn in Hy. injection Hy as <-. cbn [cfg_ms cfg_model] in Hspec |- *.
      apply (brk_ok_iff segs ms (getr regs 17) model eff m' evs Hno) in Hspec as (_ & _ & Hok & _).
      apply Hcases in Hok.
      rewrite (brk_refusal_b_eq ms _ model _ Hno), H0, Hok. unfold brk_refusal_b. fold h. fold b.
      unfold w_is0. rewrite (bv_eqb_neq _ _ Hneq), bv_eqb_refl.
      replace (bv_eqb req (Z_to_bv 64 0)) with false
        by (symmetry; apply bv_eqb_neq; intros E; apply (f_equal bv_unsigned) in E;
            change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E; lia).
      unfold min_brk. fold h. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
  intros [r Hr]. cbn [proj1_sig]. fold h.
  pose proof (proj1 (Hcases r) Hr) as Er. subst r. fold b.
  rewrite brk_zeros_keep, brk_unmaps_keep. unfold b, h. rewrite brk_model_keep.
  unfold ms. rewrite adv_ret_epend. exact HA.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_brk_grow_lit : forall regs (pc : word) mem rom model w (d : Z) KA KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->
  (brk_grow_adm d model = false ->
   realizes segs (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem rom) model) KA) ->
  (brk_grow_adm d model = true ->
   realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                              (zfill b (Z_to_bv 64 d) mem) rom)
                        (brk_grown_model d model)) KB) ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) (t_if_adm (brk_grow_adm d model) KA KB).
Proof.
  intros regs pc mem rom model w d KA KB HF HE Hh Hlazy H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 HA HB.
  unfold t_if_adm. destruct (brk_grow_adm d model) eqn:Hadm.
  - eapply rz_brk_grow; try eassumption. apply HB. reflexivity.
  - pose proof (u64_range b) as Hbr.
    eapply (rz_brk_grow_blocked regs pc mem rom model w (Z_to_bv 64 (bv_unsigned b + d)));
      try eassumption; rewrite ?u64_lit by lia; try lia.
    + exact Hs.
    + unfold b, h. lia.
    + apply HA. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma rz_mmap_anon : forall regs (pc : word) mem rom model w (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  (exists a, grant_ok (getr regs 10) model a nZ = true) ->
  (forall a, grant_ok (getr regs 10) model a nZ = true ->
     realizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom)
                         (mmap_model a n model)) KB) ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w len KB HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 nZ n Hex HB.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  destruct (a1_len_facts regs pc mem rom len H11 Hlen) as [Hu1 Hne1]. fold ms in Hu1, Hne1.
  assert (Hpr : page_round_up (ms_gpr ms 1) = n).
  { unfold page_round_up. rewrite Hu1. reflexivity. }
  assert (Hargs : mmap_args_ok ms).
  { unfold mmap_args_ok, ms.
    rewrite ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H12, H13, H14, H15. repeat split; try reflexivity. exact Hne1. }
  assert (H0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; rewrite ms_gpr_epend0; reflexivity).
  eapply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.rz_mmap segs ms model (getr regs 17) KB Hh Hlazy eq_refl
            ltac:(rewrite H17; apply u64_lit; lia) Hargs).
  - intros a Ha. rewrite Hpr. rewrite H0, Hu1 in Ha. unfold ms, epend. rewrite adv_mmap_grant. apply HB. exact Ha.
  - rewrite H0, Hu1. exact Hex.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_mmap_anon_nogrant : forall regs (pc : word) mem rom model w (len : Z) KA,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  (forall a, grant_ok (getr regs 10) model a (page_round_up_Z len) = false) ->
  realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) mem rom) model) KA ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) KA.
Proof.
  intros regs pc mem rom model w len KA HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 Hng HA.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  destruct (a1_len_facts regs pc mem rom len H11 Hlen) as [Hu1 Hne1]. fold ms in Hu1, Hne1.
  assert (Hargs : mmap_args_ok ms).
  { unfold mmap_args_ok, ms.
    rewrite ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H12, H13, H14, H15. repeat split; try reflexivity. exact Hne1. }
  set (I := {e : Z | In e mmap_errnos}).
  apply (rz_conseq segs _ (t_alt (fun _ : I => KA)));
    [| intros tr; split; [intros [_ Ht]; exact Ht
                         | intros Ht; exists (exist _ ENOMEM ENOMEM_in_mmap_errnos); exact Ht]].
  apply (rz_cases segs _ I (fun i => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret (proj1_sig i)))) model)
           (fun _ => KA) (exist _ ENOMEM ENOMEM_in_mmap_errnos)).
  - apply cnode_lift_forced.
    { (* [comment removed for export] *)
      intros y eff m' evs Hy Hspec. cbn in Hy. injection Hy as <-. cbn [cfg_ms cfg_model] in Hspec |- *.
      destruct (mmap_ok_inv segs ms (getr regs 17) model eff m' evs Hno Hargs Hspec)
        as [_ [(er & Her & -> & ->) | (a & Ha & -> & ->)]]; cbn [eff_ret].
      + apply errno_refusal; assumption.
      + exfalso. unfold ms in Ha. rewrite ms_gpr_epend0 in Ha. fold ms in Ha. rewrite Hu1, Hng in Ha. discriminate. }
    split.
    + intros [e He]. cbn [proj1_sig].
      rewrite <- (apply_effect_no_write ms (errno_ret e)).
      apply (sstep_syscall segs ms model (getr regs 17) (mkEffect (errno_ret e) [] []) model model []);
        [exact Hh | reflexivity | apply mmap_fail_ok; assumption | exact Hh
        | apply materialize_model_accesses_no_lazy; exact Hlazy].
    + intros e st Hss.
      destruct (sstep_mmap_inv segs ms model (getr regs 17) e st Hh Hlazy eq_refl Hno Hargs Hss)
        as [-> [(er & Her & ->) | (a & Ha & ->)]].
      * exists (exist _ er Her). split; reflexivity.
      * exfalso. unfold ms in Ha. rewrite ms_gpr_epend0 in Ha. fold ms in Ha. rewrite Hu1, Hng in Ha. discriminate.
  - intros [e He]. cbn [proj1_sig]. rewrite (mmap_errnos_is_ENOMEM e He). unfold ms. rewrite adv_set_epend. exact HA.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma rz_mmap_noaccess : forall regs (pc : word) mem rom model w (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  (exists a, grant_ok_na_pin model a nZ = true) ->
  (forall a, grant_ok_na_pin model a nZ = true ->
     realizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (unfill a n mem) rom)
                         (noaccess_model a n model)) KB) ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w len KB HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 nZ n [a0 Ha0] HB.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  destruct (a1_len_facts regs pc mem rom len H11 Hlen) as [Hu1 Hne1]. fold ms in Hu1, Hne1.
  assert (Hargs : mmap_noaccess_args_ok ms).
  { unfold mmap_noaccess_args_ok, ms.
    rewrite ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H12, H13, H14, H15. repeat split; try reflexivity. exact Hne1. }
  pose proof (fun eff => mmap_noaccess_check segs ms (getr regs 17) model eff Hno Hargs) as Hchk.
  rewrite Hu1 in Hchk. cbv zeta in Hchk. fold nZ in Hchk. fold n in Hchk.
  assert (Hn0 : (0 <= nZ)%Z) by (unfold nZ; apply pruZ_nonneg; lia).
  pose (IB := {a : word | grant_ok_na_pin model a nZ = true}).
  pose (effs := fun i : unit + IB => match i with
                           | inl _ => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                           | inr (exist _ a _) => mkEffectU a [] [] [(a, n)] [] [] end).
  pose (ms' := fun i : unit + IB => match i with
                          | inl _ => model
                          | inr (exist _ a _) => noaccess_model a n model end).
  pose (keep := fun i : unit + IB => match i with inl _ => false | inr _ => true end).
  apply (rz_alloc_keep ms model (getr regs 17) (unit + IB) effs ms' keep (inr (exist _ a0 Ha0)) KB
           eq_refl ltac:(rewrite Hno; reflexivity)).
  - apply (node_chk segs ms model (getr regs 17) (unit + IB) effs ms' Hh eq_refl).
    + intros [[] | [a Ha]]; cbn [effs ms']; rewrite Hchk.
      * rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos). reflexivity.
      * rewrite (grant_na_pin_not_errno model a nZ Hn0 Ha), Ha. cbn [andb].
        rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * destruct us; [|discriminate]. injection Hc as <- <-.
        destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->).
        rewrite (mmap_errnos_is_ENOMEM e He). exists (inl tt). repeat split; reflexivity.
      * destruct (grant_ok_na_pin model r nZ) eqn:Hg; [|discriminate].
        destruct (listNN_eqb us [(r, n)]) eqn:Hl; [|discriminate].
        apply listNN_eqb_eq in Hl. subst us. injection Hc as <- <-.
        exists (inr (exist _ r Hg)). repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
      destruct (grant_ok_na_pin model r nZ && listNN_eqb us [(r, n)])%bool; discriminate.
    + intros [[] | [a Ha]]; cbn [ms']; [exact Hh | unfold noaccess_model; rewrite with_vmmaps_halted; exact Hh].
    + intros [[] | [a Ha]]; cbn [ms']; [exact Hlazy | unfold noaccess_model; rewrite with_vmmaps_lazy'; exact Hlazy].
  - intros [[] | [a Ha]] Hk; [discriminate Hk|]. cbn [effs eff_ret].
    rewrite (mmap_refusal_b segs ms _ model _ Hno). exact (grant_na_pin_not_errno model a nZ Hn0 Ha).
  - intros [[] | [a Ha]] Hk; [|discriminate Hk]. cbn [effs eff_ret]. apply errno_refusal; [exact Hno | exact ENOMEM_in_mmap_errnos].
  - reflexivity.
  - intros [[] | [a Ha]] Hk; [discriminate Hk|]. cbn [effs ms']. unfold ms. rewrite adv_unmaps1_epend. apply HB. exact Ha.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma rz_mprotect : forall regs (pc : word) mem rom model w (addr : word) (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 226 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  getr regs 12 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  mprotect_budget_ok model addr n = true ->
  realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill addr n mem) rom)
                       (mprotect_model addr n model)) KB ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len KB HF HE Hh Hlazy H17 H10 Hal H11 Hlen Hnw H12 n Hna Hma Hbud HB.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 226%Z) by (rewrite H17; apply u64_lit; lia).
  pose proof (fun eff => mprotect_check segs ms (getr regs 17) model eff addr len Hno
                           ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal
                           ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hnw
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12) Hna Hma) as Hchk.
  cbv zeta in Hchk. fold n in Hchk. rewrite Hbud in Hchk.
  pose (I := (unit + unit)%type).
  pose (effs := fun i : I => match i with
                           | inl _ => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                           | inr _ => mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] [] end).
  pose (ms' := fun i : I => match i with inl _ => model | inr _ => mprotect_model addr n model end).
  pose (keep := fun i : I => match i with inl _ => false | inr _ => true end).
  apply (rz_alloc_keep ms model (getr regs 17) I effs ms' keep (inr tt) KB eq_refl ltac:(rewrite Hno; reflexivity)).
  - apply (node_chk segs ms model (getr regs 17) I effs ms' Hh eq_refl).
    + intros [[] | []]; cbn [effs ms']; rewrite Hchk.
      * rewrite (errno_ret_in_intro _ _ ENOMEM_in_mprotect_errnos). reflexivity.
      * change (errno_ret_in mprotect_errnos (Z_to_bv 64 0)) with false.
        unfold w_is0. rewrite bv_eqb_refl. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mprotect_errnos r) eqn:Er.
      * destruct zs; [|discriminate]. injection Hc as <- <-.
        destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->).
        rewrite (mprotect_errnos_is_ENOMEM e He). exists (inl tt). repeat split; reflexivity.
      * cbn [andb] in Hc. destruct (w_is0 r) eqn:E0; [|discriminate].
        destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
        apply listNN_eqb_eq in Hl. subst zs. injection Hc as <- <-.
        unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r.
        exists (inr tt). repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mprotect_errnos r); [destruct zs; discriminate|].
      cbn [andb] in Hc. destruct (w_is0 r && listNN_eqb zs [(addr, n)])%bool; discriminate.
    + intros [[] | []]; cbn [ms']; [exact Hh | unfold mprotect_model; rewrite with_vmmaps_halted; exact Hh].
    + intros [[] | []]; cbn [ms']; [exact Hlazy | unfold mprotect_model; rewrite with_vmmaps_lazy'; exact Hlazy].
  - intros [[] | []] Hk; [discriminate Hk|]. cbn [effs eff_ret]. rewrite (mprotect_refusal_b ms _ model _ Hno). reflexivity.
  - intros [[] | []] Hk; [|discriminate Hk]. cbn [effs eff_ret]. rewrite (mprotect_refusal_b ms _ model _ Hno).
    apply errno_ret_in_intro. exact ENOMEM_in_mprotect_errnos.
  - reflexivity.
  - intros [[] | []] Hk; [discriminate Hk|]. cbn [effs ms']. unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_mprotect_blocked : forall regs (pc : word) mem rom model w (addr : word) (len : Z) KA,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 226 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  getr regs 12 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  mprotect_budget_ok model addr n = false ->
  realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) mem rom) model) KA ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) KA.
Proof.
  intros regs pc mem rom model w addr len KA HF HE Hh Hlazy H17 H10 Hal H11 Hlen Hnw H12 n Hna Hma Hbud HA.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 226%Z) by (rewrite H17; apply u64_lit; lia).
  pose proof (fun eff => mprotect_check segs ms (getr regs 17) model eff addr len Hno
                           ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal
                           ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hnw
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12) Hna Hma) as Hchk.
  cbv zeta in Hchk. fold n in Hchk. rewrite Hbud in Hchk.
  apply (rz_silent1 segs _ (mkCfg (advance_past_svc (apply_effect ms (mkEffect (errno_ret ENOMEM) [] []))) model));
    [| unfold ms; rewrite adv_ret_epend; exact HA].
  apply cnode_lift_forced.
  { intros y eff m' evs Hy Hspec. cbn in Hy. injection Hy as <-. cbn [cfg_ms cfg_model] in Hspec |- *.
    apply check_syscall_ok_iff in Hspec. rewrite Hchk in Hspec.
    destruct eff as [r ws zs us cs ci]. cbn [eff_ret].
    destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    rewrite (mprotect_refusal_b ms _ model _ Hno).
    destruct (errno_ret_in mprotect_errnos r); [reflexivity|]. cbn [andb] in Hspec.
    destruct (w_is0 r && listNN_eqb zs [(addr, n)])%bool; discriminate. }
  apply (node_det segs ms model (getr regs 17) (mkEffect (errno_ret ENOMEM) [] []) model [] Hh eq_refl).
  - intros eff m' evs. rewrite Hchk. split.
    + destruct eff as [r ws zs us cs ci]. intros Hc. destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mprotect_errnos r) eqn:Er.
      * destruct zs; [|discriminate]. injection Hc as <- <-.
        destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->).
        rewrite (mprotect_errnos_is_ENOMEM e He). repeat split; reflexivity.
      * cbn [andb] in Hc. destruct (w_is0 r && listNN_eqb zs [(addr, n)])%bool; discriminate.
    + intros (-> & -> & ->). cbv beta iota. rewrite (errno_ret_in_intro _ _ ENOMEM_in_mprotect_errnos). reflexivity.
  - intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_ret_in mprotect_errnos r); [destruct zs; discriminate|].
    cbn [andb] in Hc. destruct (w_is0 r && listNN_eqb zs [(addr, n)])%bool; discriminate.
  - exact Hh.
  - exact Hlazy.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_mprotect_lit : forall regs (pc : word) mem rom model w (addr : word) (len : Z) KA KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 226 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  getr regs 12 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (mprotect_budget_ok model addr n = false ->
   realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) mem rom) model) KA) ->
  (mprotect_budget_ok model addr n = true ->
   realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill addr n mem) rom)
                        (mprotect_model addr n model)) KB) ->
  realizes segs (mkCfg (mkst regs pc mem rom) model)
           (t_if_adm (mprotect_budget_ok model addr n) KA KB).
Proof.
  intros regs pc mem rom model w addr len KA KB HF HE Hh Hlazy H17 H10 Hal H11 Hlen Hnw H12 n Hna Hma HA HB.
  unfold t_if_adm. destruct (mprotect_budget_ok model addr n) eqn:Hbud.
  - eapply rz_mprotect; try eassumption. apply HB. reflexivity.
  - eapply rz_mprotect_blocked; try eassumption. apply HA. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma rz_munmap : forall regs (pc : word) mem rom model w (a : word) (len : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 215 ->
  getr regs 10 = a -> (bv_unsigned a mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned a + page_round_up_Z len <= TASK_SIZE)%Z ->
  map_has (vm_maps (m_vmmaps model)) a (Z_to_bv 64 (page_round_up_Z len)) = true ->
  realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
                             (unfill a (Z_to_bv 64 (page_round_up_Z len)) mem) rom)
                      (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model)) K ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w a len K HF HE Hh Hlazy H17 H10 Hal H11 Hlen Hts Hhas Hc.
  assert (Hlen' : (len < 2 ^ 64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a).
    unfold TASK_SIZE in Hts. lia. }
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  destruct (a1_len_facts regs pc mem rom len H11 ltac:(lia)) as [Hu1 Hne1]. fold ms in Hu1, Hne1.
  assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)).
  { unfold page_round_up. rewrite Hu1. reflexivity. }
  assert (H0 : ms_gpr ms 0 = a) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hargs : munmap_args_ok ms model).
  { unfold munmap_args_ok. rewrite H0, Hu1, Hpr. repeat split; assumption. }
  eapply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.rz_munmap segs ms model (getr regs 17));
    [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Hargs |].
  unfold munmap_eff. rewrite H0, Hpr. unfold ms. rewrite adv_unmaps1_epend. exact Hc.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_fixed_check : forall ms x8 model eff (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z -> mmap_fixed_args_ok ms ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in mmap_errnos r
        then match us with
             | [] => CheckOk model []
             | _ => if listNN_eqb us [(addr, n)]
                    then CheckOk (fixed_destroyed_model addr n model) []
                    else CheckReject
             end
        else if bv_eqb r addr && listNN_eqb us [(addr, n)]
             then CheckOk (fixed_noaccess_model addr n model) []
             else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff addr len Hno (H1 & H2 & H3 & H4 & H5) H0 Hal Hpos H1' Hlen Htop n Hrf Hmc.
  pose proof (alloc_top_lt (m_vmmaps model)) as Htl.
  assert (Hlen' : (len < 2 ^ 64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). unfold two_pow_64 in Htl. lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1'; apply u64_lit; lia).
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
  rewrite E1, H2, H3, H5, H0, Hu1.
  replace (mmap_off_aligned_b (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
  replace (mmap_anon_b (Z_to_bv 64 50)) with true by (vm_compute; reflexivity).
  replace (mmap_modeled_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0)) with false
    by (vm_compute; reflexivity).
  replace (mmap_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0)) with false
    by (vm_compute; reflexivity).
  replace (mmap_fixed_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0)) with true
    by (vm_compute; reflexivity).
  cbn [negb]. cbv beta iota zeta. pose proof (u64_range addr).
  pose proof (page_round_up_Z_bounds len ltac:(lia)).
  rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64 in *; lia).
  rewrite (proj2 (Z.leb_le _ _) Htop). cbn [negb].
  rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
  rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n. rewrite Hrf, Hmc. cbn [andb].
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
  destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct us; reflexivity].
  destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct us; reflexivity].
  unfold fixed_destroyed_model, fixed_noaccess_model, with_mmap_destroyed, with_mmap_replacement, with_mmap_backing, mmap_fixed_destroyed_next.
  replace (mmap_noreserve_b (Z_to_bv 64 50)) with false by (vm_compute; reflexivity).
  reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_mmap_fixed_noaccess : forall regs (pc : word) mem rom model w (addr : word) (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 50 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (* [comment removed for export] *)
  realizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr n mem) rom)
                       (fixed_noaccess_model addr n model)) KB ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len KB HF HE Hh Hlazy H17 H10 Hal Hpos H11 Hlen Htop H12 H13 H14 H15 n Hrf Hmc HB.
  pose proof (u64_range addr) as Har. pose proof (alloc_top_room (m_vmmaps model)) as Hroom.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as Hprb.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hlen' : (len < 2 ^ 64)%Z) by (unfold two_pow_64, stack_max_size in Hroom; lia).
  assert (Hargs : mmap_fixed_args_ok ms).
  { unfold mmap_fixed_args_ok, ms.
    rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
    intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
  pose proof (fun eff => mmap_fixed_check ms (getr regs 17) model eff addr len Hno Hargs
                           ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                           ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Htop Hrf Hmc) as Hchk.
  cbv zeta in Hchk. fold n in Hchk.
  assert (Haddr_ne : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|]. unfold stack_max_size, two_pow_64 in *. lia. }
  pose (effs := fun i : three => match i with
                           | T1 => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                           | T2 => mkEffectU addr [] [] [(addr, n)] [] []
                           | T3 => mkEffectU (errno_ret ENOMEM) [] [] [(addr, n)] [] [] end).
  pose (ms' := fun i : three => match i with
                          | T1 => model
                          | T2 => fixed_noaccess_model addr n model
                          | T3 => fixed_destroyed_model addr n model end).
  pose (keep := fun i : three => match i with T2 => true | _ => false end).
  apply (rz_alloc_keep ms model (getr regs 17) three effs ms' keep T2 KB eq_refl ltac:(rewrite Hno; reflexivity)).
  - apply (node_chk segs ms model (getr regs 17) three effs ms' Hh eq_refl).
    + intros [| |]; cbn [effs ms']; rewrite Hchk.
      * rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos). reflexivity.
      * rewrite Haddr_ne, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
      * rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos), (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->). rewrite (mmap_errnos_is_ENOMEM e He).
        destruct us.
        -- injection Hc as <- <-. exists T1. repeat split; reflexivity.
        -- destruct (listNN_eqb (p :: us) [(addr, n)]) eqn:Hl; [|discriminate].
           apply listNN_eqb_eq in Hl. rewrite Hl. injection Hc as <- <-. exists T3. repeat split; reflexivity.
      * destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
        destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
        apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-.
        exists T2. repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct us; [discriminate|]; destruct (listNN_eqb _ _); discriminate|].
      destruct (bv_eqb r addr && listNN_eqb us [(addr, n)])%bool; discriminate.
    + intros [| |]; cbn [ms']; [exact Hh | unfold fixed_noaccess_model | unfold fixed_destroyed_model];
        rewrite vm_forget_range_halted, with_vmmaps_halted; exact Hh.
    + intros [| |]; cbn [ms']; [exact Hlazy | unfold fixed_noaccess_model | unfold fixed_destroyed_model];
        apply vm_forget_range_lazy_nil; rewrite with_vmmaps_lazy'; exact Hlazy.
  - intros [| |] Hk; try discriminate Hk. cbn [effs eff_ret]. rewrite (mmap_refusal_b segs ms _ model _ Hno). exact Haddr_ne.
  - intros [| |] Hk; try discriminate Hk; cbn [effs eff_ret]; apply errno_refusal; first [exact Hno | exact ENOMEM_in_mmap_errnos].
  - reflexivity.
  - intros [| |] Hk; try discriminate Hk. cbn [effs ms']. unfold ms. rewrite adv_unmaps1_epend. exact HB.
Qed.

End WithSegs.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_model_vm : forall a n m,
  m_vmmaps (mmap_model a n m)
  = mkVmMapsFull (vm_reserved (m_vmmaps m)) ((a, n) :: vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m))
      (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
      (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m)).
Proof. reflexivity. Qed.
Lemma mmap_model_mat : forall a n m, m_vm_materialized (mmap_model a n m) = m_vm_materialized m.
Proof. reflexivity. Qed.
Lemma mmap_model_fds : forall a n m, m_fds (mmap_model a n m) = m_fds m.
Proof. reflexivity. Qed.
Lemma mmap_model_tid : forall a n m, m_tid (mmap_model a n m) = m_tid m.
Proof. reflexivity. Qed.

Lemma noaccess_model_vm : forall a n m,
  m_vmmaps (noaccess_model a n m)
  = mkVmMapsFull (vm_reserved (m_vmmaps m)) ((a, n) :: vm_maps (m_vmmaps m)) ((a, n) :: vm_noaccess (m_vmmaps m))
      (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
      (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m)).
Proof. reflexivity. Qed.
Lemma noaccess_model_halted : forall a n m, m_halted (noaccess_model a n m) = m_halted m.
Proof. reflexivity. Qed.
Lemma noaccess_model_lazy : forall a n m, m_vm_lazy (noaccess_model a n m) = m_vm_lazy m.
Proof. reflexivity. Qed.
Lemma noaccess_model_mat : forall a n m, m_vm_materialized (noaccess_model a n m) = m_vm_materialized m.
Proof. reflexivity. Qed.
Lemma noaccess_model_fs : forall a n m, m_fs (noaccess_model a n m) = m_fs m.
Proof. reflexivity. Qed.
Lemma noaccess_model_fds : forall a n m, m_fds (noaccess_model a n m) = m_fds m.
Proof. reflexivity. Qed.
Lemma noaccess_model_tid : forall a n m, m_tid (noaccess_model a n m) = m_tid m.
Proof. reflexivity. Qed.

Lemma mprotect_model_vm : forall a n m,
  m_vmmaps (mprotect_model a n m)
  = mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
      (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
      (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
      (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m)).
Proof. reflexivity. Qed.
Lemma mprotect_model_halted : forall a n m, m_halted (mprotect_model a n m) = m_halted m.
Proof. reflexivity. Qed.
Lemma mprotect_model_lazy : forall a n m, m_vm_lazy (mprotect_model a n m) = m_vm_lazy m.
Proof. reflexivity. Qed.
Lemma mprotect_model_mat : forall a n m, m_vm_materialized (mprotect_model a n m) = m_vm_materialized m.
Proof. reflexivity. Qed.
Lemma mprotect_model_fs : forall a n m, m_fs (mprotect_model a n m) = m_fs m.
Proof. reflexivity. Qed.
Lemma mprotect_model_fds : forall a n m, m_fds (mprotect_model a n m) = m_fds m.
Proof. reflexivity. Qed.
Lemma mprotect_model_tid : forall a n m, m_tid (mprotect_model a n m) = m_tid m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma vm_forget_range_fs : forall lo hi m, m_fs (vm_forget_range lo hi m) = m_fs m.
Proof. reflexivity. Qed.
Lemma vm_forget_range_fds : forall lo hi m, m_fds (vm_forget_range lo hi m) = m_fds m.
Proof. reflexivity. Qed.
Lemma vm_forget_range_tid : forall lo hi m, m_tid (vm_forget_range lo hi m) = m_tid m.
Proof. reflexivity. Qed.
Lemma vm_forget_range_vm : forall lo hi m, m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m.
Proof. reflexivity. Qed.
Lemma vm_forget_range_mat_nil : forall lo hi m,
  m_vm_materialized m = [] -> m_vm_materialized (vm_forget_range lo hi m) = [].
Proof. intros lo hi m H. unfold vm_forget_range, with_vm_backing. cbn. rewrite H. reflexivity. Qed.

Lemma munmap_model_fds : forall a n m, m_fds (munmap_model a n m) = m_fds m.
Proof. reflexivity. Qed.
Lemma munmap_model_tid : forall a n m, m_tid (munmap_model a n m) = m_tid m.
Proof. reflexivity. Qed.
Lemma munmap_model_mat_nil : forall a n m,
  m_vm_materialized m = [] -> m_vm_materialized (munmap_model a n m) = [].
Proof. intros. unfold munmap_model, with_mmap_destroyed. apply vm_forget_range_mat_nil. assumption. Qed.
Lemma munmap_model_vm : forall a n m,
  m_vmmaps (munmap_model a n m)
  = mkVmMapsFull (vm_reserved (m_vmmaps m)) (map_remove (vm_maps (m_vmmaps m)) a)
      (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
      (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
      (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m)).
Proof. reflexivity. Qed.

Lemma fixed_noaccess_model_halted : forall a n m, m_halted (fixed_noaccess_model a n m) = m_halted m.
Proof. reflexivity. Qed.
Lemma fixed_noaccess_model_lazy_nil : forall a n m,
  m_vm_lazy m = [] -> m_vm_lazy (fixed_noaccess_model a n m) = [].
Proof. intros. unfold fixed_noaccess_model. apply vm_forget_range_lazy_nil. assumption. Qed.
Lemma fixed_noaccess_model_mat_nil : forall a n m,
  m_vm_materialized m = [] -> m_vm_materialized (fixed_noaccess_model a n m) = [].
Proof. intros. unfold fixed_noaccess_model. apply vm_forget_range_mat_nil. assumption. Qed.
Lemma fixed_noaccess_model_fs : forall a n m, m_fs (fixed_noaccess_model a n m) = m_fs m.
Proof. reflexivity. Qed.
Lemma fixed_noaccess_model_fds : forall a n m, m_fds (fixed_noaccess_model a n m) = m_fds m.
Proof. reflexivity. Qed.
Lemma fixed_noaccess_model_tid : forall a n m, m_tid (fixed_noaccess_model a n m) = m_tid m.
Proof. reflexivity. Qed.
Lemma fixed_noaccess_model_vm : forall a n m,
  m_vmmaps (fixed_noaccess_model a n m)
  = mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
      ((a, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
      (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
      (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m)).
Proof. reflexivity. Qed.

Lemma fixed_destroyed_model_halted : forall a n m, m_halted (fixed_destroyed_model a n m) = m_halted m.
Proof. reflexivity. Qed.
Lemma fixed_destroyed_model_lazy_nil : forall a n m,
  m_vm_lazy m = [] -> m_vm_lazy (fixed_destroyed_model a n m) = [].
Proof. intros. unfold fixed_destroyed_model. apply vm_forget_range_lazy_nil. assumption. Qed.
Lemma fixed_destroyed_model_mat_nil : forall a n m,
  m_vm_materialized m = [] -> m_vm_materialized (fixed_destroyed_model a n m) = [].
Proof. intros. unfold fixed_destroyed_model. apply vm_forget_range_mat_nil. assumption. Qed.
Lemma fixed_destroyed_model_fs : forall a n m, m_fs (fixed_destroyed_model a n m) = m_fs m.
Proof. reflexivity. Qed.
Lemma fixed_destroyed_model_fds : forall a n m, m_fds (fixed_destroyed_model a n m) = m_fds m.
Proof. reflexivity. Qed.
Lemma fixed_destroyed_model_tid : forall a n m, m_tid (fixed_destroyed_model a n m) = m_tid m.
Proof. reflexivity. Qed.
Lemma fixed_destroyed_model_vm : forall a n m,
  m_vmmaps (fixed_destroyed_model a n m)
  = mkVmMapsFull (vm_reserved (m_vmmaps m))
      (maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
      (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
      (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
      (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m)).
Proof. reflexivity. Qed.

Lemma with_tid_vm : forall t m, m_vmmaps (with_tid t m) = m_vmmaps m.
Proof. reflexivity. Qed.
Lemma with_tid_mat : forall t m, m_vm_materialized (with_tid t m) = m_vm_materialized m.
Proof. reflexivity. Qed.
Lemma with_tid_fs : forall t m, m_fs (with_tid t m) = m_fs m.
Proof. reflexivity. Qed.
Lemma with_tid_fds : forall t m, m_fds (with_tid t m) = m_fds m.
Proof. reflexivity. Qed.
Lemma with_tid_tid : forall t m, m_tid (with_tid t m) = Some t.
Proof. reflexivity. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Section EFace.
Variable segs : list Segment.

#[using="Type"] Lemma star_sys : forall regs pc mem rom model w,
  m_halted model = None -> m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  star_cfg segs CFG (mkCfg (mkst regs pc mem rom) model) [] (mkCfg (epend regs pc mem rom (getr regs 17)) model).
Proof.
  intros regs pc mem rom model w Hh Hlazy HF HE.
  apply star_cfg_msteps; [exact Hh | exact Hlazy |].
  apply msteps_one; [reflexivity | eapply step_ecall_epend; eassumption].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma star_sys_eff : forall regs pc mem rom model w eff m',
  m_halted model = None -> m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  alloc_no (bv_unsigned (getr regs 17)) = false ->
  check_syscall (sys_input segs (epend regs pc mem rom (getr regs 17)) (getr regs 17)) eff model = CheckOk m' [] ->
  m_halted m' = None -> m_vm_lazy m' = [] ->
  star_cfg segs CFG (mkCfg (mkst regs pc mem rom) model) []
       (mkCfg (advance_past_svc (apply_effect (epend regs pc mem rom (getr regs 17)) eff)) m').
Proof.
  intros regs pc mem rom model w eff m' Hh Hlazy HF HE Hu Hc Hh' Hlazy'.
  eapply (star_cfg_trans_nil segs); [eapply star_sys; eassumption|].
  apply star_cfg_one. apply sstep_cfg_of_unfiltered; [eapply unfiltered_sysno; [apply epend_svc | exact Hu]|].
  apply (sstep_of_check segs _ model (getr regs 17) eff m' []); try assumption. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma star_sys_eff_nr : forall regs pc mem rom model w eff m',
  m_halted model = None -> m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  check_syscall (sys_input segs (epend regs pc mem rom (getr regs 17)) (getr regs 17)) eff model = CheckOk m' [] ->
  refusal_b (sys_input segs (epend regs pc mem rom (getr regs 17)) (getr regs 17)) model (eff_ret eff) = false ->
  m_halted m' = None -> m_vm_lazy m' = [] ->
  star_cfg segs CFG (mkCfg (mkst regs pc mem rom) model) []
       (mkCfg (advance_past_svc (apply_effect (epend regs pc mem rom (getr regs 17)) eff)) m').
Proof.
  intros regs pc mem rom model w eff m' Hh Hlazy HF HE Hc Hnr Hh' Hlazy'.
  eapply (star_cfg_trans_nil segs); [eapply star_sys; eassumption|].
  apply (star_cfg_succ_nr segs _ model (getr regs 17)); [apply epend_svc | | exact Hnr].
  apply (sstep_of_check segs _ model (getr regs 17) eff m' []); try assumption. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma star_set_tid : forall regs (pc : word) mem rom model w (tid : word),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
  star_cfg segs CFG (mkCfg (mkst regs pc mem rom) model) []
       (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)).
Proof.
  intros regs pc mem rom model w tid HF HE Hh Hlazy H17 Htid Hr.
  assert (Hno : bv_unsigned (getr regs 17) = 96%Z) by (rewrite H17; apply u64_lit; lia).
  pose proof (proj1 (node_set_tid segs (epend regs pc mem rom (getr regs 17)) model (getr regs 17) Hh Hlazy eq_refl
                       Hno Htid) (exist _ tid Hr)) as Hs.
  cbn [proj1_sig] in Hs. rewrite adv_set_epend in Hs.
  eapply (star_cfg_trans_nil segs); [eapply star_sys; eassumption|]. apply star_cfg_one.
  apply sstep_cfg_of_unfiltered; [eapply unfiltered_sysno; [apply epend_svc | rewrite Hno; reflexivity]|]. exact Hs.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma star_brk_query : forall regs (pc : word) mem rom model w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 214 ->
  getr regs 10 = Z_to_bv 64 0 ->
  star_cfg segs CFG (mkCfg (mkst regs pc mem rom) model) []
       (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem rom) model).
Proof.
  intros regs pc mem rom model w HF HE Hh Hlazy H17 H10.
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hq : brk_resolution_ok model (ms_gpr ms 0) (vm_brk (m_vmmaps model))).
  { rewrite H0. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta. unfold w_is0. rewrite bv_eqb_refl. cbn [orb]. apply bv_eqb_refl. }
  pose proof (proj1 (node_brk segs ms model (getr regs 17) Hh Hlazy eq_refl Hno) (exist _ _ Hq)) as Hs.
  cbn [proj1_sig] in Hs.
  eapply (star_cfg_trans_nil segs); [eapply star_sys; eassumption|]. fold ms.
  pose proof (star_cfg_succ_nr segs ms model (getr regs 17) _ _ (epend_svc _ _ _ _ _) Hs) as Hsc.
  cbn [eff_ret] in Hsc. rewrite (brk_refusal_b_eq segs ms _ model _ Hno) in Hsc.
  rewrite H0, brk_zeros_query, brk_unmaps_keep in Hsc.
  rewrite (brk_model_query _ model eq_refl), vmmaps_eta, with_vmmaps_eta in Hsc.
  unfold ms in Hsc. rewrite adv_ret_epend in Hsc. apply Hsc.
  unfold brk_refusal_b, w_is0. rewrite bv_eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma star_brk_blocked : forall regs (pc : word) mem rom model w (req : word),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 214 ->
  getr regs 10 = req ->
  (0 < bv_unsigned req)%Z ->
  (bv_unsigned (vm_start_brk (m_vmmaps model)) <= bv_unsigned req)%Z ->
  (bv_unsigned (vm_brk (m_vmmaps model)) <= bv_unsigned req)%Z ->
  Mmap.brk_grow_ok model req req = false ->
  star_cfg segs CFG (mkCfg (mkst regs pc mem rom) model) []
       (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem rom) model).
Proof.
  intros regs pc mem rom model w req HF HE Hh Hlazy H17 H10 Hpos Hs Hb Hblk.
  eapply (star_cfg_trans_nil segs); [eapply star_sys; eassumption|].
  pose proof (rz_brk_grow_blocked) as _unused.
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = vm_brk (m_vmmaps model)).
  { intros r. rewrite H0, (brk_r_ok_grow_cases model req r Hpos Hs Hb). split.
    - intros [-> | [-> Hg]]; [reflexivity | rewrite Hblk in Hg; discriminate].
    - intros ->. left. reflexivity. }
  assert (Hq : brk_resolution_ok model (ms_gpr ms 0) (vm_brk (m_vmmaps model))) by (apply Hcases; reflexivity).
  pose proof (proj1 (node_brk segs ms model (getr regs 17) Hh Hlazy eq_refl Hno) (exist _ _ Hq)) as Hst.
  cbn [proj1_sig] in Hst. rewrite brk_zeros_keep, brk_unmaps_keep, brk_model_keep in Hst.
  unfold ms in Hst. rewrite adv_ret_epend in Hst. fold ms in Hst.
  apply star_cfg_one.
  destruct (bv_eqb req (vm_brk (m_vmmaps model))) eqn:Ereq.
  - (* [comment removed for export] *)
    apply bv_eqb_eq in Ereq. apply sstep_cfg_of_nonrefusal; [| exact Hst].
    intros y eff m' evs Hy _. cbn in Hy |- *. injection Hy as <-.
    rewrite (brk_refusal_b_eq segs ms _ model _ Hno), H0, Ereq. unfold brk_refusal_b.
    rewrite bv_eqb_refl. cbn [negb]. rewrite !Bool.andb_false_r. reflexivity.
  - (* [comment removed for export] *)
    apply sstep_cfg_of_forced; [| exact Hst].
    intros y eff m' evs Hy Hspec. cbn in Hy. injection Hy as <-. cbn [cfg_ms cfg_model] in Hspec |- *.
    apply (brk_ok_iff segs ms (getr regs 17) model eff m' evs Hno) in Hspec as (_ & _ & Hok & _).
    apply Hcases in Hok.
    assert (Hneq : req <> vm_brk (m_vmmaps model)) by (intros E; rewrite E, bv_eqb_refl in Ereq; discriminate Ereq).
    rewrite (brk_refusal_b_eq segs ms _ model _ Hno), H0, Hok. unfold brk_refusal_b.
    unfold w_is0. rewrite (bv_eqb_neq _ _ Hneq), bv_eqb_refl.
    replace (bv_eqb req (Z_to_bv 64 0)) with false
      by (symmetry; apply bv_eqb_neq; intros E; apply (f_equal bv_unsigned) in E;
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E; lia).
    unfold min_brk. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma star_brk_grant : forall regs (pc : word) mem rom model w (d : Z),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->
  brk_grow_adm d model = true ->
  star_cfg segs CFG (mkCfg (mkst regs pc mem rom) model) []
       (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                    (zfill b (Z_to_bv 64 d) mem) rom)
              (brk_grown_model d model)).
Proof.
  intros regs pc mem rom model w d HF HE Hh Hlazy H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  eapply (star_cfg_trans_nil segs); [eapply star_sys; eassumption|].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hgrow : brk_resolution_ok model (ms_gpr ms 0) req).
  { rewrite H0. refine (proj2 (brk_r_ok_grow_cases model req req _ _ _) _); fold h; fold b; rewrite ?Hureq; try lia.
    right. split; [reflexivity | exact Hadm]. }
  assert (Hneq : req <> b).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E. unfold b in E. lia. }
  pose proof (proj1 (node_brk segs ms model (getr regs 17) Hh Hlazy eq_refl Hno) (exist _ _ Hgrow)) as Hst.
  cbn [proj1_sig] in Hst.
  assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
  assert (Hreq0 : req <> Z_to_bv 64 0).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  rewrite H0 in Hst. fold h b in Hst. rewrite (brk_zeros_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) in Hst by lia.
  unfold brk_page_range in Hst.
  rewrite (page_round_up_Z_aligned (bv_unsigned b)) in Hst by (first [lia | exact Hbal]).
  rewrite (page_round_up_Z_aligned (bv_unsigned req)) in Hst
    by (rewrite Hureq; first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
  rewrite (proj2 (Z.ltb_lt _ _) Hlt) in Hst.
  replace (Z_to_bv 64 (bv_unsigned b)) with b in Hst by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
  rewrite Hureq in Hst. replace (bv_unsigned b + d - bv_unsigned b)%Z with d in Hst by lia.
  assert (Em : brk_model req req model = brk_grown_model d model).
  { unfold req, b, h. rewrite (brk_model_grow_eq model d) by assumption. reflexivity. }
  rewrite Em in Hst.
  assert (Hnr : forall zs us, refusal_b (sys_input segs ms (getr regs 17)) model (eff_ret (mkEffectU req [] zs us [] [])) = false).
  { intros zs us. cbn [eff_ret]. rewrite (brk_refusal_b_eq segs ms _ model _ Hno), H0. unfold brk_refusal_b. fold h. fold b.
    rewrite (bv_eqb_neq _ _ Hneq). rewrite !Bool.andb_false_r. reflexivity. }
  pose proof (star_cfg_succ_nr segs ms model (getr regs 17) _ _ (epend_svc _ _ _ _ _) Hst (Hnr _ _)) as Hsc.
  unfold ms in Hsc. rewrite adv_zeros1_epend in Hsc. exact Hsc.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma star_mmap_anon_grant : forall regs (pc : word) mem rom model w (len : Z) (a : word),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  grant_ok (getr regs 10) model a nZ = true ->
  star_cfg segs CFG (mkCfg (mkst regs pc mem rom) model) []
       (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom) (mmap_model a n model)).
Proof.
  intros regs pc mem rom model w len a HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 nZ n Hg.
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  set (ms := epend regs pc mem rom (getr regs 17)).
  destruct (a1_len_facts regs pc mem rom len H11 Hlen) as [Hu1 Hne1]. fold ms in Hu1, Hne1.
  assert (Hpr : page_round_up (ms_gpr ms 1) = n) by (unfold page_round_up; rewrite Hu1; reflexivity).
  assert (Hargs : mmap_args_ok ms).
  { unfold mmap_args_ok, ms. rewrite ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H12, H13, H14, H15. repeat split; try reflexivity. exact Hne1. }
  assert (H0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; rewrite ms_gpr_epend0; reflexivity).
  pose proof (mmap_succ_ok segs ms (getr regs 17) model a Hno Hargs ltac:(rewrite H0, Hu1; exact Hg)) as Hspec.
  rewrite Hpr in Hspec.
  eapply (star_cfg_trans_nil segs); [eapply star_sys; eassumption|]. fold ms.
  replace (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom)
    with (advance_past_svc (apply_effect ms (mkEffect a [] [(a, n)]))) by (unfold ms, epend; rewrite adv_mmap_grant; reflexivity).
  apply (star_cfg_succ_nr segs ms model (getr regs 17)); [apply epend_svc | |].
  - apply (sstep_syscall segs ms model (getr regs 17) _ (mmap_model a n model) (mmap_model a n model) []);
      [exact Hh | reflexivity | exact Hspec | rewrite mmap_model_halted; exact Hh
      | apply materialize_model_accesses_no_lazy; rewrite mmap_model_lazy; exact Hlazy].
  - cbn [eff_ret]. apply (grant_not_refusal segs ms _ model a nZ (getr regs 10) Hno); [| exact Hg].
    unfold nZ. apply pruZ_nonneg. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma star_mmap_noaccess_grant : forall regs (pc : word) mem rom model w (len : Z) (a : word),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  grant_ok_na_pin model a nZ = true ->
  star_cfg segs CFG (mkCfg (mkst regs pc mem rom) model) []
       (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (unfill a n mem) rom) (noaccess_model a n model)).
Proof.
  intros regs pc mem rom model w len a HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 nZ n Hg.
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  set (ms := epend regs pc mem rom (getr regs 17)).
  destruct (a1_len_facts regs pc mem rom len H11 Hlen) as [Hu1 Hne1]. fold ms in Hu1, Hne1.
  assert (Hargs : mmap_noaccess_args_ok ms).
  { unfold mmap_noaccess_args_ok, ms. rewrite ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H12, H13, H14, H15. repeat split; try reflexivity. exact Hne1. }
  pose proof (mmap_noaccess_check segs ms (getr regs 17) model (mkEffectU a [] [] [(a, n)] [] []) Hno Hargs) as Hchk.
  rewrite Hu1 in Hchk. cbv zeta in Hchk. fold nZ in Hchk. fold n in Hchk.
  assert (Hn0 : (0 <= nZ)%Z) by (unfold nZ; apply pruZ_nonneg; lia).
  rewrite (grant_na_pin_not_errno model a nZ Hn0 Hg), Hg in Hchk. cbn [andb] in Hchk.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl) in Hchk.
  pose proof (star_sys_eff_nr regs pc mem rom model w _ _ Hh Hlazy HF HE Hchk
                ltac:(cbn [eff_ret]; rewrite (mmap_refusal_b segs _ _ model _ Hno); exact (grant_na_pin_not_errno model a nZ Hn0 Hg))
                ltac:(rewrite noaccess_model_halted; exact Hh) ltac:(rewrite noaccess_model_lazy; exact Hlazy)) as Hs.
  rewrite adv_unmaps1_epend in Hs. exact Hs.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma star_mprotect_grant : forall regs (pc : word) mem rom model w (addr : word) (len : Z),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 226 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  getr regs 12 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  mprotect_budget_ok model addr n = true ->
  star_cfg segs CFG (mkCfg (mkst regs pc mem rom) model) []
       (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill addr n mem) rom) (mprotect_model addr n model)).
Proof.
  intros regs pc mem rom model w addr len HF HE Hh Hlazy H17 H10 Hal H11 Hlen Hnw H12 n Hna Hma Hbud.
  assert (Hno : bv_unsigned (getr regs 17) = 226%Z) by (rewrite H17; apply u64_lit; lia).
  set (ms := epend regs pc mem rom (getr regs 17)).
  pose proof (mprotect_check segs ms (getr regs 17) model (mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] []) addr len Hno
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal
                ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hnw
                ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12) Hna Hma) as Hchk.
  cbv zeta in Hchk. fold n in Hchk. rewrite Hbud in Hchk.
  change (errno_ret_in mprotect_errnos (Z_to_bv 64 0)) with false in Hchk.
  unfold w_is0 in Hchk. rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl) in Hchk. cbn [andb] in Hchk. cbv iota in Hchk.
  pose proof (star_sys_eff_nr regs pc mem rom model w _ _ Hh Hlazy HF HE Hchk
                ltac:(cbn [eff_ret]; rewrite (mprotect_refusal_b segs _ _ model _ Hno); reflexivity)
                ltac:(rewrite mprotect_model_halted; exact Hh) ltac:(rewrite mprotect_model_lazy; exact Hlazy)) as Hs.
  unfold ms in Hs. rewrite adv_zeros1_epend in Hs. exact Hs.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma star_mmap_fixed_noaccess : forall regs (pc : word) mem rom model w (addr : word) (len : Z),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 50 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  star_cfg segs CFG (mkCfg (mkst regs pc mem rom) model) []
       (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr n mem) rom)
              (fixed_noaccess_model addr n model)).
Proof.
  intros regs pc mem rom model w addr len HF HE Hh Hlazy H17 H10 Hal Hpos H11 Hlen Htop H12 H13 H14 H15 n Hrf Hmc.
  pose proof (u64_range addr) as Har. pose proof (alloc_top_room (m_vmmaps model)) as Hroom.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as Hprb.
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hlen' : (len < 2 ^ 64)%Z) by (unfold two_pow_64, stack_max_size in Hroom; lia).
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hargs : mmap_fixed_args_ok ms).
  { unfold mmap_fixed_args_ok, ms.
    rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
    intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
  assert (Haddr_ne : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|]. unfold stack_max_size, two_pow_64 in *. lia. }
  pose proof (mmap_fixed_check segs ms (getr regs 17) model (mkEffectU addr [] [] [(addr, n)] [] []) addr len Hno Hargs
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Htop Hrf Hmc) as Hchk.
  cbv beta iota zeta in Hchk. fold n in Hchk. rewrite Haddr_ne, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl) in Hchk.
  cbn [andb] in Hchk.
  pose proof (star_sys_eff_nr regs pc mem rom model w _ _ Hh Hlazy HF HE Hchk
                ltac:(cbn [eff_ret]; rewrite (mmap_refusal_b segs _ _ model _ Hno); exact Haddr_ne)
                ltac:(unfold fixed_noaccess_model; rewrite vm_forget_range_halted, with_vmmaps_halted; exact Hh)
                ltac:(unfold fixed_noaccess_model; apply vm_forget_range_lazy_nil; rewrite with_vmmaps_lazy'; exact Hlazy)) as Hs.
  unfold ms in Hs. rewrite adv_unmaps1_epend in Hs. exact Hs.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma star_munmap : forall regs (pc : word) mem rom model w (a : word) (len : Z),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 215 ->
  getr regs 10 = a -> (bv_unsigned a mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned a + page_round_up_Z len <= TASK_SIZE)%Z ->
  map_has (vm_maps (m_vmmaps model)) a (Z_to_bv 64 (page_round_up_Z len)) = true ->
  star_cfg segs CFG (mkCfg (mkst regs pc mem rom) model) []
       (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
                    (unfill a (Z_to_bv 64 (page_round_up_Z len)) mem) rom)
              (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model)).
Proof.
  intros regs pc mem rom model w a len HF HE Hh Hlazy H17 H10 Hal H11 Hlen Hts Hhas.
  assert (Hlen' : (len < 2 ^ 64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a). unfold TASK_SIZE in Hts. lia. }
  assert (Hno : bv_unsigned (getr regs 17) = 215%Z) by (rewrite H17; apply u64_lit; lia).
  set (ms := epend regs pc mem rom (getr regs 17)).
  destruct (a1_len_facts regs pc mem rom len H11 ltac:(lia)) as [Hu1 Hne1]. fold ms in Hu1, Hne1.
  assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)).
  { unfold page_round_up. rewrite Hu1. reflexivity. }
  assert (H0 : ms_gpr ms 0 = a) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hargs : munmap_args_ok ms model).
  { unfold munmap_args_ok. rewrite H0, Hu1, Hpr. repeat split; assumption. }
  pose proof (munmap_ok segs ms (getr regs 17) model Hno Hargs) as Hspec.
  unfold munmap_eff in Hspec. rewrite H0, Hpr in Hspec.
  eapply (star_cfg_trans_nil segs); [eapply star_sys; eassumption|]. apply star_cfg_one.
  replace (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (unfill a (Z_to_bv 64 (page_round_up_Z len)) mem) rom)
    with (advance_past_svc (apply_effect ms (mkEffectU (Z_to_bv 64 0) [] [] [(a, Z_to_bv 64 (page_round_up_Z len))] [] [])))
    by (unfold ms; rewrite adv_unmaps1_epend; reflexivity).
  apply sstep_cfg_of_unfiltered; [eapply unfiltered_sysno; [apply epend_svc | rewrite Hno; reflexivity]|].
  apply (sstep_syscall segs ms model (getr regs 17) _ (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model)
           (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model) []);
    [exact Hh | reflexivity | exact Hspec | rewrite munmap_model_halted; exact Hh
    | apply materialize_model_accesses_no_lazy; apply munmap_model_no_lazy; exact Hlazy].
Qed.

End EFace.


Local Open Scope Z_scope.

Lemma grant_exists_na_gen : forall (m : Model) (N n C : Z),
  0 < N -> N mod page_size = 0 -> 0 <= n <= N ->
  init_sp_ok (m_vmmaps m) ->
  Forall (fun p => bv_unsigned (snd p) <= N) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= C ->
  bottomup_floor + C * (2 * N) + N <= alloc_ceiling ->
  exists a, grant_ok_na_pin m a n = true.
Proof.
  intros m N n C HN HNal Hn Hisp Hsz Hcnt Hband.
  set (l := vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) in *.
  destruct (pick_candidate N n l (seq 0 (S (length l))) Hn Hsz (List.seq_NoDup _ _) ltac:(rewrite length_seq; lia))
    as (j & Hj & Hfree).
  apply in_seq in Hj.
  exists (Z_to_bv 64 (cand N j)).
  pose proof alloc_ceiling_val as Hcv. pose proof bottomup_floor_val as Hfv.
  pose proof (alloc_ceiling_le_alloc_top _ Hisp) as Htop.
  assert (Hc : bottomup_floor <= cand N j <= bottomup_floor + C * (2 * N)) by (unfold cand; nia).
  unfold grant_ok_na_pin. rewrite !u64_lit by lia.
  assert (E1 : cand N j mod page_size = 0).
  { unfold cand. rewrite Hfv. unfold page_size in *. rewrite Z.add_mod, Z.mul_assoc, Z.mul_mod, HNal by lia.
    rewrite Z.mul_0_r. reflexivity. }
  rewrite (proj2 (Z.eqb_eq _ _) E1), (proj2 (Z.ltb_lt 0 _)) by lia.
  rewrite (proj2 (Z.leb_le _ _)) by lia.
  fold l. rewrite (region_free_of_noconflict l (cand N j) n) by (first [lia | exact Hfree]).
  reflexivity.
Qed.

Lemma grant_exists_gen : forall hint (m : Model) (N n C : Z),
  0 < N -> N mod page_size = 0 -> 0 <= n <= N ->
  init_sp_ok (m_vmmaps m) ->
  Forall (fun p => bv_unsigned (snd p) <= N) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= C ->
  bottomup_floor + C * (2 * N) + N <= alloc_ceiling ->
  vm_backing_used m + n <= vm_limit (m_vmmaps m) ->
  exists a, grant_ok hint m a n = true.
Proof.
  intros hint m N n C HN HNal Hn Hisp Hsz Hcnt Hband Hlive.
  destruct (grant_exists_na_gen m N n C HN HNal Hn Hisp Hsz Hcnt Hband) as [a Ha].
  exists a. unfold grant_ok. unfold grant_ok_na_pin in Ha. rewrite Ha.
  rewrite (proj2 (Z.leb_le _ _) Hlive). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma grant_exists : forall hint (m : Model) (n : Z),
  0 <= n <= 2 ^ 30 ->
  init_sp_ok (m_vmmaps m) ->
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 30) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= 1000 ->
  vm_backing_used m + n <= vm_limit (m_vmmaps m) ->
  exists a, grant_ok hint m a n = true.
Proof.
  intros hint m n Hn Hisp Hsz Hcnt Hlive.
  apply (grant_exists_gen hint m (2 ^ 30) n 1000); try assumption; try lia.
  - reflexivity.
  - rewrite alloc_ceiling_val, bottomup_floor_val. cbv. discriminate.
Qed.

Lemma grant_exists_na : forall (m : Model) (n : Z),
  0 <= n <= 2 ^ 30 ->
  init_sp_ok (m_vmmaps m) ->
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 30) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= 1000 ->
  exists a, grant_ok_na_pin m a n = true.
Proof.
  intros m n Hn Hisp Hsz Hcnt.
  apply (grant_exists_na_gen m (2 ^ 30) n 1000); try assumption; try lia.
  - reflexivity.
  - rewrite alloc_ceiling_val, bottomup_floor_val. cbv. discriminate.
Qed.

(* [comment removed for export] *)
Lemma grant_ok_over_budget : forall hint (m : Model) (a : word) (n : Z),
  vm_limit (m_vmmaps m) < vm_backing_used m + n ->
  grant_ok hint m a n = false.
Proof.
  intros hint m a n H. unfold grant_ok.
  rewrite (proj2 (Z.leb_gt _ _) H). rewrite !andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma grant_budget_live : forall m n,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_live_bytes (m_vmmaps m) + n <= vm_limit (m_vmmaps m) ->
  vm_backing_used m + n <= vm_limit (m_vmmaps m).
Proof. intros. apply grant_budget_intro; assumption. Qed.

(* [comment removed for export] *)
Lemma grant_ok_na_pin_unpack : forall m a n,
  grant_ok_na_pin m a n = true ->
  bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\
  bv_unsigned a + n <= alloc_top (m_vmmaps m) /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true.
Proof.
  intros m a n H. unfold grant_ok_na_pin in H.
  apply andb_true_iff in H as [H Hrf]. apply andb_true_iff in H as [H Htop]. apply andb_true_iff in H as [Hal Hpos].
  apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop. auto.
Qed.
End NodesMm.
