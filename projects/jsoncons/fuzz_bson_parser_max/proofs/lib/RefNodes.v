(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes StoreOk AgentLib AgentNodes SpecConsts.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition t_alt3 (A B C : TSet) : TSet := t_alt2 A (t_alt2 B C).

Lemma t_alt2_idem : forall A, t_eq (t_alt2 A A) A.
Proof. intros A tr. unfold t_alt2. tauto. Qed.

Lemma t_alt3_idem : forall A, t_eq (t_alt3 A A A) A.
Proof. intros A tr. unfold t_alt3, t_alt2. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_fds_halted' : forall fds m, m_halted (with_fds fds m) = m_halted m.
Proof. reflexivity. Qed.

Lemma with_fds_lazy : forall fds m, m_vm_lazy (with_fds fds m) = m_vm_lazy m.
Proof. reflexivity. Qed.

Lemma with_tid_halted : forall t m, m_halted (with_tid t m) = m_halted m.
Proof. reflexivity. Qed.

Lemma with_tid_lazy : forall t m, m_vm_lazy (with_tid t m) = m_vm_lazy m.
Proof. reflexivity. Qed.

Lemma with_vmmaps_lazy' : forall h m, m_vm_lazy (with_vmmaps h m) = m_vm_lazy m.
Proof. reflexivity. Qed.

Lemma with_vmmaps_eta : forall m,
  with_vmmaps (m_vmmaps m) m = m.
Proof. intros m. destruct m as [? [? ? ?] ? ? ? ?]; reflexivity. Qed.

Lemma vmmaps_eta : forall h,
  mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) = h.
Proof. intros h. destruct h; reflexivity. Qed.

Lemma Z_to_bv_u_eq' : forall (a : word) (z : Z), z = bv_unsigned a -> Z_to_bv 64 z = a.
Proof.
  intros a z ->. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Lemma vm_forget_range_id : forall lo hi m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_forget_range lo hi m = m.
Proof.
  intros lo hi m Hl Hm. unfold vm_forget_range, with_vm_backing.
  rewrite Hl, Hm. cbn [maps_subtract List.filter].
  destruct m as [? [? l mt] ? ? ? ?]. cbn in Hl, Hm. subst. reflexivity.
Qed.

Lemma vm_forget_range_lazy_nil : forall lo hi m,
  m_vm_lazy m = [] -> m_vm_lazy (vm_forget_range lo hi m) = [].
Proof.
  intros lo hi m Hl. unfold vm_forget_range, with_vm_backing. cbn [m_vm_lazy]. rewrite Hl. reflexivity.
Qed.

Lemma vm_forget_range_halted : forall lo hi m,
  m_halted (vm_forget_range lo hi m) = m_halted m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma access_okb_intro_le : forall (b : word) (n : Z),
  (0 <= n)%Z -> (bv_unsigned b + n <= TASK_SIZE)%Z -> access_okb b n = true.
Proof.
  intros b n Hn H. unfold access_okb. pose proof (bv_unsigned_in_range 64 b) as [Hb _].
  apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.

(* [comment removed for export] *)
Lemma mmap_check : forall ms x8 model eff,
  bv_unsigned x8 = 222%Z ->
  check_syscall (sys_input segs ms x8) eff model
  = check_mmap (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 4) (ms_gpr ms 5) eff model.
Proof. intros ms x8 model eff Hno. unfold check_syscall. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.

Lemma munmap_check : forall ms x8 model eff,
  bv_unsigned x8 = 215%Z ->
  check_syscall (sys_input segs ms x8) eff model = check_munmap (ms_gpr ms 0) (ms_gpr ms 1) eff model.
Proof. intros ms x8 model eff Hno. unfold check_syscall. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.

Lemma check_syscall_29 : forall ms x8 eff m,
  bv_unsigned x8 = 29%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_ioctl (fd32 (ms_gpr ms 0)) (cmd32 (ms_gpr ms 1)) eff m.
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.

Lemma check_syscall_226 : forall ms x8 eff m,
  bv_unsigned x8 = 226%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_mprotect (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) eff m.
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.

Lemma check_syscall_96 : forall ms x8 eff m,
  bv_unsigned x8 = 96%Z ->
  check_syscall (sys_input segs ms x8) eff m = check_set_tid_address eff m.
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive three : Type := T1 | T2 | T3.

Lemma rz_alt3 : forall c (nx : three -> config) (A B C : TSet),
  node_ok segs scfg c three (fun _ => []) nx ->
  srealizes segs scfg (nx T1) A -> srealizes segs scfg (nx T2) B -> srealizes segs scfg (nx T3) C ->
  srealizes segs scfg c (t_alt3 A B C).
Proof.
  intros c nx A B C Hnode HA HB HC.
  apply (srz_conseq segs scfg c (t_alt (fun i => match i with T1 => A | T2 => B | T3 => C end))).
  - apply (rz_cases segs scfg c three nx _ T1 Hnode). intros [| |]; assumption.
  - intros tr. unfold t_alt3, t_alt2, t_alt. split.
    + intros [[| |] H]; tauto.
    + intros [H | [H | H]]; [exists T1 | exists T2 | exists T3]; exact H.
Qed.

(* [comment removed for export] *)
Lemma node_of_iff : forall c (I : Type) (evs : I -> list event) (nx : I -> config),
  (forall i, sstep_cfg segs scfg c (evs i) (SNext (nx i))) ->
  (forall e st, sstep_cfg segs scfg c e st -> exists i, e = evs i /\ st = SNext (nx i)) ->
  node_ok segs scfg c I evs nx.
Proof. intros; split; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma adv_ret_epend : forall regs pc mem rom x8 r,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [] [] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof. intros. unfold epend. apply adv_eff_ret. Qed.

Lemma adv_zeros1_epend : forall regs pc mem rom x8 r a n,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [(a, n)] [] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (zfill a n mem) rom.
Proof.
  intros. unfold epend.
  assert (Hm : apply_zeros (apply_unmaps mem []) [(a, n)] = zfill a n mem).
  { cbn [apply_unmaps]. unfold zfill. exact (apply_zeros_one mem a n). }
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_writes apply_copies].
  unfold mkst, regupd. rewrite b_npc4, Hm. reflexivity.
Qed.

Lemma adv_unmaps1_epend : forall regs pc mem rom x8 r a n,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [] [(a, n)] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (unfill a n mem) rom.
Proof.
  intros. unfold epend.
  assert (Hm : apply_writes (apply_zeros (apply_unmaps mem [(a, n)]) []) [] = unfill a n mem).
  { cbn [apply_writes apply_zeros].
    apply functional_extensionality. intro x.
    unfold apply_unmaps, zeros_cover, unfill. cbn [existsb fst snd].
    rewrite orb_false_r. reflexivity. }
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies].
  unfold mkst, regupd. rewrite b_npc4, Hm. reflexivity.
Qed.

Lemma adv_write1_epend : forall regs pc mem rom x8 r buf data,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffect r [(buf, data)] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (wbytes mem buf data) rom.
Proof. intros. unfold epend. rewrite adv_apply_write, write_to_mem_wbytes. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_close : forall regs (pc : word) mem model w fd e K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 57 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some e ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs))
                       (with_fds (fd_remove (m_fds model) fd) model)) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd e K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hc.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply rz_ret_only_silent; [exact Hh | reflexivity | | | | rewrite adv_set_epend; exact Hc].
  - intros eff. rewrite (check_syscall_57 segs) by (rewrite H17; apply u64_lit; lia).
    unfold check_close. rewrite ms_gpr_epend0, Hfd, (fd32_id fd Hfd32), Hlk. reflexivity.
  - rewrite with_fds_halted'. exact Hh.
  - rewrite with_fds_lazy. exact Hlazy.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_ioctl_winsz : forall regs (pc : word) mem model w fd e K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 29 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some e ->
  (* [comment removed for export] *)
  match e with FdDevNull _ _ => false | FdUrandom => false | _ => true end = true ->
  getr regs 11 = Z_to_bv 64 0x5413 ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi pc 4) mem (seg_rom segs))
                       model) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd e K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hnd H11 Hc.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply rz_ret_only_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
  intros eff. rewrite check_syscall_29 by (rewrite H17; apply u64_lit; lia).
  unfold check_ioctl. rewrite ms_gpr_epend0, ms_gpr_epend1, Hfd, (fd32_id fd Hfd32), Hlk, H11.
  destruct e; first [reflexivity | discriminate Hnd].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_read_dir : forall regs (pc : word) mem model w fd K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  (bv_unsigned (getr regs 11) + bv_unsigned (getr regs 12) <= TASK_SIZE)%Z ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hts Hc.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply rz_ret_only_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
  intros eff. rewrite (check_syscall_63 segs _ _ eff model) by (rewrite H17; apply u64_lit; lia).
  unfold check_read. rewrite ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, Hfd, (fd32_id fd Hfd32), Hlk.
  rewrite (access_okb_intro_le _ _ (proj1 (bv_unsigned_in_range 64 (getr regs 12))) Hts).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rz_read_dir_cnt : forall regs (pc : word) mem model w fd (cnt : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  getr regs 12 = Z_to_bv 64 cnt -> (0 <= cnt)%Z ->
  (bv_unsigned (getr regs 11) + cnt <= TASK_SIZE)%Z ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd cnt K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk H12 Hc0 Hts Hc.
  eapply (rz_read_dir regs pc mem model w fd K); try eassumption.
  rewrite H12, u64_lit; [exact Hts|]. unfold TASK_SIZE in Hts. pose proof (u64_range (getr regs 11)). lia.
Qed.

(* [comment removed for export] *)
Lemma read_file_check : forall ms x8 model fd p off data wv,
  bv_unsigned x8 = 63%Z ->
  ms_gpr ms 0 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdFile p off) ->
  fs_lookup (m_fs model) p = Some data ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some wv ->
  (0 < bv_unsigned (ms_gpr ms 2))%Z -> (bv_unsigned (ms_gpr ms 2) <= 65536)%Z ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  let bs := file_read data off (ms_gpr ms 2) in
  let m' := with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model in
  (forall eff mx evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk mx evs <->
     (eff = mkEffect (len_word bs) (delivered_writes (ms_gpr ms 1) bs) [] /\ mx = m' /\ evs = []))
  /\ (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled).
Proof.
  intros ms x8 model fd p off data wv Hno H0 Hfd32 Hlk Hfs Hw Hpos Hcnt65 Haok bs m'.
  assert (Hcnt : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z) by (pose proof rw_bytes_max_ge17; lia).
  assert (HL : (bv_unsigned (len_word (file_read data off (ms_gpr ms 2)))
                <= bv_unsigned (ms_gpr ms 2))%Z).
  { unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
    pose proof (u64_range (ms_gpr ms 2)) as Hc.
    rewrite length_file_read, Nat2Z.inj_min. unfold word_to_nat.
    rewrite Z.mod_small; lia. }
  assert (Hred : forall eff, check_syscall (sys_input segs ms x8) eff model =
    match bs, eff with
    | [], _ => check_ret_only eff (Z_to_bv 64 0) m' []
    | _ :: _, mkEffectU ret [(a, bs')] [] [] [] [] =>
        if bv_eqb a (ms_gpr ms 1) && listN_eqb bs' bs && bv_eqb ret (len_word bs)
        then CheckOk m' [] else CheckReject
    | _ :: _, _ => CheckReject
    end).
  { intros eff. rewrite (check_syscall_63 segs ms x8 eff model Hno). unfold check_read.
    rewrite H0, (fd32_id fd Hfd32), Hlk. cbv beta iota.
    rewrite Haok. cbn [negb]. cbv beta iota.
    rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned.
    rewrite Hfs. cbv beta iota zeta. rewrite in_wmem_si.
    rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw). cbv beta iota.
    fold bs. fold m'.
    destruct bs as [|b bsr]; reflexivity. }
  split.
  - intros eff mx evs. rewrite Hred. destruct bs as [|b bsr].
    + rewrite check_ret_only_ok_iff. cbn [delivered_writes]. unfold len_word. cbn [length Z.of_nat]. tauto.
    + destruct eff as [ret ws zs us cs ci]. split.
      * intro H.
        destruct ws as [|[a bs'] [|? ?]]; try discriminate.
        destruct zs; [|discriminate]. destruct us; [|discriminate].
        destruct cs; [|discriminate]. destruct ci; [|discriminate].
        destruct (bv_eqb a (ms_gpr ms 1) && listN_eqb bs' (b :: bsr) && bv_eqb ret (len_word (b :: bsr)))%bool eqn:E;
          [|discriminate].
        apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
        apply bv_eqb_eq in E1. apply listN_eqb_eq in E2. apply bv_eqb_eq in E3. subst.
        injection H; intros; subst. repeat split; reflexivity.
      * intros (E1 & -> & ->). cbn [delivered_writes] in E1. injection E1; intros; subst.
        rewrite !bv_eqb_refl, (proj2 (listN_eqb_eq _ _) eq_refl). reflexivity.
  - intros eff. rewrite Hred. destruct bs as [|b bsr].
    + apply check_ret_only_no_unmodeled.
    + destruct eff as [ret ws zs us cs ci].
      destruct ws as [|[a bs'] [|? ?]]; try discriminate.
      destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (_ && _)%bool; discriminate.
Qed.

Lemma rz_read_file : forall regs (pc : word) mem model w fd p off data (cnt : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdFile p off) ->
  fs_lookup (m_fs model) p = Some data ->
  getr regs 12 = Z_to_bv 64 cnt ->
  (1 <= cnt)%Z -> (cnt <= 65536)%Z -> (cnt < 2 ^ 64)%Z ->
  store_ok segs mem (getr regs 11) (Z.to_nat cnt) = true ->
  (bv_unsigned (getr regs 11) + cnt <= TASK_SIZE)%Z ->
  let bs := file_read data off (getr regs 12) in
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4)
                              (wbytes mem (getr regs 11) bs) (seg_rom segs))
                       (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model)) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd p off data cnt K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Hok Hts bs Hc.
  assert (Hno : bv_unsigned (getr regs 17) = 63%Z) by (rewrite H17; apply u64_lit; lia).
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  destruct (read_bytes_map_of_store_ok segs mem (getr regs 11) (Z.to_nat cnt) Hok ltac:(lia)) as [wv Hw].
  rewrite Z2Nat.id in Hw by lia.
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hu2 : bv_unsigned (ms_gpr ms 2) = cnt).
  { unfold ms. rewrite ms_gpr_epend2, H12. apply u64_lit. lia. }
  destruct (read_file_check ms (getr regs 17) model fd p off data wv Hno
              ltac:(unfold ms; rewrite ms_gpr_epend0; exact Hfd) Hfd32 Hlk Hfs
              ltac:(unfold ms; rewrite ms_writable_byte_epend, ms_gpr_epend1, ms_gpr_epend2, H12; exact Hw)
              ltac:(rewrite Hu2; lia) ltac:(rewrite Hu2; exact Hmax)
              ltac:(rewrite Hu2; unfold ms; rewrite ms_gpr_epend1; apply access_okb_intro_le; lia)) as [Hchk Hnu].
  unfold ms in Hchk, Hnu. rewrite ms_gpr_epend1, ms_gpr_epend2 in Hchk.
  subst bs. revert Hc Hchk.
  generalize (file_read data off (getr regs 12)) as bs. intros bs Hc Hchk.
  eapply (rz_det segs scfg _ model _ (mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) [])
            (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model));
    [exact Hh | reflexivity | exact Hchk | exact Hnu
    | rewrite with_fds_halted'; exact Hh | rewrite with_fds_lazy; exact Hlazy | ].
  destruct bs as [|b bsr]; cbn [delivered_writes].
  - unfold ms. rewrite adv_ret_epend. cbn [wbytes] in Hc. exact Hc.
  - unfold ms. rewrite adv_write1_epend. exact Hc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma check_copyins_after_open_result : forall reads eff m mk,
  Prelude.check_copyins_after reads eff (check_open_result (clear_copyins eff) m mk)
  = check_open_result_copyins reads eff m mk.
Proof.
  intros reads eff m mk. unfold Prelude.check_copyins_after, check_open_result_copyins.
  destruct (check_open_result (clear_copyins eff) m mk) eqn:E; [reflexivity|reflexivity|].
  exfalso. exact (check_open_result_never_unmodeled _ _ _ E).
Qed.

Section Openat.
  Variables (regs : bvmap 5 word) (pc : word) (mem : word -> option byte) (model : Model).
  Variable w : bv 32.
  Hypothesis HF : fetch_word segs pc = Some w.
  Hypothesis HE : is_ecall w = true.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis H17 : getr regs 17 = Z_to_bv 64 56.
  Hypothesis H10 : getr regs 10 = AT_FDCWD.
  (* [comment removed for export] *)
  Hypothesis Hfl : Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z.
  (* [comment removed for export] *)
  Hypothesis Hfs_on : sc_fs scfg = true.

  Let ms := epend regs pc mem (seg_rom segs) (getr regs 17).
  Let post (r : word) := mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs).
  Let fds := m_fds model.

  Lemma Hno56 : bv_unsigned (getr regs 17) = 56%Z.
  Proof. rewrite H17. apply u64_lit. lia. Qed.

  Lemma fam_on_openat_ms : fam_on segs scfg ms.
  Proof. apply (fam_on_openat segs scfg ms (getr regs 17)); [reflexivity | exact Hno56 | exact Hfs_on]. Qed.

  (* [comment removed for export] *)
  Lemma openat_check_head : forall eff,
    check_syscall (sys_input segs ms (getr regs 17)) eff model
    = Prelude.check_copyins_after (open_copyins ms) eff
      match read_cstr (mrb segs mem) (getr regs 11) with
      | CstrTooLong => check_ret_only (clear_copyins eff) (errno_ret ENAMETOOLONG) model []
      | CstrFault => check_ret_only (clear_copyins eff) (errno_ret EFAULT) model []
      | CstrOk p =>
          if path_eqb p [] then check_ret_only (clear_copyins eff) (errno_ret ENOENT) model []
          else if path_has_slash p then Open.check_openat_sep p (getr regs 12) (clear_copyins eff) model  (* [comment removed for export] *)
          else if path_is_dirref p then
                 check_open_result (clear_copyins eff) model (fun fd => with_fds (fd_insert (m_fds model) fd FdDir) model)
               else match fs_lookup (m_fs model) p with
                    | None => check_ret_only (clear_copyins eff) (errno_ret ENOENT) model []
                    | Some _ => check_open_result (clear_copyins eff) model
                                  (fun fd => with_fds (fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model)
                    end
      end.
  Proof.
    intros eff. cbv delta [ms].
    rewrite (check_syscall_56 segs _ _ eff model Hno56). unfold check_openat.
    rewrite ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2.
    rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota zeta.
    unfold Open.check_openat_body. rewrite in_mem_si, ms_read_byte_epend.
    unfold open_copyins. rewrite ms_read_byte_epend, ms_gpr_epend1.
    destruct (read_cstr (mrb segs mem) (getr regs 11)) as [p| |]; [|reflexivity|reflexivity].
    destruct (path_eqb p []); [reflexivity|].
    rewrite H10. norm_fd32. rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
    unfold Open.check_openat_resolved.
    destruct (path_has_slash p); [reflexivity|].
    rewrite Hfl. cbn [Z.eqb]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_toolong : forall bs K,
    rdn segs mem (getr regs 11) 4096 = Some bs -> ~ In (Z_to_bv 8 0) bs ->
    srealizes segs scfg (mkCfg (post (errno_ret ENAMETOOLONG)) model) K ->
    srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros bs K Hrd Hnz Hc. cbv delta [post] in *.
    pose proof (read_cstr_toolong_of_rdn segs mem (getr regs 11) bs (rdn_length _ _ _ _ _ Hrd) Hnz Hrd) as Hp.
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply rz_ret_only_copyins_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
    intros eff. fold ms. rewrite openat_check_head, Hp. apply check_copyins_after_ret_only.
  Qed.

  (* [comment removed for export] *)
  Definition path_at (p : list byte) : Prop :=
    (length p <= 4095)%nat /\ ~ In (Z_to_bv 8 0) p
    /\ rdn segs mem (getr regs 11) (length p + 1) = Some (p ++ [Z_to_bv 8 0]).

  Lemma path_at_cstr : forall p, path_at p -> read_cstr (mrb segs mem) (getr regs 11) = CstrOk p.
  Proof. intros p (H1 & H2 & H3). apply read_cstr_of_rdn; assumption. Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_empty : forall K,
    path_at [] ->
    srealizes segs scfg (mkCfg (post (errno_ret ENOENT)) model) K ->
    srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros K Hp Hc. cbv delta [post] in *.
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply rz_ret_only_copyins_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
    intros eff. fold ms. rewrite openat_check_head, (path_at_cstr [] Hp). apply check_copyins_after_ret_only.
  Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_absent : forall p K,
    path_at p -> p <> [] -> openat_plain_name p = true -> fs_lookup (m_fs model) p = None ->
    srealizes segs scfg (mkCfg (post (errno_ret ENOENT)) model) K ->
    srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros p K Hp Hne Hpl Hfs Hc. cbv delta [post] in *.
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply rz_ret_only_copyins_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
    intros eff. fold ms. rewrite openat_check_head, (path_at_cstr p Hp).
    rewrite (path_eqb_neq _ _ Hne), (openat_plain_name_noslash _ Hpl), (openat_plain_name_nodirref _ Hpl), Hfs.
    apply check_copyins_after_ret_only.
  Qed.

  Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.

  (* [comment removed for export] *)
  Lemma rz_openat_dirref : forall p KA KB,
    path_at p -> path_is_dirref p = true ->
    (forall e, In e openat_errnos -> srealizes segs scfg (mkCfg (post (errno_ret e)) model) KA) ->
    srealizes segs scfg (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)) KB ->
    srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof.
    intros p KA KB Hp Hdr HA HB. cbv delta [post] in *.
    assert (Hne : p <> []) by (intros ->; discriminate Hdr).
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply rz_open; [exact Hh | exact Hlazy | reflexivity | | | | exact Hfree | exact fam_on_openat_ms | |].
    - intros eff. fold ms. rewrite openat_check_head, (path_at_cstr _ Hp).
      rewrite (path_eqb_neq _ _ Hne), (path_is_dirref_no_slash _ Hdr), Hdr.
      apply check_copyins_after_open_result.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_halted'. exact Hh.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_lazy. exact Hlazy.
    - intros e He. rewrite adv_set_epend. apply HA. exact He.
    - rewrite adv_set_epend. exact HB.
  Qed.

  Lemma rz_openat_dot : forall KA KB,
    path_at dot_path ->
    (forall e, In e openat_errnos -> srealizes segs scfg (mkCfg (post (errno_ret e)) model) KA) ->
    srealizes segs scfg (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)) KB ->
    srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof. intros KA KB Hp. apply (rz_openat_dirref dot_path KA KB Hp). reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_file : forall p d KA KB,
    path_at p -> p <> [] -> openat_plain_name p = true -> fs_lookup (m_fs model) p = Some d ->
    (forall e, In e openat_errnos -> srealizes segs scfg (mkCfg (post (errno_ret e)) model) KA) ->
    srealizes segs scfg (mkCfg (post (alloc_fd fds))
                         (with_fds (fd_insert fds (alloc_fd fds) (FdFile p (Z_to_bv 64 0))) model)) KB ->
    srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof.
    intros p d KA KB Hp Hne Hpl Hfs HA HB. cbv delta [post] in *.
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply rz_open; [exact Hh | exact Hlazy | reflexivity | | | | exact Hfree | exact fam_on_openat_ms | |].
    - intros eff. fold ms. rewrite openat_check_head, (path_at_cstr p Hp).
      rewrite (path_eqb_neq _ _ Hne), (openat_plain_name_noslash _ Hpl), (openat_plain_name_nodirref _ Hpl), Hfs.
      apply check_copyins_after_open_result.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_halted'. exact Hh.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_lazy. exact Hlazy.
    - intros e He. rewrite adv_set_epend. apply HA. exact He.
    - rewrite adv_set_epend. exact HB.
  Qed.
End Openat.

(* [comment removed for export] *)
Lemma alloc_fd_init : forall e0 e1 e2,
  alloc_fd [(Z_to_bv 64 0, e0); (Z_to_bv 64 1, e1); (Z_to_bv 64 2, e2)] = Z_to_bv 64 3.
Proof. intros. reflexivity. Qed.

Lemma fd_lookup_init_3 : forall e0 e1 e2,
  fd_lookup [(Z_to_bv 64 0, e0); (Z_to_bv 64 1, e1); (Z_to_bv 64 2, e2)] (Z_to_bv 64 3) = None.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_mmap_anon : forall regs (pc : word) mem model w (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  sc_alloc scfg = false ->
  let n := page_round_up_Z len in
  (exists a, grant_ok (getr regs 10) model a n = true) ->
  (forall a, grant_ok (getr regs 10) model a n = true ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4)
                                (zfill a (Z_to_bv 64 n) mem) (seg_rom segs))
                         (mmap_model a (Z_to_bv 64 n) model)) KB) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) KB.
Proof.
  intros regs pc mem model w len KB HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 Halloc n Hex HB.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. lia. }
  assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 n).
  { unfold page_round_up. rewrite Hu1. reflexivity. }
  assert (Hargs : mmap_args_ok ms).
  { unfold mmap_args_ok, ms.
    rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
    intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
  assert (H0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; rewrite ms_gpr_epend0; reflexivity).
  destruct Hex as (a0 & Ha0).
  eapply (srz_mmap segs scfg ms model (getr regs 17) KB Hh Hlazy eq_refl
            ltac:(rewrite H17; apply u64_lit; lia) Hargs Halloc).
  - intros a Ha. rewrite Hpr. rewrite H0, Hu1 in Ha. unfold ms, epend. rewrite adv_mmap_grant. apply HB. exact Ha.
  - rewrite H0, Hu1. exists a0. exact Ha0.
Qed.

(* [comment removed for export] *)
Lemma rz_mmap_anon_nogrant : forall regs (pc : word) mem model w (len : Z) KA,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  (forall a, grant_ok (getr regs 10) model a (page_round_up_Z len) = false) ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) mem (seg_rom segs)) model) KA ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) KA.
Proof.
  intros regs pc mem model w len KA HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 Hng HA.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. lia. }
  assert (Hargs : mmap_args_ok ms).
  { unfold mmap_args_ok, ms.
    rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
    intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
  assert (H0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; rewrite ms_gpr_epend0; reflexivity).
  eapply (srz_mmap_nogrant segs scfg ms model (getr regs 17) KA Hh Hlazy eq_refl
            ltac:(rewrite H17; apply u64_lit; lia) Hargs).
  - rewrite H0, Hu1. exact Hng.
  - unfold ms. rewrite adv_set_epend. exact HA.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma srz_munmap : forall regs (pc : word) mem model w (a : word) (len : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 215 ->
  getr regs 10 = a -> (bv_unsigned a mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned a + page_round_up_Z len <= TASK_SIZE)%Z ->      (* [comment removed for export] *)
  map_has (vm_maps (m_vmmaps model)) a (Z_to_bv 64 (page_round_up_Z len)) = true ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
                             (unfill a (Z_to_bv 64 (page_round_up_Z len)) mem) (seg_rom segs))
                      (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model)) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w a len K HF HE Hh Hlazy H17 H10 Hal H11 Hlen Hnw Hhas Hc.
  assert (Hlen' : (len < two_pow_64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a). unfold TASK_SIZE in Hnw. unfold two_pow_64. lia. }
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. unfold two_pow_64 in Hlen'. lia. }
  assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)).
  { unfold page_round_up. rewrite Hu1. reflexivity. }
  assert (H0 : ms_gpr ms 0 = a) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hargs : munmap_args_ok ms model).
  { unfold munmap_args_ok. rewrite H0, Hu1, Hpr. repeat split; try assumption.
    intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
  eapply (SpinAlg.srz_munmap segs scfg ms model (getr regs 17));
    [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Hargs |].
  unfold munmap_eff. rewrite H0, Hpr. unfold ms. rewrite adv_unmaps1_epend. exact Hc.
Qed.

Lemma munmap_model_simple : forall (a n : word) m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  munmap_model a n m
  = with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (map_remove (vm_maps (m_vmmaps m)) a)
                   (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Proof.
  intros a n m Hl Hm. unfold munmap_model, with_mmap_destroyed.
  apply vm_forget_range_id; [rewrite with_vmmaps_lazy'; exact Hl | exact Hm].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition brk_eff (ms : machine_state) (model : Model) (r : word) : SyscallEffect :=
  mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                 (brk_unmaps r (vm_brk (m_vmmaps model))) [] [].

(* [comment removed for export] *)
Definition brk_adm (model : Model) (req r : word) : Prop :=
  brk_resolution_ok model req r
  /\ (sc_alloc scfg = false -> brk_refusal_b model req r = true ->
      forall r', brk_resolution_ok model req r' -> brk_refusal_b model req r' = true).

(* [comment removed for export] *)
Lemma brk_r_ok_cases : forall m req r,
  brk_resolution_ok m req r -> r = vm_brk (m_vmmaps m) \/ r = req.
Proof.
  intros m req r H. unfold brk_resolution_ok, Mmap.brk_r_ok in H. cbv zeta in H.
  destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (min_brk (m_vmmaps m)))%Z)%bool.
  - left. apply bv_eqb_eq. exact H.
  - destruct (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps m)))%Z.
    + apply orb_true_iff in H as [H|H]; apply bv_eqb_eq in H; auto.
    + apply andb_true_iff in H as [H _]. apply orb_true_iff in H as [H|H]; apply bv_eqb_eq in H; auto.
Qed.

Lemma refusal_b_brk_ms : forall ms x8 model r,
  bv_unsigned x8 = 214%Z ->
  refusal_b (sys_input segs ms x8) model r = brk_refusal_b model (ms_gpr ms 0) r.
Proof.
  intros ms x8 model r Hno. rewrite (refusal_b_brk (sys_input segs ms x8) model r)
    by (rewrite in_sysno_sys_input; exact Hno).
  rewrite in_arg0_sys_input214. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_brk : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  node_ok segs scfg (mkCfg ms model)
    {r : word | brk_adm model (ms_gpr ms 0) r}
    (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms
                       (mkEffectU (proj1_sig i) []
                          (brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
                          (brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])))
                    (brk_model (ms_gpr ms 0) (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno.
  set (req := ms_gpr ms 0).
  assert (Hshape : forall r, brk_resolution_ok model req r ->
            m_halted (brk_model req r model) = None /\ m_vm_lazy (brk_model req r model) = []).
  { intros r Hr.
    destruct (brk_step_shape segs ms x8 model _ _ _ Hh Hlazy Hno (brk_ok_intro segs ms x8 model r Hno Hr))
      as (_ & Hh' & _ & _ & Hlazy'). rewrite Hlazy in Hlazy'. split; assumption. }
  apply (node_svc segs scfg ms model x8 {r : word | brk_adm model req r}
           (fun i => brk_eff ms model (proj1_sig i))
           (fun i => brk_model req (proj1_sig i) model)
           (fun _ => []) Hh Hsvc).
  - intros [r [Hr Hf]]. cbn [proj1_sig]. apply (brk_ok_intro segs ms x8 model r Hno Hr).
  - intros [r [Hr Hf]]. cbn [proj1_sig].
    destruct (sc_alloc scfg) eqn:Ealloc.
    + apply not_spurious_on. rewrite (injected_family_off_alloc scfg _ 214%Z);
        [rewrite Ealloc; reflexivity | rewrite in_sysno_sys_input; exact Hno | auto].
    + destruct (brk_refusal_b model req r) eqn:Eref.
      * apply not_spurious_forced. intros eff' m' evs' Hspec.
        apply (brk_ok_iff segs ms x8 model eff' m' evs' Hno) in Hspec.
        destruct Hspec as (_ & _ & Hok' & _).
        rewrite (refusal_b_brk_ms ms x8 model _ Hno). apply (Hf eq_refl eq_refl). exact Hok'.
      * apply not_spurious_nonrefusal. unfold brk_eff. cbn [eff_ret].
        rewrite (refusal_b_brk_ms ms x8 model _ Hno). exact Eref.
  - intros eff m' ev Hspec.
    pose proof (proj1 (brk_ok_iff segs ms x8 model eff m' ev Hno) Hspec) as (Heff & -> & Hok & ->).
    fold req in Heff, Hok.
    assert (Hmem : brk_adm model req (eff_ret eff) ->
              exists i : {r : word | brk_adm model req r},
                eff = brk_eff ms model (proj1_sig i) /\ brk_model req (eff_ret eff) model = brk_model req (proj1_sig i) model /\ ([] : list event) = []).
    { intros Hadm. exists (exist _ (eff_ret eff) Hadm). cbn [proj1_sig]. unfold brk_eff.
      split; [exact Heff | split; reflexivity]. }
    destruct (sc_alloc scfg) eqn:Ealloc.
    + left. apply Hmem. split; [exact Hok | intros E; rewrite Ealloc in E; discriminate E].
    + destruct (brk_refusal_b model req (eff_ret eff)) eqn:Eref.
      * (* [comment removed for export] *)
        assert (Hrq : negb (w_is0 req) = true /\ (bv_unsigned req <? bv_unsigned (min_brk (m_vmmaps model)))%Z = false
                      /\ bv_eqb req (vm_brk (m_vmmaps model)) = false /\ eff_ret eff = vm_brk (m_vmmaps model)).
        { unfold brk_refusal_b in Eref. cbv zeta in Eref.
          apply andb_true_iff in Eref as [Eref E4]. apply andb_true_iff in Eref as [Eref E3].
          apply andb_true_iff in Eref as [E1 E2].
          apply negb_true_iff in E2. apply negb_true_iff in E3. apply bv_eqb_eq in E4. auto. }
        destruct Hrq as (E1 & E2 & E3 & E4).
        destruct (Mmap.brk_r_ok model req req) eqn:Egrant.
        -- right. split; [| apply (proj1 (Hshape _ Hok))].
           apply (spurious_intro scfg (sys_input segs ms x8) model eff (brk_eff ms model req)
                    (brk_model req req model) []).
           ++ rewrite (injected_family_off_alloc scfg _ 214%Z);
                [rewrite Ealloc; reflexivity | rewrite in_sysno_sys_input; exact Hno | auto].
           ++ rewrite (refusal_b_brk_ms ms x8 model _ Hno). exact Eref.
           ++ apply (brk_ok_intro segs ms x8 model req Hno). exact Egrant.
           ++ unfold brk_eff. cbn [eff_ret]. rewrite (refusal_b_brk_ms ms x8 model _ Hno).
              unfold brk_refusal_b. cbv zeta. fold req. rewrite E3. apply andb_false_r.
        -- left. apply Hmem. split; [exact Hok|]. intros _ _ r' Hr'.
           destruct (brk_r_ok_cases model req r' Hr') as [-> | ->].
           ++ unfold brk_refusal_b. cbv zeta. fold req. rewrite E2, E3, bv_eqb_refl.
              destruct (w_is0 req); [discriminate E1 | reflexivity].
           ++ unfold brk_resolution_ok in Hr'. rewrite Egrant in Hr'. discriminate Hr'.
      * left. apply Hmem. split; [exact Hok|]. intros _ E. rewrite Eref in E. discriminate E.
  - apply brk_no_unmodeled. exact Hno.
  - intros [r [Hr Hf]]. cbn [proj1_sig]. apply (proj1 (Hshape r Hr)).
  - intros [r [Hr Hf]]. cbn [proj1_sig]. apply (proj2 (Hshape r Hr)).
Qed.

(* [comment removed for export] *)
Lemma brk_adm_query : forall model r,
  brk_adm model (Z_to_bv 64 0) r <-> r = vm_brk (m_vmmaps model).
Proof.
  intros model r. unfold brk_adm, brk_resolution_ok, Mmap.brk_r_ok, brk_refusal_b. cbv zeta.
  unfold w_is0. rewrite bv_eqb_refl. cbn [orb negb andb]. rewrite bv_eqb_eq. split.
  - intros [H _]. exact H.
  - intros H. split; [exact H | intros _ E; discriminate E].
Qed.

(* [comment removed for export] *)
Lemma srz_brk_query_at : forall ms model x8 K,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  ms_gpr ms 0 = Z_to_bv 64 0 ->
  srealizes segs scfg (mkCfg (advance_past_svc (apply_effect ms (mkEffectU (vm_brk (m_vmmaps model)) [] [] [] [] [])))
                             model) K ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model x8 K Hh Hlazy Hsvc Hno H0 Hc.
  assert (Hq : brk_adm model (ms_gpr ms 0) (vm_brk (m_vmmaps model))) by (rewrite H0; apply brk_adm_query; reflexivity).
  apply (srz_cases1 segs scfg (mkCfg ms model) _ _ K (exist _ _ Hq) (node_brk ms model x8 Hh Hlazy Hsvc Hno)).
  intros [r Hr]. cbn [proj1_sig].
  assert (Er : r = vm_brk (m_vmmaps model)) by (apply (brk_adm_query model); rewrite <- H0; exact Hr). subst r.
  rewrite H0, brk_zeros_query, brk_unmaps_keep.
  rewrite (brk_model_query _ model eq_refl), vmmaps_eta, with_vmmaps_eta.
  exact Hc.
Qed.

Lemma rz_brk_query : forall regs (pc : word) mem model w K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 214 ->
  getr regs 10 = Z_to_bv 64 0 ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem (seg_rom segs))
                       model) K ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w K HF HE Hh Hlazy H17 H10 Hc.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply (srz_brk_query_at _ model (getr regs 17));
    [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 |].
  rewrite adv_ret_epend. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma brk_r_ok_grow_cases : forall m req r,
  let h := m_vmmaps m in
  (0 < bv_unsigned req)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
  (bv_unsigned (vm_brk h) <= bv_unsigned req)%Z ->
  brk_resolution_ok m req r <->
  (r = vm_brk h \/ (r = req /\ Mmap.brk_grow_ok m req req = true)).
Proof.
  intros m req r h Hpos Hs Hb.
  unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta. fold h.
  assert (E0 : w_is0 req = false).
  { unfold w_is0, bv_eqb. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia. }
  rewrite E0. unfold min_brk.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [orb].
  rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  rewrite andb_true_iff, orb_true_iff, !bv_eqb_eq. split.
  - intros [[-> | ->] Hg]; [right; auto | left; reflexivity].
  - intros [-> | [-> Hg]]; split; [right; reflexivity | | left; reflexivity | exact Hg].
    unfold Mmap.brk_grow_ok. fold h. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_adm_grow_cases : forall m req r,
  let h := m_vmmaps m in
  sc_alloc scfg = false ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
  (bv_unsigned (vm_brk h) < bv_unsigned req)%Z ->
  brk_adm m req r <->
  r = (if Mmap.brk_grow_ok m req req then req else vm_brk h).
Proof.
  intros m req r. cbv zeta. intros Halloc Hs Hb.
  set (b := vm_brk (m_vmmaps m)) in *.
  pose proof (proj1 (bv_unsigned_in_range 64 b)) as Hb0.
  assert (Hpos : (0 < bv_unsigned req)%Z) by lia.
  assert (Hble : (bv_unsigned b <= bv_unsigned req)%Z) by lia.
  assert (Hneq : bv_eqb req b = false).
  { apply bv_eqb_neq. intros E. rewrite E in Hb. lia. }
  assert (Href : forall r', brk_refusal_b m req r' = bv_eqb r' b).
  { intros r'. unfold brk_refusal_b. cbv zeta. fold b. unfold min_brk.
    replace (w_is0 req) with false
      by (symmetry; unfold w_is0, bv_eqb; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; apply Z.eqb_neq; lia).
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite Hneq. reflexivity. }
  pose proof (fun r' => brk_r_ok_grow_cases m req r' Hpos Hs Hble) as Hcases. cbv zeta in Hcases. fold b in Hcases.
  unfold brk_adm. rewrite (Hcases r).
  destruct (Mmap.brk_grow_ok m req req) eqn:Eg; split.
  - intros [[-> | [-> _]] Hf]; [| reflexivity].
    exfalso.
    assert (E1 : brk_refusal_b m req b = true) by (rewrite Href; apply bv_eqb_refl).
    assert (E2 : brk_refusal_b m req req = true).
    { apply (Hf Halloc E1 req). apply (proj2 (Hcases req)). right. split; [reflexivity | first [exact Eg | reflexivity]]. }
    rewrite Href, Hneq in E2. discriminate E2.
  - intros ->. split; [right; split; [reflexivity | first [exact Eg | reflexivity]]|]. rewrite Href, Hneq. intros _ E. discriminate E.
  - intros [[-> | [-> Habs]] _]; [reflexivity | rewrite ?Eg in Habs; discriminate Habs].
  - intros ->. split; [left; reflexivity|]. intros _ _ r' Hr'. rewrite Href.
    destruct (proj1 (Hcases r') Hr') as [-> | [-> Habs]]; [apply bv_eqb_refl | rewrite ?Eg in Habs; discriminate Habs].
Qed.

(* [comment removed for export] *)
Lemma brk_model_keep : forall m req,
  brk_model req (vm_brk (m_vmmaps m)) m = m.
Proof.
  intros m req. unfold brk_model, with_brk_next. cbv zeta.
  rewrite brk_unmaps_keep. cbn [forget_vm_ranges].
  unfold brk_model_next, brk_maps_next.
  rewrite Z.ltb_irrefl, andb_false_r, brk_grants_keep, brk_unmaps_keep.
  cbn [app maps_subtract_ranges fold_left]. rewrite vmmaps_eta. apply with_vmmaps_eta.
Qed.

(* [comment removed for export] *)
Lemma brk_model_grow_eq : forall m (d : Z),
  let h := m_vmmaps m in
  let b := vm_brk h in
  (0 < d)%Z -> (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z ->
  brk_model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) m
  = with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                   (vm_noaccess h) (vm_start_brk h)
                   (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m.
Proof.
  intros m d h b Hd Hb0 Hnw Hbal Hdal.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)).
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
  assert (Hreq0 : req <> Z_to_bv 64 0).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  unfold brk_model, with_brk_next. cbv zeta. fold h. fold b.
  rewrite (brk_unmaps_grow req b) by lia. cbn [forget_vm_ranges].
  unfold brk_model_next, brk_maps_next. fold b.
  rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned b))) by lia. rewrite andb_false_r.
  rewrite (brk_grants_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
  cbn [app maps_subtract_ranges fold_left].
  replace (req - b) with (Z_to_bv 64 d); [reflexivity|].
  apply bv_eq. rewrite bv_sub_unsigned, Hureq.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). rewrite u64_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma srz_brk_grow_at : forall ms model x8 (d : Z) K,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  sc_alloc scfg = false ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  ms_gpr ms 0 = Z_to_bv 64 (bv_unsigned b + d) ->
  (* [comment removed for export] *)
  (Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = false ->
   srealizes segs scfg (mkCfg (advance_past_svc (apply_effect ms (mkEffectU b [] [] [] [] []))) model) K) ->
  (* [comment removed for export] *)
  (Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
   srealizes segs scfg (mkCfg (advance_past_svc (apply_effect ms
                                 (mkEffectU (Z_to_bv 64 (bv_unsigned b + d)) [] [(b, Z_to_bv 64 d)] [] [] [])))
                       (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                                      (vm_noaccess h) (vm_start_brk h)
                                      (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) K) ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model x8 d K Hh Hlazy Hsvc Hno Halloc h b Hbal Hdal Hd Hb0 Hnw Hs H0 HA HB.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  assert (Hcases : forall r, brk_adm model (ms_gpr ms 0) r <-> r = (if Mmap.brk_grow_ok model req req then req else b)).
  { intros r. rewrite H0. apply (brk_adm_grow_cases model req r Halloc); fold h; fold b; rewrite Hureq; lia. }
  set (r0 := if Mmap.brk_grow_ok model req req then req else b).
  assert (Hr0 : brk_adm model (ms_gpr ms 0) r0) by (apply Hcases; reflexivity).
  apply (srz_cases1 segs scfg (mkCfg ms model) _ _ K (exist _ r0 Hr0) (node_brk ms model x8 Hh Hlazy Hsvc Hno)).
  intros [r Hr]. cbn [proj1_sig]. fold h.
  pose proof (proj1 (Hcases r) Hr) as Er. subst r.
  destruct (Mmap.brk_grow_ok model req req) eqn:Eg.
  - (* [comment removed for export] *)
    assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
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
    apply HB. first [exact Eg | reflexivity].
  - (* [comment removed for export] *)
    fold b. rewrite brk_zeros_keep, brk_unmaps_keep. unfold b, h. rewrite brk_model_keep.
    apply HA. first [exact Eg | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma rz_brk_grow : forall regs (pc : word) mem model w (d : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 214 ->
  sc_alloc scfg = false ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->
  (* [comment removed for export] *)
  (Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = false ->
   srealizes segs scfg (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem (seg_rom segs)) model) K) ->
  (* [comment removed for export] *)
  (Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
   srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                             (zfill b (Z_to_bv 64 d) mem) (seg_rom segs))
                       (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                                      (vm_noaccess h) (vm_start_brk h)
                                      (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) K) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w d K HF HE Hh Hlazy H17 Halloc h b Hbal Hdal Hd Hb0 Hnw Hs H10 HA HB.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  apply (srz_brk_grow_at (epend regs pc mem (seg_rom segs) (getr regs 17)) model (getr regs 17) d K
           Hh Hlazy eq_refl ltac:(rewrite H17; apply u64_lit; lia) Halloc Hbal Hdal Hd Hb0 Hnw Hs
           ltac:(rewrite ms_gpr_epend0; exact H10)).
  - intros Eg. rewrite adv_ret_epend. apply HA. exact Eg.
  - intros Eg. rewrite adv_zeros1_epend. apply HB. exact Eg.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma errno_ret_in_mmap : forall r, errno_ret_in mmap_errnos r = bv_eqb r (errno_ret ENOMEM).
Proof. intros r. unfold errno_ret_in, mmap_errnos. cbn [existsb]. apply orb_false_r. Qed.

Lemma errno_ret_in_mprotect : forall r, errno_ret_in mprotect_errnos r = bv_eqb r (errno_ret ENOMEM).
Proof. intros r. unfold errno_ret_in, mprotect_errnos. cbn [existsb]. apply orb_false_r. Qed.

(* [comment removed for export] *)
Lemma node_chk_grant_only : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (i0 : I),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  injected_family_off scfg (sys_input segs ms x8) = true ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) []) ->
  (forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false) ->
  (forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
       (exists i, eff = effs i /\ m' = ms' i /\ evs = [])
    \/ (refusal_b (sys_input segs ms x8) model (eff_ret eff) = true /\ m_halted m' = None)) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  node_ok segs scfg (mkCfg ms model) I (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' i0 Hh Hsvc Hoff Hok Hnr Hinv Hnu Hh' Hlazy.
  apply (node_chk_sp segs scfg ms model x8 I effs ms' Hh Hsvc Hok).
  - intros i. apply not_spurious_nonrefusal. apply Hnr.
  - intros eff m' evs Hc. destruct (Hinv eff m' evs Hc) as [Hm | [Hr Hhm]]; [left; exact Hm | right].
    split; [| exact Hhm].
    apply (spurious_intro scfg _ model eff (effs i0) (ms' i0) []); [exact Hoff | exact Hr | | apply Hnr].
    apply check_syscall_ok_iff. apply Hok.
  - exact Hnu.
  - exact Hh'.
  - exact Hlazy.
Qed.

Lemma injected_family_off_222 : forall ms x8,
  bv_unsigned x8 = 222%Z -> sc_alloc scfg = false ->
  injected_family_off scfg (sys_input segs ms x8) = true.
Proof.
  intros ms x8 Hno Halloc. rewrite (injected_family_off_alloc scfg _ 222%Z);
    [rewrite Halloc; reflexivity | rewrite in_sysno_sys_input; exact Hno | auto].
Qed.

Lemma injected_family_off_226 : forall ms x8,
  bv_unsigned x8 = 226%Z -> sc_alloc scfg = false ->
  injected_family_off scfg (sys_input segs ms x8) = true.
Proof.
  intros ms x8 Hno Halloc. rewrite (injected_family_off_alloc scfg _ 226%Z);
    [rewrite Halloc; reflexivity | rewrite in_sysno_sys_input; exact Hno | auto 6].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition noaccess_model (a n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                 ((a, n) :: vm_maps (m_vmmaps m))
                 ((a, n) :: vm_noaccess (m_vmmaps m))
                 (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.

(* [comment removed for export] *)
Definition grant_ok_na (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).

Lemma grant_ok_grant_ok_na : forall hint m a n, grant_ok hint m a n = true -> grant_ok_na hint m a n = true.
Proof.
  intros hint m a n H. unfold grant_ok in H. unfold grant_ok_na.
  apply andb_true_iff in H as [H _]. exact H.
Qed.

Lemma grant_ok_na_unpack : forall hint m a n,
  grant_ok_na hint m a n = true ->
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\
  (bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true.
Proof.
  intros hint m a n H. unfold grant_ok_na in H.
  rewrite !andb_true_iff in H. destruct H as [[[H1 H2] H3] H4].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. auto.
Qed.

Lemma grant_na_not_errno : forall hint model a n,
  (0 <= n)%Z -> grant_ok_na hint model a n = true -> errno_ret_in mmap_errnos a = false.
Proof.
  intros hint model a n Hn Hg. destruct (grant_ok_na_unpack _ _ _ _ Hg) as (_ & _ & Htop & _).
  apply errno_ret_in_below; [reflexivity|]. alloc_top_bounds. unfold two_pow_64 in *. lia.
Qed.

Definition mmap_noaccess_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 0
  /\ ms_gpr ms 3 = Z_to_bv 64 34 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

Lemma mmap_noaccess_check : forall ms x8 model eff,
  bv_unsigned x8 = 222%Z -> mmap_noaccess_args_ok ms ->
  check_syscall (sys_input segs ms x8) eff model
  = let n := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
    match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in mmap_errnos r
        then match us with [] => CheckOk model [] | _ => CheckReject end
        else if grant_ok_na (ms_gpr ms 0) model r n && listNN_eqb us [(r, Z_to_bv 64 n)]
             then CheckOk (noaccess_model r (Z_to_bv 64 n) model) []
             else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff Hno (H1 & H2 & H3 & H4 & H5).
  rewrite (mmap_check ms x8 model eff Hno). unfold check_mmap.
  assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
  rewrite E1, H2, H3, H5.
  replace (mmap_off_aligned_b (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
  replace (mmap_anon_b (Z_to_bv 64 34)) with true by (vm_compute; reflexivity).
  replace (mmap_modeled_b (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 0)) with false
    by (vm_compute; reflexivity).
  replace (mmap_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 0)) with true
    by (vm_compute; reflexivity).
  cbn [negb]. cbv beta iota zeta.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
  destruct cs; [|destruct us; reflexivity]. destruct ci; [|destruct us; reflexivity].
  destruct (errno_ret_in mmap_errnos r); [reflexivity|].
  unfold grant_ok_na, noaccess_model, with_mmap_backing.
  replace (mmap_noreserve_b (Z_to_bv 64 34)) with false by (vm_compute; reflexivity).
  rewrite <- !andb_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_mmap_noaccess : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  mmap_noaccess_args_ok ms ->
  sc_alloc scfg = false ->
  let n := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  (exists a, grant_ok_na (ms_gpr ms 0) model a n = true) ->
  node_ok segs scfg (mkCfg ms model)
          {a : word | grant_ok_na (ms_gpr ms 0) model a n = true}
          (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (mkEffectU (proj1_sig i) [] [] [(proj1_sig i, Z_to_bv 64 n)] [] [])))
                          (noaccess_model (proj1_sig i) (Z_to_bv 64 n) model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Hargs Halloc n [a0 Ha0].
  pose proof (fun eff => mmap_noaccess_check ms x8 model eff Hno Hargs) as Hchk. cbv zeta in Hchk. fold n in Hchk.
  assert (Hn0 : (0 <= n)%Z) by (unfold n; apply page_round_up_Z_nonneg; apply (proj1 (bv_unsigned_in_range 64 _))).
  apply (node_chk_grant_only ms model x8 {a : word | grant_ok_na (ms_gpr ms 0) model a n = true}
           (fun i => mkEffectU (proj1_sig i) [] [] [(proj1_sig i, Z_to_bv 64 n)] [] [])
           (fun i => noaccess_model (proj1_sig i) (Z_to_bv 64 n) model)
           (exist _ a0 Ha0) Hh Hsvc (injected_family_off_222 ms x8 Hno Halloc)).
  - intros [a Ha]. cbn [proj1_sig]. rewrite Hchk, (grant_na_not_errno _ _ _ _ Hn0 Ha), Ha.
    cbn [andb]. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  - intros [a Ha]. cbn [proj1_sig eff_ret].
    rewrite (refusal_b_mmap (sys_input segs ms x8) model a) by (rewrite in_sysno_sys_input; exact Hno).
    rewrite <- errno_ret_in_mmap. exact (grant_na_not_errno _ _ _ _ Hn0 Ha).
  - intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
    destruct (errno_ret_in mmap_errnos r) eqn:Er.
    + destruct us; [|discriminate]. injection Hc as <- <-. right. cbn [eff_ret].
      rewrite (refusal_b_mmap (sys_input segs ms x8) model r) by (rewrite in_sysno_sys_input; exact Hno).
      rewrite <- errno_ret_in_mmap. split; [exact Er | exact Hh].
    + destruct (grant_ok_na (ms_gpr ms 0) model r n) eqn:Hg; [|discriminate].
      destruct (listNN_eqb us [(r, Z_to_bv 64 n)]) eqn:Hl; [|discriminate].
      apply listNN_eqb_eq in Hl. subst us. injection Hc as <- <-.
      left. exists (exist _ r Hg). repeat split; reflexivity.
  - intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
    destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
    destruct (grant_ok_na (ms_gpr ms 0) model r n && listNN_eqb us [(r, Z_to_bv 64 n)])%bool; discriminate.
  - intros [a Ha]; cbn [proj1_sig]. unfold noaccess_model; rewrite with_vmmaps_halted; exact Hh.
  - intros [a Ha]; cbn [proj1_sig]. unfold noaccess_model; rewrite with_vmmaps_lazy'; exact Hlazy.
Qed.

Lemma srz_mmap_noaccess_at : forall ms model x8 K,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  mmap_noaccess_args_ok ms ->
  sc_alloc scfg = false ->
  let n := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  (exists a, grant_ok_na (ms_gpr ms 0) model a n = true) ->
  (forall a, grant_ok_na (ms_gpr ms 0) model a n = true ->
     srealizes segs scfg (mkCfg (advance_past_svc (apply_effect ms (mkEffectU a [] [] [(a, Z_to_bv 64 n)] [] [])))
                                (noaccess_model a (Z_to_bv 64 n) model)) K) ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model x8 K Hh Hlazy Hsvc Hno Hargs Halloc n Hex HK.
  destruct Hex as [a0 Ha0].
  apply (srz_cases1 segs scfg (mkCfg ms model) _ _ K (exist _ a0 Ha0)
           (node_mmap_noaccess ms model x8 Hh Hlazy Hsvc Hno Hargs Halloc (ex_intro _ a0 Ha0))).
  intros [a Ha]. cbn [proj1_sig]. apply HK. exact Ha.
Qed.

Lemma rz_mmap_noaccess : forall regs (pc : word) mem model w (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  sc_alloc scfg = false ->
  let n := page_round_up_Z len in
  (exists a, grant_ok_na (getr regs 10) model a n = true) ->
  (forall a, grant_ok_na (getr regs 10) model a n = true ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4)
                                (unfill a (Z_to_bv 64 n) mem) (seg_rom segs))
                         (noaccess_model a (Z_to_bv 64 n) model)) KB) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) KB.
Proof.
  intros regs pc mem model w len KB HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 Halloc n Hex HB.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. lia. }
  assert (Hargs : mmap_noaccess_args_ok ms).
  { unfold mmap_noaccess_args_ok, ms.
    rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
    intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
  assert (H0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; rewrite ms_gpr_epend0; reflexivity).
  pose proof (srz_mmap_noaccess_at ms model (getr regs 17) KB Hh Hlazy eq_refl
                ltac:(rewrite H17; apply u64_lit; lia) Hargs Halloc) as H.
  cbv zeta in H. rewrite Hu1, H0 in H. fold n in H. apply H; [exact Hex|].
  intros a Ha. unfold ms. rewrite adv_unmaps1_epend. apply HB. exact Ha.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mprotect_model (addr n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                 (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                 (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.

Lemma mprotect_model_next_eq : forall m addr n, mprotect_model_next m addr n = mprotect_model addr n m.
Proof. reflexivity. Qed.

Lemma mprotect_check : forall ms x8 model eff (addr : word) (len : Z),
  bv_unsigned x8 = 226%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs [] [] [] =>
        if errno_ret_in mprotect_errnos r
        then match zs with [] => CheckOk model [] | _ => CheckReject end
        else if mprotect_budget_ok model addr n && w_is0 r && listNN_eqb zs [(addr, n)]
             then CheckOk (mprotect_model addr n model) []
             else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff addr len Hno H0 Hal H1 Hlen Hnw H2 n Hna Hma.
  assert (Hlen' : (len < two_pow_64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; unfold two_pow_64 in Hlen'; lia).
  rewrite (check_syscall_226 ms x8 eff model Hno). unfold check_mprotect.
  rewrite H0, H2, Hu1.
  replace (mprotect_grows_conflict_b (Z_to_bv 64 3)) with false by (vm_compute; reflexivity).
  replace (mprotect_modeled_b (Z_to_bv 64 3)) with true by (vm_compute; reflexivity).
  rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0, bv_eqb. rewrite Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia. }
  rewrite E1. rewrite (proj2 (Z.leb_gt _ _)) by lia.
  cbv beta iota zeta. fold n. rewrite Hna, Hma. cbn [andb].
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
  destruct us; [| destruct (errno_ret_in mprotect_errnos r); reflexivity].
  destruct cs; [| destruct (errno_ret_in mprotect_errnos r); reflexivity].
  destruct ci; [| destruct (errno_ret_in mprotect_errnos r); reflexivity].
  reflexivity.
Qed.

Lemma ENOMEM_in_mprotect_errnos : In ENOMEM mprotect_errnos.
Proof. left. reflexivity. Qed.

(* [comment removed for export] *)
Lemma srz_mprotect_at : forall ms model x8 (addr : word) (len : Z) K,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 226%Z ->
  sc_alloc scfg = false ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  mprotect_budget_ok model addr n = true ->
  srealizes segs scfg (mkCfg (advance_past_svc (apply_effect ms (mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] [])))
                             (mprotect_model addr n model)) K ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model x8 addr len K Hh Hlazy Hsvc Hno Halloc H0 Hal H1 Hlen Hnw H2 n Hna Hma Hbud HK.
  pose proof (fun eff => mprotect_check ms x8 model eff addr len Hno H0 Hal H1 Hlen Hnw H2 Hna Hma) as Hchk.
  cbv zeta in Hchk. fold n in Hchk. rewrite Hbud in Hchk.
  apply (srz_cases1 segs scfg (mkCfg ms model) unit
           (fun _ => mkCfg (advance_past_svc (apply_effect ms (mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] [])))
                           (mprotect_model addr n model)) K tt).
  2:{ intros []. exact HK. }
  apply (node_chk_grant_only ms model x8 unit (fun _ => mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] [])
           (fun _ => mprotect_model addr n model) tt Hh Hsvc (injected_family_off_226 ms x8 Hno Halloc)).
  - intros []. rewrite Hchk, errno_ret_in_mprotect.
    replace (bv_eqb (Z_to_bv 64 0) (errno_ret ENOMEM)) with false by (symmetry; apply bv_eqb_neq; discriminate).
    unfold w_is0. rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  - intros []. cbn [eff_ret]. rewrite (refusal_b_mprotect (sys_input segs ms x8)) by (rewrite in_sysno_sys_input; exact Hno).
    apply bv_eqb_neq. discriminate.
  - intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_ret_in mprotect_errnos r) eqn:Er.
    + destruct zs; [|discriminate]. injection Hc as <- <-. right. cbn [eff_ret].
      rewrite (refusal_b_mprotect (sys_input segs ms x8)) by (rewrite in_sysno_sys_input; exact Hno).
      rewrite <- errno_ret_in_mprotect. split; [exact Er | exact Hh].
    + cbn [andb] in Hc. destruct (w_is0 r) eqn:E0; [|discriminate].
      destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
      apply listNN_eqb_eq in Hl. subst zs. injection Hc as <- <-.
      unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r. left. exists tt. repeat split; reflexivity.
  - intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_ret_in mprotect_errnos r); [destruct zs; discriminate|].
    cbn [andb] in Hc. destruct (w_is0 r && listNN_eqb zs [(addr, n)])%bool; discriminate.
  - intros []. unfold mprotect_model; rewrite with_vmmaps_halted; exact Hh.
  - intros []. unfold mprotect_model; rewrite with_vmmaps_lazy'; exact Hlazy.
Qed.

Lemma rz_mprotect : forall regs (pc : word) mem model w (addr : word) (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 226 ->
  sc_alloc scfg = false ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  getr regs 12 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  mprotect_budget_ok model addr n = true ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill addr n mem) (seg_rom segs))
                       (mprotect_model addr n model)) KB ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) KB.
Proof.
  intros regs pc mem model w addr len KB HF HE Hh Hlazy H17 Halloc H10 Hal H11 Hlen Hnw H12 n Hna Hma Hbud HB.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  apply (srz_mprotect_at (epend regs pc mem (seg_rom segs) (getr regs 17)) model (getr regs 17) addr len KB
           Hh Hlazy eq_refl ltac:(rewrite H17; apply u64_lit; lia) Halloc
           ltac:(rewrite ms_gpr_epend0; exact H10) Hal
           ltac:(rewrite ms_gpr_epend1; exact H11) Hlen Hnw
           ltac:(rewrite ms_gpr_epend2; exact H12) Hna Hma Hbud).
  rewrite adv_zeros1_epend. exact HB.
Qed.

(* [comment removed for export] *)
Lemma srz_mprotect_blocked_at : forall ms model x8 (addr : word) (len : Z) K,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 226%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  mprotect_budget_ok model addr n = false ->
  srealizes segs scfg (mkCfg (advance_past_svc (apply_effect ms (mkEffectU (errno_ret ENOMEM) [] [] [] [] []))) model) K ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model x8 addr len K Hh Hlazy Hsvc Hno H0 Hal H1 Hlen Hnw H2 n Hna Hma Hbud HK.
  pose proof (fun eff => mprotect_check ms x8 model eff addr len Hno H0 Hal H1 Hlen Hnw H2 Hna Hma) as Hchk.
  cbv zeta in Hchk. fold n in Hchk. rewrite Hbud in Hchk. cbn [andb] in Hchk.
  eapply srz_silent1; [| exact HK].
  apply (node_det segs scfg ms model x8 (mkEffectU (errno_ret ENOMEM) [] [] [] [] []) model [] Hh Hsvc).
  - intros [r ws zs us cs ci] m' evs. rewrite Hchk. split.
    + intros Hc. destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mprotect_errnos r) eqn:Er; [|discriminate].
      destruct zs; [|discriminate]. injection Hc as <- <-.
      rewrite errno_ret_in_mprotect in Er. apply bv_eqb_eq in Er. subst r. repeat split; reflexivity.
    + intros (He & -> & ->). injection He as -> -> -> -> -> ->.
      rewrite (errno_ret_in_intro _ _ ENOMEM_in_mprotect_errnos). reflexivity.
  - intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_ret_in mprotect_errnos r); [destruct zs; discriminate | discriminate].
  - exact Hh.
  - exact Hlazy.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fixed_noaccess_model (addr n : word) (m : Model) : Model :=
  vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                   ((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).

(* [comment removed for export] *)
Definition fixed_destroyed_model (addr n : word) (m : Model) : Model :=
  vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                   (maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).

Lemma fixed_noaccess_model_simple : forall addr n m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  fixed_noaccess_model addr n m
  = with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                   ((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Proof. intros. unfold fixed_noaccess_model. apply vm_forget_range_id; [rewrite with_vmmaps_lazy'|]; assumption. Qed.

Lemma fixed_destroyed_model_simple : forall addr n m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  fixed_destroyed_model addr n m
  = with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                   (maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Proof. intros. unfold fixed_destroyed_model. apply vm_forget_range_id; [rewrite with_vmmaps_lazy'|]; assumption. Qed.

Definition mmap_fixed_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 0
  /\ ms_gpr ms 3 = Z_to_bv 64 50 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

(* [comment removed for export] *)
Lemma mmap_fixed_check : forall ms x8 model eff (addr : word) (len : Z),
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
  pose proof (u64_range addr) as Har.
  assert (Hlen' : (len < 2 ^ 64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). alloc_top_bounds. unfold two_pow_64 in *. lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1'; apply u64_lit; lia).
  rewrite (mmap_check ms x8 model eff Hno). unfold check_mmap.
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
  cbn [negb]. cbv beta iota zeta.
  rewrite (proj2 (Z.leb_gt _ _)) by (alloc_top_bounds; unfold two_pow_64 in *; lia).
  rewrite (proj2 (Z.leb_le _ _) Htop). cbn [negb].
  rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
  rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n. rewrite Hrf, Hmc. cbn [andb].
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
  destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct us; reflexivity].
  destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct us; reflexivity].
  unfold fixed_noaccess_model, fixed_destroyed_model, with_mmap_replacement, with_mmap_backing, with_mmap_destroyed.
  replace (mmap_noreserve_b (Z_to_bv 64 50)) with false by (vm_compute; reflexivity).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma srz_mmap_fixed_noaccess_at : forall ms model x8 (addr : word) (len : Z) K,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  mmap_fixed_args_ok ms ->
  sc_alloc scfg = false ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  srealizes segs scfg (mkCfg (advance_past_svc (apply_effect ms (mkEffectU addr [] [] [(addr, n)] [] [])))
                             (fixed_noaccess_model addr n model)) K ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model x8 addr len K Hh Hlazy Hsvc Hno Hargs Halloc H0 Hal Hpos H1 Hlen Htop n Hrf Hmc HK.
  pose proof (fun eff => mmap_fixed_check ms x8 model eff addr len Hno Hargs H0 Hal Hpos H1 Hlen Htop Hrf Hmc) as Hchk.
  cbv zeta in Hchk. fold n in Hchk.
  assert (Hne : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|].
    pose proof (page_round_up_Z_bounds len ltac:(lia)). alloc_top_bounds. unfold two_pow_64 in *. lia. }
  apply (srz_cases1 segs scfg (mkCfg ms model) unit
           (fun _ => mkCfg (advance_past_svc (apply_effect ms (mkEffectU addr [] [] [(addr, n)] [] [])))
                           (fixed_noaccess_model addr n model)) K tt).
  2:{ intros []. exact HK. }
  apply (node_chk_grant_only ms model x8 unit (fun _ => mkEffectU addr [] [] [(addr, n)] [] [])
           (fun _ => fixed_noaccess_model addr n model) tt Hh Hsvc (injected_family_off_222 ms x8 Hno Halloc)).
  - intros []. rewrite Hchk, Hne, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  - intros []. cbn [eff_ret]. rewrite (refusal_b_mmap (sys_input segs ms x8)) by (rewrite in_sysno_sys_input; exact Hno).
    rewrite <- errno_ret_in_mmap. exact Hne.
  - intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_ret_in mmap_errnos r) eqn:Er.
    + right. cbn [eff_ret]. rewrite (refusal_b_mmap (sys_input segs ms x8)) by (rewrite in_sysno_sys_input; exact Hno).
      rewrite <- errno_ret_in_mmap. split; [exact Er|].
      destruct us; [injection Hc as <- <-; exact Hh|].
      destruct (listNN_eqb _ _); [|discriminate]. injection Hc as <- <-.
      unfold fixed_destroyed_model. rewrite vm_forget_range_halted, with_vmmaps_halted. exact Hh.
    + destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
      destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
      apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r us. injection Hc as <- <-.
      left. exists tt. repeat split; reflexivity.
  - intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_ret_in mmap_errnos r); [destruct us; [discriminate | destruct (listNN_eqb _ _); discriminate]|].
    destruct (bv_eqb r addr && listNN_eqb us [(addr, n)])%bool; discriminate.
  - intros []. unfold fixed_noaccess_model. rewrite vm_forget_range_halted, with_vmmaps_halted; exact Hh.
  - intros []. unfold fixed_noaccess_model. apply vm_forget_range_lazy_nil; rewrite with_vmmaps_lazy'; exact Hlazy.
Qed.

Lemma rz_mmap_fixed_noaccess : forall regs (pc : word) mem model w (addr : word) (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  sc_alloc scfg = false ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 50 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr n mem) (seg_rom segs))
                       (fixed_noaccess_model addr n model)) KB ->
  srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) KB.
Proof.
  intros regs pc mem model w addr len KB HF HE Hh Hlazy H17 Halloc H10 Hal Hpos H11 Hlen Htop H12 H13 H14 H15 n Hrf Hmc HB.
  pose proof (u64_range addr) as Har.
  assert (Hlen' : (len < 2 ^ 64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). alloc_top_bounds. unfold two_pow_64 in *. lia. }
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hargs : mmap_fixed_args_ok ms).
  { unfold mmap_fixed_args_ok, ms.
    rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
    intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
  apply (srz_mmap_fixed_noaccess_at ms model (getr regs 17) addr len KB Hh Hlazy eq_refl
           ltac:(rewrite H17; apply u64_lit; lia) Hargs Halloc
           ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
           ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Htop Hrf Hmc).
  unfold ms. rewrite adv_unmaps1_epend. exact HB.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition tid_I : Type := { t : word | (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z }.

Lemma one_tid_ok : (0 < bv_unsigned (Z_to_bv 64 1) < PID_MAX_ENVELOPE)%Z.
Proof. unfold PID_MAX_ENVELOPE. rewrite u64_lit by lia. lia. Qed.

Lemma node_set_tid : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
  m_tid model = None ->
  node_ok segs scfg (mkCfg ms model) tid_I (fun _ => [])
    (fun i => mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Htid.
  assert (Hchk : forall eff, check_syscall (sys_input segs ms x8) eff model =
     match eff with
     | mkEffectU ret [] [] [] [] [] =>
         if (0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z
         then CheckOk (with_tid ret model) [] else CheckReject
     | _ => CheckReject end).
  { intros eff. rewrite (check_syscall_96 ms x8 eff model Hno). unfold check_set_tid_address. rewrite Htid. reflexivity. }
  pose (effs := fun i : tid_I => mkEffectU (proj1_sig i) [] [] [] [] []).
  assert (Enx : forall i : tid_I,
    mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)
    = mkCfg (advance_past_svc (apply_effect ms (effs i))) (with_tid (proj1_sig i) model)).
  { intros [t Ht]. cbn [proj1_sig effs]. rewrite <- (apply_effect_no_write ms t). reflexivity. }
  assert (Hnode : node_ok segs scfg (mkCfg ms model) tid_I (fun _ => [])
                    (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (with_tid (proj1_sig i) model))).
  { apply (node_chk segs scfg ms model x8 tid_I effs (fun i => with_tid (proj1_sig i) model) Hh Hsvc).
    - intros [t [Ht1 Ht2]]. subst effs. cbn [proj1_sig]. rewrite Hchk.
      rewrite (proj2 (Z.ltb_lt _ _) Ht1), (proj2 (Z.ltb_lt _ _) Ht2). reflexivity.
    - intros [ret ws zs us cs ci] m' ev Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z) eqn:Eb; [|discriminate].
      apply andb_true_iff in Eb as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
      injection Hc as <- <-. exists (exist _ ret (conj E1 E2)). repeat split; reflexivity.
    - intros [ret ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z); discriminate.
    - intros i. rewrite with_tid_halted. exact Hh.
    - intros i. rewrite with_tid_lazy. exact Hlazy.
    - intros i. apply not_spurious_on. apply injected_family_off_none. rewrite in_sysno_sys_input, Hno. exact injected_arm_96. }
  destruct Hnode as [Hfw Hbw]. split.
  - intros i. rewrite Enx. apply Hfw.
  - intros e st Hss. destruct (Hbw e st Hss) as (i & -> & ->). exists i. rewrite Enx. split; reflexivity.
Qed.

Lemma srz_set_tid_at : forall ms model x8 K,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     srealizes segs scfg (mkCfg (advance_past_svc (set_gpr0 ms tid)) (with_tid tid model)) K) ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model x8 K Hh Hlazy Hsvc Hno Htid Hk.
  apply (srz_cases1 segs scfg (mkCfg ms model) _ _ K (exist _ (Z_to_bv 64 1) one_tid_ok)
           (node_set_tid ms model x8 Hh Hlazy Hsvc Hno Htid)).
  intros [t Ht]. cbn [proj1_sig]. apply Hk. exact Ht.
Qed.

Lemma rz_set_tid : forall regs (pc : word) mem rom model K w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model K w HF HE Hh Hlazy H17 Htid Hk.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply (srz_set_tid_at _ model (getr regs 17));
    [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid |].
  intros t Ht. rewrite adv_set_epend. apply Hk. exact Ht.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_exit_at : forall regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply srz_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rz_exit_at_lit : forall regs (pc : word) mem rom model w (code : Z),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = Z_to_bv 64 code -> (0 <= code < 256)%Z ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10 Hc.
  rewrite <- (bv_and_255_small code Hc). eapply rz_exit_at; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma vm_backing_used_simple : forall m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_backing_used m = vm_backed_bytes (m_vmmaps m).
Proof.
  intros m Hl Hm. unfold vm_backing_used. rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat Z.mul]. unfold vm_backed_bytes. lia.
Qed.

Lemma vm_backed_bytes_no_noaccess : forall h,
  vm_noaccess h = [] -> vm_backed_bytes h = vm_live_bytes h.
Proof. intros h H. unfold vm_backed_bytes, vm_backed_maps. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma brk_grow_ok_aligned_intro : forall m d,
  let h := m_vmmaps m in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z ->
  (bv_unsigned b + d <= alloc_top h)%Z ->
  region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 (d + page_size)) = true ->
  (vm_backing_used m + d <= vm_limit h)%Z ->
  Mmap.brk_grow_ok m (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true.
Proof.
  intros m d h b Hbal Hdal Hd Hb0 Htop Hrf Hlive.
  pose proof (u64_range b) as Hbr.
  assert (Htb : (alloc_top h < 2 ^ 64)%Z) by (alloc_top_bounds; unfold two_pow_64 in *; lia).
  assert (Hureq : bv_unsigned (Z_to_bv 64 (bv_unsigned b + d)) = (bv_unsigned b + d)%Z) by (apply u64_lit; lia).
  unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok. fold h. fold b. rewrite Hureq.
  rewrite (proj2 (Z.ltb_lt 0 _) Hb0), (proj2 (Z.ltb_lt (bv_unsigned b) _)) by lia. cbn [andb].
  rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
  rewrite (page_round_up_Z_aligned (bv_unsigned b + d))
    by (first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
  rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  rewrite (proj2 (Z.leb_le _ _)) by lia.
  replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
  replace (bv_unsigned b + d + page_size - bv_unsigned b)%Z with (d + page_size)%Z by lia. rewrite Hrf.
  replace (bv_unsigned (Z_to_bv 64 (bv_unsigned b + d) - b)) with d.
  2:{ rewrite bv_sub_unsigned, Hureq. rewrite bv_wrap_small by (unfold bv_modulus; lia). lia. }
  rewrite (proj2 (Z.leb_le _ _) Hlive). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_grow_admissible_init : forall reserved (brk0 mbase sp : word) lim (model : Model) d,
  (reserved_top reserved <= bv_unsigned brk0)%Z ->
  (bv_unsigned brk0 mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned brk0)%Z ->
  (bv_unsigned brk0 + d <= alloc_top (mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp))%Z ->
  (d <= lim)%Z ->
  m_vmmaps model = mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp ->
  m_vm_lazy model = [] -> m_vm_materialized model = [] ->
  Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned brk0 + d)) (Z_to_bv 64 (bv_unsigned brk0 + d)) = true.
Proof.
  intros reserved brk0 mbase sp lim model d Htop Hbal Hdal Hd Hb0 Hce Hlim Hvm Hlz Hmt.
  pose proof (brk_grow_ok_aligned_intro model d) as H. cbv zeta in H. rewrite Hvm in H. cbn -[alloc_top Z_to_bv bv_unsigned Z.add Z.modulo region_free] in H.
  apply H; try assumption; try lia.
  - rewrite app_nil_r. apply region_free_above_top. exact Htop.
  - rewrite vm_backing_used_simple by assumption. rewrite Hvm. cbn. lia.
Qed.

End WithSegs.
End FPX_1.

Section FPX_2. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u64_roundtrip : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma region_free_app : forall l1 l2 (lo n : word),
  region_free (l1 ++ l2) lo n = region_free l1 lo n && region_free l2 lo n.
Proof.
  induction l1 as [|[b s] l1 IH]; intros l2 lo n; [reflexivity|].
  cbn [region_free app]. rewrite IH, andb_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma region_free_In : forall l (lo n b s : word),
  region_free l lo n = true -> In (b, s) l ->
  bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo.
Proof.
  induction l as [|[b' s'] l IH]; intros lo n b s Hrf Hin; [destruct Hin|].
  apply region_free_cons in Hrf as [Hd Hrf].
  destruct Hin as [E | Hin]; [injection E as -> ->; exact Hd | exact (IH _ _ _ _ Hrf Hin)].
Qed.

Lemma region_free_intro : forall l (lo n : word),
  (forall b s, In (b, s) l ->
     bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo) ->
  region_free l lo n = true.
Proof.
  induction l as [|[b s] l IH]; intros lo n H; [reflexivity|].
  cbn [region_free]. rewrite IH by (intros b' s' Hin; apply H; right; exact Hin).
  rewrite andb_true_r. apply negb_true_iff. unfold iv_overlap. apply andb_false_iff.
  destruct (H b s (or_introl eq_refl)) as [Hl | Hr]; [right | left]; apply Z.ltb_ge; lia.
Qed.

(* [comment removed for export] *)
Lemma map_has_head : forall (a n : word) l, map_has ((a, n) :: l) a n = true.
Proof. intros. unfold map_has. cbn [existsb fst snd]. rewrite !bv_eqb_refl. reflexivity. Qed.

Lemma map_has_cons : forall p (a n : word) l, map_has l a n = true -> map_has (p :: l) a n = true.
Proof. intros p a n l H. unfold map_has in *. cbn [existsb]. rewrite H. apply orb_true_r. Qed.

Lemma map_contains_head : forall (a sz lo n : word) l,
  bv_unsigned a <= bv_unsigned lo ->
  bv_unsigned lo + bv_unsigned n <= bv_unsigned a + bv_unsigned sz ->
  map_contains ((a, sz) :: l) lo n = true.
Proof.
  intros a sz lo n l H1 H2. unfold map_contains. cbn [existsb fst snd].
  rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2). reflexivity.
Qed.

Lemma map_contains_cons : forall p (lo n : word) l,
  map_contains l lo n = true -> map_contains (p :: l) lo n = true.
Proof. intros p lo n l H. unfold map_contains in *. cbn [existsb]. rewrite H. apply orb_true_r. Qed.

(* [comment removed for export] *)
Lemma map_remove_nil : forall (a : word), map_remove [] a = [].
Proof. reflexivity. Qed.

Lemma map_remove_head : forall (a n : word) l, map_remove ((a, n) :: l) a = map_remove l a.
Proof. intros. unfold map_remove. cbn [List.filter fst]. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma map_remove_skip : forall (b s a : word) l,
  b <> a -> map_remove ((b, s) :: l) a = (b, s) :: map_remove l a.
Proof. intros b s a l H. unfold map_remove. cbn [List.filter fst]. rewrite (bv_eqb_neq _ _ H). reflexivity. Qed.

Lemma map_remove_notin : forall l (a : word),
  (forall b s, In (b, s) l -> b <> a) -> map_remove l a = l.
Proof.
  induction l as [|[b s] l IH]; intros a H; [reflexivity|].
  rewrite map_remove_skip by (apply (H b s); left; reflexivity).
  rewrite IH by (intros b' s' Hin; apply (H b' s'); right; exact Hin). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma disjoint_base_ne : forall (lo n b s : word),
  0 < bv_unsigned n -> 0 < bv_unsigned s ->
  (bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo) ->
  b <> lo.
Proof. intros lo n b s Hn Hs Hd ->. lia. Qed.

(* [comment removed for export] *)
Lemma live_bytes_cons : forall (a n : word) l, live_bytes ((a, n) :: l) = bv_unsigned n + live_bytes l.
Proof. reflexivity. Qed.

Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros l2; [reflexivity|]. cbn [live_bytes app]. rewrite IH. lia. Qed.

Lemma live_bytes_nonneg : forall l, 0 <= live_bytes l.
Proof. induction l as [|[a n] l IH]; [cbn; lia|]. cbn [live_bytes]. pose proof (u64_range n). lia. Qed.

Lemma live_bytes_map_remove_le : forall l (a : word), live_bytes (map_remove l a) <= live_bytes l.
Proof.
  induction l as [|[b s] l IH]; intros a; [cbn; lia|].
  unfold map_remove. cbn [List.filter fst]. destruct (negb (bv_eqb b a)); cbn [live_bytes];
    fold (map_remove l a); pose proof (IH a); pose proof (u64_range s); lia.
Qed.

(* [comment removed for export] *)
Lemma maps_subtract_nil : forall (lo hi : Z), maps_subtract [] lo hi = [].
Proof. reflexivity. Qed.

Lemma maps_subtract_cons : forall (a sz : word) (lo hi : Z) l,
  maps_subtract ((a, sz) :: l) lo hi = iv_subtract a sz lo hi ++ maps_subtract l lo hi.
Proof. reflexivity. Qed.

Lemma maps_subtract_app : forall l1 l2 (lo hi : Z),
  maps_subtract (l1 ++ l2) lo hi = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi.
Proof.
  induction l1 as [|[a sz] l1 IH]; intros l2 lo hi; [reflexivity|].
  cbn [maps_subtract app]. rewrite IH, app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_covered : forall (a sz : word) (lo hi : Z),
  lo <= bv_unsigned a -> bv_unsigned a + bv_unsigned sz <= hi ->
  iv_subtract a sz lo hi = [].
Proof.
  intros a sz lo hi H1 H2. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_ge _ _) H2). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_self : forall (a sz : word),
  iv_subtract a sz (bv_unsigned a) (bv_unsigned a + bv_unsigned sz) = [].
Proof. intros a sz. apply iv_subtract_covered; lia. Qed.

(* [comment removed for export] *)
Lemma iv_subtract_disjoint : forall (a sz : word) (lo hi : Z),
  0 < bv_unsigned sz -> lo <= hi ->
  (hi <= bv_unsigned a \/ bv_unsigned a + bv_unsigned sz <= lo) ->
  iv_subtract a sz lo hi = [(a, sz)].
Proof.
  intros a sz lo hi Hsz Hlh Hd. unfold iv_subtract.
  destruct Hd as [Hd | Hd].
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned a) lo)) by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [app].
    rewrite Z.max_l by lia. rewrite u64_roundtrip.
    replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite u64_roundtrip. reflexivity.
  - rewrite (proj2 (Z.ltb_lt (bv_unsigned a) lo)) by lia.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [app].
    rewrite Z.min_l by lia. rewrite u64_roundtrip. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_suffix : forall (a sz : word) (lo hi : Z),
  bv_unsigned a < lo -> lo <= bv_unsigned a + bv_unsigned sz ->
  bv_unsigned a + bv_unsigned sz <= hi ->
  iv_subtract a sz lo hi = [(a, Z_to_bv 64 (lo - bv_unsigned a))].
Proof.
  intros a sz lo hi H1 H2 H3. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.ltb_ge _ _) H3). cbn [app].
  rewrite Z.min_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_prefix : forall (a sz : word) (lo hi : Z),
  lo <= bv_unsigned a -> bv_unsigned a <= hi ->
  hi < bv_unsigned a + bv_unsigned sz ->
  iv_subtract a sz lo hi = [(Z_to_bv 64 hi, Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - hi))].
Proof.
  intros a sz lo hi H1 H2 H3. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_lt _ _) H3). cbn [app].
  rewrite Z.max_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_sizes : forall (a sz : word) (lo hi : Z) N,
  0 <= lo -> hi < 2 ^ 64 ->
  bv_unsigned sz <= N ->
  Forall (fun p => bv_unsigned (snd p) <= N) (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi N Hlo Hhi Hs. pose proof (u64_range a). pose proof (u64_range sz).
  unfold iv_subtract. apply Forall_app. split.
  - destruct (bv_unsigned a <? lo) eqn:E; [|constructor].
    apply Z.ltb_lt in E. constructor; [|constructor]. cbn [snd].
    rewrite u64_lit by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|constructor].
    apply Z.ltb_lt in E. constructor; [|constructor]. cbn [snd].
    rewrite u64_lit by lia. lia.
Qed.

Lemma maps_subtract_sizes : forall l (lo hi : Z) N,
  0 <= lo -> hi < 2 ^ 64 ->
  Forall (fun p => bv_unsigned (snd p) <= N) l ->
  Forall (fun p => bv_unsigned (snd p) <= N) (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi N Hlo Hhi H; [constructor|].
  inversion H as [|p l' Hp Hl]; subst. cbn [maps_subtract]. apply Forall_app. split.
  - apply iv_subtract_sizes; assumption.
  - apply IH; assumption.
Qed.

Lemma map_remove_sizes : forall l (a : word) N,
  Forall (fun p => bv_unsigned (snd p) <= N) l ->
  Forall (fun p => bv_unsigned (snd p) <= N) (map_remove l a).
Proof.
  intros l a N H. unfold map_remove. apply List.incl_Forall with (l1 := l); [|exact H].
  apply List.incl_filter.
Qed.

Lemma maps_subtract_length : forall l (lo hi : Z),
  (length (maps_subtract l lo hi) <= 2 * length l)%nat.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi; [cbn; lia|].
  cbn [maps_subtract]. rewrite length_app. cbn [length].
  assert (length (iv_subtract a sz lo hi) <= 2)%nat.
  { unfold iv_subtract. rewrite length_app.
    destruct (_ <? _); destruct (_ <? _); cbn; lia. }
  specialize (IH lo hi). lia.
Qed.

Lemma map_remove_length : forall l (a : word), (length (map_remove l a) <= length l)%nat.
Proof.
  induction l as [|[b s] l IH]; intros a; [cbn; lia|].
  unfold map_remove. cbn [List.filter fst]. destruct (negb (bv_eqb b a)); cbn [length];
    fold (map_remove l a); specialize (IH a); lia.
Qed.

(* [comment removed for export] *)
Lemma live_bytes_iv_subtract_le : forall (a sz : word) (lo hi : Z),
  lo <= hi ->
  live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  intros a sz lo hi Hlh. pose proof (u64_range a). pose proof (u64_range sz).
  unfold iv_subtract.
  destruct (bv_unsigned a <? lo) eqn:E1; destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2;
    cbn [app live_bytes];
    first [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1]; first [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2];
    rewrite ?u64_lit by lia; lia.
Qed.

Lemma live_bytes_maps_subtract_le : forall l (lo hi : Z),
  lo <= hi -> live_bytes (maps_subtract l lo hi) <= live_bytes l.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hlh; [cbn; lia|].
  cbn [maps_subtract live_bytes]. rewrite live_bytes_app.
  pose proof (live_bytes_iv_subtract_le a sz lo hi Hlh). specialize (IH lo hi Hlh). lia.
Qed.

Lemma maps_subtract_all_nil : forall maps, maps_subtract_all maps [] = maps.
Proof. reflexivity. Qed.

Lemma maps_subtract_all_cons : forall maps (a n : word) cuts,
  maps_subtract_all maps ((a, n) :: cuts)
  = maps_subtract_all (maps_subtract maps (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) cuts.
Proof. reflexivity. Qed.

Lemma live_bytes_maps_subtract_all_le : forall cuts maps,
  live_bytes (maps_subtract_all maps cuts) <= live_bytes maps.
Proof.
  induction cuts as [|[a n] cuts IH]; intros maps; [cbn; lia|].
  rewrite maps_subtract_all_cons. etransitivity; [apply IH|].
  apply live_bytes_maps_subtract_le. pose proof (u64_range n). lia.
Qed.

(* [comment removed for export] *)
Lemma vm_backed_bytes_le_live : forall h, vm_backed_bytes h <= vm_live_bytes h.
Proof. intros h. unfold vm_backed_bytes, vm_backed_maps, vm_live_bytes. apply live_bytes_maps_subtract_all_le. Qed.

(* [comment removed for export] *)
Lemma vm_backing_used_le_live : forall m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_backing_used m <= vm_live_bytes (m_vmmaps m).
Proof.
  intros m Hl Hm. rewrite (vm_backing_used_simple m Hl Hm). apply vm_backed_bytes_le_live.
Qed.

Lemma grant_budget_intro : forall m n,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_live_bytes (m_vmmaps m) + n <= vm_limit (m_vmmaps m) ->
  vm_backing_used m + n <= vm_limit (m_vmmaps m).
Proof. intros m n Hl Hm H. pose proof (vm_backing_used_le_live m Hl Hm). lia. Qed.

(* [comment removed for export] *)
Lemma mprotect_budget_ok_intro : forall m addr n,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_live_bytes (m_vmmaps m) <= vm_limit (m_vmmaps m) ->
  mprotect_budget_ok m addr n = true.
Proof.
  intros m addr n Hl Hm Hlive. unfold mprotect_budget_ok, vm_backing_within_limit.
  rewrite mprotect_model_next_eq. apply Z.leb_le.
  etransitivity; [apply vm_backing_used_le_live; [unfold mprotect_model; rewrite with_vmmaps_lazy'; exact Hl | exact Hm]|].
  unfold mprotect_model. rewrite with_vmmaps_vm. cbn [vm_live_bytes vm_maps vm_limit]. exact Hlive.
Qed.

(* [comment removed for export] *)
Lemma file_read_length_eq : forall data (off count : word),
  length (file_read data off count) = Nat.min (word_to_nat count) (length data - word_to_nat off).
Proof. intros. rewrite length_file_read. reflexivity. Qed.

Lemma file_read_length_le : forall data (off count : word),
  (length (file_read data off count) <= word_to_nat count)%nat
  /\ (length (file_read data off count) <= length data - word_to_nat off)%nat.
Proof. intros data off count. rewrite file_read_length_eq. split; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cand (base N : Z) (j : nat) : Z := base + Z.of_nat j * (2 * N).

Definition zconflict (a n : Z) (p : word * word) : Prop :=
  a < bv_unsigned (fst p) + bv_unsigned (snd p) /\ bv_unsigned (fst p) < a + n.

Definition zconflictb (a n : Z) (p : word * word) : bool :=
  (a <? bv_unsigned (fst p) + bv_unsigned (snd p)) && (bv_unsigned (fst p) <? a + n).

Lemma zconflictb_spec : forall a n p, zconflictb a n p = true <-> zconflict a n p.
Proof.
  intros a n p. unfold zconflictb, zconflict. rewrite andb_true_iff, !Z.ltb_lt. tauto.
Qed.

Lemma cand_spacing : forall base N j k, 0 <= N -> (j < k)%nat -> cand base N j + 2 * N <= cand base N k.
Proof. intros base N j k HN H. unfold cand. nia. Qed.

(* [comment removed for export] *)
Lemma conflict_unique : forall base N n p j k,
  0 <= n <= N -> bv_unsigned (snd p) <= N ->
  zconflict (cand base N j) n p -> zconflict (cand base N k) n p -> j = k.
Proof.
  intros base N n p j k Hn Hs [A1 A2] [B1 B2].
  destruct (Nat.lt_trichotomy j k) as [Hlt | [Heq | Hgt]]; [| exact Heq |].
  - pose proof (cand_spacing base N j k ltac:(lia) Hlt). lia.
  - pose proof (cand_spacing base N k j ltac:(lia) Hgt). lia.
Qed.

(* [comment removed for export] *)
Lemma filter_keep_all_but_one : forall (P : nat -> bool) (js : list nat),
  List.NoDup js ->
  (forall j k, In j js -> In k js -> P j = true -> P k = true -> j = k) ->
  (length js <= S (length (List.filter (fun j => negb (P j)) js)))%nat.
Proof.
  intros P js Hnd Huniq. induction js as [|j js IH]; [cbn; lia|].
  inversion Hnd as [|x l Hnotin Hnd']; subst.
  cbn [List.filter List.length]. destruct (P j) eqn:Pj; cbn [negb].
  - (* [comment removed for export] *)
    assert (Hall : forall k, In k js -> P k = false).
    { intros k Hk. destruct (P k) eqn:Pk; [|reflexivity].
      exfalso. assert (j = k) by (apply Huniq; [left; reflexivity | right; exact Hk | exact Pj | exact Pk]).
      subst k. exact (Hnotin Hk). }
    assert (Hid : List.filter (fun j0 => negb (P j0)) js = js).
    { clear -Hall. induction js as [|k js IH]; [reflexivity|].
      cbn [List.filter]. rewrite (Hall k (or_introl eq_refl)). cbn [negb]. f_equal. apply IH.
      intros k' Hk'. apply Hall. right. exact Hk'. }
    rewrite Hid. lia.
  - cbn [List.length].
    assert (IH' : (length js <= S (length (List.filter (fun j0 : nat => negb (P j0)) js)))%nat).
    { apply IH; [exact Hnd'|]. intros a b Ha Hb Pa Pb. apply Huniq; [right | right | |]; assumption. }
    lia.
Qed.

Lemma pick_candidate : forall (base N n : Z) (l : list (word * word)) (js : list nat),
  0 <= n <= N ->
  Forall (fun p => bv_unsigned (snd p) <= N) l ->
  List.NoDup js -> (length l < length js)%nat ->
  exists j, In j js /\ forall p, In p l -> ~ zconflict (cand base N j) n p.
Proof.
  intros base N n l. induction l as [|p l IH]; intros js Hn Hsz Hnd Hlen.
  - destruct js as [|j js]; [cbn in Hlen; lia|]. exists j. split; [left; reflexivity | intros q []].
  - inversion Hsz as [|p' l' Hp Hl]; subst.
    set (js' := List.filter (fun j => negb (zconflictb (cand base N j) n p)) js).
    assert (Hnd' : List.NoDup js') by (apply List.NoDup_filter; exact Hnd).
    assert (Hlen' : (length js <= S (length js'))%nat).
    { apply filter_keep_all_but_one; [exact Hnd|].
      intros j k _ _ Pj Pk. apply zconflictb_spec in Pj. apply zconflictb_spec in Pk.
      eapply (conflict_unique base N n p); eassumption. }
    destruct (IH js' Hn Hl Hnd' ltac:(cbn in Hlen; lia)) as (j & Hj & Hfree).
    exists j. unfold js' in Hj. apply filter_In in Hj as [Hj Hnp]. split; [exact Hj|].
    intros q [<- | Hq].
    + intros Hc. apply zconflictb_spec in Hc. rewrite Hc in Hnp. discriminate.
    + apply Hfree. exact Hq.
Qed.

Lemma region_free_of_noconflict : forall l (a n : Z),
  0 <= a -> 0 <= n -> a + n < 2 ^ 64 ->
  (forall p, In p l -> ~ zconflict a n p) ->
  region_free l (Z_to_bv 64 a) (Z_to_bv 64 n) = true.
Proof.
  induction l as [|[b s] l IH]; intros a n Ha Hn Hnw Hno; [reflexivity|].
  cbn [region_free]. rewrite IH; [| lia | lia | lia | intros p Hp; apply Hno; right; exact Hp].
  rewrite andb_true_r. apply negb_true_iff. unfold iv_overlap.
  rewrite !u64_lit by lia.
  specialize (Hno (b, s) (or_introl eq_refl)). unfold zconflict in Hno. cbn [fst snd] in Hno.
  apply andb_false_iff. destruct (Z_lt_le_dec a (bv_unsigned b + bv_unsigned s)).
  - right. apply Z.ltb_ge. lia.
  - left. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Lemma grant_exists_na_gen : forall hint (m : Model) (N n C base : Z),
  0 < N -> N mod page_size = 0 -> 0 <= n <= N ->
  Forall (fun p => bv_unsigned (snd p) <= N) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= C ->
  base mod page_size = 0 -> 0 < base ->
  base + C * (2 * N) + N <= alloc_top (m_vmmaps m) ->
  exists a, grant_ok_na hint m a n = true.
Proof.
  intros hint m N n C base HN HNal Hn Hsz Hcnt Hbal Hb0 Hband.
  set (l := vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) in *.
  destruct (pick_candidate base N n l (seq 0 (S (length l))) Hn Hsz (List.seq_NoDup _ _) ltac:(rewrite length_seq; lia))
    as (j & Hj & Hfree).
  apply in_seq in Hj.
  exists (Z_to_bv 64 (cand base N j)).
  pose proof (alloc_top_lt (m_vmmaps m)) as Htl. unfold two_pow_64 in Htl.
  assert (Hc : base <= cand base N j <= base + C * (2 * N)) by (unfold cand; nia).
  assert (E1 : cand base N j mod page_size = 0).
  { unfold cand. unfold page_size in *. rewrite Z.add_mod, Z.mul_assoc, Z.mul_mod, HNal, Hbal by lia.
    rewrite Z.mul_0_r. reflexivity. }
  generalize dependent (cand base N j). intros c Hfree Hc E1.
  assert (G : 0 <= c < 2 ^ 64 /\ (0 <= n < 2 ^ 64 /\ (0 < c /\ (c + n <= alloc_top (m_vmmaps m) /\ c + n < 2 ^ 64)))).
  { clear Hfree Hsz E1 HNal Hbal. generalize dependent (alloc_top (m_vmmaps m)). intros top Hband Htl. nia. }
  destruct G as (G0 & G1 & G2 & G3 & G4).
  unfold grant_ok_na. rewrite (u64_lit c G0).
  rewrite (proj2 (Z.eqb_eq _ _) E1), (proj2 (Z.ltb_lt 0 _) G2), (proj2 (Z.leb_le _ _) G3).
  fold l. rewrite (region_free_of_noconflict l c n (proj1 G0) (proj1 Hn) G4 Hfree).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma grant_exists_gen : forall hint (m : Model) (N n C base : Z),
  0 < N -> N mod page_size = 0 -> 0 <= n <= N ->
  Forall (fun p => bv_unsigned (snd p) <= N) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= C ->
  base mod page_size = 0 -> 0 < base ->
  base + C * (2 * N) + N <= alloc_top (m_vmmaps m) ->
  vm_backing_used m + n <= vm_limit (m_vmmaps m) ->
  exists a, grant_ok hint m a n = true.
Proof.
  intros hint m N n C base HN HNal Hn Hsz Hcnt Hbal Hb0 Hband Hlive.
  destruct (grant_exists_na_gen hint m N n C base HN HNal Hn Hsz Hcnt Hbal Hb0 Hband) as [a Ha].
  exists a. unfold grant_ok. unfold grant_ok_na in Ha. rewrite Ha.
  rewrite (proj2 (Z.leb_le _ _) Hlive). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma alloc_top_ge_window : forall h,
  sp_window_lo <= bv_unsigned (vm_init_sp h) -> 0x7fff7f800000 <= alloc_top h.
Proof. intros h H. unfold alloc_top. rewrite stack_max_size_val. unfold sp_window_lo in H. lia. Qed.

Lemma grant_exists : forall hint (m : Model) (n : Z),
  sp_window_lo <= bv_unsigned (vm_init_sp (m_vmmaps m)) ->
  0 <= n <= 2 ^ 30 ->
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 30) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= 40000 ->
  vm_backing_used m + n <= vm_limit (m_vmmaps m) ->
  exists a, grant_ok hint m a n = true.
Proof.
  intros hint m n Hsp Hn Hsz Hcnt Hlive.
  pose proof (alloc_top_ge_window _ Hsp).
  apply (grant_exists_gen hint m (2 ^ 30) n 40000 (2 ^ 32)); try assumption; try lia; reflexivity.
Qed.

Lemma grant_exists_na : forall hint (m : Model) (n : Z),
  sp_window_lo <= bv_unsigned (vm_init_sp (m_vmmaps m)) ->
  0 <= n <= 2 ^ 30 ->
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 30) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= 40000 ->
  exists a, grant_ok_na hint m a n = true.
Proof.
  intros hint m n Hsp Hn Hsz Hcnt.
  pose proof (alloc_top_ge_window _ Hsp).
  apply (grant_exists_na_gen hint m (2 ^ 30) n 40000 (2 ^ 32)); try assumption; try lia; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma grant_exists_big : forall hint (m : Model) (n : Z),
  sp_window_lo <= bv_unsigned (vm_init_sp (m_vmmaps m)) ->
  0 <= n <= 2 ^ 35 ->
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 35) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= 1000 ->
  vm_backing_used m + n <= vm_limit (m_vmmaps m) ->
  exists a, grant_ok hint m a n = true.
Proof.
  intros hint m n Hsp Hn Hsz Hcnt Hlive.
  pose proof (alloc_top_ge_window _ Hsp).
  apply (grant_exists_gen hint m (2 ^ 35) n 1000 (2 ^ 32)); try assumption; try lia; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma grant_ok_over_budget : forall hint (m : Model) (a : word) (n : Z),
  vm_limit (m_vmmaps m) < vm_backing_used m + n ->
  grant_ok hint m a n = false.
Proof.
  intros hint m a n H. unfold grant_ok.
  destruct (bv_unsigned a mod page_size =? 0); [|reflexivity].
  destruct (0 <? bv_unsigned a); [|reflexivity].
  destruct (bv_unsigned a + n <=? alloc_top (m_vmmaps m)); [|reflexivity].
  destruct (region_free _ a (Z_to_bv 64 n)); [|reflexivity].
  rewrite (proj2 (Z.leb_gt _ _) H). reflexivity.
Qed.

End FPX_2.
