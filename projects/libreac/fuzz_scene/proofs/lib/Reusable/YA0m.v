(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YA0m.v (donor image sha256 7093581aab04), with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK16 YK0n YK11 YK0i YK0h YK14 YK0v YK0p YK02 YK15 YK18.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0n YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.R Require Import Cfg.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Section g.
Context {fx : FPState}.
Section h.
Variable segs : list Segment.
Variable H : word -> bool.
Variable A : list (Z * Z).
Definition ranges_unlazy (lazy : list (word * word)) (accs : list (word * nat)) : Prop :=
forall a n k, In (a, n) accs -> (k < n)%nat ->
page_in_ranges (page_base_of (bv_unsigned a + Z.of_nat k)%Z) lazy = false.
Lemma eager_used_vmmaps : forall m m',
m_vmmaps m' = m_vmmaps m -> m_vm_lazy m' = m_vm_lazy m -> eager_used m' = eager_used m.
Proof. intros m m' H1 H2. unfold eager_used. rewrite H1, H2. reflexivity. Qed.
Lemma AI_ledgers : forall md md',
AI segs H A md ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> m_vm_materialized md' = m_vm_materialized md ->
m_halted md' = None -> AI segs H A md'.
Proof.
intros md md' HAI Hv Hl Hm Hh. apply (AI_transport segs H A md md' HAI Hm Hl Hh).
rewrite (eager_used_vmmaps md md' Hv Hl), Hv. exact (minv_budget _ _ (AI_MInv segs H A md HAI)).
Qed.
Lemma node_chk_lazy : forall ms model x8 (I : Type) (i0 : I)
(ef : I -> SyscallEffect) (md : I -> Model) (ev : I -> list event),
AI segs H A model ->
ms_svc_pending ms = Some x8 ->
(forall i, check_syscall (sys_input segs ms x8) (ef i) model = CheckOk (md i) (ev i)) ->
(forall i, m_halted (md i) = None) ->
(forall i, m_vmmaps (md i) = m_vmmaps model /\ m_vm_lazy (md i) = m_vm_lazy model
/\ m_vm_materialized (md i) = m_vm_materialized model) ->
(forall i, ranges_avoid H (syscall_effect_accesses (ef i))) ->
(forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
exists i, eff = ef i /\ m' = md i /\ evs = ev i) ->
(forall i, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (ef i)) ->
node_ok segs (mkCfg ms model) I ev
(fun i => mkCfg (advance_past_svc (apply_effect ms (ef i)))
(materialized_succ (md i) (syscall_effect_accesses (ef i))))
/\ (forall i, AI segs H A (materialized_succ (md i) (syscall_effect_accesses (ef i)))
/\ same_but_materialized (md i) (materialized_succ (md i) (syscall_effect_accesses (ef i)))).
Proof.
intros ms model x8 I i0 ef md ev HAI Hsvc Hok Hhl Hled Hav Hinv Hns.
assert (HAIi : forall i, AI segs H A (md i)).
{ intros i. destruct (Hled i) as (Hv & Hl & Hm). exact (AI_ledgers model (md i) HAI Hv Hl Hm (Hhl i)). }
destruct HAI as (HH & Hwf & Hcov & Hinv0 & Hh).
destruct (node_syscall_restricted segs H A ms model x8 I ef md ev Hwf Hh Hsvc) as [Hsucc Hnode].
- intros i. apply check_syscall_ok_iff. apply Hok.
- intros r Hr. destruct r as [eff m' evs|].
+ apply check_syscall_ok_iff in Hr. destruct (Hinv eff m' evs Hr) as (i & -> & -> & ->). exists i. reflexivity.
+ exfalso. apply (check_syscall_complete_unmodeled _ _ (ef i0)) in Hr. rewrite (Hok i0) in Hr. discriminate Hr.
- exact Hhl.
- exact Hns.
- intros i. destruct (HAIi i) as (_ & _ & Hc & _). exact Hc.
- intros i. exact (AI_MInv segs H A (md i) (HAIi i)).
- exact Hav.
- split; [exact Hnode|]. intros i. destruct (Hsucc i) as [Hm Hs]. split; [|exact Hs].
exact (AI_same segs H A (md i) _ (HAIi i) Hs Hm).
Qed.
Lemma filter_all_false {X} : forall (f : X -> bool) l, (forall x, In x l -> f x = false) -> List.filter f l = [].
Proof.
intros f l. induction l as [|x l IH]; intros Hf; [reflexivity|]. cbn [List.filter].
rewrite (Hf x (or_introl eq_refl)). apply IH. intros y Hy. apply Hf. right. exact Hy.
Qed.
Lemma materialize_unlazy : forall m accs,
ranges_unlazy (m_vm_lazy m) accs -> materialize_model_accesses m accs = Some m.
Proof.
intros m accs Hu. unfold materialize_model_accesses, materialize_accesses.
replace (newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) accs) with (@nil word).
- cbn. rewrite with_vm_backing_id. reflexivity.
- symmetry. unfold newly_materialized_pages. apply filter_all_false. intros p Hp.
destruct (accesses_pages_in accs [] p Hp) as [[] | (a & n & k & Hin & Hk & ->)].
rewrite (Hu a n k Hin Hk). reflexivity.
Qed.
Lemma materialized_succ_unlazy : forall m accs, ranges_unlazy (m_vm_lazy m) accs -> materialized_succ m accs = m.
Proof. intros m accs Hu. unfold materialized_succ. rewrite (materialize_unlazy m accs Hu). reflexivity. Qed.
Lemma materialized_succ_nil : forall m, materialized_succ m [] = m.
Proof. intros m. apply materialized_succ_unlazy. intros a n k []. Qed.
Lemma node_ok_ext : forall c (I : Type) (evs : I -> list event) (nx nx' : I -> config),
node_ok segs c I evs nx -> (forall i, nx i = nx' i) -> node_ok segs c I evs nx'.
Proof.
intros c I evs nx nx' [H1 H2] He. split.
- intros i. rewrite <- He. apply H1.
- intros e st Hs. destruct (H2 e st Hs) as (i & -> & ->). exists i. rewrite He. auto.
Qed.
Lemma ledgers_with_fds : forall f m,
m_vmmaps (with_fds f m) = m_vmmaps m /\ m_vm_lazy (with_fds f m) = m_vm_lazy m
/\ m_vm_materialized (with_fds f m) = m_vm_materialized m.
Proof. intros f m. repeat split; reflexivity. Qed.
Lemma ledgers_same : forall m : Model,
m_vmmaps m = m_vmmaps m /\ m_vm_lazy m = m_vm_lazy m /\ m_vm_materialized m = m_vm_materialized m.
Proof. intros m. repeat split; reflexivity. Qed.
Lemma node_chk1_lazy : forall regs pc mem rom model eff m' evs,
AI segs H A model ->
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model = CheckOk m' evs ->
m_halted m' = None ->
m_vmmaps m' = m_vmmaps model /\ m_vm_lazy m' = m_vm_lazy model /\ m_vm_materialized m' = m_vm_materialized model ->
ranges_avoid H (syscall_effect_accesses eff) ->
(forall eff2 m2 evs2,
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff2 model = CheckOk m2 evs2 ->
eff2 = eff /\ m2 = m' /\ evs2 = evs) ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) unit (fun _ => evs)
(fun _ => mkCfg (mkst (regupd regs 10 (eff_ret eff)) (v_addi pc 4) (effmem mem eff) rom)
(materialized_succ m' (syscall_effect_accesses eff)))
/\ AI segs H A (materialized_succ m' (syscall_effect_accesses eff))
/\ same_but_materialized m' (materialized_succ m' (syscall_effect_accesses eff)).
Proof.
intros regs pc mem rom model eff m' evs HAI Hok Hh' Hled Hav Huniq.
destruct (node_chk_lazy (pend_at regs pc mem rom) model (getr regs 17) unit tt
(fun _ => eff) (fun _ => m') (fun _ => evs) HAI eq_refl
(fun _ => Hok) (fun _ => Hh') (fun _ => Hled) (fun _ => Hav)) as [Hn Hs].
- intros eff2 m2 evs2 H2. exists tt. apply Huniq. exact H2.
- intros []. apply nonspurious_of_unique. intros eff2 m2 evs2 Hs2.
apply check_syscall_ok_iff in Hs2. apply Huniq in Hs2 as (-> & _ & _). reflexivity.
- split; [|exact (Hs tt)]. eapply node_ok_ext; [exact Hn|]. intros []. cbn beta. rewrite adv_pend. reflexivity.
Qed.
Lemma node_ret_only_lazy : forall regs pc mem rom model r m' evs,
AI segs H A model ->
(forall eff, check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_ret_only eff r m' evs) ->
m_halted m' = None ->
m_vmmaps m' = m_vmmaps model /\ m_vm_lazy m' = m_vm_lazy model /\ m_vm_materialized m' = m_vm_materialized model ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) unit (fun _ => evs)
(fun _ => mkCfg (mkst (regupd regs 10 r) (v_addi pc 4) mem rom) m')
/\ AI segs H A m'.
Proof.
intros regs pc mem rom model r m' evs HAI Hchk Hh' Hled.
destruct (node_chk1_lazy regs pc mem rom model (mkEffect r [] []) m' evs HAI) as (Hn & HA & _).
- rewrite Hchk. apply check_ret_only_self.
- exact Hh'.
- exact Hled.
- intros a n [].
- intros eff2 m2 evs2 H2. rewrite Hchk in H2. apply check_ret_only_uniq. exact H2.
- cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app eff_ret] in Hn, HA.
rewrite materialized_succ_nil, effmem_ret_only in Hn. rewrite materialized_succ_nil in HA. exact (conj Hn HA).
Qed.
Lemma node_ret_only_copyins_lazy : forall regs pc mem rom model reads r m' evs,
AI segs H A model ->
(forall eff, check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_ret_only_copyins reads eff r m' evs) ->
m_halted m' = None ->
m_vmmaps m' = m_vmmaps model /\ m_vm_lazy m' = m_vm_lazy model /\ m_vm_materialized m' = m_vm_materialized model ->
ranges_avoid H reads ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) unit (fun _ => evs)
(fun _ => mkCfg (mkst (regupd regs 10 r) (v_addi pc 4) mem rom) (materialized_succ m' reads))
/\ AI segs H A (materialized_succ m' reads) /\ same_but_materialized m' (materialized_succ m' reads).
Proof.
intros regs pc mem rom model reads r m' evs HAI Hchk Hh' Hled Hav.
assert (Hacc : syscall_effect_accesses (with_copyins reads (mkEffect r [] [])) = reads).
{ cbn. apply app_nil_r. }
destruct (node_chk1_lazy regs pc mem rom model (with_copyins reads (mkEffect r [] [])) m' evs HAI) as (Hn & HA & Hs).
- rewrite Hchk. apply check_ret_only_copyins_refl.
- exact Hh'.
- exact Hled.
- rewrite Hacc. exact Hav.
- intros eff2 m2 evs2 H2. rewrite Hchk in H2. apply check_ret_only_copyins_ok_iff. exact H2.
- rewrite Hacc in Hn, HA, Hs. cbn [eff_ret with_copyins] in Hn. rewrite effmem_copyins_ret_only in Hn.
exact (conj Hn (conj HA Hs)).
Qed.
Lemma node_close_lazy : forall regs pc mem rom model fd e,
AI segs H A model ->
bv_unsigned (getr regs 17) = 57%Z ->
getr regs 10 = fd -> fd32 fd = fd ->
fd_lookup (m_fds model) fd = Some e ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) unit (fun _ => [])
(fun _ => mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom)
(with_fds (fd_remove (m_fds model) fd) model))
/\ AI segs H A (with_fds (fd_remove (m_fds model) fd) model).
Proof.
intros regs pc mem rom model fd e HAI Hno Hfd H32 Hlk.
apply (node_ret_only_lazy regs pc mem rom model (Z_to_bv 64 0) _ [] HAI).
- intro eff. rewrite chk57 by exact Hno. rewrite Hfd, H32. unfold check_close. rewrite Hlk. reflexivity.
- exact (AI_halted segs H A model HAI).
- apply ledgers_with_fds.
Qed.
Lemma node_close_badf_lazy : forall regs pc mem rom model fd,
AI segs H A model ->
bv_unsigned (getr regs 17) = 57%Z ->
getr regs 10 = fd -> fd32 fd = fd ->
fd_lookup (m_fds model) fd = None ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) unit (fun _ => [])
(fun _ => mkCfg (mkst (regupd regs 10 (errno_ret EBADF)) (v_addi pc 4) mem rom) model)
/\ AI segs H A model.
Proof.
intros regs pc mem rom model fd HAI Hno Hfd H32 Hlk.
apply (node_ret_only_lazy regs pc mem rom model (errno_ret EBADF) model [] HAI).
- intro eff. rewrite chk57 by exact Hno. rewrite Hfd, H32. unfold check_close. rewrite Hlk. reflexivity.
- exact (AI_halted segs H A model HAI).
- apply ledgers_same.
Qed.
Lemma node_ioctl_winsz_lazy : forall regs pc mem rom model fd e,
AI segs H A model ->
bv_unsigned (getr regs 17) = 29%Z ->
getr regs 10 = fd -> fd32 fd = fd ->
fd_lookup (m_fds model) fd = Some e ->
(forall rd wr : bool, e <> FdUrandom) ->
cmd32 (getr regs 11) = TIOCGWINSZ ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) unit (fun _ => [])
(fun _ => mkCfg (mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi pc 4) mem rom) model)
/\ AI segs H A model.
Proof.
intros regs pc mem rom model fd e HAI Hno Hfd H32 Hlk Hnd Hcmd.
apply (node_ret_only_lazy regs pc mem rom model (errno_ret ENOTTY) model [] HAI).
- intro eff. rewrite chk29 by exact Hno. rewrite Hfd, H32, Hcmd. unfold check_ioctl.
rewrite Hlk. change (tty_only_request TIOCGWINSZ) with true. destruct e; try reflexivity. exfalso; eapply (Hnd true true); reflexivity.
- exact (AI_halted segs H A model HAI).
- apply ledgers_same.
Qed.
#[local] Notation OCI regs pc mem rom := (open_copyins (pend_at regs pc mem rom)).
Lemma node_openat_toolong_lazy : forall regs pc mem rom model,
AI segs H A model ->
bv_unsigned (getr regs 17) = 56%Z ->
modeled_open_flags (getr regs 12) = true ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrTooLong ->
ranges_avoid H (OCI regs pc mem rom) ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) unit (fun _ => [])
(fun _ => mkCfg (mkst (regupd regs 10 (errno_ret ENAMETOOLONG)) (v_addi pc 4) mem rom)
(materialized_succ model (OCI regs pc mem rom)))
/\ AI segs H A (materialized_succ model (OCI regs pc mem rom))
/\ same_but_materialized model (materialized_succ model (OCI regs pc mem rom)).
Proof.
intros regs pc mem rom model HAI Hno Hfl Hp Hav.
apply (node_ret_only_copyins_lazy regs pc mem rom model _ (errno_ret ENAMETOOLONG) model [] HAI).
- intro eff. apply (openat_toolong_check segs (pend_at regs pc mem rom) (getr regs 17) model Hno).
+ rewrite pend_gpr2. exact Hfl.
+ rewrite pend_gpr1. exact Hp.
- exact (AI_halted segs H A model HAI).
- apply ledgers_same.
- exact Hav.
Qed.
Lemma node_openat_fault_lazy : forall regs pc mem rom model,
AI segs H A model ->
bv_unsigned (getr regs 17) = 56%Z ->
modeled_open_flags (getr regs 12) = true ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrFault ->
ranges_avoid H (OCI regs pc mem rom) ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) unit (fun _ => [])
(fun _ => mkCfg (mkst (regupd regs 10 (errno_ret EFAULT)) (v_addi pc 4) mem rom)
(materialized_succ model (OCI regs pc mem rom)))
/\ AI segs H A (materialized_succ model (OCI regs pc mem rom))
/\ same_but_materialized model (materialized_succ model (OCI regs pc mem rom)).
Proof.
intros regs pc mem rom model HAI Hno Hfl Hp Hav.
apply (node_ret_only_copyins_lazy regs pc mem rom model _ (errno_ret EFAULT) model [] HAI).
- intro eff. rewrite chk56 by exact Hno. unfold check_openat.
rewrite Hfl. cbn [negb]. unfold Prelude.check_copyins_after, Open.check_openat_body.
rewrite si_mem, Hp. unfold check_ret_only_copyins, check_copyins, open_copyins.
rewrite pend_gpr1. cbn [ms_read_byte pend_at ms_mem ms_rom].
destruct (check_ret_only (clear_copyins eff) (errno_ret EFAULT) model []) eqn:Hq;
[reflexivity| |reflexivity].
destruct (access_ranges_eqb _ _); reflexivity.
- exact (AI_halted segs H A model HAI).
- apply ledgers_same.
- exact Hav.
Qed.
Lemma node_openat_empty_lazy : forall regs pc mem rom model,
AI segs H A model ->
bv_unsigned (getr regs 17) = 56%Z ->
modeled_open_flags (getr regs 12) = true ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk [] ->
ranges_avoid H (OCI regs pc mem rom) ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) unit (fun _ => [])
(fun _ => mkCfg (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4) mem rom)
(materialized_succ model (OCI regs pc mem rom)))
/\ AI segs H A (materialized_succ model (OCI regs pc mem rom))
/\ same_but_materialized model (materialized_succ model (OCI regs pc mem rom)).
Proof.
intros regs pc mem rom model HAI Hno Hfl Hp Hav.
apply (node_ret_only_copyins_lazy regs pc mem rom model _ (errno_ret ENOENT) model [] HAI).
- intro eff. rewrite chk56 by exact Hno. unfold check_openat.
rewrite Hfl. cbn [negb]. unfold Prelude.check_copyins_after, Open.check_openat_body.
rewrite si_mem, Hp. change (path_eqb [] []) with true. cbv beta iota.
unfold check_ret_only_copyins, check_copyins, open_copyins.
rewrite pend_gpr1. cbn [ms_read_byte pend_at ms_mem ms_rom].
destruct (check_ret_only (clear_copyins eff) (errno_ret ENOENT) model []) eqn:Hq;
[reflexivity| |reflexivity].
destruct (access_ranges_eqb _ _); reflexivity.
- exact (AI_halted segs H A model HAI).
- apply ledgers_same.
- exact Hav.
Qed.
Lemma node_openat_absent_lazy : forall regs pc mem rom model p,
AI segs H A model ->
bv_unsigned (getr regs 17) = 56%Z ->
getr regs 10 = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
p <> [] -> openat_plain_name p = true ->
fs_lookup (m_fs model) p = None ->
ranges_avoid H (OCI regs pc mem rom) ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) unit (fun _ => [])
(fun _ => mkCfg (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4) mem rom)
(materialized_succ model (OCI regs pc mem rom)))
/\ AI segs H A (materialized_succ model (OCI regs pc mem rom))
/\ same_but_materialized model (materialized_succ model (OCI regs pc mem rom)).
Proof.
intros regs pc mem rom model p HAI Hno Hdir Hfl Hp Hne Hnd Hfs Hav.
pose proof (openat_plain_name_noslash _ Hnd) as Hsl.
apply openat_plain_name_nodirref in Hnd.
apply (node_ret_only_copyins_lazy regs pc mem rom model _ (errno_ret ENOENT) model [] HAI).
- intro eff. rewrite chk56 by exact Hno. unfold check_openat.
rewrite (modeled_open_flags_rd _ Hfl). cbn [negb].
unfold Prelude.check_copyins_after, Open.check_openat_body. rewrite si_mem, Hp.
rewrite (path_eqb_neq _ _ Hne). rewrite Hdir, fd32_AT_FDCWD, bv_eqb_refl. cbn [negb].
unfold Open.check_openat_resolved. rewrite Hsl.
rewrite Hfl. cbn [Z.eqb]. unfold Open.check_openat_read.
rewrite Hnd, Hfs.
unfold check_ret_only_copyins, check_copyins, open_copyins.
rewrite pend_gpr1. cbn [ms_read_byte pend_at ms_mem ms_rom].
destruct (check_ret_only (clear_copyins eff) (errno_ret ENOENT) model []) eqn:Hq;
[reflexivity| |reflexivity].
destruct (access_ranges_eqb _ _); reflexivity.
- exact (AI_halted segs H A model HAI).
- apply ledgers_same.
- exact Hav.
Qed.
Definition open_ix : Type := ({e : Z | In e openat_errnos} + unit)%type.
Definition open_ret (fds : list (word * FdEntry)) (i : open_ix) : word :=
match i with inl e => errno_ret (proj1_sig e) | inr _ => alloc_fd fds end.
Definition open_md (model : Model) (mk : word -> Model) (i : open_ix) : Model :=
match i with inl _ => model | inr _ => mk (alloc_fd (m_fds model)) end.
Lemma node_open_core_lazy : forall regs pc mem rom model reads (mk : word -> Model),
AI segs H A model ->
(forall eff, check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_open_result_copyins reads eff model mk) ->
(forall fd, m_halted (mk fd) = None) ->
(forall fd, m_vmmaps (mk fd) = m_vmmaps model /\ m_vm_lazy (mk fd) = m_vm_lazy model
/\ m_vm_materialized (mk fd) = m_vm_materialized model) ->
fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
ranges_avoid H reads ->
alloc_no_b (bv_unsigned (getr regs 17)) = false ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) open_ix (fun _ => [])
(fun i => mkCfg (mkst (regupd regs 10 (open_ret (m_fds model) i)) (v_addi pc 4) mem rom)
(materialized_succ (open_md model mk i) reads))
/\ (forall i, AI segs H A (materialized_succ (open_md model mk i) reads)
/\ same_but_materialized (open_md model mk i) (materialized_succ (open_md model mk i) reads)).
Proof.
intros regs pc mem rom model reads mk HAI Hchk Hmk Hmkl Hfree Hav Hna.
pose (ef := fun i : open_ix => with_copyins reads (mkEffect (open_ret (m_fds model) i) [] [])).
assert (Hacc : forall i, syscall_effect_accesses (ef i) = reads) by (intros i; cbn; apply app_nil_r).
destruct (node_chk_lazy (pend_at regs pc mem rom) model (getr regs 17) open_ix (inr tt)
ef (open_md model mk) (fun _ => []) HAI eq_refl) as [Hn Hs].
- intros [[e He] | []]; unfold ef, open_md, open_ret; cbn [proj1_sig]; rewrite Hchk; apply check_open_result_copyins_ok_iff.
+ left. exists e. auto.
+ right. exists (alloc_fd (m_fds model)). auto.
- intros [[e He] | []]; unfold open_md; [exact (AI_halted segs H A model HAI) | apply Hmk].
- intros [[e He] | []]; unfold open_md; [apply ledgers_same | apply Hmkl].
- intros i. rewrite Hacc. exact Hav.
- intros eff m' evs Hk. rewrite Hchk in Hk. apply check_open_result_copyins_ok_iff in Hk.
destruct Hk as [(e & He & -> & -> & ->) | (fd & _ & -> & -> & -> & ->)].
+ exists (inl (exist _ e He)). unfold ef, open_md, open_ret; cbn [proj1_sig]. auto.
+ exists (inr tt). unfold ef, open_md, open_ret. auto.
- exact (fun _ => acfg_nonspurious_no _ _ _ _ _ _ eq_refl Hna).
- split.
+ eapply node_ok_ext; [exact Hn|]. intros i. cbn beta. rewrite adv_pend, Hacc.
unfold ef. cbn [eff_ret with_copyins]. rewrite effmem_copyins_ret_only. reflexivity.
+ intros i. rewrite <- (Hacc i). exact (Hs i).
Qed.
Lemma node_openat_file_lazy : forall regs pc mem rom model p d,
AI segs H A model ->
bv_unsigned (getr regs 17) = 56%Z ->
getr regs 10 = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
p <> [] -> openat_plain_name p = true ->
fs_lookup (m_fs model) p = Some d ->
fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
ranges_avoid H (OCI regs pc mem rom) ->
let mk := fun fd => with_fds (fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model in
node_ok segs (mkCfg (pend_at regs pc mem rom) model) open_ix (fun _ => [])
(fun i => mkCfg (mkst (regupd regs 10 (open_ret (m_fds model) i)) (v_addi pc 4) mem rom)
(materialized_succ (open_md model mk i) (OCI regs pc mem rom)))
/\ (forall i, AI segs H A (materialized_succ (open_md model mk i) (OCI regs pc mem rom))
/\ same_but_materialized (open_md model mk i) (materialized_succ (open_md model mk i) (OCI regs pc mem rom))).
Proof.
intros regs pc mem rom model p d HAI Hno Hdir Hfl Hp Hne Hnd Hfs Hfree Hav mk.
apply (node_open_core_lazy regs pc mem rom model (OCI regs pc mem rom) mk HAI).
- intro eff.
apply (openat_rd_check segs (pend_at regs pc mem rom) (getr regs 17) model p d Hno).
+ rewrite pend_gpr0. exact Hdir.
+ rewrite pend_gpr1. exact Hp.
+ apply path_eqb_neq. exact Hne.
+ rewrite pend_gpr2. exact Hfl.
+ exact Hnd.
+ exact Hfs.
- intro fd. exact (AI_halted segs H A model HAI).
- intro fd. apply ledgers_with_fds.
- exact Hfree.
- exact Hav.
- rewrite Hno; reflexivity.
Qed.
Lemma node_openat_dir_lazy : forall regs pc mem rom model,
AI segs H A model ->
bv_unsigned (getr regs 17) = 56%Z ->
getr regs 10 = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk dot_path ->
fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
ranges_avoid H (OCI regs pc mem rom) ->
let mk := fun fd => with_fds (fd_insert (m_fds model) fd FdDir) model in
node_ok segs (mkCfg (pend_at regs pc mem rom) model) open_ix (fun _ => [])
(fun i => mkCfg (mkst (regupd regs 10 (open_ret (m_fds model) i)) (v_addi pc 4) mem rom)
(materialized_succ (open_md model mk i) (OCI regs pc mem rom)))
/\ (forall i, AI segs H A (materialized_succ (open_md model mk i) (OCI regs pc mem rom))
/\ same_but_materialized (open_md model mk i) (materialized_succ (open_md model mk i) (OCI regs pc mem rom))).
Proof.
intros regs pc mem rom model HAI Hno Hdir Hfl Hp Hfree Hav mk.
apply (node_open_core_lazy regs pc mem rom model (OCI regs pc mem rom) mk HAI).
- intro eff. rewrite chk56 by exact Hno. unfold check_openat.
rewrite (modeled_open_flags_rd _ Hfl). cbn [negb].
unfold Prelude.check_copyins_after, Open.check_openat_body. rewrite si_mem, Hp.
change (path_eqb dot_path []) with false.
rewrite Hdir, fd32_AT_FDCWD, bv_eqb_refl. cbn [negb].
unfold Open.check_openat_resolved.
rewrite Hfl. cbn [Z.eqb]. unfold Open.check_openat_read.
change (path_eqb dot_path dot_path) with true. cbv beta iota.
unfold check_open_result_copyins, open_copyins.
rewrite pend_gpr1. cbn [ms_read_byte pend_at ms_mem ms_rom].
destruct (check_open_result (clear_copyins eff) model _) eqn:Hq; try reflexivity.
exfalso. exact (check_open_result_never_unmodeled _ _ _ Hq).
- intro fd. exact (AI_halted segs H A model HAI).
- intro fd. apply ledgers_with_fds.
- exact Hfree.
- exact Hav.
- rewrite Hno; reflexivity.
Qed.
Lemma node_read_file_lazy : forall regs pc mem rom model fd p off data bs w,
AI segs H A model ->
bv_unsigned (getr regs 17) = 63%Z ->
getr regs 10 = fd -> fd32 fd = fd ->
fd_lookup (m_fds model) fd = Some (FdFile p off) ->
fs_lookup (m_fs model) p = Some data ->
modeled_rw_count (getr regs 12) = true ->
file_read data off (getr regs 12) = bs ->
read_bytes_map (wview segs mem) (getr regs 11) (len_word bs) = Some w ->
access_okb (getr regs 11) (bv_unsigned (getr regs 12)) = true ->
range_avoids H (getr regs 11) (length bs) ->
let md' := with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model in
let accs := match bs with [] => [] | _ :: _ => [(getr regs 11, length bs)] end in
node_ok segs (mkCfg (pend_at regs pc mem rom) model) unit (fun _ => [])
(fun _ => mkCfg (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4)
(match bs with [] => mem | _ :: _ => write_to_mem mem (getr regs 11) bs end) rom)
(materialized_succ md' accs))
/\ AI segs H A (materialized_succ md' accs) /\ same_but_materialized md' (materialized_succ md' accs).
Proof.
intros regs pc mem rom model fd p off data bs w HAI Hno Hfd H32 Hlk Hfs Hcnt Hbs Hw Hz Hav md' accs.
pose proof (AI_halted segs H A model HAI) as Hh.
assert (Hchk : forall eff,
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= match bs, eff with
| [], _ => check_ret_only eff (Z_to_bv 64 0) md' []
| _ :: _, mkEffectU ret [(a, bs')] [] [] [] [] =>
if bv_eqb a (getr regs 11) && listN_eqb bs' bs && bv_eqb ret (len_word bs)
then CheckOk md' [] else CheckReject
| _, _ => CheckReject
end).
{ intro eff. rewrite chk63 by exact Hno. unfold check_read.
assert (HcntZ : (bv_unsigned (getr regs 12) <= rw_bytes_max)%Z)
by (unfold modeled_rw_count in Hcnt; apply Z.leb_le; exact Hcnt).
rewrite Hfd, H32, Hlk, Hz. cbn [negb]. rewrite Hfs. cbv zeta.
rewrite (rw_count_clamp_of_rw _ HcntZ), Z_to_bv_bv_unsigned.
rewrite Hbs, si_wmem, Hw.
destruct bs as [|b bs']; reflexivity. }
destruct bs as [|b bs'].
- cbn zeta in *. subst accs. rewrite materialized_succ_nil.
destruct (node_ret_only_lazy regs pc mem rom model (Z_to_bv 64 0) md' [] HAI Hchk Hh (ledgers_with_fds _ _)) as [Hn HA].
split; [exact Hn|]. split; [exact HA | apply same_but_materialized_refl].
- subst accs.
destruct (node_chk1_lazy regs pc mem rom model
(mkEffect (len_word (b :: bs')) [(getr regs 11, b :: bs')] []) md' [] HAI) as (Hn & HA & Hs).
+ rewrite Hchk. rewrite !bv_eqb_refl, (proj2 (listN_eqb_eq _ _) eq_refl). reflexivity.
+ exact Hh.
+ apply ledgers_with_fds.
+ cbn. intros a n [Hin|[]]. injection Hin as <- <-. exact Hav.
+ intros [r ws zs us cs ci] m2 evs2 Hk. rewrite Hchk in Hk.
destruct ws as [|[a bsx] [|? ?]]; try discriminate.
destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (bv_eqb a (getr regs 11)) eqn:E1; [|discriminate].
destruct (listN_eqb bsx (b :: bs')) eqn:E2; [|discriminate].
destruct (bv_eqb r (len_word (b :: bs'))) eqn:E3; [|discriminate].
cbn [andb] in Hk. inversion Hk; subst.
apply bv_eqb_eq in E1. apply listN_eqb_eq in E2. apply bv_eqb_eq in E3. subst. auto.
+ cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app eff_ret] in Hn, HA, Hs.
rewrite effmem_write1 in Hn. exact (conj Hn (conj HA Hs)).
Qed.
Lemma node_read_dir_lazy : forall regs pc mem rom model fd,
AI segs H A model ->
bv_unsigned (getr regs 17) = 63%Z ->
getr regs 10 = fd -> fd32 fd = fd ->
fd_lookup (m_fds model) fd = Some FdDir ->
access_okb (getr regs 11) (bv_unsigned (getr regs 12)) = true ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) unit (fun _ => [])
(fun _ => mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem rom) model)
/\ AI segs H A model.
Proof.
intros regs pc mem rom model fd HAI Hno Hfd H32 Hlk Hdr.
apply (node_ret_only_lazy regs pc mem rom model (errno_ret EISDIR) model [] HAI).
- intro eff. rewrite chk63 by exact Hno. unfold check_read. rewrite Hfd, H32, Hlk, Hdr. reflexivity.
- exact (AI_halted segs H A model HAI).
- apply ledgers_same.
Qed.
Lemma node_writev_lazy : forall regs pc mem rom model fd ch iovs bs,
AI segs H A model ->
bv_unsigned (getr regs 17) = 66%Z ->
fdchan fd ch model -> fd32 fd = fd -> getr regs 10 = fd ->
w_is0 (iovcnt32 (getr regs 12)) = false ->
(bv_unsigned (getr regs 12) <= IOV_MAX)%Z ->
copy_iovecs_aux (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11)
(word_to_nat (iovcnt32 (getr regs 12))) = ImpOk iovs ->
access_okb (getr regs 11) (16 * bv_unsigned (getr regs 12)) = true ->
iovs_access_okb iovs = true ->
gather_iovecs (ms_read_byte (pend_at regs pc mem rom)) iovs = Some bs ->
(iovs_total iovs <= MAX_RW_COUNT)%Z ->
(1 <= length bs)%nat ->
(forall n, (1 <= n)%nat -> (n <= length bs)%nat ->
ranges_avoid H (writev_copyins (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) (getr regs 12) iovs n)) ->
let accs := fun i : wr_index bs =>
writev_copyins (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) (getr regs 12) iovs (proj1_sig i) in
node_ok segs (mkCfg (pend_at regs pc mem rom) model) (wr_index bs)
(fun i => map (WriteEv ch) (firstn (proj1_sig i) bs))
(fun i => mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat (proj1_sig i)))) (v_addi pc 4) mem rom)
(materialized_succ model (accs i)))
/\ (forall i, AI segs H A (materialized_succ model (accs i)) /\ same_but_materialized model (materialized_succ model (accs i))).
Proof.
intros regs pc mem rom model fd ch iovs bs HAI Hno Hfdc H32 Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb Hav accs.
pose proof (AI_halted segs H A model HAI) as Hh.
pose proof (writev_chk_canon segs regs pc mem rom model fd ch iovs bs Hno Hfdc H32 Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb)
as Hchk.
pose proof (gather_iovecs_length _ _ _ Hg) as Hlen.
assert (HMv : MAX_RW_COUNT = 0x7ffff000%Z) by reflexivity.
set (mp := ms_read_byte (pend_at regs pc mem rom)) in *.
pose (ef := fun i : wr_index bs => writev_eff mp (getr regs 11) (getr regs 12) iovs (proj1_sig i)).
assert (Hacc : forall i, syscall_effect_accesses (ef i) = accs i) by (intros i; cbn; apply app_nil_r).
destruct (node_chk_lazy (pend_at regs pc mem rom) model (getr regs 17) (wr_index bs) (wr_full bs Hnb)
ef (fun _ => model) (fun i => map (WriteEv ch) (firstn (proj1_sig i) bs)) HAI eq_refl) as [Hn Hs].
- intros [n [Hn1 Hn2]]. unfold ef, writev_eff; cbn [proj1_sig]. rewrite Hchk.
assert (Hu : bv_unsigned (Z_to_bv 64 (Z.of_nat n)) = Z.of_nat n).
{ rewrite Z_to_bv_unsigned, bv_wrap64_mod. apply Z.mod_small. lia. }
rewrite Hu, Nat2Z.id.
rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia.
replace (addr_is_error_b (Z_to_bv 64 (Z.of_nat n))) with false
by (symmetry; unfold addr_is_error_b; apply Z.ltb_ge; rewrite Hu; unfold two_pow_64; lia).
rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl). reflexivity.
- intros _. exact Hh.
- intros _. apply ledgers_same.
- intros [n [Hn1 Hn2]]. rewrite Hacc. unfold accs; cbn [proj1_sig]. apply Hav; assumption.
- intros [ret ws zs us cs ci] m' evs Hk. rewrite Hchk in Hk.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate].
destruct (((1 <=? bv_unsigned ret)%Z && (bv_unsigned ret <=? Z.of_nat (length bs))%Z) &&
negb (addr_is_error_b ret) && access_ranges_eqb ci _) eqn:E; [|discriminate].
injection Hk as <- <-.
apply andb_prop in E as [E Hci]. apply andb_prop in E as [E _]. apply andb_prop in E as [E1 E2].
apply Z.leb_le in E1. apply Z.leb_le in E2. apply access_ranges_eqb_eq in Hci.
assert (Hr : (1 <= Z.to_nat (bv_unsigned ret))%nat /\ (Z.to_nat (bv_unsigned ret) <= length bs)%nat) by lia.
exists (exist _ (Z.to_nat (bv_unsigned ret)) Hr). unfold ef, writev_eff; cbn [proj1_sig].
rewrite Z2Nat.id by lia. rewrite Z_to_bv_bv_unsigned, Hci. auto.
- exact (fun _ => acfg_nonspurious_no _ _ _ _ _ _ Hno eq_refl).
- split.
+ eapply node_ok_ext; [exact Hn|]. intros i. cbn beta. rewrite adv_pend, Hacc.
unfold ef. rewrite effmem_writev_eff. unfold writev_eff; cbn [eff_ret]. reflexivity.
+ intros i. rewrite <- (Hacc i). exact (Hs i).
Qed.
Lemma srz_exit_lazy : forall regs pc mem rom model,
m_halted model = None -> is_exit_no (getr regs 17) ->
srealizes segs (mkCfg (pend_at regs pc mem rom) model)
(t_exit (bv_and (getr regs 10) (Z_to_bv 64 255)) (m_fs model)).
Proof.
intros regs pc mem rom model Hh Hx8. rewrite <- (pend_gpr0 regs pc mem rom).
exact (srz_exit segs (pend_at regs pc mem rom) model (getr regs 17) Hh eq_refl Hx8).
Qed.
Lemma srz_exit_small_lazy : forall regs pc mem rom model (c : word),
m_halted model = None -> is_exit_no (getr regs 17) ->
getr regs 10 = c -> (bv_unsigned c < 256)%Z ->
srealizes segs (mkCfg (pend_at regs pc mem rom) model) (t_exit c (m_fs model)).
Proof.
intros regs pc mem rom model c Hh Hx8 Hc Hsmall.
rewrite <- (land_255_small c Hsmall), <- Hc. apply srz_exit_lazy; assumption.
Qed.
Lemma srz_writev_lazy : forall regs pc mem rom model fd ch iovs bs T,
AI segs H A model ->
bv_unsigned (getr regs 17) = 66%Z ->
fdchan fd ch model -> fd32 fd = fd -> getr regs 10 = fd ->
w_is0 (iovcnt32 (getr regs 12)) = false ->
(bv_unsigned (getr regs 12) <= IOV_MAX)%Z ->
copy_iovecs_aux (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11)
(word_to_nat (iovcnt32 (getr regs 12))) = ImpOk iovs ->
access_okb (getr regs 11) (16 * bv_unsigned (getr regs 12)) = true ->
iovs_access_okb iovs = true ->
gather_iovecs (ms_read_byte (pend_at regs pc mem rom)) iovs = Some bs ->
(iovs_total iovs <= MAX_RW_COUNT)%Z ->
(1 <= length bs)%nat ->
(forall n, (1 <= n)%nat -> (n <= length bs)%nat ->
ranges_avoid H (writev_copyins (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) (getr regs 12) iovs n)) ->
(forall n model', (1 <= n)%nat -> (n <= length bs)%nat ->
AI segs H A model' -> same_but_materialized model model' ->
srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) (v_addi pc 4) mem rom) model') T) ->
srealizes segs (mkCfg (pend_at regs pc mem rom) model) (t_write_ch ch bs T).
Proof.
intros regs pc mem rom model fd ch iovs bs T HAI Hno Hfdc H32 Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb Hav Hc.
destruct (node_writev_lazy regs pc mem rom model fd ch iovs bs HAI Hno Hfdc H32 Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb Hav)
as [Hn Hs].
unfold t_write_ch.
eapply (srz_node segs _ (wr_index bs) _ _ (fun _ => T) (wr_full bs Hnb) Hn).
intros [n [Hn1 Hn2]]. cbn [proj1_sig]. destruct (Hs (exist _ n (conj Hn1 Hn2))) as [HA Hsm]. cbn [proj1_sig] in HA, Hsm.
apply (Hc n _ Hn1 Hn2 HA Hsm).
Qed.
Lemma srz_close_lazy : forall regs pc mem rom model fd e T,
AI segs H A model ->
bv_unsigned (getr regs 17) = 57%Z -> getr regs 10 = fd -> fd32 fd = fd ->
fd_lookup (m_fds model) fd = Some e ->
srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom)
(with_fds (fd_remove (m_fds model) fd) model)) T ->
srealizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model fd e T HAI Hno Hfd H32 Hlk Hc.
destruct (node_close_lazy regs pc mem rom model fd e HAI Hno Hfd H32 Hlk) as [Hn _].
exact (srz_silent1 segs _ _ T Hn Hc).
Qed.
Lemma srz_ioctl_winsz_lazy : forall regs pc mem rom model fd e T,
AI segs H A model ->
bv_unsigned (getr regs 17) = 29%Z -> getr regs 10 = fd -> fd32 fd = fd ->
fd_lookup (m_fds model) fd = Some e -> (forall rd wr : bool, e <> FdUrandom) -> cmd32 (getr regs 11) = TIOCGWINSZ ->
srealizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi pc 4) mem rom) model) T ->
srealizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model fd e T HAI Hno Hfd H32 Hlk Hnd Hcmd Hc.
destruct (node_ioctl_winsz_lazy regs pc mem rom model fd e HAI Hno Hfd H32 Hlk Hnd Hcmd) as [Hn _].
exact (srz_silent1 segs _ _ T Hn Hc).
Qed.
Lemma srz_read_dir_lazy : forall regs pc mem rom model fd T,
AI segs H A model ->
bv_unsigned (getr regs 17) = 63%Z -> getr regs 10 = fd -> fd32 fd = fd ->
fd_lookup (m_fds model) fd = Some FdDir ->
access_okb (getr regs 11) (bv_unsigned (getr regs 12)) = true ->
srealizes segs (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem rom) model) T ->
srealizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model fd T HAI Hno Hfd H32 Hlk Hdr Hc.
destruct (node_read_dir_lazy regs pc mem rom model fd HAI Hno Hfd H32 Hlk Hdr) as [Hn _].
exact (srz_silent1 segs _ _ T Hn Hc).
Qed.
Lemma srz_read_file_lazy : forall regs pc mem rom model fd p off data bs w T,
AI segs H A model ->
bv_unsigned (getr regs 17) = 63%Z -> getr regs 10 = fd -> fd32 fd = fd ->
fd_lookup (m_fds model) fd = Some (FdFile p off) ->
fs_lookup (m_fs model) p = Some data ->
modeled_rw_count (getr regs 12) = true ->
file_read data off (getr regs 12) = bs ->
read_bytes_map (wview segs mem) (getr regs 11) (len_word bs) = Some w ->
access_okb (getr regs 11) (bv_unsigned (getr regs 12)) = true ->
range_avoids H (getr regs 11) (length bs) ->
(forall model', AI segs H A model' ->
same_but_materialized (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model) model' ->
srealizes segs (mkCfg (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4)
(match bs with [] => mem | _ :: _ => write_to_mem mem (getr regs 11) bs end) rom)
model') T) ->
srealizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model fd p off data bs w T HAI Hno Hfd H32 Hlk Hfs Hcnt Hbs Hw Hz Hav Hc.
destruct (node_read_file_lazy regs pc mem rom model fd p off data bs w HAI Hno Hfd H32 Hlk Hfs Hcnt Hbs Hw Hz Hav)
as (Hn & HA & Hs).
exact (srz_silent1 segs _ _ T Hn (Hc _ HA Hs)).
Qed.
Lemma srz_openat_file_lazy : forall regs pc mem rom model p d KA KB,
AI segs H A model ->
bv_unsigned (getr regs 17) = 56%Z -> getr regs 10 = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
p <> [] -> openat_plain_name p = true ->
fs_lookup (m_fs model) p = Some d ->
fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
ranges_avoid H (OCI regs pc mem rom) ->
(forall e model', In e openat_errnos -> AI segs H A model' -> same_but_materialized model model' ->
srealizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model') KA) ->
(forall model', AI segs H A model' ->
same_but_materialized (with_fds (fd_insert (m_fds model) (alloc_fd (m_fds model)) (FdFile p (Z_to_bv 64 0))) model) model' ->
srealizes segs (mkCfg (mkst (regupd regs 10 (alloc_fd (m_fds model))) (v_addi pc 4) mem rom) model') KB) ->
srealizes segs (mkCfg (pend_at regs pc mem rom) model) (t_alt2 KA KB).
Proof.
intros regs pc mem rom model p d KA KB HAI Hno Hdir Hfl Hp Hne Hnd Hfs Hfree Hav HKA HKB.
destruct (node_openat_file_lazy regs pc mem rom model p d HAI Hno Hdir Hfl Hp Hne Hnd Hfs Hfree Hav) as [Hn Hs].
apply (srz_alt2 segs _ _ _ _ KA KB (exist _ ENOMEM ENOMEM_in_openat_errnos) tt Hn).
- intros [e He]. destruct (Hs (inl (exist _ e He))) as [HA Hsm]. cbn [open_ret open_md proj1_sig] in *.
exact (HKA e _ He HA Hsm).
- intros []. destruct (Hs (inr tt)) as [HA Hsm]. cbn [open_ret open_md] in *. exact (HKB _ HA Hsm).
Qed.
Lemma srz_openat_dir_lazy : forall regs pc mem rom model KA KB,
AI segs H A model ->
bv_unsigned (getr regs 17) = 56%Z -> getr regs 10 = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk dot_path ->
fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
ranges_avoid H (OCI regs pc mem rom) ->
(forall e model', In e openat_errnos -> AI segs H A model' -> same_but_materialized model model' ->
srealizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model') KA) ->
(forall model', AI segs H A model' ->
same_but_materialized (with_fds (fd_insert (m_fds model) (alloc_fd (m_fds model)) FdDir) model) model' ->
srealizes segs (mkCfg (mkst (regupd regs 10 (alloc_fd (m_fds model))) (v_addi pc 4) mem rom) model') KB) ->
srealizes segs (mkCfg (pend_at regs pc mem rom) model) (t_alt2 KA KB).
Proof.
intros regs pc mem rom model KA KB HAI Hno Hdir Hfl Hp Hfree Hav HKA HKB.
destruct (node_openat_dir_lazy regs pc mem rom model HAI Hno Hdir Hfl Hp Hfree Hav) as [Hn Hs].
apply (srz_alt2 segs _ _ _ _ KA KB (exist _ ENOMEM ENOMEM_in_openat_errnos) tt Hn).
- intros [e He]. destruct (Hs (inl (exist _ e He))) as [HA Hsm]. cbn [open_ret open_md proj1_sig] in *.
exact (HKA e _ He HA Hsm).
- intros []. destruct (Hs (inr tt)) as [HA Hsm]. cbn [open_ret open_md] in *. exact (HKB _ HA Hsm).
Qed.
Lemma srz_openat_absent_lazy : forall regs pc mem rom model p T,
AI segs H A model ->
bv_unsigned (getr regs 17) = 56%Z -> getr regs 10 = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
p <> [] -> openat_plain_name p = true -> fs_lookup (m_fs model) p = None ->
ranges_avoid H (OCI regs pc mem rom) ->
(forall model', AI segs H A model' -> same_but_materialized model model' ->
srealizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4) mem rom) model') T) ->
srealizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model p T HAI Hno Hdir Hfl Hp Hne Hnd Hfs Hav Hc.
destruct (node_openat_absent_lazy regs pc mem rom model p HAI Hno Hdir Hfl Hp Hne Hnd Hfs Hav) as (Hn & HA & Hs).
exact (srz_silent1 segs _ _ T Hn (Hc _ HA Hs)).
Qed.
Lemma srz_openat_empty_lazy : forall regs pc mem rom model T,
AI segs H A model ->
bv_unsigned (getr regs 17) = 56%Z -> modeled_open_flags (getr regs 12) = true ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk [] ->
ranges_avoid H (OCI regs pc mem rom) ->
(forall model', AI segs H A model' -> same_but_materialized model model' ->
srealizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4) mem rom) model') T) ->
srealizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model T HAI Hno Hfl Hp Hav Hc.
destruct (node_openat_empty_lazy regs pc mem rom model HAI Hno Hfl Hp Hav) as (Hn & HA & Hs).
exact (srz_silent1 segs _ _ T Hn (Hc _ HA Hs)).
Qed.
Lemma srz_openat_toolong_lazy : forall regs pc mem rom model T,
AI segs H A model ->
bv_unsigned (getr regs 17) = 56%Z -> modeled_open_flags (getr regs 12) = true ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrTooLong ->
ranges_avoid H (OCI regs pc mem rom) ->
(forall model', AI segs H A model' -> same_but_materialized model model' ->
srealizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENAMETOOLONG)) (v_addi pc 4) mem rom) model') T) ->
srealizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model T HAI Hno Hfl Hp Hav Hc.
destruct (node_openat_toolong_lazy regs pc mem rom model HAI Hno Hfl Hp Hav) as (Hn & HA & Hs).
exact (srz_silent1 segs _ _ T Hn (Hc _ HA Hs)).
Qed.
End h.
End g.
