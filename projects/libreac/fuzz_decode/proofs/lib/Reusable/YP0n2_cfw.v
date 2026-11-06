(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/Reusable/YP0n.v. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/libreac/fuzz_scene/lib/Reusable/YP0n2_cfw.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK16 YK0n YK11 YK0i YK0h YK14 YK0v YK0p YK02 YK15.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.Z Require Import Placement.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.R Require Import Place Cfg.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YO0d YP0n YK15_cfw YK15b_cfw YP0n_cfw.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import SlotAgree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Section g.
Context {fx : FPState}.
Variable B : malloc_syms.
Let segs := ms_segs B.
Lemma crz_ret_only_copyins_silent : forall regs pc mem rom model reads r m' T,
m_halted model = None -> m_vm_lazy model = [] ->
alloc_no_b (bv_unsigned (getr regs 17)) = false ->
(forall eff, check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_ret_only_copyins reads eff r m' []) ->
m_halted m' = None -> m_vm_lazy m' = [] ->
crealizes B (mkCfg (mkst (regupd regs 10 r) (v_addi pc 4) mem rom) m') T ->
crealizes B (mkCfg (pend_at regs pc mem rom) model) T.
Proof using.
intros regs pc mem rom model reads r m' T Hh Hlz Hal Hchk Hh' Hlz' Hc.
apply (crz_chk1_silent B regs pc mem rom model (with_copyins reads (mkEffect r [] [])) m' T Hh Hlz Hal).
- rewrite Hchk. apply check_ret_only_copyins_refl.
- exact Hh'.
- exact Hlz'.
- intros eff2 m2 evs2 H2. rewrite Hchk in H2. apply check_ret_only_copyins_ok_iff. exact H2.
- cbn [eff_ret with_copyins]. rewrite effmem_copyins_ret_only. exact Hc.
Qed.
Lemma crz_set_tid_first : forall regs pc mem rom model T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 96%Z ->
m_tid model = None ->
(forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
crealizes B (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom)
(with_tid tid model)) T) ->
crealizes B (mkCfg (pend_at regs pc mem rom) model) T.
Proof using.
intros regs pc mem rom model T Hh Hlz Hno Htid Hc.
pose (I := {tid : word | (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z}).
assert (H1 : (0 < bv_unsigned (Z_to_bv 64 1) < PID_MAX_ENVELOPE)%Z).
{ rewrite PID_MAX_ENVELOPE_val. change (bv_unsigned (Z_to_bv 64 1)) with 1%Z. lia. }
eapply (crz_silent_allI_sys B (pend_at regs pc mem rom) model (getr regs 17) I _ (exist _ (Z_to_bv 64 1) H1) T
eq_refl ltac:(rewrite Hno; reflexivity)).
- apply (node_chk segs (pend_at regs pc mem rom) model (getr regs 17) I (exist _ (Z_to_bv 64 1) H1)
(fun i => mkEffect (proj1_sig i) [] [])
(fun i => with_tid (proj1_sig i) model)
(fun _ => []) Hh eq_refl).
+ intros [tid Ht]. cbn [proj1_sig]. rewrite chk96 by exact Hno.
unfold check_set_tid_address. rewrite Htid.
rewrite (proj2 (Z.ltb_lt _ _) (proj1 Ht)), (proj2 (Z.ltb_lt _ _) (proj2 Ht)).
reflexivity.
+ intros [tid Ht]. cbn. exact Hh.
+ intros [tid Ht]. cbn. exact Hlz.
+ intros [r ws zs us cs ci] m' evs Hk. rewrite chk96 in Hk by exact Hno.
unfold check_set_tid_address in Hk. rewrite Htid in Hk.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct ((0 <? bv_unsigned r)%Z) eqn:E1; [|discriminate].
destruct ((bv_unsigned r <? PID_MAX_ENVELOPE)%Z) eqn:E2; [|discriminate].
cbn [andb] in Hk. inversion Hk; subst.
apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
exists (exist _ r (conj E1 E2)). cbn [proj1_sig]. auto.
+ exact (fun _ => acfg_nonspurious_no _ _ _ _ _ _ Hno eq_refl).
- intros [tid Ht]. cbn [proj1_sig]. rewrite adv_pend. cbn [eff_ret].
rewrite effmem_ret_only. apply Hc. exact Ht.
Qed.
Lemma crz_close : forall regs pc mem rom model fd e T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 57%Z ->
getr regs 10 = fd -> fd32 fd = fd ->
fd_lookup (m_fds model) fd = Some e ->
crealizes B (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom)
(with_fds (fd_remove (m_fds model) fd) model)) T ->
crealizes B (mkCfg (pend_at regs pc mem rom) model) T.
Proof using.
intros regs pc mem rom model fd e T Hh Hlz Hno Hfd H32 Hlk Hc.
apply (crz_ret_only_silent B regs pc mem rom model (Z_to_bv 64 0)
(with_fds (fd_remove (m_fds model) fd) model) T Hh Hlz ltac:(rewrite Hno; reflexivity)).
- intro eff. rewrite chk57 by exact Hno. rewrite Hfd, H32. unfold check_close.
rewrite Hlk. reflexivity.
- exact Hh.
- exact Hlz.
- exact Hc.
Qed.
Lemma crz_openat_toolong : forall regs pc mem rom model T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 56%Z ->
modeled_open_flags (getr regs 12) = true ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrTooLong ->
crealizes B (mkCfg (mkst (regupd regs 10 (errno_ret ENAMETOOLONG)) (v_addi pc 4) mem rom)
model) T ->
crealizes B (mkCfg (pend_at regs pc mem rom) model) T.
Proof using.
intros regs pc mem rom model T Hh Hlz Hno Hfl Hp Hc.
apply (crz_ret_only_copyins_silent regs pc mem rom model (open_copyins (pend_at regs pc mem rom))
(errno_ret ENAMETOOLONG) model T Hh Hlz ltac:(rewrite Hno; reflexivity)).
- intro eff. apply (openat_toolong_check segs (pend_at regs pc mem rom) (getr regs 17) model Hno).
+ rewrite pend_gpr2. exact Hfl.
+ rewrite pend_gpr1. exact Hp.
- exact Hh.
- exact Hlz.
- exact Hc.
Qed.
Lemma crz_openat_empty : forall regs pc mem rom model T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 56%Z ->
modeled_open_flags (getr regs 12) = true ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk [] ->
crealizes B (mkCfg (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4) mem rom)
model) T ->
crealizes B (mkCfg (pend_at regs pc mem rom) model) T.
Proof using.
intros regs pc mem rom model T Hh Hlz Hno Hfl Hp Hc.
apply (crz_ret_only_copyins_silent regs pc mem rom model (open_copyins (pend_at regs pc mem rom))
(errno_ret ENOENT) model T Hh Hlz ltac:(rewrite Hno; reflexivity)).
- intro eff. rewrite chk56 by exact Hno. unfold check_openat.
rewrite Hfl. cbn [negb]. unfold Prelude.check_copyins_after, Open.check_openat_body.
rewrite si_mem, Hp. change (path_eqb [] []) with true. cbv beta iota.
unfold check_ret_only_copyins, check_copyins, open_copyins.
rewrite pend_gpr1. cbn [ms_read_byte pend_at ms_mem ms_rom].
destruct (check_ret_only (clear_copyins eff) (errno_ret ENOENT) model []) eqn:Hq;
[reflexivity| |reflexivity].
destruct (access_ranges_eqb _ _); reflexivity.
- exact Hh.
- exact Hlz.
- exact Hc.
Qed.
Lemma crz_openat_absent : forall regs pc mem rom model p T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 56%Z ->
getr regs 10 = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
p <> [] -> openat_plain_name p = true ->
fs_lookup (m_fs model) p = None ->
crealizes B (mkCfg (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4) mem rom)
model) T ->
crealizes B (mkCfg (pend_at regs pc mem rom) model) T.
Proof using.
intros regs pc mem rom model p T Hh Hlz Hno Hdir Hfl Hp Hne Hnd Hfs Hc.
pose proof (openat_plain_name_noslash _ Hnd) as Hsl.
apply openat_plain_name_nodirref in Hnd.
apply (crz_ret_only_copyins_silent regs pc mem rom model (open_copyins (pend_at regs pc mem rom))
(errno_ret ENOENT) model T Hh Hlz ltac:(rewrite Hno; reflexivity)).
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
- exact Hh.
- exact Hlz.
- exact Hc.
Qed.
Lemma crz_open_core : forall regs pc mem rom model reads (mk : word -> Model) A B',
m_halted model = None -> m_vm_lazy model = [] ->
(forall eff, check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_open_result_copyins reads eff model mk) ->
(forall fd, m_halted (mk fd) = None) -> (forall fd, m_vm_lazy (mk fd) = []) ->
fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
(forall e, In e openat_errnos ->
crealizes B (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model) A) ->
crealizes B (mkCfg (mkst (regupd regs 10 (alloc_fd (m_fds model))) (v_addi pc 4) mem rom)
(mk (alloc_fd (m_fds model)))) B' ->
alloc_no_b (bv_unsigned (getr regs 17)) = false ->
crealizes B (mkCfg (pend_at regs pc mem rom) model) (t_alt2 A B').
Proof using.
intros regs pc mem rom model reads mk A B' Hh Hlz Hchk Hmk Hmkl Hfree HA HB Hna.
pose (IA := {e : Z | In e openat_errnos}).
pose (ef := fun i : IA + unit =>
match i with
| inl e => with_copyins reads (mkEffect (errno_ret (proj1_sig e)) [] [])
| inr _ => with_copyins reads (mkEffect (alloc_fd (m_fds model)) [] [])
end).
pose (md := fun i : IA + unit =>
match i with inl _ => model | inr _ => mk (alloc_fd (m_fds model)) end).
apply (crz_alt2_sys B (pend_at regs pc mem rom) model (getr regs 17) IA unit
(fun i => mkCfg (advance_past_svc (apply_effect (pend_at regs pc mem rom) (ef i))) (md i))
A B' (exist _ ENOMEM ENOMEM_in_openat_errnos) tt eq_refl Hna).
- apply (node_chk segs (pend_at regs pc mem rom) model (getr regs 17) (IA + unit) (inr tt)
ef md (fun _ => []) Hh eq_refl).
+ intros [[e He] | []]; unfold ef, md; cbn [proj1_sig]; rewrite Hchk; apply check_open_result_copyins_ok_iff.
* left. exists e. auto.
* right. exists (alloc_fd (m_fds model)). auto.
+ intros [[e He] | []]; unfold md; [exact Hh | apply Hmk].
+ intros [[e He] | []]; unfold md; [exact Hlz | apply Hmkl].
+ intros eff m' evs Hk. rewrite Hchk in Hk. apply check_open_result_copyins_ok_iff in Hk.
destruct Hk as [(e & He & -> & -> & ->) | (fd & _ & -> & -> & -> & ->)].
* exists (inl (exist _ e He)). unfold ef, md; cbn [proj1_sig]. auto.
* exists (inr tt). unfold ef, md. auto.
+ exact (fun _ => acfg_nonspurious_no _ _ _ _ _ _ eq_refl Hna).
- intros [e He]. unfold ef, md; cbn [proj1_sig]. rewrite adv_pend. cbn [eff_ret with_copyins].
rewrite effmem_copyins_ret_only. apply HA. exact He.
- intros []. unfold ef, md. rewrite adv_pend. cbn [eff_ret with_copyins].
rewrite effmem_copyins_ret_only. exact HB.
Qed.
Lemma crz_openat_file : forall regs pc mem rom model p d A B',
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 56%Z ->
getr regs 10 = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
p <> [] -> openat_plain_name p = true ->
fs_lookup (m_fs model) p = Some d ->
fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
(forall e, In e openat_errnos ->
crealizes B (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model) A) ->
crealizes B (mkCfg (mkst (regupd regs 10 (alloc_fd (m_fds model))) (v_addi pc 4) mem rom)
(with_fds (fd_insert (m_fds model) (alloc_fd (m_fds model))
(FdFile p (Z_to_bv 64 0))) model)) B' ->
crealizes B (mkCfg (pend_at regs pc mem rom) model) (t_alt2 A B').
Proof using.
intros regs pc mem rom model p d A B' Hh Hlz Hno Hdir Hfl Hp Hne Hnd Hfs Hfree HA HB.
apply (crz_open_core regs pc mem rom model (open_copyins (pend_at regs pc mem rom))
(fun fd => with_fds (fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model)
A B' Hh Hlz).
- intro eff.
apply (openat_rd_check segs (pend_at regs pc mem rom) (getr regs 17) model p d Hno).
+ rewrite pend_gpr0. exact Hdir.
+ rewrite pend_gpr1. exact Hp.
+ apply path_eqb_neq. exact Hne.
+ rewrite pend_gpr2. exact Hfl.
+ exact Hnd.
+ exact Hfs.
- intro fd. exact Hh.
- intro fd. exact Hlz.
- exact Hfree.
- exact HA.
- exact HB.
- rewrite Hno; reflexivity.
Qed.
Lemma crz_openat_dir : forall regs pc mem rom model A B',
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 56%Z ->
getr regs 10 = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk dot_path ->
fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
(forall e, In e openat_errnos ->
crealizes B (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model) A) ->
crealizes B (mkCfg (mkst (regupd regs 10 (alloc_fd (m_fds model))) (v_addi pc 4) mem rom)
(with_fds (fd_insert (m_fds model) (alloc_fd (m_fds model)) FdDir) model)) B' ->
crealizes B (mkCfg (pend_at regs pc mem rom) model) (t_alt2 A B').
Proof using.
intros regs pc mem rom model A B' Hh Hlz Hno Hdir Hfl Hp Hfree HA HB.
apply (crz_open_core regs pc mem rom model (open_copyins (pend_at regs pc mem rom))
(fun fd => with_fds (fd_insert (m_fds model) fd FdDir) model) A B' Hh Hlz).
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
- intro fd. exact Hh.
- intro fd. exact Hlz.
- exact Hfree.
- exact HA.
- exact HB.
- rewrite Hno; reflexivity.
Qed.
Lemma crz_read_file : forall regs pc mem rom model fd p off data bs w T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 63%Z ->
getr regs 10 = fd -> fd32 fd = fd ->
fd_lookup (m_fds model) fd = Some (FdFile p off) ->
fs_lookup (m_fs model) p = Some data ->
modeled_rw_count (getr regs 12) = true ->
file_read data off (getr regs 12) = bs ->
read_bytes_map (wview segs mem) (getr regs 11) (len_word bs) = Some w ->
access_okb (getr regs 11) (bv_unsigned (getr regs 12)) = true ->
crealizes B (mkCfg (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4)
(match bs with
| [] => mem
| _ :: _ => write_to_mem mem (getr regs 11) bs
end) rom)
(with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs)))
model)) T ->
crealizes B (mkCfg (pend_at regs pc mem rom) model) T.
Proof using.
intros regs pc mem rom model fd p off data bs w T Hh Hlz Hno Hfd H32 Hlk Hfs Hcnt Hbs Hw Hz Hc.
set (m' := with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model) in Hc.
assert (Hchk : forall eff,
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= match bs, eff with
| [], _ => check_ret_only eff (Z_to_bv 64 0) m' []
| _ :: _, mkEffectU ret [(a, bs')] [] [] [] [] =>
if bv_eqb a (getr regs 11) && listN_eqb bs' bs && bv_eqb ret (len_word bs)
then CheckOk m' [] else CheckReject
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
- apply (crz_ret_only_silent B regs pc mem rom model (Z_to_bv 64 0) m' T Hh Hlz ltac:(rewrite Hno; reflexivity) Hchk).
+ exact Hh.
+ exact Hlz.
+ exact Hc.
- apply (crz_chk1_silent B regs pc mem rom model
(mkEffect (len_word (b :: bs')) [(getr regs 11, b :: bs')] []) m' T Hh Hlz ltac:(rewrite Hno; reflexivity)).
+ rewrite Hchk. rewrite !bv_eqb_refl, (proj2 (listN_eqb_eq _ _) eq_refl). reflexivity.
+ exact Hh.
+ exact Hlz.
+ intros [r ws zs us cs ci] m2 evs2 Hk. rewrite Hchk in Hk.
destruct ws as [|[a bsx] [|? ?]]; try discriminate.
destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (bv_eqb a (getr regs 11)) eqn:E1; [|discriminate].
destruct (listN_eqb bsx (b :: bs')) eqn:E2; [|discriminate].
destruct (bv_eqb r (len_word (b :: bs'))) eqn:E3; [|discriminate].
cbn [andb] in Hk. inversion Hk; subst.
apply bv_eqb_eq in E1. apply listN_eqb_eq in E2. apply bv_eqb_eq in E3. subst. auto.
+ cbn [eff_ret]. rewrite effmem_write1. exact Hc.
Qed.
Lemma crz_read_dir : forall regs pc mem rom model fd T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 63%Z ->
getr regs 10 = fd -> fd32 fd = fd ->
fd_lookup (m_fds model) fd = Some FdDir ->
access_okb (getr regs 11) (bv_unsigned (getr regs 12)) = true ->
crealizes B (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem rom) model) T ->
crealizes B (mkCfg (pend_at regs pc mem rom) model) T.
Proof using.
intros regs pc mem rom model fd T Hh Hlz Hno Hfd H32 Hlk Hdr Hc.
apply (crz_ret_only_silent B regs pc mem rom model (errno_ret EISDIR) model T Hh Hlz ltac:(rewrite Hno; reflexivity)).
- intro eff. rewrite chk63 by exact Hno. unfold check_read. rewrite Hfd, H32, Hlk, Hdr. reflexivity.
- exact Hh.
- exact Hlz.
- exact Hc.
Qed.
End g.
