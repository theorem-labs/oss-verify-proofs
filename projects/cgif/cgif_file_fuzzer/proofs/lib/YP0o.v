(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open ReadWrite.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK16 YK0n YK11 YK0i YK0h YK14 YK0v YK0p YK02 YK15 YP0n.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib.R Require Import Cfg.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Section a.
Context {fx : FPState}.
Lemma check_unlink_result_never_unmodeled : forall p eff m, check_unlink_result p eff m <> CheckUnmodeled.
Proof.
intros p [ret ws zs us cs ci] m. unfold check_unlink_result.
destruct ws as [|? ?]; destruct zs as [|? ?]; destruct us as [|? ?]; destruct cs as [|? ?]; destruct ci as [|? ?]; try discriminate.
destruct (errno_ret_in unlinkat_errnos ret); [discriminate|]. destruct (bv_eqb ret (Z_to_bv 64 0)); discriminate.
Qed.
Lemma check_unlink_result_ok_iff : forall p eff m m' evs,
check_unlink_result p eff m = CheckOk m' evs <->
((exists e, In e unlinkat_errnos /\ eff = mkEffect (errno_ret e) [] [] /\ m' = m /\ evs = [])
\/ (eff = mkEffect (Z_to_bv 64 0) [] [] /\ m' = with_fs (fs_remove (m_fs m) p) m /\ evs = [])).
Proof.
intros p [ret ws zs us cs ci] m m' evs. unfold check_unlink_result. split.
- intro H.
destruct ws as [|? ?]; [|discriminate]. destruct zs as [|? ?]; [|discriminate]. destruct us as [|? ?]; [|discriminate].
destruct cs as [|? ?]; [|discriminate]. destruct ci as [|? ?]; [|discriminate].
destruct (errno_ret_in unlinkat_errnos ret) eqn:Herr.
+ inversion H; subst. apply errno_ret_in_true in Herr. destruct Herr as (e & HIn & ->). left. exists e. auto.
+ destruct (bv_eqb ret (Z_to_bv 64 0)) eqn:Heq; [|discriminate]. inversion H; subst. apply bv_eqb_eq in Heq. subst ret. right. auto.
- intros [(e & HIn & Heff & -> & ->) | (Heff & -> & ->)].
+ inversion Heff; subst. rewrite (errno_ret_in_intro _ e HIn). reflexivity.
+ inversion Heff; subst. rewrite errno_ret_in_unlinkat_zero, bv_eqb_refl. reflexivity.
Qed.
Lemma check_syscall_35 : forall segs ms x8 eff m,
bv_unsigned x8 = 35%Z ->
check_syscall (sys_input segs ms x8) eff m
= check_unlinkat (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2) eff m.
Proof. intros segs ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.
Definition check_unlink_present_copyins (reads : list (word * nat)) (eff : SyscallEffect) (m : Model) (p : path) : check_result :=
check_copyins reads eff (check_unlink_result p (clear_copyins eff) m).
Lemma check_unlink_present_copyins_ok_iff : forall reads eff m p m' evs,
check_unlink_present_copyins reads eff m p = CheckOk m' evs <->
((exists e, In e unlinkat_errnos /\ eff = with_copyins reads (mkEffect (errno_ret e) [] []) /\ m' = m /\ evs = [])
\/ (eff = with_copyins reads (mkEffect (Z_to_bv 64 0) [] []) /\ m' = with_fs (fs_remove (m_fs m) p) m /\ evs = [])).
Proof.
intros reads eff m p m' evs. unfold check_unlink_present_copyins, check_copyins.
destruct (access_ranges_eqb (eff_copyins eff) reads) eqn:Hreads.
- apply access_ranges_eqb_eq in Hreads. rewrite check_unlink_result_ok_iff. split.
+ intros [(e & HIn & Hcore & -> & ->) | (Hcore & -> & ->)].
* left. exists e. repeat split; try assumption. eapply effect_from_copyins_and_clear; eassumption.
* right. repeat split. eapply effect_from_copyins_and_clear; eassumption.
+ intros [(e & HIn & Heff & -> & ->) | (Heff & -> & ->)].
* left. exists e. repeat split; try assumption. rewrite Heff. reflexivity.
* right. repeat split. rewrite Heff. reflexivity.
- split; [discriminate|].
intros [(e & _ & Heff & _) | (Heff & _)].
all: rewrite Heff in Hreads; cbn [eff_copyins with_copyins] in Hreads;
pose proof (proj2 (access_ranges_eqb_eq reads reads) eq_refl) as Htrue; congruence.
Qed.
Lemma unlinkat_tmp_check_gen : forall segs ms x8 model p n,
bv_unsigned x8 = 35%Z ->
ms_gpr ms 0 = AT_FDCWD ->
read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
bv_unsigned (flag32 (ms_gpr ms 2)) = 0%Z ->
path_eqb p [] = false -> path_strip_trailing_slashes p = p -> path_has_slash p = true -> tmp_name p = Some n ->
Nat.ltb NAME_MAX (length n) = false ->
fd_names_path (m_fds model) p = false ->
forall eff,
check_syscall (sys_input segs ms x8) eff model
= if fs_under (m_fs model) p then check_ret_only_copyins (open_copyins ms) eff (errno_ret EISDIR) model []
else match fs_lookup (m_fs model) p with
| Some _ => check_unlink_present_copyins (open_copyins ms) eff model p
| None => check_ret_only_copyins (open_copyins ms) eff (errno_ret ENOENT) model []
end.
Proof.
intros segs ms x8 model p n Hno Hdirfd Hpath Hfl Hpe Hstrip Hsl Htmp Hnm Hfdn eff.
rewrite (check_syscall_35 segs ms x8 eff model Hno). unfold check_unlinkat.
unfold modeled_unlink_flags. rewrite Hfl. cbn [Z.eqb orb negb]. cbv beta iota zeta.
unfold Prelude.check_copyins_after, Checks.Sys.Fs.Namei.check_unlinkat_body.
rewrite in_mem_si, Hpath. cbv beta iota zeta.
rewrite Hpe. cbv beta iota.
rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota zeta.
rewrite Hstrip, Hpe, Hsl, Htmp. cbv beta iota.
unfold Checks.Sys.Fs.Namei.check_unlinkat_tmp. unfold unlink_rmdir. rewrite Hfl, Hnm.
change (0 =? AT_REMOVEDIR)%Z with false. cbv beta iota.
unfold check_unlink_present_copyins, check_ret_only_copyins, open_copyins.
destruct (fs_under (m_fs model) p).
- destruct (check_ret_only (clear_copyins eff) (errno_ret EISDIR) model []) eqn:Hr;
[reflexivity | unfold check_copyins; destruct (access_ranges_eqb _ _); reflexivity | exfalso; now apply check_ret_only_no_unmodeled in Hr].
- destruct (fs_lookup (m_fs model) p) as [d|].
+ unfold Checks.Sys.Fs.Namei.check_unlink_found. unfold unlink_rmdir, path_trailing_slash. rewrite Hfl, Hstrip, Nat.eqb_refl, Hfdn.
change (0 =? AT_REMOVEDIR)%Z with false. cbn [negb]. cbv beta iota.
destruct (check_unlink_result p (clear_copyins eff) model) eqn:Hr; [reflexivity | reflexivity | exfalso; now apply check_unlink_result_never_unmodeled in Hr].
+ destruct (check_ret_only (clear_copyins eff) (errno_ret ENOENT) model []) eqn:Hr;
[reflexivity | unfold check_copyins; destruct (access_ranges_eqb _ _); reflexivity | exfalso; now apply check_ret_only_no_unmodeled in Hr].
Qed.
Section b.
Variable segs : list Segment.
Lemma ENOMEM_in_unlinkat_errnos : In ENOMEM unlinkat_errnos.
Proof. left. reflexivity. Qed.
Lemma rz_unlink_core : forall regs pc mem rom model reads (es : list Z) (m1 : Model) e0 A B,
m_halted model = None -> m_vm_lazy model = [] ->
In e0 es ->
(forall eff m' evs,
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model = CheckOk m' evs <->
((exists e, In e es /\ eff = with_copyins reads (mkEffect (errno_ret e) [] []) /\ m' = model /\ evs = [])
\/ (eff = with_copyins reads (mkEffect (Z_to_bv 64 0) [] []) /\ m' = m1 /\ evs = []))) ->
m_halted m1 = None -> m_vm_lazy m1 = [] ->
(forall e, In e es ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model) A) ->
realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom) m1) B ->
alloc_no_b (bv_unsigned (getr regs 17)) = false ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) (t_alt2 A B).
Proof.
intros regs pc mem rom model reads es m1 e0 A B Hh Hlz He0 Hchk Hh1 Hlz1 HA HB Hna.
pose (IA := {e : Z | In e es}).
pose (ef := fun i : IA + unit =>
match i with
| inl e => with_copyins reads (mkEffect (errno_ret (proj1_sig e)) [] [])
| inr _ => with_copyins reads (mkEffect (Z_to_bv 64 0) [] [])
end).
pose (md := fun i : IA + unit => match i with inl _ => model | inr _ => m1 end).
apply (rz_alt2 segs (mkCfg (pend_at regs pc mem rom) model) IA unit
(fun i => mkCfg (advance_past_svc (apply_effect (pend_at regs pc mem rom) (ef i))) (md i))
A B (exist _ e0 He0) tt).
- apply (node_chk segs (pend_at regs pc mem rom) model (getr regs 17) (IA + unit) (inr tt)
ef md (fun _ => []) Hh eq_refl).
+ intros [[e He] | []]; unfold ef, md; cbn [proj1_sig]; apply Hchk.
* left. exists e. auto.
* right. auto.
+ intros [[e He] | []]; unfold md; [exact Hh | exact Hh1].
+ intros [[e He] | []]; unfold md; [exact Hlz | exact Hlz1].
+ intros eff m' evs Hk. apply Hchk in Hk.
destruct Hk as [(e & He & -> & -> & ->) | (-> & -> & ->)].
* exists (inl (exist _ e He)). unfold ef, md; cbn [proj1_sig]. auto.
* exists (inr tt). unfold ef, md. auto.
+ exact (fun _ => acfg_nonspurious_no _ _ _ _ _ _ eq_refl Hna).
- intros [e He]. unfold ef, md; cbn [proj1_sig]. rewrite adv_pend. cbn [eff_ret with_copyins].
rewrite effmem_copyins_ret_only. apply HA. exact He.
- intros []. unfold ef, md. rewrite adv_pend. cbn [eff_ret with_copyins].
rewrite effmem_copyins_ret_only. exact HB.
Qed.
Lemma rz_unlink_tmp_present : forall regs pc mem rom model p n d A B,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 35%Z ->
getr regs 10 = AT_FDCWD ->
bv_unsigned (flag32 (getr regs 12)) = 0%Z ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
path_eqb p [] = false -> path_strip_trailing_slashes p = p -> path_has_slash p = true -> tmp_name p = Some n ->
Nat.ltb NAME_MAX (length n) = false ->
fs_under (m_fs model) p = false ->
fs_lookup (m_fs model) p = Some d ->
fd_names_path (m_fds model) p = false ->
(forall e, In e unlinkat_errnos ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model) A) ->
realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom)
(with_fs (fs_remove (m_fs model) p) model)) B ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) (t_alt2 A B).
Proof.
intros regs pc mem rom model p n d A B Hh Hlz Hno Hdir Hfl Hp Hpe Hstrip Hsl Htmp Hnm Hun Hfs Hfdn HA HB.
apply (rz_unlink_core regs pc mem rom model (open_copyins (pend_at regs pc mem rom)) unlinkat_errnos
(with_fs (fs_remove (m_fs model) p) model) ENOMEM A B Hh Hlz ENOMEM_in_unlinkat_errnos).
- intros eff m' evs.
rewrite (unlinkat_tmp_check_gen segs (pend_at regs pc mem rom) (getr regs 17) model p n Hno
ltac:(rewrite pend_gpr0; exact Hdir) ltac:(rewrite pend_gpr1; exact Hp) ltac:(rewrite pend_gpr2; exact Hfl)
Hpe Hstrip Hsl Htmp Hnm Hfdn eff).
rewrite Hun, Hfs. apply check_unlink_present_copyins_ok_iff.
- rewrite with_fs_halted. exact Hh.
- exact Hlz.
- exact HA.
- exact HB.
- rewrite Hno; reflexivity.
Qed.
Lemma rz_unlink_tmp_absent : forall regs pc mem rom model p n T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 35%Z ->
getr regs 10 = AT_FDCWD ->
bv_unsigned (flag32 (getr regs 12)) = 0%Z ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
path_eqb p [] = false -> path_strip_trailing_slashes p = p -> path_has_slash p = true -> tmp_name p = Some n ->
Nat.ltb NAME_MAX (length n) = false ->
fs_under (m_fs model) p = false ->
fs_lookup (m_fs model) p = None ->
fd_names_path (m_fds model) p = false ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4) mem rom) model) T ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model p n T Hh Hlz Hno Hdir Hfl Hp Hpe Hstrip Hsl Htmp Hnm Hun Hfs Hfdn Hc.
apply (rz_ret_only_copyins_silent segs regs pc mem rom model (open_copyins (pend_at regs pc mem rom))
(errno_ret ENOENT) model T Hh Hlz).
- intro eff.
rewrite (unlinkat_tmp_check_gen segs (pend_at regs pc mem rom) (getr regs 17) model p n Hno
ltac:(rewrite pend_gpr0; exact Hdir) ltac:(rewrite pend_gpr1; exact Hp) ltac:(rewrite pend_gpr2; exact Hfl)
Hpe Hstrip Hsl Htmp Hnm Hfdn eff).
rewrite Hun, Hfs. reflexivity.
- exact Hh.
- exact Hlz.
- exact Hc.
Qed.
Lemma rz_unlink_tmp_isdir : forall regs pc mem rom model p n T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 35%Z ->
getr regs 10 = AT_FDCWD ->
bv_unsigned (flag32 (getr regs 12)) = 0%Z ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
path_eqb p [] = false -> path_strip_trailing_slashes p = p -> path_has_slash p = true -> tmp_name p = Some n ->
Nat.ltb NAME_MAX (length n) = false ->
fs_under (m_fs model) p = true ->
fd_names_path (m_fds model) p = false ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem rom) model) T ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model p n T Hh Hlz Hno Hdir Hfl Hp Hpe Hstrip Hsl Htmp Hnm Hun Hfdn Hc.
apply (rz_ret_only_copyins_silent segs regs pc mem rom model (open_copyins (pend_at regs pc mem rom))
(errno_ret EISDIR) model T Hh Hlz).
- intro eff.
rewrite (unlinkat_tmp_check_gen segs (pend_at regs pc mem rom) (getr regs 17) model p n Hno
ltac:(rewrite pend_gpr0; exact Hdir) ltac:(rewrite pend_gpr1; exact Hp) ltac:(rewrite pend_gpr2; exact Hfl)
Hpe Hstrip Hsl Htmp Hnm Hfdn eff).
rewrite Hun. reflexivity.
- exact Hh.
- exact Hlz.
- exact Hc.
Qed.
Lemma tmp_name_not_dirref : forall p n, tmp_name p = Some n -> Open.path_is_dirref p = false.
Proof.
intros p n H. unfold tmp_name in H.
destruct (path_strip_prefix tmp_prefix p) as [n'|] eqn:Hs; [|discriminate].
apply path_strip_prefix_app in Hs. subst p. unfold Open.path_is_dirref.
destruct (path_eqb (tmp_prefix ++ n') dot_path) eqn:E1.
{ apply path_eqb_eq in E1. apply (f_equal (@length _)) in E1. rewrite length_app in E1. cbn in E1. lia. }
destruct (path_eqb (tmp_prefix ++ n') dotdot_path) eqn:E2; [|reflexivity].
apply path_eqb_eq in E2. apply (f_equal (@length _)) in E2. rewrite length_app in E2. cbn in E2. lia.
Qed.
Lemma openat_tmp_wr_check_gen : forall ms x8 model p n,
bv_unsigned x8 = 56%Z ->
ms_gpr ms 0 = AT_FDCWD ->
read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
path_eqb p [] = false ->
Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = wr_create_flags ->
path_has_slash p = true -> path_eqb p localtime_path = false -> path_eqb p devnull_path = false -> path_eqb p urandom_path = false ->
tmp_name p = Some n -> Nat.ltb NAME_MAX (length n) = false ->
forall eff,
check_syscall (sys_input segs ms x8) eff model
= if fs_under (m_fs model) p then check_ret_only_copyins (open_copyins ms) eff (errno_ret EISDIR) model []
else check_open_result_copyins (open_copyins ms) eff model
(fun fd => with_fds (fd_insert (m_fds model) fd (FdFileW p (Z_to_bv 64 0)))
(with_fs (fs_set (m_fs model) p []) model)).
Proof.
intros ms x8 model p n Hno Hdirfd Hpath Hpe Hfl Hsl Hlt Hdn Hur Htmp Hnm eff.
rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
rewrite (modeled_open_flags_wr _ Hfl). cbn [negb]. cbv beta iota.
unfold Prelude.check_copyins_after, Checks.Sys.Fs.Open.check_openat_body.
rewrite in_mem_si, Hpath. cbv beta iota zeta.
rewrite Hpe. cbv beta iota.
rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
unfold Checks.Sys.Fs.Open.check_openat_resolved. rewrite Hsl. cbv beta iota.
unfold Checks.Sys.Fs.Open.check_openat_sep. rewrite Hlt, Hdn, Hur, Htmp. cbv beta iota.
unfold Checks.Sys.Fs.Open.check_openat_tmp. rewrite Hnm. cbv beta iota zeta. rewrite Hfl.
rewrite Z.eqb_refl. change (wr_create_flags =? 0)%Z with false. cbv beta iota.
unfold Checks.Sys.Fs.Open.check_openat_create. rewrite (tmp_name_not_dirref p n Htmp). cbn [orb].
unfold check_create_wronly, check_open_result_copyins, check_ret_only_copyins, open_copyins.
destruct (fs_under (m_fs model) p).
- destruct (check_ret_only (clear_copyins eff) (errno_ret EISDIR) model []) eqn:Hr;
[reflexivity | unfold check_copyins; destruct (access_ranges_eqb _ _); reflexivity | exfalso; now apply check_ret_only_no_unmodeled in Hr].
- destruct (check_open_result (clear_copyins eff) model
(fun fd : word => with_fds (fd_insert (m_fds model) fd (FdFileW p (Z_to_bv 64 0))) (with_fs (fs_set (m_fs model) p []) model)))
eqn:Hresult.
+ reflexivity.
+ reflexivity.
+ exfalso. now apply check_open_result_never_unmodeled in Hresult.
Qed.
Lemma rz_openat_tmp_create : forall regs pc mem rom model p n A B,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 56%Z ->
getr regs 10 = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = wr_create_flags ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
path_eqb p [] = false ->
path_has_slash p = true -> path_eqb p localtime_path = false -> path_eqb p devnull_path = false -> path_eqb p urandom_path = false ->
tmp_name p = Some n -> Nat.ltb NAME_MAX (length n) = false ->
fs_under (m_fs model) p = false ->
fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
(forall e, In e openat_errnos ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model) A) ->
realizes segs (mkCfg (mkst (regupd regs 10 (alloc_fd (m_fds model))) (v_addi pc 4) mem rom)
(with_fds (fd_insert (m_fds model) (alloc_fd (m_fds model)) (FdFileW p (Z_to_bv 64 0)))
(with_fs (fs_set (m_fs model) p []) model))) B ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) (t_alt2 A B).
Proof.
intros regs pc mem rom model p n A B Hh Hlz Hno Hdir Hfl Hp Hpe Hsl Hlt Hdn Hur Htmp Hnm Hun Hfree HA HB.
apply (rz_open_core segs regs pc mem rom model (open_copyins (pend_at regs pc mem rom))
(fun fd => with_fds (fd_insert (m_fds model) fd (FdFileW p (Z_to_bv 64 0))) (with_fs (fs_set (m_fs model) p []) model))
A B Hh Hlz).
- intro eff.
rewrite (openat_tmp_wr_check_gen (pend_at regs pc mem rom) (getr regs 17) model p n Hno
ltac:(rewrite pend_gpr0; exact Hdir) ltac:(rewrite pend_gpr1; exact Hp) Hpe ltac:(rewrite pend_gpr2; exact Hfl)
Hsl Hlt Hdn Hur Htmp Hnm eff).
rewrite Hun. reflexivity.
- intro fd. rewrite with_fds_halted, with_fs_halted. exact Hh.
- intro fd. exact Hlz.
- exact Hfree.
- exact HA.
- exact HB.
- rewrite Hno; reflexivity.
Qed.
Lemma rz_open_core_full : forall regs pc mem rom model reads (mk : word -> Model) T,
m_halted model = None -> m_vm_lazy model = [] ->
(forall eff, check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_open_result_copyins reads eff model mk) ->
fd_lookup (m_fds model) (alloc_fd (m_fds model)) <> None ->
(forall e, In e openat_errnos ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model) T) ->
alloc_no_b (bv_unsigned (getr regs 17)) = false ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model reads mk T Hh Hlz Hchk Hocc HA Hna.
pose (IA := {e : Z | In e openat_errnos}).
pose (ef := fun i : IA => with_copyins reads (mkEffect (errno_ret (proj1_sig i)) [] [])).
apply (rz_silent segs (mkCfg (pend_at regs pc mem rom) model) IA (exist _ ENOMEM ENOMEM_in_openat_errnos)
(fun i => mkCfg (advance_past_svc (apply_effect (pend_at regs pc mem rom) (ef i))) model)).
- apply (node_chk segs (pend_at regs pc mem rom) model (getr regs 17) IA (exist _ ENOMEM ENOMEM_in_openat_errnos)
ef (fun _ => model) (fun _ => []) Hh eq_refl).
+ intros [e He]; unfold ef; cbn [proj1_sig]. rewrite Hchk. apply check_open_result_copyins_ok_iff. left. exists e. auto.
+ intros _; exact Hh.
+ intros _; exact Hlz.
+ intros eff m' evs Hk. rewrite Hchk in Hk. apply check_open_result_copyins_ok_iff in Hk.
destruct Hk as [(e & He & -> & -> & ->) | (fd & Hfree & Efd & _ & _ & _)].
* exists (exist _ e He). unfold ef; cbn [proj1_sig]. auto.
* exfalso. apply Hocc. rewrite <- Efd. exact Hfree.
+ exact (fun _ => acfg_nonspurious_no _ _ _ _ _ _ eq_refl Hna).
- intros [e He]. unfold ef; cbn [proj1_sig]. rewrite adv_pend. cbn [eff_ret with_copyins].
rewrite effmem_copyins_ret_only. apply HA. exact He.
Qed.
Lemma rz_openat_tmp_create_full : forall regs pc mem rom model p n T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 56%Z ->
getr regs 10 = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = wr_create_flags ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
path_eqb p [] = false ->
path_has_slash p = true -> path_eqb p localtime_path = false -> path_eqb p devnull_path = false -> path_eqb p urandom_path = false ->
tmp_name p = Some n -> Nat.ltb NAME_MAX (length n) = false ->
fs_under (m_fs model) p = false ->
fd_lookup (m_fds model) (alloc_fd (m_fds model)) <> None ->
(forall e, In e openat_errnos ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model) T) ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model p n T Hh Hlz Hno Hdir Hfl Hp Hpe Hsl Hlt Hdn Hur Htmp Hnm Hun Hocc HA.
apply (rz_open_core_full regs pc mem rom model (open_copyins (pend_at regs pc mem rom))
(fun fd => with_fds (fd_insert (m_fds model) fd (FdFileW p (Z_to_bv 64 0))) (with_fs (fs_set (m_fs model) p []) model))
T Hh Hlz).
- intro eff.
rewrite (openat_tmp_wr_check_gen (pend_at regs pc mem rom) (getr regs 17) model p n Hno
ltac:(rewrite pend_gpr0; exact Hdir) ltac:(rewrite pend_gpr1; exact Hp) Hpe ltac:(rewrite pend_gpr2; exact Hfl)
Hsl Hlt Hdn Hur Htmp Hnm eff).
rewrite Hun. reflexivity.
- exact Hocc.
- exact HA.
- rewrite Hno; reflexivity.
Qed.
Lemma rz_openat_tmp_isdir : forall regs pc mem rom model p n T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 56%Z ->
getr regs 10 = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = wr_create_flags ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
path_eqb p [] = false ->
path_has_slash p = true -> path_eqb p localtime_path = false -> path_eqb p devnull_path = false -> path_eqb p urandom_path = false ->
tmp_name p = Some n -> Nat.ltb NAME_MAX (length n) = false ->
fs_under (m_fs model) p = true ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem rom) model) T ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model p n T Hh Hlz Hno Hdir Hfl Hp Hpe Hsl Hlt Hdn Hur Htmp Hnm Hun Hc.
apply (rz_ret_only_copyins_silent segs regs pc mem rom model (open_copyins (pend_at regs pc mem rom))
(errno_ret EISDIR) model T Hh Hlz).
- intro eff.
rewrite (openat_tmp_wr_check_gen (pend_at regs pc mem rom) (getr regs 17) model p n Hno
ltac:(rewrite pend_gpr0; exact Hdir) ltac:(rewrite pend_gpr1; exact Hp) Hpe ltac:(rewrite pend_gpr2; exact Hfl)
Hsl Hlt Hdn Hur Htmp Hnm eff).
rewrite Hun. reflexivity.
- exact Hh.
- exact Hlz.
- exact Hc.
Qed.
Lemma writev_file_chk_canon : forall regs pc mem rom model fd p off data iovs bs,
bv_unsigned (getr regs 17) = 66%Z ->
fd_lookup (m_fds model) fd = Some (FdFileW p off) -> fd32 fd = fd -> getr regs 10 = fd ->
w_is0 (iovcnt32 (getr regs 12)) = false ->
(bv_unsigned (getr regs 12) <= IOV_MAX)%Z ->
copy_iovecs_aux (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11)
(word_to_nat (iovcnt32 (getr regs 12))) = ImpOk iovs ->
access_okb (getr regs 11) (16 * bv_unsigned (getr regs 12)) = true ->
iovs_access_okb iovs = true ->
gather_iovecs (ms_read_byte (pend_at regs pc mem rom)) iovs = Some bs ->
(iovs_total iovs <= MAX_RW_COUNT)%Z ->
(1 <= length bs)%nat ->
fs_lookup (m_fs model) p = Some data ->
(bv_unsigned off + iovs_total iovs <= 2 ^ 63 - 1)%Z ->
(bv_unsigned off <= Z.of_nat (length data) + rw_bytes_max)%Z ->
forall eff,
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_ret_only_copyins
(writev_copyins (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) (getr regs 12) iovs (length bs))
eff (len_word bs)
(with_fds (fd_insert (m_fds model) fd (FdFileW p (off + len_word bs)))
(with_fs (fs_set (m_fs model) p (file_write data off bs)) model))
[].
Proof.
intros regs pc mem rom model fd p off data iovs bs Hno Hlk H32 Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb Hfs Hpos Hgap eff.
pose proof (gather_iovecs_length _ _ _ Hg) as Hlen.
assert (HMv : MAX_RW_COUNT = 0x7ffff000%Z) by reflexivity.
assert (Hiov : (IOV_MAX <? bv_unsigned (getr regs 12))%Z = false) by (apply Z.ltb_ge; lia).
assert (E32 : iovcnt32 (getr regs 12) = getr regs 12)
by (apply iovcnt32_small; unfold IOV_MAX in Hmax; lia).
rewrite E32 in Hcnt, Himp.
assert (Himp' : import_iovecs (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) (getr regs 12) = ImpOk iovs).
{ unfold import_iovecs.
destruct (bv_eqb (getr regs 12) (Z_to_bv 64 1)) eqn:E1.
- apply bv_eqb_eq in E1. rewrite E1 in Himp, Hiok.
change (16 * bv_unsigned (Z_to_bv 64 1))%Z with 16%Z in Hiok. rewrite Hiok. cbn [negb].
change (word_to_nat (Z_to_bv 64 1)) with 1%nat in Himp. cbn [copy_iovecs_aux] in Himp.
destruct (read_iovec_entry (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11)) as [base len| |] eqn:Er;
try discriminate.
injection Himp as <-. cbn [iovs_access_okb forallb fst snd] in Hbok. rewrite andb_true_r in Hbok.
cbn [iovs_total] in Htot.
rewrite Z.min_l by lia. rewrite Hbok. reflexivity.
- destruct (bv_eqb (getr regs 12) (Z_to_bv 64 0)) eqn:E0.
+ apply bv_eqb_eq in E0. rewrite E0 in Hcnt. discriminate.
+ rewrite Hiov, Hiok. cbn [negb]. rewrite Himp, Hbok. reflexivity. }
rewrite chk66 by exact Hno. rewrite Hfd, H32. unfold check_writev.
rewrite ?E32, Hlk, si_mem, Himp'.
rewrite cap_iovecs_id by lia. cbv zeta.
replace (iovs_total iovs =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
unfold rw_pos_einvalb. replace (2 ^ 63 - 1 <? bv_unsigned off + iovs_total iovs)%Z with false by (symmetry; apply Z.ltb_ge; lia).
unfold writev_gathered. rewrite cap_iovecs_id by lia. rewrite (gather_prefix_full _ _ _ Hg).
replace (Nat.eqb (length bs) 0) with false by (symmetry; apply Nat.eqb_neq; lia).
rewrite Hfs. rewrite (file_gap_in_range data off bs Hgap).
assert (Herr : addr_is_error_b (len_word bs) = false).
{ unfold addr_is_error_b. apply Z.ltb_ge. rewrite len_word_unsigned; unfold two_pow_64; lia. }
rewrite Herr. unfold writev_copyins. rewrite ?E32. reflexivity.
Qed.
Lemma rz_writev_file : forall regs pc mem rom model fd p off data iovs bs T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 66%Z ->
fd_lookup (m_fds model) fd = Some (FdFileW p off) -> fd32 fd = fd -> getr regs 10 = fd ->
w_is0 (iovcnt32 (getr regs 12)) = false ->
(bv_unsigned (getr regs 12) <= IOV_MAX)%Z ->
copy_iovecs_aux (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11)
(word_to_nat (iovcnt32 (getr regs 12))) = ImpOk iovs ->
access_okb (getr regs 11) (16 * bv_unsigned (getr regs 12)) = true ->
iovs_access_okb iovs = true ->
gather_iovecs (ms_read_byte (pend_at regs pc mem rom)) iovs = Some bs ->
(iovs_total iovs <= MAX_RW_COUNT)%Z ->
(1 <= length bs)%nat ->
fs_lookup (m_fs model) p = Some data ->
(bv_unsigned off + iovs_total iovs <= 2 ^ 63 - 1)%Z ->
(bv_unsigned off <= Z.of_nat (length data) + rw_bytes_max)%Z ->
realizes segs (mkCfg (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4) mem rom)
(with_fds (fd_insert (m_fds model) fd (FdFileW p (off + len_word bs)))
(with_fs (fs_set (m_fs model) p (file_write data off bs)) model))) T ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model fd p off data iovs bs T Hh Hlz Hno Hlk H32 Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb Hfs Hpos Hgap Hc.
apply (rz_ret_only_copyins_silent segs regs pc mem rom model
(writev_copyins (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) (getr regs 12) iovs (length bs))
(len_word bs)
(with_fds (fd_insert (m_fds model) fd (FdFileW p (off + len_word bs)))
(with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) T Hh Hlz).
- intro eff. exact (writev_file_chk_canon regs pc mem rom model fd p off data iovs bs Hno Hlk H32 Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb Hfs Hpos Hgap eff).
- rewrite with_fds_halted, with_fs_halted. exact Hh.
- exact Hlz.
- exact Hc.
Qed.
Lemma rz_writev_file2 : forall regs pc mem rom model fd p off data (b0 l0 b1 l1 : word) bs0 bs1 T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 66%Z ->
fd_lookup (m_fds model) fd = Some (FdFileW p off) -> fd32 fd = fd ->
getr regs 10 = fd ->
getr regs 12 = Z_to_bv 64 2 ->
ms_read_u64 (pend_at regs pc mem rom) (getr regs 11) = Some b0 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 8)) = Some l0 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 16)) = Some b1 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 24)) = Some l1 ->
ms_read_bytes (pend_at regs pc mem rom) b0 l0 = Some bs0 ->
ms_read_bytes (pend_at regs pc mem rom) b1 l1 = Some bs1 ->
access_okb (getr regs 11) 32 = true ->
access_okb b0 (bv_unsigned l0) = true -> access_okb b1 (bv_unsigned l1) = true ->
(1 <= bv_unsigned l0 + bv_unsigned l1 <= MAX_RW_COUNT)%Z ->
fs_lookup (m_fs model) p = Some data ->
(bv_unsigned off + (bv_unsigned l0 + bv_unsigned l1) <= 2 ^ 63 - 1)%Z ->
(bv_unsigned off <= Z.of_nat (length data) + rw_bytes_max)%Z ->
realizes segs (mkCfg (mkst (regupd regs 10 (len_word (bs0 ++ bs1))) (v_addi pc 4) mem rom)
(with_fds (fd_insert (m_fds model) fd (FdFileW p (off + len_word (bs0 ++ bs1))))
(with_fs (fs_set (m_fs model) p (file_write data off (bs0 ++ bs1))) model))) T ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model fd p off data b0 l0 b1 l1 bs0 bs1 T
Hh Hlz Hno Hlk H32 Hfd Hcnt Hb0 Hl0 Hb1 Hl1 Hbs0 Hbs1 Hiok Hok0 Hok1 Htot Hfs Hpos Hgap Hc.
rewrite <- read_bytes_map_read_byte in Hbs0, Hbs1.
pose proof (gather_iovecs_2 _ _ _ _ _ _ _ Hbs0 Hbs1) as Hg.
pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. cbn [iovs_total] in Hlen.
pose proof (read_bytes_map_length _ _ _ _ Hbs0). pose proof (read_bytes_map_length _ _ _ _ Hbs1).
unfold MAX_RW_COUNT in Htot.
eapply (rz_writev_file regs pc mem rom model fd p off data [(b0, l0); (b1, l1)] (bs0 ++ bs1) T Hh Hlz Hno Hlk H32 Hfd).
- rewrite Hcnt. reflexivity.
- rewrite Hcnt. cbv. discriminate.
- rewrite Hcnt. change (word_to_nat (iovcnt32 (Z_to_bv 64 2))) with 2%nat.
apply copy_iovecs_2; try assumption; lia.
- rewrite Hcnt. exact Hiok.
- cbn [iovs_access_okb forallb fst snd]. rewrite Hok0, Hok1. reflexivity.
- exact Hg.
- cbn [iovs_total]. unfold MAX_RW_COUNT. lia.
- lia.
- exact Hfs.
- cbn [iovs_total]. lia.
- exact Hgap.
- exact Hc.
Qed.
Lemma rz_writev_file1 : forall regs pc mem rom model fd p off data (b0 l0 : word) bs0 T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 66%Z ->
fd_lookup (m_fds model) fd = Some (FdFileW p off) -> fd32 fd = fd ->
getr regs 10 = fd ->
getr regs 12 = Z_to_bv 64 1 ->
ms_read_u64 (pend_at regs pc mem rom) (getr regs 11) = Some b0 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 8)) = Some l0 ->
ms_read_bytes (pend_at regs pc mem rom) b0 l0 = Some bs0 ->
access_okb (getr regs 11) 16 = true ->
access_okb b0 (bv_unsigned l0) = true ->
(1 <= bv_unsigned l0 <= MAX_RW_COUNT)%Z ->
fs_lookup (m_fs model) p = Some data ->
(bv_unsigned off + bv_unsigned l0 <= 2 ^ 63 - 1)%Z ->
(bv_unsigned off <= Z.of_nat (length data) + rw_bytes_max)%Z ->
realizes segs (mkCfg (mkst (regupd regs 10 (len_word bs0)) (v_addi pc 4) mem rom)
(with_fds (fd_insert (m_fds model) fd (FdFileW p (off + len_word bs0)))
(with_fs (fs_set (m_fs model) p (file_write data off bs0)) model))) T ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model fd p off data b0 l0 bs0 T
Hh Hlz Hno Hlk H32 Hfd Hcnt Hb0 Hl0 Hbs0 Hiok Hok0 Htot Hfs Hpos Hgap Hc.
rewrite <- read_bytes_map_read_byte in Hbs0.
pose proof (gather_iovecs_1 _ _ _ _ Hbs0) as Hg.
pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. cbn [iovs_total] in Hlen.
pose proof (read_bytes_map_length _ _ _ _ Hbs0).
unfold MAX_RW_COUNT in Htot.
eapply (rz_writev_file regs pc mem rom model fd p off data [(b0, l0)] bs0 T Hh Hlz Hno Hlk H32 Hfd).
- rewrite Hcnt. reflexivity.
- rewrite Hcnt. cbv. discriminate.
- rewrite Hcnt. change (word_to_nat (iovcnt32 (Z_to_bv 64 1))) with 1%nat.
apply copy_iovecs_1; try assumption; lia.
- rewrite Hcnt. exact Hiok.
- cbn [iovs_access_okb forallb fst snd]. rewrite Hok0. reflexivity.
- exact Hg.
- cbn [iovs_total]. unfold MAX_RW_COUNT. lia.
- lia.
- exact Hfs.
- cbn [iovs_total]. lia.
- exact Hgap.
- exact Hc.
Qed.
End b.
End a.
