(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open ReadWrite.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s YK0p YK0r YP0n YP0o.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP0h YP01.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI06 YI16 YI00 YI14 YI07 YI19.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Export YI18.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma realizes_via_SR : forall segs c T, SR segs c (fun c1 => realizes segs c1 T) -> realizes segs c T.
Proof. intros segs c T H. apply (SR_realizes segs c _ T H). intros c' H'. exact H'. Qed.
Section b.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Context {SH : sink_head} {SK : sink_syms}.
Local Notation segs := (ms_segs B).
Lemma JX_unlink_node : forall regs pc mem0 STK sp0 FP L A mem md Lc Ac mdc TA TB,
journal B MR STK sp0 FP L A mem md Lc Ac mem0 mdc ->
sink_open_fp FP ->
stdio_env B mem0 ->
fd_names_path (m_fds mdc) sink_path = false ->
bv_unsigned (getr regs 17) = 35 -> getr regs 10 = AT_FDCWD -> bv_unsigned (flag32 (getr regs 12)) = 0 ->
getr regs 11 = Z_to_bv 64 sk_path_addr ->
(forall e, In e unlink_tmp_errnos ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem0 (seg_rom segs)) mdc) TA) ->
(forall md', journal B MR STK sp0 FP L A mem md Lc Ac mem0 md' ->
m_fds md' = m_fds mdc -> m_fs md' = fs_remove (m_fs mdc) sink_path -> fs_lookup (m_fs mdc) sink_path <> None ->
realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem0 (seg_rom segs)) md') TB) ->
realizes segs (mkCfg (pend_at regs pc mem0 (seg_rom segs)) mdc) (unlink_shape (m_fs mdc) TA TB).
Proof.
intros regs pc mem0 STK sp0 FP L A mem md Lc Ac mdc TA TB HJ Hfp Henv Hfdn Hno Hdir Hfl Hpath HA HB.
destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
destruct sink_path_facts as (F1 & F2 & F3 & _ & _ & _ & F7 & F8). rewrite <- sink_path_eq in F1, F2, F3, F7.
pose proof (stdio_env_path B regs pc mem0 Henv) as Hcstr. rewrite <- Hpath in Hcstr.
unfold unlink_shape.
destruct (fs_under (m_fs mdc) sink_path) eqn:Hun.
{ apply (rz_unlink_tmp_isdir segs regs pc mem0 (seg_rom segs) mdc sink_path sink_name_bytes TA Hh Hlz Hno Hdir Hfl Hcstr F1 F2 F3 F7 F8 Hun Hfdn).
apply HA. left. reflexivity. }
destruct (fs_lookup (m_fs mdc) sink_path) as [d|] eqn:Hlk.
- apply (rz_unlink_tmp_present segs regs pc mem0 (seg_rom segs) mdc sink_path sink_name_bytes d TA TB Hh Hlz Hno Hdir Hfl Hcstr F1 F2 F3 F7 F8 Hun Hlk Hfdn).
+ intros e He. apply HA. right. right. exact He.
+ apply HB.
* rewrite with_fs_os_upd. apply (journal_os_upd B MR LAWS); [exact HJ | exact Hfp | apply fds_rel_refl | | apply fs_remove_sorted].
intros p Hp. apply fs_lookup_remove_other. exact Hp.
* rewrite with_fs_os_upd. reflexivity.
* rewrite with_fs_os_upd. reflexivity.
* congruence.
- apply (rz_unlink_tmp_absent segs regs pc mem0 (seg_rom segs) mdc sink_path sink_name_bytes TA Hh Hlz Hno Hdir Hfl Hcstr F1 F2 F3 F7 F8 Hun Hlk Hfdn).
apply HA. right. left. reflexivity.
Qed.
Lemma JX_openat_node : forall regs pc mem0 STK sp0 FP L A mem md Lc Ac mdc TA TB,
journal B MR STK sp0 FP L A mem md Lc Ac mem0 mdc ->
sink_open_fp FP ->
stdio_env B mem0 ->
fd_lookup (m_fds mdc) (alloc_fd (m_fds mdc)) = None ->
bv_unsigned (getr regs 17) = 56 -> getr regs 10 = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = wr_create_flags ->
getr regs 11 = Z_to_bv 64 sk_path_addr ->
(forall e, In e open_tmp_errnos ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem0 (seg_rom segs)) mdc) TA) ->
(forall (fd : Z) md', journal B MR STK sp0 FP L A mem md Lc Ac mem0 md' ->
0 <= fd <= 4096 -> fd_lookup (m_fds mdc) (Z_to_bv 64 fd) = None ->
m_fds md' = fd_insert (m_fds mdc) (Z_to_bv 64 fd) (FdFileW sink_path (Z_to_bv 64 0)) ->
m_fs md' = fs_set (m_fs mdc) sink_path [] ->
realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 fd)) (v_addi pc 4) mem0 (seg_rom segs)) md') TB) ->
realizes segs (mkCfg (pend_at regs pc mem0 (seg_rom segs)) mdc) (openat_shape (m_fs mdc) TA TB).
Proof.
intros regs pc mem0 STK sp0 FP L A mem md Lc Ac mdc TA TB HJ Hfp Henv Hfree Hno Hdir Hfl Hpath HA HB.
destruct (heap_model B MR LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _).
destruct sink_path_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8). rewrite <- sink_path_eq in F1, F2, F3, F4, F5, F6, F7.
pose proof (stdio_env_path B regs pc mem0 Henv) as Hcstr. rewrite <- Hpath in Hcstr.
unfold openat_shape.
destruct (fs_under (m_fs mdc) sink_path) eqn:Hun.
{ apply (rz_openat_tmp_isdir segs regs pc mem0 (seg_rom segs) mdc sink_path sink_name_bytes TA Hh Hlz Hno Hdir Hfl Hcstr F1 F3 F4 F5 F6 F7 F8 Hun).
apply HA. left. reflexivity. }
apply (rz_openat_tmp_create segs regs pc mem0 (seg_rom segs) mdc sink_path sink_name_bytes TA TB Hh Hlz Hno Hdir Hfl Hcstr F1 F3 F4 F5 F6 F7 F8 Hun Hfree).
- intros e He. apply HA. right. exact He.
- pose proof (Checks.Sys.Fs.Open.alloc_fd_le (m_fds mdc)) as Hle. pose proof (u64_range (alloc_fd (m_fds mdc))) as Hr0.
set (fdw := alloc_fd (m_fds mdc)) in *.
rewrite <- (Z_to_bv_bv_unsigned 64 fdw). apply HB.
+ rewrite (with_fs_os_upd (fs_set (m_fs mdc) sink_path []) mdc). rewrite with_fds_os_upd. rewrite os_upd_twice.
rewrite os_upd_fs, os_upd_vmmaps, os_upd_statpins.
apply (journal_os_upd B MR LAWS); [exact HJ | exact Hfp | | | apply fs_set_sorted].
* intros fd'. rewrite Z_to_bv_bv_unsigned. destruct (bv_eqb fdw fd') eqn:E.
-- apply bv_eqb_eq in E. subst fd'. right. split; [left; exact Hfree|].
right. eexists. unfold fd_insert. cbn [fd_lookup fst]. rewrite (proj2 (bv_eqb_eq _ _) eq_refl). reflexivity.
-- left. unfold fd_insert. cbn [fd_lookup fst].
rewrite E. fold (fd_remove (m_fds mdc) fdw). apply fd_lookup_remove_neq.
intros ->. rewrite (proj2 (bv_eqb_eq _ _) eq_refl) in E. discriminate E.
* intros p Hp. apply fs_lookup_set_other. exact Hp.
+ lia.
+ rewrite Z_to_bv_bv_unsigned. exact Hfree.
+ rewrite Z_to_bv_bv_unsigned, (with_fs_os_upd (fs_set (m_fs mdc) sink_path []) mdc), with_fds_os_upd, os_upd_twice, os_upd_fds. reflexivity.
+ rewrite (with_fs_os_upd (fs_set (m_fs mdc) sink_path []) mdc), with_fds_os_upd, os_upd_twice, os_upd_fs, os_upd_fs. reflexivity.
Qed.
End b.
End a.
