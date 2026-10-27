(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0q.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL07.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variables (sp brk mbase tid : word) (lim : Z) (a0 path : list byte) (inp : ProcInput) (rnd : EntryDraw).
Hypothesis Hargv : in_argv inp = [a0; path].
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv [a0; path].
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Htid : 0 < bv_unsigned tid < 4194304.
Hypothesis Hfits : entry_stack_fits sp [a0; path] (in_envp inp).
Hypothesis HCO : cannot_open_hyp.
Lemma open_prefix : forall ms T,
st_ok src0segs (E_main sp [a0; path] (in_envp inp) tid rnd) ss_main_t ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp [a0; path] (in_envp inp) rnd) ->
(forall regs mem,
regs_ok (E_main sp [a0; path] (in_envp inp) tid rnd) (ss_regs ss_open) regs ->
mem_ok src0segs (E_main sp [a0; path] (in_envp inp) tid rnd) mem (ss_mem ss_open) ->
facts_ok (E_main sp [a0; path] (in_envp inp) tid rnd) (ss_facts ss_open) ->
runs_at (bv_unsigned sp) mem (runs_main true sp [a0; path] (in_envp inp) rnd) ->
bv_unsigned (getr regs 17%bv) = 56 ->
getr regs 10%bv = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12%bv)) open_ignored_flags = 0 ->
modeled_open_flags (getr regs 12%bv) = true ->
getr regs 11%bv = Z_to_bv 64 (z_argv (bv_unsigned sp) [a0; path] (in_envp inp) 1) ->
rdn src0segs mem (Z_to_bv 64 (z_argv (bv_unsigned sp) [a0; path] (in_envp inp) 1)) (length (path ++ [NUL])) = Some (path ++ [NUL]) ->
realizes src0segs (mkCfg (pend_at regs (Z_to_bv 64 (ss_pc ss_open)) mem (seg_rom src0segs)) (MD0 tid brk mbase sp lim inp)) T) ->
realizes src0segs (mkCfg ms (MD0 tid brk mbase sp lim inp)) T.
Proof.
intros ms T HS0 HR K.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp) = []) by reflexivity.
pose proof (st_ok_drv true _ ms HS0) as HS. change (ss_drv true) with ss_drv_t in HS. clear HS0.
pose proof (ew2' sp [a0; path] (in_envp inp) Hsp Hva Hve (xw_main sp [a0; path] (in_envp inp) tid rnd) (xd_main rnd) ltac:(cbn; lia)) as H2.
change (E0 _ _ _ _ _) with (E_main sp [a0; path] (in_envp inp) tid rnd) in H2.
apply (st_ok_add_cond src0segs _ _ _ BC_EQ (SOff 3 0) (SLit 2)) in HS; [ sym_norm HS | vm_compute; reflexivity ].
sym_run_with src0tbl_ok HS.
lazymatch type of HS with st_ok_ecall _ _ _ ?msx =>
change (st_ok_ecall src0segs (E_main sp [a0; path] (in_envp inp) tid rnd) ss_open msx) in HS end.
sym_ecall_open HS.
repeat match goal with H : runs_at _ (ms_mem (pend_at _ _ _ _)) _ |- _ => cbn [ms_mem pend_at] in H end.
lazymatch goal with |- realizes _ (mkCfg (pend_at ?regs _ ?mem _) _) _ => apply (K regs mem Hregs Hmem HG HR) end.
- rewrite (Hregs (17%bv:reg)); eval_sr_get; cbn [sv_denot]. reflexivity.
- rewrite (Hregs (10%bv:reg)); eval_sr_get; cbn [sv_denot]. apply bv_eq. vm_compute. reflexivity.
- rewrite (Hregs (12%bv:reg)); eval_sr_get; cbn [sv_denot]. vm_compute. reflexivity.
- rewrite (Hregs (12%bv:reg)); eval_sr_get; cbn [sv_denot]. vm_compute. reflexivity.
- rewrite (Hregs (11%bv:reg)); eval_sr_get; cbn [sv_denot]. rewrite Z.add_0_r, H2. reflexivity.
- pose proof (runs_at_nth _ mem _ 2 _ _ HR eq_refl) as Hb. exact (bytes_at_rdn src0segs mem _ _ Hb).
Qed.
Lemma errno_branch : forall regs mem e,
regs_ok (E_main sp [a0; path] (in_envp inp) tid rnd) (ss_regs ss_open) regs ->
mem_ok src0segs (E_main sp [a0; path] (in_envp inp) tid rnd) mem (ss_mem ss_open) ->
facts_ok (E_main sp [a0; path] (in_envp inp) tid rnd) (ss_facts ss_open) ->
runs_at (bv_unsigned sp) mem (runs_main true sp [a0; path] (in_envp inp) rnd) ->
0 < e < 4096 ->
realizes src0segs
(mkCfg (mkst (regupd regs 10%bv (errno_ret e)) (v_addi (Z_to_bv 64 (ss_pc ss_open)) 4) mem (seg_rom src0segs)) (MD0 tid brk mbase sp lim inp))
(diag (msg_cannot_open path) (in_fs inp)).
Proof.
intros regs mem e Hregs Hmem HG HR He.
rewrite <- (MD0_fs tid brk mbase sp lim inp).
apply (HCO sp a0 path (in_envp inp) tid rnd regs mem _ e Hsp Hva Hve Hfits Htid Hregs Hmem HG HR); [reflexivity | reflexivity | | exact He].
split; [| reflexivity]. rewrite MD0_fds. reflexivity.
Qed.
Lemma openat_errnos_small : forall e, In e openat_errnos -> 0 < e < 4096.
Proof.
intros e H. unfold openat_errnos in H. cbn in H.
unfold ENOMEM, EACCES, EMFILE, ENFILE in H.
destruct H as [<-|[<-|[<-|[<-|[]]]]]; lia.
Qed.
Theorem src0_open_file : forall ms data,
(length path < 4096)%nat -> path <> [] -> openat_plain_name path = true ->
fs_lookup (in_fs inp) path = Some data ->
st_ok src0segs (E_main sp [a0; path] (in_envp inp) tid rnd) ss_main_t ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp [a0; path] (in_envp inp) rnd) ->
forall T,
(forall ms1, st_ok src0segs (E_main sp [a0; path] (in_envp inp) tid rnd) ss_m1 ms1 ->
runs_at (bv_unsigned sp) (ms_mem ms1) (runs_main true sp [a0; path] (in_envp inp) rnd) ->
realizes src0segs (mkCfg ms1 (MD_file path tid brk mbase sp lim inp)) T) ->
realizes src0segs (mkCfg ms (MD0 tid brk mbase sp lim inp)) (t_alt2 (diag (msg_cannot_open path) (in_fs inp)) T).
Proof.
intros ms data Hlen Hne Hnd Hlk HS0 HR0 T K.
apply (open_prefix ms _ HS0 HR0). intros regs mem Hregs Hmem HG HR H17 H10 H12 H12' H11 Hrd.
pose proof (argv_no_nul [a0; path] Hva 1 ltac:(cbn; lia)) as Hnul1. cbn [nth] in Hnul1.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp) = []) by reflexivity.
eapply (rz_openat_file src0segs regs _ mem (seg_rom src0segs) _ path data _ _ Hh Hlz H17 H10 H12).
- rewrite pend_read_byte_mrb, H11. apply (read_cstr_of_rdn src0segs mem _ path); [lia | exact Hnul1 |].
replace (length path + 1)%nat with (length (path ++ [NUL])) by (rewrite length_app; cbn; lia). exact Hrd.
- exact Hne.
- exact Hnd.
- rewrite MD0_fs. exact Hlk.
- rewrite MD0_fds, alloc_fd_std3. apply fd_lookup_std3.
- intros e He. apply (errno_branch regs mem e Hregs Hmem HG HR (openat_errnos_small e He)).
- rewrite MD0_fds, alloc_fd_std3. rewrite <- (MD0_fds tid brk mbase sp lim inp). fold (MD_file path tid brk mbase sp lim inp).
assert (Hh1 : m_halted (MD_file path tid brk mbase sp lim inp) = None) by reflexivity.
assert (Hlz1 : m_vm_lazy (MD_file path tid brk mbase sp lim inp) = []) by reflexivity.
resume_sv src0segs (SLit 3). { reflexivity. }
let pc := eval vm_compute in src0_A_malloc in sym_run_to_with src0tbl_ok HS pc.
lazymatch type of HS with st_ok _ _ _ ?msx =>
change (st_ok src0segs (E_main sp [a0; path] (in_envp inp) tid rnd) ss_m1 msx) in HS;
exact (K msx HS HR) end.
Qed.
Theorem src0_open_dir : forall ms,
path = dot_path ->
st_ok src0segs (E_main sp [a0; path] (in_envp inp) tid rnd) ss_main_t ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp [a0; path] (in_envp inp) rnd) ->
forall T,
(forall ms1, st_ok src0segs (E_main sp [a0; path] (in_envp inp) tid rnd) ss_m1 ms1 ->
runs_at (bv_unsigned sp) (ms_mem ms1) (runs_main true sp [a0; path] (in_envp inp) rnd) ->
realizes src0segs (mkCfg ms1 (MD_dir tid brk mbase sp lim inp)) T) ->
realizes src0segs (mkCfg ms (MD0 tid brk mbase sp lim inp)) (t_alt2 (diag (msg_cannot_open path) (in_fs inp)) T).
Proof.
intros ms Hdot HS0 HR0 T K.
apply (open_prefix ms _ HS0 HR0). intros regs mem Hregs Hmem HG HR H17 H10 H12 H12' H11 Hrd.
pose proof (argv_no_nul [a0; path] Hva 1 ltac:(cbn; lia)) as Hnul1. cbn [nth] in Hnul1.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp) = []) by reflexivity.
eapply (rz_openat_dir src0segs regs _ mem (seg_rom src0segs) _ _ _ Hh Hlz H17 H10 H12).
- rewrite pend_read_byte_mrb, H11, <- Hdot. apply (read_cstr_of_rdn src0segs mem _ path); [rewrite Hdot; cbn; lia | exact Hnul1 |].
replace (length path + 1)%nat with (length (path ++ [NUL])) by (rewrite length_app; cbn; lia). exact Hrd.
- rewrite MD0_fds, alloc_fd_std3. apply fd_lookup_std3.
- intros e He. apply (errno_branch regs mem e Hregs Hmem HG HR (openat_errnos_small e He)).
- rewrite MD0_fds, alloc_fd_std3. rewrite <- (MD0_fds tid brk mbase sp lim inp). fold (MD_dir tid brk mbase sp lim inp).
assert (Hh1 : m_halted (MD_dir tid brk mbase sp lim inp) = None) by reflexivity.
assert (Hlz1 : m_vm_lazy (MD_dir tid brk mbase sp lim inp) = []) by reflexivity.
resume_sv src0segs (SLit 3). { reflexivity. }
let pc := eval vm_compute in src0_A_malloc in sym_run_to_with src0tbl_ok HS pc.
lazymatch type of HS with st_ok _ _ _ ?msx =>
change (st_ok src0segs (E_main sp [a0; path] (in_envp inp) tid rnd) ss_m1 msx) in HS;
exact (K msx HS HR) end.
Qed.
Theorem src0_open_empty : forall ms,
path = [] ->
st_ok src0segs (E_main sp [a0; path] (in_envp inp) tid rnd) ss_main_t ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp [a0; path] (in_envp inp) rnd) ->
realizes src0segs (mkCfg ms (MD0 tid brk mbase sp lim inp)) (diag (msg_cannot_open path) (in_fs inp)).
Proof.
intros ms Hnil HS0 HR0.
apply (open_prefix ms _ HS0 HR0). intros regs mem Hregs Hmem HG HR H17 H10 H12 H12' H11 Hrd.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp) = []) by reflexivity.
eapply (rz_openat_empty src0segs regs _ mem (seg_rom src0segs) _ _ Hh Hlz H17 H12').
- rewrite pend_read_byte_mrb, H11. apply (read_cstr_of_rdn src0segs mem _ []); [cbn; lia | intros [] |].
rewrite Hnil in Hrd. cbn [length app Nat.add] in Hrd |- *. exact Hrd.
- apply (errno_branch regs mem ENOENT Hregs Hmem HG HR). unfold ENOENT. lia.
Qed.
Theorem src0_open_absent : forall ms,
(length path < 4096)%nat -> path <> [] -> openat_plain_name path = true ->
fs_lookup (in_fs inp) path = None ->
st_ok src0segs (E_main sp [a0; path] (in_envp inp) tid rnd) ss_main_t ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp [a0; path] (in_envp inp) rnd) ->
realizes src0segs (mkCfg ms (MD0 tid brk mbase sp lim inp)) (diag (msg_cannot_open path) (in_fs inp)).
Proof.
intros ms Hlen Hne Hnd Hlk HS0 HR0.
apply (open_prefix ms _ HS0 HR0). intros regs mem Hregs Hmem HG HR H17 H10 H12 H12' H11 Hrd.
pose proof (argv_no_nul [a0; path] Hva 1 ltac:(cbn; lia)) as Hnul1. cbn [nth] in Hnul1.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp) = []) by reflexivity.
eapply (rz_openat_absent src0segs regs _ mem (seg_rom src0segs) _ path _ Hh Hlz H17 H10 H12).
- rewrite pend_read_byte_mrb, H11. apply (read_cstr_of_rdn src0segs mem _ path); [lia | exact Hnul1 |].
replace (length path + 1)%nat with (length (path ++ [NUL])) by (rewrite length_app; cbn; lia). exact Hrd.
- exact Hne.
- exact Hnd.
- rewrite MD0_fs. exact Hlk.
- apply (errno_branch regs mem ENOENT Hregs Hmem HG HR). unfold ENOENT. lia.
Qed.
Theorem src0_open_toolong : forall ms,
(4096 <= length path)%nat ->
st_ok src0segs (E_main sp [a0; path] (in_envp inp) tid rnd) ss_main_t ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp [a0; path] (in_envp inp) rnd) ->
realizes src0segs (mkCfg ms (MD0 tid brk mbase sp lim inp)) (diag (msg_cannot_open path) (in_fs inp)).
Proof.
intros ms Hlen HS0 HR0.
apply (open_prefix ms _ HS0 HR0). intros regs mem Hregs Hmem HG HR H17 H10 H12 H12' H11 Hrd.
pose proof (argv_no_nul [a0; path] Hva 1 ltac:(cbn; lia)) as Hnul1. cbn [nth] in Hnul1.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp) = []) by reflexivity.
eapply (rz_openat_toolong src0segs regs _ mem (seg_rom src0segs) _ _ Hh Hlz H17 H12').
- rewrite pend_read_byte_mrb, H11.
assert (Hlenf : length (firstn 4096 path) = 4096%nat) by (rewrite length_firstn; lia).
apply (read_cstr_toolong_of_rdn src0segs mem _ (firstn 4096 path) Hlenf).
+ intros Hin. apply Hnul1. rewrite <- (firstn_skipn 4096 path). apply in_app_iff. left. exact Hin.
+ pose proof (rdn_firstn src0segs mem (length (path ++ [NUL])) _ (path ++ [NUL]) 4096 Hrd ltac:(rewrite length_app; cbn; lia)) as Hf.
rewrite firstn_app, (proj2 (Nat.sub_0_le _ _)) in Hf by lia. cbn [firstn] in Hf. rewrite app_nil_r in Hf.
exact Hf.
- apply (errno_branch regs mem ENAMETOOLONG Hregs Hmem HG HR). unfold ENAMETOOLONG. lia.
Qed.
End b.
End a.
