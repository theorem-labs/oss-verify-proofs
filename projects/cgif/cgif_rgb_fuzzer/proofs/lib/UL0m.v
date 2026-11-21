(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the open arms are stated over the run, with the launch premises in place of entry_stack_fits, the CONFIG_RSEQ-indexed states split on the run's flag, the models carrying the entry draw, the TASK_SIZE premise of read_cstr_of_rdn proved for argv[1], and the run's channel-reader fact for the reader conjunct of fdchan). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK0o YK0q YQ0k YN06 YN02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ0d YQ05 YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH05 UH07 UH06 UO3p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO04 YL05 YL01 UL06 YL0b UL0g UL0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variables (sp brk mbase tid : word) (lim : Z) (a0 path : list byte) (inp : ProcInput) (rnd : EntryDraw).
Hypothesis Hargv : in_argv inp = [a0; path].
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Htid : 0 < bv_unsigned tid < 4194304.
(* #38: [entry_stack_fits] no longer fixes the stack image; the launch
   premises UO3p's Section f takes stand in its place. *)
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp.
(* 727298f3: [fdchan] also asks that the channel still has a reader, which
   the initial model takes from the run ([Run.valid_input_channel_reader]). *)
Hypothesis Hcr : in_channel_reader inp = true.
Hypothesis HCO : cannot_open_hyp.
Local Notation envp := (in_envp inp) (only parsing).
Local Notation efn := (in_execfn inp) (only parsing).
Local Notation rs := (kb_rseq (in_kernel inp)) (only parsing).
(* [read_cstr_of_rdn] (YK0q.v) asks that the string end below TASK_SIZE
   (= SP_HI = 2^47), because [read_cstr] tests [access_okb] at every byte.
   Every call below reads argv[1], which [z_argv_fits] puts below SP_HI - 8. *)
Lemma argv1_bound :
0 <= z_argv (bv_unsigned (ed_top rnd)) [a0; path] envp efn 1
/\ z_argv (bv_unsigned (ed_top rnd)) [a0; path] envp efn 1 + Z.of_nat (length path) + 1 <= 2 ^ 47 - 8.
Proof.
assert (Hal : (1 < length (in_argv inp))%nat) by (rewrite Hargv; cbn; lia).
pose proof (layout_facts inp mbase sp brk rnd Hsp Hlau) as L.
pose proof (z_argv_bounds inp rnd 1 Hal) as B1.
pose proof (z_argv_fits inp mbase sp brk rnd Hsp Hlau 1 Hal) as F1.
rewrite Hargv in L, B1, F1. cbn [nth] in B1, F1.
unfold SP_LO, SP_HI in L, F1. split; lia.
Qed.
Lemma argv1_cstr_bound :
bv_unsigned (Z_to_bv 64 (z_argv (bv_unsigned (ed_top rnd)) [a0; path] envp efn 1))
+ Z.of_nat (length path) < TASK_SIZE.
Proof.
assert (HT : TASK_SIZE = 2 ^ 47) by reflexivity.
pose proof argv1_bound as (HA0 & HA1).
rewrite u_Z2bv by lia. lia.
Qed.
Lemma open_prefix : forall ms T,
st_ok ubs2segs (E_main sp inp [a0; path] envp efn tid rnd) (ss_main true rs) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp (ed_top rnd) [a0; path] envp efn rnd) ->
(forall regs mem,
regs_ok (E_main sp inp [a0; path] envp efn tid rnd) (ss_regs (ss_open rs)) regs ->
mem_ok ubs2segs (E_main sp inp [a0; path] envp efn tid rnd) mem (ss_mem (ss_open rs)) ->
facts_ok (E_main sp inp [a0; path] envp efn tid rnd) (ss_facts (ss_open rs)) ->
runs_at (bv_unsigned sp) mem (runs_main true sp (ed_top rnd) [a0; path] envp efn rnd) ->
bv_unsigned (getr regs 17%bv) = 56 ->
getr regs 10%bv = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12%bv)) open_ignored_flags = 0 ->
modeled_open_flags (getr regs 12%bv) = true ->
getr regs 11%bv = Z_to_bv 64 (z_argv (bv_unsigned (ed_top rnd)) [a0; path] envp efn 1) ->
rdn ubs2segs mem (Z_to_bv 64 (z_argv (bv_unsigned (ed_top rnd)) [a0; path] envp efn 1)) (length (path ++ [NUL])) = Some (path ++ [NUL]) ->
realizes ubs2segs (mkCfg (pend_at regs (Z_to_bv 64 (ss_pc (ss_open rs))) mem (seg_rom ubs2segs)) (MD0 tid brk mbase sp lim inp rnd)) T) ->
realizes ubs2segs (mkCfg ms (MD0 tid brk mbase sp lim inp rnd)) T.
Proof.
intros ms T HS0 HR K.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp rnd) = []) by reflexivity.
assert (H2 : bv_unsigned (ew (E_main sp inp [a0; path] envp efn tid rnd) 2)
= z_argv (bv_unsigned (ed_top rnd)) [a0; path] envp efn 1).
{ unfold E_main. rewrite <- Hargv. eapply ew2'; first [eassumption | rewrite Hargv; cbn; lia]. }
pose proof (st_ok_drv _ _ ms HS0) as HS. clear HS0.
(* the symbolic states need the flag concrete; the environment reads it
   inside and stays as it is *)
revert HS K. destruct (kb_rseq (in_kernel inp)); intros HS K; cbn [ss_drv ss_open] in HS, K |- *.
all: apply (st_ok_add_cond ubs2segs _ _ _ BC_EQ (SOff 3 0) (SLit 2)) in HS; [ sym_norm HS | vm_compute; reflexivity ].
all: sym_run_with ubs2tbl_ok HS.
all: lazymatch type of K with forall regs mem, regs_ok _ (ss_regs ?S) _ -> _ =>
lazymatch type of HS with st_ok_ecall _ _ _ ?msx =>
change (st_ok_ecall ubs2segs (E_main sp inp [a0; path] envp efn tid rnd) S msx) in HS end end.
all: sym_ecall_open HS.
all: repeat match goal with H : runs_at _ (ms_mem (pend_at _ _ _ _)) _ |- _ => cbn [ms_mem pend_at] in H end.
all: lazymatch goal with |- realizes _ (mkCfg (pend_at ?regs _ ?mem _) _) _ =>
apply (K regs mem Hregs Hmem HG HR);
[ rewrite (Hregs (17%bv:reg)); eval_sr_get; cbn [sv_denot]; reflexivity
| rewrite (Hregs (10%bv:reg)); eval_sr_get; cbn [sv_denot]; apply bv_eq; vm_compute; reflexivity
| rewrite (Hregs (12%bv:reg)); eval_sr_get; cbn [sv_denot]; vm_compute; reflexivity
| rewrite (Hregs (12%bv:reg)); eval_sr_get; cbn [sv_denot]; vm_compute; reflexivity
| rewrite (Hregs (11%bv:reg)); eval_sr_get; cbn [sv_denot]; rewrite Z.add_0_r, H2; reflexivity
| pose proof (runs_at_nth _ mem _ 2 _ _ HR eq_refl) as Hb; exact (bytes_at_rdn ubs2segs mem _ _ Hb) ] end.
Qed.
(* the K-continuation's resumed state, read off its own type so both flags
   share one tactic *)
Ltac to_m1 K HS HR :=
lazymatch type of HS with st_ok _ _ _ ?msx =>
lazymatch type of K with forall ms1, st_ok _ _ ?S ms1 -> _ =>
change (st_ok ubs2segs (E_main sp inp [a0; path] envp efn tid rnd) S msx) in HS;
exact (K msx HS HR) end end.
Lemma errno_branch : forall regs mem e,
regs_ok (E_main sp inp [a0; path] envp efn tid rnd) (ss_regs (ss_open rs)) regs ->
mem_ok ubs2segs (E_main sp inp [a0; path] envp efn tid rnd) mem (ss_mem (ss_open rs)) ->
facts_ok (E_main sp inp [a0; path] envp efn tid rnd) (ss_facts (ss_open rs)) ->
runs_at (bv_unsigned sp) mem (runs_main true sp (ed_top rnd) [a0; path] envp efn rnd) ->
0 < e < 4096 ->
realizes ubs2segs
(mkCfg (mkst (regupd regs 10%bv (errno_ret e)) (v_addi (Z_to_bv 64 (ss_pc (ss_open rs))) 4) mem (seg_rom ubs2segs)) (MD0 tid brk mbase sp lim inp rnd))
(diag (msg_cannot_open path) (in_fs inp)).
Proof.
intros regs mem e Hregs Hmem HG HR He.
destruct (open_c_ok _ _ regs mem Hregs Hmem HG) as (Hregs' & Hmem' & HG' & Hpc).
rewrite Hpc, <- (MD0_fs tid brk mbase sp lim inp rnd).
apply (HCO sp brk mbase inp a0 path tid rnd regs mem _ e Hsp Hargv Hva Hve Hvl Hlau Htid Hregs' Hmem' HG' HR);
[reflexivity | reflexivity | | exact He].
split; [| split; [reflexivity | exact Hcr]]. rewrite MD0_fds. reflexivity.
Qed.
Lemma openat_errnos_small : forall e, In e openat_errnos -> 0 < e < 4096.
Proof.
intros e H. unfold openat_errnos in H. cbn in H.
unfold ENOMEM, EACCES, EMFILE, ENFILE in H.
destruct H as [<-|[<-|[<-|[<-|[]]]]]; lia.
Qed.
Lemma argv1_no_nul : ~ In NUL path.
Proof.
pose proof (argv_no_nul inp Hva 1 ltac:(rewrite Hargv; cbn; lia)) as H.
rewrite Hargv in H. exact H.
Qed.
Theorem ubs2_open_file : forall ms data,
(length path < 4096)%nat -> path <> [] -> openat_plain_name path = true ->
fs_lookup (in_fs inp) path = Some data ->
st_ok ubs2segs (E_main sp inp [a0; path] envp efn tid rnd) (ss_main true rs) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp (ed_top rnd) [a0; path] envp efn rnd) ->
forall T,
(forall ms1, st_ok ubs2segs (E_main sp inp [a0; path] envp efn tid rnd) (ss_m1 rs) ms1 ->
runs_at (bv_unsigned sp) (ms_mem ms1) (runs_main true sp (ed_top rnd) [a0; path] envp efn rnd) ->
realizes ubs2segs (mkCfg ms1 (MD_file path tid brk mbase sp lim inp rnd)) T) ->
realizes ubs2segs (mkCfg ms (MD0 tid brk mbase sp lim inp rnd)) (t_alt2 (diag (msg_cannot_open path) (in_fs inp)) T).
Proof.
intros ms data Hlen Hne Hnd Hlk HS0 HR0 T K.
apply (open_prefix ms _ HS0 HR0). intros regs mem Hregs Hmem HG HR H17 H10 H12 H12' H11 Hrd.
pose proof argv1_no_nul as Hnul1.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp rnd) = []) by reflexivity.
eapply (rz_openat_file ubs2segs regs _ mem (seg_rom ubs2segs) _ path data _ _ Hh Hlz H17 H10 H12).
- rewrite pend_read_byte_mrb, H11.
apply (read_cstr_of_rdn ubs2segs mem _ path); [lia | exact Hnul1 | exact argv1_cstr_bound |].
replace (length path + 1)%nat with (length (path ++ [NUL])) by (rewrite length_app; cbn; lia). exact Hrd.
- exact Hne.
- exact Hnd.
- rewrite MD0_fs. exact Hlk.
- rewrite MD0_fds, alloc_fd_std3. apply fd_lookup_std3.
- intros e He. apply (errno_branch regs mem e Hregs Hmem HG HR (openat_errnos_small e He)).
- rewrite MD0_fds, alloc_fd_std3. rewrite <- (MD0_fds tid brk mbase sp lim inp rnd). fold (MD_file path tid brk mbase sp lim inp rnd).
assert (Hh1 : m_halted (MD_file path tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz1 : m_vm_lazy (MD_file path tid brk mbase sp lim inp rnd) = []) by reflexivity.
revert Hregs Hmem HG K. destruct (kb_rseq (in_kernel inp)); intros Hregs Hmem HG K; cbn [ss_open ss_m1] in Hregs, Hmem, HG, K |- *.
all: resume_sv ubs2segs (SLit 3); [ reflexivity | ].
all: let pc := eval vm_compute in ubs2_A_malloc in sym_run_to_with ubs2tbl_ok HS pc.
all: to_m1 K HS HR.
Qed.
Theorem ubs2_open_dir : forall ms,
path = dot_path ->
st_ok ubs2segs (E_main sp inp [a0; path] envp efn tid rnd) (ss_main true rs) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp (ed_top rnd) [a0; path] envp efn rnd) ->
forall T,
(forall ms1, st_ok ubs2segs (E_main sp inp [a0; path] envp efn tid rnd) (ss_m1 rs) ms1 ->
runs_at (bv_unsigned sp) (ms_mem ms1) (runs_main true sp (ed_top rnd) [a0; path] envp efn rnd) ->
realizes ubs2segs (mkCfg ms1 (MD_dir tid brk mbase sp lim inp rnd)) T) ->
realizes ubs2segs (mkCfg ms (MD0 tid brk mbase sp lim inp rnd)) (t_alt2 (diag (msg_cannot_open path) (in_fs inp)) T).
Proof.
intros ms Hdot HS0 HR0 T K.
apply (open_prefix ms _ HS0 HR0). intros regs mem Hregs Hmem HG HR H17 H10 H12 H12' H11 Hrd.
pose proof argv1_no_nul as Hnul1.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp rnd) = []) by reflexivity.
eapply (rz_openat_dir ubs2segs regs _ mem (seg_rom ubs2segs) _ _ _ Hh Hlz H17 H10 H12).
- rewrite pend_read_byte_mrb, H11.
pose proof argv1_cstr_bound as HB.
rewrite <- Hdot. apply (read_cstr_of_rdn ubs2segs mem _ path); [rewrite Hdot; cbn; lia | exact Hnul1 | exact HB |].
replace (length path + 1)%nat with (length (path ++ [NUL])) by (rewrite length_app; cbn; lia). exact Hrd.
- rewrite MD0_fds, alloc_fd_std3. apply fd_lookup_std3.
- intros e He. apply (errno_branch regs mem e Hregs Hmem HG HR (openat_errnos_small e He)).
- rewrite MD0_fds, alloc_fd_std3. rewrite <- (MD0_fds tid brk mbase sp lim inp rnd). fold (MD_dir tid brk mbase sp lim inp rnd).
assert (Hh1 : m_halted (MD_dir tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz1 : m_vm_lazy (MD_dir tid brk mbase sp lim inp rnd) = []) by reflexivity.
revert Hregs Hmem HG K. destruct (kb_rseq (in_kernel inp)); intros Hregs Hmem HG K; cbn [ss_open ss_m1] in Hregs, Hmem, HG, K |- *.
all: resume_sv ubs2segs (SLit 3); [ reflexivity | ].
all: let pc := eval vm_compute in ubs2_A_malloc in sym_run_to_with ubs2tbl_ok HS pc.
all: to_m1 K HS HR.
Qed.
Theorem ubs2_open_empty : forall ms,
path = [] ->
st_ok ubs2segs (E_main sp inp [a0; path] envp efn tid rnd) (ss_main true rs) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp (ed_top rnd) [a0; path] envp efn rnd) ->
realizes ubs2segs (mkCfg ms (MD0 tid brk mbase sp lim inp rnd)) (diag (msg_cannot_open path) (in_fs inp)).
Proof.
intros ms Hnil HS0 HR0.
apply (open_prefix ms _ HS0 HR0). intros regs mem Hregs Hmem HG HR H17 H10 H12 H12' H11 Hrd.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp rnd) = []) by reflexivity.
eapply (rz_openat_empty ubs2segs regs _ mem (seg_rom ubs2segs) _ _ Hh Hlz H17 H12').
- rewrite pend_read_byte_mrb, H11. pose proof argv1_cstr_bound as HB.
apply (read_cstr_of_rdn ubs2segs mem _ []); [cbn; lia | intros [] | cbn [length]; lia |].
rewrite Hnil in Hrd |- *. cbn [length app Nat.add] in Hrd |- *. exact Hrd.
- apply (errno_branch regs mem ENOENT Hregs Hmem HG HR). unfold ENOENT. lia.
Qed.
Theorem ubs2_open_absent : forall ms,
(length path < 4096)%nat -> path <> [] -> openat_plain_name path = true ->
fs_lookup (in_fs inp) path = None ->
st_ok ubs2segs (E_main sp inp [a0; path] envp efn tid rnd) (ss_main true rs) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp (ed_top rnd) [a0; path] envp efn rnd) ->
realizes ubs2segs (mkCfg ms (MD0 tid brk mbase sp lim inp rnd)) (diag (msg_cannot_open path) (in_fs inp)).
Proof.
intros ms Hlen Hne Hnd Hlk HS0 HR0.
apply (open_prefix ms _ HS0 HR0). intros regs mem Hregs Hmem HG HR H17 H10 H12 H12' H11 Hrd.
pose proof argv1_no_nul as Hnul1.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp rnd) = []) by reflexivity.
eapply (rz_openat_absent ubs2segs regs _ mem (seg_rom ubs2segs) _ path _ Hh Hlz H17 H10 H12).
- rewrite pend_read_byte_mrb, H11.
apply (read_cstr_of_rdn ubs2segs mem _ path); [lia | exact Hnul1 | exact argv1_cstr_bound |].
replace (length path + 1)%nat with (length (path ++ [NUL])) by (rewrite length_app; cbn; lia). exact Hrd.
- exact Hne.
- exact Hnd.
- rewrite MD0_fs. exact Hlk.
- apply (errno_branch regs mem ENOENT Hregs Hmem HG HR). unfold ENOENT. lia.
Qed.
Theorem ubs2_open_toolong : forall ms,
(4096 <= length path)%nat ->
st_ok ubs2segs (E_main sp inp [a0; path] envp efn tid rnd) (ss_main true rs) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp (ed_top rnd) [a0; path] envp efn rnd) ->
realizes ubs2segs (mkCfg ms (MD0 tid brk mbase sp lim inp rnd)) (diag (msg_cannot_open path) (in_fs inp)).
Proof.
intros ms Hlen HS0 HR0.
apply (open_prefix ms _ HS0 HR0). intros regs mem Hregs Hmem HG HR H17 H10 H12 H12' H11 Hrd.
pose proof argv1_no_nul as Hnul1.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp rnd) = []) by reflexivity.
eapply (rz_openat_toolong ubs2segs regs _ mem (seg_rom ubs2segs) _ _ Hh Hlz H17 H12').
- rewrite pend_read_byte_mrb, H11.
assert (Hlenf : length (firstn 4096 path) = 4096%nat) by (rewrite length_firstn; lia).
apply (read_cstr_toolong_of_rdn ubs2segs mem _ (firstn 4096 path) Hlenf).
+ intros Hin. apply Hnul1. rewrite <- (firstn_skipn 4096 path). apply in_app_iff. left. exact Hin.
+ pose proof argv1_cstr_bound as HB. lia.
+ pose proof (rdn_firstn ubs2segs mem (length (path ++ [NUL])) _ (path ++ [NUL]) 4096 Hrd ltac:(rewrite length_app; cbn; lia)) as Hf.
rewrite firstn_app, (proj2 (Nat.sub_0_le _ _)) in Hf by lia. cbn [firstn] in Hf. rewrite app_nil_r in Hf.
exact Hf.
- apply (errno_branch regs mem ENAMETOOLONG Hregs Hmem HG HR). unfold ENAMETOOLONG. lia.
Qed.
End b.
End a.
