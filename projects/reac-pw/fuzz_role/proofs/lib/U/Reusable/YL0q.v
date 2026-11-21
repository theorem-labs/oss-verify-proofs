(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0q.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput (kernel build, exec file name, SIGPIPE disposition) and entry; the channel-reader premise; the stack strings at the top of the stack VMA; the string reads' access check). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_pw.fuzz_role.images Require Import Ubsan.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YO0i YO0f YO0x YO0d YO05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YH00 YH01 YH03 YH02 YN3e.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL0k YL0p.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable.R Require Import Cfg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {AM : AllocMode}.
Section b.
Variables (sp brk mbase tid : word) (lim : Z) (a0 path : list byte) (inp : ProcInput) (rnd : EntryDraw).
Hypothesis Hargv : in_argv inp = [a0; path].
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Htid : 0 < bv_unsigned tid < 4194304.
(* [entry_stack_fits] no longer determines the stack image: REPLACED by the three premises
   YN3e's Section f takes (YN3e.v:189-194). *)
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp.
Hypothesis Hvi : valid_input inp.
Hypothesis HCO : cannot_open_hyp.
#[local] Notation envp := (in_envp inp).
#[local] Notation efn := (in_execfn inp).
(* [Common.FileSim.read_cstr_of_rdn] gained a third premise at this revision --
   [bv_unsigned a + Z.of_nat (length str) < TASK_SIZE], 75d69e00:theories/Common/FileSim.v:
   434-437, because [State.read_cstr_aux] now tests [access_okb a 1] at every byte
   (75d69e00:FileSim.v:378-397).  Every call below is to the argv[1] string, so the bound is
   proved once here.  The strings are TOP-anchored now, so it comes from [YP08.z_argv_fits]
   against [SP_HI] (0x800000000000 = 2^47, YP08.v:311), not from the old sp-relative form. *)
Lemma argv1_bound :
0 <= z_argv (bv_unsigned (ed_top rnd)) [a0; path] envp efn 1
/\ z_argv (bv_unsigned (ed_top rnd)) [a0; path] envp efn 1 + Z.of_nat (length path) + 1 <= 2 ^ 47 - 9.
Proof.
assert (Hal : (2 <= length (in_argv inp))%nat) by (rewrite Hargv; cbn; lia).
pose proof (LF inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau) as L.
pose proof (SB inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau) as S.
pose proof (ZAB inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia)) as B1.
assert (F1 : z_argv (bv_unsigned (ed_top rnd)) (in_argv inp) envp efn 1
+ Z.of_nat (length (nth 1 (in_argv inp) [])) + 1 <= SP_HI - 9)
by (exact (YP08.z_argv_fits src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia))).
rewrite Hargv in L, S, B1, F1. cbn [nth] in B1, F1.
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
st_ok src0segs (E_main sp inp tid rnd) ss_main_t ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp inp rnd) ->
(forall regs mem,
regs_ok (E_main sp inp tid rnd) (ss_regs ss_open) regs ->
mem_ok src0segs (E_main sp inp tid rnd) mem (ss_mem ss_open) ->
facts_ok (E_main sp inp tid rnd) (ss_facts ss_open) ->
runs_at (bv_unsigned sp) mem (runs_main true sp inp rnd) ->
bv_unsigned (getr regs 17%bv) = 56 ->
getr regs 10%bv = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12%bv)) open_ignored_flags = 0 ->
modeled_open_flags (getr regs 12%bv) = true ->
getr regs 11%bv = Z_to_bv 64 (z_argv (bv_unsigned (ed_top rnd)) [a0; path] envp efn 1) ->
rdn src0segs mem (Z_to_bv 64 (z_argv (bv_unsigned (ed_top rnd)) [a0; path] envp efn 1)) (length (path ++ [NUL])) = Some (path ++ [NUL]) ->
realizes src0segs (mkCfg (pend_at regs (Z_to_bv 64 (ss_pc ss_open)) mem (seg_rom src0segs)) (MD0 tid brk mbase sp lim inp rnd)) T) ->
realizes src0segs (mkCfg ms (MD0 tid brk mbase sp lim inp rnd)) T.
Proof using Hargv Hlau Hsp Hva Hve Hvi Hvl.
intros ms T HS0 HR K.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp rnd) = []) by reflexivity.
pose proof (st_ok_drv true _ ms HS0) as HS. change (ss_drv true) with ss_drv_t in HS. clear HS0.
assert (H2 : bv_unsigned (ew (E_main sp inp tid rnd) 2)
= z_argv (bv_unsigned (ed_top rnd)) (in_argv inp) envp efn 1)
by (unfold E_main; exact (YP08.ew2' src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia) (xw_main inp rnd tid) (xd_main rnd) ltac:(rewrite Hargv; cbn; lia))).
rewrite Hargv in H2.
(* 727298f3: argc named by [ew3] and the side condition decided on closed words, as
   libdiginet/fuzz_decode's copy (the old `rewrite Hargv` finds no [in_argv inp] once [E0]
   takes the rseq flag). *)
apply (st_ok_add_cond src0segs _ _ _ BC_EQ (SOff 3 0) (SLit 2)) in HS; [ sym_norm HS | ].
2:{ pose proof (YP08.ew3 src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia) (xw_main inp rnd tid) (xd_main rnd)) as H3.
change (E0 _ _ _ _ _ _ _ _) with (E_main sp inp tid rnd) in H3. rewrite Hargv in H3. cbn [length] in H3.
unfold branch_taken. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
replace (ew (E_main sp inp tid rnd) 3) with (Z_to_bv 64 2)
  by (apply bv_eq; rewrite H3; vm_compute; reflexivity).
vm_compute; reflexivity. }
sym_run_with src0tbl_ok HS.
lazymatch type of HS with st_ok_ecall _ _ _ ?msx =>
change (st_ok_ecall src0segs (E_main sp inp tid rnd) ss_open msx) in HS end.
sym_ecall_open HS.
repeat match goal with H : runs_at _ (ms_mem (pend_at _ _ _ _)) _ |- _ => cbn [ms_mem pend_at] in H end.
lazymatch goal with |- realizes _ (mkCfg (pend_at ?regs _ ?mem _) _) _ => apply (K regs mem Hregs Hmem HG HR) end.
- rewrite (Hregs (17%bv:reg)); eval_sr_get; cbn [sv_denot]. reflexivity.
- rewrite (Hregs (10%bv:reg)); eval_sr_get; cbn [sv_denot]. apply bv_eq. vm_compute. reflexivity.
- rewrite (Hregs (12%bv:reg)); eval_sr_get; cbn [sv_denot]. vm_compute. reflexivity.
- rewrite (Hregs (12%bv:reg)); eval_sr_get; cbn [sv_denot]. vm_compute. reflexivity.
- rewrite (Hregs (11%bv:reg)); eval_sr_get; cbn [sv_denot]. rewrite Z.add_0_r, H2. reflexivity.
- pose proof (runs_at_nth _ mem _ 2 _ _ HR eq_refl) as Hb.
cbn [runs_main] in Hb. rewrite Hargv in Hb. cbn [nth] in Hb.
exact (bytes_at_rdn src0segs mem _ _ Hb).
Qed.
Lemma errno_branch : forall regs mem e,
regs_ok (E_main sp inp tid rnd) (ss_regs ss_open) regs ->
mem_ok src0segs (E_main sp inp tid rnd) mem (ss_mem ss_open) ->
facts_ok (E_main sp inp tid rnd) (ss_facts ss_open) ->
runs_at (bv_unsigned sp) mem (runs_main true sp inp rnd) ->
0 < e < 4096 ->
realizes src0segs
(mkCfg (mkst (regupd regs 10%bv (errno_ret e)) (v_addi (Z_to_bv 64 (ss_pc ss_open)) 4) mem (seg_rom src0segs)) (MD0 tid brk mbase sp lim inp rnd))
(diag (msg_cannot_open path) (in_fs inp)).
Proof.
intros regs mem e Hregs Hmem HG HR He.
rewrite <- (MD0_fs tid brk mbase sp lim inp rnd).
apply (HCO sp brk mbase inp a0 path tid rnd regs mem _ e Hsp Hargv Hva Hve Hvl Hlau Hvi Htid Hregs Hmem HG HR);
[reflexivity | reflexivity | | exact He].
(* 727298f3: [fdchan] is three conjuncts; the third, the channel reader, is the input's
   ([MD0_channel_reader]), which [Run.valid_input] pins to true. *)
split; [| split; [reflexivity | rewrite MD0_channel_reader; exact (valid_input_channel_reader inp Hvi)]].
rewrite MD0_fds. reflexivity.
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
st_ok src0segs (E_main sp inp tid rnd) ss_main_t ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp inp rnd) ->
forall T,
(forall ms1, st_ok src0segs (E_main sp inp tid rnd) ss_m1 ms1 ->
runs_at (bv_unsigned sp) (ms_mem ms1) (runs_main true sp inp rnd) ->
realizes src0segs (mkCfg ms1 (MD_file path tid brk mbase sp lim inp rnd)) T) ->
realizes src0segs (mkCfg ms (MD0 tid brk mbase sp lim inp rnd)) (t_alt2 (diag (msg_cannot_open path) (in_fs inp)) T).
Proof.
intros ms data Hlen Hne Hnd Hlk HS0 HR0 T K.
apply (open_prefix ms _ HS0 HR0). intros regs mem Hregs Hmem HG HR H17 H10 H12 H12' H11 Hrd.
pose proof (ANN inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(rewrite Hargv; cbn; lia)) as Hnul1.
rewrite Hargv in Hnul1. cbn [nth] in Hnul1.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp rnd) = []) by reflexivity.
eapply (rz_openat_file src0segs regs _ mem (seg_rom src0segs) _ path data _ _ Hh Hlz H17 H10 H12).
- rewrite pend_read_byte_mrb, H11.
apply (read_cstr_of_rdn src0segs mem _ path); [lia | exact Hnul1 | exact argv1_cstr_bound |].
replace (length path + 1)%nat with (length (path ++ [NUL])) by (rewrite length_app; cbn; lia). exact Hrd.
- exact Hne.
- exact Hnd.
- rewrite MD0_fs. exact Hlk.
- rewrite MD0_fds, alloc_fd_std3. apply fd_lookup_std3.
- intros e He. apply (errno_branch regs mem e Hregs Hmem HG HR (openat_errnos_small e He)).
- rewrite MD0_fds, alloc_fd_std3. rewrite <- (MD0_fds tid brk mbase sp lim inp rnd). fold (MD_file path tid brk mbase sp lim inp rnd).
assert (Hh1 : m_halted (MD_file path tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz1 : m_vm_lazy (MD_file path tid brk mbase sp lim inp rnd) = []) by reflexivity.
resume_sv src0segs (SLit 3). { reflexivity. }
let pc := eval vm_compute in src0_A_malloc in sym_run_to_with src0tbl_ok HS pc.
lazymatch type of HS with st_ok _ _ _ ?msx =>
change (st_ok src0segs (E_main sp inp tid rnd) ss_m1 msx) in HS;
exact (K msx HS HR) end.
Qed.
Theorem src0_open_dir : forall ms,
path = dot_path ->
st_ok src0segs (E_main sp inp tid rnd) ss_main_t ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp inp rnd) ->
forall T,
(forall ms1, st_ok src0segs (E_main sp inp tid rnd) ss_m1 ms1 ->
runs_at (bv_unsigned sp) (ms_mem ms1) (runs_main true sp inp rnd) ->
realizes src0segs (mkCfg ms1 (MD_dir tid brk mbase sp lim inp rnd)) T) ->
realizes src0segs (mkCfg ms (MD0 tid brk mbase sp lim inp rnd)) (t_alt2 (diag (msg_cannot_open path) (in_fs inp)) T).
Proof.
intros ms Hdot HS0 HR0 T K.
apply (open_prefix ms _ HS0 HR0). intros regs mem Hregs Hmem HG HR H17 H10 H12 H12' H11 Hrd.
pose proof (ANN inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(rewrite Hargv; cbn; lia)) as Hnul1.
rewrite Hargv in Hnul1. cbn [nth] in Hnul1.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp rnd) = []) by reflexivity.
eapply (rz_openat_dir src0segs regs _ mem (seg_rom src0segs) _ _ _ Hh Hlz H17 H10 H12).
- rewrite pend_read_byte_mrb, H11, <- Hdot.
apply (read_cstr_of_rdn src0segs mem _ path);
[rewrite Hdot; cbn; lia | exact Hnul1 | exact argv1_cstr_bound |].
replace (length path + 1)%nat with (length (path ++ [NUL])) by (rewrite length_app; cbn; lia). exact Hrd.
- rewrite MD0_fds, alloc_fd_std3. apply fd_lookup_std3.
- intros e He. apply (errno_branch regs mem e Hregs Hmem HG HR (openat_errnos_small e He)).
- rewrite MD0_fds, alloc_fd_std3. rewrite <- (MD0_fds tid brk mbase sp lim inp rnd). fold (MD_dir tid brk mbase sp lim inp rnd).
assert (Hh1 : m_halted (MD_dir tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz1 : m_vm_lazy (MD_dir tid brk mbase sp lim inp rnd) = []) by reflexivity.
resume_sv src0segs (SLit 3). { reflexivity. }
let pc := eval vm_compute in src0_A_malloc in sym_run_to_with src0tbl_ok HS pc.
lazymatch type of HS with st_ok _ _ _ ?msx =>
change (st_ok src0segs (E_main sp inp tid rnd) ss_m1 msx) in HS;
exact (K msx HS HR) end.
Qed.
Theorem src0_open_empty : forall ms,
path = [] ->
st_ok src0segs (E_main sp inp tid rnd) ss_main_t ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp inp rnd) ->
realizes src0segs (mkCfg ms (MD0 tid brk mbase sp lim inp rnd)) (diag (msg_cannot_open path) (in_fs inp)).
Proof.
intros ms Hnil HS0 HR0.
apply (open_prefix ms _ HS0 HR0). intros regs mem Hregs Hmem HG HR H17 H10 H12 H12' H11 Hrd.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp rnd) = []) by reflexivity.
eapply (rz_openat_empty src0segs regs _ mem (seg_rom src0segs) _ _ Hh Hlz H17 H12').
- rewrite pend_read_byte_mrb, H11.
apply (read_cstr_of_rdn src0segs mem _ []);
[cbn; lia | intros [] | pose proof argv1_cstr_bound as HB; cbn [length] in *; lia |].
rewrite Hnil in Hrd |- *. cbn [length app Nat.add] in Hrd |- *. exact Hrd.
- apply (errno_branch regs mem ENOENT Hregs Hmem HG HR). unfold ENOENT. lia.
Qed.
Theorem src0_open_absent : forall ms,
(length path < 4096)%nat -> path <> [] -> openat_plain_name path = true ->
fs_lookup (in_fs inp) path = None ->
st_ok src0segs (E_main sp inp tid rnd) ss_main_t ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp inp rnd) ->
realizes src0segs (mkCfg ms (MD0 tid brk mbase sp lim inp rnd)) (diag (msg_cannot_open path) (in_fs inp)).
Proof.
intros ms Hlen Hne Hnd Hlk HS0 HR0.
apply (open_prefix ms _ HS0 HR0). intros regs mem Hregs Hmem HG HR H17 H10 H12 H12' H11 Hrd.
pose proof (ANN inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(rewrite Hargv; cbn; lia)) as Hnul1.
rewrite Hargv in Hnul1. cbn [nth] in Hnul1.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp rnd) = []) by reflexivity.
eapply (rz_openat_absent src0segs regs _ mem (seg_rom src0segs) _ path _ Hh Hlz H17 H10 H12).
- rewrite pend_read_byte_mrb, H11.
apply (read_cstr_of_rdn src0segs mem _ path); [lia | exact Hnul1 | exact argv1_cstr_bound |].
replace (length path + 1)%nat with (length (path ++ [NUL])) by (rewrite length_app; cbn; lia). exact Hrd.
- exact Hne.
- exact Hnd.
- rewrite MD0_fs. exact Hlk.
- apply (errno_branch regs mem ENOENT Hregs Hmem HG HR). unfold ENOENT. lia.
Qed.
Theorem src0_open_toolong : forall ms,
(4096 <= length path)%nat ->
st_ok src0segs (E_main sp inp tid rnd) ss_main_t ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp inp rnd) ->
realizes src0segs (mkCfg ms (MD0 tid brk mbase sp lim inp rnd)) (diag (msg_cannot_open path) (in_fs inp)).
Proof.
intros ms Hlen HS0 HR0.
apply (open_prefix ms _ HS0 HR0). intros regs mem Hregs Hmem HG HR H17 H10 H12 H12' H11 Hrd.
pose proof (ANN inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(rewrite Hargv; cbn; lia)) as Hnul1.
rewrite Hargv in Hnul1. cbn [nth] in Hnul1.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp rnd) = []) by reflexivity.
eapply (rz_openat_toolong src0segs regs _ mem (seg_rom src0segs) _ _ Hh Hlz H17 H12').
- rewrite pend_read_byte_mrb, H11.
assert (Hlenf : length (firstn 4096 path) = 4096%nat) by (rewrite length_firstn; lia).
apply (read_cstr_toolong_of_rdn src0segs mem _ (firstn 4096 path) Hlenf).
+ intros Hin. apply Hnul1. rewrite <- (firstn_skipn 4096 path). apply in_app_iff. left. exact Hin.
+ (* [read_cstr_toolong_of_rdn]'s own TASK_SIZE premise, the [<= 4096] form
     (YK0p.v:338-342); [argv1_cstr_bound] is the [+ length path] form and
     [4096 <= length path] here, so it is the weaker of the two. *)
pose proof argv1_cstr_bound as HB. lia.
+ pose proof (rdn_firstn src0segs mem (length (path ++ [NUL])) _ (path ++ [NUL]) 4096 Hrd ltac:(rewrite length_app; cbn; lia)) as Hf.
rewrite firstn_app, (proj2 (Nat.sub_0_le _ _)) in Hf by lia. cbn [firstn] in Hf. rewrite app_nil_r in Hf.
exact Hf.
- apply (errno_branch regs mem ENAMETOOLONG Hregs Hmem HG HR). unfold ENAMETOOLONG. lia.
Qed.
End b.
End a.
