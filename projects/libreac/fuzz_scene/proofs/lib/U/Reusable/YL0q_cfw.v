(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/Reusable/YL0q.v. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3, with libreac/fuzz_boxreg's port of its copy of this file (changed open_prefix_cf, errno_branch_cf, src0_open_file_cf, src0_open_dir_cf, src0_open_empty_cf, src0_open_absent_cf and 1 more; added csym_run_ecall_eq, csym_run_to_eq, HvaI, openat_errnos_small_cf, argv1_room_cf). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_scene.images Require Import Ubsan.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YO0i YO0f YO0x YO0d YO05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YH00 YH01 YH03 YH02 YN3e.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL0k YL0p.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YL0q YK15_cfw YP03_cfw YP0n2_cfw SymTac_cfw YL0p_cfw.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require Import SlotAgree AgreeLift.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
(* YL0q's two symbolic runs ([grun_open], [grun_m1]) taken as given opaque lemmas, through the
   crealizes rules of YK15_cfw: [csym_run_with]/[csym_run_to_with] recompute them inline. *)
Ltac csym_run_ecall_eq tblok HS ss0 ssz Hrun :=
lazymatch goal with |- crealizes ?B _ _ =>
lazymatch type of HS with
| st_ok ?segs ?E _ ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let ms' := fresh "ms" in let HF := fresh "HF" in
eapply (crz_run_ecall B tbl tblok FUEL E ss0 ssz ms);
[ | | exact HS | exact Hrun | clear HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport_ecall segs E ss0 ssz ms' HS HF
end
end
end.
Ltac csym_run_to_eq tblok HS stop ss0 ssz Hrun :=
lazymatch goal with |- crealizes ?B _ _ =>
lazymatch type of HS with
| st_ok ?segs ?E _ ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let ms' := fresh "ms" in let HF := fresh "HF" in
eapply (crz_run_to_running B tbl tblok FUEL stop E ss0 ssz ms);
[ | | exact HS | exact Hrun | clear HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport segs E ss0 ssz ms' HS HF
end
end
end.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Local Set Default Proof Using "All".
Variables (sp brk mbase tid : word) (lim : Z) (a0 path : list byte) (inp : ProcInput) (rnd : EntryDraw).
Hypothesis Hargv : in_argv inp = [a0; path].
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv [a0; path].
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp.
Hypothesis Htid : 0 < bv_unsigned tid < 4194304.
Hypothesis Hfits : entry_stack_fits sp [a0; path] (in_envp inp).
Hypothesis HCO : cannot_open_hyp_cf.
Hypothesis Hcr : in_channel_reader inp = true.
Lemma HvaI : valid_argv (in_argv inp). Proof. rewrite Hargv. exact Hva. Qed.
(* As YL0q.openat_errnos_small, which takes YL0q's section arguments first. *)
Lemma openat_errnos_small_cf : forall e, In e openat_errnos -> 0 < e < 4096.
Proof.
intros e H. unfold openat_errnos in H. cbn in H.
unfold ENOMEM, EACCES, EMFILE, ENFILE in H.
destruct H as [<-|[<-|[<-|[<-|[]]]]]; lia.
Qed.
(* As YL0q.argv1_room (which takes YL0q's own section hypotheses). *)
Lemma argv1_room_cf :
(bv_unsigned (Z_to_bv 64 (z_argv (bv_unsigned (ed_top rnd)) [a0; path] (in_envp inp) (in_execfn inp) 1))
 + Z.of_nat (length path) + 1 <= SP_HI - 9)%Z.
Proof.
pose proof (layout_facts src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp HvaI Hve Hvl Hlau) as L.
rewrite ?Hargv in L.
pose proof (z_argv_bounds src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp HvaI Hve Hvl Hlau 1 ltac:(rewrite ?Hargv; cbn; lia)) as B1.
rewrite ?Hargv in B1. cbn [nth] in B1.
pose proof (z_argv_fits src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp HvaI Hve Hvl Hlau 1 ltac:(rewrite ?Hargv; cbn; lia)) as F1.
rewrite ?Hargv in F1. cbn [nth] in F1.
pose proof (auxv_bytes_range (kb_rseq (in_kernel inp))) as ARL.
destruct L as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
destruct B1 as [B1a B1b].
unfold SP_LO, SP_HI in L7, L8, L9, F1 |- *.
rewrite u_Z2bv by lia.
lia.
Qed.
Lemma open_prefix_cf : forall ms T,
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
getr regs 11%bv = Z_to_bv 64 (z_argv (bv_unsigned (ed_top rnd)) [a0; path] (in_envp inp) (in_execfn inp) 1) ->
rdn src0segs mem (Z_to_bv 64 (z_argv (bv_unsigned (ed_top rnd)) [a0; path] (in_envp inp) (in_execfn inp) 1)) (length (path ++ [NUL])) = Some (path ++ [NUL]) ->
crealizes src0_msyms (mkCfg (pend_at regs (Z_to_bv 64 (ss_pc ss_open)) mem (seg_rom src0segs)) (MD0 tid brk mbase sp lim inp rnd)) T) ->
crealizes src0_msyms (mkCfg ms (MD0 tid brk mbase sp lim inp rnd)) T.
Proof.
intros ms T HS0 HR K.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp rnd) = []) by reflexivity.
pose proof (st_ok_drv true _ ms HS0) as HS. change (ss_drv true) with ss_drv_t in HS. clear HS0.
pose proof (ew2' src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp HvaI Hve Hvl Hlau 1 ltac:(lia) (xw_main inp rnd tid) (xd_main rnd) ltac:(rewrite ?Hargv; cbn; lia)) as H2.
change (E0 _ _ _ _ _ _ _ _) with (E_main sp inp tid rnd) in H2. rewrite ?Hargv in H2.
(* As YL0q.open_prefix: argc named by [ew3], so the branch is decided on closed words (a
   [vm_compute] over [E_main], which is built from the whole input, is where the memory went). *)
apply (st_ok_add_cond src0segs _ _ _ BC_EQ (SOff 3 0) (SLit 2)) in HS; [ | ].
2:{ pose proof (ew3 src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp HvaI Hve Hvl Hlau 1 ltac:(lia) (xw_main inp rnd tid) (xd_main rnd)) as H3.
change (E0 _ _ _ _ _ _ _ _) with (E_main sp inp tid rnd) in H3. rewrite Hargv in H3. cbn [length] in H3.
unfold branch_taken. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
replace (ew (E_main sp inp tid rnd) 3) with (Z_to_bv 64 2)
  by (apply bv_eq; rewrite H3; vm_compute; reflexivity).
vm_compute; reflexivity. }
rewrite ss_drv_eq_def in HS.
csym_run_ecall_eq src0tbl_ok HS ss_drv_eq ss_open grun_open.
sym_ecall_open HS.
repeat match goal with H : runs_at _ (ms_mem (pend_at _ _ _ _)) _ |- _ => cbn [ms_mem pend_at] in H end.
lazymatch goal with |- crealizes _ (mkCfg (pend_at ?regs _ ?mem _) _) _ => apply (K regs mem Hregs Hmem HG HR) end.
- rewrite (Hregs (17%bv:reg)); eval_sr_get; cbn [sv_denot]. reflexivity.
- rewrite (Hregs (10%bv:reg)); eval_sr_get; cbn [sv_denot]. apply bv_eq. vm_compute. reflexivity.
- rewrite (Hregs (12%bv:reg)); eval_sr_get; cbn [sv_denot]. vm_compute. reflexivity.
- rewrite (Hregs (12%bv:reg)); eval_sr_get; cbn [sv_denot]. vm_compute. reflexivity.
- rewrite (Hregs (11%bv:reg)); eval_sr_get; cbn [sv_denot]. rewrite Z.add_0_r, H2. reflexivity.
- pose proof (runs_at_nth _ mem _ 2 _ _ HR eq_refl) as Hb. rewrite Hargv in Hb. cbn [nth] in Hb. exact (bytes_at_rdn src0segs mem _ _ Hb).
Qed.
Lemma errno_branch_cf : forall regs mem e,
regs_ok (E_main sp inp tid rnd) (ss_regs ss_open) regs ->
mem_ok src0segs (E_main sp inp tid rnd) mem (ss_mem ss_open) ->
facts_ok (E_main sp inp tid rnd) (ss_facts ss_open) ->
runs_at (bv_unsigned sp) mem (runs_main true sp inp rnd) ->
0 < e < 4096 ->
crealizes src0_msyms
(mkCfg (mkst (regupd regs 10%bv (errno_ret e)) (v_addi (Z_to_bv 64 (ss_pc ss_open)) 4) mem (seg_rom src0segs)) (MD0 tid brk mbase sp lim inp rnd))
(diag (msg_cannot_open path) (in_fs inp)).
Proof.
intros regs mem e Hregs Hmem HG HR He.
rewrite <- (MD0_fs tid brk mbase sp lim inp rnd).
apply (HCO sp inp mbase brk a0 path tid rnd regs mem _ e Hargv Hsp Hva Hve Hvl Hlau Hfits Htid Hregs Hmem HG HR); [reflexivity | reflexivity | | exact He].
split; [| split; [reflexivity|]].
- rewrite MD0_fds. reflexivity.
- first [ rewrite MD0_channel_reader; exact Hcr | unfold MD0, init_model; autorewrite with model; exact Hcr ].
Qed.
Theorem src0_open_file_cf : forall ms data,
(length path < 4096)%nat -> path <> [] -> openat_plain_name path = true ->
fs_lookup (in_fs inp) path = Some data ->
st_ok src0segs (E_main sp inp tid rnd) ss_main_t ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp inp rnd) ->
forall T,
(forall ms1, st_ok src0segs (E_main sp inp tid rnd) ss_m1 ms1 ->
runs_at (bv_unsigned sp) (ms_mem ms1) (runs_main true sp inp rnd) ->
crealizes src0_msyms (mkCfg ms1 (MD_file path tid brk mbase sp lim inp rnd)) T) ->
crealizes src0_msyms (mkCfg ms (MD0 tid brk mbase sp lim inp rnd)) (t_alt2 (diag (msg_cannot_open path) (in_fs inp)) T).
Proof.
intros ms data Hlen Hne Hnd Hlk HS0 HR0 T K.
apply (open_prefix_cf ms _ HS0 HR0). intros regs mem Hregs Hmem HG HR H17 H10 H12 H12' H11 Hrd.
pose proof (argv_no_nul src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp HvaI Hve Hvl Hlau 1 ltac:(rewrite ?Hargv; cbn; lia)) as Hnul1. rewrite ?Hargv in Hnul1. cbn [nth] in Hnul1.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp rnd) = []) by reflexivity.
eapply (crz_openat_file src0_msyms regs _ mem (seg_rom src0segs) _ path data _ _ Hh Hlz H17 H10 H12).
- rewrite pend_read_byte_mrb, H11. apply (read_cstr_of_rdn src0segs mem _ path);
  [lia | exact Hnul1 | pose proof argv1_room_cf as R; unfold SP_HI, TASK_SIZE in R |- *; lia |].
replace (length path + 1)%nat with (length (path ++ [NUL])) by (rewrite length_app; cbn; lia). exact Hrd.
- exact Hne.
- exact Hnd.
- rewrite MD0_fs. exact Hlk.
- rewrite MD0_fds, alloc_fd_std3. apply fd_lookup_std3.
- intros e He. apply (errno_branch_cf regs mem e Hregs Hmem HG HR (openat_errnos_small_cf e He)).
- rewrite MD0_fds, alloc_fd_std3. rewrite <- (MD0_fds tid brk mbase sp lim inp rnd). fold (MD_file path tid brk mbase sp lim inp rnd).
assert (Hh1 : m_halted (MD_file path tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz1 : m_vm_lazy (MD_file path tid brk mbase sp lim inp rnd) = []) by reflexivity.
cresume_sv src0segs (SLit 3). { reflexivity. }
lazymatch type of HS with st_ok _ _ _ ?msx =>
change (st_ok src0segs (E_main sp inp tid rnd) ss_o3 msx) in HS end.
csym_run_to_eq src0tbl_ok HS src0_A_malloc ss_o3 ss_m1 grun_m1.
lazymatch type of HS with st_ok _ _ _ ?msx => exact (K msx HS HR) end.
Qed.
Theorem src0_open_dir_cf : forall ms,
path = dot_path ->
st_ok src0segs (E_main sp inp tid rnd) ss_main_t ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp inp rnd) ->
forall T,
(forall ms1, st_ok src0segs (E_main sp inp tid rnd) ss_m1 ms1 ->
runs_at (bv_unsigned sp) (ms_mem ms1) (runs_main true sp inp rnd) ->
crealizes src0_msyms (mkCfg ms1 (MD_dir tid brk mbase sp lim inp rnd)) T) ->
crealizes src0_msyms (mkCfg ms (MD0 tid brk mbase sp lim inp rnd)) (t_alt2 (diag (msg_cannot_open path) (in_fs inp)) T).
Proof.
intros ms Hdot HS0 HR0 T K.
apply (open_prefix_cf ms _ HS0 HR0). intros regs mem Hregs Hmem HG HR H17 H10 H12 H12' H11 Hrd.
pose proof (argv_no_nul src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp HvaI Hve Hvl Hlau 1 ltac:(rewrite ?Hargv; cbn; lia)) as Hnul1. rewrite ?Hargv in Hnul1. cbn [nth] in Hnul1.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp rnd) = []) by reflexivity.
eapply (crz_openat_dir src0_msyms regs _ mem (seg_rom src0segs) _ _ _ Hh Hlz H17 H10 H12).
- rewrite pend_read_byte_mrb, H11, <- Hdot. apply (read_cstr_of_rdn src0segs mem _ path);
  [rewrite Hdot; cbn; lia | exact Hnul1 | pose proof argv1_room_cf as R; unfold SP_HI, TASK_SIZE in R |- *; lia |].
replace (length path + 1)%nat with (length (path ++ [NUL])) by (rewrite length_app; cbn; lia). exact Hrd.
- rewrite MD0_fds, alloc_fd_std3. apply fd_lookup_std3.
- intros e He. apply (errno_branch_cf regs mem e Hregs Hmem HG HR (openat_errnos_small_cf e He)).
- rewrite MD0_fds, alloc_fd_std3. rewrite <- (MD0_fds tid brk mbase sp lim inp rnd). fold (MD_dir tid brk mbase sp lim inp rnd).
assert (Hh1 : m_halted (MD_dir tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz1 : m_vm_lazy (MD_dir tid brk mbase sp lim inp rnd) = []) by reflexivity.
cresume_sv src0segs (SLit 3). { reflexivity. }
lazymatch type of HS with st_ok _ _ _ ?msx =>
change (st_ok src0segs (E_main sp inp tid rnd) ss_o3 msx) in HS end.
csym_run_to_eq src0tbl_ok HS src0_A_malloc ss_o3 ss_m1 grun_m1.
lazymatch type of HS with st_ok _ _ _ ?msx => exact (K msx HS HR) end.
Qed.
Theorem src0_open_empty_cf : forall ms,
path = [] ->
st_ok src0segs (E_main sp inp tid rnd) ss_main_t ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp inp rnd) ->
crealizes src0_msyms (mkCfg ms (MD0 tid brk mbase sp lim inp rnd)) (diag (msg_cannot_open path) (in_fs inp)).
Proof.
intros ms Hnil HS0 HR0.
apply (open_prefix_cf ms _ HS0 HR0). intros regs mem Hregs Hmem HG HR H17 H10 H12 H12' H11 Hrd.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp rnd) = []) by reflexivity.
eapply (crz_openat_empty src0_msyms regs _ mem (seg_rom src0segs) _ _ Hh Hlz H17 H12').
- rewrite pend_read_byte_mrb, H11. apply (read_cstr_of_rdn src0segs mem _ []);
  [cbn; lia | intros [] | pose proof argv1_room_cf as R; unfold SP_HI, TASK_SIZE in R |- *; cbn [length]; lia |].
rewrite Hnil in Hrd |- *. cbn [length app Nat.add] in Hrd |- *. exact Hrd.
- apply (errno_branch_cf regs mem ENOENT Hregs Hmem HG HR). unfold ENOENT. lia.
Qed.
Theorem src0_open_absent_cf : forall ms,
(length path < 4096)%nat -> path <> [] -> openat_plain_name path = true ->
fs_lookup (in_fs inp) path = None ->
st_ok src0segs (E_main sp inp tid rnd) ss_main_t ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp inp rnd) ->
crealizes src0_msyms (mkCfg ms (MD0 tid brk mbase sp lim inp rnd)) (diag (msg_cannot_open path) (in_fs inp)).
Proof.
intros ms Hlen Hne Hnd Hlk HS0 HR0.
apply (open_prefix_cf ms _ HS0 HR0). intros regs mem Hregs Hmem HG HR H17 H10 H12 H12' H11 Hrd.
pose proof (argv_no_nul src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp HvaI Hve Hvl Hlau 1 ltac:(rewrite ?Hargv; cbn; lia)) as Hnul1. rewrite ?Hargv in Hnul1. cbn [nth] in Hnul1.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp rnd) = []) by reflexivity.
eapply (crz_openat_absent src0_msyms regs _ mem (seg_rom src0segs) _ path _ Hh Hlz H17 H10 H12).
- rewrite pend_read_byte_mrb, H11. apply (read_cstr_of_rdn src0segs mem _ path);
  [lia | exact Hnul1 | pose proof argv1_room_cf as R; unfold SP_HI, TASK_SIZE in R |- *; lia |].
replace (length path + 1)%nat with (length (path ++ [NUL])) by (rewrite length_app; cbn; lia). exact Hrd.
- exact Hne.
- exact Hnd.
- rewrite MD0_fs. exact Hlk.
- apply (errno_branch_cf regs mem ENOENT Hregs Hmem HG HR). unfold ENOENT. lia.
Qed.
Theorem src0_open_toolong_cf : forall ms,
(4096 <= length path)%nat ->
st_ok src0segs (E_main sp inp tid rnd) ss_main_t ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp inp rnd) ->
crealizes src0_msyms (mkCfg ms (MD0 tid brk mbase sp lim inp rnd)) (diag (msg_cannot_open path) (in_fs inp)).
Proof.
intros ms Hlen HS0 HR0.
apply (open_prefix_cf ms _ HS0 HR0). intros regs mem Hregs Hmem HG HR H17 H10 H12 H12' H11 Hrd.
pose proof (argv_no_nul src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp HvaI Hve Hvl Hlau 1 ltac:(rewrite ?Hargv; cbn; lia)) as Hnul1. rewrite ?Hargv in Hnul1. cbn [nth] in Hnul1.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp rnd) = []) by reflexivity.
eapply (crz_openat_toolong src0_msyms regs _ mem (seg_rom src0segs) _ _ Hh Hlz H17 H12').
- rewrite pend_read_byte_mrb, H11.
assert (Hlenf : length (firstn 4096 path) = 4096%nat) by (rewrite length_firstn; lia).
apply (read_cstr_toolong_of_rdn src0segs mem _ (firstn 4096 path) Hlenf).
2:{ pose proof argv1_room_cf as R. unfold SP_HI, TASK_SIZE in R |- *. lia. }
+ intros Hin. apply Hnul1. rewrite <- (firstn_skipn 4096 path). apply in_app_iff. left. exact Hin.
+ pose proof (rdn_firstn src0segs mem (length (path ++ [NUL])) _ (path ++ [NUL]) 4096 Hrd ltac:(rewrite length_app; cbn; lia)) as Hf.
rewrite firstn_app, (proj2 (Nat.sub_0_le _ _)) in Hf by lia. cbn [firstn] in Hf. rewrite app_nil_r in Hf.
exact Hf.
- apply (errno_branch_cf regs mem ENAMETOOLONG Hregs Hmem HG HR). unfold ENAMETOOLONG. lia.
Qed.
End b.
End a.
