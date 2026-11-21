(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Trevor Hansen, 2026-11: module names. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the driver arms and the top theorem are stated over the run with the launch premises in place of entry_stack_fits, the CONFIG_RSEQ-indexed states and the models carrying the entry's vDSO draw, and the arms take the run's channel-reader fact, proved at the top from valid_input, for the reader conjunct of fdchan. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YK0o YK0q YQ0k YN06 YN02.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ0d YQ05 YO3v.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YP0j YP0g YP0r YP0c YP0e YP07.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YH04 YH05 YH07 YH06 YO3p.
From OSSVerify.libtasn1.asn1_get_length_der_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YO04 YL05 YL01 YL06 YL0b YL0c YL0g YL0l YL0m YL0j YL0e YL0i YL0h YL0o YL0u YL0t YL0r YL0s.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {rc : YN05.RunCeil}.
Lemma plain_name_of_argv : forall a0 path, valid_argv [a0; path] -> path <> dot_path -> openat_plain_name path = true.
Proof.
intros a0 path (_ & _ & _ & _ & HF) Hnd. cbn [tl] in HF. apply Forall_inv in HF. destruct HF as [Hs Hdd].
unfold openat_plain_name, path_is_dirref. rewrite Hs, Hdd.
destruct (path_eqb path dot_path) eqn:E; [apply path_eqb_eq in E; contradiction | reflexivity].
Qed.
Section c.
Variable API : AllocAPI src2_msyms.
Hypothesis AX : AllocExtra src2_msyms (aa_MR API).
Lemma HU : usage_hyp.
Proof. exact src2_usage_hyp. Qed.
Lemma HCO : cannot_open_hyp.
Proof. exact src2_cannot_open_hyp. Qed.
Lemma HRE : read_error_hyp.
Proof. exact src2_read_error_hyp. Qed.
Hypothesis LIB : lib_contract_all src2_msyms API LIBPC RA_LIB EMPTY LIB_STACK_RGB.
Hypothesis DOB : driver_obligations.
(* #38: the arms below are stated over the run [inp] with the launch premises
   ([valid_launch], [entry_launch_ok_va]) in place of [entry_stack_fits], over
   the run's own CONFIG_RSEQ-indexed states, and over the models carrying the
   entry's vDSO draw (YL0g.MD0).  The lemmas they call take their section's
   launch premises first; [lfeed] (YL0g) supplies those from the context. *)
Lemma dir_arm : forall sp brk mbase tid lim a0 inp rnd ms1,
in_argv inp = [a0; dot_path] ->
valid_sp sp -> YN05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
valid_brk src2segs brk -> valid_mmap_base mbase -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> in_channel_reader inp = true ->
0 < bv_unsigned tid < 4194304 -> SRC_LIM_MIN <= lim ->
st_ok src2segs (E_main sp inp [a0; dot_path] (in_envp inp) (in_execfn inp) tid rnd) (ss_m1 (kb_rseq (in_kernel inp))) ms1 ->
runs_at (bv_unsigned sp) (ms_mem ms1) (runs_main true sp (ed_top rnd) [a0; dot_path] (in_envp inp) (in_execfn inp) rnd) ->
realizes src2segs (mkCfg ms1 (MD_dir tid brk mbase sp lim inp rnd)) (SPEC_dir dot_path (in_fs inp)).
Proof.
intros sp brk mbase tid lim a0 inp rnd ms1 Hargv Hsp Hceil Hbrk Hmb Hva Hve Hvl Hlau Hcr Htid Hlim HS HR.
unfold SPEC_dir. rewrite (tset_bind_eq _ _ _ _ _ (dir_m_eq init_state)).
rewrite <- Hargv in HS.
pose proof (src2_malloc1 API AX sp brk mbase tid lim inp rnd) as M. lfeed M.
destruct (init_ledger (MD_dir tid brk mbase sp lim inp rnd) brk mbase sp lim inp ltac:(reflexivity) ltac:(reflexivity) Hsp Hbrk Hmb)
as (rx & Hvm0 & Hrx & Hrxl & Hvin).
eapply (M ms1 (MD_dir tid brk mbase sp lim inp rnd) rx);
[ exact Hvm0 | exact Hrx | exact Hrxl | exact Hvin | reflexivity | reflexivity | reflexivity | exact HS | |].
- exact (jinv_head_eq _ _ _ _ _ (dir_m_eq init_state) (dir_jinv dot_path (in_fs inp))).
- intros res A' L' ms' md' g tr HS' HSA' HMR' HW' HB' [vm' Hmd] Hpath Hfr Hres.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (Hh' & Hlz' & _).
assert (Hch : fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) md').
{ split; [| split; [reflexivity | rewrite Hmd; exact Hcr]]. rewrite Hmd. autorewrite with model. unfold MD_dir. autorewrite with model. rewrite MD0_fds. reflexivity. }
assert (Hfs : m_fs md' = in_fs inp).
{ rewrite Hmd. autorewrite with model. unfold MD_dir. autorewrite with model. apply MD0_fs. }
assert (HR' : runs_at (bv_unsigned sp) (ms_mem ms') (runs_main true sp (ed_top rnd) [a0; dot_path] (in_envp inp) (in_execfn inp) rnd)).
{ eapply runs_at_mbyte; [| | exact HR].
- destruct Hsp as (H & _). revert H. unfold sp_window_lo. lia.
- intros a Ha1 Ha2. apply Hfr; [| exact Ha1 | exact Ha2].
pose proof (YN05.ceil_le_top _ Hceil) as Hle. revert Hle Ha1. unfold stack_max_size. lia. }
destruct res as [q|]; cbn [tset dir_k ret fst snd].
+ rewrite <- Hfs. destruct Hres as (Ha0 & Hnz & b1 & b2 & Hub & _).
assert (Hin : In (q, CAP0) (user_blocks A')) by (rewrite Hub; apply in_app_iff; right; left; reflexivity).
pose proof (src2_dir_after_m1 API AX sp brk mbase tid lim inp rnd) as D. lfeed D.
exact (D a0 dot_path (ms_regs ms') g ms' md' L' A' q Hargv HRE ltac:(cbn; lia) Htid HS' eq_refl HR' HMR' Hin Ha0 (ex_intro _ vm' Hmd)).
+ rewrite <- Hfs. destruct Hres as [Ha0 _].
eapply src2_m1_oom; first [exact HS' | exact Ha0 | reflexivity | exact Hh' | exact Hlz' | exact Hch | eassumption].
Qed.
Lemma file_arm : forall sp brk mbase tid lim a0 path inp data rnd ms1,
in_argv inp = [a0; path] ->
valid_sp sp -> YN05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
valid_brk src2segs brk -> valid_mmap_base mbase -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> in_channel_reader inp = true ->
0 < bv_unsigned tid < 4194304 -> SRC_LIM_MIN <= lim ->
fs_lookup (in_fs inp) path = Some data ->
st_ok src2segs (E_main sp inp [a0; path] (in_envp inp) (in_execfn inp) tid rnd) (ss_m1 (kb_rseq (in_kernel inp))) ms1 ->
runs_at (bv_unsigned sp) (ms_mem ms1) (runs_main true sp (ed_top rnd) [a0; path] (in_envp inp) (in_execfn inp) rnd) ->
realizes src2segs (mkCfg ms1 (MD_file path tid brk mbase sp lim inp rnd)) (SPEC_loaded data (in_fs inp)).
Proof.
intros sp brk mbase tid lim a0 path inp data rnd ms1 Hargv Hsp Hceil Hbrk Hmb Hva Hve Hvfs Hvl Hlau Hcr Htid Hlim Hlk HS HR.
unfold SPEC_loaded. rewrite (tset_bind_eq _ _ _ _ _ (driver_tree_eq data)).
pose proof (do_jinv DOB data (in_fs inp)) as HJ. pose proof (do_gtree DOB data) as HGT.
assert (HSA0 : forall G, anchored_atoms G = anchored_atoms RD_facts
-> stack_anchored (E_main sp inp [a0; path] (in_envp inp) (in_execfn inp) tid rnd) G).
{ intros G HG. rewrite <- Hargv. eapply anchored_main; try eassumption.
all: rewrite HG; vm_compute; reflexivity. }
rewrite <- Hargv in HS.
pose proof (src2_malloc1 API AX sp brk mbase tid lim inp rnd) as M. lfeed M.
destruct (init_ledger (MD_file path tid brk mbase sp lim inp rnd) brk mbase sp lim inp ltac:(reflexivity) ltac:(reflexivity) Hsp Hbrk Hmb)
as (rx & Hvm0 & Hrx & Hrxl & Hvin).
eapply (M ms1 (MD_file path tid brk mbase sp lim inp rnd) rx);
[ exact Hvm0 | exact Hrx | exact Hrxl | exact Hvin | reflexivity | reflexivity | reflexivity | exact HS | |].
- exact (jinv_head_eq _ _ _ _ _ (driver_tree_eq data) HJ).
- intros res A' L' ms' md' g tr HS' HSA' HMR' HW' HB' [vm' Hmd] Hpath Hfr Hres.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (Hh' & Hlz' & _).
assert (Hch : fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) md').
{ split; [| split; [reflexivity | rewrite Hmd; exact Hcr]]. rewrite Hmd. autorewrite with model. unfold MD_file. autorewrite with model. rewrite MD0_fds. reflexivity. }
assert (Hfs : m_fs md' = in_fs inp).
{ rewrite Hmd. autorewrite with model. unfold MD_file. autorewrite with model. apply MD0_fs. }
destruct res as [b0|]; cbn [driver_after_m1 tset ret fst snd leaf_shape].
+ destruct Hres as (Ha0 & Hnz & b1 & b2 & Hub & Hub0).
assert (Hb12 : b1 = [] /\ b2 = []).
{ change (user_blocks init_state) with (@nil (sptr * Z)) in Hub0.
destruct b1; [| discriminate]. destruct b2; [| discriminate]. auto. }
destruct Hb12 as [-> ->]. cbn [app] in Hub.
assert (Hid : st_init_done A' = true).
{ exact (malloc_init_state_init_done CAP0 tr b0 A' ltac:(unfold CAP0; lia) (cpath_yields _ _ _ Hpath)). }
rewrite Hargv in HS'.
pose proof (src2_read_loop API AX sp tid a0 path inp data rnd Hlk HSA0 Hcr brk mbase lim (ms_regs ms') g ms' md' L' A' b0 vm' _
HS' Ha0 HMR' HW' HB' Hid Hub Hmd
(jinv_after_eq _ _ _ _ _ _ _ _ (driver_tree_eq data) HJ Hpath) (gtree_after_eq _ _ _ _ _ _ _ _ (driver_tree_eq data) HGT Hpath)
(fun r => t_eq_refl _) (src2_post API AX LIB fp_frm_zero_fx0 sp tid a0 path inp data rnd HSA0 _ (fun r => t_eq_refl _))) as X.
exact X.
+ rewrite <- Hfs. destruct Hres as [Ha0 _].
eapply src2_m1_oom; first [exact HS' | exact Ha0 | reflexivity | exact Hh' | exact Hlz' | exact Hch | eassumption].
Qed.
Lemma argv2_arm : forall sp brk mbase tid lim a0 path inp rnd ms,
in_argv inp = [a0; path] ->
valid_sp sp -> YN05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
valid_brk src2segs brk -> valid_mmap_base mbase -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> in_channel_reader inp = true ->
0 < bv_unsigned tid < 4194304 -> SRC_LIM_MIN <= lim ->
st_ok src2segs (E_main sp inp [a0; path] (in_envp inp) (in_execfn inp) tid rnd) (ss_main true (kb_rseq (in_kernel inp))) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp (ed_top rnd) [a0; path] (in_envp inp) (in_execfn inp) rnd) ->
realizes src2segs (mkCfg ms (MD0 tid brk mbase sp lim inp rnd)) (SPEC_args [a0; path] (in_fs inp)).
Proof.
intros sp brk mbase tid lim a0 path inp rnd ms Hargv Hsp Hceil Hbrk Hmb Hva Hve Hvfs Hvl Hlau Hcr Htid Hlim HS HR.
pose proof HCO as HCOh.
unfold SPEC_args, classify_open.
destruct (Nat.leb_spec path_max (length path)) as [Hlong|Hshort].
{ change path_max with 4096%nat in Hlong.
pose proof (src2_open_toolong sp brk mbase tid lim a0 path inp rnd) as X. lfeed X. exact (X ms Hlong HS HR). }
change path_max with 4096%nat in Hshort.
destruct (path_eqb path []) eqn:Enil.
{ apply path_eqb_eq in Enil.
pose proof (src2_open_empty sp brk mbase tid lim a0 path inp rnd) as X. lfeed X. exact (X ms Enil HS HR). }
assert (Hne : path <> []) by (intros ->; rewrite path_eqb_refl in Enil; discriminate).
destruct (path_eqb path dot_path) eqn:Edot.
{ apply path_eqb_eq in Edot. subst path.
pose proof (src2_open_dir sp brk mbase tid lim a0 dot_path inp rnd) as X. lfeed X.
apply (X ms eq_refl HS HR).
intros ms1 HS1 HR1. exact (dir_arm sp brk mbase tid lim a0 inp rnd ms1 Hargv Hsp Hceil Hbrk Hmb Hva Hve Hvl Hlau Hcr Htid Hlim HS1 HR1). }
assert (Hnd : path <> dot_path) by (intros ->; rewrite path_eqb_refl in Edot; discriminate).
pose proof (plain_name_of_argv a0 path ltac:(rewrite <- Hargv; exact Hva) Hnd) as Hpn.
destruct (fs_lookup (in_fs inp) path) as [data|] eqn:Hlk.
- pose proof (src2_open_file sp brk mbase tid lim a0 path inp rnd) as X. lfeed X.
apply (X ms data Hshort Hne Hpn Hlk HS HR).
intros ms1 HS1 HR1. exact (file_arm sp brk mbase tid lim a0 path inp data rnd ms1 Hargv Hsp Hceil Hbrk Hmb Hva Hve Hvfs Hvl Hlau Hcr Htid Hlim Hlk HS1 HR1).
- pose proof (src2_open_absent sp brk mbase tid lim a0 path inp rnd) as X. lfeed X.
exact (X ms Hshort Hne Hpn Hlk HS HR).
Qed.
(* #38: [valid_entry] at 727298f3 carries [entry_launch_ok_va] as its last
   conjunct (Run.v [valid_entry_sv48]), which is the premise the start-up
   layout facts need; [entry_stack_fits] no longer fixes the image. *)
Theorem src2_realizes_spec : forall sp brk mbase rnd lim inp,
valid_sp sp -> valid_brk src2segs brk -> valid_mmap_base mbase ->
entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
valid_input inp -> SRC_LIM_MIN <= lim ->
YN05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
realizes src2segs (init_config src2segs Plain_init_pc Plain_phdrs sp brk mbase rnd lim inp) (SPEC inp).
Proof.
intros sp brk mbase rnd lim inp Hsp Hbrk Hmb Hlau Hinp Hlim Hceil.
pose proof (valid_input_launch inp Hinp) as Hvl.
pose proof (valid_input_channel_reader inp Hinp) as Hcr.
destruct Hinp as (Hva & Hve & Hvfs & Hcreds).
unfold SPEC.
destruct (Nat.eq_dec (length (in_argv inp)) 2) as [Hlen | Hlen].
- destruct (in_argv inp) as [|a0 [|path [|x r]]] eqn:Hargv; try (cbn in Hlen; lia).
assert (Hva' : valid_argv (in_argv inp)) by (rewrite Hargv; exact Hva).
apply (src2_start true sp brk mbase rnd lim inp _ Hsp Hva' Hve Hvl Hlau); [rewrite Hargv; cbn; lia |].
intros ms tid Htid HS HR. rewrite Hargv in HS, HR.
change (with_tid tid (with_vdso (vdso_run_init (ed_vdso rnd)) (init_model (segments_reserved src2segs) brk mbase sp lim inp)))
with (MD0 tid brk mbase sp lim inp rnd).
exact (argv2_arm sp brk mbase tid lim a0 path inp rnd ms Hargv Hsp Hceil Hbrk Hmb Hva' Hve Hvfs Hvl Hlau Hcr Htid Hlim HS HR).
- apply (src2_start false sp brk mbase rnd lim inp _ Hsp Hva Hve Hvl Hlau I).
intros ms tid Htid HS HR.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp rnd) = []) by reflexivity.
change (with_tid tid (with_vdso (vdso_run_init (ed_vdso rnd)) (init_model (segments_reserved src2segs) brk mbase sp lim inp)))
with (MD0 tid brk mbase sp lim inp rnd).
replace (SPEC_args (in_argv inp) (in_fs inp)) with (diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
2:{ unfold SPEC_args. destruct (in_argv inp) as [|x [|y [|z r]]]; try reflexivity. cbn in Hlen. lia. }
change (in_fs inp) with (m_fs (MD0 tid brk mbase sp lim inp rnd)).
apply (HU sp brk mbase tid rnd inp ms _ Hsp Hva Hve Hvl Hlau).
+ exact Hlen.
+ apply st_ok_add_cond; [exact HS |].
assert (H3 : bv_unsigned (ew (E_main sp inp (in_argv inp) (in_envp inp) (in_execfn inp) tid rnd) 3) = Z.of_nat (length (in_argv inp)))
by (unfold E_main; eapply ew3; eassumption).
unfold branch_taken. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
apply Bool.negb_true_iff. apply bv_eqb_neq. intros Heq.
apply (f_equal bv_unsigned) in Heq. rewrite H3 in Heq. change (bv_unsigned (Z_to_bv 64 2)) with 2 in Heq. lia.
+ exact HR.
+ exact Hh.
+ exact Hlz.
+ split; [reflexivity | split; [reflexivity | exact Hcr]].
Qed.
End c.
End b.
