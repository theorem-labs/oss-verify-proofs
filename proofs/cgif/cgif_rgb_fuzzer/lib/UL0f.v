(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YK0o YK0q YQ0k YN06 YN02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ0d YQ05 YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e YP07.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH05 UH07 UH06 UO3p.
From OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO04 YL05 YL01 UL06 YL0b YL0c UL0g UL0l UL0m UL0j YL0e UL0i UL0h UL0o UL0u UL0t UL0r UL0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
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
Variable API : AllocAPI ubs2_msyms.
Hypothesis AX : AllocExtra ubs2_msyms (aa_MR API).
Lemma HU : usage_hyp.
Proof. exact ubs2_usage_hyp. Qed.
Lemma HCO : cannot_open_hyp.
Proof. exact ubs2_cannot_open_hyp. Qed.
Lemma HRE : read_error_hyp.
Proof. exact ubs2_read_error_hyp. Qed.
Hypothesis LIB : lib_contract_all ubs2_msyms API LIBPC RA_LIB EMPTY LIB_STACK_RGB.
Hypothesis DOB : driver_obligations.
Lemma dir_arm : forall sp brk mbase tid lim a0 inp rnd ms1,
in_argv inp = [a0; dot_path] ->
valid_sp sp -> YN05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
valid_brk ubs2segs brk -> valid_argv [a0; dot_path] -> valid_envp (in_envp inp) ->
entry_stack_fits sp [a0; dot_path] (in_envp inp) ->
0 < bv_unsigned tid < 4194304 -> SRC_LIM_MIN <= lim ->
st_ok ubs2segs (E_main sp [a0; dot_path] (in_envp inp) tid rnd) ss_m1 ms1 ->
runs_at (bv_unsigned sp) (ms_mem ms1) (runs_main true sp [a0; dot_path] (in_envp inp) rnd) ->
realizes ubs2segs (mkCfg ms1 (MD_dir tid brk mbase sp lim inp)) (SPEC_dir dot_path (in_fs inp)).
Proof.
intros sp brk mbase tid lim a0 inp rnd ms1 Hargv Hsp Hceil Hbrk Hva Hve Hfits Htid Hlim HS HR.
unfold SPEC_dir. rewrite (tset_bind_eq _ _ _ _ _ (dir_m_eq init_state)).
eapply (ubs2_malloc1 API AX sp brk mbase tid lim [a0; dot_path] (in_envp inp) rnd Hsp Hbrk Hlim Hva Hve Hceil ms1 (MD_dir tid brk mbase sp lim inp));
[ unfold MD_dir, MD0, init_model; autorewrite with model; reflexivity
| reflexivity | reflexivity | reflexivity | exact HS | |].
- exact (jinv_head_eq _ _ _ _ _ (dir_m_eq init_state) (dir_jinv dot_path (in_fs inp))).
- intros res A' L' ms' md' g tr HS' HSA' HMR' HW' HB' [vm' Hmd] Hpath Hfr Hres.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (Hh' & Hlz' & _).
assert (Hch : fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) md').
{ split; [| reflexivity]. rewrite Hmd. autorewrite with model. unfold MD_dir. autorewrite with model. rewrite MD0_fds. reflexivity. }
assert (Hfs : m_fs md' = in_fs inp).
{ rewrite Hmd. autorewrite with model. unfold MD_dir. autorewrite with model. apply MD0_fs. }
assert (HR' : runs_at (bv_unsigned sp) (ms_mem ms') (runs_main true sp [a0; dot_path] (in_envp inp) rnd)).
{ eapply runs_at_mbyte; [| | exact HR].
- destruct Hsp as (H & _). revert H. unfold sp_window_lo. lia.
- intros a Ha1 Ha2. apply Hfr; [| exact Ha1 | exact Ha2].
pose proof (YN05.ceil_le_top _ Hceil) as Hle. revert Hle Ha1. unfold stack_max_size. lia. }
destruct res as [q|]; cbn [tset dir_k ret fst snd].
+ rewrite <- Hfs. destruct Hres as (Ha0 & Hnz & b1 & b2 & Hub & _).
assert (Hin : In (q, CAP0) (user_blocks A')) by (rewrite Hub; apply in_app_iff; right; left; reflexivity).
pose proof (ubs2_dir_after_m1 API AX sp brk mbase tid lim [a0; dot_path] (in_envp inp) rnd Hsp Hva Hve Hfits Hceil a0 dot_path (ms_regs ms') g ms' md' L' A' q
eq_refl HRE ltac:(cbn; lia) Htid HS' eq_refl HR' HMR' Hin Ha0 inp (ex_intro _ vm' Hmd)) as X.
exact X.
+ rewrite <- Hfs. destruct Hres as [Ha0 _].
exact (ubs2_m1_oom sp tid [a0; dot_path] (in_envp inp) rnd (ms_regs ms') g ms' md' _ HS' Ha0 eq_refl Hh' Hlz' Hch eq_refl).
Qed.
Lemma file_arm : forall sp brk mbase tid lim a0 path inp data rnd ms1,
in_argv inp = [a0; path] ->
valid_sp sp -> YN05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
valid_brk ubs2segs brk -> valid_argv [a0; path] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
entry_stack_fits sp [a0; path] (in_envp inp) ->
0 < bv_unsigned tid < 4194304 -> SRC_LIM_MIN <= lim ->
fs_lookup (in_fs inp) path = Some data ->
st_ok ubs2segs (E_main sp [a0; path] (in_envp inp) tid rnd) ss_m1 ms1 ->
runs_at (bv_unsigned sp) (ms_mem ms1) (runs_main true sp [a0; path] (in_envp inp) rnd) ->
realizes ubs2segs (mkCfg ms1 (MD_file path tid brk mbase sp lim inp)) (SPEC_loaded data (in_fs inp)).
Proof.
intros sp brk mbase tid lim a0 path inp data rnd ms1 Hargv Hsp Hceil Hbrk Hva Hve Hvfs Hfits Htid Hlim Hlk HS HR.
unfold SPEC_loaded. rewrite (tset_bind_eq _ _ _ _ _ (driver_tree_eq data)).
pose proof (do_jinv DOB data (in_fs inp)) as HJ. pose proof (do_gtree DOB data) as HGT.
assert (HSA0 : forall G, anchored_atoms G = anchored_atoms RD_facts -> stack_anchored (E_main sp [a0; path] (in_envp inp) tid rnd) G).
{ intros G HG. apply (anchored_main sp [a0; path] (in_envp inp) rnd Hsp Hva Hve Hceil G tid). rewrite HG. vm_compute. reflexivity. }
eapply (ubs2_malloc1 API AX sp brk mbase tid lim [a0; path] (in_envp inp) rnd Hsp Hbrk Hlim Hva Hve Hceil ms1 (MD_file path tid brk mbase sp lim inp));
[ unfold MD_file, MD0, init_model; autorewrite with model; reflexivity
| reflexivity | reflexivity | reflexivity | exact HS | |].
- exact (jinv_head_eq _ _ _ _ _ (driver_tree_eq data) HJ).
- intros res A' L' ms' md' g tr HS' HSA' HMR' HW' HB' [vm' Hmd] Hpath Hfr Hres.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (Hh' & Hlz' & _).
assert (Hch : fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) md').
{ split; [| reflexivity]. rewrite Hmd. autorewrite with model. unfold MD_file. autorewrite with model. rewrite MD0_fds. reflexivity. }
assert (Hfs : m_fs md' = in_fs inp).
{ rewrite Hmd. autorewrite with model. unfold MD_file. autorewrite with model. apply MD0_fs. }
assert (HR' : runs_at (bv_unsigned sp) (ms_mem ms') (runs_main true sp [a0; path] (in_envp inp) rnd)).
{ eapply runs_at_mbyte; [| | exact HR].
- destruct Hsp as (H & _). revert H. unfold sp_window_lo. lia.
- intros a Ha1 Ha2. apply Hfr; [| exact Ha1 | exact Ha2].
pose proof (YN05.ceil_le_top _ Hceil) as Hle. revert Hle Ha1. unfold stack_max_size. lia. }
destruct res as [b0|]; cbn [driver_after_m1 tset ret fst snd leaf_shape].
+ destruct Hres as (Ha0 & Hnz & b1 & b2 & Hub & Hub0).
assert (Hb12 : b1 = [] /\ b2 = []).
{ change (user_blocks init_state) with (@nil (sptr * Z)) in Hub0.
destruct b1; [| discriminate]. destruct b2; [| discriminate]. auto. }
destruct Hb12 as [-> ->]. cbn [app] in Hub.
assert (Hid : st_init_done A' = true).
{ exact (malloc_init_state_init_done CAP0 tr b0 A' ltac:(unfold CAP0; lia) (cpath_yields _ _ _ Hpath)). }
pose proof (ubs2_read_loop API AX sp tid a0 path inp data rnd Hlk HSA0 brk mbase lim (ms_regs ms') g ms' md' L' A' b0 vm' _
HS' Ha0 HMR' HW' HB' Hid Hub Hmd
(jinv_after_eq _ _ _ _ _ _ _ _ (driver_tree_eq data) HJ Hpath) (gtree_after_eq _ _ _ _ _ _ _ _ (driver_tree_eq data) HGT Hpath)
(fun r => t_eq_refl _) (ubs2_post API AX LIB fp_frm_zero_fx0 sp tid a0 path inp data rnd HSA0 _ (fun r => t_eq_refl _))) as X.
exact X.
+ rewrite <- Hfs. destruct Hres as [Ha0 _].
exact (ubs2_m1_oom sp tid [a0; path] (in_envp inp) rnd (ms_regs ms') g ms' md' _ HS' Ha0 eq_refl Hh' Hlz' Hch eq_refl).
Qed.
Lemma argv2_arm : forall sp brk mbase tid lim a0 path inp rnd ms,
in_argv inp = [a0; path] ->
valid_sp sp -> YN05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
valid_brk ubs2segs brk -> valid_argv [a0; path] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
entry_stack_fits sp [a0; path] (in_envp inp) ->
0 < bv_unsigned tid < 4194304 -> SRC_LIM_MIN <= lim ->
st_ok ubs2segs (E_main sp [a0; path] (in_envp inp) tid rnd) ss_main_t ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp [a0; path] (in_envp inp) rnd) ->
realizes ubs2segs (mkCfg ms (MD0 tid brk mbase sp lim inp)) (SPEC_args [a0; path] (in_fs inp)).
Proof.
intros sp brk mbase tid lim a0 path inp rnd ms Hargv Hsp Hceil Hbrk Hva Hve Hvfs Hfits Htid Hlim HS HR.
unfold SPEC_args, classify_open.
destruct (Nat.leb_spec path_max (length path)) as [Hlong|Hshort].
{ change path_max with 4096%nat in Hlong. exact (ubs2_open_toolong sp brk mbase tid lim a0 path inp rnd Hsp Hva Hve Htid Hfits HCO ms Hlong HS HR). }
change path_max with 4096%nat in Hshort.
destruct (path_eqb path []) eqn:Enil.
{ apply path_eqb_eq in Enil. exact (ubs2_open_empty sp brk mbase tid lim a0 path inp rnd Hsp Hva Hve Htid Hfits HCO ms Enil HS HR). }
assert (Hne : path <> []) by (intros ->; rewrite path_eqb_refl in Enil; discriminate).
destruct (path_eqb path dot_path) eqn:Edot.
{ apply path_eqb_eq in Edot. subst path.
apply (ubs2_open_dir sp brk mbase tid lim a0 dot_path inp rnd Hsp Hva Hve Htid Hfits HCO ms eq_refl HS HR).
intros ms1 HS1 HR1. exact (dir_arm sp brk mbase tid lim a0 inp rnd ms1 Hargv Hsp Hceil Hbrk Hva Hve Hfits Htid Hlim HS1 HR1). }
assert (Hnd : path <> dot_path) by (intros ->; rewrite path_eqb_refl in Edot; discriminate).
pose proof (plain_name_of_argv a0 path Hva Hnd) as Hpn.
destruct (fs_lookup (in_fs inp) path) as [data|] eqn:Hlk.
- apply (ubs2_open_file sp brk mbase tid lim a0 path inp rnd Hsp Hva Hve Htid Hfits HCO ms data Hshort Hne Hpn Hlk HS HR).
intros ms1 HS1 HR1. exact (file_arm sp brk mbase tid lim a0 path inp data rnd ms1 Hargv Hsp Hceil Hbrk Hva Hve Hvfs Hfits Htid Hlim Hlk HS1 HR1).
- exact (ubs2_open_absent sp brk mbase tid lim a0 path inp rnd Hsp Hva Hve Htid Hfits HCO ms Hshort Hne Hpn Hlk HS HR).
Qed.
Theorem ubs2_realizes_spec : forall sp brk mbase rnd lim inp,
valid_sp sp -> valid_brk ubs2segs brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) ->
valid_input inp -> SRC_LIM_MIN <= lim ->
YN05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
realizes ubs2segs (init_config ubs2segs Ubsan_init_pc Ubsan_phdrs sp brk mbase rnd lim inp) (SPEC inp).
Proof.
intros sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits (Hva & Hve & Hvfs & Hcreds) Hlim Hceil.
unfold SPEC.
destruct (Nat.eq_dec (length (in_argv inp)) 2) as [Hlen | Hlen].
- destruct (in_argv inp) as [|a0 [|path [|x r]]] eqn:Hargv; try (cbn in Hlen; lia).
apply (ubs2_start true sp brk mbase rnd lim inp _ Hsp); [rewrite Hargv; exact Hva | exact Hve | rewrite Hargv; exact Hfits | rewrite Hargv; cbn; lia |].
intros ms tid Htid HS HR. rewrite Hargv in HS, HR.
change (with_tid tid (init_model (segments_reserved ubs2segs) brk mbase sp lim inp)) with (MD0 tid brk mbase sp lim inp).
exact (argv2_arm sp brk mbase tid lim a0 path inp rnd ms Hargv Hsp Hceil Hbrk Hva Hve Hvfs Hfits Htid Hlim HS HR).
- apply (ubs2_start false sp brk mbase rnd lim inp _ Hsp Hva Hve Hfits I).
intros ms tid Htid HS HR.
assert (Hh : m_halted (with_tid tid (init_model (segments_reserved ubs2segs) brk mbase sp lim inp)) = None) by reflexivity.
assert (Hlz : m_vm_lazy (with_tid tid (init_model (segments_reserved ubs2segs) brk mbase sp lim inp)) = []) by reflexivity.
replace (SPEC_args (in_argv inp) (in_fs inp)) with (diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
2:{ unfold SPEC_args. destruct (in_argv inp) as [|x [|y [|z r]]]; try reflexivity. cbn in Hlen. lia. }
change (in_fs inp) with (m_fs (MD0 tid brk mbase sp lim inp)).
apply (HU sp (in_argv inp) (in_envp inp) tid rnd ms _ Hsp Hva Hve Hfits).
+ exact Hlen.
+ apply st_ok_add_cond; [exact HS |].
pose proof (ew3 sp (in_argv inp) (in_envp inp) Hva (xw_main sp (in_argv inp) (in_envp inp) tid rnd) (xd_main rnd)) as H3.
change (E0 _ _ _ _ _) with (E_main sp (in_argv inp) (in_envp inp) tid rnd) in H3.
unfold branch_taken. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
apply Bool.negb_true_iff. apply bv_eqb_neq. intros Heq.
apply (f_equal bv_unsigned) in Heq. rewrite H3 in Heq. change (bv_unsigned (Z_to_bv 64 2)) with 2 in Heq. lia.
+ exact HR.
+ exact Hh.
+ exact Hlz.
+ split; reflexivity.
Qed.
End c.
End b.
