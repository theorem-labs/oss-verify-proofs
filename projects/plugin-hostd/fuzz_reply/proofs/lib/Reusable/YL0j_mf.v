(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0j.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Reusable/YL0j.v; 70 of its 208 lines of code are new or changed and 58 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO0e YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO06 YO04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YH00 YH01 YH03 YH02 YN3e.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Plain.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL0e YL0k YL0p YL0q YL0n YL0g YL0m YL0s YL0y YL0w YL0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI06 YI16 YI14 YI5b YI5c YL0i YL06 YL03 YL0l YL0t YL0z.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL0j YO0d_mf YO06_mf YL0e_mf YL0d_mf YL06_mf YL0n_mf YL0l_mf YL0u_mf YL0z_mf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.R Require Import Cfg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {rc : YM05.RunCeil} {LS : lib_shape}.
Section g.
Context {AM : AllocMode}.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).
Hypothesis HAM : amf = true.
Hypothesis Hmal : forall fx : FPState, malloc_realizes (fx:=fx) (AM:=AM) src0_msyms (aa_MR API).
Hypothesis Hfre : forall fx : FPState, free_realizes (fx:=fx) (AM:=AM) src0_msyms (aa_MR API).
Variable GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop.
Variable RI : list byte -> nat -> list (Z * Z) -> astate -> Prop.
Variable OUT : list byte -> list byte.
Hypothesis GIL : G_local_T src0segs src0_G GI.
Hypothesis GI0 : forall mem, G_img src0segs src0_G mem -> GI 0%nat [] mem.
Hypothesis LIBX : lib_contract_x_R_all src0_msyms API RI src0_G src0_R GI OUT LIBPC RA_LIB EMPTY LIB_STACK.
Hypothesis DRV : forall data, leaves (run_RI RI (payload data)) (driver_tree data).
Lemma dir_arm_mf : forall sp brk mbase tid lim a0 inp rnd ms1,
in_argv inp = [a0; dot_path] ->
valid_sp sp -> YM05.ceil_of_top (bv_unsigned sp - stack_max_size) -> YM05.rc_lim = lim ->
valid_brk src0segs brk -> valid_argv [a0; dot_path] -> valid_envp (in_envp inp) ->
entry_stack_fits sp [a0; dot_path] (in_envp inp) ->
0 < bv_unsigned tid < 4194304 -> SRC_LIM_MIN <= lim ->
st_ok src0segs (E_main sp [a0; dot_path] (in_envp inp) tid rnd) ss_m1 ms1 ->
runs_at (bv_unsigned sp) (ms_mem ms1) (runs_main true sp [a0; dot_path] (in_envp inp) rnd) ->
realizes src0segs (mkCfg ms1 (MD_dir tid brk mbase sp lim inp)) (SPEC_dir_mf dot_path (in_fs inp)).
Proof using AX HAM Hmal.
intros sp brk mbase tid lim a0 inp rnd ms1 Hargv Hsp Hceil Hrclim Hbrk Hva Hve Hfits Htid Hlim HS HR.
unfold SPEC_dir_mf. eapply rz_conseq; [| apply t_eq_sym; apply (tset_mf_bind_eq _ _ _ _ _ (dir_m_eq init_state))].
eapply (src0_malloc1_mf API AX HAM Hmal sp brk mbase tid lim [a0; dot_path] (in_envp inp) rnd Hsp Hbrk Hlim Hva Hve Hceil Hrclim ms1 (MD_dir tid brk mbase sp lim inp));
[ unfold MD_dir, MD0, init_model; autorewrite with model; reflexivity
| reflexivity | reflexivity | reflexivity | exact HS |].
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
pose proof (YM05.ceil_le_top _ Hceil) as Hle. revert Hle Ha1. unfold stack_max_size. lia. }
destruct res as [q|]; cbn [tset_mf dir_k ret fst snd].
+ rewrite <- Hfs. destruct Hres as (Ha0 & Hnz & b1 & b2 & Hub & _).
assert (Hin : In (q, CAP0) (user_blocks A')) by (rewrite Hub; apply in_app_iff; right; left; reflexivity).
pose proof (src0_dir_after_m1_mf API AX sp brk mbase tid lim [a0; dot_path] (in_envp inp) rnd Hsp Hva Hve Hfits Hceil a0 dot_path (ms_regs ms') g ms' md' L' A' q
eq_refl src0_read_error_hyp ltac:(cbn; lia) Htid HS' eq_refl HR' HMR' Hin Ha0 inp (ex_intro _ vm' Hmd)) as X.
exact X.
+ rewrite <- Hfs. destruct Hres as [Ha0 _].
exact (src0_m1_oom_mf sp tid [a0; dot_path] (in_envp inp) rnd (ms_regs ms') g ms' md' _ HS' Ha0 eq_refl Hh' Hlz' Hch eq_refl).
Qed.
Lemma file_arm_mf : forall sp brk mbase tid lim a0 path inp data rnd ms1,
in_argv inp = [a0; path] ->
valid_sp sp -> YM05.ceil_of_top (bv_unsigned sp - stack_max_size) -> YM05.rc_lim = lim ->
valid_brk src0segs brk -> valid_argv [a0; path] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
entry_stack_fits sp [a0; path] (in_envp inp) ->
0 < bv_unsigned tid < 4194304 -> SRC_LIM_MIN <= lim ->
fs_lookup (in_fs inp) path = Some data ->
st_ok src0segs (E_main sp [a0; path] (in_envp inp) tid rnd) ss_m1 ms1 ->
runs_at (bv_unsigned sp) (ms_mem ms1) (runs_main true sp [a0; path] (in_envp inp) rnd) ->
realizes src0segs (mkCfg ms1 (MD_file path tid brk mbase sp lim inp)) (SPECX_loaded_mf data (in_fs inp)).
Proof using AX HAM Hmal Hfre GIL GI0 LIBX DRV.
intros sp brk mbase tid lim a0 path inp data rnd ms1 Hargv Hsp Hceil Hrclim Hbrk Hva Hve Hvfs Hfits Htid Hlim Hlk HS HR.
unfold SPECX_loaded_mf. eapply rz_conseq; [| apply t_eq_sym; apply (tset_mf_bind_eq _ _ _ _ _ (driver_tree_eq data))].
pose proof (DRV data) as HL. rewrite (driver_tree_eq data) in HL.
assert (HSA0 : forall G, anchored_atoms G = anchored_atoms RD_facts -> stack_anchored (E_main sp [a0; path] (in_envp inp) tid rnd) G).
{ intros G HG. apply (anchored_main sp [a0; path] (in_envp inp) rnd Hsp Hva Hve Hceil G tid). rewrite HG. vm_compute. reflexivity. }
eapply (src0_malloc1_mf API AX HAM Hmal sp brk mbase tid lim [a0; path] (in_envp inp) rnd Hsp Hbrk Hlim Hva Hve Hceil Hrclim ms1 (MD_file path tid brk mbase sp lim inp));
[ unfold MD_file, MD0, init_model; autorewrite with model; reflexivity
| reflexivity | reflexivity | reflexivity | exact HS |].
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
pose proof (YM05.ceil_le_top _ Hceil) as Hle. revert Hle Ha1. unfold stack_max_size. lia. }
destruct res as [b0|]; cbn [driver_after_m1 tset_mf ret fst snd leaf_shape].
+ destruct Hres as (Ha0 & Hnz & b1 & b2 & Hub & Hub0).
assert (Hb12 : b1 = [] /\ b2 = []).
{ change (user_blocks init_state) with (@nil (sptr * Z)) in Hub0.
destruct b1; [| discriminate]. destruct b2; [| discriminate]. auto. }
destruct Hb12 as [-> ->]. cbn [app] in Hub.
assert (Hid : st_init_done A' = true).
{ exact (malloc_init_state_init_done CAP0 tr b0 A' ltac:(unfold CAP0; lia) (cpath_yields _ _ _ Hpath)). }
pose proof (src0_read_loop_mf API AX HAM Hmal Hfre sp tid a0 path inp data rnd Hlk HSA0 (run_RI RI (payload data)) brk mbase lim (ms_regs ms') g ms' md' L' A' b0 vm' _
HS' Ha0 HMR' HW' HB' Hid Hub Hmd
(leaves_mbind_after _ _ _ _ _ _ _ HL Hpath)
(fun r => t_eq_refl _) (src0_postX_mf API AX HAM Hmal Hfre GI RI OUT GIL GI0 LIBX fp_frm_zero_fx0 sp tid a0 path inp data rnd HSA0 Hvfs ltac:(exact (proj1 (proj2 Hsp))) _ (fun r => t_eq_refl _))) as X.
exact X.
+ rewrite <- Hfs. destruct Hres as [Ha0 _].
exact (src0_m1_oom_mf sp tid [a0; path] (in_envp inp) rnd (ms_regs ms') g ms' md' _ HS' Ha0 eq_refl Hh' Hlz' Hch eq_refl).
Qed.
Lemma argv2_arm_mf : forall sp brk mbase tid lim a0 path inp rnd ms,
in_argv inp = [a0; path] ->
valid_sp sp -> YM05.ceil_of_top (bv_unsigned sp - stack_max_size) -> YM05.rc_lim = lim ->
valid_brk src0segs brk -> valid_argv [a0; path] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
entry_stack_fits sp [a0; path] (in_envp inp) ->
0 < bv_unsigned tid < 4194304 -> SRC_LIM_MIN <= lim ->
st_ok src0segs (E_main sp [a0; path] (in_envp inp) tid rnd) ss_main_t ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp [a0; path] (in_envp inp) rnd) ->
realizes src0segs (mkCfg ms (MD0 tid brk mbase sp lim inp)) (SPECX_args_mf [a0; path] (in_fs inp)).
Proof using AX HAM Hmal Hfre GIL GI0 LIBX DRV.
intros sp brk mbase tid lim a0 path inp rnd ms Hargv Hsp Hceil Hrclim Hbrk Hva Hve Hvfs Hfits Htid Hlim HS HR.
unfold SPECX_args_mf, classify_open.
destruct (Nat.leb_spec path_max (length path)) as [Hlong|Hshort].
{ change path_max with 4096%nat in Hlong. exact (src0_open_toolong sp brk mbase tid lim a0 path inp rnd Hsp Hva Hve Htid Hfits src0_cannot_open_hyp ms Hlong HS HR). }
change path_max with 4096%nat in Hshort.
destruct (path_eqb path []) eqn:Enil.
{ apply path_eqb_eq in Enil. exact (src0_open_empty sp brk mbase tid lim a0 path inp rnd Hsp Hva Hve Htid Hfits src0_cannot_open_hyp ms Enil HS HR). }
assert (Hne : path <> []) by (intros ->; rewrite path_eqb_refl in Enil; discriminate).
destruct (path_eqb path dot_path) eqn:Edot.
{ apply path_eqb_eq in Edot. subst path.
apply (src0_open_dir sp brk mbase tid lim a0 dot_path inp rnd Hsp Hva Hve Htid Hfits src0_cannot_open_hyp ms eq_refl HS HR).
intros ms1 HS1 HR1. exact (dir_arm_mf sp brk mbase tid lim a0 inp rnd ms1 Hargv Hsp Hceil Hrclim Hbrk Hva Hve Hfits Htid Hlim HS1 HR1). }
assert (Hnd : path <> dot_path) by (intros ->; rewrite path_eqb_refl in Edot; discriminate).
pose proof (plain_name_of_argv a0 path Hva Hnd) as Hpn.
destruct (fs_lookup (in_fs inp) path) as [data|] eqn:Hlk.
- apply (src0_open_file sp brk mbase tid lim a0 path inp rnd Hsp Hva Hve Htid Hfits src0_cannot_open_hyp ms data Hshort Hne Hpn Hlk HS HR).
intros ms1 HS1 HR1. exact (file_arm_mf sp brk mbase tid lim a0 path inp data rnd ms1 Hargv Hsp Hceil Hrclim Hbrk Hva Hve Hvfs Hfits Htid Hlim Hlk HS1 HR1).
- exact (src0_open_absent sp brk mbase tid lim a0 path inp rnd Hsp Hva Hve Htid Hfits src0_cannot_open_hyp ms Hshort Hne Hpn Hlk HS HR).
Qed.
Theorem src0_realizes_specX_g : forall sp brk mbase rnd lim inp,
valid_sp sp -> valid_brk src0segs brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) ->
valid_input inp -> SRC_LIM_MIN <= lim ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
YM05.rc_lim = lim ->
realizes src0segs (init_config src0segs Plain_init_pc Plain_phdrs sp brk mbase rnd lim inp) (SPECX_mf inp).
Proof using AX HAM Hmal Hfre GIL GI0 LIBX DRV.
intros sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits (Hva & Hve & Hvfs & Hcreds) Hlim Hceil Hrclim.
unfold SPECX_mf.
destruct (Nat.eq_dec (length (in_argv inp)) 2) as [Hlen | Hlen].
- destruct (in_argv inp) as [|a0 [|path [|x r]]] eqn:Hargv; try (cbn in Hlen; lia).
apply (src0_start true sp brk mbase rnd lim inp _ Hsp); [rewrite Hargv; exact Hva | exact Hve | rewrite Hargv; exact Hfits | rewrite Hargv; cbn; lia |].
intros ms tid Htid HS HR. rewrite Hargv in HS, HR.
change (with_tid tid (init_model (segments_reserved src0segs) brk mbase sp lim inp)) with (MD0 tid brk mbase sp lim inp).
exact (argv2_arm_mf sp brk mbase tid lim a0 path inp rnd ms Hargv Hsp Hceil Hrclim Hbrk Hva Hve Hvfs Hfits Htid Hlim HS HR).
- apply (src0_start false sp brk mbase rnd lim inp _ Hsp Hva Hve Hfits I).
intros ms tid Htid HS HR.
assert (Hh : m_halted (with_tid tid (init_model (segments_reserved src0segs) brk mbase sp lim inp)) = None) by reflexivity.
assert (Hlz : m_vm_lazy (with_tid tid (init_model (segments_reserved src0segs) brk mbase sp lim inp)) = []) by reflexivity.
replace (SPECX_args_mf (in_argv inp) (in_fs inp)) with (diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
2:{ unfold SPECX_args_mf. destruct (in_argv inp) as [|x [|y [|z r]]]; try reflexivity. cbn in Hlen. lia. }
change (in_fs inp) with (m_fs (MD0 tid brk mbase sp lim inp)).
apply (src0_usage_hyp sp (in_argv inp) (in_envp inp) tid rnd ms _ Hsp Hva Hve Hfits).
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
End g.
Section c.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).
Hypothesis HMm : forall fx : FPState, malloc_realizes (fx:=fx) (AM:=MayFail) src0_msyms (aa_MR API).
Hypothesis HFm : forall fx : FPState, free_realizes (fx:=fx) (AM:=MayFail) src0_msyms (aa_MR API).
Hypothesis HFNm : forall fx : FPState, free_null_realizes (fx:=fx) (AM:=MayFail) src0_msyms.
Variable GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop.
Variable RI : list byte -> nat -> list (Z * Z) -> astate -> Prop.
Variable OUT : list byte -> list byte.
Hypothesis GIL : G_local_T src0segs src0_G GI.
Hypothesis GI0 : forall mem, G_img src0segs src0_G mem -> GI 0%nat [] mem.
Hypothesis LIBXm : lib_contract_x_R_all (AM:=MayFail) src0_msyms API RI src0_G src0_R GI OUT LIBPC RA_LIB EMPTY LIB_STACK.
Hypothesis DRV : forall data, leaves (run_RI RI (payload data)) (driver_tree data).
Theorem src0_realizes_specX_mf : forall sp brk mbase rnd lim inp,
  valid_sp sp -> valid_brk src0segs brk -> valid_mmap_base mbase ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  valid_input inp -> SRC_LIM_MIN <= lim ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  YM05.rc_lim = lim ->
  @realizes src0segs MayFail (init_config src0segs Plain_init_pc Plain_phdrs sp brk mbase rnd lim inp) (SPECX_mf inp).
Proof using AX HMm HFm HFNm GIL GI0 LIBXm DRV.
exact (src0_realizes_specX_g (AM:=MayFail) API AX eq_refl HMm HFm GI RI OUT GIL GI0 LIBXm DRV).
Qed.
End c.
End b.
