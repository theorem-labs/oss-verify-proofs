(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0j.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_qdisc/lib/Reusable/YL0j.v; 70 of its 208 lines of code are new or changed and 58 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput and its entry-launch facts; the channel-reader conjunct of fdchan; the allocation mode the allocator record carries (a refused munmap leaves a leaked map); the vDSO step cases and the launch's vDSO state). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK11 YK0o YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO0e YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO06 YO04.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YH00 YH01 YH03 YH02 YN3e.
From OSSVerify.reac_pw.fuzz_qdisc.images Require Import Plain.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL0e YL0k YL0p YL0q YL0n YL0g YL0m YL0s YL0y YL0w YL0x.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YI06 YI16 YI14 YI5b YI5c YL0i YL06 YL03 YL0l YL0t YL0z.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YL0j YO0d_mf YO06_mf YL0e_mf YL0d_mf YL06_mf YL0n_mf YL0l_mf YL0u_mf YL0z_mf.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable.R Require Import Cfg.
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
valid_brk src0segs brk -> valid_mmap_base mbase -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
0 < bv_unsigned tid < 4194304 -> SRC_LIM_MIN <= lim ->
st_ok src0segs (E_main sp inp tid rnd) ss_m1 ms1 ->
runs_at (bv_unsigned sp) (ms_mem ms1) (runs_main true sp inp rnd) ->
realizes src0segs (mkCfg ms1 (MD_dir tid brk mbase sp lim inp rnd)) (SPEC_dir_mf dot_path (in_fs inp)).
Proof using AX HAM Hmal.
intros sp brk mbase tid lim a0 inp rnd ms1 Hargv Hsp Hceil Hrclim Hbrk Hmb Hva Hve Hvl Hlau Hvi Htid Hlim HS HR.
unfold SPEC_dir_mf. eapply rz_conseq; [| apply t_eq_sym; apply (tset_mf_bind_eq _ _ _ _ _ (dir_m_eq init_state))].
eapply (src0_malloc1_mf API AX HAM Hmal sp brk mbase tid lim inp rnd Hsp Hbrk Hlim Hva Hve Hvl Hlau Hceil Hrclim Hmb ms1 (MD_dir tid brk mbase sp lim inp rnd));
[ unfold MD_dir, MD0, init_model; autorewrite with model; reflexivity
| reflexivity | reflexivity | reflexivity | exact HS | exact HR |].
- intros res A' L' ms' md' g tr HS' HSA' HMR' HW' HB' [vm' Hmd] Hpath Hfr Hres.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (Hh' & Hlz' & _).
assert (Hch : fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) md').
{ split; [| split; [reflexivity|]].
- rewrite Hmd. autorewrite with model. unfold MD_dir. autorewrite with model. rewrite MD0_fds. reflexivity.
- rewrite Hmd. autorewrite with model. unfold MD_dir. autorewrite with model. rewrite ?MD0_channel_reader. exact (valid_input_channel_reader inp Hvi). }
assert (Hfs : m_fs md' = in_fs inp).
{ rewrite Hmd. autorewrite with model. unfold MD_dir. autorewrite with model. apply MD0_fs. }
assert (HR' : runs_at (bv_unsigned sp) (ms_mem ms') (runs_main true sp inp rnd)).
{ eapply runs_at_mbyte; [| | exact HR].
- destruct Hsp as (H & _). revert H. unfold sp_window_lo. lia.
- intros a Ha1 Ha2. apply Hfr; [| exact Ha1 | exact Ha2].
pose proof (YM05.ceil_le_top _ Hceil) as Hle. revert Hle Ha1. unfold stack_max_size. lia. }
destruct res as [q|]; cbn [tset_mf dir_k ret fst snd].
+ rewrite <- Hfs. destruct Hres as (Ha0 & Hnz & b1 & b2 & Hub & _).
assert (Hin : In (q, CAP0) (user_blocks A')) by (rewrite Hub; apply in_app_iff; right; left; reflexivity).
pose proof (src0_dir_after_m1_mf API AX sp brk mbase tid lim inp rnd Hsp Hva Hve Hvl Hlau Hvi Hceil a0 dot_path (ms_regs ms') g ms' md' L' A' q
Hargv (src0_read_error_hyp (AM:=AM)) ltac:(cbn; lia) Htid HS' eq_refl HR' HMR' Hin Ha0 (ex_intro _ vm' Hmd)) as X.
exact X.
+ rewrite <- Hfs. destruct Hres as [Ha0 _].
exact (src0_m1_oom_mf sp tid inp rnd (ms_regs ms') g ms' md' _ HS' Ha0 eq_refl Hh' Hlz' Hch eq_refl).
Qed.
Lemma file_arm_mf : forall sp brk mbase tid lim a0 path inp data rnd ms1,
in_argv inp = [a0; path] ->
valid_sp sp -> YM05.ceil_of_top (bv_unsigned sp - stack_max_size) -> YM05.rc_lim = lim ->
valid_brk src0segs brk -> valid_mmap_base mbase -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
0 < bv_unsigned tid < 4194304 -> SRC_LIM_MIN <= lim ->
fs_lookup (in_fs inp) path = Some data ->
st_ok src0segs (E_main sp inp tid rnd) ss_m1 ms1 ->
runs_at (bv_unsigned sp) (ms_mem ms1) (runs_main true sp inp rnd) ->
realizes src0segs (mkCfg ms1 (MD_file path tid brk mbase sp lim inp rnd)) (SPECX_loaded_mf data (in_fs inp)).
Proof using AX HAM Hmal Hfre GIL GI0 LIBX DRV.
intros sp brk mbase tid lim a0 path inp data rnd ms1 Hargv Hsp Hceil Hrclim Hbrk Hmb Hva Hve Hvfs Hvl Hlau Hvi Htid Hlim Hlk HS HR.
unfold SPECX_loaded_mf. eapply rz_conseq; [| apply t_eq_sym; apply (tset_mf_bind_eq _ _ _ _ _ (driver_tree_eq data))].
pose proof (DRV data) as HL. rewrite (driver_tree_eq data) in HL.
assert (HSA0 : forall G, anchored_atoms G = anchored_atoms RD_facts -> stack_anchored (E_main sp inp tid rnd) G).
{ intros G HG. eapply anchored_main; first [eassumption | rewrite HG; vm_compute; reflexivity]. }
eapply (src0_malloc1_mf API AX HAM Hmal sp brk mbase tid lim inp rnd Hsp Hbrk Hlim Hva Hve Hvl Hlau Hceil Hrclim Hmb ms1 (MD_file path tid brk mbase sp lim inp rnd));
[ unfold MD_file, MD0, init_model; autorewrite with model; reflexivity
| reflexivity | reflexivity | reflexivity | exact HS | exact HR |].
- intros res A' L' ms' md' g tr HS' HSA' HMR' HW' HB' [vm' Hmd] Hpath Hfr Hres.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (Hh' & Hlz' & _).
assert (Hch : fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) md').
{ split; [| split; [reflexivity|]].
- rewrite Hmd. autorewrite with model. unfold MD_file. autorewrite with model. rewrite MD0_fds. reflexivity.
- rewrite Hmd. autorewrite with model. unfold MD_file. autorewrite with model. rewrite ?MD0_channel_reader. exact (valid_input_channel_reader inp Hvi). }
assert (Hfs : m_fs md' = in_fs inp).
{ rewrite Hmd. autorewrite with model. unfold MD_file. autorewrite with model. apply MD0_fs. }
assert (HR' : runs_at (bv_unsigned sp) (ms_mem ms') (runs_main true sp inp rnd)).
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
pose proof (src0_read_loop_mf API AX HAM Hmal Hfre sp tid path inp data rnd Hlk HSA0 (run_RI RI (payload data)) brk mbase lim (ms_regs ms') g ms' md' L' A' b0 vm' _
HS' Ha0 HMR' HW' HB' Hid Hub Hmd
(* the reader premise of [src0_read_loop], proved from this arm's [valid_input] *)
(valid_input_channel_reader inp Hvi)
(leaves_mbind_after _ _ _ _ _ _ _ HL Hpath)
(fun r => t_eq_refl _) (src0_postX_mf API AX HAM Hmal Hfre GI RI OUT GIL GI0 LIBX fp_frm_zero_fx0 sp tid inp data rnd HSA0 Hvfs ltac:(exact (proj1 (proj2 Hsp))) _ (fun r => t_eq_refl _))) as X.
exact X.
+ rewrite <- Hfs. destruct Hres as [Ha0 _].
exact (src0_m1_oom_mf sp tid inp rnd (ms_regs ms') g ms' md' _ HS' Ha0 eq_refl Hh' Hlz' Hch eq_refl).
Qed.
(* The open wrappers take the cannot-open fact as a proof argument: [YL0w.src0_cannot_open_hyp] at this
   section's mode (YL0j's [HCO] is the AcfgMode instance). *)
Lemma argv2_arm_mf : forall sp brk mbase tid lim a0 path inp rnd ms,
in_argv inp = [a0; path] ->
valid_sp sp -> YM05.ceil_of_top (bv_unsigned sp - stack_max_size) -> YM05.rc_lim = lim ->
valid_brk src0segs brk -> valid_mmap_base mbase -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
0 < bv_unsigned tid < 4194304 -> SRC_LIM_MIN <= lim ->
st_ok src0segs (E_main sp inp tid rnd) ss_main_t ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp inp rnd) ->
realizes src0segs (mkCfg ms (MD0 tid brk mbase sp lim inp rnd)) (SPECX_args_mf [a0; path] (in_fs inp)).
Proof using AX HAM Hmal Hfre GIL GI0 LIBX DRV.
intros sp brk mbase tid lim a0 path inp rnd ms Hargv Hsp Hceil Hrclim Hbrk Hmb Hva Hve Hvfs Hvl Hlau Hvi Htid Hlim HS HR.
unfold SPECX_args_mf, classify_open.
destruct (Nat.leb_spec path_max (length path)) as [Hlong|Hshort].
{ change path_max with 4096%nat in Hlong.
  exact (src0_open_toolong sp brk mbase tid lim a0 path inp rnd
    Hargv Hsp Hva Hve Htid Hvl Hlau Hvi (src0_cannot_open_hyp (AM:=AM)) ms Hlong HS HR). }
change path_max with 4096%nat in Hshort.
destruct (path_eqb path []) eqn:Enil.
{ apply path_eqb_eq in Enil.
  exact (src0_open_empty sp brk mbase tid lim a0 path inp rnd
    Hargv Hsp Hva Hve Htid Hvl Hlau Hvi (src0_cannot_open_hyp (AM:=AM)) ms Enil HS HR). }
assert (Hne : path <> []) by (intros ->; rewrite path_eqb_refl in Enil; discriminate).
destruct (path_eqb path dot_path) eqn:Edot.
{ apply path_eqb_eq in Edot. subst path.
eapply src0_open_dir;
first [eassumption | reflexivity | exact (src0_cannot_open_hyp (AM:=AM))
| intros ms1 HS1 HR1;
exact (dir_arm_mf sp brk mbase tid lim a0 inp rnd ms1 Hargv Hsp Hceil Hrclim Hbrk Hmb Hva Hve Hvl Hlau Hvi Htid Hlim HS1 HR1)]. }
assert (Hnd : path <> dot_path) by (intros ->; rewrite path_eqb_refl in Edot; discriminate).
pose proof (plain_name_of_argv a0 path ltac:(rewrite <- Hargv; exact Hva) Hnd) as Hpn.
destruct (fs_lookup (in_fs inp) path) as [data|] eqn:Hlk.
- eapply src0_open_file with (data := data);
first [eassumption | reflexivity | exact (src0_cannot_open_hyp (AM:=AM))
| intros ms1 HS1 HR1;
exact (file_arm_mf sp brk mbase tid lim a0 path inp data rnd ms1 Hargv Hsp Hceil Hrclim Hbrk Hmb Hva Hve Hvfs Hvl Hlau Hvi Htid Hlim Hlk HS1 HR1)].
- exact (src0_open_absent sp brk mbase tid lim a0 path inp rnd
    Hargv Hsp Hva Hve Htid Hvl Hlau Hvi (src0_cannot_open_hyp (AM:=AM)) ms Hshort Hne Hpn Hlk HS HR).
Qed.
Theorem src0_realizes_specX_g : forall sp brk mbase rnd lim inp,
valid_sp sp -> valid_brk src0segs brk -> valid_mmap_base mbase ->
entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
valid_input inp -> SRC_LIM_MIN <= lim ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
YM05.rc_lim = lim ->
realizes src0segs (init_config src0segs Plain_init_pc Plain_phdrs sp brk mbase rnd lim inp) (SPECX_mf inp).
Proof using AX HAM Hmal Hfre GIL GI0 LIBX DRV.
intros sp brk mbase rnd lim inp Hsp Hbrk Hmb Hlau Hvi Hlim Hceil Hrclim.
assert (Hva : valid_argv (in_argv inp)) by (unfold valid_input in Hvi; tauto).
assert (Hve : valid_envp (in_envp inp)) by (unfold valid_input in Hvi; tauto).
assert (Hvfs : valid_fs (in_fs inp)) by (unfold valid_input in Hvi; tauto).
assert (Hvl : valid_launch inp) by (unfold valid_input in Hvi; tauto).
unfold SPECX_mf.
destruct (Nat.eq_dec (length (in_argv inp)) 2) as [Hlen | Hlen].
- destruct (in_argv inp) as [|a0 [|path [|x r]]] eqn:Hargv; try (cbn in Hlen; lia).
(* [destruct ... eqn:] rewrote [Hva] to the literal list; the callees read it at [in_argv inp]. *)
rewrite <- Hargv in Hva.
apply (src0_start true sp brk mbase rnd lim inp _ Hsp Hva Hve Hvl Hlau ltac:(rewrite Hargv; cbn; lia)).
intros ms tid Htid HS HR.
change (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rnd)) (init_model (segments_reserved src0segs) brk mbase sp lim inp))) with (MD0 tid brk mbase sp lim inp rnd).
exact (argv2_arm_mf sp brk mbase tid lim a0 path inp rnd ms Hargv Hsp Hceil Hrclim Hbrk Hmb Hva Hve Hvfs Hvl Hlau Hvi Htid Hlim HS HR).
- apply (src0_start false sp brk mbase rnd lim inp _ Hsp Hva Hve Hvl Hlau I).
intros ms tid Htid HS HR.
assert (Hh : m_halted (with_tid tid (init_model (segments_reserved src0segs) brk mbase sp lim inp)) = None) by reflexivity.
assert (Hlz : m_vm_lazy (with_tid tid (init_model (segments_reserved src0segs) brk mbase sp lim inp)) = []) by reflexivity.
replace (SPECX_args_mf (in_argv inp) (in_fs inp)) with (diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
2:{ unfold SPECX_args_mf. destruct (in_argv inp) as [|x [|y [|z r]]]; try reflexivity. cbn in Hlen. lia. }
change (in_fs inp) with (m_fs (MD0 tid brk mbase sp lim inp rnd)).
apply (src0_usage_hyp (AM:=AM) sp brk mbase tid rnd inp ms _ Hsp Hva Hve Hvl Hlau Hvi).
+ exact Hlen.
+ apply st_ok_add_cond; [exact HS |].
assert (H3 : bv_unsigned (ew (E_main sp inp tid rnd) 3) = Z.of_nat (length (in_argv inp)))
by (unfold E_main; exact (YP08.ew3 src0segs Plain_phdrs inp mbase Plain_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia) (xw_main inp rnd tid) (xd_main rnd))).
unfold branch_taken. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
apply Bool.negb_true_iff. apply bv_eqb_neq. intros Heq.
apply (f_equal bv_unsigned) in Heq. rewrite H3 in Heq. change (bv_unsigned (Z_to_bv 64 2)) with 2 in Heq. lia.
+ exact HR.
+ exact Hh.
+ exact Hlz.
+ (* 727298f3: [fdchan] has three conjuncts; the channel reader is the launch's ([valid_input]). *)
  split; [reflexivity | split; [reflexivity |]].
  exact (valid_input_channel_reader inp Hvi).
Qed.
End g.
Section c.
(* 08b1429: the may-fail record (YO0d.AllocAPI carries its mode; ZAllocatorMF.zlib_API_mf). *)
Variable API : AllocAPI (AM:=MayFail) src0_msyms.
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
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
  valid_input inp -> SRC_LIM_MIN <= lim ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  YM05.rc_lim = lim ->
  @realizes src0segs MayFail (init_config src0segs Plain_init_pc Plain_phdrs sp brk mbase rnd lim inp) (SPECX_mf inp).
Proof using AX HMm HFm HFNm GIL GI0 LIBXm DRV.
exact (src0_realizes_specX_g (AM:=MayFail) API AX eq_refl HMm HFm GI RI OUT GIL GI0 LIBXm DRV).
Qed.
End c.
End b.
