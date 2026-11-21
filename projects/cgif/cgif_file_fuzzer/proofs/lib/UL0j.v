(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch premises entry_launch_ok_va and valid_input; the run's CONFIG_RSEQ flag; the start-up stack anchored at its top; AT_EXECFN; the vDSO's mappings and steps; the launch's channel-reader and SIGPIPE fields): changed ROOMX, dir_arm, file_arm, argv2_arm, ubs0_realizes_specX. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0o YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO06 YO04.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH01 UH03 UH02 UN3e.
From OSSVerify.cgif.cgif_file_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN03 YL07 YL01 YL08 YL0d YL0e UL0k UL0p UL0q UL0n YL0g UL0m UL0s UL0y UL0w UL0x.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI06 YI16 YI14 UI5b UI5c YL0i YL06 YL03 UL0l UL0t UL0z.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {rc : YM05.RunCeil} {LS : lib_shape}.
Lemma plain_name_of_argv : forall a0 path, valid_argv [a0; path] -> path <> dot_path -> openat_plain_name path = true.
Proof using.
intros a0 path (_ & _ & _ & _ & HF) Hnd. cbn [tl] in HF. apply Forall_inv in HF. destruct HF as [Hs Hdd].
unfold openat_plain_name, path_is_dirref. rewrite Hs, Hdd.
destruct (path_eqb path dot_path) eqn:E; [apply path_eqb_eq in E; contradiction | reflexivity].
Qed.
Section c.
Variable API : AllocAPI ubs0_msyms.
Hypothesis AX : AllocExtra ubs0_msyms (aa_MR API).
Lemma HU : usage_hyp.
Proof using. exact ubs0_usage_hyp. Qed.
Lemma HCO : cannot_open_hyp.
Proof using. exact ubs0_cannot_open_hyp. Qed.
Lemma HRE : read_error_hyp.
Proof using. exact ubs0_read_error_hyp. Qed.
Hypothesis LIBX : lib_contract_x_all ubs0_msyms API LIBPC RA_LIB EMPTY LIB_STACK.
Hypothesis DOB : driver_obligationsX.
Hypothesis ROOMX : forall data, room_calls (payload_len data) (calls data) DRB.
(* Throughout this file [entry_stack_fits] is REPLACED by the three premises the new
   initial-state theorem asks for ([valid_launch], [entry_launch_ok_va], [valid_input]:
   UN3e.v:597-599).  Only [entry_launch_ok_va] is genuinely new at the top: [valid_launch]
   is conjunct 13 of [valid_input] (75d69e00:theories/LinuxProcessSem/Run.v:4596) and
   [entry_launch_ok_va] is conjunct 5 of the published [valid_entry]
   (75d69e00:Run.v:3733-3738), so the quantifier of the published statement supplies it.
   [E_main] gained [inp] and [efn], [runs_main] takes [ed_top rnd] instead of the draw, and
   the layout facts are stated over [in_argv inp], so the two-element argv travels as an
   EQUATION rather than as a free list. *)
Lemma dir_arm : forall sp brk mbase tid lim a0 inp rnd ms1,
in_argv inp = [a0; dot_path] ->
valid_sp sp -> YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
valid_brk ubs0segs brk -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
0 < bv_unsigned tid < 4194304 -> SRC_LIM_MIN <= lim ->
st_ok ubs0segs (E_main sp inp [a0; dot_path] (in_envp inp) (in_execfn inp) tid rnd) ss_m1 ms1 ->
runs_at (bv_unsigned sp) (ms_mem ms1) (runs_main (kb_rseq (in_kernel inp)) true sp (ed_top rnd) [a0; dot_path] (in_envp inp) (in_execfn inp)) ->
realizes ubs0segs (mkCfg ms1 (MD_dir tid brk mbase sp lim inp rnd)) (SPEC_dir dot_path (in_fs inp)).
Proof using AX.
intros sp brk mbase tid lim a0 inp rnd ms1 Hargv Hsp Hceil Hbrk Hva Hve Hvl Hlau Hvi Htid Hlim HS HR.
rewrite <- Hargv in HS, HR.
unfold SPEC_dir. rewrite (tset_bind_eq _ _ _ _ _ (dir_m_eq init_state)).
eapply (ubs0_malloc1 API AX sp brk mbase tid lim inp rnd Hsp Hbrk Hlim Hva Hve Hvl Hlau Hvi Hceil ms1 (MD_dir tid brk mbase sp lim inp rnd)
(vdso_reserved (in_kernel inp) (page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)))));
[ reflexivity
| exact (MD0_rx_ok sp brk mbase rnd inp Hsp Hbrk Hlau Hvi)
| apply (MD0_vdso_incl brk mbase sp lim inp); reflexivity
| reflexivity | reflexivity | reflexivity | exact HS | exact HR | |].
- exact (jinv_head_eq _ _ _ _ _ (dir_m_eq init_state) (dir_jinv dot_path (in_fs inp))).
- intros res A' L' ms' md' g tr HS' HSA' HMR' HW' HB' [vm' Hmd] Hpath Hfr Hres.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (Hh' & Hlz' & _).
assert (Hch : fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) md').
{ split; [| split; [reflexivity | rewrite Hmd; exact (reader_of_inp inp Hvi)]]. rewrite Hmd. autorewrite with model. unfold MD_dir. autorewrite with model. rewrite MD0_fds. reflexivity. }
assert (Hfs : m_fs md' = in_fs inp).
{ rewrite Hmd. autorewrite with model. unfold MD_dir. autorewrite with model. apply MD0_fs. }
assert (HR' : runs_at (bv_unsigned sp) (ms_mem ms') (runs_main (kb_rseq (in_kernel inp)) true sp (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp))).
{ eapply runs_at_mbyte; [| | exact HR].
- destruct Hsp as (H & _). revert H. unfold sp_window_lo. lia.
- intros a Ha1 Ha2. apply Hfr; [| exact Ha1 | exact Ha2].
pose proof (YM05.ceil_le_top _ Hceil) as Hle. revert Hle Ha1. unfold stack_max_size. lia. }
destruct res as [q|]; cbn [tset dir_k ret fst snd].
+ rewrite <- Hfs. destruct Hres as (Ha0 & Hnz & b1 & b2 & Hub & _).
assert (Hin : In (q, CAP0) (user_blocks A')) by (rewrite Hub; apply in_app_iff; right; left; reflexivity).
pose proof (ubs0_dir_after_m1 API AX sp brk mbase tid lim inp rnd Hsp Hva Hve Hvl Hlau Hvi Hceil a0 dot_path (ms_regs ms') g ms' md' L' A' q
Hargv HRE ltac:(cbn; lia) Htid HS' eq_refl HR' HMR' Hin Ha0 (ex_intro _ vm' Hmd)) as X.
exact X.
+ rewrite <- Hfs. destruct Hres as [Ha0 _].
exact (ubs0_m1_oom sp tid inp rnd (ms_regs ms') g ms' md' _ HS' Ha0 eq_refl Hh' Hlz' Hch eq_refl).
Qed.
Lemma file_arm : forall sp brk mbase tid lim a0 path inp data rnd ms1,
in_argv inp = [a0; path] ->
valid_sp sp -> YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
valid_brk ubs0segs brk -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
0 < bv_unsigned tid < 4194304 -> SRC_LIM_MIN <= lim ->
fs_lookup (in_fs inp) path = Some data ->
st_ok ubs0segs (E_main sp inp [a0; path] (in_envp inp) (in_execfn inp) tid rnd) ss_m1 ms1 ->
runs_at (bv_unsigned sp) (ms_mem ms1) (runs_main (kb_rseq (in_kernel inp)) true sp (ed_top rnd) [a0; path] (in_envp inp) (in_execfn inp)) ->
realizes ubs0segs (mkCfg ms1 (MD_file path tid brk mbase sp lim inp rnd)) (SPECX_loaded data (in_fs inp)).
Proof using AX DOB LIBX ROOMX.
intros sp brk mbase tid lim a0 path inp data rnd ms1 Hargv Hsp Hceil Hbrk Hva Hve Hvfs Hvl Hlau Hvi Htid Hlim Hlk HS HR.
rewrite <- Hargv in HS, HR.
unfold SPECX_loaded. rewrite (tset_bind_eq _ _ _ _ _ (driver_tree_eq data)).
pose proof (do_jinvX DOB data (in_fs inp)) as HJ. pose proof (do_gtreeX DOB data) as HGT.
pose proof (driver_res data) as HL. rewrite (driver_tree_eq data) in HL.
assert (HSA0 : forall G, anchored_atoms G = anchored_atoms RD_facts -> stack_anchored (E_main sp inp [a0; path] (in_envp inp) (in_execfn inp) tid rnd) G).
{ intros G HG. rewrite <- Hargv.
(* position-free: [anchored_main]'s discharged argument list is whatever UN3e's and UL0n's
   sections turn out to need, so unification and [eassumption] choose it (rule 25j). *)
eapply anchored_main; first [eassumption | rewrite HG; vm_compute; reflexivity]. }
eapply (ubs0_malloc1 API AX sp brk mbase tid lim inp rnd Hsp Hbrk Hlim Hva Hve Hvl Hlau Hvi Hceil ms1 (MD_file path tid brk mbase sp lim inp rnd)
(vdso_reserved (in_kernel inp) (page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)))));
[ reflexivity
| exact (MD0_rx_ok sp brk mbase rnd inp Hsp Hbrk Hlau Hvi)
| apply (MD0_vdso_incl brk mbase sp lim inp); reflexivity
| reflexivity | reflexivity | reflexivity | exact HS | exact HR | |].
- exact (jinv_head_eq _ _ _ _ _ (driver_tree_eq data) HJ).
- intros res A' L' ms' md' g tr HS' HSA' HMR' HW' HB' [vm' Hmd] Hpath Hfr Hres.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (Hh' & Hlz' & _).
assert (Hch : fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) md').
{ split; [| split; [reflexivity | rewrite Hmd; exact (reader_of_inp inp Hvi)]]. rewrite Hmd. autorewrite with model. unfold MD_file. autorewrite with model. rewrite MD0_fds. reflexivity. }
assert (Hfs : m_fs md' = in_fs inp).
{ rewrite Hmd. autorewrite with model. unfold MD_file. autorewrite with model. apply MD0_fs. }
assert (HR' : runs_at (bv_unsigned sp) (ms_mem ms') (runs_main (kb_rseq (in_kernel inp)) true sp (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp))).
{ eapply runs_at_mbyte; [| | exact HR].
- destruct Hsp as (H & _). revert H. unfold sp_window_lo. lia.
- intros a Ha1 Ha2. apply Hfr; [| exact Ha1 | exact Ha2].
pose proof (YM05.ceil_le_top _ Hceil) as Hle. revert Hle Ha1. unfold stack_max_size. lia. }
destruct res as [b0|]; cbn [driver_after_m1 tset ret fst snd leaf_shape].
+ destruct Hres as (Ha0 & Hnz & b1 & b2 & Hub & Hub0).
assert (Hb12 : b1 = [] /\ b2 = []).
{ change (user_blocks init_state) with (@nil (sptr * Z)) in Hub0.
destruct b1; [| discriminate]. destruct b2; [| discriminate]. auto. }
destruct Hb12 as [-> ->]. cbn [app] in Hub.
assert (Hid : st_init_done A' = true).
{ exact (malloc_init_state_init_done CAP0 tr b0 A' ltac:(unfold CAP0; lia) (cpath_yields _ _ _ Hpath)). }
pose proof (ubs0_read_loop API AX sp tid a0 path inp data rnd Hlk HSA0 (fun r => res_ok (snd r) DRB) brk mbase lim (ms_regs ms') g ms' md' L' A' b0 vm' _
ltac:(rewrite Hargv in HS'; exact HS') Ha0 HMR' HW' HB' Hid Hub Hmd (reader_of_inp inp Hvi)
(jinv_after_eq _ _ _ _ _ _ _ _ (driver_tree_eq data) HJ Hpath) (gtree_after_eq _ _ _ _ _ _ _ _ (driver_tree_eq data) HGT Hpath)
(leaves_mbind_after _ _ _ _ _ _ _ HL Hpath)
(fun r => t_eq_refl _) (ubs0_postX API AX LIBX fp_frm_zero_fx0 sp tid a0 path inp data rnd HSA0 DRB (ROOMX data) Hvfs ltac:(exact (proj1 (proj2 Hsp))) _ (fun r => t_eq_refl _))) as X.
exact X.
+ rewrite <- Hfs. destruct Hres as [Ha0 _].
exact (ubs0_m1_oom sp tid inp rnd (ms_regs ms') g ms' md' _ HS' Ha0 eq_refl Hh' Hlz' Hch eq_refl).
Qed.
Lemma argv2_arm : forall sp brk mbase tid lim a0 path inp rnd ms,
in_argv inp = [a0; path] ->
valid_sp sp -> YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
valid_brk ubs0segs brk -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
0 < bv_unsigned tid < 4194304 -> SRC_LIM_MIN <= lim ->
st_ok ubs0segs (E_main sp inp [a0; path] (in_envp inp) (in_execfn inp) tid rnd) (ss_canon true) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main (kb_rseq (in_kernel inp)) true sp (ed_top rnd) [a0; path] (in_envp inp) (in_execfn inp)) ->
realizes ubs0segs (mkCfg ms (MD0 tid brk mbase sp lim inp rnd)) (SPECX_args [a0; path] (in_fs inp)).
Proof using AX DOB LIBX ROOMX.
intros sp brk mbase tid lim a0 path inp rnd ms Hargv Hsp Hceil Hbrk Hva Hve Hvfs Hvl Hlau Hvi Htid Hlim HS HR.
unfold SPECX_args, classify_open.
(* Each [eapply … ; first [eassumption | …]] below lets unification pick UL0q's discharged
   argument list rather than hard-coding it: the section there dropped [entry_stack_fits]
   and gained three premises, and a dropped-because-unused hypothesis is invisible in the
   source (rule 25j). *)
destruct (Nat.leb_spec path_max (length path)) as [Hlong|Hshort].
{ change path_max with 4096%nat in Hlong. eapply ubs0_open_toolong; first [eassumption | exact HCO]. }
change path_max with 4096%nat in Hshort.
destruct (path_eqb path []) eqn:Enil.
{ apply path_eqb_eq in Enil. eapply ubs0_open_empty; first [eassumption | exact HCO]. }
assert (Hne : path <> []) by (intros ->; rewrite path_eqb_refl in Enil; discriminate).
destruct (path_eqb path dot_path) eqn:Edot.
{ apply path_eqb_eq in Edot. subst path.
eapply ubs0_open_dir;
first [eassumption | exact HCO | reflexivity
| intros ms1 HS1 HR1;
exact (dir_arm sp brk mbase tid lim a0 inp rnd ms1 Hargv Hsp Hceil Hbrk Hva Hve Hvl Hlau Hvi Htid Hlim HS1 HR1)]. }
assert (Hnd : path <> dot_path) by (intros ->; rewrite path_eqb_refl in Edot; discriminate).
pose proof (plain_name_of_argv a0 path ltac:(rewrite <- Hargv; exact Hva) Hnd) as Hpn.
destruct (fs_lookup (in_fs inp) path) as [data|] eqn:Hlk.
- eapply ubs0_open_file with (data := data);
first [eassumption | exact HCO
| intros ms1 HS1 HR1;
exact (file_arm sp brk mbase tid lim a0 path inp data rnd ms1 Hargv Hsp Hceil Hbrk Hva Hve Hvfs Hvl Hlau Hvi Htid Hlim Hlk HS1 HR1)].
- eapply ubs0_open_absent; first [eassumption | exact HCO].
Qed.
(* [entry_stack_fits] is REPLACED by [entry_launch_ok_va], which is conjunct 5 of the
   published [valid_entry] (75d69e00:theories/LinuxProcessSem/Run.v:3733-3738) and IMPLIES
   the other four, [entry_stack_fits] included ([entry_launch_ok_va_fits], Run.v:4031).  So
   this is the premise the published quantifier already supplies, not a new demand. *)
Theorem ubs0_realizes_specX : forall sp brk mbase rnd lim inp,
valid_sp sp -> valid_brk ubs0segs brk -> valid_mmap_base mbase ->
entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
valid_input inp -> SRC_LIM_MIN <= lim ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
realizes ubs0segs (init_config ubs0segs Ubsan_init_pc Ubsan_phdrs sp brk mbase rnd lim inp) (SPECX inp).
Proof using AX DOB LIBX ROOMX.
intros sp brk mbase rnd lim inp Hsp Hbrk Hmb Hlau Hvi Hlim Hceil.
(* [valid_launch] is conjunct 13 of [valid_input] now (75d69e00:Run.v:4596); these four come
   out by [tauto] rather than by counting [proj2]s through a seventeen-way conjunction. *)
assert (Hva : valid_argv (in_argv inp)) by (unfold valid_input in Hvi; tauto).
assert (Hve : valid_envp (in_envp inp)) by (unfold valid_input in Hvi; tauto).
assert (Hvfs : valid_fs (in_fs inp)) by (unfold valid_input in Hvi; tauto).
assert (Hvl : valid_launch inp) by (unfold valid_input in Hvi; tauto).
unfold SPECX.
destruct (Nat.eq_dec (length (in_argv inp)) 2) as [Hlen | Hlen].
- (* The two-element argv by equation, not by [destruct], so [Hva] keeps the [in_argv inp] spelling
     that [ubs0_start] and [argv2_arm] take. *)
assert (Hex : exists a0 path, in_argv inp = [a0; path]).
{ destruct (in_argv inp) as [|a0 [|path [|x r]]]; cbn in Hlen; try lia. exists a0, path. reflexivity. }
destruct Hex as (a0 & path & Hargv).
apply (ubs0_start true sp brk mbase rnd lim inp _ Hsp Hva Hve Hvl Hlau Hvi ltac:(rewrite Hargv; cbn; lia)).
intros ms tid Htid HS HR.
(* [ubs0_start] hands back [ss_main (kb_rseq (in_kernel inp)) two], case-split over all four
   (rs, two) bullets at UN3e.v:613-620.  [UL0k.st_ok_main_rs] is the bridge to the rseq-OFF
   state the driver chain is computed from (UL0k.v:232).  It is a ONE-WAY IMPLICATION, not
   the equality the old [ss_main_rs_eq] asserted: the four states do not collapse, and the
   rseq-off one is the WEAKER, so this is the only direction that exists.  No flag is
   pinned -- [kb_rseq (in_kernel inp)] stays exactly as [ubs0_start] handed it over. *)
apply (st_ok_main_rs (kb_rseq (in_kernel inp)) true) in HS.
rewrite Hargv in HS, HR.
fold (MD0 tid brk mbase sp lim inp rnd). try rewrite Hargv.
exact (argv2_arm sp brk mbase tid lim a0 path inp rnd ms Hargv Hsp Hceil Hbrk Hva Hve Hvfs Hvl Hlau Hvi Htid Hlim HS HR).
- apply (ubs0_start false sp brk mbase rnd lim inp _ Hsp Hva Hve Hvl Hlau Hvi I).
intros ms tid Htid HS HR.
apply (st_ok_main_rs (kb_rseq (in_kernel inp)) false) in HS.
assert (Hh : m_halted (MD0 tid brk mbase sp lim inp rnd) = None) by reflexivity.
assert (Hlz : m_vm_lazy (MD0 tid brk mbase sp lim inp rnd) = []) by reflexivity.
fold (MD0 tid brk mbase sp lim inp rnd).
replace (SPECX_args (in_argv inp) (in_fs inp)) with (diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
2:{ unfold SPECX_args. destruct (in_argv inp) as [|x [|y [|z r]]]; try reflexivity. cbn in Hlen. lia. }
change (in_fs inp) with (m_fs (MD0 tid brk mbase sp lim inp rnd)).
apply (HU sp brk mbase tid rnd inp ms _ Hsp Hva Hve Hvl Hlau Hvi).
+ exact Hlen.
+ apply st_ok_add_cond; [exact HS |].
assert (H3 : bv_unsigned (ew (E_main sp inp (in_argv inp) (in_envp inp) (in_execfn inp) tid rnd) 3)
= Z.of_nat (length (in_argv inp)))
by (unfold E_main; eapply YP08.ew3; eassumption).
unfold branch_taken. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
apply Bool.negb_true_iff. apply bv_eqb_neq. intros Heq.
apply (f_equal bv_unsigned) in Heq. rewrite H3 in Heq. change (bv_unsigned (Z_to_bv 64 2)) with 2 in Heq. lia.
+ exact HR.
+ exact Hh.
+ exact Hlz.
+ split; [reflexivity | split; [reflexivity | exact (reader_of_inp inp Hvi)]].
Qed.
End c.
End b.
