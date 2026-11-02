(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0j.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0o.
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3e.
From OssFuzzTheorems.zlib.checksum_fuzzer.images Require Import Plain.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL07.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0y.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YI16.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YI5b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI5c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {rc : YM05.RunCeil} {LS : lib_shape}.
Lemma plain_name_of_argv : forall a0 path, valid_argv [a0; path] -> path <> dot_path -> openat_plain_name path = true.
Proof.
intros a0 path (_ & _ & _ & _ & HF) Hnd. cbn [tl] in HF. apply Forall_inv in HF. destruct HF as [Hs Hdd].
unfold openat_plain_name, path_is_dirref. rewrite Hs, Hdd.
destruct (path_eqb path dot_path) eqn:E; [apply path_eqb_eq in E; contradiction | reflexivity].
Qed.
Section c.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).
Lemma HU : usage_hyp.
Proof. exact src0_usage_hyp. Qed.
Lemma HCO : cannot_open_hyp.
Proof. exact src0_cannot_open_hyp. Qed.
Lemma HRE : read_error_hyp.
Proof. exact src0_read_error_hyp. Qed.
Hypothesis LIBX : lib_contract_x_all src0_msyms API LIBPC RA_LIB EMPTY LIB_STACK.
Hypothesis DOB : driver_obligationsX.
Hypothesis ROOMX : forall data, room_calls (payload_len data) (calls data) DRB.
Lemma dir_arm : forall sp brk mbase tid lim a0 inp rnd ms1,
in_argv inp = [a0; dot_path] ->
valid_sp sp -> YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
valid_brk src0segs brk -> valid_argv [a0; dot_path] -> valid_envp (in_envp inp) ->
entry_stack_fits sp [a0; dot_path] (in_envp inp) ->
0 < bv_unsigned tid < 4194304 -> SRC_LIM_MIN <= lim ->
st_ok src0segs (E_main sp [a0; dot_path] (in_envp inp) tid rnd) ss_m1 ms1 ->
runs_at (bv_unsigned sp) (ms_mem ms1) (runs_main true sp [a0; dot_path] (in_envp inp) rnd) ->
realizes src0segs (mkCfg ms1 (MD_dir tid brk mbase sp lim inp)) (SPEC_dir dot_path (in_fs inp)).
Proof.
intros sp brk mbase tid lim a0 inp rnd ms1 Hargv Hsp Hceil Hbrk Hva Hve Hfits Htid Hlim HS HR.
unfold SPEC_dir. rewrite (tset_bind_eq _ _ _ _ _ (dir_m_eq init_state)).
eapply (src0_malloc1 API AX sp brk mbase tid lim [a0; dot_path] (in_envp inp) rnd Hsp Hbrk Hlim Hva Hve Hceil ms1 (MD_dir tid brk mbase sp lim inp));
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
pose proof (YM05.ceil_le_top _ Hceil) as Hle. revert Hle Ha1. unfold stack_max_size. lia. }
destruct res as [q|]; cbn [tset dir_k ret fst snd].
+ rewrite <- Hfs. destruct Hres as (Ha0 & Hnz & b1 & b2 & Hub & _).
assert (Hin : In (q, CAP0) (user_blocks A')) by (rewrite Hub; apply in_app_iff; right; left; reflexivity).
pose proof (src0_dir_after_m1 API AX sp brk mbase tid lim [a0; dot_path] (in_envp inp) rnd Hsp Hva Hve Hfits Hceil a0 dot_path (ms_regs ms') g ms' md' L' A' q
eq_refl HRE ltac:(cbn; lia) Htid HS' eq_refl HR' HMR' Hin Ha0 inp (ex_intro _ vm' Hmd)) as X.
exact X.
+ rewrite <- Hfs. destruct Hres as [Ha0 _].
exact (src0_m1_oom sp tid [a0; dot_path] (in_envp inp) rnd (ms_regs ms') g ms' md' _ HS' Ha0 eq_refl Hh' Hlz' Hch eq_refl).
Qed.
Lemma file_arm : forall sp brk mbase tid lim a0 path inp data rnd ms1,
in_argv inp = [a0; path] ->
valid_sp sp -> YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
valid_brk src0segs brk -> valid_argv [a0; path] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
entry_stack_fits sp [a0; path] (in_envp inp) ->
0 < bv_unsigned tid < 4194304 -> SRC_LIM_MIN <= lim ->
fs_lookup (in_fs inp) path = Some data ->
st_ok src0segs (E_main sp [a0; path] (in_envp inp) tid rnd) ss_m1 ms1 ->
runs_at (bv_unsigned sp) (ms_mem ms1) (runs_main true sp [a0; path] (in_envp inp) rnd) ->
realizes src0segs (mkCfg ms1 (MD_file path tid brk mbase sp lim inp)) (SPECX_loaded data (in_fs inp)).
Proof.
intros sp brk mbase tid lim a0 path inp data rnd ms1 Hargv Hsp Hceil Hbrk Hva Hve Hvfs Hfits Htid Hlim Hlk HS HR.
unfold SPECX_loaded. rewrite (tset_bind_eq _ _ _ _ _ (driver_tree_eq data)).
pose proof (do_jinvX DOB data (in_fs inp)) as HJ. pose proof (do_gtreeX DOB data) as HGT.
pose proof (driver_res data) as HL. rewrite (driver_tree_eq data) in HL.
assert (HSA0 : forall G, anchored_atoms G = anchored_atoms RD_facts -> stack_anchored (E_main sp [a0; path] (in_envp inp) tid rnd) G).
{ intros G HG. apply (anchored_main sp [a0; path] (in_envp inp) rnd Hsp Hva Hve Hceil G tid). rewrite HG. vm_compute. reflexivity. }
eapply (src0_malloc1 API AX sp brk mbase tid lim [a0; path] (in_envp inp) rnd Hsp Hbrk Hlim Hva Hve Hceil ms1 (MD_file path tid brk mbase sp lim inp));
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
pose proof (YM05.ceil_le_top _ Hceil) as Hle. revert Hle Ha1. unfold stack_max_size. lia. }
destruct res as [b0|]; cbn [driver_after_m1 tset ret fst snd leaf_shape].
+ destruct Hres as (Ha0 & Hnz & b1 & b2 & Hub & Hub0).
assert (Hb12 : b1 = [] /\ b2 = []).
{ change (user_blocks init_state) with (@nil (sptr * Z)) in Hub0.
destruct b1; [| discriminate]. destruct b2; [| discriminate]. auto. }
destruct Hb12 as [-> ->]. cbn [app] in Hub.
assert (Hid : st_init_done A' = true).
{ exact (malloc_init_state_init_done CAP0 tr b0 A' ltac:(unfold CAP0; lia) (cpath_yields _ _ _ Hpath)). }
pose proof (src0_read_loop API AX sp tid a0 path inp data rnd Hlk HSA0 (fun r => res_ok (snd r) DRB) brk mbase lim (ms_regs ms') g ms' md' L' A' b0 vm' _
HS' Ha0 HMR' HW' HB' Hid Hub Hmd
(jinv_after_eq _ _ _ _ _ _ _ _ (driver_tree_eq data) HJ Hpath) (gtree_after_eq _ _ _ _ _ _ _ _ (driver_tree_eq data) HGT Hpath)
(leaves_mbind_after _ _ _ _ _ _ _ HL Hpath)
(fun r => t_eq_refl _) (src0_postX API AX LIBX fp_frm_zero_fx0 sp tid a0 path inp data rnd HSA0 DRB (ROOMX data) Hvfs ltac:(exact (proj1 (proj2 Hsp))) _ (fun r => t_eq_refl _))) as X.
exact X.
+ rewrite <- Hfs. destruct Hres as [Ha0 _].
exact (src0_m1_oom sp tid [a0; path] (in_envp inp) rnd (ms_regs ms') g ms' md' _ HS' Ha0 eq_refl Hh' Hlz' Hch eq_refl).
Qed.
Lemma argv2_arm : forall sp brk mbase tid lim a0 path inp rnd ms,
in_argv inp = [a0; path] ->
valid_sp sp -> YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
valid_brk src0segs brk -> valid_argv [a0; path] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
entry_stack_fits sp [a0; path] (in_envp inp) ->
0 < bv_unsigned tid < 4194304 -> SRC_LIM_MIN <= lim ->
st_ok src0segs (E_main sp [a0; path] (in_envp inp) tid rnd) ss_main_t ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp [a0; path] (in_envp inp) rnd) ->
realizes src0segs (mkCfg ms (MD0 tid brk mbase sp lim inp)) (SPECX_args [a0; path] (in_fs inp)).
Proof.
intros sp brk mbase tid lim a0 path inp rnd ms Hargv Hsp Hceil Hbrk Hva Hve Hvfs Hfits Htid Hlim HS HR.
unfold SPECX_args, classify_open.
destruct (Nat.leb_spec path_max (length path)) as [Hlong|Hshort].
{ change path_max with 4096%nat in Hlong. exact (src0_open_toolong sp brk mbase tid lim a0 path inp rnd Hsp Hva Hve Htid Hfits HCO ms Hlong HS HR). }
change path_max with 4096%nat in Hshort.
destruct (path_eqb path []) eqn:Enil.
{ apply path_eqb_eq in Enil. exact (src0_open_empty sp brk mbase tid lim a0 path inp rnd Hsp Hva Hve Htid Hfits HCO ms Enil HS HR). }
assert (Hne : path <> []) by (intros ->; rewrite path_eqb_refl in Enil; discriminate).
destruct (path_eqb path dot_path) eqn:Edot.
{ apply path_eqb_eq in Edot. subst path.
apply (src0_open_dir sp brk mbase tid lim a0 dot_path inp rnd Hsp Hva Hve Htid Hfits HCO ms eq_refl HS HR).
intros ms1 HS1 HR1. exact (dir_arm sp brk mbase tid lim a0 inp rnd ms1 Hargv Hsp Hceil Hbrk Hva Hve Hfits Htid Hlim HS1 HR1). }
assert (Hnd : path <> dot_path) by (intros ->; rewrite path_eqb_refl in Edot; discriminate).
pose proof (plain_name_of_argv a0 path Hva Hnd) as Hpn.
destruct (fs_lookup (in_fs inp) path) as [data|] eqn:Hlk.
- apply (src0_open_file sp brk mbase tid lim a0 path inp rnd Hsp Hva Hve Htid Hfits HCO ms data Hshort Hne Hpn Hlk HS HR).
intros ms1 HS1 HR1. exact (file_arm sp brk mbase tid lim a0 path inp data rnd ms1 Hargv Hsp Hceil Hbrk Hva Hve Hvfs Hfits Htid Hlim Hlk HS1 HR1).
- exact (src0_open_absent sp brk mbase tid lim a0 path inp rnd Hsp Hva Hve Htid Hfits HCO ms Hshort Hne Hpn Hlk HS HR).
Qed.
Theorem src0_realizes_specX : forall sp brk mbase rnd lim inp,
valid_sp sp -> valid_brk src0segs brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) ->
valid_input inp -> SRC_LIM_MIN <= lim ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
realizes src0segs (init_config src0segs Plain_init_pc Plain_phdrs sp brk mbase rnd lim inp) (SPECX inp).
Proof.
intros sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits (Hva & Hve & Hvfs & Hcreds) Hlim Hceil.
unfold SPECX.
destruct (Nat.eq_dec (length (in_argv inp)) 2) as [Hlen | Hlen].
- destruct (in_argv inp) as [|a0 [|path [|x r]]] eqn:Hargv; try (cbn in Hlen; lia).
apply (src0_start true sp brk mbase rnd lim inp _ Hsp); [rewrite Hargv; exact Hva | exact Hve | rewrite Hargv; exact Hfits | rewrite Hargv; cbn; lia |].
intros ms tid Htid HS HR. rewrite Hargv in HS, HR.
change (with_tid tid (init_model (segments_reserved src0segs) brk mbase sp lim inp)) with (MD0 tid brk mbase sp lim inp).
exact (argv2_arm sp brk mbase tid lim a0 path inp rnd ms Hargv Hsp Hceil Hbrk Hva Hve Hvfs Hfits Htid Hlim HS HR).
- apply (src0_start false sp brk mbase rnd lim inp _ Hsp Hva Hve Hfits I).
intros ms tid Htid HS HR.
assert (Hh : m_halted (with_tid tid (init_model (segments_reserved src0segs) brk mbase sp lim inp)) = None) by reflexivity.
assert (Hlz : m_vm_lazy (with_tid tid (init_model (segments_reserved src0segs) brk mbase sp lim inp)) = []) by reflexivity.
replace (SPECX_args (in_argv inp) (in_fs inp)) with (diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
2:{ unfold SPECX_args. destruct (in_argv inp) as [|x [|y [|z r]]]; try reflexivity. cbn in Hlen. lia. }
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
