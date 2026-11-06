(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/Reusable/YL0j.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Reusable/YL0j_cfw.v, with its module paths and module names changed; 86 of its 219 lines of code are new or changed and 63 lines of the source are left out. *)
(* Modified by Theorem Labs: the twin of lib/U/Reusable/YL0j_cfw.v, lib/U/AgreeWalk.v and lib/U/AgreeZlib.v (no licence line) for a return value of the fuzz target of 0 or -1, walking U/Prog/AgreeRetD2.v SPECX_q for any shape *)
(* Donor: reac-repacer/fuzz_lock, proofs/reac-repacer/fuzz_lock/lib/U/Reusable/YL0j_cfw.v, U/AgreeWalk.v and
   U/AgreeZlib.v at 901d1549395.
   Module: OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog.AgreeRetD4. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.reac_repacer.fuzz_lock Require Statements Images.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YK11 YK0o YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO0i YO0f YO0g YO0x YO0d YO0e YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO06 YO04 YO03.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YH00 YH01 YH03 YH02 YN3e.
From OSSVerify.reac_repacer.fuzz_lock.images Require Import Ubsan.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL0e YL0k YL0p YL0q YL0n YL0g YL0m YL0s YL0y YL0w YL0x.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YI06 YI16 YI14 YI5b YI5c YL0i YL06 YL03 YL0l YL0t YL0z.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YM05 YM0b YL0j DriverSlots YN2b YN33.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO0d_cf YO04_cfw YK15_cfw YL0i_cfw.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YN3e_cfw YL0p_cfw YL0q_cfw YL0w_cfw YL0x_cfw YL0y_cfw.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YL0n_cfw YL0l_cfw YL0z_cfw YL0j_cfw.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG
  SlotAgree AllocCf Agree AgreeZlib.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import FrameRet FrameRetD2 AgreeRet AgreeRetD1 AgreeRetD2 AgreeRetD3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {rc : YM05.RunCeil} {LS : lib_shape}.
Section c.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).
Variable GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop.
Variable RI : list byte -> nat -> list (Z * Z) -> astate -> Prop.
Variable OUT : list byte -> list byte.
Variable rt : list byte -> Z.
Hypothesis GIL : G_local_T src0segs src0_G GI.
Hypothesis GI0 : forall mem, G_img src0segs src0_G mem -> GI 0%nat [] mem.
Hypothesis LIBXc : lib_contract_x_Rc_all_r src0_msyms API rt RI src0_G src0_R GI OUT LIBPC RA_LIB EMPTY LIB_STACK.
Hypothesis HR01 : forall pl, rt pl = 0 \/ rt pl = -1.
Hypothesis ARMS : arms_m1_cf.
Hypothesis DRV : forall data, leaves (run_RI RI (payload data)) (driver_tree data).
Hypothesis FCF : forall fx' : FPState, @free_contract_cf fx' rc src0_msyms API.
Hypothesis TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned src0_msyms a -> 0 <= a < 2 ^ 64 ->
Mem.ro_addr src0segs (Z_to_bv 64 a) = true -> mbyte src0segs mem a = seg_rom src0segs (Z_to_bv 64 a).
Hypothesis RIres : forall pl j T A, RI pl j T A -> exists b, res_ok_slots A b.
Hypothesis MRC : forall fx' : FPState, @malloc_realizes_cf fx' rc src0_msyms (aa_MR API).
Hypothesis FRC : forall fx' : FPState, @free_realizes_cf fx' rc src0_msyms (aa_MR API).
Hypothesis LIMLAW : forall L A mem md, aa_MR API L A mem md -> SRC_LIM_MIN <= vm_limit (m_vmmaps md).
Lemma file_arm_q_cf : forall sp brk mbase tid lim a0 path inp data rnd ms1,
in_argv inp = [a0; path] ->
valid_sp sp -> YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
valid_brk src0segs brk -> valid_argv [a0; path] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
entry_stack_fits sp [a0; path] (in_envp inp) ->
0 < bv_unsigned tid < 4194304 -> SRC_LIM_MIN <= lim ->
fs_lookup (in_fs inp) path = Some data ->
st_ok src0segs (E_main sp [a0; path] (in_envp inp) tid rnd) ss_m1 ms1 ->
runs_at (bv_unsigned sp) (ms_mem ms1) (runs_main true sp [a0; path] (in_envp inp) rnd) ->
crealizes src0_msyms (mkCfg ms1 (MD_file path tid brk mbase sp lim inp)) (SPECX_loaded_q rt data (in_fs inp)).
Proof using AX GIL GI0 LIBXc HR01 ARMS DRV FCF TBL RIres MRC FRC LIMLAW.
intros sp brk mbase tid lim a0 path inp data rnd ms1 Hargv Hsp Hceil Hbrk Hva Hve Hvfs Hfits Htid Hlim Hlk HS HR.
unfold SPECX_loaded_q. rewrite (tset_bind_eq _ _ _ _ _ (driver_tree_eq data)).
pose proof (do_jinvX_q rt data (in_fs inp)) as HJ.
pose proof (OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable.YO03.do_gtree_proved data) as HGT.
pose proof (DRV data) as HL. rewrite (driver_tree_eq data) in HL.
assert (HSA0 : forall G, anchored_atoms G = anchored_atoms RD_facts -> stack_anchored (E_main sp [a0; path] (in_envp inp) tid rnd) G).
{ intros G HG. apply (anchored_main sp [a0; path] (in_envp inp) rnd Hsp Hva Hve Hceil G tid). rewrite HG. vm_compute. reflexivity. }
eapply (src0_malloc1_cf API AX MRC LIMLAW sp brk mbase tid lim [a0; path] (in_envp inp) rnd Hsp Hbrk Hlim Hva Hve Hceil ms1 (MD_file path tid brk mbase sp lim inp));
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
pose proof (leaves_cpath _ _ _ _ (malloc_leaves_res init_state (RB 0 0 0 0) CAP0 wf_init res_ok_init room_m1) Hpath) as [_ HR0]. cbn [snd] in HR0.
pose proof (DI_malloc init_state CAP0 tr (Some b0) A' DI_init ltac:(unfold CAP0; lia) (cpath_yields _ _ _ Hpath)) as HDI.
pose proof (src0_read_loop_cf (LS:=shape_q rt data) API AX MRC FRC LIMLAW sp tid a0 path inp data rnd Hlk HSA0 (run_RI RI (payload data)) brk mbase lim (ms_regs ms') g ms' md' L' A' b0 vm' _
HS' Ha0 HMR' HW' HB' Hid HDI HR0 Hub Hmd
(jinv_after_eq _ _ _ _ _ _ _ _ (driver_tree_eq data) HJ Hpath) (gtree_after_eq _ _ _ _ _ _ _ _ (driver_tree_eq data) HGT Hpath)
(leaves_mbind_after _ _ _ _ _ _ _ HL Hpath)
(leaf_shapeX_q_at rt data (in_fs inp))
(src0_postX_q_cf API AX GI RI OUT rt GIL GI0 LIBXc FCF TBL RIres MRC LIMLAW HR01 ARMS fp_frm_zero_fx0 sp tid a0 path inp data rnd HSA0 Hvfs ltac:(exact (proj1 (proj2 Hsp))) _ (fun r => t_eq_refl _))) as X.
exact X.
+ rewrite <- Hfs. destruct Hres as [Ha0 _].
unfold leaf_shapeX_q. destruct (rt (payload data) =? 0); cbn [leaf_shapeX leaf_shapeX_r leaf_shape fst];
exact (src0_m1_oom_cf sp tid [a0; path] (in_envp inp) rnd (ms_regs ms') g ms' md' _ HS' Ha0 eq_refl Hh' Hlz' Hch eq_refl).
Qed.
Lemma argv2_arm_q_cf : forall sp brk mbase tid lim a0 path inp rnd ms,
in_argv inp = [a0; path] ->
valid_sp sp -> YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
valid_brk src0segs brk -> valid_argv [a0; path] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
entry_stack_fits sp [a0; path] (in_envp inp) ->
0 < bv_unsigned tid < 4194304 -> SRC_LIM_MIN <= lim ->
st_ok src0segs (E_main sp [a0; path] (in_envp inp) tid rnd) ss_main_t ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main true sp [a0; path] (in_envp inp) rnd) ->
crealizes src0_msyms (mkCfg ms (MD0 tid brk mbase sp lim inp)) (SPECX_args_q rt [a0; path] (in_fs inp)).
Proof using AX GIL GI0 LIBXc HR01 ARMS DRV FCF TBL RIres MRC FRC LIMLAW.
intros sp brk mbase tid lim a0 path inp rnd ms Hargv Hsp Hceil Hbrk Hva Hve Hvfs Hfits Htid Hlim HS HR.
unfold SPECX_args_q, classify_open.
destruct (Nat.leb_spec path_max (length path)) as [Hlong|Hshort].
{ change path_max with 4096%nat in Hlong. exact (src0_open_toolong_cf sp brk mbase tid lim a0 path inp rnd Hsp Hva Hve Htid Hfits src0_cannot_open_hyp_cf ms Hlong HS HR). }
change path_max with 4096%nat in Hshort.
destruct (path_eqb path []) eqn:Enil.
{ apply path_eqb_eq in Enil. exact (src0_open_empty_cf sp brk mbase tid lim a0 path inp rnd Hsp Hva Hve Htid Hfits src0_cannot_open_hyp_cf ms Enil HS HR). }
assert (Hne : path <> []) by (intros ->; rewrite path_eqb_refl in Enil; discriminate).
destruct (path_eqb path dot_path) eqn:Edot.
{ apply path_eqb_eq in Edot. subst path.
apply (src0_open_dir_cf sp brk mbase tid lim a0 dot_path inp rnd Hsp Hva Hve Htid Hfits src0_cannot_open_hyp_cf ms eq_refl HS HR).
intros ms1 HS1 HR1. exact (dir_arm_cf API AX MRC LIMLAW sp brk mbase tid lim a0 inp rnd ms1 Hargv Hsp Hceil Hbrk Hva Hve Hfits Htid Hlim HS1 HR1). }
assert (Hnd : path <> dot_path) by (intros ->; rewrite path_eqb_refl in Edot; discriminate).
pose proof (plain_name_of_argv a0 path Hva Hnd) as Hpn.
destruct (fs_lookup (in_fs inp) path) as [data|] eqn:Hlk.
- apply (src0_open_file_cf sp brk mbase tid lim a0 path inp rnd Hsp Hva Hve Htid Hfits src0_cannot_open_hyp_cf ms data Hshort Hne Hpn Hlk HS HR).
intros ms1 HS1 HR1. exact (file_arm_q_cf sp brk mbase tid lim a0 path inp data rnd ms1 Hargv Hsp Hceil Hbrk Hva Hve Hvfs Hfits Htid Hlim Hlk HS1 HR1).
- exact (src0_open_absent_cf sp brk mbase tid lim a0 path inp rnd Hsp Hva Hve Htid Hfits src0_cannot_open_hyp_cf ms Hshort Hne Hpn Hlk HS HR).
Qed.
(* YL0j_cfw.v src0_realizes_specX_cf, which U/AgreeWalk.v ubsan_walk_crealizes restates, with SPECX_q *)
Theorem src0_realizes_specX_q_cf : forall sp brk mbase rnd lim inp,
valid_sp sp -> valid_brk src0segs brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) ->
valid_input inp -> SRC_LIM_MIN <= lim ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
crealizes src0_msyms (init_config src0segs Ubsan_init_pc Ubsan_phdrs sp brk mbase rnd lim inp) (SPECX_q rt inp).
Proof using AX GIL GI0 LIBXc HR01 ARMS DRV FCF TBL RIres MRC FRC LIMLAW.
intros sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits (Hva & Hve & Hvfs & Hcreds) Hlim Hceil.
unfold SPECX_q.
destruct (Nat.eq_dec (length (in_argv inp)) 2) as [Hlen | Hlen].
- destruct (in_argv inp) as [|a0 [|path [|x r]]] eqn:Hargv; try (cbn in Hlen; lia).
apply (src0_start_cf true sp brk mbase rnd lim inp _ Hsp); [rewrite Hargv; exact Hva | exact Hve | rewrite Hargv; exact Hfits | rewrite Hargv; cbn; lia |].
intros ms tid Htid HS HR. rewrite Hargv in HS, HR.
change (with_tid tid (init_model (segments_reserved src0segs) brk mbase sp lim inp)) with (MD0 tid brk mbase sp lim inp).
exact (argv2_arm_q_cf sp brk mbase tid lim a0 path inp rnd ms Hargv Hsp Hceil Hbrk Hva Hve Hvfs Hfits Htid Hlim HS HR).
- apply (src0_start_cf false sp brk mbase rnd lim inp _ Hsp Hva Hve Hfits I).
intros ms tid Htid HS HR.
assert (Hh : m_halted (with_tid tid (init_model (segments_reserved src0segs) brk mbase sp lim inp)) = None) by reflexivity.
assert (Hlz : m_vm_lazy (with_tid tid (init_model (segments_reserved src0segs) brk mbase sp lim inp)) = []) by reflexivity.
replace (SPECX_args_q rt (in_argv inp) (in_fs inp)) with (diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
2:{ unfold SPECX_args_q. destruct (in_argv inp) as [|x [|y [|z r]]]; try reflexivity. cbn in Hlen. lia. }
change (in_fs inp) with (m_fs (MD0 tid brk mbase sp lim inp)).
apply (src0_usage_hyp_cf sp (in_argv inp) (in_envp inp) tid rnd ms _ Hsp Hva Hve Hfits).
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

(* U/AgreeZlib.v zlib_walk_crealizes, with SPECX_q *)
Theorem zlib_walk_crealizes_q : forall (rc : RunCeil) (LS : lib_shape) (rt : list byte -> Z)
    (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) (OUT : list byte -> list byte),
  (forall pl, rt pl = 0 \/ rt pl = -1) ->
  arms_m1_cf ->
  (forall data, @room_calls LS (payload_len data) (calls data) SBD_AG) ->
  G_local_T src0segs src0_G GI ->
  (forall mem, G_img src0segs src0_G mem -> GI 0%nat [] mem) ->
  lib_contract_x_Rc_all_r src0_msyms (@zlib_API rc) rt (@RI_G LS) src0_G src0_R GI OUT LIBPC RA_LIB EMPTY LIB_STACK ->
  forall sp brk mbase rnd lim inp,
  valid_sp sp -> valid_brk src0segs brk -> valid_mmap_base mbase ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  valid_input inp -> SRC_LIM_MIN <= lim ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  crealizes src0_msyms (init_config src0segs Ubsan_init_pc Ubsan_phdrs sp brk mbase rnd lim inp) (SPECX_q (LS:=LS) rt inp).
Proof.
  intros rc LS rt GI OUT HR01 ARMS HROOM GIL GI0 LIBXc.
  exact (@src0_realizes_specX_q_cf rc LS (@zlib_API rc) zlib_allocator_extra GI (@RI_G LS) OUT rt GIL GI0 LIBXc HR01 ARMS
    (driver_RI_AG LS HROOM) (fun fx' => @zlib_free_contract_cf fx' rc) (zlib_tables rc) (@RI_G_res LS)
    (fun fx' => @src0_malloc_realizes_cf fx' rc) (fun fx' => @src0_free_realizes_cf fx' rc) (zlib_limit rc)).
Qed.

(* U/AgreeZlib.v ubsan_crealizes_of_cg, from U/Prog/AgreeRet.v lib_contract_cgr rt at every call: the UBSan build
   realizes SPECX_q rt with cut-free runs *)
Theorem ubsan_crealizes_of_cgr : forall (LS : lib_shape) (rt : list byte -> Z)
    (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop),
  (forall pl, rt pl = 0 \/ rt pl = -1) ->
  arms_m1_cf ->
  (forall data, @room_calls LS (payload_len data) (calls data) SBD_AG) ->
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_c src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_cgr fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       rt G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  forall en inp lim, valid_entry Images.ubsan en inp -> valid_input inp -> SRC_LIM_MIN <= lim ->
    rz_run Images.ubsan lim en inp (SPECX_q (LS:=LS) rt inp) /\ cf_run Images.ubsan lim en inp.
Proof.
  intros LS rt G GI HR01 ARMS HROOM HG GIL GI0 H [sp brk0 mbase rnd] inp lim Hentry Hinput Hlim.
  apply (valid_entry_sv48 _ _ inp (valid_input_va_size inp Hinput)) in Hentry.
  destruct Hentry as [Hsp [Hbrk [Hmb Hfits]]].
  set (rc := RunCeilOf (bv_unsigned sp) (valid_sp_window_for_ceil sp Hsp)).
  assert (HG' : forall a, in_globals G a -> in_globals src0_G a) by (intros a h; exact (frame_G_src0 a (HG a h))).
  change (crealizes src0_msyms (init_config src0segs Ubsan_init_pc Ubsan_phdrs sp brk0 mbase rnd lim inp)
    (SPECX_q (LS:=LS) rt inp)).
  apply (zlib_walk_crealizes_q rc LS rt (fun j T m => T = [] /\ GI j m) (fun _ => []) HR01 ARMS HROOM
    (G_local_T_mono src0segs G src0_G _ HG' (G_local_T_of_G src0segs G GI GIL))
    (fun mem Hm => conj eq_refl (GI0 mem (G_img_mono src0segs G src0_G mem HG' Hm)))
    (lib_contract_x_Rc_all_r_of_cgr src0_msyms (@zlib_API rc) (zlib_tables rc) rt G src0_G frame_RELRO src0_R GI
      LIBPC RA_LIB EMPTY LIB_STACK HG' frame_RELRO_src0 (H rc))
    sp brk0 mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinput Hlim).
  unfold rc. apply ceil_of_top_run.
Qed.
