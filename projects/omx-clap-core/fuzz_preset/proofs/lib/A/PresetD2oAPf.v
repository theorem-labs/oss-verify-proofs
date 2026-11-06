(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from the proof of TFIB_T_of_partsXF in proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v:40-84
   (asan; its asan-ubsan twin is lib/YD2o.v:35-79) for fuzz_preset's asan image.
   The PROOF of TFIB_T_of_partsXF_A (lib/A/PresetD2oA.v): the donor's Section b assembly, in which every input that is
   not a theorem of this tree is a NAMED Section hypothesis, one per obligation, with its owner. The donor's `Let`s
   that are proved in this tree are used as theorems: TfibB_syms (lib/A/AD2l.v), tfib_xst_frame / tfib_est_img /
   tfib_est_frame / est_written / est_after_vf (lib/A/AD1k.v), tfib_srealizesX_A_holds (lane CwD1q, lib/A/PresetD1qA.v)
   and tfib_lib_x_all_A_holds (lane CwCfiA, lib/A/PresetCfiAPf.v). Nothing in this file is a proof of a function
   (rule 24: no function proved; this is the composition / driver layer of a port).
   The donor's tfib_srealizesX_top (AD2o.v:75-82) is the last step: the run ceiling at sp's window (YM05.RunCeilOf). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PresetD2oAPf.v, with its module paths changed; 113 of its 168 lines of code are new or changed and 30 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: made from the proof of TFIB_T_of_partsXF in proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v:40-84
   (asan; its asan-ubsan twin is lib/YD2o.v:35-79) for fuzz_preset's asan image.
   The PROOF of TFIB_T_of_partsXF_A (lib/A/PresetD2oA.v): the donor's Section b assembly, in which every input that is
   not a theorem of this tree is a NAMED Section hypothesis, one per obligation, with its owner. The donor's `Let`s
   that are proved in this tree are used as theorems: TfibB_syms (lib/A/AD2l.v), tfib_xst_frame / tfib_est_img /
   tfib_est_frame / est_written / est_after_vf (lib/A/AD1k.v), tfib_srealizesX_A_holds (lane CwD1q, lib/A/PresetD1qA.v)
   and tfib_lib_x_all_A_holds (lane CwCfiA, lib/A/PresetCfiAPf.v). Nothing in this file is a proof of a function
   (rule 24: no function proved; this is the composition / driver layer of a port).
   The donor's tfib_srealizesX_top (AD2o.v:75-82) is the last step: the run ceiling at sp's window (YM05.RunCeilOf). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Shapes.
From OSSVerify.omx_clap_core.fuzz_preset Require Images.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK15 YK18 YA02 YM05 YO06 YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0f YG0n YG0d YC5d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG0ncf YG0dcf YG0d2cf YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YP0b YPsym YC4aP YGcallMxmn YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB01 AF0m AD2l ACeg AD1w AD1x AD1k.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfImgA CfParamsPreset PresetCfnA PresetTFIB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetD1sitesA PresetD1preA PresetD1preAx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetD1qA PresetCfiA PresetCfiAPf PresetD1pA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetD2oA.
(* a Theorem Labs lane's NR forms of the start-up + driver step, in their own file since the split of lib/A/HaltsClosedA.v
   (lib/A/PresetD1qNRA.v, the asan twin of lib/AU/PresetD1qNRB.v): NR_agrees_A, drv_mainX_stmt_NR_A,
   tfib_srealizesX_NR_A_holds *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetD1qNRA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Base.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* The donor's valid_sp_windowX (AD2o.v:27-28). *)
Lemma valid_sp_window_D2A : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

(* The class (C) check of the CfImg record (owner order 06:00Z): CfImg_A's memcpy cells are the image's, the rows
   lib/A/AF0m.v:95 `z8 (ANum 0xa3e88) 0x9b2b4` (cf_real_memcpy holds cf_pc_memcpy) and :179 `z8 (ANum 0xa2038)
   0xa3e88` (cf_got_memcpy holds &real_memcpy), both in Tfib_const_abs (checked in all 50 states at width 8). *)
Lemma cfimg_A_memcpy_cells :
  @cf_real_memcpy CfImg_A = 0xa3e88 /\ @cf_got_memcpy CfImg_A = 0xa2038 /\ @cf_pc_memcpy CfImg_A = 0x9b2b4.
Proof. split; [reflexivity | split; reflexivity]. Qed.

Section parts.
(* The driver walk's elaboration context (lib/A/PresetD1pA.v:75-78): the hypotheses below that stand for its
   premises are written in the same context, so that they have exactly its binders' types. *)
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance CfImg_A.

(* START-UP. Donor AD2o.v -> AD1q.v:88-89 tfib_startup_T1 (lib/A/AB1n.v). Statement lib/A/PresetD1qA.v (lane CwD1q,
   PROVISIONAL there); OWNER a Theorem Labs lane. HS_tfib: the core's hand-off table (lib/A/AB01.v). *)
Hypothesis H_tfib_startup_T1_A : tfib_startup_T1_A HS_tfib.

(* THE DRIVER WALK. Donor AD1q.v:77-78 DRV_MAINX / AD1p.v:85 tfib_drv_main. OWNER CwD1pA (lib/A/PresetD1pA.v). *)
Hypothesis H_tfib_drv_main_A : tfib_drv_main_A.

(* THE SECOND ALLOCATOR INSTANCE at TfibB. OWNER a Theorem Labs lane. Donor Lets AD2o.v:42-44 (AMALLOC, AFREE, AICPY). The
   frame area (the donor's ACfi.v:90-91 link_ASM2) is the callee record's pcc_stack_malloc on #102 (a premise of the
   statement, not of this Section). malloc and free in their keep forms (YGcfMallocComposeKeep): the leaf's
   memnorm keep, which the layer's leaves no longer carry since field round 3 part 3c; free in its primed form under the
   re-hide (YG0dcfR.afree_realizes_cf_rh with the keep). *)
Hypothesis H_amalloc_realizes_cf_A : forall rc : YM05.RunCeil,
  YGcfMallocComposeKeep.amalloc_realizes_cf_keep (cp := CfParams_preset) tfibsegs TfibB.
Hypothesis H_afree_realizes_cf_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fx) (cp := CfParams_preset) tfibsegs TfibB.
(* the memcpy / memset texts in a Theorem Labs lane's KEEP form (lib/Reusable/YGcallMxmn.v aintrin_realizes_xm: a8's
   aintrin_realizes_cf with the memnorm keep `memnorm segs mem -> memnorm segs mem'` as its last post conjunct). The
   driver walk's AICPY (lib/A/PresetD1pA.v, lane MnPrefix) and CwSites' printf results (lib/A/PresetD1sitesA.v)
   take this form, so it replaces the plain aintrin_realizes_cf premises of this Section. *)
Hypothesis H_aintrin_realizes_xm_cpy_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcallMxmn.aintrin_realizes_xm (fx := fx) tfibsegs TfibB
    (ARcf (rc := rc) (cp := CfParams_preset) tfibsegs TfibB) OCpy (pc_wrap_memcpy (as_code TfibB)).
Hypothesis H_aintrin_realizes_xm_set_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcallMxmn.aintrin_realizes_xm (fx := fx) tfibsegs TfibB
    (ARcf (rc := rc) (cp := CfParams_preset) tfibsegs TfibB) OSet (pc_wrap_memset (as_code TfibB)).

(* THE READ INTERCEPTOR'S CHECK over ARcf. Donor Let AD2o.v:48 ARDCHK (AD2m.v:22 tfib_ARDCHK). Statement
   aread_check_stmt_cf (lane CwPreA, lib/A/PresetD1preA.v); no result statement yet. *)
Hypothesis H_aread_check_stmt_cf_A : forall rc : YM05.RunCeil, aread_check_stmt_cf (cp := CfParams_preset) TfibB.

(* THE INTERCEPTOR SITES over ARcf. Donor Lets AD2o.v:57-61 (FWS, RFS, FPO, FPR, FPU). Results of lane CwPreA
   (lib/A/PresetD1preAx.v). *)
Hypothesis H_tfib_fwrite_site_cf_A : tfib_fwrite_site_cf_A.
Hypothesis H_tfib_refused_site_cf_A : tfib_refused_site_cf_A.
Hypothesis H_tfib_fprintf_open_site_cf_A : tfib_fprintf_open_site_cf_A.
Hypothesis H_tfib_fprintf_rderr_site_cf_A : tfib_fprintf_rderr_site_cf_A.
Hypothesis H_tfib_fprintf_usage_site_cf_A : tfib_fprintf_usage_site_cf_A.

(* THE PRINTF AND EXIT SITES over ARcf. Donor Lets AD2o.v:52-53, :62 (PF1, PFN, EXS). Results of lane CwSites
   (lib/A/PresetD1sitesA.v). *)
Hypothesis H_tfib_printf_first_cf_A : tfib_printf_first_cf_A.
Hypothesis H_tfib_printf_next_cf_A : tfib_printf_next_cf_A.
Hypothesis H_tfib_exit_site_cf_A : tfib_exit_site_cf_A.
(* #102 (no-DW interface, PresetCfnA.v, first at commit 8259b94c42ee): THE INSTANCE UNIVERSE'S CLOSURE at the slot's
   context set (the slot pre's last conjunct, state-free). OWNER: the universe generator (two Theorem Labs lanes)
   with a Theorem Labs lane's per-run universe ruling; the driver passes it to every slot call. *)
Hypothesis H_univ_closure_A : @PRH_Base.prh_univ_closure PresetCfnA.preset_prh_img TfibB CfImg_A PresetCfnA.iface_ctx0.

(* THE RELRO RANGE IS READ-ONLY. Donor Let AD2o.v:47 RO_IN (`or_intror`). PROVED at core 615056094a8f, which sets
   lib/A/ACeg.v's in_ro_tfa to preset's PT_GNU_RELRO [0xa19f0, 0xa3000) = the listing's relro range
   (lib/A/PAImg_prog.v A_prog_relro_lo / A_prog_relro_hi), so the donor's `or_intror` carries over unchanged. *)
Lemma relro_in_ro_A : forall (rc : YM05.RunCeil) (a : Z),
  @YC4aP.pa_relro_lo rc A_prog_listing (PI_prog_A (rc := rc)) <= a <
  @YC4aP.pa_relro_hi rc A_prog_listing (PI_prog_A (rc := rc)) -> in_ro_tfa a.
Proof. intros rc a H. right. exact H. Qed.

Theorem TFIB_T_of_partsXF_A_holds : TFIB_T_of_partsXF_A.
Proof.
intros sm iface_room_np XM_LIB XN_LIB PAYLOAD_ROOM A_MOD_AT A_STAMP NPI NPS NPT HC HLX PROOM.
intros sp brk mbase rnd inp en_p Hsp Hbrk Hmb Hfit Hinp HNR.
pose (rc := YM05.RunCeilOf (bv_unsigned sp) (valid_sp_window_D2A sp Hsp)).
pose proof (tfib_lib_x_all_A_holds rc CfImg_A A_prog_listing (PI_prog_A (rc := rc)) TfibB
  sm iface_room_np ameter_triv XM_LIB XN_LIB PAYLOAD_ROOM A_MOD_AT A_STAMP (HC rc) (HLX rc)) as LIBX.
refine (tfib_srealizesX_A_holds rc HS_tfib H_tfib_startup_T1_A _ sp rnd brk mbase inp en_p
  Hsp Hbrk Hmb Hfit Hinp HNR (YM05.ceil_of_top_run (valid_sp_window_D2A sp Hsp))).
exact (H_tfib_drv_main_A rc A_prog_listing (PI_prog_A (rc := rc)) sm iface_room_np NPI NPS NPT
  TfibB TfibB_syms
  (H_amalloc_realizes_cf_A rc) (H_afree_realizes_cf_A rc) (H_aintrin_realizes_xm_cpy_A rc YK11.fx0) (H_aread_check_stmt_cf_A rc)
  ameter_triv XM_LIB XN_LIB (fun _ _ => I) (relro_in_ro_A rc) PAYLOAD_ROOM NR_agrees_A PROOM LIBX H_univ_closure_A (ltac:(vm_compute; lia) : (4 * YCbqGwild.K_LLVMF <= u_wmax (as_universe TfibB))%nat)
  (proj1 PAImg_prog.A_entry_LLVMFuzzerTestOneInput)
  AD1k.xst tfib_xst_frame
  (fun fx => H_tfib_printf_first_cf_A fx rc CfImg_A CfParams_preset TfibB TfibB_syms
     (H_aintrin_realizes_xm_cpy_A rc fx) (H_aintrin_realizes_xm_set_A rc fx))
  (fun fx => H_tfib_printf_next_cf_A fx rc CfImg_A CfParams_preset TfibB TfibB_syms
     (H_aintrin_realizes_xm_cpy_A rc fx) (H_aintrin_realizes_xm_set_A rc fx))
  AD1k.est tfib_est_img tfib_est_frame
  (H_tfib_fwrite_site_cf_A YK11.fx0 rc CfImg_A CfParams_preset TfibB AD1k.est TfibB_syms est_written)
  (H_tfib_refused_site_cf_A YK11.fx0 rc CfImg_A CfParams_preset TfibB AD1k.est TfibB_syms est_after_vf)
  (H_tfib_fprintf_open_site_cf_A YK11.fx0 rc CfImg_A CfParams_preset TfibB AD1k.est TfibB_syms est_after_vf)
  (H_tfib_fprintf_rderr_site_cf_A YK11.fx0 rc CfImg_A CfParams_preset TfibB AD1k.est TfibB_syms est_after_vf)
  (H_tfib_fprintf_usage_site_cf_A YK11.fx0 rc CfImg_A CfParams_preset TfibB AD1k.est TfibB_syms est_after_vf)
  (fun fx => H_tfib_exit_site_cf_A fx rc CfImg_A CfParams_preset TfibB TfibB_syms)).
Qed.

(* The ROOM forms (PresetD2oA.v section 2): the same parts, the payload's room given directly. The driver walk is
   taken at the premise NR := the room of this input's payload (every argv / file arm), so its payload bridge is
   the identity, and the start-up + driver step is a Theorem Labs lane's tfib_srealizesX_NR_A_holds at that NR. *)
Theorem TFIB_T_room_all_A_holds : TFIB_T_room_all_A.
Proof.
intros sm iface_room_np XM_LIB XN_LIB PAYLOAD_ROOM A_MOD_AT A_STAMP NPI NPS NPT HC HLX.
intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp HROOM.
pose (rc := YM05.RunCeilOf (bv_unsigned sp) (valid_sp_window_D2A sp Hsp)).
pose proof (tfib_lib_x_all_A_holds rc CfImg_A A_prog_listing (PI_prog_A (rc := rc)) TfibB
  sm iface_room_np ameter_triv XM_LIB XN_LIB PAYLOAD_ROOM A_MOD_AT A_STAMP (HC rc) (HLX rc)) as LIBX.
pose (NR := fun (_ : ExecEntry) (i : ProcInput) => forall a0 p data : list byte,
  in_argv i = [a0; p] -> Fs.fs_lookup (in_fs i) p = Some data -> PAYLOAD_ROOM (payload data)).
refine (tfib_srealizesX_NR_A_holds NR rc HS_tfib H_tfib_startup_T1_A _ sp rnd brk mbase inp (mkEntry sp brk mbase rnd)
  Hsp Hbrk Hmb Hfit Hinp HROOM (YM05.ceil_of_top_run (valid_sp_window_D2A sp Hsp))).
exact (H_tfib_drv_main_A rc A_prog_listing (PI_prog_A (rc := rc)) sm iface_room_np NPI NPS NPT
  TfibB TfibB_syms
  (H_amalloc_realizes_cf_A rc) (H_afree_realizes_cf_A rc) (H_aintrin_realizes_xm_cpy_A rc YK11.fx0) (H_aread_check_stmt_cf_A rc)
  ameter_triv XM_LIB XN_LIB (fun _ _ => I) (relro_in_ro_A rc) PAYLOAD_ROOM NR (fun en_p' i a0 p data HN => HN a0 p data) LIBX H_univ_closure_A (ltac:(vm_compute; lia) : (4 * YCbqGwild.K_LLVMF <= u_wmax (as_universe TfibB))%nat)
  (proj1 PAImg_prog.A_entry_LLVMFuzzerTestOneInput)
  AD1k.xst tfib_xst_frame
  (fun fx => H_tfib_printf_first_cf_A fx rc CfImg_A CfParams_preset TfibB TfibB_syms
     (H_aintrin_realizes_xm_cpy_A rc fx) (H_aintrin_realizes_xm_set_A rc fx))
  (fun fx => H_tfib_printf_next_cf_A fx rc CfImg_A CfParams_preset TfibB TfibB_syms
     (H_aintrin_realizes_xm_cpy_A rc fx) (H_aintrin_realizes_xm_set_A rc fx))
  AD1k.est tfib_est_img tfib_est_frame
  (H_tfib_fwrite_site_cf_A YK11.fx0 rc CfImg_A CfParams_preset TfibB AD1k.est TfibB_syms est_written)
  (H_tfib_refused_site_cf_A YK11.fx0 rc CfImg_A CfParams_preset TfibB AD1k.est TfibB_syms est_after_vf)
  (H_tfib_fprintf_open_site_cf_A YK11.fx0 rc CfImg_A CfParams_preset TfibB AD1k.est TfibB_syms est_after_vf)
  (H_tfib_fprintf_rderr_site_cf_A YK11.fx0 rc CfImg_A CfParams_preset TfibB AD1k.est TfibB_syms est_after_vf)
  (H_tfib_fprintf_usage_site_cf_A YK11.fx0 rc CfImg_A CfParams_preset TfibB AD1k.est TfibB_syms est_after_vf)
  (fun fx => H_tfib_exit_site_cf_A fx rc CfImg_A CfParams_preset TfibB TfibB_syms)).
Qed.

Theorem TFIB_T_room_A_holds : TFIB_T_room_A.
Proof.
intros sm iface_room_np XM_LIB XN_LIB PAYLOAD_ROOM A_MOD_AT A_STAMP NPI NPS NPT HC HLX.
intros sp brk mbase rnd inp a0 p data Hsp Hbrk Hmb Hfit Hinp Hargv Hlook HPR.
refine (TFIB_T_room_all_A_holds sm iface_room_np XM_LIB XN_LIB PAYLOAD_ROOM A_MOD_AT A_STAMP
  NPI NPS NPT HC HLX sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp _).
(* argv fixes p and the file system fixes data, so the one arm given is every arm *)
intros a0' p' data' Hargv' Hlook'. rewrite Hargv in Hargv'. injection Hargv' as _ Hp. subst p'.
rewrite Hlook in Hlook'. injection Hlook' as Hd. subst data'. exact HPR.
Qed.
(* the all-arms room form at the program SLOT itself (the A' halts top proves the slot from the callee record and the
   harness walk), from the driver parts of this Section, at any non-primary room with its three laws (the image-A twin
   of PresetD2oBPf.TFIB_T_room_all_B_of_slot) *)
Theorem TFIB_T_room_all_A_of_slot : forall (iface_room_np : astate -> Prop),
  iface_room_np_init iface_room_np -> iface_room_np_step (ci := CfImg_A) (cp := CfParams_preset) iface_room_np ->
  iface_room_np_tail (cp := CfParams_preset) iface_room_np ->
  forall (sm : list Z -> Z * Z) (XM_LIB XN_LIB : Z -> Z) (PAYLOAD_ROOM : list byte -> Prop),
  (forall rc : YM05.RunCeil,
     preset_lib_contract_x_all (rc := rc) (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape)
       (L := A_prog_listing) (PA := PI_prog_A (rc := rc)) (ci := CfImg_A)
       sm iface_room_np TfibB ameter_triv XM_LIB XN_LIB PAYLOAD_ROOM) ->
  TFIB_T_room_all_concl_A PAYLOAD_ROOM.
Proof.
intros iface_room_np NPI NPS NPT sm XM_LIB XN_LIB PAYLOAD_ROOM SLOT.
intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp HROOM.
pose (rc := YM05.RunCeilOf (bv_unsigned sp) (valid_sp_window_D2A sp Hsp)).
pose (NR := fun (_ : ExecEntry) (i : ProcInput) => forall a0 p data : list byte,
  in_argv i = [a0; p] -> Fs.fs_lookup (in_fs i) p = Some data -> PAYLOAD_ROOM (payload data)).
refine (tfib_srealizesX_NR_A_holds NR rc HS_tfib H_tfib_startup_T1_A _ sp rnd brk mbase inp (mkEntry sp brk mbase rnd)
  Hsp Hbrk Hmb Hfit Hinp HROOM (YM05.ceil_of_top_run (valid_sp_window_D2A sp Hsp))).
exact (H_tfib_drv_main_A rc A_prog_listing (PI_prog_A (rc := rc)) sm iface_room_np NPI NPS NPT
  TfibB TfibB_syms
  (H_amalloc_realizes_cf_A rc) (H_afree_realizes_cf_A rc) (H_aintrin_realizes_xm_cpy_A rc YK11.fx0) (H_aread_check_stmt_cf_A rc)
  ameter_triv XM_LIB XN_LIB (fun _ _ => I) (relro_in_ro_A rc) PAYLOAD_ROOM NR (fun en_p' i a0 p data HN => HN a0 p data) (SLOT rc) H_univ_closure_A (ltac:(vm_compute; lia) : (4 * YCbqGwild.K_LLVMF <= u_wmax (as_universe TfibB))%nat)
  (proj1 PAImg_prog.A_entry_LLVMFuzzerTestOneInput)
  AD1k.xst tfib_xst_frame
  (fun fx => H_tfib_printf_first_cf_A fx rc CfImg_A CfParams_preset TfibB TfibB_syms
     (H_aintrin_realizes_xm_cpy_A rc fx) (H_aintrin_realizes_xm_set_A rc fx))
  (fun fx => H_tfib_printf_next_cf_A fx rc CfImg_A CfParams_preset TfibB TfibB_syms
     (H_aintrin_realizes_xm_cpy_A rc fx) (H_aintrin_realizes_xm_set_A rc fx))
  AD1k.est tfib_est_img tfib_est_frame
  (H_tfib_fwrite_site_cf_A YK11.fx0 rc CfImg_A CfParams_preset TfibB AD1k.est TfibB_syms est_written)
  (H_tfib_refused_site_cf_A YK11.fx0 rc CfImg_A CfParams_preset TfibB AD1k.est TfibB_syms est_after_vf)
  (H_tfib_fprintf_open_site_cf_A YK11.fx0 rc CfImg_A CfParams_preset TfibB AD1k.est TfibB_syms est_after_vf)
  (H_tfib_fprintf_rderr_site_cf_A YK11.fx0 rc CfImg_A CfParams_preset TfibB AD1k.est TfibB_syms est_after_vf)
  (H_tfib_fprintf_usage_site_cf_A YK11.fx0 rc CfImg_A CfParams_preset TfibB AD1k.est TfibB_syms est_after_vf)
  (fun fx => H_tfib_exit_site_cf_A fx rc CfImg_A CfParams_preset TfibB TfibB_syms)).
Qed.
End parts.
