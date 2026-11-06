(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from the proof of TFIB_T_of_partsXF in proofs/cgif/cgif_file_fuzzer/lib/YD2o.v:35-79
   (asan-ubsan; its asan twin is lib/A/AD2o.v:40-84) for fuzz_preset's asan-ubsan image.
   The PROOF of TFIB_T_of_partsXF_B (lib/AU/PresetD2oB.v): the donor's Section b assembly, in which every input that is
   not a theorem of this tree is a NAMED Section hypothesis, one per obligation, with its owner. The donor's `Let`s
   that are proved in this tree are used as theorems: TfibB_syms (lib/Reusable/YD2l.v), tfib_xst_frame / tfib_est_img /
   tfib_est_frame / est_written / est_after_vf (lib/Reusable/YD1k.v), tfib_srealizesX_B_holds (lane CwD1q, lib/AU/PresetD1qB.v)
   and tfib_lib_x_all_B_holds (lane CwCfiB, lib/AU/PresetCfiBPf.v). Nothing in this file is a proof of a function
   (rule 24: no function proved; this is the composition / driver layer of a port).
   The donor's tfib_srealizesX_top (YD2o.v:70-77) is the last step: the run ceiling at sp's window (YM05.RunCeilOf). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Shapes.
From OSSVerify.omx_clap_core.fuzz_preset Require Images.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK15 YK18 YA02 YM05 YO06 YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0f YG0n YG0d YC5d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG0ncf YG0dcf YG0d2cf YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YP0b YPsym YC4aP YGcallMxmn YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB01 YF0m YD2l YCeg YD1w YD1x YD1k.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetCfnB PresetTFIBAU.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetD1sitesB PresetD1preB PresetD1preBx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetD1qB PresetCfiB PresetCfiBPf PresetD1pB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetD2oB PresetDrvTopBStmt.
(* the image's CfImg record (lib/AU/CfImgB.v, blob 4b8e1b9596a7; its one home a working branch 5023be8f2869) and the B NR
   form of the start-up + driver step *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB PresetD1qNRB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Base.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* The donor's valid_sp_windowX (YD2o.v:22-23). *)
Lemma valid_sp_window_D2B : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

(* The class (C) check of the CfImg record (owner order 06:00Z): CfImg_B's memcpy cells are the image's, the rows
   lib/Reusable/YF0m.v:96 `z8 (ANum 0xa46c8) 0x9bb04` (cf_real_memcpy holds cf_pc_memcpy) and :180 `z8 (ANum 0xa2878)
   0xa46c8` (cf_got_memcpy holds &real_memcpy), owned-static :1582 (a Theorem Labs lane, YF0m 82bd1cbdc76). *)
Lemma cfimg_B_memcpy_cells :
  @cf_real_memcpy CfImg_B = 0xa46c8 /\ @cf_got_memcpy CfImg_B = 0xa2878 /\ @cf_pc_memcpy CfImg_B = 0x9bb04.
Proof. split; [reflexivity | split; reflexivity]. Qed.

Section parts.
(* The driver walk's elaboration context (lib/AU/PresetD1pB.v): the hypotheses below that stand for its
   premises are written in the same context, so that they have exactly its binders' types. *)
#[local] Existing Instance YK11.fx0.
(* the image's CfImg record: CfImg_B (lib/AU/CfImgB.v; owner order 06:00Z) *)
#[local] Existing Instance CfImg_B.

(* START-UP. Donor YD2o.v -> YD1q.v:88-89 tfib_startup_T1 (lib/Reusable/YB1n.v). Statement lib/AU/PresetD1qB.v (lane CwD1q,
   PROVISIONAL there); OWNER a Theorem Labs lane. HS_tfib: the core's hand-off table (lib/Reusable/YB01.v). *)
Hypothesis H_tfib_startup_T1_B : tfib_startup_T1_B HS_tfib.

(* THE DRIVER WALK. Donor YD1q.v:73-74 DRV_MAINX / YD1p.v:77 tfib_drv_main. OWNER CwD1pB (lib/AU/PresetD1pB.v). *)
Hypothesis H_tfib_drv_main_B : tfib_drv_main_B.

(* THE SECOND ALLOCATOR INSTANCE at TfibB. OWNER a Theorem Labs lane. Donor Lets YD2o.v:37-39 (AMALLOC, AFREE, AICPY). The
   frame area (the donor's YCfi.v:88-89 link_ASM2) is the callee record's pcc_stack_malloc on #102 (a premise of the
   statement, not of this Section). malloc and free in their keep forms (YGcfMallocComposeKeep): the leaf's
   memnorm keep, which the layer's leaves no longer carry since field round 3 part 3c; free in its primed form under the
   re-hide (YG0dcfR.afree_realizes_cf_rh with the keep). *)
Hypothesis H_amalloc_realizes_cf_B : forall rc : YM05.RunCeil,
  YGcfMallocComposeKeep.amalloc_realizes_cf_keep (cp := CfParams_preset) tfibsegs TfibB.
Hypothesis H_afree_realizes_cf_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fx) (cp := CfParams_preset) tfibsegs TfibB.
(* the memcpy / memset texts in a Theorem Labs lane's KEEP form (lib/Reusable/YGcallMxmn.v aintrin_realizes_xm: a8's
   aintrin_realizes_cf with the memnorm keep `memnorm segs mem -> memnorm segs mem'` as its last post conjunct). The
   driver walk's AICPY (lib/AU/PresetD1pB.v, lane MnPrefix) and CwSites' printf results (lib/AU/PresetD1sitesB.v)
   take this form, so it replaces the plain aintrin_realizes_cf premises of this Section. *)
Hypothesis H_aintrin_realizes_xm_cpy_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcallMxmn.aintrin_realizes_xm (fx := fx) tfibsegs TfibB
    (ARcf (rc := rc) (cp := CfParams_preset) tfibsegs TfibB) OCpy (pc_wrap_memcpy (as_code TfibB)).
Hypothesis H_aintrin_realizes_xm_set_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcallMxmn.aintrin_realizes_xm (fx := fx) tfibsegs TfibB
    (ARcf (rc := rc) (cp := CfParams_preset) tfibsegs TfibB) OSet (pc_wrap_memset (as_code TfibB)).

(* THE READ INTERCEPTOR'S CHECK over ARcf. Donor Let YD2o.v:43 ARDCHK (YD2m tfib_ARDCHK). Statement
   aread_check_stmt_cf (lane CwPreB, lib/AU/PresetD1preB.v); no result statement yet. *)
Hypothesis H_aread_check_stmt_cf_B : forall rc : YM05.RunCeil, aread_check_stmt_cf (cp := CfParams_preset) TfibB.

(* THE INTERCEPTOR SITES over ARcf. Donor Lets YD2o.v:52-56 (FWS, RFS, FPO, FPR, FPU). Results of lane CwPreB
   (lib/AU/PresetD1preBx.v). *)
Hypothesis H_tfib_fwrite_site_cf_B : tfib_fwrite_site_cf_B.
Hypothesis H_tfib_refused_site_cf_B : tfib_refused_site_cf_B.
Hypothesis H_tfib_fprintf_open_site_cf_B : tfib_fprintf_open_site_cf_B.
Hypothesis H_tfib_fprintf_rderr_site_cf_B : tfib_fprintf_rderr_site_cf_B.
Hypothesis H_tfib_fprintf_usage_site_cf_B : tfib_fprintf_usage_site_cf_B.

(* THE PRINTF AND EXIT SITES over ARcf. Donor Lets YD2o.v:47-48, :57 (PF1, PFN, EXS). Results of lane CwSites
   (lib/AU/PresetD1sitesB.v). *)
Hypothesis H_tfib_printf_first_cf_B : tfib_printf_first_cf_B.
Hypothesis H_tfib_printf_next_cf_B : tfib_printf_next_cf_B.
Hypothesis H_tfib_exit_site_cf_B : tfib_exit_site_cf_B.
(* #102 (no-DW interface, PresetCfnB.v, first at commit 8259b94c42ee): THE INSTANCE UNIVERSE'S CLOSURE at the slot's
   context set (the slot pre's last conjunct, state-free). OWNER: the universe generator (two Theorem Labs lanes)
   with a Theorem Labs lane's per-run universe ruling; the driver passes it to every slot call. *)
Hypothesis H_univ_closure_B : @PRH_Base.prh_univ_closure PresetCfnB.preset_prh_img TfibB CfImg_B PresetCfnB.iface_ctx0.

(* THE RELRO RANGE IS READ-ONLY. Donor Let YD2o.v:42 RO_IN (`or_intror`). PROVED on a Theorem Labs lane's relocation
   (a working branch 933892daaab group G2 and later): lib/Reusable/YCeg.v's in_ro_tfa has
   TFIB_RELRO_LO / HI = 0xa2240 / 0xa4000 = the listing's relro range (lib/B/PAImg_prog.v B_prog_relro_lo / hi, the
   image's PT_GNU_RELRO), so the donor's `or_intror` carries over unchanged. Pending relocB: on the unrelocated YCeg
   (cgif's window) this proof does not type-check. *)
Lemma relro_in_ro_B : forall (rc : YM05.RunCeil) (a : Z),
  @YC4aP.pa_relro_lo rc B_prog_listing (PI_prog_B (rc := rc)) <= a <
  @YC4aP.pa_relro_hi rc B_prog_listing (PI_prog_B (rc := rc)) -> in_ro_tfa a.
Proof. intros rc a H. right. exact H. Qed.

Theorem TFIB_T_of_partsXF_B_holds : TFIB_T_of_partsXF_B.
Proof.
intros sm iface_room_np XM_LIB XN_LIB PAYLOAD_ROOM A_MOD_AT A_STAMP NPI NPS NPT HC HLX PROOM.
intros sp brk mbase rnd inp en_p Hsp Hbrk Hmb Hfit Hinp HNR.
pose (rc := YM05.RunCeilOf (bv_unsigned sp) (valid_sp_window_D2B sp Hsp)).
pose proof (tfib_lib_x_all_B_holds rc CfImg_B B_prog_listing (PI_prog_B (rc := rc)) TfibB
  sm iface_room_np ameter_triv XM_LIB XN_LIB PAYLOAD_ROOM A_MOD_AT A_STAMP (HC rc) (HLX rc)) as LIBX.
refine (tfib_srealizesX_B_holds rc HS_tfib H_tfib_startup_T1_B _ sp rnd brk mbase inp en_p
  Hsp Hbrk Hmb Hfit Hinp HNR (YM05.ceil_of_top_run (valid_sp_window_D2B sp Hsp))).
exact (H_tfib_drv_main_B rc B_prog_listing (PI_prog_B (rc := rc)) sm iface_room_np NPI NPS NPT
  TfibB TfibB_syms
  (H_amalloc_realizes_cf_B rc) (H_afree_realizes_cf_B rc) (H_aintrin_realizes_xm_cpy_B rc YK11.fx0) (H_aread_check_stmt_cf_B rc)
  ameter_triv XM_LIB XN_LIB (fun _ _ => I) (relro_in_ro_B rc) PAYLOAD_ROOM NR_agrees_B PROOM LIBX H_univ_closure_B (ltac:(vm_compute; lia) : (4 * YCbqGwild.K_LLVMF <= u_wmax (as_universe TfibB))%nat)
  (proj1 PAImg_prog.B_entry_LLVMFuzzerTestOneInput)
  YD1k.xst tfib_xst_frame
  (fun fx => H_tfib_printf_first_cf_B fx rc CfImg_B CfParams_preset TfibB TfibB_syms
     (H_aintrin_realizes_xm_cpy_B rc fx) (H_aintrin_realizes_xm_set_B rc fx))
  (fun fx => H_tfib_printf_next_cf_B fx rc CfImg_B CfParams_preset TfibB TfibB_syms
     (H_aintrin_realizes_xm_cpy_B rc fx) (H_aintrin_realizes_xm_set_B rc fx))
  YD1k.est tfib_est_img tfib_est_frame
  (H_tfib_fwrite_site_cf_B YK11.fx0 rc CfImg_B CfParams_preset TfibB YD1k.est TfibB_syms est_written)
  (H_tfib_refused_site_cf_B YK11.fx0 rc CfImg_B CfParams_preset TfibB YD1k.est TfibB_syms est_after_vf)
  (H_tfib_fprintf_open_site_cf_B YK11.fx0 rc CfImg_B CfParams_preset TfibB YD1k.est TfibB_syms est_after_vf)
  (H_tfib_fprintf_rderr_site_cf_B YK11.fx0 rc CfImg_B CfParams_preset TfibB YD1k.est TfibB_syms est_after_vf)
  (H_tfib_fprintf_usage_site_cf_B YK11.fx0 rc CfImg_B CfParams_preset TfibB YD1k.est TfibB_syms est_after_vf)
  (fun fx => H_tfib_exit_site_cf_B fx rc CfImg_B CfParams_preset TfibB TfibB_syms)).
Qed.

(* The ROOM forms (PresetD2oB.v section 2): the same parts, the payload's room given directly. The driver walk is
   taken at the premise NR := the room of this input's payload (every argv / file arm), so its payload bridge is
   the identity, and the start-up + driver step is a Theorem Labs lane's tfib_srealizesX_NR_B_holds at that NR. *)
Theorem TFIB_T_room_all_B_holds : TFIB_T_room_all_B.
Proof.
intros sm iface_room_np XM_LIB XN_LIB PAYLOAD_ROOM A_MOD_AT A_STAMP NPI NPS NPT HC HLX.
intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp HROOM.
pose (rc := YM05.RunCeilOf (bv_unsigned sp) (valid_sp_window_D2B sp Hsp)).
pose proof (tfib_lib_x_all_B_holds rc CfImg_B B_prog_listing (PI_prog_B (rc := rc)) TfibB
  sm iface_room_np ameter_triv XM_LIB XN_LIB PAYLOAD_ROOM A_MOD_AT A_STAMP (HC rc) (HLX rc)) as LIBX.
pose (NR := fun (_ : ExecEntry) (i : ProcInput) => forall a0 p data : list byte,
  in_argv i = [a0; p] -> Fs.fs_lookup (in_fs i) p = Some data -> PAYLOAD_ROOM (payload data)).
refine (tfib_srealizesX_NR_B_holds NR rc HS_tfib H_tfib_startup_T1_B _ sp rnd brk mbase inp (mkEntry sp brk mbase rnd)
  Hsp Hbrk Hmb Hfit Hinp HROOM (YM05.ceil_of_top_run (valid_sp_window_D2B sp Hsp))).
exact (H_tfib_drv_main_B rc B_prog_listing (PI_prog_B (rc := rc)) sm iface_room_np NPI NPS NPT
  TfibB TfibB_syms
  (H_amalloc_realizes_cf_B rc) (H_afree_realizes_cf_B rc) (H_aintrin_realizes_xm_cpy_B rc YK11.fx0) (H_aread_check_stmt_cf_B rc)
  ameter_triv XM_LIB XN_LIB (fun _ _ => I) (relro_in_ro_B rc) PAYLOAD_ROOM NR (fun en_p' i a0 p data HN => HN a0 p data) LIBX H_univ_closure_B (ltac:(vm_compute; lia) : (4 * YCbqGwild.K_LLVMF <= u_wmax (as_universe TfibB))%nat)
  (proj1 PAImg_prog.B_entry_LLVMFuzzerTestOneInput)
  YD1k.xst tfib_xst_frame
  (fun fx => H_tfib_printf_first_cf_B fx rc CfImg_B CfParams_preset TfibB TfibB_syms
     (H_aintrin_realizes_xm_cpy_B rc fx) (H_aintrin_realizes_xm_set_B rc fx))
  (fun fx => H_tfib_printf_next_cf_B fx rc CfImg_B CfParams_preset TfibB TfibB_syms
     (H_aintrin_realizes_xm_cpy_B rc fx) (H_aintrin_realizes_xm_set_B rc fx))
  YD1k.est tfib_est_img tfib_est_frame
  (H_tfib_fwrite_site_cf_B YK11.fx0 rc CfImg_B CfParams_preset TfibB YD1k.est TfibB_syms est_written)
  (H_tfib_refused_site_cf_B YK11.fx0 rc CfImg_B CfParams_preset TfibB YD1k.est TfibB_syms est_after_vf)
  (H_tfib_fprintf_open_site_cf_B YK11.fx0 rc CfImg_B CfParams_preset TfibB YD1k.est TfibB_syms est_after_vf)
  (H_tfib_fprintf_rderr_site_cf_B YK11.fx0 rc CfImg_B CfParams_preset TfibB YD1k.est TfibB_syms est_after_vf)
  (H_tfib_fprintf_usage_site_cf_B YK11.fx0 rc CfImg_B CfParams_preset TfibB YD1k.est TfibB_syms est_after_vf)
  (fun fx => H_tfib_exit_site_cf_B fx rc CfImg_B CfParams_preset TfibB TfibB_syms)).
Qed.

Theorem TFIB_T_room_B_holds : TFIB_T_room_B.
Proof.
intros sm iface_room_np XM_LIB XN_LIB PAYLOAD_ROOM A_MOD_AT A_STAMP NPI NPS NPT HC HLX.
intros sp brk mbase rnd inp a0 p data Hsp Hbrk Hmb Hfit Hinp Hargv Hlook HPR.
refine (TFIB_T_room_all_B_holds sm iface_room_np XM_LIB XN_LIB PAYLOAD_ROOM A_MOD_AT A_STAMP
  NPI NPS NPT HC HLX sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp _).
(* argv fixes p and the file system fixes data, so the one arm given is every arm *)
intros a0' p' data' Hargv' Hlook'. rewrite Hargv in Hargv'. injection Hargv' as _ Hp. subst p'.
rewrite Hlook in Hlook'. injection Hlook' as Hd. subst data'. exact HPR.
Qed.
(* S1 of the B' halts top (lib/AU/PresetDrvTopBStmt.v TFIB_T_room_all_B_closed_stmt): the all-arms room form at the
   program SLOT itself (the halts top proves the slot from the callee record and the harness walk, HaltsClosedB.v),
   from the driver parts of this Section, at any non-primary room with its three laws. *)
Theorem TFIB_T_room_all_B_of_slot : forall (iface_room_np : astate -> Prop),
  iface_room_np_init iface_room_np -> iface_room_np_step (ci := CfImg_B) (cp := CfParams_preset) iface_room_np ->
  iface_room_np_tail (cp := CfParams_preset) iface_room_np ->
  forall (sm : list Z -> Z * Z) (XM_LIB XN_LIB : Z -> Z) (PAYLOAD_ROOM : list byte -> Prop),
  (forall rc : YM05.RunCeil,
     preset_lib_contract_x_all (rc := rc) (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape)
       (L := B_prog_listing) (PA := PI_prog_B (rc := rc)) (ci := CfImg_B)
       sm iface_room_np TfibB ameter_triv XM_LIB XN_LIB PAYLOAD_ROOM) ->
  TFIB_T_room_all_concl_B PAYLOAD_ROOM.
Proof.
intros iface_room_np NPI NPS NPT sm XM_LIB XN_LIB PAYLOAD_ROOM SLOT.
intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp HROOM.
pose (rc := YM05.RunCeilOf (bv_unsigned sp) (valid_sp_window_D2B sp Hsp)).
pose (NR := fun (_ : ExecEntry) (i : ProcInput) => forall a0 p data : list byte,
  in_argv i = [a0; p] -> Fs.fs_lookup (in_fs i) p = Some data -> PAYLOAD_ROOM (payload data)).
refine (tfib_srealizesX_NR_B_holds NR rc HS_tfib H_tfib_startup_T1_B _ sp rnd brk mbase inp (mkEntry sp brk mbase rnd)
  Hsp Hbrk Hmb Hfit Hinp HROOM (YM05.ceil_of_top_run (valid_sp_window_D2B sp Hsp))).
exact (H_tfib_drv_main_B rc B_prog_listing (PI_prog_B (rc := rc)) sm iface_room_np NPI NPS NPT
  TfibB TfibB_syms
  (H_amalloc_realizes_cf_B rc) (H_afree_realizes_cf_B rc) (H_aintrin_realizes_xm_cpy_B rc YK11.fx0) (H_aread_check_stmt_cf_B rc)
  ameter_triv XM_LIB XN_LIB (fun _ _ => I) (relro_in_ro_B rc) PAYLOAD_ROOM NR (fun en_p' i a0 p data HN => HN a0 p data) (SLOT rc) H_univ_closure_B (ltac:(vm_compute; lia) : (4 * YCbqGwild.K_LLVMF <= u_wmax (as_universe TfibB))%nat)
  (proj1 PAImg_prog.B_entry_LLVMFuzzerTestOneInput)
  YD1k.xst tfib_xst_frame
  (fun fx => H_tfib_printf_first_cf_B fx rc CfImg_B CfParams_preset TfibB TfibB_syms
     (H_aintrin_realizes_xm_cpy_B rc fx) (H_aintrin_realizes_xm_set_B rc fx))
  (fun fx => H_tfib_printf_next_cf_B fx rc CfImg_B CfParams_preset TfibB TfibB_syms
     (H_aintrin_realizes_xm_cpy_B rc fx) (H_aintrin_realizes_xm_set_B rc fx))
  YD1k.est tfib_est_img tfib_est_frame
  (H_tfib_fwrite_site_cf_B YK11.fx0 rc CfImg_B CfParams_preset TfibB YD1k.est TfibB_syms est_written)
  (H_tfib_refused_site_cf_B YK11.fx0 rc CfImg_B CfParams_preset TfibB YD1k.est TfibB_syms est_after_vf)
  (H_tfib_fprintf_open_site_cf_B YK11.fx0 rc CfImg_B CfParams_preset TfibB YD1k.est TfibB_syms est_after_vf)
  (H_tfib_fprintf_rderr_site_cf_B YK11.fx0 rc CfImg_B CfParams_preset TfibB YD1k.est TfibB_syms est_after_vf)
  (H_tfib_fprintf_usage_site_cf_B YK11.fx0 rc CfImg_B CfParams_preset TfibB YD1k.est TfibB_syms est_after_vf)
  (fun fx => H_tfib_exit_site_cf_B fx rc CfImg_B CfParams_preset TfibB TfibB_syms)).
Qed.
End parts.
