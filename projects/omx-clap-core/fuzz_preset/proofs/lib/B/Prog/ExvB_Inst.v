(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image B' (#102 pin d663f82d7f48, asan-ubsan; unstripped twin c90d4fa54d43),
   ex_value: THE WALK AT THE INSTANCE. ExvB_Final.ex_value_holds_B_final at
     B   := YD2l.TfibB (the B'-generated record, blob 95803a8b9493),
     cp  := CfParamsPreset.CfParams_preset,
     ARx := fun ly S Hp W mem md => YG0ncf.ARcf rsegs TfibB ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S
            (YGcallcf.v's ARxs, the generic rules' cf relation; written out here because ARxs is local to YGcallcf),
     PA  := PI_prog_B (passed explicitly, with PI := prh_img_B and L := B_prog_listing),
   with every image-fact / law field of EXV_HYP (ExvB_Stmt.v) discharged:
   - the closed image facts and the ARcf state facts by ExvB_ImgFacts.exvi_* (each ARcf fact lifted to ARxs by its
     first conjunct, since the field takes ARx only as a premise);
   - eh_errno / eh_palib / eh_head by PALibB.exvi_eh_*;
   - eh_laws by YGcallcf.AR_laws_x_xs and eh_ownlow by YGcallcf.ARx_owned_low_law_xs, both of YG0lawscf.AR_laws_ok_cf;
   - eh_asfx by YGcallScf.astack_free_x_xs (the free law at ARxs: xs_placed_cf survives stack_free_state);
   - eh_string by h-pre-b3's PROVED B' walk of ex_string, ExsB_Discharge.es_eh_string (blob 8f1ff97233d3), from the
     three discharges above (laws, head, PALib).
   NAMED PREMISES (the callee rows, stated at this instance verbatim as EXV_HYP's fields; owners as ExvB_Stmt.v
   records them):
   - HSTRCMP (eh_strcmp): YGcallMxmn.astrcmp_realizes_xrom at __wrap_strcmp, read-only-premise m-row; owner c-libc-stdio.
   - HSTRLEN (eh_strlen): YGcallMxmn.astrlen_realizes_xrom at __wrap_strlen, read-only-premise m-row; owner c-libc-stdio.
   - HBCMP (eh_bcmp): YGcallMxmn.abcmp_realizes_xm at __wrap_bcmp, m-row; owner c-libc-stdio.
   - HMEMCPY (eh_memcpy): YGcallMxmn.aintrin_realizes_xm at __asan_memcpy (OCpy), m-row; owner c-asan.
   - HSM1 (eh_sm1): YGcallMxmn.astack_malloc_realizes_xm, class 1 (__asan_stack_malloc_1), the class-1 frame area of
     FCiface.v; owner h-hpreset-7-frameclass.
   rc, ci, RL and SK stay universally quantified.
   Rule 24: proves function ex_value (image B') at the instance GIVEN the five callee rows above. No numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMx YGcallx YC1fP YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require ExvB_Final ExvB_ImgFacts ExsB_Discharge.
(* the instance: Required, not Imported, and cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YG0ncf YG0lawscf YGcallcf YGcallScf.
(* the four callee rows of record (c-libc-stdio rows102), cited in ex_value_holds_B_rows *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PRowCmp PRowCpy PSstrRo CfImgB.
(* the class-1 frame-area row of record (c-omx-alloc FrameXm102 07210922d952), cited in ex_value_holds_B_closed *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require FCxmCfxB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation ARXS :=
  (fun ly S Hp (W : world rsegs) mem md => YG0ncf.ARcf (cp := CP) rsegs TB ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).

Theorem ex_value_holds_B_inst : forall {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive} (SK : YI16.sink_head)
  (HSTRCMP : forall fx : YK11.FPState,
     YGcallMxmn.astrcmp_realizes_xrom (fx := fx) rsegs TB ARXS B_prog_relro_lo B_prog_relro_hi
       (B_prog_sigma AS___wrap_strcmp))
  (HSTRLEN : forall fx : YK11.FPState,
     YGcallMxmn.astrlen_realizes_xrom (fx := fx) rsegs TB ARXS B_prog_relro_lo B_prog_relro_hi
       (B_prog_sigma AS___wrap_strlen))
  (HBCMP : forall fx : YK11.FPState, YGcallMxmn.abcmp_realizes_xm (fx := fx) rsegs TB ARXS (B_prog_sigma AS___wrap_bcmp))
  (HMEMCPY : forall fx : YK11.FPState,
     YGcallMxmn.aintrin_realizes_xm (fx := fx) rsegs TB ARXS OCpy (B_prog_sigma AS___asan_memcpy))
  (HSM1 : forall fx : YK11.FPState, YGcallMxmn.astack_malloc_realizes_xm (fx := fx) rsegs TB ARXS 1),
  forall n (fx : YK11.FPState),
    tex_value_specX (fx := fx) (cp := CP) (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) TB ARXS SK n.
Proof.
intros rc ci RL SK HSTRCMP HSTRLEN HBCMP HMEMCPY HSM1 n fx.
pose proof (YGcallcf.AR_laws_x_xs (cp := CP) rsegs TB (YG0lawscf.AR_laws_ok_cf (cp := CP) rsegs TB)) as LAWSX.
apply (ExvB_Final.ex_value_holds_B_final (cp := CP) TB ARXS SK).
constructor.
- (* eh_string *) intros fx'.
  exact (ExsB_Discharge.es_eh_string (cp := CP) TB ARXS SK LAWSX PALibB.exvi_eh_head PALibB.exvi_eh_palib fx').
- (* eh_strcmp *) exact HSTRCMP.
- (* eh_strlen *) exact HSTRLEN.
- (* eh_bcmp *) exact HBCMP.
- (* eh_memcpy *) exact HMEMCPY.
- (* eh_tp *) exact ExvB_ImgFacts.exvi_eh_tp.
- (* eh_errno_B *) exact ExvB_ImgFacts.exvi_eh_errno_B.
- (* eh_got_const *) exact ExvB_ImgFacts.exvi_eh_got_const.
- (* eh_errno_own *) exact ExvB_ImgFacts.exvi_eh_errno_own.
- (* eh_blk32 *) intros ly S Hp W mem md p k HA.
  exact (ExvB_ImgFacts.exvi_eh_blk32 ly S Hp W mem md p k (proj1 HA)).
- (* eh_blk_amem8 *) intros ly S Hp W mem md p k j HA.
  exact (ExvB_ImgFacts.exvi_eh_blk_amem8 ly S Hp W mem md p k j (proj1 HA)).
- (* eh_litsh *) intros ly S Hp W mem md HA.
  exact (ExvB_ImgFacts.exvi_eh_litsh ly S Hp W mem md (proj1 HA)).
- (* eh_pst_own *) exact ExvB_ImgFacts.exvi_eh_pst_own.
- (* eh_head *) exact PALibB.exvi_eh_head.
- (* eh_uar_cell *) exact ExvB_ImgFacts.exvi_eh_uar_cell.
- (* eh_stk_hull *) intros ly S Hp W mem md x k HA.
  exact (ExvB_ImgFacts.exvi_eh_stk_hull ly S Hp W mem md x k (proj1 HA)).
- (* eh_frame_hull *) intros ly S Hp W mem md cid pos x k HA.
  exact (ExvB_ImgFacts.exvi_eh_frame_hull ly S Hp W mem md cid pos x k (proj1 HA)).
- (* eh_fpos *) intros ly S Hp W mem md cid pos HA.
  exact (ExvB_ImgFacts.exvi_eh_fpos ly S Hp W mem md cid pos (proj1 HA)).
- (* eh_frames_cid *) intros ly S Hp W mem md cid pos HA.
  exact (ExvB_ImgFacts.exvi_eh_frames_cid ly S Hp W mem md cid pos (proj1 HA)).
- (* eh_lit_own *) exact ExvB_ImgFacts.exvi_eh_lit_own.
- (* eh_sm1 *) exact HSM1.
- (* eh_sm1_pc *) exact ExvB_ImgFacts.exvi_eh_sm1_pc.
- (* eh_laws *) exact LAWSX.
- (* eh_errno *) exact PALibB.exvi_eh_errno.
- (* eh_ownlow *)
  exact (YGcallcf.ARx_owned_low_law_xs (cp := CP) rsegs TB (YG0lawscf.AR_laws_ok_cf (cp := CP) rsegs TB)).
- (* eh_smx *) intros ly S Hp W mem md cid HA.
  exact (ExvB_ImgFacts.exvi_eh_smx ly S Hp W mem md cid (proj1 HA)).
- (* eh_asfx *) exact (YGcallScf.astack_free_x_xs (cp := CP) rsegs TB).
- (* eh_fflx *) intros ly S Hp W mem md cid pos HA.
  exact (ExvB_ImgFacts.exvi_eh_fflx ly S Hp W mem md cid pos (proj1 HA)).
- (* eh_sfx *) intros ly S Hp W mem md cid pos HA.
  exact (ExvB_ImgFacts.exvi_eh_sfx ly S Hp W mem md cid pos (proj1 HA)).
- (* eh_palib *) exact PALibB.exvi_eh_palib.
- (* eh_got_uar *) exact ExvB_ImgFacts.exvi_eh_got_uar.
Qed.

(* the statement with every implicit argument and no abbreviation (TB / CP / ARXS printed out): the count of
   PI_prog_A / PL_prog_A in this output must be 0 *)
Set Printing Implicit. Unset Printing Notations.
Print ex_value_holds_B_inst.
Unset Printing Implicit. Set Printing Notations.
Print Assumptions ex_value_holds_B_inst.

(* ---- ex_value_holds_B_rows: four of the five callee premises DISCHARGED by citation of c-libc-stdio's B' rows of
   record (rows102 407ddab4a12a, in int102 c059d3a151e0), at ARXS with LAWS := YGcallcf.AR_laws_x_xs (HL := cf_head)
   and TfibSyms := YD2l.TfibB_syms:
   - HSTRCMP by lib/AU/PSstrRo.v ps_strcmp_xrom_xs_B (ARcx = ARXS, rlo / rhi := B_prog_relro_lo / _hi),
   - HSTRLEN by lib/AU/PSstrRo.v ps_strlen_xrom_xs_B,
   - HBCMP by lib/AU/PRowCmp.v pr_bcmp_xm_B_pc,
   - HMEMCPY by lib/AU/PRowCpy.v prow_asan_memcpy_xm_B;
   each row's pc (a field of the record image / CfImg_B) equals this instance's B_prog_sigma pc, closed by vm_compute.
   The ONE remaining premise is HSM1 (class-1 __asan_stack_malloc_1 frame area; owner h-hpreset-7-frameclass).
   Rule 24: proves function ex_value (image B') at the instance GIVEN HSM1 only. No numeral. ---- *)
Theorem ex_value_holds_B_rows : forall {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive} (SK : YI16.sink_head)
  (HSM1 : forall fx : YK11.FPState, YGcallMxmn.astack_malloc_realizes_xm (fx := fx) rsegs TB ARXS 1),
  forall n (fx : YK11.FPState),
    tex_value_specX (fx := fx) (cp := CP) (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) TB ARXS SK n.
Proof.
intros rc ci RL SK HSM1 n fx.
pose proof (YGcallcf.AR_laws_x_xs (cp := CP) rsegs TB (YG0lawscf.AR_laws_ok_cf (cp := CP) rsegs TB)) as LAWSX.
apply (ex_value_holds_B_inst (rc := rc) (ci := ci) (RL := RL) SK); [| | | |exact HSM1]; intros fx'.
- pose proof (PSstrRo.ps_strcmp_xrom_xs_B (fx := fx') (rc := rc) (cp := CP) TB YD2l.TfibB_syms
    B_prog_relro_lo B_prog_relro_hi) as H.
  match type of H with YGcallMxmn.astrcmp_realizes_xrom _ _ _ _ _ ?p =>
    replace (B_prog_sigma AS___wrap_strcmp) with p; [exact H | apply Z.eqb_eq; vm_compute; reflexivity] end.
- pose proof (PSstrRo.ps_strlen_xrom_xs_B (fx := fx') (rc := rc) (cp := CP) TB YD2l.TfibB_syms
    B_prog_relro_lo B_prog_relro_hi) as H.
  match type of H with YGcallMxmn.astrlen_realizes_xrom _ _ _ _ _ ?p =>
    replace (B_prog_sigma AS___wrap_strlen) with p; [exact H | apply Z.eqb_eq; vm_compute; reflexivity] end.
- pose proof (PRowCmp.pr_bcmp_xm_B_pc (fx := fx') (rc := rc) TB ARXS _ LAWSX YD2l.TfibB_syms) as H.
  match type of H with YGcallMxmn.abcmp_realizes_xm _ _ _ ?p =>
    replace (B_prog_sigma AS___wrap_bcmp) with p; [exact H | apply Z.eqb_eq; vm_compute; reflexivity] end.
- pose proof (PRowCpy.prow_asan_memcpy_xm_B (fx := fx') (rc := rc) TB ARXS _ LAWSX YD2l.TfibB_syms) as H.
  match type of H with YGcallMxmn.aintrin_realizes_xm _ _ _ _ ?p =>
    replace (B_prog_sigma AS___asan_memcpy) with p; [exact H | apply Z.eqb_eq; vm_compute; reflexivity] end.
Qed.

Set Printing Implicit. Unset Printing Notations.
Print ex_value_holds_B_rows.
Unset Printing Implicit. Set Printing Notations.
Print Assumptions ex_value_holds_B_rows.

(* ---- ex_value_holds_B_closed: the LAST premise HSM1 discharged by c-omx-alloc's class-1 row of record,
   lib/AU/FCxmCfxB.v stack_malloc1_contract_xm_cfx_B (FrameXm102 07210922d952). No premise left.
   Rule 24: proves function ex_value (image B') at the instance of record. No numeral. ---- *)
Theorem ex_value_holds_B_closed : forall {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive} (SK : YI16.sink_head)
  n (fx : YK11.FPState),
    tex_value_specX (fx := fx) (cp := CP) (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) TB ARXS SK n.
Proof.
intros rc ci RL SK n fx.
exact (ex_value_holds_B_rows (rc := rc) (ci := ci) (RL := RL) SK
  (fun fx' => FCxmCfxB.stack_malloc1_contract_xm_cfx_B fx') n fx).
Qed.

Set Printing Implicit. Unset Printing Notations.
Print ex_value_holds_B_closed.
Unset Printing Implicit. Set Printing Notations.
Print Assumptions ex_value_holds_B_closed.
