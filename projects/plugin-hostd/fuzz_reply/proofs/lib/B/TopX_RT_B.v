(* The image-B twin of lib/A/TopX_RT3.v's topx_ABCMP (a working branch): image B's bcmp contract
   AT B's top_x instance
     ARX_B := lib/B/W_LLVMFuzzerTestOneInput_top_x.v:154-155's ARX, restated VERBATIM
              (fun ly S Hp W mem md => ARcf (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = []),
   in the form lib/B/W_check_shape_event.v:83's `Hypothesis ABCMP : abcmp_realizes_x SEGS B ARx (SIGMA WS_bcmp)` takes:
     topx_ABCMP_B : abcmp_realizes_x segs TfibB ARX_B (SIGMA WS_bcmp)        (W_sites_x.v abcmp_realizes_x)
   The proof is the generic one: lib/B/Rt/Bcmp.v bcmp_site_realizes_x over YE2y.icpt_laws_x and TfibSyms
   (YD2l.TfibB_syms); its IcptRealizesX.abcmp_realizes_x at tfibsegs is W_sites_x's at pa_segs PB_fr by conversion
   (Rt/Bcmp.v bcmp_id_segs).
   icpt_laws_x at ARX_B, field by field, WITHOUT lib/Rt/RTx.v (not on this base): ARX_B_laws is top_x.v:156-160's
   ARX_laws proof verbatim (W_journal_x.AR_laws_x_and_hp over YGcallcf.AR_laws_x_cf / YG0lawscf.AR_laws_ok_cf,
   hl := cf_head); ilx_frame / ilx_stack / ilx_zshadow / ilx_const are its alx_frame / alx_stack / alx_zshadow /
   alx_const_cells (YE2y.v's field texts are YCbqG.v's law texts verbatim), and ilx_layout is ARcf's amc_layout.
   No premise is left: every lemma here is closed. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_sites_x.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YE2y.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Rt.Bcmp.
Import ListNotations.
Open Scope Z_scope.

Module IX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YE2y.
Module BC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Rt.Bcmp.

Section topx_rt_b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).

(* top_x.v:154-155's ARX, verbatim *)
Definition ARX_B : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop :=
  fun ly S Hp W mem md => ARcf (ci := CfImg_B) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [].
(* top_x.v:156-160's ARX_laws, verbatim *)
Lemma ARX_B_laws : AR_laws_x segs TfibB ARX_B (@cf_head CfParams_reply).
Proof.
  unfold ARX_B. apply AR_laws_x_and_hp.
  exact (AR_laws_x_cf (cp := CfParams_reply) segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)).
Qed.

(* the interceptor laws at ARX_B: four fields from ARX_B_laws, layout from ARcf's amc_layout *)
Lemma icpt_laws_ARX_B : IX.icpt_laws_x TfibB ARX_B.
Proof.
  constructor.
  - (* QMm W0': YE2y's frame field keeps ARx_frame_law's text before W0' (no kept-bytes premise), so it is ARcf's own
       frame law (alc_frame) with Hp = [] unchanged, as TopX_RT_lock's rt_laws_ARX does *)
    intros ly S Hp W mem md mem' md' (HAR & Hp0) H1 H2 H3 H4 H5 H6.
    exact (conj (YG0dcf.alc_frame _ _ (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB) ly S Hp W mem md mem' md' HAR H1 H2 H3 H4 H5 H6) Hp0).
  - exact (alx_stack _ _ _ ARX_B_laws).
  - exact (alx_zshadow _ _ _ ARX_B_laws).
  - exact (alx_const_cells _ _ _ ARX_B_laws).
  - intros ly S Hp W mem md (HAR & _). exact (amc_layout _ _ _ _ _ (proj1 HAR)).
Qed.

Lemma topx_ABCMP_B : abcmp_realizes_x segs TfibB ARX_B (SIGMA WS_bcmp).
Proof. exact (BC.bcmp_site_realizes_x TfibB ARX_B icpt_laws_ARX_B TfibB_syms). Qed.

End topx_rt_b.
