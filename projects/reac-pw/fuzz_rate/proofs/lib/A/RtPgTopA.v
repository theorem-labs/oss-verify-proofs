(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; addresses from the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3): THE WHOLE RUN OF LLVMFuzzerTestOneInput AT IMAGE
   A, with every walk piece and every segment statement given by its walk.

     rate_lib_x_A_close : rt_lib_contract_x Img0.rsegs B ameter_triv K XL XL 0x9b6e0 0x9cb68 A_LLVMF RA_LLVMF ...

   It is lib/A/RtPgTopI.v rate_lib_x_A with these statements given by their walks (each piece at the trivial meter,
   whose laws are YCbp.ameter_triv_laws, and the kernel's AR laws YG0d.AR_laws_ok):
     rs_piece_W3b_hdr_stmt, rs_piece_W3b_b7_stmt      lib/A/RtPgW3b.v rs_piece_W3b_hdr, rs_piece_W3b_b7
     rs_piece_W3b_pre_stmt                            lib/A/RtPgW3bPre.v rs_piece_W3b_pre
     rs_piece_W4_sel_stmt                             lib/A/RtPgPropSelB.v pa_piece_sel
     rs_piece_W4_int7_stmt                            lib/A/RtPgPropIntB.v pa_piece_int7 (AMEMSET)
     rs_piece_W4_key_stmt                             lib/A/RtPgPropKeyB.v pa_piece_key
     rs_piece_W4_latch_stmt                           lib/A/RtPgPropSel.v pa_piece_latch
     rs_piece_W5_close_stmt                           lib/A/RtPgW5CloseP.v w5_piece_close
     rs_piece_W5_int_stmt                             lib/A/RtPgW5IntP.v w5_piece_int (AMEMSET)
     rs_piece_W6a_disp_stmt, rs_piece_W6a_cases_stmt  lib/A/RtPgW6a.v w6_disp, w6_cases (AMEMSET)
     rs_piece_W11a_outer_stmt                         lib/A/RtPgScanOuter.v rk_outer_A
     rs_piece_W11a_inner_stmt                         lib/A/RtPgScanInner.v rk_inner_A
     rs_piece_W11a_setup_stmt                         lib/A/RtPgScanSetup.v rk_setup_A
     rs_piece_W5_open_stmt                            lib/A/RtPgW5OpenP.v w5_piece_open
     rs_piece_W11a_head_stmt                          lib/A/RtPgScanHead.v rk_head_A (AMEMCPY; the parse by
                                                      lib/A/RtPgParse.v rt_parse_A)
     rs_piece_W11b_checks_stmt                        lib/A/RtPgM02Chk.v rt_m02_checks_A
     rs_piece_W3a_stmt                                lib/A/RtPgW3a.v rt_A_piece_W3a (AMEMSET)
     rs_piece_W6c_stmt                                lib/A/RtPgW6c.v w6c_piece (AMEMCPY, AMEMSET)
     rs_piece_W7a_stmt                                lib/A/RtPgEnt0.v rt7_W7a (ASTRLEN, AMEMCPY)
     rs_piece_W7b_stmt                                lib/A/RtPgW7bPiece.v w7_piece (ASTRLEN, AMEMCPY)
     rs_piece_W6b_stmt                                lib/A/RtPgW6bTop.v w6b_piece (AMEMCPY, ASTRLEN)
     rs_piece_W8_stmt                                 lib/A/RtPgW8Top.v rs_piece_W8 (AMEMCPY, AMEMSET)
     rs_piece_W11b_key_stmt                           lib/A/RtPgM02Key.v rt_m02_key_A (HGOT, HSC, ASTRCMP)
     rs_piece_W14_csv_stmt (every float state)        lib/A/RtPgW14Csv.v rt_w14_csv_A (AMEMSET, CCSV, IMGF; drivable_csv
                                                      by lib/A/RtPgDcsv.v rt_drivable_csv_A with ASM1, ASNP, HPCS1,
                                                      HPCMC)
     rs_piece_W13_stmt                                lib/A/RtPgDec.v rt_dec_turn_A (HGOT, HSC, ASTRCMP)
     rs_piece_W10_post_stmt                           lib/A/RtPgPost.v w10_post
     rs_piece_W10_req_stmt                            lib/A/RtPgPostReq.v w10_req
     rs_piece_W10_corr_stmt                           lib/A/RtPgPostCorr.v w10_corr
     rs_piece_W14_asked_stmt                          lib/A/RtPgW14Ask.v rt_w14_asked_A
     rs_piece_W14_tail_stmt                           lib/A/RtPgW14Tail.v rt_w14_tail_A (refuse_code and check_code by
                                                      lib/A/RtPgRefuse.v rt_refuse_code_A, RtPgCheckCode.v
                                                      rt_check_code_A)
     rh_S_C23_stmt (malloc(pod))                      lib/A/RtPgPostMal.v rt_A_S_C23 (AMALLOC, HPCM, HLIVE, HTRACE_C23)
     rh_S_C46_stmt (malloc(buf))                      lib/A/RtPgW14Mal.v rt_w14_S_C46_A (AMALLOC, HPCM, HLIVE, HTRACE_C46)
     S_E01                                            lib/A/RtPgE01.v rt_S_E01 (HAPI, ML, SMP, ASM3, HPCS3, AMALLOC, HPCM,
                                                      HTRACE_E01, HGOT, HSC, HGOTU, HUAR, HEMPTY, the static law, the
                                                      read-only
                                                      range in the image)
     S_X01                                            lib/A/RtPgX01.v rtx_S_X01 (ML, HAPI, AFREE, FFL, ASHF5, HFREE,
                                                      HTRACE; ASHF5 is lib/Reusable/SetShadowDef.v's
                                                      aset_shadow_realizes at 0x54828)
   The Section hypotheses left are the runtime, callee and symbol laws the walks take (each a statement of another
   lane: a runtime walk, a callee walk, the start-up's symbol record, the image's read-only facts) and the relocated
   frame's facts (the sink's overflow head and laws, the harness constants, the lib shape's leaf law). Proves no
   function of its own (kind: merge). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import Img0 RtPgBase RtPgCSpec RtPgImgA RtPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgMainL RtPgTop RtPgTopI.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Rt Require Import StrlenDef.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgW3b RtPgW3bPre.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgPropSelB RtPgPropIntB RtPgPropKeyB RtPgPropSel.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgW5CloseP RtPgW5IntP RtPgW5OpenP RtPgW6a.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgScanHead RtPgScanOuter RtPgScanInner RtPgScanSetup.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgM02Chk RtPgPostCorr RtPgW14Ask RtPgW14Tail RtPgW7bPiece.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgPostMal RtPgW14Mal RtPgX01.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgW3a RtPgPost RtPgPostReq.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgW6c RtPgEnt0 RtPgE01D RtPgE01.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgW8Top RtPgDec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgSiteA RtPgSatSeg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgW6bTop RtPgM02Key RtPgW14Csv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgParse RtPgRefuse RtPgCheckCode.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0t.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgDcsvDefs RtPgDcsv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Rt Require Import SnprintfRateDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* rh_hcx's projections, with the segments implicit in this file *)
Local Arguments h_regs {segs} _.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
(* the sink's overflow head of the relocated frame (AE2k.tfib_sink_head) lies above the read-only data *)
Hypothesis HOFL : 0x9cb68 <= YI16.sk_ofl_head.
Variable B : asyms.
(* the image's read-only facts at the symbols (RtPgSiteA.rate_A_img_facts: the static strings, cells and tables are
   unowned image bytes) and the owned read-only bytes pinned as AR constant cells (RtPgBase.rt_rom_pinned); with them
   RtPgSatSeg.rate_A_static_full gives the chaining's static law *)
Hypothesis IMGF : RtPgSiteA.rate_A_img_facts rsegs B.
Hypothesis PIN : rt_rom_pinned rsegs B.
Lemma rate_static_A : rh_static_law rsegs B 0x9b6e0 0x9cb68.
Proof. intros ly S W mem md HAR HRO. exact (RtPgSatSeg.rate_A_static_full B IMGF PIN ly S W mem md HAR HRO). Qed.
Variable K : asink_syms.
Variable XL : Z -> Z.
Variables A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
(* the harness constants (the relocated frame's ACfn; by computation) *)
Hypothesis HA : A_LLVMF = RS_ENTRY.
Hypothesis HEV : RS_EV <= EV_LIB.
Hypothesis HSTK : RS_RSZ + 32 + ASTACK <= LLVMF_STK.
Hypothesis HLIVE : Layout.PP_SIZE + 5440 + 23 <= LIVE_LIB.
(* the core's sink laws at the symbols (the relocated frame's AD1u.tfib_AIL) *)
Hypothesis AIL : asink_img_laws rsegs B K.
(* the lib shape's one-leaf law (RtPgLib.rate_lib_x_all_stmt's first premise) *)
Hypothesis LEAF : forall pl fs (Kl : lleaf -> TSet), LIBK pl fs Kl = Kl (LL 0 fs []).

(* the empty input's address (the relocated frame's ACfn.A_EMPTY) lies in low application memory *)
Hypothesis HEMPTY : 0 < A_EMPTY < kLowMemEnd.
(* ---------------- the runtime and symbol laws the proved statements take ---------------- *)
(* __asan_memset (0x51cfc) under the journal (the relocated frame's AE2r), at every float state *)
Hypothesis AMEMSET : forall fy : YK11.FPState, aintrin_realizes (fx := fy) rsegs B OSet 0x51cfc.
(* __asan_memcpy (0x51860) under the journal (the relocated frame's AE2q), at every float state *)
Hypothesis AMEMCPY : forall fy : YK11.FPState, aintrin_realizes (fx := fy) rsegs B OCpy 0x51860.
(* the strlen wrapper __interceptor_trampoline_strlen (0x42194; the runtime walk's StrlenDef form) *)
Hypothesis ASTRLEN : astrlen_realizes rsegs B 0x42194.
(* the strcmp wrapper (0x4219c; the runtime walk's AStrcmpDef form) at every float state *)
Hypothesis ASTRCMP : forall fy : YK11.FPState, AStrcmpDef.astrcmp_realizes (fx := fy) rsegs B 0x4219c.
(* check_csv (0x838e0, class-2 frame, closed_list) at every float state (the callee walk) *)
Hypothesis CCSV : forall fy : YK11.FPState,
  rt_check_csv_specX (fx := fy) rsegs B ameter_triv 0x838e0 2 RtPgSiteA.T_csv_STK 0x21520.
(* the allocator: its model laws, its environment, malloc and free at every float state, the malloc wrapper's
   entry 0x52bb4, the side-stack frame's flag pointer, and __asan_set_shadow_f5 (0x54828) at every float state *)
Hypothesis ML : model_laws (as_universe B).
Hypothesis HAPI : api_env rsegs B.
Hypothesis AMALLOC : forall fx' : YK11.FPState, amalloc_realizes (fx := fx') rsegs B.
Hypothesis AFREE : forall fx' : YK11.FPState, afree_realizes (fx := fx') rsegs B.
Hypothesis HPCM : pc_wrap_malloc (as_code B) = 0x52bb4.
Hypothesis HFREE : pc_wrap_free (as_code B) = RtPgX01.RTX_FREE.
Hypothesis FFL : frame_flag_lawP rsegs B.
Hypothesis ASHF5 : forall fx' : YK11.FPState, aset_shadow_realizes (fx := fx') rsegs B 0x54828 0xf5.
(* the frame for locals: __asan_stack_malloc_3 (0x3d2c8) and the side stack's progress law; the runtime's shadow-offset
   and use-after-return cells and their GOT entries *)
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASM3 : astack_malloc_realizes rsegs B 3.
Hypothesis HPCS3 : pc_stack_malloc (as_code B) 3 = 0x3d2c8.
Hypothesis HGOT : as_got_shadow B = 0x9be70.
Hypothesis HSC : as_shadow_cell B = 0xa4c38.
Hypothesis HGOTU : as_got_uar B = 0x9bec8.
Hypothesis HUAR : as_uar_cell B = 0xa4c40.
(* drivable_csv's own frame and callees: __asan_stack_malloc_1 (0x3cf9c) at every float state and its code entry,
   __asan_memcpy's code entry, and the snprintf wrapper __interceptor_trampoline_snprintf (0x421d4; the runtime walk's
   SnprintfRateDef form) at every float state *)
Hypothesis ASM1 : forall fy : YK11.FPState, astack_malloc_realizes (fx := fy) rsegs B 1.
Hypothesis HPCS1 : pc_stack_malloc (as_code B) 1 = 0x3cf9c.
Hypothesis HPCMC : pc_asan_memcpy (as_code B) = 0x51860.
Hypothesis ASNP : forall fy : YK11.FPState, rate_snprintf_sd_realizes (fx := fy) rsegs B 0x421d4.
(* the allocation traces of malloc(pp), malloc(pod), malloc(buf) and of the three frees are in the allocation
   universe *)
Hypothesis HTRACE_E01 : RtPgE01D.e01_trace_stmt B RA_LLVMF.
Hypothesis HTRACE_C23 : forall (regsT : bvmap 5 word) (hx : rh_hcx rsegs),
  raZ (h_regs hx) = RA_LLVMF -> raZ regsT = RS_C3 ->
  In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT (RtPgPostMal.rt_c23_ch hx)) (as_universe B).
Hypothesis HTRACE_C46 : forall (regsT : bvmap 5 word) (hx : rh_hcx rsegs),
  raZ (h_regs hx) = RA_LLVMF -> raZ regsT = RS_C6 ->
  In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT (RtPgW14Mal.w14m_ch hx)) (as_universe B).
Hypothesis HTRACE : forall c,
  In c [[RtPgX01.RTX_RA1]; [RtPgX01.RTX_RA1; RA_LLVMF]; [RtPgX01.RTX_RA2]; [RtPgX01.RTX_RA2; RA_LLVMF];
        [RtPgX01.RTX_RA3]; [RtPgX01.RTX_RA3; RA_LLVMF]] ->
  In (firstn kUnwindMax (pc_free_ra0 (as_code B) :: flat_map (fun r => if r =? pc_free_ra0 (as_code B) then [] else [r]) c))
  (as_universe B).

(* a proved statement's own premises, from the hypotheses above *)
Local Ltac rt_kit0 := first
  [ exact ameter_triv_laws | exact ameter_triv_fs_laws | apply AR_laws_ok | apply astack_free_law_ok
  | exact AMEMSET | exact (AMEMSET _) | exact AMEMCPY | exact (AMEMCPY _) | exact ASTRLEN
  | exact ML | exact IMGF | exact CCSV | exact ASM1 | exact HPCS1 | exact HPCMC | exact ASNP
  | exact HAPI
  | exact FFL | exact SMP | exact ASM3 | exact HPCS3 | exact HGOT | exact HSC | exact HGOTU | exact HUAR
  | exact HEMPTY | exact rate_static_A | exact rate_relro_A | exact HTRACE_E01
  | exact HPCM | exact HFREE | exact HTRACE | exact HTRACE_C23 | exact HTRACE_C46
  | exact ASTRCMP | exact (ASTRCMP _)
  | exact AMALLOC | exact (AMALLOC _) | (intros fx'; exact (AFREE fx')) | (intros fx'; exact (ASHF5 fx'))
  | (unfold RS_RSZ in HSTK; lia) | (unfold RS_EV in HEV; lia) | lia ].
(* ... and the callee contracts the pieces take, from the callee walks: reac_rate_prop_parse (RtPgParse.rt_parse_A),
   reac_rate_refuse_code (RtPgRefuse.rt_refuse_code_A), check_code (RtPgCheckCode.rt_check_code_A) and
   reac_rate_drivable_csv (RtPgDcsv.rt_drivable_csv_A, its runtime conjunction RtPgDcsvDefs.dc_rt), the last three
   at every float state *)
Local Ltac rt_kit := first
  [ rt_kit0
  | (apply RtPgParse.rt_parse_A; rt_kit0)
  | (intros fy; apply RtPgRefuse.rt_refuse_code_A; rt_kit0)
  | (intros fy; apply RtPgCheckCode.rt_check_code_A; rt_kit0)
  | (intros fy; apply RtPgDcsv.rt_drivable_csv_A; unfold RtPgDcsvDefs.dc_rt;
     repeat match goal with |- _ /\ _ => split end; rt_kit0) ].

Theorem rate_lib_x_A_close : rt_lib_contract_x rsegs B ameter_triv K XL XL 0x9b6e0 0x9cb68
  A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
eapply (rate_lib_x_A HOFL B rate_static_A).
all: first
  [ exact (RtPgW3b.rs_piece_W3b_hdr B ameter_triv)
  | exact (RtPgW3b.rs_piece_W3b_b7 B ameter_triv)
  | exact (RtPgW3bPre.rs_piece_W3b_pre B ameter_triv)
  | (apply RtPgPropSelB.pa_piece_sel; rt_kit)
  | (apply RtPgPropIntB.pa_piece_int7; rt_kit)
  | (apply RtPgPropKeyB.pa_piece_key; rt_kit)
  | (apply RtPgPropSel.pa_piece_latch; rt_kit)
  | (apply RtPgW5CloseP.w5_piece_close; rt_kit)
  | (apply RtPgW5IntP.w5_piece_int; rt_kit)
  | (apply RtPgW6a.w6_disp; rt_kit)
  | (apply RtPgW6a.w6_cases; rt_kit)
  | exact (RtPgScanOuter.rk_outer_A B ameter_triv)
  | exact (RtPgScanInner.rk_inner_A B ameter_triv)
  | exact (RtPgScanSetup.rk_setup_A B ameter_triv)
  | (apply RtPgM02Chk.rt_m02_checks_A; rt_kit)
  | (apply RtPgW5OpenP.w5_piece_open; rt_kit)
  | (apply RtPgScanHead.rk_head_A; rt_kit)
  | exact (RtPgPostCorr.w10_corr B ameter_triv)
  | (apply RtPgW7bPiece.w7_piece; rt_kit)
  | (apply RtPgW3a.rt_A_piece_W3a; rt_kit)
  | exact (RtPgPost.w10_post B ameter_triv)
  | exact (RtPgPostReq.w10_req B ameter_triv)
  | (apply RtPgW14Ask.rt_w14_asked_A; rt_kit)
  | (apply RtPgW14Tail.rt_w14_tail_A; rt_kit)
  | (eapply RtPgPostMal.rt_A_S_C23; rt_kit)
  | (eapply RtPgW14Mal.rt_w14_S_C46_A; rt_kit)
  | (eapply RtPgX01.rtx_S_X01; rt_kit)
  | (apply RtPgW6c.w6c_piece; rt_kit)
  | (apply RtPgEnt0.rt7_W7a; rt_kit)
  | (eapply RtPgE01.rt_S_E01; rt_kit)
  | (apply RtPgW8Top.rs_piece_W8; rt_kit)
  | (apply RtPgDec.rt_dec_turn_A; rt_kit)
  | (apply RtPgW6bTop.w6b_piece; rt_kit)
  | (apply RtPgM02Key.rt_m02_key_A; rt_kit)
  | (intros fx'; apply RtPgW14Csv.rt_w14_csv_A; rt_kit)
  | eassumption ].
Qed.
End i.

Print Assumptions rate_lib_x_A_close.
