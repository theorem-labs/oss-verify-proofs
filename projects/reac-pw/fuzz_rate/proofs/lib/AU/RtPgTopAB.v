(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgTopA.v at af0538adbf24 for image B
   (fuzz_rate.asan-ubsan): rate_lib_x_A_close's discharge of the pieces by their walks, at image B's pieces
   (lib/AU/RtPgSegB.v), image B's walk lanes (lib/AU) and image B's runtime entries, cells and traces; the static law
   from image B's read-only facts by lib/AU/RtPgStaticB.v. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses from the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): THE WHOLE RUN OF LLVMFuzzerTestOneInput
   (0x8076c) AT IMAGE B, with each walk piece and segment statement that has a walk given by it.

     rate_lib_x_B : rt_lib_contract_x Img0.rsegs B ameter_triv K XL XL 0x9b9e0 0x9ce68 A_LLVMF RA_LLVMF ...

   It is lib/AU/RtPgTopIB.v rate_lib_x_B_pieces with these statements given by their walks (each piece at the trivial
   meter, whose laws are YCbp.ameter_triv_laws, and the kernel's AR laws YG0d.AR_laws_ok):
     rsb_piece_W3a_stmt                 lib/AU/RtPgW3aB.v rt_B_piece_W3a (AMEMSET)
     rsb_piece_W3b_hdr_stmt / _pre      lib/AU/RtPgW3bB.v rsb_piece_W3b_hdr, RtPgW3bPreB.v rsb_piece_W3b_pre
     rsb_piece_W3b_b7_stmt              lib/AU/RtPgW3aB7.v rt_B_piece_W3b_b7
     rsb_piece_W4_sel_stmt              lib/AU/RtPgPropBSel.v pab_piece_sel
     rsb_piece_W4_int7_stmt             lib/AU/RtPgPropB.v pab_piece_int7_B (AMEMSET, AMEMCPY, HGOT, HSC; pod_write_ent
                                        by lib/AU/PweRun.v pod_write_ent_B)
     rsb_piece_W4_key_stmt              lib/AU/RtPgPropBKey.v pab_piece_key
     rsb_piece_W4_latch_stmt            lib/AU/RtPgPropBLatch.v pab_piece_latch
     rsb_piece_W5_int_stmt              lib/AU/RtPgW5IntPB.v w5b_piece_int (AMEMSET; pod_write_ent by lib/AU/PweRun.v
                                        pod_write_ent_B with AMEMCPY, AMEMSET, HGOT, HSC)
     rsb_piece_W5_open_stmt             lib/AU/RtPgW5OpenPB.v w5b_piece_open
     rsb_piece_W5_close_stmt            lib/AU/RtPgW5ClosePB.v w5b_piece_close
     rsb_piece_W6a_disp_stmt / _cases   lib/AU/RtPgW6aB.v w6b_disp (AMEMSET), w6b_cases
     rsb_piece_W6b_stmt                 lib/AU/RtPgW6bTopB.v w6bb_piece (AMEMCPY, ASTRLEN)
     rsb_piece_W6c_stmt                 lib/AU/RtPgW6cB.v w6cb_piece (AMEMCPY, AMEMSET)
     rsb_piece_W7a_stmt                 lib/AU/RtPgEnt0B.v rt7b_W7a (ASTRLEN in lib/AU/RtPgW7bCallB.v's form, AMEMCPY)
     rsb_piece_W7b_stmt                 lib/AU/RtPgW7bPieceB.v w7b_piece (ASTRLEN in that form, AMEMCPY)
     rsb_piece_W8_stmt                  lib/AU/RtPgBW8Top.v rsb_piece_W8 (AMEMCPY, AMEMSET, HGOT, HSC)
     rsb_piece_W10_post / _corr / _req  lib/AU/RtPgPostB.v wb10_post, RtPgPostCorrB.v wb10_corr, RtPgPostReqB.v wb10_req
     rhb_S_C23_stmt (malloc(pod))       lib/AU/RtPgPostMalB.v rt_B_S_C23 (AMALLOC, HAPI, ML, HPCM, HTRACE_C23)
     rsb_piece_W11a_head_stmt           lib/AU/RtPgScanHeadB.v rkb_head_B (AMEMCPY; the parse by lib/AU/RtPgParseB.v
                                        rt_parse_B with HGOT, HSC, ASTRCMP)
     rsb_piece_W11a_setup / _outer /   lib/AU/RtPgScanSetupB.v rkb_setup_B, RtPgScanOuterB.v rkb_outer_B,
       _inner                          RtPgScanInnerB.v rkb_inner_B
     rsb_piece_W11b_checks_stmt         lib/AU/RtPgM02ChkB.v rt_m02_checks_B
     rsb_piece_W11b_key_stmt            lib/AU/RtPgM02KeyB.v rt_m02_key_B (ASTRCMP, HGOT, HSC; the soft-float callees by
                                        lib/CJ/RL/I/InstB.v at image B's symbol map)
     rsb_piece_W13_stmt                 lib/AU/RtPgDecB.v rt_dec_turn_B (HGOT, HSC, ASTRCMP)
     rsb_piece_W14_asked_stmt           lib/AU/RtPgW14AskB.v rt_w14_asked_B
     rsb_piece_W14_tail_stmt            lib/AU/RtPgW14TailB.v rt_w14_tail_B (refuse_code by lib/AU/RtPgRefuseB.v
                                        rt_refuse_code_B, check_code by lib/AU/RtPgCheckCode.v rt_check_code_B)
     rhb_S_C46_stmt (malloc(buf))       lib/AU/RtPgW14MalB.v rt_w14_S_C46_B (AMALLOC, HAPI, ML, HPCM, HTRACE_C46)
     rsb_piece_W14_csv_stmt (every fx)  lib/AU/RtPgW14CsvB.v rt_w14_csv_B (AMEMSET, IMGF; drivable_csv by
                                        lib/AU/RtPgDcsvB.v rt_drivable_csv_B with ASM1, ASNP, HPCS1, HPCMC, AMEMCPY,
                                        IMGF; check_csv by lib/AU/RtPgCcsvB.v rt_check_csv_B with ASM2, HPCS2, ABCMP,
                                        HAPI, ML, SMP, FFL, HGOT, HSC, HGOTU, HUAR, IMGF)
     S_E01                              lib/AU/RtPgE01B.v rtb_S_E01 (HAPI, ML, SMP, ASM4, HPCS4, AMALLOC, HPCM,
                                        HTRACE_E01, HGOT, HSC, HGOTU, HUAR, HEMPTY, the static law, the read-only
                                        range in the image)
     S_X01                              lib/AU/RtPgX01B.v rtxb_S_X01 (ML, HAPI, AFREE, FFL, ASHF5, HFREE, HTRACE)
     rhb_static_law                     lib/AU/RtPgStaticB.v rate_B_static_full (IMGF, PIN)
   The strlen wrapper's law is stated once, as lib/A/Rt/StrlenDef.v's image-parametric astrlen_realizes at image B's
   entry 0x421ec (the definition only; no image-A constant is used); W7a / W7b state it in lib/AU/RtPgW7bCallB.v's
   word-for-word copy w7b_astrlen_realizes, which rate_B_strlen_w7b gives by unfolding.
   Every walk piece and segment statement is given by its walk. The Section hypotheses left are
   the runtime, callee and symbol laws the walks take (each a statement of another lane: a runtime
   walk, a callee walk, the start-up's symbol record, the image's read-only facts) and the frame's facts (the sink's
   overflow head and laws, the harness constants, the lib shape's leaf law). Proves no function of its own (kind:
   merge). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import SetShadowDef YG0t.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Rt Require Import StrlenDef.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import Img0 RtPgImgB RtPgSegB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgMainLB RtPgTopB RtPgTopIB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgSiteB RtPgStaticB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgW7bCallB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgW3aB RtPgW3aB7 RtPgW3bB RtPgW3bPreB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgPropB RtPgW5ClosePB RtPgW5OpenPB RtPgW5IntPB PweRun.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgW6aB RtPgW6bTopB RtPgW6cB RtPgEnt0B RtPgW7bPieceB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgBW8Top RtPgPostB RtPgPostCorrB RtPgPostReqB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgPostMalB RtPgW14MalB RtPgE01DB RtPgE01B RtPgX01B.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgScanHeadB RtPgScanSetupB RtPgScanOuterB RtPgScanInnerB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgM02ChkB RtPgM02KeyB RtPgDecB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgW14AskB RtPgW14TailB RtPgW14CsvB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgRefuseB RtPgParseB RtPgDcsvDefsB RtPgDcsvB RtPgCcsvB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgCheckCode.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.I Require InstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Module CCB := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.RtPgCheckCode.

(* rhb_hcx's projections, with the segments implicit in this file *)
Local Arguments h_regs {segs} _.

(* The strlen wrapper's law in the form W7a / W7b state it (lib/AU/RtPgW7bCallB.v's copy, whose read-only premise
   w7b_aro_unowned is lib/A/Rt/WrapRo.v's aro_unowned word for word), from lib/A/Rt/StrlenDef.v's. *)
Lemma rate_B_strlen_w7b : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms),
  astrlen_realizes rsegs B 0x421ec -> RtPgW7bCallB.w7b_astrlen_realizes rsegs B RtPgW7bBaseB.W7B_STRLEN.
Proof.
intros fx rc B H. unfold RtPgW7bCallB.w7b_astrlen_realizes, RtPgW7bCallB.w7b_aro_unowned, RtPgW7bBaseB.W7B_STRLEN.
unfold astrlen_realizes, WrapRo.aro_unowned in H. exact H.
Qed.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
(* the sink's overflow head lies above the read-only data *)
Hypothesis HOFL : 0x9ce68 <= YI16.sk_ofl_head.
Variable B : asyms.
(* the image's read-only facts at the symbols (RtPgSiteB.rate_B_img_facts: the static strings, cells and tables are
   unowned image bytes) and the owned read-only bytes pinned as AR constant cells (RtPgBase.rt_rom_pinned); with them
   RtPgStaticB.rate_B_static_full gives the chaining's static law *)
Hypothesis IMGF : rate_B_img_facts rsegs B.
Hypothesis PIN : rt_rom_pinned rsegs B.
Lemma rate_static_B : rhb_static_law rsegs B 0x9b9e0 0x9ce68.
Proof. exact (rate_B_static_full B IMGF PIN). Qed.
Variable K : asink_syms.
Variable XL : Z -> Z.
Variables A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
(* the harness constants *)
Hypothesis HA : A_LLVMF = RSB_ENTRY.
Hypothesis HEV : RSB_EV <= EV_LIB.
Hypothesis HSTK : RSB_RSZ + 32 + ASTACK <= LLVMF_STK.
Hypothesis HLIVE : Layout.PP_SIZE + 5440 + 23 <= LIVE_LIB.
(* the core's sink laws at the symbols *)
Hypothesis AIL : asink_img_laws rsegs B K.
(* the lib shape's one-leaf law *)
Hypothesis LEAF : forall pl fs (Kl : lleaf -> TSet), LIBK pl fs Kl = Kl (LL 0 fs []).
(* the empty input's address lies in low application memory *)
Hypothesis HEMPTY : 0 < A_EMPTY < kLowMemEnd.

(* ---------------- the runtime and symbol laws the proved statements take ---------------- *)
(* __asan_memset (0x51d54) and __asan_memcpy (0x518b8) under the journal, at every float state *)
Hypothesis AMEMSET : forall fy : YK11.FPState, aintrin_realizes (fx := fy) rsegs B OSet 0x51d54.
Hypothesis AMEMCPY : forall fy : YK11.FPState, aintrin_realizes (fx := fy) rsegs B OCpy 0x518b8.
(* the strlen wrapper (0x421ec; lib/A/Rt/StrlenDef.v's parametric form) *)
Hypothesis ASTRLEN : astrlen_realizes rsegs B 0x421ec.
(* the strcmp wrapper (0x421f4; lib/Reusable/AStrcmpDef.v's form) at every float state *)
Hypothesis ASTRCMP : forall fy : YK11.FPState, AStrcmpDef.astrcmp_realizes (fx := fy) rsegs B 0x421f4.
(* check_csv's own frame and callee: __asan_stack_malloc_2 (0x3d164) at every float state and its code entry, and
   the bcmp wrapper (0x42200; YG0d.abcmp_realizes) at every float state *)
Hypothesis ASM2 : forall fy : YK11.FPState, astack_malloc_realizes (fx := fy) rsegs B 2.
Hypothesis HPCS2 : pc_stack_malloc (as_code B) 2 = 0x3d164.
Hypothesis ABCMP : forall fy : YK11.FPState, abcmp_realizes (fx := fy) rsegs B 0x42200.
(* reac_rate_drivable_csv's own frame and callees: __asan_stack_malloc_1 (0x3cfd4) at every float state and its
   code entry, __asan_memcpy's code entry, and the snprintf wrapper __interceptor_trampoline_snprintf (0x4222c;
   lib/AU/RtPgDcsvDefsB.v's form) at every float state *)
Hypothesis ASM1 : forall fy : YK11.FPState, astack_malloc_realizes (fx := fy) rsegs B 1.
Hypothesis HPCS1 : pc_stack_malloc (as_code B) 1 = 0x3cfd4.
Hypothesis HPCMC : pc_asan_memcpy (as_code B) = 0x518b8.
Hypothesis ASNP : forall fy : YK11.FPState, RtPgDcsvDefsB.rate_snprintf_sd_realizes (fx := fy) rsegs B 0x4222c.
(* the allocator: its model laws, its environment, malloc and free at every float state, the malloc and free
   trampolines' entries 0x52c0c / 0x52c08, the side-stack frame's flag pointer, and __asan_set_shadow_f5 (0x54880) at
   every float state *)
Hypothesis ML : model_laws (as_universe B).
Hypothesis HAPI : api_env rsegs B.
Hypothesis AMALLOC : forall fx' : YK11.FPState, amalloc_realizes (fx := fx') rsegs B.
Hypothesis AFREE : forall fx' : YK11.FPState, afree_realizes (fx := fx') rsegs B.
Hypothesis HPCM : pc_wrap_malloc (as_code B) = 0x52c0c.
Hypothesis HFREE : pc_wrap_free (as_code B) = 0x52c08.
Hypothesis FFL : frame_flag_lawP rsegs B.
Hypothesis ASHF5 : forall fx' : YK11.FPState, aset_shadow_realizes (fx := fx') rsegs B 0x54880 0xf5.
(* the frame for locals: __asan_stack_malloc_4 (0x3d300) and the side stack's progress law; the runtime's
   shadow-offset and use-after-return cells and their GOT entries *)
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASM4 : astack_malloc_realizes rsegs B 4.
Hypothesis HPCS4 : pc_stack_malloc (as_code B) 4 = 0x3d300.
Hypothesis HGOT : as_got_shadow B = 0x9c170.
Hypothesis HSC : as_shadow_cell B = 0xa4f38.
Hypothesis HGOTU : as_got_uar B = 0x9c1c8.
Hypothesis HUAR : as_uar_cell B = 0xa4f40.
(* the allocation traces of malloc(pp), malloc(pod), malloc(buf) and of the three frees are in the allocation
   universe *)
Hypothesis HTRACE_E01 : RtPgE01DB.e01b_trace_stmt B RA_LLVMF.
Hypothesis HTRACE_C23 : forall (regsT : bvmap 5 word) (hx : rhb_hcx rsegs),
  raZ (h_regs hx) = RA_LLVMF -> raZ regsT = RSB_C3 ->
  In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT (RtPgPostMalB.rtb_c23_ch hx)) (as_universe B).
Hypothesis HTRACE_C46 : forall (regsT : bvmap 5 word) (hx : rhb_hcx rsegs),
  raZ (h_regs hx) = RA_LLVMF -> raZ regsT = RSB_C6 ->
  In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT (RtPgW14MalB.w14m_ch hx)) (as_universe B).
Hypothesis HTRACE : forall c,
  In c [[RtPgX01B.RTXB_RA1]; [RtPgX01B.RTXB_RA1; RA_LLVMF]; [RtPgX01B.RTXB_RA2]; [RtPgX01B.RTXB_RA2; RA_LLVMF];
        [RtPgX01B.RTXB_RA3]; [RtPgX01B.RTXB_RA3; RA_LLVMF]] ->
  In (firstn kUnwindMax (pc_free_ra0 (as_code B) :: flat_map (fun r => if r =? pc_free_ra0 (as_code B) then [] else [r]) c))
  (as_universe B).

(* a proved statement's own premises, from the hypotheses above *)
Local Ltac rt_kit0 := first
  [ exact ameter_triv_laws | exact ameter_triv_fs_laws | apply AR_laws_ok | apply astack_free_law_ok
  | exact AMEMSET | exact (AMEMSET _) | exact AMEMCPY | exact (AMEMCPY _)
  | exact ASTRLEN | exact (rate_B_strlen_w7b B ASTRLEN)
  | exact ASTRCMP | exact (ASTRCMP _)
  | exact ML | exact IMGF | exact ASM1 | exact HPCS1 | exact HPCMC | exact ASNP | exact HAPI
  | exact ASM2 | exact (ASM2 _) | exact HPCS2 | exact ABCMP | exact (ABCMP _)
  | exact FFL | exact SMP | exact ASM4 | exact HPCS4 | exact HGOT | exact HSC | exact HGOTU | exact HUAR
  | exact HEMPTY | exact rate_static_B | exact rate_relro_B | exact HTRACE_E01
  | exact HPCM | exact HFREE | exact HTRACE | exact HTRACE_C23 | exact HTRACE_C46
  | exact AMALLOC | exact (AMALLOC _) | exact AFREE | (intros fx'; exact (AFREE fx'))
  | exact ASHF5 | (intros fx'; exact (ASHF5 fx'))
  | exact InstB.N_extendsftf2_contract | exact InstB.N_letf2_contract | exact InstB.N_floatditf_contract
  | exact InstB.N_subtf3_contract | exact InstB.N_getf2_contract
  | (unfold RSB_RSZ in HSTK; lia) | (unfold RSB_EV in HEV; lia) | lia ].
(* ... and the callee contracts the pieces take, from the callee walks: reac_rate_prop_parse
   (RtPgParseB.rt_parse_B), reac_rate_refuse_code (RtPgRefuseB.rt_refuse_code_B), check_code
   (RtPgCheckCode.rt_check_code_B), reac_rate_drivable_csv (RtPgDcsvB.rt_drivable_csv_B, its runtime conjunction
   RtPgDcsvDefsB.dc_rt) and check_csv (RtPgCcsvB.rt_check_csv_B), the last four at every float state *)
Local Ltac rt_kit := first
  [ rt_kit0
  | (apply RtPgParseB.rt_parse_B; rt_kit0)
  | (apply PweRun.pod_write_ent_B; rt_kit0)
  | (intros fy; apply RtPgRefuseB.rt_refuse_code_B; rt_kit0)
  | (intros fy; apply CCB.rt_check_code_B; rt_kit0)
  | (intros fy; apply RtPgCcsvB.rt_check_csv_B; rt_kit0)
  | (intros fy; apply RtPgDcsvB.rt_drivable_csv_B; unfold RtPgDcsvDefsB.dc_rt;
     repeat match goal with |- _ /\ _ => split end; rt_kit0) ].

Theorem rate_lib_x_B : rt_lib_contract_x rsegs B ameter_triv K XL XL 0x9b9e0 0x9ce68
  A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
eapply (rate_lib_x_B_pieces HOFL B rate_static_B).
all: first
  [ (apply RtPgW3aB.rt_B_piece_W3a; rt_kit)
  | (apply RtPgW3aB7.rt_B_piece_W3b_b7; rt_kit)
  | (apply RtPgW3bB.rsb_piece_W3b_hdr; rt_kit)
  | (apply RtPgW3bPreB.rsb_piece_W3b_pre; rt_kit)
  | (apply RtPgPropBSel.pab_piece_sel; rt_kit)
  | (apply RtPgPropB.pab_piece_int7_B; rt_kit)
  | (apply RtPgPropBKey.pab_piece_key; rt_kit)
  | (apply RtPgPropBLatch.pab_piece_latch; rt_kit)
  | (apply RtPgW5IntPB.w5b_piece_int; rt_kit)
  | (apply RtPgW5OpenPB.w5b_piece_open; rt_kit)
  | (apply RtPgW5ClosePB.w5b_piece_close; rt_kit)
  | (apply RtPgW6aB.w6b_disp; rt_kit)
  | (apply RtPgW6aB.w6b_cases; rt_kit)
  | (apply RtPgW6bTopB.w6bb_piece; rt_kit)
  | (apply RtPgW6cB.w6cb_piece; rt_kit)
  | (apply RtPgEnt0B.rt7b_W7a; rt_kit)
  | (apply RtPgW7bPieceB.w7b_piece; rt_kit)
  | (apply RtPgBW8Top.rsb_piece_W8; rt_kit)
  | (apply RtPgPostB.wb10_post; rt_kit)
  | (apply RtPgPostCorrB.wb10_corr; rt_kit)
  | (apply RtPgPostReqB.wb10_req; rt_kit)
  | (eapply RtPgPostMalB.rt_B_S_C23; rt_kit)
  | (apply RtPgScanHeadB.rkb_head_B; rt_kit)
  | (apply RtPgScanSetupB.rkb_setup_B; rt_kit)
  | (apply RtPgScanOuterB.rkb_outer_B; rt_kit)
  | (apply RtPgScanInnerB.rkb_inner_B; rt_kit)
  | (apply RtPgM02ChkB.rt_m02_checks_B; rt_kit)
  | (apply RtPgM02KeyB.rt_m02_key_B; rt_kit)
  | (apply RtPgDecB.rt_dec_turn_B; rt_kit)
  | (apply RtPgW14AskB.rt_w14_asked_B; rt_kit)
  | (apply RtPgW14TailB.rt_w14_tail_B; rt_kit)
  | (eapply RtPgW14MalB.rt_w14_S_C46_B; rt_kit)
  | (intros fx'; apply RtPgW14CsvB.rt_w14_csv_B; rt_kit)
  | (eapply RtPgE01B.rtb_S_E01; rt_kit)
  | (eapply RtPgX01B.rtxb_S_X01; rt_kit)
  | eassumption ].
Qed.
(* inside the Section: the Section hypotheses the theorem uses show as its hypotheses *)
Print Assumptions rate_lib_x_B.
End i.

Print Assumptions rate_B_strlen_w7b.
Print Assumptions rate_lib_x_B.
