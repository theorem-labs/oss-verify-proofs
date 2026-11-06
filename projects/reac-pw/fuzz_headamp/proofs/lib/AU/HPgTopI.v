(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v:120-122
   [Apache-2.0]; proofs/cgif/cgif_file_fuzzer/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   proofs/cgif/cgif_rgb_fuzzer/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v at origin/ossv/recipes 6ebe35ba632; its three generic lemmas L_set_shadow_at, L_fresh and L_chain are kept as rx_set_shadow_at, rx_fresh and rx_chain (rx_set_shadow_at takes the kit's ajournal_after_write, which the strong shadow-fill text allows, in place of L_after_write_win), module paths changed to reac_pw.fuzz_role; the segment walk of reac-pw/fuzz_role's image A below is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at c83d21158e9 for reac-pw/fuzz_headamp's
   image A: module paths changed to reac_pw.fuzz_headamp and the prefix rx_ renamed to hx_; kept: rx_chain,
   rx_rdword_of_val, rx_st_region, rx_chunk_zero, rx_reg_atom, rx_reg_ext, rx_reg_lit, rx_ew_reg, rx_flag0_of,
   rx_entry0, rx_jF, the tactics rx_atom, rx_lit, rx_ext, z5, z5g, rx_mach and the flag-store tactic rx_run_flag
   (the corrected local copy of the kit's aj_run_flag); rx_ffacts restated for the class-4 frame (1024 bytes, 128
   shadow bytes, flag pointer at F+0x3f8); rx_fresh, rx_regs, rx_regs_pres, rx_regs_run and rx_aview_same dropped;
   rx_set_shadow_at replaced by fuzz_identity's L_set_shadow_at and L_after_write_win
   (proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v at origin/ossv/recipes 2d2ff01bb6f, renamed
   hx_set_shadow_at and hx_after_write_win), whose journal step needs only the shadow-fill text of
   libreac/fuzz_boxreg's released lib/A/Rt/SetShadowDef.v; the step-keep lemma and the 8-byte read follow
   proofs/libreac/fuzz_disco/lib/A/Prog/ReacRateSnap.v (origin/ossv/recipes 2d2ff01bb6f) rs_step_keep and rs_rdn8;
   the walks of headamp's X01 (lib/A/HPgSegM.v hq_S_X01f_stmt and hq_S_X01r_stmt) are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgX01.v, with its module paths, module names and addresses changed; 306 of its 361 lines of code are new or changed and 1170 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses from the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff): THE WHOLE RUN OF LLVMFuzzerTestOneInput AT IMAGE
   B's SEGMENTS (lib/AU/Img0U.v rsegs = images.AsanUbsan.M.loaded_segments) and its read-only range
   0x9c100 .. 0x9d4e8 (.data.rel.ro start .. .got end), for every symbol record B whose static facts hold.

     headamp_lib_x_B : hd_lib_contract_x rsegs B ameter_triv K XL XL 0x9c100 0x9d4e8 A_LLVMF RA_LLVMF ...

   It instantiates lib/AU/HPgTop.v headamp_lib_x and discharges what image B's lanes have proved:
   - the read-only range lies in the image (HPgSiteB.headamp_B_relro_img) and, with every non-writable segment,
     below the sink's overflow head when that head is at or above 0x9d4e8 (HOFL);
   - headamp_build_contract by HPgMainL.headamp_build_holds over the 21 build pieces (W3a, W3b, W4, W5, W6a, W6b,
     W6c, W7a, W7b, W8, W10), headamp_check_contract by HPgSegM.headamp_check_holds over M03's twelve pieces (M3a,
     M3b, M3c, M3d, M3e, M24_first; M3e's and M3a's check callees by the check walks of HPgChkU_*.v); pod_write_ent
     (0x84634, called out of line by W4's shape-7 body, W5's value pod and W8) by PweRun.pod_write_ent_B;
   - E01 (HPgE01.hqu_E01_ok), the three malloc steps (HPgM24C23 / C45 / C67), M02 / M04a / M04b (HPgM24Dup /
     HPgM24Cpy / HPgM24Plain, M04b's check_plain by its walk) and X01's two parts (HPgX01U.hxu_S_X01f /
     hxu_S_X01r); the meter's laws by YCbp.ameter_triv_laws, AR's laws by the kernel's AR_laws_ok, the segments'
     stack, event and live-byte budgets from HSTK, HEV and HLIVE.
   headamp_lib_x_B takes, as Section hypotheses, the symbol record's facts, the harness constants' facts, the sink's
   laws, the lib shape's leaf law, the runtime contracts, and M03's key piece (M3c), whose proof takes the strncmp /
   strcmp wrappers' contracts and is discharged at the core's record.
   Section fin then proves headamp_lib_x_all_fx, HPgLibU.headamp_lib_x_all_stmt's contract at image B's core record
   (YD2l.TfibB, YE2k.tfib_K, YB1v.tfibsegs, YCfn's constants), every image fact of the core, every runtime
   contract and every piece discharged at TfibB (the class-4 side stack, strlen and __asan_set_shadow_f5 by
   lib/AU/Rt's RtSM4, Strlen and SetShadow; the parse by lib/AU/HPgParse.v's tops over the strncmp / strtol /
   strcmp wrappers' hole forms; M3c by lib/AU/HPgKcuM3c.v over lib/AU/HPgWrapNcmp.v and lib/AU/Rt/Strcmp.v), and
   headamp_lib_x_all, HPgLibU.headamp_lib_x_all_stmt itself, from it.
   Proves no function of its own (kind: merge). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import StrlenDef.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgE01D HPgHarn HPgMainL HPgTop HPgSiteB.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgM24MalKit PweSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgE01 HPgW3a HPgW3bHdr HPgW3bB7 HPgW3bPre
  HPgPropSel HPgPropInt HPgPropKey HPgPropLatch HPgW5Int HPgW5Open HPgW5Close HPgW6aTop HPgW6b HPgW6cTop HPgE0
  HPgW7bTop HPgW8BTop HPgW10Post HPgW10Corr HPgW10Req PweRun HPgM24C23 HPgM24C45 HPgM24C67 HPgM24Dup HPgM24Cpy
  HPgM24Plain HPgM24Req HPgBM3aHead HPgBM3aSetup HPgBM3bPair HPgBM3bScan HPgBM3bLatch HPgBM3bRefuse HPgM3dBU
  HPgBM3eCell HPgBM3eRc HPgX01U HPgChkU_check_object HPgChkU_check_cells HPgChkU_check_keys HPgChkU_check_refusal
  HPgChkU_check_plain HPgChkU_check_no_overrun HPgChkU_check_count HPgChkU_check_cells_valid.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require YB1v YF0m YD2l YE2k YCfn YCeg YD1u YE2r YE2q YCej
  HPgLibU HPgStatB.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU.Rt Require Strlen SetShadow RtSM4 RtLStrtolH StrcmpHole Strcmp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgParse HPgWrapNcmpH HPgWrapNcmp HPgKcuM3c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* Every non-writable loaded segment of image B ends at or below 0x9d4e8. *)
Lemma headamp_B_rom_end_chk :
  forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x9d4e8)) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

(* The parse's two contracts take the read-only range only in the premise arodata_okP (HPgCSpec.hd_parse_args);
   in_roP segs 0 0 is the non-writable segments alone, so a contract stated at RLO = RHI = 0 gives it at any range
   (the same lemma as image A's lib/A/HPgTopI.v hq_parse_ro_mono: the parse's texts are image-free). *)
Section ro. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable MT : ameter_ops.
Lemma hqu_arodata_00 : forall rlo rhi rd, arodata_okP segs rlo rhi B rd -> arodata_okP segs 0 0 B rd.
Proof.
intros rlo rhi rd H a Hro Ho He. apply H; [|exact Ho | exact He].
destruct Hro as [Hs|Hr]; [left; exact Hs | lia].
Qed.
Lemma hqu_parse_ro_mono : forall a RLO RHI akey aph apad asens gotw guard dcs,
  hd_parse_specX segs B MT a 0 0 akey aph apad asens gotw guard dcs ->
  hd_parse_specX segs B MT a RLO RHI akey aph apad asens gotw guard dcs.
Proof.
intros a RLO RHI akey aph apad asens gotw guard dcs H STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
  null P O cap ev bs Hpre Hn H10 H11 H12 Hargs.
apply (H STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs null P O cap ev bs Hpre Hn H10 H11 H12).
destruct Hargs as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & Haro & Hfrm).
exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj A9 (conj A10 (conj A11
  (conj A12 (conj A13 (conj (hqu_arodata_00 RLO RHI _ Haro) Hfrm)))))))))))))).
Qed.
End ro.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.

(* the sink's overflow head of the core (YE2k.tfib_sink_head, 0x5f88c8) lies above the read-only data *)
Hypothesis HOFL : 0x9d4e8 <= YI16.sk_ofl_head.
#[local] Instance headamp_ro_B : ro_below_ofl rsegs 0x9c100 0x9d4e8.
Proof.
intros a [(s & Hs & Hw & Hr) | Hr]; [|lia].
pose proof headamp_B_rom_end_chk as C. rewrite forallb_forall in C. pose proof (C s Hs) as Cs.
rewrite Hw in Cs. cbn [orb] in Cs. apply Z.leb_le in Cs. lia.
Qed.

Variable B : asyms.
(* the static facts of the symbols (the start-up's const cells, zero-shadow ranges and pinned owned bytes) *)
Hypothesis HSTAT : hqu_static_law rsegs B 0x9c100 0x9d4e8.
(* the errno cell lies in the image, low, and the allocator's one-entry traces are in the universe *)
Hypothesis errno_low : api_env rsegs B.
Variable K : asink_syms.
Variable XL : Z -> Z.
Variables A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
(* the harness constants (the core's YCfn: A_LLVMF 0x80c40, EV_LIB, LIVE_LIB, LLVMF_STK; by computation) *)
Hypothesis HA : A_LLVMF = HQU_ENTRY.
Hypothesis HEV : HQU_EV <= EV_LIB.
Hypothesis HSTK : HQU_RSZ + 32 + ASTACK <= LLVMF_STK.
Hypothesis HLIVE : Layout.PP_SIZE + 5440 + 30 + 27 <= LIVE_LIB.
(* the core's sink laws at the symbols (the core's YD1u.tfib_AIL) *)
Hypothesis AIL : asink_img_laws rsegs B K.
(* the lib shape's one-leaf law (headamp_lib_x_all_stmt's first premise) *)
Hypothesis LEAF : forall pl fs (Kl : lleaf -> TSet), LIBK pl fs Kl = Kl (LL 0 fs []).

(* ---------------- the runtime's facts the proved segments take ---------------- *)
(* the runtime's malloc against the allocator model, at every float state, and the model's laws *)
Hypothesis AMALLOC : forall fx' : YK11.FPState, amalloc_realizes (fx := fx') rsegs B.
Hypothesis ML : model_laws (as_universe B).
(* the code record: malloc's entry is the `jal` target 0x530e0 *)
Hypothesis HPCM : pc_wrap_malloc (as_code B) = 0x530e0.
(* the malloc traces at the return addresses C3 0x82f00, C5 0x82f38 and C7 0x83904 are in the universe *)
Hypothesis HTRACE_C23 : forall (regsT : bvmap 5 word) (hx : hqu_hcx rsegs),
  raZ (hu_regs rsegs hx) = RA_LLVMF -> raZ regsT = HQU_C3 ->
  In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT (hkb_ch hx)) (as_universe B).
Hypothesis HTRACE_C45 : forall (regsT : bvmap 5 word) (hx : hqu_hcx rsegs),
  raZ (hu_regs rsegs hx) = RA_LLVMF -> raZ regsT = HQU_C5 ->
  In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT (hkb_ch hx)) (as_universe B).
Hypothesis HTRACE_C67 : forall (regsT : bvmap 5 word) (hx : hqu_hcx rsegs),
  raZ (hu_regs rsegs hx) = RA_LLVMF -> raZ regsT = HQU_C7 ->
  In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT (hkb_ch hx)) (as_universe B).
(* __asan_memcpy at 0x51d8c and __asan_memset at 0x52228, at every float state *)
Hypothesis AMEMCPY : forall fx' : YK11.FPState, aintrin_realizes (fx := fx') rsegs B OCpy 0x51d8c.
Hypothesis AMEMSET : forall fx' : YK11.FPState, aintrin_realizes (fx := fx') rsegs B OSet 0x52228.
(* the parse (the result function 0x849ac and its 8-byte wrapper 0x849a4) at every float state, stated at the
   read-only range RLO = RHI = 0 (the strongest form; hqu_parse_ro_mono gives M04b's range) *)
Hypothesis PARSE_R : forall fx' : YK11.FPState, hd_parse_result_specX (fx := fx') rsegs B ameter_triv 0x849ac 0 0
  (hi_akey headamp_himg_B) (hi_aph headamp_himg_B) (hi_apad headamp_himg_B) (hi_asens headamp_himg_B)
  (hi_gotw headamp_himg_B) (hi_guard headamp_himg_B) (hi_dcs headamp_himg_B).
Hypothesis PARSE_W : forall fx' : YK11.FPState, hd_parse_specX (fx := fx') rsegs B ameter_triv 0x849a4 0 0
  (hi_akey headamp_himg_B) (hi_aph headamp_himg_B) (hi_apad headamp_himg_B) (hi_asens headamp_himg_B)
  (hi_gotw headamp_himg_B) (hi_guard headamp_himg_B) (hi_dcs headamp_himg_B).
(* the errno cell is not in a read-only segment *)
Hypothesis ERRNO_RW : forall a, as_errno B <= a < as_errno B + 4 -> ~ in_rom rsegs a.

(* the free operation and the side stack's class-4 frame at every float state, the frame flag law, the code
   record's entries (class-4 frame 0x3cd2c, free 0x530dc) *)
Hypothesis AFREE : forall fx' : YK11.FPState, afree_realizes (fx := fx') rsegs B.
Hypothesis ASM4 : forall fx' : YK11.FPState, astack_malloc_realizes (fx := fx') rsegs B 4.
Hypothesis HSM4 : pc_stack_malloc (as_code B) 4 = 0x3cd2c.
Hypothesis FFL : frame_flag_lawP rsegs B.
Hypothesis HFREE : pc_wrap_free (as_code B) = 0x530dc.
(* the shadow-offset and use-after-return .got words and the runtime cells they name; the empty input's address *)
Hypothesis HBgot : as_got_shadow B = 0x9c7f0.
Hypothesis HBcell : as_shadow_cell B = 0xa5238.
Hypothesis HGU : as_got_uar B = 0x9c848.
Hypothesis HUC : as_uar_cell B = 0xa5240.
Hypothesis HAE : 0 < A_EMPTY < kLowMemEnd.
(* the strlen wrapper at its trampoline 0x41c18, at every float state *)
Hypothesis ASTRLEN : forall fx' : YK11.FPState, astrlen_realizes (fx := fx') rsegs B STRLEN_ENTRY_B.
(* __asan_set_shadow_f5 at 0x54d54, at every float state (lib/AU/HPgX01U.v's text) *)
Hypothesis ASHF5 : forall fx : YK11.FPState,
forall ly S W regs mem md cid pos q n,
ecall_pre rsegs B ly S W regs mem md -> In (cid, pos) (frames S) ->
getr regs 10 = w64 q -> getr regs 11 = w64 n -> 0 < n ->
shadow_addr (frame_addr ly cid pos) <= q -> q + n <= shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 ->
SRr rsegs W (@cfg_at fx rsegs 0x54d54 regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = @cfg_at fx rsegs (raZ regs) regs' mem' md' /\
AR rsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall i, 0 <= i < n -> aview rsegs (w_H W) mem' (q + i) = Some 0xf5) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a)).
(* the traces of the malloc call site C1 (E01) and of the four free sites *)
Hypothesis HTRACE_E01 : e01u_trace_stmt B RA_LLVMF.
Hypothesis HTRACE_X01 : forall c, In c [[HPgX01U.HXU_RA1]; [HPgX01U.HXU_RA1; RA_LLVMF]; [HPgX01U.HXU_RA2];
  [HPgX01U.HXU_RA2; RA_LLVMF]; [HPgX01U.HXU_RA3]; [HPgX01U.HXU_RA3; RA_LLVMF]; [HPgX01U.HXU_RA4];
  [HPgX01U.HXU_RA4; RA_LLVMF]] ->
In (firstn kUnwindMax (pc_free_ra0 (as_code B) :: flat_map (fun r => if r =? pc_free_ra0 (as_code B) then [] else [r]) c))
(as_universe B).
(* M03's key piece (hqu_piece_M3c_key_stmt): its proof takes the two string wrappers' contracts, discharged with it
   at the core's record in Section fin *)
Hypothesis PM3c_key : hqu_piece_M3c_key_stmt rsegs B ameter_triv.

(* the runtime and symbol facts a lane's theorem asks, from this Section's hypotheses and the kernel *)
Local Ltac hqu_rt0 := first
  [ assumption | exact errno_low | exact headamp_B_relro_img | apply ameter_triv_laws | apply AR_laws_ok
  | apply AMEMSET | apply AMEMCPY | apply ASTRLEN | apply AMALLOC | apply AFREE | apply ASM4
  | apply PARSE_R | apply PARSE_W | (apply hqu_parse_ro_mono; apply PARSE_W)
  | (apply PweRun.pod_write_ent_B; [apply ameter_triv_laws | exact HBgot | exact HBcell | apply AMEMCPY | apply AMEMSET])
  | lia
  | (assert (8 <= EV_LIB) by exact HEV; lia)
  | (assert (0x220 + 32 + ASTACK <= LLVMF_STK) by exact HSTK; try unfold HQU_RSZ; lia) ].
Local Ltac hqu_rt := first
  [ hqu_rt0
  | (intros ?fy; apply HPgChkU_check_object.hd_check_object_B; hqu_rt0)
  | (intros ?fy; apply HPgChkU_check_cells.hd_check_cells_B; hqu_rt0)
  | (intros ?fy; apply HPgChkU_check_keys.hd_check_keys_B; hqu_rt0)
  | (intros ?fy; apply HPgChkU_check_refusal.hd_check_refusal_B; hqu_rt0)
  | (intros ?fy; apply HPgChkU_check_plain.hd_check_plain_B; hqu_rt0)
  | (intros ?fy; apply HPgChkU_check_no_overrun.hd_check_no_overrun_B; hqu_rt0)
  | (intros ?fy; apply HPgChkU_check_count.hd_check_count_B; hqu_rt0)
  | (intros ?fy; apply HPgChkU_check_cells_valid.hd_check_cells_valid_B; hqu_rt0) ].

(* ---------------- the segments, each from its lane's theorem ---------------- *)
Lemma hqB_E01 : hqu_S_E01_stmt rsegs B 0x9c100 0x9d4e8 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof. apply HPgE01.hqu_E01_ok; hqu_rt. Qed.
Lemma hqB_build : headamp_build_contract rsegs B ameter_triv headamp_himg_B 0x9c100 0x9d4e8.
Proof.
apply (headamp_build_holds rsegs B ameter_triv headamp_himg_B headamp_bld_B).
all: first
  [ (apply HPgW3a.hsu_piece_W3a; hqu_rt)
  | (apply HPgW3bHdr.hsu_piece_W3b_hdr_B; hqu_rt)
  | (apply HPgW3bB7.hsu_piece_W3b_b7_B; hqu_rt)
  | (apply HPgW3bPre.hsu_piece_W3b_pre_B; hqu_rt)
  | (apply HPgPropSel.hbp_piece_sel; hqu_rt)
  | (apply HPgPropInt.hbp_piece_int7; hqu_rt)
  | (apply HPgPropKey.hbp_piece_key; hqu_rt)
  | (apply HPgPropLatch.hbp_piece_latch; hqu_rt)
  | (apply HPgW5Int.hw5_piece_int; hqu_rt)
  | (apply HPgW5Open.hw5_piece_open; hqu_rt)
  | (apply HPgW5Close.hw5_piece_close; hqu_rt)
  | (apply HPgW6aTop.w6b_piece_disp; hqu_rt)
  | (apply HPgW6aTop.w6b_piece_cases; hqu_rt)
  | (apply HPgW6b.hsu_piece_W6b; hqu_rt)
  | (apply HPgW6cTop.hsu_piece_W6c; hqu_rt)
  | (apply HPgE0.e0_piece_W7a; hqu_rt)
  | (apply HPgW7bTop.hsu_piece_W7b_ok; hqu_rt)
  | (apply HPgW8BTop.hsu_piece_W8_headamp_B; hqu_rt)
  | (apply HPgW10Post.hw10_post; hqu_rt)
  | (apply HPgW10Corr.hw10_corr; hqu_rt)
  | (apply HPgW10Req.hw10_req; hqu_rt) ].
Qed.
Lemma hqB_C23 : hqu_S_C23_stmt rsegs B 0x9c100 0x9d4e8 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof. apply HPgM24C23.hqu_B_S_C23; hqu_rt. Qed.
Lemma hqB_dup : headamp_dup_contract rsegs B ameter_triv headamp_himg_B 0x9c100 0x9d4e8.
Proof. apply HPgM24Dup.headamp_B_dup_holds; hqu_rt. Qed.
Lemma hqB_C45 : hqu_S_C45_stmt rsegs B 0x9c100 0x9d4e8 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof. apply HPgM24C45.hqu_B_S_C45; hqu_rt. Qed.
Lemma hqB_check : headamp_check_contract rsegs B ameter_triv headamp_himg_B 0x9c100 0x9d4e8.
Proof.
apply headamp_check_holds.
all: first
  [ exact PM3c_key
  | (apply HPgBM3aHead.hqu_M3a_head; hqu_rt)
  | (apply HPgBM3aSetup.hqu_M3a_setup; hqu_rt)
  | (apply HPgBM3bPair.hbu_pair_B; hqu_rt)
  | (apply HPgBM3bScan.hbu_scan_B; hqu_rt)
  | (apply HPgBM3bScan.hbu_scanf_B; hqu_rt)
  | (apply HPgBM3bLatch.hbu_latch_B; hqu_rt)
  | (apply HPgBM3bRefuse.hbu_refuse_B; hqu_rt)
  | (apply HPgM3dBU.headamp_m3d_value_B; hqu_rt)
  | (apply HPgBM3eCell.hbe_piece_M3e_cell; hqu_rt)
  | (apply HPgBM3eRc.hbe_piece_M3e_rc; hqu_rt)
  | (apply HPgM24Req.hqu_B_piece_M24_first; hqu_rt) ].
Qed.
Lemma hqB_C67 : hqu_S_C67_stmt rsegs B 0x9c100 0x9d4e8 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof. apply HPgM24C67.hqu_B_S_C67; hqu_rt. Qed.
Lemma hqB_first : forall fx' : YK11.FPState,
  headamp_first_contract (fx := fx') rsegs B ameter_triv headamp_himg_B 0x9c100 0x9d4e8.
Proof. intros fx'. apply HPgM24Cpy.headamp_B_first_holds; hqu_rt. Qed.
Lemma hqB_plain : forall fx' : YK11.FPState,
  headamp_plain_contract (fx := fx') rsegs B ameter_triv headamp_himg_B 0x9c100 0x9d4e8.
Proof. intros fx'. apply HPgM24Plain.headamp_B_plain_holds; hqu_rt. Qed.
Lemma hqB_X01f : hqu_S_X01f_stmt rsegs B 0x9c100 0x9d4e8 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof. apply HPgX01U.hxu_S_X01f; hqu_rt. Qed.
Lemma hqB_X01r : hqu_S_X01r_stmt rsegs B 0x9c100 0x9d4e8 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof. apply HPgX01U.hxu_S_X01r; hqu_rt. Qed.

Theorem headamp_lib_x_B : hd_lib_contract_x rsegs B ameter_triv K XL XL 0x9c100 0x9d4e8
  A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
eapply (headamp_lib_x rsegs B).
all: first
  [ exact headamp_B_relro_img | exact headamp_ro_B | exact HSTAT | exact errno_low
  | exact hqB_E01 | exact hqB_build | exact hqB_C23 | exact hqB_dup | exact hqB_C45 | exact hqB_check
  | exact hqB_C67 | exact hqB_first | exact hqB_plain | exact hqB_X01f | exact hqB_X01r | eassumption ].
Qed.
End i.

Print Assumptions headamp_lib_x_B.

(* ============================ the final statement at image B's own record ============================ *)
(* HPgLibU.headamp_lib_x_all_stmt's contract at image B's core record: the symbols YD2l.TfibB, the sink
   YE2k.tfib_K with its overflow head YE2k.tfib_sink_head, the segments YB1v.tfibsegs (Img0U.rsegs: both are
   images.AsanUbsan.M.loaded_segments), XL0, the read-only range RO_LO .. RO_HI and YCfn's constants. The image facts
   of headamp_lib_x_B are discharged here (the record's fields, the constants, the trace universe YCej.Tfib_universe
   by computation; the sink laws YD1u.tfib_AIL; the model laws YG05.model_laws_ok; the frame flag law from AR's laws
   and YCeg.tfib_img_cover; __asan_memset / __asan_memcpy by YE2r / YE2q; the errno cell by YCeg.tl_env; the static
   facts of the symbols by HPgStatB.hqu_static_B); the facts still open are this Section's hypotheses. *)
Lemma hqu_rsegs_tfib : rsegs = YB1v.tfibsegs.
Proof. reflexivity. Qed.

Lemma hqF_TL : YCeg.TfibLib YD2l.TfibB.
Proof.
constructor; try reflexivity.
- cbn [as_errno YD2l.TfibB]. unfold YF0m.TFIB_ERRNO, kLowMemEnd. lia.
- cbn [as_errno YD2l.TfibB]. unfold YF0m.TFIB_ERRNO.
  assert (E : existsb (fun sg => (Z.of_N (seg_base sg) <=? 0x5d812c) &&
    (0x5d8130 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) YB1v.tfibsegs = true) by (vm_compute; reflexivity).
  intros a Ha. apply existsb_exists in E as (sg & Hin & Hb). apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. exists sg. split; [exact Hin | lia].
- intros a [].
- cbn [as_gp YD2l.TfibB]. unfold YF0m.TFIB_GP. lia.
Qed.

Lemma hqF_api : api_env rsegs YD2l.TfibB.
Proof. exact (YCeg.tl_env YD2l.TfibB hqF_TL). Qed.

Lemma hqF_errno_rw : forall a, as_errno YD2l.TfibB <= a < as_errno YD2l.TfibB + 4 -> ~ in_rom rsegs a.
Proof.
intros a Ha (s & Hs & Hw & Hr). cbn [as_errno YD2l.TfibB] in Ha. unfold YF0m.TFIB_ERRNO in Ha.
pose proof headamp_B_rom_end_chk as C. rewrite forallb_forall in C. pose proof (C s Hs) as Cs.
rewrite Hw in Cs. cbn [orb] in Cs. apply Z.leb_le in Cs. lia.
Qed.

Lemma hqF_ml : model_laws (as_universe YD2l.TfibB).
Proof. exact (YG05.model_laws_ok _ YCej.Tfib_universe_ok). Qed.

(* the two malloc-call traces at a call site whose return address is X: [ra0; X] and [ra0; X; R] *)
Lemma hqu_ct0 : forall pc0 X R (regsT : bvmap 5 word) (ch : list (Z * Z * Z)) U,
  raZ regsT = X -> (ch = [] \/ exists fp v, ch = [(fp, R, v)]) ->
  In (unwind_of_chain pc0 [(0, X, 0)]) U -> In (unwind_of_chain pc0 [(0, X, 0); (0, R, 0)]) U ->
  In (call_trace0 pc0 regsT ch) U.
Proof.
intros pc0 X R regsT ch U HX Hch H1 H2. unfold call_trace0.
destruct Hch as [->|(fp & v & ->)]; unfold unwind_of_chain in *; cbn [flat_map] in *; rewrite HX; assumption.
Qed.

Ltac hqu_univ := apply YD2l.In_of_existsb; vm_compute; reflexivity.

Lemma hqu_hk_ch : forall (hx : hqu_hcx rsegs), raZ (hu_regs rsegs hx) = YCfn.RA_LLVMF ->
  hkb_ch hx = [] \/ exists fp v, hkb_ch hx = [(fp, YCfn.RA_LLVMF, v)].
Proof.
intros hx H. unfold hkb_ch. destruct (_ <? _); [right; rewrite <- H; eexists; eexists; reflexivity | left; reflexivity].
Qed.

Section fin. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Local Notation TB := YD2l.TfibB.
#[local] Existing Instance YE2k.tfib_sink_head.

Lemma hqF_ofl : 0x9d4e8 <= @YI16.sk_ofl_head YE2k.tfib_sink_head.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma hqF_AIL : asink_img_laws rsegs TB YE2k.tfib_K.
Proof. first [exact (YD1u.tfib_AIL TB YD2l.TfibB_syms (AR_laws_ok _ _)) | exact (YD1u.tfib_AIL TB YD2l.TfibB_syms)]. Qed.

Lemma hqF_amemset : forall fx' : YK11.FPState, aintrin_realizes (fx := fx') rsegs TB OSet 0x52228.
Proof.
intros fx' ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
exact (YE2r.asan_memset_realizes TB (AR_laws_ok _ _) YD2l.TfibB_syms ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd
  Hdn Hdst Hra Hhull Ham).
Qed.

Lemma hqF_amemcpy : forall fx' : YK11.FPState, aintrin_realizes (fx := fx') rsegs TB OCpy 0x51d8c.
Proof.
intros fx' ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc.
exact (YE2q.asan_memcpy_realizes TB (AR_laws_ok _ _) YD2l.TfibB_syms ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd
  Hdn Hdst Ham Hra Hhull Hsrc).
Qed.

(* the frame's flag word is present, owned, an application address off the image [cgif ACed.v:133 tfibX_FFL] *)
Lemma hqF_ffl : frame_flag_lawP rsegs TB.
Proof.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ (AR_laws_ok rsegs TB) ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ (AR_laws_ok rsegs TB) ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (YCeg.tfib_img_cover ly S md L) as [C1 C2].
unfold YCeg.TFIB_IMG_LO, YCeg.TFIB_IMG_END in C1, C2.
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

Lemma hqF_tr_e01 : e01u_trace_stmt TB YCfn.RA_LLVMF.
Proof. intros regsT ch Hra Hch. apply (hqu_ct0 _ _ _ regsT ch _ Hra Hch); hqu_univ. Qed.
Lemma hqF_tr_c23 : forall (regsT : bvmap 5 word) (hx : hqu_hcx rsegs),
  raZ (hu_regs rsegs hx) = YCfn.RA_LLVMF -> raZ regsT = HQU_C3 ->
  In (call_trace0 (pc_malloc_ra0 (as_code TB)) regsT (hkb_ch hx)) (as_universe TB).
Proof. intros regsT hx Hh Hra. apply (hqu_ct0 _ _ _ regsT _ _ Hra (hqu_hk_ch hx Hh)); hqu_univ. Qed.
Lemma hqF_tr_c45 : forall (regsT : bvmap 5 word) (hx : hqu_hcx rsegs),
  raZ (hu_regs rsegs hx) = YCfn.RA_LLVMF -> raZ regsT = HQU_C5 ->
  In (call_trace0 (pc_malloc_ra0 (as_code TB)) regsT (hkb_ch hx)) (as_universe TB).
Proof. intros regsT hx Hh Hra. apply (hqu_ct0 _ _ _ regsT _ _ Hra (hqu_hk_ch hx Hh)); hqu_univ. Qed.
Lemma hqF_tr_c67 : forall (regsT : bvmap 5 word) (hx : hqu_hcx rsegs),
  raZ (hu_regs rsegs hx) = YCfn.RA_LLVMF -> raZ regsT = HQU_C7 ->
  In (call_trace0 (pc_malloc_ra0 (as_code TB)) regsT (hkb_ch hx)) (as_universe TB).
Proof. intros regsT hx Hh Hra. apply (hqu_ct0 _ _ _ regsT _ _ Hra (hqu_hk_ch hx Hh)); hqu_univ. Qed.
Lemma hqF_tr_x01 : forall c, In c [[HPgX01U.HXU_RA1]; [HPgX01U.HXU_RA1; YCfn.RA_LLVMF]; [HPgX01U.HXU_RA2];
  [HPgX01U.HXU_RA2; YCfn.RA_LLVMF]; [HPgX01U.HXU_RA3]; [HPgX01U.HXU_RA3; YCfn.RA_LLVMF]; [HPgX01U.HXU_RA4];
  [HPgX01U.HXU_RA4; YCfn.RA_LLVMF]] ->
  In (firstn kUnwindMax (pc_free_ra0 (as_code TB) :: flat_map (fun r => if r =? pc_free_ra0 (as_code TB) then [] else [r]) c))
  (as_universe TB).
Proof.
intros c Hc. repeat (destruct Hc as [<-|Hc]; [hqu_univ|]). destruct Hc.
Qed.

(* ---------------- the parse at image B's record ----------------
   lib/AU/HPgParse.v's tops at RLO = RHI = 0, their hypotheses at TfibB: the meter's laws, the symbol record's
   .got / shadow-cell / errno fields (by computation), the errno cell (YCeg.tl_env), and the three wrapper contracts
   in hole form at image B's trampolines: strncmp 0x41c24 (lib/AU/HPgWrapNcmpH.v), strtol 0x41ca8 with the guard
   cells 0x9d478 / 0x5f8210 (lib/AU/Rt/RtLStrtolH.v), strcmp 0x41c20 (lib/AU/Rt/StrcmpHole.v). *)
Local Ltac hqu_prs := first
  [ apply ameter_triv_laws | reflexivity | exact hqF_api
  | (intros ?F ?fc; exact AU.HPgWrapNcmpH.hd_astrncmp_hole_TfibB_rsegs)
  | (intros ?F ?fc; apply AU.Rt.RtLStrtolH.hd_strtol_hole; exact YD2l.TfibB_syms)
  | (intros ?F ?fc; exact (AU.Rt.StrcmpHole.strcmp_hole_contract TB (AR_laws_ok _ _) YD2l.TfibB_syms)) ].
Lemma hqF_parse_r : forall fx' : YK11.FPState, hd_parse_result_specX (fx := fx') rsegs TB ameter_triv 0x849ac 0 0
  (hi_akey headamp_himg_B) (hi_aph headamp_himg_B) (hi_apad headamp_himg_B) (hi_asens headamp_himg_B)
  (hi_gotw headamp_himg_B) (hi_guard headamp_himg_B) (hi_dcs headamp_himg_B).
Proof. intros fx'. apply AU.HPgParse.hd_parse_result_B00; hqu_prs. Qed.
Lemma hqF_parse_w : forall fx' : YK11.FPState, hd_parse_specX (fx := fx') rsegs TB ameter_triv 0x849a4 0 0
  (hi_akey headamp_himg_B) (hi_aph headamp_himg_B) (hi_apad headamp_himg_B) (hi_asens headamp_himg_B)
  (hi_gotw headamp_himg_B) (hi_guard headamp_himg_B) (hi_dcs headamp_himg_B).
Proof. intros fx'. apply AU.HPgParse.hd_parse_B00; hqu_prs. Qed.

(* ---------------- M03's key piece at image B's record ----------------
   lib/AU/HPgKcuM3c.v hqu_piece_M3c_key, its hypotheses at TfibB: the errno cell (YCeg.tl_env), the strncmp wrapper
   at 0x41c24 (lib/AU/HPgWrapNcmp.v hd_astrncmp_TfibB_rsegs) and the strcmp wrapper at 0x41c20 (lib/AU/Rt/Strcmp.v
   strcmp_icpt_contract), each at every float state. *)
Lemma hqF_m3c : hqu_piece_M3c_key_stmt rsegs TB ameter_triv.
Proof.
apply AU.HPgKcuM3c.hqu_piece_M3c_key.
all: first
  [ exact hqF_api
  | (intros ?fy; exact AU.HPgWrapNcmp.hd_astrncmp_TfibB_rsegs)
  | (intros ?fy; exact (AU.Rt.Strcmp.strcmp_icpt_contract TB (AR_laws_ok _ _) YD2l.TfibB_syms)) ].
Qed.

Theorem headamp_lib_x_all_fx :
  (forall pl fs (K : lleaf -> TSet), LIBK pl fs K = K (LL 0 fs [])) ->
  (forall fx' : YK11.FPState, @afree_realizes fx' rc YB1v.tfibsegs TB) ->
  (forall fx' : YK11.FPState, @amalloc_realizes fx' rc YB1v.tfibsegs TB) ->
  @HPgLibU.headamp_lib_contract_x fx rc LS TB ameter_triv HPgLibU.XL0 HPgLibU.XL0 HPgLibU.RO_LO HPgLibU.RO_HI.
Proof.
intros LEAF AFREE AMALLOC. unfold HPgLibU.headamp_lib_contract_x, HPgLibU.RO_LO, HPgLibU.RO_HI.
eapply (@headamp_lib_x_B fx rc YE2k.tfib_sink_head LS).
all: first
  [ exact hqF_ofl | exact (HPgStatB.hqu_static_B TB YD2l.TfibB_syms) | exact hqF_api
  | reflexivity
  | (apply Z.leb_le; vm_compute; reflexivity)
  | (split; apply Z.ltb_lt; vm_compute; reflexivity)
  | exact hqF_AIL | exact LEAF | exact AMALLOC | exact AFREE | exact hqF_ml | exact hqF_errno_rw
  | exact hqF_amemset | exact hqF_amemcpy | exact hqF_ffl
  | exact hqF_tr_e01 | exact hqF_tr_c23 | exact hqF_tr_c45 | exact hqF_tr_c67 | exact hqF_tr_x01
  | (intros ?fy; exact (AU.Rt.RtSM4.stack_malloc4_contract TB (AR_laws_ok _ _) YD2l.TfibB_syms))
  | (intros ?fy; exact (AU.Rt.Strlen.strlen_icpt_contract TB (AR_laws_ok _ _) YD2l.TfibB_syms))
  | (intros ?fy; exact (AU.Rt.SetShadow.box_set_shadow_f5 TB (AR_laws_ok _ _) YD2l.TfibB_syms))
  | exact hqF_parse_r | exact hqF_parse_w | exact hqF_m3c ].
Qed.
End fin.

Print Assumptions headamp_lib_x_all_fx.
About headamp_lib_x_all_fx.

(* lib/AU/HPgLibU.v's statement, the one image B's closing takes: the contract at every float state, given the lib
   shape's leaf law and the allocator's two operations. *)
Theorem headamp_lib_x_all : HPgLibU.headamp_lib_x_all_stmt.
Proof. intros rc LS LEAF AFREE AMALLOC fx. exact (@headamp_lib_x_all_fx fx rc LS LEAF AFREE AMALLOC). Qed.

Print Assumptions headamp_lib_x_all.
