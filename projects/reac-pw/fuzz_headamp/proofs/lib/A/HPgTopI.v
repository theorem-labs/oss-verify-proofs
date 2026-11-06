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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgX01.v, with its module paths and module names changed; 355 of its 411 lines of code are new or changed and 1169 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgTopI.v at 3c7e900fc63 for reac-pw/fuzz_headamp image A: module paths changed, role_ renamed to headamp_; image A's read-only range 0x9bc80 .. 0x9d068 (lib/A/HPgLib.v RO_LO / RO_HI, lib/A/HPgSiteA.v headamp_A_relro_img); role's two middle contracts become headamp's five and its three walk segments headamp's eight (E01, the three malloc steps, X01's two parts); every segment and piece a lane has proved is discharged here by that lane's theorem, with its runtime hypotheses taken here. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; addresses from the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a): THE WHOLE RUN OF LLVMFuzzerTestOneInput AT IMAGE
   A's SEGMENTS (lib/A/Img0.v rsegs = images.Asan.M.loaded_segments) and its read-only range 0x9bc80 .. 0x9d068
   (.data.rel.ro start .. .got end), for every symbol record B whose static facts hold.

     headamp_lib_x_A : hd_lib_contract_x rsegs B ameter_triv K XL XL 0x9bc80 0x9d068 A_LLVMF RA_LLVMF ...

   It instantiates lib/A/HPgTop.v headamp_lib_x and discharges what the lanes have proved:
   - the read-only range lies in the image (HPgSiteA.headamp_A_relro_img) and, with every non-writable segment,
     below the sink's overflow head when that head is at or above 0x9d068 (HOFL);
   - headamp_build_contract by HPgMainL.headamp_build_holds over the build pieces, headamp_check_contract by
     HPgSegM.headamp_check_holds over M03's pieces; the pieces W3a, W3b, W4, W5, W6a, W6b, W7a, W8, W10, M3a, M3b,
     M3c, M3d, M3e and M24_first by their lanes' theorems (M3e's check callees by the check walks of HPgChk_*.v);
   - E01 (HPgE01.headamp_E01_ok), the three malloc steps (HPgPostMal.hq_A_S_C23, HPgM24Out.hq_A_S_C45,
     HPgM24Mal.hq_A_S_C67), M02 / M04a / M04b (HPgM02 / HPgM04a / HPgM04b, M04b's check_plain by its walk) and
     X01's two parts (HPgX01.hx_S_X01f / hx_S_X01r); the meter's laws by YCbp.ameter_triv_laws, AR's laws by the
     kernel's AR_laws_ok, the segments' stack, event and live-byte budgets from HSTK, HEV and HLIVE.
   headamp_lib_x_A takes, as Section hypotheses, the symbol record's facts, the harness constants' facts, the sink's
   laws, the lib shape's leaf law and the runtime contracts.
   Section fin then proves headamp_lib_x_all_fx, HPgLib.headamp_lib_x_all_stmt's contract at the relocated frame's
   record (AD2l.TfibB, AE2k.tfib_K, AB1v.tfibsegs, ACfn's constants), every image fact and the parse discharged at
   TfibB, and headamp_lib_x_all proves HPgLib.headamp_lib_x_all_stmt with no Section hypothesis. Proves no function
   of its own (kind: merge). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgE01D HPgSegC23 HPgM24Out HPgHarn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgMainL HPgTop HPgSiteA.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgM02 HPgM04a HPgM04b HPgM24F HPgM24Mal.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgCalls HPgCallsStr HPgKcStr HPgX01 HPgE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import StrlenDef.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgW3a HPgW3b HPgW3bPre HPgProp HPgW5IntP HPgW5OpenP
  HPgW5CloseP HPgW6a HPgW6b HPgEnt0 HPgW8 HPgPostTop HPgPostCorr HPgPostReq HPgPostMal HPgM3bPair HPgM3bScan
  HPgM3bLatch HPgM3bRefuse HPgKcA HPgM3eCell HPgM3eRc HPgChk_check_object HPgChk_check_cells HPgChk_check_keys
  HPgChk_check_refusal HPgChk_check_plain HPgChk_check_no_overrun HPgChk_check_count HPgChk_check_cells_valid
  HPgM3aHead HPgM3aSetup HPgM3dA HPgW6c HPgW7b.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require AB1v AF0m AD2l AE2k ACfn ACeg AD1u AE2r AE2q ACej HPgLib.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require RtSM4 Strlen Strcmp SetShadow RtLStrtolH StrcmpHole.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgWrapNcmp HPgWrapNcmpH HPgStatA HPgParse.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* Every non-writable loaded segment ends at or below 0x9d068 (R [0x10000, 0x2f6e4), RX [0x306e4, 0x9ac44)). *)
Lemma headamp_rom_end_chk : forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x9d068))
  rsegs = true.
Proof. vm_compute. reflexivity. Qed.

(* The parse's two contracts take the read-only range only in the premise arodata_okP (HPgCSpec.hd_parse_args);
   in_roP segs 0 0 is the non-writable segments alone, so a contract stated at RLO = RHI = 0 gives it at any range. *)
Section ro. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable MT : ameter_ops.
Lemma hq_arodata_00 : forall rlo rhi rd, arodata_okP segs rlo rhi B rd -> arodata_okP segs 0 0 B rd.
Proof.
intros rlo rhi rd H a Hro Ho He. apply H; [|exact Ho | exact He].
destruct Hro as [Hs|Hr]; [left; exact Hs | lia].
Qed.
Lemma hq_parse_ro_mono : forall a RLO RHI akey aph apad asens gotw guard dcs,
  hd_parse_specX segs B MT a 0 0 akey aph apad asens gotw guard dcs ->
  hd_parse_specX segs B MT a RLO RHI akey aph apad asens gotw guard dcs.
Proof.
intros a RLO RHI akey aph apad asens gotw guard dcs H STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
  null P O cap ev bs Hpre Hn H10 H11 H12 Hargs.
apply (H STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs null P O cap ev bs Hpre Hn H10 H11 H12).
destruct Hargs as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & Haro & Hfrm).
exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj A9 (conj A10 (conj A11
  (conj A12 (conj A13 (conj (hq_arodata_00 RLO RHI _ Haro) Hfrm)))))))))))))).
Qed.
End ro.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.

(* the sink's overflow head of the relocated frame (AE2k.tfib_sink_head) lies above the read-only data *)
Hypothesis HOFL : 0x9d068 <= YI16.sk_ofl_head.
#[local] Instance headamp_ro_A : ro_below_ofl rsegs 0x9bc80 0x9d068.
Proof.
intros a [(s & Hs & Hw & Hr) | Hr]; [|lia].
pose proof headamp_rom_end_chk as C. rewrite forallb_forall in C. pose proof (C s Hs) as Cs.
rewrite Hw in Cs. cbn [orb] in Cs. apply Z.leb_le in Cs. lia.
Qed.

Variable B : asyms.
(* the static facts of the symbols (the start-up's const cells, zero-shadow ranges and pinned owned bytes) *)
Hypothesis HSTAT : hq_static_law rsegs B 0x9bc80 0x9d068.
(* the errno cell lies in the image, low, and the allocator's one-entry traces are in the universe *)
Hypothesis errno_low : api_env rsegs B.
Variable K : asink_syms.
Variable XL : Z -> Z.
Variables A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
(* the harness constants (the relocated frame's ACfn: A_LLVMF 0x80bc0, EV_LIB, LIVE_LIB, LLVMF_STK; by computation) *)
Hypothesis HA : A_LLVMF = HQ_ENTRY.
Hypothesis HEV : HQ_EV <= EV_LIB.
Hypothesis HSTK : HQ_RSZ + 32 + ASTACK <= LLVMF_STK.
Hypothesis HLIVE : Layout.PP_SIZE + 5440 + 30 + 27 <= LIVE_LIB.
(* the core's sink laws at the symbols (the relocated frame's AD1u.tfib_AIL) *)
Hypothesis AIL : asink_img_laws rsegs B K.
(* the lib shape's one-leaf law (headamp_lib_x_all_stmt's first premise) *)
Hypothesis LEAF : forall pl fs (Kl : lleaf -> TSet), LIBK pl fs Kl = Kl (LL 0 fs []).

(* ---------------- the runtime's facts the proved segments take ---------------- *)
(* the runtime's malloc against the allocator model, at every float state, and the model's laws *)
Hypothesis AMALLOC : forall fx' : YK11.FPState, amalloc_realizes (fx := fx') rsegs B.
Hypothesis ML : model_laws (as_universe B).
(* the code record: malloc's entry is the `jal` target 0x53060 *)
Hypothesis HPCM : pc_wrap_malloc (as_code B) = 0x53060.
(* the malloc traces at the return addresses C5 0x82e98 and C7 0x83744 are in the universe *)
Hypothesis HTRACE_C45 : forall (regsT : bvmap 5 word) (hx : hq_hcx rsegs),
  raZ (h_regs rsegs hx) = RA_LLVMF -> raZ regsT = HQ_C5 ->
  In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT (hk_ch hx)) (as_universe B).
Hypothesis HTRACE_C67 : forall (regsT : bvmap 5 word) (hx : hq_hcx rsegs),
  raZ (h_regs rsegs hx) = RA_LLVMF -> raZ regsT = HQ_C7 ->
  In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT (hk_ch hx)) (as_universe B).
(* __asan_memcpy at 0x51d0c and __asan_memset at 0x521a8, at every float state *)
Hypothesis AMEMCPY : forall fx' : YK11.FPState, aintrin_realizes (fx := fx') rsegs B OCpy 0x51d0c.
Hypothesis AMEMSET : forall fx' : YK11.FPState, aintrin_realizes (fx := fx') rsegs B OSet 0x521a8.
(* the parse (the result function 0x845b4 and its 8-byte wrapper 0x845ac) at every float state, stated at the
   read-only range RLO = RHI = 0 (the strongest form; hq_parse_ro_mono gives M04b's range) *)
Hypothesis PARSE_R : forall fx' : YK11.FPState, hd_parse_result_specX (fx := fx') rsegs B ameter_triv A_PARSE_RESULT 0 0
  (hi_akey headamp_himg_A) (hi_aph headamp_himg_A) (hi_apad headamp_himg_A) (hi_asens headamp_himg_A)
  (hi_gotw headamp_himg_A) (hi_guard headamp_himg_A) (hi_dcs headamp_himg_A).
Hypothesis PARSE_W : forall fx' : YK11.FPState, hd_parse_specX (fx := fx') rsegs B ameter_triv 0x845ac 0 0
  0x21460 0x21480 0x214a0 0x214c0 0x9cff8 0x5f7d90 headamp_A_dcs.
(* the errno cell is not in a read-only segment *)
Hypothesis ERRNO_RW : forall a, as_errno B <= a < as_errno B + 4 -> ~ in_rom rsegs a.

(* the free operation and the side stack's class-4 frame at every float state, the frame flag law, the code
   record's entries (class-4 frame 0x3ccac, free 0x5305c) *)
Hypothesis AFREE : forall fx' : YK11.FPState, afree_realizes (fx := fx') rsegs B.
Hypothesis ASM4 : forall fx' : YK11.FPState, astack_malloc_realizes (fx := fx') rsegs B 4.
Hypothesis HSM4 : pc_stack_malloc (as_code B) 4 = A_SM4.
Hypothesis FFL : frame_flag_lawP rsegs B.
Hypothesis HFREE : pc_wrap_free (as_code B) = HX_FREE.
(* the shadow-offset and use-after-return .got words and the runtime cells they name; the empty input's address *)
Hypothesis HBgot : as_got_shadow B = 0x9c370.
Hypothesis HBcell : as_shadow_cell B = 0xa4db8.
Hypothesis HGU : as_got_uar B = 0x9c3c8.
Hypothesis HUC : as_uar_cell B = 0xa4dc0.
Hypothesis HAE : 0 < A_EMPTY < kLowMemEnd.
(* the strlen wrapper at 0x41b98, at every float state *)
Hypothesis ASTRLEN : forall fx' : YK11.FPState, astrlen_realizes (fx := fx') rsegs B STRLEN_ENTRY_A.
(* the strncmp wrapper at 0x41ba4 and the strcmp wrapper at 0x41ba0, at every float state (lib/A/HPgKcA.v's texts) *)
Hypothesis STRNCMP : forall fx' : YK11.FPState,
forall ly S W regs mem md x y n (ls rs : list byte) (d : Z),
ecall_pre rsegs B ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs ->
(forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n ->
0 <= n < 2 ^ 32 ->
(0 < x /\ ~ In (Z_to_bv 8 0) ls /\
 Z.of_nat (length ls) + 1 < 2 ^ 32 /\ x + Z.of_nat (length ls) + 1 <= 2 ^ 63 /\
 garr8 rsegs (mrestrict (w_H W) mem) x (map (fun b : byte => bv_unsigned b) ls ++ [0]) /\
 src_ok rsegs W regs mem x (Z.of_nat (length ls) + 1) /\
 (forall a, x <= a <= x + Z.of_nat (length ls) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) /\
 amem_range x (Z.of_nat (length ls) + 1) /\
 range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF x (Z.of_nat (length ls) + 1) /\
 shadow_hull_vis (aview rsegs (w_H W) mem) x (Z.of_nat (length ls) + 1) /\
 (forall a, x + Z.of_nat (length ls) < a < x + Z.of_nat (length ls) - (x + Z.of_nat (length ls)) mod 8 + 8 ->
  aview rsegs (w_H W) mem a <> None)) ->
(0 < y /\ ~ In (Z_to_bv 8 0) rs /\
 Z.of_nat (length rs) + 1 < 2 ^ 32 /\ y + Z.of_nat (length rs) + 1 <= 2 ^ 63 /\
 garr8 rsegs (mrestrict (w_H W) mem) y (map (fun b : byte => bv_unsigned b) rs ++ [0]) /\
 src_ok rsegs W regs mem y (Z.of_nat (length rs) + 1) /\
 (forall a, y <= a <= y + Z.of_nat (length rs) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) /\
 amem_range y (Z.of_nat (length rs) + 1) /\
 range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF y (Z.of_nat (length rs) + 1) /\
 shadow_hull_vis (aview rsegs (w_H W) mem) y (Z.of_nat (length rs) + 1) /\
 (forall a, y + Z.of_nat (length rs) < a < y + Z.of_nat (length rs) - (y + Z.of_nat (length rs)) mod 8 + 8 ->
  aview rsegs (w_H W) mem a <> None)) ->
amem_range x (Z.of_nat (length ls) + 8) -> amem_range y (Z.of_nat (length rs) + 8) ->
StrFun.strncmp_model (ls ++ [Z_to_bv 8 0]) (rs ++ [Z_to_bv 8 0]) n = Some d ->
(forall a, in_rom rsegs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
 aview rsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom rsegs (Z_to_bv 64 a))) ->
SRr rsegs W (@cfg_at fx' rsegs A_STRNCMP regs mem md)
(fun (W' : world rsegs) (c' : config) => W' = W /\ exists regs' mem' md',
 c' = @cfg_at fx' rsegs (raZ regs) regs' mem' md' /\
 AR rsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
 (exists v : word, getr regs' 10 = v /\ (v = w64 0 <-> d = 0)) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
  aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) /\
 (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Hypothesis STRCMP : forall fx' : YK11.FPState,
  forall ly S W regs mem md x y k c1 c2,
  ecall_pre rsegs B ly S W regs mem md ->
  ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> 0 < x -> 0 < y ->
  k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 -> y + k + 1 <= 2 ^ 63 ->
  (0 <= k /\
   (forall i, 0 <= i < k -> exists b, aview rsegs (w_H W) mem (x + i) = Some b /\
                                      aview rsegs (w_H W) mem (y + i) = Some b /\ b <> 0) /\
   aview rsegs (w_H W) mem (x + k) = Some c1 /\ aview rsegs (w_H W) mem (y + k) = Some c2 /\
   (c1 <> c2 \/ c1 = 0)) ->
  src_ok rsegs W regs mem x (k + 1) -> src_ok rsegs W regs mem y (k + 1) ->
  (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
  (forall a, y <= a <= y + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
  amem_range x (k + 1) -> amem_range y (k + 1) ->
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF x (k + 1) -> shadow_hull_vis (aview rsegs (w_H W) mem) x (k + 1) ->
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF y (k + 1) -> shadow_hull_vis (aview rsegs (w_H W) mem) y (k + 1) ->
  SRr rsegs W (@cfg_at fx' rsegs A_STRCMP regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = @cfg_at fx' rsegs (raZ regs) regs' mem' md' /\
       AR rsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
       getr regs' 10 = w64 (if c1 =? c2 then 0 else if c1 <? c2 then -1 else 1) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
          aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
(* __asan_set_shadow_f5 at 0x54cd4, at every float state (lib/A/HPgX01.v's text) *)
Hypothesis ASHF5 : forall fx : YK11.FPState,
forall ly S W regs mem md cid pos q n,
ecall_pre rsegs B ly S W regs mem md -> In (cid, pos) (frames S) ->
getr regs 10 = w64 q -> getr regs 11 = w64 n -> 0 < n ->
shadow_addr (frame_addr ly cid pos) <= q -> q + n <= shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 ->
SRr rsegs W (@cfg_at fx rsegs 0x54cd4 regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = @cfg_at fx rsegs (raZ regs) regs' mem' md' /\
AR rsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall i, 0 <= i < n -> aview rsegs (w_H W) mem' (q + i) = Some 0xf5) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a)).
(* the traces of the malloc call sites C1 (E01), C3 (lib/A/HPgPostMal.v's text) and of the four free sites *)
Hypothesis HTRACE_E01 : e01_trace_stmt B RA_LLVMF.
Hypothesis HTRACE_C23 : forall (regsT : bvmap 5 word) (ch : list (Z * Z * Z)),
  raZ regsT = HQ_C3 -> (ch = [] \/ exists fp v, ch = [(fp, RA_LLVMF, v)]) ->
  In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT ch) (as_universe B).
Hypothesis HTRACE_X01 : forall c, In c [[HX_RA1]; [HX_RA1; RA_LLVMF]; [HX_RA2]; [HX_RA2; RA_LLVMF];
  [HX_RA3]; [HX_RA3; RA_LLVMF]; [HX_RA4]; [HX_RA4; RA_LLVMF]] ->
In (firstn kUnwindMax (pc_free_ra0 (as_code B) :: flat_map (fun r => if r =? pc_free_ra0 (as_code B) then [] else [r]) c))
(as_universe B).

(* the runtime and symbol facts a lane's theorem asks, from this Section's hypotheses and the kernel *)
Local Ltac hq_rt0 := first
  [ assumption | exact errno_low | exact headamp_A_relro_img | apply ameter_triv_laws | apply AR_laws_ok
  | apply AMEMSET | apply AMEMCPY | apply ASTRLEN | apply AMALLOC | apply AFREE | apply ASM4
  | apply STRNCMP | apply STRCMP | apply PARSE_R | apply PARSE_W | (apply hq_parse_ro_mono; apply PARSE_W) | lia
  | (assert (8 <= EV_LIB) by exact HEV; lia)
  | (assert (0x1e0 + 32 + ASTACK <= LLVMF_STK) by exact HSTK; lia) ].
Local Ltac hq_rt := first
  [ hq_rt0
  | (intros ?fy; apply HPgChk_check_object.hd_check_object_A; hq_rt0)
  | (intros ?fy; apply HPgChk_check_cells.hd_check_cells_A; hq_rt0)
  | (intros ?fy; apply HPgChk_check_keys.hd_check_keys_A; hq_rt0)
  | (intros ?fy; apply HPgChk_check_refusal.hd_check_refusal_A; hq_rt0)
  | (intros ?fy; apply HPgChk_check_plain.hd_check_plain_A; hq_rt0)
  | (intros ?fy; apply HPgChk_check_no_overrun.hd_check_no_overrun_A; hq_rt0)
  | (intros ?fy; apply HPgChk_check_count.hd_check_count_A; hq_rt0)
  | (intros ?fy; apply HPgChk_check_cells_valid.hd_check_cells_valid_A; hq_rt0) ].
(* ---------------- the segments, each from its lane's theorem ---------------- *)
Lemma hqA_E01 : hq_S_E01_stmt rsegs B 0x9bc80 0x9d068 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof. apply HPgE01.headamp_E01_ok; hq_rt. Qed.
Lemma hqA_build : headamp_build_contract rsegs B ameter_triv headamp_himg_A 0x9bc80 0x9d068.
Proof.
apply headamp_build_holds.
- apply HPgW3a.hs_piece_W3a; hq_rt.
- apply HPgW3b.hs_piece_W3b_hdr; hq_rt.
- apply HPgW3b.hs_piece_W3b_b7; hq_rt.
- apply HPgW3bPre.hs_piece_W3b_pre; hq_rt.
- apply HPgProp.pa_piece_sel; hq_rt.
- apply HPgProp.pa_piece_int7; hq_rt.
- apply HPgProp.pa_piece_key; hq_rt.
- apply HPgProp.pa_piece_latch; hq_rt.
- apply HPgW5IntP.w5_piece_int; hq_rt.
- apply HPgW5OpenP.w5_piece_open; hq_rt.
- apply HPgW5CloseP.w5_piece_close; hq_rt.
- apply HPgW6a.w6_disp; hq_rt.
- apply HPgW6a.w6_cases; hq_rt.
- apply HPgW6b.hs_piece_W6b; hq_rt.
- apply HPgW6c.w6c_piece_A; hq_rt.
- apply HPgEnt0.r7_piece_W7a; hq_rt.
- apply HPgW7b.w7b_piece_A; hq_rt.
- apply HPgW8.hs_piece_W8; hq_rt.
- apply HPgPostTop.w10_post; hq_rt.
- apply HPgPostCorr.w10_corr; hq_rt.
- apply HPgPostReq.w10_req; hq_rt.
Qed.
Lemma hqA_C23 : hq_S_C23_stmt rsegs B 0x9bc80 0x9d068 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof. apply HPgPostMal.hq_A_S_C23; hq_rt. Qed.
Lemma hqA_dup : headamp_dup_contract rsegs B ameter_triv headamp_himg_A 0x9bc80 0x9d068.
Proof. apply headamp_A_dup_holds; hq_rt. Qed.
Lemma hqA_C45 : hq_S_C45_stmt rsegs B 0x9bc80 0x9d068 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof. apply hq_A_S_C45; hq_rt. Qed.
Lemma hqA_check : headamp_check_contract rsegs B ameter_triv headamp_himg_A 0x9bc80 0x9d068.
Proof.
apply headamp_check_holds.
- apply HPgM3aHead.hq_A_piece_M3a_head; hq_rt.
- apply HPgM3aSetup.hq_A_piece_M3a_setup; hq_rt.
- apply HPgM3bPair.hb_pair_A; hq_rt.
- apply HPgM3bScan.hb_scan_A; hq_rt.
- apply HPgM3bLatch.hb_latch_A; hq_rt.
- apply HPgM3bRefuse.hb_refuse_A; hq_rt.
- apply HPgKcA.hk_key_A; hq_rt.
- apply HPgM3dA.headamp_m3d_value_A; hq_rt.
- apply HPgM3eCell.he_cell; hq_rt.
- apply HPgM3eRc.he_rc; hq_rt.
- apply hq_A_piece_M24_first; hq_rt.
Qed.
Lemma hqA_C67 : hq_S_C67_stmt rsegs B 0x9bc80 0x9d068 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof. apply hq_A_S_C67; hq_rt. Qed.
Lemma hqA_first : forall fx' : YK11.FPState,
  headamp_first_contract (fx := fx') rsegs B ameter_triv headamp_himg_A 0x9bc80 0x9d068.
Proof. intros fx'. apply headamp_A_first_holds; hq_rt. Qed.
Lemma hqA_plain : forall fx' : YK11.FPState,
  headamp_plain_contract (fx := fx') rsegs B ameter_triv headamp_himg_A 0x9bc80 0x9d068.
Proof. intros fx'. apply headamp_A_plain_holds; hq_rt. Qed.
Lemma hqA_X01f : hq_S_X01f_stmt rsegs B 0x9bc80 0x9d068 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof. apply HPgX01.hx_S_X01f; hq_rt. Qed.
Lemma hqA_X01r : hq_S_X01r_stmt rsegs B 0x9bc80 0x9d068 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof. apply HPgX01.hx_S_X01r; hq_rt. Qed.

Theorem headamp_lib_x_A : hd_lib_contract_x rsegs B ameter_triv K XL XL 0x9bc80 0x9d068
  A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
eapply (headamp_lib_x rsegs B).
all: first
  [ exact headamp_A_relro_img | exact headamp_ro_A | exact HSTAT | exact errno_low
  | exact hqA_E01 | exact hqA_build | exact hqA_C23 | exact hqA_dup | exact hqA_C45 | exact hqA_check
  | exact hqA_C67 | exact hqA_first | exact hqA_plain | exact hqA_X01f | exact hqA_X01r | eassumption ].
Qed.
End i.

Print Assumptions headamp_lib_x_A.

(* ============================ the final statement at image A's own record ============================ *)
(* HPgLib.headamp_lib_x_all_stmt's contract at the relocated frame's record: the symbols AD2l.TfibB, the
   sink AE2k.tfib_K with its overflow head AE2k.tfib_sink_head, the segments AB1v.tfibsegs (Img0.rsegs: both are
   images.Asan.M.loaded_segments), XL0, the read-only range RO_LO .. RO_HI and ACfn's constants. The image facts
   of headamp_lib_x_A are discharged here (the record's fields, the constants, the trace universe ACej.Tfib_universe
   by computation; the sink laws AD1u.tfib_AIL; the model laws YG05.model_laws_ok; the frame flag law from AR's
   laws and ACeg.tfib_img_cover; __asan_memset / __asan_memcpy by AE2r / AE2q; the class-4 side stack by
   RtSM4.stack_malloc4_contract; the errno cell by ACeg.tl_env; the static facts of the symbols by
   HPgStatA.hq_static_A; the strlen / strncmp / strcmp wrappers and __asan_set_shadow_f5 by Rt/Strlen.v
   strlen_icpt_contract, HPgWrapNcmp.hd_astrncmp_TfibB, Rt/Strcmp.v strcmp_icpt_contract and Rt/SetShadow.v
   box_set_shadow_f5; the parse by HPgParse.hd_parse_result_A00 / hd_parse_A00 with the three hole contracts
   HPgWrapNcmpH.hd_astrncmp_hole_TfibB, Rt/RtLStrtolH.v hd_strtol_hole and Rt/StrcmpHole.v strcmp_hole_contract). *)
Lemma hq_rsegs_tfib : rsegs = AB1v.tfibsegs.
Proof. reflexivity. Qed.

Lemma hqF_TL : ACeg.TfibLib AD2l.TfibB.
Proof.
constructor; try reflexivity.
- cbn [as_errno AD2l.TfibB]. unfold AF0m.TFIB_ERRNO, kLowMemEnd. lia.
- cbn [as_errno AD2l.TfibB]. unfold AF0m.TFIB_ERRNO.
  assert (E : existsb (fun sg => (Z.of_N (seg_base sg) <=? 0x5d7cac) &&
    (0x5d7cb0 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) AB1v.tfibsegs = true) by (vm_compute; reflexivity).
  intros a Ha. apply existsb_exists in E as (sg & Hin & Hb). apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. exists sg. split; [exact Hin | lia].
- intros a [].
- cbn [as_gp AD2l.TfibB]. unfold AF0m.TFIB_GP. lia.
Qed.

Lemma hqF_api : api_env rsegs AD2l.TfibB.
Proof. exact (ACeg.tl_env AD2l.TfibB hqF_TL). Qed.

Lemma hqF_errno_rw : forall a, as_errno AD2l.TfibB <= a < as_errno AD2l.TfibB + 4 -> ~ in_rom rsegs a.
Proof.
intros a Ha (s & Hs & Hw & Hr). cbn [as_errno AD2l.TfibB] in Ha. unfold AF0m.TFIB_ERRNO in Ha.
pose proof headamp_rom_end_chk as C. rewrite forallb_forall in C. pose proof (C s Hs) as Cs.
rewrite Hw in Cs. cbn [orb] in Cs. apply Z.leb_le in Cs. lia.
Qed.

Lemma hqF_ml : model_laws (as_universe AD2l.TfibB).
Proof. exact (YG05.model_laws_ok _ ACej.Tfib_universe_ok). Qed.

(* the two malloc-call traces at a call site whose return address is X: [ra0; X] and [ra0; X; R] *)
Lemma hq_ct0 : forall pc0 X R (regsT : bvmap 5 word) (ch : list (Z * Z * Z)) U,
  raZ regsT = X -> (ch = [] \/ exists fp v, ch = [(fp, R, v)]) ->
  In (unwind_of_chain pc0 [(0, X, 0)]) U -> In (unwind_of_chain pc0 [(0, X, 0); (0, R, 0)]) U ->
  In (call_trace0 pc0 regsT ch) U.
Proof.
intros pc0 X R regsT ch U HX Hch H1 H2. unfold call_trace0.
destruct Hch as [->|(fp & v & ->)]; unfold unwind_of_chain in *; cbn [flat_map] in *; rewrite HX; assumption.
Qed.

Ltac hq_univ := apply AD2l.In_of_existsb; vm_compute; reflexivity.

Lemma hq_hk_ch : forall (hx : hq_hcx rsegs), raZ (h_regs rsegs hx) = ACfn.RA_LLVMF ->
  hk_ch hx = [] \/ exists fp v, hk_ch hx = [(fp, ACfn.RA_LLVMF, v)].
Proof.
intros hx H. unfold hk_ch. destruct (_ <? _); [right; rewrite <- H; eexists; eexists; reflexivity | left; reflexivity].
Qed.

Section fin. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Local Notation TB := AD2l.TfibB.
#[local] Existing Instance AE2k.tfib_sink_head.

Lemma hqF_ofl : 0x9d068 <= @YI16.sk_ofl_head AE2k.tfib_sink_head.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma hqF_AIL : asink_img_laws rsegs TB AE2k.tfib_K.
Proof. first [exact (AD1u.tfib_AIL TB AD2l.TfibB_syms (AR_laws_ok _ _)) | exact (AD1u.tfib_AIL TB AD2l.TfibB_syms)]. Qed.

Lemma hqF_asm4 : forall fx' : YK11.FPState, astack_malloc_realizes (fx := fx') rsegs TB 4.
Proof. intros fx'. exact (RtSM4.stack_malloc4_contract TB (AR_laws_ok _ _) AD2l.TfibB_syms). Qed.

Lemma hqF_amemset : forall fx' : YK11.FPState, aintrin_realizes (fx := fx') rsegs TB OSet 0x521a8.
Proof.
intros fx' ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
exact (AE2r.asan_memset_realizes TB (AR_laws_ok _ _) AD2l.TfibB_syms ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd
  Hdn Hdst Hra Hhull Ham).
Qed.

Lemma hqF_amemcpy : forall fx' : YK11.FPState, aintrin_realizes (fx := fx') rsegs TB OCpy 0x51d0c.
Proof.
intros fx' ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc.
exact (AE2q.asan_memcpy_realizes TB (AR_laws_ok _ _) AD2l.TfibB_syms ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd
  Hdn Hdst Ham Hra Hhull Hsrc).
Qed.

(* the frame's flag word is present, owned, an application address off the image [cgif ACed.v:133 tfibX_FFL] *)
Lemma hqF_ffl : frame_flag_lawP rsegs TB.
Proof.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ (AR_laws_ok rsegs TB) ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ (AR_laws_ok rsegs TB) ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (ACeg.tfib_img_cover ly S md L) as [C1 C2].
unfold ACeg.TFIB_IMG_LO, ACeg.TFIB_IMG_END in C1, C2.
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

Lemma hqF_tr_e01 : e01_trace_stmt TB ACfn.RA_LLVMF.
Proof. intros regsT ch Hra Hch. apply (hq_ct0 _ _ _ regsT ch _ Hra Hch); hq_univ. Qed.
Lemma hqF_tr_c23 : forall (regsT : bvmap 5 word) (ch : list (Z * Z * Z)),
  raZ regsT = HQ_C3 -> (ch = [] \/ exists fp v, ch = [(fp, ACfn.RA_LLVMF, v)]) ->
  In (call_trace0 (pc_malloc_ra0 (as_code TB)) regsT ch) (as_universe TB).
Proof. intros regsT ch Hra Hch. apply (hq_ct0 _ _ _ regsT ch _ Hra Hch); hq_univ. Qed.
Lemma hqF_tr_c45 : forall (regsT : bvmap 5 word) (hx : hq_hcx rsegs),
  raZ (h_regs rsegs hx) = ACfn.RA_LLVMF -> raZ regsT = HQ_C5 ->
  In (call_trace0 (pc_malloc_ra0 (as_code TB)) regsT (hk_ch hx)) (as_universe TB).
Proof. intros regsT hx Hh Hra. apply (hq_ct0 _ _ _ regsT _ _ Hra (hq_hk_ch hx Hh)); hq_univ. Qed.
Lemma hqF_tr_c67 : forall (regsT : bvmap 5 word) (hx : hq_hcx rsegs),
  raZ (h_regs rsegs hx) = ACfn.RA_LLVMF -> raZ regsT = HQ_C7 ->
  In (call_trace0 (pc_malloc_ra0 (as_code TB)) regsT (hk_ch hx)) (as_universe TB).
Proof. intros regsT hx Hh Hra. apply (hq_ct0 _ _ _ regsT _ _ Hra (hq_hk_ch hx Hh)); hq_univ. Qed.
Lemma hqF_tr_x01 : forall c, In c [[HX_RA1]; [HX_RA1; ACfn.RA_LLVMF]; [HX_RA2]; [HX_RA2; ACfn.RA_LLVMF];
  [HX_RA3]; [HX_RA3; ACfn.RA_LLVMF]; [HX_RA4]; [HX_RA4; ACfn.RA_LLVMF]] ->
  In (firstn kUnwindMax (pc_free_ra0 (as_code TB) :: flat_map (fun r => if r =? pc_free_ra0 (as_code TB) then [] else [r]) c))
  (as_universe TB).
Proof.
intros c Hc. repeat (destruct Hc as [<-|Hc]; [hq_univ|]). destruct Hc.
Qed.

(* ---------------- the parse (lib/A/HPgParse.v) at TfibB ---------------- *)
(* the parse's premises at TfibB: the meter's laws, the .got word 0x9c370 and the cell 0xa4db8, the errno cell
   (place: hqF_api; address 0x5d7cac), and the strncmp / strtol / strcmp contracts in the hole form *)
Local Ltac hqF_parse_rt := first
  [ apply ameter_triv_laws | reflexivity | exact hqF_api
  | (intros ? ?; exact HPgWrapNcmpH.hd_astrncmp_hole_TfibB)
  | (intros ? ?; exact (RtLStrtolH.hd_strtol_hole TB AD2l.TfibB_syms))
  | (intros ? ?; exact (StrcmpHole.strcmp_hole_contract TB (AR_laws_ok _ _) AD2l.TfibB_syms)) ].

Lemma hqF_parse_R : forall fx' : YK11.FPState, hd_parse_result_specX (fx := fx') rsegs TB ameter_triv A_PARSE_RESULT 0 0
  (hi_akey headamp_himg_A) (hi_aph headamp_himg_A) (hi_apad headamp_himg_A) (hi_asens headamp_himg_A)
  (hi_gotw headamp_himg_A) (hi_guard headamp_himg_A) (hi_dcs headamp_himg_A).
Proof. intros fx'. apply HPgParse.hd_parse_result_A00; hqF_parse_rt. Qed.

Lemma hqF_parse_W : forall fx' : YK11.FPState, hd_parse_specX (fx := fx') rsegs TB ameter_triv 0x845ac 0 0
  0x21460 0x21480 0x214a0 0x214c0 0x9cff8 0x5f7d90 headamp_A_dcs.
Proof. intros fx'. apply HPgParse.hd_parse_A00; hqF_parse_rt. Qed.

Theorem headamp_lib_x_all_fx :
  (forall pl fs (K : lleaf -> TSet), LIBK pl fs K = K (LL 0 fs [])) ->
  (forall fx' : YK11.FPState, @afree_realizes fx' rc AB1v.tfibsegs TB) ->
  (forall fx' : YK11.FPState, @amalloc_realizes fx' rc AB1v.tfibsegs TB) ->
  @HPgLib.headamp_lib_contract_x fx rc LS TB ameter_triv HPgLib.XL0 HPgLib.XL0 HPgLib.RO_LO HPgLib.RO_HI.
Proof.
intros LEAF AFREE AMALLOC. unfold HPgLib.headamp_lib_contract_x, HPgLib.RO_LO, HPgLib.RO_HI.
eapply (@headamp_lib_x_A fx rc AE2k.tfib_sink_head LS).
all: first
  [ exact hqF_ofl | exact (HPgStatA.hq_static_A TB AD2l.TfibB_syms) | exact hqF_api
  | reflexivity
  | (apply Z.leb_le; vm_compute; reflexivity)
  | (split; apply Z.ltb_lt; vm_compute; reflexivity)
  | exact hqF_AIL | exact LEAF | exact AMALLOC | exact AFREE | exact hqF_ml | exact hqF_errno_rw
  | exact hqF_asm4 | exact hqF_amemset | exact hqF_amemcpy | exact hqF_ffl
  | exact hqF_tr_e01 | exact hqF_tr_c23 | exact hqF_tr_c45 | exact hqF_tr_c67 | exact hqF_tr_x01
  | (intros ?fy; exact (Strlen.strlen_icpt_contract TB (AR_laws_ok _ _) AD2l.TfibB_syms))
  | (intros ?fy; exact HPgWrapNcmp.hd_astrncmp_TfibB)
  | (intros ?fy; exact (Strcmp.strcmp_icpt_contract TB (AR_laws_ok _ _) AD2l.TfibB_syms))
  | (intros ?fy; exact (SetShadow.box_set_shadow_f5 TB (AR_laws_ok _ _) AD2l.TfibB_syms))
  | exact hqF_parse_R | exact hqF_parse_W ].
Qed.
End fin.

Print Assumptions headamp_lib_x_all_fx.

(* ============================ HPgLib's final statement, closed ============================ *)
Theorem headamp_lib_x_all : HPgLib.headamp_lib_x_all_stmt.
Proof.
intros rc LS LEAF AFREE AMALLOC fx. exact (@headamp_lib_x_all_fx fx rc LS LEAF AFREE AMALLOC).
Qed.

Print Assumptions headamp_lib_x_all.
