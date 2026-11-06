(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_knock's ASan image (fuzz_knock.asan, sha256
   61768cf4739b7641c99c825dde45eddafc55b601d41109555be0272fc7ca4118) from proofs/cgif/cgif_file_fuzzer/lib/A at
   c8557374ad2e: ACfn.v lines 22-72 (the contract tfib_lib_contract_x / _all), ACfj.v lines 180-255 (its proof
   tfib_lib_x_body / tfib_lib_x, with lx_leaf_fail's post), ACfh.v lines 29-50 and 153-164 (ajournal_fp_nil,
   srz_enter, ajournal_closed_io, ajournal_nil_io) and ACfi.v lines 56-140 (XL0, the links,
   tfib_lib_x_closed / tfib_lib_x_all), with their module paths changed. rule 24: no function proved (a port of the
   released cgif_file_fuzzer program part). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_knock/lib/A/APgLib.v, with its module paths and module names changed; 246 of its 308 lines of code are new or changed and 245 lines of the source are left out. *)
(* The program side of fuzz_codec's image-B closing (fuzz_codec.asan-ubsan), the twin of lib/A/Prog/CPgClose.v: the
   entry function's contract codec_lib_contract_x (lib/A/Prog/CPgMainC.v, image-independent) at the start-up record
   TfibB (lib/AU/YD2l.v), ameter_triv, the sink tfib_K (lib/AU/YE2k.v) and the read window CB_RLO .. CB_RHI, from the
   program walks, and its bridge to the core's text lib/AU/YCfn.v tfib_lib_contract_x_all, which lib/AU/YD1q.v takes.

   Discharged here, at TfibB: the kit's laws and the start-up facts as in lib/A/Prog/CPgClose.v, with image B's
   modules (lib/AU/APgImgLink.v tfibX_lib, lib/AU/YD1u.v tfib_AIL, lib/AU/CodecStartupClose.v codec_GM_TfibB /
   codec_IV_TfibB, lib/AU/Prog/CPgWalkRoU.v cpw_rows_free_syms, lib/AU/APgImg.v codec_asanubsan_relro_img); the
   frame-flag law is proved in lib/AU/YCbqU.v's form (image B's bounds) and turned into lib/Reusable/YCbq.v's, which
   the contracts state, by lib/AU/Prog/CPgWalkU.v lde_ffl_of_U. The runtime contracts: side-stack frames of class
   0 / 1 / 3 (lib/AU/Rt/StackMalloc0.v, lib/AU/YF0s.v, lib/AU/Rt/StackMalloc3.v), __asan_memcpy 0x51ae8 /
   __asan_memset 0x51f84 (lib/AU/YE2q.v / YE2r.v), the compare wrappers 0x42430 / 0x42424 (lib/AU/YE2s.v /
   lib/AU/Rt/Strcmp.v), the shadow fill with 0xf5 0x54ab0 (lib/AU/Rt/SetShadow.v).

   The entry function's walk at image B is lib/AU/Prog/codec_bmain_holds.v codec_bmain_holds, whose statement is
   codecU_bmain_T below (the kit's laws, the runtime contracts, the start-up facts and the contracts of its 24
   callees give codec_lib_contract_x; image B's entry function calls owe_sysex, which image A inlines). It and every
   callee walk are applied here with every premise discharged: no premise stays open. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0s YK14 YK15 YK18 YP09 YI00 YI04 YI08 YI09 YI16 YN3v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG05 YG0q YG0t YCbp.
From OSSVerify.libdiginet.fuzz_codec.images Require AsanUbsan.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCeh YCfm YF0m YD2l.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require YImgTopU YCbqU YE2k YD1u YCfn YE2q YE2r YE2s YF0s APgImg APgImgLink CodecStartupClose.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Rt Require Import SetShadowDef.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Rt Require StrcmpDef StackMalloc0 StackMalloc3 Strcmp SetShadow.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import
CPgBaseU CPgEncU CPgChkU CodecRo CodecGlobs CPgWalkU CPgWalkRoU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require
check_bytes_B check_personality_B check_range_B check_refusal_B check_text_masks_B check_text_seg7_B
diginet_button_encode_B diginet_counter_leds_encode_B diginet_counter_text_B diginet_fader_encode_B
diginet_jog_encode_B diginet_meter_mask_B diginet_meter_segments_B diginet_personality_from_name_B
diginet_personality_of_B diginet_ring_dot_B diginet_ring_fill_B diginet_scribble_text_B diginet_seg7_B
diginet_strip_leds_encode_B diginet_touch_encode_B diginet_vpot_encode_B leds_encode_B owed_seg7_B text_arg_B
diginet_counter_encode_B diginet_ring_encode_B diginet_scribble_encode_B owe_sysex_B diginet_sysex_encode_B check_text_scribble_B owed_counter_text_B diginet_meter_encode_B check_text_counter_B codec_bmain_holds.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ============================== the entry function's walk at image B, as a premise ==============================
   The form of lib/A/Prog/CPgClose.v codec_amain_stmt at image B's entries: the same kit laws, runtime contracts at
   image B's entries, the start-up facts, and the contracts of the 24 callees of image B's entry function (image A's
   23 and owe_sysex 0x84e8c). This Section names no sink head instance. *)
Section T. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variables XM_LIB XN_LIB : Z -> Z.
Definition codecU_bmain_stmt : Prop :=
  ameter_laws MT -> ameter_fs_laws MT -> TfibLib B -> AR_laws tfibsegs B -> model_laws (as_universe B) ->
  asink_img_laws tfibsegs B K -> (forall n, 0 <= XN_LIB n) ->
  (forall pl fs (Kl : lleaf -> TSet), LIBK pl fs Kl = Kl (LL 0 fs [])) ->
  astack_malloc_realizes tfibsegs B 3 -> stack_malloc_progressP B -> astack_free_law tfibsegs B ->
  frame_flag_lawP tfibsegs B ->
  aintrin_realizes tfibsegs B OSet 0x51f84 -> aintrin_realizes tfibsegs B OCpy 0x51ae8 ->
  aset_shadow_realizes tfibsegs B 0x54ab0 0xf5 ->
  globs_marked tfibsegs B CODEC_GLOBS -> img_shadow_vis tfibsegs B -> cpw_rows_free B CB_ROSTRS ->
  cdcU_check_pers_specX tfibsegs B MT CB_RLO CB_RHI CB_PERS CB_ROSTRS 0x8391c ->
  cdcU_pers_of_specX tfibsegs B MT 0x8513c CB_PERS ->
  cdcU_text_arg_specX tfibsegs B MT 0x83ba0 ->
  cdcU_check_seg7_specX tfibsegs B MT CB_RLO CB_RHI CB_SEG7 CB_GLYPH CB_ROSTRS 0x84148 ->
  cdcU_check_text_counter_specX tfibsegs B MT CB_RLO CB_RHI CB_SEG7 CB_GLYPH CB_ROSTRS 0x841c4 ->
  cdcU_owed_counter_text_specX tfibsegs B MT CB_RLO CB_RHI CB_GLYPH CB_ROSTRS 0x84474 ->
  cdcU_check_text_scribble_specX tfibsegs B MT 0x83dbc ->
  cdcU_check_masks_specX tfibsegs B MT 0x84974 ->
  cdcU_check_refusal_specX tfibsegs B MT 0x84bc4 ->
  cdcU_check_range_specX tfibsegs B MT 0x84c84 ->
  cdcU_check_bytes_specX tfibsegs B MT 0x84d40 ->
  cdcU_fader_specX tfibsegs B MT 0x8540c ->
  cdcU_button_specX tfibsegs B MT 0x855dc ->
  cdcU_touch_specX tfibsegs B MT 0x85744 ->
  cdcU_vpot_specX tfibsegs B MT 0x85914 ->
  cdcU_jog_specX tfibsegs B MT 0x85a8c ->
  cdcU_sysex_specX tfibsegs B MT 0x85174 ->
  cdcU_ring_specX tfibsegs B MT 0x85c1c ->
  cdcU_meter_specX tfibsegs B MT 0x85f4c ->
  cdcU_sleds_specX tfibsegs B MT 0x861d0 ->
  cdcU_cleds_specX tfibsegs B MT 0x8648c ->
  cdcU_scribble_specX tfibsegs B MT 0x866c4 ->
  cdcU_counter_specX tfibsegs B MT 0x86ee4 ->
  cdcU_owe_sysex_specX tfibsegs B MT 0x84e8c ->
  codec_lib_contract_x tfibsegs B MT K XM_LIB XN_LIB CB_RLO CB_RHI A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
End T.
Definition codecU_bmain_T : Prop :=
  forall (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (ROB : @ro_tfa_below_ofl SK) (LS : lib_shape)
    (B : asyms) (MT : ameter_ops) (K : asink_syms) (XM_LIB XN_LIB : Z -> Z),
  @codecU_bmain_stmt fx rc SK LS B MT K XM_LIB XN_LIB.

(* The walk is on the branch: lib/AU/Prog/codec_bmain_holds.v states it with `Proof using All`, so its type is
   codecU_bmain_T. *)
Lemma codecU_bmain_T_holds : codecU_bmain_T.
Proof. exact @codec_bmain_holds.codec_bmain_holds. Qed.

(* ============================== from here on, the image's sink head ============================== *)
#[local] Existing Instance YE2k.tfib_sink_head.
Definition XL0 : Z -> Z := fun _ => 0.
Lemma XL0_HXL : forall n, 0 <= XL0 n.
Proof. intros n. unfold XL0. lia. Qed.

(* in_ro_tfa lies below the sink head A_ofl_head 0x5fa448 (lib/AU/YE2k.v): the read-only PT_LOADs end below the
   read window, which is 0x9dba0 .. 0x9f128 (lib/AU/YCeh.v). *)
#[local] Instance codecU_ROB : @ro_tfa_below_ofl YE2k.tfib_sink_head.
Proof.
intros a [(sg & Hs & Hw & Hr) | Hr]; cbn [YI16.sk_ofl_head YE2k.tfib_sink_head]; unfold YE2k.A_ofl_head; [|lia].
assert (E : tfibsegs = [AsanUbsan.AsanUbsan_segment_000; AsanUbsan.AsanUbsan_segment_001;
  AsanUbsan.AsanUbsan_segment_002; AsanUbsan.AsanUbsan_segment_003]) by reflexivity.
rewrite E in Hs. destruct Hs as [<-|[<-|[<-|[<-|[]]]]]; vm_compute in Hw; try discriminate Hw;
lazymatch type of Hr with ?lo <= a < ?hi =>
let l := eval vm_compute in lo in let h := eval vm_compute in hi in change (l <= a < h) in Hr end; lia.
Qed.

(* The program walks still to land at image B, each as its contract at TfibB / ameter_triv. *)

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- the kit's laws and the start-up facts at TfibB ---- *)
Lemma cpcU_MTL : ameter_laws ameter_triv.
Proof. exact ameter_triv_laws. Qed.
Lemma cpcU_MTF : ameter_fs_laws ameter_triv.
Proof. exact ameter_triv_fs_laws. Qed.
Lemma cpcU_TL : TfibLib TfibB.
Proof. exact APgImgLink.tfibX_lib. Qed.
Lemma cpcU_LAWS : AR_laws tfibsegs TfibB.
Proof. exact (AR_laws_ok tfibsegs TfibB). Qed.
Lemma cpcU_HB : TfibSyms TfibB.
Proof. exact TfibB_syms. Qed.
Lemma cpcU_ML : model_laws (as_universe TfibB).
Proof. exact (model_laws_ok (as_universe TfibB) (ts_universe TfibB TfibB_syms)). Qed.
Lemma cpcU_AIL : asink_img_laws tfibsegs TfibB YE2k.tfib_K.
Proof. exact (YD1u.tfib_AIL TfibB TfibB_syms). Qed.
Lemma cpcU_SMP : stack_malloc_progressP TfibB.
Proof. intros s cid W Hc Hn. exact (stack_malloc_progress (as_universe TfibB) s cid W Hc Hn). Qed.
Lemma cpcU_ASF : astack_free_law tfibsegs TfibB.
Proof. exact (astack_free_law_ok tfibsegs TfibB). Qed.
Lemma cpcU_FFL_U : YCbqU.frame_flag_lawP tfibsegs TfibB.
Proof.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ cpcU_LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ cpcU_LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (tfib_img_cover ly S md L) as [C1 C2].
unfold TFIB_IMG_LO, TFIB_IMG_END, YImgTopU.IMG_LO, YImgTopU.IMG_TOP in C1, C2.
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil].
unfold YCbqU.zone2, YCbqU.off_img, YImgTopU.IMG_LO, YImgTopU.IMG_TOP, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma cpcU_FFL : frame_flag_lawP tfibsegs TfibB.
Proof. exact (lde_ffl_of_U TfibB cpcU_FFL_U). Qed.
Lemma cpcU_GM : globs_marked tfibsegs TfibB CODEC_GLOBS.
Proof. exact (CodecStartupClose.codec_GM_TfibB tfibsegs). Qed.
Lemma cpcU_IV : img_shadow_vis tfibsegs TfibB.
Proof. exact (CodecStartupClose.codec_IV_TfibB tfibsegs). Qed.
Lemma cpcU_RF : cpw_rows_free TfibB CB_ROSTRS.
Proof. exact (cpw_rows_free_syms TfibB TfibB_syms). Qed.
Lemma cpcU_RELRO : forall a, CB_RLO <= a < CB_RHI -> in_img tfibsegs a.
Proof. exact APgImg.codec_asanubsan_relro_img. Qed.

(* ---- the runtime contracts at TfibB ---- *)
Lemma cpcU_ASM0 : astack_malloc_realizes tfibsegs TfibB 0.
Proof. exact (StackMalloc0.stack_malloc0_contract TfibB cpcU_LAWS TfibB_syms). Qed.
Lemma cpcU_ASM1 : astack_malloc_realizes tfibsegs TfibB 1.
Proof. exact (YF0s.stack_malloc1_contract TfibB cpcU_LAWS TfibB_syms). Qed.
Lemma cpcU_ASM3 : astack_malloc_realizes tfibsegs TfibB 3.
Proof. exact (StackMalloc3.stack_malloc3_contract TfibB cpcU_LAWS TfibB_syms). Qed.
Lemma cpcU_AMEMCPY : aintrin_realizes tfibsegs TfibB OCpy 0x51ae8.
Proof. exact (YE2q.asan_memcpy_realizes TfibB cpcU_LAWS TfibB_syms). Qed.
Lemma cpcU_AMEMSET : aintrin_realizes tfibsegs TfibB OSet 0x51f84.
Proof.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL _.
exact (YE2r.asan_memset_realizes TfibB cpcU_LAWS TfibB_syms ly S W regs mem md d x n HPRE G10 G11 G12
  Hn Hd Hdn HDST HRA HHULL HAM).
Qed.
Lemma cpcU_ABCMP : abcmp_realizes tfibsegs TfibB 0x42430.
Proof. exact (YE2s.bcmp_icpt_contract TfibB cpcU_LAWS TfibB_syms). Qed.
Lemma cpcU_ASTRCMP : StrcmpDef.astrcmp_realizes tfibsegs TfibB 0x42424.
Proof. exact (Strcmp.strcmp_icpt_contract TfibB cpcU_LAWS TfibB_syms). Qed.
Lemma cpcU_ASSF5 : aset_shadow_realizes tfibsegs TfibB 0x54ab0 0xf5.
Proof. exact (SetShadow.ident_set_shadow_f5 TfibB cpcU_LAWS TfibB_syms). Qed.

Ltac cpcU_fact :=
  first [ exact cpcU_MTL | exact cpcU_MTF | exact cpcU_TL | exact cpcU_LAWS | exact cpcU_HB | exact cpcU_ML
        | exact cpcU_AIL | exact cpcU_SMP | exact cpcU_ASF | exact cpcU_FFL | exact cpcU_FFL_U | exact cpcU_GM
        | exact cpcU_IV | exact cpcU_RF | exact cpcU_RELRO | exact cpcU_ASM0 | exact cpcU_ASM1 | exact cpcU_ASM3
        | exact cpcU_AMEMCPY | exact cpcU_AMEMSET | exact cpcU_ABCMP | exact cpcU_ASTRCMP | exact cpcU_ASSF5
        | exact XL0_HXL ].

(* ---- the callee contracts whose walks are on this branch, at TfibB / ameter_triv ---- *)
Lemma cpcU_pers_of : cdcU_pers_of_specX tfibsegs TfibB ameter_triv 0x8513c CB_PERS.
Proof. eapply diginet_personality_of_B.diginet_personality_of_B_holds; cpcU_fact. Qed.
Lemma cpcU_from_name : cdcU_from_name_specX tfibsegs TfibB ameter_triv CB_RLO CB_RHI CB_PERS CB_ROSTRS 0x85090.
Proof. eapply diginet_personality_from_name_B.diginet_personality_from_name_B_holds; cpcU_fact. Qed.
Lemma cpcU_check_pers : cdcU_check_pers_specX tfibsegs TfibB ameter_triv CB_RLO CB_RHI CB_PERS CB_ROSTRS 0x8391c.
Proof.
eapply check_personality_B.check_personality_B_holds; first [cpcU_fact | exact cpcU_pers_of | exact cpcU_from_name].
Qed.
Lemma cpcU_text_arg : cdcU_text_arg_specX tfibsegs TfibB ameter_triv 0x83ba0.
Proof. eapply text_arg_B.text_arg_B_holds; cpcU_fact. Qed.
Lemma cpcU_seg7 : forall RLO RHI, cdcU_seg7_specX tfibsegs TfibB ameter_triv RLO RHI CB_SEG7 0x86978.
Proof. intros RLO RHI. eapply diginet_seg7_B.diginet_seg7_B_holds; cpcU_fact. Qed.
Lemma cpcU_owed_seg7 : cdcU_owed_seg7_specX tfibsegs TfibB ameter_triv CB_RLO CB_RHI CB_GLYPH CB_ROSTRS 0x84a54.
Proof. eapply owed_seg7_B.owed_seg7_B_holds; cpcU_fact. Qed.
Lemma cpcU_check_seg7 : cdcU_check_seg7_specX tfibsegs TfibB ameter_triv CB_RLO CB_RHI CB_SEG7 CB_GLYPH CB_ROSTRS 0x84148.
Proof.
eapply check_text_seg7_B.check_text_seg7_B_holds; first [cpcU_fact | exact (cpcU_seg7 CB_RLO CB_RHI) | exact cpcU_owed_seg7].
Qed.
(* the two text helpers that check_text_counter and check_text_scribble call: their walks are on this branch, so the
   contracts are ready for the final link of those two *)
Lemma cpcU_counter_text : cdcU_counter_text_specX tfibsegs TfibB ameter_triv CB_RLO CB_RHI CB_SEG7 0x869e4.
Proof. eapply diginet_counter_text_B.diginet_counter_text_B_holds; first [cpcU_fact | exact (cpcU_seg7 CB_RLO CB_RHI)]. Qed.
Lemma cpcU_scribble_text : cdcU_scribble_text_specX tfibsegs TfibB ameter_triv 0x86500.
Proof. eapply diginet_scribble_text_B.diginet_scribble_text_B_holds; cpcU_fact. Qed.
Lemma cpcU_check_text_scribble : cdcU_check_text_scribble_specX tfibsegs TfibB ameter_triv 0x83dbc.
Proof. eapply check_text_scribble_B.check_text_scribble_B_holds; first [cpcU_fact | exact cpcU_scribble_text]. Qed.
Lemma cpcU_owed_counter_text : cdcU_owed_counter_text_specX tfibsegs TfibB ameter_triv CB_RLO CB_RHI CB_GLYPH CB_ROSTRS 0x84474.
Proof. eapply owed_counter_text_B.owed_counter_text_B_holds; first [cpcU_fact | exact cpcU_owed_seg7]. Qed.
Lemma cpcU_check_text_counter :
  cdcU_check_text_counter_specX tfibsegs TfibB ameter_triv CB_RLO CB_RHI CB_SEG7 CB_GLYPH CB_ROSTRS 0x841c4.
Proof.
eapply check_text_counter_B.check_text_counter_B_holds;
first [cpcU_fact | exact cpcU_owed_counter_text | exact cpcU_counter_text].
Qed.
Lemma cpcU_meter_mask : cdcU_meter_mask_specX tfibsegs TfibB ameter_triv 0x85ef8.
Proof. eapply diginet_meter_mask_B.diginet_meter_mask_B_holds; cpcU_fact. Qed.
Lemma cpcU_meter_segs : cdcU_meter_segs_specX tfibsegs TfibB ameter_triv 0x85f14.
Proof. eapply diginet_meter_segments_B.diginet_meter_segments_B_holds; cpcU_fact. Qed.
Lemma cpcU_ring_dot : cdcU_ring_dot_specX tfibsegs TfibB ameter_triv 0x85bd8.
Proof. eapply diginet_ring_dot_B.diginet_ring_dot_B_holds; cpcU_fact. Qed.
Lemma cpcU_ring_fill : cdcU_ring_fill_specX tfibsegs TfibB ameter_triv 0x85bf8.
Proof. eapply diginet_ring_fill_B.diginet_ring_fill_B_holds; cpcU_fact. Qed.
Lemma cpcU_check_masks : cdcU_check_masks_specX tfibsegs TfibB ameter_triv 0x84974.
Proof.
eapply check_text_masks_B.check_text_masks_B_holds;
first [cpcU_fact | exact cpcU_meter_mask | exact cpcU_meter_segs | exact cpcU_ring_dot | exact cpcU_ring_fill].
Qed.
Lemma cpcU_check_refusal : cdcU_check_refusal_specX tfibsegs TfibB ameter_triv 0x84bc4.
Proof. eapply check_refusal_B.check_refusal_B_holds; cpcU_fact. Qed.
Lemma cpcU_check_range : cdcU_check_range_specX tfibsegs TfibB ameter_triv 0x84c84.
Proof. eapply check_range_B.check_range_B_holds; cpcU_fact. Qed.
Lemma cpcU_check_bytes : cdcU_check_bytes_specX tfibsegs TfibB ameter_triv 0x84d40.
Proof. eapply check_bytes_B.check_bytes_B_holds; cpcU_fact. Qed.
Lemma cpcU_fader : cdcU_fader_specX tfibsegs TfibB ameter_triv 0x8540c.
Proof. eapply diginet_fader_encode_B.diginet_fader_encode_B_holds; cpcU_fact. Qed.
Lemma cpcU_button : cdcU_button_specX tfibsegs TfibB ameter_triv 0x855dc.
Proof. eapply diginet_button_encode_B.diginet_button_encode_B_holds; cpcU_fact. Qed.
Lemma cpcU_touch : cdcU_touch_specX tfibsegs TfibB ameter_triv 0x85744.
Proof. eapply diginet_touch_encode_B.diginet_touch_encode_B_holds; cpcU_fact. Qed.
Lemma cpcU_vpot : cdcU_vpot_specX tfibsegs TfibB ameter_triv 0x85914.
Proof. eapply diginet_vpot_encode_B.diginet_vpot_encode_B_holds; cpcU_fact. Qed.
Lemma cpcU_jog : cdcU_jog_specX tfibsegs TfibB ameter_triv 0x85a8c.
Proof. eapply diginet_jog_encode_B.diginet_jog_encode_B_holds; cpcU_fact. Qed.
Lemma cpcU_sysex : cdcU_sysex_specX tfibsegs TfibB ameter_triv 0x85174.
Proof. eapply diginet_sysex_encode_B.diginet_sysex_encode_B_holds; cpcU_fact. Qed.
Lemma cpcU_leds : cdcU_leds_specX tfibsegs TfibB ameter_triv 0x86248.
Proof. eapply leds_encode_B.leds_encode_B_holds; first [cpcU_fact | exact cpcU_sysex]. Qed.
Lemma cpcU_sleds : cdcU_sleds_specX tfibsegs TfibB ameter_triv 0x861d0.
Proof. eapply diginet_strip_leds_encode_B.diginet_strip_leds_encode_B_holds; first [cpcU_fact | exact cpcU_leds]. Qed.
Lemma cpcU_cleds : cdcU_cleds_specX tfibsegs TfibB ameter_triv 0x8648c.
Proof. eapply diginet_counter_leds_encode_B.diginet_counter_leds_encode_B_holds; first [cpcU_fact | exact cpcU_leds]. Qed.
Lemma cpcU_ring : cdcU_ring_specX tfibsegs TfibB ameter_triv 0x85c1c.
Proof. eapply diginet_ring_encode_B.diginet_ring_encode_B_holds; first [cpcU_fact | exact cpcU_sysex]. Qed.
Lemma cpcU_scribble : cdcU_scribble_specX tfibsegs TfibB ameter_triv 0x866c4.
Proof. eapply diginet_scribble_encode_B.diginet_scribble_encode_B_holds; first [cpcU_fact | exact cpcU_sysex]. Qed.
Lemma cpcU_counter : cdcU_counter_specX tfibsegs TfibB ameter_triv 0x86ee4.
Proof. eapply diginet_counter_encode_B.diginet_counter_encode_B_holds; first [cpcU_fact | exact cpcU_sysex]. Qed.
Lemma cpcU_meter : cdcU_meter_specX tfibsegs TfibB ameter_triv 0x85f4c.
Proof. eapply diginet_meter_encode_B.diginet_meter_encode_B_holds; first [cpcU_fact | exact cpcU_sysex]. Qed.
Lemma cpcU_owe_sysex : cdcU_owe_sysex_specX tfibsegs TfibB ameter_triv 0x84e8c.
Proof. eapply owe_sysex_B.owe_sysex_B_holds; cpcU_fact. Qed.

(* ---- the entry function's contract at the instance ---- *)
Lemma codecU_main_x_rc :
  forall LS : lib_shape, (forall pl fs (Kl : lleaf -> TSet), LIBK pl fs Kl = Kl (LL 0 fs [])) ->
  codec_lib_contract_x (LS := LS) tfibsegs TfibB ameter_triv YE2k.tfib_K XL0 XL0 CB_RLO CB_RHI
    A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
intros LS LEAF.
pose proof (codecU_bmain_T_holds fx rc YE2k.tfib_sink_head codecU_ROB LS TfibB ameter_triv YE2k.tfib_K XL0 XL0) as H.
unfold codecU_bmain_stmt in H.
apply H; first [ cpcU_fact | exact LEAF | exact cpcU_check_text_counter | exact cpcU_owed_counter_text | exact cpcU_check_text_scribble
               | exact cpcU_sysex | exact cpcU_meter | exact cpcU_ring | exact cpcU_scribble
               | exact cpcU_counter | exact cpcU_owe_sysex | exact cpcU_check_pers | exact cpcU_pers_of | exact cpcU_text_arg
               | exact cpcU_check_seg7 | exact cpcU_check_masks | exact cpcU_check_refusal | exact cpcU_check_range
               | exact cpcU_check_bytes | exact cpcU_fader | exact cpcU_button | exact cpcU_touch | exact cpcU_vpot
               | exact cpcU_jog | exact cpcU_sleds | exact cpcU_cleds ].
Qed.
End s.

(* ============================== the bridge to the core's contract (lib/AU/YCfn.v) ==============================
   As lib/A/Prog/CPgClose.v: the two texts are the same with YCfn's constants for YCfm's (EV_LIB 2000 against 0);
   YCfn states its journal through lib/AU/YCbqU.v, whose ajournal and afn_pre are lib/Reusable/YCbq.v's text. *)
Lemma codecU_consts :
  YCfn.A_LLVMF = A_LLVMF /\ YCfn.RA_LLVMF = RA_LLVMF /\ YCfn.A_EMPTY = A_EMPTY /\
  YCfn.LIVE_LIB = LIVE_LIB /\ YCfn.LLVMF_STK = LLVMF_STK.
Proof. repeat split; reflexivity. Qed.
Lemma codecU_ev : EV_LIB <= YCfn.EV_LIB.
Proof. unfold EV_LIB, YCfn.EV_LIB. lia. Qed.
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Lemma codecU_lib_pre_x_of_tfib : forall regs ly S (W : world tfibsegs) mem md p n pl M,
  YCfn.tfib_lib_pre_x B MT XM_LIB RLO RHI regs ly S W mem md p n pl M ->
  codec_lib_pre_x tfibsegs B MT YE2k.tfib_K XM_LIB RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK
    regs ly S W mem md p n pl M.
Proof.
intros regs ly S W mem md p n pl M H. unfold YCfn.tfib_lib_pre_x in H. unfold codec_lib_pre_x.
destruct codecU_consts as (_ & HRA & HE & HLIVE & HSTK). rewrite HRA, HE, HLIVE, HSTK in H.
destruct H as (HPRE & HRA' & H10 & H11 & HPN & HLEN & HARR & HFR & HEV & HREST).
refine (conj HPRE (conj HRA' (conj H10 (conj H11 (conj HPN (conj HLEN (conj HARR (conj HFR (conj _ HREST))))))))).
pose proof codecU_ev as Hle. lia.
Qed.
Lemma codecU_lib_post_x_tfib : forall regs ly S (W : world tfibsegs) mem md p n M l ly' S' W' regs' mem' md' k,
  codec_lib_post_x tfibsegs B MT YE2k.tfib_K XN_LIB EV_LIB LLVMF_STK regs ly S W mem md p n M l ly' S' W' regs' mem' md' k ->
  YCfn.tfib_lib_post_x B MT XN_LIB regs ly S W mem md p n M l ly' S' W' regs' mem' md' k.
Proof.
intros regs ly S W mem md p n M l ly' S' W' regs' mem' md' k H.
unfold codec_lib_post_x in H. unfold YCfn.tfib_lib_post_x.
destruct codecU_consts as (_ & _ & _ & _ & HSTK). rewrite HSTK.
destruct H as (HJ & Hk & HREST).
refine (conj HJ (conj _ HREST)).
pose proof codecU_ev as Hle. lia.
Qed.
Lemma codecU_lib_contract_x_tfib :
  codec_lib_contract_x tfibsegs B MT YE2k.tfib_K XM_LIB XN_LIB RLO RHI A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK ->
  YCfn.tfib_lib_contract_x B MT XM_LIB XN_LIB RLO RHI.
Proof.
unfold codec_lib_contract_x, YCfn.tfib_lib_contract_x.
destruct codecU_consts as (HA & HRA & _ & _ & _). rewrite HA, HRA.
intros HX ly S W regs mem md p n pl M Kl HAI HPRE HK.
apply (HX ly S W regs mem md p n pl M Kl HAI (codecU_lib_pre_x_of_tfib regs ly S W mem md p n pl M HPRE)).
intros l W' c' Hle HAI' (ly' & S' & regs' & mem' & md' & k & Hc & HPOST).
apply (HK l W' c' Hle HAI').
exists ly', S', regs', mem', md', k. split; [exact Hc|].
exact (codecU_lib_post_x_tfib regs ly S W mem md p n M l ly' S' W' regs' mem' md' k HPOST).
Qed.
End k.

(* The core's program contract at TfibB / ameter_triv / XL0 / CB_RLO .. CB_RHI, from the program walks. *)
Theorem codecU_lib_x_all_of_walks :
  forall (rc : YM05.RunCeil) (LS : lib_shape), (forall pl fs (Kl : lleaf -> TSet), LIBK pl fs Kl = Kl (LL 0 fs [])) ->
  @YCfn.tfib_lib_contract_x_all rc LS TfibB ameter_triv XL0 XL0 CB_RLO CB_RHI.
Proof.
intros rc LS LEAF fx.
apply codecU_lib_contract_x_tfib.
exact (@codecU_main_x_rc fx rc LS LEAF).
Qed.
