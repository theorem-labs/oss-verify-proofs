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
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_knock/lib/A/APgLib.v, with its module paths and module names changed; 235 of its 298 lines of code are new or changed and 244 lines of the source are left out. *)
(* The program side of fuzz_codec's image-A closing (fuzz_codec.asan): the entry function's contract
   codec_lib_contract_x (lib/A/Prog/CPgMainC.v) at the start-up record TfibB (lib/A/AD2l.v), the meter ameter_triv,
   the sink tfib_K and the read window CA_RLO .. CA_RHI, from the program walks, and its bridge to the core's text
   lib/A/ACfn.v tfib_lib_contract_x_all, which the driver lib/A/AD1q.v takes. The form is
   projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgLib.v's links and bridge (and projects/libreac/fuzz_knock/proofs/lib/A/APgLib.v's
   link_* lemmas).

   What the walks leave open is discharged here, at TfibB:
     ameter_laws / ameter_fs_laws   Reusable/YCbp.v ameter_triv_laws / ameter_triv_fs_laws
     TfibLib                        lib/A/APgImgLink.v tfibX_lib
     AR_laws                        Reusable/YG0q.v AR_laws_ok
     model_laws                     Reusable/YG05.v model_laws_ok, at TfibB_syms's universe fact
     asink_img_laws                 lib/A/AD1u.v tfib_AIL
     stack_malloc_progressP         Reusable/YG05.v stack_malloc_progress
     astack_free_law                Reusable/YG0t.v astack_free_law_ok
     frame_flag_lawP                from AR_laws (al_flag, al_client_img) and lib/A/ACeh.v tfib_img_cover
     globs_marked / img_shadow_vis  lib/A/CodecStartupClose.v codec_GM_TfibB / codec_IV_TfibB
     cpw_rows_free                  lib/A/Prog/CPgWalkRo.v cpw_rows_free_syms
     the read window in the image   lib/A/APgImg.v codec_asan_relro_img
     ro_tfa_below_ofl               codec_ROB below (the read-only bytes lie below the sink head)
   and the runtime contracts the walks call:
     side-stack frames of class 0 / 1 / 3   lib/A/Rt/StackMalloc0.v, lib/A/AF0s.v, lib/A/Rt/StackMalloc3.v
     __asan_memcpy 0x51998 / __asan_memset 0x51e34   lib/A/AE2q.v / lib/A/AE2r.v
     the compare wrappers 0x422e0 / 0x422d4          lib/A/AE2s.v / lib/A/Rt/Strcmp.v
     the shadow fill with 0xf5 0x54960               lib/A/Rt/SetShadow.v

   The entry function's walk is lib/A/Prog/codec_amain.v codec_amain_holds, whose statement is codec_amain_T below
   (the kit's laws, the runtime contracts, the start-up facts and the 23 callee contracts give codec_lib_contract_x);
   it and every callee walk are applied here with every premise discharged: no premise stays open. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0s YK14 YK15 YK18 YP09 YI00 YI04 YI08 YI09 YI16 YN3v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG05 YG0q YG0t YCbp.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YImgTop.
From OSSVerify.libdiginet.fuzz_codec.images Require Asan.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACeh ACfm AF0m AD2l.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require AE2k AD1u ACfn AE2q AE2r AE2s AF0s APgImg APgImgLink CodecStartupClose AB13.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Rt Require Import SetShadowDef.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Rt Require StrcmpDef StackMalloc0 StackMalloc3 Strcmp SetShadow.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import
CodecCJ CPgBase CPgEncC CPgChkC CPgMainC CodecRo CodecGlobs CPgWalk CPgWalkRo.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require
check_bytes_A check_personality_A check_range_A check_refusal_A check_text_masks_A check_text_seg7_A
diginet_button_encode_A diginet_counter_encode_A diginet_counter_leds_encode_A diginet_fader_encode_A
diginet_jog_encode_A diginet_meter_encode_A diginet_meter_mask_A diginet_meter_segments_A
diginet_personality_from_name_A diginet_personality_of_A diginet_ring_dot_A diginet_ring_encode_A
diginet_ring_fill_A diginet_scribble_encode_A diginet_seg7_A diginet_strip_leds_encode_A diginet_sysex_encode_A
diginet_touch_encode_A diginet_vpot_encode_A owed_seg7_A text_arg_A diginet_counter_text_A codec_amain
owed_counter_text_A diginet_scribble_text_A check_text_counter_A check_text_scribble_A_H.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ============================== the entry function's walk, as a premise ==============================
   The statement of lib/A/Prog/codec_amain.v codec_amain_holds, Section a's hypotheses in that Section's order,
   with the callees' image-A entries as numerals (the AM_ names of lib/A/Prog/codec_amain_inv.v). This Section names no sink
   head instance, so every SK below is the Section's own. *)
Section T. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variables XM_LIB XN_LIB : Z -> Z.
Definition codec_amain_stmt : Prop :=
  ameter_laws MT -> ameter_fs_laws MT -> TfibLib B -> AR_laws tfibsegs B -> model_laws (as_universe B) ->
  asink_img_laws tfibsegs B K -> (forall n, 0 <= XN_LIB n) ->
  (forall pl fs (Kl : lleaf -> TSet), LIBK pl fs Kl = Kl (LL 0 fs [])) ->
  astack_malloc_realizes tfibsegs B 3 -> stack_malloc_progressP B -> astack_free_law tfibsegs B ->
  frame_flag_lawP tfibsegs B ->
  aintrin_realizes tfibsegs B OSet 0x51e34 -> aintrin_realizes tfibsegs B OCpy 0x51998 ->
  aset_shadow_realizes tfibsegs B 0x54960 0xf5 ->
  globs_marked tfibsegs B CODEC_GLOBS -> img_shadow_vis tfibsegs B -> cpw_rows_free B CA_ROSTRS ->
  cdc_check_pers_specX tfibsegs B MT CA_RLO CA_RHI CA_PERS CA_ROSTRS 0x83364 ->
  cdc_pers_of_specX tfibsegs B MT 0x84888 CA_PERS ->
  cdc_text_arg_specX tfibsegs B MT 0x835d4 ->
  cdc_check_seg7_specX tfibsegs B MT CA_RLO CA_RHI CA_SEG7 CA_GLYPH CA_ROSTRS 0x83ae4 ->
  cdc_check_text_counter_specX tfibsegs B MT CA_RLO CA_RHI CA_SEG7 CA_GLYPH CA_ROSTRS 0x83b5c ->
  cdc_owed_counter_text_specX tfibsegs B MT CA_RLO CA_RHI CA_GLYPH CA_ROSTRS 0x83df8 ->
  cdc_check_text_scribble_specX tfibsegs B MT 0x83798 ->
  cdc_check_masks_specX tfibsegs B MT 0x842b0 ->
  cdc_check_refusal_specX tfibsegs B MT 0x844dc ->
  cdc_check_range_specX tfibsegs B MT 0x84590 ->
  cdc_check_bytes_specX tfibsegs B MT 0x84640 ->
  cdc_fader_specX tfibsegs B MT 0x84ba8 ->
  cdc_button_specX tfibsegs B MT 0x84d5c ->
  cdc_touch_specX tfibsegs B MT 0x84eb8 ->
  cdc_vpot_specX tfibsegs B MT 0x8502c ->
  cdc_jog_specX tfibsegs B MT 0x85190 ->
  cdc_sysex_specX tfibsegs B MT 0x848b4 ->
  cdc_ring_specX tfibsegs B MT 0x85314 ->
  cdc_meter_specX tfibsegs B MT 0x85600 ->
  cdc_sleds_specX tfibsegs B MT 0x85834 ->
  cdc_cleds_specX tfibsegs B MT 0x85a7c ->
  cdc_scribble_specX tfibsegs B MT 0x85e24 ->
  cdc_counter_specX tfibsegs B MT 0x86608 ->
  codec_lib_contract_x tfibsegs B MT K XM_LIB XN_LIB CA_RLO CA_RHI A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
End T.
Definition codec_amain_T : Prop :=
  forall (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (ROB : @ro_tfa_below_ofl SK) (LS : lib_shape)
    (B : asyms) (MT : ameter_ops) (K : asink_syms) (XM_LIB XN_LIB : Z -> Z),
  @codec_amain_stmt fx rc SK LS B MT K XM_LIB XN_LIB.

(* The walk is on the branch: lib/A/Prog/codec_amain.v states it with `Proof using All`, so its type is codec_amain_T. *)
Lemma codec_amain_T_holds : codec_amain_T.
Proof. exact @codec_amain.codec_amain_holds. Qed.

(* ============================== from here on, the image's sink head ============================== *)
#[local] Existing Instance AE2k.tfib_sink_head.
Definition XL0 : Z -> Z := fun _ => 0.
Lemma XL0_HXL : forall n, 0 <= XL0 n.
Proof. intros n. unfold XL0. lia. Qed.

(* in_ro_tfa lies below the sink head A_ofl_head 0x5f9b08 (lib/A/AE2k.v): the read-only PT_LOADs end at 0x30000 and
   0x9d000, and the second disjunct is 0x9d280 .. 0x9e808 (lib/A/ACeh.v). *)
#[local] Instance codec_ROB : @ro_tfa_below_ofl AE2k.tfib_sink_head.
Proof.
intros a [(sg & Hs & Hw & Hr) | Hr]; cbn [YI16.sk_ofl_head AE2k.tfib_sink_head]; unfold AE2k.A_ofl_head; [|lia].
assert (E : tfibsegs = [Asan.Asan_segment_000; Asan.Asan_segment_001; Asan.Asan_segment_002; Asan.Asan_segment_003])
by reflexivity.
rewrite E in Hs. destruct Hs as [<-|[<-|[<-|[<-|[]]]]]; vm_compute in Hw; try discriminate Hw;
lazymatch type of Hr with ?lo <= a < ?hi =>
let l := eval vm_compute in lo in let h := eval vm_compute in hi in change (l <= a < h) in Hr end; lia.
Qed.


Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- the kit's laws and the start-up facts at TfibB ---- *)
Lemma cpc_MTL : ameter_laws ameter_triv.
Proof. exact ameter_triv_laws. Qed.
Lemma cpc_MTF : ameter_fs_laws ameter_triv.
Proof. exact ameter_triv_fs_laws. Qed.
Lemma cpc_TL : TfibLib TfibB.
Proof. exact APgImgLink.tfibX_lib. Qed.
Lemma cpc_LAWS : AR_laws tfibsegs TfibB.
Proof. exact (AR_laws_ok tfibsegs TfibB). Qed.
Lemma cpc_ML : model_laws (as_universe TfibB).
Proof. exact (model_laws_ok (as_universe TfibB) (ts_universe TfibB TfibB_syms)). Qed.
Lemma cpc_AIL : asink_img_laws tfibsegs TfibB AE2k.tfib_K.
Proof. exact (AD1u.tfib_AIL TfibB TfibB_syms). Qed.
Lemma cpc_SMP : stack_malloc_progressP TfibB.
Proof. intros s cid W Hc Hn. exact (stack_malloc_progress (as_universe TfibB) s cid W Hc Hn). Qed.
Lemma cpc_ASF : astack_free_law tfibsegs TfibB.
Proof. exact (astack_free_law_ok tfibsegs TfibB). Qed.
Lemma cpc_FFL : frame_flag_lawP tfibsegs TfibB.
Proof.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ cpc_LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ cpc_LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (tfib_img_cover ly S md L) as [C1 C2].
unfold TFIB_IMG_LO, TFIB_IMG_END, YImgTop.IMG_LO, YImgTop.IMG_TOP in C1, C2.
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil].
unfold zone2, off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma cpc_GM : globs_marked tfibsegs TfibB CODEC_GLOBS.
Proof. exact (CodecStartupClose.codec_GM_TfibB tfibsegs). Qed.
Lemma cpc_IV : img_shadow_vis tfibsegs TfibB.
Proof. exact (CodecStartupClose.codec_IV_TfibB tfibsegs). Qed.
Lemma cpc_RF : cpw_rows_free TfibB CA_ROSTRS.
Proof. exact (cpw_rows_free_syms TfibB TfibB_syms). Qed.
Lemma cpc_RELRO : forall a, CA_RLO <= a < CA_RHI -> in_img tfibsegs a.
Proof. exact APgImg.codec_asan_relro_img. Qed.
Lemma cpc_SEG7ROM : forall a, CA_SEG7 <= a < CA_SEG7 + 364 -> seg_rom tfibsegs (Z_to_bv 64 a) <> None.
Proof. intros a Ha. unfold CA_SEG7 in Ha. exact (AB13.tfib_rom_all a ltac:(lia)). Qed.

(* ---- the runtime contracts at TfibB ---- *)
Lemma cpc_ASM0 : astack_malloc_realizes tfibsegs TfibB 0.
Proof. exact (StackMalloc0.stack_malloc0_contract TfibB cpc_LAWS TfibB_syms). Qed.
Lemma cpc_ASM1 : astack_malloc_realizes tfibsegs TfibB 1.
Proof. exact (AF0s.stack_malloc1_contract TfibB cpc_LAWS TfibB_syms). Qed.
Lemma cpc_ASM3 : astack_malloc_realizes tfibsegs TfibB 3.
Proof. exact (StackMalloc3.stack_malloc3_contract TfibB cpc_LAWS TfibB_syms). Qed.
Lemma cpc_AMEMCPY : aintrin_realizes tfibsegs TfibB OCpy 0x51998.
Proof. exact (AE2q.asan_memcpy_realizes TfibB cpc_LAWS TfibB_syms). Qed.
(* __asan_memset's theorem takes amem_range after the two shadow premises; aintrin_realizes before them, and its
   OSet premise is True. *)
Lemma cpc_AMEMSET : aintrin_realizes tfibsegs TfibB OSet 0x51e34.
Proof.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL _.
exact (AE2r.asan_memset_realizes TfibB cpc_LAWS TfibB_syms ly S W regs mem md d x n HPRE G10 G11 G12
  Hn Hd Hdn HDST HRA HHULL HAM).
Qed.
Lemma cpc_ABCMP : abcmp_realizes tfibsegs TfibB 0x422e0.
Proof. exact (AE2s.bcmp_icpt_contract TfibB cpc_LAWS TfibB_syms). Qed.
Lemma cpc_ASTRCMP : StrcmpDef.astrcmp_realizes tfibsegs TfibB 0x422d4.
Proof. exact (Strcmp.strcmp_icpt_contract TfibB cpc_LAWS TfibB_syms). Qed.
Lemma cpc_ASSF5 : aset_shadow_realizes tfibsegs TfibB 0x54960 0xf5.
Proof. exact (SetShadow.ident_set_shadow_f5 TfibB cpc_LAWS TfibB_syms). Qed.

Ltac cpc_fact :=
  first [ exact cpc_MTL | exact cpc_MTF | exact cpc_TL | exact cpc_LAWS | exact cpc_ML | exact cpc_AIL
        | exact cpc_SMP | exact cpc_ASF | exact cpc_FFL | exact cpc_GM | exact cpc_IV | exact cpc_RF
        | exact cpc_RELRO | exact cpc_SEG7ROM | exact cpc_ASM0 | exact cpc_ASM1 | exact cpc_ASM3 | exact cpc_AMEMCPY
        | exact cpc_AMEMSET | exact cpc_ABCMP | exact cpc_ASTRCMP | exact cpc_ASSF5 | exact XL0_HXL ].

(* ---- the callee contracts whose walks are on this branch, at TfibB / ameter_triv ---- *)
Lemma cpc_pers_of : cdc_pers_of_specX tfibsegs TfibB ameter_triv 0x84888 CA_PERS.
Proof. eapply diginet_personality_of_A.diginet_personality_of_A_holds; cpc_fact. Qed.
Lemma cpc_from_name : cdc_from_name_specX tfibsegs TfibB ameter_triv CA_RLO CA_RHI CA_PERS CA_ROSTRS 0x847dc.
Proof. eapply diginet_personality_from_name_A.diginet_personality_from_name_A_holds; cpc_fact. Qed.
Lemma cpc_check_pers : cdc_check_pers_specX tfibsegs TfibB ameter_triv CA_RLO CA_RHI CA_PERS CA_ROSTRS 0x83364.
Proof. eapply check_personality_A.check_personality_A_holds; first [cpc_fact | exact cpc_pers_of | exact cpc_from_name]. Qed.
Lemma cpc_seg7 : cdc_seg7_specX tfibsegs TfibB ameter_triv CA_RLO CA_RHI CA_SEG7 0x860b4.
Proof. eapply diginet_seg7_A.diginet_seg7_A_holds; cpc_fact. Qed.
Lemma cpc_owed_seg7 : cdc_owed_seg7_specX tfibsegs TfibB ameter_triv CA_RLO CA_RHI CA_GLYPH CA_ROSTRS 0x8438c.
Proof. eapply owed_seg7_A.owed_seg7_A_holds; first [cpc_fact | exact TfibB_syms]. Qed.
Lemma cpc_check_seg7 :
  cdc_check_seg7_specX tfibsegs TfibB ameter_triv CA_RLO CA_RHI CA_SEG7 CA_GLYPH CA_ROSTRS 0x83ae4.
Proof. eapply check_text_seg7_A.check_text_seg7_A_holds; first [cpc_fact | exact cpc_seg7 | exact cpc_owed_seg7]. Qed.
Lemma cpc_text_arg : cdc_text_arg_specX tfibsegs TfibB ameter_triv 0x835d4.
Proof. eapply text_arg_A.text_arg_A_holds; cpc_fact. Qed.
(* counter_text, which check_text_counter calls: its walk is on the branch, so its contract is ready for the final
   link of check_text_counter (the read window in the image and the seg7 table in the image's bytes, discharged) *)
Lemma cpc_counter_text : cdc_counter_text_specX tfibsegs TfibB ameter_triv CA_RLO CA_RHI CA_SEG7 0x86120.
Proof. eapply diginet_counter_text_A.diginet_counter_text_A_holds; first [cpc_fact | exact cpc_seg7]. Qed.
Lemma cpc_owed_counter_text : cdc_owed_counter_text_specX tfibsegs TfibB ameter_triv CA_RLO CA_RHI CA_GLYPH CA_ROSTRS 0x83df8.
Proof. eapply owed_counter_text_A.owed_counter_text_A_holds; first [cpc_fact | exact cpc_owed_seg7]. Qed.
(* scribble_text, which check_text_scribble calls: its walk is on the branch, so its contract is ready for the final
   link of check_text_scribble *)
Lemma cpc_scribble_text : cdc_scribble_text_specX tfibsegs TfibB ameter_triv 0x85cc4.
Proof. eapply diginet_scribble_text_A.diginet_scribble_text_A_holds; cpc_fact. Qed.
Lemma cpc_check_text_counter :
  cdc_check_text_counter_specX tfibsegs TfibB ameter_triv CA_RLO CA_RHI CA_SEG7 CA_GLYPH CA_ROSTRS 0x83b5c.
Proof.
eapply check_text_counter_A.check_text_counter_A_holds;
first [cpc_fact | exact cpc_owed_counter_text | exact cpc_counter_text].
Qed.
Lemma cpc_check_text_scribble : cdc_check_text_scribble_specX tfibsegs TfibB ameter_triv 0x83798.
Proof. eapply check_text_scribble_A_H.check_text_scribble_A_holds; first [cpc_fact | exact cpc_scribble_text]. Qed.
Lemma cpc_meter_mask : cdc_meter_mask_specX tfibsegs TfibB ameter_triv 0x855ac.
Proof. eapply diginet_meter_mask_A.diginet_meter_mask_A_holds; cpc_fact. Qed.
Lemma cpc_meter_segs : cdc_meter_segs_specX tfibsegs TfibB ameter_triv 0x855c8.
Proof. eapply diginet_meter_segments_A.diginet_meter_segments_A_holds; cpc_fact. Qed.
Lemma cpc_ring_dot : cdc_ring_dot_specX tfibsegs TfibB ameter_triv 0x852d0.
Proof. eapply diginet_ring_dot_A.diginet_ring_dot_A_holds; cpc_fact. Qed.
Lemma cpc_ring_fill : cdc_ring_fill_specX tfibsegs TfibB ameter_triv 0x852f0.
Proof. eapply diginet_ring_fill_A.diginet_ring_fill_A_holds; cpc_fact. Qed.
Lemma cpc_check_masks : cdc_check_masks_specX tfibsegs TfibB ameter_triv 0x842b0.
Proof.
eapply check_text_masks_A.check_text_masks_A_holds;
first [cpc_fact | exact cpc_meter_mask | exact cpc_meter_segs | exact cpc_ring_dot | exact cpc_ring_fill].
Qed.
Lemma cpc_check_refusal : cdc_check_refusal_specX tfibsegs TfibB ameter_triv 0x844dc.
Proof. eapply check_refusal_A.check_refusal_A_holds; cpc_fact. Qed.
Lemma cpc_check_range : cdc_check_range_specX tfibsegs TfibB ameter_triv 0x84590.
Proof. eapply check_range_A.check_range_A_holds; cpc_fact. Qed.
Lemma cpc_check_bytes : cdc_check_bytes_specX tfibsegs TfibB ameter_triv 0x84640.
Proof. eapply check_bytes_A.check_bytes_A_holds; cpc_fact. Qed.
Lemma cpc_fader : cdc_fader_specX tfibsegs TfibB ameter_triv 0x84ba8.
Proof. eapply diginet_fader_encode_A.diginet_fader_encode_A_holds; cpc_fact. Qed.
Lemma cpc_button : cdc_button_specX tfibsegs TfibB ameter_triv 0x84d5c.
Proof. eapply diginet_button_encode_A.diginet_button_encode_A_holds; cpc_fact. Qed.
Lemma cpc_touch : cdc_touch_specX tfibsegs TfibB ameter_triv 0x84eb8.
Proof. eapply diginet_touch_encode_A.diginet_touch_encode_A_holds; cpc_fact. Qed.
Lemma cpc_vpot : cdc_vpot_specX tfibsegs TfibB ameter_triv 0x8502c.
Proof. eapply diginet_vpot_encode_A.diginet_vpot_encode_A_holds; cpc_fact. Qed.
Lemma cpc_jog : cdc_jog_specX tfibsegs TfibB ameter_triv 0x85190.
Proof. eapply diginet_jog_encode_A.diginet_jog_encode_A_holds; cpc_fact. Qed.
Lemma cpc_sysex : cdc_sysex_specX tfibsegs TfibB ameter_triv 0x848b4.
Proof. eapply diginet_sysex_encode_A.diginet_sysex_encode_A_holds; cpc_fact. Qed.
Lemma cpc_ring : cdc_ring_specX tfibsegs TfibB ameter_triv 0x85314.
Proof. eapply diginet_ring_encode_A.diginet_ring_encode_A_holds; cpc_fact. Qed.
Lemma cpc_meter : cdc_meter_specX tfibsegs TfibB ameter_triv 0x85600.
Proof. eapply diginet_meter_encode_A.diginet_meter_encode_A_holds; cpc_fact. Qed.
Lemma cpc_sleds : cdc_sleds_specX tfibsegs TfibB ameter_triv 0x85834.
Proof. eapply diginet_strip_leds_encode_A.diginet_strip_leds_encode_A_holds; cpc_fact. Qed.
Lemma cpc_cleds : cdc_cleds_specX tfibsegs TfibB ameter_triv 0x85a7c.
Proof. eapply diginet_counter_leds_encode_A.diginet_counter_leds_encode_A_holds; cpc_fact. Qed.
Lemma cpc_scribble : cdc_scribble_specX tfibsegs TfibB ameter_triv 0x85e24.
Proof. eapply diginet_scribble_encode_A.diginet_scribble_encode_A_holds; first [cpc_fact | exact cpc_sysex]. Qed.
Lemma cpc_counter : cdc_counter_specX tfibsegs TfibB ameter_triv 0x86608.
Proof. eapply diginet_counter_encode_A.diginet_counter_encode_A_holds; cpc_fact. Qed.

(* ---- the entry function's contract at the instance ---- *)
Lemma codec_main_x_rc :
  forall LS : lib_shape, (forall pl fs (Kl : lleaf -> TSet), LIBK pl fs Kl = Kl (LL 0 fs [])) ->
  codec_lib_contract_x (LS := LS) tfibsegs TfibB ameter_triv AE2k.tfib_K XL0 XL0 CA_RLO CA_RHI
    A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
intros LS LEAF.
pose proof (codec_amain_T_holds fx rc AE2k.tfib_sink_head codec_ROB LS TfibB ameter_triv AE2k.tfib_K XL0 XL0) as H.
unfold codec_amain_stmt in H.
apply H; first [ cpc_fact | exact LEAF | exact cpc_text_arg | exact cpc_check_text_counter
               | exact cpc_owed_counter_text | exact cpc_check_text_scribble | exact cpc_check_pers | exact cpc_pers_of
               | exact cpc_check_seg7 | exact cpc_check_masks | exact cpc_check_refusal | exact cpc_check_range
               | exact cpc_check_bytes | exact cpc_fader | exact cpc_button | exact cpc_touch | exact cpc_vpot
               | exact cpc_jog | exact cpc_sysex | exact cpc_ring | exact cpc_meter | exact cpc_sleds
               | exact cpc_cleds | exact cpc_scribble | exact cpc_counter ].
Qed.
End s.

(* ============================== the bridge to the core's contract [QPgLib.v:264-318] ==========
   The core (lib/A/AD1q.v) takes ACfn.tfib_lib_contract_x_all. The two texts are the same with ACfn's constants for
   ACfm's: A_LLVMF, RA_LLVMF, A_EMPTY, LIVE_LIB and LLVMF_STK are equal in both (codec_consts), and EV_LIB is 2000
   in ACfn and 0 in ACfm (codec_ev); ACfn's arodata_okS is CPgBase's arodata_okP by conversion. ACfn is Required,
   not Imported, so its names keep the ACfn prefix. *)
Lemma codec_consts :
  ACfn.A_LLVMF = A_LLVMF /\ ACfn.RA_LLVMF = RA_LLVMF /\ ACfn.A_EMPTY = A_EMPTY /\
  ACfn.LIVE_LIB = LIVE_LIB /\ ACfn.LLVMF_STK = LLVMF_STK.
Proof. repeat split; reflexivity. Qed.
Lemma codec_ev : EV_LIB <= ACfn.EV_LIB.
Proof. unfold EV_LIB, ACfn.EV_LIB. lia. Qed.
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Lemma codec_lib_pre_x_of_tfib : forall regs ly S (W : world tfibsegs) mem md p n pl M,
  ACfn.tfib_lib_pre_x B MT XM_LIB RLO RHI regs ly S W mem md p n pl M ->
  codec_lib_pre_x tfibsegs B MT AE2k.tfib_K XM_LIB RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK
    regs ly S W mem md p n pl M.
Proof.
intros regs ly S W mem md p n pl M H. unfold ACfn.tfib_lib_pre_x in H. unfold codec_lib_pre_x.
destruct codec_consts as (_ & HRA & HE & HLIVE & HSTK). rewrite HRA, HE, HLIVE, HSTK in H.
destruct H as (HPRE & HRA' & H10 & H11 & HPN & HLEN & HARR & HFR & HEV & HREST).
refine (conj HPRE (conj HRA' (conj H10 (conj H11 (conj HPN (conj HLEN (conj HARR (conj HFR (conj _ HREST))))))))).
pose proof codec_ev as Hle. lia.
Qed.
Lemma codec_lib_post_x_tfib : forall regs ly S (W : world tfibsegs) mem md p n M l ly' S' W' regs' mem' md' k,
  codec_lib_post_x tfibsegs B MT AE2k.tfib_K XN_LIB EV_LIB LLVMF_STK regs ly S W mem md p n M l ly' S' W' regs' mem' md' k ->
  ACfn.tfib_lib_post_x B MT XN_LIB regs ly S W mem md p n M l ly' S' W' regs' mem' md' k.
Proof.
intros regs ly S W mem md p n M l ly' S' W' regs' mem' md' k H.
unfold codec_lib_post_x in H. unfold ACfn.tfib_lib_post_x.
destruct codec_consts as (_ & _ & _ & _ & HSTK). rewrite HSTK.
destruct H as (HJ & Hk & HREST).
refine (conj HJ (conj _ HREST)).
pose proof codec_ev as Hle. lia.
Qed.
Lemma codec_lib_contract_x_tfib :
  codec_lib_contract_x tfibsegs B MT AE2k.tfib_K XM_LIB XN_LIB RLO RHI A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK ->
  ACfn.tfib_lib_contract_x B MT XM_LIB XN_LIB RLO RHI.
Proof.
unfold codec_lib_contract_x, ACfn.tfib_lib_contract_x.
destruct codec_consts as (HA & HRA & _ & _ & _). rewrite HA, HRA.
intros HX ly S W regs mem md p n pl M Kl HAI HPRE HK.
apply (HX ly S W regs mem md p n pl M Kl HAI (codec_lib_pre_x_of_tfib regs ly S W mem md p n pl M HPRE)).
intros l W' c' Hle HAI' (ly' & S' & regs' & mem' & md' & k & Hc & HPOST).
apply (HK l W' c' Hle HAI').
exists ly', S', regs', mem', md', k. split; [exact Hc|].
exact (codec_lib_post_x_tfib regs ly S W mem md p n M l ly' S' W' regs' mem' md' k HPOST).
Qed.
End k.

(* The core's program contract at TfibB / ameter_triv / XL0 / CA_RLO .. CA_RHI, from the program walks. *)
Theorem codec_lib_x_all_of_walks :
  forall (rc : YM05.RunCeil) (LS : lib_shape), (forall pl fs (Kl : lleaf -> TSet), LIBK pl fs Kl = Kl (LL 0 fs [])) ->
  @ACfn.tfib_lib_contract_x_all rc LS TfibB ameter_triv XL0 XL0 CA_RLO CA_RHI.
Proof.
intros rc LS LEAF fx.
apply codec_lib_contract_x_tfib.
exact (@codec_main_x_rc fx rc LS LEAF).
Qed.
