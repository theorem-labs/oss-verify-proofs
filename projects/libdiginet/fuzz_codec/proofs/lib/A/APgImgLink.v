(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/ACed.v at c8557374ad2e to libreac/fuzz_knock's asan image (fuzz_knock.asan, sha256 61768cf4739b...), with its module paths changed: lines 30-31 (tfibX_segs0), 35 (tfibX_base0, here the three entry addresses tfibX_init0 / tfibX_heard0 / tfibX_step0), 40-55 (tfibX_lib), 70-71, 73 and 76-87 (tfibX_LAWS, tfibX_env, tfibX_PALib0) and 145-149 (tfibX_AMEMSET) are taken; lines 27-29 (XN0), 32-34 (the second listing and the RELRO remarks), 56-69 (the ro_below_ofl instances), 72 and 74-75 (HD, tfibX_ML), 88-144 and 150-166 (the second listing's PALib and the PALibF, malloc, free, memcpy, memcmp and bcmp facts) are left out. Renames: PB_tfib -> PI_knock_asan (lib/A/APgImg.v), the abbreviations B -> TfibB and HB -> TfibB_syms (lib/A/AD2l.v), AS_asan_memset -> AS___asan_memset (lib/Reusable/YI0w.v); asan_memset_realizes is lib/A/AE2r.v's. Constants: tfibX_base0's 0x81404 -> the entry addresses of reac_knock_init 0x7f44c, reac_knock_heard 0x7f4e8 and reac_knock_step 0x7f570 (knock symbol table; text base 0x7eed0 + AF_asan_reac_knock_<F> of lib/Reusable/YI0x.v); tfibX_lib's errno segment, cgif's fourth image segment -> knock's (0x98000, 0x55b000), the fourth segment of the image module Asan.M.loaded_segments (its (base, size) list read by vm_compute: (0x10000, 0x1f000), (0x2f000, 0x67000), (0x96000, 0x2000), (0x98000, 0x55b000); the page-rounded range of the fourth PT_LOAD 0x982c8 + 0x55aae8 of the ELF program headers), which holds TFIB_ERRNO 0x5d142c .. 0x5d1430 (lib/A/AF0m.v); tfibX_lib_consts_chk and its use are dropped and the lib_consts field closes by contradiction, because knock's lib_const_addr is False (lib/A/ACeh.v). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/A/APgImgLink.v at 4b6f0df50aa7 (donor image sha256 61768cf4739b) to libdiginet/fuzz_codec's asan image (fuzz_codec.asan, sha256 7d470194ffdb...), with its module paths changed. Renames: PI_knock_asan -> PI_codec_asan (lib/A/APgImg.v). knock's three entry remarks tfibX_init0 / tfibX_heard0 / tfibX_step0 -> one remark tfibX_<f>0 for each of the 32 codec functions that a call slot of the listing reaches (entry = text base 0x8084c + AF_asan_<f> of lib/Reusable/YI0x.v). tfibX_lib's errno segment -> codec's fourth image segment (0x9f000, 0x55c000) of Asan.M.loaded_segments ((0x10000, 0x20000), (0x30000, 0x6d000), (0x9d000, 0x2000), (0x9f000, 0x55c000)), which holds TFIB_ERRNO 0x5d936c .. 0x5d9370 (lib/A/AF0m.v). The lib_consts field, closed by contradiction in knock (knock's lib_const_addr is False), is proved for codec's eight lib_const_addr ranges (lib/A/ACeh.v): the new lemma tfibX_zr_out shows each range is disjoint from every row of Tfib_owned_static by a boolean check (vm_compute), and lia shows each range is disjoint from errno. tfibX_PALib0's shadow-base cell is codec's A_OBJ 31 (lib/Reusable/YC1f.v). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YP0b YK04 YG00 YG0a YG01 YG0f YG0n YG0q YG0d YCbq.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 AF0m AF0l ACej AD2l ACeh.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI0w YI0x YC4a.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import APgImg.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YC1f.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AE2r.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Lemma tfibX_zr_out : forall lo hi (l : list (Z * Z)) a, lo <= a < hi ->
forallb (fun r => (hi <=? fst r) || (fst r + snd r <=? lo))%bool l = true -> ~ Exists (in_zr a) l.
Proof.
intros lo hi l a Ha H HE. apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz.
pose proof (proj1 (forallb_forall _ _) H r Hr) as Hb. apply orb_true_iff in Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Remark tfibX_segs0 : @pa_segs _ _ PI_codec_asan = tfibsegs.   Proof. reflexivity. Qed.
Remark tfibX_check_personality0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_check_personality = 0x83364.   Proof. reflexivity. Qed.
Remark tfibX_text_arg0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_text_arg = 0x835d4.   Proof. reflexivity. Qed.
Remark tfibX_check_text_scribble0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_check_text_scribble = 0x83798.   Proof. reflexivity. Qed.
Remark tfibX_check_text_seg70 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_check_text_seg7 = 0x83ae4.   Proof. reflexivity. Qed.
Remark tfibX_check_text_counter0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_check_text_counter = 0x83b5c.   Proof. reflexivity. Qed.
Remark tfibX_owed_counter_text0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_owed_counter_text = 0x83df8.   Proof. reflexivity. Qed.
Remark tfibX_check_text_masks0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_check_text_masks = 0x842b0.   Proof. reflexivity. Qed.
Remark tfibX_owed_seg70 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_owed_seg7 = 0x8438c.   Proof. reflexivity. Qed.
Remark tfibX_check_refusal0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_check_refusal = 0x844dc.   Proof. reflexivity. Qed.
Remark tfibX_check_range0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_check_range = 0x84590.   Proof. reflexivity. Qed.
Remark tfibX_check_bytes0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_check_bytes = 0x84640.   Proof. reflexivity. Qed.
Remark tfibX_diginet_personality_from_name0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_diginet_personality_from_name = 0x847dc.   Proof. reflexivity. Qed.
Remark tfibX_diginet_personality_of0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_diginet_personality_of = 0x84888.   Proof. reflexivity. Qed.
Remark tfibX_diginet_sysex_encode0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_diginet_sysex_encode = 0x848b4.   Proof. reflexivity. Qed.
Remark tfibX_diginet_fader_encode0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_diginet_fader_encode = 0x84ba8.   Proof. reflexivity. Qed.
Remark tfibX_diginet_button_encode0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_diginet_button_encode = 0x84d5c.   Proof. reflexivity. Qed.
Remark tfibX_diginet_touch_encode0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_diginet_touch_encode = 0x84eb8.   Proof. reflexivity. Qed.
Remark tfibX_diginet_vpot_encode0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_diginet_vpot_encode = 0x8502c.   Proof. reflexivity. Qed.
Remark tfibX_diginet_jog_encode0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_diginet_jog_encode = 0x85190.   Proof. reflexivity. Qed.
Remark tfibX_diginet_ring_dot0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_diginet_ring_dot = 0x852d0.   Proof. reflexivity. Qed.
Remark tfibX_diginet_ring_fill0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_diginet_ring_fill = 0x852f0.   Proof. reflexivity. Qed.
Remark tfibX_diginet_ring_encode0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_diginet_ring_encode = 0x85314.   Proof. reflexivity. Qed.
Remark tfibX_diginet_meter_mask0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_diginet_meter_mask = 0x855ac.   Proof. reflexivity. Qed.
Remark tfibX_diginet_meter_segments0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_diginet_meter_segments = 0x855c8.   Proof. reflexivity. Qed.
Remark tfibX_diginet_meter_encode0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_diginet_meter_encode = 0x85600.   Proof. reflexivity. Qed.
Remark tfibX_diginet_strip_leds_encode0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_diginet_strip_leds_encode = 0x85834.   Proof. reflexivity. Qed.
Remark tfibX_diginet_counter_leds_encode0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_diginet_counter_leds_encode = 0x85a7c.   Proof. reflexivity. Qed.
Remark tfibX_diginet_scribble_text0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_diginet_scribble_text = 0x85cc4.   Proof. reflexivity. Qed.
Remark tfibX_diginet_scribble_encode0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_diginet_scribble_encode = 0x85e24.   Proof. reflexivity. Qed.
Remark tfibX_diginet_seg70 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_diginet_seg7 = 0x860b4.   Proof. reflexivity. Qed.
Remark tfibX_diginet_counter_text0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_diginet_counter_text = 0x86120.   Proof. reflexivity. Qed.
Remark tfibX_diginet_counter_encode0 : @pa_val _ _ PI_codec_asan A_TEXT + AF_asan_diginet_counter_encode = 0x86608.   Proof. reflexivity. Qed.
Theorem tfibX_lib : TfibLib TfibB.
Proof.
constructor; try reflexivity.
- cbn [as_errno TfibB]. unfold TFIB_ERRNO, kLowMemEnd. lia.
- intros a Ha. cbn [as_errno TfibB] in Ha. unfold TFIB_ERRNO in Ha. unfold in_img.
assert (Hb : nth_error (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs) 3 = Some (0x9f000, 0x55c000))
by (vm_compute; reflexivity).
rewrite nth_error_map in Hb. destruct (nth_error tfibsegs 3) as [sg|] eqn:E; [|discriminate Hb]. cbn in Hb. injection Hb as H1 H2.
exists sg. split; [exact (nth_error_In _ 3 E) | rewrite H1, H2; lia].
- intros a Ha. cbn [as_owned_static as_errno TfibB]. unfold lib_const_addr in Ha. split; [| unfold TFIB_ERRNO; lia].
destruct Ha as [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; (eapply tfibX_zr_out; [exact H | vm_compute; reflexivity]).
- cbn [as_gp TfibB]. unfold TFIB_GP. lia.
Qed.
Definition tfibX_LAWS : AR_laws tfibsegs TfibB := AR_laws_ok tfibsegs TfibB.
Definition tfibX_env : api_env tfibsegs TfibB := tl_env TfibB tfibX_lib.
Lemma tfibX_PALib0 : PALib (PI := PI_codec_asan) TfibB.
Proof.
constructor.
- reflexivity.
- reflexivity.
- left. vm_compute. discriminate.
- exact tfibX_env.
- reflexivity.
- reflexivity.
- vm_compute. split; reflexivity.
Qed.
Lemma tfibX_AMEMSET : aintrin_realizes tfibsegs TfibB OSet (@pa_sigma _ _ PI_codec_asan AS___asan_memset).
Proof.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
exact (asan_memset_realizes TfibB tfibX_LAWS TfibB_syms ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham).
Qed.
End b.
