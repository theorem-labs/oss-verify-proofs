(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC94.v, with its module paths and module names changed; 204 of its 225 lines of code are new or changed and 228 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AU/Prog/codec_bmain_rdx_13.v, with its module names changed; 13 of its 46 lines of code are new or changed and 192 lines of the source are left out. *)
(* Segments RD12 (SCRIBBLE_TEXT), RD13 (COUNTER_TEXT) and RD14 (MASKS) of the image-B walk of LLVMFuzzerTestOneInput
   (lib/AU/Prog/codec_bmain_inv.v seg_rd12, seg_rd13, seg_rd14), one file per segment:
     codec_bmain_rdx_12.v  seg_rd12_holds (0x80fa4 to ENC9 0x82734);
     codec_bmain_rdx_13.v  seg_rd13_holds (0x812ec to ENC10 0x8274c or LATCH 0x82df4);
     codec_bmain_rdx_14.v  seg_rd14_holds (0x814f8 to LATCH 0x82df4).
   Here the three together, under the union of their Section hypotheses. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK14 YK15 YK18 YK0s YP09 YI00 YI04 YI08 YI09 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCeh YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgChkU CodecRo CodecGlobs CPgWalkU CPgWalkRoU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require codec_bmain_rdx_12 codec_bmain_rdx_13 codec_bmain_rdx_14.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.
Hypothesis IV : img_shadow_vis tfibsegs B.
Hypothesis RF : cpw_rows_free B CB_ROSTRS.
Hypothesis CTA : cdcU_text_arg_specX tfibsegs B MT BM_text_arg.
Hypothesis CTS : cdcU_check_text_scribble_specX tfibsegs B MT BM_check_text_scribble.
Hypothesis CS7 : cdcU_check_seg7_specX tfibsegs B MT CB_RLO CB_RHI CB_SEG7 CB_GLYPH CB_ROSTRS BM_check_seg7.
Hypothesis CTC : cdcU_check_text_counter_specX tfibsegs B MT CB_RLO CB_RHI CB_SEG7 CB_GLYPH CB_ROSTRS BM_check_text_counter.
Hypothesis COC : cdcU_owed_counter_text_specX tfibsegs B MT CB_RLO CB_RHI CB_GLYPH CB_ROSTRS BM_owed_counter_text.
Hypothesis CMASKS : cdcU_check_masks_specX tfibsegs B MT BM_check_masks.

Theorem seg_rd12_14 : seg_rd12 B MT K XM_LIB /\ seg_rd13 B MT K XM_LIB /\ seg_rd14 B MT K XM_LIB.
Proof.
split; [|split].
- eapply codec_bmain_rdx_12.seg_rd12_holds; eassumption.
- eapply codec_bmain_rdx_13.seg_rd13_holds; eassumption.
- eapply codec_bmain_rdx_14.seg_rd14_holds; eassumption.
Qed.
End b.
End a.
