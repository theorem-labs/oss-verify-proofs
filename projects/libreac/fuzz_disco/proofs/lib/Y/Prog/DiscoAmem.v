(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: tfibX_AMEMSET and tfibX_AMEMCPY copied from proofs/cgif/cgif_file_fuzzer/lib/YCed.v, with their module paths changed and their statements restated at libreac/fuzz_disco's PB_tfib image (pa_segs and pa_sigma of PB_tfib, YD2l.TfibB). *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YG0d YG0q YM05 YB1v YC4a YI0w YI12 YCbj YD2l YE2q YE2r.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma tfibX_AMEMSET : aintrin_realizes (@pa_segs _ _ PB_tfib) YD2l.TfibB OSet (@pa_sigma _ _ PB_tfib AS___asan_memset).
Proof.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
exact (asan_memset_realizes YD2l.TfibB (AR_laws_ok tfibsegs YD2l.TfibB) YD2l.TfibB_syms
  ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham).
Qed.
Lemma tfibX_AMEMCPY : aintrin_realizes (@pa_segs _ _ PB_tfib) YD2l.TfibB OCpy (@pa_sigma _ _ PB_tfib AS___asan_memcpy).
Proof.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc.
exact (asan_memcpy_realizes YD2l.TfibB (AR_laws_ok tfibsegs YD2l.TfibB) YD2l.TfibB_syms
  ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc).
Qed.
End b.
