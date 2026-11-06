(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the frame-area API of fuzz_preset's ASan image A, in the form the second allocator
   instance's API record takes (YGcfNames.v: aa_stack_malloc_cf over `In cid cf_fs_classes`, preset's classes
   [0; 1; 3]; aa_set_shadow_f5_cf in cgif_rgb's YG0e.v:48 form at 0xf5). Stated over any ARx that satisfies
   fs_iface (FCiface.v); the instance instantiates ARx := ARcf segs B and proves fs_iface for it.
   Classes and donors (RULE24-CONFIRM.md): class 0 = FCm0r/FCm0s (cgif_rgb YF9p/YF9q body, restated without
   the size premise), class 1 = FCm1r/FCm1s (cgif_file AF0r/AF0s, identical body), class 3 = FCm3r/FCm3s
   (adapted from cgif_file AF0t/AF0u; bzip2's asan build has the identical body), release stub = FCf5 (cgif_rgb
   YF8u set_shadow_gen). Preset has no class 2. No image numeral appears in this file. *)
(* Scope (a Theorem Labs lane, 2026-10-28 23:34Z): this is the fs_iface form, the statement of record for units whose allocator
   invariant is NOT cgif's AR (preset's ARcf, fuzz_state's ARU) and for classes with no released cgif walk. A unit
   whose invariant IS cgif's AR should take the released AR-form walk (cgif_file A/AF0s.v, AF0u.v and their kin,
   relocated) and, if it needs this shape, obtain it through FCiface.fs_iface_AR plus
   FCiface.astack_malloc_realizes_of_x (FCiface.v:168-200, Qed), which yields the same fact. *)
(* Modified by Theorem Labs, 2026-10: relocated from omx-clap-core/fuzz_preset (a working branch b120217aa206) to omx-clap-core/fuzz_state's ASan image A as fuzz_state's frame-area API: module paths and the image numerals of A/FCimg.v (generated from fuzz_state.asan), nothing else. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/FCapi.v at cb01f65c0f3: fuzz_state.asan-ubsan's frame-area API (classes 0, 1, 3 and the f5 stub at lib/B/FCimg.v SET_SHADOW_F5). Changes: module paths (lib.A -> lib.B: AB1v -> YB1v, AB1w -> YB1w, AE34 -> YE34, AF0l -> YF0l, AF0m -> YF0m, AF0x -> YF0x, AE2y -> YE2y, AE3d -> YE3d, and A's FCimg / FCxA / FCm<k>r / FCm<k>s / FCf5 / FSH_Base -> their lib/B twins; the image-generic lib/A FSupoison, FSupoisonU, FSifaceU, SetShadowDefU and FSuwalk stay), nothing else; no image numeral is typed. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YM05 FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YF0m YF0x FCimg.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FCm0s FCm1s FCm3s FCf5.
Import ListNotations.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The class set of fuzz_state's image B, as aa_stack_malloc_cf takes it. *)
Theorem preset_stack_malloc_x : forall B ARx, fs_iface tfibsegs B ARx -> TfibSyms B ->
  forall cid, In cid [0; 1; 3] -> astack_malloc_realizes_x tfibsegs B ARx cid.
Proof.
  intros B ARx I TB cid [<- | [<- | [<- | []]]].
  - exact (FCm0s.stack_malloc0_contract_x B ARx I TB).
  - exact (FCm1s.stack_malloc1_contract_x B ARx I TB).
  - exact (FCm3s.stack_malloc3_contract_x B ARx I TB).
Qed.

(* The class-3 release stub, as aa_set_shadow_f5_cf takes it (cf_pc_set_shadow_f5 = SET_SHADOW_F5). *)
Theorem preset_set_shadow_f5_x : forall B ARx, fs_iface tfibsegs B ARx -> TfibSyms B ->
  aset_shadow_realizes_x tfibsegs B ARx SET_SHADOW_F5 0xf5.
Proof. intros B ARx I TB. exact (FCf5.set_shadow_f5_contract_x B ARx I TB). Qed.

End a.
