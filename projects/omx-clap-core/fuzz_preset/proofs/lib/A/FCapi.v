(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the frame-area API of fuzz_preset's ASan image A, in the form the second allocator
   instance's API record takes (YGcfNames.v: aa_stack_malloc_cf over `In cid cf_fs_classes`, preset's classes
   [0; 1; 3]; aa_set_shadow_f5_cf in cgif_rgb's YG0e.v:48 form at 0xf5). Stated over any ARx that satisfies
   fs_iface (FCiface.v); the instance instantiates ARx := ARcf segs B and proves fs_iface for it.
   Classes and donors (the internal file RULE24-CONFIRM.md): class 0 = FCm0r/FCm0s (cgif_rgb YF9p/YF9q body, restated without
   the size premise), class 1 = FCm1r/FCm1s (cgif_file AF0r/AF0s, identical body), class 3 = FCm3r/FCm3s
   (adapted from cgif_file AF0t/AF0u; bzip2's asan build has the identical body), release stub = FCf5 (cgif_rgb
   YF8u set_shadow_gen). Preset has no class 2. No image numeral appears in this file. *)
(* Scope (c-asan, 2026-10-28 23:34Z): this is the fs_iface form, the statement of record for units whose allocator
   invariant is NOT cgif's AR (preset's ARcf, fuzz_state's ARU) and for classes with no released cgif walk. A unit
   whose invariant IS cgif's AR should take the released AR-form walk (cgif_file A/AF0s.v, AF0u.v and their kin,
   relocated) and, if it needs this shape, obtain it through FCiface.fs_iface_AR plus
   FCiface.astack_malloc_realizes_of_x (FCiface.v:168-200, Qed), which yields the same fact. *)
(* Instance shapes (measured, 2026-10-29): FCiface's fs_iface is discharged by three owners - preset's ARcf
   (FCifaceCf.fs_iface_ARcf), cgif's AR through AR_nohp (FCiface.fs_iface_AR, FCiface.v:168-200) and fuzz_state's ARU
   through ARU_nohp (FSifaceU.fs_iface_ARU, cold/port-state-rt-xiface 539b14b7a0e). The stack-window premise of
   ecall_pre_x is stated on the raw memory (apresent mem); an instance whose memory view differs from it only on
   shadow bytes (ARU reads unpoison U mem) satisfies it unchanged, because the stack window lies off the shadow range.
   FCiface.v's bytes are frozen (sha256 72b16d2a0987aa9a), so this note lives here. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m AF0x FCimg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require FCm0s FCm1s FCm3s FCf5.
Import ListNotations.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The class set of preset's image A, as aa_stack_malloc_cf takes it. *)
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
