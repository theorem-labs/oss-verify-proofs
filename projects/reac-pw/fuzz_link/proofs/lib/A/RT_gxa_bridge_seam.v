(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PSbz_str.v, with its module paths and module names changed; 125 of its 195 lines of code are new or changed and 89 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: relocated from omx-clap-core/fuzz_manifest lib/A/FMgxa_bzcj.v (a working branch 3e35620c52e) to libreac/fuzz_boxreg.asan-ubsan: module paths changed; 0 address numerals relocated (port_addr_check 0767e70e074a predict mode, symbol + offset). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Rt/FMgxa_bzcj.v, with its module paths changed; 28 of its 85 lines of code are new or changed and 138 lines of the source are left out. *)
(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMgxa_bzcj.v (a working branch 3e35620c52e) *)
(* Modified by Theorem Labs, 2026-10: module prefix omx_clap_core.fuzz_manifest -> libreac.fuzz_disco, record RT_IImgA.A_img -> RecAsanVfA.N_img_asan_vf; every lemma keeps fm's statement and is proved from the lemma of the same name in lib/A/RT_gxa_bridge.v (it states them at RecAsanA.N_img_asan, whose img_segs is the same rsegs), word_of_mem is an abbreviation of its word_of_mem; in-body comments dropped. *)
(* The generic bridge between the Bz tree's walks (lib/A/Bz) and GXA's CJ call contracts (lib/CJ/RL/GXA), at the
   ASan instance A_img (RT_IImgA.v) on the pinned fuzz_manifest.asan.  Nothing here is about one interceptor: each
   GXA call-contract proof (strnlen in RT_gxa_strnlen.v; memcpy, memset) imports it.
   - the vocabulary: the Bz tree (lib/A/Bz/Lib) and the CJ tree (lib/CJ/Lib) are two copies of the same machine
     library.  Every definition used here is the same term in both, so it converts by `exact`, except two:
     `msteps` (an Inductive in each tree; bz_cj_msteps, bz_cj_evt) and `mem_inv` (CJ: every byte is outside read-only
     segments and inside a segment or below TASK_SIZE; Bz: every byte and every segment byte is below UTOP).
     TASK_SIZE = UTOP = 2^47, and every segment of fuzz_manifest.asan ends below 2^47 (asegs_below).
   - the shadow: chk_ok_of_pf_rng gives the interceptors' range check `chk_ok` (Bz/A/I_qck.v) from GXA's own ASan
     vocabulary (AsanFacts.v pf_rng / shadow_rw), the quick-check words through ro_C8_of_vis.
   No address numerals. *)
(* Modified by Theorem Labs, 2026-10: relocated to omx-clap-core fuzz_manifest.asan; the image-generic lemmas of a working branch 5247aa4d0b9 proofs/plugin-hostd/fuzz_reply/lib/A/RT_gxa_calls.v (ms_cj_bz .. mem_inv_bz_cj, shad_eq .. chk_ok_of_pf_rng), module path fuzz_reply -> fuzz_manifest, the Local lemmas made global, FRbz_str's Z_to_le_bytes_roundtrip / word_of_mem / ro_C8_of_vis copied in from a working branch 445e498a469 lib/A/FMbz_str.v:99-152 (proofs unchanged) so the closure has no Reusable file, split out of RT_gxa_strnlen.v so the memcpy and memset contracts can import them; proofs unchanged. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib Require Import Mem Bytes Cells Step.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Common.PropExec.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.MState.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Exec.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Mem.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Frame.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.PropExec.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.MState.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Exec.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Mem.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Frame.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RStep.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.AsanFacts.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.I.RecAsanVfA.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.RT_gxa_bridge.
Import ListNotations.
Open Scope Z_scope.

Module BzP := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Common.PropExec.
Module BzS := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.MState.
Module BzE := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Exec.
Module BzM := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Mem.
Module BzF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Frame.
Module CJP := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.PropExec.
Module CJS := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.MState.
Module CJE := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Exec.
Module CJM := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Mem.
Module CJF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Frame.
Module CJR := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RStep.
Module GXF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.AsanFacts.
Module RTA := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.I.RecAsanVfA.
Module RGC := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.RT_gxa_bridge.

Lemma ms_cj_bz : forall R F pc fc rv m ro, CJS.MS R F pc fc rv m ro = BzS.MS R F pc fc rv m ro.
Proof. exact RGC.ms_cj_bz. Qed.

Lemma mkR_cj_bz : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  CJF.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
  = BzF.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
Proof. exact RGC.mkR_cj_bz. Qed.

Lemma seg_rom_cj_bz : CJP.seg_rom (@CJR.img_segs RTA.N_img_asan_vf) = BzP.seg_rom asegs.
Proof. exact RGC.seg_rom_cj_bz. Qed.

Lemma bz_cj_msteps : forall s s', BzE.msteps asegs s s' -> CJE.msteps (@CJR.img_segs RTA.N_img_asan_vf) s s'.
Proof. exact RGC.bz_cj_msteps. Qed.

Lemma bz_cj_evt : forall Q ms, BzE.evt asegs Q ms -> CJE.evt (@CJR.img_segs RTA.N_img_asan_vf) Q ms.
Proof. exact RGC.bz_cj_evt. Qed.

Lemma find_segment_rng : forall segs a n seg, find_segment segs a n = Some seg ->
  In seg segs /\ Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof. exact RGC.find_segment_rng. Qed.

Lemma asegs_below : forall a : word, BzM.seg_addr asegs a = true -> bv_unsigned a < BzM.UTOP.
Proof. exact RGC.asegs_below. Qed.

Lemma mem_inv_cj_bz : forall m, CJM.mem_inv (@CJR.img_segs RTA.N_img_asan_vf) m -> BzM.mem_inv asegs m.
Proof. exact RGC.mem_inv_cj_bz. Qed.

Lemma mem_inv_bz_cj : forall m, BzM.mem_inv asegs m -> CJM.mem_inv (@CJR.img_segs RTA.N_img_asan_vf) m.
Proof. exact RGC.mem_inv_bz_cj. Qed.

Lemma Z_to_le_bytes_roundtrip : forall (bs : list byte),
  Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof. exact RGC.Z_to_le_bytes_roundtrip. Qed.

Abbreviation word_of_mem := RGC.word_of_mem.

Lemma ro_C8_of_vis : forall (m : word -> option byte) a,
  0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall j, 0 <= j < 8 -> exists b, bytes_at asegs m (a + j) [b]) ->
  ro_cells asegs m a [C8 (word_of_mem m a)].
Proof. exact RGC.ro_C8_of_vis. Qed.

Lemma shad_eq : forall x, shad x = GXF.shadow_addr x.
Proof. exact RGC.shad_eq. Qed.

Lemma bytes_at1_of_mrd : forall (m : word -> option byte) a b,
  0 <= a < 2 ^ 64 -> CJM.mrd (@CJR.img_segs RTA.N_img_asan_vf) m (CJM.wa a) = Some b -> bytes_at asegs m a [b].
Proof. exact RGC.bytes_at1_of_mrd. Qed.

Lemma sh_ok_of_shadow_ok : forall (b : byte) a, GXF.shadow_ok a (bv_signed b) -> sh_ok b a.
Proof. exact RGC.sh_ok_of_shadow_ok. Qed.

Lemma al8_shad_in_shadow : forall x j, GXF.app_mem x -> 0 <= j < 8 -> GXF.in_shadow (al8 (shad x) + j).
Proof. exact RGC.al8_shad_in_shadow. Qed.

Lemma qc_word_of_shadow_rw : forall (m : word -> option byte) x,
  @GXF.shadow_rw RTA.N_img_asan_vf m -> GXF.app_mem x ->
  ro_cells asegs m (al8 (shad x)) [C8 (word_of_mem m (al8 (shad x)))].
Proof. exact RGC.qc_word_of_shadow_rw. Qed.

Lemma chk_ok_of_pf_rng : forall (m : word -> option byte) p n k,
  @GXF.pf_rng RTA.N_img_asan_vf m p n -> @GXF.shadow_rw RTA.N_img_asan_vf m -> k <= n -> chk_ok m p k.
Proof. exact RGC.chk_ok_of_pf_rng. Qed.
