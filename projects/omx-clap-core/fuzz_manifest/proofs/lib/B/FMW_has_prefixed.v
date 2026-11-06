(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 848 of its 931 lines of code are new or changed and 1841 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_hp_kit.v; 369 of its 428 lines of code are new or changed and 872 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_has_prefixed.v; 19 of its 43 lines of code are new or changed and 404 lines of the source are left out. *)
(* has_prefixed 0x823e4..0x825ac (lv2_locate.c:55-76) in fm.asan-ubsan (G2, image B): FMH_Fn.has_prefixed_spec
   (lib/B/FMH_Fn.v:200) under the runtime contracts of strlen, strstr (U = []) and strncmp (FMH_Rt) and name_char_spec
   (proved in lib/B/FMW_name_char.v), and the shadow-base cells of B. The walk: the entry (FMW_hp_entry.v), the loop
   (FMW_hp_loop.v) and its five segments (FMW_hp_seg{H,N,P,Q,T}.v, which refute B's six UBSan guards of trap 0x825a0
   with B5's lib/B/FMTrapB.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI04 YN3v YI08.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YA0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YC20 YI16 YI00 YM05 YG0q YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_g2rt FMW_hp_kit FMW_hp_entry.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require
  FMW_hp_segH FMW_hp_segN FMW_hp_segP FMW_hp_segQ FMW_hp_segT.
Import ListNotations.
Open Scope Z_scope.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HGOTS : as_got_shadow B = HP_GOT_shadow.
Hypothesis HCELL : as_shadow_cell B = HP_shadow_cell.
Hypothesis IMGF : fm_img_facts tfibsegs B.
Hypothesis NC : name_char_spec tfibsegs B.
Hypothesis ASTRLEN : astrlen_realizes tfibsegs B PC_strlen.
Hypothesis ASTRNCMP : astrncmp_realizes tfibsegs B PC_strncmp.
Hypothesis ASTRSTR : astrstr_realizes tfibsegs B PC_strstr.

Theorem has_prefixed_holds : has_prefixed_spec tfibsegs B.
Proof.
apply (has_prefixed_walk B HGOTS HCELL IMGF ASTRLEN ASTRSTR).
- apply FMW_hp_segH.seg_head; assumption.
- apply FMW_hp_segN.seg_ncmp; assumption.
- apply FMW_hp_segP.seg_pre; assumption.
- apply FMW_hp_segQ.seg_post; assumption.
- apply FMW_hp_segT.seg_tail; assumption.
Qed.
End t.
