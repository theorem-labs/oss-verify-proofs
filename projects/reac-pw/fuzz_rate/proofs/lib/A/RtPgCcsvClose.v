(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0j.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YN0j.v, with its module paths and module names changed; 546 of its 584 lines of code are new or changed and 260 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segC.v, with its module names changed; 1538 of its 1613 lines of code are new or changed and 509 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segC2.v, with its module paths changed; 237 of its 289 lines of code are new or changed and 1561 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_check_no_overread_ret.v, with its module paths and module names changed; 144 of its 179 lines of code are new or changed and 254 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/ACfi.v at origin/ossv/recipes (lines 25-41
   TfibB_libS's errno facts, 72-101 link_ML / link_SMP / link_FFL / link_AMEMSET / link_AMEMCPY, 128-141 the _all form)
   for reac-pw/fuzz_rate image A: the contract is lib/A/RtPgLib.v's rate_lib_x_all_stmt, proved from lib/A/RtPgTopA.v's
   rate_lib_x_A_close at the relocated frame's symbols (AD2l.TfibB), segments (AB1v.tfibsegs), sink (AE2k.tfib_K,
   tfib_sink_head) and constants (ACfn); the frame-flag law reads the image cover of lib/A/AF0x.v; the stack frames of
   classes 1 and 3, the strlen / strcmp / snprintf wrappers and __asan_set_shadow_f5 are the frame's and the runtime
   lanes' walks; the allocation traces and the code entries are checked on TfibB by computation. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgLink.v at af0538adbf24 for image B
   (fuzz_rate.asan-ubsan): the contract is lib/AU/RtPgLibB.v's rate_lib_x_all_stmt_B, proved from lib/AU/RtPgTopAB.v's
   rate_lib_x_B at image B's core (lib/AU YB1v / YD2l / YE2k / YCfn / YD1u / YF0m / YF0x / YCej / YE2q / YE2r); the
   frames are classes 1, 2 and 4 (YF0s, YF0u, Rt/StackMalloc4), the bcmp wrapper is YE2s's, check_csv and
   reac_rate_drivable_csv are their walks, the image's read-only facts are lib/AU/RtPgRoCloseB.v's, and the strlen /
   strcmp / set_shadow_f5 / snprintf wrappers are image B's runtime walks (lib/AU/Rt/Strlen.v, Strcmp.v, SetShadow.v,
   SnprintfRate.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/RtPgLinkB.v, with its module paths and module names changed; 17 of its 37 lines of code are new or changed and 159 lines of the source are left out. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a): check_csv's contract at image A's symbol
   record TfibB, every hypothesis of lib/A/RtPgCcsvTop.v's rt_check_csv_A discharged. Proves no function (kind:
   merge): the walk is RtPgCcsvTop.rt_check_csv_A; this file instantiates it for lib/A/RtPgLink.v's and
   lib/A/AD2o.v's Section hypothesis CCSV, whose text rate_ccsv_tfib states verbatim.
   The discharges: AR_laws by YG0q.AR_laws_ok; api_env, model_laws, frame_flag_lawP, the .got words and cells and
   rate_A_img_facts by RtPgLink's lk_api_env, lk_ML, lk_FFL, lk_HGOT, lk_HGOTU, lk_HSC, lk_HUAR, lk_IMGF; the
   class-2 frame law by A3's AF0u.stack_malloc2_contract; the bcmp wrapper by A3's AE2s.bcmp_icpt_contract; the
   class-2 entry by computation; the meter's laws by YCbp.ameter_triv_laws / ameter_triv_fs_laws.
   This file Requires RtPgLink (for the lk_* lemmas), so RtPgLink cannot Require it back: a file downstream of both
   (AD2o) instantiates RtPgLink's CCSV with rate_ccsv_tfib. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import Img0 RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgSiteA RtPgLink RtPgCcsvTop.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require AD2l AE2k AF0u AE2s.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation TB := AD2l.TfibB.
Local Notation TBS := AD2l.TfibB_syms.

Lemma cc_HPCS2 : pc_stack_malloc (as_code TB) 2 = 0x3d12c.
Proof. vm_compute. reflexivity. Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Let LAWS : AR_laws rsegs TB := AR_laws_ok rsegs TB.
Lemma cc_ASM2 : astack_malloc_realizes rsegs TB 2.
Proof. exact (AF0u.stack_malloc2_contract TB LAWS TBS). Qed.
Lemma cc_ABCMP : abcmp_realizes rsegs TB 0x421a8.
Proof. exact (AE2s.bcmp_icpt_contract TB LAWS TBS). Qed.
End k.

(* lib/A/RtPgLink.v's Section hypothesis CCSV, verbatim. *)
Theorem rate_ccsv_tfib : forall (rc : YM05.RunCeil) (fy : YK11.FPState),
  rt_check_csv_specX (fx := fy) (rc := rc) (SK := AE2k.tfib_sink_head) rsegs TB ameter_triv 0x838e0 2
    RtPgSiteA.T_csv_STK 0x21520.
Proof.
intros rc fy.
eapply (@RtPgCcsvTop.rt_check_csv_A fy rc AE2k.tfib_sink_head TB ameter_triv).
all: first
  [ exact RtPgLink.lk_api_env | exact RtPgLink.lk_ML | exact RtPgLink.lk_FFL
  | exact cc_ASM2 | exact cc_ABCMP | exact cc_HPCS2
  | exact RtPgLink.lk_HGOT | exact RtPgLink.lk_HGOTU | exact RtPgLink.lk_HSC | exact RtPgLink.lk_HUAR
  | exact RtPgLink.lk_IMGF | exact ameter_triv_laws | exact ameter_triv_fs_laws ].
Qed.

About rate_ccsv_tfib.
Print Assumptions rate_ccsv_tfib.
