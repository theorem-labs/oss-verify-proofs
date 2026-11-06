(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_boxreg's ASan build (fuzz_boxreg.asan) from the module of
   the same name in proofs/cgif/cgif_file_fuzzer/lib/A/ACed.v (origin/ossv/recipes), its lemmas tfibX_AMEMSET (:145),
   tfibX_AMEMCPY (:150) and tfibX_ABCMP (:158) only, at boxreg's asyms instance and in the statement form of
   lib/A/Prog/BoxClose.v. *)
(* The ASan intrinsic instances of fuzz_boxreg.asan. Rule 24: no function is proved here; each lemma is a premise
   reorder or a conversion of a contract of the relocated core:
   - boxX_AMEMSET: lib/A/AE2r.v asan_memset_realizes (__asan_memset, 0x51534). aintrin_realizes OSet orders the
     premises dest_ok, amem_range, range_addressable, shadow_hull_vis, then OSet's arm of the op match (True); the core
     orders them dest_ok, range_addressable, shadow_hull_vis, amem_range, with no True premise. The posts agree.
   - boxX_AMEMCPY: lib/A/AE2q.v asan_memcpy_realizes (__asan_memcpy, 0x51098), in aintrin_realizes OCpy's premise order.
   - boxX_ABCMP: lib/A/AE2s.v bc_icpt_realizes (__interceptor_trampoline_bcmp, 0x41404), in abcmp_realizes's order.
   Each statement is the type of a hypothesis of lib/A/Prog/BoxClose.v at BA := TfibB (lib/A/AD2l.v): row 12
   H_RT_MEMCPY_A, row 13 H_RT_MEMSET_A, row 14 H_RT_BCMP_A. The core's premises AR_laws and BoxregSyms are
   AR_laws_ok (lib/Reusable/YG0q.v) and TfibB_syms (lib/A/AD2l.v).
   The conversions: the core states its contracts over tfibsegs (lib/A/AB1v.v) and the walk over box_segs
   (lib/A/Prog/BoxImg.v); both are images.Asan's M.loaded_segments. The core states each entry as a numeral, the walk as
   pa_sigma at PI_box, which is box_sigma (lib/A/Prog/BoxAddr.v); the three numerals are the nm addresses of
   __asan_memcpy, __asan_memset and __interceptor_trampoline_bcmp in fuzz_boxreg.asan. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YM05 YG0f YG0d YG0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import AB1v AF0m AD2l.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require AE2q AE2r AE2s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxSyms BoxAddr BoxPa BoxImg.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Lemma boxX_AMEMSET : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  aintrin_realizes box_segs TfibB OSet (pa_sigma (PAImg := PI_box) BS___asan_memset).
Proof.
intros rc fx ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
exact (AE2r.asan_memset_realizes TfibB (AR_laws_ok tfibsegs TfibB) TfibB_syms
  ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham).
Qed.

Lemma boxX_AMEMCPY : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  aintrin_realizes box_segs TfibB OCpy (pa_sigma (PAImg := PI_box) BS___asan_memcpy).
Proof.
intros rc fx. exact (AE2q.asan_memcpy_realizes TfibB (AR_laws_ok tfibsegs TfibB) TfibB_syms).
Qed.

Lemma boxX_ABCMP : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  abcmp_realizes box_segs TfibB (pa_sigma (PAImg := PI_box) BS___interceptor_trampoline_bcmp).
Proof.
intros rc fx. exact (AE2s.bc_icpt_realizes TfibB (AR_laws_ok tfibsegs TfibB) TfibB_syms).
Qed.
