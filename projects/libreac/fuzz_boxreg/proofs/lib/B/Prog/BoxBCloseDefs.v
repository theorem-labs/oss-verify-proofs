(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Moved verbatim from lib/B/Prog/BoxBClose.v (fuzz_boxreg.asan-ubsan's closing composition): the start-up record of
   row 7 (boxb_startup_B) and the three per-image values it names (BOXB_RN_MALLOC_RA, BOXB_MSITES, BOXB_FSITES), so that
   lib/B/Prog/BoxBStartup.v can prove the record at TfibB and BoxBClose.v can Require that proof without a cycle.
   BoxBClose.v does `Require Export` of this file, so every unqualified use of these names still resolves. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK15 YK18 YM05 YO09 YO06.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YP09 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YG05 YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBAddr BoxBImg BoxBLibX BoxBCheck.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require SnprintfDefB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module BRSNP := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt.SnprintfDefB.

(* read_name's call of the malloc wrapper (jal at 0x81434 to 0x5244c) returns to 0x81438. *)
Definition BOXB_RN_MALLOC_RA : Z := 0x81438.
(* LLVMFuzzerTestOneInput's own allocator calls, as offsets from boxb_text (0x7ffac): the malloc wrapper call returns
   to 0x80180 (jal at 0x8017c), the free wrapper calls to 0x808b8, 0x808f8 and 0x80e5c (jal at 0x808b4, 0x808f4,
   0x80e58). *)
Definition BOXB_MSITES : list Z := [0x1d4].
Definition BOXB_FSITES : list Z := [0x90c; 0x94c; 0xeb0].

(* The start-up certificate's facts other than the globals' shadow, and the trace universe. *)
Record boxb_startup_B (BB : asyms) : Prop := {
  stB_errno : (0 <= as_errno BB /\ as_errno BB + 4 <= kLowMemEnd) /\
    (forall a, as_errno BB <= a < as_errno BB + 4 -> YG0d.in_img boxb_segs a);
  stB_uok : universe_ok (as_universe BB);
  stB_ra0 : In [pc_malloc_ra0 (as_code BB)] (as_universe BB) /\ In [pc_free_ra0 (as_code BB)] (as_universe BB);
  stB_rn : In [pc_malloc_ra0 (as_code BB); BOXB_RN_MALLOC_RA] (as_universe BB);
  stB_htr : forall (ly : alayout) (regs regsT : bvmap 5 word) (pcf : Z),
    raZ regs = RAB_LLVMF ->
    (pcf = pc_malloc_ra0 (as_code BB) /\ In (raZ regsT - boxb_text) BOXB_MSITES) \/
    (pcf = pc_free_ra0 (as_code BB) /\ In (raZ regsT - boxb_text) BOXB_FSITES) ->
    In (call_trace0 pcf regsT (if spZ regs + 16 <? ly_top ly then [(spZ regs, raZ regs, s0Z regs)] else []))
      (as_universe BB);
  stB_rom : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
    BRSNP.absn_rom_bytes boxb_segs BB 0x20cc0 (map (fun b : byte => bv_unsigned b) Boxreg.zero6) /\
    BRSNP.absn_rom_bytes boxb_segs BB 0x20d00 [0; 0x40; 0xab; 0; 0] /\
    BRSNP.absn_rom_bytes boxb_segs BB 0x20d40 BRSNP.ABSN_FMT /\
    BRSNP.absn_rom_bytes boxb_segs BB MCH_LOB MCH_CONSTSB /\
    BRSNP.absn_rom_str boxb_segs BB 0x20ce0 [] /\ BRSNP.absn_rom_str boxb_segs BB 0x20d60 [] }.
