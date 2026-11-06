(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cjson/cjson_read_fuzzer/lib/RL/I/IImgA.v for this unit: its address tables keep some of cjson's keys and add this unit's own, each at an address of this unit's asan image (lib/A/Img0.v); the definitions A_* are renamed N_* and asegs is renamed rsegs; the notations KV and KV3 are no longer Local; and the imports name this unit's modules. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/CJ/RL/I/IImgA.v, with its module paths and addresses changed; 2 of its 18 lines of code are new or changed and 141 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/CJ/RL/I/IImgP.v at ca77675ebeb; the same keys mapped to the addresses of the ASan image A (fuzz_role.asan, lib/A/Img0.v). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/CJ/RL/I/IImgA.v at 92636bfca57; the same keys mapped to the addresses of reac-pw/fuzz_headamp's ASan image A (fuzz_headamp.asan, lib/A/Img0.v). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.I Require Export IInst.
Import ListNotations.
Open Scope Z_scope.

Notation KV a b := (a, b) (only parsing).
Notation KV3 a b c := (a, b, c) (only parsing).
(* Measured on fuzz_headamp.asan (unstripped sha256 b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a,
   pinned f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; same bytes at every address below).
   The rounding-mode table read by __fe_getround (0x85cb8 auipc a1,0xfff9c; addi a1,a1,-0x7c0: 0x214f8, the 12 bytes
   03 00 00 00 01 00 00 00 02 00 00 00 of the plain image's 0x10610); then __extendsftf2 0x85248 (348 B, the donor's
   key) and __floatditf 0x853a4 (292 B, a synthetic key: the donor's key space has no __floatditf). *)
Definition N_exact : list (Z * Z) := [
  KV 0x1145c 0x214f8;
  KV 0x200dc 0x85248;
  KV 0x7f000900 0x853a4].
(* __cmptf2 = __lttf2 = __letf2 0x84f34 (200 B) and __getf2 = __gttf2 0x84ffc (188 B); then __subtf3 0x854c8 (16 B),
   __addtf3 0x854d8 (1996 B), __fe_getround 0x85ca4 (48 B) and __fe_raise_inexact 0x85cd4 (12 B). *)
Definition N_iv : list (Z * Z * Z) := [
  KV3 0x1b24c 0x1b3d0 433384;
  KV3 0x1bc70 0x1c488 432216].
Definition N_sym (k : Z) : Z := tsym N_exact N_iv k.
Definition N_img : RImg := {| img_segs := rsegs; sym := N_sym |}.
