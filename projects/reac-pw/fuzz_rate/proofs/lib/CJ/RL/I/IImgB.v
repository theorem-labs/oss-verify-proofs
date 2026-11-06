(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cjson/cjson_read_fuzzer/lib/RL/I/IImgB.v for this unit: its address tables keep some of cjson's keys and add this unit's own, each at an address of this unit's asan-ubsan image (lib/B/Img0.v); the definitions B_* are renamed N_* and bsegs is renamed rsegs; the notations KV and KV3 are no longer Local; and the imports name this unit's modules. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/CJ/RL/I/IImgB.v, with its module paths and addresses changed; 2 of its 18 lines of code are new or changed and 140 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/CJ/RL/I/IImgP.v at ca77675ebeb; the same keys mapped to the addresses of the ASan image A (fuzz_role.asan, lib/A/Img0.v). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/CJ/RL/I/IImgA.v at b2957340e99a; the same keys mapped to the addresses of reac-pw/fuzz_rate's ASan image A (fuzz_rate.asan, lib/A/Img0.v). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/CJ/RL/I/IImgA.v at fbf0205dfe3d; the same keys mapped to the addresses of reac-pw/fuzz_rate's ASan image B (fuzz_rate.asan-ubsan, lib/AU/Img0.v), each measured on that image. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.I Require Export IInst.
Import ListNotations.
Open Scope Z_scope.

Notation KV a b := (a, b) (only parsing).
Notation KV3 a b c := (a, b, c) (only parsing).
(* Measured on fuzz_rate.asan-ubsan (unstripped sha256 a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1,
   pinned c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; same bytes at every address below).
   The rounding-mode table read by __fe_getround (0x85a64 auipc a1,0xfff9c; addi a1,a1,-784: 0x21754 in .rodata, the
   12 bytes 03 00 00 00 01 00 00 00 02 00 00 00 of the plain image's 0x10684); then __extendsftf2 0x84ff4 (348 B, the
   donor's key) and __floatditf 0x85150 (292 B, a synthetic key: the donor's key space has no __floatditf). *)
Definition N_exact : list (Z * Z) := [
  KV 0x1145c 0x21754;
  KV 0x200dc 0x84ff4;
  KV 0x7f000900 0x85150].
(* __cmptf2 = __lttf2 = __letf2 0x84ce0 (200 B) and __getf2 = __gttf2 0x84da8 (188 B); then __subtf3 0x85274 (16 B),
   __addtf3 0x85284 (1996 B), __fe_getround 0x85a50 (48 B) and __fe_raise_inexact 0x85a80 (12 B). Each of the eight
   functions has the bytes of the image-A function (only __fe_getround's pc-relative addi differs) and of the plain
   image's. *)
Definition N_iv : list (Z * Z * Z) := [
  KV3 0x1b24c 0x1b3d0 432788;
  KV3 0x1bc70 0x1c488 431620].
Definition N_sym (k : Z) : Z := tsym N_exact N_iv k.
Definition N_img : RImg := {| img_segs := rsegs; sym := N_sym |}.
