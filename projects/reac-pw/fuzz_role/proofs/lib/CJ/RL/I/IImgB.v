(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cjson/cjson_read_fuzzer/lib/RL/I/IImgB.v for this unit: its address tables keep some of cjson's keys and add this unit's own, each at an address of this unit's asan-ubsan image (lib/B/Img0.v); the definitions B_* are renamed N_* and bsegs is renamed rsegs; the notations KV and KV3 are no longer Local; and the imports name this unit's modules. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/CJ/RL/I/IImgB.v, with its module paths and addresses changed; 2 of its 18 lines of code are new or changed and 140 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/CJ/RL/I/IImgP.v at ca77675ebeb; the same keys mapped to the addresses of the ASan image A (fuzz_role.asan, lib/A/Img0.v). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/CJ/RL/I/IImgA.v at b2957340e99a; the same keys mapped to the addresses of reac-pw/fuzz_rate's ASan image A (fuzz_rate.asan, lib/A/Img0.v). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/CJ/RL/I/IImgA.v at fbf0205dfe3d; the same keys mapped to the addresses of reac-pw/fuzz_rate's ASan image B (fuzz_rate.asan-ubsan, lib/AU/Img0.v), each measured on that image. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/CJ/RL/I/IImgB.v at 078e902e9693; the module paths name reac-pw/fuzz_role, and the same keys are mapped to the addresses of reac-pw/fuzz_role's ASan image B (fuzz_role.asan-ubsan, lib/AU/Img0.v), each measured on that image. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.I Require Export IInst.
Import ListNotations.
Open Scope Z_scope.

Notation KV a b := (a, b) (only parsing).
Notation KV3 a b c := (a, b, c) (only parsing).
(* Measured on fuzz_role.asan-ubsan (unstripped sha256 dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a,
   pinned b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; same bytes at every address below).
   The rounding-mode table read by __fe_getround (0x84458 auipc a1,0xfff9d; addi a1,a1,0x1bc: 0x21614 in .rodata, the
   12 bytes 03 00 00 00 01 00 00 00 02 00 00 00 of the plain image's 0x10640); then __extendsftf2 0x839e8 (348 B, the
   donor's key) and __floatditf 0x83b44 (292 B, a synthetic key: the donor's key space has no __floatditf). *)
Definition N_exact : list (Z * Z) := [
  KV 0x1145c 0x21614;
  KV 0x200dc 0x839e8;
  KV 0x7f000900 0x83b44].
(* __cmptf2 = __lttf2 = __letf2 0x836d4 (200 B) and __getf2 = __gttf2 0x8379c (188 B); then __subtf3 0x83c68 (16 B),
   __addtf3 0x83c78 (1996 B), __fe_getround 0x84444 (48 B) and __fe_raise_inexact 0x84474 (12 B). Each of the eight
   functions has the bytes of the image-A function (only __fe_getround's pc-relative addi differs) and of the plain
   image's. *)
Definition N_iv : list (Z * Z * Z) := [
  KV3 0x1b24c 0x1b3d0 427144;
  KV3 0x1bc70 0x1c488 425976].
Definition N_sym (k : Z) : Z := tsym N_exact N_iv k.
Definition N_img : RImg := {| img_segs := rsegs; sym := N_sym |}.
