(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cjson/cjson_read_fuzzer/lib/RL/I/IImgU.v for this unit: its address tables keep some of cjson's keys and add this unit's own, each at an address of this unit's ubsan image (lib/U/Img0.v); the definitions U_* are renamed N_* and usegs is renamed rsegs; the notations KV and KV3 are no longer Local; the Lia, Nia and Nra cache settings are removed; and the imports name this unit's modules. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/CJ/RL/I/IImgU.v, with its module paths, addresses and numbers changed; 1 of its 18 lines of code is new or changed and 171 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.I Require Export IInst.
Import ListNotations.
Open Scope Z_scope.

Notation KV a b := (a, b) (only parsing).
Notation KV3 a b c := (a, b, c) (only parsing).
(* The rounding-mode table read by __fe_getround; then __extendsftf2 (348 B, the donor's key) and
   __floatditf (292 B, a synthetic key: the donor's key space has no __floatditf). *)
Definition N_exact : list (Z * Z) := [
  KV 0x1145c 0x105f0;
  KV 0x200dc 0x152f8;
  KV 0x7f000900 0x15454].
(* __cmptf2 (200 B) and __getf2 (188 B); then __subtf3 (16 B), __addtf3 (1996 B),
   __fe_getround (48 B) and __fe_raise_inexact (12 B). *)
Definition N_iv : list (Z * Z * Z) := [
  KV3 0x1b24c 0x1b3d0 (-24792);
  KV3 0x1bc70 0x1c488 (-26360)].
Definition N_sym (k : Z) : Z := tsym N_exact N_iv k.
Definition N_img : RImg := {| img_segs := rsegs; sym := N_sym |}.
