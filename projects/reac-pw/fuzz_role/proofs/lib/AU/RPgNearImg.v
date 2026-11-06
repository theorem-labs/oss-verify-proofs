(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cjson/cjson_read_fuzzer/lib/RL/I/IImgA.v for this unit: its address tables keep some of cjson's keys and add this unit's own, each at an address of this unit's asan image (lib/A/Img0.v); the definitions A_* are renamed N_* and asegs is renamed rsegs; the notations KV and KV3 are no longer Local; and the imports name this unit's modules. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/CJ/RL/I/IImgA.v, with its module paths and addresses changed; 10 of its 26 lines of code are new or changed and 141 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/CJ/RL/I/IImgP.v at ca77675ebeb; the same keys mapped to the addresses of the ASan image A (fuzz_role.asan, lib/A/Img0.v). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/CJ/RL/I/IImgA.v at b2957340e99a; the same keys mapped to the addresses of reac-pw/fuzz_rate's ASan image A (fuzz_rate.asan, lib/A/Img0.v). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/CJ/RL/I/IImgA.v at b089f28d962e, with the address constants of proofs/reac-pw/fuzz_rate/lib/A/RtPgNearC.v at b089f28d962e; the same keys mapped to the addresses of reac-pw/fuzz_rate's ASan image B (fuzz_rate.asan-ubsan, lib/AU/Img0.v), and pod_nearest's entry, .got slot and shadow-offset cell are image B's. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgNearImgB.v at 7e722b95884; relocated to reac-pw/fuzz_role's ASan image B (fuzz_role.asan-ubsan, lib/AU/Img0.v): the module paths name reac-pw/fuzz_role, and pod_nearest's entry (0x82eb4), the .got slot (0x9aad0), the shadow-offset cell (0xa3678), the five soft-float callees and the symbol map N_img are role's image-B addresses, each measured on that image. *)
(** Every address of reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan, pinned sha256
    b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; unstripped twin
    dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a) that the image-B walk of pod_nearest
    (lib/AU/RPgNearC.v, RPgNearW.v, RPgNear.v, RPgNearA.v) uses, in this one file: those files state every
    other pc as an offset from B_POD_NEAREST. A unit whose image-B pod_nearest is the same code at other addresses
    takes the walk with its own copy of this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.RL.I Require Export IInst.
Import ListNotations.
Open Scope Z_scope.

(** pod_nearest: 0x82eb4, 384 bytes, 96 instructions. The code reads the .got slot B_GOT_SHADOW, which holds the
    address B_SHADOW_CELL of the shadow-offset cell (the 8-byte object __asan_shadow_memory_dynamic_address). *)
Definition B_POD_NEAREST : Z := 0x82eb4.
Definition B_GOT_SHADOW : Z := 0x9aad0.
Definition B_SHADOW_CELL : Z := 0xa3678.

(** The soft-float callees pod_nearest calls: __extendsftf2, __cmptf2 (= __lttf2 = __letf2), __getf2
    (= __gttf2), __floatditf and __subtf3. *)
Definition B_EXTENDSFTF2 : Z := 0x839e8.
Definition B_CMPTF2 : Z := 0x836d4.
Definition B_GETF2 : Z := 0x8379c.
Definition B_FLOATDITF : Z := 0x83b44.
Definition B_SUBTF3 : Z := 0x83c68.

Notation KV a b := (a, b) (only parsing).
Notation KV3 a b c := (a, b, c) (only parsing).
(* Measured on fuzz_role.asan-ubsan (unstripped sha256 dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a,
   pinned b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; same bytes at every address below).
   The rounding-mode table read by __fe_getround (0x84458 auipc a1; addi a1: 0x21614 in .rodata, the 12 bytes
   03 00 00 00 01 00 00 00 02 00 00 00 of the plain image's 0x10640); then __extendsftf2 0x839e8 (348 B, the
   donor's key) and __floatditf 0x83b44 (292 B, a synthetic key: the donor's key space has no __floatditf). *)
Definition N_exact : list (Z * Z) := [
  KV 0x1145c 0x21614;
  KV 0x200dc 0x839e8;
  KV 0x7f000900 0x83b44].
(* __cmptf2 = __lttf2 = __letf2 0x836d4 (200 B) and __getf2 = __gttf2 0x8379c (188 B); then __subtf3 0x83c68 (16 B),
   __addtf3 0x83c78 (1996 B), __fe_getround 0x84444 (48 B) and __fe_raise_inexact 0x84474 (12 B). Each of these
   nine functions has the words of the image-A function (only __fe_getround's pc-relative addi at +0x18 differs)
   and of reac-pw/fuzz_rate's image-B function (only __fe_getround's auipc / addi pair at +0x14 / +0x18 differs). *)
Definition N_iv : list (Z * Z * Z) := [
  KV3 0x1b24c 0x1b3d0 427144;
  KV3 0x1bc70 0x1c488 425976].
Definition N_sym (k : Z) : Z := tsym N_exact N_iv k.
Definition N_img : RImg := {| img_segs := rsegs; sym := N_sym |}.
