(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import InitMem Zlib_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac zl_range_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  let nbs := eval vm_compute in (Z.of_nat (length bs)) in
  assert (H : rw_cells psegs m A cs);
  [ apply (InitMem.rw_cells_recast psegs m A [CB (length bs) bs] cs);
    [ apply (InitMem.rw_cells_image0 psegs m A bs);
      [ intros a Ha; apply NONE; change (Z.of_nat (length bs)) with nbs in Ha;
        unfold ZL_RELRO_LO, ZL_RELRO_HI, ZL_GOT_LO, ZL_GOT_HI; lia
      | vm_compute; reflexivity | lia | change (Z.of_nat (length bs)) with nbs; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].
Ltac zl_relro_chunk ZS m A cs H := let N := fresh "NONE" in pose proof (proj1 ZS) as N; zl_range_chunk N m A cs H; clear N.
Ltac zl_got_chunk ZS m A cs H := let N := fresh "NONE" in pose proof (proj1 (proj2 ZS)) as N; zl_range_chunk N m A cs H; clear N.

Section Examples.
Context {CE__ : Ceiling.Ceiling} {RN__ : Rnd.RunRnd}.

(* zlib 1.4: zcalloc / zcfree are file-static; inflateInit_ takes their addresses pc-relative (auipc), so no
   GOT slot is read and the 1.3.1 lemma got_zcalloc_cells (slots 0x29398 / 0x293a0) is gone. *)
End Examples.
