(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import InitMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Zlib_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac zl_range_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  let nbs := eval vm_compute in (Z.of_nat (length bs)) in
  assert (H : rw_cells usegs m A cs);
  [ apply (InitMem.rw_cells_recast usegs m A [CB (length bs) bs] cs);
    [ apply (InitMem.rw_cells_image0 usegs m A bs);
      [ intros a Ha; apply NONE; change (Z.of_nat (length bs)) with nbs in Ha;
        unfold ZL_RELRO_LO, ZL_RELRO_HI, ZL_GOT_LO, ZL_GOT_HI; lia
      | vm_compute; reflexivity | lia | change (Z.of_nat (length bs)) with nbs; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].
Ltac zl_relro_chunk ZS m A cs H := let N := fresh "NONE" in pose proof (proj1 ZS) as N; zl_range_chunk N m A cs H; clear N.
Ltac zl_got_chunk ZS m A cs H := let N := fresh "NONE" in pose proof (proj1 (proj2 ZS)) as N; zl_range_chunk N m A cs H; clear N.

Section Examples.
Context {CE__ : Ceiling.Ceiling} {RN__ : Rnd.RunRnd}.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* 1.4 UBSan: inflateInit2_ / deflateInit2_ compute zcalloc / zcfree pc-relative (auipc + add) and read no GOT slot,
   so the 1.3.1 lemma got_zcalloc_cells (slots 0x2c298 / 0x2c2a0 holding 0x1ad20 / 0x1ad30) is gone; at 1.4 those
   cells hold the configuration table (a worker's small U/Z_iinit dropped the same lemma). *)
End Examples.
