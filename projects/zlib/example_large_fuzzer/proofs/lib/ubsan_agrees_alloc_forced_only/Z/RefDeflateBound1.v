(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BvAux.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflateEnd1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Deflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition db_fixed (n : Z) : Z := n / 2 ^ 3 + n + n / 2 ^ 8 + n / 2 ^ 9 + 4.
Definition db_stored (n : Z) : Z := n / 2 ^ 5 + n + n / 2 ^ 7 + n / 2 ^ 11 + 7.
(* [comment removed for export] *)
Definition db_wraplen (wrap strstart : Z) : Z :=
  if wrap =? 0 then 0
  else if wrap =? 1 then 6 + (if negb (strstart =? 0) then 4 else 0)
  else if wrap =? 2 then 18 else 6.
(* [comment removed for export] *)
Definition db_result (n wl wbits hbits level : Z) : Z :=
  if negb (wbits =? 15) || negb (hbits =? 15)
  then (if (wbits <=? hbits) && negb (level =? 0) then db_fixed n else db_stored n) + wl
  else n / 2 ^ 12 + n + n / 2 ^ 14 + n / 2 ^ 25 + wl + 7.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Entry.

(* [comment removed for export] *)
Local Ltac stcase :=
  lazymatch goal with
  | |- _ mod _ = 0 => subst; vm_compute; reflexivity
  | |- _ mod _ <> 0 => subst; vm_compute; discriminate
  | |- ~ (_ mod _ = 0) => subst; vm_compute; discriminate
  | |- 113 < _ => lia
  | |- ~ (113 < _) => lia
  | |- 68 >= _ => lia
  | |- ~ (68 >= _) => lia
  end.
End Entry.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Wrap.

(* [comment removed for export] *)

End Wrap.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Tail.
End Tail.
