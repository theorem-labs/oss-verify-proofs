(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ceil_window {CE : Ceiling} : Prop := (0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000)%Z.

Lemma ceil_window_holds {CE : Ceiling} : ceil_window.
Proof. exact alloc_ceiling_range. Qed.
