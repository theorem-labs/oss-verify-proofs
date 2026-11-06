(* The library shape of fuzz_grant's agreement statements: each call of LLVMFuzzerTestOneInput returns 0, writes
   nothing and leaves the file system as it found it. It has the fields of the shape of fuzz_grant's ubsan
   agreement (lib/Prog/AgreeGrant.v, ag_shape), so the plain build's proved realization of SPECX at that shape
   is the plain side of the ASan agreement. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK15 YO09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import AllocSlots.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require SlotAgree.
Import ListNotations.
Open Scope Z_scope.

#[export] Instance grant_shape : lib_shape.
Proof.
  refine {| LIBK := fun pl fs K => K (LL 0 fs []);
    lib_delta := fun n b => b;
    lib_room := fun b n => sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ sb_cap b = SlotAgree.CAP_AG |}.
  intros pl fs K K' H. apply H.
Defined.
