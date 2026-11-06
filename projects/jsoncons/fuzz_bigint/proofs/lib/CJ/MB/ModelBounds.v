(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Lib Require Import Decode.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Spec Require Import STree Malloc KInv MI_Kit MI_Arith.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Bridge Require Import BrRes.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.MB Require Import MBBase MBMeta MBSlot MBFree.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Lib Require Import RunP.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


Theorem creach_SH cs L : creach cs L -> SH cs.
Proof.
  induction 1 as [resv|cs L n L' cs' r HR IH Hn Hp|cs L c L' cs' HR IH Hc Hp].
  - unfold SH. cbn. lia.
  - exact (cpath_leaves (fun x => SH (fst x)) L (cmalloc cs n) L' (cs', r) Hp (cmalloc_lv cs n IH)).
  - exact (cpath_leaves SH L (cfree cs (Some c)) L' cs' Hp (cfree_lv cs c IH)).
Qed.

Theorem model_bounds_proof : model_bounds.
Proof.
  constructor.
  - intros cs L n HR Hn Hso. apply cmalloc_g; [exact (creach_SH cs L HR)| exact Hn| exact Hso].
  - intros cs L c HR Hc. apply cfree_g.
Qed.
End CEIL_WRAP_1.


(* [comment removed for export] *)
