(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
     AsanAcct L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ParseSpecsA L5OpmodSpecsA L5DivSpecsA L5UnwindSpecsA XIcptA XIcptAs0Kit L5AUnwK L5AUnwK2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

(* [comment removed for export] *)
Module L5AE2K.
Import L5A. Import L5CA. Import L5SA. Import L5AUK2.
Abbreviation RSEGS := Asan.M.loaded_segments.
(* [comment removed for export] *)
Definition zd_buf : list byte := Eval vm_compute in (match rdn RSEGS (fun _ => None) (Z_to_bv 64 142208) 16 with Some l => l | None => [] end).
Lemma zd_rdn0 : rdn RSEGS (fun _ => None) (Z_to_bv 64 142208) 16 = Some zd_buf. Proof. vm_compute. reflexivity. Qed.
Lemma zd_rdn M : L5.img_clear M 65536 880640 -> rdn RSEGS M (Z_to_bv 64 142208) 16 = Some zd_buf.
Proof. intros IC. rewrite (rdn_img M 65536 880640 IC 16 142208) by (cbn; Lia.lia). exact zd_rdn0. Qed.
Lemma zd_rdn13 M : L5.img_clear M 65536 880640 -> rdn RSEGS M (Z_to_bv 64 142208) 13 = Some (firstn 13 zd_buf).
Proof. intros IC. rewrite (rdn_img M 65536 880640 IC 13 142208) by (cbn; Lia.lia). vm_compute. reflexivity. Qed.
End L5AE2K.
