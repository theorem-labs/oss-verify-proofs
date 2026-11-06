(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
     AsanAcct L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0 L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5ParseSpecsAB0 L5OpmodSpecsAB0 L5DivSpecsAB0 L5UnwindSpecsAB0 XIcptAB0 XIcptAs0KitB0 L5BUnwK L5BUnwK2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

(* [comment removed for export] *)
Module L5BE2K.
Import L5A. Import L5CA. Import L5SA. Import L5AUK2.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
(* [comment removed for export] *)
Definition zd_buf : list byte := Eval vm_compute in (match rdn RSEGS (fun _ => None) (Z_to_bv 64 142528) 16 with Some l => l | None => [] end).
Lemma zd_rdn0 : rdn RSEGS (fun _ => None) (Z_to_bv 64 142528) 16 = Some zd_buf. Proof. vm_compute. reflexivity. Qed.
Lemma zd_rdn M : L5.img_clear M 65536 884736 -> rdn RSEGS M (Z_to_bv 64 142528) 16 = Some zd_buf.
Proof. intros IC. rewrite (rdn_img M 65536 884736 IC 16 142528) by (cbn; Lia.lia). exact zd_rdn0. Qed.
Lemma zd_rdn13 M : L5.img_clear M 65536 884736 -> rdn RSEGS M (Z_to_bv 64 142528) 13 = Some (firstn 13 zd_buf).
Proof. intros IC. rewrite (rdn_img M 65536 884736 IC 13 142528) by (cbn; Lia.lia). vm_compute. reflexivity. Qed.
End L5BE2K.
