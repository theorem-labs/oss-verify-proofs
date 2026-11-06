(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_T80p LB_Inv LB_Tree LB_Ljn7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_TF2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_T80p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Ljn7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.LB_Dead.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section LBCEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition bigb (n : Z) : Z := if MMAP_THRESHOLD <=? n then bigmap n else 0.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ROOM (BL : list blk) (P : Z -> Z) (n : Z) : Prop :=
  (n < MMAP_THRESHOLD -> LR BL (size_to_class n) + 1 <= P (size_to_class n))
  /\ (MMAP_THRESHOLD <= n -> n63 BL + 1 <= P 63)
  /\ zlen BL + 1 <= NBCAP.   (* [comment removed for export] *)

Definition CORE_POSTQ (n : Z) (BL : list blk) (P : Z -> Z) (L1 : mled) (r : mstate * option (aptr * Z)) : Prop :=
  match snd r with
  | None => SINV x0 (fst r) BL /\ AQ (fst r) BL P
  | Some (g, idx) => forall bg off, hosts (fst r) bg g ->
      SINV x0 (fst r) ((((fst bg, sstart (MR (fst r) g) idx), off), n) :: BL)
      /\ AQ (fst r) ((((fst bg, sstart (MR (fst r) g) idx), off), n) :: BL) P
  end.

Definition malloc_core_fq_stmt : Prop :=
  forall st L BL LS P n B,
    INVL x0 st L BL LS -> TF0 st -> SINV x0 st BL -> AQ st BL P -> 0 <= n -> ROOM BL P n ->
    PHI P + R63 BL + bigb n <= B + 3 * PGSZ ->
    fqtree B L (malloc_core full_lay st n) (CORE_POSTQ n BL P).

End LBCEIL.
