(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad STree Stdio AsanCtrl AsanEmbed
  Harness Adapter Driver ProgA.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Record APS := mkAPS {
  aps_m  : astate;          (* [comment removed for export] *)
  aps_so : stdout_st;       (* [comment removed for export] *)
  aps_resv : list (Z * Z);  (* [comment removed for export] *)
  aps_atop : Z              (* [comment removed for export] *)
}.
Definition aset_m (v : astate) (s : APS) : APS := mkAPS v (aps_so s) (aps_resv s) (aps_atop s).
Definition aset_so (v : stdout_st) (s : APS) : APS := mkAPS (aps_m s) v (aps_resv s) (aps_atop s).

(* [comment removed for export] *)
Definition aps_init (space_beg ptr_array : Z) (resv : list (Z * Z)) (atop : Z) : APS :=
  mkAPS (ainit space_beg ptr_array) stdout_init resv atop.

Local Notation MA := (Monad.M APS) (only parsing).

(* [comment removed for export] *)
Definition alift {R} (t : AM R) : MA R :=
  fun s => ebind (aembed (aps_atop s) t) (fun r => Ret (Ok (r, s))).

(* [comment removed for export] *)
Definition amalloc_M (n : Z) : MA (option AsanCtrl.aptr) :=
  s <- mget ;;
  x <- alift (AsanCtrl.amalloc (aps_atop s) (aps_resv s) (aps_m s) n) ;;
  mupd (aset_m (fst x)) ;;;
  mret (snd x).

Definition afree_M (p : AsanCtrl.aptr) : MA unit :=
  s <- mget ;;
  st' <- alift (AsanCtrl.afree (aps_m s) (Some p)) ;;
  mupd (aset_m st').

Definition aannot_M (p : AsanCtrl.aptr) (cap old new : Z) : MA unit :=
  s <- mget ;;
  st' <- alift (aannotate (aps_m s) p cap old new) ;;
  mupd (aset_m st').

Definition aptr_addr_M (s : APS) (p : AsanCtrl.aptr) : Z := AsanCtrl.aptr_addr (aps_m s) p.

(* [comment removed for export] *)
Definition AAllocAsan : AAlloc :=
  mkAAlloc APS AsanCtrl.aptr amalloc_M afree_M aannot_M aptr_addr_M aps_so aset_so.

(* [comment removed for export] *)
Lemma aps_get_set : forall v s, aps_so (aset_so v s) = v. Proof. reflexivity. Qed.
Lemma aps_set_set : forall v w s, aset_so v (aset_so w s) = aset_so v s. Proof. reflexivity. Qed.
Lemma aps_set_get : forall s, aset_so (aps_so s) s = s. Proof. intros [m so rv tp]; reflexivity. Qed.
Lemma aps_addr_so : forall v s p, aptr_addr_M (aset_so v s) p = aptr_addr_M s p. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma alift_ret : forall {R} (r : R) (s : APS), alift (SRet r) s = Ret (Ok (r, s)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition progAsan_tree (s0 : APS) (rs : Z) (argv : list (list Z)) : itree node (exc unit) := progA_tree AAllocAsan s0 rs argv.
