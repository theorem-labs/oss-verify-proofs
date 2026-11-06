(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import SFModel.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Malloc Require Import MallocRep MallocHINV MallocTree.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition AGP : Z := 0x1a800.          (* [comment removed for export] *)
Definition ATP : Z := 0x1a620.          (* [comment removed for export] *)
Definition ERRNO : Z := ATP - 164.      (* [comment removed for export] *)
Definition MALLOC_SYM : Z := 0x1596c.   (* [comment removed for export] *)
Definition FREE_SYM : Z := 0x156e0.     (* [comment removed for export] *)
Definition MALLOC_STACK : Z := 8192.    (* [comment removed for export] *)
Definition FREE_STACK : Z := 8192.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition MEDTAB : Z := 0x1a060.        (* [comment removed for export] *)
Definition alloc_static (a : Z) : Prop :=
  (MLOCK <= a < MLOCK + 4) \/ (LIBC <= a < CTX + 928) \/ (ERRNO <= a < ERRNO + 4) \/ (MEDTAB <= a < MEDTAB + 4).
(* [comment removed for export] *)
Definition medtab_cells : list cell := [C1 (Z_to_bv 8 28); C1 (Z_to_bv 8 24); C1 (Z_to_bv 8 20); C1 (Z_to_bv 8 32)].

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition in_block (LB : list block) (a : Z) : Prop :=
  exists b, In b LB /\ blk_addr b <= a < blk_addr b + blk_size b.

(* [comment removed for export] *)
Definition client_addr (LB : list block) (SP : Z) (a : Z) : Prop :=
  SP <= a \/ (0x19000 <= a < 0x1b000 /\ ~ alloc_static a) \/ in_block LB a.

(* [comment removed for export] *)
Definition client_range (LB : list block) (SP : Z) (A n : Z) : Prop :=
  SP <= A
  \/ (0x19000 <= A /\ A + n <= 0x1b000 /\ (A + n <= MLOCK \/ MLOCK + 4 <= A) /\ (A + n <= LIBC \/ CTX + 928 <= A)
      /\ (A + n <= ERRNO \/ ERRNO + 4 <= A) /\ (A + n <= MEDTAB \/ MEDTAB + 4 <= A))
  \/ (exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b).

Lemma client_range_addr : forall LB SP A n a,
  client_range LB SP A n -> A <= a < A + n -> client_addr LB SP a.
Proof.
  intros LB SP A n a HR Ha. unfold client_range, client_addr, alloc_static, MLOCK, LIBC, CTX, ERRNO, ATP, MEDTAB in *.
  destruct HR as [H|[H|(b & Hb & H1 & H2)]]; [left; lia| right; left; lia| right; right; exists b; split; [exact Hb|lia]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition block_range (A n : Z) : Prop :=
  0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= ATOP /\ (A + n <= 0x10000 \/ 0x1b000 <= A).

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition client_write_ok (LB : list block) (iv : Z * Z) : Prop :=
  ATOP <= fst iv
  \/ (0x19000 <= fst iv /\ snd iv <= 0x1b000 /\ (snd iv <= MLOCK \/ MLOCK + 4 <= fst iv) /\ (snd iv <= LIBC \/ CTX + 928 <= fst iv)
      /\ (snd iv <= ERRNO \/ ERRNO + 4 <= fst iv) /\ (snd iv <= MEDTAB \/ MEDTAB + 4 <= fst iv))
  \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bptr_eqb (p q : bptr) : bool :=
  aptr_eqb (fst p) (fst q) && Z.eqb (snd p) (snd q).
(* [comment removed for export] *)
Definition lb_remove (p : bptr) (LB : list block) : list block :=
  filter (fun b => negb (bptr_eqb (blk_id b) p)) LB.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)


End CANSEC1.
