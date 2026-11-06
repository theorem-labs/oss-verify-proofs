(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import BnBase BnWords BnKara BnModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bnref : Type := nat.
Definition RB1 : bnref := 0%nat.
Definition RB2 : bnref := 1%nat.
Definition RB3 : bnref := 2%nat.
Definition RB4 : bnref := 3%nat.
Definition RB5 : bnref := 4%nat.
Definition RMontRR : bnref := 5%nat.
Definition RMontN : bnref := 6%nat.
Definition RMontNi : bnref := 7%nat.
Definition RRecpN : bnref := 8%nat.
Definition RRecpNr : bnref := 9%nat.
Definition RTmod : bnref := 10%nat.
Definition ROne : bnref := 11%nat.
Definition NFIX : nat := 12%nat.
Definition RPool (i : nat) : bnref := (NFIX + i)%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record bg_ctx (ptr : Type) : Type := mkGx {
  gx_items : list ptr;
  gx_current : option nat;
  gx_pused : nat;
  gx_indexes : option ptr;
  gx_frames : list nat;
  gx_ssize : nat;
  gx_used : nat;
  gx_err_stack : nat;
  gx_too_many : bool
}.
Arguments mkGx {ptr}.
Arguments gx_items {ptr}.
Arguments gx_current {ptr}.
Arguments gx_pused {ptr}.
Arguments gx_indexes {ptr}.
Arguments gx_frames {ptr}.
Arguments gx_ssize {ptr}.
Arguments gx_used {ptr}.
Arguments gx_err_stack {ptr}.
Arguments gx_too_many {ptr}.

Definition gx_nil {ptr} : bg_ctx ptr := mkGx [] None 0 None [] 0 0 0 false.

(* [comment removed for export] *)
Record bstate (ptr : Type) : Type := mkST {
  st_bns : list (bignum ptr);
  st_ctx : bg_ctx ptr;
  st_ri : Z;
  st_n0 : Z;
  st_rbits : Z;
  st_rshift : Z
}.
Arguments mkST {ptr}.
Arguments st_bns {ptr}.
Arguments st_ctx {ptr}.
Arguments st_ri {ptr}.
Arguments st_n0 {ptr}.
Arguments st_rbits {ptr}.
Arguments st_rshift {ptr}.

(* [comment removed for export] *)
Definition bn_const_one {ptr} : bignum ptr := mkBN None [1] 1 false BN_FLG_STATIC_DATA.

(* [comment removed for export] *)
Definition st_init {ptr} : bstate ptr :=
  mkST (repeat (bn_nil 0) 11 ++ [bn_const_one]) gx_nil 0 0 0 0.

Definition getbn {ptr} (r : bnref) (s : bstate ptr) : bignum ptr := nth r (st_bns s) (bn_nil 0).

Definition set_bns {ptr} (l : list (bignum ptr)) (s : bstate ptr) : bstate ptr :=
  mkST l (st_ctx s) (st_ri s) (st_n0 s) (st_rbits s) (st_rshift s).
Definition setbn {ptr} (r : bnref) (b : bignum ptr) (s : bstate ptr) : bstate ptr :=
  set_bns (list_set (st_bns s) r b) s.
Definition set_ctx {ptr} (c : bg_ctx ptr) (s : bstate ptr) : bstate ptr :=
  mkST (st_bns s) c (st_ri s) (st_n0 s) (st_rbits s) (st_rshift s).
Definition set_mont {ptr} (ri n0 : Z) (s : bstate ptr) : bstate ptr :=
  mkST (st_bns s) (st_ctx s) ri n0 (st_rbits s) (st_rshift s).
Definition set_recp {ptr} (bits shift : Z) (s : bstate ptr) : bstate ptr :=
  mkST (st_bns s) (st_ctx s) (st_ri s) (st_n0 s) bits shift.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Monad.
Context {M : Type -> Type} {ptr : Type}.
Variable ops : bn_ops M ptr.

Local Notation ST := (bstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).

Definition BM (A : Type) : Type := ST -> M (A * ST)%type.

Definition bret {A} (a : A) : BM A := fun s => ret ops (a, s).
Definition bbind {A B} (m : BM A) (f : A -> BM B) : BM B :=
  fun s => bind ops (m s) (fun p => f (fst p) (snd p)).
Definition bunr {A} : BM A := fun _ => unreachable ops.
Definition bget (r : bnref) : BM BN := fun s => ret ops (getbn r s, s).
Definition bset (r : bnref) (b : BN) : BM unit := fun s => ret ops (tt, setbn r b s).
Definition bgetst : BM ST := fun s => ret ops (s, s).
Definition bgetctx : BM (bg_ctx ptr) := fun s => ret ops (st_ctx s, s).
Definition bsetctx (c : bg_ctx ptr) : BM unit := fun s => ret ops (tt, set_ctx c s).
Definition bsetbns (l : list BN) : BM unit := fun s => ret ops (tt, set_bns l s).
Definition bsetmont (ri n0 : Z) : BM unit := fun s => ret ops (tt, set_mont ri n0 s).
Definition bsetrecp (bits shift : Z) : BM unit := fun s => ret ops (tt, set_recp bits shift s).
(* [comment removed for export] *)
Definition bmalloc (n : Z) : BM ptr :=
  fun s => bind ops (lib_malloc ops n) (fun r => match r with Some p => ret ops (p, s) | None => unreachable ops end).
Definition bfree (p : ptr) : BM unit := fun s => bind ops (lib_free ops p) (fun _ => ret ops (tt, s)).
(* [comment removed for export] *)
Definition bfree_opt (p : option ptr) : BM unit := match p with Some q => bfree q | None => bret tt end.

End Monad.
