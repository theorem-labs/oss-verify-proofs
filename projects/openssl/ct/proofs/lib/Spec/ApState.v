(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import BnModel BnTree BgState ApBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ERR_NUM : nat := 16%nat.
Definition ERR_TXT_MALLOCED : Z := 1.
Definition ERR_TXT_STRING : Z := 2.
Definition ERR_MAX_DATA_SIZE : Z := 1024.

(* [comment removed for export] *)
Fixpoint lset {A} (l : list A) (i : nat) (x : A) : list A :=
  match l, i with
  | [], _ => []
  | _ :: l', O => x :: l'
  | y :: l', S i' => y :: lset l' i' x
  end.

Lemma lset_length {A} (l : list A) i x : length (lset l i x) = length l.
Proof. revert i. induction l as [|y l IH]; intros [|i]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma nth_lset_same {A} (l : list A) i x d : (i < length l)%nat -> nth i (lset l i x) d = x.
Proof. revert i. induction l as [|y l IH]; intros [|i] H; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.

Lemma nth_lset_other {A} (l : list A) i j x d : i <> j -> nth j (lset l i x) d = nth j l d.
Proof. revert i j. induction l as [|y l IH]; intros [|i] [|j] H; cbn; try reflexivity; [congruence|]. apply IH. congruence. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record ap_ls (ptr : Type) : Type := mkLS {
  ls_data : list (option (ptr * Z));
  ls_cnf : option (ptr * ptr * ptr)
}.
Arguments mkLS {ptr}.
Arguments ls_data {ptr}.
Arguments ls_cnf {ptr}.

Definition ap_ls0 {ptr} : ap_ls ptr := mkLS (repeat None ERR_NUM) None.

Record ap_st (ptr : Type) : Type := mkAS {
  as_top : nat;
  as_bottom : nat;
  as_file : list (option (ptr * Z));      (* [comment removed for export] *)
  as_func : list (option (ptr * Z));
  as_marks : list Z;
  as_buf : list Z;
  as_line : list Z;
  as_data : list (option (ptr * Z));
  as_dflags : list Z;
  as_cnf : option (ptr * ptr * ptr)
}.
Arguments mkAS {ptr}.
Arguments as_top {ptr}.
Arguments as_bottom {ptr}.
Arguments as_file {ptr}.
Arguments as_func {ptr}.
Arguments as_marks {ptr}.
Arguments as_buf {ptr}.
Arguments as_line {ptr}.
Arguments as_data {ptr}.
Arguments as_dflags {ptr}.
Arguments as_cnf {ptr}.

(* [comment removed for export] *)
Definition st_of_ls {ptr} (ls : ap_ls ptr) : ap_st ptr :=
  mkAS 0 0 (repeat None ERR_NUM) (repeat None ERR_NUM) (repeat 0 ERR_NUM) (repeat 0 ERR_NUM) (repeat (-1) ERR_NUM)
       (ls_data ls) (map (fun d => match d with Some _ => ERR_TXT_MALLOCED | None => 0 end) (ls_data ls)) (ls_cnf ls).
Definition ls_of_st {ptr} (s : ap_st ptr) : ap_ls ptr := mkLS (as_data s) (as_cnf s).

(* [comment removed for export] *)
Section Setters.
Context {ptr : Type}.
Implicit Types s : ap_st ptr.
Definition set_top (v : nat) s := mkAS v (as_bottom s) (as_file s) (as_func s) (as_marks s) (as_buf s) (as_line s) (as_data s) (as_dflags s) (as_cnf s).
Definition set_bottom (v : nat) s := mkAS (as_top s) v (as_file s) (as_func s) (as_marks s) (as_buf s) (as_line s) (as_data s) (as_dflags s) (as_cnf s).
Definition set_file (i : nat) (v : option (ptr * Z)) s := mkAS (as_top s) (as_bottom s) (lset (as_file s) i v) (as_func s) (as_marks s) (as_buf s) (as_line s) (as_data s) (as_dflags s) (as_cnf s).
Definition set_func (i : nat) (v : option (ptr * Z)) s := mkAS (as_top s) (as_bottom s) (as_file s) (lset (as_func s) i v) (as_marks s) (as_buf s) (as_line s) (as_data s) (as_dflags s) (as_cnf s).
Definition set_marks (i : nat) (v : Z) s := mkAS (as_top s) (as_bottom s) (as_file s) (as_func s) (lset (as_marks s) i v) (as_buf s) (as_line s) (as_data s) (as_dflags s) (as_cnf s).
Definition set_buf (i : nat) (v : Z) s := mkAS (as_top s) (as_bottom s) (as_file s) (as_func s) (as_marks s) (lset (as_buf s) i v) (as_line s) (as_data s) (as_dflags s) (as_cnf s).
Definition set_line (i : nat) (v : Z) s := mkAS (as_top s) (as_bottom s) (as_file s) (as_func s) (as_marks s) (as_buf s) (lset (as_line s) i v) (as_data s) (as_dflags s) (as_cnf s).
Definition set_data (i : nat) (v : option (ptr * Z)) s := mkAS (as_top s) (as_bottom s) (as_file s) (as_func s) (as_marks s) (as_buf s) (as_line s) (lset (as_data s) i v) (as_dflags s) (as_cnf s).
Definition set_dflags (i : nat) (v : Z) s := mkAS (as_top s) (as_bottom s) (as_file s) (as_func s) (as_marks s) (as_buf s) (as_line s) (as_data s) (lset (as_dflags s) i v) (as_cnf s).
Definition set_cnf (v : option (ptr * ptr * ptr)) s := mkAS (as_top s) (as_bottom s) (as_file s) (as_func s) (as_marks s) (as_buf s) (as_line s) (as_data s) (as_dflags s) v.
Definition get_file (i : nat) s : option (ptr * Z) := nth i (as_file s) None.
Definition get_func (i : nat) s : option (ptr * Z) := nth i (as_func s) None.
Definition get_marks (i : nat) s : Z := nth i (as_marks s) 0.
Definition get_buf (i : nat) s : Z := nth i (as_buf s) 0.
Definition get_data (i : nat) s : option (ptr * Z) := nth i (as_data s) None.
Definition get_dflags (i : nat) s : Z := nth i (as_dflags s) 0.
End Setters.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Monad.
Context {ptr : Type}.
Local Notation ST := (ap_st ptr) (only parsing).

Definition AM (A : Type) : Type := ST -> aprog ptr (A * ST)%type.

Definition aret {A} (a : A) : AM A := fun s => ARet (a, s).
Definition abind {A B} (m : AM A) (f : A -> AM B) : AM B :=
  fun s => apbind (m s) (fun p => f (fst p) (snd p)).
Definition aunr {A} : AM A := fun _ => AUnr.
Definition aget : AM ST := fun s => ARet (s, s).
Definition aput (s' : ST) : AM unit := fun _ => ARet (tt, s').
Definition amodify (f : ST -> ST) : AM unit := fun s => ARet (tt, f s).
(* [comment removed for export] *)
Definition amalloc (n : Z) : AM ptr :=
  fun s => AMalloc n (fun r => match r with Some p => ARet (p, s) | None => AUnr end).
Definition amalloc_crypto (n : Z) : AM (option ptr) :=
  fun s => if n =? 0 then ARet (None, s) else AMalloc n (fun r => match r with Some p => ARet (Some p, s) | None => AUnr end).
Definition afree (p : ptr) : AM unit := fun s => AFree p (ARet (tt, s)).
(* [comment removed for export] *)
Definition afree_opt (p : option ptr) : AM unit := match p with Some q => afree q | None => aret tt end.
Definition arealloc (p : ptr) (n : Z) : AM ptr :=
  fun s => ARealloc p n (fun r => match r with Some q => ARet (q, s) | None => AUnr end).
Definition areallocS (p : ptr) (n : Z) : AM ptr :=
  fun s => AReallocS p n (fun r => match r with Some q => ARet (q, s) | None => AUnr end).
(* [comment removed for export] *)
Definition areallocI (p : ptr) (n : Z) : AM ptr :=
  fun s => AReallocI p n (fun r => match r with Some q => ARet (q, s) | None => AUnr end).
(* [comment removed for export] *)
Definition arealloc_opt (p : option ptr) (n : Z) : AM ptr :=
  match p with Some q => arealloc q n | None => amalloc n end.
Definition asys (o : sysop) : AM Z := fun s => ASys o (fun r => ARet (r, s)).

(* [comment removed for export] *)
Definition abt {A} (t : btree ptr A) : AM A := fun s => apbind (bt_embed t) (fun a => ARet (a, s)).

End Monad.

Declare Scope am_scope.
Notation "x <- m ;; k" := (abind m (fun x => k)) (at level 100, m at next level, right associativity) : am_scope.
Notation "m ;;; k" := (abind m (fun _ => k)) (at level 100, right associativity) : am_scope.
Notation "' pat <- m ;; k" := (abind m (fun x__ => let 'pat := x__ in k)) (at level 100, pat pattern, m at next level, right associativity) : am_scope.
