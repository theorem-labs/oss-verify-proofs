(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint fib_nat (n : nat) : Z :=
  match n with
  | O => 0
  | S k => match k with O => 1 | S k' => fib_nat k + fib_nat k' end
  end.
Definition fib (d : Z) : Z := fib_nat (Z.to_nat d).

Record gtree := {
  g_lo : Z;
  g_hi : Z;
  g_par : Z -> Z;
  g_leaf : Z -> bool;
  g_code : Z -> Z;
  g_wt : Z -> Z;
  g_ext : Z -> Z
}.

Definition g_pos (g : gtree) (i : Z) : Prop := g_lo g <= i <= g_hi g.

Record gtree_ok (g : gtree) : Prop := {

  go_range : g_lo g < g_hi g;
  go_par_lt : forall i, g_lo g < i <= g_hi g -> g_lo g <= g_par g i < i;
  go_par_int : forall i, g_lo g < i <= g_hi g -> g_leaf g (g_par g i) = false;
  go_two : forall p, g_pos g p -> g_leaf g p = false ->
             exists a b, a <> b /\ g_lo g < a <= g_hi g /\ g_lo g < b <= g_hi g /\ g_par g a = p /\ g_par g b = p
             /\ (forall c, g_lo g < c <= g_hi g -> g_par g c = p -> c = a \/ c = b);

  go_wt_leaf : forall i, g_pos g i -> g_leaf g i = true -> 1 <= g_wt g i;
  go_wt_sum : forall p a b, g_pos g p -> g_leaf g p = false ->
             g_lo g < a <= g_hi g -> g_lo g < b <= g_hi g -> a <> b -> g_par g a = p -> g_par g b = p ->
             g_wt g p = g_wt g a + g_wt g b;

  go_code_inj : forall i j, g_pos g i -> g_pos g j -> g_leaf g i = true -> g_leaf g j = true ->
             g_code g i = g_code g j -> i = j;

  go_ext_inj : forall i j, g_lo g < i <= g_hi g -> g_lo g < j <= g_hi g -> g_ext g i = g_ext g j -> i = j;
  go_ext_nonneg : forall i, g_lo g < i <= g_hi g -> 0 <= g_ext g i;

  go_ext_sib : forall a b, g_lo g < a <= g_hi g -> g_lo g < b <= g_hi g -> a <> b -> g_par g a = g_par g b ->
             (g_ext g a = g_ext g b + 1 \/ g_ext g b = g_ext g a + 1);
  go_ext_par : forall i, g_lo g < i <= g_hi g -> g_lo g < g_par g i -> g_ext g i < g_ext g (g_par g i);
  go_greedy : forall i x, g_lo g < i <= g_hi g -> g_lo g < x <= g_hi g ->
             g_ext g i < g_ext g x ->
             (g_leaf g x = true \/
              exists c, g_lo g < c <= g_hi g /\ g_par g c = x /\ g_ext g c < g_ext g i) ->
             g_wt g i <= g_wt g x
}.

Fixpoint g_depth_fuel (g : gtree) (fuel : nat) (i : Z) : Z :=
  match fuel with
  | O => 0
  | S f => if i <=? g_lo g then 0 else 1 + g_depth_fuel g f (g_par g i)
  end.
Definition g_depth (g : gtree) (i : Z) : Z := g_depth_fuel g (Z.to_nat (g_hi g - g_lo g + 1)) i.

Definition g_W (g : gtree) : Z := g_wt g (g_lo g).

Record ztree := {
  zt_E : Z;
  zt_ML : Z;
  zt_g : gtree;
  zt_len : Z -> Z
}.

Definition zt_is_leaf_of (t : ztree) (c i : Z) : Prop :=
  g_pos (zt_g t) i /\ g_leaf (zt_g t) i = true /\ g_code (zt_g t) i = c.
Definition zt_used (t : ztree) (c : Z) : Prop := exists i, zt_is_leaf_of t c i.

Definition hist := Z -> Z.
Definition rep_step (ML : Z) (h : hist) (bits : Z) : hist :=
  fun b => if b =? bits then h b - 1
           else if b =? bits + 1 then (if b =? ML then h b + 2 - 1 else h b + 2)
           else if b =? ML then h b - 1 else h b.

Fixpoint rep_find (fuel : nat) (h : hist) (bits : Z) : Z :=
  match fuel with O => bits | S f => if h bits =? 0 then rep_find f h (bits - 1) else bits end.
Fixpoint rep_iter (n : nat) (ML : Z) (h : hist) : hist :=
  match n with O => h | S k => rep_iter k ML (rep_step ML h (rep_find (Z.to_nat ML) h (ML - 1))) end.

Definition kraftZ (ML : Z) (h : hist) : Z := zsum (fun b => h b * 2 ^ (ML - b)) 1 (Z.to_nat ML).
Definition repair (ML : Z) (h : hist) : hist := rep_iter (Z.to_nat (kraftZ ML h - 2 ^ ML)) ML h.

Definition g_hist (g : gtree) (f : Z -> Z) : hist :=
  fun b => zsum (fun i => zind (g_leaf g i && (f i =? b))) (g_lo g) (Z.to_nat (g_hi g - g_lo g + 1)).

Record ztree_ok (t : ztree) : Prop := {
  zo_g : gtree_ok (zt_g t);
  zo_E : forall i, g_pos (zt_g t) i -> g_leaf (zt_g t) i = true -> 0 <= g_code (zt_g t) i < zt_E t;
  zo_ML : 1 <= zt_ML t;

  zo_len_used : forall c i, zt_is_leaf_of t c i -> 1 <= zt_len t c <= zt_ML t;
  zo_len_unused : forall c, 0 <= c < zt_E t -> ~ zt_used t c -> zt_len t c = 0;

  zo_len_noovf : (forall i, g_pos (zt_g t) i -> g_leaf (zt_g t) i = true -> g_depth (zt_g t) i <= zt_ML t) ->
                 forall c i, zt_is_leaf_of t c i -> zt_len t c = g_depth (zt_g t) i;

  zo_len_hist : forall b, 1 <= b <= zt_ML t ->
                 g_hist (zt_g t) (fun i => zt_len t (g_code (zt_g t) i)) b
                 = repair (zt_ML t) (g_hist (zt_g t) (fun i => Z.min (g_depth (zt_g t) i) (zt_ML t))) b;

  zo_len_rank : (exists i, g_pos (zt_g t) i /\ g_leaf (zt_g t) i = true /\ zt_ML t < g_depth (zt_g t) i) ->
                 forall i j, g_pos (zt_g t) i -> g_pos (zt_g t) j -> g_leaf (zt_g t) i = true -> g_leaf (zt_g t) j = true ->
                 g_wt (zt_g t) i < g_wt (zt_g t) j -> zt_len t (g_code (zt_g t) j) <= zt_len t (g_code (zt_g t) i)
}.

Record block_trees := {
  bt_L : ztree;
  bt_D : ztree;
  bt_B : ztree
}.
