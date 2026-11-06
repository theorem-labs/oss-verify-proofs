(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxMem AxMemC AxState AxStep AxFetch AxEntryRel AxSys AxOcc AxJoin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.

Inductive hint : Type :=
| HSplit (f : lin) (cuts : list (Z * Z))
| HSplitReg (r : int) (cuts : list (Z * Z))
| HSplitR (f : lin) (cuts : list (Z * Z))
| HJoin
| HFresh (v : int) (h : lin) (k : Z)
| HFloor (r : int) (k : Z)
| HSum (k : Z)
| HStop
| HDynJoin    (* [comment removed for export] *)
| HWorld      (* [comment removed for export] *)
| HForkJoin (T : Z) (k : nat)
              (* [comment removed for export] *)
| HDynJoinS   (* [comment removed for export] *)
| HAlignSplit (r : int) (k : Z).
              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition htable : Type := itrie (list hint).

Definition hints_at (H : htable) (pc : w64) : list hint :=
  match iget ic_depth H (ic_key pc) with Some l => l | None => [] end.

Fixpoint mk_htable (l : list (Z * list hint)) : htable :=
  match l with
  | [] => IEmpty
  | (pc, hs) :: r => iset ic_depth (mk_htable r) (ic_key (wofZ pc)) hs
  end.

Notation AST := (astate amodel).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint cuts_cover (lo hi : Z) (cuts : list (Z * Z)) : bool :=
  match cuts with
  | [] => hi <? lo
  | (l, h) :: r => (l <=? lo) &&& ((hi <=? h) ||| cuts_cover (h + 1) hi r)
  end.

Definition split_ok (A : AST) (f : lin) (cuts : list (Z * Z)) : bool :=
  match lrange (a_facts A) f with
  | Some (lo, hi) => cuts_cover lo hi cuts
  | None => false
  end.

Definition with_store (A : AST) (s : store) : AST :=
  AS (a_pc A) (renorm_regs s (a_regs A)) (a_resv A) (a_mem A) s (a_model A) (a_budget A) (a_steps A).

Definition split_children (A : AST) (f : lin) (cuts : list (Z * Z)) : list AST :=
  map (fun c => with_store A (sadd (a_facts A) f (fst c) (snd c)))
      (List.filter (fun c => feasible (sadd (a_facts A) f (fst c) (snd c)) f) cuts).

(* [comment removed for export] *)
Definition pin_reg (r : int) (c : Z * Z) (A : AST) : AST :=
  if fst c =? snd c then AS (a_pc A) (aset (a_regs A) r (XL (wofZ (fst c)))) (a_resv A) (a_mem A) (a_facts A) (a_model A) (a_budget A) (a_steps A)
  else A.

Definition split_children_reg (A : AST) (r : int) (f : lin) (cuts : list (Z * Z)) : list AST :=
  map (fun c => pin_reg r c (with_store A (sadd (a_facts A) f (fst c) (snd c))))
      (List.filter (fun c => feasible (sadd (a_facts A) f (fst c) (snd c)) f) cuts).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint acoef (v : int) (ts : terms) : Z :=
  match ts with
  | [] => 0
  | (x, a) :: r => if (x =? v)%uint63 then a else acoef v r
  end.

(* [comment removed for export] *)
Fixpoint find_floor_fact (fs : list fact) (ts : terms) (k2 : Z) : option (int * lin) :=
  match fs with
  | [] => None
  | Fact F lo hi ho :: r =>
      if negb ho &&& (lo =? 0) &&& (hi =? k2 - 1) then
        match List.find (fun p : int * Z => (snd p =? - k2) &&& (acoef (fst p) ts =? k2)) (snd F) with
        | Some p => Some (fst p, F)
        | None => find_floor_fact r ts k2
        end
      else find_floor_fact r ts k2
  end.

(* [comment removed for export] *)
Definition lin_gcd (F : lin) : Z := fold_right (fun (p : int * Z) g => Z.gcd (snd p) g) (fst F) (snd F).

(* [comment removed for export] *)
Definition align_cases (k2 g : Z) : list Z := map (fun i => g * Z.of_nat i) (seq 0 (S (Z.to_nat ((k2 - 1) / g)))).

(* [comment removed for export] *)
Definition elim_xv (v : int) (k2 : Z) (F : lin) (q : Z) (x : xv) : xv :=
  match x with
  | XS ts o => let a := acoef v ts in
               if (a =? 0) ||| negb (a mod k2 =? 0) then x
               else let m := a / k2 in mk_xs (tadd ts (tscale m (snd F))) (w_add o (wofZ (m * (fst F - q))))
  | _ => x
  end.

Definition align_child (A : AST) (v : int) (k2 : Z) (F : lin) (q : Z) : AST :=
  let s' := sadd (a_facts A) F q q in
  AS (a_pc A) (renorm_regs s' (imap (elim_xv v k2 F q) (a_regs A))) (a_resv A) (a_mem A) s' (a_model A) (a_budget A) (a_steps A).

Definition align_children (A : AST) (r : int) (k : Z) : option (list AST) :=
  match aget (a_regs A) r with
  | XS ts _ =>
      let k2 := 2 ^ k in
      match find_floor_fact (st_facts (a_facts A)) ts k2 with
      | Some (v, F) =>
          let g := lin_gcd F in
          if (0 <? g) &&& ((k2 - 1) / g <? 8) then
            Some (map (align_child A v k2 F) (List.filter (fun q => feasible (sadd (a_facts A) F q q) F) (align_cases k2 g)))
          else None
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fresh_store (s : store) (v : int) (h : lin) (k : Z) : store :=
  let k2 := 2 ^ k in
  let s1 := ST (st_box s) (Fact (fst h, tadd (snd h) [(v, - k2)]) 0 (k2 - 1) false :: st_facts s) in
  match lrange s h with
  | Some (lo, hi) => sadd s1 (lvar v 1) (lo / k2) (hi / k2)
  | None => s1
  end.

Definition fresh_child (A : AST) (v : int) (h : lin) (k : Z) : AST :=
  AS (a_pc A) (a_regs A) (a_resv A) (a_mem A) (fresh_store (a_facts A) v h k) (a_model A) (a_budget A) (a_steps A).

Definition fresh_ok (A : AST) (v : int) (h : lin) (k : Z) : bool :=
  negb (state_occ v A) &&& negb (ts_occ v (snd h)) &&& (0 <=? k) &&& (k <? 64).

Definition bump_next (A : AST) : AST :=
  AS (a_pc A) (a_regs A) (a_resv A) (a_mem A) (a_facts A) (set_next (a_model A) (am_next (a_model A) + 1)%uint63) (a_budget A) (a_steps A).

(* [comment removed for export] *)
Definition floor_form (A : AST) (r : int) (k : Z) : option lin :=
  match xform (a_facts A) (aget (a_regs A) r) with
  | Some f => Some (fst f, snd (tsplit (2 ^ k) (snd f)))
  | None => None
  end.

Definition floor_child (A : AST) (r : int) (k : Z) : option AST :=
  match floor_form A r k with
  | Some h => let v := am_next (a_model A) in
              if fresh_ok A v h k &&& (v <? 65536)%uint63 then Some (bump_next (fresh_child A v h k)) else None
  | None => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record item : Type := IT { it_n : nat; it_dj : list int; it_st : AST }.

(* [comment removed for export] *)
Definition dj_key (d : int) : int := (d land 16777215)%uint63.
Definition dj_scoped (ra : w64) (A : AST) : int := (ic_key ra lor ((of_Z (a_steps A) land 1073741823) << 24))%uint63.

Inductive rstatus : Type :=
| RRun
| RStuck (code : Z) (pc : w64)
| RFuel.

Record rstate : Type := RS {
  rs_status : rstatus;
  rs_work : list item;
  rs_parked : list item;
  rs_final : list AST;
  rs_ic : itrie icent;
  rs_count : Z;
  rs_dbg : list AST            (* [comment removed for export] *)
}.

Definition is_nilb {X : Type} (l : list X) : bool := match l with [] => true | _ => false end.

Fixpoint ints_eqb (a b : list int) : bool :=
  match a, b with
  | [], [] => true
  | x :: r, y :: r' => (x =? y)%uint63 &&& ints_eqb r r'
  | _, _ => false
  end.

Section Run.
Variable segs : list Segment.
Variable LIM : Z.
Variable H : htable.
Variable sys : AST -> option (list AST).
Variable sum : Z -> AST -> option (list AST).

(* [comment removed for export] *)
Fixpoint park (it : item) (l : list item) : list item :=
  match l with
  | [] => [it]
  | p :: r =>
      if Nat.eqb (it_n p) (it_n it) &&& ints_eqb (it_dj p) (it_dj it) then
        match ajoin segs (it_st p) (it_st it) with
        | Some J => IT (it_n p) (it_dj p) J :: r
        | None => p :: park it r
        end
      else p :: park it r
  end.

Definition push (n : nat) (dj : list int) (l : list AST) (w : list item) : list item :=
  map (IT n dj) l ++ w.

Definition stuck (rs : rstate) (code : Z) (A : AST) : rstate :=
  RS (RStuck code (a_pc A)) (rs_work rs) (rs_parked rs) (rs_final rs) (rs_ic rs) (rs_count rs) [A].

(* [comment removed for export] *)
Definition world_tag (i : nat) : int := (of_Z (Z.of_nat (S i)) << 24)%uint63.

Fixpoint push_tag (i : nat) (dj : list int) (l : list AST) (w : list item) : list item :=
  match l with
  | [] => w
  | B :: r => IT 0 (dj ++ [world_tag i]) B :: push_tag (S i) dj r w
  end.

Definition fork_push (tag : bool) (dj : list int) (l : list AST) (w : list item) : list item :=
  if tag then (match l with _ :: _ :: _ => push_tag 0 dj l w | _ => push 0 dj l w end) else push 0 dj l w.

(* [comment removed for export] *)
Definition rstep_plain (tag : bool) (rs : rstate) (it : item) : rstate :=
  let A := it_st it in
  let n := it_n it in
  let dj := it_dj it in
  let w := rs_work rs in
  let (ic', r) := astep segs amodel LIM (rs_ic rs) A in
      match r with
      | ANext A' => RS RRun (IT 0 dj A' :: w) (rs_parked rs) (rs_final rs) ic' (rs_count rs + 1) []
      | AFork l => RS RRun (fork_push tag dj l w) (rs_parked rs) (rs_final rs) ic' (rs_count rs + 1) []
      | AEcall _ => match sys A with
                    | Some l => RS RRun (push 0 dj l w) (rs_parked rs) (rs_final rs) ic' (rs_count rs + 1) []
                    | None => RS RRun w (rs_parked rs) (A :: rs_final rs) ic' (rs_count rs + 1) []
                    end
      | AStuck code _ => RS (RStuck code (a_pc A)) w (rs_parked rs) (rs_final rs) ic' (rs_count rs) [A]
      | AFloor r k => match floor_child A r k with
                      | Some B => RS RRun (IT n dj B :: w) (rs_parked rs) (rs_final rs) ic' (rs_count rs + 1) []
                      | None => RS (RStuck 108 (a_pc A)) w (rs_parked rs) (rs_final rs) ic' (rs_count rs) [A]
                      end
      end.

(* [comment removed for export] *)
Fixpoint mini (k : nat) (T : w64) (ic : itrie icent) (C : AST) : itrie icent * option AST :=
  if w_eqb (a_pc C) T then (ic, Some C) else
  match k with
  | O => (ic, None)
  | S k' => if nomem_at segs amodel ic C then
              let (ic', r) := astep segs amodel LIM ic C in
              match r with ANext C' => mini k' T ic' C' | _ => (ic', None) end
            else (ic, None)
  end.

Definition rstep_forkjoin (T : Z) (k : nat) (rs : rstate) (it : item) : rstate :=
  let A := it_st it in
  let dj := it_dj it in
  let w := rs_work rs in
  let (ic1, r) := astep segs amodel LIM (rs_ic rs) A in
  match r with
  | AFork [Ca; Cb] =>
      let (ic2, o1) := mini k (wofZ T) ic1 Ca in
      let (ic3, o2) := mini k (wofZ T) ic2 Cb in
      match o1, o2 with
      | Some Da, Some Db =>
          match ajoin_nm Da Db with
          | Some J => RS RRun (IT 0 dj J :: w) (rs_parked rs) (rs_final rs) ic3 (rs_count rs + 1) []
          | None => RS RRun (push 0 dj [Ca; Cb] w) (rs_parked rs) (rs_final rs) ic3 (rs_count rs + 1) []
          end
      | _, _ => RS RRun (push 0 dj [Ca; Cb] w) (rs_parked rs) (rs_final rs) ic3 (rs_count rs + 1) []
      end
  | _ => rstep_plain false rs it
  end.

(* [comment removed for export] *)
Definition rstep_item (rs : rstate) (it : item) : rstate :=
  let A := it_st it in
  let n := it_n it in
  let dj := it_dj it in
  let w := rs_work rs in
  let cont (w' : list item) := RS RRun w' (rs_parked rs) (rs_final rs) (rs_ic rs) (rs_count rs + 1) [] in
  match (match dj with d :: dj' => if (dj_key d =? ic_key (a_pc A))%uint63 then Some dj' else None | [] => None end) with
  | Some dj' => (* [comment removed for export] *)
      RS RRun w (park (IT 0 dj' A) (rs_parked rs)) (rs_final rs) (rs_ic rs) (rs_count rs + 1) []
  | None =>
  match nth_error (hints_at H (a_pc A)) n with
  | Some h =>
      match h with
      | HSplit f cuts => if split_ok A f cuts then cont (push (S n) dj (split_children A f cuts) w) else stuck rs 101 A
      | HSplitReg r cuts =>
          if negb (r <? 32)%uint63 then stuck rs 109 A else
          (* [comment removed for export] *)
          match xform (a_facts A) (canon_v (a_facts A) (aget (a_regs A) r)) with
          | Some f => match snd f with
                      | [] => cont (IT (S n) dj A :: w)      (* [comment removed for export] *)
                      | _ => if split_ok A f cuts then cont (push (S n) dj (split_children_reg A r f cuts) w) else stuck rs 102 A
                      end
          | None => stuck rs 103 A
          end
      | HSplitR f cuts =>
          match aget (a_regs A) 1%uint63 with
          | XL ra => if split_ok A f cuts then cont (push (S n) (ic_key ra :: dj) (split_children A f cuts) w) else stuck rs 104 A
          | _ => stuck rs 105 A
          end
      | HJoin => RS RRun w (park (IT (S n) dj A) (rs_parked rs)) (rs_final rs) (rs_ic rs) (rs_count rs + 1) []
      | HFresh v h k => if fresh_ok A v h k then cont (IT (S n) dj (fresh_child A v h k) :: w) else stuck rs 106 A
      | HFloor r k => match floor_child A r k with Some B => cont (IT (S n) dj B :: w) | None => stuck rs 107 A end
      | HSum k => match sum k A with Some l => cont (push 0 dj l w) | None => cont (IT (S n) dj A :: w) end
      | HStop => RS RRun w (rs_parked rs) (A :: rs_final rs) (rs_ic rs) (rs_count rs + 1) []
      | HDynJoin => match aget (a_regs A) 1%uint63 with
                    | XL ra => cont (IT (S n) (ic_key ra :: dj) A :: w)
                    | _ => stuck rs 110 A
                    end
      | HWorld => rstep_plain true rs it
      | HForkJoin T k => rstep_forkjoin T k rs it
      | HDynJoinS => match aget (a_regs A) 1%uint63 with
                     | XL ra => cont (IT (S n) (dj_scoped ra A :: dj) A :: w)
                     | _ => stuck rs 111 A
                     end
      | HAlignSplit r k =>
          match align_children A r k, aget (a_regs A) 1%uint63 with
          | Some l, XL ra => cont (push (S n) (ic_key ra :: dj) l w)
          | _, _ => cont (IT (S n) dj A :: w)             (* [comment removed for export] *)
          end
      end
  | None => rstep_plain false rs it
  end
  end.

Definition rstep (rs : rstate) : rstate :=
  match rs_status rs with
  | RRun =>
      match rs_work rs with
      | it :: w => rstep_item (RS RRun w (rs_parked rs) (rs_final rs) (rs_ic rs) (rs_count rs) []) it
      | [] => match rs_parked rs with
              | [] => rs
              | p => RS RRun p [] (rs_final rs) (rs_ic rs) (rs_count rs) []
              end
      end
  | _ => rs
  end.

Definition rdone (rs : rstate) : bool :=
  match rs_status rs with
  | RRun => is_nilb (rs_work rs) &&& is_nilb (rs_parked rs)
  | _ => true
  end.

(* [comment removed for export] *)
Fixpoint riter (p : positive) (rs : rstate) : rstate :=
  if rdone rs then rs else
  match p with
  | xH => rstep rs
  | xO q => riter q (riter q rs)
  | xI q => rstep (riter q (riter q rs))
  end.

Definition run (fuel : positive) (ic : itrie icent) (A0 : AST) : rstate :=
  riter fuel (RS RRun [IT 0 [] A0] [] [] ic 0 []).

End Run.
