(* Ported by RtStr from cold/c-asan-rt-fmio-n affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Spec/TwSearch.v, unchanged. *)
From Stdlib Require Import ZArith Arith List Lia Bool.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Spec Require Import TwoWay StrStr.
Import ListNotations.
Open Scope nat_scope.

Definition inset (x : list Z) (b : Z) : bool := existsb (Z.eqb b) x.

Definition shift_of (x : list Z) (b : Z) : nat :=
  fold_left (fun acc i => if Z.eqb (at_ x i) b then S i else acc) (seq 0 (length x)) 0.

Fixpoint rscan (x y : list Z) (pos k fuel : nat) : nat :=
  match fuel with
  | O => k
  | S f => if (k <? length x) && Z.eqb (at_ x k) (at_ y (pos + k)) then rscan x y pos (S k) f else k
  end.

Fixpoint lscan (x y : list Z) (pos mem k : nat) : nat :=
  match k with
  | O => O
  | S k' => if (mem <? k) && Z.eqb (at_ x k') (at_ y (pos + k')) then lscan x y pos mem k' else k
  end.

Inductive tw_res : Type := TwFound (pos : nat) | TwNext (pos mem : nat).

Definition tw_body (x y : list Z) (c p mem0 pos mem : nat) : tw_res :=
  let l := length x in
  let b := at_ y (pos + l - 1) in
  if negb (inset x b) then TwNext (pos + l) 0
  else
    let k := l - shift_of x b in
    if negb (k =? 0) then TwNext (pos + Nat.max k mem) 0
    else
      let kr := rscan x y pos (Nat.max c mem) (l - Nat.max c mem) in
      if kr <? l then TwNext (pos + (kr + 1 - c)) 0
      else if lscan x y pos mem c <=? mem then TwFound pos
      else TwNext (pos + p) mem0.

Definition tw_periodic (x : list Z) (c p0 : nat) : bool :=
  forallb (fun j => Z.eqb (at_ x j) (at_ x (j + p0))) (seq 0 c).

Definition tw_p (x : list Z) (c p0 : nat) : nat :=
  if tw_periodic x c p0 then p0 else Nat.max (c - 1) (length x - c) + 1.

Definition tw_mem0 (x : list Z) (c p0 : nat) : nat :=
  if tw_periodic x c p0 then length x - p0 else 0.

Definition TW_INV (x y : list Z) (pos mem : nat) : Prop :=
  (forall i, i < pos -> prefix_eqb x (skipn i y) = false) /\ mem < length x /\
  (forall j, j < mem -> at_ x j = at_ y (pos + j)).

Definition SEARCH_OK : Prop :=
  forall (x y : list Z) (c p0 : nat),
    1 <= length x -> TW_CRIT x c p0 ->
    forall pos mem, TW_INV x y pos mem -> (mem = 0 \/ mem = tw_mem0 x c p0) -> pos + length x <= length y ->
    match tw_body x y c (tw_p x c p0) (tw_mem0 x c p0) pos mem with
    | TwFound q => q = pos /\ prefix_eqb x (skipn pos y) = true
    | TwNext pos' mem' =>
        pos < pos' <= pos + length x /\ TW_INV x y pos' mem' /\ (mem' = 0 \/ mem' = tw_mem0 x c p0)
    end.

Definition SEARCH_END_OK : Prop :=
  forall (x y : list Z) pos mem, 1 <= length x -> TW_INV x y pos mem -> length y < pos + length x ->
    find_first y x = None.

Definition SEARCH_FOUND_OK : Prop :=
  forall (x y : list Z) pos mem, TW_INV x y pos mem -> prefix_eqb x (skipn pos y) = true ->
    find_first y x = Some pos.
