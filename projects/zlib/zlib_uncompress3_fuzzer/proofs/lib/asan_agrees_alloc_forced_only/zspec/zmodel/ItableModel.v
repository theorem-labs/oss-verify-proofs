(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import Prog ZIface InflateState Inftrees ModelRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition itm_count (lens : arr) (lens_ofs codes : Z) : arr :=
  it_count lens lens_ofs codes (it_zero_count (arr_make 16 0)).
Definition itm_max (count : arr) : Z := it_find_max count.
Definition itm_min (count : arr) (max : Z) : Z := it_find_min count max.
Definition itm_root (bits max min : Z) : Z :=
  let root := if max <? bits then max else bits in
  if root <? min then min else root.
Definition itm_offs (count : arr) : arr := it_offs count (arr_make 16 0).
Definition itm_work (lens : arr) (lens_ofs codes : Z) (offs work : arr) : arr :=
  snd (it_sort lens lens_ofs codes (offs, work)).
Definition itm_used (root : Z) : Z := shl32 1 root.
Definition itm_ctx (ty : codetype) (lens : arr) (lens_ofs table root max : Z) : ItCtx :=
  mkItCtx ty lens lens_ofs table root max (itm_used root - 1).
Definition itm_st0 (min table root : Z) (count tbl work : arr) : ItSt :=
  mkItSt 0 0 min table root 0 4294967295 (itm_used root) 0 count tbl work.

Definition itm_reject (ty : codetype) (max : Z) (lc : option Z) : bool :=
  match lc with
  | None => true
  | Some lft => (0 <? lft) && (codetype_eqb ty CODES || negb (max =? 1))
  end.

Definition itm_finish (table root : Z) (r : ItSt + ItSt) : Z * arr * Z * Z * arr :=
  match r with
  | inr st => (1, t_tbl st, table, 0 , t_work st)
  | inl st =>
    let tbl := if negb (t_huff st =? 0)
               then arr_set (t_tbl st) (t_next st + t_huff st) (code_pack 64 (t_len st - t_drop st) 0)
               else t_tbl st in
    (0, tbl, table + t_used st, root, t_work st)
  end.

Lemma inflate_table_phases : forall ty lens lens_ofs codes tbl table bits work,
  inflate_table ty lens lens_ofs codes tbl table bits work =
  let count := itm_count lens lens_ofs codes in
  let max := itm_max count in
  if max =? 0 then
    (0, arr_set (arr_set tbl table (code_pack 64 1 0)) (table + 1) (code_pack 64 1 0), table + 2, 1, work)
  else
  let min := itm_min count max in
  let root := itm_root bits max min in
  if itm_reject ty max (it_left_check count) then (-1, tbl, table, bits, work)
  else
  let work1 := itm_work lens lens_ofs codes (itm_offs count) work in
  if it_not_enough ty (itm_used root) then (1, tbl, table, bits, work1)
  else
  match it_loop (itm_ctx ty lens lens_ofs table root max) codes (itm_st0 min table root count tbl work1) with
  | inr st => (1, t_tbl st, table, bits, t_work st)
  | inl st =>
    let tbl' := if negb (t_huff st =? 0)
                then arr_set (t_tbl st) (t_next st + t_huff st) (code_pack 64 (t_len st - t_drop st) 0)
                else t_tbl st in
    (0, tbl', table + t_used st, root, t_work st)
  end.
Proof.
  intros ty lens lens_ofs codes tbl table bits work.
  unfold inflate_table, itm_count, itm_max, itm_min, itm_root, itm_reject, itm_work, itm_offs,
    itm_used, itm_ctx, itm_st0. cbv zeta.
  destruct (it_find_max _ =? 0); [reflexivity|].
  destruct (it_left_check _) as [lft|]; [|reflexivity].
  destruct ((0 <? lft) && _); [reflexivity|].
  destruct (it_sort lens lens_ofs codes _) as [o w]. cbn [snd]. reflexivity.
Qed.


Definition it_ext_len (ty : codetype) (WN : Z) : Z :=
  match ty with CODES => WN | LENS => 31 | DISTS => 32 end.

Definition it_sort_ok (lens : arr) (lens_ofs codes : Z) (offs : arr) (WN : Z) : bool :=
  snd (forZ 0 codes (fun sym st =>
    let '(offs, ok) := st in
    let l := arr_get lens (lens_ofs + sym) in
    if negb (l =? 0) then
      let o := arr_get offs l in
      (arr_set offs l (wrap16 (o + 1)), ok && ((0 <=? o) && (o <? WN)))
    else (offs, ok)) (offs, true)).

Definition it_trip_ok (x : ItCtx) (WN LN TN : Z) (st : ItSt) : bool :=
  let ty := x_ty x in
  let sym := t_sym st in let len := t_len st in let drop := t_drop st in
  let curr := t_curr st in let huff := t_huff st in let next := t_next st in
  (0 <=? sym) && (sym <? WN) &&
  (1 <=? len) && (len <=? 15) && (0 <=? drop) && (drop <=? len) &&
  (len - drop <=? curr) && (curr <=? 15) && (0 <=? huff) && (huff <? 65536) &&
  (0 <=? next) && (0 <=? t_used st) && (t_used st <? 65536) && (0 <=? t_min st) && (t_min st <? 65536) &&
  (let w := arr_get (t_work st) sym in
   (0 <=? w) && (w <? 65536) &&
   (if w + 1 <? it_match ty then true
    else if it_match ty <=? w then w - it_match ty <? it_ext_len ty WN
    else true)) &&
  (next + Z.shiftr huff drop + Z.shiftl 1 curr - Z.shiftl 1 (len - drop) <? TN) &&
  (let c := wrap16 (arr_get (t_count st) len - 1) in
   if (c =? 0) && negb (len =? x_max x) then
     let w' := arr_get (t_work st) (sym + 1) in
     let li := x_lens_ofs x + w' in
     (sym + 1 <? WN) && (0 <=? w') && (0 <=? li) && (li <? LN) &&
     (let len' := arr_get (x_lens x) li in (1 <=? len') && (len' <=? 15))
   else true) &&
  match it_step x st with
  | ItCont st' =>
      if negb (t_low st' =? t_low st) || negb (t_next st' =? t_next st)
      then (0 <=? x_table x + t_low st') && (x_table x + t_low st' <? TN)
           && (1 <=? t_curr st') && (t_curr st' <=? 15) && (t_next st <=? t_next st')
      else true
  | _ => true
  end.

Fixpoint it_loop_ok (k : nat) (x : ItCtx) (WN LN TN : Z) (st : ItSt) : bool :=
  match k with
  | O => false
  | S k' =>
      it_trip_ok x WN LN TN st &&
      match it_step x st with
      | ItCont st' => it_loop_ok k' x WN LN TN st'
      | ItBreak st' => if negb (t_huff st' =? 0)
                       then (0 <=? t_next st' + t_huff st') && (t_next st' + t_huff st' <? TN)
                       else true
      | ItFail _ => true
      end
  end.

Definition it_safe (ty : codetype) (lens : arr) (lens_ofs codes : Z)
           (tbl : arr) (table bits : Z) (work : arr) : bool :=
  let WN := arr_len work in let LN := arr_len lens in let TN := arr_len tbl in
  let count := itm_count lens lens_ofs codes in
  let max := itm_max count in
  (0 <=? codes) && (codes <=? WN) && (WN <=? 65536) &&
  if max =? 0 then (0 <=? table) && (table + 2 <=? TN)
  else
  let min := itm_min count max in
  let root := itm_root bits max min in
  if itm_reject ty max (it_left_check count) then true
  else
  it_sort_ok lens lens_ofs codes (itm_offs count) WN &&
  (if it_not_enough ty (itm_used root) then true
   else (0 <=? table) && (table + itm_used root <=? TN) &&
        it_loop_ok (Z.to_nat (codes + 1)) (itm_ctx ty lens lens_ofs table root max) WN LN TN
                   (itm_st0 min table root count tbl (itm_work lens lens_ofs codes (itm_offs count) work))).


Lemma forZ_snoc : forall {A} lo k (body : Z -> A -> A) a,
  lo <= k -> forZ lo (k + 1) body a = body k (forZ lo k body a).
Proof.
  intros A lo k body a Hk.
  remember (Z.to_nat (k - lo)) as n eqn:Hn. revert lo a Hk Hn.
  induction n as [|n IH]; intros lo a Hk Hn.
  - assert (lo = k) by lia. subst lo.
    rewrite (forZ_unfold k (k + 1)), (proj2 (Z.ltb_lt k (k + 1))) by lia.
    rewrite (forZ_unfold (k + 1) (k + 1)), (proj2 (Z.ltb_ge (k + 1) (k + 1))) by lia.
    rewrite (forZ_unfold k k), (proj2 (Z.ltb_ge k k)) by lia. reflexivity.
  - rewrite (forZ_unfold lo (k + 1)), (proj2 (Z.ltb_lt lo (k + 1))) by lia.
    rewrite (forZ_unfold lo k), (proj2 (Z.ltb_lt lo k)) by lia.
    apply IH; lia.
Qed.

Lemma forZ_nil : forall {A} lo hi (body : Z -> A -> A) a, hi <= lo -> forZ lo hi body a = a.
Proof. intros A lo hi body a H. rewrite forZ_unfold, (proj2 (Z.ltb_ge lo hi)) by lia. reflexivity. Qed.


Definition itm_count_k (lens : arr) (lens_ofs k : Z) : arr :=
  it_count lens lens_ofs k (it_zero_count (arr_make 16 0)).

Lemma it_zero_count_spec : forall i, arr_get (it_zero_count (arr_make 16 0)) i = 0.
Proof.
  intro i. unfold it_zero_count, MAXBITS.
  change (15 + 1) with 16.
  assert (H : forall n a, (forall j, arr_get a j = 0) -> forall j, arr_get (forZ (16 - Z.of_nat n) 16 (fun len cnt => arr_set cnt len 0) a) j = 0).
  { induction n as [|n IH]; intros a Ha j.
    - rewrite forZ_nil by lia. apply Ha.
    - rewrite forZ_unfold. destruct (Z.ltb_spec (16 - Z.of_nat (S n)) 16); [|apply Ha].
      replace (16 - Z.of_nat (S n) + 1) with (16 - Z.of_nat n) by lia. apply IH.
      intro j0. rewrite arr_get_set. destruct (_ && _); [reflexivity | apply Ha]. }
  change 0 with (16 - Z.of_nat 16) at 1. apply H. intro j. apply arr_get_make.
Qed.

Lemma it_zero_count_len : arr_len (it_zero_count (arr_make 16 0)) = 16.
Proof.
  unfold it_zero_count. apply (forZ_ind (fun _ a => arr_len a = 16)); [| apply arr_len_make | unfold MAXBITS; lia].
  intros i x _ Hx. rewrite arr_len_set. exact Hx.
Qed.

Lemma itm_count_k_len : forall lens lens_ofs k, arr_len (itm_count_k lens lens_ofs k) = 16.
Proof.
  intros lens lens_ofs k. unfold itm_count_k, it_count.
  destruct (Z_lt_le_dec k 0).
  - rewrite forZ_nil by lia. apply it_zero_count_len.
  - apply (forZ_ind (fun _ a => arr_len a = 16)); [| apply it_zero_count_len | lia].
    intros i x _ Hx. rewrite arr_len_set. exact Hx.
Qed.

Lemma itm_count_k_0 : forall lens lens_ofs k, k <= 0 ->
  itm_count_k lens lens_ofs k = it_zero_count (arr_make 16 0).
Proof. intros. unfold itm_count_k, it_count. apply forZ_nil. lia. Qed.

Lemma itm_count_k_step : forall lens lens_ofs k, 0 <= k ->
  itm_count_k lens lens_ofs (k + 1) =
  let cnt := itm_count_k lens lens_ofs k in
  let l := arr_get lens (lens_ofs + k) in
  arr_set cnt l (wrap16 (arr_get cnt l + 1)).
Proof. intros lens lens_ofs k Hk. unfold itm_count_k, it_count. rewrite forZ_snoc by lia. reflexivity. Qed.

Lemma itm_count_k_range : forall lens lens_ofs k i, 0 <= arr_get (itm_count_k lens lens_ofs k) i < 65536.
Proof.
  intros lens lens_ofs k. unfold itm_count_k, it_count.
  destruct (Z_lt_le_dec k 0).
  - intros i. rewrite forZ_nil by lia. rewrite it_zero_count_spec. lia.
  - apply (forZ_ind (fun _ a => forall i, 0 <= arr_get a i < 65536)); [| intro i; rewrite it_zero_count_spec; lia | lia].
    intros j x _ Hx i. rewrite arr_get_set. destruct (_ && _); [apply wrap16_range | apply Hx].
Qed.

Lemma itm_count_eq : forall lens lens_ofs codes, itm_count lens lens_ofs codes = itm_count_k lens lens_ofs codes.
Proof. reflexivity. Qed.


Fixpoint find_max_rec (count : arr) (n : nat) (max : Z) : Z :=
  match n with
  | O => max
  | S n' => if (1 <=? max) && (arr_get count max =? 0) then find_max_rec count n' (max - 1) else max
  end.

Lemma loopZ_find_max : forall count n max,
  0 <= max -> max < Z.of_nat n ->
  loopZ (Z.of_nat n) (fun max => if (1 <=? max) && (arr_get count max =? 0) then (true, max - 1) else (false, max)) max
  = find_max_rec count n max.
Proof.
  intros count n. induction n as [|n IH]; intros max H0 Hn; [lia|].
  rewrite loopZ_step by lia. cbn [find_max_rec].
  destruct ((1 <=? max) && (arr_get count max =? 0)) eqn:E.
  - replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
    apply andb_prop in E as [E _]. apply Z.leb_le in E. apply IH; lia.
  - reflexivity.
Qed.

Lemma itm_max_rec : forall count, itm_max count = find_max_rec count 16 15.
Proof. intro count. unfold itm_max, it_find_max, MAXBITS. apply (loopZ_find_max count 16 15); lia. Qed.

Lemma find_max_rec_spec : forall count n max,
  0 <= max -> max <= Z.of_nat n ->
  let r := find_max_rec count n max in
  0 <= r <= max /\ (r = 0 \/ arr_get count r <> 0) /\ (forall j, r < j <= max -> arr_get count j = 0).
Proof.
  intros count n. induction n as [|n IH]; intros max H0 Hn.
  - cbn. assert (max = 0) by lia. subst. split; [lia|]. split; [left; reflexivity|]. intros; lia.
  - cbn [find_max_rec]. destruct (Z.leb_spec 1 max); cbn [andb].
    + destruct (Z.eqb_spec (arr_get count max) 0).
      * destruct (IH (max - 1) ltac:(lia) ltac:(lia)) as (A & B & C). cbv zeta.
        split; [lia|]. split; [exact B|]. intros j Hj.
        destruct (Z.eq_dec j max) as [->|]; [assumption | apply C; lia].
      * cbv zeta. split; [lia|]. split; [right; assumption|]. intros; lia.
    + cbv zeta. split; [lia|]. split; [left; lia|]. intros; lia.
Qed.

Lemma find_max_rec_fuel : forall count n n' max,
  0 <= max -> max <= Z.of_nat n -> max <= Z.of_nat n' -> find_max_rec count n max = find_max_rec count n' max.
Proof.
  intros count n. induction n as [|n IH]; intros n' max H0 Hn Hn'.
  - assert (max = 0) by lia. subst. destruct n'; [reflexivity|]. cbn. reflexivity.
  - destruct n' as [|n']; [assert (max = 0) by lia; subst; cbn; reflexivity|].
    cbn [find_max_rec]. destruct (Z.leb_spec 1 max); cbn [andb]; [|reflexivity].
    destruct (arr_get count max =? 0); [|reflexivity]. apply IH; lia.
Qed.

Lemma itm_max_codes0 : forall lens lens_ofs codes, codes <= 0 -> itm_max (itm_count lens lens_ofs codes) = 0.
Proof.
  intros lens lens_ofs codes Hc. rewrite itm_count_eq, itm_count_k_0 by lia.
  rewrite itm_max_rec.
  assert (H : forall n max, 0 <= max -> max <= Z.of_nat n -> find_max_rec (it_zero_count (arr_make 16 0)) n max = 0).
  { induction n as [|n IH]; intros max H0 Hn; [cbn; lia|].
    cbn [find_max_rec]. rewrite it_zero_count_spec, Z.eqb_refl, andb_true_r.
    destruct (Z.leb_spec 1 max); [apply IH; lia | lia]. }
  apply H; lia.
Qed.

Fixpoint find_min_rec (count : arr) (max : Z) (n : nat) (min : Z) : Z :=
  match n with
  | O => min
  | S n' => if (min <? max) && (arr_get count min =? 0) then find_min_rec count max n' (min + 1) else min
  end.

Lemma loopZ_find_min : forall count max n min,
  max - min < Z.of_nat n ->
  loopZ (Z.of_nat n) (fun min => if (min <? max) && (arr_get count min =? 0) then (true, min + 1) else (false, min)) min
  = find_min_rec count max n min.
Proof.
  intros count max n. induction n as [|n IH]; intros min Hn.
  - cbn [find_min_rec]. apply loopZ_le0. lia.
  - rewrite loopZ_step by lia. cbn [find_min_rec].
    destruct ((min <? max) && (arr_get count min =? 0)) eqn:E; [|reflexivity].
    replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
    apply andb_prop in E as [E _]. apply Z.ltb_lt in E. apply IH. lia.
Qed.

Lemma itm_min_rec : forall count max, max <= 15 -> itm_min count max = find_min_rec count max 16 1.
Proof. intros count max Hm. unfold itm_min, it_find_min. apply (loopZ_find_min count max 16 1). lia. Qed.

Lemma find_min_rec_spec : forall count max n min,
  min <= max -> max - min <= Z.of_nat n ->
  let r := find_min_rec count max n min in
  min <= r <= max /\ (r = max \/ arr_get count r <> 0) /\ (forall j, min <= j < r -> arr_get count j = 0).
Proof.
  intros count max n. induction n as [|n IH]; intros min H0 Hn.
  - cbn. split; [lia|]. split; [left; lia|]. intros; lia.
  - cbn [find_min_rec]. destruct (Z.ltb_spec min max); cbn [andb].
    + destruct (Z.eqb_spec (arr_get count min) 0).
      * destruct (IH (min + 1) ltac:(lia) ltac:(lia)) as (A & B & C). cbv zeta.
        split; [lia|]. split; [exact B|]. intros j Hj.
        destruct (Z.eq_dec j min) as [->|]; [assumption | apply C; lia].
      * cbv zeta. split; [lia|]. split; [right; assumption|]. intros; lia.
    + cbv zeta. split; [lia|]. split; [left; lia|]. intros; lia.
Qed.

Lemma find_min_rec_fuel : forall count max n n' min,
  min <= max -> max - min <= Z.of_nat n -> max - min <= Z.of_nat n' ->
  find_min_rec count max n min = find_min_rec count max n' min.
Proof.
  intros count max n. induction n as [|n IH]; intros n' min H0 Hn Hn'.
  - assert (min = max) by lia. subst. destruct n'; [reflexivity|]. cbn. rewrite Z.ltb_irrefl. reflexivity.
  - destruct n' as [|n'].
    + assert (min = max) by lia. subst. cbn. rewrite Z.ltb_irrefl. reflexivity.
    + cbn [find_min_rec]. destruct (Z.ltb_spec min max); cbn [andb]; [|reflexivity].
      destruct (arr_get count min =? 0); [|reflexivity]. apply IH; lia.
Qed.


Fixpoint left_rec (count : arr) (n : nat) (len lft : Z) : option Z :=
  match n with
  | O => Some lft
  | S n' =>
      if len <=? MAXBITS then
        let lft' := Z.shiftl lft 1 - arr_get count len in
        if lft' <? 0 then None else left_rec count n' (len + 1) lft'
      else Some lft
  end.

Lemma left_rec_S : forall count n len lft,
  left_rec count (S n) len lft =
  if len <=? MAXBITS then
    if Z.shiftl lft 1 - arr_get count len <? 0 then None
    else left_rec count n (len + 1) (Z.shiftl lft 1 - arr_get count len)
  else Some lft.
Proof. reflexivity. Qed.

Lemma iterZ_left : forall count n len lft,
  MAXBITS + 1 - len < Z.of_nat n ->
  iterZ (Z.of_nat n)
    (fun st : Z * Z => let '(len, lft) := st in
       if len <=? MAXBITS then
         let lft := Z.shiftl lft 1 in
         let lft := lft - arr_get count len in
         if lft <? 0 then inr None else inl (len + 1, lft)
       else inr (Some lft))
    (fun st => Some (snd st)) (len, lft)
  = left_rec count n len lft.
Proof.
  intros count n. induction n as [|n IH]; intros len lft Hn.
  - rewrite iterZ_le0 by lia. reflexivity.
  - rewrite iterZ_step by lia. cbn [left_rec].
    destruct (Z.leb_spec len MAXBITS); [|reflexivity].
    destruct (Z.shiftl lft 1 - arr_get count len <? 0); [reflexivity|].
    replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia. apply IH. lia.
Qed.

Lemma it_left_check_rec : forall count, it_left_check count = left_rec count 16 1 1.
Proof. intro count. unfold it_left_check. apply (iterZ_left count 16 1 1). unfold MAXBITS. lia. Qed.


Definition itm_offs_k (count : arr) (k : Z) : arr :=
  forZ 1 k (fun len o => arr_set o (len + 1) (wrap16 (arr_get o len + arr_get count len))) (arr_set (arr_make 16 0) 1 0).

Lemma itm_offs_eq : forall count, itm_offs count = itm_offs_k count MAXBITS.
Proof. reflexivity. Qed.

Lemma itm_offs_k_1 : forall count, itm_offs_k count 1 = arr_set (arr_make 16 0) 1 0.
Proof. intro. unfold itm_offs_k. apply forZ_nil. lia. Qed.

Lemma itm_offs_k_step : forall count k, 1 <= k ->
  itm_offs_k count (k + 1) =
  let o := itm_offs_k count k in arr_set o (k + 1) (wrap16 (arr_get o k + arr_get count k)).
Proof. intros count k Hk. unfold itm_offs_k. rewrite forZ_snoc by lia. reflexivity. Qed.

Lemma itm_offs_k_len : forall count k, arr_len (itm_offs_k count k) = 16.
Proof.
  intros count k. unfold itm_offs_k. destruct (Z_lt_le_dec k 1).
  - rewrite forZ_nil by lia. rewrite arr_len_set. apply arr_len_make.
  - apply (forZ_ind (fun _ a => arr_len a = 16)); [| rewrite arr_len_set; apply arr_len_make | lia].
    intros i x _ Hx. rewrite arr_len_set. exact Hx.
Qed.

Lemma itm_offs_k_range : forall count k i, 0 <= arr_get (itm_offs_k count k) i < 65536.
Proof.
  intros count k. unfold itm_offs_k.
  assert (B : forall i, 0 <= arr_get (arr_set (arr_make 16 0) 1 0) i < 65536).
  { intro i. rewrite arr_get_set. destruct (_ && _); [lia|]. rewrite arr_get_make. lia. }
  destruct (Z_lt_le_dec k 1).
  - intro i. rewrite forZ_nil by lia. apply B.
  - apply (forZ_ind (fun _ a => forall i, 0 <= arr_get a i < 65536)); [| exact B | lia].
    intros j x _ Hx i. rewrite arr_get_set. destruct (_ && _); [apply wrap16_range | apply Hx].
Qed.


Definition sort_body (lens : arr) (lens_ofs : Z) (sym : Z) (ow : arr * arr) : arr * arr :=
  let '(offs, work) := ow in
  let l := arr_get lens (lens_ofs + sym) in
  if negb (l =? 0) then
    let o := arr_get offs l in
    (arr_set offs l (wrap16 (o + 1)), arr_set work o (wrap16 sym))
  else (offs, work).

Definition sort_ok_body (lens : arr) (lens_ofs WN : Z) (sym : Z) (st : arr * bool) : arr * bool :=
  let '(offs, ok) := st in
  let l := arr_get lens (lens_ofs + sym) in
  if negb (l =? 0) then
    let o := arr_get offs l in
    (arr_set offs l (wrap16 (o + 1)), ok && ((0 <=? o) && (o <? WN)))
  else (offs, ok).

Definition itm_sort_k (lens : arr) (lens_ofs k : Z) (offs work : arr) : arr * arr :=
  forZ 0 k (sort_body lens lens_ofs) (offs, work).

Lemma it_sort_eq : forall lens lens_ofs codes ow,
  it_sort lens lens_ofs codes ow = forZ 0 codes (sort_body lens lens_ofs) ow.
Proof. reflexivity. Qed.

Lemma itm_work_eq : forall lens lens_ofs codes offs work,
  itm_work lens lens_ofs codes offs work = snd (itm_sort_k lens lens_ofs codes offs work).
Proof. reflexivity. Qed.

Lemma itm_sort_k_0 : forall lens lens_ofs k offs work, k <= 0 -> itm_sort_k lens lens_ofs k offs work = (offs, work).
Proof. intros. unfold itm_sort_k. apply forZ_nil. lia. Qed.

Lemma itm_sort_k_step : forall lens lens_ofs k offs work, 0 <= k ->
  itm_sort_k lens lens_ofs (k + 1) offs work = sort_body lens lens_ofs k (itm_sort_k lens lens_ofs k offs work).
Proof. intros lens lens_ofs k offs work Hk. unfold itm_sort_k. rewrite forZ_snoc by lia. reflexivity. Qed.

Definition itm_sort_ok_k (lens : arr) (lens_ofs k : Z) (offs : arr) (WN : Z) : arr * bool :=
  forZ 0 k (sort_ok_body lens lens_ofs WN) (offs, true).

Lemma it_sort_ok_eq : forall lens lens_ofs codes offs WN,
  it_sort_ok lens lens_ofs codes offs WN = snd (itm_sort_ok_k lens lens_ofs codes offs WN).
Proof. reflexivity. Qed.

Lemma itm_sort_ok_k_step : forall lens lens_ofs k offs WN, 0 <= k ->
  itm_sort_ok_k lens lens_ofs (k + 1) offs WN = sort_ok_body lens lens_ofs WN k (itm_sort_ok_k lens lens_ofs k offs WN).
Proof. intros lens lens_ofs k offs WN Hk. unfold itm_sort_ok_k. rewrite forZ_snoc by lia. reflexivity. Qed.

Lemma itm_sort_ok_k_fst : forall lens lens_ofs offs work WN k, 0 <= k ->
  fst (itm_sort_ok_k lens lens_ofs k offs WN) = fst (itm_sort_k lens lens_ofs k offs work).
Proof.
  intros lens lens_ofs offs work WN k Hk.
  remember (Z.to_nat k) as n eqn:Hn. replace k with (Z.of_nat n) by lia. clear k Hk Hn.
  induction n as [|n IH].
  - unfold itm_sort_ok_k, itm_sort_k. rewrite !forZ_nil by lia. reflexivity.
  - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    rewrite itm_sort_ok_k_step, itm_sort_k_step by lia.
    destruct (itm_sort_ok_k lens lens_ofs (Z.of_nat n) offs WN) as [o1 b].
    destruct (itm_sort_k lens lens_ofs (Z.of_nat n) offs work) as [o2 w].
    cbn [fst] in IH. subst o2. cbn [sort_body sort_ok_body]. destruct (negb _); reflexivity.
Qed.

Lemma itm_sort_ok_k_inv : forall lens lens_ofs offs work WN k, 0 <= k ->
  snd (itm_sort_ok_k lens lens_ofs (k + 1) offs WN) = true ->
  snd (itm_sort_ok_k lens lens_ofs k offs WN) = true
  /\ (arr_get lens (lens_ofs + k) <> 0 ->
      0 <= arr_get (fst (itm_sort_k lens lens_ofs k offs work)) (arr_get lens (lens_ofs + k)) < WN).
Proof.
  intros lens lens_ofs offs work WN k Hk.
  rewrite itm_sort_ok_k_step by lia. rewrite <- (itm_sort_ok_k_fst lens lens_ofs offs work WN k Hk).
  destruct (itm_sort_ok_k lens lens_ofs k offs WN) as [o b]. cbn [fst snd sort_ok_body].
  destruct (Z.eqb_spec (arr_get lens (lens_ofs + k)) 0); cbn [negb].
  - intros Hb. split; [exact Hb | intros; lia].
  - cbn [snd]. intros Hb. apply andb_prop in Hb as [Hb Hr]. apply andb_prop in Hr as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. split; [exact Hb | intros _; lia].
Qed.

Lemma itm_sort_ok_k_le : forall lens lens_ofs offs WN k j, 0 <= j <= k ->
  snd (itm_sort_ok_k lens lens_ofs k offs WN) = true ->
  snd (itm_sort_ok_k lens lens_ofs j offs WN) = true.
Proof.
  intros lens lens_ofs offs WN k j Hj.
  remember (Z.to_nat (k - j)) as n eqn:Hn. replace k with (j + Z.of_nat n) by lia. clear k Hj Hn.
  induction n as [|n IH]; intros H.
  - replace (j + Z.of_nat 0) with j in H by lia. exact H.
  - apply IH. replace (j + Z.of_nat (S n)) with (j + Z.of_nat n + 1) in H by lia.
    destruct (Z_lt_le_dec (j + Z.of_nat n) 0).
    + unfold itm_sort_ok_k. rewrite forZ_nil by lia. reflexivity.
    + exact (proj1 (itm_sort_ok_k_inv lens lens_ofs offs offs WN (j + Z.of_nat n) ltac:(lia) H)).
Qed.

Lemma itm_sort_k_len : forall lens lens_ofs k offs work,
  arr_len (fst (itm_sort_k lens lens_ofs k offs work)) = arr_len offs
  /\ arr_len (snd (itm_sort_k lens lens_ofs k offs work)) = arr_len work.
Proof.
  intros lens lens_ofs k offs work. unfold itm_sort_k.
  destruct (Z_lt_le_dec k 0).
  - rewrite forZ_nil by lia. split; reflexivity.
  - apply (forZ_ind (fun _ ow => arr_len (fst ow) = arr_len offs /\ arr_len (snd ow) = arr_len work)); [| split; reflexivity | lia].
    intros i [o w] _ [H1 H2]. cbn [sort_body fst snd] in *.
    destruct (negb _); cbn [fst snd]; [rewrite !arr_len_set|]; split; assumption.
Qed.

Lemma itm_sort_k_offs_range : forall lens lens_ofs k count work i,
  0 <= arr_get (fst (itm_sort_k lens lens_ofs k (itm_offs count) work)) i < 65536.
Proof.
  intros lens lens_ofs k count work. unfold itm_sort_k.
  assert (B : forall i, 0 <= arr_get (itm_offs count) i < 65536).
  { intro i. rewrite itm_offs_eq. apply itm_offs_k_range. }
  destruct (Z_lt_le_dec k 0).
  - rewrite forZ_nil by lia. exact B.
  - apply (forZ_ind (fun _ ow => forall i, 0 <= arr_get (fst ow) i < 65536)); [| exact B | lia].
    intros j [o w] _ H i. cbn [sort_body fst] in *.
    destruct (negb _); cbn [fst]; [|apply H]. rewrite arr_get_set. destruct (_ && _); [apply wrap16_range | apply H].
Qed.

Lemma itm_sort_k_work_range : forall lens lens_ofs k offs work,
  (forall i, 0 <= arr_get work i < 65536) ->
  forall i, 0 <= arr_get (snd (itm_sort_k lens lens_ofs k offs work)) i < 65536.
Proof.
  intros lens lens_ofs k offs work B. unfold itm_sort_k.
  destruct (Z_lt_le_dec k 0).
  - rewrite forZ_nil by lia. exact B.
  - apply (forZ_ind (fun _ ow => forall i, 0 <= arr_get (snd ow) i < 65536)); [| exact B | lia].
    intros j [o w] _ H i. cbn [sort_body snd] in *.
    destruct (negb _); cbn [snd]; [|apply H]. rewrite arr_get_set. destruct (_ && _); [apply wrap16_range | apply H].
Qed.


Lemma it_loop_step : forall x codes st, 0 <= codes ->
  it_loop x codes st =
  match it_step x st with
  | ItCont st' => iterZ codes (fun st => match it_step x st with
                                         | ItCont st' => inl st'
                                         | ItBreak st' => inr (inl st')
                                         | ItFail st' => inr (inr st')
                                         end) (fun st => inl st) st'
  | ItBreak st' => inl st'
  | ItFail st' => inr st'
  end.
Proof.
  intros x codes st Hc. unfold it_loop. rewrite iterZ_step by lia.
  replace (codes + 1 - 1) with codes by lia. destruct (it_step x st); reflexivity.
Qed.

Definition it_loop_n (x : ItCtx) (n : Z) (st : ItSt) : ItSt + ItSt :=
  iterZ n (fun st => match it_step x st with
                     | ItCont st' => inl st'
                     | ItBreak st' => inr (inl st')
                     | ItFail st' => inr (inr st')
                     end) (fun st => inl st) st.

Lemma it_loop_is_n : forall x codes st, it_loop x codes st = it_loop_n x (codes + 1) st.
Proof. reflexivity. Qed.

Lemma it_loop_n_step : forall x n st, 0 < n ->
  it_loop_n x n st = match it_step x st with
                     | ItCont st' => it_loop_n x (n - 1) st'
                     | ItBreak st' => inl st'
                     | ItFail st' => inr st'
                     end.
Proof. intros x n st Hn. unfold it_loop_n at 1. rewrite iterZ_step by lia. destruct (it_step x st); reflexivity. Qed.

Lemma it_loop_ok_S : forall k x WN LN TN st,
  it_loop_ok (S k) x WN LN TN st =
  it_trip_ok x WN LN TN st &&
      match it_step x st with
      | ItCont st' => it_loop_ok k x WN LN TN st'
      | ItBreak st' => if negb (t_huff st' =? 0)
                       then (0 <=? t_next st' + t_huff st') && (t_next st' + t_huff st' <? TN)
                       else true
      | ItFail _ => true
      end.
Proof. reflexivity. Qed.

Lemma it_fill_len : forall here incr huff drop next fill tbl,
  arr_len (it_fill here incr huff drop next fill tbl) = arr_len tbl.
Proof.
  intros here incr huff drop next fill tbl. unfold it_fill.
  destruct (Z_lt_le_dec 0 fill).
  2: { rewrite loopZ_le0 by lia. reflexivity. }
  remember (Z.to_nat fill) as n eqn:Hn.
  assert (Hf : fill = Z.of_nat n) by lia. rewrite Hf at 1. clear Hn Hf.
  generalize fill at 1 as f. revert tbl.
  induction n as [|n IH]; intros tbl f.
  - rewrite loopZ_le0 by lia. reflexivity.
  - rewrite loopZ_step by lia. replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
    destruct (negb _).
    + rewrite IH. apply arr_len_set.
    + cbn [snd]. apply arr_len_set.
Qed.

Lemma itm_used_pow2 : forall root, 0 <= root <= 15 -> itm_used root = 2 ^ root.
Proof.
  intros root Hr. unfold itm_used, shl32. rewrite Z.shiftl_1_l. apply wrap32_id.
  split; [apply Z.pow_nonneg; lia|]. apply Z.pow_lt_mono_r; lia.
Qed.

Lemma pow2_root_bounds : forall root, 1 <= root <= 15 -> 2 <= 2 ^ root <= 32768.
Proof.
  intros root Hr. change 2 with (2 ^ 1) at 1. change 32768 with (2 ^ 15).
  split; apply Z.pow_le_mono_r; lia.
Qed.

Lemma itm_root_range : forall bits max min, 1 <= min <= max -> max <= 15 -> 0 <= bits ->
  min <= itm_root bits max min <= max /\ 1 <= itm_root bits max min <= 15.
Proof.
  intros bits max min H1 H2 H3. unfold itm_root.
  destruct (Z.ltb_spec max bits); [destruct (Z.ltb_spec max min)|destruct (Z.ltb_spec bits min)]; lia.
Qed.


Section SafeInv.
Variables (ty : codetype) (lens : arr) (lens_ofs codes : Z) (tbl : arr) (table bits : Z) (work : arr).
Hypothesis Hsafe : it_safe ty lens lens_ofs codes tbl table bits work = true.
Let count := itm_count lens lens_ofs codes.
Let max := itm_max count.
Let min := itm_min count max.
Let root := itm_root bits max min.

Lemma it_safe_codes : 0 <= codes <= arr_len work /\ arr_len work <= 65536.
Proof.
  unfold it_safe in Hsafe. apply andb_prop in Hsafe as [H _]. apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. lia.
Qed.

Lemma it_safe_max0 : max = 0 -> 0 <= table /\ table + 2 <= arr_len tbl.
Proof.
  intros Hm. unfold it_safe in Hsafe. apply andb_prop in Hsafe as [_ H]. cbv zeta in H.
  fold count in H. fold max in H. rewrite Hm in H. cbn [Z.eqb] in H.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma it_safe_sort : max <> 0 -> itm_reject ty max (it_left_check count) = false ->
  it_sort_ok lens lens_ofs codes (itm_offs count) (arr_len work) = true
  /\ (it_not_enough ty (itm_used root) = false ->
      0 <= table /\ table + itm_used root <= arr_len tbl
      /\ it_loop_ok (Z.to_nat (codes + 1)) (itm_ctx ty lens lens_ofs table root max)
                    (arr_len work) (arr_len lens) (arr_len tbl)
                    (itm_st0 min table root count tbl (itm_work lens lens_ofs codes (itm_offs count) work)) = true).
Proof.
  intros Hm Hr. unfold it_safe in Hsafe. apply andb_prop in Hsafe as [_ H]. cbv zeta in H.
  fold count in H. fold max in H. replace (max =? 0) with false in H by (symmetry; apply Z.eqb_neq; exact Hm).
  fold min in H. fold root in H. rewrite Hr in H. apply andb_prop in H as [H1 H2].
  split; [exact H1|]. intros Hne. rewrite Hne in H2.
  apply andb_prop in H2 as [H2 H4]. apply andb_prop in H2 as [H2 H3].
  apply Z.leb_le in H2. apply Z.leb_le in H3. split; [lia |]. split; [lia | exact H4].
Qed.
End SafeInv.


Definition test_fixed_lens : list Z :=
  repeat 8 144 ++ repeat 9 112 ++ repeat 7 24 ++ repeat 8 8.
Definition test_fixed_dist : list Z := repeat 5 32.
Definition test_codes19 : list Z := [3;3;3;3;3;3;3;3;0;0;0;0;0;0;0;0;0;0;0].
Definition test_over : list Z := [1;1;1;0;0].
Definition test_incomplete : list Z := [2;0;0;0].
Definition test_single : list Z := [0;1;0;0].
Definition test_deep : list Z := [1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;15].

Example it_safe_tests :
  it_safe LENS (arr_of_list test_fixed_lens) 0 288 (arr_make 1444 0) 0 9 (arr_make 288 0) = true
  /\ it_safe DISTS (arr_of_list (test_fixed_lens ++ test_fixed_dist)) 288 32 (arr_make 1444 0) 512 6 (arr_make 288 0) = true
  /\ it_safe CODES (arr_of_list test_codes19) 0 19 (arr_make 1444 0) 0 7 (arr_make 288 0) = true
  /\ it_safe LENS (arr_of_list test_over) 0 5 (arr_make 1444 0) 0 9 (arr_make 288 0) = true
  /\ it_safe LENS (arr_of_list test_incomplete) 0 4 (arr_make 1444 0) 0 9 (arr_make 288 0) = true
  /\ it_safe CODES (arr_of_list test_incomplete) 0 4 (arr_make 1444 0) 0 7 (arr_make 288 0) = true
  /\ it_safe LENS (arr_of_list test_single) 0 4 (arr_make 1444 0) 0 9 (arr_make 288 0) = true
  /\ it_safe DISTS (arr_of_list test_single) 0 4 (arr_make 1444 0) 700 6 (arr_make 288 0) = true
  /\ it_safe LENS (arr_of_list test_deep) 0 16 (arr_make 1444 0) 0 9 (arr_make 288 0) = true
  /\ it_safe DISTS (arr_of_list test_deep) 0 16 (arr_make 1444 0) 852 6 (arr_make 288 0) = true
  /\ it_safe LENS (arr_of_list []) 0 0 (arr_make 1444 0) 0 9 (arr_make 288 0) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example inflate_table_tests :
  (let '(r, _, t, b, _) := inflate_table LENS (arr_of_list test_fixed_lens) 0 288 (arr_make 1444 0) 0 9 (arr_make 288 0) in (r, t, b)) = (0, 512, 9)
  /\ (let '(r, _, t, b, _) := inflate_table LENS (arr_of_list test_over) 0 5 (arr_make 1444 0) 0 9 (arr_make 288 0) in (r, t, b)) = (-1, 0, 9)
  /\ (let '(r, _, t, b, _) := inflate_table DISTS (arr_of_list test_deep) 0 16 (arr_make 1444 0) 852 6 (arr_make 288 0) in r) = 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
