(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.

Module InftreesCoverage.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition it_room (ty : codetype) : Z :=
  match ty with CODES => 128 | LENS => ENOUGH_LENS | DISTS => ENOUGH_DISTS end.

Definition may_link (e : Z) : bool :=
  (Z.land (code_op e) 240 =? 0) || ((Z.land (code_op e) 16 =? 0) && (Z.land (code_op e) 64 =? 0)).

Definition it_ty_ok (ty : codetype) (lens : arr) (lens_ofs codes bits : Z) : Prop :=
  match ty with
  | CODES => codes <= 19 /\ 7 <= bits /\ (forall i, lens_ofs <= i < lens_ofs + codes -> arr_get lens i <= 7)
  | LENS => codes <= 288
  | DISTS => codes <= 32
  end.

Definition nsyms (ty : codetype) : Z := match ty with CODES => 19 | LENS => 288 | DISTS => 32 end.

Definition sym_entry (ty : codetype) (s : Z) : Z * Z :=
  match ty with
  | CODES => (0, s)
  | LENS => if s <? 256 then (0, s)
            else if s =? 256 then (96, 0)
            else (nth (Z.to_nat (s - 257)) lext_l 0, nth (Z.to_nat (s - 257)) lbase_l 0)
  | DISTS => (nth (Z.to_nat s) dext_l 0, nth (Z.to_nat s) dbase_l 0)
  end.

Definition entry_shape (ty : codetype) (root used x e : Z) : Prop :=
  (exists s len,
     0 <= s < nsyms ty /\ 1 <= len <= 15 /\
     code_op e = fst (sym_entry ty s) /\ code_val e = snd (sym_entry ty s) /\
     ((x < 2 ^ root /\ len <= root /\ code_bits e = len) \/
      (2 ^ root <= x /\ root < len /\ code_bits e = len - root)))
  \/ (x < 2 ^ root /\ code_bits e = root /\ 1 <= code_op e <= 15 - root /\
      2 ^ root <= code_val e /\ code_val e + 2 ^ code_op e <= used)
  \/ (code_op e = 64 /\ code_bits e = 1 /\ code_val e = 0 /\ root = 1).

Section Stmts.
  Variable ty : codetype.
Variable lens1 : arr.
Variable lens2 : arr.
Variable lens_ofs : Z.
Variable codes : Z.
Variable tbl1 : arr.
Variable tbl2 : arr.
Variable table : Z.
Variable bits : Z.
Variable work1 : arr.
Variable work2 : arr.

  Definition it_inputs_related : Prop :=
    arr_len tbl1 = arr_len tbl2 /\ arr_len work1 = arr_len work2 /\
    0 <= codes <= 288 /\ codes <= arr_len work1 /\
    0 <= table /\ table + it_room ty <= arr_len tbl1 /\
    1 <= bits <= 15 /\
    (forall i, lens_ofs <= i < lens_ofs + codes -> arr_get lens1 i = arr_get lens2 i) /\
    (forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens1 i <= 15) /\
    it_ty_ok ty lens1 lens_ofs codes bits.

  Let r1 := inflate_table ty lens1 lens_ofs codes tbl1 table bits work1.
  Let r2 := inflate_table ty lens2 lens_ofs codes tbl2 table bits work2.
  Let ret1 := fst (fst (fst (fst r1))).   Let ret2 := fst (fst (fst (fst r2))).
  Let tbl1' := snd (fst (fst (fst r1))).  Let tbl2' := snd (fst (fst (fst r2))).
  Let table1' := snd (fst (fst r1)).     Let table2' := snd (fst (fst r2)).
  Let bits1' := snd (fst r1).            Let bits2' := snd (fst r2).

  Definition it_coverage_stmt : Prop :=
    it_inputs_related ->
    ret1 = ret2 /\
    (ret1 = 0 ->
       table1' = table2' /\ bits1' = bits2' /\
       1 <= bits1' <= 15 /\
       table + Z.shiftl 1 bits1' <= table1' <= table + it_room ty /\
       (forall i, table <= i < table1' -> arr_get tbl1' i = arr_get tbl2' i) /\
       (forall i, ~ (table <= i < table1') -> arr_get tbl1' i = arr_get tbl1 i /\ arr_get tbl2' i = arr_get tbl2 i)).

  Definition it_links_stmt : Prop :=
    it_inputs_related -> ret1 = 0 ->
    forall x, 0 <= x < Z.shiftl 1 bits1' ->
      let e := arr_get tbl1' (table + x) in
      may_link e = true -> code_op e <> 0 ->
      1 <= code_op e <= 15 /\
      Z.shiftl 1 bits1' <= code_val e /\
      table + code_val e + Z.shiftl 1 (code_op e) <= table1'.

  Definition it_nochain_stmt : Prop :=
    it_inputs_related -> ret1 = 0 ->
    forall i, table + Z.shiftl 1 bits1' <= i < table1' ->
      let e := arr_get tbl1' i in may_link e = true -> code_op e = 0.

  Definition it_lens_values_stmt : Prop :=
    it_inputs_related -> ret1 = 0 -> ty = LENS ->
    forall i, table <= i < table1' ->
      let e := arr_get tbl1' i in
      16 <= code_op e < 32 -> code_val e + Z.shiftl 1 (Z.land (code_op e) 15) - 1 <= 258.

  Definition it_shapes_stmt : Prop :=
    it_inputs_related -> ret1 = 0 ->
    forall i, table <= i < table1' ->
      entry_shape ty bits1' (table1' - table) (i - table) (arr_get tbl1' i).
End Stmts.


Definition inftrees_coverage : Prop :=
  forall ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2,
    it_coverage_stmt ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2 /\
    it_links_stmt ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2 /\
    it_nochain_stmt ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2 /\
    it_lens_values_stmt ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2.

Definition inftrees_shapes : Prop :=
  forall ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2,
    it_shapes_stmt ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2.
End InftreesCoverage.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Fixpoint allz (lo : Z) (n : nat) (f : Z -> bool) : bool :=
  match n with
  | O => true
  | S k => f lo && allz (lo + 1) k f
  end.

Lemma allz_spec : forall n lo f, allz lo n f = true -> forall i, lo <= i < lo + Z.of_nat n -> f i = true.
Proof.
  induction n as [|n IH]; intros lo f H i Hi; [cbn in Hi; lia|].
  cbn [allz] in H. apply andb_prop in H as [H0 H1].
  destruct (Z.eq_dec i lo) as [->|NE]; [exact H0|].
  apply (IH (lo + 1) f H1). rewrite Nat2Z.inj_succ in Hi. lia.
Qed.

Lemma allz_range : forall lo hi f, allz lo (Z.to_nat (hi - lo)) f = true ->
  forall i, lo <= i < hi -> f i = true.
Proof.
  intros lo hi f H i Hi. apply (allz_spec _ _ _ H). rewrite Z2Nat.id by lia. lia.
Qed.


Definition sym_shape_b (ty : codetype) (root x e s : Z) : bool :=
  (code_op e =? fst (sym_entry ty s)) && (code_val e =? snd (sym_entry ty s)) &&
  (((x <? 2 ^ root) && (1 <=? code_bits e) && (code_bits e <=? root) && (code_bits e <=? 15))
   || ((2 ^ root <=? x) && (1 <=? code_bits e) && (root + code_bits e <=? 15))).

Definition anyz (lo : Z) (n : nat) (f : Z -> bool) : bool := negb (allz lo n (fun s => negb (f s))).

Definition entry_shape_b (ty : codetype) (root used x e : Z) : bool :=
  anyz 0 (Z.to_nat (nsyms ty)) (sym_shape_b ty root x e)
  || ((x <? 2 ^ root) && (code_bits e =? root) && (1 <=? code_op e) && (code_op e <=? 15 - root)
      && (2 ^ root <=? code_val e) && (code_val e + 2 ^ code_op e <=? used))
  || ((code_op e =? 64) && (code_bits e =? 1) && (code_val e =? 0) && (root =? 1)).

Lemma sym_shape_b_sound : forall ty root used x e s,
  0 <= s < nsyms ty -> 0 <= root -> sym_shape_b ty root x e s = true -> entry_shape ty root used x e.
Proof.
  intros ty root used x e s Hs Hr H. unfold sym_shape_b in H.
  apply andb_prop in H as [H HB]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
  left. apply Bool.orb_prop in HB. destruct HB as [HB|HB].
  - apply andb_prop in HB as [HB B4]. apply andb_prop in HB as [HB B3]. apply andb_prop in HB as [B1 B2].
    apply Z.ltb_lt in B1. apply Z.leb_le in B2. apply Z.leb_le in B3. apply Z.leb_le in B4.
    exists s, (code_bits e). split; [exact Hs|]. split; [lia|]. split; [exact H1|]. split; [exact H2|].
    left. split; [exact B1|]. split; [exact B3|reflexivity].
  - apply andb_prop in HB as [HB B3]. apply andb_prop in HB as [B1 B2].
    apply Z.leb_le in B1. apply Z.leb_le in B2. apply Z.leb_le in B3.
    exists s, (root + code_bits e). split; [exact Hs|]. split; [lia|]. split; [exact H1|]. split; [exact H2|].
    right. split; [exact B1|]. split; [lia|lia].
Qed.

Lemma allz_negb_false : forall n lo f, allz lo n (fun s => negb (f s)) = false ->
  exists s, lo <= s < lo + Z.of_nat n /\ f s = true.
Proof.
  induction n as [|n IH]; intros lo f H; [discriminate H|].
  cbn [allz] in H. apply Bool.andb_false_iff in H. destruct H as [H|H].
  - exists lo. split; [rewrite Nat2Z.inj_succ; lia|]. destruct (f lo); [reflexivity|discriminate H].
  - destruct (IH _ _ H) as [s [Hs Hf]]. exists s. split; [rewrite Nat2Z.inj_succ; lia|exact Hf].
Qed.

Lemma anyz_true : forall n lo f, anyz lo n f = true -> exists s, lo <= s < lo + Z.of_nat n /\ f s = true.
Proof. intros n lo f H. unfold anyz in H. apply Bool.negb_true_iff in H. exact (allz_negb_false n lo f H). Qed.

Lemma entry_shape_b_sound : forall ty root used x e,
  0 <= root -> entry_shape_b ty root used x e = true -> entry_shape ty root used x e.
Proof.
  intros ty root used x e Hr H. unfold entry_shape_b in H.
  assert (Hn : 0 <= nsyms ty) by (destruct ty; cbn; lia).
  apply Bool.orb_prop in H. destruct H as [H|H]; [apply Bool.orb_prop in H; destruct H as [H|H]|].
  - destruct (anyz_true _ _ _ H) as [s [Hs Hf]]. rewrite Z2Nat.id in Hs by exact Hn.
    exact (sym_shape_b_sound ty root used x e s ltac:(lia) Hr Hf).
  - apply andb_prop in H as [H C6]. apply andb_prop in H as [H C5]. apply andb_prop in H as [H C4].
    apply andb_prop in H as [H C3]. apply andb_prop in H as [C1 C2].
    apply Z.ltb_lt in C1. apply Z.eqb_eq in C2. apply Z.leb_le in C3. apply Z.leb_le in C4.
    apply Z.leb_le in C5. apply Z.leb_le in C6.
    right; left. repeat split; assumption.
  - apply andb_prop in H as [H C4]. apply andb_prop in H as [H C3]. apply andb_prop in H as [C1 C2].
    apply Z.eqb_eq in C1. apply Z.eqb_eq in C2. apply Z.eqb_eq in C3. apply Z.eqb_eq in C4.
    right; right. repeat split; assumption.
Qed.

Definition cell_ok (ty : codetype) (root used x e : Z) : Prop :=
  entry_shape ty root used x e
  \/ (code_op e = 64 /\ ((x < 2 ^ root /\ 1 <= code_bits e <= root) \/ (2 ^ root <= x /\ 1 <= code_bits e <= 15 - root))).
Definition cell_ok_b (ty : codetype) (root used x e : Z) : bool :=
  entry_shape_b ty root used x e
  || ((code_op e =? 64) && (((x <? 2 ^ root) && (1 <=? code_bits e) && (code_bits e <=? root))
                            || ((2 ^ root <=? x) && (1 <=? code_bits e) && (code_bits e <=? 15 - root)))).
Lemma cell_ok_b_sound : forall ty root used x e, 0 <= root -> cell_ok_b ty root used x e = true -> cell_ok ty root used x e.
Proof.
  intros ty root used x e Hr H. unfold cell_ok_b in H. apply Bool.orb_prop in H. destruct H as [H|H].
  - left. exact (entry_shape_b_sound ty root used x e Hr H).
  - right. apply andb_prop in H as [A B]. apply Z.eqb_eq in A. split; [exact A|].
    apply Bool.orb_prop in B. destruct B as [B|B].
    + apply andb_prop in B as [B B3]. apply andb_prop in B as [B1 B2].
      apply Z.ltb_lt in B1. apply Z.leb_le in B2. apply Z.leb_le in B3. left. lia.
    + apply andb_prop in B as [B B3]. apply andb_prop in B as [B1 B2].
      apply Z.leb_le in B1. apply Z.leb_le in B2. apply Z.leb_le in B3. right. lia.
Qed.

Definition rep_root (get : Z -> Z) (root : Z) : Prop :=
  forall x x', 0 <= x < 2 ^ root -> 0 <= x' < 2 ^ root ->
    1 <= code_bits (get x) <= root -> x' mod 2 ^ code_bits (get x) = x mod 2 ^ code_bits (get x) ->
    get x' = get x.
Definition rep_sub (get : Z -> Z) (root : Z) : Prop :=
  forall x, 0 <= x < 2 ^ root -> 1 <= code_op (get x) <= 15 ->
    forall y y', 0 <= y < 2 ^ code_op (get x) -> 0 <= y' < 2 ^ code_op (get x) ->
      1 <= code_bits (get (code_val (get x) + y)) ->
      y' mod 2 ^ code_bits (get (code_val (get x) + y)) = y mod 2 ^ code_bits (get (code_val (get x) + y)) ->
      get (code_val (get x) + y') = get (code_val (get x) + y).
Definition TBLg (ty : codetype) (get : Z -> Z) (root used : Z) : Prop :=
  1 <= root <= 15 /\ 2 ^ root <= used
  /\ (forall x, 0 <= x < used -> cell_ok ty root used x (get x))
  /\ rep_root get root /\ rep_sub get root.

Definition cpok (ty : codetype) (codes : arr) (p : codeptr) (root : Z) : Prop :=
  match p with
  | CDyn ofs => 0 <= ofs /\ exists used, ofs + used <= 1444 /\ TBLg ty (fun x => arr_get codes (ofs + x)) root used
  | CLenfix => ty = LENS /\ root = 9
  | CDistfix => ty = DISTS /\ root = 5
  end.

Definition rep_root_b (get : Z -> Z) (root : Z) : bool :=
  allz 0 (Z.to_nat (2 ^ root)) (fun x =>
    let e := get x in let b := code_bits e in
    if (1 <=? b) && (b <=? root)
    then allz 0 (Z.to_nat (2 ^ (root - b))) (fun k => get (x mod 2 ^ b + k * 2 ^ b) =? e)
    else true).
Definition rep_sub_b (get : Z -> Z) (root : Z) : bool :=
  allz 0 (Z.to_nat (2 ^ root)) (fun x =>
    let L := get x in let o := code_op L in
    if (1 <=? o) && (o <=? 15)
    then allz 0 (Z.to_nat (2 ^ o)) (fun y =>
           let e := get (code_val L + y) in let b := code_bits e in
           if (1 <=? b) && (b <=? o)
           then allz 0 (Z.to_nat (2 ^ (o - b))) (fun k => get (code_val L + y mod 2 ^ b + k * 2 ^ b) =? e)
           else if 1 <=? b then true
           else true)
    else true).
Definition tblb (ty : codetype) (get : Z -> Z) (root used : Z) : bool :=
  (1 <=? root) && (root <=? 15) && (2 ^ root <=? used)
  && allz 0 (Z.to_nat used) (fun x => cell_ok_b ty root used x (get x))
  && rep_root_b get root && rep_sub_b get root.


Definition HB (h b : Z) : Prop := 0 <= b <= 63 /\ 0 <= h < 2 ^ b.


Definition is_linkb (e : Z) : bool := (1 <=? code_op e) && (code_op e <=? 15).
Definition lneed (s : inflate_state) (p : codeptr) (root h : Z) : Z :=
  let e := code_at s p (h mod 2 ^ root) in
  if is_linkb e
  then code_bits e + code_bits (code_at s p (code_val e + h mod 2 ^ (code_bits e + code_op e) / 2 ^ code_bits e))
  else code_bits e.
Definition cl_ext (v : Z) : Z := if v <? 16 then 0 else if v =? 16 then 2 else if v =? 17 then 3 else 7.
Definition cneed (s : inflate_state) (h : Z) : Z :=
  let e := code_at s (is_lencode s) (h mod 2 ^ is_lenbits s) in code_bits e + cl_ext (code_val e).

Definition CORE (s : inflate_state) : Prop :=
  (is_window_blk s = None -> is_wsize s = 0)
  /\ (is_window_blk s <> None -> arr_len (is_window s) = shl32 1 (is_wbits s) /\ is_wbits s <> 0)
  /\ (is_wsize s <> 0 -> is_wsize s = shl32 1 (is_wbits s))
  /\ 0 <= is_whave s /\ 0 <= is_wnext s
  /\ (is_wsize s = 0 -> is_whave s = 0 /\ is_wnext s = 0)
  /\ (is_wsize s <> 0 -> is_wnext s < is_wsize s /\ is_whave s <= is_wsize s)
  /\ (is_wsize s <> 0 -> is_whave s < is_wsize s -> is_wnext s = is_whave s)
  /\ (is_wbits s = 0 -> is_window_blk s = None /\ is_wrap s <> 0)
  /\ arr_len (is_lens s) = 320 /\ arr_len (is_work s) = 288 /\ arr_len (is_codes s) = 1444
  /\ is_sane s = 1
  /\ 0 <= is_length s < 2 ^ 32.

Definition common (s : inflate_state) : Prop :=
  is_wbits s <> 0 /\ (is_flags s = 0 -> adler_canon (is_check s)).

Definition tables (s : inflate_state) : Prop :=
  cpok LENS (is_codes s) (is_lencode s) (is_lenbits s) /\ cpok DISTS (is_codes s) (is_distcode s) (is_distbits s).

Definition MF (m : Z) (s : inflate_state) (h b : Z) : Prop :=
  if m =? HEAD then (is_wrap s = 0 -> b < 8) /\ (is_flags s = 0 -> adler_canon (is_check s))
  else if m =? FLAGS then is_wbits s <> 0 /\ adler_canon (is_check s)
  else if (m =? TIME) || (m =? OS) then common s
  else if m =? EXLEN then common s /\ (Z.land (is_flags s) 1024 = 0 -> b < 8)
  else if (m =? EXTRA) || (m =? NAME) || (m =? COMMENT) then common s /\ b < 8
  else if m =? HCRC then common s /\ (Z.land (is_flags s) 512 = 0 -> b < 8)
  else if m =? DICTID then common s
  else if m =? DICT then is_wbits s <> 0 /\ b < 8
  else if (m =? TYPE) || (m =? TYPEDO) then common s /\ b < 8
  else if m =? STORED then common s
  else if (m =? COPY_) || (m =? COPY) then common s /\ b < 8
  else if m =? TABLE then common s /\ b < 14
  else if m =? LENLENS then
    common s /\ b < 8
    /\ 4 <= is_ncode s <= 19 /\ 257 <= is_nlen s <= 286 /\ 1 <= is_ndist s <= 30 /\ 0 <= is_have s < is_ncode s
    /\ (forall k, 0 <= k < is_have s -> 0 <= arr_get (is_lens s) (arr_get order_a k) <= 7)
  else if m =? CODELENS then
    common s /\ (b < 8 \/ b < cneed s h)
    /\ 257 <= is_nlen s <= 286 /\ 1 <= is_ndist s <= 30 /\ 0 <= is_have s < is_nlen s + is_ndist s
    /\ (forall i, 0 <= i < is_have s -> 0 <= arr_get (is_lens s) i <= 15)
    /\ cpok CODES (is_codes s) (is_lencode s) (is_lenbits s)
  else if m =? LEN_ then common s /\ b < 8 /\ tables s
  else if m =? LEN then common s /\ (b < 8 \/ b < lneed s (is_lencode s) (is_lenbits s) h) /\ tables s
  else if m =? LENEXT then common s /\ (b < 8 \/ b < is_extra s) /\ tables s /\ 0 <= is_extra s <= 15 /\ 1 <= is_length s < 2 ^ 16
  else if m =? DIST then common s /\ (b < 8 \/ b < lneed s (is_distcode s) (is_distbits s) h) /\ tables s /\ 1 <= is_length s
  else if m =? DISTEXT then
    common s /\ (b < 8 \/ b < is_extra s) /\ tables s /\ 1 <= is_length s /\ 0 <= is_extra s <= 15 /\ 1 <= is_offset s < 2 ^ 16
  else if m =? MATCH then common s /\ b < 8 /\ tables s /\ 1 <= is_length s /\ 1 <= is_offset s < 2 ^ 32
  else if m =? LIT then common s /\ b < 8 /\ tables s
  else if (m =? CHECK) || (m =? LENGTH) || (m =? DONE) then common s
  else if m =? BAD then (is_flags s = 0 -> adler_canon (is_check s))
  else if m =? MEM then is_hold s = h /\ is_bits s = b
  else False.

Definition INV (s : inflate_state) : Prop :=
  CORE s /\ HB (is_hold s) (is_bits s) /\ MF (is_mode s) s (is_hold s) (is_bits s).

Definition REGS (c : icall) (r : iregs) : Prop :=
  0 <= ir_next r /\ 0 <= ir_have r /\ ir_next r + ir_have r = arr_len (ic_input c)
  /\ 0 <= ir_put r /\ 0 <= ir_left r /\ ir_put r + ir_left r = arr_len (ic_outbuf c)
  /\ HB (ir_hold r) (ir_bits r)
  /\ (forall i, 0 <= arr_get (ic_input c) i < 256)
  /\ arr_len (ic_input c) < 2 ^ 32 /\ arr_len (ic_outbuf c) < 2 ^ 32.

Definition WF (m : Z) (c : icall) (r : iregs) : Prop :=
  if (m =? LENGTH) || (m =? DONE) || (m =? BAD) then True
  else if (m =? HEAD) || (m =? FLAGS) then ir_out r = arr_len (ic_outbuf c) /\ ir_put r = 0
  else ir_out r = arr_len (ic_outbuf c).

Definition WINV (w : iw) : Prop :=
  let s := w_s w in let c := w_c w in let r := w_r w in
  CORE s /\ REGS c r /\ MF (is_mode s) s (ir_hold r) (ir_bits r) /\ WF (is_mode s) c r
  /\ (is_wbits s = 0 -> ir_put r = 0).


Definition rank (m : Z) : Z :=
  if (HEAD <=? m) && (m <=? HCRC) then 3
  else if m =? DICT then 3
  else if (m =? TYPE) || (m =? TYPEDO) then 2
  else if (m =? COPY_) || (m =? COPY) then 3
  else if (m =? STORED) || (m =? DISTEXT) || (m =? MATCH) || (m =? CHECK) || (m =? LENGTH) then 1
  else 0.

Lemma rank_range : forall m, 0 <= rank m <= 3.
Proof.
  intros m. unfold rank.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia.
Qed.

Definition PHI (w : iw) : Z :=
  let r := w_r w in 64 * ir_have r + 8 * ir_bits r + 8 * ir_left r + rank (is_mode (w_s w)).

Definition POST (w0 : iw) {A} (res : ares A) : Prop :=
  match res with
  | ARun _ w' => WINV w' /\ PHI w' < PHI w0
  | ALeave w' => WINV w'
  | ARet _ w' => WINV w' /\ INV (w_s w')
  end.
