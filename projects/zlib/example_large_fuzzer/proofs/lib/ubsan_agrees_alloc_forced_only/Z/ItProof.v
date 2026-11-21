(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItGen.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItMath.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItSort.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItSimPre.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItSim2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItCover.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItShape.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItTable.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition may_link_op (op : Z) : bool :=
  (Z.land op 240 =? 0) || ((Z.land op 16 =? 0) && (Z.land op 64 =? 0)).

Lemma forallb_nth : forall f (l : list Z) k, forallb f l = true -> (k < length l)%nat -> f (nth k l 0) = true.
Proof.
  intros f l k H Hk. apply (proj1 (forallb_forall f l) H). apply nth_In. exact Hk.
Qed.

Lemma lext_nolink : forall k, (k < 31)%nat -> may_link_op (nth k lext_l 0) = false.
Proof.
  intros k Hk. apply Bool.negb_true_iff.
  apply (forallb_nth (fun v => negb (may_link_op v)) lext_l k); [vm_compute; reflexivity | exact Hk].
Qed.

Lemma dext_nolink : forall k, (k < 32)%nat -> may_link_op (nth k dext_l 0) = false /\ nth k dext_l 0 <> 0.
Proof.
  intros k Hk.
  pose proof (forallb_nth (fun v => negb (may_link_op v) && negb (v =? 0)) dext_l k ltac:(vm_compute; reflexivity) Hk) as H.
  cbn beta in H. apply Bool.andb_true_iff in H as [A B]. apply Bool.negb_true_iff in A. apply Bool.negb_true_iff in B.
  apply Z.eqb_neq in B. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma sym_entry_nolink : forall ty s, 0 <= s < nsyms ty ->
  fst (sym_entry ty s) = 0 \/ may_link_op (fst (sym_entry ty s)) = false.
Proof.
  intros ty s Hs. destruct ty; cbn [sym_entry nsyms] in *.
  - left. reflexivity.
  - destruct (Z.ltb_spec s 256); [left; reflexivity|].
    destruct (Z.eqb_spec s 256); [right; reflexivity|].
    right. cbn [fst]. apply lext_nolink. lia.
  - right. cbn [fst]. apply (proj1 (dext_nolink (Z.to_nat s) ltac:(lia))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Runs.
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
  Hypothesis HR : it_inputs_related ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2.
  #[local] Set Default Proof Using "HR".

  Definition LL : list Z := lens_list lens1 lens_ofs codes.
  Definition WL : list Z := wl_of LL.

  Lemma HR' :
    arr_len tbl1 = arr_len tbl2 /\ arr_len work1 = arr_len work2 /\
    0 <= codes <= 288 /\ codes <= arr_len work1 /\
    0 <= table /\ table + it_room ty <= arr_len tbl1 /\
    1 <= bits <= 15 /\
    (forall i, lens_ofs <= i < lens_ofs + codes -> arr_get lens1 i = arr_get lens2 i) /\
    (forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens1 i <= 15) /\
    it_ty_ok ty lens1 lens_ofs codes bits.
  Proof. exact HR. Qed.

  Lemma LL2 : LL = lens_list lens2 lens_ofs codes.
  Proof.
    pose proof HR' as (_ & _ & Hc & _ & _ & _ & _ & Hag & _). unfold LL, lens_list.
    apply map_ext_in. intros n Hn. apply in_seq in Hn. apply Hag. lia.
  Qed.

  Lemma Hlens2 : forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens2 i <= 15.
  Proof. pose proof HR' as (_ & _ & _ & _ & _ & _ & _ & Hag & Hrg & _). intros i Hi. rewrite <- Hag by lia. apply Hrg. lia. Qed.

  Lemma Hty1 : ty = CODES -> codes <= 19.
  Proof. pose proof HR' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & T). intros ->. cbn in T. lia. Qed.

  Lemma LL_Forall : Forall (fun l => 0 <= l <= 15) LL.
  Proof. pose proof HR' as (_ & _ & _ & _ & _ & _ & _ & _ & Hrg & _). unfold LL. apply lens_list_Forall. exact Hrg. Qed.

  Lemma LL_ty_ok : ty_ok ty LL bits.
  Proof.
    pose proof HR' as (_ & _ & Hc & _ & _ & _ & _ & _ & _ & T). unfold ty_ok. unfold it_ty_ok in T.
    assert (E : NC LL = codes) by (unfold LL; apply NC_lens; lia).
    destruct ty; rewrite ?E; try lia.
    destruct T as [A [B C]]. split; [lia|]. split; [lia|].
    unfold LL, lens_list. apply Forall_map. apply Forall_forall. intros n Hn. apply in_seq in Hn. apply C. lia.
  Qed.

  Lemma run1 : inflate_table ty lens1 lens_ofs codes tbl1 table bits work1 =
    (let '(ret, ws, toff, bits', ww) := it_abs WL LL ty table bits in (ret, applyw ws tbl1, toff, bits', applyw ww work1)).
  Proof.
    pose proof HR' as (_ & _ & Hc & Hw & _ & _ & Hb & _ & Hrg & _).
    apply (inflate_table_abs ty lens1 lens_ofs codes LL WL table bits Hc Hrg eq_refl eq_refl Hty1 Hb). exact Hw.
  Qed.

  Lemma run2 : inflate_table ty lens2 lens_ofs codes tbl2 table bits work2 =
    (let '(ret, ws, toff, bits', ww) := it_abs WL LL ty table bits in (ret, applyw ws tbl2, toff, bits', applyw ww work2)).
  Proof.
    pose proof HR' as (_ & Hw12 & Hc & Hw & _ & _ & Hb & _ & Hrg & _).
    apply (inflate_table_abs ty lens2 lens_ofs codes LL WL table bits Hc Hlens2 LL2 eq_refl Hty1 Hb). lia.
  Qed.

  Lemma props : let '(ret, ws, toff, bits', ww) := it_abs WL LL ty table bits in
    ret = 0 ->
    1 <= bits' <= 15 /\ table + 2 ^ bits' <= toff <= table + it_room ty /\
    (forall i v, In (i, v) ws -> table <= i < toff) /\
    (forall i, table <= i < toff -> In i (map fst ws)) /\
    (forall i v, In (i, v) ws -> entry_shape ty bits' (toff - table) (i - table) v).
  Proof.
    pose proof HR' as (_ & _ & _ & _ & _ & _ & Hb & _).
    exact (it_abs_props WL LL table bits LL_Forall eq_refl Hb ty LL_ty_ok).
  Qed.
End Runs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac setup HR :=
  pose proof (run1 _ _ _ _ _ _ _ _ _ _ _ HR) as R1;
  pose proof (run2 _ _ _ _ _ _ _ _ _ _ _ HR) as R2;
  pose proof (props _ _ _ _ _ _ _ _ _ _ _ HR) as PR;
  pose proof (HR' _ _ _ _ _ _ _ _ _ _ _ HR) as (Ht12 & Hw12 & Hc & Hw & Ht0 & Htr & Hb & Hag & Hrg & Hty);
  cbv zeta; rewrite R1; try rewrite R2; clear R1 R2;
  match goal with |- context [it_abs ?a ?b ?c ?d ?e] =>
    destruct (it_abs a b c d e) as [[[[ret ws] toff] bits'] ww] end;
  cbn [fst snd].

