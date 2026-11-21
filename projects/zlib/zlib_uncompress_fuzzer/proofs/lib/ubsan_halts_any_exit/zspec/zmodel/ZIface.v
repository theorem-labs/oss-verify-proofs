(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From Stdlib Require Import FMapPositive.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel Require Import Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.


Definition two31 : Z := 2147483648.
Definition two32 : Z := 4294967296.
Definition two64 : Z := 18446744073709551616.

Definition wrap8  (z : Z) : Z := Z.land z 255.
Definition wrap16 (z : Z) : Z := Z.land z 65535.
Definition wrap32 (z : Z) : Z := Z.land z 4294967295.
Definition wrap64 (z : Z) : Z := Z.land z 18446744073709551615.

Lemma wrap8_mod  : forall z, wrap8 z = z mod 2^8.
Proof. intro z. unfold wrap8. rewrite <- Z.land_ones by lia. reflexivity. Qed.
Lemma wrap16_mod : forall z, wrap16 z = z mod 2^16.
Proof. intro z. unfold wrap16. rewrite <- Z.land_ones by lia. reflexivity. Qed.
Lemma wrap32_mod : forall z, wrap32 z = z mod 2^32.
Proof. intro z. unfold wrap32. rewrite <- Z.land_ones by lia. reflexivity. Qed.

Lemma wrap16_range : forall z, 0 <= wrap16 z < 2^16.
Proof. intro z. rewrite wrap16_mod. apply Z.mod_pos_bound. lia. Qed.

Lemma wrap32_id : forall z, 0 <= z < 2^32 -> wrap32 z = z.
Proof. intros z H. rewrite wrap32_mod. apply Z.mod_small. exact H. Qed.
Lemma wrap8_id : forall z, 0 <= z < 2^8 -> wrap8 z = z.
Proof. intros z H. rewrite wrap8_mod. apply Z.mod_small. exact H. Qed.
Lemma wrap16_id : forall z, 0 <= z < 2^16 -> wrap16 z = z.
Proof. intros z H. rewrite wrap16_mod. apply Z.mod_small. exact H. Qed.

Definition swrap32 (z : Z) : Z := wrap32 (z + two31) - two31.

Lemma swrap32_id : forall z, - 2^31 <= z < 2^31 -> swrap32 z = z.
Proof. intros z H. unfold swrap32, two31. rewrite wrap32_id; lia. Qed.

Definition u64_of_s (z : Z) : Z := wrap64 z.



Definition shl32 (x n : Z) : Z := wrap32 (Z.shiftl x n).
Definition shl64 (x n : Z) : Z := wrap64 (Z.shiftl x n).

Definition not64 (x : Z) : Z := wrap64 (Z.lnot x).


Definition add64 (a b : Z) : Z := wrap64 (a + b).
Definition sub64 (a b : Z) : Z := wrap64 (a - b).
Definition mul64 (a b : Z) : Z := wrap64 (a * b).

Definition znth {A} (d : A) (l : list A) (i : Z) : A :=
  if i <? 0 then d else nth (Z.to_nat i) l d.
Definition zlength {A} (l : list A) : Z := Z.of_nat (length l).
Definition zrepeat {A} (v : A) (n : Z) : list A := repeat v (Z.to_nat n).

Lemma zlength_app : forall {A} (a b : list A), zlength (a ++ b) = zlength a + zlength b.
Proof. intros A a b. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_nil : forall {A}, zlength (@nil A) = 0.
Proof. reflexivity. Qed.
Lemma zlength_cons : forall {A} (x : A) l, zlength (x :: l) = 1 + zlength l.
Proof. intros A x l. unfold zlength. cbn [length]. lia. Qed.











Definition parr (A : Type) : Type := (Z * (Z -> A) * PositiveMap.t A)%type.
Definition arr : Type := parr Z.

Definition arr_key (i : Z) : positive := Z.to_pos (i + 1).

Definition arr_init {A : Type} (n : Z) (f : Z -> A) : parr A := (n, f, PositiveMap.empty A).
Definition arr_len {A : Type} (a : parr A) : Z := fst (fst a).
Definition arr_get {A : Type} (a : parr A) (i : Z) : A :=
  match a with (n, d, m) =>
    if (0 <=? i) && (i <? n) then
      match PositiveMap.find (arr_key i) m with Some v => v | None => d i end
    else d i
  end.
Definition arr_set {A : Type} (a : parr A) (i : Z) (v : A) : parr A :=
  match a with (n, d, m) =>
    if (0 <=? i) && (i <? n) then (n, d, PositiveMap.add (arr_key i) v m) else a
  end.

Definition arr_make {A : Type} (n : Z) (v : A) : parr A := arr_init n (fun _ => v).
Definition arr_inb {A : Type} (a : parr A) (i : Z) : bool := (0 <=? i) && (i <? arr_len a).

Lemma arr_key_inj : forall i j, 0 <= i -> 0 <= j -> arr_key i = arr_key j -> i = j.
Proof. intros i j Hi Hj H. unfold arr_key in H. apply (f_equal Z.pos) in H. rewrite !Z2Pos.id in H by lia. lia. Qed.

Lemma arr_len_init : forall {A} n (f : Z -> A), arr_len (arr_init n f) = n.
Proof. reflexivity. Qed.
Lemma arr_get_init : forall {A} n (f : Z -> A) i, arr_get (arr_init n f) i = f i.
Proof. intros A n f i. cbn. rewrite PositiveMap.gempty. destruct (_ && _); reflexivity. Qed.
Lemma arr_len_make : forall {A} n (v : A), arr_len (arr_make n v) = n.
Proof. reflexivity. Qed.
Lemma arr_get_make : forall {A} n (v : A) i, arr_get (arr_make n v) i = v.
Proof. intros. unfold arr_make. apply arr_get_init. Qed.
Lemma arr_len_set : forall {A} (a : parr A) i v, arr_len (arr_set a i v) = arr_len a.
Proof. intros A [[n d] m] i v. cbn. destruct (_ && _); reflexivity. Qed.

Lemma arr_inb_spec : forall {A} (a : parr A) i,
  arr_inb a i = true <-> 0 <= i < arr_len a.
Proof. intros A a i. unfold arr_inb. rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.


Lemma arr_set_oob : forall {A} (a : parr A) i v,
  ~ (0 <= i < arr_len a) -> arr_set a i v = a.
Proof.
  intros A [[n d] m] i v H. cbn in *.
  destruct ((0 <=? i) && (i <? n)) eqn:E; [|reflexivity].
  rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt in E. lia.
Qed.

Lemma arr_get_set_same : forall {A} (a : parr A) i v,
  0 <= i < arr_len a -> arr_get (arr_set a i v) i = v.
Proof.
  intros A [[n d] m] i v H. cbn in *.
  destruct ((0 <=? i) && (i <? n)) eqn:E.
  - cbn. rewrite E. rewrite PositiveMap.gss. reflexivity.
  - rewrite Bool.andb_false_iff, Z.leb_gt, Z.ltb_ge in E. lia.
Qed.

Lemma arr_get_set_other : forall {A} (a : parr A) i j v,
  i <> j -> arr_get (arr_set a i v) j = arr_get a j.
Proof.
  intros A [[n d] m] i j v Hij. cbn.
  destruct ((0 <=? i) && (i <? n)) eqn:Ei; [|reflexivity].
  cbn. destruct ((0 <=? j) && (j <? n)) eqn:Ej; [|reflexivity].
  rewrite PositiveMap.gso; [reflexivity|].
  rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt in Ei, Ej.
  intro E. apply Hij. symmetry. apply arr_key_inj; [lia|lia|exact E].
Qed.

Lemma arr_get_set : forall {A} (a : parr A) i j v,
  arr_get (arr_set a i v) j =
  if (i =? j) && arr_inb a i then v else arr_get a j.
Proof.
  intros A a i j v. destruct (Z.eqb_spec i j) as [<-|Hij]; cbn [andb].
  - destruct (arr_inb a i) eqn:E.
    + apply arr_get_set_same. apply arr_inb_spec. exact E.
    + rewrite arr_set_oob; [reflexivity|]. rewrite <- arr_inb_spec, E. discriminate.
  - apply arr_get_set_other. exact Hij.
Qed.



Fixpoint arr_upd {A} (a : parr A) (ofs : Z) (l : list A) : parr A :=
  match l with
  | [] => a
  | x :: r => arr_upd (arr_set a ofs x) (ofs + 1) r
  end.

Fixpoint arr_slice_nat {A} (a : parr A) (ofs : Z) (n : nat) : list A :=
  match n with
  | O => []
  | S k => arr_get a ofs :: arr_slice_nat a (ofs + 1) k
  end.
Definition arr_slice {A} (a : parr A) (ofs n : Z) : list A :=
  arr_slice_nat a ofs (Z.to_nat n).

Definition parr_of_list {A} (d : A) (l : list A) : parr A :=
  arr_upd (arr_make (zlength l) d) 0 l.
Definition arr_of_list (l : list Z) : arr := parr_of_list 0 l.

Fixpoint arr_blit_nat {A} (dst : parr A) (dofs : Z) (src : parr A) (sofs : Z) (n : nat) : parr A :=
  match n with
  | O => dst
  | S k => arr_blit_nat (arr_set dst dofs (arr_get src sofs)) (dofs + 1) src (sofs + 1) k
  end.
Definition arr_blit {A} (dst : parr A) (dofs : Z) (src : parr A) (sofs n : Z) : parr A :=
  arr_blit_nat dst dofs src sofs (Z.to_nat n).




Local Ltac bcase :=
  repeat match goal with
  | |- context [?x <=? ?y] => destruct (Z.leb_spec x y)
  | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
  | |- context [?x =? ?y] => destruct (Z.eqb_spec x y)
  end; cbn [andb]; try reflexivity; try lia.





Definition SM (St A : Type) : Type := St -> M (A * St).

Section SMOps.
  Context {St : Type}.

  Definition sret {A} (a : A) : SM St A := fun s => MRet (a, s).
  Definition sbind {A B} (m : SM St A) (f : A -> SM St B) : SM St B :=
    fun s => mbind (m s) (fun p => f (fst p) (snd p)).
End SMOps.

Declare Scope sm_scope.
Delimit Scope sm_scope with sm.
Notation "'do' x <- m ; k" := (sbind m (fun x => k))
  (at level 200, x name, m at level 100, k at level 200) : sm_scope.
Notation "'let*' x ':=' m 'in' k" := (sbind m (fun x => k))
  (at level 200, x pattern, m at level 100, k at level 200) : sm_scope.
Notation "m ;; k" := (sbind m (fun _ => k))
  (at level 100, right associativity) : sm_scope.
Local Open Scope sm_scope.

Lemma sbind_ret_l : forall {St A B} (a : A) (f : A -> SM St B), sbind (sret a) f = f a.
Proof. reflexivity. Qed.

Lemma mbind_ret_r : forall {A} (m : M A), mbind m (fun a => MRet a) = m.
Proof.
  intros A m; induction m as [a|bs k IH|c|k IH]; cbn; try reflexivity.
  - rewrite IH. reflexivity.
  - f_equal. extensionality b. apply IH.
Qed.

Lemma mbind_assoc' : forall {A B C} (m : M A) (f : A -> M B) (g : B -> M C),
  mbind (mbind m f) g = mbind m (fun a => mbind (f a) g).
Proof.
  intros A B C m f g. apply mbind_assoc. intros h1 h2 H. f_equal. extensionality b. apply H.
Qed.

Lemma sbind_ret_r : forall {St A} (m : SM St A), sbind m sret = m.
Proof.
  intros St A m. extensionality s. unfold sbind, sret.
  transitivity (mbind (m s) (fun a => MRet a)); [|apply mbind_ret_r].
  f_equal. extensionality p. destruct p; reflexivity.
Qed.

Lemma sbind_assoc : forall {St A B C} (m : SM St A) (f : A -> SM St B) (g : B -> SM St C),
  sbind (sbind m f) g = sbind m (fun a => sbind (f a) g).
Proof.
  intros St A B C m f g. extensionality s. unfold sbind. rewrite mbind_assoc'. reflexivity.
Qed.




Fixpoint iterK_nat {A B : Type} (n : nat) (step : A -> A + B) (a : A) : A + B :=
  match n with
  | O => inl a
  | S k => match step a with inl a' => iterK_nat k step a' | inr b => inr b end
  end.
Fixpoint iterK_pos {A B : Type} (p : positive) (step : A -> A + B) (a : A) : A + B :=
  match p with
  | xH => step a
  | xO q => match iterK_pos q step a with inl a' => iterK_pos q step a' | inr b => inr b end
  | xI q => match step a with
            | inl a' => match iterK_pos q step a' with inl a'' => iterK_pos q step a'' | inr b => inr b end
            | inr b => inr b
            end
  end.
Lemma iterK_nat_add : forall {A B} m n (step : A -> A + B) a,
  iterK_nat (m + n) step a = match iterK_nat m step a with inl a' => iterK_nat n step a' | inr b => inr b end.
Proof. induction m as [|m IH]; intros; cbn; [reflexivity|]. destruct (step a); [apply IH|reflexivity]. Qed.
Lemma iterK_pos_nat : forall {A B} p (step : A -> A + B) a,
  iterK_pos p step a = iterK_nat (Pos.to_nat p) step a.
Proof.
  induction p as [q IH|q IH|]; intros step a.
  - cbn [iterK_pos]. rewrite Pos2Nat.inj_xI. cbn [iterK_nat]. destruct (step a) as [a'|b]; [|reflexivity].
    replace (2 * Pos.to_nat q)%nat with (Pos.to_nat q + Pos.to_nat q)%nat by lia.
    rewrite iterK_nat_add, IH. destruct (iterK_nat _ _ _); [apply IH|reflexivity].
  - cbn [iterK_pos]. rewrite Pos2Nat.inj_xO.
    replace (2 * Pos.to_nat q)%nat with (Pos.to_nat q + Pos.to_nat q)%nat by lia.
    rewrite iterK_nat_add, IH. destruct (iterK_nat _ _ _); [apply IH|reflexivity].
  - cbn [iterK_pos]. change (Pos.to_nat 1) with 1%nat. cbn [iterK_nat]. destruct (step a); reflexivity.
Qed.

Definition iterZ {A B : Type} (n : Z) (step : A -> A + B) (dflt : A -> B) (a : A) : B :=
  match n with
  | Zpos p => match iterK_pos p step a with inl a' => dflt a' | inr b => b end
  | _ => dflt a
  end.

Lemma iterZ_nat : forall {A B} n (step : A -> A + B) dflt a,
  iterZ n step dflt a = match iterK_nat (Z.to_nat n) step a with inl a' => dflt a' | inr b => b end.
Proof. intros A B n step dflt a. destruct n; cbn [iterZ Z.to_nat iterK_nat]; try reflexivity. rewrite iterK_pos_nat. reflexivity. Qed.
Lemma iterZ_le0 : forall {A B} n (step : A -> A + B) dflt a,
  n <= 0 -> iterZ n step dflt a = dflt a.
Proof. intros A B n step dflt a H. destruct n; cbn [iterZ]; try reflexivity. lia. Qed.
Lemma iterZ_step : forall {A B} n (step : A -> A + B) dflt a,
  0 < n -> iterZ n step dflt a = match step a with
                                 | inl a' => iterZ (n - 1) step dflt a'
                                 | inr b => b
                                 end.
Proof.
  intros A B n step dflt a H. rewrite iterZ_nat.
  replace (Z.to_nat n) with (S (Z.to_nat (n - 1))) by lia. cbn [iterK_nat].
  destruct (step a) as [a'|b]; [|reflexivity]. rewrite iterZ_nat. reflexivity.
Qed.

Definition loopZ {A : Type} (n : Z) (step : A -> bool * A) (a : A) : A :=
  iterZ n (fun a => let '(c, a') := step a in if c then inl a' else inr a') (fun a => a) a.

Lemma loopZ_le0 : forall {A} n (step : A -> bool * A) a, n <= 0 -> loopZ n step a = a.
Proof. intros. unfold loopZ. apply iterZ_le0. assumption. Qed.
Lemma loopZ_step : forall {A} n (step : A -> bool * A) a,
  0 < n -> loopZ n step a = (let '(c, a') := step a in if c then loopZ (n - 1) step a' else a').
Proof.
  intros A n step a H. unfold loopZ at 1. rewrite iterZ_step by exact H.
  destruct (step a) as [c a']. destruct c; reflexivity.
Qed.

Definition forZ {A : Type} (lo hi : Z) (body : Z -> A -> A) (a : A) : A :=
  snd (loopZ (hi - lo)
         (fun ia : Z * A => let '(i, a) := ia in
            if i <? hi then (true, (i + 1, body i a)) else (false, (i, a)))
         (lo, a)).

Section SLoops.
  Context {St : Type}.













End SLoops.


Section RawMalloc.
  Variable MM : MallocModel.
  Context {St : Type}.
  Variable get_mm : St -> mm_state MM.
  Variable set_mm : mm_state MM -> St -> St.

  Definition smalloc (n : Z) : SM St (option blk) :=
    fun s => mbind (malloc_M MM (get_mm s) n) (fun r => MRet (snd r, set_mm (fst r) s)).

  Definition sfree (b : blk) : SM St unit :=
    fun s => MRet (tt, set_mm (mm_free MM (get_mm s) b) s).

  Definition sfree_opt (b : option blk) : SM St unit :=
    match b with None => sret tt | Some b => sfree b end.
End RawMalloc.

Arguments smalloc MM {St} get_mm set_mm n.
Arguments sfree MM {St} get_mm set_mm b.
Arguments sfree_opt MM {St} get_mm set_mm b.


Definition Z_OK            : Z := 0.
Definition Z_STREAM_END    : Z := 1.
Definition Z_NEED_DICT     : Z := 2.
Definition Z_STREAM_ERROR  : Z := -2.
Definition Z_DATA_ERROR    : Z := -3.
Definition Z_MEM_ERROR     : Z := -4.
Definition Z_BUF_ERROR     : Z := -5.

Definition Z_FINISH        : Z := 4.
Definition Z_BLOCK         : Z := 5.
Definition Z_TREES         : Z := 6.




Definition Z_DEFLATED : Z := 8.

Definition MSG_NULL : Z := -1.
Definition MSG_incorrect_header_check      : Z := 10.
Definition MSG_unknown_compression_method  : Z := 11.
Definition MSG_invalid_window_size         : Z := 12.
Definition MSG_unknown_header_flags_set    : Z := 13.
Definition MSG_header_crc_mismatch         : Z := 14.
Definition MSG_invalid_block_type          : Z := 15.
Definition MSG_invalid_stored_block_lengths : Z := 16.
Definition MSG_too_many_length_or_distance_symbols : Z := 17.
Definition MSG_invalid_code_lengths_set    : Z := 18.
Definition MSG_invalid_bit_length_repeat   : Z := 19.
Definition MSG_invalid_code_missing_end_of_block : Z := 20.
Definition MSG_invalid_literal_lengths_set : Z := 21.
Definition MSG_invalid_distances_set       : Z := 22.
Definition MSG_invalid_literal_length_code : Z := 23.
Definition MSG_invalid_distance_code       : Z := 24.
Definition MSG_invalid_distance_too_far_back : Z := 25.
Definition MSG_incorrect_data_check        : Z := 26.
Definition MSG_incorrect_length_check      : Z := 27.


Record zstrm : Type := mkZS {
  zs_total_in : Z;
  zs_total_out : Z;
  zs_adler : Z;
  zs_data_type : Z;
  zs_msg : Z
}.


Record ZCall : Type := mkZCall {
  zc_input : list Z;
  zc_avail_out : Z;
  zc_strm : zstrm
}.

Record ZRet : Type := mkZRet {
  zr_consumed : Z;
  zr_output : list Z;
  zr_strm : zstrm;
  zr_rc : Z
}.



Record zhooks (St : Type) : Type := mkHooks {
  zalloc : Z -> Z -> SM St (option (blk * (Z -> Z)));
  zfree : blk -> SM St unit
}.
Arguments mkHooks {St} _ _.
Arguments zalloc {St} _ _ _.
Arguments zfree {St} _ _.

Definition init_u8 (init : Z -> Z) (base i : Z) : Z := wrap8 (init (base + i)).
Definition init_u16 (init : Z -> Z) (base i : Z) : Z :=
  wrap8 (init (base + 2 * i)) + 256 * wrap8 (init (base + 2 * i + 1)).
Definition init_u32 (init : Z -> Z) (base i : Z) : Z :=
  init_u16 init base (2 * i) + 65536 * init_u16 init base (2 * i + 1).
Definition init_u64 (init : Z -> Z) (base i : Z) : Z :=
  init_u32 init base (2 * i) + 4294967296 * init_u32 init base (2 * i + 1).



Record deflate_api (DS : Type) : Type := mkDeflateApi {
  da_deflateInit2 : forall St : Type, zhooks St -> ZCall ->
      Z -> Z -> Z -> Z -> Z -> SM St (option DS * ZRet);
  da_deflateSetDictionary : DS -> ZCall -> list Z -> DS * ZRet;
  da_deflateBound : DS -> Z -> Z;
  da_deflate : DS -> ZCall -> Z -> DS * ZRet;
  da_deflateEnd : forall St : Type, zhooks St -> DS -> ZCall -> SM St ZRet;
  da_compressBound : Z -> Z;
  da_compress2 : forall St : Type, zhooks St -> Z -> list Z -> Z -> SM St (Z * list Z * Z)
}.
Arguments mkDeflateApi {DS} _ _ _ _ _ _ _.
Arguments da_deflateInit2 {DS} _ {St} _ _ _ _ _ _ _.
Arguments da_deflateSetDictionary {DS} _ _ _ _.
Arguments da_deflateBound {DS} _ _ _.
Arguments da_deflate {DS} _ _ _ _.
Arguments da_deflateEnd {DS} _ {St} _ _ _.
Arguments da_compressBound {DS} _ _.
Arguments da_compress2 {DS} _ {St} _ _ _ _.

Record inflate_api (IS : Type) : Type := mkInflateApi {
  ia_inflateInit2 : forall St : Type, zhooks St -> ZCall -> Z -> SM St (option IS * ZRet);
  ia_inflate : forall St : Type, zhooks St -> IS -> ZCall -> Z -> SM St (IS * ZRet);
  ia_inflateSetDictionary : forall St : Type, zhooks St -> IS -> ZCall -> list Z ->
      SM St (IS * ZRet);
  ia_inflateEnd : forall St : Type, zhooks St -> IS -> ZCall -> SM St ZRet;
  ia_uncompress2 : forall St : Type, zhooks St -> Z -> list Z -> Z ->
      SM St (Z * list Z * Z * Z)
}.
Arguments mkInflateApi {IS} _ _ _ _ _.
Arguments ia_inflateInit2 {IS} _ {St} _ _ _.
Arguments ia_inflate {IS} _ {St} _ _ _ _.
Arguments ia_inflateSetDictionary {IS} _ {St} _ _ _ _.
Arguments ia_inflateEnd {IS} _ {St} _ _ _.
Arguments ia_uncompress2 {IS} _ {St} _ _ _ _.

