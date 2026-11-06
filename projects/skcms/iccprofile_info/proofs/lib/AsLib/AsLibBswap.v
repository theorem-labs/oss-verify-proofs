(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec SeqExec SymExec PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound.
Unset Lia Cache. Unset Nia Cache.   (* [comment removed for export] *)
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac el_t1 := (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker.
(* [comment removed for export] *)
Local Ltac el_dm_pose x k := let v := eval vm_compute in k in lazymatch v with Zpos _ =>   (* [comment removed for export] *)
  lazymatch goal with _ : (x = k * (x / k) + x mod k)%Z |- _ => fail | _ =>
    pose proof (Z.div_mod x k ltac:(vm_compute; discriminate)); pose proof (Z.mod_pos_bound x k ltac:(vm_compute; reflexivity)) end end.
Local Ltac el_dm := repeat match goal with
  | |- context [ (?x / ?k)%Z ] => el_dm_pose x k
  | |- context [ (?x mod ?k)%Z ] => el_dm_pose x k
  | H : ?T |- _ => lazymatch T with (_ <= _)%Z => idtac | (_ < _)%Z => idtac | @eq Z _ _ => idtac | _ /\ _ => idtac | _ \/ _ => idtac end;
      match T with context [ (?x / ?k)%Z ] => el_dm_pose x k | context [ (?x mod ?k)%Z ] => el_dm_pose x k end
  end.
Local Ltac el_lia_core3 := first [ el_t1 | Zify.zify; xlia zchecker ].   (* [comment removed for export] *)
Local Ltac el_lia_core := first [ el_t1 | ((progress el_dm); el_t1) ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import ASX. Import ASXS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive bbit : Type := BO | BI | BV (k j : nat).

Definition bbit_eqb (x y : bbit) : bool :=
  match x, y with
  | BO, BO => true | BI, BI => true
  | BV k j, BV k' j' => Nat.eqb k k' && Nat.eqb j j'
  | _, _ => false
  end.

Definition bval (nu : nat -> Z) (b : bbit) : bool :=
  match b with BO => false | BI => true | BV k j => Z.testbit (nu k) (Z.of_nat j) end.

Definition bconst (z : Z) : list bbit :=
  map (fun i => if Z.testbit z (Z.of_nat i) then BI else BO) (seq 0 64).

Definition bbyte (sx : bool) (k : nat) : list bbit :=
  map (fun j => BV k j) (seq 0 8) ++ repeat (if sx then BV k 7%nat else BO) 56.

Definition band1 (x y : bbit) : option bbit :=
  match x, y with
  | BO, _ => Some BO
  | _, BO => Some BO
  | BI, _ => Some y
  | _, BI => Some x
  | _, _ => if bbit_eqb x y then Some x else None
  end.

Definition bor1 (x y : bbit) : option bbit :=
  match x, y with
  | BI, _ => Some BI
  | _, BI => Some BI
  | BO, _ => Some y
  | _, BO => Some x
  | _, _ => if bbit_eqb x y then Some x else None
  end.

(* [comment removed for export] *)
Definition badd1 (x y : bbit) : option bbit :=
  match x, y with
  | BO, _ => Some y
  | _, BO => Some x
  | _, _ => None
  end.

Fixpoint map2o (f : bbit -> bbit -> option bbit) (l1 l2 : list bbit) : option (list bbit) :=
  match l1, l2 with
  | [], [] => Some []
  | x :: r1, y :: r2 =>
      match f x y, map2o f r1 r2 with
      | Some b, Some r => Some (b :: r)
      | _, _ => None
      end
  | _, _ => None
  end.

Definition bshl (s : nat) (l : list bbit) : list bbit := firstn 64 (repeat BO s ++ l).
Definition bshr (s : nat) (l : list bbit) : list bbit := skipn s l ++ repeat BO s.
(* [comment removed for export] *)
Definition bsext (w : nat) (l : list bbit) : list bbit := firstn w l ++ repeat (nth (w - 1) l BO) (64 - w).
Definition bzext (w : nat) (l : list bbit) : list bbit := firstn w l ++ repeat BO (64 - w).

Definition zbits (k : Z) : list bool := map (fun i => Z.testbit k (Z.of_nat i)) (seq 0 64).

(* [comment removed for export] *)
Fixpoint bmul (kb : list bool) (s : nat) (l : list bbit) : option (list bbit) :=
  match kb with
  | [] => Some (repeat BO 64)
  | b :: rest =>
      match bmul rest (S s) l with
      | Some r => if b then map2o badd1 (bshl s l) r else Some r
      | None => None
      end
  end.

Fixpoint find_atom (atoms : list (expr * (bool * nat))) (e : expr) : option (bool * nat) :=
  match atoms with
  | [] => None
  | (a, r) :: rest => if expr_eqb e a then Some r else find_atom rest e
  end.

Definition obind (x : option (list bbit)) (f : list bbit -> option (list bbit)) : option (list bbit) :=
  match x with Some l => f l | None => None end.

Fixpoint beval (atoms : list (expr * (bool * nat))) (e : expr) {struct e} : option (list bbit) :=
  match find_atom atoms e with
  | Some (sx, k) => Some (bbyte sx k)
  | None =>
    match e with
    | ELit z => Some (bconst (z mod 2 ^ 64))
    | EAlu op a b =>
        match op with
        | ALU_AND => obind (beval atoms a) (fun la => obind (beval atoms b) (fun lb => map2o band1 la lb))
        | ALU_OR  => obind (beval atoms a) (fun la => obind (beval atoms b) (fun lb => map2o bor1 la lb))
        | ALU_ADD => obind (beval atoms a) (fun la => obind (beval atoms b) (fun lb => map2o badd1 la lb))
        | ALU_SLL =>
            match b with
            | ELit s => if (0 <=? s) && (s <? 64) then obind (beval atoms a) (fun la => Some (bshl (Z.to_nat s) la)) else None
            | _ => None
            end
        | ALU_SRL =>
            match b with
            | ELit s => if (0 <=? s) && (s <? 64) then obind (beval atoms a) (fun la => Some (bshr (Z.to_nat s) la)) else None
            | _ => None
            end
        | _ => None
        end
    | EMd M_MUL (ELit k) a => obind (beval atoms a) (fun la => bmul (zbits (k mod 2 ^ 64)) 0 la)
    | EAluw ALU_SLL a (ELit s) =>
        if (0 <=? s) && (s <? 32) then obind (beval atoms a) (fun la => Some (bsext 32 (bshl (Z.to_nat s) la))) else None
    | EExt sx lo n a =>
        if (1 <=? n)%nat && (lo + n <=? 8)%nat then
          obind (beval atoms a) (fun la => let sh := bshr (8 * lo) la in
                                           Some (if sx then bsext (8 * n) sh else bzext (8 * n) sh))
        else None
    | _ => None
    end
  end.

(* [comment removed for export] *)
Definition bytes_bits (ks : list nat) : list bbit :=
  flat_map (fun k => map (fun j => BV k j) (seq 0 8)) ks ++ repeat BO (64 - 8 * length ks).

Fixpoint bytes_val (nu : nat -> Z) (ks : list nat) : Z :=
  match ks with [] => 0 | k :: r => nu k + 256 * bytes_val nu r end.

Fixpoint list_bbit_eqb (l1 l2 : list bbit) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: r1, y :: r2 => bbit_eqb x y && list_bbit_eqb r1 r2
  | _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bbit_eqb_eq : forall x y, bbit_eqb x y = true -> x = y.
Proof.
  intros [| |k j] [| |k' j'] H; cbn in H; try discriminate; try reflexivity.
  apply andb_prop in H as [A B]. apply Nat.eqb_eq in A. apply Nat.eqb_eq in B. subst. reflexivity.
Qed.

Lemma list_bbit_eqb_eq : forall l1 l2, list_bbit_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|x r1 IH]; intros [|y r2] H; cbn in H; try discriminate; try reflexivity.
  apply andb_prop in H as [A B]. apply bbit_eqb_eq in A. rewrite (IH _ B). subst. reflexivity.
Qed.

Lemma tb_small_high : forall v i, 0 <= v < 2 ^ i -> Z.testbit v i = false.
Proof.
  intros v i Hv.
  destruct (Z_lt_le_dec i 0) as [Hi|Hi]; [apply Z.testbit_neg_r; lia|].
  apply Z.testbit_false; [lia|]. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma tb_small_high' : forall v n i, 0 <= v < 2 ^ n -> 0 <= n <= i -> Z.testbit v i = false.
Proof.
  intros v n i Hv Hi. apply tb_small_high. split; [lia|].
  eapply Z.lt_le_trans; [apply Hv|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma tb_top : forall N x i, 0 <= i < N -> 2 ^ N - 2 ^ i <= x < 2 ^ N -> Z.testbit x i = true.
Proof.
  intros N x i Hi Hx. apply Z.testbit_true; [lia|].
  assert (Hp : 2 ^ N = 2 ^ i * 2 ^ (N - i)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (H1 : 0 < 2 ^ (N - i - 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (H2 : 2 ^ (N - i) = 2 * 2 ^ (N - i - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  assert (H0 : 0 < 2 ^ i) by (apply Z.pow_pos_nonneg; lia).
  assert (Hq : x / 2 ^ i = 2 ^ (N - i) - 1).
  { symmetry. apply Z.div_unique with (r := x - 2 ^ i * (2 ^ (N - i) - 1)); [left; nia | nia]. }
  rewrite Hq, H2. replace (2 * 2 ^ (N - i - 1) - 1) with (1 + (2 ^ (N - i - 1) - 1) * 2) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma tb_add_mul_low : forall v n m i, 0 <= v < 2 ^ n -> 0 <= i < n ->
  Z.testbit (v + 2 ^ n * m) i = Z.testbit v i.
Proof.
  intros v n m i Hv Hi.
  rewrite <- (Z.mod_pow2_bits_low (v + 2 ^ n * m) n i) by lia.
  replace (v + 2 ^ n * m) with (v + m * 2 ^ n) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma swrap_bits : forall w X i, 1 <= w <= 64 -> 0 <= i < 64 ->
  Z.testbit ((bv_swrap (Z.to_N w) X) mod 2 ^ 64) i
  = (if i <? w then Z.testbit X i else Z.testbit X (w - 1)).
Proof.
  intros w X i Hw Hi.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. rewrite !Z2N.id by lia.
  set (h := 2 ^ (w - 1)).
  assert (Hh2 : 2 ^ w / 2 = h).
  { subst h. replace w with (w - 1 + 1) at 1 by lia. rewrite Z.pow_add_r, Z.pow_1_r by lia.
    rewrite Z.div_mul by lia. reflexivity. }
  rewrite !Hh2.
  assert (Hh : 0 < h) by (subst h; apply Z.pow_pos_nonneg; lia).
  assert (H2 : 2 ^ w = 2 * h) by (subst h; rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  assert (P : 2 ^ w * 2 ^ (64 - w) = 2 ^ 64) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Hw64 : 2 ^ w <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  set (Y := X mod 2 ^ w).
  assert (HY : 0 <= Y < 2 ^ w) by (subst Y; apply Z.mod_pos_bound; lia).
  assert (Hbit : forall j, j < w -> Z.testbit Y j = Z.testbit X j).
  { intros j Hj. subst Y. apply Z.mod_pow2_bits_low. lia. }
  assert (Htop : Z.testbit X (w - 1) = (h <=? Y)).
  { rewrite <- Hbit by lia.
    destruct (Z.leb_spec h Y).
    - apply Z.testbit_true; [lia|]. subst h.
      rewrite <- (Z.div_unique Y (2 ^ (w - 1)) 1 (Y - 2 ^ (w - 1))); [reflexivity | left; lia | lia].
    - apply Z.testbit_false; [lia|]. subst h. rewrite Z.div_small by lia. reflexivity. }
  assert (Hm : (X + h) mod 2 ^ w = (Y + h) mod 2 ^ w).
  { subst Y. rewrite Zplus_mod_idemp_l. reflexivity. }
  rewrite Hm.
  destruct (Z.leb_spec h Y) as [HhY|HhY].
  - (* [comment removed for export] *)
    rewrite <- (Z.mod_unique (Y + h) (2 ^ w) 1 (Y + h - 2 ^ w)) by lia.
    replace ((Y + h - 2 ^ w - h) mod 2 ^ 64) with (Y + 2 ^ w * (2 ^ (64 - w) - 1)).
    2:{ rewrite Z.mul_sub_distr_l, P. apply Z.mod_unique with (q := -1); [left; lia | lia]. }
    destruct (Z.ltb_spec i w).
    + rewrite tb_add_mul_low by lia. apply Hbit. lia.
    + rewrite Htop. replace (h <=? Y) with true by (symmetry; apply Z.leb_le; lia).
      apply tb_top with (N := 64); [lia|].
      rewrite Z.mul_sub_distr_l, P.
      assert (2 ^ w <= 2 ^ i) by (apply Z.pow_le_mono_r; lia). lia.
  - (* [comment removed for export] *)
    rewrite (Z.mod_small (Y + h)) by lia. replace (Y + h - h) with Y by lia.
    rewrite Z.mod_small by lia.
    destruct (Z.ltb_spec i w).
    + apply Hbit. lia.
    + rewrite Htop. replace (h <=? Y) with false by (symmetry; apply Z.leb_gt; lia).
      apply (tb_small_high' Y w i); lia.
Qed.

Lemma lor_disjoint_add : forall a b, 0 <= a -> 0 <= b ->
  (forall n, 0 <= n -> Z.testbit a n && Z.testbit b n = false) -> a + b = Z.lor a b.
Proof.
  intros a b Ha Hb H.
  assert (Hl : Z.land a b = 0).
  { apply Z.bits_inj_0. intros n. rewrite Z.land_spec.
    destruct (Z_lt_le_dec n 0); [rewrite Z.testbit_neg_r by lia; reflexivity | apply H; lia]. }
  rewrite Z.add_nocarry_lxor by exact Hl. apply Z.lxor_lor. exact Hl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
Variable nu : nat -> Z.
Hypothesis Hnu : forall k, 0 <= nu k < 256.

Definition wbits (x : Z) (l : list bbit) : Prop :=
  length l = 64%nat /\ forall i, (i < 64)%nat -> Z.testbit x (Z.of_nat i) = bval nu (nth i l BO).

Lemma nth_map_seq0 : forall {A} (f : nat -> A) n len (d : A), (n < len)%nat -> nth n (map f (seq 0 len)) d = f n.
Proof.
  intros A f n len d H.
  rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact H).
  rewrite map_nth, seq_nth by exact H. reflexivity.
Qed.

Lemma wbits_const : forall z, wbits z (bconst z).
Proof.
  intros z. split; [unfold bconst; rewrite length_map, length_seq; reflexivity|].
  intros i Hi. unfold bconst. rewrite nth_map_seq0 by exact Hi.
  destruct (Z.testbit z (Z.of_nat i)); reflexivity.
Qed.

Lemma wbits_mod64 : forall x l, wbits x l -> wbits (x mod 2 ^ 64) l.
Proof.
  intros x l [Hl H]. split; [exact Hl|]. intros i Hi. rewrite Z.mod_pow2_bits_low by lia. apply H. exact Hi.
Qed.

Lemma wbits_high : forall x l i, wbits x l -> 0 <= x < 2 ^ 64 -> 64 <= i -> Z.testbit x i = false.
Proof. intros. eapply tb_small_high'; [eassumption|lia]. Qed.

Lemma bval_byte_high : forall k i, 8 <= i -> Z.testbit (nu k) i = false.
Proof. intros. apply (tb_small_high' (nu k) 8 i); [apply Hnu|lia]. Qed.

Lemma wbits_byte_u : forall k x, x = nu k -> wbits x (bbyte false k).
Proof.
  intros k x ->. split; [reflexivity|]. intros i Hi. unfold bbyte.
  destruct (Nat.ltb_spec i 8).
  - rewrite app_nth1 by (rewrite length_map, length_seq; lia). rewrite nth_map_seq0 by lia. reflexivity.
  - rewrite app_nth2 by (rewrite length_map, length_seq; lia). rewrite length_map, length_seq.
    rewrite nth_repeat_lt by lia. cbn [bval]. apply bval_byte_high. lia.
Qed.

Lemma wbits_byte_s : forall k x, x = (bv_swrap 8 (nu k)) mod 2 ^ 64 -> wbits x (bbyte true k).
Proof.
  intros k x ->. split; [reflexivity|]. intros i Hi. unfold bbyte.
  change 8%N with (Z.to_N 8). rewrite swrap_bits by lia.
  destruct (Nat.ltb_spec i 8).
  - rewrite app_nth1 by (rewrite length_map, length_seq; lia). rewrite nth_map_seq0 by lia.
    destruct (Z.ltb_spec (Z.of_nat i) 8); [reflexivity|lia].
  - rewrite app_nth2 by (rewrite length_map, length_seq; lia). rewrite length_map, length_seq.
    rewrite nth_repeat_lt by lia. destruct (Z.ltb_spec (Z.of_nat i) 8); [lia|]. reflexivity.
Qed.

Lemma map2o_length : forall f l1 l2 l, map2o f l1 l2 = Some l -> length l = length l1 /\ length l2 = length l1.
Proof.
  induction l1 as [|x r1 IH]; intros [|y r2] l H; cbn in H; try discriminate.
  - injection H as <-. split; reflexivity.
  - destruct (f x y); [|discriminate]. destruct (map2o f r1 r2) eqn:Hm; [|discriminate].
    injection H as <-. destruct (IH _ _ Hm) as [A B]. cbn. split; lia.
Qed.

Lemma map2o_nth : forall f l1 l2 l i, map2o f l1 l2 = Some l -> (i < length l1)%nat ->
  f (nth i l1 BO) (nth i l2 BO) = Some (nth i l BO).
Proof.
  induction l1 as [|x r1 IH]; intros [|y r2] l i H Hi; cbn in H; try discriminate; cbn in Hi; [lia|].
  destruct (f x y) eqn:Hf; [|discriminate]. destruct (map2o f r1 r2) eqn:Hm; [|discriminate].
  injection H as <-. destruct i; [exact Hf|]. cbn. apply IH; [exact Hm|lia].
Qed.

Lemma wbits_and : forall x y lx ly l,
  wbits x lx -> wbits y ly -> map2o band1 lx ly = Some l -> wbits (Z.land x y) l.
Proof.
  intros x y lx ly l [Lx Hx] [Ly Hy] Hm.
  destruct (map2o_length _ _ _ _ Hm) as [L1 L2].
  split; [lia|]. intros i Hi. rewrite Z.land_spec, Hx, Hy by exact Hi.
  pose proof (map2o_nth band1 lx ly l i Hm ltac:(lia)) as E.
  destruct (nth i lx BO) as [| |k j], (nth i ly BO) as [| |k' j']; cbn in E |- *;
    try (injection E as <-; cbn; try reflexivity; try (rewrite andb_true_r; reflexivity); try (rewrite andb_false_r; reflexivity)).
  destruct (Nat.eqb k k' && Nat.eqb j j')%bool eqn:Hb; [|discriminate].
  injection E as <-. apply (bbit_eqb_eq (BV k j) (BV k' j')) in Hb. injection Hb as <- <-.
  cbn. apply andb_diag.
Qed.

Lemma wbits_or : forall x y lx ly l,
  wbits x lx -> wbits y ly -> map2o bor1 lx ly = Some l -> wbits (Z.lor x y) l.
Proof.
  intros x y lx ly l [Lx Hx] [Ly Hy] Hm.
  destruct (map2o_length _ _ _ _ Hm) as [L1 L2].
  split; [lia|]. intros i Hi. rewrite Z.lor_spec, Hx, Hy by exact Hi.
  pose proof (map2o_nth bor1 lx ly l i Hm ltac:(lia)) as E.
  destruct (nth i lx BO) as [| |k j], (nth i ly BO) as [| |k' j']; cbn in E |- *;
    try (injection E as <-; cbn; try reflexivity; try (rewrite orb_true_r; reflexivity); try (rewrite orb_false_r; reflexivity)).
  destruct (Nat.eqb k k' && Nat.eqb j j')%bool eqn:Hb; [|discriminate].
  injection E as <-. apply (bbit_eqb_eq (BV k j) (BV k' j')) in Hb. injection Hb as <- <-.
  cbn. apply orb_diag.
Qed.

Lemma wbits_add : forall x y lx ly l,
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  wbits x lx -> wbits y ly -> map2o badd1 lx ly = Some l -> wbits (x + y) l.
Proof.
  intros x y lx ly l Rx Ry Wx Wy Hm.
  destruct Wx as [Lx Hx]. destruct Wy as [Ly Hy].
  destruct (map2o_length _ _ _ _ Hm) as [L1 L2].
  assert (D : forall i, (i < 64)%nat -> bval nu (nth i lx BO) && bval nu (nth i ly BO) = false
                                      /\ bval nu (nth i l BO) = bval nu (nth i lx BO) || bval nu (nth i ly BO)).
  { intros i Hi. pose proof (map2o_nth badd1 lx ly l i Hm ltac:(lia)) as E.
    destruct (nth i lx BO) as [| |k j], (nth i ly BO) as [| |k' j']; cbn in E |- *; try discriminate;
      injection E as <-; cbn; rewrite ?andb_false_r, ?orb_false_r; split; reflexivity. }
  rewrite lor_disjoint_add; [| lia | lia |].
  - split; [lia|]. intros i Hi. rewrite Z.lor_spec, Hx, Hy by exact Hi. symmetry. apply (proj2 (D i Hi)).
  - intros n Hn. destruct (Z_lt_le_dec n 64).
    + rewrite <- (Z2Nat.id n) by lia. rewrite Hx, Hy by lia. apply (proj1 (D (Z.to_nat n) ltac:(lia))).
    + rewrite (tb_small_high' x 64 n) by lia. reflexivity.
Qed.

Lemma bshl_length : forall s l, length l = 64%nat -> length (bshl s l) = 64%nat.
Proof. intros s l H. unfold bshl. rewrite length_firstn, length_app, repeat_length, H. lia. Qed.

Lemma wbits_shl : forall x lx s, wbits x lx -> (s < 64)%nat -> wbits (Z.shiftl x (Z.of_nat s)) (bshl s lx).
Proof.
  intros x lx s [Lx Hx] Hs. split; [apply bshl_length; exact Lx|].
  intros i Hi. unfold bshl. rewrite nth_firstn. destruct (Nat.ltb_spec i 64); [|lia].
  destruct (Nat.ltb_spec i s).
  - rewrite Z.shiftl_spec_low by lia. rewrite app_nth1 by (rewrite repeat_length; lia).
    rewrite nth_repeat_lt by lia. reflexivity.
  - rewrite Z.shiftl_spec_high by lia. rewrite app_nth2 by (rewrite repeat_length; lia).
    rewrite repeat_length. replace (Z.of_nat i - Z.of_nat s) with (Z.of_nat (i - s)) by lia.
    apply Hx. lia.
Qed.

Lemma wbits_shr : forall x lx s, 0 <= x < 2 ^ 64 -> wbits x lx -> (s <= 64)%nat ->
  wbits (Z.shiftr x (Z.of_nat s)) (bshr s lx).
Proof.
  intros x lx s Rx [Lx Hx] Hs. split; [unfold bshr; rewrite length_app, length_skipn, repeat_length, Lx; lia|].
  intros i Hi. unfold bshr. rewrite Z.shiftr_spec by lia.
  destruct (Nat.ltb_spec i (64 - s)).
  - rewrite app_nth1 by (rewrite length_skipn, Lx; lia). rewrite nth_skipn.
    replace (Z.of_nat i + Z.of_nat s) with (Z.of_nat (s + i)) by lia. apply Hx. lia.
  - rewrite app_nth2 by (rewrite length_skipn, Lx; lia). rewrite length_skipn, Lx.
    rewrite nth_repeat_lt by lia. cbn. apply (tb_small_high' x 64); lia.
Qed.

Lemma wbits_sext : forall X lx w,
  length lx = 64%nat -> (forall i, (i < w)%nat -> Z.testbit X (Z.of_nat i) = bval nu (nth i lx BO)) ->
  (1 <= w <= 64)%nat ->
  wbits ((bv_swrap (N.of_nat w) X) mod 2 ^ 64) (bsext w lx).
Proof.
  intros X lx w Lx Hx Hw. split; [unfold bsext; rewrite length_app, length_firstn, repeat_length, Lx; lia|].
  intros i Hi. replace (N.of_nat w) with (Z.to_N (Z.of_nat w)) by lia.
  rewrite swrap_bits by lia. unfold bsext.
  destruct (Z.ltb_spec (Z.of_nat i) (Z.of_nat w)).
  - rewrite app_nth1 by (rewrite length_firstn, Lx; lia). rewrite nth_firstn.
    destruct (Nat.ltb_spec i w); [|lia]. apply Hx. lia.
  - rewrite app_nth2 by (rewrite length_firstn, Lx; lia). rewrite length_firstn, Lx.
    rewrite nth_repeat_lt by lia. replace (Z.of_nat w - 1) with (Z.of_nat (w - 1)) by lia. apply Hx. lia.
Qed.

Lemma wbits_zext : forall X lx w, wbits X lx -> (w <= 64)%nat ->
  wbits (X mod 2 ^ (Z.of_nat w)) (bzext w lx).
Proof.
  intros X lx w [Lx Hx] Hw. split; [unfold bzext; rewrite length_app, length_firstn, repeat_length, Lx; lia|].
  intros i Hi. rewrite Z.testbit_mod_pow2 by lia. unfold bzext.
  destruct (Z.ltb_spec (Z.of_nat i) (Z.of_nat w)).
  - rewrite app_nth1 by (rewrite length_firstn, Lx; lia). rewrite nth_firstn.
    destruct (Nat.ltb_spec i w); [|lia]. cbn [andb]. apply Hx. exact Hi.
  - rewrite app_nth2 by (rewrite length_firstn, Lx; lia). rewrite length_firstn, Lx.
    rewrite nth_repeat_lt by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint kval (kb : list bool) (s : nat) : Z :=
  match kb with [] => 0 | b :: rest => (if b then 2 ^ (Z.of_nat s) else 0) + kval rest (S s) end.

Lemma kval_nonneg : forall kb s, 0 <= kval kb s.
Proof. induction kb as [|b r IH]; intros s; cbn; [lia|]. specialize (IH (S s)). destruct b; [pose proof (Z.pow_nonneg 2 (Z.of_nat s)); lia | lia]. Qed.

Lemma wbits_bmul : forall x lx kb s l,
  0 <= x < 2 ^ 64 -> wbits x lx -> bmul kb s lx = Some l -> wbits ((kval kb s * x) mod 2 ^ 64) l.
Proof.
  intros x lx kb. induction kb as [|b rest IH]; intros s l Rx Wx Hm; cbn [bmul] in Hm.
  - replace l with (repeat BO 64) by congruence. cbn [kval]. rewrite Z.mul_0_l, Z.mod_0_l by lia.
    split; [apply repeat_length|]. intros i Hi. rewrite nth_repeat_lt by lia. apply Z.testbit_0_l.
  - destruct (bmul rest (S s) lx) as [r|] eqn:Hr; [|discriminate].
    pose proof (IH (S s) r Rx Wx Hr) as Wr.
    cbn [kval]. destruct b.
    + destruct (Nat.ltb_spec s 64).
      * rewrite Z.mul_add_distr_r, <- Zplus_mod_idemp_r, <- Zplus_mod_idemp_l.
        apply wbits_mod64.
        eapply wbits_add; [apply Z.mod_pos_bound; lia | apply Z.mod_pos_bound; lia | | exact Wr | exact Hm].
        apply wbits_mod64. rewrite Z.mul_comm, <- Z.shiftl_mul_pow2 by lia. apply wbits_shl; [exact Wx | lia].
      * (* [comment removed for export] *)
        assert (Hz : (2 ^ Z.of_nat s * x) mod 2 ^ 64 = 0).
        { replace (2 ^ Z.of_nat s) with (2 ^ 64 * 2 ^ (Z.of_nat s - 64)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
          rewrite <- Z.mul_assoc, Z.mul_comm. apply Z_mod_mult. }
        rewrite Z.mul_add_distr_r, <- Zplus_mod_idemp_l, Hz, Z.add_0_l.
        destruct (map2o_length _ _ _ _ Hm) as [L1 L2].
        destruct Wr as [Lr Hr']. split; [rewrite L1; apply bshl_length; apply (proj1 Wx)|].
        intros i Hi. rewrite Hr' by exact Hi.
        pose proof (map2o_nth badd1 _ _ _ i Hm ltac:(rewrite bshl_length by apply (proj1 Wx); lia)) as E.
        assert (Hb : nth i (bshl s lx) BO = BO).
        { unfold bshl. rewrite nth_firstn. destruct (Nat.ltb_spec i 64); [|lia].
          rewrite app_nth1 by (rewrite repeat_length; lia). apply nth_repeat_lt. lia. }
        rewrite Hb in E. cbn in E. injection E as ->. reflexivity.
    + rewrite Z.add_0_l. replace l with r by congruence. exact Wr.
Qed.

Lemma kval_zbits : forall k, 0 <= k < 2 ^ 64 -> kval (zbits k) 0 = k.
Proof.
  intros k Hk.
  assert (G : forall n s, kval (map (fun i => Z.testbit k (Z.of_nat i)) (seq s n)) s
                        = (k mod 2 ^ (Z.of_nat (s + n))) - (k mod 2 ^ (Z.of_nat s))).
  { induction n as [|n IH]; intros s; cbn [seq map kval].
    - rewrite Nat.add_0_r. lia.
    - rewrite IH. replace (S s + n)%nat with (s + S n)%nat by lia.
      pose proof (Z.testbit_spec' k (Z.of_nat s) ltac:(lia)) as B.
      assert (P0 : 0 < 2 ^ Z.of_nat s) by (apply Z.pow_pos_nonneg; lia).
      assert (M1 : k mod 2 ^ Z.of_nat (S s) = k mod 2 ^ Z.of_nat s + 2 ^ Z.of_nat s * ((k / 2 ^ Z.of_nat s) mod 2)).
      { rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. rewrite (Z.mul_comm 2).
        rewrite Z.rem_mul_r by lia. lia. }
      destruct (Z.testbit k (Z.of_nat s)); cbn [Z.b2z] in B; rewrite M1, <- B; lia. }
  unfold zbits. rewrite G. change (Z.of_nat (0 + 64)) with 64. change (Z.of_nat 0) with 0.
  rewrite Z.pow_0_r, Z.mod_1_r, Z.mod_small by lia. lia.
Qed.

End Sound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Denot.
Variable E : env.
Variable nu : nat -> Z.
Hypothesis Hnu : forall k, 0 <= nu k < 256.

Definition atom_ok (a : expr * (bool * nat)) : Prop :=
  let '(e, (sx, k)) := a in
  bv_unsigned (edenot E e) = if sx then (bv_swrap 8 (nu k)) mod 2 ^ 64 else nu k.

Definition atoms_ok (atoms : list (expr * (bool * nat))) : Prop := Forall atom_ok atoms.

Lemma find_atom_sound : forall atoms e sx k,
  atoms_ok atoms -> find_atom atoms e = Some (sx, k) ->
  bv_unsigned (edenot E e) = if sx then (bv_swrap 8 (nu k)) mod 2 ^ 64 else nu k.
Proof.
  induction atoms as [|[a [sx' k']] rest IH]; intros e sx k Hok Hf; cbn in Hf; [discriminate|].
  apply Forall_cons_iff in Hok as [H1 H2].
  destruct (expr_eqb e a) eqn:He.
  - injection Hf as <- <-. apply expr_eqb_eq in He. subst a. exact H1.
  - apply (IH e sx k H2 Hf).
Qed.

Lemma u_Z_to_bv : forall z, bv_unsigned (Z_to_bv 64 z) = z mod 2 ^ 64.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap64_mod. Qed.

Lemma u_lit_small : forall s, 0 <= s < 64 -> bv_unsigned (Z_to_bv 64 s) = s.
Proof. intros. rewrite u_Z_to_bv. apply Z.mod_small. lia. Qed.

Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core3 else first [ solve [clear; el_lia_core3] | el_lia_core3 ].   (* [comment removed for export] *)
Theorem beval_sound : forall atoms e l,
  atoms_ok atoms -> beval atoms e = Some l -> wbits nu (bv_unsigned (edenot E e)) l.
Proof.
  intros atoms e. induction e; intros l Hok Hb; cbn [beval] in Hb;
  lazymatch goal with
  | Hb : match find_atom ?atoms ?e with _ => _ end = Some _ |- _ =>
      destruct (find_atom atoms e) as [[sx0 k0]|] eqn:Hf;
      [ injection Hb as <-; pose proof (find_atom_sound atoms e sx0 k0 Hok Hf) as V;
        destruct sx0; [apply (wbits_byte_s nu); exact V | apply (wbits_byte_u nu Hnu); exact V] | ]
  end; try discriminate.
  - (* [comment removed for export] *) injection Hb as <-. cbn [edenot]. rewrite u_Z_to_bv. apply wbits_const.
  - (* [comment removed for export] *)
    pose proof (u64_range (edenot E e1)) as R1. pose proof (u64_range (edenot E e2)) as R2.
    destruct op; try discriminate; cbn [edenot].
    + (* [comment removed for export] *) destruct (beval atoms e1) as [la|] eqn:Ha; [|discriminate]. destruct (beval atoms e2) as [lb|] eqn:Hb2; [|discriminate]. cbn [obind] in Hb.
      rewrite alu_add. unfold v_add. rewrite u_Z_to_bv. apply wbits_mod64.
      eapply wbits_add; try exact Hnu; [exact R1 | exact R2 | apply IHe1; auto | apply IHe2; auto | exact Hb].
    + (* [comment removed for export] *) destruct e2; try discriminate. destruct (andb (0 <=? z) (z <? 64)) eqn:Hz; [|discriminate].
      apply andb_prop in Hz as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2.
      destruct (beval atoms e1) as [la|] eqn:Ha; [|discriminate]. cbn [obind] in Hb. injection Hb as <-.
      rewrite alu_sll. unfold v_sll. cbn [edenot]. rewrite (u_lit_small z) by lia. rewrite (Z.mod_small z 64) by lia.
      rewrite u_Z_to_bv. apply wbits_mod64. rewrite <- (Z2Nat.id z) at 1 by lia. apply wbits_shl; [apply IHe1; auto | lia].
    + (* [comment removed for export] *) destruct e2; try discriminate. destruct (andb (0 <=? z) (z <? 64)) eqn:Hz; [|discriminate].
      apply andb_prop in Hz as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2.
      destruct (beval atoms e1) as [la|] eqn:Ha; [|discriminate]. cbn [obind] in Hb. injection Hb as <-.
      rewrite alu_srl. unfold v_srl. cbn [edenot]. rewrite (u_lit_small z) by lia. rewrite (Z.mod_small z 64) by lia.
      rewrite u_Z_to_bv. apply wbits_mod64. rewrite <- (Z2Nat.id z) at 1 by lia. apply wbits_shr; try exact Hnu; [exact R1 | apply IHe1; auto | lia].
    + (* [comment removed for export] *) destruct (beval atoms e1) as [la|] eqn:Ha; [|discriminate]. destruct (beval atoms e2) as [lb|] eqn:Hb2; [|discriminate]. cbn [obind] in Hb.
      rewrite alu_or. unfold v_or. rewrite u_Z_to_bv. apply wbits_mod64.
      eapply wbits_or; try exact Hnu; [apply IHe1; auto | apply IHe2; auto | exact Hb].
    + (* [comment removed for export] *) destruct (beval atoms e1) as [la|] eqn:Ha; [|discriminate]. destruct (beval atoms e2) as [lb|] eqn:Hb2; [|discriminate]. cbn [obind] in Hb.
      rewrite alu_and. unfold v_and. rewrite u_Z_to_bv. apply wbits_mod64.
      eapply wbits_and; try exact Hnu; [apply IHe1; auto | apply IHe2; auto | exact Hb].
  - (* [comment removed for export] *)
    destruct op; try discriminate. destruct e2; try discriminate.
    destruct (andb (0 <=? z) (z <? 32)) eqn:Hz; [|discriminate].
    apply andb_prop in Hz as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2.
    destruct (beval atoms e1) as [la|] eqn:Ha; [|discriminate]. cbn [obind] in Hb. injection Hb as <-.
    cbn [edenot]. rewrite w_sllw. unfold v_sllw. rewrite (u_lit_small z) by lia. rewrite (Z.mod_small z 32) by lia.
    rewrite u_Z_to_bv. change 32%N with (N.of_nat 32).
    assert (Wl : wbits nu (Z.shiftl (bv_unsigned (edenot E e1)) z) (bshl (Z.to_nat z) la)).
    { rewrite <- (Z2Nat.id z) at 1 by lia. apply wbits_shl; [apply IHe1; auto | lia]. }
    destruct Wl as [Ll Hl]. apply wbits_sext; try exact Hnu; [exact Ll | intros; apply Hl; lia | lia].
  - (* [comment removed for export] *)
    destruct op; try discriminate. destruct e1; try discriminate.
    destruct (beval atoms e2) as [la|] eqn:Ha; [|discriminate]. cbn [obind] in Hb.
    cbn [edenot]. rewrite m_mul. unfold v_mul. rewrite !u_Z_to_bv.
    rewrite <- (kval_zbits (z mod 2 ^ 64)) at 1 by (apply Z.mod_pos_bound; lia).
    eapply wbits_bmul; try exact Hnu; [apply u64_range | apply IHe2; auto | exact Hb].
  - (* [comment removed for export] *)
    destruct (andb (1 <=? n)%nat (lo + n <=? 8)%nat) eqn:Hn; [|discriminate].
    apply andb_prop in Hn as [N1 N2]. apply Nat.leb_le in N1. apply Nat.leb_le in N2.
    destruct (beval atoms e) as [la|] eqn:Ha; [|discriminate]. cbn [obind] in Hb. injection Hb as <-.
    cbn [edenot]. unfold ext_val, ext_Z. rewrite u_Z_to_bv.
    pose proof (IHe la Hok eq_refl) as W. pose proof (u64_range (edenot E e)) as R.
    assert (Ws : wbits nu (bv_unsigned (edenot E e) / 2 ^ (8 * Z.of_nat lo)) (bshr (8 * lo) la)).
    { rewrite <- Z.shiftr_div_pow2 by lia. replace (8 * Z.of_nat lo) with (Z.of_nat (8 * lo)) by lia.
      apply wbits_shr; try exact Hnu; [exact R | exact W | lia]. }
    destruct sx.
    + replace (8 * N.of_nat n)%N with (N.of_nat (8 * n)) by lia.
      destruct Ws as [Ls Hs].
      apply wbits_sext; try exact Hnu; [exact Ls | | lia].
      intros i Hi. rewrite Z.mod_pow2_bits_low by lia. apply Hs. lia.
    + rewrite Z.mod_small.
      2:{ pose proof (Z.mod_pos_bound (bv_unsigned (edenot E e) / 2 ^ (8 * Z.of_nat lo)) (2 ^ (8 * Z.of_nat n)) ltac:(lia)).
          assert (2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). lia. }
      replace (8 * Z.of_nat n) with (Z.of_nat (8 * n)) by lia. apply wbits_zext; [exact Ws | lia].
Qed.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

(* [comment removed for export] *)
Lemma wbits_bytes_val : forall ks x,
  (length ks <= 8)%nat -> 0 <= x < 2 ^ 64 -> wbits nu x (bytes_bits ks) -> x = bytes_val nu ks.
Proof.
  induction ks as [|k r IH]; intros x Hlen Rx [L W].
  - cbn [bytes_val]. apply Z.bits_inj_0. intros n.
    destruct (Z_lt_le_dec n 0); [apply Z.testbit_neg_r; lia|].
    destruct (Z_lt_le_dec n 64); [| apply (tb_small_high' x 64 n); lia].
    rewrite <- (Z2Nat.id n) by lia. rewrite W by lia. unfold bytes_bits. cbn [flat_map length Nat.mul Nat.sub app].
    rewrite nth_repeat_lt by lia. reflexivity.
  - cbn [bytes_val]. cbn [length] in Hlen.
    assert (Hlo : x mod 2 ^ 8 = nu k).
    { apply Z.bits_inj'. intros n Hn. rewrite Z.testbit_mod_pow2 by lia.
      destruct (Z.ltb_spec n 8).
      - cbn [andb]. rewrite <- (Z2Nat.id n) by lia. rewrite W by lia. unfold bytes_bits. cbn [flat_map].
        rewrite <- app_assoc, app_nth1 by (rewrite length_map, length_seq; lia).
        rewrite (nth_map_seq0 (fun j => BV k j)) by lia. reflexivity.
      - cbn [andb]. symmetry. apply (tb_small_high' (nu k) 8 n); [apply Hnu | lia]. }
    assert (Hhi : x / 2 ^ 8 = bytes_val nu r).
    { apply IH; [lia | split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia|]; assert (2^64 <= 2^8 * 2^64) by lia; lia] |].
      split.
      - unfold bytes_bits in L |- *. cbn [flat_map length] in L. rewrite length_app, length_app, length_map, length_seq, repeat_length in L.
        rewrite length_app, repeat_length. lia.
      - intros i Hi. rewrite Z.div_pow2_bits by lia.
        destruct (Nat.ltb_spec i 56).
        + replace (Z.of_nat i + 8) with (Z.of_nat (8 + i)) by lia. rewrite W by lia.
          unfold bytes_bits. cbn [flat_map]. rewrite <- app_assoc.
          rewrite app_nth2 by (rewrite length_map, length_seq; lia). rewrite length_map, length_seq.
          replace (8 + i - 8)%nat with i by lia.
          (* [comment removed for export] *)
          destruct (Nat.ltb_spec i (8 * length r)).
          * rewrite !app_nth1 by (rewrite (flat_map_constant_length (c := 8)) by (intros; rewrite length_map, length_seq; reflexivity); lia). reflexivity.
          * rewrite !app_nth2 by (rewrite (flat_map_constant_length (c := 8)) by (intros; rewrite length_map, length_seq; reflexivity); lia).
            rewrite (flat_map_constant_length (c := 8)) by (intros; rewrite length_map, length_seq; reflexivity).
            cbn [length]. rewrite !nth_repeat_lt by lia. reflexivity.
        + rewrite (tb_small_high' x 64); [|lia|lia].
          unfold bytes_bits. rewrite app_nth2 by (rewrite (flat_map_constant_length (c := 8)) by (intros; rewrite length_map, length_seq; reflexivity); lia).
          rewrite (flat_map_constant_length (c := 8)) by (intros; rewrite length_map, length_seq; reflexivity).
          rewrite nth_repeat_lt by lia. reflexivity. }
    rewrite <- Hlo, <- Hhi. pose proof (Z_div_mod_eq_full x (2 ^ 8)). change (2 ^ 8)%Z with 256%Z in *. lia.
Qed.

(* [comment removed for export] *)
Theorem beval_bytes : forall atoms e ks,
  atoms_ok atoms ->
  (length ks <= 8)%nat ->
  match beval atoms e with Some l => list_bbit_eqb l (bytes_bits ks) | None => false end = true ->
  bv_unsigned (edenot E e) = bytes_val nu ks.
Proof.
  intros atoms e ks Hok Hlen H.
  destruct (beval atoms e) as [l|] eqn:Hb; [|discriminate].
  apply list_bbit_eqb_eq in H. subst l.
  apply wbits_bytes_val; [exact Hlen | apply u64_range | eapply beval_sound; eassumption].
Qed.

(* [comment removed for export] *)
Theorem beval_same : forall atoms e1 e2,
  atoms_ok atoms ->
  match beval atoms e1, beval atoms e2 with Some l1, Some l2 => list_bbit_eqb l1 l2 | _, _ => false end = true ->
  edenot E e1 = edenot E e2.
Proof.
  intros atoms e1 e2 Hok H.
  destruct (beval atoms e1) as [l1|] eqn:H1; [|discriminate].
  destruct (beval atoms e2) as [l2|] eqn:H2; [|discriminate].
  apply list_bbit_eqb_eq in H. subst l2.
  pose proof (beval_sound atoms e1 l1 Hok H1) as [L1 W1].
  pose proof (beval_sound atoms e2 l1 Hok H2) as [L2 W2].
  apply bv_eq. apply Z.bits_inj'. intros n Hn.
  destruct (Z_lt_le_dec n 64).
  - rewrite <- (Z2Nat.id n) by lia. rewrite W1, W2 by lia. reflexivity.
  - rewrite !(tb_small_high' _ 64 n) by (try apply u64_range; lia). reflexivity.
Qed.

End Denot.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma blob_bytes_1 : forall bs i, 0 <= i -> i < Z.of_nat (length bs) ->
  blob_bytes bs i 1 = [nth (Z.to_nat i) bs (Z_to_bv 8 0)].
Proof.
  intros bs i Hi Hl. unfold blob_bytes.
  remember (skipn (Z.to_nat i) bs) as t eqn:Ht.
  destruct t as [|b r].
  - exfalso. assert (L : length (skipn (Z.to_nat i) bs) = 0%nat) by (rewrite <- Ht; reflexivity).
    rewrite length_skipn in L. lia.
  - cbn. f_equal. rewrite <- (Nat.add_0_r (Z.to_nat i)), <- nth_skipn, <- Ht. reflexivity.
Qed.

Lemma blob_val_u8 : forall bs i, 0 <= i -> i < Z.of_nat (length bs) ->
  bv_unsigned (blob_val false bs i 1) = bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
Proof.
  intros bs i Hi Hl. unfold blob_val. rewrite blob_bytes_1 by assumption. rewrite bytes_le_single.
  pose proof (bv_unsigned_in_range _ (nth (Z.to_nat i) bs (Z_to_bv 8 0))) as R. unfold bv_modulus in R.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod. apply Z.mod_small. cbn in R. lia.
Qed.

Lemma blob_val_s8 : forall bs i, 0 <= i -> i < Z.of_nat (length bs) ->
  bv_unsigned (blob_val true bs i 1) = (bv_swrap 8 (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) mod 2 ^ 64.
Proof.
  intros bs i Hi Hl. unfold blob_val. rewrite blob_bytes_1 by assumption. rewrite bytes_le_single.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod. reflexivity.
Qed.

Lemma byte_range : forall (b : byte), 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range _ b) as R. unfold bv_modulus in R. cbn in R. lia. Qed.
