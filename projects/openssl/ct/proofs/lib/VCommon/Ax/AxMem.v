(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec FastWord FastWordSem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie ExBytes.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require ExLoad.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxBytes AxImg AxEntryRel.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive cell : Type :=
| CW (w : w64)
| CB (l : list xb).

Definition cbyte (c : cell) (i : nat) : xb :=
  match c with
  | CW w => BL (w_byte w i)
  | CB l => nth i l BT
  end.

Inductive rkind : Type :=
| KZero                        (* [comment removed for export] *)
| KShadow                      (* [comment removed for export] *)
| KUnk                         (* [comment removed for export] *)
| KImg (w : bool) (i : nat)    (* [comment removed for export] *)
| KEntry (ph : PhdrInfo).      (* [comment removed for export] *)

Record region : Type := Rg {
  rg_ts : terms;              (* [comment removed for export] *)
  rg_bo : w64;
  rg_n : int;                 (* [comment removed for export] *)
  rg_kind : rkind;
  rg_d : nat;                 (* [comment removed for export] *)
  rg_cells : itrie cell
}.

Definition with_cells (R : region) (t : itrie cell) : region :=
  Rg (rg_ts R) (rg_bo R) (rg_n R) (rg_kind R) (rg_d R) t.

Definition rk_writable (k : rkind) : bool :=
  match k with KZero | KShadow | KUnk => true | KImg w _ => w | KEntry _ => false end.

Definition is_entry (R : region) : bool := match rg_kind R with KEntry _ => true | _ => false end.

Definition rbase (ρ : valuation) (R : region) : Z := smod ρ (rg_ts R) (rg_bo R).

(* [comment removed for export] *)
Definition same_fields (R R' : region) : Prop :=
  rg_ts R' = rg_ts R /\ rg_bo R' = rg_bo R /\ rg_n R' = rg_n R /\ rg_kind R' = rg_kind R /\ rg_d R' = rg_d R.

(* [comment removed for export] *)
Definition i2n (i : int) : nat :=
  if (i =? 0)%uint63 then 0%nat else if (i =? 1)%uint63 then 1%nat else if (i =? 2)%uint63 then 2%nat
  else if (i =? 3)%uint63 then 3%nat else if (i =? 4)%uint63 then 4%nat else if (i =? 5)%uint63 then 5%nat
  else if (i =? 6)%uint63 then 6%nat else 7%nat.

Definition wz (a : Z) : word := Z_to_bv 64 a.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition default_byte (k : rkind) (x : int) : xb :=
  match k with
  | KZero | KShadow => BL 0%uint63
  | KUnk => BT
  | KImg _ i => match fimg_i segs i x with Some b => BL b | None => BT end
  | KEntry _ => BT
  end.

Definition get_cell_opt (R : region) (k : int) : option cell := iget (rg_d R) (rg_cells R) k.

(* [comment removed for export] *)
Definition rbyte (R : region) (x : int) : xb :=
  match get_cell_opt R (x >> 3)%uint63 with
  | Some c => cbyte c (i2n (x land 7)%uint63)
  | None => default_byte (rg_kind R) x
  end.

(* [comment removed for export] *)
Definition rv (m : word -> option byte) (a : word) : option byte :=
  match m a with Some b => Some b | None => seg_rom segs a end.

(* [comment removed for export] *)
Definition region_wf (ρ : valuation) (R : region) : Prop :=
  rbase ρ R + to_Z (rg_n R) <= two64
  /\ to_Z (rg_n R) < 2 ^ 47
  /\ to_Z (rg_n R) <= 8 * 2 ^ Z.of_nat (rg_d R)
  /\ (rg_d R <= 44)%nat
  /\ (forall w i, rg_kind R = KImg w i -> rg_ts R = []).

Definition rdisj (ρ : valuation) (R1 R2 : region) : Prop :=
  rbase ρ R1 + to_Z (rg_n R1) <= rbase ρ R2 \/ rbase ρ R2 + to_Z (rg_n R2) <= rbase ρ R1.

Fixpoint regions_ok (ρ : valuation) (A : list region) : Prop :=
  match A with
  | [] => True
  | R :: A' => region_wf ρ R /\ Forall (rdisj ρ R) A' /\ regions_ok ρ A'
  end.

(* [comment removed for export] *)
Definition RRegion0 (ρ : valuation) (m : word -> option byte) (R : region) : Prop :=
  forall y : int, to_Z y < to_Z (rg_n R) ->
    (exists b, rv m (wz (rbase ρ R + to_Z y)) = Some b /\ xb_bv ρ (rbyte R y) b)
    /\ (rk_writable (rg_kind R) = true -> wview segs m (wz (rbase ρ R + to_Z y)) <> None).

Definition RRegion (ρ : valuation) (m : word -> option byte) (R : region) : Prop :=
  match rg_kind R with
  | KEntry ph => eb_rel ph ρ m (rbase ρ R) (to_Z (rg_n R))
  | _ => RRegion0 ρ m R
  end.

Definition RMem (ρ : valuation) (A : list region) (m : word -> option byte) : Prop :=
  regions_ok ρ A /\ Forall (RRegion ρ m) A.

Lemma RRegion_ne (ρ : valuation) (m : word -> option byte) (R : region) :
  is_entry R = false -> RRegion ρ m R = RRegion0 ρ m R.
Proof. unfold is_entry, RRegion. destruct (rg_kind R); first [reflexivity | discriminate]. Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma phi_add_small (x y : int) : to_Z x + to_Z y < 2 ^ 63 -> to_Z (x + y)%uint63 = to_Z x + to_Z y.
Proof. intros H. rewrite add_spec. apply Z.mod_small. pose proof (to_Z_bounded x). pose proof (to_Z_bounded y). change wB with (2^63). lia. Qed.

Lemma phi_sub_small (x y : int) : to_Z y <= to_Z x -> to_Z (x - y)%uint63 = to_Z x - to_Z y.
Proof. intros H. rewrite sub_spec. apply Z.mod_small. pose proof (to_Z_bounded x). pose proof (to_Z_bounded y). change wB with (2^63) in *. lia. Qed.

Lemma phi_of_nat_small (n : nat) : (n < 1000)%nat -> to_Z (of_Z (Z.of_nat n)) = Z.of_nat n.
Proof. intros H. rewrite of_Z_spec. apply Z.mod_small. change wB with (2^63). lia. Qed.

Lemma phi_of_Z_small (z : Z) : 0 <= z < 2 ^ 63 -> to_Z (of_Z z) = z.
Proof. intros H. rewrite of_Z_spec. apply Z.mod_small. change wB with (2^63). exact H. Qed.

Lemma int_add_1 (x : int) : to_Z x + 1 < 2 ^ 63 -> to_Z (x + 1)%uint63 = to_Z x + 1.
Proof. intros H. pose proof (to_Z_bounded x). change wB with (2^63) in *. rewrite phi_add_small; change (to_Z 1%uint63) with 1; lia. Qed.

Lemma phi_land7 (x : int) : to_Z (x land 7)%uint63 = to_Z x mod 8.
Proof. rewrite land_spec'. change (to_Z 7%uint63) with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma phi_lsr3 (x : int) : to_Z (x >> 3)%uint63 = to_Z x / 8.
Proof. rewrite lsr_spec. reflexivity. Qed.

Lemma i2n_spec (i : int) : to_Z i < 8 -> i2n i = Z.to_nat (to_Z i).
Proof.
  intros H. pose proof (to_Z_bounded i) as Hb.
  assert (E : to_Z i = 0 \/ to_Z i = 1 \/ to_Z i = 2 \/ to_Z i = 3 \/ to_Z i = 4 \/ to_Z i = 5 \/ to_Z i = 6 \/ to_Z i = 7) by lia.
  destruct E as [E|[E|[E|[E|[E|[E|[E|E]]]]]]];
    [ replace i with 0%uint63 by (apply to_Z_inj; rewrite E; reflexivity)
    | replace i with 1%uint63 by (apply to_Z_inj; rewrite E; reflexivity)
    | replace i with 2%uint63 by (apply to_Z_inj; rewrite E; reflexivity)
    | replace i with 3%uint63 by (apply to_Z_inj; rewrite E; reflexivity)
    | replace i with 4%uint63 by (apply to_Z_inj; rewrite E; reflexivity)
    | replace i with 5%uint63 by (apply to_Z_inj; rewrite E; reflexivity)
    | replace i with 6%uint63 by (apply to_Z_inj; rewrite E; reflexivity)
    | replace i with 7%uint63 by (apply to_Z_inj; rewrite E; reflexivity) ]; reflexivity.
Qed.

Lemma i2n_land7 (x : int) : i2n (x land 7)%uint63 = Z.to_nat (to_Z (x land 7)%uint63).
Proof. apply i2n_spec. rewrite phi_land7. pose proof (Z.mod_pos_bound (to_Z x) 8 ltac:(lia)). lia. Qed.

Lemma i2n_lt8 (x : int) : (i2n (x land 7)%uint63 < 8)%nat.
Proof. rewrite i2n_land7, phi_land7. pose proof (Z.mod_pos_bound (to_Z x) 8 ltac:(lia)). lia. Qed.

Lemma key_small (R : region) (x : int) :
  to_Z (rg_n R) <= 8 * 2 ^ Z.of_nat (rg_d R) -> to_Z x < to_Z (rg_n R) -> to_Z (x >> 3)%uint63 < 2 ^ Z.of_nat (rg_d R).
Proof. intros Hn Hx. rewrite phi_lsr3. apply Z.div_lt_upper_bound; lia. Qed.

Lemma wz_succ (a : Z) : (wz a + 1)%bv = wz (a + 1).
Proof.
  unfold wz. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. change (bv_unsigned (1 : bv 64)) with 1.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma u_wz (a : Z) : 0 <= a < 2 ^ 64 -> bv_unsigned (wz a) = a.
Proof. intros H. unfold wz. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. exact H. Qed.

Lemma Forall_nth {X : Type} (P : X -> Prop) (l : list X) (i : nat) (x : X) : Forall P l -> nth_error l i = Some x -> P x.
Proof. intros H Hi. rewrite Forall_forall in H. apply H. exact (nth_error_In l i Hi). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma regions_ok_nth (ρ : valuation) (A : list region) (i : nat) (R : region) :
  regions_ok ρ A -> nth_error A i = Some R -> region_wf ρ R.
Proof.
  revert i. induction A as [|R0 A IH]; intros i Hok Hi; [destruct i; discriminate|].
  destruct Hok as [Hw [_ Hok]]. destruct i as [|i]; cbn [nth_error] in Hi; [injection Hi as <-; exact Hw | exact (IH i Hok Hi)].
Qed.

Lemma regions_ok_in (ρ : valuation) (A : list region) (R : region) : regions_ok ρ A -> In R A -> region_wf ρ R.
Proof. intros Hok HIn. destruct (In_nth_error A R HIn) as [i Hi]. exact (regions_ok_nth ρ A i R Hok Hi). Qed.

Lemma rdisj_sym (ρ : valuation) (R1 R2 : region) : rdisj ρ R1 R2 -> rdisj ρ R2 R1.
Proof. unfold rdisj. tauto. Qed.

Lemma regions_ok_disj (ρ : valuation) (A : list region) (i j : nat) (Ri Rj : region) :
  regions_ok ρ A -> nth_error A i = Some Ri -> nth_error A j = Some Rj -> i <> j -> rdisj ρ Ri Rj.
Proof.
  revert i j. induction A as [|R0 A IH]; intros i j Hok Hi Hj Hne; [destruct i; discriminate|].
  destruct Hok as [_ [Hd Hok]]. rewrite Forall_forall in Hd.
  destruct i as [|i], j as [|j]; cbn [nth_error] in *; try lia.
  - injection Hi as <-. apply Hd. exact (nth_error_In A j Hj).
  - injection Hj as <-. apply rdisj_sym. apply Hd. exact (nth_error_In A i Hi).
  - apply (IH i j Hok Hi Hj). lia.
Qed.

Fixpoint replace_nth (A : list region) (i : nat) (R' : region) : list region :=
  match A, i with
  | [], _ => []
  | _ :: A', O => R' :: A'
  | R0 :: A', S i' => R0 :: replace_nth A' i' R'
  end.

Lemma replace_nth_length (A : list region) (i : nat) (R' : region) : length (replace_nth A i R') = length A.
Proof. revert i; induction A as [|R0 A IH]; intros [|i]; cbn [replace_nth length]; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma Forall_replace_nth' (P : region -> Prop) (A : list region) (i : nat) (R' : region) :
  (forall j Rj, nth_error A j = Some Rj -> j <> i -> P Rj) -> P R' -> (i < length A)%nat -> Forall P (replace_nth A i R').
Proof.
  revert i. induction A as [|R0 A IH]; intros i H HP Hi; [destruct i; constructor|].
  destruct i as [|i]; cbn [replace_nth]; constructor.
  - exact HP.
  - apply Forall_forall. intros x Hx. apply In_nth_error in Hx as [j Hj]. apply (H (S j) x Hj). lia.
  - apply (H 0%nat R0 eq_refl). lia.
  - apply IH; [|exact HP | cbn [length] in Hi; lia]. intros j Rj Hj Hne. apply (H (S j) Rj Hj). lia.
Qed.

Lemma Forall2_replace_nth (P : region -> region -> Prop) (A : list region) (i : nat) (R R' : region) :
  (forall X, P X X) -> nth_error A i = Some R -> P R R' -> Forall2 P A (replace_nth A i R').
Proof.
  intros Hrefl. revert i. induction A as [|R0 A IH]; intros i Hi HP; [destruct i; discriminate|].
  destruct i as [|i]; cbn [nth_error replace_nth] in *.
  - injection Hi as <-. constructor; [exact HP|]. clear -Hrefl. induction A as [|X A IHA]; constructor; [apply Hrefl | exact IHA].
  - constructor; [apply Hrefl | exact (IH i Hi HP)].
Qed.

(* [comment removed for export] *)
Lemma regions_ok_replace (ρ : valuation) (A : list region) (i : nat) (R R' : region) :
  regions_ok ρ A -> nth_error A i = Some R -> rbase ρ R' = rbase ρ R -> rg_n R' = rg_n R ->
  (region_wf ρ R -> region_wf ρ R') -> regions_ok ρ (replace_nth A i R').
Proof.
  revert i. induction A as [|R0 A IH]; intros i Hok Hi Hb Hn Hw; [destruct i; discriminate|].
  destruct i as [|i]; cbn [nth_error replace_nth regions_ok] in *.
  - injection Hi as <-. destruct Hok as [Hw0 [Hd Hok]]. split; [exact (Hw Hw0)|]. split; [|exact Hok].
    rewrite Forall_forall in *. intros R2 HR2. specialize (Hd R2 HR2). unfold rdisj in *. rewrite Hb, Hn. exact Hd.
  - destruct Hok as [Hw0 [Hd Hok]]. split; [exact Hw0|]. split; [|exact (IH i Hok Hi Hb Hn Hw)].
    clear IH Hok. revert i Hi. induction A as [|R2 A IH2]; intros i Hi; [destruct i; discriminate|].
    inversion Hd as [|? ? HR2 Hd']; subst. destruct i as [|i]; cbn [nth_error replace_nth] in *.
    + injection Hi as <-. constructor; [unfold rdisj in *; rewrite Hb, Hn; exact HR2 | exact Hd'].
    + constructor; [exact HR2 | exact (IH2 Hd' i Hi)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition xaddr (v : xv) : option (terms * w64) :=
  match v with
  | XL x => Some ([], x)
  | XS ts o => Some (ts, o)
  | _ => None
  end.

(* [comment removed for export] *)
Definition roff (R : region) (ts : terms) (o : w64) (n : int) : option int :=
  match rg_kind R with
  | KEntry _ => None
  | _ =>
      (* [comment removed for export] *)
      if teqb (rg_ts R) ts then
        let d := w_sub o (rg_bo R) in
        if wh d then None else
        if (wl d <? rg_n R)%uint63 &&& (n <=? rg_n R - wl d)%uint63 then Some (wl d) else None
      else None
  end.

Fixpoint find_reg (A : list region) (ts : terms) (o : w64) (n : int) (j : nat) : option (nat * region * int) :=
  match A with
  | [] => None
  | R :: A' => match roff R ts o n with
               | Some x => Some (j, R, x)
               | None => find_reg A' ts o n (S j)
               end
  end.

Lemma roff_spec (R : region) (ts : terms) (o : w64) (n x : int) :
  0 < to_Z n -> roff R ts o n = Some x ->
  is_entry R = false /\ rg_ts R = ts /\ wZ o = (wZ (rg_bo R) + to_Z x) mod two64 /\ to_Z x + to_Z n <= to_Z (rg_n R).
Proof.
  intros Hn H. unfold roff in H.
  assert (He : is_entry R = false /\
    (if teqb (rg_ts R) ts then
       let d := w_sub o (rg_bo R) in if wh d then None else
       if (wl d <? rg_n R)%uint63 &&& (n <=? rg_n R - wl d)%uint63 then Some (wl d) else None
     else None) = Some x).
  { unfold is_entry. destruct (rg_kind R); try discriminate; split; first [reflexivity | exact H]. }
  clear H. destruct He as [He H]. split; [exact He|].
  destruct (teqb (rg_ts R) ts) eqn:Et; [|discriminate]. cbv zeta in H.
  pose proof (wZ_sub o (rg_bo R)) as Ed0. remember (w_sub o (rg_bo R)) as d eqn:Edd. clear Edd.
  destruct (wh d) eqn:Eh; [discriminate|].
  destruct (ltbP (wl d) (rg_n R)) as [H1|H1]; [|discriminate].
  destruct (lebP n (rg_n R - wl d)) as [H2|H2]; [|discriminate]. injection H as <-.
  apply teqb_eq in Et. split; [exact Et|].
  rewrite (phi_sub_small (rg_n R) (wl d)) in H2 by lia.
  assert (Ed : wZ d = to_Z (wl d)) by (unfold wZ; rewrite Eh; lia).
  rewrite Ed0 in Ed. split; [|lia]. rewrite <- Ed.
  rewrite Zplus_mod_idemp_r. replace (wZ (rg_bo R) + (wZ o - wZ (rg_bo R))) with (wZ o) by ring.
  symmetry. apply Z.mod_small. apply wZ_range.
Qed.

Lemma roff_ne (R : region) (ts : terms) (o : w64) (n x : int) : roff R ts o n = Some x -> is_entry R = false.
Proof. unfold roff, is_entry. destruct (rg_kind R); first [reflexivity | discriminate]. Qed.

(* [comment removed for export] *)
Lemma roff_addr (ρ : valuation) (R : region) (ts : terms) (o : w64) (n x : int) (a : bv 64) :
  0 < to_Z n -> region_wf ρ R -> bv_unsigned a = smod ρ ts o -> roff R ts o n = Some x ->
  bv_unsigned a = rbase ρ R + to_Z x /\ to_Z x + to_Z n <= to_Z (rg_n R).
Proof.
  intros Hn Hwf Ha H. destruct (roff_spec R ts o n x Hn H) as [_ [Et [Eo Hfit]]]. split; [|exact Hfit].
  destruct Hwf as [W1 _]. rewrite Ha. unfold rbase, smod in *. rewrite Et in *. rewrite Eo.
  rewrite Zplus_mod_idemp_r. rewrite Z.add_assoc. rewrite <- Zplus_mod_idemp_l.
  apply Z.mod_small. pose proof (Z.mod_pos_bound (teval ρ ts + wZ (rg_bo R)) two64 ltac:(unfold two64; lia)).
  pose proof (to_Z_bounded x). lia.
Qed.

Lemma find_reg_spec (A : list region) (ts : terms) (o : w64) (n : int) : forall (j i : nat) (R : region) (x : int),
  find_reg A ts o n j = Some (i, R, x) -> (j <= i)%nat /\ nth_error A (i - j) = Some R /\ roff R ts o n = Some x.
Proof.
  induction A as [|R0 A IH]; intros j i R x H; cbn [find_reg] in H; [discriminate|].
  destruct (roff R0 ts o n) as [x0|] eqn:E.
  - injection H as <- <- <-. rewrite Nat.sub_diag. split; [lia | split; [reflexivity | exact E]].
  - destruct (IH (S j) i R x H) as [H1 [H2 H3]]. split; [lia|]. split; [|exact H3].
    replace (i - j)%nat with (S (i - S j)) by lia. exact H2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Reads.
Variable segs : list Segment.

(* [comment removed for export] *)
Fixpoint rbytes (R : region) (x : int) (n : nat) : list xb :=
  match n with
  | O => []
  | S n' => rbyte segs R x :: rbytes R (x + 1)%uint63 n'
  end.

(* [comment removed for export] *)
Definition rbytes_fast (R : region) (x : int) (n : nat) : list xb :=
  let o := i2n (x land 7)%uint63 in
  if Nat.leb (o + n) 8 then
    match get_cell_opt R (x >> 3)%uint63 with
    | Some c => map (fun i => cbyte c (o + i)) (seq 0 n)
    | None => rbytes R x n
    end
  else rbytes R x n.

Definition a_load (A : list region) (v : xv) (n : nat) : option (list xb) :=
  match xaddr v with
  | Some (ts, o) =>
      match find_reg A ts o (of_Z (Z.of_nat n)) 0 with
      | Some (_, R, x) => Some (rbytes_fast R x n)
      | None => None
      end
  | None => None
  end.

Lemma rbytes_length (R : region) (x : int) (n : nat) : length (rbytes R x n) = n.
Proof. revert x; induction n as [|n IH]; intros x; cbn [rbytes length]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma rbytes_nth (R : region) (x : int) (n : nat) (i : nat) :
  to_Z x + Z.of_nat n < 2 ^ 62 -> (i < n)%nat ->
  nth i (rbytes R x n) BT = rbyte segs R (x + of_Z (Z.of_nat i))%uint63.
Proof.
  revert x i; induction n as [|n IH]; intros x i Hx Hi; [lia|].
  pose proof (to_Z_bounded x).
  destruct i as [|i]; cbn [rbytes nth].
  - f_equal. apply to_Z_inj. rewrite phi_add_small; rewrite phi_of_Z_small; lia.
  - rewrite IH by (try lia; rewrite int_add_1; lia).
    f_equal. apply to_Z_inj.
    assert (E1 : to_Z (x + 1)%uint63 = to_Z x + 1) by (apply int_add_1; lia).
    assert (E2 : to_Z (of_Z (Z.of_nat i)) = Z.of_nat i) by (apply phi_of_Z_small; lia).
    assert (E3 : to_Z (of_Z (Z.of_nat (S i))) = Z.of_nat (S i)) by (apply phi_of_Z_small; lia).
    rewrite (phi_add_small (x + 1) (of_Z (Z.of_nat i))), (phi_add_small x (of_Z (Z.of_nat (S i)))); rewrite ?E1, ?E2, ?E3; lia.
Qed.

(* [comment removed for export] *)
Lemma cell_split (x : int) (i : nat) :
  to_Z x + Z.of_nat i < 2 ^ 62 -> (Z.to_nat (to_Z x mod 8) + i < 8)%nat ->
  ((x + of_Z (Z.of_nat i)) >> 3)%uint63 = (x >> 3)%uint63
  /\ to_Z ((x + of_Z (Z.of_nat i)) land 7)%uint63 = to_Z x mod 8 + Z.of_nat i.
Proof.
  intros Hx Ho. pose proof (to_Z_bounded x) as Hb.
  assert (Hxi : to_Z (x + of_Z (Z.of_nat i))%uint63 = to_Z x + Z.of_nat i) by (rewrite phi_add_small; rewrite phi_of_Z_small; lia).
  pose proof (Z.div_mod (to_Z x) 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound (to_Z x) 8 ltac:(lia)) as Hm.
  split.
  - apply to_Z_inj. rewrite !phi_lsr3, Hxi.
    replace (to_Z x + Z.of_nat i) with ((to_Z x mod 8 + Z.of_nat i) + (to_Z x / 8) * 8) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
  - rewrite phi_land7, Hxi.
    replace (to_Z x + Z.of_nat i) with ((to_Z x mod 8 + Z.of_nat i) + (to_Z x / 8) * 8) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma rbytes_fast_eq (R : region) (x : int) (n : nat) :
  to_Z x + Z.of_nat n < 2 ^ 62 -> rbytes_fast R x n = rbytes R x n.
Proof.
  intros Hx. unfold rbytes_fast. destruct (Nat.leb_spec (i2n (x land 7)%uint63 + n) 8) as [Hc|Hc]; [|reflexivity].
  destruct (get_cell_opt R (x >> 3)%uint63) as [c|] eqn:Ec; [|reflexivity].
  apply nth_ext with (d := BT) (d' := BT).
  - rewrite rbytes_length, length_map, length_seq. reflexivity.
  - intros i Hi. rewrite length_map, length_seq in Hi. rewrite rbytes_nth by lia.
    rewrite (nth_map_seq0 (fun i0 => cbyte c (i2n (x land 7)%uint63 + i0)) n i BT Hi).
    rewrite i2n_land7, phi_land7 in Hc |- *.
    destruct (cell_split x i ltac:(lia) ltac:(lia)) as [Ek El].
    unfold rbyte. rewrite Ek, Ec. f_equal. rewrite i2n_land7, El.
    pose proof (Z.mod_pos_bound (to_Z x) 8 ltac:(lia)). lia.
Qed.

Lemma rdn_cons' (m : word -> option byte) (a : word) (n : nat) :
  rdn segs m a (S n) = match rv segs m a with
                       | Some b => match rdn segs m (a + 1)%bv n with Some r => Some (b :: r) | None => None end
                       | None => None
                       end.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rdn_region (ρ : valuation) (m : word -> option byte) (R : region) :
  RRegion0 segs ρ m R -> forall (n : nat) (x : int), to_Z x + Z.of_nat n <= to_Z (rg_n R) ->
  exists bs, rdn segs m (wz (rbase ρ R + to_Z x)) n = Some bs /\ Forall2 (xb_bv ρ) (rbytes R x n) bs.
Proof.
  intros HR. induction n as [|n IH]; intros x Hx.
  - exists []. split; [reflexivity | constructor].
  - pose proof (to_Z_bounded x) as Hb. pose proof (to_Z_bounded (rg_n R)) as Hnb. change wB with (2 ^ 63) in *.
    destruct (HR x ltac:(lia)) as [[b [Hb1 Hab]] _].
    destruct (IH (x + 1)%uint63 ltac:(rewrite int_add_1 by lia; lia)) as [bs [Hr Hf]].
    exists (b :: bs). split; [|cbn [rbytes]; constructor; assumption].
    rewrite rdn_cons', Hb1, wz_succ. rewrite int_add_1 in Hr by lia. rewrite <- Z.add_assoc, Hr. reflexivity.
Qed.

Lemma store_ok_range (ρ : valuation) (m : word -> option byte) (R : region) (x : int) (n : nat) :
  RRegion0 segs ρ m R -> rk_writable (rg_kind R) = true -> to_Z x + Z.of_nat n <= to_Z (rg_n R) -> to_Z (rg_n R) < 2 ^ 47 ->
  store_ok segs m (wz (rbase ρ R + to_Z x)) n = true.
Proof.
  intros HR Hw Hx H47. revert x Hx. induction n as [|n IH]; intros x Hx; [reflexivity|].
  pose proof (to_Z_bounded x) as Hb. change wB with (2 ^ 63) in *.
  destruct (HR x ltac:(lia)) as [_ Hwv]. specialize (Hwv Hw). cbn [store_ok].
  destruct (wview segs m (wz (rbase ρ R + to_Z x))) eqn:Ew; [|congruence].
  rewrite wz_succ. rewrite <- Z.add_assoc. rewrite <- (int_add_1 x) by lia. apply IH. rewrite int_add_1 by lia. lia.
Qed.

Lemma a_load_length (A : list region) (v : xv) (n : nat) (l : list xb) : a_load A v n = Some l -> length l = n.
Proof.
  intros H. unfold a_load in H. destruct (xaddr v) as [[ts o]|]; [|discriminate].
  destruct (find_reg A ts o (of_Z (Z.of_nat n)) 0) as [[[i R] x]|] eqn:Ef; [|discriminate]. injection H as <-.
  unfold rbytes_fast. destruct (Nat.leb _ 8); [destruct (get_cell_opt R _)|]; rewrite ?length_map, ?length_seq, ?rbytes_length; reflexivity.
Qed.

Lemma xaddr_smod (ρ : valuation) (v : xv) (a : bv 64) (ts : terms) (o : w64) :
  xv_val ρ v a -> xaddr v = Some (ts, o) -> bv_unsigned a = smod ρ ts o.
Proof.
  intros Hv Ea. destruct v; cbn [xaddr] in Ea; try discriminate; injection Ea as <- <-; cbn [xv_val] in Hv.
  - rewrite Hv. unfold smod. cbn [teval]. rewrite Z.add_0_l. symmetry. apply Z.mod_small. apply wZ_range.
  - exact Hv.
Qed.

(* [comment removed for export] *)
Lemma a_load_sound (ρ : valuation) (A : list region) (m : word -> option byte) (v : xv) (a : bv 64) (n : nat) (l : list xb) :
  RMem segs ρ A m -> xv_val ρ v a -> (1 <= n < 1000)%nat -> a_load A v n = Some l ->
  exists bs, rdn segs m a n = Some bs /\ Forall2 (xb_bv ρ) l bs.
Proof.
  intros [Hok HR] Hv Hn H. unfold a_load in H. destruct (xaddr v) as [[ts o]|] eqn:Ea; [|discriminate].
  destruct (find_reg A ts o (of_Z (Z.of_nat n)) 0) as [[[i R] x]|] eqn:Ef; [|discriminate]. injection H as <-.
  destruct (find_reg_spec A ts o _ 0 i R x Ef) as [_ [Hi Hr]]. rewrite Nat.sub_0_r in Hi.
  pose proof (regions_ok_nth ρ A i R Hok Hi) as Hwf. pose proof (Forall_nth _ A i R HR Hi) as HRR.
  rewrite (RRegion_ne segs ρ m R (roff_ne R ts o _ x Hr)) in HRR.
  destruct (roff_addr ρ R ts o (of_Z (Z.of_nat n)) x a ltac:(rewrite phi_of_nat_small by lia; lia) Hwf (xaddr_smod ρ v a ts o Hv Ea) Hr) as [Eaddr Hfit].
  rewrite phi_of_nat_small in Hfit by lia.
  pose proof (to_Z_bounded (rg_n R)) as Hnb. change wB with (2 ^ 63) in Hnb. destruct Hwf as [W1 [H47 _]].
  rewrite rbytes_fast_eq by lia.
  replace a with (wz (rbase ρ R + to_Z x)).
  - apply rdn_region; assumption.
  - apply bv_eq. rewrite u_wz; [symmetry; exact Eaddr|]. pose proof (smod_range ρ (rg_ts R) (rg_bo R)). pose proof (to_Z_bounded x).
    unfold rbase, two64 in *. lia.
Qed.

End Reads.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Stores.
Variable segs : list Segment.

Definition unk_cell : cell := CB (repeat BT 8).

(* [comment removed for export] *)
Definition default_cell (kd : rkind) (k : int) : cell :=
  match kd with
  | KZero | KShadow => CW w_zero
  | KUnk | KEntry _ => unk_cell
  | KImg _ _ => let x := (k << 3)%uint63 in
                CB [default_byte segs kd x; default_byte segs kd (x + 1)%uint63; default_byte segs kd (x + 2)%uint63;
                    default_byte segs kd (x + 3)%uint63; default_byte segs kd (x + 4)%uint63; default_byte segs kd (x + 5)%uint63;
                    default_byte segs kd (x + 6)%uint63; default_byte segs kd (x + 7)%uint63]
  end.

Definition cell_of (R : region) (k : int) : cell :=
  match get_cell_opt R k with Some c => c | None => default_cell (rg_kind R) k end.

(* [comment removed for export] *)
Definition cell_write (c : cell) (o : nat) (nb : list xb) : cell :=
  let e := (o + length nb)%nat in
  CB (map (fun j => if Nat.leb o j then if Nat.ltb j e then nth (j - o) nb BT else cbyte c j else cbyte c j) (seq 0 8)).

(* [comment removed for export] *)
Fixpoint lits (l : list xb) : option (list int) :=
  match l with
  | [] => Some []
  | BL b :: r => if (b <? 256)%uint63 then match lits r with Some bs => Some (b :: bs) | None => None end else None
  | _ :: _ => None
  end.

Definition lit8 (l : list xb) : option w64 :=
  match lits l with
  | Some bs => if Nat.eqb (length bs) 8 then Some (ExLoad.w_of_bytes8 bs) else None
  | None => None
  end.

Definition norm_cell (c : cell) : cell :=
  match c with
  | CB l => match lit8 l with Some w => CW w | None => c end
  | _ => c
  end.

(* [comment removed for export] *)
Definition rwrite1 (nb : list xb) (R : region) (x : int) : region :=
  let k := (x >> 3)%uint63 in
  with_cells R (iset (rg_d R) (rg_cells R) k (norm_cell (cell_write (cell_of R k) (i2n (x land 7)%uint63) nb))).

Fixpoint rwrite_each (nb : list xb) (R : region) (x : int) : region :=
  match nb with
  | [] => R
  | b :: nb' => rwrite_each nb' (rwrite1 [b] R x) (x + 1)%uint63
  end.

(* [comment removed for export] *)
Fixpoint rwrite_chunks (fuel : nat) (nb : list xb) (R : region) (x : int) : region :=
  match fuel, nb with
  | S fuel', _ :: _ =>
      let k := (8 - i2n (x land 7)%uint63)%nat in
      let c := firstn k nb in
      rwrite_chunks fuel' (skipn k nb) (rwrite1 c R x) (x + of_Z (Z.of_nat (length c)))%uint63
  | _, _ => R
  end.

Definition rwrite (nb : list xb) (R : region) (x : int) : region :=
  if Nat.leb (i2n (x land 7)%uint63 + length nb) 8 then rwrite1 nb R x else rwrite_chunks (length nb) nb R x.

(* [comment removed for export] *)
Definition a_store (A : list region) (v : xv) (nb : list xb) : option (list region) :=
  match xaddr v with
  | Some (ts, o) =>
      match find_reg A ts o (of_Z (Z.of_nat (length nb))) 0 with
      | Some (i, R, x) => if rk_writable (rg_kind R) then Some (replace_nth A i (rwrite nb R x)) else None
      | None => None
      end
  | None => None
  end.

End Stores.

Section StoreLemmas.
Variable segs : list Segment.

Lemma cell_write_nth (c : cell) (o : nat) (nb : list xb) (j : nat) : (j < 8)%nat ->
  cbyte (cell_write c o nb) j = if Nat.leb o j && Nat.ltb j (o + length nb) then nth (j - o) nb BT else cbyte c j.
Proof.
  intros Hj. unfold cell_write, cbyte at 1. cbv zeta.
  rewrite (nth_map_seq0 (fun j0 => if Nat.leb o j0 then if Nat.ltb j0 (o + length nb) then nth (j0 - o) nb BT else cbyte c j0 else cbyte c j0) 8 j BT Hj).
  destruct (Nat.leb o j); reflexivity.
Qed.

Lemma lits_spec (l : list xb) : forall bs, lits l = Some bs -> l = map BL bs /\ Forall (fun b => to_Z b < 256) bs.
Proof.
  induction l as [|[b| |] r IH]; intros bs H; cbn [lits] in H; try discriminate.
  - injection H as <-. split; [reflexivity | constructor].
  - destruct (ltbP b 256) as [Hb|]; [|discriminate]. destruct (lits r) as [bs'|]; [|discriminate]. injection H as <-.
    destruct (IH bs' eq_refl) as [-> HF]. split; [reflexivity|]. constructor; [exact Hb | exact HF].
Qed.

Lemma lit8_spec (l : list xb) (w : w64) : lit8 l = Some w ->
  exists bs, l = map BL bs /\ length bs = 8%nat /\ Forall (fun b => to_Z b < 256) bs /\ w = ExLoad.w_of_bytes8 bs.
Proof.
  unfold lit8. intros H. destruct (lits l) as [bs|] eqn:E; [|discriminate].
  destruct (Nat.eqb (length bs) 8) eqn:El; [|discriminate]. injection H as <-. apply Nat.eqb_eq in El.
  destruct (lits_spec l bs E) as [-> HF]. exists bs. repeat split; assumption.
Qed.

Lemma norm_cell_byte (c : cell) (j : nat) : (j < 8)%nat -> cbyte (norm_cell c) j = cbyte c j.
Proof.
  intros Hj. destruct c as [w|l]; [reflexivity|]. cbn [norm_cell]. destruct (lit8 l) as [w|] eqn:E; [|reflexivity].
  destruct (lit8_spec l w E) as [bs [-> [Hl [Hb ->]]]]. cbn [cbyte].
  rewrite (nth_indep _ BT (BL 0%uint63)) by (rewrite length_map; lia). rewrite (map_nth BL bs 0%uint63 j). f_equal.
  apply to_Z_inj. rewrite w_byte_spec by exact Hj. rewrite (ExLoad.w_of_bytes8_spec bs Hl Hb).
  rewrite zbyte_zcombine.
  - rewrite (nth_indep _ 0 (to_Z 0%uint63)) by (rewrite length_map; lia). apply map_nth.
  - apply Forall_map. eapply Forall_impl; [|exact Hb]. intros b Hlt. cbv beta in *. pose proof (to_Z_bounded b). lia.
  - rewrite length_map. lia.
Qed.

Lemma w_byte_zero (j : nat) : (j < 8)%nat -> w_byte w_zero j = 0%uint63.
Proof. intros Hj. do 8 (destruct j as [|j]; [reflexivity|]). lia. Qed.

(* [comment removed for export] *)
Lemma key_off (y : int) : to_Z y < 2 ^ 60 -> forall k : int, to_Z k = to_Z y mod 8 -> (((y >> 3) << 3) + k)%uint63 = y.
Proof.
  intros Hy k Hk. pose proof (to_Z_bounded y) as Hb. change wB with (2 ^ 63) in Hb.
  pose proof (Z.div_mod (to_Z y) 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound (to_Z y) 8 ltac:(lia)) as Hm.
  assert (Hd : 0 <= to_Z y / 8 < 2 ^ 57) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  apply to_Z_inj. rewrite add_spec, lsl_spec, phi_lsr3, Hk. change (to_Z 3%uint63) with 3. change wB with (2 ^ 63).
  rewrite (Z.mod_small (to_Z y / 8 * 2 ^ 3)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma cbyte_default_cell (kd : rkind) (y : int) : to_Z y < 2 ^ 60 ->
  cbyte (default_cell segs kd (y >> 3)%uint63) (i2n (y land 7)%uint63) = default_byte segs kd y.
Proof.
  intros Hy. pose proof (i2n_lt8 y) as Hlt.
  destruct kd as [| | |w i|ph]; cbn [default_cell default_byte cbyte].
  - rewrite w_byte_zero by exact Hlt. reflexivity.
  - rewrite w_byte_zero by exact Hlt. reflexivity.
  - unfold unk_cell. cbn [cbyte]. apply nth_repeat.
  - rewrite i2n_land7. pose proof (phi_land7 y) as H7. pose proof (Z.mod_pos_bound (to_Z y) 8 ltac:(lia)) as Hm.
    set (K := KImg w i).
    assert (E : to_Z (y land 7)%uint63 = 0 \/ to_Z (y land 7)%uint63 = 1 \/ to_Z (y land 7)%uint63 = 2 \/ to_Z (y land 7)%uint63 = 3
             \/ to_Z (y land 7)%uint63 = 4 \/ to_Z (y land 7)%uint63 = 5 \/ to_Z (y land 7)%uint63 = 6 \/ to_Z (y land 7)%uint63 = 7) by lia.
    assert (E0 : forall z : int, (z + 0)%uint63 = z).
    { intros z. apply to_Z_inj. rewrite add_spec. change (to_Z 0%uint63) with 0. rewrite Z.add_0_r. apply Z.mod_small. apply to_Z_bounded. }
    destruct E as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add nth].
    + rewrite <- (E0 ((y >> 3) << 3)%uint63). rewrite (key_off y Hy 0%uint63) by (rewrite <- H7, E; reflexivity). reflexivity.
    + rewrite (key_off y Hy 1%uint63) by (rewrite <- H7, E; reflexivity). reflexivity.
    + rewrite (key_off y Hy 2%uint63) by (rewrite <- H7, E; reflexivity). reflexivity.
    + rewrite (key_off y Hy 3%uint63) by (rewrite <- H7, E; reflexivity). reflexivity.
    + rewrite (key_off y Hy 4%uint63) by (rewrite <- H7, E; reflexivity). reflexivity.
    + rewrite (key_off y Hy 5%uint63) by (rewrite <- H7, E; reflexivity). reflexivity.
    + rewrite (key_off y Hy 6%uint63) by (rewrite <- H7, E; reflexivity). reflexivity.
    + rewrite (key_off y Hy 7%uint63) by (rewrite <- H7, E; reflexivity). reflexivity.
  - unfold unk_cell. cbn [cbyte]. apply nth_repeat.
Qed.

Lemma cbyte_cell_of (R : region) (y : int) : to_Z y < 2 ^ 60 ->
  cbyte (cell_of segs R (y >> 3)%uint63) (i2n (y land 7)%uint63) = rbyte segs R y.
Proof.
  intros Hy. unfold cell_of, rbyte. destruct (get_cell_opt R (y >> 3)%uint63); [reflexivity|]. apply cbyte_default_cell. exact Hy.
Qed.

Lemma rwrite1_fields (nb : list xb) (R : region) (x : int) : same_fields R (rwrite1 segs nb R x).
Proof. repeat split. Qed.

Lemma rbyte_rwrite1 (nb : list xb) (R : region) (x y : int) :
  to_Z (rg_n R) <= 8 * 2 ^ Z.of_nat (rg_d R) -> to_Z (rg_n R) < 2 ^ 60 -> to_Z x < to_Z (rg_n R) -> to_Z y < to_Z (rg_n R) ->
  (i2n (x land 7)%uint63 + length nb <= 8)%nat ->
  rbyte segs (rwrite1 segs nb R x) y =
  if (to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length nb)) then nth (Z.to_nat (to_Z y - to_Z x)) nb BT
  else rbyte segs R y.
Proof.
  intros Hd H60 Hx Hy Hn.
  pose proof (to_Z_bounded x) as Hxb. pose proof (to_Z_bounded y) as Hyb.
  pose proof (key_small R x Hd Hx) as Hkx. pose proof (key_small R y Hd Hy) as Hky.
  rewrite i2n_land7, phi_land7 in Hn.
  pose proof (Z.div_mod (to_Z x) 8 ltac:(lia)) as Hdx. pose proof (Z.mod_pos_bound (to_Z x) 8 ltac:(lia)) as Hmx.
  pose proof (Z.div_mod (to_Z y) 8 ltac:(lia)) as Hdy. pose proof (Z.mod_pos_bound (to_Z y) 8 ltac:(lia)) as Hmy.
  unfold rbyte at 1. unfold rwrite1, get_cell_opt, with_cells. cbn [rg_d rg_cells rg_kind].
  rewrite iget_iset. rewrite !Z.mod_small by (split; [apply to_Z_bounded | assumption]).
  rewrite !phi_lsr3 in *.
  destruct (Z.eqb_spec (to_Z x / 8) (to_Z y / 8)) as [Ek|Ek].
  - rewrite norm_cell_byte by apply i2n_lt8. rewrite cell_write_nth by apply i2n_lt8.
    rewrite !i2n_land7, !phi_land7.
    assert (Hk : (x >> 3)%uint63 = (y >> 3)%uint63) by (apply to_Z_inj; rewrite !phi_lsr3; exact Ek).
    destruct (Nat.leb_spec (Z.to_nat (to_Z x mod 8)) (Z.to_nat (to_Z y mod 8))) as [L1|L1];
      [destruct (Nat.ltb_spec (Z.to_nat (to_Z y mod 8)) (Z.to_nat (to_Z x mod 8) + length nb)) as [L2|L2]|]; cbn [andb].
    + replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length nb))) with true
        by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      f_equal. lia.
    + replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length nb))) with false
        by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
      rewrite Hk. rewrite <- (phi_land7 y), <- i2n_land7. apply cbyte_cell_of. lia.
    + replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length nb))) with false
        by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
      rewrite Hk. rewrite <- (phi_land7 y), <- i2n_land7. apply cbyte_cell_of. lia.
  - replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length nb))) with false; [reflexivity|].
    symmetry. apply andb_false_iff. destruct (Z_lt_le_dec (to_Z y) (to_Z x)); [left; apply Z.leb_gt; lia|].
    right. apply Z.ltb_ge. assert (to_Z x / 8 < to_Z y / 8) by (assert (to_Z x / 8 <= to_Z y / 8) by (apply Z.div_le_mono; lia); lia). lia.
Qed.

Lemma rwrite_each_fields (nb : list xb) : forall (R : region) (x : int), same_fields R (rwrite_each segs nb R x).
Proof.
  induction nb as [|b nb IH]; intros R x; cbn [rwrite_each]; [repeat split|].
  destruct (IH (rwrite1 segs [b] R x) (x + 1)%uint63) as [F1 [F2 [F3 [F4 F5]]]]. repeat split; assumption.
Qed.

Lemma rbyte_rwrite_each (nb : list xb) : forall (R : region) (x y : int),
  to_Z (rg_n R) <= 8 * 2 ^ Z.of_nat (rg_d R) -> to_Z (rg_n R) < 2 ^ 60 ->
  to_Z x + Z.of_nat (length nb) <= to_Z (rg_n R) -> to_Z y < to_Z (rg_n R) ->
  rbyte segs (rwrite_each segs nb R x) y =
  if (to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length nb)) then nth (Z.to_nat (to_Z y - to_Z x)) nb BT
  else rbyte segs R y.
Proof.
  induction nb as [|b nb IH]; intros R x y Hd H60 Hx Hy; cbn [rwrite_each length].
  - replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat 0)) with false
      by (symmetry; apply andb_false_iff; destruct (Z_lt_le_dec (to_Z y) (to_Z x)); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]).
    reflexivity.
  - cbn [length] in Hx. pose proof (to_Z_bounded x) as Hxb. change wB with (2 ^ 63) in Hxb.
    assert (HL : Z.of_nat (S (length nb)) = Z.of_nat (length nb) + 1) by lia.
    assert (Hx1 : to_Z (x + 1)%uint63 = to_Z x + 1) by (apply int_add_1; lia).
    destruct (rwrite1_fields [b] R x) as [_ [_ [F3 [_ F5]]]].
    rewrite IH by (rewrite ?F3, ?F5, ?Hx1; lia).
    rewrite Hx1. rewrite rbyte_rwrite1 by (try lia; cbn [length]; pose proof (i2n_lt8 x); lia).
    cbn [length].
    destruct (Z.eqb_spec (to_Z y) (to_Z x)) as [->|Hne].
    + replace ((to_Z x + 1 <=? to_Z x) && _) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
      replace ((to_Z x <=? to_Z x) && (to_Z x <? to_Z x + Z.of_nat 1)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      replace ((to_Z x <=? to_Z x) && (to_Z x <? to_Z x + Z.of_nat (S (length nb)))) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      rewrite Z.sub_diag. reflexivity.
    + destruct ((to_Z x + 1 <=? to_Z y) && (to_Z y <? to_Z x + 1 + Z.of_nat (length nb))) eqn:E1.
      * apply andb_true_iff in E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
        replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (S (length nb)))) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
        replace (Z.to_nat (to_Z y - to_Z x)) with (S (Z.to_nat (to_Z y - (to_Z x + 1)))) by lia. reflexivity.
      * replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat 1)) with false by (symmetry; apply andb_false_iff; destruct (Z_lt_le_dec (to_Z y) (to_Z x)); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]).
        replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (S (length nb)))) with false; [reflexivity|].
        symmetry. apply andb_false_iff. apply andb_false_iff in E1 as [E1|E1]; [apply Z.leb_gt in E1 | apply Z.ltb_ge in E1].
        -- left. apply Z.leb_gt. lia.
        -- right. apply Z.ltb_ge. lia.
Qed.

Lemma rwrite_chunks_fields (fuel : nat) : forall (nb : list xb) (R : region) (x : int), same_fields R (rwrite_chunks segs fuel nb R x).
Proof.
  induction fuel as [|fuel IH]; intros nb R x; cbn [rwrite_chunks]; [repeat split|].
  destruct nb as [|b nb']; [repeat split|].
  set (c := firstn _ (b :: nb')). set (r := skipn _ (b :: nb')).
  destruct (IH r (rwrite1 segs c R x) (x + of_Z (Z.of_nat (length c)))%uint63) as [F1 [F2 [F3 [F4 F5]]]]. repeat split; assumption.
Qed.

Lemma rbyte_rwrite_chunks (fuel : nat) : forall (nb : list xb) (R : region) (x y : int),
  (length nb <= fuel)%nat ->
  to_Z (rg_n R) <= 8 * 2 ^ Z.of_nat (rg_d R) -> to_Z (rg_n R) < 2 ^ 60 ->
  to_Z x + Z.of_nat (length nb) <= to_Z (rg_n R) -> to_Z y < to_Z (rg_n R) ->
  rbyte segs (rwrite_chunks segs fuel nb R x) y =
  if (to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length nb)) then nth (Z.to_nat (to_Z y - to_Z x)) nb BT
  else rbyte segs R y.
Proof.
  induction fuel as [|fuel IH]; intros nb R x y Hf Hd H60 Hx Hy.
  - destruct nb; [|cbn [length] in Hf; lia]. cbn [rwrite_chunks length].
    replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat 0)) with false
      by (symmetry; apply andb_false_iff; destruct (Z_lt_le_dec (to_Z y) (to_Z x)); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]).
    reflexivity.
  - destruct nb as [|b nb'].
    { cbn [rwrite_chunks length].
      replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat 0)) with false
        by (symmetry; apply andb_false_iff; destruct (Z_lt_le_dec (to_Z y) (to_Z x)); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]).
      reflexivity. }
    cbn [rwrite_chunks]. set (nb := b :: nb') in *.
    pose proof (i2n_lt8 x) as H8. set (k := (8 - i2n (x land 7)%uint63)%nat) in *.
    assert (Hk1 : (1 <= k <= 8)%nat) by (unfold k; lia).
    set (c := firstn k nb). set (r := skipn k nb).
    assert (Hnb : nb = c ++ r) by (symmetry; apply firstn_skipn).
    assert (Hlc : (1 <= length c <= k)%nat).
    { unfold c. rewrite length_firstn. unfold nb. cbn [length]. lia. }
    assert (Hlen : length nb = (length c + length r)%nat) by (rewrite Hnb at 1; apply length_app).
    pose proof (to_Z_bounded x) as Hxb. change wB with (2 ^ 63) in Hxb.
    assert (Hxc : to_Z (x + of_Z (Z.of_nat (length c)))%uint63 = to_Z x + Z.of_nat (length c)).
    { rewrite add_spec, of_Z_spec. change wB with (2 ^ 63). rewrite (Z.mod_small (Z.of_nat (length c))) by lia. apply Z.mod_small. lia. }
    destruct (rwrite1_fields c R x) as [_ [_ [F3 [_ F5]]]].
    rewrite IH; [| lia | rewrite F3, F5; assumption | rewrite F3; assumption | rewrite F3, Hxc; lia | rewrite F3; exact Hy].
    rewrite Hxc. rewrite rbyte_rwrite1 by (try assumption; try lia; unfold k in Hlc; lia).
    rewrite Hlen. rewrite Nat2Z.inj_add.
    destruct (Z_lt_le_dec (to_Z y) (to_Z x)) as [L0|L0].
    + replace ((to_Z x + Z.of_nat (length c) <=? to_Z y) && _) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
      replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length c))) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
      replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + (Z.of_nat (length c) + Z.of_nat (length r)))) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
      reflexivity.
    + destruct (Z_lt_le_dec (to_Z y) (to_Z x + Z.of_nat (length c))) as [L1|L1].
      * replace ((to_Z x + Z.of_nat (length c) <=? to_Z y) && _) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
        replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length c))) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
        replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + (Z.of_nat (length c) + Z.of_nat (length r)))) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
        rewrite (f_equal (fun l => nth (Z.to_nat (to_Z y - to_Z x)) l BT) Hnb). rewrite app_nth1 by lia. reflexivity.
      * replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length c))) with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
        destruct (Z_lt_le_dec (to_Z y) (to_Z x + Z.of_nat (length c) + Z.of_nat (length r))) as [L2|L2].
        -- replace ((to_Z x + Z.of_nat (length c) <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length c) + Z.of_nat (length r))) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
           replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + (Z.of_nat (length c) + Z.of_nat (length r)))) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
           rewrite (f_equal (fun l => nth (Z.to_nat (to_Z y - to_Z x)) l BT) Hnb). rewrite app_nth2 by lia. f_equal. lia.
        -- replace ((to_Z x + Z.of_nat (length c) <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length c) + Z.of_nat (length r))) with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
           replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + (Z.of_nat (length c) + Z.of_nat (length r)))) with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
           reflexivity.
Qed.

Lemma rwrite_fields (nb : list xb) (R : region) (x : int) : same_fields R (rwrite segs nb R x).
Proof. unfold rwrite. destruct (Nat.leb _ 8); [apply rwrite1_fields | apply rwrite_chunks_fields]. Qed.

Lemma rbase_rwrite (ρ : valuation) (nb : list xb) (R : region) (x : int) : rbase ρ (rwrite segs nb R x) = rbase ρ R.
Proof. destruct (rwrite_fields nb R x) as [F1 [F2 _]]. unfold rbase. rewrite F1, F2. reflexivity. Qed.

Lemma rbyte_rwrite (nb : list xb) (R : region) (x y : int) :
  to_Z x + Z.of_nat (length nb) <= to_Z (rg_n R) -> to_Z (rg_n R) <= 8 * 2 ^ Z.of_nat (rg_d R) -> to_Z (rg_n R) < 2 ^ 47 ->
  (1 <= length nb)%nat -> to_Z y < to_Z (rg_n R) ->
  rbyte segs (rwrite segs nb R x) y =
  if (to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length nb)) then nth (Z.to_nat (to_Z y - to_Z x)) nb BT
  else rbyte segs R y.
Proof.
  intros Hx Hd H47 H1 Hy. unfold rwrite. destruct (Nat.leb_spec (i2n (x land 7)%uint63 + length nb) 8) as [Hc|Hc].
  - apply rbyte_rwrite1; try assumption; lia.
  - apply rbyte_rwrite_chunks; try assumption; lia.
Qed.

End StoreLemmas.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section StoreSound.
Variable segs : list Segment.

Lemma write_to_mem_spec (bs : list byte) : forall (m : word -> option byte) (a : Z) (y : word),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  write_to_mem m (wz a) bs y =
  if (a <=? bv_unsigned y) && (bv_unsigned y <? a + Z.of_nat (length bs))
  then nth_error bs (Z.to_nat (bv_unsigned y - a)) else m y.
Proof.
  induction bs as [|b bs IH]; intros m a y Ha Hn; cbn [write_to_mem length] in *.
  - destruct (_ && _) eqn:E; [|reflexivity].
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
  - pose proof (bv_unsigned_in_range 64 y) as Hy. change (bv_modulus 64) with (2^64) in Hy.
    rewrite wz_succ. rewrite IH by lia.
    destruct (Z.eq_dec (bv_unsigned y) a) as [Heq|Hne].
    + replace (bv_eqb y (wz a)) with true.
      2:{ symmetry. unfold bv_eqb. apply Z.eqb_eq. rewrite u_wz by lia. exact Heq. }
      rewrite Heq.
      replace ((a + 1 <=? a) && (a <? a + 1 + Z.of_nat (length bs))) with false
        by (symmetry; apply andb_false_intro1; apply Z.leb_gt; lia).
      replace ((a <=? a) && (a <? a + Z.of_nat (S (length bs)))) with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
      rewrite Z.sub_diag. reflexivity.
    + replace (bv_eqb y (wz a)) with false.
      2:{ symmetry. unfold bv_eqb. apply Z.eqb_neq. rewrite u_wz by lia. exact Hne. }
      destruct ((a + 1 <=? bv_unsigned y) && (bv_unsigned y <? a + 1 + Z.of_nat (length bs))) eqn:E1.
      * apply andb_prop in E1. destruct E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
        replace ((a <=? bv_unsigned y) && (bv_unsigned y <? a + Z.of_nat (S (length bs)))) with true
          by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
        replace (Z.to_nat (bv_unsigned y - a)) with (S (Z.to_nat (bv_unsigned y - (a + 1)))) by lia.
        reflexivity.
      * destruct ((a <=? bv_unsigned y) && (bv_unsigned y <? a + Z.of_nat (S (length bs)))) eqn:E2; [|reflexivity].
        apply andb_prop in E2. destruct E2 as [E2 E3]. apply Z.leb_le in E2. apply Z.ltb_lt in E3.
        exfalso. apply Bool.andb_false_iff in E1. destruct E1 as [E1|E1].
        -- apply Z.leb_gt in E1. lia.
        -- apply Z.ltb_ge in E1. lia.
Qed.

(* [comment removed for export] *)
Lemma RRegion_mframe (ρ : valuation) (m m' : word -> option byte) (R : region) :
  region_wf ρ R -> (forall z, rbase ρ R <= z < rbase ρ R + to_Z (rg_n R) -> m' (wz z) = m (wz z)) ->
  RRegion segs ρ m R -> RRegion segs ρ m' R.
Proof.
  intros Hwf Hfr HR. unfold RRegion in *. destruct (rg_kind R) eqn:Ek.
  1-4: (intros y Hy; pose proof (to_Z_bounded y) as Hyb;
        assert (Eq : m' (wz (rbase ρ R + to_Z y)) = m (wz (rbase ρ R + to_Z y))) by (apply Hfr; lia);
        destruct (HR y Hy) as [[b [Hb Hab]] Hw]; unfold rv, wview in *; rewrite Eq;
        split; [exists b; split; assumption | exact Hw]).
  destruct HR as [HF [Hb [Hlen Hbytes]]]. split; [exact HF|]. split; [exact Hb|]. split; [exact Hlen|].
  intros z Hz. rewrite <- (Hbytes z Hz). apply (Hfr (rbase ρ R + z)). lia.
Qed.

(* [comment removed for export] *)
Lemma a_store_sound_gen (ρ : valuation) (A A' : list region) (m m' : word -> option byte) (v : xv) (a : bv 64) (nb : list xb) :
  RMem segs ρ A m -> xv_val ρ v a -> (1 <= length nb)%nat -> Z.of_nat (length nb) < 2 ^ 40 -> a_store segs A v nb = Some A' ->
  (forall x : word, ~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length nb)) -> m' x = m x) ->
  (forall i, (i < length nb)%nat -> (exists b, m' (wz (bv_unsigned a + Z.of_nat i)) = Some b /\ xb_bv ρ (nth i nb BT) b)
     \/ (m' (wz (bv_unsigned a + Z.of_nat i)) = m (wz (bv_unsigned a + Z.of_nat i)) /\ nth i nb BT = BT)) ->
  store_ok segs m a (length nb) = true /\ RMem segs ρ A' m'.
Proof.
  intros [Hok HR] Hv Hn1 Hn H Hfr Hby. unfold a_store in H.
  destruct (xaddr v) as [[ts o]|] eqn:Ea; [|discriminate].
  destruct (find_reg A ts o (of_Z (Z.of_nat (length nb))) 0) as [[[i R0] x]|] eqn:Ef; [|discriminate].
  destruct (rk_writable (rg_kind R0)) eqn:Ew; [|discriminate]. injection H as <-.
  destruct (find_reg_spec A ts o _ 0 i R0 x Ef) as [_ [Hi Hr]]. rewrite Nat.sub_0_r in Hi.
  pose proof (regions_ok_nth ρ A i R0 Hok Hi) as Hwf. pose proof (Forall_nth _ A i R0 HR Hi) as HRR.
  pose proof (roff_ne R0 ts o _ x Hr) as Hne0. rewrite (RRegion_ne segs ρ m R0 Hne0) in HRR.
  pose proof (xaddr_smod ρ v a ts o Hv Ea) as Hav.
  assert (Hlz : to_Z (of_Z (Z.of_nat (length nb))) = Z.of_nat (length nb)) by (apply phi_of_Z_small; lia).
  destruct (roff_addr ρ R0 ts o (of_Z (Z.of_nat (length nb))) x a ltac:(rewrite Hlz; lia) Hwf Hav Hr) as [Eaddr Hfit].
  rewrite Hlz in Hfit.
  pose proof Hwf as [Hw1 [H47 [Hd [Hd44 _]]]].
  pose proof (to_Z_bounded x) as Hxb. change wB with (2^63) in Hxb.
  pose proof (smod_range ρ (rg_ts R0) (rg_bo R0)) as Hsr. fold (rbase ρ R0) in Hsr.
  destruct (rwrite_fields segs nb R0 x) as [F1 [F2 [F3 [F4 F5]]]].
  assert (Ha : a = wz (rbase ρ R0 + to_Z x)) by (apply bv_eq; rewrite u_wz; [lia | unfold two64 in *; lia]).
  split; [rewrite Ha; apply (store_ok_range segs ρ); assumption|].
  split.
  - apply (regions_ok_replace ρ A i R0); [exact Hok | exact Hi | apply rbase_rwrite | exact F3 |].
    intros [W1 [W2 [W3 [W4 W5]]]]. unfold region_wf. rewrite rbase_rwrite, F3, F5, F4, F1. repeat split; assumption.
  - apply Forall_replace_nth'.
    + intros j Rj Hj Hne. pose proof (Forall_nth _ A j Rj HR Hj) as HRj.
      pose proof (regions_ok_disj ρ A i j R0 Rj Hok Hi Hj ltac:(lia)) as Hdis.
      pose proof (regions_ok_nth ρ A j Rj Hok Hj) as Wj. pose proof Wj as [Wj1 _].
      apply (RRegion_mframe ρ m _ Rj Wj); [|exact HRj].
      intros y Hy. apply Hfr. rewrite Eaddr.
      rewrite u_wz by (pose proof (smod_range ρ (rg_ts Rj) (rg_bo Rj)); unfold rbase in *; unfold two64 in *; lia).
      unfold rdisj in Hdis. lia.
    + rewrite (RRegion_ne segs ρ _ _ ltac:(unfold is_entry in *; rewrite F4; exact Hne0)).
      intros y Hy. rewrite F3 in Hy. rewrite rbase_rwrite. rewrite F4.
      pose proof (to_Z_bounded y). change wB with (2^63) in *.
      rewrite rbyte_rwrite by lia.
      destruct (HRR y Hy) as [[b [Hb Hab]] Hwv].
      assert (Hy64 : bv_unsigned (wz (rbase ρ R0 + to_Z y)) = rbase ρ R0 + to_Z y) by (apply u_wz; unfold two64 in *; lia).
      destruct ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length nb))) eqn:Ein.
      * apply andb_prop in Ein as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
        destruct (Hby (Z.to_nat (to_Z y - to_Z x)) ltac:(lia)) as [[b1 [Hb1 Hab1]]|[Eq1 EBT]];
          replace (bv_unsigned a + Z.of_nat (Z.to_nat (to_Z y - to_Z x))) with (rbase ρ R0 + to_Z y) in * by lia.
        -- split.
           ++ exists b1. unfold rv. rewrite Hb1. split; [reflexivity | exact Hab1].
           ++ intros _. unfold wview. rewrite Hb1. discriminate.
        -- rewrite EBT. split.
           ++ exists b. unfold rv in *. rewrite Eq1. split; [exact Hb | exact I].
           ++ intros Hwr. unfold wview in *. rewrite Eq1. apply Hwv. exact Hwr.
      * assert (Eq : m' (wz (rbase ρ R0 + to_Z y)) = m (wz (rbase ρ R0 + to_Z y))).
        { apply Hfr. rewrite Hy64, Eaddr. apply andb_false_iff in Ein as [E1|E1]; [apply Z.leb_gt in E1 | apply Z.ltb_ge in E1]; lia. }
        split.
        -- exists b. unfold rv in *. rewrite Eq. split; assumption.
        -- intros Hwr. unfold wview in *. rewrite Eq. apply Hwv. exact Hwr.
    + destruct (nth_error_Some A i) as [Hs _]. apply Hs. rewrite Hi. discriminate.
Qed.

(* [comment removed for export] *)
Lemma a_store_addr (ρ : valuation) (A A' : list region) (v : xv) (a : bv 64) (nb : list xb) :
  regions_ok ρ A -> xv_val ρ v a -> (1 <= length nb)%nat -> Z.of_nat (length nb) < 2 ^ 40 -> a_store segs A v nb = Some A' ->
  bv_unsigned a + Z.of_nat (length nb) <= two64.
Proof.
  intros Hok Hv Hn1 Hn H. unfold a_store in H.
  destruct (xaddr v) as [[ts o]|] eqn:Ea; [|discriminate].
  destruct (find_reg A ts o (of_Z (Z.of_nat (length nb))) 0) as [[[i R0] x]|] eqn:Ef; [|discriminate].
  destruct (find_reg_spec A ts o _ 0 i R0 x Ef) as [_ [Hi Hr]]. rewrite Nat.sub_0_r in Hi.
  pose proof (regions_ok_nth ρ A i R0 Hok Hi) as Hwf.
  assert (Hlz : to_Z (of_Z (Z.of_nat (length nb))) = Z.of_nat (length nb)) by (apply phi_of_Z_small; lia).
  destruct (roff_addr ρ R0 ts o (of_Z (Z.of_nat (length nb))) x a ltac:(rewrite Hlz; lia) Hwf (xaddr_smod ρ v a ts o Hv Ea) Hr) as [Eaddr Hfit].
  rewrite Hlz in Hfit. destruct Hwf as [W1 _]. lia.
Qed.

(* [comment removed for export] *)
Lemma a_store_sound (ρ : valuation) (A A' : list region) (m : word -> option byte) (v : xv) (a : bv 64) (nb : list xb) (bs : list byte) :
  RMem segs ρ A m -> xv_val ρ v a -> (1 <= length nb < 1000)%nat -> Forall2 (xb_bv ρ) nb bs ->
  a_store segs A v nb = Some A' ->
  store_ok segs m a (length nb) = true /\ RMem segs ρ A' (write_to_mem m a bs).
Proof.
  intros HM Hv Hn Hf H. pose proof (Forall2_length Hf) as Hlen.
  pose proof (a_store_addr ρ A A' v a nb (proj1 HM) Hv ltac:(lia) ltac:(lia) H) as H64.
  pose proof (bvu_range a) as Har.
  assert (Hwm : forall y : word, write_to_mem m a bs y =
            if (bv_unsigned a <=? bv_unsigned y) && (bv_unsigned y <? bv_unsigned a + Z.of_nat (length bs))
            then nth_error bs (Z.to_nat (bv_unsigned y - bv_unsigned a)) else m y).
  { intros y. replace a with (wz (bv_unsigned a)) at 1 by (apply bv_eq; rewrite u_wz; [reflexivity | unfold two64 in *; lia]).
    apply write_to_mem_spec; unfold two64 in *; lia. }
  apply (a_store_sound_gen ρ A A' m _ v a nb HM Hv); try lia; try exact H.
  - intros x Hx. rewrite Hwm. rewrite <- Hlen.
    replace ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + Z.of_nat (length nb))) with false; [reflexivity|].
    symmetry. apply Bool.not_true_iff_false. intros Hc. apply andb_prop in Hc as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
  - intros i Hi. left. destruct (Forall2_nth_error_ex _ nb bs i BT Hf Hi) as [b [Hb Hab]]. exists b. split; [|exact Hab].
    rewrite Hwm. rewrite u_wz by (unfold two64 in *; lia). rewrite <- Hlen.
    replace ((bv_unsigned a <=? bv_unsigned a + Z.of_nat i) && (bv_unsigned a + Z.of_nat i <? bv_unsigned a + Z.of_nat (length nb))) with true
      by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    replace (Z.to_nat (bv_unsigned a + Z.of_nat i - bv_unsigned a)) with i by lia. exact Hb.
Qed.

Lemma a_store_fields (A A' : list region) (v : xv) (nb : list xb) : a_store segs A v nb = Some A' -> Forall2 same_fields A A'.
Proof.
  unfold a_store. destruct (xaddr v) as [[ts o]|]; [|discriminate].
  destruct (find_reg A ts o (of_Z (Z.of_nat (length nb))) 0) as [[[i R0] x]|] eqn:Ef; [|discriminate].
  destruct (rk_writable (rg_kind R0)); [|discriminate]. intros H. injection H as <-.
  destruct (find_reg_spec A ts o _ 0 i R0 x Ef) as [_ [Hi _]]. rewrite Nat.sub_0_r in Hi.
  apply (Forall2_replace_nth same_fields A i R0); [intros X; repeat split | exact Hi | apply rwrite_fields].
Qed.

End StoreSound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma w_byte_lt (w : w64) (j : nat) : (j < 8)%nat -> (w_byte w j <? 256)%uint63 = true.
Proof. intros Hj. apply Uint63.ltb_spec. rewrite w_byte_spec by exact Hj. change (to_Z 256%uint63) with 256. apply zbyte_range. Qed.

Lemma w_bytes8 (w : w64) : ExLoad.w_of_bytes8 (map (w_byte w) (seq 0 8)) = w.
Proof.
  apply wZ_inj. rewrite ExLoad.w_of_bytes8_spec.
  - rewrite map_map. rewrite (map_ext_in _ (zbyte (wZ w))) by (intros i Hi; apply in_seq in Hi; apply w_byte_spec; lia).
    rewrite zcombine_bytes by (pose proof (wZ_range w); lia). apply Z.mod_small. exact (wZ_range w).
  - reflexivity.
  - apply Forall_forall. intros b Hb. apply in_map_iff in Hb as [i [<- Hi]]. apply in_seq in Hi.
    rewrite w_byte_spec by lia. apply zbyte_range.
Qed.

Definition wbytes (w : w64) : list xb := map (fun i => BL (w_byte w i)) (seq 0 8).

(* [comment removed for export] *)
Fixpoint fimg_bytes (c : PrimString.string) (x : int) (n : nat) : option (list int) :=
  match n with
  | O => Some []
  | S n' => match fimg_c c x, fimg_bytes c (x + 1)%uint63 n' with
            | Some b, Some l => Some (b :: l)
            | _, _ => None
            end
  end.

Lemma fimg_bytes_length (c : PrimString.string) (n : nat) : forall x l, fimg_bytes c x n = Some l -> length l = n.
Proof.
  induction n as [|n IH]; intros x l H; cbn [fimg_bytes] in H; [injection H as <-; reflexivity|].
  destruct (fimg_c c x); [|discriminate]. destruct (fimg_bytes c (x + 1)%uint63 n) as [l'|] eqn:E; [|discriminate].
  injection H as <-. cbn [length]. f_equal. exact (IH _ _ E).
Qed.

Lemma fimg_bytes_lt (c : PrimString.string) (n : nat) : forall x l, fimg_bytes c x n = Some l -> Forall (fun b => to_Z b < 256) l.
Proof.
  induction n as [|n IH]; intros x l H; cbn [fimg_bytes] in H; [injection H as <-; constructor|].
  destruct (fimg_c c x) as [b|] eqn:Eb; [|discriminate]. destruct (fimg_bytes c (x + 1)%uint63 n) as [l'|] eqn:E; [|discriminate].
  injection H as <-. constructor; [exact (proj2 (fimg_c_spec c x b Eb)) | exact (IH _ _ E)].
Qed.

(* [comment removed for export] *)
Lemma wbytes_of_bytes8 (l : list int) : length l = 8%nat -> Forall (fun b => to_Z b < 256) l -> wbytes (ExLoad.w_of_bytes8 l) = map BL l.
Proof.
  intros Hl Hb. unfold wbytes.
  assert (Hz : Forall (fun b => 0 <= b < 256) (map to_Z l)).
  { apply Forall_forall. intros z Hz. apply in_map_iff in Hz as [b [<- Hin]]. rewrite Forall_forall in Hb.
    pose proof (to_Z_bounded b). pose proof (Hb b Hin). lia. }
  assert (E : forall i, (i < 8)%nat -> w_byte (ExLoad.w_of_bytes8 l) i = nth i l 0%uint63).
  { intros i Hi. apply to_Z_inj. rewrite w_byte_spec by exact Hi. rewrite (ExLoad.w_of_bytes8_spec l Hl Hb).
    rewrite zbyte_zcombine by (try exact Hz; rewrite length_map; lia).
    change 0 with (to_Z 0%uint63). rewrite map_nth. reflexivity. }
  destruct l as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|]]]]]]]]]; try discriminate Hl.
  cbn [seq map]. rewrite !E by lia. reflexivity.
Qed.


Section Fast.
Variable segs : list Segment.

Definition img_word (i : nat) (x : int) : option w64 :=
  match nth_error segs i with
  | Some sg => match seg_bytes sg with
               | [c] => match fimg_bytes c x 8 with Some l => Some (ExLoad.w_of_bytes8 l) | None => None end
               | _ => None
               end
  | None => None
  end.

(* [comment removed for export] *)
Definition absent_word (R : region) (x : int) : option w64 :=
  match rg_kind R with
  | KZero | KShadow => Some w_zero
  | KImg _ i => img_word i x
  | _ => None
  end.

Lemma key_same (x y : int) : to_Z x mod 8 = 0 -> to_Z x <= to_Z y < to_Z x + 8 -> (y >> 3)%uint63 = (x >> 3)%uint63.
Proof.
  intros Hx Hy. apply to_Z_inj. rewrite !lsr_spec. change (2 ^ to_Z 3) with 8.
  pose proof (Z.div_mod (to_Z x) 8 ltac:(lia)) as D. rewrite Hx, Z.add_0_r in D.
  symmetry. apply Z.div_unique with (to_Z y - to_Z x); lia.
Qed.

Lemma rbytes_zero (R : region) (x : int) (n : nat) : forall y,
  (rg_kind R = KZero \/ rg_kind R = KShadow) -> to_Z x mod 8 = 0 -> to_Z x + 8 < wB -> get_cell_opt R (x >> 3)%uint63 = None ->
  to_Z x <= to_Z y -> to_Z y + Z.of_nat n <= to_Z x + 8 -> rbytes segs R y n = repeat (BL 0%uint63) n.
Proof.
  induction n as [|n IH]; intros y Hk Hx Hw Hc H1 H2; [reflexivity|]. cbn [rbytes repeat].
  assert (Hy1 : to_Z (y + 1)%uint63 = to_Z y + 1) by (rewrite add_spec; change (to_Z 1%uint63) with 1; apply Z.mod_small; pose proof (to_Z_bounded y); lia).
  f_equal; [|apply IH; try assumption; lia].
  unfold rbyte. rewrite (key_same x y Hx ltac:(lia)), Hc. unfold default_byte. destruct Hk as [-> | ->]; reflexivity.
Qed.

Lemma rbytes_img (R : region) (wr : bool) (i : nat) (sg : Segment) (c : PrimString.string) (x : int) (n : nat) : forall y l,
  rg_kind R = KImg wr i -> nth_error segs i = Some sg -> seg_bytes sg = [c] ->
  to_Z x mod 8 = 0 -> to_Z x + 8 < wB -> get_cell_opt R (x >> 3)%uint63 = None ->
  to_Z x <= to_Z y -> to_Z y + Z.of_nat n <= to_Z x + 8 -> fimg_bytes c y n = Some l -> rbytes segs R y n = map BL l.
Proof.
  induction n as [|n IH]; intros y l Hk Hs Hb Hx Hw Hc H1 H2 Hf; cbn [fimg_bytes] in Hf; [injection Hf as <-; reflexivity|].
  destruct (fimg_c c y) as [b|] eqn:Eb; [|discriminate]. destruct (fimg_bytes c (y + 1)%uint63 n) as [l'|] eqn:El; [|discriminate].
  injection Hf as <-. cbn [rbytes map].
  assert (Hy1 : to_Z (y + 1)%uint63 = to_Z y + 1) by (rewrite add_spec; change (to_Z 1%uint63) with 1; apply Z.mod_small; pose proof (to_Z_bounded y); lia).
  f_equal; [|apply (IH (y + 1)%uint63 l' Hk Hs Hb Hx Hw Hc); [lia | lia | exact El]].
  unfold rbyte. rewrite (key_same x y Hx ltac:(lia)), Hc. unfold default_byte. rewrite Hk. unfold fimg_i. rewrite Hs, Hb, Eb. reflexivity.
Qed.

Lemma rbytes_absent (R : region) (x : int) (w : w64) :
  to_Z x mod 8 = 0 -> to_Z x + 8 < wB -> get_cell_opt R (x >> 3)%uint63 = None -> absent_word R x = Some w ->
  rbytes segs R x 8 = wbytes w.
Proof.
  intros Hx Hw Hc H. unfold absent_word in H. destruct (rg_kind R) as [| | |wr i|ph] eqn:Ek; try discriminate.
  - injection H as <-. rewrite (rbytes_zero R x 8 x (or_introl Ek) Hx Hw Hc ltac:(lia) ltac:(lia)). reflexivity.
  - injection H as <-. rewrite (rbytes_zero R x 8 x (or_intror Ek) Hx Hw Hc ltac:(lia) ltac:(lia)). reflexivity.
  - unfold img_word in H. destruct (nth_error segs i) as [sg|] eqn:Es; [|discriminate].
    destruct (seg_bytes sg) as [|c [|c' r]] eqn:Eb; try discriminate.
    destruct (fimg_bytes c x 8) as [l|] eqn:El; [|discriminate]. injection H as <-.
    rewrite (rbytes_img R wr i sg c x 8 x l Ek Es Eb Hx Hw Hc ltac:(lia) ltac:(lia) El).
    symmetry. apply wbytes_of_bytes8; [exact (fimg_bytes_length c 8 x l El) | exact (fimg_bytes_lt c 8 x l El)].
Qed.


Definition a_loadw (A : list region) (v : xv) : option w64 :=
  match xaddr v with
  | Some (ts, o) =>
      match find_reg A ts o 8%uint63 0 with
      | Some (_, R, x) => if (x land 7 =? 0)%uint63 then match get_cell_opt R (x >> 3)%uint63 with Some (CW w) => Some w | Some _ => None | None => absent_word R x end else None
      | None => None
      end
  | None => None
  end.

Lemma a_loadw_load (A : list region) (v : xv) (w : w64) : a_loadw A v = Some w -> a_load segs A v 8 = Some (wbytes w).
Proof.
  unfold a_loadw, a_load. destruct (xaddr v) as [[ts o]|]; [|discriminate]. change (of_Z (Z.of_nat 8)) with 8%uint63.
  destruct (find_reg A ts o 8 0) as [[[i R] x]|] eqn:Ef; [|discriminate].
  destruct (eqbP (x land 7)%uint63 0%uint63) as [E|E]; [|discriminate]. apply to_Z_inj in E.
  destruct (get_cell_opt R (x >> 3)%uint63) as [[w'|l]|] eqn:Ec; try discriminate.
  - intros H. injection H as <-. unfold rbytes_fast. rewrite E, Ec. reflexivity.
  - intros H. unfold rbytes_fast. rewrite E, Ec. change (Nat.leb (i2n 0 + 8) 8) with true. cbv iota. f_equal.
    destruct (find_reg_spec A ts o 8 0 i R x Ef) as [_ [_ Hro]].
    destruct (roff_spec R ts o 8 x ltac:(reflexivity) Hro) as [_ [_ [_ Hx8]]]. change (to_Z 8) with 8 in Hx8.
    pose proof (to_Z_bounded (rg_n R)) as Hn. apply (rbytes_absent R x w); [| lia | exact Ec | exact H].
    rewrite <- phi_land7, E. reflexivity.
Qed.

Definition a_storew (A : list region) (v : xv) (w : w64) : option (list region) :=
  match xaddr v with
  | Some (ts, o) =>
      match find_reg A ts o 8%uint63 0 with
      | Some (i, R, x) => if rk_writable (rg_kind R) &&& (x land 7 =? 0)%uint63
                          then Some (replace_nth A i (with_cells R (iset (rg_d R) (rg_cells R) (x >> 3)%uint63 (CW w)))) else None
      | None => None
      end
  | None => None
  end.

Lemma a_storew_store (A A' : list region) (v : xv) (w : w64) : a_storew A v w = Some A' -> a_store segs A v (wbytes w) = Some A'.
Proof.
  unfold a_storew, a_store. destruct (xaddr v) as [[ts o]|]; [|discriminate].
  change (of_Z (Z.of_nat (length (wbytes w)))) with 8%uint63.
  destruct (find_reg A ts o 8 0) as [[[i R] x]|]; [|discriminate].
  destruct (rk_writable (rg_kind R)); [|discriminate]. cbn [andb].
  destruct (eqbP (x land 7)%uint63 0%uint63) as [E|E]; [|discriminate]. apply to_Z_inj in E. intros H. injection H as <-.
  do 2 f_equal. unfold rwrite. rewrite E. change (Nat.leb (i2n 0 + length (wbytes w)) 8) with true. cbv iota.
  unfold rwrite1. rewrite E. f_equal. f_equal.
  unfold cell_write. change (i2n 0) with 0%nat. cbn [wbytes map seq length Nat.add Nat.leb Nat.ltb Nat.sub nth].
  unfold norm_cell, lit8. cbn [lits]. rewrite !w_byte_lt by lia. cbn [length Nat.eqb]. f_equal. exact (w_bytes8 w).
Qed.

(* [comment removed for export] *)
Definition cw_set (w0 w : w64) (j n : nat) : w64 :=
  ExLoad.w_of_bytes8 (map (fun t => if Nat.leb j t && Nat.ltb t (j + n) then w_byte w (t - j) else w_byte w0 t) (seq 0 8)).

Definition old_word (R : region) (k : int) : option w64 :=
  match get_cell_opt R k with
  | Some (CW w0) => Some w0
  | Some _ => None
  | None => match rg_kind R with KZero | KShadow => Some w_zero | _ => None end
  end.

Definition a_storek (A : list region) (v : xv) (n : nat) (w : w64) : option (list region) :=
  match xaddr v with
  | Some (ts, o) =>
      match find_reg A ts o (of_Z (Z.of_nat n)) 0 with
      | Some (i, R, x) =>
          let j := i2n (x land 7)%uint63 in
          if rk_writable (rg_kind R) &&& Nat.leb (j + n) 8 then
            match old_word R (x >> 3)%uint63 with
            | Some w0 => Some (replace_nth A i (with_cells R (iset (rg_d R) (rg_cells R) (x >> 3)%uint63 (CW (cw_set w0 w j n)))))
            | None => None
            end
          else None
      | None => None
      end
  | None => None
  end.

Lemma w_byte_ltZ (w : w64) (t : nat) : (t < 8)%nat -> to_Z (w_byte w t) < 256.
Proof. intros Ht. rewrite w_byte_spec by exact Ht. pose proof (zbyte_range (wZ w) t). lia. Qed.

Lemma lits_map_BL (bs : list int) : Forall (fun b => to_Z b < 256) bs -> lits (map BL bs) = Some bs.
Proof.
  induction 1 as [|b r Hb Hr IH]; [reflexivity|]. cbn [map lits].
  destruct (ltbP b 256) as [_|N]; [|exfalso; apply N; exact Hb]. rewrite IH. reflexivity.
Qed.

Lemma old_word_cell (R : region) (k : int) (w0 : w64) : old_word R k = Some w0 -> cell_of segs R k = CW w0.
Proof.
  unfold old_word, cell_of. destruct (get_cell_opt R k) as [[w'|l]|]; try discriminate.
  - intros H. injection H as <-. reflexivity.
  - destruct (rg_kind R); try discriminate; intros H; injection H as <-; reflexivity.
Qed.

Lemma cw_write_lit (w0 w : w64) (j n : nat) : (j + n <= 8)%nat ->
  norm_cell (cell_write (CW w0) j (map (fun i => BL (w_byte w i)) (seq 0 n))) = CW (cw_set w0 w j n).
Proof.
  intros Hjn. unfold cell_write, cw_set. rewrite length_map, length_seq.
  set (G := fun t => if Nat.leb j t && Nat.ltb t (j + n) then w_byte w (t - j) else w_byte w0 t).
  assert (EL : map (fun t => if Nat.leb j t then if Nat.ltb t (j + n) then nth (t - j) (map (fun i => BL (w_byte w i)) (seq 0 n)) BT else cbyte (CW w0) t else cbyte (CW w0) t) (seq 0 8)
               = map BL (map G (seq 0 8))).
  { rewrite map_map. apply map_ext_in. intros t Ht. apply in_seq in Ht. unfold G. cbn [cbyte].
    destruct (Nat.leb_spec j t) as [L1|L1]; [|reflexivity]. destruct (Nat.ltb_spec t (j + n)) as [L2|L2]; [|reflexivity]. cbn [andb].
    rewrite (nth_indep _ BT (BL (w_byte w 0))) by (rewrite length_map, length_seq; lia).
    rewrite (map_nth (fun i => BL (w_byte w i)) (seq 0 n) 0%nat). rewrite seq_nth by lia. reflexivity. }
  rewrite EL. cbn [norm_cell]. unfold lit8.
  rewrite lits_map_BL.
  - rewrite length_map, length_seq. reflexivity.
  - apply Forall_forall. intros b Hb. apply in_map_iff in Hb as [t [<- Ht]]. apply in_seq in Ht. unfold G.
    destruct (Nat.leb j t && Nat.ltb t (j + n)); apply w_byte_ltZ; lia.
Qed.

Lemma a_storek_store (A A' : list region) (v : xv) (n : nat) (w : w64) : (1 <= n <= 8)%nat ->
  a_storek A v n w = Some A' -> a_store segs A v (map (fun i => BL (w_byte w i)) (seq 0 n)) = Some A'.
Proof.
  intros Hn. unfold a_storek, a_store. destruct (xaddr v) as [[ts o]|]; [|discriminate].
  rewrite length_map, length_seq.
  destruct (find_reg A ts o (of_Z (Z.of_nat n)) 0) as [[[i R] x]|]; [|discriminate]. cbv zeta.
  destruct (rk_writable (rg_kind R)); [|discriminate].
  destruct (Nat.leb_spec (i2n (x land 7)%uint63 + n) 8) as [Hj|Hj]; [|discriminate].
  destruct (old_word R (x >> 3)%uint63) as [w0|] eqn:Eo; [|discriminate].
  intros H. injection H as <-. f_equal. f_equal.
  unfold rwrite. rewrite length_map, length_seq.
  destruct (Nat.leb_spec (i2n (x land 7)%uint63 + n) 8) as [_|N]; [|lia].
  unfold rwrite1. rewrite (old_word_cell R _ w0 Eo). rewrite cw_write_lit by lia. reflexivity.
Qed.


End Fast.
