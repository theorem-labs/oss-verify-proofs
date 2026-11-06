(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec FastWord FastWordSem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie ExLin ExVal ExBytes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive abyte : Type :=
| BL (b : int)               (* [comment removed for export] *)
| BT                         (* [comment removed for export] *)
| BF (v : aval) (i : nat).   (* [comment removed for export] *)

Definition abyte_val (ρ : valuation) (ab : abyte) (b : byte) : Prop :=
  match ab with
  | BL x => bv_unsigned b = to_Z x
  | BT => True
  | BF v i => exists w : bv 64, aval_val ρ v w /\ bv_unsigned b = zbyte (bv_unsigned w) i
  end.

(* [comment removed for export] *)
Inductive cell : Type :=
| CW (w : w64)
| CB (l : list abyte).

Definition cbyte (c : cell) (i : nat) : abyte :=
  match c with
  | CW w => BL (w_byte w i)
  | CB l => nth i l BT
  end.

Definition zero_cell : cell := CW w_zero.
Definition unk_cell : cell := CB (repeat BT 8).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive rkind : Type :=
| KZero               (* [comment removed for export] *)
| KUnk                (* [comment removed for export] *)
| KImg (w : bool)     (* [comment removed for export] *)
| KZL (l : list (int * int)) (* [comment removed for export] *)
| KWin (f : lin).              (* [comment removed for export] *)

Record region : Type := Rg {
  rg_lo : int;              (* [comment removed for export] *)
  rg_hi : int;              (* [comment removed for export] *)
  rg_kind : rkind;
  rg_d : nat;               (* [comment removed for export] *)
  rg_cells : itrie cell
}.

Definition rk_writable (k : rkind) : bool :=
  match k with KZero | KUnk | KZL _ | KWin _ => true | KImg w => w end.

Definition is_win (k : rkind) : bool := match k with KWin _ => true | _ => false end.

(* [comment removed for export] *)
Definition inl (l : list (int * int)) (a : Z) : bool := existsb (fun p => (to_Z (fst p) <=? a) && (a <? to_Z (snd p))) l.

Section WithSegs.
Variable segs : list Segment.

Definition wz (a : Z) : word := Z_to_bv 64 a.

(* [comment removed for export] *)
Definition img_byte (a : Z) : abyte :=
  match seg_rom segs (wz a) with Some b => BL (of_Z (bv_unsigned b)) | None => BT end.

Definition default_byte (k : rkind) (a : Z) : abyte :=
  match k with
  | KZero => BL 0%uint63
  | KUnk => BT
  | KImg _ => img_byte a
  | KZL l => if inl l a then BT else BL 0%uint63
  | KWin _ => BT
  end.

(* [comment removed for export] *)
Definition default_cell (k : rkind) (a : Z) : cell :=
  match k with
  | KZero => zero_cell
  | KUnk => unk_cell
  | KImg _ => CB (map (fun i => img_byte (a + Z.of_nat i)) (seq 0 8))
  | KZL l => if existsb (fun p => (a <? to_Z (snd p)) && (to_Z (fst p) <? a + 8)) l
             then CB (map (fun i => if inl l (a + Z.of_nat i) then BT else BL 0%uint63) (seq 0 8)) else zero_cell
  | KWin _ => unk_cell
  end.

Definition cell_key (R : region) (x : int) : int := ((x - rg_lo R) >> 3)%uint63.
(* [comment removed for export] *)
Definition int8_nat (i : int) : nat :=
  if (i =? 0)%uint63 then 0%nat else if (i =? 1)%uint63 then 1%nat else if (i =? 2)%uint63 then 2%nat
  else if (i =? 3)%uint63 then 3%nat else if (i =? 4)%uint63 then 4%nat else if (i =? 5)%uint63 then 5%nat
  else if (i =? 6)%uint63 then 6%nat else 7%nat.
Definition cell_off (R : region) (x : int) : nat := int8_nat ((x - rg_lo R) land 7)%uint63.

Definition in_region (R : region) (x : int) : bool := (rg_lo R <=? x)%uint63 && (x <? rg_hi R)%uint63.

Definition get_cell (R : region) (k : int) : cell :=
  match iget (rg_d R) (rg_cells R) k with
  | Some c => c
  | None => default_cell (rg_kind R) (to_Z (rg_lo R) + 8 * to_Z k)
  end.

(* [comment removed for export] *)
Definition rbyte (R : region) (x : int) : abyte :=
  cbyte (get_cell R (cell_key R x)) (cell_off R x).

(* [comment removed for export] *)
Fixpoint aview (A : list region) (x : int) : option (abyte * bool) :=
  match A with
  | [] => None
  | R :: A' => if in_region R x then (if is_win (rg_kind R) then None else Some (rbyte R x, rk_writable (rg_kind R))) else aview A' x
  end.

(* [comment removed for export] *)
Definition rv (m : word -> option byte) (a : word) : option byte :=
  match m a with Some b => Some b | None => seg_rom segs a end.

(* [comment removed for export] *)
Definition region_wf (R : region) : Prop :=
  0 <= to_Z (rg_lo R) /\ to_Z (rg_lo R) <= to_Z (rg_hi R) /\ to_Z (rg_hi R) < 2 ^ 47
  /\ to_Z (rg_lo R) mod 8 = 0 /\ to_Z (rg_hi R) - to_Z (rg_lo R) <= 8 * 2 ^ Z.of_nat (rg_d R)
  /\ (rg_d R <= 44)%nat.

Definition rdisj (R1 R2 : region) : Prop :=
  to_Z (rg_hi R1) <= to_Z (rg_lo R2) \/ to_Z (rg_hi R2) <= to_Z (rg_lo R1).

Fixpoint regions_ok (A : list region) : Prop :=
  match A with
  | [] => True
  | R :: A' => region_wf R /\ Forall (rdisj R) A' /\ regions_ok A'
  end.

(* [comment removed for export] *)
Definition RWin (ρ : valuation) (A : list region) (m : word -> option byte) : Prop :=
  forall R f, In R A -> rg_kind R = KWin f ->
    forall x : Z, to_Z (rg_lo R) <= x < to_Z (rg_hi R) -> x < to_Z (rg_lo R) + leval ρ f -> m (wz x) <> None.

Definition RMem (ρ : valuation) (A : list region) (m : word -> option byte) : Prop :=
  regions_ok A /\
  (forall (x : int) (ab : abyte) (w : bool), aview A x = Some (ab, w) ->
    (exists b, rv m (wz (to_Z x)) = Some b /\ abyte_val ρ ab b)
    /\ (w = true -> wview segs m (wz (to_Z x)) <> None))
  /\ RWin ρ A m.

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

Lemma nth_map_seq0 {A : Type} (f : nat -> A) (n i : nat) (d : A) : (i < n)%nat -> nth i (map f (seq 0 n)) d = f i.
Proof.
  intros H. rewrite nth_indep with (d' := f 0%nat) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma phi_of_Z_small (z : Z) : 0 <= z < 2 ^ 63 -> to_Z (of_Z z) = z.
Proof. intros H. rewrite of_Z_spec. apply Z.mod_small. change wB with (2^63). exact H. Qed.

Lemma int_add_nat (x : int) (i : nat) : to_Z x + Z.of_nat i < 2 ^ 47 ->
  to_Z (x + of_Z (Z.of_nat i))%uint63 = to_Z x + Z.of_nat i.
Proof.
  intros H. pose proof (to_Z_bounded x). change wB with (2^63) in *.
  rewrite phi_add_small; rewrite phi_of_Z_small; lia.
Qed.

Lemma int_add_1 (x : int) : to_Z x + 1 < 2 ^ 63 -> to_Z (x + 1)%uint63 = to_Z x + 1.
Proof. intros H. pose proof (to_Z_bounded x). change wB with (2^63) in *. rewrite phi_add_small; change (to_Z 1%uint63) with 1; lia. Qed.

Lemma phi_land7 (x : int) : to_Z (x land 7)%uint63 = to_Z x mod 8.
Proof. rewrite land_spec'. change (to_Z 7%uint63) with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma int8_nat_spec (i : int) : to_Z i < 8 -> int8_nat i = Z.to_nat (to_Z i).
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

Lemma cell_off_spec (R : region) (x : int) : cell_off R x = Z.to_nat (to_Z ((x - rg_lo R) land 7)%uint63).
Proof.
  unfold cell_off. apply int8_nat_spec. rewrite phi_land7. pose proof (Z.mod_pos_bound (to_Z (x - rg_lo R)%uint63) 8 ltac:(lia)). lia.
Qed.

Lemma phi_lsr3 (x : int) : to_Z (x >> 3)%uint63 = to_Z x / 8.
Proof. rewrite lsr_spec. reflexivity. Qed.

Lemma in_region_spec (R : region) (x : int) :
  in_region R x = true <-> to_Z (rg_lo R) <= to_Z x < to_Z (rg_hi R).
Proof.
  unfold in_region. destruct (lebP (rg_lo R) x), (ltbP x (rg_hi R)); cbn; split; intros; try lia; try discriminate; reflexivity.
Qed.

Lemma in_region_false (R : region) (x : int) :
  in_region R x = false <-> ~ (to_Z (rg_lo R) <= to_Z x < to_Z (rg_hi R)).
Proof.
  split; intros H.
  - intros C. apply in_region_spec in C. congruence.
  - destruct (in_region R x) eqn:E; [|reflexivity]. apply in_region_spec in E. contradiction.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Reads.
Variable segs : list Segment.

Fixpoint find_region (A : list region) (x : int) (n : int) : option region :=
  match A with
  | [] => None
  | R :: A' => if (rg_lo R <=? x)%uint63 && (x + n <=? rg_hi R)%uint63 && negb (is_win (rg_kind R)) then Some R else find_region A' x n
  end.

(* [comment removed for export] *)
Fixpoint rbytes (R : region) (x : int) (n : nat) : list abyte :=
  match n with
  | O => []
  | S n' => rbyte segs R x :: rbytes R (x + 1)%uint63 n'
  end.

(* [comment removed for export] *)
Definition rbytes_fast (R : region) (x : int) (n : nat) : list abyte :=
  let o := cell_off R x in
  if Nat.leb (o + n) 8 then (let c := get_cell segs R (cell_key R x) in map (fun i => cbyte c (o + i)) (seq 0 n))
  else rbytes R x n.

(* [comment removed for export] *)
Definition a_bytes (A : list region) (x : int) (n : nat) : option (list abyte * bool) :=
  match find_region A x (of_Z (Z.of_nat n)) with
  | Some R => Some (rbytes_fast R x n, rk_writable (rg_kind R))
  | None => None
  end.

End Reads.

Lemma wz_succ (a : Z) : (wz a + 1)%bv = wz (a + 1).
Proof.
  unfold wz. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. change (bv_unsigned (1 : bv 64)) with 1.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma u_wz (a : Z) : 0 <= a < 2 ^ 64 -> bv_unsigned (wz a) = a.
Proof. intros H. unfold wz. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. exact H. Qed.

Section ReadLemmas.
Variable segs : list Segment.

Lemma find_region_in (A : list region) (x n : int) (R : region) :
  find_region A x n = Some R -> In R A /\ to_Z (rg_lo R) <= to_Z x /\ to_Z (x + n)%uint63 <= to_Z (rg_hi R).
Proof.
  induction A as [|R0 A' IH]; cbn [find_region]; [discriminate|].
  destruct ((rg_lo R0 <=? x)%uint63 && (x + n <=? rg_hi R0)%uint63 && negb (is_win (rg_kind R0))) eqn:E.
  - intros H. injection H as <-. apply andb_prop in E as [E _]. apply andb_prop in E as [E1 E2]. apply leb_spec in E1.
    apply leb_spec in E2. split; [left; reflexivity | lia].
  - intros H. destruct (IH H) as [Hi Hb]. split; [right; exact Hi | exact Hb].
Qed.

Lemma find_region_nowin (A : list region) (x n : int) (R : region) :
  find_region A x n = Some R -> is_win (rg_kind R) = false.
Proof.
  induction A as [|R0 A' IH]; cbn [find_region]; [discriminate|].
  destruct ((rg_lo R0 <=? x)%uint63 && (x + n <=? rg_hi R0)%uint63 && negb (is_win (rg_kind R0))) eqn:E.
  - intros H. injection H as <-. apply andb_prop in E as [_ E]. apply negb_true_iff in E. exact E.
  - exact IH.
Qed.

(* [comment removed for export] *)
Lemma find_region_view (A : list region) (x n : int) (R : region) (y : int) :
  regions_ok A -> find_region A x n = Some R ->
  to_Z (rg_lo R) <= to_Z y < to_Z (rg_hi R) ->
  aview segs A y = Some (rbyte segs R y, rk_writable (rg_kind R)).
Proof.
  intros Hok0 H0 Hy0. pose proof (find_region_nowin A x n R H0) as Hnw. revert Hok0 H0 Hy0.
  induction A as [|R0 A' IH]; cbn [find_region regions_ok aview]; [discriminate|].
  intros [Hwf [Hdis Hok]] H Hy.
  destruct ((rg_lo R0 <=? x)%uint63 && (x + n <=? rg_hi R0)%uint63 && negb (is_win (rg_kind R0))) eqn:E.
  - injection H as <-. rewrite (proj2 (in_region_spec R0 y) Hy). rewrite Hnw. reflexivity.
  - destruct (find_region_in A' x n R H) as [Hi _].
    assert (Hd : rdisj R0 R) by (rewrite Forall_forall in Hdis; apply Hdis; exact Hi).
    rewrite (proj2 (in_region_false R0 y)).
    + apply IH; assumption.
    + unfold rdisj in Hd. lia.
Qed.

Lemma rbytes_length (R : region) (x : int) (n : nat) : length (rbytes segs R x n) = n.
Proof. revert x; induction n as [|n IH]; intros x; cbn [rbytes length]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma rbytes_nth (R : region) (x : int) (n : nat) (i : nat) :
  to_Z x + Z.of_nat n < 2 ^ 47 -> (i < n)%nat ->
  nth i (rbytes segs R x n) BT = rbyte segs R (x + of_Z (Z.of_nat i))%uint63.
Proof.
  revert x i; induction n as [|n IH]; intros x i Hx Hi; [lia|].
  pose proof (to_Z_bounded x).
  destruct i as [|i]; cbn [rbytes nth].
  - f_equal. apply to_Z_inj. rewrite int_add_nat by lia. lia.
  - rewrite IH by (try lia; rewrite int_add_1; lia).
    f_equal. apply to_Z_inj. rewrite int_add_nat by (rewrite ?int_add_1; lia). rewrite int_add_1 by lia.
    rewrite int_add_nat by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma rbytes_fast_eq (R : region) (x : int) (n : nat) :
  to_Z (rg_lo R) <= to_Z x -> to_Z x + Z.of_nat n < 2 ^ 47 ->
  rbytes_fast segs R x n = rbytes segs R x n.
Proof.
  intros Hlo Hx. unfold rbytes_fast. destruct (Nat.leb_spec (cell_off R x + n) 8) as [Hc|Hc]; [|reflexivity].
  apply nth_ext with (d := BT) (d' := BT).
  - rewrite rbytes_length, length_map, length_seq. reflexivity.
  - intros i Hi. rewrite length_map, length_seq in Hi. rewrite rbytes_nth by lia.
    rewrite (nth_map_seq0 (fun i0 => cbyte (get_cell segs R (cell_key R x)) (cell_off R x + i0)) n i BT Hi).
    unfold rbyte. pose proof (to_Z_bounded x) as Hb.
    assert (Hxi : to_Z (x + of_Z (Z.of_nat i))%uint63 = to_Z x + Z.of_nat i) by (apply int_add_nat; lia).
    unfold cell_key in *. rewrite ?cell_off_spec in *. rewrite !phi_land7 in *.
    rewrite !phi_sub_small in * by lia. rewrite Hxi in *.
    assert (Hdm : (to_Z x - to_Z (rg_lo R)) = 8 * ((to_Z x - to_Z (rg_lo R)) / 8) + (to_Z x - to_Z (rg_lo R)) mod 8)
      by (apply Z.div_mod; lia).
    pose proof (Z.mod_pos_bound (to_Z x - to_Z (rg_lo R)) 8 ltac:(lia)) as Hm.
    assert (E1 : (to_Z x + Z.of_nat i - to_Z (rg_lo R)) mod 8 = (to_Z x - to_Z (rg_lo R)) mod 8 + Z.of_nat i).
    { replace (to_Z x + Z.of_nat i - to_Z (rg_lo R)) with (((to_Z x - to_Z (rg_lo R)) mod 8 + Z.of_nat i) + ((to_Z x - to_Z (rg_lo R)) / 8) * 8) by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    assert (E2 : (to_Z x + Z.of_nat i - to_Z (rg_lo R)) / 8 = (to_Z x - to_Z (rg_lo R)) / 8).
    { replace (to_Z x + Z.of_nat i - to_Z (rg_lo R)) with (((to_Z x - to_Z (rg_lo R)) mod 8 + Z.of_nat i) + ((to_Z x - to_Z (rg_lo R)) / 8) * 8) by lia.
      rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
    assert (Ek : ((x + of_Z (Z.of_nat i) - rg_lo R) >> 3)%uint63 = ((x - rg_lo R) >> 3)%uint63).
    { apply to_Z_inj. rewrite !phi_lsr3, !phi_sub_small by lia. rewrite Hxi, E2. reflexivity. }
    rewrite Ek. f_equal. rewrite E1. lia.
Qed.

(* [comment removed for export] *)
Lemma a_bytes_spec (A : list region) (x : int) (n : nat) (l : list abyte) (w : bool) :
  regions_ok A -> (n < 1000)%nat -> to_Z x + Z.of_nat n < 2 ^ 47 ->
  a_bytes segs A x n = Some (l, w) ->
  length l = n /\ forall i, (i < n)%nat -> aview segs A (x + of_Z (Z.of_nat i))%uint63 = Some (nth i l BT, w).
Proof.
  intros Hok Hn Hx H. unfold a_bytes in H. destruct (find_region A x (of_Z (Z.of_nat n))) as [R|] eqn:Ef; [|discriminate].
  injection H as <- <-. destruct (find_region_in A x _ R Ef) as [Hin [Hlo Hhi]].
  rewrite phi_add_small in Hhi by (rewrite phi_of_nat_small by lia; pose proof (to_Z_bounded x); lia).
  rewrite phi_of_nat_small in Hhi by lia.
  rewrite rbytes_fast_eq by lia. split; [apply rbytes_length|].
  intros i Hi. rewrite rbytes_nth by lia.
  apply (find_region_view A x (of_Z (Z.of_nat n)) R); [exact Hok | exact Ef |].
  rewrite phi_add_small by (rewrite phi_of_nat_small by lia; pose proof (to_Z_bounded x); lia).
  rewrite phi_of_nat_small by lia. lia.
Qed.

End ReadLemmas.

Section LoadStore.
Variable segs : list Segment.

Lemma rdn_cons' (m : word -> option byte) (a : word) (n : nat) :
  rdn segs m a (S n) = match rv segs m a with
                       | Some b => match rdn segs m (a + 1)%bv n with Some r => Some (b :: r) | None => None end
                       | None => None
                       end.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma a_bytes_rdn (ρ : valuation) (A : list region) (m : word -> option byte) (x : int) (n : nat) (l : list abyte) (w : bool) :
  RMem segs ρ A m -> (n < 1000)%nat -> to_Z x + Z.of_nat n < 2 ^ 47 ->
  a_bytes segs A x n = Some (l, w) ->
  exists bs, rdn segs m (wz (to_Z x)) n = Some bs /\ Forall2 (abyte_val ρ) l bs.
Proof.
  intros [Hok [Hm HwR]] Hn Hx H. destruct (a_bytes_spec segs A x n l w Hok Hn Hx H) as [Hlen Hv].
  clear H. revert x l Hx Hlen Hv. induction n as [|n IH]; intros x l Hx Hlen Hv.
  - destruct l; [|discriminate]. exists []. split; [reflexivity | constructor].
  - destruct l as [|ab l]; [discriminate|]. cbn [length] in Hlen. injection Hlen as Hlen.
    pose proof (to_Z_bounded x).
    assert (H0 : aview segs A x = Some (ab, w)).
    { specialize (Hv 0%nat ltac:(lia)). cbn [nth] in Hv. replace (x + of_Z (Z.of_nat 0))%uint63 with x in Hv; [exact Hv|].
      apply to_Z_inj. rewrite int_add_nat by lia. lia. }
    destruct (Hm x ab w H0) as [[b [Hb Hab]] _].
    destruct (IH ltac:(lia) (x + 1)%uint63 l) as [bs [Hr Hf]].
    + rewrite int_add_1 by lia. lia.
    + exact Hlen.
    + intros i Hi. specialize (Hv (S i) ltac:(lia)). cbn [nth] in Hv. rewrite <- Hv. f_equal.
      apply to_Z_inj. rewrite int_add_nat by (rewrite ?int_add_1; lia). rewrite int_add_1 by lia.
      rewrite int_add_nat by lia. lia.
    + exists (b :: bs). split; [|constructor; assumption].
      rewrite rdn_cons'. rewrite Hb. rewrite wz_succ. rewrite int_add_1 in Hr by lia. rewrite Hr. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma a_bytes_store_ok (ρ : valuation) (A : list region) (m : word -> option byte) (x : int) (n : nat) (l : list abyte) :
  RMem segs ρ A m -> (n < 1000)%nat -> to_Z x + Z.of_nat n < 2 ^ 47 ->
  a_bytes segs A x n = Some (l, true) ->
  store_ok segs m (wz (to_Z x)) n = true.
Proof.
  intros [Hok [Hm HwR]] Hn Hx H. destruct (a_bytes_spec segs A x n l true Hok Hn Hx H) as [Hlen Hv].
  clear H. revert x l Hx Hlen Hv. induction n as [|n IH]; intros x l Hx Hlen Hv; [reflexivity|].
  destruct l as [|ab l]; [discriminate|]. cbn [length] in Hlen. injection Hlen as Hlen.
  pose proof (to_Z_bounded x).
  assert (H0 : aview segs A x = Some (ab, true)).
  { specialize (Hv 0%nat ltac:(lia)). cbn [nth] in Hv. replace (x + of_Z (Z.of_nat 0))%uint63 with x in Hv; [exact Hv|].
    apply to_Z_inj. rewrite int_add_nat by lia. lia. }
  destruct (Hm x ab true H0) as [_ Hw]. specialize (Hw eq_refl).
  cbn [store_ok]. destruct (wview segs m (wz (to_Z x))) eqn:Ew; [|congruence].
  rewrite wz_succ. rewrite <- (int_add_1 x) by lia.
  apply (IH ltac:(lia) (x + 1)%uint63 l).
  - rewrite int_add_1 by lia. lia.
  - exact Hlen.
  - intros i Hi. specialize (Hv (S i) ltac:(lia)). cbn [nth] in Hv. rewrite <- Hv. f_equal.
    apply to_Z_inj. rewrite int_add_nat by (rewrite ?int_add_1; lia). rewrite int_add_1 by lia.
    rewrite int_add_nat by lia. lia.
Qed.

End LoadStore.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Stores.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition cell_write (c : cell) (o : nat) (nb : list abyte) : cell :=
  CB (map (fun j => if Nat.leb o j && Nat.ltb j (o + length nb) then nth (j - o) nb BT else cbyte c j) (seq 0 8)).

Lemma cell_write_nth (c : cell) (o : nat) (nb : list abyte) (j : nat) : (j < 8)%nat ->
  cbyte (cell_write c o nb) j = if Nat.leb o j && Nat.ltb j (o + length nb) then nth (j - o) nb BT else cbyte c j.
Proof. intros Hj. unfold cell_write, cbyte at 1. apply (nth_map_seq0 (fun j0 => _) 8 j BT Hj). Qed.

Definition reg_with_cells (R : region) (t : itrie cell) : region :=
  Rg (rg_lo R) (rg_hi R) (rg_kind R) (rg_d R) t.

(* [comment removed for export] *)
Definition rwrite (R : region) (x : int) (nb : list abyte) : region :=
  let k := cell_key R x in
  reg_with_cells R (iset (rg_d R) (rg_cells R) k (cell_write (get_cell segs R k) (cell_off R x) nb)).

(* [comment removed for export] *)
Fixpoint rwrite_each (R : region) (x : int) (nb : list abyte) : region :=
  match nb with
  | [] => R
  | b :: nb' => rwrite_each (rwrite R x [b]) (x + 1)%uint63 nb'
  end.

Definition rwrite_all (R : region) (x : int) (nb : list abyte) : region :=
  if Nat.leb (cell_off R x + length nb) 8 then rwrite R x nb else rwrite_each R x nb.

Fixpoint replace_nth (A : list region) (i : nat) (R' : region) : list region :=
  match A, i with
  | [], _ => []
  | _ :: A', O => R' :: A'
  | R0 :: A', S i' => R0 :: replace_nth A' i' R'
  end.

(* [comment removed for export] *)
Fixpoint find_region_i (A : list region) (x n : int) (i : nat) : option (nat * region) :=
  match A with
  | [] => None
  | R :: A' => if (rg_lo R <=? x)%uint63 && (x + n <=? rg_hi R)%uint63 && negb (is_win (rg_kind R)) then Some (i, R) else find_region_i A' x n (S i)
  end.

(* [comment removed for export] *)
Definition a_store (A : list region) (x : int) (nb : list abyte) : option (list region) :=
  match find_region_i A x (of_Z (Z.of_nat (length nb))) 0 with
  | Some (i, R) => if rk_writable (rg_kind R) then Some (replace_nth A i (rwrite_all R x nb)) else None
  | None => None
  end.

End Stores.

Section StoreLemmas.
Variable segs : list Segment.

Lemma key_lt (R : region) (y : int) :
  region_wf R -> to_Z (rg_lo R) <= to_Z y < to_Z (rg_hi R) ->
  0 <= to_Z (cell_key R y) < 2 ^ Z.of_nat (rg_d R).
Proof.
  intros [H1 [H2 [H3 [H4 [H5 H6]]]]] Hy. unfold cell_key. rewrite phi_lsr3, phi_sub_small by lia.
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma key_eq_iff (R : region) (x y : int) :
  region_wf R -> to_Z (rg_lo R) <= to_Z x < to_Z (rg_hi R) -> to_Z (rg_lo R) <= to_Z y < to_Z (rg_hi R) ->
  (to_Z (cell_key R x) mod 2 ^ Z.of_nat (rg_d R) =? to_Z (cell_key R y) mod 2 ^ Z.of_nat (rg_d R))
  = (to_Z (cell_key R x) =? to_Z (cell_key R y)).
Proof.
  intros Hwf Hx Hy. pose proof (key_lt R x Hwf Hx). pose proof (key_lt R y Hwf Hy).
  rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma cell_addr (R : region) (y : int) :
  to_Z (rg_lo R) <= to_Z y ->
  to_Z y = to_Z (rg_lo R) + 8 * to_Z (cell_key R y) + Z.of_nat (cell_off R y) /\ (cell_off R y < 8)%nat.
Proof.
  intros H. unfold cell_key. rewrite cell_off_spec. rewrite phi_lsr3, phi_land7, phi_sub_small by lia.
  pose proof (Z.div_mod (to_Z y - to_Z (rg_lo R)) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (to_Z y - to_Z (rg_lo R)) 8 ltac:(lia)).
  rewrite Z2Nat.id by lia. split; lia.
Qed.

Lemma cell_key_with (R : region) (t : itrie cell) (y : int) : cell_key (reg_with_cells R t) y = cell_key R y.
Proof. reflexivity. Qed.
Lemma cell_off_with (R : region) (t : itrie cell) (y : int) : cell_off (reg_with_cells R t) y = cell_off R y.
Proof. reflexivity. Qed.
Lemma get_cell_with (R : region) (t : itrie cell) (k : int) :
  get_cell segs (reg_with_cells R t) k = match iget (rg_d R) t k with Some c => c | None => default_cell segs (rg_kind R) (to_Z (rg_lo R) + 8 * to_Z k) end.
Proof. reflexivity. Qed.

Lemma rbyte_rwrite (R : region) (x y : int) (nb : list abyte) :
  region_wf R -> to_Z (rg_lo R) <= to_Z x < to_Z (rg_hi R) -> to_Z (rg_lo R) <= to_Z y < to_Z (rg_hi R) ->
  (cell_off R x + length nb <= 8)%nat ->
  rbyte segs (rwrite segs R x nb) y =
  if (to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length nb)) then nth (Z.to_nat (to_Z y - to_Z x)) nb BT
  else rbyte segs R y.
Proof.
  intros Hwf Hx Hy Hn. unfold rbyte, rwrite.
  rewrite cell_key_with, cell_off_with, get_cell_with.
  rewrite iget_iset. rewrite (key_eq_iff R x y Hwf Hx Hy).
  destruct (cell_addr R x ltac:(lia)) as [Ex Ox]. destruct (cell_addr R y ltac:(lia)) as [Ey Oy].
  destruct (Z.eqb_spec (to_Z (cell_key R x)) (to_Z (cell_key R y))) as [Ek|Ek].
  - rewrite cell_write_nth by exact Oy.
    assert (Hk : cell_key R y = cell_key R x) by (apply to_Z_inj; lia).
    destruct (Nat.leb_spec (cell_off R x) (cell_off R y)); destruct (Nat.ltb_spec (cell_off R y) (cell_off R x + length nb));
      cbn [andb].
    + replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length nb))) with true
        by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      f_equal. lia.
    + replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length nb))) with false
        by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
      unfold rbyte. rewrite Hk. reflexivity.
    + replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length nb))) with false
        by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
      unfold rbyte. rewrite Hk. reflexivity.
    + replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length nb))) with false
        by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
      unfold rbyte. rewrite Hk. reflexivity.
  - replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length nb))) with false.
    + unfold rbyte, get_cell. reflexivity.
    + symmetry. apply andb_false_iff. destruct (Z_lt_le_dec (to_Z y) (to_Z x)); [left; apply Z.leb_gt; lia|].
      right. apply Z.ltb_ge. assert (to_Z (cell_key R x) < to_Z (cell_key R y)) by lia. lia.
Qed.

Lemma rwrite_wf (R : region) (x : int) (nb : list abyte) : region_wf R -> region_wf (rwrite segs R x nb).
Proof. intros H. exact H. Qed.

Lemma rwrite_bounds (R : region) (x : int) (nb : list abyte) :
  rg_lo (rwrite segs R x nb) = rg_lo R /\ rg_hi (rwrite segs R x nb) = rg_hi R /\ rg_kind (rwrite segs R x nb) = rg_kind R.
Proof. repeat split. Qed.

Lemma rwrite_each_bounds (nb : list abyte) : forall (R : region) (x : int),
  rg_lo (rwrite_each segs R x nb) = rg_lo R /\ rg_hi (rwrite_each segs R x nb) = rg_hi R
  /\ rg_kind (rwrite_each segs R x nb) = rg_kind R /\ (region_wf R -> region_wf (rwrite_each segs R x nb)).
Proof.
  induction nb as [|b nb IH]; intros R x; cbn [rwrite_each].
  { split; [reflexivity|split; [reflexivity|split; [reflexivity| intros H; exact H]]]. }
  destruct (IH (rwrite segs R x [b]) (x + 1)%uint63) as [H1 [H2 [H3 H4]]].
  rewrite H1, H2, H3. split; [reflexivity|split; [reflexivity|split; [reflexivity|]]].
  intros Hwf. apply H4. apply rwrite_wf. exact Hwf.
Qed.

Lemma rbyte_rwrite_each (nb : list abyte) : forall (R : region) (x y : int),
  region_wf R -> to_Z (rg_lo R) <= to_Z x -> to_Z x + Z.of_nat (length nb) <= to_Z (rg_hi R) ->
  to_Z (rg_lo R) <= to_Z y < to_Z (rg_hi R) ->
  rbyte segs (rwrite_each segs R x nb) y =
  if (to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length nb)) then nth (Z.to_nat (to_Z y - to_Z x)) nb BT
  else rbyte segs R y.
Proof.
  induction nb as [|b nb IH]; intros R x y Hwf Hx Hn Hy; cbn [rwrite_each length].
  - replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat 0)) with false
      by (symmetry; apply andb_false_iff; destruct (Z_lt_le_dec (to_Z y) (to_Z x)); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]).
    reflexivity.
  - cbn [length] in Hn. pose proof (to_Z_bounded x). pose proof Hwf as Hwf'. destruct Hwf' as [W1 [W2 [W3 W4]]].
    assert (HL : Z.of_nat (S (length nb)) = Z.of_nat (length nb) + 1) by lia.
    assert (Hx1 : to_Z x + 1 < 2 ^ 63) by lia.
    rewrite IH.
    + rewrite int_add_1 by exact Hx1. rewrite rbyte_rwrite by (first [exact Hwf | lia | (cbn [length]; destruct (cell_addr R x ltac:(lia)); lia)]).
      cbn [length].
      destruct (Z.eqb_spec (to_Z y) (to_Z x)) as [->|Hne].
      * replace ((to_Z x + 1 <=? to_Z x) && _) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
        replace ((to_Z x <=? to_Z x) && (to_Z x <? to_Z x + Z.of_nat 1)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
        replace ((to_Z x <=? to_Z x) && (to_Z x <? to_Z x + Z.of_nat (S (length nb)))) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
        rewrite Z.sub_diag. reflexivity.
      * destruct ((to_Z x + 1 <=? to_Z y) && (to_Z y <? to_Z x + 1 + Z.of_nat (length nb))) eqn:E1.
        -- apply andb_true_iff in E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
           replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (S (length nb)))) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
           replace (Z.to_nat (to_Z y - to_Z x)) with (S (Z.to_nat (to_Z y - (to_Z x + 1)))) by lia. reflexivity.
        -- replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat 1)) with false by (symmetry; apply andb_false_iff; destruct (Z_lt_le_dec (to_Z y) (to_Z x)); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]).
           replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (S (length nb)))) with false.
           ++ reflexivity.
           ++ symmetry. apply andb_false_iff. apply andb_false_iff in E1 as [E1|E1]; [apply Z.leb_gt in E1 | apply Z.ltb_ge in E1].
              ** left. apply Z.leb_gt. lia.
              ** right. apply Z.ltb_ge. lia.
    + apply rwrite_wf. exact Hwf.
    + rewrite int_add_1 by exact Hx1. cbn [rwrite rg_lo reg_with_cells]. lia.
    + rewrite int_add_1 by exact Hx1. cbn [rwrite rg_hi reg_with_cells]. lia.
    + cbn [rwrite rg_lo rg_hi reg_with_cells]. lia.
Qed.

Lemma rbyte_rwrite_all (R : region) (x y : int) (nb : list abyte) :
  region_wf R -> (1 <= length nb)%nat -> to_Z (rg_lo R) <= to_Z x -> to_Z x + Z.of_nat (length nb) <= to_Z (rg_hi R) ->
  to_Z (rg_lo R) <= to_Z y < to_Z (rg_hi R) ->
  rbyte segs (rwrite_all segs R x nb) y =
  if (to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length nb)) then nth (Z.to_nat (to_Z y - to_Z x)) nb BT
  else rbyte segs R y.
Proof.
  intros Hwf H1 Hx Hn Hy. unfold rwrite_all. destruct (Nat.leb_spec (cell_off R x + length nb) 8) as [Hc|Hc].
  - apply rbyte_rwrite; try assumption. lia.
  - apply rbyte_rwrite_each; assumption.
Qed.

Lemma rwrite_all_bounds (R : region) (x : int) (nb : list abyte) :
  rg_lo (rwrite_all segs R x nb) = rg_lo R /\ rg_hi (rwrite_all segs R x nb) = rg_hi R
  /\ rg_kind (rwrite_all segs R x nb) = rg_kind R /\ (region_wf R -> region_wf (rwrite_all segs R x nb)).
Proof.
  unfold rwrite_all. destruct (Nat.leb _ 8).
  - split; [reflexivity|split; [reflexivity|split; [reflexivity|intros H; exact H]]].
  - apply rwrite_each_bounds.
Qed.

End StoreLemmas.

Section StoreSound.
Variable segs : list Segment.

Lemma Forall2_nth_error_ex {X Y : Type} (P : X -> Y -> Prop) (l1 : list X) (l2 : list Y) (k : nat) (d : X) :
  Forall2 P l1 l2 -> (k < length l1)%nat -> exists b, nth_error l2 k = Some b /\ P (nth k l1 d) b.
Proof.
  intros H. revert k. induction H as [|x y l1' l2' Hxy H IH]; intros k Hk; cbn [length] in Hk; [lia|].
  destruct k as [|k]; cbn [nth_error nth].
  - exists y. split; [reflexivity | exact Hxy].
  - apply IH. lia.
Qed.

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

Lemma find_region_i_spec (A : list region) (x n : int) : forall (j : nat) (i : nat) (R : region),
  find_region_i A x n j = Some (i, R) -> (j <= i)%nat /\ nth_error A (i - j) = Some R /\ find_region A x n = Some R.
Proof.
  induction A as [|R0 A' IH]; intros j i R H; cbn [find_region_i find_region] in *; [discriminate|].
  destruct ((rg_lo R0 <=? x)%uint63 && (x + n <=? rg_hi R0)%uint63 && negb (is_win (rg_kind R0))) eqn:E.
  - injection H as <- <-. rewrite Nat.sub_diag. split; [lia | split; reflexivity].
  - destruct (IH (S j) i R H) as [H1 [H2 H3]]. split; [lia|]. split; [|exact H3].
    replace (i - j)%nat with (S (i - S j)) by lia. exact H2.
Qed.

Lemma aview_replace_nth (A : list region) (i : nat) (R R' : region) (y : int) :
  regions_ok A -> nth_error A i = Some R -> rg_lo R' = rg_lo R -> rg_hi R' = rg_hi R -> rg_kind R' = rg_kind R ->
  is_win (rg_kind R) = false ->
  aview segs (replace_nth A i R') y =
  if in_region R y then Some (rbyte segs R' y, rk_writable (rg_kind R)) else aview segs A y.
Proof.
  intros Hok0 Hin0 Hlo0 Hhi0 Hk0 Hnw. revert i Hok0 Hin0 Hlo0 Hhi0 Hk0.
  induction A as [|R0 A' IH]; intros i Hok Hin Hlo Hhi Hk; [destruct i; discriminate|].
  destruct Hok as [Hwf [Hdis Hok]]. destruct i as [|i]; cbn [replace_nth nth_error aview] in *.
  - injection Hin as <-. unfold in_region. rewrite Hlo, Hhi, Hk, Hnw. destruct (_ && _); reflexivity.
  - rewrite IH by assumption.
    assert (Hd : rdisj R0 R) by (rewrite Forall_forall in Hdis; apply Hdis; apply (nth_error_In A' i); exact Hin).
    destruct (in_region R y) eqn:Ey; [|reflexivity].
    apply in_region_spec in Ey. rewrite (proj2 (in_region_false R0 y)); [reflexivity|].
    unfold rdisj in Hd. lia.
Qed.

Lemma Forall_replace_nth (P : region -> Prop) (A : list region) (i : nat) (R R' : region) :
  Forall P A -> nth_error A i = Some R -> P R' -> Forall P (replace_nth A i R').
Proof.
  revert i; induction A as [|R0 A' IH]; intros i HA Hi HP; [destruct i; discriminate|].
  inversion HA as [|? ? H0 H1]; subst. destruct i as [|i]; cbn [replace_nth nth_error] in *.
  - constructor; assumption.
  - constructor; [exact H0 | apply (IH i); assumption].
Qed.

Lemma regions_ok_replace_nth (A : list region) (i : nat) (R R' : region) :
  regions_ok A -> nth_error A i = Some R -> rg_lo R' = rg_lo R -> rg_hi R' = rg_hi R -> (region_wf R -> region_wf R') ->
  regions_ok (replace_nth A i R').
Proof.
  revert i; induction A as [|R0 A' IH]; intros i Hok Hin Hlo Hhi Hwf; [destruct i; discriminate|].
  destruct Hok as [Hwf0 [Hdis Hok]]. destruct i as [|i]; cbn [replace_nth nth_error regions_ok] in *.
  - injection Hin as <-. split; [apply Hwf; exact Hwf0|]. split; [|exact Hok].
    rewrite Forall_forall in *. intros R1 H1. specialize (Hdis R1 H1). unfold rdisj in *. rewrite Hlo, Hhi. exact Hdis.
  - split; [exact Hwf0|]. split.
    + (* [comment removed for export] *)
      apply (Forall_replace_nth _ A' i R R'); [exact Hdis | exact Hin |].
      rewrite Forall_forall in Hdis. specialize (Hdis R (nth_error_In A' i Hin)). unfold rdisj in *. rewrite Hlo, Hhi. exact Hdis.
    + apply (IH i); assumption.
Qed.

Lemma wview_write_keep (bs : list byte) : forall (m : word -> option byte) (a y : word),
  wview segs m y <> None -> wview segs (write_to_mem m a bs) y <> None.
Proof.
  induction bs as [|b rest IH]; intros m a y H; cbn [write_to_mem]; [exact H|].
  apply IH. unfold wview in *. destruct (bv_eqb y a); [discriminate | exact H].
Qed.

Lemma write_keep (bs : list byte) : forall (m : word -> option byte) (a y : word),
  m y <> None -> write_to_mem m a bs y <> None.
Proof.
  induction bs as [|b rest IH]; intros m a y H; cbn [write_to_mem]; [exact H|].
  apply IH. destruct (bv_eqb y a); [discriminate | exact H].
Qed.

Lemma RWin_write (ρ : valuation) (A : list region) (m : word -> option byte) (a : word) (bs : list byte) :
  RWin ρ A m -> RWin ρ A (write_to_mem m a bs).
Proof. intros H R f Hin Hk x Hx Hl. apply (write_keep bs). exact (H R f Hin Hk x Hx Hl). Qed.

Lemma RWin_replace_nth (ρ : valuation) (A : list region) (m : word -> option byte) (i : nat) (R R' : region) :
  RWin ρ A m -> nth_error A i = Some R -> is_win (rg_kind R') = false -> RWin ρ (replace_nth A i R') m.
Proof.
  intros H Hi Hw R0 f Hin Hk. revert i Hi Hin. induction A as [|R1 A' IH]; intros i Hi Hin; [destruct i; discriminate|].
  destruct i as [|i]; cbn [replace_nth nth_error In] in *.
  - destruct Hin as [E|Hin]; [subst R0; rewrite Hk in Hw; discriminate|]. apply (H R0 f (or_intror Hin) Hk).
  - destruct Hin as [E|Hin]; [subst R0; apply (H R1 f (or_introl eq_refl) Hk)|].
    apply (IH (fun R2 f2 H2 => H R2 f2 (or_intror H2)) i Hi Hin).
Qed.

(* [comment removed for export] *)
Lemma a_store_sound (ρ : valuation) (A A' : list region) (m : word -> option byte) (x : int) (nb : list abyte) (bs : list byte) :
  RMem segs ρ A m -> a_store segs A x nb = Some A' -> Forall2 (abyte_val ρ) nb bs ->
  (1 <= length nb < 1000)%nat -> to_Z x + Z.of_nat (length nb) < 2 ^ 47 ->
  RMem segs ρ A' (write_to_mem m (wz (to_Z x)) bs).
Proof.
  intros [Hok [Hm HwR]] Hst Hf Hn Hx. unfold a_store in Hst.
  destruct (find_region_i A x (of_Z (Z.of_nat (length nb))) 0) as [[i R]|] eqn:Ef; [|discriminate].
  destruct (rk_writable (rg_kind R)) eqn:Ew; [|discriminate]. injection Hst as <-.
  destruct (find_region_i_spec A x _ 0 i R Ef) as [_ [Hi Hf']]. rewrite Nat.sub_0_r in Hi.
  destruct (find_region_in A x _ R Hf') as [Hin [Hlo Hhi]].
  pose proof (to_Z_bounded x) as Hxb.
  rewrite phi_add_small in Hhi by (rewrite phi_of_Z_small; lia). rewrite phi_of_Z_small in Hhi by lia.
  assert (Hwf : region_wf R).
  { clear -Hok Hin. induction A as [|R0 A' IH]; [destruct Hin|]. destruct Hok as [Hwf [_ Hok]].
    destruct Hin as [<-|Hin]; [exact Hwf | apply IH; assumption]. }
  destruct (rwrite_all_bounds segs R x nb) as [B1 [B2 [B3 B4]]].
  pose proof (Forall2_length Hf) as Hlen.
  pose proof (find_region_nowin A x _ R Hf') as Hnw.
  split; [|split].
  - apply (regions_ok_replace_nth A i R); try assumption.
  - intros y ab w Hv.
    rewrite (aview_replace_nth A i R (rwrite_all segs R x nb) y Hok Hi B1 B2 B3 Hnw) in Hv.
    pose proof (to_Z_bounded y) as Hyb. change wB with (2 ^ 63) in Hyb, Hxb.
    assert (Hmy : write_to_mem m (wz (to_Z x)) bs (wz (to_Z y)) =
              if (to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length bs)) then nth_error bs (Z.to_nat (to_Z y - to_Z x))
              else m (wz (to_Z y))).
    { rewrite write_to_mem_spec by lia. rewrite u_wz by lia. reflexivity. }
    rewrite <- Hlen in Hmy.
    assert (Hwv : forall (mm : word -> option byte), mm (wz (to_Z y)) = m (wz (to_Z y)) ->
                    wview segs mm (wz (to_Z y)) = wview segs m (wz (to_Z y))).
    { intros mm E. unfold wview. rewrite E. reflexivity. }
    assert (Hrv : forall (mm : word -> option byte), mm (wz (to_Z y)) = m (wz (to_Z y)) ->
                    rv segs mm (wz (to_Z y)) = rv segs m (wz (to_Z y))).
    { intros mm E. unfold rv. rewrite E. reflexivity. }
    destruct (in_region R y) eqn:Ey.
    + injection Hv as <- <-. apply in_region_spec in Ey.
      rewrite rbyte_rwrite_all by (try assumption; lia).
      destruct ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length nb))) eqn:Ein.
      * apply andb_prop in Ein as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
        destruct (Forall2_nth_error_ex _ nb bs (Z.to_nat (to_Z y - to_Z x)) BT Hf ltac:(lia)) as [b [Hb Hab]].
        split.
        -- exists b. split; [|exact Hab]. unfold rv. rewrite Hmy. rewrite Hb. reflexivity.
        -- intros _. unfold wview. rewrite Hmy, Hb. discriminate.
      * assert (Hold : aview segs A y = Some (rbyte segs R y, true)).
        { rewrite <- Ew. apply (find_region_view segs A x (of_Z (Z.of_nat (length nb))) R y Hok Hf'). lia. }
        destruct (Hm y _ _ Hold) as [[b [Hb Hab]] Hw].
        assert (Eq : write_to_mem m (wz (to_Z x)) bs (wz (to_Z y)) = m (wz (to_Z y))) by (rewrite Hmy; reflexivity).
        split.
        -- exists b. rewrite Hrv by exact Eq. split; assumption.
        -- intros _. rewrite Hwv by exact Eq. apply Hw. reflexivity.
    + destruct (Hm y ab w Hv) as [[b [Hb Hab]] Hw].
      assert (Eq : write_to_mem m (wz (to_Z x)) bs (wz (to_Z y)) = m (wz (to_Z y))).
      { rewrite Hmy. apply in_region_false in Ey.
        replace ((to_Z x <=? to_Z y) && (to_Z y <? to_Z x + Z.of_nat (length nb))) with false; [reflexivity|].
        symmetry. apply andb_false_iff. destruct (Z_lt_le_dec (to_Z y) (to_Z x)); [left; apply Z.leb_gt; lia|right; apply Z.ltb_ge; lia]. }
      split.
      * exists b. rewrite Hrv by exact Eq. split; assumption.
      * intros Hw'. rewrite Hwv by exact Eq. apply Hw. exact Hw'.
  - apply RWin_write. apply (RWin_replace_nth ρ A m i R); [exact HwR | exact Hi | rewrite B3; exact Hnw].
Qed.

End StoreSound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MemFacts.
Variable segs : list Segment.

Lemma regions_ok_in_wf (A : list region) (R : region) : regions_ok A -> In R A -> region_wf R.
Proof.
  induction A as [|R0 A' IH]; intros Hok Hin; [destruct Hin|]. destruct Hok as [Hwf [_ Hok]].
  destruct Hin as [<-|Hin]; [exact Hwf | apply IH; assumption].
Qed.

Lemma a_bytes_bound (A : list region) (x : int) (n : nat) (l : list abyte) (w : bool) :
  regions_ok A -> (n < 1000)%nat -> to_Z x < 2 ^ 47 -> a_bytes segs A x n = Some (l, w) -> to_Z x + Z.of_nat n < 2 ^ 47.
Proof.
  intros Hok Hn Hx H. unfold a_bytes in H. destruct (find_region A x (of_Z (Z.of_nat n))) as [R|] eqn:Ef; [|discriminate].
  destruct (find_region_in A x _ R Ef) as [Hin [Hlo Hhi]]. pose proof (regions_ok_in_wf A R Hok Hin) as [W1 [W2 [W3 _]]].
  pose proof (to_Z_bounded x). change wB with (2^63) in *.
  rewrite add_spec, phi_of_Z_small in Hhi by lia. change wB with (2^63) in *.
  rewrite Z.mod_small in Hhi by lia. lia.
Qed.

Lemma a_store_region (A A' : list region) (x : int) (nb : list abyte) :
  a_store segs A x nb = Some A' ->
  exists i R, find_region_i A x (of_Z (Z.of_nat (length nb))) 0 = Some (i, R) /\ rk_writable (rg_kind R) = true
              /\ A' = replace_nth A i (rwrite_all segs R x nb).
Proof.
  unfold a_store. destruct (find_region_i A x _ 0) as [[i R]|] eqn:Ef; [|discriminate].
  destruct (rk_writable (rg_kind R)) eqn:Ew; [|discriminate]. intros H. injection H as <-. eauto.
Qed.

Lemma a_store_bytes (A A' : list region) (x : int) (nb : list abyte) :
  a_store segs A x nb = Some A' -> a_bytes segs A x (length nb) = Some (rbytes_fast segs (match find_region A x (of_Z (Z.of_nat (length nb))) with Some R => R | None => Rg 0 0 KUnk 0 IEmpty end) x (length nb), true).
Proof.
  intros H. destruct (a_store_region A A' x nb H) as [i [R [Ef [Ew _]]]].
  destruct (find_region_i_spec A x _ 0 i R Ef) as [_ [_ Hf]]. unfold a_bytes. rewrite Hf. rewrite Ew. reflexivity.
Qed.

Lemma a_store_store_ok (ρ : valuation) (A A' : list region) (m : word -> option byte) (x : int) (nb : list abyte) :
  RMem segs ρ A m -> (length nb < 1000)%nat -> to_Z x < 2 ^ 47 -> a_store segs A x nb = Some A' ->
  store_ok segs m (wz (to_Z x)) (length nb) = true /\ to_Z x + Z.of_nat (length nb) < 2 ^ 47.
Proof.
  intros HR Hn Hx H. pose proof (a_store_bytes A A' x nb H) as Hb. destruct HR as [Hok [Hm HwR]].
  assert (Hbd : to_Z x + Z.of_nat (length nb) < 2 ^ 47) by (eapply a_bytes_bound; eassumption).
  split; [|exact Hbd]. eapply (a_bytes_store_ok segs ρ A m x); [split; [assumption | split; assumption] | exact Hn | exact Hbd | exact Hb].
Qed.

Lemma a_store_top (A A' : list region) (x : int) (nb : list abyte) (SP : Z) :
  a_store segs A x nb = Some A' -> (forall r, In r A -> to_Z (rg_hi r) <= SP) -> (forall r, In r A' -> to_Z (rg_hi r) <= SP).
Proof.
  intros H Ht. destruct (a_store_region A A' x nb H) as [i [R [Ef [_ ->]]]].
  destruct (find_region_i_spec A x _ 0 i R Ef) as [_ [Hi _]]. rewrite Nat.sub_0_r in Hi.
  destruct (rwrite_all_bounds segs R x nb) as [_ [B2 _]].
  clear -Ht Hi B2. revert i Hi. induction A as [|R0 A'' IH]; intros i Hi r Hr; [destruct i; discriminate|].
  destruct i as [|i]; cbn [replace_nth nth_error In] in *.
  - injection Hi as <-. destruct Hr as [<-|Hr]; [rewrite B2; apply Ht; left; reflexivity | apply Ht; right; exact Hr].
  - destruct Hr as [<-|Hr]; [apply Ht; left; reflexivity|]. apply (IH (fun r Hr => Ht r (or_intror Hr)) i Hi r Hr).
Qed.

(* [comment removed for export] *)
Lemma a_store_below (A A' : list region) (x : int) (nb : list abyte) (SP : Z) :
  regions_ok A -> (length nb < 1000)%nat -> to_Z x < 2 ^ 47 ->
  a_store segs A x nb = Some A' -> (forall r, In r A -> to_Z (rg_hi r) <= SP) ->
  to_Z x + Z.of_nat (length nb) <= SP.
Proof.
  intros Hok Hn Hx H Ht. destruct (a_store_region A A' x nb H) as [i [R [Ef _]]].
  destruct (find_region_i_spec A x _ 0 i R Ef) as [_ [_ Hf]].
  destruct (find_region_in A x _ R Hf) as [Hin [_ Hhi]]. pose proof (Ht R Hin).
  pose proof (to_Z_bounded x). change wB with (2^63) in *.
  rewrite add_spec, phi_of_Z_small in Hhi by lia. change wB with (2^63) in *.
  rewrite Z.mod_small in Hhi by lia. lia.
Qed.

End MemFacts.
