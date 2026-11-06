(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimString PrimInt63.
From Stdlib Require Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Module SEGSCAN.
Local Notation "'φ' x" := (Uint63.to_Z x) (at level 0).
Local Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint p2i (p : positive) (n : nat) (sh : int) (acc : int) {struct p} : option int :=
  match p with
  | xH => match n with O => None | S _ => Some (PrimInt63.add acc (PrimInt63.lsl 1%uint63 sh)) end
  | xO q => match n with O => None | S m => p2i q m (PrimInt63.add sh 1%uint63) acc end
  | xI q => match n with O => None | S m => p2i q m (PrimInt63.add sh 1%uint63) (PrimInt63.add acc (PrimInt63.lsl 1%uint63 sh)) end
  end.
(* [comment removed for export] *)
Definition z61 (z : Z) : option int :=
  match z with
  | Z0 => Some 0%uint63
  | Zpos p => p2i p 61 0%uint63 0%uint63
  | Zneg _ => None
  end.
Lemma wB63 : Uint63.wB = 2 ^ 63. Proof. reflexivity. Qed.
Lemma p2i_spec : forall p n sh acc r,
  p2i p n sh acc = Some r -> φ sh + Z.of_nat n <= 62 -> 0 <= φ acc < 2 ^ φ sh ->
  φ r = φ acc + Zpos p * 2 ^ φ sh /\ Zpos p < 2 ^ Z.of_nat n.
Proof.
  induction p as [q IH|q IH|]; intros n sh acc r H Hs Ha; (destruct n as [|m]; [discriminate|]); cbn [p2i] in H;
    pose proof (Uint63.to_Z_bounded sh) as Bs;
    assert (E1 : φ (PrimInt63.lsl 1%uint63 sh) = 2 ^ φ sh)
      by (rewrite Uint63.lsl_spec, wB63; change (φ 1%uint63) with 1; rewrite Z.mul_1_l; apply Z.mod_small;
          split; [apply Z.pow_nonneg; lia|apply Z.pow_lt_mono_r; lia]);
    assert (P1 : 2 ^ (φ sh + 1) = 2 ^ φ sh * 2) by (rewrite Z.pow_add_r by lia; lia);
    assert (P62 : 2 ^ φ sh * 2 <= 2 ^ 62) by (rewrite <- P1; apply Z.pow_le_mono_r; lia);
    assert (E2 : φ (PrimInt63.add acc (PrimInt63.lsl 1%uint63 sh)) = φ acc + 2 ^ φ sh)
      by (rewrite Uint63.add_spec, E1, wB63; apply Z.mod_small; lia);
    assert (E3 : φ (PrimInt63.add sh 1%uint63) = φ sh + 1)
      by (rewrite Uint63.add_spec, wB63; change (φ 1%uint63) with 1; apply Z.mod_small; lia);
    assert (PN : 2 ^ Z.of_nat (S m) = 2 * 2 ^ Z.of_nat m) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; reflexivity).
  - apply IH in H; [|rewrite E3; lia|rewrite E2, E3, P1; lia].
    destruct H as [H1 H2]. rewrite H1, E2, E3, P1, PN. split; [|lia]. change (Z.pos q~1) with (2 * Z.pos q + 1). generalize (2 ^ φ sh). intros X. clear. ring.
  - apply IH in H; [|rewrite E3; lia|rewrite E3, P1; lia].
    destruct H as [H1 H2]. rewrite H1, E3, P1, PN. split; [|lia]. change (Z.pos q~0) with (2 * Z.pos q). generalize (2 ^ φ sh). intros X. clear. ring.
  - injection H as <-. rewrite E2, PN. split; [lia|]. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat m) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma z61_spec : forall z a, z61 z = Some a -> φ a = z /\ 0 <= z < 2 ^ 61.
Proof.
  intros z a H. destruct z as [|p|p]; cbn [z61] in H; [injection H as <-; split; [reflexivity|lia]| |discriminate].
  apply p2i_spec in H; [|change (φ 0%uint63) with 0; lia|change (φ 0%uint63) with 0; cbn; lia].
  change (φ 0%uint63) with 0 in H. change (Z.of_nat 61) with 61 in H. destruct H as [H1 H2]. split; [rewrite H1; cbn; lia|lia].
Qed.

(* [comment removed for export] *)
Definition nybI (c : int) : int :=
  if (if PrimInt63.leb 48%uint63 c then PrimInt63.leb c 57%uint63 else false) then PrimInt63.sub c 48%uint63
  else if (if PrimInt63.leb 97%uint63 c then PrimInt63.leb c 102%uint63 else false) then PrimInt63.sub c 87%uint63
  else 16%uint63.
Definition hex_byte_atI (s : PrimString.string) (o : int) : option Z :=
  let ci := PrimInt63.add o o in
  let ci1 := PrimInt63.add ci 1%uint63 in
  let s_len := PrimString.length s in
  if (if PrimInt63.ltb ci1 s_len then true else PrimInt63.eqb ci1 (PrimInt63.sub s_len 1%uint63)) then
    let h := nybI (PrimString.get s ci) in
    let l := nybI (PrimString.get s ci1) in
    if (if PrimInt63.ltb h 16%uint63 then PrimInt63.ltb l 16%uint63 else false)
    then Some (Uint63Axioms.to_Z_rec 8 (PrimInt63.add (PrimInt63.lsl h 4%uint63) l))
    else None
  else None.
Fixpoint seg_byte_atI (chunks : list PrimString.string) (o : int) : option Z :=
  match chunks with
  | [] => None
  | c :: rest =>
      let cb := PrimInt63.lsr (PrimString.length c) 1%uint63 in
      if PrimInt63.ltb o cb then hex_byte_atI c o else seg_byte_atI rest (PrimInt63.sub o cb)
  end.
(* [comment removed for export] *)
Record sgi : Type := SGI { sg_lo : int; sg_hi : int; sg_r : bool; sg_seg : Segment }.
Fixpoint mk_stab (segs : list Segment) : option (list sgi) :=
  match segs with
  | [] => Some []
  | s :: r => match z61 (Z.of_N (seg_base s)), z61 (Z.of_N (seg_size s)), mk_stab r with
              | Some b, Some z, Some t => Some (SGI b (PrimInt63.add b z) (seg_readable s) s :: t)
              | _, _, _ => None
              end
  end.
(* [comment removed for export] *)
Fixpoint find_sgi (t : list sgi) (a e : int) : option sgi :=
  match t with
  | [] => None
  | g :: r => if (if PrimInt63.leb (sg_lo g) a then PrimInt63.leb e (sg_hi g) else false) then Some g
              else if (if PrimInt63.leb (sg_hi g) a then true else PrimInt63.leb e (sg_lo g)) then find_sgi r a e
              else None
  end.


Lemma to_Z_rec_small : forall n x, φ x < 2 ^ Z.of_nat n -> Uint63Axioms.to_Z_rec n x = φ x.
Proof.
  induction n as [|n IH]; intros x H.
  - pose proof (Uint63.to_Z_bounded x). change (2 ^ Z.of_nat 0) with 1 in H. cbn [Uint63Axioms.to_Z_rec]. lia.
  - cbn [Uint63Axioms.to_Z_rec].
    assert (PN : 2 ^ Z.of_nat (S n) = 2 * 2 ^ Z.of_nat n) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; reflexivity).
    pose proof (Uint63.to_Z_bounded x) as Bx.
    assert (E : φ (PrimInt63.lsr x 1%uint63) = φ x / 2) by (rewrite Uint63.lsr_spec; reflexivity).
    rewrite IH by (rewrite E; apply Z.div_lt_upper_bound; lia).
    rewrite E. pose proof (Uint63.is_even_spec x) as Hev. pose proof (Z.div_mod (φ x) 2 ltac:(lia)) as DM.
    destruct (Uint63Axioms.is_even x); [change (IntDef.Z.double (φ x / 2)) with (Z.double (φ x / 2)); rewrite Z.double_spec|change (IntDef.Z.succ_double (φ x / 2)) with (Z.succ_double (φ x / 2)); rewrite Z.succ_double_spec]; lia.
Qed.
Lemma leb_iff : forall x y, PrimInt63.leb x y = true <-> φ x <= φ y. Proof. exact Uint63.leb_spec. Qed.
Lemma ltb_iff : forall x y, PrimInt63.ltb x y = true <-> φ x < φ y. Proof. exact Uint63.ltb_spec. Qed.
Lemma leb_b : forall x y, PrimInt63.leb x y = Z.leb (φ x) (φ y).
Proof. intros. destruct (Z.leb_spec (φ x) (φ y)) as [H|H]; [apply leb_iff; exact H|]. destruct (PrimInt63.leb x y) eqn:E; [apply leb_iff in E; lia|reflexivity]. Qed.
Lemma ltb_b : forall x y, PrimInt63.ltb x y = Z.ltb (φ x) (φ y).
Proof. intros. destruct (Z.ltb_spec (φ x) (φ y)) as [H|H]; [apply ltb_iff; exact H|]. destruct (PrimInt63.ltb x y) eqn:E; [apply ltb_iff in E; lia|reflexivity]. Qed.
Lemma nybI_spec : forall c, φ (nybI c) = Z.of_N (hex_nybble c).
Proof.
  intros c. unfold nybI, hex_nybble. pose proof (Uint63.to_Z_bounded c) as Bc. rewrite wB63 in Bc.
  change (Uint63.leb 48 c) with (PrimInt63.leb 48%uint63 c). change (Uint63.leb c 57) with (PrimInt63.leb c 57%uint63).
  change (Uint63.leb 97 c) with (PrimInt63.leb 97%uint63 c). change (Uint63.leb c 102) with (PrimInt63.leb c 102%uint63).
  rewrite !leb_b. change (φ 48%uint63) with 48. change (φ 57%uint63) with 57. change (φ 97%uint63) with 97. change (φ 102%uint63) with 102.
  destruct (Z.leb_spec 48 (φ c)) as [H1|H1]; cbn [andb].
  - destruct (Z.leb_spec (φ c) 57) as [H2|H2].
    + rewrite Uint63.sub_spec, wB63. change (φ 48%uint63) with 48. rewrite Z.mod_small by lia. rewrite Z2N.id by lia. reflexivity.
    + destruct (Z.leb_spec 97 (φ c)) as [H3|H3]; cbn [andb]; [|reflexivity].
      destruct (Z.leb_spec (φ c) 102) as [H4|H4]; [|reflexivity].
      rewrite Uint63.sub_spec, wB63. change (φ 87%uint63) with 87. rewrite Z.mod_small by lia. rewrite Z2N.id by lia. reflexivity.
  - destruct (Z.leb_spec 97 (φ c)) as [H3|H3]; [lia|]. reflexivity.
Qed.
Lemma nybI_le : forall c, 0 <= φ (nybI c) <= 16.
Proof.
  intros c. rewrite nybI_spec. unfold hex_nybble. pose proof (Uint63.to_Z_bounded c) as Bc.
  destruct (Uint63.leb 48 c && Uint63.leb c 57)%bool eqn:E1.
  - apply andb_prop in E1. destruct E1 as [A B]. apply Uint63.leb_spec in A, B. change (φ 48%uint63) with 48 in A. change (φ 57%uint63) with 57 in B. rewrite Z2N.id by lia. lia.
  - destruct (Uint63.leb 97 c && Uint63.leb c 102)%bool eqn:E2; [|cbn; lia].
    apply andb_prop in E2. destruct E2 as [A B]. apply Uint63.leb_spec in A, B. change (φ 97%uint63) with 97 in A. change (φ 102%uint63) with 102 in B. rewrite Z2N.id by lia. lia.
Qed.
Lemma hex_byte_atI_spec : forall s o i, φ o = Z.of_N i -> Z.of_N i < 2 ^ 62 ->
  hex_byte_atI s o = option_map (fun b : byte => bv_unsigned b) (hex_byte_at s i).
Proof.
  intros s o i Ho Hi. unfold hex_byte_atI, hex_byte_at. cbv zeta.
  assert (E0 : PrimInt63.add o o = Uint63.of_Z (Z.of_N (2 * i))).
  { apply Uint63.to_Z_inj. rewrite Uint63.add_spec, Uint63.of_Z_spec, Ho, wB63. f_equal. lia. }
  assert (E1 : PrimInt63.add (PrimInt63.add o o) 1%uint63 = Uint63.of_Z (Z.of_N (2 * i + 1))).
  { apply Uint63.to_Z_inj. rewrite E0, Uint63.add_spec, !Uint63.of_Z_spec, wB63. change (φ 1%uint63) with 1.
    rewrite Zplus_mod_idemp_l. f_equal. lia. }
  rewrite E1, E0.
  set (ci := Uint63.of_Z (Z.of_N (2 * i))). set (ci1 := Uint63.of_Z (Z.of_N (2 * i + 1))).
  destruct (PrimInt63.ltb ci1 (PrimString.length s)) eqn:EL; cbn [orb].
  2: destruct (PrimInt63.eqb ci1 (PrimInt63.sub (PrimString.length s) 1%uint63)); [|reflexivity].
  all: pose proof (nybI_spec (get s ci)) as Sh; pose proof (nybI_spec (get s ci1)) as Sl;
       pose proof (nybI_le (get s ci)) as Bh; pose proof (nybI_le (get s ci1)) as Bl;
       set (h := hex_nybble (get s ci)) in *; set (l := hex_nybble (get s ci1)) in *;
       rewrite !ltb_b; change (φ 16%uint63) with 16; rewrite Sh, Sl;
       replace (N.ltb h 16) with (Z.ltb (Z.of_N h) 16) by (destruct (Z.ltb_spec (Z.of_N h) 16), (N.ltb_spec h 16); try reflexivity; lia);
       replace (N.ltb l 16) with (Z.ltb (Z.of_N l) 16) by (destruct (Z.ltb_spec (Z.of_N l) 16), (N.ltb_spec l 16); try reflexivity; lia);
       destruct (Z.ltb_spec (Z.of_N h) 16) as [H1|H1]; cbn [andb]; [|reflexivity];
       destruct (Z.ltb_spec (Z.of_N l) 16) as [H2|H2]; [|reflexivity];
       cbn [option_map]; f_equal;
       (assert (E4 : φ (PrimInt63.add (PrimInt63.lsl (nybI (get s ci)) 4%uint63) (nybI (get s ci1))) = Z.of_N (h * 16 + l))
         by (rewrite Uint63.add_spec, Uint63.lsl_spec, Sh, Sl, wB63; change (φ 4%uint63) with 4;
             rewrite (Z.mod_small (Z.of_N h * 2 ^ 4)) by lia; rewrite Z.mod_small by lia; lia));
       rewrite to_Z_rec_small by (rewrite E4; change (2 ^ Z.of_nat 8) with 256; lia);
       rewrite E4, Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 8) with 256; lia); reflexivity.
Qed.
Lemma seg_byte_atI_spec : forall chunks o off, φ o = Z.of_N off -> Z.of_N off < 2 ^ 62 ->
  seg_byte_atI chunks o = option_map (fun b : byte => bv_unsigned b) (segment_byte_at chunks off).
Proof.
  induction chunks as [|c rest IH]; intros o off Ho Hoff; [reflexivity|].
  cbn [seg_byte_atI segment_byte_at]. cbv zeta.
  pose proof (Uint63.to_Z_bounded (PrimString.length c)) as Bl. rewrite wB63 in Bl.
  assert (E : φ (PrimInt63.lsr (PrimString.length c) 1%uint63) = φ (PrimString.length c) / 2) by (rewrite Uint63.lsr_spec; reflexivity).
  assert (D : 0 <= φ (PrimString.length c) / 2) by (apply Z.div_pos; lia).
  rewrite ltb_b, E, Ho.
  replace (N.ltb off (Z.to_N (φ (PrimString.length c) / 2))) with (Z.ltb (Z.of_N off) (φ (PrimString.length c) / 2))
    by (destruct (Z.ltb_spec (Z.of_N off) (φ (PrimString.length c) / 2)), (N.ltb_spec off (Z.to_N (φ (PrimString.length c) / 2))); try reflexivity; lia).
  destruct (Z.ltb_spec (Z.of_N off) (φ (PrimString.length c) / 2)) as [H|H].
  - apply hex_byte_atI_spec; assumption.
  - apply IH; [|lia]. rewrite Uint63.sub_spec, E, Ho, wB63. rewrite Z.mod_small by lia. lia.
Qed.
Definition sgi_ok (s : Segment) (g : sgi) : Prop :=
  sg_seg g = s /\ φ (sg_lo g) = Z.of_N (seg_base s) /\ φ (sg_hi g) = Z.of_N (seg_base s) + Z.of_N (seg_size s) /\ sg_r g = seg_readable s.
Lemma mk_stab_spec : forall segs t, mk_stab segs = Some t -> Forall2 sgi_ok segs t.
Proof.
  induction segs as [|s r IH]; intros t H; cbn [mk_stab] in H; [injection H as <-; constructor|].
  destruct (z61 (Z.of_N (seg_base s))) as [b|] eqn:Eb; [|discriminate].
  destruct (z61 (Z.of_N (seg_size s))) as [z|] eqn:Ez; [|discriminate].
  destruct (mk_stab r) as [t'|]; [|discriminate]. injection H as <-.
  constructor; [|apply IH; reflexivity].
  destruct (z61_spec _ _ Eb) as [B1 B2]. destruct (z61_spec _ _ Ez) as [Z1 Z2].
  unfold sgi_ok. cbn [sg_seg sg_lo sg_hi sg_r]. repeat split; [exact B1|].
  rewrite Uint63.add_spec, B1, Z1, wB63. apply Z.mod_small. lia.
Qed.
Lemma find_sgi_spec : forall segs t a e g, Forall2 sgi_ok segs t -> find_sgi t a e = Some g -> φ a < φ e ->
  (forall u, φ a <= u < φ e -> find_segment segs u 1 = Some (sg_seg g))
  /\ φ (sg_lo g) = Z.of_N (seg_base (sg_seg g)) /\ φ (sg_lo g) <= φ a /\ sg_r g = seg_readable (sg_seg g).
Proof.
  intros segs t a e g F. induction F as [|s g0 segs t [S1 [S2 [S3 S4]]] F IH]; intros H Hae; cbn [find_sgi] in H; [discriminate|].
  rewrite !leb_b in H.
  destruct (Z.leb_spec (φ (sg_lo g0)) (φ a)) as [H1|H1].
  - destruct (Z.leb_spec (φ e) (φ (sg_hi g0))) as [H2|H2].
    + injection H as <-. split; [|rewrite S1; repeat split; assumption].
      intros u Hu. cbn [find_segment]. rewrite S1.
      destruct (Z.leb_spec (Z.of_N (seg_base s)) u) as [A|A]; [|lia].
      destruct (Z.leb_spec (u + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s))) as [B|B]; [reflexivity|lia].
    + destruct (Z.leb_spec (φ (sg_hi g0)) (φ a)) as [H3|H3]; [|destruct (Z.leb_spec (φ e) (φ (sg_lo g0))); [lia|discriminate]].
      destruct (IH H Hae) as [I1 I2]. split; [|exact I2].
      intros u Hu. cbn [find_segment].
      destruct (Z.leb_spec (Z.of_N (seg_base s)) u) as [A|A]; cbn [andb]; [|apply I1; exact Hu].
      destruct (Z.leb_spec (u + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s))) as [B|B]; [lia|apply I1; exact Hu].
  - destruct (Z.leb_spec (φ (sg_hi g0)) (φ a)) as [H3|H3].
    + destruct (IH H Hae) as [I1 I2]. split; [|exact I2].
      intros u Hu. cbn [find_segment].
      destruct (Z.leb_spec (Z.of_N (seg_base s)) u) as [A|A]; cbn [andb]; [|apply I1; exact Hu].
      destruct (Z.leb_spec (u + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s))) as [B|B]; [lia|apply I1; exact Hu].
    + destruct (Z.leb_spec (φ e) (φ (sg_lo g0))) as [H4|H4]; [|discriminate].
      destruct (IH H Hae) as [I1 I2]. split; [|exact I2].
      intros u Hu. cbn [find_segment].
      destruct (Z.leb_spec (Z.of_N (seg_base s)) u) as [A|A]; cbn [andb]; [lia|apply I1; exact Hu].
Qed.

(* [comment removed for export] *)
Fixpoint scanI (chunks : list PrimString.string) (o : int) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => match seg_byte_atI chunks o with Some _ => scanI chunks (PrimInt63.add o 1%uint63) n' | None => false end
  end.
Lemma scanI_spec : forall chunks n o off, φ o = Z.of_N off -> Z.of_N off + Z.of_nat n < 2 ^ 62 -> scanI chunks o n = true ->
  forall i, 0 <= i < Z.of_nat n -> segment_byte_at chunks (off + Z.to_N i) <> None.
Proof.
  intros chunks n. induction n as [|n IH]; intros o off Ho Hn H i Hi; [lia|]. cbn [scanI] in H.
  rewrite (seg_byte_atI_spec chunks o off Ho) in H by lia.
  destruct (segment_byte_at chunks off) as [b|] eqn:EB; cbn [option_map] in H; [|discriminate].
  destruct (Z.eq_dec i 0) as [->|NZ]; [change (Z.to_N 0) with 0%N; rewrite N.add_0_r, EB; discriminate|].
  replace (off + Z.to_N i)%N with ((off + 1) + Z.to_N (i - 1))%N by lia.
  apply (IH (PrimInt63.add o 1%uint63) (off + 1)%N); [| |exact H|lia].
  - rewrite Uint63.add_spec, Ho, wB63. change (φ 1%uint63) with 1. rewrite Z.mod_small by lia. lia.
  - lia.
Qed.

(* [comment removed for export] *)
Definition range_okI (p : Segment -> bool) (segs : list Segment) (a : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S _ =>
      match mk_stab segs, z61 a, z61 (Z.of_nat n) with
      | Some t, Some a63, Some n63 =>
          match find_sgi t a63 (PrimInt63.add a63 n63) with
          | Some g => if p (sg_seg g) then scanI (seg_bytes (sg_seg g)) (PrimInt63.sub a63 (sg_lo g)) n else false
          | None => false
          end
      | _, _, _ => false
      end
  end.
Theorem range_okI_spec : forall p segs a n, range_okI p segs a n = true ->
  forall u, a <= u < a + Z.of_nat n ->
  exists seg, find_segment segs u 1 = Some seg /\ p seg = true /\
              segment_byte_at (seg_bytes seg) (Z.to_N (u - Z.of_N (seg_base seg))) <> None.
Proof.
  intros p segs a n H u Hu. unfold range_okI in H. destruct n as [|n']; [lia|]. set (n := S n') in *.
  destruct (mk_stab segs) as [t|] eqn:Et; [|discriminate].
  destruct (z61 a) as [a63|] eqn:Ea; [|discriminate]. destruct (z61 (Z.of_nat n)) as [n63|] eqn:En; [|discriminate].
  destruct (z61_spec _ _ Ea) as [A1 A2]. destruct (z61_spec _ _ En) as [N1 N2].
  assert (EE : φ (PrimInt63.add a63 n63) = a + Z.of_nat n) by (rewrite Uint63.add_spec, A1, N1, wB63; apply Z.mod_small; lia).
  destruct (find_sgi t a63 (PrimInt63.add a63 n63)) as [g|] eqn:Ef; [|discriminate].
  destruct (find_sgi_spec segs t _ _ g (mk_stab_spec _ _ Et) Ef) as [F1 [F2 [F3 F4]]]; [rewrite EE, A1; lia|].
  rewrite EE, A1 in F1. rewrite A1 in F3.
  destruct (p (sg_seg g)) eqn:Hp; [|discriminate].
  exists (sg_seg g). split; [apply F1; exact Hu|]. split; [exact Hp|].
  assert (Eo : φ (PrimInt63.sub a63 (sg_lo g)) = Z.of_N (Z.to_N (a - Z.of_N (seg_base (sg_seg g))))).
  { rewrite Uint63.sub_spec, A1, F2, wB63. rewrite Z.mod_small by lia. rewrite Z2N.id by lia. reflexivity. }
  pose proof (scanI_spec _ n _ _ Eo ltac:(rewrite Z2N.id by lia; lia) H (u - a) ltac:(lia)) as S.
  replace (Z.to_N (u - Z.of_N (seg_base (sg_seg g)))) with (Z.to_N (a - Z.of_N (seg_base (sg_seg g))) + Z.to_N (u - a))%N by lia.
  exact S.
Qed.
End SEGSCAN.
