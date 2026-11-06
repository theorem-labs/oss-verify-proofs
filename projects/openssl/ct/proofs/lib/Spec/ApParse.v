(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition INT_MAX : Z := 2147483647.
Definition LONG_MAX : Z := 9223372036854775807.
Definition V_ASN1_CONSTRUCTED : Z := 32.

Inductive go_errk : Type := GeHdr | GeTooLong | GeTooSmall.

Record go_res : Type := mkGO {
  go_err : option go_errk;
  go_ret : Z;        (* [comment removed for export] *)
  go_p : Z;          (* [comment removed for export] *)
  go_len : Z;
  go_tag : Z;
  go_cls : Z
}.

Definition go_fail (k : go_errk) (p : Z) : go_res := mkGO (Some k) 0 p 0 0 0.

(* [comment removed for export] *)
Fixpoint tag_loop (fuel : nat) (d : list Z) (len p max : Z) {struct fuel} : option (Z * Z * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
      if Z.land (znth d p) 128 =? 0 then Some (len, p, max)
      else
        let len' := Z.lor (Z.shiftl len 7) (Z.land (znth d p) 127) in
        let max' := max - 1 in
        if max' =? 0 then None
        else if INT_MAX / 128 <? len' then None
        else tag_loop fuel' d len' (p + 1) max'
  end.

(* [comment removed for export] *)
Fixpoint skip_zeros (fuel : nat) (d : list Z) (p i : Z) {struct fuel} : Z * Z :=
  match fuel with
  | O => (p, i)
  | S fuel' => if (0 <? i) && (znth d p =? 0) then skip_zeros fuel' d (p + 1) (i - 1) else (p, i)
  end.

(* [comment removed for export] *)
Fixpoint be_octets (fuel : nat) (d : list Z) (p i acc : Z) {struct fuel} : Z * Z :=
  match fuel with
  | O => (acc, p)
  | S fuel' => if 0 <? i then be_octets fuel' d (p + 1) (i - 1) (acc * 256 + znth d p) else (acc, p)
  end.

(* [comment removed for export] *)
Definition get_length (d : list Z) (p max : Z) : option (bool * Z * Z) :=
  if max <? 1 then None
  else
    let max := max - 1 in
    let b := znth d p in
    if b =? 128 then Some (true, 0, p + 1)
    else
      let i := Z.land b 127 in
      if Z.land b 128 =? 0 then Some (false, i, p + 1)
      else
        let p := p + 1 in
        if max <? i then None
        else
          let '(p, i) := skip_zeros (Z.to_nat i) d p i in
          if 8 <? i then None
          else
            let '(ret, p) := be_octets (Z.to_nat i) d p i 0 in
            if LONG_MAX <? ret then None else Some (false, ret, p).

Definition get_object (d : list Z) (p0 omax : Z) : go_res :=
  if omax <=? 0 then go_fail GeTooSmall p0
  else
    let b0 := znth d p0 in
    let ret := Z.land b0 V_ASN1_CONSTRUCTED in
    let xclass := Z.land b0 192 in
    let i := Z.land b0 31 in
    let hdr :=                                     (* [comment removed for export] *)
      if i =? 31 then
        let p := p0 + 1 in
        let max := omax - 1 in
        if max =? 0 then None
        else
          match tag_loop (Z.to_nat max) d 0 p max with
          | None => None
          | Some (len, p, max) =>
              let len := Z.lor (Z.shiftl len 7) (Z.land (znth d p) 127) in
              let p := p + 1 in
              let max := max - 1 in
              if max =? 0 then None else Some (len, p, max)
          end
      else
        let p := p0 + 1 in
        let max := omax - 1 in
        if max =? 0 then None else Some (i, p, max) in
    match hdr with
    | None => go_fail GeHdr p0
    | Some (tag, p, max) =>
        match get_length d p max with
        | None => go_fail GeHdr p0
        | Some (inf, len, p) =>
            if inf && (ret =? 0) then go_fail GeHdr p0
            else
              let r := Z.lor ret (if inf then 1 else 0) in
              if omax - (p - p0) <? len then mkGO (Some GeTooLong) r p len tag xclass
              else mkGO None r p len tag xclass
        end
    end.

(* [comment removed for export] *)
Definition go_hl (p0 : Z) (g : go_res) : Z := go_p g - p0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tag_loop_bounds : forall fuel d len p max len' p' max', 1 <= max ->
  tag_loop fuel d len p max = Some (len', p', max') -> p <= p' /\ max' = max - (p' - p) /\ 1 <= max'.
Proof.
  induction fuel as [|f IH]; intros d len p max len' p' max' Hm H; cbn -[Z.shiftl Z.lor Z.land Z.ltb Z.div Z.eqb Z.sub INT_MAX] in H; [discriminate|].
  destruct (Z.land (znth d p) 128 =? 0).
  - inversion H; subst. lia.
  - destruct (max - 1 =? 0) eqn:E; [discriminate|]. destruct (INT_MAX / 128 <? _); [discriminate|].
    apply Z.eqb_neq in E. apply IH in H; [|lia]. lia.
Qed.

Lemma skip_zeros_bounds : forall fuel d p i p' i', skip_zeros fuel d p i = (p', i') -> p <= p' /\ i' = i - (p' - p) /\ (0 <= i -> 0 <= i').
Proof.
  induction fuel as [|f IH]; intros d p i p' i' H; cbn -[Z.ltb Z.eqb Z.sub Z.add] in H.
  - inversion H; subst. lia.
  - destruct ((0 <? i) && (znth d p =? 0)) eqn:E.
    + apply IH in H. apply andb_prop in E as [E _]. apply Z.ltb_lt in E. lia.
    + inversion H; subst. lia.
Qed.

Lemma be_octets_bounds : forall fuel d p i acc r p', be_octets fuel d p i acc = (r, p') -> 0 <= acc -> Forall (fun b => 0 <= b) d ->
  p <= p' /\ p' - p <= Z.max 0 i /\ 0 <= r.
Proof.
  induction fuel as [|f IH]; intros d p i acc r p' H Hacc Hd; cbn -[Z.ltb Z.mul Z.add Z.sub znth] in H.
  - inversion H; subst. lia.
  - destruct (0 <? i) eqn:E.
    + apply Z.ltb_lt in E. apply IH in H; [| |exact Hd].
      * lia.
      * assert (0 <= znth d p); [|lia]. unfold znth. destruct (p <? 0); [lia|]. destruct (nth_in_or_default (Z.to_nat p) d 0) as [Hin| ->]; [|lia].
        rewrite Forall_forall in Hd. apply Hd. exact Hin.
    + inversion H; subst. lia.
Qed.

Lemma get_length_bounds : forall d p max inf len p', Forall (fun b => 0 <= b) d ->
  get_length d p max = Some (inf, len, p') -> 1 <= p' - p <= max /\ 0 <= len.
Proof.
  intros d p max inf len p' Hd H. unfold get_length in H.
  destruct (max <? 1) eqn:E1; [discriminate|]. apply Z.ltb_ge in E1.
  destruct (znth d p =? 128).
  - inversion H; subst. lia.
  - destruct (Z.land (znth d p) 128 =? 0).
    + inversion H; subst. split; [lia|]. apply Z.land_nonneg. right. lia.
    + destruct (max - 1 <? Z.land (znth d p) 127) eqn:E2; [discriminate|]. apply Z.ltb_ge in E2.
      destruct (skip_zeros _ d (p + 1) _) as [p1 i1] eqn:Es. apply skip_zeros_bounds in Es.
      destruct (8 <? i1); [discriminate|].
      destruct (be_octets _ d p1 i1 0) as [ret p2] eqn:Eb. apply be_octets_bounds in Eb; [|lia|exact Hd].
      destruct (LONG_MAX <? ret); [discriminate|]. inversion H; subst.
      assert (0 <= Z.land (znth d p) 127) by (apply Z.land_nonneg; right; lia). lia.
Qed.

Lemma get_object_bounds : forall d p omax, Forall (fun b => 0 <= b) d -> 0 < omax ->
  let g := get_object d p omax in
  match go_err g with
  | None => 2 <= go_p g - p /\ 0 <= go_len g /\ go_p g - p + go_len g <= omax
  | Some GeTooLong => 2 <= go_p g - p <= omax /\ 0 <= go_len g
  | Some GeHdr => go_p g = p
  | Some GeTooSmall => False
  end.
Proof.
  intros d p omax Hd Hom. unfold get_object.
  destruct (omax <=? 0) eqn:E0; [apply Z.leb_le in E0; lia|]. cbn -[tag_loop get_length Z.sub Z.add Z.eqb Z.land Z.lor Z.shiftl Z.ltb].
  set (hdr := if Z.land (znth d p) 31 =? 31 then _ else _).
  assert (Hh : match hdr with None => True | Some (tag, p1, max1) => 1 <= p1 - p /\ max1 = omax - (p1 - p) /\ 1 <= max1 end).
  { unfold hdr. destruct (Z.land (znth d p) 31 =? 31).
    - destruct (omax - 1 =? 0) eqn:E1; [exact I|]. apply Z.eqb_neq in E1.
      destruct (tag_loop _ d 0 (p + 1) (omax - 1)) as [[[len p1] max1]|] eqn:Et; [|exact I].
      apply tag_loop_bounds in Et; [|lia]. destruct (max1 - 1 =? 0) eqn:E2; [exact I|]. apply Z.eqb_neq in E2. lia.
    - destruct (omax - 1 =? 0) eqn:E1; [exact I|]. apply Z.eqb_neq in E1. lia. }
  destruct hdr as [[[tag p1] max1]|]; [|cbn; reflexivity].
  destruct Hh as (H1 & H2 & H3).
  destruct (get_length d p1 max1) as [[[inf len] p2]|] eqn:Eg; [|cbn; reflexivity].
  apply get_length_bounds in Eg; [|exact Hd].
  destruct (inf && _); [cbn; reflexivity|].
  destruct (omax - (p2 - p) <? len) eqn:Et; cbn; [apply Z.ltb_lt in Et|apply Z.ltb_ge in Et]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tag_loop_indep : forall f1 d len p max1 len' p' m1,
  1 <= max1 -> tag_loop f1 d len p max1 = Some (len', p', m1) ->
  forall f2 max2, p' - p + 1 <= max2 -> (p' - p < Z.of_nat f2) ->
  tag_loop f2 d len p max2 = Some (len', p', max2 - (p' - p)).
Proof.
  induction f1 as [|f1 IH]; intros d len p max1 len' p' m1 Hm1 H f2 max2 Hm2 Hf2; cbn -[Z.shiftl Z.lor Z.land Z.ltb Z.div Z.eqb Z.sub INT_MAX] in H; [discriminate|].
  assert (B0 : p <= p').
  { destruct (Z.land (znth d p) 128 =? 0); [inversion H; subst; lia|]. destruct (max1 - 1 =? 0) eqn:E1; [discriminate|]. apply Z.eqb_neq in E1.
    destruct (INT_MAX / 128 <? _); [discriminate|]. destruct (Z.le_gt_cases 1 (max1 - 1)) as [Hm|Hm]; [pose proof (tag_loop_bounds _ _ _ _ _ _ _ _ Hm H); lia|].
    exfalso; lia. }
  destruct f2 as [|f2]; [cbn in Hf2; lia|].
  cbn -[Z.shiftl Z.lor Z.land Z.ltb Z.div Z.eqb Z.sub INT_MAX Z.of_nat].
  destruct (Z.land (znth d p) 128 =? 0).
  - inversion H; subst. f_equal. f_equal. lia.
  - destruct (max1 - 1 =? 0) eqn:E1; [discriminate|]. apply Z.eqb_neq in E1.
    destruct (INT_MAX / 128 <? Z.lor (Z.shiftl len 7) (Z.land (znth d p) 127)); [discriminate|].
    assert (Hm1' : 1 <= max1 - 1) by (clear - Hm1 E1; lia). pose proof (tag_loop_bounds _ _ _ _ _ _ _ _ Hm1' H) as (B1 & B2 & B3).
    destruct (Z.eqb_spec (max2 - 1) 0) as [E2|E2]; [exfalso; lia|].
    rewrite (IH d _ (p + 1) (max1 - 1) len' p' m1 Hm1' H f2 (max2 - 1) ltac:(clear H; lia) ltac:(clear H; rewrite Nat2Z.inj_succ in Hf2; lia)).
    f_equal. f_equal. lia.
Qed.

Lemma be_octets_exact : forall fuel d p i acc, 0 <= i -> (Z.to_nat i <= fuel)%nat -> snd (be_octets fuel d p i acc) = p + i.
Proof.
  induction fuel as [|f IH]; intros d p i acc Hi Hf; cbn -[Z.ltb Z.mul Z.add Z.sub znth].
  - cbn. lia.
  - destruct (Z.ltb_spec 0 i).
    + rewrite IH; lia.
    + cbn. lia.
Qed.

Lemma get_length_indep : forall d p max1 inf len p', Forall (fun b => 0 <= b) d ->
  get_length d p max1 = Some (inf, len, p') -> forall max2, p' - p <= max2 -> get_length d p max2 = Some (inf, len, p').
Proof.
  intros d p max1 inf len p' Hd H max2 Hm2. pose proof (get_length_bounds d p max1 inf len p' Hd H) as [B1 B2].
  unfold get_length in *.
  destruct (max1 <? 1) eqn:E1; [discriminate|]. apply Z.ltb_ge in E1.
  destruct (Z.ltb_spec max2 1) as [C|C]; [exfalso; lia|].
  destruct (znth d p =? 128); [exact H|].
  destruct (Z.land (znth d p) 128 =? 0); [exact H|].
  destruct (max1 - 1 <? Z.land (znth d p) 127) eqn:E2; [discriminate|]. apply Z.ltb_ge in E2.
  destruct (skip_zeros _ d (p + 1) _) as [p1 i1] eqn:Es. pose proof (skip_zeros_bounds _ _ _ _ _ _ Es) as (S1 & S2 & S3).
  destruct (8 <? i1); [discriminate|].
  destruct (be_octets _ d p1 i1 0) as [ret p2] eqn:Eb. pose proof (be_octets_bounds _ _ _ _ _ _ _ Eb ltac:(lia) Hd) as (Q1 & Q2 & Q3).
  assert (0 <= Z.land (znth d p) 127) by (apply Z.land_nonneg; right; lia).
  pose proof (be_octets_exact (Z.to_nat i1) d p1 i1 0 ltac:(lia) ltac:(lia)) as EX. rewrite Eb in EX. cbn in EX.
  destruct (LONG_MAX <? ret); [discriminate|]. inversion H; subst.
  destruct (Z.ltb_spec (max2 - 1) (Z.land (znth d p) 127)) as [C2|C2]; [exfalso; lia|reflexivity].
Qed.

(* [comment removed for export] *)
Definition go_hdr (d : list Z) (p0 omax : Z) : option (Z * Z * Z) :=
  if Z.land (znth d p0) 31 =? 31 then
    let p := p0 + 1 in
    let max := omax - 1 in
    if max =? 0 then None
    else
      match tag_loop (Z.to_nat max) d 0 p max with
      | None => None
      | Some (len, p, max) =>
          let len := Z.lor (Z.shiftl len 7) (Z.land (znth d p) 127) in
          let p := p + 1 in
          let max := max - 1 in
          if max =? 0 then None else Some (len, p, max)
      end
  else
    let p := p0 + 1 in
    let max := omax - 1 in
    if max =? 0 then None else Some (Z.land (znth d p0) 31, p, max).

Lemma get_object_eq d p0 omax : get_object d p0 omax =
  (if omax <=? 0 then go_fail GeTooSmall p0
   else match go_hdr d p0 omax with
        | None => go_fail GeHdr p0
        | Some (tag, p, max) =>
            match get_length d p max with
            | None => go_fail GeHdr p0
            | Some (inf, len, p) =>
                if inf && (Z.land (znth d p0) V_ASN1_CONSTRUCTED =? 0) then go_fail GeHdr p0
                else
                  let r := Z.lor (Z.land (znth d p0) V_ASN1_CONSTRUCTED) (if inf then 1 else 0) in
                  if omax - (p - p0) <? len then mkGO (Some GeTooLong) r p len tag (Z.land (znth d p0) 192)
                  else mkGO None r p len tag (Z.land (znth d p0) 192)
            end
        end).
Proof. reflexivity. Qed.

Lemma go_hdr_indep : forall d p0 omax tag p1 max1, 0 < omax -> go_hdr d p0 omax = Some (tag, p1, max1) ->
  1 <= p1 - p0 /\ max1 = omax - (p1 - p0) /\ 1 <= max1 /\
  forall omax2, p1 - p0 + 1 <= omax2 -> go_hdr d p0 omax2 = Some (tag, p1, omax2 - (p1 - p0)).
Proof.
  intros d p0 omax tag p1 max1 Hom H. unfold go_hdr in *.
  destruct (Z.land (znth d p0) 31 =? 31).
  - destruct (Z.eqb_spec (omax - 1) 0) as [E1|E1]; [discriminate|].
    destruct (tag_loop _ d 0 (p0 + 1) (omax - 1)) as [[[len p] max]|] eqn:Et; [|discriminate].
    assert (HM : 1 <= omax - 1) by lia. pose proof (tag_loop_bounds _ _ _ _ _ _ _ _ HM Et) as (B1 & B2 & B3).
    destruct (Z.eqb_spec (max - 1) 0) as [E2|E2]; [discriminate|]. inversion H; subst.
    split; [lia|]. split; [lia|]. split; [lia|].
    intros omax2 Hom2. destruct (Z.eqb_spec (omax2 - 1) 0) as [E3|E3]; [exfalso; lia|].
    rewrite (tag_loop_indep _ _ _ _ _ _ _ _ HM Et (Z.to_nat (omax2 - 1)) (omax2 - 1) ltac:(lia) ltac:(lia)).
    destruct (Z.eqb_spec (omax2 - 1 - (p - (p0 + 1)) - 1) 0) as [E4|E4]; [exfalso; lia|]. f_equal. f_equal. lia.
  - destruct (Z.eqb_spec (omax - 1) 0) as [E1|E1]; [discriminate|]. inversion H; subst.
    split; [lia|]. split; [lia|]. split; [lia|].
    intros omax2 Hom2. destruct (Z.eqb_spec (omax2 - 1) 0) as [E3|E3]; [exfalso; lia|]. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Theorem get_object_inner : forall d p omax, Forall (fun b => 0 <= b) d -> go_err (get_object d p omax) = None ->
  get_object d p (go_p (get_object d p omax) - p + go_len (get_object d p omax)) = get_object d p omax.
Proof.
  intros d p omax Hd. rewrite !(get_object_eq d p).
  destruct (Z.leb_spec omax 0) as [E0|E0]; [cbn; discriminate|].
  destruct (go_hdr d p omax) as [[[tag p1] max1]|] eqn:Eh; [|cbn; discriminate].
  pose proof (go_hdr_indep d p omax tag p1 max1 ltac:(lia) Eh) as (H1 & H2 & H3 & H4).
  destruct (get_length d p1 max1) as [[[inf len] p2]|] eqn:El; [|cbn; discriminate].
  pose proof (get_length_bounds d p1 max1 inf len p2 Hd El) as [G1 G2].
  destruct (inf && (Z.land (znth d p) V_ASN1_CONSTRUCTED =? 0)) eqn:Einf; [cbn; discriminate|].
  destruct (Z.ltb_spec (omax - (p2 - p)) len) as [T|T]; [cbn; discriminate|]. cbn [go_err go_p go_len]. intros _.
  destruct (Z.leb_spec (p2 - p + len) 0) as [E5|E5]; [exfalso; lia|].
  rewrite (H4 (p2 - p + len) ltac:(lia)). rewrite (get_length_indep d p1 max1 inf len p2 Hd El (p2 - p + len - (p1 - p)) ltac:(lia)).
  rewrite Einf. destruct (Z.ltb_spec (p2 - p + len - (p2 - p)) len) as [T2|T2]; [exfalso; lia|reflexivity].
Qed.
