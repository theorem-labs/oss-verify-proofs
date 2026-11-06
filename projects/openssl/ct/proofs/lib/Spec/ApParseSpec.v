(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim PrintfModel BnModel BnTree BgState ApBase ApState ApLogic ApErr ApCnf ApInv
  ApFmt ApParse ApPrim ApObj ApObjTab ApBn ApParse2.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import ApSpecs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

Ltac nlia := unfold SZ_ASN1_STRING, SZ_ASN1_OBJECT, SZ_BIO, SZ_PREFIX_CTX, SZ_CNF_NAME, SZ_CONF, SZ_MUTEX, SZ_LHASH, SZ_LH_BUCKETS in *;
  unfold R_NB, R_TOT, ST_NB, ST_TOT in *; unfold AP_TOT in *; unfold AP_NB, AP_MAX_INPUT in *; unfold zlength in *; simpl; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma digits_aux_length fuel base dig x acc : (length acc <= length (digits_aux fuel base dig x acc) <= fuel + length acc)%nat.
Proof. revert x acc. induction fuel as [|f IH]; intros x acc; cbn; [lia|]. destruct (x =? 0); cbn; [lia|]. specialize (IH (x / base) (dig (x mod base) :: acc)). cbn in IH. lia. Qed.

Lemma digits_aux_S f base dig x acc :
  digits_aux (S f) base dig x acc = if x =? 0 then acc else digits_aux f base dig (x / base) (dig (x mod base) :: acc).
Proof. reflexivity. Qed.

Lemma zdigits_bound v : 1 <= zdigits v <= 20.
Proof.
  unfold zdigits, zdec, zlength. destruct (Z.eqb_spec v 0) as [->|NE]; [cbn; lia|].
  unfold dec_digits. change 20%nat with (S 19). rewrite digits_aux_S. destruct (Z.eqb_spec v 0) as [E|_]; [lia|].
  pose proof (digits_aux_length 19 10 (fun v0 => 48 + v0) (v / 10) [48 + v mod 10]) as H.
  remember (digits_aux 19 10 (fun v0 : Z => 48 + v0) (v / 10) [48 + v mod 10]) as l. clear Heql. cbn [length] in H. lia.
Qed.

Lemma sdigits_bound v : 1 <= sdigits v <= 21.
Proof. unfold sdigits, sdec. pose proof (zdigits_bound (- v)). pose proof (zdigits_bound v). unfold zdigits, zlength in *. destruct (v <? 0); cbn [length]; lia. Qed.

Lemma hdr_len_bound offset depth hl len inf : 0 < hdr_len offset depth hl len inf < 128.
Proof.
  unfold hdr_len, hdr_pieces_len, padw. pose proof (sdigits_bound offset). pose proof (sdigits_bound depth). pose proof (sdigits_bound hl). pose proof (sdigits_bound len).
  unfold sdigits in *. destruct inf; cbn -[Z.max Z.add zlength sdec]; unfold zsum; cbn -[Z.max Z.add zlength sdec]; lia.
Qed.

Lemma ap_bytes_nonneg d : Forall (fun b => 0 <= b) (ap_bytes d).
Proof. unfold ap_bytes. induction d as [|b d IH]; cbn; constructor; [|exact IH]. unfold u8. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Parse.
Context {ptr : Type}.
Local Notation ST := (ap_st ptr) (only parsing).
Variables rcrit rcritS rcritI : Z -> Z -> Prop.      (* [comment removed for export] *)
Variable spre : sysop -> Prop.
Local Notation awp := (awp (okAp AP_NB AP_TOT) rcrit rcritS rcritI spre) (only parsing).
Hypothesis Hrc_grow : forall m, 0 <= m <= 46 -> rcrit m 1024.
Hypothesis Hrc_shrink : forall n, 1 <= n <= 46 -> rcritS 1024 n.
Hypothesis Hspre : forall o, spre o.
Hypothesis obj2txt_num_bwp : forall content X,
  roomy X -> 1 <= zlength content <= 586 ->
  bwp (okAp AP_NB AP_TOT) (tbind (obj2txt_num (tree_ops ptr) content abs0) (fun p => TRet (fst p))) X
      (fun n X' => Permutation X' X /\ -1 <= n <= OBJ_TXT_MAX).
Variable dd : list Z.
Hypothesis Hdd : Forall (fun b => 0 <= b) dd.
Let N := zlength dd.
Hypothesis HN : N <= AP_MAX_INPUT.

Definition Wl (len depth : Z) : Z := 2 * len + 3 * (130 - depth) + 2.
Definition Wp (len depth : Z) : Z := 2 * len + 3 * (130 - depth) + 3.

Definition post_parse (p length : Z) (F : list (ptr * Z)) (r : (Z * Z) * ST) (X' : list (ptr * Z)) : Prop :=
  rel (snd r) F X' /\ p <= snd (fst r) <= p + length /\ (fst (fst r) = 1 -> snd (fst r) = p + length) /\ (fst (fst r) = 2 -> p < snd (fst r))
  /\ (fst (fst r) = 0 \/ fst (fst r) = 1 \/ fst (fst r) = 2).

Definition P_parse (fuel : nat) : Prop := forall p length offset depth (s : ST) F X,
  Wp length depth <= Z.of_nat fuel -> 0 <= p -> 0 <= length -> p + length <= N -> 0 <= depth <= 129 ->
  rel s F X -> bnonneg F -> zlength F <= 2 * depth -> bsum F <= 40 * depth + p ->
  awp (parse2 dd fuel p length offset depth s) X (post_parse p length F).

Definition P_loop (fuel : nat) : Prop := forall p length offset depth pp0 tot o (s : ST) F X,
  Wl length depth <= Z.of_nat fuel -> 0 <= pp0 <= p -> 0 <= length -> tot = p + length -> tot <= N -> 0 <= depth <= 128 ->
  rel s (objb o ++ F) X -> owf o -> bnonneg F -> zlength F <= 2 * depth -> bsum F <= 40 * depth + pp0 -> osum o <= 40 + (p - pp0) ->
  awp (ploop dd fuel p length offset depth pp0 tot o s) X (post_parse p length F).

Definition P_kinf (fuel : nat) : Prop := forall p tot offset depth pp0 (s : ST) F X,
  Wl (tot - p) depth <= Z.of_nat fuel -> 0 <= p <= tot -> tot <= N -> 0 <= depth <= 128 ->
  rel s F X -> bnonneg F -> zlength F <= 2 * (depth + 1) -> bsum F <= 40 * (depth + 1) + p ->
  awp (kids_inf dd fuel p tot offset depth pp0 s) X (fun r X' => rel (snd r) F X' /\ p <= snd (fst r) <= tot).

Definition P_kdef (fuel : nat) : Prop := forall p ep tmp offset depth pp0 (s : ST) F X,
  Wl (ep - p) depth <= Z.of_nat fuel -> tmp = ep - p -> 0 <= p <= ep -> ep <= N -> 0 <= depth <= 128 ->
  rel s F X -> bnonneg F -> zlength F <= 2 * (depth + 1) -> bsum F <= 40 * (depth + 1) + p ->
  awp (kids_def dd fuel p ep tmp offset depth pp0 s) X (fun r X' => rel (snd r) F X' /\ p <= snd (fst r) <= ep /\ (fst (fst r) = true -> snd (fst r) = ep)).

(* [comment removed for export] *)
Lemma parse2_S f p length offset depth :
  parse2 (ptr:=ptr) dd (S f) p length offset depth =
  (if ASN1_PARSE_MAXDEPTH <? depth then aret (0, p) else ploop dd f p length offset depth p (p + length) ONone).
Proof. reflexivity. Qed.
Lemma kids_inf_S f p tot offset depth pp0 :
  kids_inf (ptr:=ptr) dd (S f) p tot offset depth pp0 =
  (' (r, p') <- parse2 dd f p (tot - p) (offset + (p - pp0)) (depth + 1) ;;
   if r =? 0 then aret (false, p') else if (r =? 2) || (tot <=? p') then aret (true, p') else kids_inf dd f p' tot offset depth pp0).
Proof. reflexivity. Qed.
Lemma kids_def_S f p ep tmp offset depth pp0 :
  kids_def (ptr:=ptr) dd (S f) p ep tmp offset depth pp0 =
  (if p <? ep then
     ' (r, p') <- parse2 dd f p tmp (offset + (p - pp0)) (depth + 1) ;;
     if r =? 0 then aret (false, p') else kids_def dd f p' ep (tmp - (p' - p)) offset depth pp0
   else aret (true, p)).
Proof. reflexivity. Qed.

Lemma ploop_S f p length offset depth pp0 tot o :
  ploop (ptr:=ptr) dd (S f) p length offset depth pp0 tot o =
  (if length <=? 0 then asn1_object_free o ;;; aret (1, p)
   else
     let op := p in
     let g := get_object dd op length in
     match go_err g with
     | Some GeTooSmall => aunr
     | Some GeHdr => err_raise RS_hdr_too_long ;;; asn1_object_free o ;;; aret (0, go_p g)
     | Some GeTooLong => err_raise RS_too_long ;;; asn1_object_free o ;;; aret (0, go_p g)
     | None =>
         let p := go_p g in
         let hl := p - op in
         let length := length - hl in
         let len := go_len g in
         let j := go_ret g in
         let tag := go_tag g in
         let xclass := go_cls g in
         print_info (offset + (op - pp0)) depth hl len j ;;;
         if negb (Z.land j V_ASN1_CONSTRUCTED =? 0) then
           if length <? len then asn1_object_free o ;;; aret (0, p)
           else if (j =? 33) && (len =? 0) then
             ' (ok, p') <- kids_inf dd f p tot offset depth pp0 ;;
             if ok then ploop dd f p' (length - (p' - p)) offset depth pp0 tot o else asn1_object_free o ;;; aret (0, p')
           else
             ' (ok, p') <- kids_def dd f p (p + len) len offset depth pp0 ;;
             if ok then ploop dd f p' (length - len) offset depth pp0 tot o else asn1_object_free o ;;; aret (0, p')
         else if negb (xclass =? 0) then ploop dd f (p + len) (length - len) offset depth pp0 tot o
         else
           o' <- prim_content dd o tag op hl len ;;
           let p := p + len in
           if tag =? 0 then asn1_object_free o' ;;; aret (2, p) else ploop dd f p (length - len) offset depth pp0 tot o'
     end).
Proof. reflexivity. Qed.

Lemma parse_all : forall fuel, P_parse fuel /\ P_loop fuel /\ P_kinf fuel /\ P_kdef fuel.
Proof.
  induction fuel as [|f IH].
  { split; [|split; [|split]]; red; intros; exfalso; unfold Wp, Wl in *; cbn [Z.of_nat] in *; lia. }
  destruct IH as (IHp & IHl & IHi & IHd).
  split; [|split; [|split]].
  - (* [comment removed for export] *)
    red. intros p length offset depth s F X HW Hp Hl HpN Hd HR HFn HFc HFs.
    rewrite parse2_S. destruct (Z.ltb_spec ASN1_PARSE_MAXDEPTH depth) as [Hgt|Hle].
    + cbn. split; [exact HR|]. cbn. split; [lia|]. split; [intros E; discriminate|]. split; [intros E; discriminate|]. left; reflexivity.
    + apply (IHl p length offset depth p (p + length) ONone s F X); try assumption; try lia.
      * unfold Wp, Wl in *. rewrite Nat2Z.inj_succ in HW. lia.
      * unfold ASN1_PARSE_MAXDEPTH in Hle. lia.
      * exact I.
      * unfold osum, objb. rewrite bsum_nil. lia.
  - (* [comment removed for export] *)
    red. intros p length offset depth pp0 tot o s F X HW Hpp0 Hl Htot HtN Hd HR Ho HFn HFc HFs Hos.
    rewrite ploop_S. destruct (Z.leb_spec length 0) as [Hz|Hnz].
    + apply awp_abind. eapply awp_mono; [apply asn1_object_free_spec; exact HR|]. intros [u1 s1] X1 [HR1 E1]. cbn in HR1, E1. subst s1. cbn.
      split; [exact HR1|]. cbn. repeat split; intros; try discriminate; lia.
    + pose proof (get_object_bounds dd p length Hdd Hnz) as GB. cbn zeta in GB.
      destruct (objb_facts o Ho) as (Hon & Hoz & Ho0). pose proof (bnonneg_sum F HFn) as HF0.
      assert (HFR : frameR (objb o ++ F)).
      { unfold frameR. rewrite zlen_app', bsum_app. unfold osum in Hos. split; [nlia|]. split; [nlia|]. apply bnonneg_app; assumption. }
      cbn zeta. destruct (go_err (get_object dd p length)) as [[| |]|] eqn:Eg.
      * (* [comment removed for export] *)
        apply awp_abind. eapply awp_mono; [apply (err_raise_spec rcrit rcritS rcritI spre); [exact HR|exact HFR|cbn; lia|cbn; lia]|]. intros [u1 s1] X1 (HR1 & _). cbn [fst snd] in *.
        apply awp_abind. eapply awp_mono; [apply asn1_object_free_spec; exact HR1|]. intros [u2 s2] X2 [HR2 E2]. cbn in HR2, E2; subst s2. cbn.
        split; [exact HR2|]. cbn. rewrite GB. repeat split; intros; try discriminate; lia.
      * (* [comment removed for export] *)
        apply awp_abind. eapply awp_mono; [apply (err_raise_spec rcrit rcritS rcritI spre); [exact HR|exact HFR|cbn; lia|cbn; lia]|]. intros [u1 s1] X1 (HR1 & _). cbn [fst snd] in *.
        apply awp_abind. eapply awp_mono; [apply asn1_object_free_spec; exact HR1|]. intros [u2 s2] X2 [HR2 E2]. cbn in HR2, E2; subst s2. cbn.
        split; [exact HR2|]. cbn. repeat split; intros; try discriminate; lia.
      * exfalso. exact GB.
      * (* [comment removed for export] *)
        destruct GB as (Ghl & Glen & Gfit). set (g := get_object dd p length) in *.
        assert (HW' : 2 * length + 3 * (130 - depth) + 1 <= Z.of_nat f) by (unfold Wl in HW; rewrite Nat2Z.inj_succ in HW; lia).
        apply awp_abind. eapply awp_mono; [apply (print_info_spec rcrit rcritS rcritI spre); [exact HR|exact HFR|apply hdr_len_bound]|]. intros [u1 s1] X1 [HR1 E1]. cbn [fst snd] in HR1, E1. subst s1. cbn [fst snd].
        assert (HoF : bsum (objb o ++ F) <= 40 * (depth + 1) + go_p g) by (rewrite bsum_app; unfold osum in Hos; lia).
        assert (HcF : zlength (objb o ++ F) <= 2 * (depth + 1)) by (rewrite zlen_app'; lia).
        assert (HnF : bnonneg (objb o ++ F)) by (apply bnonneg_app; assumption).
        destruct (negb (Z.land (go_ret g) V_ASN1_CONSTRUCTED =? 0)).
        -- (* [comment removed for export] *)
           destruct (Z.ltb_spec (length - (go_p g - p)) (go_len g)) as [Hlt|Hge].
           ++ apply awp_abind. eapply awp_mono; [apply asn1_object_free_spec; exact HR1|]. intros [u2 s2] X2 [HR2 E2]. cbn in HR2, E2; subst s2. cbn.
              split; [exact HR2|]. cbn. repeat split; intros; try discriminate; lia.
           ++ destruct ((go_ret g =? 33) && (go_len g =? 0)).
              ** apply awp_abind. eapply awp_mono; [apply (IHi (go_p g) tot offset depth pp0 s (objb o ++ F) X1); try assumption; try lia|].
                 { unfold Wl. lia. }
                 intros [[ok p'] s2] X2 [HR2 Hb2]. cbn [fst snd] in *. destruct ok.
                 +++ eapply awp_mono; [apply (IHl p' (length - (go_p g - p) - (p' - go_p g)) offset depth pp0 tot o s2 F X2); try assumption; try lia|].
                     { unfold Wl. lia. }
                     intros [[r p''] s3] X3 (HR3 & A3 & B3 & C3 & D3). cbn [fst snd] in *. unfold post_parse; cbn [fst snd]. split; [exact HR3|]. repeat split; try lia; try (intros E; specialize (C3 E); lia).
                 +++ apply awp_abind. eapply awp_mono; [apply asn1_object_free_spec; exact HR2|]. intros [u3 s3] X3 [HR3 E3]. cbn in HR3, E3; subst s3. cbn.
                     split; [exact HR3|]. cbn. repeat split; intros; try discriminate; lia.
              ** apply awp_abind. eapply awp_mono; [apply (IHd (go_p g) (go_p g + go_len g) (go_len g) offset depth pp0 s (objb o ++ F) X1); try assumption; try lia|].
                 { unfold Wl. lia. }
                 intros [[ok p'] s2] X2 (HR2 & Hb2 & Hok2). cbn [fst snd] in *. destruct ok.
                 +++ specialize (Hok2 eq_refl).
                     eapply awp_mono; [apply (IHl p' (length - (go_p g - p) - go_len g) offset depth pp0 tot o s2 F X2); try assumption; try lia|].
                     { unfold Wl. lia. }
                     intros [[r p''] s3] X3 (HR3 & A3 & B3 & C3 & D3). cbn [fst snd] in *. unfold post_parse; cbn [fst snd]. split; [exact HR3|]. repeat split; try lia; try (intros E; specialize (C3 E); lia).
                 +++ apply awp_abind. eapply awp_mono; [apply asn1_object_free_spec; exact HR2|]. intros [u3 s3] X3 [HR3 E3]. cbn in HR3, E3; subst s3. cbn.
                     split; [exact HR3|]. cbn. repeat split; intros; try discriminate; lia.
        -- destruct (Z.eqb_spec (go_cls g) 0) as [Hcls|Hcls]; cbn [negb].
           ++ (* [comment removed for export] *)
              apply awp_abind. eapply awp_mono; [apply (prim_content_spec rcrit rcritS rcritI spre Hrc_grow Hrc_shrink Hspre obj2txt_num_bwp dd o p length s F X1); try assumption; try lia|].
              { fold g. unfold R_NB, AP_NB in *. lia. }
              { fold g. rewrite bsum_app in *. unfold osum in *. unfold R_TOT in *; unfold AP_TOT in *; unfold AP_MAX_INPUT in *. lia. }
              intros [o' s2] X2 (HR2 & Ho2 & Hos2). cbn [fst snd] in HR2, Ho2, Hos2. fold g in Hos2. cbn [fst snd].
              destruct (Z.eqb_spec (go_tag g) 0) as [Ht0|Ht0].
              ** apply awp_abind. eapply awp_mono; [apply asn1_object_free_spec; exact HR2|]. intros [u3 s3] X3 [HR3 E3]. cbn in HR3, E3; subst s3. cbn.
                 split; [exact HR3|]. cbn. repeat split; intros; try discriminate; lia.
              ** eapply awp_mono; [apply (IHl (go_p g + go_len g) (length - (go_p g - p) - go_len g) offset depth pp0 tot o' s2 F X2); try assumption; try lia|].
                 { unfold Wl. lia. }
                 intros [[r p''] s3] X3 (HR3 & A3 & B3 & C3 & D3). cbn [fst snd] in *. unfold post_parse; cbn [fst snd]. split; [exact HR3|]. repeat split; try lia; try (intros E; specialize (C3 E); lia).
           ++ (* [comment removed for export] *)
              eapply awp_mono; [apply (IHl (go_p g + go_len g) (length - (go_p g - p) - go_len g) offset depth pp0 tot o s F X1); try assumption; try lia|].
              { unfold Wl. lia. }
              intros [[r p''] s3] X3 (HR3 & A3 & B3 & C3 & D3). cbn [fst snd] in *. unfold post_parse; cbn [fst snd]. split; [exact HR3|]. repeat split; try lia; try (intros E; specialize (C3 E); lia).
  - (* [comment removed for export] *)
    red. intros p tot offset depth pp0 s F X HW Hp Ht Hd HR HFn HFc HFs.
    rewrite kids_inf_S. apply awp_abind. eapply awp_mono.
    { apply (IHp p (tot - p) (offset + (p - pp0)) (depth + 1) s F X); try assumption; try lia.
      unfold Wp, Wl in *. rewrite Nat2Z.inj_succ in HW. lia. }
    intros [[r p'] s1] X1 (HR1 & Hb1 & H1 & H2 & Hr). cbn [fst snd] in *.
    destruct (Z.eqb_spec r 0) as [->|NE0]; [cbn; split; [exact HR1|lia]|].
    destruct (Z.eqb_spec r 2) as [->|NE2]; [cbn; split; [exact HR1|lia]|].
    destruct (Z.leb_spec tot p') as [Hge|Hlt]; [cbn; split; [exact HR1|lia]|].
    exfalso. destruct Hr as [Hr|[Hr|Hr]]; try contradiction. specialize (H1 Hr). lia.
  - (* [comment removed for export] *)
    red. intros p ep tmp offset depth pp0 s F X HW Htmp Hp He Hd HR HFn HFc HFs.
    rewrite kids_def_S. destruct (Z.ltb_spec p ep) as [Hlt|Hge]; [|cbn; split; [exact HR|split; [lia|intros _; lia]]].
    apply awp_abind. eapply awp_mono.
    { apply (IHp p tmp (offset + (p - pp0)) (depth + 1) s F X); try assumption; try lia.
      unfold Wp, Wl in *. rewrite Nat2Z.inj_succ in HW. lia. }
    intros [[r p'] s1] X1 (HR1 & Hb1 & H1 & H2 & Hr). cbn [fst snd] in *.
    destruct (Z.eqb_spec r 0) as [->|NE0]; [cbn; split; [exact HR1|split; [lia|intros; discriminate]]|].
    eapply awp_mono.
    { apply (IHd p' ep (tmp - (p' - p)) offset depth pp0 s1 F X1); try assumption; try lia.
      unfold Wl in *. rewrite Nat2Z.inj_succ in HW. destruct Hr as [Hr|[Hr|Hr]]; [contradiction| |]; [specialize (H1 Hr)|specialize (H2 Hr)]; lia. }
    intros [[ok p''] s2] X2 (HR2 & Hb2 & Hok2). cbn [fst snd] in *. split; [exact HR2|split; [lia|exact Hok2]].
Qed.
End Parse.
