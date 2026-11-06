(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Uint63.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import W64 ITrie FxInstr FxState FxMem FxImage FxHandoff FxHoBuild FxHandoff2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope uint63_scope.

(* [comment removed for export] *)
Definition sure_disj (o l P : int) : bool :=
  (o <? b62) && (l <=? b62) && ((P + 4096 <=? o) || (o + l <=? P)).

Definition rel (t P : int) (f : hfact) : bool :=
  match f with
  | HCell t' o n _ => if t' =? t then negb (sure_disj o n P) else false
  | HVal t' o _ => if t' =? t then negb (sure_disj o 8 P) else false
  | HBytes t' o n _ => if t' =? t then negb (sure_disj o n P) else false
  | HZero t' o l => if t' =? t then negb (sure_disj o l P) else false
  | HWr t' o l => if t' =? t then negb (sure_disj o l P) else false
  | HClear lo hi => negb ((hi <=? P) || (P + 4096 <=? lo))
  | _ => false
  end.

Lemma iseq_ltL n ci : In ci (iseq n) -> (to_Z ci < Z.of_nat n)%Z.
Proof.
  unfold iseq. intros H. apply in_map_iff in H as (k & <- & Hk). apply in_seq in Hk.
  rewrite Uint63.of_Z_spec. pose proof (Z.mod_pos_bound (Z.of_nat k) wB ltac:(change wB with 9223372036854775808%Z; lia)).
  assert (Z.of_nat k mod wB <= Z.of_nat k)%Z by (apply Z.mod_le; [lia | change wB with 9223372036854775808%Z; lia]). lia.
Qed.

Lemma existsb_filter {T : Type} (g h : T -> bool) (l : list T) : existsb g (filter h l) = true -> existsb g l = true.
Proof.
  intros H. apply existsb_exists in H as (x & Hx & Hg). apply filter_In in Hx as [Hx _]. apply existsb_exists. exists x. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma sure_disj_in_iv o l P a n :
  (to_Z P + 4096 <= 2 ^ 62)%Z -> (to_Z P <= to_Z a)%Z -> (to_Z a + to_Z n <= to_Z P + 4096)%Z -> (1 <= to_Z n)%Z ->
  sure_disj o l P = true -> in_iv o l a n = false.
Proof.
  intros HP Ha Han Hn Hd. unfold sure_disj in Hd. apply andb_prop in Hd as [Hd Hor]. apply andb_prop in Hd as [Ho Hl].
  apply i_ltb_lt in Ho. apply i_leb_le in Hl. rewrite ho_b62 in Ho, Hl.
  destruct (in_iv o l a n) eqn:Ei; [exfalso|reflexivity]. unfold in_iv in Ei.
  apply andb_prop in Ei as [Ei H6]. apply andb_prop in Ei as [Ei H5]. apply andb_prop in Ei as [Ei H4]. apply andb_prop in Ei as [Ei H3].
  apply i_leb_le in H5, H6, H4. apply i_ltb_lt in H3. rewrite ho_b62 in H3, H4.
  pose proof (i63_range o). pose proof (i63_range l). pose proof (i63_range a). pose proof (i63_range n). pose proof (i63_range P).
  rewrite !toZ_add_small in H6 by lia.
  apply orb_prop in Hor as [Hq|Hq]; apply i_leb_le in Hq.
  - rewrite toZ_add_small in Hq by (change (to_Z 4096) with 4096%Z; lia). change (to_Z 4096) with 4096%Z in Hq. lia.
  - rewrite toZ_add_small in Hq by lia. lia.
Qed.

Section Local.
Variable IM : fimage.
Variable facts : list hfact.

Lemma byte_known_rel t P a : forall fs,
  (to_Z P + 4096 <= 2 ^ 62)%Z -> (to_Z P <= to_Z a < to_Z P + 4096)%Z ->
  byte_known_in IM (filter (rel t P) fs) t a = byte_known_in IM fs t a.
Proof.
  intros fs HP Ha. pose proof (i63_range P) as HP0. pose proof (i63_range a) as Ha0.
  assert (Hin : forall o l, sure_disj o l P = true -> in_iv o l a 1 = false).
  { intros o l Hd. apply (sure_disj_in_iv o l P a 1 HP); [lia | change (to_Z 1) with 1%Z; lia | change (to_Z 1) with 1%Z; lia | exact Hd]. }
  induction fs as [|f r IH]; [reflexivity|]. cbn [filter].
  destruct f as [t' o n w | t' o v | t' o n v | t' o l | lo hi | t' o l | rr v | t' lo len al | t1 lo1 len1 t2 lo2 len2]; cbn [rel].
  - (* [comment removed for export] *) destruct (t' =? t) eqn:Et.
    + destruct (sure_disj o n P) eqn:Ed; cbn [negb].
      * cbn [byte_known_in]. rewrite Et, (Hin o n Ed), andb_false_r. cbn [andb]. exact IH.
      * cbn [byte_known_in]. rewrite IH. reflexivity.
    + cbn [byte_known_in]. rewrite Et. cbn [andb]. exact IH.
  - (* [comment removed for export] *) destruct (t' =? t) eqn:Et.
    + destruct (sure_disj o 8 P) eqn:Ed; cbn [negb].
      * cbn [byte_known_in]. rewrite Et, (Hin o 8 Ed), andb_false_r. cbn [andb]. exact IH.
      * cbn [byte_known_in]. rewrite IH. reflexivity.
    + cbn [byte_known_in]. rewrite Et. cbn [andb]. exact IH.
  - (* [comment removed for export] *) destruct (if t' =? t then negb (sure_disj o n P) else false); cbn [byte_known_in]; exact IH.
  - (* [comment removed for export] *) destruct (t' =? t) eqn:Et.
    + destruct (sure_disj o l P) eqn:Ed; cbn [negb].
      * cbn [byte_known_in]. rewrite Et, (Hin o l Ed). cbn [andb]. exact IH.
      * cbn [byte_known_in]. rewrite IH. reflexivity.
    + cbn [byte_known_in]. rewrite Et. cbn [andb]. exact IH.
  - (* [comment removed for export] *) destruct ((hi <=? P) || (P + 4096 <=? lo)) eqn:Ed; cbn [negb].
    + cbn [byte_known_in].
      assert (Ec : ((t =? 0) && (lo <=? a) && (a <? hi) && (hi <=? b62)) = false).
      { destruct ((t =? 0) && (lo <=? a) && (a <? hi) && (hi <=? b62)) eqn:Ec; [exfalso|reflexivity].
        apply andb_prop in Ec as [Ec _]. apply andb_prop in Ec as [Ec H2]. apply andb_prop in Ec as [_ H1].
        apply i_leb_le in H1. apply i_ltb_lt in H2.
        apply orb_prop in Ed as [Hq|Hq]; apply i_leb_le in Hq.
        - lia.
        - rewrite toZ_add_small in Hq by (change (to_Z 4096) with 4096%Z; lia). change (to_Z 4096) with 4096%Z in Hq. lia. }
      rewrite Ec. exact IH.
    + cbn [byte_known_in]. rewrite IH. reflexivity.
  - (* [comment removed for export] *) destruct (if t' =? t then negb (sure_disj o l P) else false); cbn [byte_known_in]; exact IH.
  - cbn [byte_known_in]. exact IH.
  - cbn [byte_known_in]. exact IH.
  - cbn [byte_known_in]. exact IH.
Qed.

(* [comment removed for export] *)
Definition pfacts (t pn : int) : list hfact := filter (rel t (pn << 12)) facts.

Definition page_ok_b2L (r : rdesc) (p : pdesc) : bool :=
  (pd_pn p <? b50) && page_ok_b2 IM (pfacts (rd_tag r) (pd_pn p)) r p.

Section Page.
Variable t pn : int.
Hypothesis Hpn : (to_Z pn < 2 ^ 50)%Z.
Local Notation P := (pn << 12).
Local Notation F' := (pfacts t pn).

Lemma P_Z : to_Z P = (to_Z pn * 4096)%Z.
Proof.
  pose proof (i63_range pn). pose proof Hpn as Hq.
  rewrite (toZ_lsl_small pn 12 12%uint63); [reflexivity | reflexivity | lia |].
  change (2 ^ 12)%Z with 4096%Z. change (2 ^ 63)%Z with (2 ^ 50 * 8192)%Z. lia.
Qed.

Lemma P_small : (to_Z P + 4096 <= 2 ^ 62)%Z.
Proof. pose proof Hpn as Hq. rewrite P_Z. change (2 ^ 62)%Z with (2 ^ 50 * 4096)%Z. lia. Qed.

Lemma byte_known_page a : (to_Z P <= to_Z a < to_Z P + 4096)%Z -> byte_known IM F' t a = byte_known IM facts t a.
Proof. intros Ha. unfold byte_known, pfacts. exact (byte_known_rel t P a facts P_small Ha). Qed.

(* [comment removed for export] *)
Lemma cell_byte_in ci j : (to_Z ci < 512)%Z -> (to_Z j < 8)%Z ->
  (to_Z P <= to_Z (P + (ci << 3) + j) < to_Z P + 4096)%Z.
Proof.
  intros Hci Hj. pose proof (i63_range ci). pose proof (i63_range j). pose proof (i63_range pn). pose proof P_small as HPs.
  assert (Ec : to_Z (ci << 3) = (to_Z ci * 8)%Z).
  { rewrite (toZ_lsl_small ci 3 3%uint63); [reflexivity | reflexivity | lia | change (2 ^ 3)%Z with 8%Z; lia]. }
  rewrite !toZ_add_small; rewrite ?toZ_add_small, ?Ec; lia.
Qed.

Lemma cell_ok_L ci v : (to_Z ci < 512)%Z -> cell_ok IM F' t (P + (ci << 3)) v = true -> cell_ok IM facts t (P + (ci << 3)) v = true.
Proof.
  intros Hci. unfold cell_ok. destruct (vtag v =? 0).
  - intros Hc. apply forallb_forall. intros j Hj. rewrite forallb_forall in Hc. pose proof (Hc j Hj) as H1. cbn beta in H1.
    pose proof (iseq_ltL 8 j Hj) as Hj8. change (Z.of_nat 8) with 8%Z in Hj8.
    rewrite (byte_known_page _ (cell_byte_in ci j Hci Hj8)) in H1. exact H1.
  - apply existsb_filter.
Qed.

Lemma slot_ok_L ci j sl : (to_Z ci < 512)%Z -> (to_Z j < 8)%Z ->
  slot_ok_b IM F' t (P + (ci << 3) + j) sl = true -> slot_ok_b IM facts t (P + (ci << 3) + j) sl = true.
Proof.
  intros Hci Hj. destruct sl as [b | v jj |]; cbn [slot_ok_b].
  - rewrite (byte_known_page _ (cell_byte_in ci j Hci Hj)). exact (fun H => H).
  - unfold sv_cov. apply existsb_filter.
  - exact (fun H => H).
Qed.
End Page.

Lemma page_ok_b2L_ok r p : page_ok_b2L r p = true -> page_ok_b2 IM facts r p = true.
Proof.
  unfold page_ok_b2L. intros H. apply andb_prop in H as [Hpn H]. apply i_ltb_lt in Hpn. rewrite ho_b50 in Hpn.
  set (t := rd_tag r) in *. set (pn := pd_pn p) in *.
  assert (Hcells : page_cells_b2 IM (pfacts t pn) r p = true -> page_cells_b2 IM facts r p = true).
  { unfold page_cells_b2. cbv zeta. intros Hc. apply forallb_forall. intros ci Hci. rewrite forallb_forall in Hc.
    pose proof (Hc ci Hci) as H1. cbn beta in H1. destruct (plim r (pd_pn p) <=? ci); [reflexivity|].
    rewrite ho_iseq512_eq in Hci. pose proof (iseq_ltL 512 ci Hci) as Hci5. change (Z.of_nat 512) with 512%Z in Hci5.
    unfold cell_chk in *. cbv zeta in *. fold t pn in H1 |- *.
    destruct (iget ci (pg_cells (page_of p))) as [[v | | sl]|].
    - exact (cell_ok_L t pn Hpn ci v Hci5 H1).
    - reflexivity.
    - apply forallb_forall. intros j Hj. rewrite forallb_forall in H1. pose proof (H1 j Hj) as H2. cbn beta in H2.
      rewrite ho_iseq8_eq in Hj. pose proof (iseq_ltL 8 j Hj) as Hj8. change (Z.of_nat 8) with 8%Z in Hj8.
      exact (slot_ok_L t pn Hpn ci j _ Hci5 Hj8 H2).
    - destruct (pd_kind p); [unfold zero_cov in *; exact (existsb_filter _ _ _ H1) | unfold clear_cov in *; exact (existsb_filter _ _ _ H1) | reflexivity]. }
  unfold page_ok_b2 in *. fold t pn in H |- *.
  assert (Hhdr : page_hdr_b2 IM (pfacts t pn) r p = true -> page_hdr_b2 IM facts r p = true).
  { unfold page_hdr_b2. cbv zeta. fold t pn. intros Hh.
    apply andb_prop in Hh as [Hh HE]. apply andb_prop in Hh as [Hh HW]. rewrite Hh, HE. cbn [andb]. rewrite andb_true_r.
    destruct (pd_wr p); [|reflexivity]. destruct (t =? 0); [exact HW|]. unfold wr_cov in *. exact (existsb_filter _ _ _ HW). }
  destruct (page_hdr_b2 IM (pfacts t pn) r p) eqn:Eh; [|discriminate]. rewrite (Hhdr eq_refl).
  destruct (pd_cells p) as [|c cs]; [|exact (Hcells H)].
  destruct (pd_kind p); try exact (Hcells H).
  destruct (zero_cov (pfacts t pn) t (pn << 12) (plim r pn << 3)) eqn:Ez.
  - unfold zero_cov in Ez. apply existsb_filter in Ez. fold (zero_cov facts t (pn << 12) (plim r pn << 3)) in Ez. rewrite Ez. reflexivity.
  - destruct (zero_cov facts t (pn << 12) (plim r pn << 3)); [reflexivity | exact (Hcells H)].
Qed.

(* [comment removed for export] *)
Definition relT (t : int) (f : hfact) : bool :=
  match f with
  | HCell t' _ _ _ | HVal t' _ _ | HBytes t' _ _ _ | HZero t' _ _ | HWr t' _ _ => t' =? t
  | HClear _ _ => true
  | _ => false
  end.
Lemma rel_relT t P f : rel t P f = true -> relT t f = true.
Proof. destruct f; cbn [rel relT]; try discriminate; try reflexivity; destruct (_ =? t); (reflexivity || discriminate). Qed.
Lemma filter_filter_imp {T : Type} (g h : T -> bool) : (forall x, g x = true -> h x = true) -> forall l, filter g (filter h l) = filter g l.
Proof.
  intros Hi. induction l as [|x l IH]; [reflexivity|]. cbn [filter]. destruct (h x) eqn:Eh.
  - cbn [filter]. rewrite IH. reflexivity.
  - destruct (g x) eqn:Eg; [rewrite (Hi x Eg) in Eh; discriminate | exact IH].
Qed.
Definition page_ok_b2T (tf : list hfact) (r : rdesc) (p : pdesc) : bool :=
  (pd_pn p <? b50) && page_ok_b2 IM (filter (rel (rd_tag r) (pd_pn p << 12)) tf) r p.
Lemma page_ok_b2T_ok r p : page_ok_b2T (filter (relT (rd_tag r)) facts) r p = true -> page_ok_b2 IM facts r p = true.
Proof.
  unfold page_ok_b2T. rewrite (filter_filter_imp _ _ (rel_relT (rd_tag r) (pd_pn p << 12))). exact (page_ok_b2L_ok r p).
Qed.

(* [comment removed for export] *)
Definition region_ok_b2L (d : sdesc) (r : rdesc) : bool :=
  region_fact_b facts r
  && forallb (fun r' => (rd_tag r' =? rd_tag r) || disj_fact_b facts r r') (sd_mem d)
  && (let tf := filter (relT (rd_tag r)) facts in forallb (page_ok_b2T tf r) (rd_pages r))
  && (if rd_tag r =? 0 then
        image_pages_ok IM facts r && (match rd_dflt r with None => true | Some _ => false end)
      else
        match rd_dflt r with
        | None => true
        | Some PKUnk => (rd_lo r <=? rd_len r) && wr_cov facts (rd_tag r) (rd_lo r) (rd_len r - rd_lo r)
        | Some PKZero => (rd_lo r <=? rd_len r) && wr_cov facts (rd_tag r) (rd_lo r) (rd_len r - rd_lo r)
                         && zero_cov facts (rd_tag r) (rd_lo r) (rd_len r - rd_lo r)
        | Some PKImage => false
        end).

Definition ho_check2L (d : sdesc) : bool :=
  regs_ok_b facts d && forallb (region_ok_b2L d) (sd_mem d).

Theorem ho_check2L_ok d : ho_check2L d = true -> ho_check2 IM facts d = true.
Proof.
  unfold ho_check2L, ho_check2. intros H. apply andb_prop in H as [H1 H2]. rewrite H1. cbn [andb].
  apply forallb_forall. intros r Hr. rewrite forallb_forall in H2. pose proof (H2 r Hr) as H3.
  unfold region_ok_b2L in H3. unfold region_ok_b2.
  apply andb_prop in H3 as [H3 H4]. apply andb_prop in H3 as [H3 H5]. rewrite H3, H4. cbn [andb]. rewrite andb_true_r.
  cbv zeta in H5. apply forallb_forall. intros p Hp. rewrite forallb_forall in H5. exact (page_ok_b2T_ok r p (H5 p Hp)).
Qed.
End Local.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hfact_pages (t : int) (f : hfact) : list int :=
  let span (o n : int) :=
    if (0 <? n) && (n <=? 1048576)
    then pages_list (S (Z.to_nat (to_Z (((o + n - 1) >> 12) - (o >> 12))))) (o >> 12) ((o + n - 1) >> 12) else [] in
  match f with
  | HCell t' o n _ | HBytes t' o n _ | HZero t' o n => if t' =? t then span o n else []
  | HVal t' o _ => if t' =? t then span o 8 else []
  | _ => []
  end.

Definition region_desc2L (IM : fimage) (facts : list hfact) (shape : int * int * int * int * option pkind) : rdesc :=
  let '(t, lo, len, al, dflt) := shape in
  if t =? 0 then region_desc2 IM facts shape
  else
    let pns := map fst (ielements (fold_left (fun acc pn => iset pn tt acc) (flat_map (hfact_pages t) facts) iempty)) in
    RD t lo len al dflt
       (flat_map (fun pn => filter (fun p => pd_pn p =? pn) (rd_pages (region_desc2 IM (filter (rel t (pn << 12)) facts) shape))) pns).

