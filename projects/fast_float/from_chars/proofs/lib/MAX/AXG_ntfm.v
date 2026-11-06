(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import MngImage MngSurgery.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Ltac msimp := cbn [ibind fst snd set_metas st_metas st_active links_of with_links am_prev am_next am_set_links am_set_freed osptr_eqb andb negb].
Ltac mlk := repeat first [ rewrite mlookup_mupdate_same | rewrite mlookup_mupdate_other by congruence ].

Definition ntf_freed (am : ameta) (i : Z) : ameta := am_set_freed (Z.lor (am_freed am) (bit i)) am.

(* [comment removed for export] *)
Definition ntf_e12 (s : astate) (g : sptr) (am : ameta) (i : Z) : astate := set_meta s g (MUsed (ntf_freed am i)).
(* [comment removed for export] *)
Definition ntf_e3 (s : astate) (g : sptr) (am : ameta) (i : Z) : astate :=
  set_active (lupd (st_active s) (Z.to_nat (am_sc am)) (Some g)) (set_meta s g (MUsed (ntf_freed (am_set_links (Some g) (Some g) am) i))).
(* [comment removed for export] *)
Definition ntf_e4 (s : astate) (g : sptr) (am : ameta) (i : Z) (h : sptr) (amh : ameta) (hp : sptr) (amhp : ameta) : astate :=
  set_meta (set_meta (set_meta s g (MUsed (ntf_freed (am_set_links (Some hp) (Some h) am) i))) hp (MUsed (am_set_links (am_prev amhp) (Some g) amhp)))
           h (MUsed (am_set_links (Some g) (am_next amh) amh)).
Definition ntf_e4s (s : astate) (g : sptr) (am : ameta) (i : Z) (h : sptr) (amh : ameta) : astate :=
  set_meta (set_meta s g (MUsed (ntf_freed (am_set_links (Some h) (Some h) am) i))) h (MUsed (am_set_links (Some g) (Some g) amh)).

Section E.
Variables (fuel : nat) (g : sptr) (i : Z) (s : astate) (am : ameta).
Hypothesis Mg : MT s g = Some (MUsed am).
Hypothesis Hcond : (Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am)) && okay_to_free s g am = false.

#[using="Mg Hcond"] Lemma ntf_e12_itree : (Z.lor (am_freed am) (am_avail am) <> 0 \/ (Z.lor (am_freed am) (am_avail am) = 0 /\ am_sc am < 48 /\ active_hd s (am_sc am) = Some g)) ->
  nontrivial_free (S fuel) g i s = IRet (None, ntf_e12 s g am i).
Proof. LiaFast.lf_pins (fun (Mg Hcond : LiaFast.U) => LiaFast.u0).
  intros C. unfold MT in Mg. cbn [nontrivial_free]. unfold getm, get, bind, ret. cbn [ibind fst snd]. rewrite Mg. cbn [ibind fst snd].
  rewrite Hcond. cbn [ibind].
  destruct C as [C | (C & Hsc & Hhd)].
  - replace (Z.lor (am_freed am) (am_avail am) =? 0) with false by (symmetry; apply Z.eqb_neq; exact C).
    unfold getm, get, setm, modify, bind, ret. cbn [ibind fst snd]. rewrite Mg. cbn [ibind fst snd]. reflexivity.
  - rewrite C. cbn [Z.eqb]. unfold massert. replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; exact Hsc).
    unfold get_head, getm, get, setm, modify, bind, ret. cbn [ibind fst snd]. unfold active_hd in Hhd. rewrite Hhd.
    cbn [osptr_eqb]. rewrite sptr_eqb_refl. cbn [ibind fst snd]. rewrite Mg. cbn [ibind fst snd]. reflexivity.
Qed.
End E.

Lemma In_keys_mupdate' : forall l p x q, In q (map fst l) -> In q (map fst (mupdate l p x)).
Proof.
  induction l as [|[k y] t IH]; intros p x q H; [destruct H|]. cbn [mupdate]. destruct (sptr_eqb p k); cbn [map fst In] in *.
  - exact H.
  - destruct H as [H|H]; [left; exact H | right; apply IH; exact H].
Qed.

Lemma mupdate_twice'' : forall l p x y, mupdate (mupdate l p x) p y = mupdate l p y.
Proof.
  induction l as [|[q z] t IH]; intros p x y; cbn [mupdate]; [rewrite sptr_eqb_refl; reflexivity|].
  destruct (sptr_eqb p q) eqn:E; cbn [mupdate]; rewrite E; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma set_metas_twice'' : forall v v' s, set_metas v (set_metas v' s) = set_metas v s.
Proof. reflexivity. Qed.

Section E3.
Variables (fuel : nat) (g : sptr) (i : Z) (s : astate) (am : ameta).
Hypothesis Mg : MT s g = Some (MUsed am).
Hypothesis Hcond : (Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am)) && okay_to_free s g am = false.
Hypothesis Hm0 : Z.lor (am_freed am) (am_avail am) = 0.
Hypothesis Hsc : am_sc am < 48.
Hypothesis Hpr : am_prev am = None.
Hypothesis Hnx : am_next am = None.

#[using="Mg Hcond Hm0 Hsc Hpr Hnx"] Lemma ntf_e3_itree : active_hd s (am_sc am) = None -> nontrivial_free (S fuel) g i s = IRet (None, ntf_e3 s g am i).
Proof. LiaFast.lf_pins (fun (Mg Hcond Hm0 Hsc Hpr Hnx : LiaFast.U) => LiaFast.u0).
  intros Hhd. unfold MT in Mg. cbn [nontrivial_free]. unfold getm, get, bind, ret. cbn [ibind fst snd]. rewrite Mg. cbn [ibind fst snd].
  rewrite Hcond. cbn [ibind]. rewrite Hm0. cbn [Z.eqb]. unfold massert. replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; exact Hsc).
  unfold get_head, get, bind, ret. cbn [ibind fst snd]. unfold active_hd in Hhd. rewrite Hhd. cbn [osptr_eqb ibind fst snd].
  unfold queue, get_links, set_links, get_head, set_head, setslot, getm, setm, modify, massert, bind, ret, get. msimp. rewrite Mg. msimp.
  rewrite Hpr, Hnx. msimp. rewrite ?Hhd. msimp.
  do 4 (msimp; mlk; rewrite ?Mg, ?Hhd, ?Hpr, ?Hnx).
  unfold set_active. msimp. mlk. msimp.
  f_equal. f_equal. unfold ntf_e3, set_meta, set_active. cbn [st_metas set_metas st_active]. rewrite ?mupdate_twice''. reflexivity.
Qed.

#[using="Mg Hcond Hm0 Hsc Hpr Hnx"] Lemma ntf_e4_itree : forall h amh hp amhp, active_hd s (am_sc am) = Some h -> h <> g ->
  MT s h = Some (MUsed amh) -> am_prev amh = Some hp -> hp <> g -> hp <> h -> MT s hp = Some (MUsed amhp) ->
  nontrivial_free (S fuel) g i s = IRet (None, ntf_e4 s g am i h amh hp amhp).
Proof. LiaFast.lf_pins (fun (Mg Hcond Hm0 Hsc Hpr Hnx : LiaFast.U) => LiaFast.u0).
  intros h amh hp amhp Hhd Hhg Mh Hhp Hhpg Hhph Mhp.
  pose proof (MT_keys s h _ Mh) as Kh. pose proof (MT_keys s hp _ Mhp) as Khp. pose proof (MT_keys s g _ Mg) as Kg.
  unfold MT in Mg, Mh, Mhp. cbn [nontrivial_free]. unfold getm, get, bind, ret. cbn [ibind fst snd]. rewrite Mg. cbn [ibind fst snd].
  rewrite Hcond. cbn [ibind]. rewrite Hm0. cbn [Z.eqb]. unfold massert. replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; exact Hsc).
  unfold get_head, get, bind, ret. cbn [ibind fst snd]. unfold active_hd in Hhd. rewrite Hhd. cbn [osptr_eqb].
  replace (sptr_eqb h g) with false by (symmetry; apply sptr_eqb_neq; exact Hhg). cbn [ibind fst snd].
  unfold queue, get_links, set_links, set_next, set_prev, get_head, setslot, getm, setm, modify, massert, bind, ret, get. msimp. rewrite Mg. msimp.
  rewrite Hpr, Hnx. msimp. rewrite ?Hhd. msimp.
  do 8 (unfold get_links, set_links, setslot, getm, setm, modify, bind, ret, get; msimp; mlk; rewrite ?Mg, ?Mh, ?Mhp, ?Hhp, ?Hhd; msimp).
  f_equal. f_equal. unfold ntf_e4, set_meta. rewrite !set_metas_twice''. cbn [st_metas set_metas]. f_equal.
  unfold keys in Kg, Kh, Khp.
  rewrite (mupdate_comm _ h g) by (first [congruence | repeat apply In_keys_mupdate'; assumption]).
  rewrite (mupdate_comm _ hp g) by (first [congruence | repeat apply In_keys_mupdate'; assumption]).
  rewrite mupdate_twice''. unfold ntf_freed. reflexivity.
Qed.

#[using="Mg Hcond Hm0 Hsc Hpr Hnx"] Lemma ntf_e4s_itree : forall h amh, active_hd s (am_sc am) = Some h -> h <> g ->
  MT s h = Some (MUsed amh) -> am_prev amh = Some h ->
  nontrivial_free (S fuel) g i s = IRet (None, ntf_e4s s g am i h amh).
Proof. LiaFast.lf_pins (fun (Mg Hcond Hm0 Hsc Hpr Hnx : LiaFast.U) => LiaFast.u0).
  intros h amh Hhd Hhg Mh Hhp.
  pose proof (MT_keys s h _ Mh) as Kh. pose proof (MT_keys s g _ Mg) as Kg.
  unfold MT in Mg, Mh. cbn [nontrivial_free]. unfold getm, get, bind, ret. cbn [ibind fst snd]. rewrite Mg. cbn [ibind fst snd].
  rewrite Hcond. cbn [ibind]. rewrite Hm0. cbn [Z.eqb]. unfold massert. replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; exact Hsc).
  unfold get_head, get, bind, ret. cbn [ibind fst snd]. unfold active_hd in Hhd. rewrite Hhd. cbn [osptr_eqb].
  replace (sptr_eqb h g) with false by (symmetry; apply sptr_eqb_neq; exact Hhg). cbn [ibind fst snd].
  unfold queue, get_links, set_links, set_next, set_prev, get_head, setslot, getm, setm, modify, massert, bind, ret, get. msimp. rewrite Mg. msimp.
  rewrite Hpr, Hnx. msimp. rewrite ?Hhd. msimp.
  do 8 (unfold get_links, set_links, setslot, getm, setm, modify, bind, ret, get; msimp; mlk; rewrite ?Mg, ?Mh, ?Hhp, ?Hhd; msimp).
  f_equal. f_equal. unfold ntf_e4s, set_meta. rewrite !set_metas_twice''. cbn [st_metas set_metas]. f_equal.
  unfold keys in Kg, Kh.
  rewrite mupdate_twice''.
  rewrite (mupdate_comm _ g h) by (first [congruence | repeat apply In_keys_mupdate'; assumption]).
  rewrite mupdate_twice''.
  rewrite (mupdate_comm _ h g) by (first [congruence | repeat apply In_keys_mupdate'; assumption]).
  unfold ntf_freed. reflexivity.
Qed.
End E3.
