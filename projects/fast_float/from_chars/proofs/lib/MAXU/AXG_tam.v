(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import MngImage MngSurgery MngCtx AXG_ntfm AXG_ntfg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

(* [comment removed for export] *)
Definition ta_take (m3 : sptr) (mask : Z) : M Z :=
  let first := lowbit mask in
  am3 <- getm m3 ;;
  setm m3 (am_set_avail (mask - first) am3) ;;
  ret first.

Definition ta_fin (m3 : sptr) : M Z :=
  mask <- activate_group m3 ;;
  massert (negb (mask =? 0)) 3 ;;
  am3 <- getm m3 ;;
  decay_bounces (am_sc am3) ;;
  ta_take m3 mask.

Definition ta_m2 (sc : Z) (m2 : sptr) : M Z :=
  am2 <- getm m2 ;;
  let mask := am_freed am2 in
  m3 <- (if Z.land mask (ones (am_aidx am2)) =? 0 then
           if negb (osptr_eqb (am_next am2) (Some m2)) then
             match am_next am2 with
             | Some nx => set_head (HActive sc) (Some nx) ;; ret nx
             | None => fail (FModel 7)
             end
           else
             let size := class_size (am_sc am2) in
             let cnt0 := am_aidx am2 + 2 in
             let cnt1 := span_loop 300%nat cnt0 (UNIT + size * cnt0) size in
             let cnt := if am_last am2 + 1 <? cnt1 then am_last am2 + 1 else cnt1 in
             setm m2 (am_set_aidx (cnt - 1) am2) ;; ret m2
         else ret m2) ;;
  ta_fin m3.

Definition ta_m1 (sc : Z) (m1 : sptr) : M Z :=
  am1 <- getm m1 ;;
  m2 <- (if am_freed am1 =? ones (am_last am1)
         then match am_next am1 with
              | Some nx => set_head (HActive sc) (Some nx) ;; ret nx
              | None => fail (FModel 6)
              end
         else ret m1) ;;
  ta_m2 sc m2.

Lemma try_avail_eq : forall sc, try_avail sc =
  (hd <- get_head (HActive sc) ;;
   match hd with
   | None => ret 0
   | Some m0 =>
     am0 <- getm m0 ;;
     if negb (am_avail am0 =? 0) then
       let first := lowbit (am_avail am0) in
       setm m0 (am_set_avail (am_avail am0 - first) am0) ;; ret first
     else
       om1 <- (if am_freed am0 =? 0
               then dequeue (HActive sc) m0 ;; get_head (HActive sc)
               else set_head (HActive sc) (am_next am0) ;; ret (am_next am0)) ;;
       match om1 with
       | None => ret 0
       | Some m1 => ta_m1 sc m1
       end
   end).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition s_head (s : astate) (sc : Z) (v : option sptr) : astate := set_active (lupd (st_active s) (Z.to_nat sc) v) s.

Section TaModel.
Variables (s : astate) (sc : Z).

#[using="Type"] Lemma ta_none : active_hd s sc = None -> try_avail sc s = IRet (0, s).
Proof. LiaFast.lf_pins LiaFast.u0. intros H. unfold active_hd in H. rewrite try_avail_eq. unfold get_head, bind, get, ret. cbn [ibind]. rewrite H. reflexivity. Qed.

#[using="Type"] Lemma ta_rot : forall g am nx, active_hd s sc = Some g -> MT s g = Some (MUsed am) -> am_avail am = 0 -> am_freed am <> 0 ->
  am_next am = Some nx -> try_avail sc s = ta_m1 sc nx (s_head s sc (Some nx)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros g am nx Hhd Mg Hav Hfr Hnx. unfold active_hd in Hhd. unfold MT in Mg. rewrite try_avail_eq.
  unfold get_head, getm, set_head, modify, bind, get, ret. cbn [ibind]. rewrite Hhd. cbn [ibind]. rewrite Mg. cbn [ibind].
  rewrite Hav. cbn [Z.eqb negb]. replace (am_freed am =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hfr).
  cbn [ibind]. rewrite Hnx. reflexivity.
Qed.

#[using="Type"] Lemma ta_dq1 : forall g am, active_hd s sc = Some g -> MT s g = Some (MUsed am) -> am_avail am = 0 -> am_freed am = 0 ->
  am_next am = Some g -> length (st_active s) = 48%nat -> 0 <= sc < 48 ->
  try_avail sc s = IRet (0, s_dq1 s g sc am).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros g am Hhd Mg Hav Hfr Hnx Hlen Hsc. unfold active_hd in Hhd. unfold MT in Mg. rewrite try_avail_eq.
  unfold get_head, getm, bind, get, ret. cbn [ibind]. rewrite Hhd. cbn [ibind]. rewrite Mg. cbn [ibind].
  rewrite Hav, Hfr. cbn [Z.eqb negb ibind].
  unfold dequeue. do 6 (mrun1; rewrite ?Mg, ?Hhd, ?Hnx, ?sptr_eqb_refl; cbn [osptr_eqb]).
  rewrite nth_lupd_same by (rewrite Hlen; lia). cbn. unfold s_dq1, set_meta, set_active. cbn. reflexivity.
Qed.
End TaModel.

(* [comment removed for export] *)
Definition s_tdn (s : astate) (g : sptr) (sc : Z) (am : ameta) (pr : sptr) (ampr : ameta) (nx : sptr) (amnx : ameta) : astate :=
  set_meta (set_active (lupd (st_active s) (Z.to_nat sc) (Some nx))
      (set_meta (set_meta s pr (MUsed (am_set_links (am_prev ampr) (Some nx) ampr))) nx (MUsed (am_set_links (Some pr) (am_next amnx) amnx))))
    g (MUsed (unl am)).
(* [comment removed for export] *)
Definition s_td2 (s : astate) (g : sptr) (sc : Z) (am : ameta) (h : sptr) (amh : ameta) : astate :=
  set_meta (set_active (lupd (st_active s) (Z.to_nat sc) (Some h)) (set_meta s h (MUsed (am_set_links (Some h) (Some h) amh))))
    g (MUsed (unl am)).

Section TaDq.
Variables (s : astate) (sc : Z) (g : sptr) (am : ameta).
Hypothesis Hhd : active_hd s sc = Some g.
Hypothesis Mg : MT s g = Some (MUsed am).
Hypothesis Hav : am_avail am = 0.
Hypothesis Hfr : am_freed am = 0.
Hypothesis Hlen : length (st_active s) = 48%nat.
Hypothesis Hsc : 0 <= sc < 48.

#[using="Hhd Mg Hav Hfr Hlen Hsc"] Lemma ta_dqn : forall pr ampr nx amnx, am_next am = Some nx -> am_prev am = Some pr -> nx <> g -> pr <> g -> pr <> nx ->
  MT s pr = Some (MUsed ampr) -> MT s nx = Some (MUsed amnx) ->
  try_avail sc s = ta_m1 sc nx (s_tdn s g sc am pr ampr nx amnx).
Proof. LiaFast.lf_pins (fun (Hhd Mg Hav Hfr Hlen Hsc : LiaFast.U) => LiaFast.u0).
  intros pr ampr nx amnx Hnx Hpr Hnxg Hprg Hprnx Mpr Mnx.
  unfold active_hd in Hhd. unfold MT in Mg, Mpr, Mnx. rewrite try_avail_eq.
  unfold get_head, getm, bind, get, ret. cbn [ibind]. rewrite Hhd. cbn [ibind]. rewrite Mg. cbn [ibind].
  rewrite Hav, Hfr. cbn [Z.eqb negb ibind].
  replace (sptr_eqb nx g) with false by (symmetry; apply sptr_eqb_neq; exact Hnxg).
  unfold dequeue. do 12 (mrun1; rewrite ?Mg, ?Mpr, ?Mnx, ?Hhd, ?Hnx, ?Hpr, ?sptr_eqb_refl; cbn [osptr_eqb];
     rewrite ?(proj2 (sptr_eqb_neq nx g) Hnxg); try (rewrite nth_lupd_same by (rewrite ?length_lupd, Hlen; lia))).
  unfold s_tdn, set_meta, set_active. cbn. reflexivity.
Qed.
#[using="Hhd Mg Hav Hfr Hlen Hsc"] Lemma ta_dq2 : forall h amh, am_next am = Some h -> am_prev am = Some h -> h <> g ->
  MT s h = Some (MUsed amh) -> try_avail sc s = ta_m1 sc h (s_td2 s g sc am h amh).
Proof. LiaFast.lf_pins (fun (Hhd Mg Hav Hfr Hlen Hsc : LiaFast.U) => LiaFast.u0).
  intros h amh Hnx Hpr Hhg Mh.
  unfold active_hd in Hhd. unfold MT in Mg, Mh. rewrite try_avail_eq.
  unfold get_head, getm, bind, get, ret. cbn [ibind]. rewrite Hhd. cbn [ibind]. rewrite Mg. cbn [ibind].
  rewrite Hav, Hfr. cbn [Z.eqb negb ibind].
  replace (sptr_eqb h g) with false by (symmetry; apply sptr_eqb_neq; exact Hhg).
  unfold dequeue. do 12 (mrun1; rewrite ?Mg, ?Mh, ?Hhd, ?Hnx, ?Hpr, ?sptr_eqb_refl; cbn [osptr_eqb];
     rewrite ?(proj2 (sptr_eqb_neq h g) Hhg); try (rewrite nth_lupd_same by (rewrite ?length_lupd, Hlen; lia))).
  unfold s_td2, set_meta, set_active. cbn. rewrite !mupdate_twice''. reflexivity.
Qed.
End TaDq.

(* [comment removed for export] *)

Lemma ta_m1n : forall s sc m1 am1, MT s m1 = Some (MUsed am1) -> am_freed am1 <> ones (am_last am1) ->
  ta_m1 sc m1 s = ta_m2 sc m1 s.
Proof.
  intros s sc m1 am1 M1 Hf. unfold MT in M1. unfold ta_m1, getm, bind, get, ret. cbn [ibind]. rewrite M1. cbn [ibind].
  replace (am_freed am1 =? ones (am_last am1)) with false by (symmetry; apply Z.eqb_neq; exact Hf). reflexivity.
Qed.

Lemma ta_m1f : forall s sc m1 am1 nx, MT s m1 = Some (MUsed am1) -> am_freed am1 = ones (am_last am1) -> am_next am1 = Some nx ->
  ta_m1 sc m1 s = ta_m2 sc nx (s_head s sc (Some nx)).
Proof.
  intros s sc m1 am1 nx M1 Hf Hnx. unfold MT in M1. unfold ta_m1, getm, set_head, modify, bind, get, ret. cbn [ibind]. rewrite M1. cbn [ibind].
  rewrite Hf, Z.eqb_refl. rewrite Hnx. reflexivity.
Qed.

Lemma ta_m2a : forall s sc m2 am2, MT s m2 = Some (MUsed am2) -> Z.land (am_freed am2) (ones (am_aidx am2)) <> 0 ->
  ta_m2 sc m2 s = ta_fin m2 s.
Proof.
  intros s sc m2 am2 M2 Hm. unfold MT in M2. unfold ta_m2, getm, bind, get, ret. cbn [ibind]. rewrite M2. cbn [ibind].
  replace (Z.land (am_freed am2) (ones (am_aidx am2)) =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hm). reflexivity.
Qed.

Lemma ta_m2b : forall s sc m2 am2 nx, MT s m2 = Some (MUsed am2) -> Z.land (am_freed am2) (ones (am_aidx am2)) = 0 ->
  am_next am2 = Some nx -> nx <> m2 -> ta_m2 sc m2 s = ta_fin nx (s_head s sc (Some nx)).
Proof.
  intros s sc m2 am2 nx M2 Hm Hnx Hne. unfold MT in M2. unfold ta_m2, getm, set_head, modify, bind, get, ret. cbn [ibind]. rewrite M2. cbn [ibind].
  rewrite Hm, Z.eqb_refl. rewrite Hnx. cbn [osptr_eqb]. rewrite (proj2 (sptr_eqb_neq nx m2) Hne). reflexivity.
Qed.

(* [comment removed for export] *)
Definition span_cnt (am2 : ameta) : Z :=
  let size := class_size (am_sc am2) in
  let cnt0 := am_aidx am2 + 2 in
  let cnt1 := span_loop 300%nat cnt0 (UNIT + size * cnt0) size in
  if am_last am2 + 1 <? cnt1 then am_last am2 + 1 else cnt1.

Lemma ta_m2c : forall s sc m2 am2, MT s m2 = Some (MUsed am2) -> Z.land (am_freed am2) (ones (am_aidx am2)) = 0 ->
  am_next am2 = Some m2 -> ta_m2 sc m2 s = ta_fin m2 (set_meta s m2 (MUsed (am_set_aidx (span_cnt am2 - 1) am2))).
Proof.
  intros s sc m2 am2 M2 Hm Hnx. unfold MT in M2. unfold ta_m2, getm, setm, modify, bind, get, ret. cbn [ibind]. rewrite M2. cbn [ibind].
  rewrite Hm, Z.eqb_refl. rewrite Hnx. cbn [osptr_eqb negb]. rewrite sptr_eqb_refl. cbn [negb ibind]. unfold span_cnt. reflexivity.
Qed.

(* [comment removed for export] *)

Definition s_decay (s : astate) (sc : Z) : astate :=
  match bounce_idx sc with
  | Some k => let b := znth k (st_bounces s) in if b =? 0 then s else set_bounces (zset k (b - 1) (st_bounces s)) s
  | None => s
  end.

Lemma MT_decay : forall s sc q, MT (s_decay s sc) q = MT s q.
Proof. intros s sc q. unfold s_decay. destruct (bounce_idx sc); [destruct (_ =? 0)|]; reflexivity. Qed.

Definition ta_mask (am3 : ameta) : Z := Z.land (am_freed am3) (ones (am_aidx am3)).

Definition s_fin (s : astate) (m3 : sptr) (am3 : ameta) : astate :=
  set_meta (s_decay (set_meta s m3 (MUsed (act_meta am3))) (am_sc am3)) m3
    (MUsed (am_set_avail (ta_mask am3 - lowbit (ta_mask am3)) (act_meta am3))).

Lemma ta_fin_eq : forall s m3 am3, MT s m3 = Some (MUsed am3) -> am_avail am3 = 0 -> ta_mask am3 <> 0 ->
  ta_fin m3 s = IRet (lowbit (ta_mask am3), s_fin s m3 am3).
Proof.
  intros s m3 am3 M3 Hav Hm. unfold MT in M3. unfold ta_fin, activate_group, ta_take, getm, setm, modify, massert, bind, get, ret. cbn [ibind].
  rewrite M3. cbn [ibind]. rewrite Hav, Z.eqb_refl. cbn [ibind].
  fold (ta_mask am3). replace (negb (ta_mask am3 =? 0)) with true by (symmetry; apply negb_true_iff; apply Z.eqb_neq; exact Hm). cbn [ibind].
  cbn [st_metas set_metas]. rewrite mlookup_mupdate_same. cbn [ibind am_sc am_set_avail am_set_freed].
  unfold decay_bounces, s_fin, s_decay, act_meta. destruct (bounce_idx (am_sc am3)) as [k|] eqn:Eb.
  - unfold modify. cbn [ibind st_bounces set_metas]. destruct (znth k (st_bounces s) =? 0) eqn:Ez.
    + cbn [st_metas set_metas]. rewrite mlookup_mupdate_same. cbn [ibind]. unfold set_meta, ta_mask. cbn [st_bounces set_metas]. rewrite Ez. reflexivity.
    + cbn [st_metas set_metas set_bounces]. rewrite mlookup_mupdate_same. cbn [ibind]. unfold set_meta, ta_mask. cbn [st_bounces set_metas]. rewrite Ez. reflexivity.
  - unfold ret. cbn [ibind st_metas set_metas]. rewrite mlookup_mupdate_same. cbn [ibind]. unfold set_meta, ta_mask. reflexivity.
Qed.
