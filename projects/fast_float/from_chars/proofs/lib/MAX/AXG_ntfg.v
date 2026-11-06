(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import MngImage MngSurgery MngCtx AXG_ntfm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Definition deq_part (g : sptr) (sc : Z) (am : ameta) : M unit :=
  match am_next am with
  | Some _ =>
      massert (sc <? 48) 5 ;;
      hd <- get_head (HActive sc) ;;
      let activate_new := osptr_eqb hd (Some g) in
      dequeue (HActive sc) g ;;
      hd' <- get_head (HActive sc) ;;
      match activate_new, hd' with
      | true, Some h => _ <- activate_group h ;; ret tt
      | _, _ => ret tt
      end
  | None => ret tt
  end.

Definition g_rest (fuel' : nat) (g : sptr) (s : astate) (sc : Z) : M (option (nat * Z)) :=
  am <- getm g ;;
  (if sc <? 48 then set_usage_of sc (usage_of s sc - (am_last am + 1)) else ret tt) ;;
  mi <- (if negb (am_maplen am =? 0) then
           step_seq ;; record_seq sc ;;
           ret (Some (prid (am_mem am), am_maplen am * 4096))
         else
           pf <- find_frame (am_mem am) ;;
           amp <- getm (fst pf) ;;
           mcheck (slot_is_group (nth_slot amp (snd pf))) 10 ;;
           forget_frame (fst pf) (snd pf) ;;
           nontrivial_free fuel' (fst pf) (snd pf)) ;;
  free_meta g ;;
  ret mi.

Lemma ntf_g_unfold : forall fuel g i s am, MT s g = Some (MUsed am) ->
  (Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am)) && okay_to_free s g am = true ->
  nontrivial_free (S fuel) g i s = bind (deq_part g (am_sc am) am) (fun _ => g_rest fuel g s (am_sc am)) s.
Proof.
  intros fuel g i s am Mg Hcond. unfold MT in Mg. cbn [nontrivial_free]. unfold getm, get, bind, ret. cbn [ibind fst snd]. rewrite Mg.
  cbn [ibind fst snd]. rewrite Hcond. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition unl (am : ameta) : ameta := am_set_links None None am.

Definition s_dq1 (s : astate) (g : sptr) (sc : Z) (am : ameta) : astate :=
  set_meta (set_active (lupd (st_active s) (Z.to_nat sc) None) s) g (MUsed (unl am)).
Definition s_dq3 (s : astate) (g : sptr) (am : ameta) (pr : sptr) (ampr : ameta) (nx : sptr) (amnx : ameta) : astate :=
  set_meta (set_meta (set_meta s pr (MUsed (am_set_links (am_prev ampr) (Some nx) ampr))) nx (MUsed (am_set_links (Some pr) (am_next amnx) amnx)))
           g (MUsed (unl am)).
Definition s_dq3s (s : astate) (g : sptr) (am : ameta) (h : sptr) (amh : ameta) : astate :=
  set_meta (set_meta s h (MUsed (am_set_links (Some h) (Some h) amh))) g (MUsed (unl am)).

Definition act_meta (amx : ameta) : ameta :=
  am_set_avail (Z.land (am_freed amx) (ones (am_aidx amx))) (am_set_freed (Z.ldiff (am_freed amx) (ones (am_aidx amx))) amx).

Definition s_dq2 (s : astate) (g : sptr) (sc : Z) (am : ameta) (pr : sptr) (ampr : ameta) (nx : sptr) (amnx : ameta) : astate :=
  set_meta (set_meta (set_active (lupd (st_active s) (Z.to_nat sc) (Some nx))
      (set_meta (set_meta s pr (MUsed (am_set_links (am_prev ampr) (Some nx) ampr))) nx (MUsed (am_set_links (Some pr) (am_next amnx) amnx))))
    g (MUsed (unl am))) nx (MUsed (act_meta (am_set_links (Some pr) (am_next amnx) amnx))).
Definition s_dq2s (s : astate) (g : sptr) (sc : Z) (am : ameta) (h : sptr) (amh : ameta) : astate :=
  set_meta (set_meta (set_active (lupd (st_active s) (Z.to_nat sc) (Some h)) (set_meta s h (MUsed (am_set_links (Some h) (Some h) amh))))
    g (MUsed (unl am))) h (MUsed (act_meta (am_set_links (Some h) (Some h) amh))).

Ltac mrun1 := unfold get_links, set_links, set_next, set_prev, get_head, set_head, setslot, getm, setm, modify, massert, bind, ret, get;
               msimp; cbn [st_free_meta_head st_usage st_seq st_unmap_seq set_free_meta_head set_metas]; mlk; try (unfold set_active; msimp).

Section Deq.
Variables (g : sptr) (s : astate) (am : ameta).
Hypothesis Mg : MT s g = Some (MUsed am).

#[using="Type"] Lemma deq0 : am_next am = None -> deq_part g (am_sc am) am s = IRet (tt, s).
Proof. LiaFast.lf_pins LiaFast.u0. intros Hn. unfold deq_part. rewrite Hn. reflexivity. Qed.

Hypothesis Hlen : length (st_active s) = 48%nat.

#[using="Mg Hlen"] Lemma deq1 : am_next am = Some g -> 0 <= am_sc am < 48 -> active_hd s (am_sc am) = Some g ->
  deq_part g (am_sc am) am s = IRet (tt, s_dq1 s g (am_sc am) am).
Proof. LiaFast.lf_pins (fun (Mg Hlen : LiaFast.U) => LiaFast.u0).
  intros Hn Hsc Hhd. unfold MT in Mg. unfold active_hd in Hhd. unfold deq_part. rewrite Hn.
  unfold massert. replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold dequeue. do 8 (mrun1; rewrite ?Mg, ?Hhd, ?Hn, ?sptr_eqb_refl; cbn [osptr_eqb]).
  rewrite nth_lupd_same by (rewrite Hlen; lia). cbn. unfold s_dq1, set_meta, set_active. cbn. reflexivity.
Qed.

#[using="Mg Hlen"] Lemma deq3 : forall pr ampr nx amnx h, am_next am = Some nx -> am_prev am = Some pr -> nx <> g -> pr <> g -> pr <> nx ->
  MT s pr = Some (MUsed ampr) -> MT s nx = Some (MUsed amnx) -> 0 <= am_sc am < 48 -> active_hd s (am_sc am) = Some h -> h <> g ->
  deq_part g (am_sc am) am s = IRet (tt, s_dq3 s g am pr ampr nx amnx).
Proof. LiaFast.lf_pins (fun (Mg Hlen : LiaFast.U) => LiaFast.u0).
  intros pr ampr nx amnx h Hn Hp Hnxg Hprg Hprnx Mpr Mnx Hsc Hhd Hhg.
  pose proof (MT_keys s g _ Mg) as Kg. pose proof (MT_keys s pr _ Mpr) as Kpr. pose proof (MT_keys s nx _ Mnx) as Knx.
  unfold MT in Mg, Mpr, Mnx. unfold active_hd in Hhd. unfold deq_part. rewrite Hn.
  unfold massert. replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (sptr_eqb nx g) with false by (symmetry; apply sptr_eqb_neq; exact Hnxg).
  replace (sptr_eqb h g) with false by (symmetry; apply sptr_eqb_neq; exact Hhg).
  unfold dequeue. do 12 (mrun1; rewrite ?Mg, ?Mpr, ?Mnx, ?Hhd, ?Hn, ?Hp, ?sptr_eqb_refl; cbn [osptr_eqb];
     rewrite ?(proj2 (sptr_eqb_neq nx g) Hnxg), ?(proj2 (sptr_eqb_neq h g) Hhg)).
  unfold s_dq3, set_meta. rewrite !set_metas_twice''. reflexivity.
Qed.

#[using="Mg Hlen"] Lemma deq3s : forall h amh hd, am_next am = Some h -> am_prev am = Some h -> h <> g ->
  MT s h = Some (MUsed amh) -> 0 <= am_sc am < 48 -> active_hd s (am_sc am) = Some hd -> hd <> g ->
  deq_part g (am_sc am) am s = IRet (tt, s_dq3s s g am h amh).
Proof. LiaFast.lf_pins (fun (Mg Hlen : LiaFast.U) => LiaFast.u0).
  intros h amh hd Hn Hp Hhg Mh Hsc Hhd Hdg.
  pose proof (MT_keys s g _ Mg) as Kg. pose proof (MT_keys s h _ Mh) as Kh.
  unfold MT in Mg, Mh. unfold active_hd in Hhd. unfold deq_part. rewrite Hn.
  unfold massert. replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold dequeue. do 12 (mrun1; rewrite ?Mg, ?Mh, ?Hhd, ?Hn, ?Hp, ?sptr_eqb_refl; cbn [osptr_eqb];
     rewrite ?(proj2 (sptr_eqb_neq h g) Hhg), ?(proj2 (sptr_eqb_neq hd g) Hdg)).
  unfold s_dq3s, set_meta. rewrite !set_metas_twice''. rewrite mupdate_twice''. reflexivity.
Qed.

#[using="Mg Hlen"] Lemma deq2 : forall pr ampr nx amnx, am_next am = Some nx -> am_prev am = Some pr -> nx <> g -> pr <> g -> pr <> nx ->
  MT s pr = Some (MUsed ampr) -> MT s nx = Some (MUsed amnx) -> 0 <= am_sc am < 48 -> active_hd s (am_sc am) = Some g ->
  am_avail amnx = 0 ->
  deq_part g (am_sc am) am s = IRet (tt, s_dq2 s g (am_sc am) am pr ampr nx amnx).
Proof. LiaFast.lf_pins (fun (Mg Hlen : LiaFast.U) => LiaFast.u0).
  intros pr ampr nx amnx Hn Hp Hnxg Hprg Hprnx Mpr Mnx Hsc Hhd Hav.
  pose proof (MT_keys s g _ Mg) as Kg. pose proof (MT_keys s pr _ Mpr) as Kpr. pose proof (MT_keys s nx _ Mnx) as Knx.
  unfold MT in Mg, Mpr, Mnx. unfold active_hd in Hhd. unfold deq_part. rewrite Hn.
  unfold massert. replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold dequeue, activate_group. do 14 (mrun1; rewrite ?Mg, ?Mpr, ?Mnx, ?Hhd, ?Hn, ?Hp, ?Hav, ?sptr_eqb_refl; cbn [osptr_eqb am_avail am_set_links Z.eqb];
     rewrite ?(proj2 (sptr_eqb_neq nx g) Hnxg); try (rewrite nth_lupd_same by (rewrite ?length_lupd, Hlen; lia))).
  unfold s_dq2, set_meta, set_active, act_meta. cbn. reflexivity.
Qed.

#[using="Mg Hlen"] Lemma deq2s : forall h amh, am_next am = Some h -> am_prev am = Some h -> h <> g ->
  MT s h = Some (MUsed amh) -> 0 <= am_sc am < 48 -> active_hd s (am_sc am) = Some g -> am_avail amh = 0 ->
  deq_part g (am_sc am) am s = IRet (tt, s_dq2s s g (am_sc am) am h amh).
Proof. LiaFast.lf_pins (fun (Mg Hlen : LiaFast.U) => LiaFast.u0).
  intros h amh Hn Hp Hhg Mh Hsc Hhd Hav.
  pose proof (MT_keys s g _ Mg) as Kg. pose proof (MT_keys s h _ Mh) as Kh.
  unfold MT in Mg, Mh. unfold active_hd in Hhd. unfold deq_part. rewrite Hn.
  unfold massert. replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold dequeue, activate_group. do 14 (mrun1; rewrite ?Mg, ?Mh, ?Hhd, ?Hn, ?Hp, ?Hav, ?sptr_eqb_refl; cbn [osptr_eqb am_avail am_set_links Z.eqb];
     rewrite ?(proj2 (sptr_eqb_neq h g) Hhg); try (rewrite nth_lupd_same by (rewrite ?length_lupd, Hlen; lia))).
  unfold s_dq2s, set_meta, set_active, act_meta. cbn. rewrite !mupdate_twice''. reflexivity.
Qed.
End Deq.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition s_usg (s s1 : astate) (sc last : Z) : astate :=
  if sc <? 48 then set_usage (zset sc (usage_of s sc - (last + 1)) (st_usage s1)) s1 else s1.
Definition s_seq (s2 : astate) : astate :=
  if st_seq s2 =? 255 then set_seq 1 (set_unmap_seq (repeat 0 32) s2) else set_seq (st_seq s2 + 1) s2.
Definition s_rec (sc : Z) (s3 : astate) : astate :=
  match bounce_idx sc with Some k => set_unmap_seq (zset k (st_seq s3) (st_unmap_seq s3)) s3 | None => s3 end.

Definition s_fm0 (s4 : astate) (g : sptr) : astate := set_free_meta_head (Some g) (set_meta s4 g (MFree (Some g) (Some g))).
Definition s_fm1 (s4 : astate) (g h : sptr) (hp : sptr) (hpp hn : option sptr) : astate :=
  set_meta (set_meta (set_meta s4 g (MFree (Some hp) (Some h))) hp (MFree hpp (Some g))) h (MFree (Some g) hn).
Definition s_fm1s (s4 : astate) (g h : sptr) : astate :=
  set_meta (set_meta s4 g (MFree (Some h) (Some h))) h (MFree (Some g) (Some g)).

Section FM.
Variables (g : sptr) (s4 : astate) (am : ameta).
Hypothesis Mg : MT s4 g = Some (MUsed am).

#[using="am Mg"] Lemma fm0_itree : st_free_meta_head s4 = None -> free_meta g s4 = IRet (tt, s_fm0 s4 g).
Proof. LiaFast.lf_pins (fun (am Mg : LiaFast.U) => LiaFast.u0).
  intros Hh. pose proof (MT_keys s4 g _ Mg) as Kg. unfold MT in Mg. unfold free_meta, queue.
  do 8 (mrun1; rewrite ?Mg, ?Hh; cbn [osptr_eqb]; try (unfold set_free_meta_head; msimp)).
  unfold s_fm0, set_meta, set_free_meta_head. cbn. rewrite ?mupdate_twice''. reflexivity.
Qed.

#[using="am Mg"] Lemma fm1_itree : forall h hp hpp hn, st_free_meta_head s4 = Some h -> h <> g -> hp <> g -> hp <> h ->
  MT s4 h = Some (MFree (Some hp) hn) -> MT s4 hp = Some (MFree hpp (Some h)) ->
  free_meta g s4 = IRet (tt, s_fm1 s4 g h hp hpp hn).
Proof. LiaFast.lf_pins (fun (am Mg : LiaFast.U) => LiaFast.u0).
  intros h hp hpp hn Hh Hhg Hpg Hph Mh Mhp. pose proof (MT_keys s4 g _ Mg) as Kg. pose proof (MT_keys s4 h _ Mh) as Kh. pose proof (MT_keys s4 hp _ Mhp) as Khp.
  unfold MT in Mg, Mh, Mhp. unfold free_meta, queue.
  do 12 (mrun1; rewrite ?Mg, ?Mh, ?Mhp, ?Hh; cbn [osptr_eqb links_of with_links]).
  unfold s_fm1, set_meta. rewrite !set_metas_twice''. rewrite mupdate_twice''. reflexivity.
Qed.

#[using="am Mg"] Lemma fm1s_itree : forall h, st_free_meta_head s4 = Some h -> h <> g -> MT s4 h = Some (MFree (Some h) (Some h)) ->
  free_meta g s4 = IRet (tt, s_fm1s s4 g h).
Proof. LiaFast.lf_pins (fun (am Mg : LiaFast.U) => LiaFast.u0).
  intros h Hh Hhg Mh. pose proof (MT_keys s4 g _ Mg) as Kg. pose proof (MT_keys s4 h _ Mh) as Kh.
  unfold MT in Mg, Mh. unfold free_meta, queue.
  do 12 (mrun1; rewrite ?Mg, ?Mh, ?Hh; cbn [osptr_eqb links_of with_links]).
  unfold s_fm1s, set_meta. rewrite !set_metas_twice''. rewrite !mupdate_twice''. reflexivity.
Qed.
End FM.

Lemma g_rest_map : forall f g s s1 sc am1 s5,
  MT s1 g = Some (MUsed am1) -> am_maplen am1 <> 0 ->
  free_meta g (s_rec sc (s_seq (s_usg s s1 sc (am_last am1)))) = IRet (tt, s5) ->
  g_rest f g s sc s1 = IRet (Some (prid (am_mem am1), am_maplen am1 * 4096), s5).
Proof.
  intros f g s s1 sc am1 s5 M1 Hml Hfm. unfold MT in M1. unfold g_rest, getm, get, bind, ret. cbn [ibind fst snd]. rewrite M1. cbn [ibind fst snd].
  replace (negb (am_maplen am1 =? 0)) with true by (symmetry; apply negb_true_iff; apply Z.eqb_neq; exact Hml).
  unfold s_usg in Hfm. destruct (sc <? 48) eqn:E48.
  - unfold set_usage_of, modify, step_seq, record_seq, bind, ret. cbn [ibind fst snd].
    unfold s_rec, s_seq in Hfm. destruct (bounce_idx sc) as [k|] eqn:Eb;
      unfold modify, bind, ret; cbn [ibind fst snd]; rewrite Hfm; reflexivity.
  - unfold step_seq, record_seq, modify, bind, ret. cbn [ibind fst snd].
    unfold s_rec, s_seq in Hfm. destruct (bounce_idx sc) as [k|] eqn:Eb;
      unfold modify, bind, ret; cbn [ibind fst snd]; rewrite Hfm; reflexivity.
Qed.

(* [comment removed for export] *)
Definition s_ff (s2 : astate) (pg : sptr) (amp : ameta) (idx : Z) : astate :=
  set_meta s2 pg (MUsed (upd_slot amp idx (mkSlot (ss_hdr (nth_slot amp idx)) None))).

Lemma g_rest_nest : forall f g s s1 sc am1 pg idx amp mi sr s5,
  MT s1 g = Some (MUsed am1) -> am_maplen am1 = 0 -> sc < 48 ->
  find_frame_in (st_metas (s_usg s s1 sc (am_last am1))) (am_mem am1) = Some (pg, idx) ->
  MT (s_usg s s1 sc (am_last am1)) pg = Some (MUsed amp) -> slot_is_group (nth_slot amp idx) = true ->
  nontrivial_free f pg idx (s_ff (s_usg s s1 sc (am_last am1)) pg amp idx) = IRet (mi, sr) ->
  free_meta g sr = IRet (tt, s5) ->
  g_rest f g s sc s1 = IRet (mi, s5).
Proof.
  intros f g s s1 sc am1 pg idx amp mi sr s5 M1 Hml Hsc Hff Mp Hgrp Hrec Hfm.
  unfold MT in M1, Mp. unfold g_rest, getm, get, bind, ret. cbn [ibind fst snd]. rewrite M1. cbn [ibind fst snd].
  rewrite Hml. cbn [Z.eqb negb]. unfold s_usg in *. replace (sc <? 48) with true in * by (symmetry; apply Z.ltb_lt; exact Hsc).
  unfold set_usage_of, modify, find_frame, get, bind, ret. cbn [ibind fst snd]. rewrite Hff. cbn [ibind fst snd].
  unfold getm, get, bind, ret. cbn [ibind fst snd]. rewrite Mp. cbn [ibind fst snd]. unfold mcheck. rewrite Hgrp.
  unfold forget_frame, getm, setm, modify, get, bind, ret. cbn [ibind fst snd]. rewrite Mp. cbn [ibind fst snd].
  unfold s_ff, set_meta in Hrec. rewrite Hrec. cbn [ibind fst snd]. rewrite Hfm. reflexivity.
Qed.
