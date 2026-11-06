(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngShape.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AXG_as7.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma itok_ibind_inv : forall {A B} (t : itree astate A) (k : A -> itree astate B) (Q : B -> Prop),
  itok (ibind t k) Q -> itok t (fun a => itok (k a) Q).
Proof.
  intros A B t k Q. induction t as [a | q sn c IH | f]; cbn; intros H; [exact H | | exact H].
  destruct H as [Hr Hk]. split; [exact Hr|]. intros z Hz. apply IH. apply Hk, Hz.
Qed.

Lemma itok_ask_inv : forall {A} q sn (k : Z -> itree astate A) (Q : A -> Prop) z, itok (IAsk q sn k) Q -> answer_ok q z -> itok (k z) Q.
Proof. intros A q sn k Q z H Hz. destruct H as [_ H]. exact (H z Hz). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition AGK (fuel' : nat) (sc req : Z) (om : option sptr) : M (option sptr) :=
    match om with
    | None => ret None
    | Some m =>
      s <- get ;;
      let size := class_size sc in
      let usage := usage_of s sc in
      let cnt0 := initial_cnt sc usage in
      if PGSZ / 2 <? size * cnt0 + UNIT then
        (* [comment removed for export] *)
        let plan := mmap_plan s sc req cnt0 usage in
        account_bounce sc ;;
        step_seq ;;
        ok <- ask (KMmapRW (snd plan)) ;;
        if negb ok then free_meta m ;; ret None
        else
          (* [comment removed for export] *)
          r <- new_region RkMap (page_round (snd plan)) ;;
          s <- get ;;
          put (set_mmap_counter (Z.land (st_mmap_counter s + 1) (2^32 - 1)) s) ;;
          let cnt := fst plan in
          let a0 := (4096 - UNIT) / size - 1 in
          let a1 := if cnt - 1 <? a0 then cnt - 1 else a0 in
          let aidx := if a1 <? 0 then 0 else a1 in
          install_group m sc cnt aidx (snd plan / 4096) (SP r 0) slot_zero ;;
          ret (Some m)
      else
        (* [comment removed for export] *)
        let total := UNIT + cnt0 * size - IB in
        let j := size_to_class total in
        idx <- alloc_slot fuel' j total ;;
        if idx <? 0 then free_meta m ;; ret None
        else
          hj <- get_head (HActive j) ;;
          match hj with
          | None => fail (FModel 8)
          | Some g =>
              amg <- getm g ;;
              mcheck (stride_of amg =? class_size j) 11 ;;
              s <- get ;;
              p <- enframe g idx (class_size j - IB) (st_mmap_counter s) FGroup ;;
              install_group m sc cnt0 (cnt0 - 1) 0 p slot_junk ;;
              ret (Some m)
          end
    end.

Lemma alloc_group_S : forall f sc req s, alloc_group (S f) sc req s = ibind (alloc_meta s) (fun r => match r with (a, s') => AGK f sc req a s' end).
Proof. intros f sc req s. reflexivity. Qed.

(* [comment removed for export] *)
Lemma as_group_eq : forall f sc req s, as_group f sc req s =
  ibind (alloc_group f sc req s) (fun r => match r with (og, s') => (match og with None => ret (-1) | Some _ => ret 0 end) s' end).
Proof. intros f sc req s. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ab_st (s : astate) (sc : Z) : astate :=
  match bounce_idx sc with
  | Some k =>
      let useq := znth k (st_unmap_seq s) in
      let b := znth k (st_bounces s) in
      if negb (useq =? 0) && (st_seq s - useq <? 10)
      then set_bounces (zset k (if b + 1 <? 100 then b + 1 else 150) (st_bounces s)) s
      else s
  | None => s
  end.

Definition sq_st (s : astate) : astate :=
  if st_seq s =? 255 then set_seq 1 (set_unmap_seq (repeat 0 32) s) else set_seq (st_seq s + 1) s.

Lemma account_bounce_eq : forall sc s, account_bounce sc s = IRet (tt, ab_st s sc).
Proof. intros sc s. unfold account_bounce, ab_st. destruct (bounce_idx sc); reflexivity. Qed.

Lemma step_seq_eq : forall s, step_seq s = IRet (tt, sq_st s).
Proof. intros s. reflexivity. Qed.

Definition ag_cnt0 (s : astate) (sc : Z) : Z := initial_cnt sc (usage_of s sc).
Definition ag_plan (s : astate) (sc req : Z) : Z * Z := mmap_plan s sc req (ag_cnt0 s sc) (usage_of s sc).
Definition ag_s3 (s : astate) (sc : Z) : astate := sq_st (ab_st s sc).
Definition ag_aidx (sc cnt : Z) : Z :=
  let a0 := (4096 - UNIT) / class_size sc - 1 in
  let a1 := if cnt - 1 <? a0 then cnt - 1 else a0 in
  if a1 <? 0 then 0 else a1.
(* [comment removed for export] *)
Definition ag_s5 (s3 : astate) (len : Z) : astate :=
  set_mmap_counter (Z.land (st_mmap_counter s3 + 1) (2^32 - 1)) (set_regions (st_regions s3 ++ [mkRegion RkMap (page_round len) [] true]) s3).

(* [comment removed for export] *)
Definition ins_st (m : sptr) (sc cnt aidx maplen : Z) (mem : sptr) (sl : slotst) (s : astate) : astate :=
  let s1 := set_usage (zset sc (usage_of s sc + cnt) (st_usage s)) s in
  let s2 := set_metas (mupdate (st_metas s1) m (MUsed (new_am mem sc cnt aidx maplen sl))) s1 in
  let s3 := set_metas (mupdate (st_metas s2) m (MUsed (am_set_links (Some m) (Some m) (new_am mem sc cnt aidx maplen sl)))) s2 in
  set_active (lupd (st_active s3) (Z.to_nat sc) (Some m)) s3.

Lemma mlookup_mupdate_same' : forall l p x, mlookup (mupdate l p x) p = Some x.
Proof. intros l p x. apply mlookup_mupdate_same. Qed.

Lemma install_group_empty : forall m sc cnt aidx maplen mem sl s, active_hd s sc = None ->
  install_group m sc cnt aidx maplen mem sl s = IRet (tt, ins_st m sc cnt aidx maplen mem sl s).
Proof.
  intros m sc cnt aidx maplen mem sl s Hhd. unfold install_group, ins_st.
  unfold queue, get_links, set_links, set_head, get_head, setm, set_usage_of, modify, get, ret, bind, massert, setslot.
  cbn [ibind st_metas set_metas set_usage fst snd].
  rewrite mlookup_mupdate_same'. cbn [ibind links_of new_am am_prev am_next osptr_eqb andb fst snd].
  unfold ret. cbn [ibind st_metas set_metas st_active set_usage fst snd].
  change (nth (Z.to_nat sc) (st_active s) None) with (active_hd s sc). rewrite Hhd.
  cbn [ibind st_metas set_metas]. rewrite mlookup_mupdate_same'. unfold modify. cbn [ibind with_links]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ab_regions : forall s sc, st_regions (ab_st s sc) = st_regions s.
Proof. intros s sc. unfold ab_st. destruct (bounce_idx sc); [|reflexivity]. cbn. destruct (_ && _); reflexivity. Qed.

Lemma sq_regions : forall s, st_regions (sq_st s) = st_regions s.
Proof. intros s. unfold sq_st. destruct (st_seq s =? 255); reflexivity. Qed.

Lemma ab_active : forall s sc, st_active (ab_st s sc) = st_active s.
Proof. intros s sc. unfold ab_st. destruct (bounce_idx sc); [|reflexivity]. cbn. destruct (_ && _); reflexivity. Qed.

Lemma sq_active : forall s, st_active (sq_st s) = st_active s.
Proof. intros s. unfold sq_st. destruct (st_seq s =? 255); reflexivity. Qed.

Definition ag_s6 (m : sptr) (s2 : astate) (sc req : Z) : astate :=
  let plan := ag_plan s2 sc req in
  ins_st m sc (fst plan) (ag_aidx sc (fst plan)) (snd plan / 4096) (SP (length (st_regions (ag_s3 s2 sc))) 0) slot_zero (ag_s5 (ag_s3 s2 sc) (snd plan)).

Lemma ag_mmap_tree : forall f sc req m s2, (PGSZ / 2 <? class_size sc * initial_cnt sc (usage_of s2 sc) + UNIT) = true -> active_hd s2 sc = None ->
  exists Kt, AGK f sc req (Some m) s2 = IAsk (KMmapRW (snd (ag_plan s2 sc req))) (ag_s3 s2 sc) Kt /\ Kt 1 = IRet (Some m, ag_s6 m s2 sc req).
Proof.
  intros f sc req m s2 Hc Hhd. eexists. split.
  - unfold AGK. unfold bind at 1, get. cbn [ibind]. rewrite Hc. unfold bind at 1. rewrite account_bounce_eq. cbn [ibind].
    unfold bind at 1. rewrite step_seq_eq. cbn [ibind]. unfold bind at 1, ask. cbn [ibind]. reflexivity.
  - cbn beta iota. cbn [negb Z.eqb]. unfold new_region, bind, get, put, ret. cbn [ibind st_regions set_regions].
    rewrite install_group_empty.
    + unfold ag_s6, ag_s5, ag_aidx, ag_plan, ag_cnt0. cbn [ibind]. reflexivity.
    + unfold active_hd. cbn [st_active set_mmap_counter set_regions]. rewrite sq_active, ab_active. exact Hhd.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition AGN (sc : Z) (m : sptr) (cnt0 j : Z) (idx : Z) : M (option sptr) :=
        if idx <? 0 then free_meta m ;; ret None
        else
          hj <- get_head (HActive j) ;;
          match hj with
          | None => fail (FModel 8)
          | Some g =>
              amg <- getm g ;;
              mcheck (stride_of amg =? class_size j) 11 ;;
              s <- get ;;
              p <- enframe g idx (class_size j - IB) (st_mmap_counter s) FGroup ;;
              install_group m sc cnt0 (cnt0 - 1) 0 p slot_junk ;;
              ret (Some m)
          end.

Definition ag_total (s : astate) (sc : Z) : Z := UNIT + ag_cnt0 s sc * class_size sc - IB.
Definition ag_j (s : astate) (sc : Z) : Z := size_to_class (ag_total s sc).

Lemma ag_nested_tree : forall f sc req m s2, (PGSZ / 2 <? class_size sc * initial_cnt sc (usage_of s2 sc) + UNIT) = false ->
  AGK f sc req (Some m) s2 = ibind (alloc_slot f (ag_j s2 sc) (ag_total s2 sc) s2)
    (fun r => match r with (idx, s') => AGN sc m (ag_cnt0 s2 sc) (ag_j s2 sc) idx s' end).
Proof. intros f sc req m s2 Hc. unfold AGK. unfold bind at 1, get. cbn [ibind]. rewrite Hc. reflexivity. Qed.

(* [comment removed for export] *)
Definition ef_grp_st (g : sptr) (amg : ameta) (idx n : Z) (s : astate) : astate :=
  set_metas (mupdate (st_metas s) g (MUsed (upd_slot amg idx (mkSlot (Some (idx + 192, (stride_of amg * idx) / UNIT)) (Some (mkFrame 0 n FGroup)))))) s.

Lemma enframe_grp : forall g amg idx n ctr s, MT s g = Some (MUsed amg) -> 0 <= idx <= am_last amg -> stride_of amg - IB - n = 0 ->
  enframe g idx n ctr FGroup s = IRet (padd (slot_start amg idx) 0, ef_grp_st g amg idx n s).
Proof.
  intros g amg idx n ctr s Mg Hidx Hn. unfold enframe, getm, bind, get. cbn [ibind]. unfold MT in Mg. rewrite Mg. cbn [ibind ret].
  replace ((0 <=? idx) && (idx <=? am_last amg)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.leb_le]; lia).
  unfold mcheck. cbn [ibind ret]. rewrite Hn. cbn [Z.div Z.eqb]. unfold ret. cbn [ibind].
  cbn [Z.ltb Z.compare]. cbn [massert Z.leb Z.compare ret]. unfold massert, ret. cbn [ibind].
  replace (stride_of amg - IB - UNIT * 0 - n) with 0 by (unfold UNIT; lia). cbn [Z.leb Z.compare Z.eqb].
  unfold setm, modify, ef_grp_st. cbn [ibind]. reflexivity.
Qed.

Definition ag_nest_st (m : sptr) (sc cnt0 : Z) (g : sptr) (amg : ameta) (idx j : Z) (s : astate) : astate :=
  ins_st m sc cnt0 (cnt0 - 1) 0 (padd (slot_start amg idx) 0) slot_junk (ef_grp_st g amg idx (class_size j - IB) s).

Lemma AGN_eq : forall sc m cnt0 j idx s g amg, 0 <= idx -> active_hd s j = Some g -> MT s g = Some (MUsed amg) -> stride_of amg = class_size j ->
  idx <= am_last amg -> active_hd s sc = None ->
  AGN sc m cnt0 j idx s = IRet (Some m, ag_nest_st m sc cnt0 g amg idx j s).
Proof.
  intros sc m cnt0 j idx s g amg Hidx Hhd Mg Hstr Hl Hsc. unfold AGN.
  replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  unfold get_head, bind, get. cbn [ibind]. change (nth (Z.to_nat j) (st_active s) None) with (active_hd s j). rewrite Hhd. unfold ret at 1. cbn [ibind].
  unfold getm, bind, get. cbn [ibind]. unfold MT in Mg. rewrite Mg. unfold ret. cbn [ibind].
  rewrite Hstr, Z.eqb_refl. unfold mcheck, ret. cbn [ibind].
  rewrite (enframe_grp g amg idx (class_size j - IB) (st_mmap_counter s) s Mg ltac:(lia) ltac:(rewrite Hstr; lia)). cbn [ibind].
  rewrite install_group_empty; [reflexivity|].
  unfold active_hd, ef_grp_st. cbn [st_active set_metas]. exact Hsc.
Qed.
