(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN2y.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO12.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0y.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN26.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN31.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Local Open Scope mm_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition TA_D (m3 : sptr) : M Z :=
mask <- activate_group m3 ;;
massert (negb (mask =? 0)) 3 ;;
am3 <- getm m3 ;;
decay_bounces (am_sc am3) ;;
let first := lowbit mask in
am3 <- getm m3 ;;
setm m3 (am_set_avail (mask - first) am3) ;;
ret first.
Definition SEL_C (sc : Z) (m2 : sptr) (am2 : ameta) : M sptr :=
let mask := am_freed am2 in
if Z.land mask (ones (am_aidx am2)) =? 0 then
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
else ret m2.
Definition TA_C (sc : Z) (m2 : sptr) : M Z :=
am2 <- getm m2 ;; m3 <- SEL_C sc m2 am2 ;; TA_D m3.
Definition SEL_B (sc : Z) (m1 : sptr) (am1 : ameta) : M sptr :=
if am_freed am1 =? ones (am_last am1)
then match am_next am1 with
| Some nx => set_head (HActive sc) (Some nx) ;; ret nx
| None => fail (FModel 6)
end
else ret m1.
Definition TA_B (sc : Z) (m1 : sptr) : M Z :=
am1 <- getm m1 ;; m2 <- SEL_B sc m1 am1 ;; TA_C sc m2.
Definition STEP_A (sc : Z) (m0 : sptr) (am0 : ameta) : M (option sptr) :=
if am_freed am0 =? 0
then dequeue (HActive sc) m0 ;; get_head (HActive sc)
else set_head (HActive sc) (am_next am0) ;; ret (am_next am0).
Definition KA (sc : Z) (r : option sptr * astate) : itree astate (Z * astate) :=
match fst r with None => IRet (0, snd r) | Some m1 => TA_B sc m1 (snd r) end.
Definition span_cnt (am2 : ameta) : Z :=
let size := class_size (am_sc am2) in
let cnt0 := am_aidx am2 + 2 in
let cnt1 := span_loop 300%nat cnt0 (UNIT + size * cnt0) size in
if am_last am2 + 1 <? cnt1 then am_last am2 + 1 else cnt1.
Definition sameX (s s' : astate) : Prop :=
st_regions s' = st_regions s /\ st_areas s' = st_areas s /\ st_usage s' = st_usage s /\
st_meta_alloc_shift s' = st_meta_alloc_shift s /\ st_avail_meta_areas s' = st_avail_meta_areas s /\
st_brk s' = st_brk s /\ st_init_done s' = st_init_done s /\ keys s' = keys s /\
length (st_active s') = length (st_active s) /\ length (st_bounces s') = length (st_bounces s).
Lemma sameX_refl s : sameX s s.
Proof. repeat split; reflexivity. Qed.
Lemma sameX_trans s1 s2 s3 : sameX s1 s2 -> sameX s2 s3 -> sameX s1 s3.
Proof. unfold sameX. intros (?&?&?&?&?&?&?&?&?&?) (?&?&?&?&?&?&?&?&?&?). repeat split; congruence. Qed.
Lemma sameX_set_active s k v : sameX s (set_active (lupd (st_active s) k v) s).
Proof. repeat split; try reflexivity. cbn. apply length_lupd. Qed.
Lemma sameX_upd_meta s g am am' : MT s g = Some (MUsed am) -> sameX s (upd_meta g (MUsed am') s).
Proof.
intros Mg. repeat split; try reflexivity. apply keys_upd_In. eapply MT_Some_In_keys. exact Mg.
Qed.
Lemma sameX_set_bounces s l : length l = length (st_bounces s) -> sameX s (set_bounces l s).
Proof. intros Hl. repeat split; try reflexivity. exact Hl. Qed.
Lemma mask_u32' (m last : Z) : 0 <= m -> 0 <= last <= 31 -> (forall i, last < i -> Z.testbit m i = false) -> m < 2 ^ 32.
Proof.
intros Hm Hl Hb. apply (Z.lt_le_trans _ (2 ^ (last + 1))); [|apply Z.pow_le_mono_r; lia].
apply lt_pow2_of_testbit; [lia|lia|]. intros i Hi. apply Hb. lia.
Qed.
Record bnd (X : list sptr) (U : Z -> Z) (s0 : astate) (sc : Z) (s : astate) (m : sptr) (am : ameta) : Prop := BND_ {
b_inv : Inv X None U s;
b_hd : active_hd s sc = Some m;
b_used : usedX X s m am;
b_sc : am_sc am = sc;
b_freed : am_freed am <> 0;
b_zero : allzero X s sc;
b_oth : forall c, 0 <= c -> c <> sc -> active_hd s c = active_hd s0 c;
b_ub : ub_same s0 s;
b_same : sameX s0 s;
b_span : span_ok s0 -> span_ok s     }.
Lemma set_head_eval sc v s : set_head (HActive sc) v s = IRet (tt, set_active (lupd (st_active s) (Z.to_nat sc) v) s).
Proof. reflexivity. Qed.
Lemma am_links_next ampr nx : am_set_links (am_prev ampr) nx ampr = am_set_next nx ampr.
Proof. destruct ampr; reflexivity. Qed.
Lemma am_links_prev amnx pr : am_set_links pr (am_next amnx) amnx = am_set_prev pr amnx.
Proof. destruct amnx; reflexivity. Qed.
Section b.
Variables (X : list sptr) (U : Z -> Z) (s : astate) (sc : Z) (m0 : sptr) (am0 : ameta).
Hypothesis HI : Inv X None U s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hhd : active_hd s sc = Some m0.
Hypothesis M0 : MT s m0 = Some (MUsed am0).
Hypothesis Hav : am_avail am0 = 0.
Lemma m0_used : usedX X s m0 am0 /\ am_sc am0 = sc.
Proof.
destruct (head_used X None U s sc m0 HI Hsc Hhd) as (am' & Hu & Hs').
pose proof (proj1 (usedX_MT _ _ _ _ Hu)) as M'. rewrite M0 in M'. injection M' as <-. auto.
Qed.
Lemma zero0 : allzero X s sc.
Proof.
destruct m0_used as [Hu0 Hs0]. destruct (inv_rings HI) as (_ & A & _). destruct (A sc Hsc) as (ms & Rg & Mem & Full & Q1 & Q2).
intros g am Hg Hsg. destruct (Z.eq_dec (am_avail am) 0) as [E|E]; [exact E|]. exfalso.
pose proof (Q1 g am Hg Hsg E) as E2. rewrite Hhd in E2. injection E2 as ->.
pose proof (usedX_fun _ _ _ _ _ Hg Hu0) as ->. exact (E Hav).
Qed.
Lemma act_len : length (st_active s) = 48%nat.
Proof. exact (proj1 (inv_ctx HI)). Qed.
Lemma try_avail_slow : try_avail sc s = ibind (STEP_A sc m0 am0 s) (KA sc).
Proof.
unfold try_avail. erewrite (bind_eval _ _ s) by apply get_head_active_eval. rewrite Hhd.
erewrite (bind_eval _ _ s) by (apply getm_eval; exact M0). rewrite Hav. cbn [Z.eqb negb].
unfold bind at 1. apply ibind_ext. intros [[m1|] s1]; reflexivity.
Qed.
Lemma links0 : exists pr nx ampr amnx, am_prev am0 = Some pr /\ am_next am0 = Some nx /\
usedX X s pr ampr /\ usedX X s nx amnx /\ am_sc ampr = sc /\ am_sc amnx = sc /\
(nx = m0 <-> pr = m0) /\ (nx <> m0 -> am_freed amnx <> 0 /\ am_avail amnx = 0) /\
(pr = nx -> pr <> m0 -> am_prev amnx = Some m0 /\ am_next amnx = Some m0) /\
(pr <> nx -> am_prev amnx = Some m0 /\ am_next ampr = Some m0).
Proof.
destruct m0_used as [Hu0 Hs0]. destruct (inv_rings HI) as (_ & A & _). destruct (A sc Hsc) as (ms & Rg & Mem & Full & Q1 & Q2).
rewrite Hhd in Rg. destruct (ring_head_links X s sc m0 am0 ms Rg Hu0) as (rest & Ems & Hpr & Hnx).
assert (Inx : In (hd m0 rest) ms) by (rewrite Ems; destruct rest; [left; reflexivity | right; left; reflexivity]).
assert (Ipr : In (last rest m0) ms).
{ rewrite Ems. destruct rest as [|r rest']; [left; reflexivity | right]. apply In_last. discriminate. }
destruct (ring_members_used _ _ _ _ _ _ Rg Inx) as (amnx & Hun & Hsn).
destruct (ring_members_used _ _ _ _ _ _ Rg Ipr) as (ampr & Hup & Hsp).
exists (last rest m0), (hd m0 rest), ampr, amnx. split; [exact Hpr|]. split; [exact Hnx|]. split; [exact Hup|]. split; [exact Hun|].
split; [exact Hsp|]. split; [exact Hsn|].
destruct Rg as [[Hnd Hch] _]. rewrite Ems in Hnd, Hch.
assert (LKnx : forall r rest', rest = r :: rest' -> alinks X s sc r = Some (Some m0, Some (hd m0 rest'))).
{ intros r rest' ->. cbn [chain] in Hch. exact (proj1 (proj2 Hch)). }
split; [|split; [|split]].
- destruct rest as [|r rest']; [cbn; split; intros; reflexivity|]. cbn [hd].
pose proof (proj1 (proj1 (NoDup_cons_iff _ _) Hnd)) as Hni.
split; intros E; exfalso; apply Hni.
+ left. exact E.
+ rewrite <- E at 1. apply In_last. discriminate.
- intros Hne. destruct (head_links X U s sc m0 am0 HI Hsc Hhd Hu0 Hs0) as (pr' & nx' & Hpr' & Hnx' & amn' & Hun' & _ & Hnxf).
rewrite Hnx in Hnx'. injection Hnx' as <-. pose proof (usedX_fun _ _ _ _ _ Hun' Hun) as ->. exact (Hnxf Hne).
- intros Epn Hpm.
destruct rest as [|r rest']; cbn [hd] in *; [exfalso; exact (Hpm eq_refl)|].
assert (rest' = []) as ->.
{ destruct rest' as [|r2 rest2]; [reflexivity|]. exfalso.
pose proof (proj1 (proj1 (NoDup_cons_iff _ _) (proj2 (proj1 (NoDup_cons_iff _ _) Hnd)))) as Hni2.
apply Hni2. rewrite <- Epn at 1. change (In (last (r2 :: rest2) m0) (r2 :: rest2)). apply In_last. discriminate. }
destruct (alinks_used _ _ _ _ _ (LKnx r [] eq_refl)) as (am' & Hu' & _ & El). pose proof (usedX_fun _ _ _ _ _ Hu' Hun) as ->.
cbn [hd] in El. injection El as E1 E2. auto.
- intros Hpn. destruct rest as [|r rest']; cbn [hd] in *; [exfalso; exact (Hpn eq_refl)|]. split.
+ destruct (alinks_used _ _ _ _ _ (LKnx r rest' eq_refl)) as (am' & Hu' & _ & El). pose proof (usedX_fun _ _ _ _ _ Hu' Hun) as ->.
injection El as E1 E2. symmetry. exact E1.
+
assert (LAST : forall l p, chain (alinks X s sc) p l m0 -> l <> [] -> exists q, alinks X s sc (last l m0) = Some (q, Some m0)).
{ induction l as [|x l IH]; intros p Hc Hne; [exfalso; exact (Hne eq_refl)|]. cbn [chain] in Hc. destruct Hc as [Hx Hc].
destruct l as [|y l']; [exists (Some p); cbn [last hd] in *; exact Hx|].
change (last (x :: y :: l') m0) with (last (y :: l') m0). apply (IH x Hc). discriminate. }
cbn [chain] in Hch. destruct Hch as [_ Hc]. destruct (LAST (r :: rest') m0 Hc ltac:(discriminate)) as (q & Hl).
destruct (alinks_used _ _ _ _ _ Hl) as (am' & Hu' & _ & El). pose proof (usedX_fun _ _ _ _ _ Hu' Hup) as ->.
injection El as E1 E2. symmetry. exact E2.
Qed.
Definition am0' : ameta := am_set_links None None am0.
Definition hd_upd (v : option sptr) (s1 : astate) : astate := set_active (lupd (st_active s1) (Z.to_nat sc) v) s1.
Definition sA_rot (nx : sptr) : astate := hd_upd (Some nx) s.
Definition sA_D1 : astate := upd_meta m0 (MUsed am0') (hd_upd None s).
Definition sA_D2 (nx : sptr) (amnx : ameta) : astate :=
upd_meta m0 (MUsed am0') (hd_upd (Some nx) (upd_meta nx (MUsed (am_set_links (Some nx) (Some nx) amnx)) s)).
Definition sA_D3 (pr nx : sptr) (ampr amnx : ameta) : astate :=
upd_meta m0 (MUsed am0') (hd_upd (Some nx) (upd_meta nx (MUsed (am_set_prev (Some pr) amnx)) (upd_meta pr (MUsed (am_set_next (Some nx) ampr)) s))).
Lemma itok_IRet {T} (r : T) (Q : T -> Prop) : itok (IRet r) Q -> Q r.
Proof. exact (fun H => H). Qed.
Lemma stepA_R1 nx : am_freed am0 <> 0 -> am_next am0 = Some nx -> STEP_A sc m0 am0 s = IRet (Some nx, sA_rot nx).
Proof.
intros Hfr Hnx. unfold STEP_A. rewrite (proj2 (Z.eqb_neq _ _) Hfr), Hnx.
erewrite (bind_eval _ _ s) by apply set_head_eval. reflexivity.
Qed.
Lemma dequeue_D1 : am_next am0 = Some m0 -> dequeue (HActive sc) m0 s = IRet (tt, sA_D1).
Proof.
intros Hnx. unfold dequeue.
erewrite (bind_eval _ _ s) by (apply (get_links_eval s m0 (MUsed am0)); exact M0). cbn [links_of snd fst]. rewrite Hnx. cbn [osptr_eqb]. rewrite sptr_eqb_refl.
erewrite (bind_eval _ _ s) by apply set_head_eval.
rewrite (set_links_eval _ m0 (MUsed am0)) by (unfold MT; cbn; exact M0). reflexivity.
Qed.
Lemma stepA_D1 : am_freed am0 = 0 -> am_next am0 = Some m0 -> STEP_A sc m0 am0 s = IRet (None, sA_D1).
Proof.
intros Hfr Hnx. unfold STEP_A. rewrite Hfr. cbn [Z.eqb].
rewrite (bind_eval _ _ s tt sA_D1 (dequeue_D1 Hnx)). rewrite get_head_active_eval. f_equal. f_equal.
unfold sA_D1. rewrite active_hd_upd_meta. unfold hd_upd. apply active_hd_set_active_same. rewrite act_len. lia.
Qed.
Lemma dequeue_D2 nx amnx : am_prev am0 = Some nx -> am_next am0 = Some nx -> nx <> m0 -> MT s nx = Some (MUsed amnx) ->
dequeue (HActive sc) m0 s = IRet (tt, sA_D2 nx amnx).
Proof.
intros Hpr Hnx Hne Mnx. unfold dequeue.
erewrite (bind_eval _ _ s) by (apply (get_links_eval s m0 (MUsed am0)); exact M0). cbn [links_of snd fst]. rewrite Hnx, Hpr. cbn [osptr_eqb].
replace (sptr_eqb nx m0) with false by (symmetry; apply sptr_eqb_neq; exact Hne).
erewrite (bind_eval (bind _ _) _ s).
2:{ unfold set_next. erewrite (bind_eval (bind _ _) _ s).
2:{ erewrite (bind_eval _ _ s) by (apply (get_links_eval s nx (MUsed amnx)); exact Mnx). cbn [links_of fst]. apply (set_links_eval s nx (MUsed amnx)). exact Mnx. }
unfold set_prev. erewrite (bind_eval (bind _ _) _ _).
2:{ erewrite (bind_eval _ _ _) by (apply get_links_eval; apply MT_upd_same). cbn [with_links links_of snd am_next am_set_links]. apply set_links_eval. apply MT_upd_same. }
erewrite (bind_eval _ _ _) by apply get_head_active_eval. rewrite !active_hd_upd_meta, Hhd. cbn [osptr_eqb]. rewrite sptr_eqb_refl.
apply set_head_eval. }
rewrite (set_links_eval _ m0 (MUsed am0)).
2:{ rewrite MT_set_active, !MT_upd_other by (intros E; exact (Hne (eq_sym E))). exact M0. }
f_equal. f_equal. unfold sA_D2, hd_upd, am0'. cbn [with_links]. rewrite upd_meta_twice.
destruct amnx; reflexivity.
Qed.
Lemma stepA_D2 nx amnx : am_freed am0 = 0 -> am_prev am0 = Some nx -> am_next am0 = Some nx -> nx <> m0 -> MT s nx = Some (MUsed amnx) ->
STEP_A sc m0 am0 s = IRet (Some nx, sA_D2 nx amnx).
Proof.
intros Hfr Hpr Hnx Hne Mnx. unfold STEP_A. rewrite Hfr. cbn [Z.eqb].
rewrite (bind_eval _ _ s tt (sA_D2 nx amnx) (dequeue_D2 nx amnx Hpr Hnx Hne Mnx)). rewrite get_head_active_eval. f_equal. f_equal.
unfold sA_D2. rewrite active_hd_upd_meta. unfold hd_upd. apply active_hd_set_active_same. cbn [st_active upd_meta set_metas]. rewrite act_len. lia.
Qed.
Lemma dequeue_D3 pr nx ampr amnx : am_prev am0 = Some pr -> am_next am0 = Some nx -> nx <> m0 -> pr <> m0 -> pr <> nx ->
MT s pr = Some (MUsed ampr) -> MT s nx = Some (MUsed amnx) ->
dequeue (HActive sc) m0 s = IRet (tt, sA_D3 pr nx ampr amnx).
Proof.
intros Hpr Hnx Hne Hpe Hpn Mpr Mnx. unfold dequeue.
erewrite (bind_eval _ _ s) by (apply (get_links_eval s m0 (MUsed am0)); exact M0). cbn [links_of snd fst]. rewrite Hnx, Hpr. cbn [osptr_eqb].
replace (sptr_eqb nx m0) with false by (symmetry; apply sptr_eqb_neq; exact Hne).
erewrite (bind_eval (bind _ _) _ s).
2:{ unfold set_next. erewrite (bind_eval (bind _ _) _ s).
2:{ erewrite (bind_eval _ _ s) by (apply (get_links_eval s pr (MUsed ampr)); exact Mpr). cbn [links_of fst]. apply (set_links_eval s pr (MUsed ampr)). exact Mpr. }
unfold set_prev. erewrite (bind_eval (bind _ _) _ _).
2:{ erewrite (bind_eval _ _ _) by (apply (get_links_eval _ nx (MUsed amnx)); rewrite MT_upd_other by (intros E; exact (Hpn (eq_sym E))); exact Mnx).
cbn [with_links links_of snd]. apply (set_links_eval _ nx (MUsed amnx)). rewrite MT_upd_other by (intros E; exact (Hpn (eq_sym E))). exact Mnx. }
erewrite (bind_eval _ _ _) by apply get_head_active_eval. rewrite !active_hd_upd_meta, Hhd. cbn [osptr_eqb]. rewrite sptr_eqb_refl.
apply set_head_eval. }
rewrite (set_links_eval _ m0 (MUsed am0)).
2:{ rewrite MT_set_active, MT_upd_other by (intros E; exact (Hne (eq_sym E))). rewrite MT_upd_other by (intros E; exact (Hpe (eq_sym E))). exact M0. }
reflexivity.
Qed.
Lemma stepA_D3 pr nx ampr amnx : am_freed am0 = 0 -> am_prev am0 = Some pr -> am_next am0 = Some nx -> nx <> m0 -> pr <> m0 -> pr <> nx ->
MT s pr = Some (MUsed ampr) -> MT s nx = Some (MUsed amnx) ->
STEP_A sc m0 am0 s = IRet (Some nx, sA_D3 pr nx ampr amnx).
Proof.
intros Hfr Hpr Hnx Hne Hpe Hpn Mpr Mnx. unfold STEP_A. rewrite Hfr. cbn [Z.eqb].
rewrite (bind_eval _ _ s tt (sA_D3 pr nx ampr amnx) (dequeue_D3 pr nx ampr amnx Hpr Hnx Hne Hpe Hpn Mpr Mnx)). rewrite get_head_active_eval. f_equal. f_equal.
unfold sA_D3. rewrite active_hd_upd_meta. unfold hd_upd. apply active_hd_set_active_same. cbn [st_active upd_meta set_metas]. rewrite act_len. lia.
Qed.
Lemma stepA_post : itok (STEP_A sc m0 am0 s) (fun r =>
Inv X None U (snd r) /\ active_hd (snd r) sc = fst r /\ allzero X (snd r) sc /\
(forall c, 0 <= c -> c <> sc -> active_hd (snd r) c = active_hd s c) /\ ub_same s (snd r) /\
match fst r with
| None => True
| Some m1 => exists am1, usedX X (snd r) m1 am1 /\ am_sc am1 = sc /\ am_freed am1 <> 0
end).
Proof.
destruct m0_used as [Hu0 Hs0]. pose proof zero0 as Hz. unfold STEP_A.
destruct (am_freed am0 =? 0) eqn:Efr.
- apply Z.eqb_eq in Efr. apply itok_bind.
eapply (Inv_dequeue_full_head X None U s sc m0 am0); try assumption; [intros q i; discriminate|].
intros s1 HI1 Sb Hse Bwd Fwd M0' Hnew UB1. cbn [fst snd]. apply itok_get_head. cbn [fst snd].
change (nth (Z.to_nat sc) (st_active s1) None) with (active_hd s1 sc).
split; [exact HI1|]. split; [reflexivity|]. split.
{ intros g am' Hg Hsg. destruct (Bwd _ _ Hg) as (am & Hga & E). pose proof (strip_fields _ _ E) as (_&Eav'&_&_&Es&_).
rewrite Eav'. apply (Hz g am Hga). congruence. }
split.
{ intros c Hc0 Hc. destruct Hse as (Hoth & _ & _). unfold active_hd. apply Hoth. intros sc' E. injection E as <-. lia. }
split; [exact UB1|].
destruct (active_hd s1 sc) as [m1|]; [|exact I].
destruct Hnew as (Hne & am1 & Hu1 & Hs1 & Hf1 & _). exists am1. auto.
- apply Z.eqb_neq in Efr.
destruct (head_links X U s sc m0 am0 HI Hsc Hhd Hu0 Hs0) as (pr & nx & Hpr & Hnx & amn & Hun & Hsn & Hnxf).
rewrite Hnx. apply itok_bind. rewrite set_head_eval. cbn [itok fst snd]. apply itok_ret. cbn [fst snd].
split; [exact (Inv_rotate_head X None U s sc m0 am0 nx HI Hsc Hu0 Hs0 Hhd Hav Efr Hnx)|].
split; [apply active_hd_set_active_same; rewrite act_len; lia|].
split; [intros g am Hg Hsg; apply (Hz g am Hg Hsg)|].
split; [intros c Hc0 Hc; rewrite active_hd_set_active_other by lia; reflexivity|].
split; [apply ub_same_metas; reflexivity|].
exists amn. split; [exact Hun|]. split; [exact Hsn|].
destruct (sptr_eq_dec nx m0) as [->|Hne]; [| apply (proj1 (Hnxf Hne))].
pose proof (usedX_fun _ _ _ _ _ Hun Hu0) as ->. exact Efr.
Qed.
Lemma bnd_A m1 s1 : STEP_A sc m0 am0 s = IRet (Some m1, s1) -> sameX s s1 -> (span_ok s -> span_ok s1) -> exists am1, bnd X U s sc s1 m1 am1.
Proof.
intros E SX SP. pose proof stepA_post as P. rewrite E in P. cbn [itok fst snd] in P.
destruct P as (HI1 & Hhd1 & Hz1 & Hoth1 & UB1 & am1 & Hu1 & Hs1 & Hf1). exists am1. split; assumption.
Qed.
Lemma span_R1 nx : span_ok s -> span_ok (sA_rot nx).
Proof. unfold sA_rot, hd_upd. apply span_ok_set_active. Qed.
Lemma span_D1 : span_ok s -> span_ok sA_D1.
Proof.
intros SP. unfold sA_D1, hd_upd, am0'. apply (span_ok_upd_set_links _ m0 am0); [apply span_ok_set_active; exact SP|]. rewrite MT_set_active. exact M0.
Qed.
Lemma span_D2 nx amnx : MT s nx = Some (MUsed amnx) -> nx <> m0 -> span_ok s -> span_ok (sA_D2 nx amnx).
Proof.
intros Mnx Hne SP. unfold sA_D2, hd_upd, am0'. apply (span_ok_upd_set_links _ m0 am0).
- apply span_ok_set_active. apply (span_ok_upd_set_links _ nx amnx); [exact SP | exact Mnx].
- rewrite MT_set_active, MT_upd_other by (intros E; exact (Hne (eq_sym E))). exact M0.
Qed.
Lemma span_D3 pr nx ampr amnx : MT s pr = Some (MUsed ampr) -> MT s nx = Some (MUsed amnx) -> nx <> m0 -> pr <> m0 -> pr <> nx ->
span_ok s -> span_ok (sA_D3 pr nx ampr amnx).
Proof.
intros Mpr Mnx Hne Hpe Hpn SP. unfold sA_D3, hd_upd, am0'. apply (span_ok_upd_set_links _ m0 am0).
- apply span_ok_set_active. apply (span_ok_upd_set_prev _ nx amnx); [apply (span_ok_upd_set_next _ pr ampr); [exact SP | exact Mpr]|].
rewrite MT_upd_other by (intros E; exact (Hpn (eq_sym E))). exact Mnx.
- rewrite MT_set_active, MT_upd_other by (intros E; exact (Hne (eq_sym E))). rewrite MT_upd_other by (intros E; exact (Hpe (eq_sym E))). exact M0.
Qed.
Lemma sameX_R1 nx : sameX s (sA_rot nx).
Proof. apply sameX_set_active. Qed.
Lemma sameX_D1 : sameX s sA_D1.
Proof.
unfold sA_D1. eapply sameX_trans; [apply (sameX_set_active s (Z.to_nat sc) None)|].
apply (sameX_upd_meta _ m0 am0). rewrite MT_set_active. exact M0.
Qed.
Lemma sameX_D2 nx amnx : MT s nx = Some (MUsed amnx) -> nx <> m0 -> sameX s (sA_D2 nx amnx).
Proof.
intros Mnx Hne. unfold sA_D2.
eapply sameX_trans; [apply (sameX_upd_meta s nx amnx); exact Mnx|].
eapply sameX_trans; [apply sameX_set_active|]. unfold hd_upd.
apply (sameX_upd_meta _ m0 am0). rewrite MT_set_active, MT_upd_other by (intros E; exact (Hne (eq_sym E))). exact M0.
Qed.
Lemma sameX_D3 pr nx ampr amnx : MT s pr = Some (MUsed ampr) -> MT s nx = Some (MUsed amnx) -> nx <> m0 -> pr <> m0 -> pr <> nx ->
sameX s (sA_D3 pr nx ampr amnx).
Proof.
intros Mpr Mnx Hne Hpe Hpn. unfold sA_D3.
eapply sameX_trans; [apply (sameX_upd_meta s pr ampr); exact Mpr|].
eapply sameX_trans; [apply (sameX_upd_meta _ nx amnx); rewrite MT_upd_other by (intros E; exact (Hpn (eq_sym E))); exact Mnx|].
eapply sameX_trans; [apply sameX_set_active|]. unfold hd_upd.
apply (sameX_upd_meta _ m0 am0). rewrite MT_set_active, MT_upd_other by (intros E; exact (Hne (eq_sym E))). rewrite MT_upd_other by (intros E; exact (Hpe (eq_sym E))). exact M0.
Qed.
Lemma post_D1 : am_freed am0 = 0 -> am_next am0 = Some m0 ->
Inv X None U sA_D1 /\ active_hd sA_D1 sc = None /\ (forall c, 0 <= c -> c <> sc -> active_hd sA_D1 c = active_hd s c) /\
ub_same s sA_D1 /\ sameX s sA_D1 /\ MT sA_D1 m0 = Some (MUsed am0').
Proof.
intros Hfr Hnx. pose proof stepA_post as P. rewrite (stepA_D1 Hfr Hnx) in P. cbn [itok fst snd] in P.
destruct P as (HI1 & Hhd1 & _ & Hoth1 & UB1 & _). repeat (split; [assumption|]). split; [apply sameX_D1|].
unfold sA_D1. apply MT_upd_same.
Qed.
Section d.
Variables (s1 : astate) (m1 : sptr) (am1 : ameta).
Hypothesis B1 : bnd X U s sc s1 m1 am1.
Lemma act_len1 : length (st_active s1) = 48%nat.
Proof. exact (proj1 (inv_ctx (b_inv _ _ _ _ _ _ _ B1))). Qed.
Lemma TA_B_eval : TA_B sc m1 s1 = ibind (SEL_B sc m1 am1 s1) (fun r => TA_C sc (fst r) (snd r)).
Proof.
unfold TA_B. erewrite (bind_eval _ _ s1) by (apply getm_eval; exact (proj1 (usedX_MT _ _ _ _ (b_used _ _ _ _ _ _ _ B1)))).
unfold bind at 1. apply ibind_ext. intros [m2 s2]; reflexivity.
Qed.
Lemma links1 : exists pr nx amnx, am_prev am1 = Some pr /\ am_next am1 = Some nx /\
usedX X s1 nx amnx /\ am_sc amnx = sc /\ am_freed amnx <> 0 /\ am_avail amnx = 0.
Proof.
destruct B1 as [HI1 Hhd1 Hu1 Hs1 Hf1 Hz1 _ _ _ SP1].
destruct (head_links X U s1 sc m1 am1 HI1 Hsc Hhd1 Hu1 Hs1) as (pr & nx & Hpr & Hnx & amn & Hun & Hsn & Hnxf).
exists pr, nx, amn. split; [exact Hpr|]. split; [exact Hnx|]. split; [exact Hun|]. split; [exact Hsn|]. split.
- destruct (sptr_eq_dec nx m1) as [->|Hne]; [| apply (proj1 (Hnxf Hne))]. pose proof (usedX_fun _ _ _ _ _ Hun Hu1) as ->. exact Hf1.
- apply (Hz1 nx amn Hun Hsn).
Qed.
Lemma selB_noskip : am_freed am1 <> ones (am_last am1) -> SEL_B sc m1 am1 s1 = IRet (m1, s1).
Proof. intros H. unfold SEL_B. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.
Lemma selB_skip nx : am_freed am1 = ones (am_last am1) -> am_next am1 = Some nx -> SEL_B sc m1 am1 s1 = IRet (nx, hd_upd (Some nx) s1).
Proof. intros H Hnx. unfold SEL_B. rewrite H, Z.eqb_refl, Hnx. erewrite (bind_eval _ _ s1) by apply set_head_eval. reflexivity. Qed.
Lemma bnd_B m2 s2 : SEL_B sc m1 am1 s1 = IRet (m2, s2) -> exists am2, bnd X U s sc s2 m2 am2.
Proof.
intros E. destruct B1 as [HI1 Hhd1 Hu1 Hs1 Hf1 Hz1 Hoth1 UB1 SX1 SP1].
unfold SEL_B in E. destruct (am_freed am1 =? ones (am_last am1)) eqn:Eall.
- destruct links1 as (pr & nx & amnx & Hpr & Hnx & Hun & Hsn & Hfn & Havn). rewrite Hnx in E.
rewrite (bind_eval _ _ s1 tt _ (set_head_eval sc (Some nx) s1)) in E. unfold ret in E. injection E as <- <-.
exists amnx. split.
+ exact (Inv_rotate_head X None U s1 sc m1 am1 nx HI1 Hsc Hu1 Hs1 Hhd1 (Hz1 _ _ Hu1 Hs1) Hf1 Hnx).
+ apply active_hd_set_active_same. rewrite act_len1. lia.
+ exact Hun.
+ exact Hsn.
+ exact Hfn.
+ intros g am Hg Hsg. apply (Hz1 g am Hg Hsg).
+ intros c Hc0 Hc. rewrite active_hd_set_active_other by lia. apply Hoth1; assumption.
+ eapply ub_same_trans; [exact UB1 | apply ub_same_metas; reflexivity].
+ eapply sameX_trans; [exact SX1 | apply sameX_set_active].
+ intros SP. apply span_ok_set_active. exact (SP1 SP).
- unfold ret in E. injection E as <- <-. exists am1. exact B1.
Qed.
End d.
Section e.
Variables (s2 : astate) (m2 : sptr) (am2 : ameta).
Hypothesis B2 : bnd X U s sc s2 m2 am2.
Lemma act_len2 : length (st_active s2) = 48%nat.
Proof. exact (proj1 (inv_ctx (b_inv _ _ _ _ _ _ _ B2))). Qed.
Lemma TA_C_eval : TA_C sc m2 s2 = ibind (SEL_C sc m2 am2 s2) (fun r => TA_D (fst r) (snd r)).
Proof.
unfold TA_C. erewrite (bind_eval _ _ s2) by (apply getm_eval; exact (proj1 (usedX_MT _ _ _ _ (b_used _ _ _ _ _ _ _ B2)))).
unfold bind at 1. apply ibind_ext. intros [m3 s3]; reflexivity.
Qed.
Lemma grp2 : 0 <= am_aidx am2 <= am_last am2 /\ am_last am2 <= 31 /\ 0 <= am_freed am2 < 2 ^ 32 /\ am_avail am2 = 0 /\
(Z.land (am_freed am2) (ones (am_aidx am2)) = 0 -> am_aidx am2 < am_last am2).
Proof.
destruct B2 as [HI2 Hhd2 Hu2 Hs2 Hf2 Hz2 _ _ _ SP2].
pose proof (inv_groups HI2 m2 am2 Hu2) as ((Glast & Gaidx & Glen & Gav & Gfr & Gdisj & Gabove & Gavp & Gfra) & _).
assert (Hfr32 : am_freed am2 < 2 ^ 32) by (apply (mask_u32' _ (am_last am2)); [lia|lia|intros i Hi; apply (proj2 (Gabove i Hi))]).
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact (Hz2 _ _ Hu2 Hs2)|].
intros Ec. destruct (Z_lt_dec (am_aidx am2) (am_last am2)) as [|Hge]; [assumption|]. exfalso. apply Hf2.
apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0.
destruct (Z_le_dec i (am_last am2)).
- apply (f_equal (fun z => Z.testbit z i)) in Ec. rewrite Z.land_spec, Z.bits_0, testbit_ones in Ec by lia.
replace (0 <=? i) with true in Ec by (symmetry; apply Z.leb_le; lia).
replace (i <=? am_aidx am2) with true in Ec by (symmetry; apply Z.leb_le; lia).
rewrite andb_true_r in Ec. exact Ec.
- apply (proj2 (Gabove i ltac:(lia))).
Qed.
Lemma links2 : exists pr nx amnx, am_prev am2 = Some pr /\ am_next am2 = Some nx /\
usedX X s2 nx amnx /\ am_sc amnx = sc /\ am_freed amnx <> 0 /\ am_avail amnx = 0 /\
(Z.land (am_freed am2) (ones (am_aidx am2)) = 0 -> nx <> m2 -> Z.land (am_freed amnx) (ones (am_aidx amnx)) <> 0).
Proof.
destruct B2 as [HI2 Hhd2 Hu2 Hs2 Hf2 Hz2 _ _ _ SP2].
destruct (head_links X U s2 sc m2 am2 HI2 Hsc Hhd2 Hu2 Hs2) as (pr & nx & Hpr & Hnx & amn & Hun & Hsn & Hnxf).
exists pr, nx, amn. split; [exact Hpr|]. split; [exact Hnx|]. split; [exact Hun|]. split; [exact Hsn|].
assert (Hfn : am_freed amn <> 0).
{ destruct (sptr_eq_dec nx m2) as [->|Hne]; [| apply (proj1 (Hnxf Hne))]. pose proof (usedX_fun _ _ _ _ _ Hun Hu2) as ->. exact Hf2. }
split; [exact Hfn|]. split; [apply (Hz2 nx amn Hun Hsn)|].
intros Ec Enx E0. pose proof (proj2 (proj2 (proj2 (proj2 grp2))) Ec) as Haidx.
assert (Hnp : ~ am_aidx amn < am_last amn).
{ intros Hp. apply Enx. eapply (inv_partial HI2 nx amn m2 am2); eauto. congruence. }
pose proof (inv_groups HI2 nx amn Hun) as ((Nlast & Naidx & _ & _ & _ & _ & Nabove & _) & _).
apply Hfn. apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0.
destruct (Z_le_dec i (am_last amn)).
- apply (f_equal (fun z => Z.testbit z i)) in E0. rewrite Z.land_spec, Z.bits_0, testbit_ones in E0 by lia.
replace (0 <=? i) with true in E0 by (symmetry; apply Z.leb_le; lia).
replace (i <=? am_aidx amn) with true in E0 by (symmetry; apply Z.leb_le; lia).
rewrite andb_true_r in E0. exact E0.
- apply (proj2 (Nabove i ltac:(lia))).
Qed.
Definition sC2 : astate := upd_meta m2 (MUsed (am_set_aidx (span_cnt am2 - 1) am2)) s2.
Lemma selC_0 : Z.land (am_freed am2) (ones (am_aidx am2)) <> 0 -> SEL_C sc m2 am2 s2 = IRet (m2, s2).
Proof. intros H. unfold SEL_C. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.
Lemma selC_1 nx : Z.land (am_freed am2) (ones (am_aidx am2)) = 0 -> am_next am2 = Some nx -> nx <> m2 ->
SEL_C sc m2 am2 s2 = IRet (nx, hd_upd (Some nx) s2).
Proof.
intros H Hnx Hne. unfold SEL_C. rewrite H, Z.eqb_refl, Hnx. cbn [osptr_eqb]. replace (sptr_eqb nx m2) with false by (symmetry; apply sptr_eqb_neq; exact Hne).
cbn [negb]. erewrite (bind_eval _ _ s2) by apply set_head_eval. reflexivity.
Qed.
Lemma selC_2 : Z.land (am_freed am2) (ones (am_aidx am2)) = 0 -> am_next am2 = Some m2 -> SEL_C sc m2 am2 s2 = IRet (m2, sC2).
Proof.
intros H Hnx. unfold SEL_C. rewrite H, Z.eqb_refl, Hnx. cbn [osptr_eqb]. rewrite sptr_eqb_refl. cbn [negb].
erewrite (bind_eval _ _ s2) by apply setm_eval. reflexivity.
Qed.
Lemma span_cnt_range : Z.land (am_freed am2) (ones (am_aidx am2)) = 0 -> am_aidx am2 + 2 <= span_cnt am2 <= am_last am2 + 1.
Proof.
intros H. pose proof grp2 as (G1 & G2 & _ & _ & G5). specialize (G5 H). unfold span_cnt.
pose proof (span_loop_ge 300 (am_aidx am2 + 2) (UNIT + class_size (am_sc am2) * (am_aidx am2 + 2)) (class_size (am_sc am2))) as Hsp.
destruct (am_last am2 + 1 <? _) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia.
Qed.
Lemma bnd_C m3 s3 : SEL_C sc m2 am2 s2 = IRet (m3, s3) ->
exists am3, bnd X U s sc s3 m3 am3 /\ Z.land (am_freed am3) (ones (am_aidx am3)) <> 0.
Proof.
intros E. destruct B2 as [HI2 Hhd2 Hu2 Hs2 Hf2 Hz2 Hoth2 UB2 SX2 SP2] eqn:EB. clear EB.
pose proof (usedX_MT _ _ _ _ Hu2) as [M2 NX2].
destruct (Z.eq_dec (Z.land (am_freed am2) (ones (am_aidx am2))) 0) as [Ec|Ec].
- destruct links2 as (pr & nx & amnx & Hpr & Hnx & Hun & Hsn & Hfn & Havn & Hpart).
destruct (sptr_eq_dec nx m2) as [->|Hne].
+ rewrite (selC_2 Ec Hnx) in E. injection E as <- <-. pose proof (span_cnt_range Ec) as Hcnt.
exists (am_set_aidx (span_cnt am2 - 1) am2). split; [split|].
* unfold sC2. eapply extend_aidx_Inv; eauto; [lia | rewrite Hs2; exact Hhd2 | lia].
* unfold sC2. rewrite active_hd_upd_meta. exact Hhd2.
* apply usedX_intro; [exact NX2 | apply MT_upd_same].
* exact Hs2.
* exact Hf2.
* intros g am Hg Hs'. apply usedX_upd in Hg as [[-> [_ E']] | [Hne Hg]]; [injection E' as <-; cbn; apply (Hz2 _ _ Hu2 Hs2) | apply (Hz2 _ _ Hg Hs')].
* intros c Hc0 Hc. unfold sC2. rewrite active_hd_upd_meta. apply Hoth2; assumption.
* eapply ub_same_trans; [exact UB2|]. apply ub_same_upd_In; [eapply MT_Some_In_keys; exact M2|]. rewrite M2. cbn. apply blocks_of_aidx.
* eapply sameX_trans; [exact SX2 | apply (sameX_upd_meta _ _ am2); exact M2].
* intros SP. unfold sC2. apply (span_ok_upd_set_aidx s2 m2 am2); [exact (SP2 SP) | exact M2 |]. intros _. exact (proj2 (proj2 (proj2 (proj2 grp2))) Ec).
* cbn [am_freed am_aidx am_set_aidx]. intros E0. pose proof grp2 as (Ga & Gb & _).
pose proof (inv_groups HI2 m2 am2 Hu2) as ((_ & _ & _ & _ & _ & _ & _ & _ & Gfra) & _).
apply (f_equal (fun z => Z.testbit z (am_aidx am2 + 1))) in E0.
rewrite Z.land_spec, Z.bits_0, testbit_ones, (Gfra (am_aidx am2 + 1)) in E0 by lia.
replace (0 <=? am_aidx am2 + 1) with true in E0 by (symmetry; apply Z.leb_le; lia).
replace (am_aidx am2 + 1 <=? span_cnt am2 - 1) with true in E0 by (symmetry; apply Z.leb_le; lia). discriminate.
+ rewrite (selC_1 nx Ec Hnx Hne) in E. injection E as <- <-.
exists amnx. split; [split|].
* exact (Inv_rotate_head X None U s2 sc m2 am2 nx HI2 Hsc Hu2 Hs2 Hhd2 (Hz2 _ _ Hu2 Hs2) Hf2 Hnx).
* unfold hd_upd. apply active_hd_set_active_same. rewrite act_len2. lia.
* exact Hun.
* exact Hsn.
* exact Hfn.
* intros g am Hg Hsg. apply (Hz2 g am Hg Hsg).
* intros c Hc0 Hc. unfold hd_upd. rewrite active_hd_set_active_other by lia. apply Hoth2; assumption.
* eapply ub_same_trans; [exact UB2 | apply ub_same_metas; reflexivity].
* eapply sameX_trans; [exact SX2 | apply sameX_set_active].
* intros SP. unfold hd_upd. apply span_ok_set_active. exact (SP2 SP).
* exact (Hpart Ec Hne).
- rewrite (selC_0 Ec) in E. injection E as <- <-. exists am2. split; [exact B2 | exact Ec].
Qed.
End e.
Section h.
Variables (s3 : astate) (m3 : sptr) (am3 : ameta).
Hypothesis B3 : bnd X U s sc s3 m3 am3.
Hypothesis Hmask : Z.land (am_freed am3) (ones (am_aidx am3)) <> 0.
Definition actv : Z := ones (am_aidx am3).
Definition maskD : Z := Z.land (am_freed am3) actv.
Definition firstD : Z := lowbit maskD.
Definition am3a : ameta := am_set_avail maskD (am_set_freed (Z.ldiff (am_freed am3) actv) am3).
Definition s4 : astate := upd_meta m3 (MUsed am3a) s3.
Definition bval : Z := match bounce_idx sc with Some k => znth k (st_bounces s3) | None => 0 end.
Definition s5 : astate :=
match bounce_idx sc with
| Some k => if bval =? 0 then s4 else set_bounces (zset k (bval - 1) (st_bounces s3)) s4
| None => s4
end.
Definition am3f : ameta := am_set_avail (maskD - firstD) am3a.
Definition sF : astate := upd_meta m3 (MUsed am3f) s5.
Lemma grp3 : 0 <= am_aidx am3 <= am_last am3 /\ am_last am3 <= 31 /\ 0 <= am_freed am3 < 2 ^ 32 /\ am_avail am3 = 0 /\
0 < maskD < 2 ^ 32 /\ 0 < firstD <= maskD /\ 0 <= Z.ldiff (am_freed am3) actv < 2 ^ 32 /\ 0 <= bval <= 255.
Proof.
destruct B3 as [HI3 Hhd3 Hu3 Hs3 Hf3 Hz3 _ _ _ SP3].
pose proof (inv_groups HI3 m3 am3 Hu3) as ((Glast & Gaidx & Glen & Gav & Gfr & Gdisj & Gabove & Gavp & Gfra) & _).
assert (Hfr32 : am_freed am3 < 2 ^ 32) by (apply (mask_u32' _ (am_last am3)); [lia|lia|intros i Hi; apply (proj2 (Gabove i Hi))]).
assert (M1 : 0 <= maskD <= am_freed am3) by (unfold maskD; split; [apply Z.land_nonneg; lia | apply land_le_l; lia]).
assert (M2 : maskD <> 0) by exact Hmask.
pose proof (lowbit_le maskD ltac:(lia)) as LB.
assert (D1 : 0 <= Z.ldiff (am_freed am3) actv <= am_freed am3).
{ split; [apply Z.ldiff_nonneg; lia|]. rewrite Z.ldiff_land. apply land_le_l. lia. }
assert (BV : 0 <= bval <= 255).
{ unfold bval. destruct (bounce_idx sc) as [k|]; [|lia]. pose proof (inv_ctx HI3) as (_&_&_&C4&_&_&C7&_).
unfold znth. apply nth_In_range; [exact C7 | lia]. }
unfold firstD. repeat split; try lia. exact (Hz3 _ _ Hu3 Hs3).
Qed.
Lemma TA_D_eval : TA_D m3 s3 = IRet (firstD, sF).
Proof.
destruct B3 as [HI3 Hhd3 Hu3 Hs3 Hf3 Hz3 _ _ _ SP3]. pose proof (usedX_MT _ _ _ _ Hu3) as [M3 NX3]. pose proof grp3 as (_ & _ & _ & Hav3 & Mr & _).
unfold TA_D, activate_group.
erewrite (bind_eval (bind _ _) _ s3).
2:{ erewrite (bind_eval _ _ s3) by (apply getm_eval; exact M3). rewrite Hav3. cbn [Z.eqb massert].
erewrite (bind_eval _ _ s3) by apply ret_eval. erewrite (bind_eval _ _ s3) by apply setm_eval. apply ret_eval. }
fold actv. fold maskD. fold am3a. fold s4. replace (maskD =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb massert].
erewrite (bind_eval _ _ s4) by apply ret_eval.
erewrite (bind_eval _ _ s4) by (apply getm_eval; unfold s4; apply MT_upd_same). change (am_sc am3a) with (am_sc am3). rewrite Hs3.
erewrite (bind_eval _ _ s4 tt s5).
2:{ unfold decay_bounces, s5, bval. destruct (bounce_idx sc) as [k|]; [|apply ret_eval]. rewrite modify_eval. reflexivity. }
erewrite (bind_eval _ _ s5).
2:{ apply getm_eval. unfold s5. assert (M4 : MT s4 m3 = Some (MUsed am3a)) by (unfold s4; apply MT_upd_same).
destruct (bounce_idx sc); [destruct (bval =? 0); [exact M4|]|exact M4]. unfold MT. cbn. exact M4. }
erewrite (bind_eval _ _ s5) by apply setm_eval. reflexivity.
Qed.
Lemma post_D : ta_post X U s sc firstD sF /\ sameX s sF.
Proof.
destruct B3 as [HI3 Hhd3 Hu3 Hs3 Hf3 Hz3 Hoth3 UB3 SX3 SP3] eqn:EB. clear EB. pose proof (usedX_MT _ _ _ _ Hu3) as [M3 NX3].
pose proof (try_avail_finish X U s s3 sc m3 am3 (fun r => ta_post X U s sc (fst r) (snd r)) HI3 Hsc Hhd3 Hu3 Hs3 Hmask Hz3 Hoth3 UB3 ltac:(intros f s' H; exact H)) as P.
change (itok (TA_D m3 s3) (fun r => ta_post X U s sc (fst r) (snd r))) in P. rewrite TA_D_eval in P. cbn [itok fst snd] in P.
split; [exact P|].
eapply sameX_trans; [exact SX3|].
assert (S4 : sameX s3 s4) by (unfold s4; apply (sameX_upd_meta _ _ am3); exact M3).
assert (S5 : sameX s3 s5).
{ unfold s5. destruct (bounce_idx sc) as [k|]; [|exact S4]. destruct (bval =? 0); [exact S4|].
eapply sameX_trans; [exact S4|]. apply sameX_set_bounces. change (st_bounces s4) with (st_bounces s3). apply length_zset. }
eapply sameX_trans; [exact S5|]. unfold sF. apply (sameX_upd_meta _ _ am3a).
unfold s5. assert (M4 : MT s4 m3 = Some (MUsed am3a)) by (unfold s4; apply MT_upd_same).
destruct (bounce_idx sc); [destruct (bval =? 0); [exact M4|]|exact M4]. unfold MT. cbn. exact M4.
Qed.
Lemma final_D : Inv X (Some (m3, ctz32 firstD)) U sF /\ active_hd sF sc = Some m3 /\ usedX X sF m3 am3f /\
MT sF m3 = Some (MUsed am3f) /\ class_size sc <= stride_of am3f /\ 0 <= ctz32 firstD <= am_last am3 /\ ub_same s sF /\ sameX s sF /\
st_bounces sF = match bounce_idx sc with Some k => if bval =? 0 then st_bounces s3 else zset k (bval - 1) (st_bounces s3) | None => st_bounces s3 end /\
st_metas s5 = st_metas s4 /\ firstD = bit (ctz32 firstD) /\ Z.testbit maskD (ctz32 firstD) = true /\ 0 <= ctz32 firstD < 32.
Proof.
destruct post_D as [(Hnz & g & am & HI6 & Hhd6 & Hu6 & Hs6 & Hfit & Hidx & Hoth6 & UB6) SX6].
assert (Hhd6' : active_hd sF sc = Some m3).
{ unfold sF, s5, s4. rewrite active_hd_upd_meta. destruct (bounce_idx sc); [destruct (bval =? 0)|]; cbn; rewrite ?active_hd_upd_meta; exact (b_hd _ _ _ _ _ _ _ B3). }
assert (g = m3) as -> by congruence.
assert (M6 : MT sF m3 = Some (MUsed am3f)) by (unfold sF; apply MT_upd_same).
pose proof (proj1 (usedX_MT _ _ _ _ Hu6)) as M6'. assert (am = am3f) as -> by congruence.
pose proof grp3 as (G1 & G2 & _ & _ & Mr & LB & _).
destruct (lowbit_spec maskD ltac:(lia)) as (k0 & Hk0 & Hlb & Hbit & Hlow).
assert (Ek : ctz32 firstD = k0) by (unfold firstD; rewrite Hlb; apply ctz32_bit; exact Hk0).
assert (Hk32 : k0 < 32).
{ destruct (Z_lt_dec k0 32) as [|Hge]; [assumption|]. exfalso.
pose proof (Z.pow_le_mono_r 2 32 k0 ltac:(lia) ltac:(lia)). unfold bit in Hlb. unfold firstD in LB. rewrite Hlb in LB. lia. }
split; [exact HI6|]. split; [exact Hhd6|]. split; [exact Hu6|]. split; [exact M6|]. split; [exact Hfit|].
split; [change (am_last am3f) with (am_last am3) in Hidx; exact Hidx|]. split; [exact UB6|]. split; [exact SX6|].
split; [unfold sF, s5, s4; destruct (bounce_idx sc); [destruct (bval =? 0)|]; reflexivity|].
split; [unfold s5; destruct (bounce_idx sc); [destruct (bval =? 0)|]; reflexivity|].
rewrite Ek. unfold firstD. split; [exact Hlb|]. split; [exact Hbit | lia].
Qed.
Lemma span_F : span_ok s -> span_ok sF.
Proof.
intros SP. pose proof (b_span _ _ _ _ _ _ _ B3 SP) as SP3. pose proof (proj1 (usedX_MT _ _ _ _ (b_used _ _ _ _ _ _ _ B3))) as M3.
assert (SP4 : span_ok s4) by (unfold s4, am3a; apply (span_ok_upd_set_avail_freed s3 m3 am3); [exact SP3 | exact M3]).
assert (M4 : MT s4 m3 = Some (MUsed am3a)) by (unfold s4; apply MT_upd_same).
assert (SP5 : span_ok s5 /\ MT s5 m3 = Some (MUsed am3a)).
{ unfold s5. destruct (bounce_idx sc) as [k|]; [destruct (bval =? 0); [split; [exact SP4 | exact M4]|] | split; [exact SP4 | exact M4]].
split; [apply span_ok_set_bounces; exact SP4 | unfold MT; cbn; exact M4]. }
destruct SP5 as [SP5 M5]. unfold sF, am3f. apply (span_ok_upd_set_avail s5 m3 am3a); [exact SP5 | exact M5].
Qed.
End h.
End b.
End a.
