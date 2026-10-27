(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL07.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma forallb_In : forall {A} (f : A -> bool) (l : list A) x,
forallb f l = true -> In x l -> f x = true.
Proof. intros A f l x H Hin. exact (proj1 (forallb_forall f l) H x Hin). Qed.
Lemma existsb_In : forall {A} (f : A -> bool) (l : list A),
existsb f l = true -> exists x, In x l /\ f x = true.
Proof.
intros A f l H. induction l as [|a l IH]; cbn in H; [discriminate|].
apply orb_prop in H as [H|H].
- exists a. split; [left; reflexivity | exact H].
- destruct (IH H) as (x & Hx & Hf). exists x. split; [right; exact Hx | exact Hf].
Qed.
Definition ivl := list (Z * Z).
Definition in_ivl (l : ivl) (a : Z) : bool :=
existsb (fun p => (fst p <=? a) && (a <? snd p)) l.
Definition sub_ivl (l : ivl) (lo hi : Z) : bool :=
(hi <=? lo) || existsb (fun p => (fst p <=? lo) && (hi <=? snd p)) l.
Lemma sub_ivl_sound : forall l lo hi a, sub_ivl l lo hi = true -> lo <= a < hi -> in_ivl l a = true.
Proof.
intros l lo hi a H Ha. unfold sub_ivl in H. apply orb_prop in H as [H|H].
- apply Z.leb_le in H. lia.
- apply existsb_In in H as (p & Hp & Hf). apply andb_prop in Hf as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
unfold in_ivl. apply existsb_exists. exists p. split; [exact Hp|].
apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Section h.
Variable segs : list Segment.
Fixpoint img_lit (a : Z) (z : Z) (n : nat) : bool :=
match n with
| O => true
| S n' => match img_byte segs a with
| Some b => (bv_unsigned b =? z mod 256) && img_lit (a + 1) (Z.shiftr z 8) n'
| None => false
end
end.
Lemma img_lit_sound : forall n a z i,
img_lit a z n = true -> 0 <= i < Z.of_nat n ->
img_byte segs (a + i) = Some (Z_to_bv 8 (Z.shiftr z (8 * i))).
Proof.
induction n as [|n IH]; intros a z i H Hi; [lia|]. cbn [img_lit] in H.
destruct (img_byte segs a) as [b|] eqn:Hb; [|discriminate].
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1.
destruct (Z.eq_dec i 0) as [->|Hne].
- rewrite Z.add_0_r, Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, H1.
rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
- replace (a + i) with (a + 1 + (i - 1)) by lia.
rewrite (IH (a + 1) (Z.shiftr z 8) (i - 1) H2) by lia. f_equal. f_equal.
rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Definition subchunk_of (abs : bool) (c' c : chunk) : bool :=
(c_off c <=? c_off c') && (c_off c' + c_len c' <=? c_off c + c_len c) && (0 <=? c_len c') &&
match c_val c with
| CImg _ => match c_val c' with
| CImg _ => true
| CVal w' v' => match v' with
| SLit z => abs && img_lit (c_off c') (zcanon z) (N.to_nat w')
| _ => false
end
| _ => false
end
| CZero _ => match c_val c' with CZero _ => true | _ => false end
| CData d s _ => match c_val c' with
| CData d' s' _ => Nat.eqb d' d && (s' =? s + (c_off c' - c_off c)) && (0 <=? s)
| _ => false
end
| CVal w v => match c_val c' with
| CVal w' v' => (c_off c' =? c_off c) && N.eqb w' w && sv_eqb v' v
| _ => false
end
end.
Lemma byte_of_word_lit : forall z i,
byte_of_word (Z_to_bv 64 z) i = Z_to_bv 8 (Z.shiftr (zcanon z) (8 * i)).
Proof.
intros z i. unfold byte_of_word. rewrite Z_to_bv_unsigned.
unfold bv_wrap, zcanon, M64. change (bv_modulus 64) with (2 ^ 64). reflexivity.
Qed.
Lemma subchunk_of_sound : forall E m base abs c' c,
(abs = true -> base = 0) ->
chunk_ok segs E m base c -> subchunk_of abs c' c = true -> chunk_ok segs E m base c'.
Proof.
intros E m base abs c' c Habs Hc H i Hi.
unfold subchunk_of in H. apply andb_prop in H as [H Hv]. apply andb_prop in H as [H H3].
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
set (j := c_off c' - c_off c + i).
assert (Hj : 0 <= j < c_len c) by (subst j; unfold c_len in *; lia).
assert (Haddr : base + c_off c' + i = base + c_off c + j) by (subst j; lia).
destruct (Hc j Hj) as (b & Hb1 & Hb2).
exists b. rewrite Haddr. split; [| exact Hb2]. rewrite <- Hb1. clear Hb2 Hc.
unfold c_len in *.
destruct (c_val c) as [w v | l | l | d s l] eqn:Ec; destruct (c_val c') as [w' v' | l' | l' | d' s' l'] eqn:Ec';
try discriminate; cbn [cbyte].
-   apply andb_prop in Hv as [Hv Hsv]. apply andb_prop in Hv as [Ho Hw].
apply Z.eqb_eq in Ho. apply N.eqb_eq in Hw. apply sv_eqb_eq in Hsv. subst w' v'.
f_equal. f_equal. subst j. lia.
-   reflexivity.
-   destruct v' as [z| | | | | | | | | |]; try discriminate.
apply andb_prop in Hv as [Ha Hl]. rewrite (Habs Ha). cbn [sv_denot]. rewrite Z.add_0_l.
rewrite byte_of_word_lit.
replace (c_off c + j) with (c_off c' + i) by (subst j; lia).
rewrite (img_lit_sound (N.to_nat w') (c_off c') (zcanon z) i Hl) by (rewrite N_nat_Z; cbn [cv_len] in Hi; lia).
reflexivity.
-   f_equal. lia.
-   apply andb_prop in Hv as [Hv Hs0]. apply andb_prop in Hv as [Hd Hs].
apply Nat.eqb_eq in Hd. apply Z.eqb_eq in Hs. apply Z.leb_le in Hs0. subst d' s'.
f_equal. f_equal. subst j. lia.
Qed.
Definition derived_ok (r r' : region) : bool :=
obase_eqb (r_base r') (r_base r)
&& (r_lo r <=? r_lo r') && (r_hi r' <=? r_hi r) && (r_lo r' <=? r_hi r')
&& ((r_whi r' <=? r_wlo r') || ((r_wlo r <=? r_wlo r') && (r_whi r' <=? r_whi r) && (r_lo r' <=? r_wlo r') && (r_whi r' <=? r_hi r')))
&& forallb (fun c' => chunk_inside r' c' &&
existsb (subchunk_of (match r_base r with None => true | Some _ => false end) c') (r_chunks r))
(r_chunks r').
Lemma derived_ok_sound : forall E m r r',
derived_ok r r' = true -> region_ok segs E m r ->
region_wf r' = true /\ region_ok segs E m r' /\ r_base r' = r_base r /\ r_lo r <= r_lo r' /\ r_hi r' <= r_hi r.
Proof.
intros E m r r' H (H0 & H1 & Hw & Hcs).
unfold derived_ok in H.
apply andb_prop in H as [H Hch]. apply andb_prop in H as [H Hwr]. apply andb_prop in H as [H Hle].
apply andb_prop in H as [H Hhi]. apply andb_prop in H as [Hb Hlo].
apply obase_eqb_eq in Hb. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. apply Z.leb_le in Hle.
assert (Hwr' : r_whi r' <= r_wlo r' \/ (r_wlo r <= r_wlo r' /\ r_whi r' <= r_whi r /\ r_lo r' <= r_wlo r' /\ r_whi r' <= r_hi r')).
{ apply orb_prop in Hwr as [Hwr|Hwr]; [left; apply Z.leb_le in Hwr; exact Hwr | right].
apply andb_prop in Hwr as [Hwr H4]. apply andb_prop in Hwr as [Hwr H3]. apply andb_prop in Hwr as [H5 H6].
apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.leb_le in H5. apply Z.leb_le in H6. lia. }
split; [|split; [|split; [exact Hb | lia]]].
- unfold region_wf. apply andb_true_intro. split; [apply andb_true_intro; split|].
+ apply Z.leb_le. exact Hle.
+ destruct Hwr' as [Hwr'|Hwr']; apply orb_true_intro; [left; apply Z.leb_le; lia | right].
apply andb_true_intro; split; apply Z.leb_le; lia.
+ apply forallb_forall. intros c Hc. apply (forallb_In _ _ c Hch) in Hc. apply andb_prop in Hc as [Hc _]. exact Hc.
- unfold region_ok. rewrite Hb. split; [lia|]. split; [lia|]. split.
+ intros o Ho. destruct Hwr' as [Hwr'|Hwr']; [lia|]. apply Hw. lia.
+ apply Forall_forall. intros c' Hc'. pose proof (forallb_In _ _ c' Hch Hc') as Hc. cbn beta in Hc.
apply andb_prop in Hc as [_ Hex]. apply existsb_In in Hex as (c & Hcin & Hsub).
eapply subchunk_of_sound; [| exact (proj1 (Forall_forall _ _) Hcs c Hcin) | exact Hsub].
intros Habs. destruct (r_base r); [discriminate | reflexivity].
Qed.
Fixpoint parents_ok (rs : smem) (l : list (nat * region)) : bool :=
match l with
| [] => true
| (i, r') :: l' => match nth_error rs i with
| Some r => derived_ok r r'
| None => false
end && parents_ok rs l'
end.
Definition dpair_ok (x y : nat * region) : bool :=
if Nat.eqb (fst x) (fst y)
then (r_hi (snd x) <=? r_lo (snd y)) || (r_hi (snd y) <=? r_lo (snd x))
else true.
Fixpoint dpairwise_ok (l : list (nat * region)) : bool :=
match l with
| [] => true
| x :: l' => forallb (dpair_ok x) l' && dpairwise_ok l'
end.
Definition relayout_ok (rs : smem) (l : list (nat * region)) : bool :=
parents_ok rs l && dpairwise_ok l.
Lemma all_disjoint_In : forall E r rs x, all_disjoint E r rs -> In x rs -> extent_disjoint E r x.
Proof.
intros E r rs x. induction rs as [|y rs IH]; cbn; intros H Hin; [destruct Hin|].
destruct H as [Hd Ha]. destruct Hin as [<-|Hin]; [exact Hd | apply IH; assumption].
Qed.
Lemma pairwise_disjoint_nth : forall E rs i j a b,
pairwise_disjoint E rs -> nth_error rs i = Some a -> nth_error rs j = Some b -> i <> j ->
extent_disjoint E a b.
Proof.
intros E rs. induction rs as [|r rs IH]; intros i j a b Hpd Ha Hb Hij.
- destruct i; discriminate.
- cbn in Hpd. destruct Hpd as [Hall Hpd].
destruct i as [|i], j as [|j]; cbn in Ha, Hb.
+ lia.
+ injection Ha as <-. apply (all_disjoint_In E r rs b Hall). eapply nth_error_In; eauto.
+ injection Hb as <-. pose proof (all_disjoint_In E r rs a Hall ltac:(eapply nth_error_In; eauto)) as Hd.
unfold extent_disjoint in *. lia.
+ eapply IH; eauto.
Qed.
Lemma relayout_regions_ok : forall E m rs l,
Forall (region_ok segs E m) rs -> parents_ok rs l = true ->
regions_wf (map snd l) = true /\ Forall (region_ok segs E m) (map snd l) /\
Forall (fun x => exists r, nth_error rs (fst x) = Some r /\ r_base (snd x) = r_base r /\
r_lo r <= r_lo (snd x) /\ r_hi (snd x) <= r_hi r) l.
Proof.
intros E m rs l Hok. induction l as [|[i r'] l IH]; cbn; intros H.
- repeat split; constructor.
- apply andb_prop in H as [Hd Hl]. destruct (nth_error rs i) as [r|] eqn:Hi; [|discriminate].
assert (Hr : region_ok segs E m r) by (apply (proj1 (Forall_forall _ _) Hok); eapply nth_error_In; eauto).
destruct (derived_ok_sound E m r r' Hd Hr) as (W & O & B & LO & HI).
destruct (IH Hl) as (W' & O' & P'). rewrite W, W'. split; [reflexivity|].
split; [constructor; assumption|]. constructor; [| exact P']. cbn. exists r. auto.
Qed.
Lemma relayout_disjoint : forall E rs l,
pairwise_disjoint E rs ->
Forall (fun x => exists r, nth_error rs (fst x) = Some r /\ r_base (snd x) = r_base r /\
r_lo r <= r_lo (snd x) /\ r_hi (snd x) <= r_hi r) l ->
dpairwise_ok l = true -> pairwise_disjoint E (map snd l).
Proof.
intros E rs l Hpd. induction l as [|[i x] l IH]; cbn; intros HP H; [exact I|].
apply andb_prop in H as [Hx Hl]. inversion HP as [|y l0 Hy HP']; subst. cbn in Hy.
destruct Hy as (rx & Hix & Bx & LOx & HIx).
split; [| apply IH; assumption].
clear IH Hl HP. induction l as [|[j y] l IH]; cbn; [exact I|].
cbn in Hx. apply andb_prop in Hx as [Hxy Hx]. inversion HP' as [|z l1 Hz HP'']; subst. cbn in Hz.
destruct Hz as (ry & Hjy & By & LOy & HIy).
split; [| apply IH; assumption].
unfold dpair_ok in Hxy. cbn [fst snd] in Hxy.
unfold extent_disjoint. rewrite Bx, By.
destruct (Nat.eqb_spec i j) as [->|Hne].
- rewrite Hix in Hjy. injection Hjy as <-.
apply orb_prop in Hxy as [Hxy|Hxy]; apply Z.leb_le in Hxy; lia.
- pose proof (pairwise_disjoint_nth E rs i j rx ry Hpd Hix Hjy Hne) as Hd. unfold extent_disjoint in Hd. lia.
Qed.
Theorem mem_ok_relayout : forall E m rs l,
mem_ok segs E m rs -> relayout_ok rs l = true -> mem_ok segs E m (map snd l).
Proof.
intros E m rs l (Hwf & Hok & Hpd) H. unfold relayout_ok in H. apply andb_prop in H as [Hp Hd].
destruct (relayout_regions_ok E m rs l Hok Hp) as (W & O & P).
split; [exact W|]. split; [exact O|]. eapply relayout_disjoint; eauto.
Qed.
Lemma st_ok_relayout : forall E ss ms l,
st_ok segs E ss ms -> relayout_ok (ss_mem ss) l = true ->
st_ok segs E (mkSS (ss_pc ss) (ss_regs ss) (map snd l) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms l (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) H.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
eapply mem_ok_relayout; eauto.
Qed.
Definition clip_chunk (lo hi : Z) (c : chunk) : list chunk :=
let a := Z.max lo (c_off c) in
let b := Z.min hi (c_off c + c_len c) in
if b <=? a then []
else match c_val c with
| CVal w v => if (lo <=? c_off c) && (c_off c + c_len c <=? hi) then [c] else []
| CZero _ => [mkChunk a (CZero (b - a))]
| CImg _ => [mkChunk a (CImg (b - a))]
| CData d s _ => [mkChunk a (CData d (s + (a - c_off c)) (b - a))]
end.
Definition clip_chunks (lo hi : Z) (cs : list chunk) : list chunk := flat_map (clip_chunk lo hi) cs.
Definition cut_chunk (lo hi : Z) (c : chunk) : list chunk :=
if (c_off c + c_len c <=? lo) || (hi <=? c_off c) then [c]
else clip_chunk (c_off c) lo c ++ clip_chunk hi (c_off c + c_len c) c.
Definition cut_chunks (lo hi : Z) (cs : list chunk) : list chunk := flat_map (cut_chunk lo hi) cs.
Fixpoint cut_chunks_ivl (F : ivl) (cs : list chunk) : list chunk :=
match F with
| [] => cs
| (lo, hi) :: F' => cut_chunks_ivl F' (cut_chunks lo hi cs)
end.
Definition keep_chunks_ivl (K : ivl) (cs : list chunk) : list chunk :=
flat_map (fun p => clip_chunks (fst p) (snd p) cs) K.
Definition carve (r : region) (lo hi wlo whi : Z) : region :=
mkRegion (r_base r) lo hi wlo whi (clip_chunks lo hi (r_chunks r)).
Definition with_chunks (r : region) (cs : list chunk) : region :=
mkRegion (r_base r) (r_lo r) (r_hi r) (r_wlo r) (r_whi r) cs.
Definition with_rw (r : region) (wlo whi : Z) : region :=
mkRegion (r_base r) (r_lo r) (r_hi r) wlo whi (r_chunks r).
Definition same_layout (rs : smem) : list (nat * region) :=
combine (seq 0 (length rs)) rs.
Fixpoint fact_lo (fs : list (nat * afact)) (n : nat) : option Z :=
match fs with
| [] => None
| (k, f) :: fs' => if Nat.eqb k n then Some (af_lo f) else fact_lo fs' n
end.
Lemma fact_lo_sound : forall E fs n lo,
atoms_ok E fs -> fact_lo fs n = Some lo -> lo <= bv_unsigned (ew E n).
Proof.
intros E fs n lo. induction fs as [|[k f] fs IH]; cbn; intros Hok H; [discriminate|].
destruct Hok as [Hf Hok]. destruct (Nat.eqb_spec k n) as [->|Hne].
- injection H as <-. destruct Hf as (Hlo & _). exact (proj1 Hlo).
- apply IH; assumption.
Qed.
Fixpoint fact_of (fs : list (nat * afact)) (n : nat) : option afact :=
match fs with
| [] => None
| (k, f) :: fs' => if Nat.eqb k n then Some f else fact_of fs' n
end.
Lemma fact_of_sound : forall E fs n f, atoms_ok E fs -> fact_of fs n = Some f -> afact_ok E n f.
Proof.
intros E fs n f. induction fs as [|[k g] fs IH]; cbn; intros Hok H; [discriminate|].
destruct Hok as [Hg Hok]. destruct (Nat.eqb_spec k n) as [->|Hne]; [injection H as <-; exact Hg | apply IH; assumption].
Qed.
Definition anch_lo (G : facts) (n : nat) : option Z :=
match fact_lo (f_atoms G) n with
| Some lo => if CEIL_MIN <=? lo then Some (lo - CEIL_MIN) else None
| None => None
end.
Definition anchored_atoms (G : facts) : list (nat * Z) :=
map (fun kf : nat * afact => (fst kf, af_lo (snd kf) - CEIL_MIN))
(List.filter (fun kf : nat * afact => CEIL_MIN <=? af_lo (snd kf)) (f_atoms G)).
Definition stack_anchored (E : env) (G : facts) : Prop :=
Forall (fun a : nat * Z => alloc_ceiling + snd a <= bv_unsigned (ew E (fst a))) (anchored_atoms G).
Lemma fact_lo_In : forall fs n lo, fact_lo fs n = Some lo -> exists f, In (n, f) fs /\ af_lo f = lo.
Proof.
intros fs n lo. induction fs as [|[k f] fs IH]; cbn; intros H; [discriminate|].
destruct (Nat.eqb_spec k n) as [->|Hne].
- injection H as <-. exists f. split; [left; reflexivity | reflexivity].
- destruct (IH H) as (g & Hg & Hlo). exists g. split; [right; exact Hg | exact Hlo].
Qed.
Lemma fact_lo_of : forall fs n f, fact_of fs n = Some f -> fact_lo fs n = Some (af_lo f).
Proof.
intros fs n f. induction fs as [|[k g] fs IH]; cbn; intros H; [discriminate|].
destruct (Nat.eqb k n); [injection H as ->; reflexivity | apply IH; exact H].
Qed.
Lemma stack_anchored_sound : forall E G n K,
stack_anchored E G -> anch_lo G n = Some K -> alloc_ceiling + K <= bv_unsigned (ew E n).
Proof.
intros E G n K HSA HK. unfold anch_lo in HK.
destruct (fact_lo (f_atoms G) n) as [lo|] eqn:Hlo; [|discriminate].
destruct (Z.leb_spec CEIL_MIN lo) as [Hle|Hgt]; [|discriminate]. injection HK as <-.
destruct (fact_lo_In _ _ _ Hlo) as (f & Hin & Hf).
unfold stack_anchored in HSA. rewrite Forall_forall in HSA.
specialize (HSA (n, af_lo f - CEIL_MIN)). cbn [fst snd] in HSA. rewrite Hf in HSA. apply HSA.
unfold anchored_atoms. apply in_map_iff. exists (n, f). split; [cbn [fst snd]; rewrite Hf; reflexivity|].
apply filter_In. split; [exact Hin|]. cbn [snd]. rewrite Hf. apply Z.leb_le. exact Hle.
Qed.
Lemma stack_anchored_ext : forall E E' G G',
stack_anchored E G -> anchored_atoms G' = anchored_atoms G ->
(forall a, In a (anchored_atoms G) -> ew E' (fst a) = ew E (fst a)) ->
stack_anchored E' G'.
Proof.
intros E E' G G' HSA EG HE. unfold stack_anchored in *. rewrite EG. rewrite Forall_forall in HSA |- *.
intros a Ha. rewrite (HE a Ha). exact (HSA a Ha).
Qed.
Lemma stack_anchored_agree : forall k E E' G,
env_agree k E E' -> facts_atoms_lt k G = true -> stack_anchored E G -> stack_anchored E' G.
Proof.
intros k E E' G [HA _] Hlt HSA. unfold stack_anchored in *. rewrite Forall_forall in HSA |- *.
intros [n K] Hin. cbn [fst snd]. specialize (HSA (n, K) Hin). cbn [fst snd] in HSA.
unfold anchored_atoms in Hin. apply in_map_iff in Hin as ([n' f] & Heq & Hin). cbn [fst snd] in Heq.
injection Heq as <- <-. apply filter_In in Hin as [Hin _].
unfold facts_atoms_lt in Hlt. apply andb_prop in Hlt as [Hlt _]. apply andb_prop in Hlt as [Hlt _].
pose proof (proj1 (forallb_forall _ _) Hlt (n', f) Hin) as Hn. cbn [fst] in Hn. apply Nat.ltb_lt in Hn.
rewrite (HA n' Hn). exact HSA.
Qed.
Lemma stack_anchored_agree_ss : forall k E E' ss,
env_agree k E E' -> ss_atoms_lt k ss = true -> stack_anchored E (ss_facts ss) -> stack_anchored E' (ss_facts ss).
Proof.
intros k E E' ss HA Hlt HSA. unfold ss_atoms_lt in Hlt.
apply andb_prop in Hlt as [Hlt _]. apply andb_prop in Hlt as [Hlt Hf].
exact (stack_anchored_agree k E E' (ss_facts ss) HA Hf HSA).
Qed.
Fixpoint blk_size (blks : list (nat * Z)) (n : nat) : option Z :=
match blks with
| [] => None
| (k, sz) :: bl => if Nat.eqb k n then Some sz else blk_size bl n
end.
Lemma blk_size_In : forall blks n sz, blk_size blks n = Some sz -> In (n, sz) blks.
Proof.
induction blks as [|[k s] bl IH]; cbn; intros n sz H; [discriminate|].
destruct (Nat.eqb_spec k n) as [->|Hne]; [injection H as ->; left; reflexivity | right; apply IH; exact H].
Qed.
Definition chunk_out (lo hi : Z) (c : chunk) : bool := (c_off c + c_len c <=? lo) || (hi <=? c_off c).
Section q.
Variable G : facts.
Variable sp_off stk : Z.
Variable keep : ivl.
Variable wnew : ivl.
Variable blks : list (nat * Z).
Definition region_call_ok (r : region) : bool :=
match r_base r with
| None =>
forallb (fun c => sub_ivl keep (c_off c) (c_off c + c_len c)) (r_chunks r)
&& (sub_ivl keep (r_wlo r) (r_whi r) || sub_ivl wnew (r_wlo r) (r_whi r))
| Some n =>
match blk_size blks n with
| Some sz => (0 <=? r_lo r) && (r_hi r <=? sz)
&& ((r_whi r <=? r_wlo r) || ((0 <=? r_wlo r) && (r_whi r <=? sz)))
| None =>
match anch_lo G n with
| Some K => (0 <=? K + r_lo r)
&& (if Nat.eqb n 0 then forallb (chunk_out (sp_off - stk) sp_off) (r_chunks r) else true)
| None => false
end
end
end.
Definition scratch_home (r : region) : bool :=
obase_eqb (r_base r) (Some 0%nat) && (r_lo r <=? sp_off - stk) && (sp_off <=? r_hi r)
&& match blk_size blks 0%nat with None => true | Some _ => false end.
Definition call_frame_check (rs : smem) : bool :=
existsb scratch_home rs && forallb region_call_ok rs && (0 <=? stk).
Variable E : env.
Variables m m' : word -> option byte.
Let spv := bv_unsigned (ew E 0).
Hypothesis Hhi : forall a, alloc_ceiling <= a -> a < 2 ^ 64 -> ~ (spv + sp_off - stk <= a < spv + sp_off) ->
mbyte segs m' a = mbyte segs m a /\ (writable_at segs m a -> writable_at segs m' a).
Hypothesis Hscr : forall a, spv + sp_off - stk <= a < spv + sp_off -> writable_at segs m' a.
Hypothesis Himg : forall a, in_ivl keep a = true ->
mbyte segs m' a = mbyte segs m a /\ (writable_at segs m a -> writable_at segs m' a).
Hypothesis Hwnew : forall a, in_ivl wnew a = true -> writable_at segs m' a.
Hypothesis Hblk : forall n sz i, In (n, sz) blks -> 0 <= i < sz ->
mbyte segs m' (bv_unsigned (ew E n) + i) = mbyte segs m (bv_unsigned (ew E n) + i) /\
writable_at segs m' (bv_unsigned (ew E n) + i).
Hypothesis HG : facts_ok E G.
Hypothesis HSA : stack_anchored E G.
Lemma chunk_ok_kept : forall base c,
chunk_ok segs E m base c ->
(forall i, 0 <= i < c_len c -> mbyte segs m' (base + c_off c + i) = mbyte segs m (base + c_off c + i)) ->
chunk_ok segs E m' base c.
Proof.
intros base c Hc Hs i Hi. destruct (Hc i Hi) as (b & H1 & H2). exists b. split; [exact H1|].
rewrite Hs by exact Hi. exact H2.
Qed.
Theorem mem_ok_call_frame : forall rs,
mem_ok segs E m rs -> call_frame_check rs = true -> mem_ok segs E m' rs.
Proof using HG HSA Hhi Hscr Himg Hwnew Hblk.
intros rs (Hwf & Hok & Hpd) Hck.
unfold call_frame_check in Hck. apply andb_prop in Hck as [Hck Hstk]. apply andb_prop in Hck as [Hhome Hall].
apply Z.leb_le in Hstk.
apply existsb_In in Hhome as (r0 & Hr0in & Hr0).
unfold scratch_home in Hr0. apply andb_prop in Hr0 as [Hr0 Hnb0]. apply andb_prop in Hr0 as [Hr0 H0hi].
apply andb_prop in Hr0 as [H0b H0lo].
apply obase_eqb_eq in H0b. apply Z.leb_le in H0lo. apply Z.leb_le in H0hi.
split; [exact Hwf|]. split; [|exact Hpd].
destruct (in_split r0 rs Hr0in) as (l1 & l2 & Hsplit).
assert (Hdis : Forall (extent_disjoint E r0) (l1 ++ l2)).
{ rewrite Hsplit in Hpd. exact (pairwise_disjoint_split E l1 r0 l2 Hpd). }
apply Forall_forall. intros r Hin.
pose proof (proj1 (Forall_forall _ _) Hok r Hin) as Hr. destruct Hr as (Hb0 & Hb1 & Hw & Hcs).
pose proof (forallb_In _ _ r Hall Hin) as Hrc. unfold region_call_ok in Hrc.
pose proof (regions_wf_In rs r Hwf Hin) as Hrwf. apply region_wf_facts in Hrwf as (Hlohi & Hwr & Hcin).
split; [exact Hb0|]. split; [exact Hb1|].
destruct (r_base r) as [n|] eqn:Hbase.
- destruct (blk_size blks n) as [sz|] eqn:Hbs.
+
apply blk_size_In in Hbs.
apply andb_prop in Hrc as [Hrc Hwr2]. apply andb_prop in Hrc as [Hlo0 Hhisz].
apply Z.leb_le in Hlo0. apply Z.leb_le in Hhisz.
cbn [base_val] in *. split.
* intros o Ho. apply (proj2 (Hblk n sz o Hbs ltac:(apply orb_prop in Hwr2 as [Hwr2|Hwr2];
[apply Z.leb_le in Hwr2; lia | apply andb_prop in Hwr2 as [X Y]; apply Z.leb_le in X; apply Z.leb_le in Y; lia]))).
* apply Forall_forall. intros c Hc. apply chunk_ok_kept; [exact (proj1 (Forall_forall _ _) Hcs c Hc)|].
pose proof (chunk_inside_facts r c (forallb_In _ _ c Hcin Hc)) as (C1 & C2 & C3).
intros i Hi. rewrite <- Z.add_assoc. apply (proj1 (Hblk n sz (c_off c + i) Hbs ltac:(lia))).
+
destruct (anch_lo G n) as [K|] eqn:HK; [|discriminate].
apply andb_prop in Hrc as [Hac Hch]. apply Z.leb_le in Hac.
pose proof (stack_anchored_sound E G n K HSA HK) as Hnlo.
cbn [base_val] in *.
assert (Hout : forall a, bv_unsigned (ew E n) + r_lo r <= a < bv_unsigned (ew E n) + r_hi r ->
(Nat.eqb n 0 = false) -> ~ (spv + sp_off - stk <= a < spv + sp_off)).
{ intros a Ha Hn0 Hin'.
assert (Hne : r <> r0) by (intros ->; rewrite Hbase in H0b; injection H0b as ->; rewrite Nat.eqb_refl in Hn0; discriminate).
assert (Hrin : In r (l1 ++ l2)).
{ rewrite Hsplit in Hin. apply in_app_iff in Hin. apply in_app_iff.
destruct Hin as [H|[H|H]]; [left; exact H | exfalso; exact (Hne (eq_sym H)) | right; exact H]. }
pose proof (proj1 (Forall_forall _ _) Hdis r Hrin) as Hd. unfold extent_disjoint in Hd.
rewrite H0b, Hbase in Hd. cbn [base_val] in Hd. subst spv. lia. }
split.
* intros o Ho.
assert (Hac' : alloc_ceiling <= bv_unsigned (ew E n) + o) by lia.
assert (H64 : bv_unsigned (ew E n) + o < 2 ^ 64) by lia.
destruct (Nat.eqb_spec n 0) as [->|Hn0].
-- destruct (Z_lt_dec (bv_unsigned (ew E 0%nat) + o) (spv + sp_off - stk)) as [L|L].
++ apply (proj2 (Hhi (bv_unsigned (ew E 0%nat) + o) Hac' H64 ltac:(subst spv; lia))). apply Hw. exact Ho.
++ destruct (Z_lt_dec (bv_unsigned (ew E 0%nat) + o) (spv + sp_off)) as [L2|L2].
** apply Hscr. subst spv. lia.
** apply (proj2 (Hhi (bv_unsigned (ew E 0%nat) + o) Hac' H64 ltac:(subst spv; lia))). apply Hw. exact Ho.
-- apply (proj2 (Hhi (bv_unsigned (ew E n) + o) Hac' H64 ltac:(apply Hout; [lia | reflexivity]))). apply Hw. exact Ho.
* apply Forall_forall. intros c Hc. apply chunk_ok_kept; [exact (proj1 (Forall_forall _ _) Hcs c Hc)|].
pose proof (chunk_inside_facts r c (forallb_In _ _ c Hcin Hc)) as (C1 & C2 & C3).
intros i Hi.
assert (Hac' : alloc_ceiling <= bv_unsigned (ew E n) + c_off c + i) by lia.
assert (H64 : bv_unsigned (ew E n) + c_off c + i < 2 ^ 64) by lia.
assert (Hns : ~ (spv + sp_off - stk <= bv_unsigned (ew E n) + c_off c + i < spv + sp_off)).
{ destruct (Nat.eqb_spec n 0) as [->|Hn0].
-- pose proof (forallb_In _ _ c Hch Hc) as Hco. unfold chunk_out in Hco.
apply orb_prop in Hco as [Hco|Hco]; apply Z.leb_le in Hco; subst spv; lia.
-- apply Hout; [lia | reflexivity]. }
exact (proj1 (Hhi (bv_unsigned (ew E n) + c_off c + i) Hac' H64 Hns)).
-
apply andb_prop in Hrc as [Hch Hwk]. cbn [base_val] in *.
split.
+ intros o Ho. apply orb_prop in Hwk as [Hwk|Hwk].
* apply (proj2 (Himg o ltac:(eapply sub_ivl_sound; [exact Hwk | lia]))). apply Hw. exact Ho.
* apply Hwnew. eapply sub_ivl_sound; [exact Hwk | lia].
+ apply Forall_forall. intros c Hc. apply chunk_ok_kept; [exact (proj1 (Forall_forall _ _) Hcs c Hc)|].
pose proof (chunk_inside_facts r c (forallb_In _ _ c Hcin Hc)) as (C1 & C2 & C3).
intros i Hi. rewrite !Z.add_0_l.
assert (Hii : c_off c <= c_off c + i < c_off c + c_len c) by lia.
exact (proj1 (Himg (c_off c + i) (sub_ivl_sound _ _ _ _ (forallb_In _ _ c Hch Hc) Hii))).
Qed.
End q.
End h.
End e.
