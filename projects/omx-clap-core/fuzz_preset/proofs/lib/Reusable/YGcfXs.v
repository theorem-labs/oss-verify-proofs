(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by a Theorem Labs lane (DeallocNmaxA), 2026-10-30: cfx_fr_free_cf's script covers free_cf's recycle side (cfx_fr_recycle_chunk); statements unchanged. *)
(* Modified by a Theorem Labs lane (DeallocNmaxA), 2026-10-30: cfx_fr_free_cf's script covers free_cf's recycle side (cfx_fr_recycle_chunk); statements unchanged. A change request to a Theorem Labs lane. *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YGcfXs.v at commit fec7cbb6287c (the cf layer of record, field rounds 1 + 2), module paths changed; the preset-side hunks kept on top are listed in the round6f report. *)
(* Theorem Labs, 2026-10: facts about xs_placed_cf (YG0ncf.v), the placement of the error-message-buffer extent
   xs_cf ly S = [(ly_sec ly i, errb_cap_cf S)] like a live secondary. ARcf does not pin that extent (every ARcf
   fact about ly_sec ranges over sec_extents, built from st_chunks), so the call leaves carry xs_placed_cf at the
   post (malloc_leaf_cf, YG0dcf.v; realloc_leaf_cf, YGcfRealloc.v) and the walk carries it between calls:
   - xs_placed_cf_init: it holds at the initial state (no errbuf);
   - xs_placed_cf_layout: a layout step keeps it (ly_sec is pinned below length st_secs);
   - xs_placed_cf_mono / _keep / _sec_grow: a state step keeps it when the errbuf entry is unchanged and every
     new sec extent is disjoint from the errbuf (for a new secondary: xs_fresh_of_grant, from the LPS grant's
     region_free and the walk fact xs_mapped_cf that the errbuf extent is one of the model's maps);
   - xs_placed_cf_remap: the class-full remap (errb_map_cf) gives it from the placement of the fresh slot
     (grant_aligned_cf and grant_apart_cf give its alignment and its disjointness from every mapped extent);
   - malloc_leaf_cf_xs_keep: the leaf's conjunct; free_leaf_cf_xs_keep: from the free path's state frame
     free_frame_cf (free maps neither a secondary nor the errbuf), with the layout step;
   - xs_cf_not_extra_cf: the extent misses ly_extra.
   No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK13 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0s YGcfRealloc.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section X. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* ---------------------------------------------------------------------------- *)
(* 1. The extent misses ly_extra.                                                   *)
Lemma cfx_pick : forall ly S a, xs_placed_cf ly S -> Exists (in_zr a) (xs_cf ly S) ->
exists e, in_zr a e /\ in_app (fst e) (snd e) /\ fst e + snd e <= alloc_ceiling /\
(forall z, In z (sec_extents ly S ++ static_extents ly ++ ly_extra ly) -> zdisjoint e z).
Proof.
intros ly S a HP Hx. apply Exists_exists in Hx as (e & He & Ha).
pose proof (proj1 (Forall_forall _ _) HP e He) as (_ & H1 & H2 & H3).
exists e. split; [exact Ha|]. split; [exact H1|]. split; [exact H2|].
intros z Hz. exact (proj1 (Forall_forall _ _) H3 z Hz).
Qed.

Lemma cfx_disj_out : forall a e z, in_zr a e -> zdisjoint e z -> ~ in_zr a z.
Proof. intros a e z H1 H2 H3. unfold in_zr, zdisjoint in *. lia. Qed.

Lemma xs_cf_not_extra_cf : forall ly S a, xs_placed_cf ly S -> Exists (in_zr a) (xs_cf ly S) -> ~ Exists (in_zr a) (ly_extra ly).
Proof.
intros ly S a HP Hx Hx'. destruct (cfx_pick ly S a HP Hx) as (e & Hae & _ & _ & Hdis).
apply Exists_exists in Hx' as (z & Hz & Hza).
exact (cfx_disj_out a e z Hae (Hdis z ltac:(apply in_or_app; right; apply in_or_app; right; exact Hz)) Hza).
Qed.

(* A client block misses the extent: a primary block lies in its class region, inside (ly_prim, kPrimResvSize)
   of static_extents; a secondary block lies in its own sec_extents entry. *)
Lemma block_not_xs_cf : forall segs B ly S Hp W mem md p n a, ARcf segs B ly S Hp W mem md ->
xs_placed_cf ly S -> In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> ~ Exists (in_zr a) (xs_cf ly S).
Proof.
intros segs B ly S Hp W mem md p n a (M & _ & _) HP Hin Ha Hx.
destruct (cfx_pick ly S a HP Hx) as (e & Hae & _ & _ & Hdis).
apply YG0s.In_ablocks in Hin as (k & Hk & _ & Hu & Hr). subst p n.
pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
rewrite G4 in Ha.
assert (Hext : ck_base B ly k <= a < ck_base B ly k + ck_extent k) by lia.
pose proof (amc_layout _ _ _ _ _ M) as LO.
destruct (ck_beg k) as [|off|r o|cid pos] eqn:Eb; try (exfalso; exact GG).
- destruct GG as (C1 & _ & _ & EX & EB & X0 & _ & XA & A1 & A2).
  apply (cfx_disj_out a e (ly_prim ly, kPrimResvSize) Hae
  (Hdis _ ltac:(apply in_or_app; right; apply in_or_app; left;
   unfold static_extents, owned_extents; apply in_or_app; left; left; reflexivity))).
  pose proof (lo_space_in _ LO) as [SP1 SP2].
  assert (RO : region_off (prim_class off) = prim_class off * 2 ^ 32) by (unfold region_off; apply Z.shiftl_mul_pow2; lia).
  unfold region_base in EB. rewrite RO in EB, X0, XA.
  unfold in_zr. cbn [fst snd]. unfold kSpaceSize, kFreeArrayOffset in *. lia.
- destruct GG as (_ & _ & EB & EX & HinS & _).
  apply (cfx_disj_out a e (ly_sec ly r, sec_map_size (ck_req k)) Hae
  (Hdis _ ltac:(apply in_or_app; left; exact HinS))).
  unfold in_zr. cbn [fst snd]. unfold kPage in *. lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. The errbuf entry along the model.                                             *)
Lemma cfx_last_cap_idx_app : forall l1 l2 i acc,
last_cap_idx (l1 ++ l2) i acc = last_cap_idx l2 (i + length l1) (last_cap_idx l1 i acc).
Proof.
induction l1 as [|x t IH]; intros l2 i acc; cbn [app length last_cap_idx].
- rewrite Nat.add_0_r. reflexivity.
- rewrite IH. replace (i + S (length t))%nat with (S i + length t)%nat by lia. reflexivity.
Qed.

Lemma cfx_last_cap_idx_lt : forall l i acc j, last_cap_idx l i acc = Some j ->
(forall k, acc = Some k -> (k < i)%nat) -> (j < i + length l)%nat.
Proof.
induction l as [|x t IH]; intros i acc j H Hacc; cbn [last_cap_idx length] in *.
- apply Hacc in H. lia.
- apply IH in H; [lia|]. intros k Hk. destruct (is_errb_cap x); [injection Hk as <-; lia | apply Hacc in Hk; lia].
Qed.

Lemma xs_cf_layout : forall ly ly' S, layout_le (length (st_secs S)) ly ly' -> xs_cf ly' S = xs_cf ly S.
Proof.
intros ly ly' S LE. unfold xs_cf. destruct (last_cap_idx (st_secs S) 0 None) as [j|] eqn:E; [|reflexivity].
pose proof (cfx_last_cap_idx_lt _ 0 None j E ltac:(intros k Hk; discriminate Hk)) as Hj.
destruct LE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Esec).
rewrite (Esec j ltac:(lia)). reflexivity.
Qed.

Lemma cfx_static_layout : forall n ly ly', layout_le n ly ly' -> static_extents ly' = static_extents ly.
Proof.
intros n ly ly' LE.
destruct LE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & ED & EI & _).
unfold static_extents, owned_extents. rewrite E1, E3, E4, E5, E6, E7, E8, E10, E11, ED, EI. reflexivity.
Qed.

Lemma xs_cf_app_noncap : forall ly S S' sm, st_secs S' = st_secs S ++ [sm] -> is_errb_cap sm = false ->
xs_cf ly S' = xs_cf ly S.
Proof.
intros ly S S' sm Es Hn. unfold xs_cf, errb_cap_cf, errb_e. rewrite Es, cfx_last_cap_idx_app, filter_app.
replace (filter is_errb_cap [sm]) with (@nil secmap) by (cbn [filter]; rewrite Hn; reflexivity).
rewrite app_nil_r. cbn [last_cap_idx]. rewrite Hn. reflexivity.
Qed.

(* errb_retire's re-tag (YG00cf.v:97-99). *)
Definition cfx_retire (sm : secmap) : secmap :=
if is_errb_cap sm then mkSec (sm_len sm) ERRB_DEAD_TAG false else sm.

Lemma cfx_retire_noncap : forall sm, is_errb_cap (cfx_retire sm) = false.
Proof. intros sm. unfold cfx_retire. destruct (is_errb_cap sm) eqn:E; [reflexivity | exact E]. Qed.

Lemma cfx_filter_retired : forall l, filter is_errb_cap (map cfx_retire l) = [].
Proof. induction l as [|x t IH]; [reflexivity|]. cbn [map filter]. rewrite cfx_retire_noncap. exact IH. Qed.

(* After errb_map_cf (YG00cf.v:121-126): every old capacity entry retired, the new one appended. *)
Lemma xs_cf_remap : forall ly S S' ncap,
st_secs S' = map cfx_retire (st_secs S) ++ [mkSec ncap ERRB_CAP_TAG false] ->
xs_cf ly S' = [(ly_sec ly (length (st_secs S)), Z.max 0 ncap)].
Proof.
intros ly S S' ncap Es. unfold xs_cf, errb_cap_cf, errb_e.
rewrite Es, cfx_last_cap_idx_app, filter_app, cfx_filter_retired.
cbn [last_cap_idx app filter]. rewrite length_map. reflexivity.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. xs_placed_cf along the walk.                                                  *)
Lemma xs_placed_cf_init : forall ly, xs_placed_cf ly init_state.
Proof.
intros ly. unfold xs_placed_cf. replace (xs_cf ly init_state) with (@nil (Z * Z)) by reflexivity. constructor.
Qed.

(* A layout step. *)
Lemma xs_placed_cf_layout : forall U pp cc bb ly ly' S, WfP_cf U pp cc bb S ->
layout_le (length (st_secs S)) ly ly' -> xs_placed_cf ly S -> xs_placed_cf ly' S.
Proof.
intros U pp cc bb ly ly' S W LE HP. unfold xs_placed_cf in *.
rewrite (xs_cf_layout ly ly' S LE), (sec_extents_le_cf ly ly' S U pp cc bb LE W), (cfx_static_layout _ ly ly' LE).
pose proof LE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EX & _). rewrite EX. exact HP.
Qed.

(* A state step: the errbuf entry is unchanged, and every sec extent after the step is either one from
   before or disjoint from the errbuf. *)
Lemma xs_placed_cf_mono : forall ly S S', xs_cf ly S' = xs_cf ly S ->
(forall z, In z (sec_extents ly S') -> In z (sec_extents ly S) \/ Forall (fun e => zdisjoint e z) (xs_cf ly S)) ->
xs_placed_cf ly S -> xs_placed_cf ly S'.
Proof.
intros ly S S' Ex Hz HP. unfold xs_placed_cf in *. rewrite Ex. apply Forall_forall. intros e He.
pose proof (proj1 (Forall_forall _ _) HP e He) as (A1 & A2 & A3 & A4).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
apply Forall_forall. intros z Hzin. apply in_app_iff in Hzin as [Hzin|Hzin].
- destruct (Hz z Hzin) as [Hold|Hfr].
  + exact (proj1 (Forall_forall _ _) A4 z (in_or_app _ _ _ (or_introl Hold))).
  + exact (proj1 (Forall_forall _ _) Hfr e He).
- exact (proj1 (Forall_forall _ _) A4 z (in_or_app _ _ _ (or_intror Hzin))).
Qed.

(* Steps that keep st_secs and add no sec extent. *)
Lemma xs_placed_cf_keep : forall ly S S', st_secs S' = st_secs S -> incl (sec_extents ly S') (sec_extents ly S) ->
xs_placed_cf ly S -> xs_placed_cf ly S'.
Proof.
intros ly S S' Es HI. apply xs_placed_cf_mono; [|intros z Hz; left; exact (HI z Hz)].
unfold xs_cf, errb_cap_cf, errb_e. rewrite Es. reflexivity.
Qed.

(* A new secondary (sec_alloc appends a live, non-capacity st_secs entry): its extent must be disjoint from the
   errbuf; xs_fresh_of_grant below gives that from the grant. *)
Lemma xs_placed_cf_sec_grow : forall ly S S' sm, st_secs S' = st_secs S ++ [sm] -> is_errb_cap sm = false ->
(forall z, In z (sec_extents ly S') -> In z (sec_extents ly S) \/ Forall (fun e => zdisjoint e z) (xs_cf ly S)) ->
xs_placed_cf ly S -> xs_placed_cf ly S'.
Proof. intros ly S S' sm Es Hn. apply xs_placed_cf_mono. exact (xs_cf_app_noncap ly S S' sm Es Hn). Qed.

(* The walk fact behind the grow case: the errbuf extent is one of the model's maps. *)
Definition xs_mapped_cf (ly : alayout) (S : astate) (md : Model) : Prop :=
forall e, In e (xs_cf ly S) -> In (wiv e) (vm_maps (m_vmmaps md)).

(* ARcf carries it: the ledger's last field alc_xs (YG0ncf.v) is its body. *)
Lemma ARcf_xsm : forall segs B ly S Hp W mem md, ARcf segs B ly S Hp W mem md -> xs_mapped_cf ly S md.
Proof. intros segs B ly S Hp W mem md (_ & L & _). exact (alc_xs _ _ _ _ L). Qed.

(* The LPS grant (grant_ok_na_pin, YK13.v:204) is region_free over every map of the model. *)
Lemma grant_apart_cf : forall md a n b s, grant_ok_na_pin md (w64 a) n = true ->
0 <= a < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> In (wiv (b, s)) (vm_maps (m_vmmaps md)) -> 0 <= b < 2 ^ 64 -> 0 <= s < 2 ^ 64 ->
zdisjoint (a, n) (b, s).
Proof.
intros md a n b s H Ha Hn Hin Hb Hs. unfold grant_ok_na_pin in H.
apply andb_true_iff in H as [_ H4]. rewrite YK13.region_free_app in H4. apply andb_true_iff in H4 as [_ H4].
change (wiv (b, s)) with (w64 b, w64 s) in Hin.
pose proof (YK13.region_free_In _ _ _ _ _ H4 Hin) as R. unfold w64 in R.
rewrite !Z_to_bv_unsigned in R. rewrite !bv_wrap_small in R by (change (bv_modulus 64) with (2 ^ 64); lia).
unfold zdisjoint. cbn [fst snd]. lia.
Qed.

Lemma grant_aligned_cf : forall md a n, grant_ok_na_pin md (w64 a) n = true -> 0 <= a < 2 ^ 64 -> page_aligned a.
Proof.
intros md a n H Ha. unfold grant_ok_na_pin in H.
apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H _].
apply Z.eqb_eq in H. unfold w64 in H. rewrite Z_to_bv_unsigned, bv_wrap_small in H by (change (bv_modulus 64) with (2 ^ 64); lia).
exact H.
Qed.

Lemma cfx_xs_snd_nonneg : forall ly S, Forall (fun e => 0 <= snd e) (xs_cf ly S).
Proof.
intros ly S. unfold xs_cf. destruct (last_cap_idx (st_secs S) 0 None); [|constructor].
constructor; [cbn [snd]; apply errb_cap_cf_nonneg | constructor].
Qed.

(* The grow case's premise, from the grant of the new map at a and the walk fact xs_mapped_cf. *)
Lemma xs_fresh_of_grant : forall ly S md a n, xs_placed_cf ly S -> xs_mapped_cf ly S md ->
grant_ok_na_pin md (w64 a) n = true -> 0 <= a -> 0 <= n -> a + n < 2 ^ 64 ->
Forall (fun e => zdisjoint e (a, n)) (xs_cf ly S).
Proof.
intros ly S md a n HP Hm Hg Ha Hn Han. apply Forall_forall. intros e He.
pose proof (proj1 (Forall_forall _ _) HP e He) as (_ & [I0 _] & UB & _).
pose proof (proj1 (Forall_forall _ _) (cfx_xs_snd_nonneg ly S) e He) as S0.
pose proof alloc_ceiling_lt as CL.
destruct e as [b s]. cbn [fst snd] in *.
pose proof (grant_apart_cf md a n b s Hg ltac:(lia) ltac:(lia) (Hm _ He) ltac:(lia) ltac:(lia)) as D.
unfold zdisjoint in *. cbn [fst snd] in *. lia.
Qed.

(* The class-full remap: the fresh slot at index length (st_secs S), of length Z.max 0 ncap, placed. *)
Lemma xs_placed_cf_remap : forall ly S S' ncap,
st_secs S' = map cfx_retire (st_secs S) ++ [mkSec ncap ERRB_CAP_TAG false] ->
page_aligned (ly_sec ly (length (st_secs S))) /\ in_app (ly_sec ly (length (st_secs S))) (Z.max 0 ncap) /\
ly_sec ly (length (st_secs S)) + Z.max 0 ncap <= alloc_ceiling /\
Forall (zdisjoint (ly_sec ly (length (st_secs S)), Z.max 0 ncap)) (sec_extents ly S' ++ static_extents ly ++ ly_extra ly) ->
xs_placed_cf ly S'.
Proof.
intros ly S S' ncap Es Hok. unfold xs_placed_cf. rewrite (xs_cf_remap ly S S' ncap Es).
constructor; [exact Hok | constructor].
Qed.

(* ---------------------------------------------------------------------------- *)
(* 4. The free path's state frame: free maps neither a secondary nor the errbuf, re-tags st_secs entries   *)
(*    in place (sec_dealloc keeps sm_len and sm_size) and only drops or re-states chunks.                  *)
Definition free_frame_cf (S S' : astate) : Prop :=
(forall ly0, xs_cf ly0 S' = xs_cf ly0 S) /\ (forall ly0, incl (sec_extents ly0 S') (sec_extents ly0 S)).

Definition cfx_same_sm (sm sm' : secmap) : Prop := sm_len sm' = sm_len sm /\ sm_size sm' = sm_size sm.

Lemma cfx_cap_same : forall sm sm', cfx_same_sm sm sm' -> is_errb_cap sm' = is_errb_cap sm.
Proof. intros sm sm' [_ E]. unfold is_errb_cap. rewrite E. reflexivity. Qed.

Lemma cfx_last_cap_idx_f2 : forall l l', Forall2 cfx_same_sm l l' ->
forall i acc, last_cap_idx l' i acc = last_cap_idx l i acc.
Proof.
intros l l' H. induction H as [|x x' t t' Hx Ht IH]; intros i acc; [reflexivity|].
cbn [last_cap_idx]. rewrite (cfx_cap_same x x' Hx). apply IH.
Qed.

Lemma cfx_filter_f2 : forall l l', Forall2 cfx_same_sm l l' ->
Forall2 cfx_same_sm (filter is_errb_cap l) (filter is_errb_cap l').
Proof.
intros l l' H. induction H as [|x x' t t' Hx Ht IH]; cbn [filter]; [constructor|].
rewrite (cfx_cap_same x x' Hx). destruct (is_errb_cap x); [constructor; assumption | exact IH].
Qed.

Lemma cfx_last_len_f2 : forall l l' d, Forall2 cfx_same_sm l l' -> sm_len (last l' d) = sm_len (last l d).
Proof.
intros l l' d H. induction H as [|x x' t t' Hx Ht IH]; [reflexivity|].
destruct t as [|y t0]; inversion Ht; subst; [exact (proj1 Hx) | exact IH].
Qed.

(* The frame from its two state facts, the form a model lemma over free_cf's path would give. *)
Lemma free_frame_cf_of_state : forall S S',
Forall2 cfx_same_sm (st_secs S) (st_secs S') ->
(forall k, In k (st_chunks S') -> exists k0, In k0 (st_chunks S) /\ ck_beg k0 = ck_beg k /\ ck_req k0 = ck_req k) ->
free_frame_cf S S'.
Proof.
intros S S' HS HC. split.
- intros ly0. unfold xs_cf, errb_cap_cf, errb_e.
  rewrite (cfx_last_cap_idx_f2 _ _ HS 0 None).
  rewrite (cfx_last_len_f2 _ _ (mkSec 0 ERRB_CAP_TAG false) (cfx_filter_f2 _ _ HS)). reflexivity.
- intros ly0 e He. unfold sec_extents in *. apply in_flat_map in He as (k & Hk & He).
  destruct (HC k Hk) as (k0 & Hk0 & Eb & Er). apply in_flat_map. exists k0. split; [exact Hk0|].
  rewrite Eb, Er. exact He.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 4b. The frame on EVERY path of free_cf (no gflag, no invariant).                *)
(*     cfx_ipost t P: every IRet of t satisfies P (YGcfAmx.v's ipost, restated).    *)
Fixpoint cfx_ipost {A : Type} (t : itree astate A) (P : A -> Prop) : Prop :=
match t with
| IRet a => P a
| IAsk _ _ k => forall z, cfx_ipost (k z) P
| ISpin _ => True
| IFail _ => True
end.

Lemma cfx_ipost_mono {A} (t : itree astate A) : forall (P Q : A -> Prop), (forall a, P a -> Q a) -> cfx_ipost t P -> cfx_ipost t Q.
Proof.
induction t as [a | q sn k IH | pc | f]; cbn [cfx_ipost]; intros P Q HPQ H.
- exact (HPQ a H).
- intros z. exact (IH z P Q HPQ (H z)).
- exact I.
- exact I.
Qed.

Lemma cfx_ipost_ibind {A B0} (t : itree astate A) : forall (k : A -> itree astate B0) (P : B0 -> Prop),
cfx_ipost t (fun a => cfx_ipost (k a) P) -> cfx_ipost (ibind t k) P.
Proof.
induction t as [a | q sn c IH | pc | f]; cbn [ibind cfx_ipost]; intros k P H.
- exact H.
- intros z. apply IH. exact (H z).
- exact I.
- exact I.
Qed.

Lemma cfx_ipost_ibind_assoc {A B0 C} (t : itree astate A) : forall (k1 : A -> itree astate B0) (k2 : B0 -> itree astate C) P,
cfx_ipost (ibind t (fun a => ibind (k1 a) k2)) P -> cfx_ipost (ibind (ibind t k1) k2) P.
Proof.
induction t as [a | q sn c IH | pc | f]; cbn [ibind cfx_ipost]; intros k1 k2 P H.
- exact H.
- intros z. apply IH. exact (H z).
- exact I.
- exact I.
Qed.

Lemma cfx_ipost_apath {A : Type} : forall (t : itree astate A) (P : A -> Prop) tr a, cfx_ipost t P -> apath t tr a -> P a.
Proof.
induction t as [a' | q sn k IH | pc | f]; intros P tr a H Hp; destruct tr as [|[q' z] tr];
cbn [apath cfx_ipost] in Hp, H; try contradiction.
- subst a'. exact H.
- destruct Hp as (_ & _ & Hp). exact (IH z P tr a (H z) Hp).
Qed.

(* The frame from a start state s0: st_secs pointwise the same length and size, every chunk one of s0's. *)
Definition cfx_fr (s0 s : astate) : Prop :=
Forall2 cfx_same_sm (st_secs s0) (st_secs s) /\
(forall k, In k (st_chunks s) -> exists k0, In k0 (st_chunks s0) /\ ck_beg k0 = ck_beg k /\ ck_req k0 = ck_req k).
(* No change at all, relative to the call's own start state. *)
Definition cfx_same (s s' : astate) : Prop := st_secs s' = st_secs s /\ st_chunks s' = st_chunks s.

Lemma cfx_f2_refl : forall l, Forall2 cfx_same_sm l l.
Proof. induction l as [|x t IH]; constructor; [split; reflexivity | exact IH]. Qed.

Lemma cfx_f2_trans : forall l1 l2 l3, Forall2 cfx_same_sm l1 l2 -> Forall2 cfx_same_sm l2 l3 -> Forall2 cfx_same_sm l1 l3.
Proof.
intros l1 l2 l3 H. revert l3. induction H as [|x y t1 t2 Hxy H IH]; intros l3 H2; [exact H2|].
destruct l3 as [|z t3]; inversion H2 as [|a b c d Hyz H23]; subst.
constructor; [destruct Hxy as [E1 E2], Hyz as [F1 F2]; split; congruence | exact (IH t3 H23)].
Qed.

Lemma cfx_f2_lupd : forall l r sm, nth_error l r = Some sm ->
Forall2 cfx_same_sm l (lupd l r (mkSec (sm_len sm) (sm_size sm) false)).
Proof.
induction l as [|x t IH]; intros r sm H; [destruct r; discriminate H|].
destruct r as [|r]; cbn [lupd nth_error] in *.
- injection H as <-. constructor; [split; reflexivity | apply cfx_f2_refl].
- constructor; [split; reflexivity | exact (IH r sm H)].
Qed.

Lemma cfx_del_incl : forall l b x, In x (del_chunk l b) -> In x l.
Proof.
induction l as [|k t IH]; intros b x H; cbn [del_chunk] in H; [destruct H|].
destruct (sptr_eqb (ck_beg k) b); [right; exact H | destruct H as [<-|H]; [left; reflexivity | right; exact (IH b x H)]].
Qed.

Lemma cfx_upd_in : forall l k' x, In x (upd_chunk l k') -> x = k' \/ In x l.
Proof.
induction l as [|k t IH]; intros k' x H; cbn [upd_chunk] in H.
- destruct H as [<-|[]]. left. reflexivity.
- destruct (sptr_eqb (ck_beg k) (ck_beg k')).
  + destruct H as [<-|H]; [left; reflexivity | right; right; exact H].
  + destruct H as [<-|H]; [right; left; reflexivity|]. destruct (IH k' x H) as [E|E]; [left; exact E | right; right; exact E].
Qed.

Lemma cfx_find_user_in : forall l p k, find_user l p = Some k -> In k l.
Proof.
induction l as [|k' t IH]; intros p k H; cbn [find_user] in H; [discriminate H|].
destruct (sptr_eqb (ck_user k') p); [injection H as <-; left; reflexivity | right; exact (IH p k H)].
Qed.

Lemma cfx_fr_same : forall s0 s, st_secs s = st_secs s0 -> st_chunks s = st_chunks s0 -> cfx_fr s0 s.
Proof.
intros s0 s E1 E2. split; [rewrite E1; apply cfx_f2_refl|].
intros k Hk. rewrite E2 in Hk. exists k. split; [exact Hk | split; reflexivity].
Qed.

Lemma cfx_fr_trans : forall s0 s1 s2, cfx_fr s0 s1 -> cfx_fr s1 s2 -> cfx_fr s0 s2.
Proof.
intros s0 s1 s2 [A1 B1] [A2 B2]. split; [exact (cfx_f2_trans _ _ _ A1 A2)|].
intros k Hk. destruct (B2 k Hk) as (k1 & Hk1 & E1 & F1). destruct (B1 k1 Hk1) as (k0 & Hk0 & E0 & F0).
exists k0. split; [exact Hk0 | split; congruence].
Qed.

Lemma cfx_fr_del : forall s0 s s' b, cfx_fr s0 s -> st_secs s' = st_secs s -> st_chunks s' = del_chunk (st_chunks s) b ->
cfx_fr s0 s'.
Proof.
intros s0 s s' b H E1 E2. apply (cfx_fr_trans s0 s s' H). split; [rewrite E1; apply cfx_f2_refl|].
intros k Hk. rewrite E2 in Hk. exists k. split; [exact (cfx_del_incl _ _ _ Hk) | split; reflexivity].
Qed.

Lemma cfx_fr_dead : forall s0 s s' r sm, cfx_fr s0 s -> nth_error (st_secs s) r = Some sm ->
st_secs s' = lupd (st_secs s) r (mkSec (sm_len sm) (sm_size sm) false) -> st_chunks s' = st_chunks s -> cfx_fr s0 s'.
Proof.
intros s0 s s' r sm H E E1 E2. apply (cfx_fr_trans s0 s s' H). split; [rewrite E1; exact (cfx_f2_lupd _ _ _ E)|].
intros k Hk. rewrite E2 in Hk. exists k. split; [exact Hk | split; reflexivity].
Qed.

Lemma cfx_fr_upd : forall s0 s p k, find_user (st_chunks s0) p = Some k -> st_secs s = st_secs s0 ->
st_chunks s = upd_chunk (st_chunks s0) (mkChunk (ck_beg k) (ck_req k) CQuarantined) -> cfx_fr s0 s.
Proof.
intros s0 s p k Hf E1 E2. split; [rewrite E1; apply cfx_f2_refl|].
intros x Hx. rewrite E2 in Hx. destruct (cfx_upd_in _ _ _ Hx) as [->|Hx'].
- exists k. split; [exact (cfx_find_user_in _ _ _ Hf) | split; reflexivity].
- exists x. split; [exact Hx' | split; reflexivity].
Qed.

Lemma cfx_fr_ipost_same {A : Type} : forall (t : itree astate (A * astate)) s0 s, cfx_fr s0 s ->
cfx_ipost t (fun r => cfx_same s (snd r)) -> cfx_ipost t (fun r => cfx_fr s0 (snd r)).
Proof.
intros t s0 s H1 H2. eapply cfx_ipost_mono; [|exact H2]. intros [x sx] [E1 E2]. cbn [snd] in *.
exact (cfx_fr_trans s0 s sx H1 (cfx_fr_same s sx E1 E2)).
Qed.

Create HintDb frdb.

Ltac fr_unf :=
progress (unfold YG00.get_region, YG00.set_region, YG00.get_pc, YG00.set_pc, YG00.init_cache_if_needed, YG00.tick,
YG00.bind, YG00.get, YG00.put, YG00.modify, YG00.askz, YG00.ret, YG00.mcheck, YG00.fail, YG00.spin, cfx_same in *).

Ltac fr_cbn :=
cbn [ibind cfx_ipost fst snd st_secs st_chunks st_regions st_cache st_cache_inited st_sec_arr st_sec_reserved st_qthread
st_qglobal st_fs st_depot st_internal_inited st_nev set_regions set_cache set_chunks set_secs set_sec_arr
set_sec_reserved set_depot set_cache_inited set_nev set_qglobal set_qthread set_internal_inited] in *.

Ltac fr_hint :=
first
[ match goal with |- cfx_ipost (ibind _ _) _ =>
  apply cfx_ipost_ibind; eapply cfx_ipost_mono; [|solve [eauto with frdb]];
  let x := fresh "x" in let sx := fresh "sx" in let H1 := fresh "Hs" in let H2 := fresh "Hc" in
  intros [x sx] [H1 H2]; cbn [fst snd] in H1, H2 end
| match goal with |- cfx_ipost _ _ =>
  eapply cfx_ipost_mono; [|solve [eauto with frdb]];
  let x := fresh "x" in let sx := fresh "sx" in let H1 := fresh "Hs" in let H2 := fresh "Hc" in
  intros [x sx] [H1 H2]; cbn [fst snd] in H1, H2 end ].

Ltac fr_step :=
first
[ progress fr_cbn
| fr_unf
| progress intros
| match goal with |- cfx_ipost (ibind (ibind _ _) _) _ => apply cfx_ipost_ibind_assoc end
| fr_hint
| match goal with |- context [match ?x with _ => _ end] => destruct x end
| exact I
| split; congruence ].

(* The callees that touch neither st_secs nor st_chunks. *)
Lemma cfx_same_ensure : forall c need sof s, cfx_ipost (ensure_free_array c need sof s) (fun r => cfx_same s (snd r)).
Proof. intros c need sof s. unfold ensure_free_array. repeat fr_step. Qed.
#[local] Hint Resolve cfx_same_ensure : frdb.

Lemma cfx_same_mmu : forall c need s, cfx_ipost (map_more_user c need s) (fun r => cfx_same s (snd r)).
Proof. intros c need s. unfold map_more_user. repeat fr_step. Qed.
#[local] Hint Resolve cfx_same_mmu : frdb.

Lemma cfx_same_populate : forall c need s, cfx_ipost (populate c need s) (fun r => cfx_same s (snd r)).
Proof. intros c need s. unfold populate. repeat fr_step. Qed.
#[local] Hint Resolve cfx_same_populate : frdb.

Lemma cfx_same_gfa : forall c n s, cfx_ipost (get_from_allocator c n s) (fun r => cfx_same s (snd r)).
Proof. intros c n s. unfold get_from_allocator. repeat fr_step. Qed.
#[local] Hint Resolve cfx_same_gfa : frdb.

Lemma cfx_same_refill : forall c s, cfx_ipost (refill_if_empty c s) (fun r => cfx_same s (snd r)).
Proof. intros c s. unfold refill_if_empty. repeat fr_step. Qed.
#[local] Hint Resolve cfx_same_refill : frdb.

Lemma cfx_same_cache_alloc : forall c s, cfx_ipost (cache_alloc c s) (fun r => cfx_same s (snd r)).
Proof. intros c s. unfold cache_alloc. repeat fr_step. Qed.
#[local] Hint Resolve cfx_same_cache_alloc : frdb.

Lemma cfx_same_depot_put : forall tr s, cfx_ipost (depot_put tr s) (fun r => cfx_same s (snd r)).
Proof. intros tr s. unfold depot_put. repeat fr_step. Qed.
#[local] Hint Resolve cfx_same_depot_put : frdb.

Lemma cfx_same_rta : forall c offs s, cfx_ipost (return_to_allocator c offs s) (fun r => cfx_same s (snd r)).
Proof. intros c offs s. unfold return_to_allocator. repeat fr_step. Qed.
#[local] Hint Resolve cfx_same_rta : frdb.

Lemma cfx_same_cache_dealloc : forall c off s, cfx_ipost (cache_dealloc c off s) (fun r => cfx_same s (snd r)).
Proof. intros c off s. unfold cache_dealloc. repeat fr_step. Qed.
#[local] Hint Resolve cfx_same_cache_dealloc : frdb.

Lemma cfx_same_enqueue : forall k s, cfx_ipost (enqueue k s) (fun r => cfx_same s (snd r)).
Proof. intros k s. unfold enqueue. repeat fr_step. Qed.
#[local] Hint Resolve cfx_same_enqueue : frdb.

(* The steps that change st_secs or st_chunks, in the frame form. *)
Lemma cfx_fr_sec_dealloc : forall r s0 s, cfx_fr s0 s -> cfx_ipost (sec_dealloc r s) (fun x => cfx_fr s0 (snd x)).
Proof.
intros r s0 s H. unfold sec_dealloc. fr_unf. fr_cbn.
destruct (nth_error (st_secs s) r) as [sm|] eqn:E; [|exact I].
destruct (index_of (st_sec_arr s) r 0) as [i|]; [|exact I].
repeat (first [progress fr_cbn | fr_unf | progress intros
| match goal with |- cfx_ipost (ibind (ibind _ _) _) _ => apply cfx_ipost_ibind_assoc end
| match goal with |- context [match ?x with _ => _ end] => destruct x end
| exact I]).
all: eapply cfx_fr_dead; [exact H | exact E | reflexivity | reflexivity].
Qed.

Lemma cfx_fr_recycle_chunk : forall k s0 s, cfx_fr s0 s -> cfx_ipost (recycle_chunk k s) (fun x => cfx_fr s0 (snd x)).
Proof.
intros k s0 s H. unfold recycle_chunk. fr_unf. fr_cbn.
destruct (mem_chunk k (st_chunks s)); fr_cbn; [|exact I].
assert (H1 : cfx_fr s0 (set_chunks (del_chunk (st_chunks s) (ck_beg k)) s)) by (eapply cfx_fr_del; [exact H | reflexivity | reflexivity]).
destruct (ck_beg k) as [|off|r o|cid pos]; fr_cbn.
- exact I.
- eapply cfx_fr_ipost_same; [|apply cfx_same_cache_dealloc]. exact H1.
- apply cfx_fr_sec_dealloc. exact H1.
- exact I.
Qed.

Lemma cfx_fr_recycle_items : forall fuel items s0 s, cfx_fr s0 s -> cfx_ipost (recycle_items fuel items s) (fun x => cfx_fr s0 (snd x)).
Proof.
induction fuel as [|f IH]; intros items s0 s H; destruct items as [|k t]; cbn [recycle_items]; try fr_unf; try fr_cbn;
try exact H; try exact I.
apply cfx_ipost_ibind. eapply cfx_ipost_mono; [|exact (cfx_fr_recycle_chunk k s0 s H)].
intros [x sx] Hx. cbn [fst snd] in *. apply IH. exact Hx.
Qed.

Lemma cfx_fr_do_recycle : forall fuel bs s0 s, cfx_fr s0 s -> cfx_ipost (do_recycle fuel bs s) (fun x => cfx_fr s0 (snd x)).
Proof.
induction fuel as [|f IH]; intros bs s0 s H; destruct bs as [|b t]; cbn [do_recycle]; try fr_unf; try fr_cbn;
try exact H; try exact I.
apply cfx_ipost_ibind. eapply cfx_ipost_mono; [|exact (cfx_fr_recycle_items 1100 (b_items b) s0 s H)].
intros [x sx] Hx. cbn [fst snd] in *.
apply cfx_ipost_ibind. eapply cfx_ipost_mono; [|exact (cfx_fr_ipost_same _ s0 sx Hx (cfx_same_cache_dealloc kBatchClass (b_self b) sx))].
intros [y sy] Hy. cbn [fst snd] in *. apply IH. exact Hy.
Qed.

Lemma cfx_fr_maybe_drain : forall s0 s, cfx_fr s0 s -> cfx_ipost (maybe_drain_cf s) (fun x => cfx_fr s0 (snd x)).
Proof.
intros s0 s H. unfold maybe_drain_cf.
repeat (first [progress fr_cbn | fr_unf | progress intros
| match goal with |- cfx_ipost (ibind (ibind _ _) _) _ => apply cfx_ipost_ibind_assoc end
| match goal with |- cfx_ipost (do_recycle _ _ _) _ => apply cfx_fr_do_recycle end
| match goal with |- context [match ?x with _ => _ end] => destruct x end
| exact I
| assumption]).
Qed.

Lemma cfx_fr_free_cf : forall p tr S, cfx_ipost (free_cf p tr S) (fun x => cfx_fr S (snd x)).
Proof.
intros p tr S. unfold free_cf.
repeat (first [progress fr_cbn | fr_unf | progress intros
| match goal with |- cfx_ipost (ibind (recycle_chunk ?k ?s) _) _ =>
    apply cfx_ipost_ibind; eapply cfx_ipost_mono;
    [|apply (cfx_fr_recycle_chunk k S s); eapply cfx_fr_upd; [eassumption | fr_cbn; congruence | fr_cbn; congruence]];
    let x := fresh "x" in let sx := fresh "sx" in let H := fresh "Hr" in intros [x sx] H; cbn [fst snd] in H end
| match goal with |- cfx_ipost (ibind (ibind _ _) _) _ => apply cfx_ipost_ibind_assoc end
| match goal with |- cfx_ipost (maybe_drain_cf _) _ => apply cfx_fr_maybe_drain end
| match goal with |- context [find_user ?l ?q] => let E := fresh "Ef" in destruct (find_user l q) eqn:E end
| fr_hint
| match goal with |- context [match ?x with _ => _ end] => destruct x end
| exact I
| (apply cfx_fr_same; reflexivity)
| (apply cfx_fr_same; congruence)
| (eapply cfx_fr_upd; [eassumption | congruence | congruence])
| assumption ]).
Qed.

(* The model lemma: on every path of free_cf, the state frame holds. *)
Theorem free_cf_frame : forall p tr S t S', apath (free_cf p tr S) t (tt, S') -> free_frame_cf S S'.
Proof.
intros p tr S t S' Hp. pose proof (cfx_ipost_apath _ _ t (tt, S') (cfx_fr_free_cf p tr S) Hp) as [HS HC].
cbn [snd] in HS, HC. exact (free_frame_cf_of_state S S' HS HC).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 5. The keep lemmas: xs_placed_cf at each leaf's post layout and state.          *)
Lemma malloc_leaf_cf_xs_keep : forall segs B ly S Hp W regs mem md ch n r W' c',
acall_pre_cf segs B ly S Hp W regs mem md ch -> xs_placed_cf ly S ->
malloc_leaf_cf segs B ly S Hp W regs mem md n r W' c' ->
exists ly' regs' mem' md', c' = cfg_at segs (raZ regs) regs' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\
ARcf segs B ly' (snd r) Hp W' mem' md' /\ xs_placed_cf ly' (snd r).
Proof.
intros segs B ly S Hp W regs mem md ch n r W' c' _ _ (ly' & regs' & mem' & md' & Hc & (A1 & A2 & _) & _ & _ & _ & HX & _).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact A2|]. split; [exact A1 | exact HX].
Qed.

(* free_leaf_cf relates its post state to S through nothing but ARcf, so the state frame is a premise. *)
Lemma free_leaf_cf_xs_keep : forall segs B ly S Hp W regs mem md ch p n r W' c',
acall_pre_cf segs B ly S Hp W regs mem md ch -> xs_placed_cf ly S -> free_frame_cf S (snd r) ->
free_leaf_cf segs B ly S Hp W regs mem md p n r W' c' ->
exists ly' regs' mem' md', c' = cfg_at segs (raZ regs) regs' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\
ARcf segs B ly' (snd r) Hp W' mem' md' /\ xs_placed_cf ly' (snd r).
Proof.
intros segs B ly S Hp W regs mem md ch p n r W' c' Hpre HP (FX & FS) (ly' & regs' & mem' & md' & Hc & (A1 & A2 & _) & _).
pose proof (amc_wf _ _ _ _ _ (proj1 (proj1 Hpre))) as W0. unfold Wf_cf in W0.
pose proof (xs_placed_cf_layout _ _ _ _ ly ly' S W0 A2 HP) as HP'.
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact A2|]. split; [exact A1|].
apply (xs_placed_cf_mono ly' S (snd r)); [exact (FX ly') | intros z Hz; left; exact (FS ly' z Hz) | exact HP'].
Qed.

(* The same, from the model path a walk holds (amreal_SRr04): no extra premise. *)
Lemma free_leaf_cf_xs_keep_path : forall segs B ly S Hp W regs mem md ch p n tr t r W' c',
acall_pre_cf segs B ly S Hp W regs mem md ch -> xs_placed_cf ly S ->
apath (free_cf p tr S) t (tt, snd r) ->
free_leaf_cf segs B ly S Hp W regs mem md p n r W' c' ->
exists ly' regs' mem' md', c' = cfg_at segs (raZ regs) regs' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\
ARcf segs B ly' (snd r) Hp W' mem' md' /\ xs_placed_cf ly' (snd r).
Proof.
intros segs B ly S Hp W regs mem md ch p n tr t r W' c' Hpre HP Hpath HL.
exact (free_leaf_cf_xs_keep segs B ly S Hp W regs mem md ch p n r W' c' Hpre HP (free_cf_frame p tr S t (snd r) Hpath) HL).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 6. block_not_xs_cf at each leaf's post layout and state.                         *)
Lemma block_not_xs_malloc_cf : forall segs B ly S Hp W regs mem md ch n r W' c',
acall_pre_cf segs B ly S Hp W regs mem md ch -> xs_placed_cf ly S ->
malloc_leaf_cf segs B ly S Hp W regs mem md n r W' c' ->
exists ly' regs' mem' md', c' = cfg_at segs (raZ regs) regs' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\
forall p m a, In (p, m) (ablocks B ly' (snd r)) -> p <= a < p + req_size m -> ~ Exists (in_zr a) (xs_cf ly' (snd r)).
Proof.
intros segs B ly S Hp W regs mem md ch n r W' c' Hpre HP HL.
destruct (malloc_leaf_cf_xs_keep segs B ly S Hp W regs mem md ch n r W' c' Hpre HP HL) as (ly' & regs' & mem' & md' & Hc & LE & AR & HX).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact LE|].
intros p m a Hin Ha. exact (block_not_xs_cf segs B ly' (snd r) Hp W' mem' md' p m a AR HX Hin Ha).
Qed.

Lemma block_not_xs_free_cf : forall segs B ly S Hp W regs mem md ch p n tr t r W' c',
acall_pre_cf segs B ly S Hp W regs mem md ch -> xs_placed_cf ly S ->
apath (free_cf p tr S) t (tt, snd r) ->
free_leaf_cf segs B ly S Hp W regs mem md p n r W' c' ->
exists ly' regs' mem' md', c' = cfg_at segs (raZ regs) regs' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\
forall q m a, In (q, m) (ablocks B ly' (snd r)) -> q <= a < q + req_size m -> ~ Exists (in_zr a) (xs_cf ly' (snd r)).
Proof.
intros segs B ly S Hp W regs mem md ch p n tr t r W' c' Hpre HP Hpath HL.
destruct (free_leaf_cf_xs_keep_path segs B ly S Hp W regs mem md ch p n tr t r W' c' Hpre HP Hpath HL)
as (ly' & regs' & mem' & md' & Hc & LE & AR & HX).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact LE|].
intros q m a Hin Ha. exact (block_not_xs_cf segs B ly' (snd r) Hp W' mem' md' q m a AR HX Hin Ha).
Qed.

Lemma block_not_xs_realloc_cf : forall segs B ly S Hp W regs mem md ch p n_old n r W' c',
acall_pre_cf segs B ly S Hp W regs mem md ch -> xs_placed_cf ly S ->
YGcfRealloc.realloc_leaf_cf segs B ly S Hp W regs mem md p n_old n r W' c' ->
exists ly' regs' mem' md', c' = cfg_at segs (raZ regs) regs' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\
forall q m a, In (q, m) (ablocks B ly' (snd r)) -> q <= a < q + req_size m -> ~ Exists (in_zr a) (xs_cf ly' (snd r)).
Proof.
intros segs B ly S Hp W regs mem md ch p n_old n r W' c' Hpre HP HL.
destruct (YGcfRealloc.realloc_leaf_cf_xs_keep segs B ly S Hp W regs mem md ch p n_old n r W' c' Hpre HP HL)
as (ly' & regs' & mem' & md' & Hc & LE & AR & HX).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact LE|].
intros q m a Hin Ha. exact (block_not_xs_cf segs B ly' (snd r) _ W' mem' md' q m a AR HX Hin Ha).
Qed.

End X.
