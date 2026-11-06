(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), the SHADOW LAW over ARcf.
   cgif's AR_shadow_law_ok (YG0s.v:771-831) re-proved for AR_shadow_law_cf (YG0dcf.v). cgif's YG0s.v is NOT
   edited. The one new piece is the hidden head: a granule of a live block at or past p + hd_skip Hp p is in no
   base's head (hd_free_cf), because every base in Hp is the user base of a live block (amc_hp_live) and two
   live blocks' extents are disjoint (find_chunk_at_hit_cf), so shadow_ok_cf gives cgif's ashadow value there.
   The head is granule-aligned by CfParams' cf_head_al. The hull needs presence only, which 0xf7 keeps.
   No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := let H := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.

(* ---------------------------------------------------------------------------- *)
(* The head of a hidden base lies inside its own live block, so a granule of any  *)
(* live block k that is in q's head makes q the user base of k itself.           *)
Lemma hp_owner_cf : forall B ly S Hp rd k q g, ARmcf B ly S Hp rd -> In k (st_chunks S) -> In q Hp ->
q <= g < q + cf_head -> ck_base B ly k <= g < ck_base B ly k + ck_extent k ->
q = sptr_addr B ly (ck_user k) /\ cf_head <= ck_n k.
Proof.
intros B ly S Hp rd k q g M Hk Hq Hg Hgk.
pose proof (proj1 (Forall_forall _ _) (amc_hp_live _ _ _ _ _ M) q Hq) as (k' & Hk' & _ & Eq & Hn).
pose proof (chunk_facts_cf B ly S Hp rd k' M Hk') as (_ & _ & _ & X4 & X5 & _ & X7 & X8 & _).
pose proof (req_size_bounds (ck_req k') ltac:(lia)) as (Q1 & Q2 & Q3).
pose proof (wfc_chunks_nodup _ _ _ _ _ (amc_wf _ _ _ _ _ M)) as ND.
pose proof (find_chunk_at_hit_cf B ly S Hp rd (st_chunks S) k g M (fun x Hx => Hx) ND Hk Hgk) as F1.
assert (F2 : find_chunk_at B ly (st_chunks S) g = Some k').
{ apply (find_chunk_at_hit_cf B ly S Hp rd (st_chunks S) k' g M (fun x Hx => Hx) ND Hk'). unfold ck_n in Hn. lia. }
rewrite F1 in F2. injection F2 as E. subst k'. split; [exact Eq | exact Hn].
Qed.

(* The skipped head is 0 or cf_head, and never longer than the block. *)
Lemma hd_bound_cf : forall B ly S Hp rd k p, ARmcf B ly S Hp rd -> In k (st_chunks S) -> sptr_addr B ly (ck_user k) = p ->
0 <= hd_skip Hp p <= ck_n k.
Proof.
intros B ly S Hp rd k p M Hk Hu.
pose proof cf_head_nonneg as CH. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (_ & _ & _ & G4 & G5 & _ & G7 & G8 & _).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
unfold hd_skip. destruct (existsb (Z.eqb p) Hp) eqn:E; cbv beta iota; [|unfold ck_n; lia].
apply existsb_exists in E as (q & Hq & Eq). apply Z.eqb_eq in Eq. subst q.
destruct (Z.eq_dec cf_head 0) as [Z0|NZ]; [unfold ck_n; lia|].
destruct (hp_owner_cf B ly S Hp rd k p p M Hk Hq ltac:(lia) ltac:(lia)) as [_ Hn]. exact (conj CH Hn).
Qed.

(* THE NEW MATHEMATICS: past the skipped head, no granule of a live block is in any base's head. *)
Lemma hd_free_cf : forall B ly S Hp rd k p, ARmcf B ly S Hp rd -> In k (st_chunks S) -> sptr_addr B ly (ck_user k) = p ->
forall g, p + hd_skip Hp p <= g < p + ck_n k -> in_head Hp g = false.
Proof.
intros B ly S Hp rd k p M Hk Hu g Hg.
destruct (in_head Hp g) eqn:E; [exfalso|reflexivity].
unfold in_head in E. apply existsb_exists in E as (q & Hq & Eq). apply andb_prop in Eq as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (_ & _ & _ & G4 & G5 & _ & G7 & G8 & _).
pose proof (hd_bound_cf B ly S Hp rd k p M Hk Hu) as [HS _].
unfold ck_n in Hg.
destruct (hp_owner_cf B ly S Hp rd k q g M Hk Hq ltac:(lia) ltac:(lia)) as [Eq _].
assert (Hin : existsb (Z.eqb p) Hp = true) by (apply existsb_exists; exists q; split; [exact Hq | apply Z.eqb_eq; lia]).
replace (hd_skip Hp p) with cf_head in Hg by (unfold hd_skip; rewrite Hin; reflexivity). lia.
Qed.

(* cgif's AR_shadow_law_ok (YG0s.v:771-831), for any granule-aligned skip. *)
Lemma AR_shadow_law_ok_cf_al : forall segs B ly S Hp W mem md p n,
ARcf segs B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> hd_skip Hp p mod 8 = 0 ->
block_shadow (aview segs (w_H W) mem) SHADOW_OFF (p + hd_skip Hp p) (req_size n - hd_skip Hp p) /\
shadow_hull_vis (aview segs (w_H W) mem) p (req_size n).
Proof.
intros segs B ly S Hp W mem md p n (M & L & _) Hin Hal. apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hr).
pose proof (hd_free_cf B ly S Hp _ k p M Hk Hu) as HD. pose proof (hd_bound_cf B ly S Hp _ k p M Hk Hu) as H0.
set (h := hd_skip Hp p) in *. clearbody h.
subst p n.
pose proof (amc_shadow _ _ _ _ _ M) as SH. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (amc_wf _ _ _ _ _ M) as WF.
pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG). rewrite G4 in HD |- *.
unfold ck_n in HD, H0.
pose proof (proj1 G1) as G1lo.
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
assert (RNG : exists lo len, In (lo, len) (fa_poison_ranges ly S) /\ lo mod 64 = 0 /\ len mod 64 = 0 /\ 0 <= lo /\
lo <= ck_base B ly k /\ ck_base B ly k + ck_extent k <= lo + len).
{ destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal). unfold kFreeArrayOffset in Gal.
pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wrc_mapped_al _ _ _ _ _ _ (wfc_classes _ _ _ _ _ WF (prim_class o) ltac:(lia))) as MA.
exists (region_base ly (prim_class o)), (rg_mapped_user (reg S (prim_class o))).
unfold kHighMemBeg, kUserMapSize in *. splits; try lia.
all: try (unfold fa_poison_ranges; apply in_app_iff; left; apply in_flat_map; exists (prim_class o); split; [apply In_zseq; lia | left; reflexivity]).
all: try (apply Z.mod_divide; [lia|]; apply Z.mod_divide in R3 as [q Hq]; [|lia]; exists (q * 1024); lia).
all: try (apply Z.mod_divide; [lia|]; apply Z.mod_divide in MA as [q Hq]; [|lia]; exists (q * 4096); lia).
- destruct GG as (-> & Gp & Gbase & Gext & Gin & Gal & _).
pose proof (secondary_geometry (ck_req k) ltac:(lia) Gp) as (S1 & S2 & S3 & S4 & S5 & S6).
exists (ly_sec ly r), (sec_map_size (ck_req k)). unfold page_aligned, kPage, kHighMemBeg in *. splits; try lia.
all: try (apply Z.mod_divide; [lia|]; apply Z.mod_divide in Gal as [q Hq]; [|lia]; exists (q * 64); lia).
all: try (apply Z.mod_divide; [lia|]; apply Z.mod_divide in S5 as [q Hq]; [|lia]; exists (q * 64); lia).
unfold fa_poison_ranges. apply in_app_iff. right. exact Gin. }
destruct RNG as (lo & len & RIn & Rlo & Rlen & Rlo0 & R1 & R2).
pose proof (wfc_chunks_nodup _ _ _ _ _ WF) as ND.
split.
-
pose proof G3 as G3'. apply Z.mod_divide in G3' as [qb Hqb]; [|lia].
pose proof G6 as G6'. apply Z.mod_divide in G6' as [qr Hqr]; [|lia].
apply Z.mod_divide in Hal as [qh Hqh]; [|lia]. subst h.
unfold block_shadow. splits; [|lia|].
{ apply Z.mod_divide; [lia|]. exists (2 * qb + 2 * qr + qh). lia. }
intros i Hi.
assert (D1 : (req_size (ck_req k) - qh * 8) / 8 = req_size (ck_req k) / 8 - qh).
{ replace (req_size (ck_req k) - qh * 8) with (req_size (ck_req k) + (- qh) * 8) by lia. rewrite Z.div_add by lia. lia. }
assert (D2 : (req_size (ck_req k) - qh * 8) mod 8 = req_size (ck_req k) mod 8).
{ replace (req_size (ck_req k) - qh * 8) with (req_size (ck_req k) + (- qh) * 8) by lia. apply Z.mod_add. lia. }
assert (D3 : (req_size (ck_req k) - qh * 8 + 7) / 8 = (req_size (ck_req k) + 7) / 8 - qh).
{ replace (req_size (ck_req k) - qh * 8 + 7) with (req_size (ck_req k) + 7 + (- qh) * 8) by lia. rewrite Z.div_add by lia. lia. }
rewrite D1, D2. rewrite D3 in Hi.
assert (I8 : 8 * ((req_size (ck_req k) + 7) / 8) <= req_size (ck_req k) + 7) by (apply Z.mul_div_le; lia).
set (g := ck_base B ly k + ck_rz k + qh * 8 + 8 * i).
assert (Eg : shadow_of_addr SHADOW_OFF (ck_base B ly k + ck_rz k + qh * 8) + i = shadow_addr g).
{ unfold shadow_of_addr, shadow_addr. subst g.
replace (ck_base B ly k + ck_rz k + qh * 8) with ((2 * qb + 2 * qr + qh) * 8) by lia.
replace ((2 * qb + 2 * qr + qh) * 8 + 8 * i) with ((2 * qb + 2 * qr + qh + i) * 8) by lia. rewrite !Z.div_mul by lia. lia. }
rewrite Eg.
assert (Hg8 : g mod 8 = 0).
{ subst g. apply Z.mod_divide; [lia|]. exists (2 * qb + 2 * qr + qh + i). lia. }
assert (Hash : ashadow B ly S g = Some (chunk_granule k ((g - ck_base B ly k) / 8))).
{ unfold ashadow. rewrite (find_chunk_at_hit_cf B ly S Hp _ (st_chunks S) k g M (fun x Hx => Hx) ND Hk) by (subst g; lia). reflexivity. }
rewrite (SH g _ Hg8 Hash). rewrite (HD g ltac:(subst g; lia)).
f_equal. unfold chunk_granule. rewrite Hst.
assert (U8 : ck_rz k / 8 = 2 * qr) by (rewrite Hqr; replace (qr * 16) with ((2 * qr) * 8) by lia; apply Z.div_mul; lia).
replace ((g - ck_base B ly k) / 8) with (ck_rz k / 8 + (qh + i)).
2:{ subst g. replace (ck_base B ly k + ck_rz k + qh * 8 + 8 * i - ck_base B ly k) with ((2 * qr + qh + i) * 8) by lia. rewrite Z.div_mul by lia. lia. }
unfold ck_n.
destruct (Z.ltb_spec (ck_rz k / 8 + (qh + i)) (ck_rz k / 8)); [lia|].
destruct (Z.ltb_spec i (req_size (ck_req k) / 8 - qh)) as [Hlt|Hge].
+ replace (ck_rz k / 8 + (qh + i) <? ck_rz k / 8 + req_size (ck_req k) / 8) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
+ replace (ck_rz k / 8 + (qh + i) <? ck_rz k / 8 + req_size (ck_req k) / 8) with false by (symmetry; apply Z.ltb_ge; lia).
pose proof (Z.div_mod (req_size (ck_req k)) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (req_size (ck_req k)) 8 ltac:(lia)) as MB.
assert (EJ : qh + i = req_size (ck_req k) / 8).
{ assert ((req_size (ck_req k) + 7) / 8 < req_size (ck_req k) / 8 + 2); [|lia].
apply Z.div_lt_upper_bound; [lia|]. lia. }
replace (ck_rz k / 8 + (qh + i) =? ck_rz k / 8 + req_size (ck_req k) / 8) with true by (symmetry; apply Z.eqb_eq; lia).
destruct (Z.eqb_spec (req_size (ck_req k) mod 8) 0) as [E0|NE]; cbn [andb negb]; [|reflexivity].
exfalso. assert ((req_size (ck_req k) + 7) / 8 < req_size (ck_req k) / 8 + 1); [|lia]. apply Z.div_lt_upper_bound; [lia|]. lia.
-
intros sa Hs.
destruct (hull_inside lo (lo + len) (ck_base B ly k + ck_rz k) (req_size (ck_req k)) sa Rlo ltac:(rewrite Z.add_mod, Rlo, Rlen by lia; reflexivity) Rlo0
ltac:(lia) ltac:(lia) ltac:(lia) Hs) as (g & Hg8 & Hgr & ->).
destruct (ashadow_total B ly S g lo len RIn ltac:(lia)) as [v Hv]. rewrite (SH g v Hg8 Hv). discriminate.
Qed.

(* The skip is 0 or cf_head, and cf_head is granule-aligned (cf_head_al). *)
Lemma hd_skip_al : forall Hp p, hd_skip Hp p mod 8 = 0.
Proof. intros Hp p. unfold hd_skip. destruct (existsb (Z.eqb p) Hp); [exact cf_head_al | reflexivity]. Qed.

Theorem AR_shadow_law_ok_cf : forall segs B, AR_shadow_law_cf segs B.
Proof.
intros segs B ly S Hp W mem md p n A Hin. exact (AR_shadow_law_ok_cf_al segs B ly S Hp W mem md p n A Hin (hd_skip_al Hp p)).
Qed.
End j.
