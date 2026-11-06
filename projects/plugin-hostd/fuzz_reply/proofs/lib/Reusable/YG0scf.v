(* CARRIED from commit 0deb5310273b0d538ec2a1697f391a1c8ad21c34,
   proofs/cgif/cgif_file_fuzzer/lib/YG0scf.v, sha256 fd117c002b49744cd2087f7d73e2d7546345e4806328c38dafdf1410196b3e15 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
*)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Taken by path from a working branch a0fed4266a1b, provisional. *)
(* Modified by Theorem Labs, 2026-10: module paths changed from fuzz_preset lib.Reusable to cgif_file_fuzzer lib; the text is otherwise unchanged. *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), cgif's YG0s.v re-proved over
   the fresh record ARmcf / ARcf (YG0ncf.v). cgif's YG0s.v is NOT edited; its lemmas that name neither ARm,
   AR, Wf / WfP nor ALedger are imported from it and used as they stand.
   Every lemma here is cgif's name + `_cf`, with cgif's statement under the substitutions ARm B ly S rd ->
   ARmcf B ly S Hp rd, AR segs B ly S W mem md -> ARcf segs B ly S Hp W mem md, WfP -> WfP_cf,
   ALedger -> ALedger_cf, abudget -> abudget_cf. Changed beyond those substitutions:
     - cfacts_cf: `ck_req k < MALLOC_MAX` -> `< cf_malloc_max` (chunk_ok_cf) and the class bound
       `rg_mapped_user <= 2 ^ 31` -> `<= kFreeArrayOffset` (wrc_mapped_bound, YG01cf.v).
     - am_noholes_cf: `rg_holes (reg S c) = []` -> every hole is the sentinel (EXH_HOLE, 0) (wrc_holes).
   Added, cf forms of cgif helpers outside YG0s.v that the proofs here need: prim_chunk_off_cf (YG07.v:155,
   `< 2 ^ 31` -> `< kFreeArrayOffset`), ARmcf_ext (YG0n.v:508) and AR_wle_cf (YG0n.v:526).
   The shadow law (YG0s.v:771-) is NOT here: AR_shadow_law_ok_cf is in YG0sshcf.v. No address. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := let H := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.

(* ---------------------------------------------------------------------------- *)
(* cf forms of cgif helpers that live outside YG0s.v.                            *)
(* YG07.v:155, with the class window re-based on wrc_mapped_bound.               *)
Lemma prim_chunk_off_cf : forall U pp cc bb s k off, WfP_cf U pp cc bb s -> In k (st_chunks s) -> ck_beg k = PPrim off ->
let c := prim_class off in
1 <= c <= 30 /\ c = chunk_class (ck_req k) /\ from_primary (ck_req k) = true /\ 0 <= ck_req k /\
0 <= off - region_off c < kFreeArrayOffset /\ (off - region_off c) mod class_size c = 0.
Proof.
intros U pp cc bb s k off W Hk Hb c.
pose proof (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ W) k Hk) as [CKn CK]. rewrite Hb in CK. destruct CK as (CKp & CKc & CKo).
pose proof (primary_geometry (ck_req k) ltac:(lia) CKp) as (Gc & _).
assert (Hc : 1 <= c <= 30) by (subst c; rewrite CKc; exact Gc).
pose proof (In_chunk_offs s k off Hk Hb) as Hin. fold c in Hin.
pose proof (wfc_classes _ _ _ _ _ W c ltac:(lia)) as CL.
pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) (off - region_off c)) as E.
specialize (E ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact Hin)).
pose proof (wrc_alloc _ _ _ _ _ _ CL). pose proof (mapped_bound_cf U pp cc bb s c W ltac:(lia)).
subst c. destruct E as [E1 E2]. splits; try lia; try assumption.
Qed.

(* Printf's two cells (field round 3) under a reader that only adds bytes. *)
Lemma pf_cells_cf_ext : forall B ly rd rd', rd_ext rd rd' -> pf_cells_cf B ly rd -> pf_cells_cf B ly rd'.
Proof.
intros B ly rd rd' Hx [T P].
assert (C1 : forall c, cell_holds B ly rd c -> cell_holds B ly rd' c).
{ intros c Hc. assert (F1 : Forall (cell_holds B ly rd) [c]) by (constructor; [exact Hc | constructor]).
  pose proof (Forall_cell_holds_ext B ly rd rd' [c] Hx F1) as F2. inversion F2; assumption. }
exact (conj (C1 _ T) (C1 _ P)).
Qed.

(* YG0n.v:508. *)
Lemma ARmcf_ext : forall B ly S Hp rd rd', rd_ext rd rd' -> ARmcf B ly S Hp rd -> ARmcf B ly S Hp rd'.
Proof.
intros B ly S HG rd rd' Hx M.
destruct M as [Xwf Xuni Xsyms Xlay Xplaced Xconst Xcowned Xcells Xfa Xflags Xdepot Xshadow Xzsh Xjunk Xareas Xclient Xzero Xtsd Xsimg Xhp Xxs Xexh Xerr Xown Xpf Xpfo].
assert (C1 : forall c, cell_holds B ly rd c -> cell_holds B ly rd' c).
{ intros c Hc. assert (F1 : Forall (cell_holds B ly rd) [c]) by (constructor; [exact Hc | constructor]).
  pose proof (Forall_cell_holds_ext B ly rd rd' [c] Hx F1) as F2. inversion F2; assumption. }
constructor; try assumption.
- eapply Forall_cell_holds_ext; eassumption.
- eapply Forall_cell_holds_ext; eassumption.
- intros c i v Hc Hi Hv k Hk. apply Hx. exact (Xfa c i v Hc Hi Hv k Hk).
- intros cid pos Hc Hq. apply Hx. exact (Xflags cid pos Hc Hq).
- destruct Xdepot as (heads & links & D1 & D2 & D3). exists heads, links. split; [|split; [|exact D3]].
+ intros b Hb. destruct (D1 b Hb) as [H1 H2]. split; [exact H1|]. intros k Hk. apply Hx, H2, Hk.
+ intros id Hid. destruct (D2 id Hid) as (H1 & H2 & H3). split; [exact H1|]. split; intros k Hk; apply Hx; auto.
- intros g v Hg Hv. apply Hx. exact (Xshadow g v Hg Hv).
- unfold zshadow_ok in *. apply Forall_forall. intros r Hr.
eapply zero_shadow_ext; [exact Hx|]. exact (proj1 (Forall_forall _ _) Xzsh r Hr).
- eapply Forall_range_vis_ext; eassumption.
- eapply Forall_range_vis_ext; eassumption.
- eapply Forall_range_vis_ext; eassumption.
- apply Forall_forall. intros r Hr i Hi. apply Hx. exact (proj1 (Forall_forall _ _) Xzero r Hr i Hi).
- destruct Xexh as [E1 E2]. split; [|exact E2]. intros c Hc. exact (C1 _ (E1 c Hc)).
- destruct Xerr as (P & Q & D & C & SZ & V & LE & MD). unfold errb_cells_cf.
  split; [exact (C1 _ P)|]. split; [exact (C1 _ Q)|]. split; [exact (C1 _ D)|]. split; [exact (C1 _ C)|].
  split; [exact (C1 _ SZ)|]. split; [|exact (conj LE MD)].
  intros a Ha. pose proof (V a Ha) as Va. destruct (rd a) as [v|] eqn:E; [|contradiction].
  rewrite (Hx a v E). discriminate.
- exact (pf_cells_cf_ext B ly rd rd' Hx Xpf).
Qed.

Section m.
Variable segs : list Segment.
Variable B : asyms.

(* YG0n.v:526; the band (abudget_ok_cf's third conjunct) passes by hsub (cls1_band_vis_hsub_cf). *)
Lemma AR_wle_cf : forall ly S Hp W W' mem md,
ARcf segs B ly S Hp W mem md -> wle W W' -> (forall i, In i (w_A W) -> In i (w_A W')) -> A_bytes (w_A W') <= abudget_cf S ->
ARcf segs B ly S Hp W' mem md.
Proof.
intros ly S HG W W' mem md (M & L & (_ & PIN & BAND) & MW & HS) Hs HI Hb.
split; [|split; [exact L | split; [exact (conj Hb (conj (asecA_transfer ly ly S S _ _ PIN (fun e He => He) HI)
(cls1_band_vis_hsub_cf ly _ _ Hs BAND))) |
split; [exact MW | exact (ahs_hsub B ly S _ _ mem Hs HS)]]]].
eapply ARmcf_ext; [|exact M]. apply aview_ext; [apply w_Hoff | exact Hs].
Qed.

(* ---------------------------------------------------------------------------- *)
(* The helpers of YG0s.v, in its order.                                          *)
Lemma sec_extents_len_cf : forall ly S Hp rd, ARmcf B ly S Hp rd -> Forall (fun e => 4096 < snd e) (sec_extents ly S).
Proof.
intros ly S HG rd M. pose proof (wfc_chunks _ _ _ _ _ (amc_wf _ _ _ _ _ M)) as CK. unfold sec_extents.
apply Forall_forall. intros e He. apply in_flat_map in He as (k & Hk & He).
pose proof (proj1 (Forall_forall _ _) CK k Hk) as [Hn C]. destruct (ck_beg k) as [|o|r o|c p]; try destruct He as [<-|[]]; try destruct He.
cbn [snd]. destruct C as (Hfp & _). pose proof (secondary_geometry (ck_req k) ltac:(lia) Hfp) as (G1 & G2 & G3 & G4 & _).
pose proof (req_size_bounds (ck_req k) ltac:(lia)). unfold kPage, kSecRz in *. lia.
Qed.
Lemma owned_shadow_ranges_cf : forall ly S Hp rd, ARmcf B ly S Hp rd ->
Forall (fun r => 0 <= fst r /\ 0 <= snd r /\ fst r + snd r <= kHighMemEnd) (static_extents ly ++ sec_extents ly S ++ zero_shadow_ranges B ly ++ as_owned_static B ++ [hm_zone; lm_zone]).
Proof.
intros ly S HG rd M. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (amc_placed _ _ _ _ _ M) as [PL _]. pose proof (amc_syms _ _ _ _ _ M) as SY.
pose proof (lo_top _ LO) as TOP. pose proof (lo_app _ LO) as HI. pose proof (lo_img _ LO) as IMG. pose proof ASAN_CEIL_range as [CR _].
unfold kHighMemEnd, kHighMemBeg, kLowMemEnd, kImgLo, kImgEnd in *.
apply Forall_app. split; [|apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split; [|constructor; [unfold hm_zone; cbn; unfold kHighMemBeg, kHighMemEnd; lia | constructor; [unfold lm_zone; cbn; unfold kLowMemEnd, kHighMemEnd; lia | constructor]]]]]].
- unfold static_extents. apply Forall_app. split.
+ apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) HI e He) as [H1 H2].
assert (Hs : 0 <= snd e).
{ unfold owned_extents in He. unfold kPrimResvSize, kPtrArrayResv, kThreadObjSize, kFakeStackSize, kNodesBlockSize, kStoreBlockSize in He.
repeat (destruct He as [<-|He]; [cbn; lia|]). destruct He. }
unfold kLowShadowBeg, kHighMemBeg in H2. lia.
+ constructor; [cbn; lia | constructor; [cbn [fst snd]; unfold page_aligned in IMG; lia | constructor]].
- apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) PL e He) as (_ & [H1 H2] & H3).
pose proof (proj1 (Forall_forall _ _) (sec_extents_len_cf ly S HG rd M) e He) as H4. cbv beta in H4. unfold kLowShadowBeg, kHighMemBeg in *. lia.
- unfold zero_shadow_ranges. constructor; [cbn; lia|]. eapply Forall_impl; [|exact (aso_zshadow _ SY)]. cbv beta. intros r Hr. unfold kLowMemEnd in Hr. lia.
- eapply Forall_impl; [|exact (aso_static _ SY)]. cbv beta. intros r Hr. unfold kImgEnd in Hr. lia.
Qed.
Lemma owned_sec_bound_cf : forall ly S Hp rd a, ARmcf B ly S Hp rd -> Exists (in_zr a) (sec_extents ly S) ->
app_addr a /\ ~ (ly_stk_lo ly <= a < ly_stk_hi ly) /\ ~ in_zr a (ly_img ly).
Proof.
intros ly S HG rd a M H. apply Exists_exists in H as (e & He & [H1 H2]). pose proof (amc_placed _ _ _ _ _ M) as [PL PD].
pose proof (proj1 (Forall_forall _ _) PL e He) as (_ & K & K3).
pose proof (pairwise_In zdisjoint _ e (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) (sec_extents ly S) (static_extents ly) eq_refl PD He
ltac:(unfold static_extents; apply in_app_iff; right; left; reflexivity)) as D.
pose proof (pairwise_In zdisjoint _ e (ly_img ly) (sec_extents ly S) (static_extents ly) eq_refl PD He
ltac:(unfold static_extents; apply in_app_iff; right; right; left; reflexivity)) as D2.
unfold zdisjoint, in_zr in *. cbn [fst snd] in D. split; [exact (in_app_addr _ _ _ K (conj H1 H2)) | lia].
Qed.
Lemma owned_shadow_bound_cf : forall ly S Hp rd a, ARmcf B ly S Hp rd ->
Exists (fun r => in_zr a (shadow_addr (fst r), (snd r + 7) / 8)) (static_extents ly ++ sec_extents ly S ++ zero_shadow_ranges B ly ++ as_owned_static B ++ [hm_zone; lm_zone]) ->
SHADOW_OFF <= a < kHighMemBeg.
Proof.
intros ly S HG rd a M H. apply Exists_exists in H as (r & Hr & [H1 H2]). cbn [fst snd] in H1, H2.
pose proof (proj1 (Forall_forall _ _) (owned_shadow_ranges_cf ly S HG rd M) r Hr) as (K1 & K2 & K3).
pose proof (shadow_addr_bounds (fst r) K1) as [P1 _].
unfold shadow_addr, SHADOW_OFF, kHighMemEnd, kHighMemBeg in *.
assert (fst r / 8 + (snd r + 7) / 8 <= 17592186044416); [|lia].
assert (L : (fst r + snd r + 7) / 8 <= 140737488355335 / 8) by (apply Z.div_le_mono; lia).
change (140737488355335 / 8) with 17592186044416 in L.
assert (fst r / 8 + (snd r + 7) / 8 <= (fst r + snd r + 7) / 8); [|lia].
apply Z.div_le_lower_bound; [lia|].
pose proof (Z.mul_div_le (fst r) 8 ltac:(lia)). pose proof (Z.mul_div_le (snd r + 7) 8 ltac:(lia)). lia.
Qed.
(* CHANGED beyond the substitutions: cgif's `rg_holes (reg S c) = []` is false here, since a cf class may
   carry the one sentinel hole (EXH_HOLE, 0) (wrc_holes, YG01cf.v). *)
Lemma am_noholes_cf : forall ly S Hp rd c, ARmcf B ly S Hp rd -> 1 <= c <= 31 ->
Forall (fun h => h = (EXH_HOLE, 0)) (rg_holes (reg S c)).
Proof. intros ly S HG rd c M Hc. exact (proj1 (wrc_holes _ _ _ _ _ _ (wfc_classes _ _ _ _ _ (amc_wf _ _ _ _ _ M) c Hc))). Qed.
(* The sentinel has length 0, so it covers no address and the cgif statement stands. *)
Lemma wf_no_prim_hole_cf : forall U pp cc bb s ly a, WfP_cf U pp cc bb s -> ~ prim_hole_at ly s a.
Proof.
intros U pp cc bb s ly a W (c & h & Hc & Hin & Hz).
pose proof (proj1 (Forall_forall _ _) (proj1 (wrc_holes _ _ _ _ _ _ (wfc_classes _ _ _ _ _ W c Hc))) h Hin) as Eh.
cbv beta in Eh. subst h. unfold in_zr in Hz. cbn [fst snd] in Hz. lia.
Qed.
Lemma am_no_prim_hole_cf : forall ly S Hp rd a, ARmcf B ly S Hp rd -> ~ prim_hole_at ly S a.
Proof. intros ly S HG rd a M. exact (wf_no_prim_hole_cf _ _ _ _ _ ly a (amc_wf _ _ _ _ _ M)). Qed.
Lemma al_prim_covered_cf : forall ly S Hp rd md a, ARmcf B ly S Hp rd -> ALedger_cf segs ly S md -> ly_prim ly <= a < ly_prim ly + kPrimResvSize ->
exists e, In e (vm_maps (m_vmmaps md)) /\ bv_unsigned (fst e) <= a < bv_unsigned (fst e) + bv_unsigned (snd e).
Proof.
intros ly S HG rd md a M L Ha. destruct (alc_prim _ _ _ _ L) as (pieces & (_ & _ & COV) & PCS).
pose proof (proj2 (COV a Ha) (am_no_prim_hole_cf ly S HG rd a M)) as Hx.
apply Exists_exists in Hx as (q & Hq & HQ). destruct (proj1 (PCS q) Hq) as (Hin & Hpos & Hlo & Hhi).
pose proof (lo_high _ (amc_layout _ _ _ _ _ M)) as [K1 K2].
cbn [fst snd] in K1, K2.
exists (wiv q). split; [exact Hin|]. unfold wiv, w64. cbn [fst snd]. destruct HQ as [Q1 Q2].
rewrite !Z_to_bv_unsigned, !bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); ceil; unfold in_high, kPrimResvSize, ASAN_CEIL, kHighMemBeg in *; lia). lia.
Qed.
(* CHANGED beyond the substitutions: the request bound is chunk_ok_cf's cf_malloc_max, and the class bound is
   wrc_mapped_bound's kFreeArrayOffset (3.5 GiB, still below a region's 2 ^ 32), not cgif's 2 ^ 31. The
   conjuncts are cgif's, in cgif's order, so cgif's destruct patterns carry over. *)
Definition cfacts_cf (ly : alayout) (S : astate) (k : chunk) : Prop :=
in_app (ck_base B ly k) (ck_extent k) /\ ck_base B ly k + ck_extent k <= ASAN_CEIL /\ ck_base B ly k mod 16 = 0 /\
sptr_addr B ly (ck_user k) = ck_base B ly k + ck_rz k /\ 16 <= ck_rz k <= 2048 /\ ck_rz k mod 16 = 0 /\
0 <= ck_req k < cf_malloc_max /\ ck_rz k + req_size (ck_req k) <= ck_extent k /\
match ck_beg k with
| PPrim off => let c := prim_class off in let x := off - region_off c in
1 <= c <= 30 /\ from_primary (ck_req k) = true /\ chunk_class (ck_req k) = c /\ ck_extent k = class_size c /\
ck_base B ly k = region_base ly c + x /\ 0 <= x /\ x mod class_size c = 0 /\ x + class_size c <= rg_alloc_user (reg S c) /\
rg_alloc_user (reg S c) <= rg_mapped_user (reg S c) <= kFreeArrayOffset
| PSec r o => o = kPage /\ from_primary (ck_req k) = false /\ ck_base B ly k = ly_sec ly r + kPage /\
ck_extent k = sec_map_size (ck_req k) - kPage /\ In (ly_sec ly r, sec_map_size (ck_req k)) (sec_extents ly S) /\
page_aligned (ly_sec ly r) /\ (r < length (st_secs S))%nat
| _ => False
end.
Lemma chunk_facts_cf : forall ly S Hp rd k, ARmcf B ly S Hp rd -> In k (st_chunks S) -> cfacts_cf ly S k.
Proof.
intros ly S HG rd k M Hk. pose proof (amc_wf _ _ _ _ _ M) as W. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (amc_placed _ _ _ _ _ M) as [PL PD].
pose proof (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ W) k Hk) as [Hn CK].
pose proof (rz_size_bounds (ck_req k)) as [RZ1 RZ2]. pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
unfold cfacts_cf, ck_base, ck_user, ck_rz.
destruct (ck_beg k) as [|off|r o|c p] eqn:Eb; try solve [destruct CK].
-
destruct CK as (Hfp & Hc & Hoff).
pose proof (prim_chunk_off_cf (as_universe B) 0 0 0 S k off W Hk Eb) as (G1 & G2 & G3 & G4 & G5 & G6). cbv zeta in *.
set (c := prim_class off) in *. set (x := off - region_off c) in *.
pose proof (primary_geometry (ck_req k) ltac:(lia) Hfp) as (P1 & P2 & P3 & P4 & P5). rewrite <- G2 in P2, P3, P4, P5.
pose proof (class_ok c ltac:(lia)) as (K1 & K2 & K3 & _).
pose proof (region_in_prim ly c LO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wfc_classes _ _ _ _ _ W c ltac:(lia)) as CL. pose proof (wrc_alloc _ _ _ _ _ _ CL) as A1. pose proof (wrc_alloc_al _ _ _ _ _ _ CL) as A2.
pose proof (mapped_bound_cf (as_universe B) 0 0 0 S c W ltac:(lia)) as MB. unfold kFreeArrayOffset in *.
assert (XA : 0 <= x < rg_alloc_user (reg S c)).
{ pose proof (In_chunk_offs S k off Hk Eb) as IN. fold c x in IN.
pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) x) as E.
exact (proj1 (E ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact IN))). }
assert (XS : x + class_size c <= rg_alloc_user (reg S c)).
{ pose proof G6 as G6'. apply Z.mod_divide in G6' as [qx Hqx]; [|lia]. pose proof A2 as A2'. apply Z.mod_divide in A2' as [qa Hqa]; [|lia].
assert (Hq : qx < qa) by (apply (Z.mul_lt_mono_pos_r (class_size c)); lia).
pose proof (Z.mul_le_mono_nonneg_r (qx + 1) qa (class_size c) ltac:(lia) ltac:(lia)). lia. }
assert (EXT : ck_extent k = class_size c) by (unfold ck_extent; rewrite Hfp, G2; reflexivity).
assert (BASE : sptr_addr B ly (PPrim off) = region_base ly c + x).
{ unfold sptr_addr, region_base. cbn. subst x. lia. }
rewrite EXT, BASE. cbn [padd]. unfold sptr_addr at 1. cbn [sptr_exp aeval].
assert (XM16 : x mod 16 = 0).
{ apply Z.mod_divide in G6 as [q Hq]; [|lia]. apply Z.mod_divide in K2 as [q' Hq']; [|lia]. apply Z.mod_divide; [lia|]. exists (q * (q' * 2)). lia. }
ceil; unfold ASAN_CEIL, kHighMemBeg, kMaxSize in *.
split. { apply in_high_app. unfold in_high, ASAN_CEIL, kHighMemBeg in *. split; [clear - R4 XA; lia | clear - XS A1 MB R5; lia]. }
splits; try lia; try assumption; try (unfold region_base; subst x; lia).
all: apply Z.mod_divide; [lia|]; apply Z.mod_divide in R3 as [q Hq]; [|lia]; apply Z.mod_divide in XM16 as [q' Hq']; [|lia]; exists (q * 4096 + q'); lia.
-
destruct CK as (Hfp & -> & sm & Hsm & Hlive & Hsz & Hlen).
pose proof (secondary_geometry (ck_req k) ltac:(lia) Hfp) as (S1 & S2 & S3 & S4 & S5 & S6).
assert (INE : In (ly_sec ly r, sec_map_size (ck_req k)) (sec_extents ly S)).
{ unfold sec_extents. apply in_flat_map. exists k. split; [exact Hk|]. rewrite Eb. left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) PL _ INE) as (PA & [I1 I2] & I3). cbn [fst snd] in PA, I1, I2, I3.
assert (EXT : ck_extent k = sec_map_size (ck_req k) - kPage) by (unfold ck_extent; rewrite Hfp; reflexivity).
rewrite EXT. unfold sptr_addr. cbn [sptr_exp aeval padd]. ceil; unfold page_aligned, kPage, kSecRz, ASAN_CEIL, kHighMemBeg in *.
split; [eapply in_app_sub; [exact (conj I1 I2) | lia | lia | lia] |].
assert (I2' : ly_sec ly r + sec_map_size (ck_req k) <= alloc_ceiling) by exact I3.
splits; try lia; try assumption; try reflexivity; try (eapply nth_error_lt; exact Hsm).
all: apply Z.mod_divide; [lia|]; apply Z.mod_divide in PA as [q Hq]; [|lia]; exists (q * 256 + 256); lia.
Qed.
Lemma chunk_apart_cf : forall ly S Hp rd k a, ARmcf B ly S Hp rd -> In k (st_chunks S) ->
ck_base B ly k <= a < ck_base B ly k + ck_extent k -> ~ in_zr a (ly_img ly) /\ ~ (ly_stk_lo ly <= a < ly_stk_hi ly).
Proof.
intros ly S HG rd k a M Hk Ha. pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (chunk_facts_cf ly S HG _ k M Hk) as (G1 & G2 & _ & G4 & G5 & _ & _ & G8 & GG).
destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal). unfold kFreeArrayOffset in Gal.
pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1 & R2 & _).
destruct (owned_extents_bound ly a LO ltac:(apply Exists_exists; exists (ly_prim ly, kPrimResvSize); split; [unfold owned_extents; cbn; tauto | unfold in_zr; cbn [fst snd]; lia])) as (_ & NS & NI). tauto.
- destruct GG as (_ & _ & Gbase & Gext & Gin & _).
destruct (owned_sec_bound_cf ly S HG _ a M ltac:(apply Exists_exists; exists (ly_sec ly r, sec_map_size (ck_req k)); split; [exact Gin | unfold in_zr; cbn [fst snd]; unfold kPage in *; lia])) as (_ & NS & NI). tauto.
Qed.
Lemma chunks_disjoint_cf : forall ly S Hp rd k1 k2, ARmcf B ly S Hp rd -> In k1 (st_chunks S) -> In k2 (st_chunks S) -> ck_beg k1 <> ck_beg k2 ->
zdisjoint (ck_base B ly k1, ck_extent k1) (ck_base B ly k2, ck_extent k2).
Proof.
intros ly S HG rd k1 k2 M H1 H2 Hne.
pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (amc_placed _ _ _ _ _ M) as [PL PD]. pose proof (amc_wf _ _ _ _ _ M) as W.
pose proof (chunk_facts_cf ly S HG rd k1 M H1) as F1. pose proof (chunk_facts_cf ly S HG rd k2 M H2) as F2.
unfold cfacts_cf in F1, F2.
destruct F1 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & C1). destruct F2 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & C2).
assert (PRIMSEC : forall ka kb oa rb ob, In ka (st_chunks S) -> In kb (st_chunks S) -> ck_beg ka = PPrim oa -> ck_beg kb = PSec rb ob ->
cfacts_cf ly S ka -> cfacts_cf ly S kb -> zdisjoint (ck_base B ly ka, ck_extent ka) (ck_base B ly kb, ck_extent kb)).
{ intros ka kb oa rb ob Ha Hb Ea Eb (X1 & X2 & _ & _ & _ & _ & _ & _ & Xa) (Y1 & Y2 & _ & _ & _ & _ & _ & _ & Yb). rewrite Ea in Xa. rewrite Eb in Yb.
cbv zeta in Xa. destruct Xa as (Xc & _ & _ & Xext & Xbase & Xx & _ & Xxs & Xal). destruct Yb as (_ & _ & Ybase & Yext & Yin & _). unfold kFreeArrayOffset in Xal.
pose proof (region_in_prim ly (prim_class oa) LO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (pairwise_In zdisjoint _ (ly_sec ly rb, sec_map_size (ck_req kb)) (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly)
eq_refl PD Yin ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
unfold zdisjoint in D |- *. cbn [fst snd] in D |- *. unfold kPage in *. lia. }
destruct (ck_beg k1) as [|o1|r1 q1|c1 p1] eqn:E1; try solve [destruct C1]; destruct (ck_beg k2) as [|o2|r2 q2|c2 p2] eqn:E2; try solve [destruct C2].
-
cbv zeta in C1, C2. destruct C1 as (Xc & _ & _ & Xext & Xbase & Xx & Xxm & Xxs & Xal). destruct C2 as (Yc & _ & _ & Yext & Ybase & Yx & Yxm & Yxs & Yal). unfold kFreeArrayOffset in Xal, Yal.
rewrite Xext, Yext, Xbase, Ybase. unfold zdisjoint. cbn [fst snd].
destruct (Z.eq_dec (prim_class o1) (prim_class o2)) as [Ec|Hc].
+ rewrite <- Ec in *. set (c := prim_class o1) in *. set (x1 := o1 - region_off c) in *. set (x2 := o2 - region_off c) in *.
pose proof (class_ok c ltac:(lia)) as (K1 & _).
assert (x1 <> x2) by (intros E; apply Hne; f_equal; subst x1 x2; lia).
pose proof Xxm as D1. apply Z.mod_divide in D1 as [q1 Hq1]; [|lia]. pose proof Yxm as D2. apply Z.mod_divide in D2 as [q2 Hq2]; [|lia].
assert (q1 <> q2) by (intros E; subst; lia).
destruct (Z.lt_ge_cases q1 q2).
* pose proof (Z.mul_le_mono_nonneg_r (q1 + 1) q2 (class_size c) ltac:(lia) ltac:(lia)). lia.
* pose proof (Z.mul_le_mono_nonneg_r (q2 + 1) q1 (class_size c) ltac:(lia) ltac:(lia)). lia.
+ pose proof (region_in_prim ly (prim_class o1) LO ltac:(lia)) as (R1 & R2 & _). pose proof (region_in_prim ly (prim_class o2) LO ltac:(lia)) as (R1' & R2' & _).
unfold region_base in *. rewrite !region_off_eq in * by lia.
destruct (Z.lt_ge_cases (prim_class o1) (prim_class o2)).
* pose proof (Z.mul_le_mono_nonneg_r (prim_class o1 + 1) (prim_class o2) (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
* pose proof (Z.mul_le_mono_nonneg_r (prim_class o2 + 1) (prim_class o1) (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
- exact (PRIMSEC k1 k2 o1 r2 q2 H1 H2 E1 E2 (chunk_facts_cf ly S HG rd k1 M H1) (chunk_facts_cf ly S HG rd k2 M H2)).
- apply zdisjoint_sym. exact (PRIMSEC k2 k1 o2 r1 q1 H2 H1 E2 E1 (chunk_facts_cf ly S HG rd k2 M H2) (chunk_facts_cf ly S HG rd k1 M H1)).
-
destruct C1 as (-> & _ & Xbase & Xext & Xin & _). destruct C2 as (-> & _ & Ybase & Yext & Yin & _).
rewrite Xbase, Ybase, Xext, Yext.
destruct (In_split_beg _ _ H1 (wfc_chunks_nodup _ _ _ _ _ W)) as (l1 & l2 & E & N1 & N2).
assert (E1in : In (ly_sec ly r1, sec_map_size (ck_req k1)) (sec_extents ly (set_chunks [k1] S))).
{ unfold sec_extents. cbn. rewrite E1. left. reflexivity. }
assert (H2' : In k2 l1 \/ In k2 l2).
{ rewrite E in H2. apply in_app_iff in H2 as [?|[E12|?]]; [left; assumption | exfalso; subst k2; apply Hne; congruence | right; assumption]. }
pose proof (sec_extents_split ly S l1 k1 l2 E) as SE. rewrite SE in PD.
assert (D : zdisjoint (ly_sec ly r1, sec_map_size (ck_req k1)) (ly_sec ly r2, sec_map_size (ck_req k2))).
{ destruct H2' as [H2'|H2'].
- apply zdisjoint_sym. rewrite <- !app_assoc in PD.
eapply (pairwise_In zdisjoint _ _ _ (sec_extents ly (set_chunks l1 S))); [reflexivity | exact PD | | apply in_app_iff; left; exact E1in].
unfold sec_extents. apply in_flat_map. exists k2. split; [exact H2'|]. rewrite E2. left. reflexivity.
- rewrite <- !app_assoc in PD. rewrite (app_assoc (sec_extents ly (set_chunks l1 S))) in PD.
eapply (pairwise_In zdisjoint _ _ _ (sec_extents ly (set_chunks l1 S) ++ sec_extents ly (set_chunks [k1] S))); [reflexivity | exact PD | apply in_app_iff; right; exact E1in |].
apply in_app_iff. left. unfold sec_extents. apply in_flat_map. exists k2. split; [exact H2'|]. rewrite E2. left. reflexivity. }
unfold zdisjoint in D |- *. cbn [fst snd] in D |- *. unfold kPage. lia.
Qed.
Lemma frame_facts_cf : forall ly S Hp rd cid pos, ARmcf B ly S Hp rd -> In (cid, pos) (frames S) ->
0 <= cid <= 10 /\ 0 <= pos < fs_frames cid /\
in_app (ly_F ly) kFakeStackSize /\ ~ (exists a, in_zr a (ly_F ly, kFakeStackSize) /\ (in_zr a (ly_img ly) \/ ly_stk_lo ly <= a < ly_stk_hi ly)) /\ page_aligned (ly_F ly) /\
kFakeFramesOff + cid * 2 ^ 20 <= fs_frame_off cid pos /\ fs_frame_off cid pos + fs_frame_bytes cid <= kFakeStackSize /\
fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0 /\
kFakeFlagsOff <= fs_flag_off cid pos < kFakeFramesOff.
Proof.
intros ly S HG rd cid pos M Hin. pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (wfs_live _ (wfc_fakestack _ _ _ _ _ (amc_wf _ _ _ _ _ M))) as LV. unfold frames in Hin.
pose proof (proj1 (Forall_forall _ _) LV _ Hin) as [H1 H2]. cbn [fst snd] in H1, H2.
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as F1. cbn [fst snd] in F1.
pose proof (frame_off_bounds cid pos H1 H2) as (A1 & A2 & A3 & A4 & A5 & A6). pose proof (flag_off_bounds cid pos H1 H2) as A7.
splits; try assumption; try lia; [| exact (lo_F_al _ LO)].
intros (a & Ha & Hbad). destruct (owned_extents_bound ly a LO ltac:(apply Exists_exists; exists (ly_F ly, kFakeStackSize); split; [unfold owned_extents; cbn; tauto | exact Ha])) as (_ & NS & NI). tauto.
Qed.
Lemma aview_present_cf : forall ly S md H mem a, ALedger_cf segs ly S md -> 0 <= a < 2 ^ 64 -> ~ in_zr a (ly_img ly) ->
aview segs H mem a <> None -> apresent H mem a.
Proof.
intros ly S md H mem a L Ha Himg Hv. unfold aview, mbyte, mrestrict in Hv. unfold apresent.
assert (NIMG : seg_rom segs (Z_to_bv 64 a) = None).
{ destruct (seg_rom segs (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
destruct (seg_rom_in_img segs a Ha ltac:(rewrite E; discriminate)) as (sg & Hsg & Hr). pose proof (alc_img _ _ _ _ L sg Hsg). apply Himg. unfold in_zr. lia. }
destruct (H (Z_to_bv 64 a)) eqn:EH; [rewrite NIMG in Hv; exfalso; apply Hv; reflexivity|].
destruct (mem (Z_to_bv 64 a)) as [b|] eqn:EM; [split; [reflexivity | exists b; reflexivity]|].
rewrite NIMG in Hv. exfalso. apply Hv. reflexivity.
Qed.
Lemma chunk_vs_F_cf : forall ly S Hp rd k, ARmcf B ly S Hp rd -> In k (st_chunks S) -> zdisjoint (ck_base B ly k, ck_extent k) (ly_F ly, kFakeStackSize).
Proof.
intros ly S HG rd k M Hk. pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (chunk_facts_cf ly S HG _ k M Hk) as (G1 & G2 & _ & G4 & G5 & _ & _ & G8 & GG).
destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal). unfold kFreeArrayOffset in Gal.
pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1 & R2 & _).
pose proof (pairwise_In zdisjoint (static_extents ly) (ly_prim ly, kPrimResvSize) (ly_F ly, kFakeStackSize) [_] _
ltac:(unfold static_extents, owned_extents; reflexivity) (lo_disj _ LO) (or_introl eq_refl) ltac:(cbn; tauto)) as D.
unfold zdisjoint in D |- *. cbn [fst snd] in D |- *. lia.
- destruct GG as (_ & _ & Gbase & Gext & Gin & _).
pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req k)) (ly_F ly, kFakeStackSize) _ (static_extents ly) eq_refl (proj2 (amc_placed _ _ _ _ _ M)) Gin
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
unfold zdisjoint in D |- *. cbn [fst snd] in D |- *. unfold kPage in *. lia.
Qed.
Lemma blocks_pairwise_cf : forall ly S Hp rd, ARmcf B ly S Hp rd -> pairwise zdisjoint (map (brange B ly) (List.filter is_alloc (st_chunks S))).
Proof.
intros ly S HG rd M.
apply (pairwise_map (fun k1 k2 => ck_beg k1 <> ck_beg k2) zdisjoint (brange B ly)).
- intros x y Hx Hy Hne. apply filter_In in Hx as [Hx _]. apply filter_In in Hy as [Hy _].
pose proof (chunks_disjoint_cf ly S HG rd x y M Hx Hy Hne) as D.
pose proof (chunk_facts_cf ly S HG rd x M Hx) as (_ & _ & _ & X4 & X5 & _ & X7 & X8 & _).
pose proof (chunk_facts_cf ly S HG rd y M Hy) as (_ & _ & _ & Y4 & Y5 & _ & Y7 & Y8 & _).
pose proof (req_size_bounds (ck_req x) ltac:(lia)). pose proof (req_size_bounds (ck_req y) ltac:(lia)).
unfold brange, zdisjoint in *. cbn [fst snd] in *. lia.
- apply (pairwise_of_keys ck_beg). { apply NoDup_map_filter. exact (wfc_chunks_nodup _ _ _ _ _ (amc_wf _ _ _ _ _ M)). }
intros x y _ _ Hne. exact Hne.
Qed.
Lemma frames_pairwise_cf : forall ly S Hp rd, ARmcf B ly S Hp rd -> pairwise zdisjoint (map (frange ly) (frames S)).
Proof.
intros ly S HG rd M. pose proof (wfs_nodup _ (wfc_fakestack _ _ _ _ _ (amc_wf _ _ _ _ _ M))) as ND. unfold frames.
apply (pairwise_map (fun f1 f2 => f1 <> f2) zdisjoint (frange ly)).
- intros [c1 p1] [c2 p2] H1 H2 Hne.
pose proof (frame_facts_cf ly S HG rd c1 p1 M H1) as (A1 & A2 & _). pose proof (frame_facts_cf ly S HG rd c2 p2 M H2) as (B1 & B2 & _).
pose proof (frames_apart c1 p1 c2 p2 A1 A2 B1 B2 Hne) as D. unfold frange, frame_addr, zdisjoint in *. cbn [fst snd] in *. lia.
- apply (pairwise_of_keys (fun f : Z * Z => f)); [rewrite map_id; exact ND|]. intros x y _ _ Hne. exact Hne.
Qed.
Lemma client_byte_not_img_cf : forall ly S Hp rd a, ARmcf B ly S Hp rd -> aclient_byte B ly S a -> ~ in_zr a (ly_img ly).
Proof.
intros ly S HG rd a M C. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (lo_img _ LO) as IMG.
destruct C as [(k & Hk & Hst & Hr)|(cp' & Hcp & Hr)].
- pose proof (chunk_facts_cf ly S HG rd k M Hk) as (G1 & _ & _ & G4 & G5 & _ & G7 & G8 & _). pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
apply (proj1 (chunk_apart_cf ly S HG rd k a M Hk ltac:(rewrite G4 in Hr; unfold ck_n in Hr; lia))).
- destruct cp' as [cid pos]. cbn [fst snd] in Hr. pose proof (frame_facts_cf ly S HG rd cid pos M Hcp) as (C1 & _ & F1 & F2 & _ & P1 & P2 & _).
pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)).
destruct Hr as [Hr|Hr].
+ intros Hi. apply F2. exists a. split; [unfold in_zr, frame_addr, kFakeFramesOff, kFakeStackSize in *; cbn [fst snd] in *; lia | left; exact Hi].
+ unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr. unfold in_app, kFakeFramesOff in *.
pose proof (shadow_addr_bounds (ly_F ly + fs_frame_off cid pos) ltac:(lia)) as [SB _].
unfold SHADOW_OFF, in_zr, kImgLo, kImgEnd, page_aligned in *. cbn [fst snd] in *. lia.
Qed.
Lemma sec_extents_le_cf : forall ly ly' S U pp cc bb, layout_le (length (st_secs S)) ly ly' -> WfP_cf U pp cc bb S ->
sec_extents ly' S = sec_extents ly S.
Proof.
intros ly ly' S U pp cc bb LE W. destruct LE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & ED & EI & E15).
unfold sec_extents. pose proof (wfc_chunks _ _ _ _ _ W) as CK.
induction (st_chunks S) as [|k t IH]; [reflexivity|]. inversion CK as [|k0 t0 [Hn C] CKt]; subst. cbn [flat_map].
rewrite (IH CKt). destruct (ck_beg k) as [|o|r o|c p]; try reflexivity. destruct C as (_ & _ & sm & Hsm & _).
rewrite E15 by (eapply nth_error_lt; exact Hsm). reflexivity.
Qed.
Lemma find_chunk_at_hit_cf : forall ly S Hp rd l k g, ARmcf B ly S Hp rd -> incl l (st_chunks S) -> List.NoDup (map ck_beg l) -> In k l ->
ck_base B ly k <= g < ck_base B ly k + ck_extent k -> find_chunk_at B ly l g = Some k.
Proof.
intros ly S HG rd l k g M. induction l as [|k' t IH]; intros Hincl ND Hk Hg; [destruct Hk|]. cbn [find_chunk_at].
inversion ND as [|b0 l0 Hni ND']; subst.
destruct (andb (ck_base B ly k' <=? g) (g <? ck_base B ly k' + ck_extent k')) eqn:E.
- apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. f_equal.
destruct (sptr_eqb (ck_beg k') (ck_beg k)) eqn:Ebq; [apply sptr_eqb_spec in Ebq as Eb | assert (Nb : ck_beg k' <> ck_beg k) by (intros E'; apply sptr_eqb_spec in E'; congruence)].
+ destruct Hk as [->|Hk]; [reflexivity|]. exfalso. apply Hni. rewrite Eb. apply in_map_iff. exists k. auto.
+ exfalso. pose proof (chunks_disjoint_cf ly S HG rd k' k M (Hincl k' (or_introl eq_refl)) (Hincl k ltac:(exact (or_introl eq_refl) || (destruct Hk as [->|Hk]; [left; reflexivity | right; exact Hk]))) Nb) as D.
unfold zdisjoint in D. cbn [fst snd] in D.
pose proof (chunk_facts_cf ly S HG rd k M (Hincl k ltac:(destruct Hk as [->|Hk]; [left; reflexivity | right; exact Hk]))) as (_ & _ & _ & _ & X5 & _ & X7 & X8 & _).
pose proof (req_size_bounds (ck_req k) ltac:(lia)). lia.
- destruct Hk as [->|Hk].
+ exfalso. apply Bool.andb_false_iff in E as [E|E]; [apply Z.leb_gt in E | apply Z.ltb_ge in E]; lia.
+ apply IH; [intros x Hx; apply Hincl; right; exact Hx | exact ND' | exact Hk | exact Hg].
Qed.

(* ---------------------------------------------------------------------------- *)
(* The twelve non-shadow laws of YG0s.v, over ARcf.                              *)
Theorem AR_wle_law_ok_cf : AR_wle_law_cf segs B.
Proof. intros ly S HG W W' mem md. apply AR_wle_cf. Qed.
Theorem AR_zshadow_law_ok_cf : AR_zshadow_law_cf segs B.
Proof.
intros ly S HG W mem md r (M & _ & _) Hr. exact (proj1 (Forall_forall _ _) (amc_zshadow _ _ _ _ _ M) r Hr).
Qed.
Theorem AR_const_law_ok_cf : AR_const_law_cf segs B.
Proof.
intros ly S HG W mem md (M & _ & _).
pose proof (amc_const _ _ _ _ _ M) as C. pose proof (aso_const_law _ (amc_syms _ _ _ _ _ M) ly) as (I1 & I2 & I3 & I4).
pose proof (asyms_area_bound B (as_shadow_cell B, 8) (amc_syms _ _ _ _ _ M) ltac:(cbn; tauto)) as [A1 A2].
pose proof (asyms_area_bound B (as_uar_cell B, 4) (amc_syms _ _ _ _ _ M) ltac:(cbn; tauto)) as [A3 A4]. cbn [fst snd] in A1, A2, A3, A4.
assert (F := fun c (H : In c (as_const B ly)) => proj1 (Forall_forall _ _) C c H).
unfold SHADOW_OFF, kImgEnd in *. splits.
- eapply rdword_cell; [lia | exact (F _ I1)].
- pose proof (F _ I2) as H2. unfold cell_holds in H2. cbn [c_at c_val c_w z4 c4 aeval] in H2. intros k Hk. exact (H2 k Hk).
- eapply rdword_cell; [lia | exact (F _ I3)].
- eapply rdword_cell; [lia | exact (F _ I4)].
Qed.
Theorem AR_stack_law_ok_cf : AR_stack_law_cf segs B.
Proof.
intros ly S HG W mem md a (M & _ & _) Ha [OW _]. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (lo_top _ LO) as TOP.
destruct OW as [O|[O|[O|[O|O]]]].
- pose proof (owned_static_bound B a (amc_syms _ _ _ _ _ M) O). unfold kImgEnd, kHighMemBeg in *. lia.
- exact (proj1 (proj2 (owned_extents_bound ly a LO O)) Ha).
- apply (proj1 (proj2 (owned_extents_bound ly a LO ltac:(apply Exists_exists; exists (ly_C ly, 256); split; [unfold owned_extents; cbn; tauto | exact O]))) Ha).
- exact (proj1 (proj2 (owned_sec_bound_cf ly S HG _ a M O)) Ha).
- pose proof (owned_shadow_bound_cf ly S HG _ a M O). lia.
Qed.
Theorem AR_owned_low_law_ok_cf : AR_owned_low_law_cf segs B.
Proof.
intros ly S HG W mem md a (M & _ & _) [OW _]. pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof ASAN_CEIL_range as [CR _]. ceil; unfold ASAN_CEIL in CR.
destruct OW as [O|[O|[O|[O|O]]]].
- pose proof (owned_static_bound B a (amc_syms _ _ _ _ _ M) O). unfold kImgEnd in *. lia.
- pose proof (app_addr_below_ceil a (proj1 (owned_extents_bound ly a LO O))). ceil; unfold ASAN_CEIL in *. lia.
- pose proof (app_addr_below_ceil a (proj1 (owned_extents_bound ly a LO ltac:(apply Exists_exists; exists (ly_C ly, 256); split; [unfold owned_extents; cbn; tauto | exact O])))).
ceil; unfold ASAN_CEIL in *. lia.
- pose proof (app_addr_below_ceil a (proj1 (owned_sec_bound_cf ly S HG _ a M O))). ceil; unfold ASAN_CEIL in *. lia.
- pose proof (owned_shadow_bound_cf ly S HG _ a M O). unfold SHADOW_OFF, kHighMemBeg in *. lia.
Qed.
Theorem AR_frames_law_ok_cf : AR_frames_law_cf segs B.
Proof.
intros ly S HG W mem md cid pos (M & L & _) Hin.
pose proof (frame_facts_cf ly S HG _ cid pos M Hin) as (C1 & C2 & F1 & F2 & FA & O1 & O2 & O3 & O4 & O5 & O6).
pose proof (lo_img _ (amc_layout _ _ _ _ _ M)) as IMG.
assert (IA : in_app (ly_F ly + fs_frame_off cid pos) (fs_frame_bytes cid)).
{ eapply in_app_sub; [exact F1 | | |]; unfold kFakeFramesOff, kFakeStackSize in *; pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)); lia. }
ceil; unfold frame_addr, in_app, page_aligned, ASAN_CEIL, kHighMemBeg, kLowShadowBeg, kImgLo, kImgEnd, kFakeFramesOff, kFakeStackSize, kFakeFlagsOff in *.
pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)).
assert (VIS1 : forall i, 0 <= i < fs_frame_bytes cid -> aview segs (w_H W) mem (ly_F ly + fs_frame_off cid pos + i) <> None).
{ intros i Hi. pose proof (proj1 (Forall_forall _ _) (amc_client _ _ _ _ _ M) (AF (fs_frame_off cid pos), fs_frame_bytes cid)) as V.
unfold aclient in V. specialize (V ltac:(apply in_app_iff; right; apply in_app_iff; left; apply in_map_iff; exists (cid, pos); split; [reflexivity | exact Hin])).
exact (V i Hi). }
assert (VIS2 : forall i, 0 <= i < fs_frame_bytes cid / 8 -> aview segs (w_H W) mem (shadow_addr (ly_F ly + fs_frame_off cid pos) + i) <> None).
{ intros i Hi. pose proof (proj1 (Forall_forall _ _) (amc_client _ _ _ _ _ M) (ASh (AF (fs_frame_off cid pos)), fs_frame_bytes cid / 8)) as V.
unfold aclient in V. specialize (V ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_map_iff; exists (cid, pos); split; [reflexivity | exact Hin])).
exact (V i Hi). }
pose proof (shadow_addr_bounds (ly_F ly + fs_frame_off cid pos) ltac:(lia)) as [SB1 SB2]. unfold SHADOW_OFF, kHighMemEnd, kHighMemBeg in SB1, SB2.
assert (NI1 : forall a, ly_F ly + fs_frame_off cid pos <= a < ly_F ly + fs_frame_off cid pos + fs_frame_bytes cid -> ~ in_zr a (ly_img ly)).
{ intros a Ha Hi. apply F2. exists a. split; [unfold in_zr; cbn [fst snd]; lia | left; exact Hi]. }
assert (NI2 : forall a, 2147450880 <= a -> ~ in_zr a (ly_img ly)) by (intros a Ha Hi; unfold in_zr, page_aligned in *; lia).
split; [|split; [exact IA | split]].
- apply Z.mod_divide; [lia|]. apply Z.mod_divide in FA as [q Hq]; [|lia]. apply Z.mod_divide in O3 as [q' Hq']; [|lia]. exists (q * 128 + q' * 2). lia.
- intros a Ha. split.
+ replace a with (ly_F ly + fs_frame_off cid pos + (a - (ly_F ly + fs_frame_off cid pos))) by lia.
eapply aview_present_cf; [exact L | lia | apply NI1; lia | apply VIS1; lia].
+ intros [_ NC]. apply NC. right. exists (cid, pos). split; [exact Hin|]. left. unfold in_zr, frame_addr. cbn [fst snd]. lia.
- intros i Hi. split.
+ eapply aview_present_cf; [exact L | lia | apply NI2; lia | apply VIS2; exact Hi].
+ intros [_ NC]. apply NC. right. exists (cid, pos). split; [exact Hin|]. right. unfold in_zr, frame_addr. cbn [fst snd]. lia.
Qed.
Theorem AR_flag_law_ok_cf : AR_flag_law_cf segs B.
Proof.
intros ly S HG W mem md cid pos (M & L & _) Hin.
pose proof (frame_facts_cf ly S HG _ cid pos M Hin) as (C1 & C2 & F1 & F2 & FA & O1 & O2 & O3 & O4 & O5 & O6).
pose proof (amc_flags _ _ _ _ _ M cid pos C1 C2) as FL.
pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (lo_img _ LO) as IMG.
assert (IA : in_app (ly_F ly + fs_flag_off cid pos) 1).
{ eapply in_app_sub; [exact F1 | | |]; unfold kFakeFramesOff, kFakeFlagsOff, kFakeStackSize in *; lia. }
pose proof (app_addr_below_ceil _ (in_app_addr _ _ (ly_F ly + fs_flag_off cid pos) IA ltac:(lia))) as AC.
assert (NI : ~ in_zr (ly_F ly + fs_flag_off cid pos) (ly_img ly)).
{ intros Hi. apply F2. exists (ly_F ly + fs_flag_off cid pos). split; [unfold in_zr, kFakeFramesOff, kFakeFlagsOff, kFakeStackSize in *; cbn [fst snd]; lia | left; exact Hi]. }
ceil; unfold flag_addr, in_app, kHighMemBeg, kLowShadowBeg, ASAN_CEIL, kImgEnd, kFakeFramesOff, kFakeFlagsOff, kFakeStackSize in *.
split; [|split; [|split; [exact IA | exact (proj2 AC)]]].
- eapply aview_present_cf; [exact L | lia | exact NI | unfold flag_addr in FL; rewrite FL; discriminate].
- split.
+ right. left. apply Exists_exists. exists (ly_F ly, kFakeStackSize). split; [unfold owned_extents; cbn; tauto | unfold in_zr, kFakeStackSize; cbn; lia].
+ intros [(k & Hk & Hst & Hr)|(cp' & Hcp & [Hr|Hr])].
*
pose proof (chunk_facts_cf ly S HG _ k M Hk) as (G1 & G2 & _ & G4 & G5 & _ & _ & G8 & GG).
assert (D : zdisjoint (ck_base B ly k, ck_extent k) (ly_F ly, kFakeStackSize)).
{ destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal). unfold kFreeArrayOffset in Gal.
pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1 & R2 & _).
pose proof (pairwise_In zdisjoint (static_extents ly) (ly_prim ly, kPrimResvSize) (ly_F ly, kFakeStackSize) [_] _
ltac:(unfold static_extents, owned_extents; reflexivity) (lo_disj _ LO) (or_introl eq_refl) ltac:(cbn; tauto)) as D.
unfold zdisjoint in D |- *. cbn [fst snd] in D |- *. lia.
- destruct GG as (_ & _ & Gbase & Gext & Gin & _).
pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req k)) (ly_F ly, kFakeStackSize) _ (static_extents ly) eq_refl (proj2 (amc_placed _ _ _ _ _ M)) Gin
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
unfold zdisjoint in D |- *. cbn [fst snd] in D |- *. unfold kPage in *. lia. }
unfold zdisjoint, kFakeStackSize, ck_n in *. cbn [fst snd] in D. lia.
* destruct cp' as [c2 p2]. cbn [fst snd] in Hr. unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr.
pose proof (frame_facts_cf ly S HG _ c2 p2 M Hcp) as (Q1 & _ & _ & _ & _ & P1 & P2 & _). unfold kFakeFramesOff, kFakeStackSize in P1, P2.
pose proof (Z.mul_nonneg_nonneg c2 (2 ^ 20) ltac:(lia) ltac:(lia)). lia.
* destruct cp' as [c2 p2]. cbn [fst snd] in Hr. unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr.
pose proof (frame_facts_cf ly S HG _ c2 p2 M Hcp) as (Q1 & _ & _ & _ & _ & P1 & P2 & P3 & P4 & _). unfold kFakeFramesOff, kFakeStackSize in P1, P2.
pose proof (Z.mul_nonneg_nonneg c2 (2 ^ 20) ltac:(lia) ltac:(lia)).
pose proof (shadow_range_below (ly_F ly + fs_frame_off c2 p2) (fs_frame_bytes c2) ltac:(lia) ltac:(lia)) as SB.
pose proof (shadow_addr_bounds (ly_F ly + fs_frame_off c2 p2) ltac:(lia)) as [SB0 _].
unfold kHighMemEnd, kHighMemBeg, SHADOW_OFF in SB, SB0. lia.
Qed.
Theorem AR_sep_law_ok_cf : AR_sep_law_cf segs B.
Proof.
intros ly S HG W mem md (M & L & _). split.
- rewrite blocks_ranges_eq. change (fun f : Z * Z => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) with (frange ly).
apply pairwise_app; [eapply blocks_pairwise_cf; exact M | eapply frames_pairwise_cf; exact M |].
intros x y Hx Hy. apply in_map_iff in Hx as (k & <- & Hk). apply filter_In in Hk as [Hk _]. apply in_map_iff in Hy as ([cid pos] & <- & Hf).
pose proof (chunk_vs_F_cf ly S HG _ k M Hk) as D. pose proof (chunk_facts_cf ly S HG _ k M Hk) as (_ & _ & _ & X4 & X5 & _ & X7 & X8 & _).
pose proof (frame_facts_cf ly S HG _ cid pos M Hf) as (Fc & _ & _ & _ & _ & P1 & P2 & _). pose proof (req_size_bounds (ck_req k) ltac:(lia)).
unfold brange, frange, frame_addr, zdisjoint, kFakeFramesOff, kFakeStackSize in *. cbn [fst snd] in *. pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)). lia.
- apply Forall_forall. intros [cid pos] Hf. cbn [fst snd].
pose proof (frame_facts_cf ly S HG _ cid pos M Hf) as (C1 & _ & F1 & F2 & _ & P1 & P2 & _).
ceil; unfold frame_addr, in_app, kHighMemBeg, kLowShadowBeg, ASAN_CEIL, kFakeFramesOff, kFakeStackSize in *.
pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)). lia.
Qed.
Theorem AR_blocks_law_ok_cf : AR_blocks_law_cf segs B.
Proof.
intros ly S HG W mem md p n (M & L & _) Hin. pose proof Hin as Hin0.
apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hr). subst p n.
pose proof (chunk_facts_cf ly S HG _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG). rewrite G4.
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
assert (IA : in_app (ck_base B ly k + ck_rz k) (req_size (ck_req k))) by (eapply in_app_sub; [exact G1 | lia | lia | lia]).
ceil; unfold in_app, kHighMemBeg, kLowShadowBeg, ASAN_CEIL in *.
splits; try lia.
all: try (apply Z.mod_divide; [lia|]; apply Z.mod_divide in G3 as [q Hq]; [|lia]; apply Z.mod_divide in G6 as [q' Hq']; [|lia]; exists (q + q'); lia).
- intros a Ha. split.
+ pose proof (proj1 (Forall_forall _ _) (amc_client _ _ _ _ _ M) (sptr_exp (ck_user k), ck_n k)) as V. unfold aclient in V.
specialize (V ltac:(apply in_app_iff; left; apply in_flat_map; exists k; split; [exact Hk | unfold chunk_user; rewrite Hst; left; reflexivity])).
unfold range_vis in V. cbn [fst snd] in V. fold (sptr_addr B ly (ck_user k)) in V. rewrite G4 in V.
replace a with (ck_base B ly k + ck_rz k + (a - (ck_base B ly k + ck_rz k))) by lia.
destruct (chunk_apart_cf ly S HG _ k (ck_base B ly k + ck_rz k + (a - (ck_base B ly k + ck_rz k))) M Hk ltac:(clear - Ha G5 G8; lia)) as [NI _].
eapply aview_present_cf; [exact L | lia | exact NI | apply V; unfold ck_n; lia].
+ intros [_ NC]. apply NC. left. exists k. rewrite G4. unfold ck_n. auto.
- rewrite blocks_ranges_eq. eapply blocks_pairwise_cf. exact M.
Qed.
Theorem AR_client_img_law_ok_cf : AR_client_img_law_cf segs B.
Proof.
intros ly S HG W mem md a (M & L & _) HC.
assert (NZ : ~ in_zr a (ly_img ly)).
{ destruct HC as [(p & n & Hin & Hr)|[(cid & pos & Hin & Hr)|(cid & pos & Hin & ->)]].
- apply (client_byte_not_img_cf ly S HG _ a M).
apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hn). subst p n. left. exists k. split; [exact Hk|]. split; [exact Hst|].
unfold ck_n. exact Hr.
- apply (client_byte_not_img_cf ly S HG _ a M).
right. exists (cid, pos). split; [exact Hin|]. left. unfold in_zr. cbn [fst snd]. exact Hr.
-
pose proof (frame_facts_cf ly S HG _ cid pos M Hin) as (Fc & Fp & F1 & F2 & _). pose proof (flag_off_bounds cid pos Fc Fp) as FB.
intros IN. apply F2. exists (flag_addr ly cid pos).
split; [unfold in_zr, flag_addr; cbn [fst snd]; unfold kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *; lia | left; exact IN]. }
split; [exact NZ|]. intros (sg & Hsg & Ha). apply NZ. pose proof (alc_img _ _ _ _ L sg Hsg) as [I1 I2]. unfold in_zr. lia.
Qed.
Theorem AR_owned_image_law_ok_cf : AR_owned_image_law_cf segs B.
Proof.
intros ly S HG W mem md a (M & L & _) (sg & Hsg & Ha). pose proof (alc_img _ _ _ _ L sg Hsg) as [I1 I2]. pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (lo_img _ LO) as IMG.
assert (AI : in_zr a (ly_img ly)) by (unfold in_zr; lia).
split.
- intros [[O|[O|[O|[O|O]]]] _]; [exact O | exfalso ..].
+ exact (proj2 (proj2 (owned_extents_bound ly a LO O)) AI).
+ exact (proj2 (proj2 (owned_extents_bound ly a LO ltac:(apply Exists_exists; exists (ly_C ly, 256); split; [unfold owned_extents; cbn; tauto | exact O]))) AI).
+ exact (proj2 (proj2 (owned_sec_bound_cf ly S HG _ a M O)) AI).
+ pose proof (owned_shadow_bound_cf ly S HG _ a M O). unfold SHADOW_OFF, in_zr, kImgLo, kImgEnd, page_aligned in *. cbn [fst snd] in *. lia.
- intros O. split; [left; exact O|]. intros C. exact (client_byte_not_img_cf ly S HG _ a M C AI).
Qed.
Theorem AR_layout_law_ok_cf : AR_layout_law_cf segs B.
Proof.
intros ly S HG W mem md ly' (M & L & _) LE. pose proof (amc_wf _ _ _ _ _ M) as WF.
pose proof LE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & ED & EI & E15).
assert (USR : forall k, In k (st_chunks S) -> sptr_addr B ly' (ck_user k) = sptr_addr B ly (ck_user k)).
{ intros k Hk. apply (sptr_addr_le B ly ly' (length (st_secs S))); [exact LE|].
pose proof (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ WF) k Hk) as [_ C]. unfold ck_user.
destruct (ck_beg k) as [|o|r o|c p]; cbn; try exact I. destruct C as (_ & _ & sm & Hsm & _). eapply nth_error_lt. exact Hsm. }
assert (FR : forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos) by (intros; unfold frame_addr; rewrite E6; reflexivity).
splits.
- unfold ablocks, blocks. rewrite !map_map. apply map_ext_in. intros k Hk. apply filter_In in Hk as [Hk _]. cbn [fst snd]. rewrite (USR k Hk). reflexivity.
- exact FR.
- intros a. unfold aowned, aclient_byte.
rewrite (sec_extents_le_cf ly ly' S _ _ _ _ LE WF).
assert (EO : owned_extents ly' = owned_extents ly) by (unfold owned_extents; rewrite E1, E3, E4, E5, E6, E7, E8, ED; reflexivity).
assert (ES : static_extents ly' = static_extents ly) by (unfold static_extents; rewrite EO, E10, E11, EI; reflexivity).
assert (EZ : zero_shadow_ranges B ly' = zero_shadow_ranges B ly) by (unfold zero_shadow_ranges; rewrite E10, E11; reflexivity).
rewrite EO, ES, EZ, E5.
assert (CB : (exists k, In k (st_chunks S) /\ ck_state k = CAllocated /\ sptr_addr B ly' (ck_user k) <= a < sptr_addr B ly' (ck_user k) + ck_n k) <->
(exists k, In k (st_chunks S) /\ ck_state k = CAllocated /\ sptr_addr B ly (ck_user k) <= a < sptr_addr B ly (ck_user k) + ck_n k)).
{ split; intros (k & Hk & Hs & Hr); exists k; rewrite ?(USR k Hk) in *; auto. }
assert (CF : forall cq, (in_zr a (frame_addr ly' (fst cq) (snd cq), fs_frame_bytes (fst cq)) \/ in_zr a (shadow_addr (frame_addr ly' (fst cq) (snd cq)), fs_frame_bytes (fst cq) / 8)) <->
(in_zr a (frame_addr ly (fst cq) (snd cq), fs_frame_bytes (fst cq)) \/ in_zr a (shadow_addr (frame_addr ly (fst cq) (snd cq)), fs_frame_bytes (fst cq) / 8))).
{ intros cq. rewrite !FR. tauto. }
split; intros [O NC]; (split; [exact O|]); intros C; apply NC; destruct C as [C|(cq & Hcq & C)].
+ left. apply CB. exact C.
+ right. exists cq. split; [exact Hcq|]. apply CF. exact C.
+ left. apply CB. exact C.
+ right. exists cq. split; [exact Hcq|]. apply CF. exact C.
Qed.
End m.
End j.
