(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG0o.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: EV_MAX raised to 11776, as in omx-clap-core/fuzz_manifest's copy of this file; the region facts in the area-bound proof bound rg_mapped_user by kFreeArrayOffset instead of 2 ^ 31, and the proofs unfold kFreeArrayOffset in the primary-chunk bound of cfacts. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/YG0o.v (donor image sha256 c2c7559b29bd), with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0i YO0d YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG03 YG0f YG0v YG0n YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold ASAN_CEIL in H2.
Local Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section g.
Variable B : asyms.
Lemma vis0_zones_aligned : forall ly z, layout_ok ly -> In z (vis0_zones ly) -> fst z mod 8 = 0.
Proof.
intros ly z LO Hz. unfold vis0_zones in Hz. apply in_app_iff in Hz as [Hz|Hz].
- assert (P8 : forall x, YG0f.page_aligned x -> x mod 8 = 0).
{ intros x Hx. unfold YG0f.page_aligned in Hx. apply Z.mod_divide in Hx as [q Hq]; [|lia]. rewrite Hq. replace (q * 4096) with ((q * 512) * 8) by lia. apply Z_mod_mult. }
cbn in Hz. destruct Hz as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; cbn [fst].
+ apply P8, (lo_T_al _ LO). + apply P8, (lo_F_al _ LO). + apply P8, (lo_NB_al _ LO). + apply P8, (lo_SB_al _ LO).
+ exact (lo_C_al _ LO). + apply P8, (lo_D_al _ LO). + apply P8, (lo_Q_al _ LO).
+ pose proof (lo_space_al _ LO) as SA. apply Z.mod_divide in SA as [q Hq]; [|lia]. rewrite Hq. unfold kRegionInfoOff.
replace (q * 65536 + 2 ^ 37) with ((q * 8192 + 2 ^ 34) * 8) by lia. apply Z_mod_mult.
+   rewrite (proj1 (lo_img _ LO)). reflexivity.
- pose proof (lo_extra _ LO) as (_ & EF & _). pose proof (proj1 (Forall_forall _ _) EF z Hz) as (A & _).
unfold YG0f.page_aligned in A. apply Z.mod_divide in A as [q Hq]; [|lia]. rewrite Hq. replace (q * 4096) with ((q * 512) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma shadow_apart_not_vis0 : forall ly x0 len x, layout_ok ly -> x0 mod 8 = 0 ->
(forall z, In z (vis0_zones ly) -> zdisjoint (x0, len) z) ->
x0 <= x < x0 + len -> ~ in_vis0 ly (shadow_addr x).
Proof.
intros ly x0 len x LO A0 DZ Hx IN. unfold in_vis0 in IN. apply Exists_exists in IN as (v & Hv & Hin). unfold in_zr in Hin.
pose proof (proj1 (Forall_forall _ _) (lo_vis0 _ LO) v Hv) as X. apply Exists_exists in X as (z & Hz & [Z1 Z2]).
pose proof (DZ z Hz) as D. pose proof (vis0_zones_aligned ly z LO Hz) as ZA.
apply Z.mod_divide in A0 as [q0 Hq0]; [|lia]. apply Z.mod_divide in ZA as [qz Hqz]; [|lia].
unfold zdisjoint in D. cbn [fst snd] in D. unfold shadow_addr in *.
destruct D as [D|D].
-
assert (x / 8 <= (fst z - 1) / 8) by (apply Z.div_le_mono; lia).
assert ((fst z - 1) / 8 < fst z / 8) by (rewrite Hqz; rewrite Z_div_mult by lia; apply Z.div_lt_upper_bound; lia).
lia.
-
assert ((fst z + snd z - 1) / 8 <= (x0 - 1) / 8) by (apply Z.div_le_mono; lia).
assert ((x0 - 1) / 8 < x0 / 8) by (rewrite Hq0; rewrite Z_div_mult by lia; apply Z.div_lt_upper_bound; lia).
assert (x0 / 8 <= x / 8) by (apply Z.div_le_mono; lia).
lia.
Qed.
Lemma pw_In : forall (l : list (Z * Z)) x y, pairwise zdisjoint l -> In x l -> In y l -> x = y \/ zdisjoint x y.
Proof.
induction l as [|h t IH]; intros x y P Hx Hy; [destruct Hx|]. cbn in P. destruct P as [F P].
destruct Hx as [<-|Hx], Hy as [<-|Hy]; [left; reflexivity | right; exact (proj1 (Forall_forall _ _) F y Hy) | |].
- right. pose proof (proj1 (Forall_forall _ _) F x Hx) as D. unfold zdisjoint in *. lia.
- exact (IH x y P Hx Hy).
Qed.
Lemma region_apart_vis0_zones : forall ly c z, layout_ok ly -> 1 <= c <= 31 -> In z (vis0_zones ly) ->
zdisjoint (region_base ly c, 2 ^ 32) z.
Proof.
intros ly c z LO Hc Hz. pose proof (region_in_prim ly c LO Hc) as (R1 & R2 & R3 & R4 & R5).
pose proof (lo_disj _ LO) as DJ. pose proof (lo_extra _ LO) as (_ & EF & ED). pose proof (lo_ctx _ LO) as CX. pose proof (lo_space_in _ LO) as [S1 S2].
assert (INP : In (ly_prim ly, kPrimResvSize) (static_extents ly)) by (unfold static_extents, owned_extents; cbn; tauto).
assert (SUB : forall y, zdisjoint y (ly_prim ly, kPrimResvSize) \/ zdisjoint (ly_prim ly, kPrimResvSize) y -> zdisjoint (region_base ly c, 2 ^ 32) y).
{ intros y D. unfold zdisjoint in *. cbn [fst snd] in *. lia. }
assert (STA : forall y, In y (static_extents ly) -> y <> (ly_prim ly, kPrimResvSize) -> zdisjoint (region_base ly c, 2 ^ 32) y).
{ intros y Hy Hne. apply SUB. destruct (pw_In _ _ _ DJ INP Hy) as [E|D]; [exfalso; exact (Hne (eq_sym E)) | right; exact D]. }
unfold vis0_zones in Hz. apply in_app_iff in Hz as [Hz|Hz].
- cbn in Hz. destruct Hz as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]].
+ apply STA; [unfold static_extents, owned_extents; cbn; tauto | intros E; pose proof (f_equal snd E) as E2; cbn in E2; unfold kThreadObjSize, kPrimResvSize in E2; lia].
+ apply STA; [unfold static_extents, owned_extents; cbn; tauto | intros E; pose proof (f_equal snd E) as E2; cbn in E2; unfold kFakeStackSize, kPrimResvSize in E2; lia].
+ apply STA; [unfold static_extents, owned_extents; cbn; tauto | intros E; pose proof (f_equal snd E) as E2; cbn in E2; unfold kNodesBlockSize, kPrimResvSize in E2; lia].
+ apply STA; [unfold static_extents, owned_extents; cbn; tauto | intros E; pose proof (f_equal snd E) as E2; cbn in E2; unfold kStoreBlockSize, kPrimResvSize in E2; lia].
+ apply SUB. left. exact CX.
+ apply STA; [unfold static_extents, owned_extents; cbn; tauto | intros E; pose proof (f_equal snd E) as E2; cbn in E2; unfold kPrimResvSize in E2; lia].
+ apply STA; [unfold static_extents, owned_extents; cbn; tauto | intros E; pose proof (f_equal snd E) as E2; cbn in E2; unfold kPtrArrayResv, kPrimResvSize in E2; lia].
+
unfold zdisjoint, region_base. cbn [fst snd]. rewrite region_off_eq by lia. unfold kRegionInfoOff. left. nia.
+
apply STA; [unfold static_extents, owned_extents; cbn; tauto | intros E; pose proof (f_equal snd E) as E2; cbn in E2; pose proof (lo_img _ LO) as (_ & _ & I3 & _); unfold kImgEnd, kImgLo, kPrimResvSize in *; lia].
- apply SUB. destruct (pw_In _ _ _ ED ltac:(apply in_app_iff; left; exact Hz) ltac:(apply in_app_iff; right; exact INP)) as [E|D]; [|left; exact D].
exfalso. pose proof (proj1 (Forall_forall _ _) EF z Hz) as (_ & SZ & _). rewrite E in SZ. cbn [snd] in SZ. unfold kPrimResvSize in SZ. lia.
Qed.
Lemma prim_shadow_not_vis0 : forall ly c x, layout_ok ly -> 1 <= c <= 31 ->
region_base ly c <= x < region_base ly c + 2 ^ 32 -> ~ in_vis0 ly (shadow_addr x).
Proof.
intros ly c x LO Hc Hx. pose proof (region_in_prim ly c LO Hc) as (_ & _ & R3 & _).
apply (shadow_apart_not_vis0 ly (region_base ly c) (2 ^ 32) x LO); [| intros z Hz; exact (region_apart_vis0_zones ly c z LO Hc Hz) | exact Hx].
apply Z.mod_divide in R3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 65536) with ((q * 8192) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma shadow_apart_not_client : forall ly S rd x0 len x, ARm B ly S rd -> x0 mod 8 = 0 -> 0 <= x0 -> x0 + len <= kHighMemEnd ->
zdisjoint (x0, len) (ly_F ly, kFakeStackSize) -> x0 <= x < x0 + len -> ~ aclient_byte B ly S (shadow_addr x).
Proof.
intros ly S rd x0 len x M A0 P0 HI D Hx C.
assert (SB2 : shadow_addr x < kHighMemBeg).
{ assert (DX : x / 8 <= (kHighMemEnd - 1) / 8) by (apply Z.div_le_mono; lia).
unfold shadow_addr, SHADOW_OFF, kHighMemBeg, kHighMemEnd in *. change ((2 ^ 47 - 1) / 8) with 17592186044415 in DX. lia. }
assert (SB1 : SHADOW_OFF <= shadow_addr x) by (unfold shadow_addr; pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)); lia).
destruct C as [(k & Hk & Hst & Hr)|([cid pos] & Hcp & [Hr|Hr])]; cbn [fst snd] in *.
- pose proof (chunk_facts B ly S rd k M Hk) as (G1 & _ & _ & G4 & G5 & _ & G7 & G8 & _). rewrite G4 in Hr. unfold ck_n in Hr.
unfold in_app, kLowShadowBeg, SHADOW_OFF, kHighMemBeg in G1, SB1, SB2. clear - G1 SB1 SB2 Hr G5 G8. lia.
- pose proof (frame_facts B ly S rd cid pos M Hcp) as (Fc & Fp & F1 & F2 & F3 & F4 & F5 & _). unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr. unfold kFakeFramesOff in F4.
unfold in_app, kLowShadowBeg, SHADOW_OFF, kHighMemBeg in F1, SB1, SB2. clear - F1 SB1 SB2 Hr F4 F5 Fc. lia.
- pose proof (frame_facts B ly S rd cid pos M Hcp) as (Fc & Fp & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _). unfold kFakeFramesOff in F4.
unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr. unfold shadow_addr in Hr.
set (fa := ly_F ly + fs_frame_off cid pos) in *.
assert (FA : fa mod 8 = 0).
{ subst fa. unfold YG0f.page_aligned in F3. apply Z.mod_divide in F3 as [q Hq]; [|lia]. apply Z.mod_divide in F6 as [q' Hq']; [|lia].
rewrite Hq, Hq'. replace (q * 4096 + q' * 64) with ((q * 512 + q' * 8) * 8) by lia. apply Z_mod_mult. }
apply Z.mod_divide in FA as [qf Hqf]; [|lia]. apply Z.mod_divide in A0 as [q0 Hq0]; [|lia]. apply Z.mod_divide in F8 as [qb Hqb]; [|lia].
unfold zdisjoint in D. cbn [fst snd] in D. destruct D as [D|D].
+
assert (x / 8 <= (fa - 1) / 8) by (apply Z.div_le_mono; lia).
assert ((fa - 1) / 8 < fa / 8) by (rewrite Hqf; rewrite Z_div_mult by lia; apply Z.div_lt_upper_bound; lia). lia.
+
assert ((fa + fs_frame_bytes cid) / 8 <= x0 / 8) by (apply Z.div_le_mono; lia).
assert (E1 : (fa + fs_frame_bytes cid) / 8 = fa / 8 + fs_frame_bytes cid / 8).
{ rewrite Hqf, Hqb. replace (qf * 8 + qb * 64) with ((qf + qb * 8) * 8) by lia. rewrite !Z_div_mult by lia. replace (qb * 64) with ((qb * 8) * 8) by lia. rewrite Z_div_mult by lia. lia. }
assert (x0 / 8 <= x / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
Lemma prim_shadow_not_client : forall ly S rd c x, ARm B ly S rd -> 1 <= c <= 31 ->
region_base ly c <= x < region_base ly c + 2 ^ 32 -> ~ aclient_byte B ly S (shadow_addr x).
Proof.
intros ly S rd c x M Hc Hx. pose proof (am_layout _ _ _ _ M) as LO. pose proof (region_in_prim ly c LO Hc) as (R1 & R2 & R3 & R4 & R5).
apply (shadow_apart_not_client ly S rd (region_base ly c) (2 ^ 32) x M); [| unfold kHighMemBeg in *; lia | ceil; unfold ASAN_CEIL, kHighMemEnd in *; lia | | exact Hx].
- apply Z.mod_divide in R3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 65536) with ((q * 8192) * 8) by lia. apply Z_mod_mult.
- pose proof (lo_disj _ LO) as DJ. unfold static_extents, owned_extents in DJ. cbn [pairwise app] in DJ. destruct DJ as [DP _].
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PF _].
unfold zdisjoint in PF |- *. cbn [fst snd] in PF |- *. lia.
Qed.
Lemma aclient_band_same_frames : forall ly S S' rd', ARm B ly S' rd' -> frames S' = frames S ->
forall a, in_band_rw a -> aclient_byte B ly S' a -> aclient_byte B ly S a.
Proof.
intros ly S S' rd' M' FR a Ha [(k & Hk & Hst & Hr)|(cp & Hcp & Hr)].
- exfalso. pose proof (chunk_facts B ly S' rd' k M' Hk) as (G1 & _ & _ & G4 & G5 & _ & G7 & G8 & _). rewrite G4 in Hr. unfold ck_n in Hr.
unfold in_band_rw, in_app, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. clear - G1 Ha Hr G5 G8. lia.
- right. exists cp. rewrite <- FR. exact (conj Hcp Hr).
Qed.
Lemma vis_lists_committed : forall ly S rd, ARm B ly S rd ->
(forall r, In r (as_junk B ly) -> exists z, fst r = ANum z /\ 4096 <= z /\ z + snd r <= kImgEnd) ->
forall r i, In r (ajunk B ly S ++ aareas S ++ aclient S) -> 0 <= i < snd r ->
ly_prim ly <= aeval B ly (fst r) + i < ly_prim ly + kPrimResvSize -> prim_committed_at ly S (aeval B ly (fst r) + i).
Proof.
intros ly S rd M JK r i Hr Hi Hp. pose proof (am_layout _ _ _ _ M) as LO. pose proof (am_wf _ _ _ _ M) as WF. pose proof (am_syms _ _ _ _ M) as SY.
pose proof (lo_space_in _ LO) as [S1 S2]. pose proof (aso_cells _ SY) as AC.
pose proof (lo_high _ LO) as [P1 P2].
pose proof (lo_disj _ LO) as DJ. unfold static_extents, owned_extents in DJ. cbn [pairwise app] in DJ. destruct DJ as [DP _].
apply Forall_cons_iff in DP as [DQ DP]. apply Forall_cons_iff in DP as [DT DP]. apply Forall_cons_iff in DP as [DF DP].
apply Forall_cons_iff in DP as [DNB DP]. apply Forall_cons_iff in DP as [DSB _].
unfold zdisjoint in DQ, DT, DF, DNB, DSB. cbn [fst snd] in DQ, DT, DF, DNB, DSB.
assert (LOW : forall x, x < kHighMemBeg -> ~ (ly_prim ly <= x < ly_prim ly + kPrimResvSize)) by (intros x Hx; unfold in_high, kHighMemBeg in *; lia).
assert (SEC : forall e x, In e (sec_extents ly S) -> fst e <= x < fst e + snd e -> ~ (ly_prim ly <= x < ly_prim ly + kPrimResvSize)).
{ intros e x He Hx. pose proof (pairwise_In zdisjoint _ e (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) He
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia. }
assert (CK : forall k x, In k (st_chunks S) ->
ck_base B ly k - (match ck_beg k with PSec _ _ => kPage | _ => 0 end) <= x < ck_base B ly k + ck_extent k ->
ly_prim ly <= x < ly_prim ly + kPrimResvSize -> prim_committed_at ly S x).
{ intros k x Hk Hx Hxp. pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg k) as [|o|r0 o|c p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal). unfold kFreeArrayOffset in Gal.
right. exists (prim_class o). split; [lia|]. left. unfold in_zr. cbn [fst snd]. lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _). exfalso. apply (SEC _ x Gin); [cbn [fst snd]; unfold kPage in *; lia | exact Hxp]. }
assert (EA : forall e d, match e with ASh _ => False | _ => True end -> aeval B ly (aoff e d) = aeval B ly e + d).
{ intros e d He. apply aeval_aoff. intros e' ->. exact He. }
set (a := aeval B ly (fst r) + i) in *.
rewrite !in_app_iff in Hr. destruct Hr as [Hr|[Hr|Hr]].
-
unfold ajunk in Hr.
destruct Hr as [E|[E|Hr]]; [subst r; cbn [fst snd aeval] in Hi, a; left; unfold in_zr, ly_rinfo; cbn [fst snd]; subst a; lia | subst r; cbn [snd] in Hi; lia |].
rewrite !in_app_iff in Hr.
destruct Hr as [Hr|[Hr|[Hr|[Hr|[Hr|[Hr|[Hr|Hr]]]]]]].
+ apply in_flat_map in Hr as (c & Hc & Hr). apply zseq_In in Hc. unfold region_junk in Hr. cbv zeta in Hr.
left. unfold in_zr, ly_rinfo. cbn [fst snd]. subst a.
destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hi |- *; rewrite EA by exact I; cbn [aeval]; lia.
+ apply in_flat_map in Hr as (c & Hc & Hr). apply zseq_In in Hc. unfold cache_junk in Hr. destruct Hr as [<-|[]]. cbn [fst snd aeval] in Hi, a. exfalso.
assert (N : 0 <= (if st_cache_inited S then Z.of_nat (length (pc_chunks (cache S c))) else 0) <= 16).
{ destruct (st_cache_inited S) eqn:Ei; [|lia]. pose proof (wr_cache _ _ _ _ _ _ (wf_classes _ _ _ _ _ WF c ltac:(lia))) as WC. rewrite Ei in WC.
destruct WC as [_ PL]. pose proof (class_ok c ltac:(lia)) as (_ & _ & _ & K4 & _). lia. }
subst a. unfold t_cache, kThreadObjSize in *. lia.
+ apply in_flat_map in Hr as (k & Hk & Hr). apply (CK k); [exact Hk | | exact Hp].
pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
assert (SP : match sptr_exp (ck_beg k) with ASh _ => False | _ => True end) by (destruct (ck_beg k); exact I).
assert (E0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
unfold chunk_junk in Hr. cbv zeta in Hr. rewrite !in_app_iff in Hr. subst a. unfold ck_n in *.
assert (K0 : match ck_beg k with PSec _ _ => kPage | _ => 0 end >= 0) by (destruct (ck_beg k); unfold kPage; lia).
destruct Hr as [Hr|[[<-|[]]|[Hr|[<-|[]]]]].
* destruct (Z.eqb_spec (ck_rz k) kChunkHeaderSize); [destruct Hr|]. destruct Hr as [<-|[]]. cbn [fst snd] in Hi |- *. rewrite EA by exact SP. rewrite E0. unfold kChunkHeaderSize in *. lia.
* cbn [fst snd] in Hi |- *. rewrite EA by exact SP. rewrite E0. lia.
* destruct (ck_state k); [destruct Hr|]. destruct Hr as [<-|[]]. cbn [fst snd] in Hi |- *. rewrite EA by exact SP. rewrite E0. lia.
* cbn [fst snd] in Hi |- *. rewrite EA by exact SP. rewrite E0. lia.
+   exfalso. unfold sec_junk in Hr. destruct Hr as [<-|[<-|[<-|Hr]]]; cbn [fst snd aeval] in Hi, a.
* apply (LOW a); [subst a; unfold o_sec_sorted, kLowMemEnd, kHighMemBeg in *; lia | exact Hp].
* apply (LOW a); [subst a; unfold o_sec_sorted, o_sec_stats, o_sec_mutex, kLowMemEnd, kHighMemBeg in *; lia | exact Hp].
* pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ WF)) as R1. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv in *. subst a. lia.
* apply in_flat_map in Hr as (k & Hk & Hr). pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & _ & _ & _ & _ & G7 & _ & GG).
destruct (ck_beg k) as [|o|r' o|c p]; try solve [destruct Hr]. destruct Hr as [<-|[]]. cbn [fst snd aeval] in Hi, a.
destruct GG as (-> & Gp & Gbase & Gext & Gin & _). pose proof (secondary_geometry (ck_req k) ltac:(lia) Gp) as (SG1 & _ & _ & SG & _). unfold kMaxSize in SG1.
apply (SEC _ a Gin); [cbn [fst snd]; subst a; unfold kPage in *; lia | exact Hp].
+
unfold quar_junk in Hr. apply in_flat_map in Hr as (b & Hb & Hr). unfold batch_junk in Hr. destruct Hr as [<-|[]]. cbn [fst snd] in Hi, a.
subst a. unfold batch_exp in Hp |- *. rewrite EA in Hp |- * by exact I. cbn [aeval] in Hp |- *.
pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; auto).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL. pose proof (wr_alloc_al _ _ _ _ _ _ CL) as AA. assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2, AA.
apply Z.mod_divide in X2 as [q1 Hq1]; [|lia]. apply Z.mod_divide in AA as [q2 Hq2]; [|lia].
assert (q1 < q2) by nia.
right. exists kBatchClass. split; [unfold kBatchClass; lia|]. left. unfold in_zr, region_base. cbn [fst snd]. subst x. unfold kBatchBytes in *. nia.
+   exfalso. unfold thread_junk in Hr. subst a.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd aeval] in Hi, Hp |- *; unfold t_cache, t_cache_stats, t_stats, t_unwinding, kThreadObjSize in *; lia.
+   exfalso. apply (LOW a); [|exact Hp]. subst a.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd aeval] in Hi, Hp |- *; unfold d_nuniq, kLowMemEnd, kHighMemBeg in *; lia.
+ exfalso. apply (LOW a); [|exact Hp]. subst a. destruct (JK r Hr) as (z & E & Z1 & Z2). rewrite E. cbn [aeval]. unfold kImgEnd, kHighMemBeg in *. lia.
-
unfold aareas in Hr. rewrite !in_app_iff in Hr. destruct Hr as [Hr|[[<-|[]]|[Hr|Hr]]].
+ apply in_flat_map in Hr as (c & Hc & Hr). apply zseq_In in Hc. pose proof (region_in_prim ly c LO ltac:(lia)) as (R1 & R2 & _).
right. exists c. split; [lia|]. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in Hi, a; [left | right]; unfold in_zr, region_base, fa_base; cbn [fst snd]; subst a; lia.
+ exfalso. cbn [fst snd aeval] in Hi, a. pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ WF)) as R1. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv in *. subst a. lia.
+ exfalso. apply in_flat_map in Hr as (k & Hk & Hr). pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & _ & _ & _ & _ & G7 & _ & GG).
destruct (ck_beg k) as [|o|r' o|c p]; try solve [destruct Hr]. destruct Hr as [<-|[]]. cbn [fst snd aeval] in Hi, a.
destruct GG as (-> & Gp & Gbase & Gext & Gin & _). apply (SEC _ a Gin); [cbn [fst snd]; subst a; lia | exact Hp].
+ destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd aeval] in Hi, a.
* exfalso. subst a. unfold kFakeStackSize in *. lia.
* exfalso. subst a. unfold kNodesBlockSize in *. lia.
* exfalso. subst a. unfold kStoreBlockSize in *. lia.
* exfalso. subst a. unfold kThreadObjSize in *. lia.
* left. unfold in_zr, ly_rinfo. cbn [fst snd]. subst a. lia.
* exfalso. apply (LOW a); [|exact Hp]. subst a.
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as [F1 F2]. cbn [fst snd] in F1, F2.
pose proof (shadow_range_below (ly_F ly + kFakeFramesOff) (kFakeStackSize - kFakeFramesOff) ltac:(unfold kFakeFramesOff in *; lia) ltac:(unfold kFakeStackSize, kFakeFramesOff; lia)
ltac:(clear - F1 F2; ceil; unfold ASAN_CEIL, kHighMemEnd, kHighMemBeg, kLowShadowBeg, kFakeFramesOff in *; lia)). lia.
-
unfold aclient in Hr. rewrite !in_app_iff in Hr. destruct Hr as [Hr|[Hr|Hr]].
+ apply in_flat_map in Hr as (k & Hk & Hr). unfold chunk_user in Hr. pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
destruct (ck_state k); [|destruct Hr]. destruct Hr as [<-|[]]. cbn [fst snd] in Hi, a.
apply (CK k); [exact Hk | | exact Hp]. subst a. change (aeval B ly (sptr_exp (ck_user k))) with (sptr_addr B ly (ck_user k)). rewrite G4. unfold ck_n in *.
assert (K0 : match ck_beg k with PSec _ _ => kPage | _ => 0 end >= 0) by (destruct (ck_beg k); unfold kPage; lia). lia.
+ exfalso. apply in_map_iff in Hr as ([cid pos] & <- & Hcp). cbn [fst snd aeval] in Hi, a.
pose proof (frame_facts B ly S rd cid pos M Hcp) as (Fc & Fp & F1 & F2 & F3 & F4 & F5 & _). subst a. unfold kFakeFramesOff in *. lia.
+ exfalso. apply in_map_iff in Hr as ([cid pos] & <- & Hcp). cbn [fst snd aeval] in Hi, a. apply (LOW a); [|exact Hp]. subst a.
pose proof (frame_facts B ly S rd cid pos M Hcp) as (Fc & Fp & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
pose proof (shadow_range_below (ly_F ly + fs_frame_off cid pos) (fs_frame_bytes cid) ltac:(clear - F1 F4 Fc; unfold in_app, kFakeFramesOff in *; lia) ltac:(lia)
ltac:(clear - F1 F4 F5 Fc; ceil; unfold in_app, ASAN_CEIL, kHighMemEnd, kHighMemBeg, kLowShadowBeg, kFakeFramesOff in *; lia)). lia.
Qed.
Lemma vis_lists_u64 : forall ly S rd, ARm B ly S rd ->
(forall r, In r (as_junk B ly) -> exists z, fst r = ANum z /\ 4096 <= z /\ z + snd r <= kImgEnd) ->
forall r i, In r (ajunk B ly S ++ aareas S ++ aclient S) -> 0 <= i < snd r ->
0 <= aeval B ly (fst r) + i < ASAN_CEIL.
Proof.
intros ly S rd M JK r i Hr Hi. pose proof (am_layout _ _ _ _ M) as LO. pose proof (am_wf _ _ _ _ M) as WF. pose proof (am_syms _ _ _ _ M) as SY.
pose proof (lo_space_in _ LO) as [S1 S2]. pose proof (aso_cells _ SY) as AC.
assert (OX : forall e, In e (owned_extents ly) -> 4096 <= fst e /\ fst e + snd e <= ASAN_CEIL).
{ intros e He. pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) e He) as [X1 X2]. ceil. unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
pose proof (OX (ly_prim ly, kPrimResvSize) ltac:(unfold owned_extents; cbn; tauto)) as [P1 P2]. cbn [fst snd] in P1, P2.
pose proof (OX (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as [KT1 KT2]. cbn [fst snd] in KT1, KT2.
pose proof (OX (ly_Q ly, kPtrArrayResv) ltac:(unfold owned_extents; cbn; tauto)) as [KQ1 KQ2]. cbn [fst snd] in KQ1, KQ2.
pose proof (OX (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as [KF1 KF2]. cbn [fst snd] in KF1, KF2.
pose proof (OX (ly_NB ly, kNodesBlockSize) ltac:(unfold owned_extents; cbn; tauto)) as [KN1 KN2]. cbn [fst snd] in KN1, KN2.
pose proof (OX (ly_SB ly, kStoreBlockSize) ltac:(unfold owned_extents; cbn; tauto)) as [KB1 KB2]. cbn [fst snd] in KB1, KB2.
clear OX.
assert (KH : 0 <= SHADOW_OFF /\ 0 < kHighMemBeg /\ kLowMemEnd < kHighMemBeg /\ kImgEnd < kHighMemBeg /\ SHADOW_OFF < kHighMemBeg /\ kHighMemBeg < ASAN_CEIL) by (ceil; unfold kHighMemBeg, kLowMemEnd, kImgEnd, SHADOW_OFF, ASAN_CEIL; lia).
assert (SH0 : forall x, 0 <= x -> SHADOW_OFF <= shadow_addr x) by (intros x Hx; unfold shadow_addr; pose proof (Z.div_pos x 8 Hx ltac:(lia)); lia).
assert (SEC : forall e x, In e (sec_extents ly S) -> fst e <= x < fst e + snd e -> 4096 <= x < ASAN_CEIL).
{ intros e x He Hx. exact (app_addr_below_ceil _ (proj1 (owned_sec_bound B ly S rd x M ltac:(apply Exists_exists; exists e; split; [exact He | exact Hx])))). }
assert (CK : forall k x, In k (st_chunks S) ->
ck_base B ly k - (match ck_beg k with PSec _ _ => kPage | _ => 0 end) <= x < ck_base B ly k + ck_extent k -> 4096 <= x < ASAN_CEIL).
{ intros k x Hk Hx. pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg k) as [|o|r0 o|c p] eqn:Eb; try solve [destruct GG].
- unfold in_app in G1. lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _). apply (SEC _ x Gin). cbn [fst snd]. unfold kPage in *. lia. }
assert (EA : forall e d, match e with ASh _ => False | _ => True end -> aeval B ly (aoff e d) = aeval B ly e + d).
{ intros e d He. apply aeval_aoff. intros e' ->. exact He. }
assert (CL : forall c, 1 <= c <= 31 -> kHighMemBeg <= region_base ly c /\ region_base ly c + 2 ^ 32 <= ASAN_CEIL /\
0 <= rg_mapped_user (reg S c) <= kFreeArrayOffset /\ 0 <= rg_mapped_fa (reg S c) <= kFreeArrayMax).
{ intros c Hc. pose proof (region_in_prim ly c LO Hc) as (_ & _ & _ & R4 & R5). pose proof (wf_classes _ _ _ _ _ WF c Hc) as WC.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S c WF Hc) as MB. unfold kUserMapSize, EV_MAX in MB. unfold kFreeArrayOffset.
pose proof (wr_alloc _ _ _ _ _ _ WC) as M1. pose proof (wr_fa _ _ _ _ _ _ WC) as [M2 _]. pose proof (wr_fa_bound _ _ _ _ _ _ WC). lia. }
set (a := aeval B ly (fst r) + i) in *.
rewrite !in_app_iff in Hr. destruct Hr as [Hr|[Hr|Hr]].
-
unfold ajunk in Hr.
destruct Hr as [E|[E|Hr]]; [subst r; cbn [fst snd aeval] in Hi, a; subst a; unfold ly_rinfo, kRegionInfoOff, kSpaceSize, kPrimResvSize in *; lia | subst r; cbn [snd] in Hi; lia |].
rewrite !in_app_iff in Hr.
destruct Hr as [Hr|[Hr|[Hr|[Hr|[Hr|[Hr|[Hr|Hr]]]]]]].
+ apply in_flat_map in Hr as (c & Hc & Hr). apply zseq_In in Hc. unfold region_junk in Hr. cbv zeta in Hr. subst a.
destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hi |- *; rewrite EA by exact I; cbn [aeval]; unfold ly_rinfo, kRegionInfoOff, kSpaceSize, kPrimResvSize in *; lia.
+ apply in_flat_map in Hr as (c & Hc & Hr). apply zseq_In in Hc. unfold cache_junk in Hr. destruct Hr as [<-|[]]. cbn [fst snd aeval] in Hi, a.
assert (N : 0 <= (if st_cache_inited S then Z.of_nat (length (pc_chunks (cache S c))) else 0) <= 16).
{ destruct (st_cache_inited S) eqn:Ei; [|lia]. pose proof (wr_cache _ _ _ _ _ _ (wf_classes _ _ _ _ _ WF c ltac:(lia))) as WC. rewrite Ei in WC.
destruct WC as [_ PL]. pose proof (class_ok c ltac:(lia)) as (_ & _ & _ & K4 & _). lia. }
subst a. unfold t_cache, kThreadObjSize in *. lia.
+ apply in_flat_map in Hr as (k & Hk & Hr). enough (R : 4096 <= a < ASAN_CEIL) by lia. apply (CK k); [exact Hk |].
pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
assert (SP : match sptr_exp (ck_beg k) with ASh _ => False | _ => True end) by (destruct (ck_beg k); exact I).
assert (E0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
unfold chunk_junk in Hr. cbv zeta in Hr. rewrite !in_app_iff in Hr. subst a. unfold ck_n in *.
assert (K0 : match ck_beg k with PSec _ _ => kPage | _ => 0 end >= 0) by (destruct (ck_beg k); unfold kPage; lia).
destruct Hr as [Hr|[[<-|[]]|[Hr|[<-|[]]]]].
* destruct (Z.eqb_spec (ck_rz k) kChunkHeaderSize); [destruct Hr|]. destruct Hr as [<-|[]]. cbn [fst snd] in Hi |- *. rewrite EA by exact SP. rewrite E0. unfold kChunkHeaderSize in *. lia.
* cbn [fst snd] in Hi |- *. rewrite EA by exact SP. rewrite E0. lia.
* destruct (ck_state k); [destruct Hr|]. destruct Hr as [<-|[]]. cbn [fst snd] in Hi |- *. rewrite EA by exact SP. rewrite E0. lia.
* cbn [fst snd] in Hi |- *. rewrite EA by exact SP. rewrite E0. lia.
+   unfold sec_junk in Hr. destruct Hr as [<-|[<-|[<-|Hr]]]; cbn [fst snd aeval] in Hi, a.
* subst a; ceil; unfold o_sec_sorted, kLowMemEnd, ASAN_CEIL in *; lia.
* subst a; ceil; unfold o_sec_sorted, o_sec_stats, o_sec_mutex, kLowMemEnd, ASAN_CEIL in *; lia.
* pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ WF)) as R1. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv in *. subst a. lia.
* apply in_flat_map in Hr as (k & Hk & Hr). pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & _ & _ & _ & _ & G7 & _ & GG).
destruct (ck_beg k) as [|o|r' o|c p]; try solve [destruct Hr]. destruct Hr as [<-|[]]. cbn [fst snd aeval] in Hi, a.
destruct GG as (-> & Gp & Gbase & Gext & Gin & _). pose proof (secondary_geometry (ck_req k) ltac:(lia) Gp) as (SG1 & _ & _ & SG & _). unfold kMaxSize in SG1.
enough (R : 4096 <= a < ASAN_CEIL) by lia. apply (SEC _ a Gin). cbn [fst snd]; subst a; unfold kPage in *; lia.
+
unfold quar_junk in Hr. apply in_flat_map in Hr as (b & Hb & Hr). unfold batch_junk in Hr. destruct Hr as [<-|[]]. cbn [fst snd] in Hi, a.
subst a. unfold batch_exp in *. rewrite EA by exact I. cbn [aeval].
pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as WC.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; auto).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ WC) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wr_alloc _ _ _ _ _ _ WC) as AL. pose proof (CL kBatchClass ltac:(unfold kBatchClass; lia)) as (R4 & R5 & MB & _).
unfold region_base in R4, R5. subst x. clear X2 INB. unfold kBatchBytes in Hi. unfold kFreeArrayOffset in MB. lia.
+   unfold thread_junk in Hr. subst a.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd aeval] in Hi |- *; unfold t_cache, t_cache_stats, t_stats, t_unwinding, kThreadObjSize in *; lia.
+   subst a.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd aeval] in Hi |- *; unfold d_nuniq, kLowMemEnd in *; lia.
+ subst a. destruct (JK r Hr) as (z & E & Z1 & Z2). rewrite E. cbn [aeval]. lia.
-
unfold aareas in Hr. rewrite !in_app_iff in Hr. destruct Hr as [Hr|[[<-|[]]|[Hr|Hr]]].
+ apply in_flat_map in Hr as (c & Hc & Hr). apply zseq_In in Hc. pose proof (CL c ltac:(lia)) as (R4 & R5 & MB & FB).
destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in Hi, a; unfold region_base in R4, R5; subst a; unfold kFreeArrayOffset, kFreeArrayMax in *; lia.
+ cbn [fst snd aeval] in Hi, a. pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ WF)) as R1. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv in *. subst a. lia.
+ apply in_flat_map in Hr as (k & Hk & Hr). pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & _ & _ & _ & _ & G7 & _ & GG).
destruct (ck_beg k) as [|o|r' o|c p]; try solve [destruct Hr]. destruct Hr as [<-|[]]. cbn [fst snd aeval] in Hi, a.
destruct GG as (-> & Gp & Gbase & Gext & Gin & _). enough (R : 4096 <= a < ASAN_CEIL) by lia. apply (SEC _ a Gin). cbn [fst snd]; subst a; lia.
+ destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd aeval] in Hi, a; subst a.
* lia.
* lia.
* lia.
* lia.
* unfold kRegionInfoOff, kSpaceSize, kPrimResvSize in *. lia.
* pose proof (shadow_range_below (ly_F ly + kFakeFramesOff) (kFakeStackSize - kFakeFramesOff) ltac:(unfold kHighMemBeg, kFakeFramesOff in *; lia) ltac:(unfold kFakeStackSize, kFakeFramesOff; lia)
ltac:(ceil; unfold ASAN_CEIL, kHighMemEnd, kFakeFramesOff in *; lia)).
pose proof (SH0 (ly_F ly + kFakeFramesOff) ltac:(unfold kHighMemBeg, kFakeFramesOff in *; lia)). ceil; unfold ASAN_CEIL, kHighMemBeg in *. lia.
-
unfold aclient in Hr. rewrite !in_app_iff in Hr. destruct Hr as [Hr|[Hr|Hr]].
+ apply in_flat_map in Hr as (k & Hk & Hr). unfold chunk_user in Hr. pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
destruct (ck_state k); [|destruct Hr]. destruct Hr as [<-|[]]. cbn [fst snd] in Hi, a.
enough (R : 4096 <= a < ASAN_CEIL) by lia.
apply (CK k); [exact Hk |]. subst a. change (aeval B ly (sptr_exp (ck_user k))) with (sptr_addr B ly (ck_user k)). rewrite G4. unfold ck_n in *.
assert (K0 : match ck_beg k with PSec _ _ => kPage | _ => 0 end >= 0) by (destruct (ck_beg k); unfold kPage; lia). lia.
+ apply in_map_iff in Hr as ([cid pos] & <- & Hcp). cbn [fst snd aeval] in Hi, a.
pose proof (frame_facts B ly S rd cid pos M Hcp) as (Fc & Fp & F1 & F2 & F3 & F4 & F5 & _). subst a. unfold kFakeFramesOff in *. lia.
+ apply in_map_iff in Hr as ([cid pos] & <- & Hcp). cbn [fst snd aeval] in Hi, a. subst a.
pose proof (frame_facts B ly S rd cid pos M Hcp) as (Fc & Fp & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
pose proof (shadow_range_below (ly_F ly + fs_frame_off cid pos) (fs_frame_bytes cid) ltac:(unfold kHighMemBeg, kFakeFramesOff in *; lia) ltac:(lia)
ltac:(ceil; unfold ASAN_CEIL, kHighMemEnd in *; lia)).
pose proof (SH0 (ly_F ly + fs_frame_off cid pos) ltac:(unfold kHighMemBeg, kFakeFramesOff in *; lia)). ceil; unfold ASAN_CEIL, kHighMemBeg in *. lia.
Qed.
End g.
End f.
