(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepVisLcf.v (commit f01d79f3fb5, cf refill round 3; file sha256 25d728052a20) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Theorem Labs, 2026-10-30: the cf twins of cgif's vis_lists_committed (YG0o.v:140) and vis_lists_u64 (YG0o.v:249),
   over the fresh record ARmcf of YG0ncf.v, and visloc_cf, the premise VISLOC of YFkmcf.v:573 in one lemma.
   rule 24: proves no function (kind: invariant lemma: cf twins of vis_lists_u64 / vis_lists_committed).
   Substitutions (YG0qcf.v:7-9): ARm B ly S rd -> ARmcf B ly S Hp rd, am_X -> amc_X, wf_X / wr_X / ws_X ->
   wfc_X / wrc_X / wsc_X, chunk_facts / frame_facts / owned_sec_bound -> their YG0scf _cf forms, and
   ajunk -> ajunk_cf (YG0ncf.v:59, the junk list ARmcf's amc_junk states). Proof changes beyond those:
     - region_junk_cf (YG0ncf.v:45) lists the exhausted byte (R+68,1) before cgif's three region_junk entries,
       so the region-junk case destructs four entries; R+68 lies in the region-info page as the others do.
     - cgif's mapped_user_bound (2 GiB per class) -> mapped_bound_cf (kFreeArrayOffset, YG01cf.v:230); the
       region-window steps unfold kFreeArrayOffset (3,758,096,384 < 2 ^ 32 keeps every step true).
   visloc_cf states VISLOC over YG0n's ajunk exactly as YFkmcf.v:573 does; ajunk_incl_cf (YG0ncf.v:80) carries
   it to ajunk_cf. visloc_jcf is the same over ajunk_cf. The as_junk premise is cgif's (YG0o.v:141), which the
   callers of cgif's lemmas discharge from ts_junk. cgif's files are NOT edited. No address. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0i YO0d YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG03 YG0f YG0v YG0n YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0scf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold ASAN_CEIL in H2.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section g.
Variable B : asyms.
Lemma vis_lists_committed_cf : forall ly S Hp rd, ARmcf B ly S Hp rd ->
(forall r, In r (as_junk B ly) -> exists z, fst r = ANum z /\ 4096 <= z /\ z + snd r <= kImgEnd) ->
forall r i, In r (ajunk_cf B ly S ++ aareas S ++ aclient S) -> 0 <= i < snd r ->
ly_prim ly <= aeval B ly (fst r) + i < ly_prim ly + kPrimResvSize -> prim_committed_at ly S (aeval B ly (fst r) + i).
Proof.
intros ly S HG rd M JK r i Hr Hi Hp. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (amc_syms _ _ _ _ _ M) as SY.
pose proof (lo_space_in _ LO) as [S1 S2]. pose proof (aso_cells _ SY) as AC.
pose proof (lo_high _ LO) as [P1 P2].
pose proof (lo_disj _ LO) as DJ. unfold static_extents, owned_extents in DJ. cbn [pairwise app] in DJ. destruct DJ as [DP _].
apply Forall_cons_iff in DP as [DQ DP]. apply Forall_cons_iff in DP as [DT DP]. apply Forall_cons_iff in DP as [DF DP].
apply Forall_cons_iff in DP as [DNB DP]. apply Forall_cons_iff in DP as [DSB _].
unfold zdisjoint in DQ, DT, DF, DNB, DSB. cbn [fst snd] in DQ, DT, DF, DNB, DSB.
assert (LOW : forall x, x < kHighMemBeg -> ~ (ly_prim ly <= x < ly_prim ly + kPrimResvSize)) by (intros x Hx; unfold in_high, kHighMemBeg in *; lia).
assert (SEC : forall e x, In e (sec_extents ly S) -> fst e <= x < fst e + snd e -> ~ (ly_prim ly <= x < ly_prim ly + kPrimResvSize)).
{ intros e x He Hx. pose proof (pairwise_In zdisjoint _ e (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl (proj2 (amc_placed _ _ _ _ _ M)) He
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia. }
assert (CK : forall k x, In k (st_chunks S) ->
ck_base B ly k - (match ck_beg k with PSec _ _ => kPage | _ => 0 end) <= x < ck_base B ly k + ck_extent k ->
ly_prim ly <= x < ly_prim ly + kPrimResvSize -> prim_committed_at ly S x).
{ intros k x Hk Hx Hxp. pose proof (chunk_facts_cf B ly S HG rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg k) as [|o|r0 o|c p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal).
right. exists (prim_class o). split; [lia|]. left. unfold in_zr. cbn [fst snd]. lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _). exfalso. apply (SEC _ x Gin); [cbn [fst snd]; unfold kPage in *; lia | exact Hxp]. }
assert (EA : forall e d, match e with ASh _ => False | _ => True end -> aeval B ly (aoff e d) = aeval B ly e + d).
{ intros e d He. apply aeval_aoff. intros e' ->. exact He. }
set (a := aeval B ly (fst r) + i) in *.
rewrite !in_app_iff in Hr. destruct Hr as [Hr|[Hr|Hr]].
-
unfold ajunk_cf in Hr.
destruct Hr as [E|[E|Hr]]; [subst r; cbn [fst snd aeval] in Hi, a; left; unfold in_zr, ly_rinfo; cbn [fst snd]; subst a; lia | subst r; cbn [snd] in Hi; lia |].
rewrite !in_app_iff in Hr.
destruct Hr as [Hr|[Hr|[Hr|[Hr|[Hr|[Hr|[Hr|Hr]]]]]]].
+ apply in_flat_map in Hr as (c & Hc & Hr). apply zseq_In in Hc. unfold region_junk_cf, region_junk in Hr. cbv zeta in Hr.
left. unfold in_zr, ly_rinfo. cbn [fst snd]. subst a.
destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hi |- *; rewrite EA by exact I; cbn [aeval]; lia.
+ apply in_flat_map in Hr as (c & Hc & Hr). apply zseq_In in Hc. unfold cache_junk in Hr. destruct Hr as [<-|[]]. cbn [fst snd aeval] in Hi, a. exfalso.
assert (N : 0 <= (if st_cache_inited S then Z.of_nat (length (pc_chunks (cache S c))) else 0) <= 16).
{ destruct (st_cache_inited S) eqn:Ei; [|lia]. pose proof (wrc_cache _ _ _ _ _ _ (wfc_classes _ _ _ _ _ WF c ltac:(lia))) as WC. rewrite Ei in WC.
destruct WC as [_ PL]. pose proof (class_ok c ltac:(lia)) as (_ & _ & _ & K4 & _). lia. }
subst a. unfold t_cache, kThreadObjSize in *. lia.
+ apply in_flat_map in Hr as (k & Hk & Hr). apply (CK k); [exact Hk | | exact Hp].
pose proof (chunk_facts_cf B ly S HG rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
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
* pose proof (wsc_reserved _ (wfc_secondary _ _ _ _ _ WF)) as R1. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv in *. subst a. lia.
* apply in_flat_map in Hr as (k & Hk & Hr). pose proof (chunk_facts_cf B ly S HG rd k M Hk) as (_ & _ & _ & _ & _ & _ & G7 & _ & GG).
destruct (ck_beg k) as [|o|r' o|c p]; try solve [destruct Hr]. destruct Hr as [<-|[]]. cbn [fst snd aeval] in Hi, a.
destruct GG as (-> & Gp & Gbase & Gext & Gin & _). pose proof (secondary_geometry (ck_req k) ltac:(lia) Gp) as (SG1 & _ & _ & SG & _). unfold kMaxSize in SG1.
apply (SEC _ a Gin); [cbn [fst snd]; subst a; unfold kPage in *; lia | exact Hp].
+
unfold quar_junk in Hr. apply in_flat_map in Hr as (b & Hb & Hr). unfold batch_junk in Hr. destruct Hr as [<-|[]]. cbn [fst snd] in Hi, a.
subst a. unfold batch_exp in Hp |- *. rewrite EA in Hp |- * by exact I. cbn [aeval] in Hp |- *.
pose proof (wfc_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; auto).
pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wrc_alloc _ _ _ _ _ _ CL) as AL. pose proof (wrc_alloc_al _ _ _ _ _ _ CL) as AA. assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2, AA.
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
+ exfalso. cbn [fst snd aeval] in Hi, a. pose proof (wsc_reserved _ (wfc_secondary _ _ _ _ _ WF)) as R1. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv in *. subst a. lia.
+ exfalso. apply in_flat_map in Hr as (k & Hk & Hr). pose proof (chunk_facts_cf B ly S HG rd k M Hk) as (_ & _ & _ & _ & _ & _ & G7 & _ & GG).
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
+ apply in_flat_map in Hr as (k & Hk & Hr). unfold chunk_user in Hr. pose proof (chunk_facts_cf B ly S HG rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
destruct (ck_state k); [|destruct Hr]. destruct Hr as [<-|[]]. cbn [fst snd] in Hi, a.
apply (CK k); [exact Hk | | exact Hp]. subst a. change (aeval B ly (sptr_exp (ck_user k))) with (sptr_addr B ly (ck_user k)). rewrite G4. unfold ck_n in *.
assert (K0 : match ck_beg k with PSec _ _ => kPage | _ => 0 end >= 0) by (destruct (ck_beg k); unfold kPage; lia). lia.
+ exfalso. apply in_map_iff in Hr as ([cid pos] & <- & Hcp). cbn [fst snd aeval] in Hi, a.
pose proof (frame_facts_cf B ly S HG rd cid pos M Hcp) as (Fc & Fp & F1 & F2 & F3 & F4 & F5 & _). subst a. unfold kFakeFramesOff in *. lia.
+ exfalso. apply in_map_iff in Hr as ([cid pos] & <- & Hcp). cbn [fst snd aeval] in Hi, a. apply (LOW a); [|exact Hp]. subst a.
pose proof (frame_facts_cf B ly S HG rd cid pos M Hcp) as (Fc & Fp & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
pose proof (shadow_range_below (ly_F ly + fs_frame_off cid pos) (fs_frame_bytes cid) ltac:(clear - F1 F4 Fc; unfold in_app, kFakeFramesOff in *; lia) ltac:(lia)
ltac:(clear - F1 F4 F5 Fc; ceil; unfold in_app, ASAN_CEIL, kHighMemEnd, kHighMemBeg, kLowShadowBeg, kFakeFramesOff in *; lia)). lia.
Qed.
Lemma vis_lists_u64_cf : forall ly S Hp rd, ARmcf B ly S Hp rd ->
(forall r, In r (as_junk B ly) -> exists z, fst r = ANum z /\ 4096 <= z /\ z + snd r <= kImgEnd) ->
forall r i, In r (ajunk_cf B ly S ++ aareas S ++ aclient S) -> 0 <= i < snd r ->
0 <= aeval B ly (fst r) + i < ASAN_CEIL.
Proof.
intros ly S HG rd M JK r i Hr Hi. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (amc_syms _ _ _ _ _ M) as SY.
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
{ intros e x He Hx. exact (app_addr_below_ceil _ (proj1 (owned_sec_bound_cf B ly S HG rd x M ltac:(apply Exists_exists; exists e; split; [exact He | exact Hx])))). }
assert (CK : forall k x, In k (st_chunks S) ->
ck_base B ly k - (match ck_beg k with PSec _ _ => kPage | _ => 0 end) <= x < ck_base B ly k + ck_extent k -> 4096 <= x < ASAN_CEIL).
{ intros k x Hk Hx. pose proof (chunk_facts_cf B ly S HG rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg k) as [|o|r0 o|c p] eqn:Eb; try solve [destruct GG].
- unfold in_app in G1. lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _). apply (SEC _ x Gin). cbn [fst snd]. unfold kPage in *. lia. }
assert (EA : forall e d, match e with ASh _ => False | _ => True end -> aeval B ly (aoff e d) = aeval B ly e + d).
{ intros e d He. apply aeval_aoff. intros e' ->. exact He. }
assert (CL : forall c, 1 <= c <= 31 -> kHighMemBeg <= region_base ly c /\ region_base ly c + 2 ^ 32 <= ASAN_CEIL /\
0 <= rg_mapped_user (reg S c) <= kFreeArrayOffset /\ 0 <= rg_mapped_fa (reg S c) <= kFreeArrayMax).
{ intros c Hc. pose proof (region_in_prim ly c LO Hc) as (_ & _ & _ & R4 & R5). pose proof (wfc_classes _ _ _ _ _ WF c Hc) as WC.
pose proof (mapped_bound_cf (as_universe B) 0 0 0 S c WF Hc) as MB.
pose proof (wrc_alloc _ _ _ _ _ _ WC) as M1. pose proof (wrc_fa _ _ _ _ _ _ WC) as [M2 _]. pose proof (wrc_fa_bound _ _ _ _ _ _ WC). lia. }
set (a := aeval B ly (fst r) + i) in *.
rewrite !in_app_iff in Hr. destruct Hr as [Hr|[Hr|Hr]].
-
unfold ajunk_cf in Hr.
destruct Hr as [E|[E|Hr]]; [subst r; cbn [fst snd aeval] in Hi, a; subst a; unfold ly_rinfo, kRegionInfoOff, kSpaceSize, kPrimResvSize in *; lia | subst r; cbn [snd] in Hi; lia |].
rewrite !in_app_iff in Hr.
destruct Hr as [Hr|[Hr|[Hr|[Hr|[Hr|[Hr|[Hr|Hr]]]]]]].
+ apply in_flat_map in Hr as (c & Hc & Hr). apply zseq_In in Hc. unfold region_junk_cf, region_junk in Hr. cbv zeta in Hr. subst a.
destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hi |- *; rewrite EA by exact I; cbn [aeval]; unfold ly_rinfo, kRegionInfoOff, kSpaceSize, kPrimResvSize in *; lia.
+ apply in_flat_map in Hr as (c & Hc & Hr). apply zseq_In in Hc. unfold cache_junk in Hr. destruct Hr as [<-|[]]. cbn [fst snd aeval] in Hi, a.
assert (N : 0 <= (if st_cache_inited S then Z.of_nat (length (pc_chunks (cache S c))) else 0) <= 16).
{ destruct (st_cache_inited S) eqn:Ei; [|lia]. pose proof (wrc_cache _ _ _ _ _ _ (wfc_classes _ _ _ _ _ WF c ltac:(lia))) as WC. rewrite Ei in WC.
destruct WC as [_ PL]. pose proof (class_ok c ltac:(lia)) as (_ & _ & _ & K4 & _). lia. }
subst a. unfold t_cache, kThreadObjSize in *. lia.
+ apply in_flat_map in Hr as (k & Hk & Hr). enough (R : 4096 <= a < ASAN_CEIL) by lia. apply (CK k); [exact Hk |].
pose proof (chunk_facts_cf B ly S HG rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
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
* pose proof (wsc_reserved _ (wfc_secondary _ _ _ _ _ WF)) as R1. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv in *. subst a. lia.
* apply in_flat_map in Hr as (k & Hk & Hr). pose proof (chunk_facts_cf B ly S HG rd k M Hk) as (_ & _ & _ & _ & _ & _ & G7 & _ & GG).
destruct (ck_beg k) as [|o|r' o|c p]; try solve [destruct Hr]. destruct Hr as [<-|[]]. cbn [fst snd aeval] in Hi, a.
destruct GG as (-> & Gp & Gbase & Gext & Gin & _). pose proof (secondary_geometry (ck_req k) ltac:(lia) Gp) as (SG1 & _ & _ & SG & _). unfold kMaxSize in SG1.
enough (R : 4096 <= a < ASAN_CEIL) by lia. apply (SEC _ a Gin). cbn [fst snd]; subst a; unfold kPage in *; lia.
+
unfold quar_junk in Hr. apply in_flat_map in Hr as (b & Hb & Hr). unfold batch_junk in Hr. destruct Hr as [<-|[]]. cbn [fst snd] in Hi, a.
subst a. unfold batch_exp in *. rewrite EA by exact I. cbn [aeval].
pose proof (wfc_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as WC.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; auto).
pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ WC) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wrc_alloc _ _ _ _ _ _ WC) as AL. pose proof (CL kBatchClass ltac:(unfold kBatchClass; lia)) as (R4 & R5 & MB & _).
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
+ cbn [fst snd aeval] in Hi, a. pose proof (wsc_reserved _ (wfc_secondary _ _ _ _ _ WF)) as R1. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv in *. subst a. lia.
+ apply in_flat_map in Hr as (k & Hk & Hr). pose proof (chunk_facts_cf B ly S HG rd k M Hk) as (_ & _ & _ & _ & _ & _ & G7 & _ & GG).
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
+ apply in_flat_map in Hr as (k & Hk & Hr). unfold chunk_user in Hr. pose proof (chunk_facts_cf B ly S HG rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
destruct (ck_state k); [|destruct Hr]. destruct Hr as [<-|[]]. cbn [fst snd] in Hi, a.
enough (R : 4096 <= a < ASAN_CEIL) by lia.
apply (CK k); [exact Hk |]. subst a. change (aeval B ly (sptr_exp (ck_user k))) with (sptr_addr B ly (ck_user k)). rewrite G4. unfold ck_n in *.
assert (K0 : match ck_beg k with PSec _ _ => kPage | _ => 0 end >= 0) by (destruct (ck_beg k); unfold kPage; lia). lia.
+ apply in_map_iff in Hr as ([cid pos] & <- & Hcp). cbn [fst snd aeval] in Hi, a.
pose proof (frame_facts_cf B ly S HG rd cid pos M Hcp) as (Fc & Fp & F1 & F2 & F3 & F4 & F5 & _). subst a. unfold kFakeFramesOff in *. lia.
+ apply in_map_iff in Hr as ([cid pos] & <- & Hcp). cbn [fst snd aeval] in Hi, a. subst a.
pose proof (frame_facts_cf B ly S HG rd cid pos M Hcp) as (Fc & Fp & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
pose proof (shadow_range_below (ly_F ly + fs_frame_off cid pos) (fs_frame_bytes cid) ltac:(unfold kHighMemBeg, kFakeFramesOff in *; lia) ltac:(lia)
ltac:(ceil; unfold ASAN_CEIL, kHighMemEnd in *; lia)).
pose proof (SH0 (ly_F ly + fs_frame_off cid pos) ltac:(unfold kHighMemBeg, kFakeFramesOff in *; lia)). ceil; unfold ASAN_CEIL, kHighMemBeg in *. lia.
Qed.
(* VISLOC (YFkmcf.v:573) over ajunk_cf, ARmcf's own junk list. *)
Lemma visloc_jcf : forall ly S Hp rd, ARmcf B ly S Hp rd ->
(forall r, In r (as_junk B ly) -> exists z, fst r = ANum z /\ 4096 <= z /\ z + snd r <= kImgEnd) ->
forall r i, In r (ajunk_cf B ly S ++ aareas S ++ aclient S) -> 0 <= i < snd r ->
(0 <= aeval B ly (fst r) + i < 2 ^ 64) /\
((ly_prim ly <= aeval B ly (fst r) + i < ly_prim ly + kPrimResvSize) -> prim_committed_at ly S (aeval B ly (fst r) + i)).
Proof.
intros ly S HG rd M JK r i Hr Hi. split.
- pose proof (vis_lists_u64_cf ly S HG rd M JK r i Hr Hi) as X. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as [_ C2]. lia.
- exact (vis_lists_committed_cf ly S HG rd M JK r i Hr Hi).
Qed.
(* VISLOC (YFkmcf.v:573) exactly: over YG0n's ajunk, which ajunk_cf contains (ajunk_incl_cf). *)
Lemma visloc_cf : forall ly S Hp rd, ARmcf B ly S Hp rd ->
(forall r, In r (as_junk B ly) -> exists z, fst r = ANum z /\ 4096 <= z /\ z + snd r <= kImgEnd) ->
forall r i, In r (ajunk B ly S ++ aareas S ++ aclient S) -> 0 <= i < snd r ->
(0 <= aeval B ly (fst r) + i < 2 ^ 64) /\
((ly_prim ly <= aeval B ly (fst r) + i < ly_prim ly + kPrimResvSize) -> prim_committed_at ly S (aeval B ly (fst r) + i)).
Proof.
intros ly S HG rd M JK r i Hr Hi. apply (visloc_jcf ly S HG rd M JK r i); [|exact Hi].
apply in_app_iff in Hr as [Hr|Hr]; apply in_app_iff; [left; exact (ajunk_incl_cf B ly S r Hr) | right; exact Hr].
Qed.
End g.
End f.
