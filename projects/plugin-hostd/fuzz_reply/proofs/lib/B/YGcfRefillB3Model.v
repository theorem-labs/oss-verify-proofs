(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/YGcfRefillB3Model.v (commit f01d79f3fb5, cf refill round 3; file sha256 847d39390ef9) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Theorem Labs, 2026-10-30 (ReallocPrimary.CfW, lane W, cf refill re-base, B3 half): the cf model lemmas of the B3 top
   MnRefillB3cf.v.
   - Section g: cgif's YG0o.v helpers over ARmcf (shadow_apart_not_client_cf, prim_shadow_not_client_cf,
     vis_lists_committed_cf, vis_lists_u64_cf): cgif's statements and proofs, with the cf projections (amc_*, wfc_*,
     wrc_*, chunk_facts_cf, frame_facts_cf, owned_sec_bound_cf, mapped_bound_cf).
   - no_prim_hole_exh: a cf class carries only the (EXH_HOLE, 0) sentinel, of length 0, so no address is a hole.
   - ALedger_shape_cf: cgif's ALedger_shape (MnRefillB3.v) over ALedger_cf (the errbuf zone and capacity too).
   - Section LG: cgif's YG0h.v grant lemmas (one user map, one free-array map of a class) over WfP_cf / ALedger_cf.
   EVENT-FREE.  rule 24: no function proved (kind: re-base of the proved refill walk's model lemmas onto the cf model). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0i YO0d YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG03 YG0f YG0v YG0n YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YG0h YG0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YK0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG02cf YG06cf YG06bcf YG08cf YG0ncf YG0dcf YG0qcf YG0scf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold ASAN_CEIL in H2.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section g.
Variable B : asyms.

(* ---- YG0o's ARm helpers over ARmcf (cgif's statements, the cf projections) ---- *)
Lemma shadow_apart_not_client_cf : forall ly S Hp rd x0 len x, ARmcf B ly S Hp rd -> x0 mod 8 = 0 -> 0 <= x0 -> x0 + len <= kHighMemEnd ->
zdisjoint (x0, len) (ly_F ly, kFakeStackSize) -> x0 <= x < x0 + len -> ~ aclient_byte B ly S (shadow_addr x).
Proof.
intros ly S Hp rd x0 len x M A0 P0 HI D Hx C.
assert (SB2 : shadow_addr x < kHighMemBeg).
{ assert (DX : x / 8 <= (kHighMemEnd - 1) / 8) by (apply Z.div_le_mono; lia).
unfold shadow_addr, SHADOW_OFF, kHighMemBeg, kHighMemEnd in *. change ((2 ^ 47 - 1) / 8) with 17592186044415 in DX. lia. }
assert (SB1 : SHADOW_OFF <= shadow_addr x) by (unfold shadow_addr; pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)); lia).
destruct C as [(k & Hk & Hst & Hr)|([cid pos] & Hcp & [Hr|Hr])]; cbn [fst snd] in *.
- pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & _ & _ & G4 & G5 & _ & G7 & G8 & _). rewrite G4 in Hr. unfold ck_n in Hr.
unfold in_app, kLowShadowBeg, SHADOW_OFF, kHighMemBeg in G1, SB1, SB2. clear - G1 SB1 SB2 Hr G5 G8. lia.
- pose proof (frame_facts_cf B ly S Hp rd cid pos M Hcp) as (Fc & Fp & F1 & F2 & F3 & F4 & F5 & _). unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr. unfold kFakeFramesOff in F4.
unfold in_app, kLowShadowBeg, SHADOW_OFF, kHighMemBeg in F1, SB1, SB2. clear - F1 SB1 SB2 Hr F4 F5 Fc. lia.
- pose proof (frame_facts_cf B ly S Hp rd cid pos M Hcp) as (Fc & Fp & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _). unfold kFakeFramesOff in F4.
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
Lemma prim_shadow_not_client_cf : forall ly S Hp rd c x, ARmcf B ly S Hp rd -> 1 <= c <= 31 ->
region_base ly c <= x < region_base ly c + 2 ^ 32 -> ~ aclient_byte B ly S (shadow_addr x).
Proof.
intros ly S Hp rd c x M Hc Hx. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (region_in_prim ly c LO Hc) as (R1 & R2 & R3 & R4 & R5).
apply (shadow_apart_not_client_cf ly S Hp rd (region_base ly c) (2 ^ 32) x M); [| unfold kHighMemBeg in *; lia | ceil; unfold ASAN_CEIL, kHighMemEnd in *; lia | | exact Hx].
- apply Z.mod_divide in R3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 65536) with ((q * 8192) * 8) by lia. apply Z_mod_mult.
- pose proof (lo_disj _ LO) as DJ. unfold static_extents, owned_extents in DJ. cbn [pairwise app] in DJ. destruct DJ as [DP _].
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PF _].
unfold zdisjoint in PF |- *. cbn [fst snd] in PF |- *. lia.
Qed.
Lemma vis_lists_committed_cf : forall ly S Hp rd, ARmcf B ly S Hp rd ->
(forall r, In r (as_junk B ly) -> exists z, fst r = ANum z /\ 4096 <= z /\ z + snd r <= kImgEnd) ->
forall r i, In r (ajunk B ly S ++ aareas S ++ aclient S) -> 0 <= i < snd r ->
ly_prim ly <= aeval B ly (fst r) + i < ly_prim ly + kPrimResvSize -> prim_committed_at ly S (aeval B ly (fst r) + i).
Proof.
intros ly S Hp rd M JK r i Hr Hi Hp0. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (amc_syms _ _ _ _ _ M) as SY.
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
{ intros k x Hk Hx Hxp. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg k) as [|o|r0 o|c p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal).
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
{ destruct (st_cache_inited S) eqn:Ei; [|lia]. pose proof (wrc_cache _ _ _ _ _ _ (wfc_classes _ _ _ _ _ WF c ltac:(lia))) as WC. rewrite Ei in WC.
destruct WC as [_ PL]. pose proof (class_ok c ltac:(lia)) as (_ & _ & _ & K4 & _). lia. }
subst a. unfold t_cache, kThreadObjSize in *. lia.
+ apply in_flat_map in Hr as (k & Hk & Hr). apply (CK k); [exact Hk | | exact Hp0].
pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
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
* apply (LOW a); [subst a; unfold o_sec_sorted, kLowMemEnd, kHighMemBeg in *; lia | exact Hp0].
* apply (LOW a); [subst a; unfold o_sec_sorted, o_sec_stats, o_sec_mutex, kLowMemEnd, kHighMemBeg in *; lia | exact Hp0].
* pose proof (wsc_reserved _ (wfc_secondary _ _ _ _ _ WF)) as R1. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv in *. subst a. lia.
* apply in_flat_map in Hr as (k & Hk & Hr). pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (_ & _ & _ & _ & _ & _ & G7 & _ & GG).
destruct (ck_beg k) as [|o|r' o|c p]; try solve [destruct Hr]. destruct Hr as [<-|[]]. cbn [fst snd aeval] in Hi, a.
destruct GG as (-> & Gp & Gbase & Gext & Gin & _). pose proof (secondary_geometry (ck_req k) ltac:(lia) Gp) as (SG1 & _ & _ & SG & _). unfold kMaxSize in SG1.
apply (SEC _ a Gin); [cbn [fst snd]; subst a; unfold kPage in *; lia | exact Hp0].
+
unfold quar_junk in Hr. apply in_flat_map in Hr as (b & Hb & Hr). unfold batch_junk in Hr. destruct Hr as [<-|[]]. cbn [fst snd] in Hi, a.
subst a. unfold batch_exp in Hp0 |- *. rewrite EA in Hp0 |- * by exact I. cbn [aeval] in Hp0 |- *.
pose proof (wfc_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; auto).
pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wrc_alloc _ _ _ _ _ _ CL) as AL. pose proof (wrc_alloc_al _ _ _ _ _ _ CL) as AA. assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2, AA.
apply Z.mod_divide in X2 as [q1 Hq1]; [|lia]. apply Z.mod_divide in AA as [q2 Hq2]; [|lia].
assert (q1 < q2) by nia.
right. exists kBatchClass. split; [unfold kBatchClass; lia|]. left. unfold in_zr, region_base. cbn [fst snd]. subst x. unfold kBatchBytes in *. nia.
+   exfalso. unfold thread_junk in Hr. subst a.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd aeval] in Hi, Hp0 |- *; unfold t_cache, t_cache_stats, t_stats, t_unwinding, kThreadObjSize in *; lia.
+   exfalso. apply (LOW a); [|exact Hp0]. subst a.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd aeval] in Hi, Hp0 |- *; unfold d_nuniq, kLowMemEnd, kHighMemBeg in *; lia.
+ exfalso. apply (LOW a); [|exact Hp0]. subst a. destruct (JK r Hr) as (z & E & Z1 & Z2). rewrite E. cbn [aeval]. unfold kImgEnd, kHighMemBeg in *. lia.
-
unfold aareas in Hr. rewrite !in_app_iff in Hr. destruct Hr as [Hr|[[<-|[]]|[Hr|Hr]]].
+ apply in_flat_map in Hr as (c & Hc & Hr). apply zseq_In in Hc. pose proof (region_in_prim ly c LO ltac:(lia)) as (R1 & R2 & _).
right. exists c. split; [lia|]. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in Hi, a; [left | right]; unfold in_zr, region_base, fa_base; cbn [fst snd]; subst a; lia.
+ exfalso. cbn [fst snd aeval] in Hi, a. pose proof (wsc_reserved _ (wfc_secondary _ _ _ _ _ WF)) as R1. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv in *. subst a. lia.
+ exfalso. apply in_flat_map in Hr as (k & Hk & Hr). pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (_ & _ & _ & _ & _ & _ & G7 & _ & GG).
destruct (ck_beg k) as [|o|r' o|c p]; try solve [destruct Hr]. destruct Hr as [<-|[]]. cbn [fst snd aeval] in Hi, a.
destruct GG as (-> & Gp & Gbase & Gext & Gin & _). apply (SEC _ a Gin); [cbn [fst snd]; subst a; lia | exact Hp0].
+ destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd aeval] in Hi, a.
* exfalso. subst a. unfold kFakeStackSize in *. lia.
* exfalso. subst a. unfold kNodesBlockSize in *. lia.
* exfalso. subst a. unfold kStoreBlockSize in *. lia.
* exfalso. subst a. unfold kThreadObjSize in *. lia.
* left. unfold in_zr, ly_rinfo. cbn [fst snd]. subst a. lia.
* exfalso. apply (LOW a); [|exact Hp0]. subst a.
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as [F1 F2]. cbn [fst snd] in F1, F2.
pose proof (shadow_range_below (ly_F ly + kFakeFramesOff) (kFakeStackSize - kFakeFramesOff) ltac:(unfold kFakeFramesOff in *; lia) ltac:(unfold kFakeStackSize, kFakeFramesOff; lia)
ltac:(clear - F1 F2; ceil; unfold ASAN_CEIL, kHighMemEnd, kHighMemBeg, kLowShadowBeg, kFakeFramesOff in *; lia)). lia.
-
unfold aclient in Hr. rewrite !in_app_iff in Hr. destruct Hr as [Hr|[Hr|Hr]].
+ apply in_flat_map in Hr as (k & Hk & Hr). unfold chunk_user in Hr. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
destruct (ck_state k); [|destruct Hr]. destruct Hr as [<-|[]]. cbn [fst snd] in Hi, a.
apply (CK k); [exact Hk | | exact Hp0]. subst a. change (aeval B ly (sptr_exp (ck_user k))) with (sptr_addr B ly (ck_user k)). rewrite G4. unfold ck_n in *.
assert (K0 : match ck_beg k with PSec _ _ => kPage | _ => 0 end >= 0) by (destruct (ck_beg k); unfold kPage; lia). lia.
+ exfalso. apply in_map_iff in Hr as ([cid pos] & <- & Hcp). cbn [fst snd aeval] in Hi, a.
pose proof (frame_facts_cf B ly S Hp rd cid pos M Hcp) as (Fc & Fp & F1 & F2 & F3 & F4 & F5 & _). subst a. unfold kFakeFramesOff in *. lia.
+ exfalso. apply in_map_iff in Hr as ([cid pos] & <- & Hcp). cbn [fst snd aeval] in Hi, a. apply (LOW a); [|exact Hp0]. subst a.
pose proof (frame_facts_cf B ly S Hp rd cid pos M Hcp) as (Fc & Fp & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
pose proof (shadow_range_below (ly_F ly + fs_frame_off cid pos) (fs_frame_bytes cid) ltac:(clear - F1 F4 Fc; unfold in_app, kFakeFramesOff in *; lia) ltac:(lia)
ltac:(clear - F1 F4 F5 Fc; ceil; unfold in_app, ASAN_CEIL, kHighMemEnd, kHighMemBeg, kLowShadowBeg, kFakeFramesOff in *; lia)). lia.
Qed.
Lemma vis_lists_u64_cf : forall ly S Hp rd, ARmcf B ly S Hp rd ->
(forall r, In r (as_junk B ly) -> exists z, fst r = ANum z /\ 4096 <= z /\ z + snd r <= kImgEnd) ->
forall r i, In r (ajunk B ly S ++ aareas S ++ aclient S) -> 0 <= i < snd r ->
0 <= aeval B ly (fst r) + i < ASAN_CEIL.
Proof.
intros ly S Hp rd M JK r i Hr Hi. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (amc_syms _ _ _ _ _ M) as SY.
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
{ intros e x He Hx. exact (app_addr_below_ceil _ (proj1 (owned_sec_bound_cf B ly S Hp rd x M ltac:(apply Exists_exists; exists e; split; [exact He | exact Hx])))). }
assert (CK : forall k x, In k (st_chunks S) ->
ck_base B ly k - (match ck_beg k with PSec _ _ => kPage | _ => 0 end) <= x < ck_base B ly k + ck_extent k -> 4096 <= x < ASAN_CEIL).
{ intros k x Hk Hx. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
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
unfold ajunk in Hr.
destruct Hr as [E|[E|Hr]]; [subst r; cbn [fst snd aeval] in Hi, a; subst a; unfold ly_rinfo, kRegionInfoOff, kSpaceSize, kPrimResvSize in *; lia | subst r; cbn [snd] in Hi; lia |].
rewrite !in_app_iff in Hr.
destruct Hr as [Hr|[Hr|[Hr|[Hr|[Hr|[Hr|[Hr|Hr]]]]]]].
+ apply in_flat_map in Hr as (c & Hc & Hr). apply zseq_In in Hc. unfold region_junk in Hr. cbv zeta in Hr. subst a.
destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hi |- *; rewrite EA by exact I; cbn [aeval]; unfold ly_rinfo, kRegionInfoOff, kSpaceSize, kPrimResvSize in *; lia.
+ apply in_flat_map in Hr as (c & Hc & Hr). apply zseq_In in Hc. unfold cache_junk in Hr. destruct Hr as [<-|[]]. cbn [fst snd aeval] in Hi, a.
assert (N : 0 <= (if st_cache_inited S then Z.of_nat (length (pc_chunks (cache S c))) else 0) <= 16).
{ destruct (st_cache_inited S) eqn:Ei; [|lia]. pose proof (wrc_cache _ _ _ _ _ _ (wfc_classes _ _ _ _ _ WF c ltac:(lia))) as WC. rewrite Ei in WC.
destruct WC as [_ PL]. pose proof (class_ok c ltac:(lia)) as (_ & _ & _ & K4 & _). lia. }
subst a. unfold t_cache, kThreadObjSize in *. lia.
+ apply in_flat_map in Hr as (k & Hk & Hr). enough (R : 4096 <= a < ASAN_CEIL) by lia. apply (CK k); [exact Hk |].
pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
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
* apply in_flat_map in Hr as (k & Hk & Hr). pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (_ & _ & _ & _ & _ & _ & G7 & _ & GG).
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
unfold region_base in R4, R5. subst x. clear X2 INB. unfold kBatchBytes, kFreeArrayOffset in *. lia.
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
+ apply in_flat_map in Hr as (k & Hk & Hr). pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (_ & _ & _ & _ & _ & _ & G7 & _ & GG).
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
+ apply in_flat_map in Hr as (k & Hk & Hr). unfold chunk_user in Hr. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
destruct (ck_state k); [|destruct Hr]. destruct Hr as [<-|[]]. cbn [fst snd] in Hi, a.
enough (R : 4096 <= a < ASAN_CEIL) by lia.
apply (CK k); [exact Hk |]. subst a. change (aeval B ly (sptr_exp (ck_user k))) with (sptr_addr B ly (ck_user k)). rewrite G4. unfold ck_n in *.
assert (K0 : match ck_beg k with PSec _ _ => kPage | _ => 0 end >= 0) by (destruct (ck_beg k); unfold kPage; lia). lia.
+ apply in_map_iff in Hr as ([cid pos] & <- & Hcp). cbn [fst snd aeval] in Hi, a.
pose proof (frame_facts_cf B ly S Hp rd cid pos M Hcp) as (Fc & Fp & F1 & F2 & F3 & F4 & F5 & _). subst a. unfold kFakeFramesOff in *. lia.
+ apply in_map_iff in Hr as ([cid pos] & <- & Hcp). cbn [fst snd aeval] in Hi, a. subst a.
pose proof (frame_facts_cf B ly S Hp rd cid pos M Hcp) as (Fc & Fp & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
pose proof (shadow_range_below (ly_F ly + fs_frame_off cid pos) (fs_frame_bytes cid) ltac:(unfold kHighMemBeg, kFakeFramesOff in *; lia) ltac:(lia)
ltac:(ceil; unfold ASAN_CEIL, kHighMemEnd in *; lia)).
pose proof (SH0 (ly_F ly + fs_frame_off cid pos) ltac:(unfold kHighMemBeg, kFakeFramesOff in *; lia)). ceil; unfold ASAN_CEIL, kHighMemBeg in *. lia.
Qed.
End g.

(* ---- holes: a cf class carries only the (EXH_HOLE, 0) sentinel, of length 0, so no address is a hole ---- *)
Lemma no_prim_hole_exh : forall ly S', (forall c', 1 <= c' <= 31 -> Forall (fun h => h = (EXH_HOLE, 0)) (rg_holes (reg S' c'))) ->
forall a, ~ prim_hole_at ly S' a.
Proof.
intros ly S' H a (c' & h & Hc' & Hin & Ha). pose proof (proj1 (Forall_forall _ _) (H c' Hc') h Hin) as E. cbv beta in E. subst h.
unfold in_zr in Ha. cbn [fst snd] in Ha. lia.
Qed.

(* ---- cgif's ALedger_shape over ALedger_cf: the errbuf zone and capacity are the state's too ---- *)
Lemma ALedger_shape_cf : forall segs ly S1 S2 md,
(forall c', 1 <= c' <= 31 -> rg_mapped_user (reg S2 c') = rg_mapped_user (reg S1 c') /\ rg_mapped_fa (reg S2 c') = rg_mapped_fa (reg S1 c')) ->
(forall a, prim_hole_at ly S2 a <-> prim_hole_at ly S1 a) ->
sec_extents ly S2 = sec_extents ly S1 -> prim_committed S2 = prim_committed S1 ->
st_sec_reserved S2 = st_sec_reserved S1 -> errb_zone ly S2 = errb_zone ly S1 -> errb_cap_cf S2 = errb_cap_cf S1 ->
ALedger_cf segs ly S1 md -> ALedger_cf segs ly S2 md.
Proof.
intros segs ly S1 S2 md RGEQ HOLE SE PC SR EZ EC L. destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15 L16 L17].
assert (CUT : forall x, cut_ok ly S2 x <-> cut_ok ly S1 x).
{ intros x. unfold cut_ok. split; (intros [H|[H|(c' & Hc' & H)]]; [left; exact H | right; left; exact H | right; right; exists c'; split; [exact Hc'|]]);
destruct (RGEQ c' Hc') as (Q1 & Q2); [rewrite <- Q1, <- Q2 | rewrite Q1, Q2]; exact H. }
constructor; try assumption.
- destruct L4 as (pieces & (Q1 & Q2 & Q3) & P2). exists pieces. split; [|exact P2]. split; [|split; [exact Q2|]].
+ apply Forall_forall. intros p' Hp. pose proof (proj1 (Forall_forall _ _) Q1 p' Hp) as (A1 & A2 & A3). split; [exact A1|]. split; apply CUT; assumption.
+ intros a Ha. rewrite (Q3 a Ha). rewrite HOLE. tauto.
- rewrite SE. exact L7.
- rewrite SE, EZ. exact L8.
- unfold eager_cf in L9 |- *. rewrite PC, SR, SE, EZ. exact L9.
- rewrite SE. exact L12.
- intros e He. unfold errb_zone in EZ. rewrite EZ in He. exact (L17 e He).
Qed.

(* ---- cgif's YG0h piece lemmas (the user / free-array grant of one class) over WfP_cf and ALedger_cf ---- *)
(* a map that contains [a, a + n) covers each of its addresses *)
Lemma covered_of_map_contains : forall l (a n : word) x, map_contains l a n = true ->
  bv_unsigned a <= x < bv_unsigned a + bv_unsigned n -> YK0g.covered l x = true.
Proof.
intros l a n x H Hx. unfold map_contains in H. apply existsb_exists in H as (e & He & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1, H2.
unfold YK0g.covered. apply existsb_exists. exists e. split; [exact He|].
unfold YK0g.in_iv, YK0g.in_rng, YK0g.B, YK0g.S. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Section LG.
Variable segs : list Segment.
Variables (U : Univ) (pp cc bb : Z).
Variables (ly : alayout) (S : astate) (md md' : Model) (c : Z).
Hypothesis LO : layout_ok ly.
Hypothesis WS : WfP_cf U pp cc bb S.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis L : ALedger_cf segs ly S md.
Hypothesis RES : vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md).
Hypothesis LIM : vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md).
Hypothesis ISP : vm_init_sp (m_vmmaps md') = vm_init_sp (m_vmmaps md).
Hypothesis SPL : sec_placed ly S.
Hypothesis COV : forall x, ~ (ly_prim ly <= x < ly_prim ly + kPrimResvSize) ->
YK0g.covered (vm_noaccess (m_vmmaps md') ++ m_vm_lazy md') x = YK0g.covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x.
Hypothesis NAF : forall lo n, region_free (vm_noaccess (m_vmmaps md)) lo n = true -> region_free (vm_noaccess (m_vmmaps md')) lo n = true.
(* the errbuf slot's placement (ARmcf's amc_xs_placed): apart from the static extents, so off the primary reserve *)
Hypothesis XPL : xs_placed_cf ly S.
Local Abbreviation r := (reg S c).
Local Abbreviation n := kUserMapSize.
Lemma lg_img_env : forall sg, In sg segs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd.
Proof using All.
intros sg Hsg. pose proof (alc_img _ _ _ _ L sg Hsg) as [I1 I2]. pose proof (lo_img ly LO) as (J0 & J1 & J2 & J3).
rewrite J0 in I1, I2. unfold kImgLo in *. lia.
Qed.
Lemma lg_TOP : alloc_top (m_vmmaps md') = alloc_top (m_vmmaps md).
Proof using All. unfold alloc_top. rewrite ISP. reflexivity. Qed.
Lemma lg_HL : (Z.to_nat c < length (st_regions S))%nat.
Proof using All. rewrite (wfc_len_regions _ _ _ _ _ WS). lia. Qed.
Lemma lg_reg_upd : forall r', reg (upd_reg c r' S) c = r'.
Proof using All. intros r'. unfold upd_reg. apply reg_upd_same; [lia | exact lg_HL]. Qed.
Lemma lg_reg_upd_ne : forall r' c', 0 <= c' -> c' <> c -> reg (upd_reg c r' S) c' = reg S c'.
Proof using All. intros r' c' H1 H2. unfold upd_reg. apply reg_upd_other; lia. Qed.
Lemma lg_sec_upd : forall r', sec_extents ly (upd_reg c r' S) = sec_extents ly S.
Proof using All. reflexivity. Qed.
Lemma lg_res_upd : forall r', st_sec_reserved (upd_reg c r' S) = st_sec_reserved S.
Proof using All. reflexivity. Qed.
Lemma lg_errbz_upd : forall r', errb_zone ly (upd_reg c r' S) = errb_zone ly S.
Proof using All. reflexivity. Qed.
Lemma lg_errbc_upd : forall r', errb_cap_cf (upd_reg c r' S) = errb_cap_cf S.
Proof using All. reflexivity. Qed.
Lemma lg_sec_off_prim : forall e x, In e (sec_extents ly S) -> fst e <= x < fst e + snd e ->
~ (ly_prim ly <= x < ly_prim ly + kPrimResvSize).
Proof using All.
intros e x He Hx. destruct SPL as [_ PD].
assert (INP : In (ly_prim ly, kPrimResvSize) (static_extents ly)) by (unfold static_extents, owned_extents; cbn; tauto).
assert (D : zdisjoint e (ly_prim ly, kPrimResvSize)).
{ clear - PD He INP. induction (sec_extents ly S) as [|y t IH]; [destruct He|]. cbn [app] in PD. destruct PD as [F PD].
destruct He as [<-|He]; [| exact (IH He PD)].
exact (proj1 (Forall_forall _ _) F _ ltac:(apply in_app_iff; right; exact INP)). }
unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.
Lemma lg_esec : esec (vm_noaccess (m_vmmaps md')) (m_vm_lazy md') (sec_extents ly S) = esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) (sec_extents ly S).
Proof using All.
apply esec_ext.
- destruct SPL as [PF _]. pose proof (sec_extents_sizes64P_cf U pp cc bb ly S WS) as SZ. apply Forall_forall. intros e He.
pose proof (proj1 (Forall_forall _ _) PF e He) as (_ & [H1 H2] & H3). pose proof (proj1 (Forall_forall _ _) SZ e He) as H4. cbn beta in H4.
clear - H1 H2 H3 H4. ceil; unfold kHighMemBeg, kLowShadowBeg, ASAN_CEIL in *. lia.
- intros e x He Hx. apply COV. exact (lg_sec_off_prim e x He Hx).
Qed.
Lemma lg_esec_ez : esec (vm_noaccess (m_vmmaps md')) (m_vm_lazy md') (errb_zone ly S) = esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) (errb_zone ly S).
Proof using All.
unfold errb_zone. apply esec_ext.
- apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) XPL e He) as (_ & [H1 H2] & H3 & _).
  assert (E0 : 0 <= snd e).
  { unfold xs_cf in He. destruct (last_cap_idx (st_secs S) 0 None); [destruct He as [<-|[]]; cbn [snd]; apply errb_cap_cf_nonneg | destruct He]. }
  clear - H1 H2 H3 E0. ceil; unfold kHighMemBeg, kLowShadowBeg, ASAN_CEIL in *. lia.
- intros e x He Hx. apply COV. pose proof (proj1 (Forall_forall _ _) XPL e He) as (_ & _ & _ & D).
  assert (INP : In (ly_prim ly, kPrimResvSize) (sec_extents ly S ++ static_extents ly ++ ly_extra ly))
    by (apply in_app_iff; right; apply in_app_iff; left; unfold static_extents, owned_extents; cbn; tauto).
  pose proof (proj1 (Forall_forall _ _) D _ INP) as DZ. unfold zdisjoint in DZ. cbn [fst snd] in DZ. lia.
Qed.
Lemma lg_esec2 : esec (vm_noaccess (m_vmmaps md')) (m_vm_lazy md') (sec_extents ly S ++ errb_zone ly S)
  = esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) (sec_extents ly S ++ errb_zone ly S).
Proof using All. rewrite !esec_app, lg_esec, lg_esec_ez. reflexivity. Qed.
Lemma lg_prim_committed_upd : forall r',
prim_committed (upd_reg c r' S) = prim_committed S - (rg_mapped_user r + rg_mapped_fa r) + (rg_mapped_user r' + rg_mapped_fa r').
Proof using All. intros r'. unfold upd_reg. apply prim_committed_set_region; [lia | exact lg_HL]. Qed.
Lemma lg_mu_fa : 0 <= rg_mapped_user r <= kFreeArrayOffset /\ rg_mapped_user r mod kUserMapSize = 0 /\
0 <= rg_mapped_fa r <= kFreeArrayMax /\ rg_mapped_fa r mod kFreeArrayMapSize = 0.
Proof using All.
pose proof (wfc_classes _ _ _ _ _ WS c Hc) as C. unfold wf_class_cf in C.
pose proof (wrc_alloc _ _ _ _ _ _ C). pose proof (wrc_mapped_al _ _ _ _ _ _ C). pose proof (wrc_fa _ _ _ _ _ _ C). pose proof (wrc_fa_bound _ _ _ _ _ _ C).
pose proof (wrc_mapped_bound _ _ _ _ _ _ C). repeat split; lia.
Qed.
Lemma lg_holes_exh : forall c', 1 <= c' <= 31 -> Forall (fun h => h = (EXH_HOLE, 0)) (rg_holes (reg S c')).
Proof using All. intros c' Hc'. exact (proj1 (wrc_holes _ _ _ _ _ _ (wfc_classes _ _ _ _ _ WS c' Hc'))). Qed.
Lemma lg_hole_iff : forall r', Forall (fun h => h = (EXH_HOLE, 0)) (rg_holes r') -> forall a, prim_hole_at ly (upd_reg c r' S) a <-> prim_hole_at ly S a.
Proof using All.
intros r' H a. split; intros X; exfalso; [|exact (no_prim_hole_exh ly S lg_holes_exh a X)].
apply (no_prim_hole_exh ly (upd_reg c r' S)) with (a := a); [|exact X].
intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [rewrite lg_reg_upd; exact H | rewrite lg_reg_upd_ne by lia; exact (lg_holes_exh c' Hc')].
Qed.
Lemma lg_cut_mono : forall S', (forall c', 1 <= c' <= 31 -> rg_mapped_user (reg S c') <= rg_mapped_user (reg S' c') /\ rg_mapped_fa (reg S c') <= rg_mapped_fa (reg S' c')) ->
forall x, cut_ok ly S x -> cut_ok ly S' x.
Proof using All.
intros S' H x [X|[X|(c' & Hc' & [(k & E & Bk)|(k & E & Bk)])]]; [left; exact X | right; left; exact X | |]; right; right; exists c'; split; [exact Hc'| |exact Hc'|];
destruct (H c' Hc') as [H1 H2]; [left | right]; exists k; split; [exact E | lia | exact E | lia].
Qed.
(* the user grant at the class's mapped end *)
Definition lg_offU : Z := rg_mapped_user r.
Definition lg_addrU : Z := region_base ly c + lg_offU.
Definition lg_rUp : region := mkRegion (lg_offU + n) (rg_alloc_user r) (rg_mapped_fa r) (rg_free r) (del_hole lg_offU (rg_holes r)).
Definition lg_SUp : astate := upd_reg c lg_rUp S.
Lemma lg_user_granted :
vm_maps (m_vmmaps md') = vm_maps (m_vmmaps md) ->
eager_used md' <= eager_used md + n ->
(forall x, YK0g.covered (vm_noaccess (m_vmmaps md') ++ m_vm_lazy md') x = true -> YK0g.covered (vm_maps (m_vmmaps md')) x = true) ->
ALedger_cf segs ly lg_SUp md'.
Proof using All.
intros VM EG LZ. rewrite VM in LZ. pose proof L as L0. destruct L0 as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15 L16 L17].
assert (HE : Forall (fun h => h = (EXH_HOLE, 0)) (rg_holes lg_rUp)) by (unfold lg_rUp; cbn [rg_holes]; exact (exh_holes_del _ _ (lg_holes_exh c Hc))).
assert (MONO : forall c', 1 <= c' <= 31 -> rg_mapped_user (reg S c') <= rg_mapped_user (reg lg_SUp c') /\ rg_mapped_fa (reg S c') <= rg_mapped_fa (reg lg_SUp c')).
{ intros c' Hc'. unfold lg_SUp. destruct (Z.eq_dec c' c) as [->|NE]; [rewrite lg_reg_upd; cbn [rg_mapped_user rg_mapped_fa lg_rUp]; unfold lg_offU, kUserMapSize; lia | rewrite lg_reg_upd_ne by lia; lia]. }
unfold lg_SUp.
constructor; rewrite ?RES, ?LIM, ?VM, ?lg_TOP, ?lg_sec_upd, ?lg_errbz_upd; try assumption; try (intros zz Hzz; first [exact (L10 zz Hzz) | right; exact (L10 zz Hzz)]); try (intros zz Hzz; first [exact (L11 zz Hzz) | right; exact (L11 zz Hzz)]); try (destruct L15 as [N1 N2]; split; apply NAF; assumption).
- destruct L4 as (pieces & (P1 & P2 & P3) & P4). exists pieces. split; [split; [|split; [exact P2|]]|exact P4].
+ eapply Forall_impl; [|exact P1]. intros p (A & Bp & Cp). split; [exact A|]. split; apply (lg_cut_mono lg_SUp MONO); assumption.
+ intros a Ha. rewrite (P3 a Ha). rewrite (lg_hole_iff lg_rUp HE a). tauto.
- unfold eager_cf in L9 |- *. rewrite lg_sec_upd, lg_errbz_upd, lg_esec2, lg_res_upd, lg_prim_committed_upd.
  cbn [rg_mapped_user rg_mapped_fa lg_rUp]. unfold lg_offU, kUserMapSize in *. lia.
Qed.
Lemma lg_prim_bounds : rg_mapped_user r + n <= kFreeArrayOffset ->
kHighMemBeg <= ly_prim ly /\ ly_prim ly <= region_base ly c /\ lg_addrU + n <= region_base ly c + kFreeArrayOffset /\
region_base ly c + kFreeArrayOffset + kFreeArrayMax <= ly_prim ly + kPrimResvSize /\ 0 <= lg_offU.
Proof using All.
intros HU. pose proof lg_mu_fa as (M1 & M2 & M3 & M4). pose proof (lo_space_in ly LO) as [S1 S2].
pose proof (lo_high ly LO) as HP. unfold in_high in HP.
unfold lg_addrU, lg_offU, region_base in *. rewrite region_off_eq by lia.
unfold kFreeArrayOffset, kFreeArrayMax, kPrimResvSize, kSpaceSize, kUserMapSize in *. repeat split; try lia; nia.
Qed.
Lemma lg_no_cut_inside : rg_mapped_user r + n <= kFreeArrayOffset -> forall x, cut_ok ly S x -> ~ (lg_addrU < x < lg_addrU + n).
Proof using All.
intros HU x CX HX. pose proof (lg_prim_bounds HU) as (B1 & B2 & B3 & B4 & B5). pose proof lg_mu_fa as (M1 & M2 & M3 & M4). pose proof (lo_space_in ly LO) as [S1 S2].
unfold lg_addrU, lg_offU, region_base in HX, B2, B3, B4. rewrite region_off_eq in HX, B2, B3, B4 by lia.
destruct CX as [->|[->|(c' & Hc' & [(k & -> & Bk)|(k & -> & Bk)])]]; unfold region_base, fa_base in *; rewrite ?region_off_eq in HX by lia; try rewrite ?region_off_eq in Bk by lia.
- unfold kUserMapSize in *. lia.
- unfold kUserMapSize, kPrimResvSize, kSpaceSize, kFreeArrayOffset, kFreeArrayMax in *. lia.
- pose proof (mapped_bound_cf U pp cc bb S c' WS Hc') as MB'.
apply Z.mod_divide in M2 as [q Hq]; [|unfold kUserMapSize; lia]. unfold kUserMapSize, kFreeArrayOffset in *. lia.
- pose proof (wrc_fa_bound _ _ _ _ _ _ (wfc_classes _ _ _ _ _ WS c' Hc')) as FB'. pose proof (proj1 (wrc_fa _ _ _ _ _ _ (wfc_classes _ _ _ _ _ WS c' Hc'))) as F0'.
apply Z.mod_divide in M2 as [q Hq]; [|unfold kUserMapSize; lia]. unfold kUserMapSize, kFreeArrayMapSize, kFreeArrayOffset, kFreeArrayMax in *. lia.
Qed.
Lemma lg_user_place : rg_mapped_user r + n <= kFreeArrayOffset ->
region_free (vm_reserved (m_vmmaps md)) (w64 lg_addrU) (w64 n) = true /\
map_contains (vm_maps (m_vmmaps md)) (w64 lg_addrU) (w64 n) = true.
Proof using All.
intros HU. pose proof L as L0. destruct L0 as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15].
pose proof (lg_prim_bounds HU) as (B1 & B2 & B3 & B4 & B5). pose proof (YG0h.prim_hi ly LO) as [C1 C2].
assert (R : ly_prim ly <= lg_addrU /\ lg_addrU + n <= ly_prim ly + kPrimResvSize /\ kImgEnd + 4096 <= lg_addrU /\ lg_addrU + n < 2 ^ 63).
{ clear - B1 B2 B3 B4 B5 C1 C2. unfold lg_addrU, kHighMemBeg, kImgEnd, kFreeArrayOffset, kFreeArrayMax, kUserMapSize in *. lia. }
destruct R as (R1 & R2 & R3 & R4).
split.
- rewrite L3. apply (region_free_reserved segs); [exact lg_img_env | exact R3 | unfold kUserMapSize; lia | lia].
- destruct L4 as (pieces & (P1 & P2 & P3) & P4).
destruct (proj1 (Exists_exists _ _) (proj2 (P3 lg_addrU ltac:(unfold kUserMapSize in *; lia)) (wf_no_prim_hole_cf U pp cc bb S ly lg_addrU WS))) as (P0 & HP & Hin).
pose proof (proj1 (Forall_forall _ _) P1 P0 HP) as (Q0 & _ & QE). pose proof (lg_no_cut_inside HU _ QE) as NC. unfold in_zr in Hin.
destruct (proj1 (P4 P0) HP) as (V0 & _ & Q3 & Q4).
unfold map_contains. apply (proj2 (existsb_exists _ _)). exists (wiv P0). split; [exact V0|].
unfold wiv. cbn [fst snd]. rewrite !w64_unsigned by (clear - Q0 Q3 Q4 C1 C2 B1 R1 R2 R4 Hin; unfold kHighMemBeg, kUserMapSize in *; lia).
apply andb_true_intro. split; apply Z.leb_le; unfold kUserMapSize in *; lia.
Qed.
(* the free-array grant at the class's mapped free-array end *)
Definition lg_offF : Z := kFreeArrayOffset + rg_mapped_fa r.
Definition lg_addrF : Z := region_base ly c + lg_offF.
Definition lg_rFp : region := mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_mapped_fa r + n) (rg_free r) (del_hole lg_offF (rg_holes r)).
Definition lg_SFp : astate := upd_reg c lg_rFp S.
Lemma lg_fa_granted :
vm_maps (m_vmmaps md') = vm_maps (m_vmmaps md) ->
eager_used md' <= eager_used md + n ->
(forall x, YK0g.covered (vm_noaccess (m_vmmaps md') ++ m_vm_lazy md') x = true -> YK0g.covered (vm_maps (m_vmmaps md')) x = true) ->
ALedger_cf segs ly lg_SFp md'.
Proof using All.
intros VM EG LZ. rewrite VM in LZ. pose proof L as L0. destruct L0 as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15 L16 L17].
assert (HE : Forall (fun h => h = (EXH_HOLE, 0)) (rg_holes lg_rFp)) by (unfold lg_rFp; cbn [rg_holes]; exact (exh_holes_del _ _ (lg_holes_exh c Hc))).
assert (MONO : forall c', 1 <= c' <= 31 -> rg_mapped_user (reg S c') <= rg_mapped_user (reg lg_SFp c') /\ rg_mapped_fa (reg S c') <= rg_mapped_fa (reg lg_SFp c')).
{ intros c' Hc'. unfold lg_SFp. destruct (Z.eq_dec c' c) as [->|NE]; [rewrite lg_reg_upd; cbn [rg_mapped_user rg_mapped_fa lg_rFp]; unfold kUserMapSize; lia | rewrite lg_reg_upd_ne by lia; lia]. }
unfold lg_SFp.
constructor; rewrite ?RES, ?LIM, ?VM, ?lg_TOP, ?lg_sec_upd, ?lg_errbz_upd; try assumption; try (intros zz Hzz; first [exact (L10 zz Hzz) | right; exact (L10 zz Hzz)]); try (intros zz Hzz; first [exact (L11 zz Hzz) | right; exact (L11 zz Hzz)]); try (destruct L15 as [N1 N2]; split; apply NAF; assumption).
- destruct L4 as (pieces & (P1 & P2 & P3) & P4). exists pieces. split; [split; [|split; [exact P2|]]|exact P4].
+ eapply Forall_impl; [|exact P1]. intros p (A & Bp & Cp). split; [exact A|]. split; apply (lg_cut_mono lg_SFp MONO); assumption.
+ intros a Ha. rewrite (P3 a Ha). rewrite (lg_hole_iff lg_rFp HE a). tauto.
- unfold eager_cf in L9 |- *. rewrite lg_sec_upd, lg_errbz_upd, lg_esec2, lg_res_upd, lg_prim_committed_upd.
  cbn [rg_mapped_user rg_mapped_fa lg_rFp]. unfold kUserMapSize in *. lia.
Qed.
Lemma lg_prim_boundsF : rg_mapped_fa r + n <= kFreeArrayMax ->
kHighMemBeg <= ly_prim ly /\ ly_prim ly <= region_base ly c /\ lg_addrF + n <= region_base ly c + kFreeArrayOffset + kFreeArrayMax /\
region_base ly c + kFreeArrayOffset + kFreeArrayMax <= ly_prim ly + kPrimResvSize /\ kFreeArrayOffset <= lg_offF.
Proof using All.
intros HF. pose proof lg_mu_fa as (M1 & M2 & M3 & M4). pose proof (lo_space_in ly LO) as [S1 S2].
pose proof (lo_high ly LO) as HP. unfold in_high in HP.
unfold lg_addrF, lg_offF, region_base in *. rewrite region_off_eq by lia.
unfold kFreeArrayOffset, kFreeArrayMax, kPrimResvSize, kSpaceSize, kUserMapSize in *. repeat split; try lia; nia.
Qed.
Lemma lg_no_cut_insideF : rg_mapped_fa r + n <= kFreeArrayMax -> forall x, cut_ok ly S x -> ~ (lg_addrF < x < lg_addrF + n).
Proof using All.
intros HF x CX HX. pose proof (lg_prim_boundsF HF) as (B1 & B2 & B3 & B4 & B5). pose proof lg_mu_fa as (M1 & M2 & M3 & M4). pose proof (lo_space_in ly LO) as [S1 S2].
unfold lg_addrF, lg_offF, region_base in HX, B2, B3, B4. rewrite region_off_eq in HX, B2, B3, B4 by lia.
destruct CX as [->|[->|(c' & Hc' & [(k & -> & Bk)|(k & -> & Bk)])]]; unfold region_base, fa_base in *; rewrite ?region_off_eq in HX by lia; try rewrite ?region_off_eq in Bk by lia.
- unfold kUserMapSize, kFreeArrayOffset in *. lia.
- unfold kUserMapSize, kPrimResvSize, kSpaceSize, kFreeArrayOffset, kFreeArrayMax in *. lia.
- pose proof (mapped_bound_cf U pp cc bb S c' WS Hc') as MB'.
apply Z.mod_divide in M4 as [q Hq]; [|unfold kFreeArrayMapSize; lia]. unfold kUserMapSize, kFreeArrayMapSize, kFreeArrayOffset, kFreeArrayMax in *. lia.
- pose proof (wrc_fa_bound _ _ _ _ _ _ (wfc_classes _ _ _ _ _ WS c' Hc')) as FB'. pose proof (proj1 (wrc_fa _ _ _ _ _ _ (wfc_classes _ _ _ _ _ WS c' Hc'))) as F0'.
apply Z.mod_divide in M4 as [q Hq]; [|unfold kFreeArrayMapSize; lia]. unfold kUserMapSize, kFreeArrayMapSize, kFreeArrayOffset, kFreeArrayMax in *. lia.
Qed.
Lemma lg_fa_place : rg_mapped_fa r + n <= kFreeArrayMax ->
region_free (vm_reserved (m_vmmaps md)) (w64 lg_addrF) (w64 n) = true /\
map_contains (vm_maps (m_vmmaps md)) (w64 lg_addrF) (w64 n) = true.
Proof using All.
intros HF. pose proof L as L0. destruct L0 as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15].
pose proof (lg_prim_boundsF HF) as (B1 & B2 & B3 & B4 & B5). pose proof (YG0h.prim_hi ly LO) as [C1 C2]. pose proof lg_mu_fa as (M1 & M2 & M3 & M4).
assert (R : ly_prim ly <= lg_addrF /\ lg_addrF + n <= ly_prim ly + kPrimResvSize /\ kImgEnd + 4096 <= lg_addrF /\ lg_addrF + n < 2 ^ 63).
{ clear - B1 B2 B3 B4 B5 C1 C2 M3. unfold lg_addrF, lg_offF, kHighMemBeg, kImgEnd, kFreeArrayOffset, kFreeArrayMax, kUserMapSize in *. lia. }
destruct R as (R1 & R2 & R3 & R4).
split.
- rewrite L3. apply (region_free_reserved segs); [exact lg_img_env | exact R3 | unfold kUserMapSize; lia | lia].
- destruct L4 as (pieces & (P1 & P2 & P3) & P4).
destruct (proj1 (Exists_exists _ _) (proj2 (P3 lg_addrF ltac:(unfold kUserMapSize in *; lia)) (wf_no_prim_hole_cf U pp cc bb S ly lg_addrF WS))) as (P0 & HP & Hin).
pose proof (proj1 (Forall_forall _ _) P1 P0 HP) as (Q0 & _ & QE). pose proof (lg_no_cut_insideF HF _ QE) as NC. unfold in_zr in Hin.
destruct (proj1 (P4 P0) HP) as (V0 & _ & Q3 & Q4).
unfold map_contains. apply (proj2 (existsb_exists _ _)). exists (wiv P0). split; [exact V0|].
unfold wiv. cbn [fst snd]. rewrite !w64_unsigned by (clear - Q0 Q3 Q4 C1 C2 B1 R1 R2 R4 Hin; unfold kHighMemBeg, kUserMapSize in *; lia).
apply andb_true_intro. split; apply Z.leb_le; unfold kUserMapSize in *; lia.
Qed.
End LG.
End f.
