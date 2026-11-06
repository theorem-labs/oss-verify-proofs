(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG0t.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YG0t.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_role. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0i YO0d YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG05 YG0s YG0q DepotCfg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold ASAN_CEIL in H2.
Local Open Scope Z_scope.
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section u.
Variable segs : list Segment.
Variable B : asyms.
Definition nf (ly : alayout) (a : Z) : Prop :=
((a < ly_F ly \/ ly_F ly + kFakeStackSize <= a) \/ (ly_F ly + 88 <= a < ly_F ly + kFakeFlagsOff)) /\
(a < shadow_addr (ly_F ly) \/ shadow_addr (ly_F ly) + kFakeStackSize / 8 <= a)
.
Definition nf_range (ly : alayout) (lo len : Z) : Prop := forall a, lo <= a < lo + len -> nf ly a.
Definition cell_bytes_nf (ly : alayout) (c : acell) : Prop :=
forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> nf ly (aeval B ly (c_at c) + k).
Lemma cnf_of_range : forall ly c lo len, nf_range ly lo len ->
lo <= aeval B ly (c_at c) -> aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len -> cell_bytes_nf ly c.
Proof. intros ly c lo len OR H1 H2 k Hk. apply OR. lia. Qed.
Lemma Forall_cnf_of_range : forall ly l lo len, nf_range ly lo len ->
Forall (fun c => lo <= aeval B ly (c_at c) /\ aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len) l -> Forall (cell_bytes_nf ly) l.
Proof. intros ly l lo len OR H. eapply Forall_impl; [|exact H]. intros c [H1 H2]. eapply cnf_of_range; eauto. Qed.
Lemma F_app : forall ly, layout_ok ly ->
4096 <= ly_F ly /\ (ly_F ly + kFakeStackSize <= kLowShadowBeg \/ (kHighMemBeg <= ly_F ly /\ ly_F ly + kFakeStackSize <= ASAN_CEIL)) /\ page_aligned (ly_F ly).
Proof.
intros ly LO. pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as [H1 H2].
cbn [fst snd] in H1, H2. split; [exact H1|]. split; [exact H2 | exact (lo_F_al _ LO)].
Qed.
Lemma F_shadow_band : forall ly, layout_ok ly ->
kLowShadowBeg < shadow_addr (ly_F ly) /\ shadow_addr (ly_F ly) + kFakeStackSize / 8 <= kHighMemBeg.
Proof.
intros ly LO. destruct (F_app ly LO) as (F0 & FZ & _). ceil.
pose proof (shadow_range_below (ly_F ly) kFakeStackSize ltac:(lia) ltac:(unfold kFakeStackSize; lia)
ltac:(clear - FZ CR CR0 F0; unfold ASAN_CEIL, kHighMemEnd, kLowShadowBeg, kHighMemBeg in *; lia)) as SB.
split; [| exact SB]. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg. pose proof (Z.div_pos (ly_F ly) 8 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma nf2_app : forall ly a, layout_ok ly -> (a < kLowShadowBeg \/ kHighMemBeg <= a) ->
a < shadow_addr (ly_F ly) \/ shadow_addr (ly_F ly) + kFakeStackSize / 8 <= a.
Proof. intros ly a LO Ha. pose proof (F_shadow_band ly LO) as [B1 B2]. lia. Qed.
Lemma nf1_band : forall ly a, layout_ok ly -> SHADOW_OFF <= a < kHighMemBeg -> a < ly_F ly \/ ly_F ly + kFakeStackSize <= a.
Proof. intros ly a LO Ha. destruct (F_app ly LO) as (F0 & FZ & _). unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia. Qed.
Lemma shadow_apart_F : forall ly lo len x, layout_ok ly -> zdisjoint (lo, len) (ly_F ly, kFakeStackSize) -> lo <= x < lo + len ->
shadow_addr x < shadow_addr (ly_F ly) \/ shadow_addr (ly_F ly) + kFakeStackSize / 8 <= shadow_addr x.
Proof.
intros ly lo len x LO D Hx. pose proof (lo_F_al _ LO) as FAL. unfold page_aligned in FAL. apply Z.mod_divide in FAL as [q Hq]; [|lia].
unfold zdisjoint in D. cbn [fst snd] in D. unfold shadow_addr.
assert (E1 : ly_F ly / 8 = q * 512) by (rewrite Hq; replace (q * 4096) with ((q * 512) * 8) by lia; apply Z_div_mult; lia).
assert (E2 : kFakeStackSize / 8 = 1446400) by reflexivity.
destruct D as [D|D].
- left. assert (x / 8 <= (ly_F ly - 1) / 8) by (apply Z.div_le_mono; lia).
assert ((ly_F ly - 1) / 8 = q * 512 - 1) by (rewrite Hq; replace (q * 4096 - 1) with ((q * 512 - 1) * 8 + 7) by lia; rewrite Z.div_add_l by lia; rewrite Z.div_small by lia; lia). lia.
- right. assert ((ly_F ly + kFakeStackSize) / 8 <= x / 8) by (apply Z.div_le_mono; lia).
assert ((ly_F ly + kFakeStackSize) / 8 = q * 512 + 1446400) by (rewrite Hq; unfold kFakeStackSize; replace (q * 4096 + 11571200) with ((q * 512 + 1446400) * 8) by lia; apply Z_div_mult; lia). lia.
Qed.
Lemma nf_of_disjoint : forall ly e a, layout_ok ly -> zdisjoint e (ly_F ly, kFakeStackSize) ->
(fst e + snd e <= kLowShadowBeg \/ kHighMemBeg <= fst e) -> fst e <= a < fst e + snd e -> nf ly a.
Proof.
intros ly e a LO D He Ha. unfold zdisjoint in D. cbn [fst snd] in D. split; [left; lia|]. apply (nf2_app ly a LO). lia.
Qed.
Lemma static_extents_app : forall ly e, layout_ok ly -> In e (static_extents ly) -> fst e + snd e <= kLowShadowBeg \/ kHighMemBeg <= fst e.
Proof.
intros ly e LO He. unfold static_extents in He. apply in_app_iff in He as [He|[<-|[<-|[]]]].
- pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) e He) as [H1 H2]. lia.
- cbn [fst snd]. pose proof (lo_stk_ceil _ LO) as T. ceil. right. unfold kHighMemBeg, ASAN_CEIL in *. lia.
- pose proof (lo_img _ LO) as (I0 & I1 & I2 & I3). left. unfold kImgLo, kImgEnd, kLowShadowBeg in *. lia.
Qed.
Lemma nf_static_ext : forall ly e a, layout_ok ly -> In e (static_extents ly) -> e <> (ly_F ly, kFakeStackSize) -> fst e <= a < fst e + snd e -> nf ly a.
Proof.
intros ly e a LO He Hne Ha. eapply nf_of_disjoint; [exact LO | | exact (static_extents_app ly e LO He) | exact Ha].
pose proof (lo_disj _ LO) as D.
lazymatch eval cbv in depot_has_trace with
| true =>
assert (SPLIT : static_extents ly = [(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv); (ly_T ly, kThreadObjSize)] ++
(ly_F ly, kFakeStackSize) :: [(ly_NB ly, kNodesBlockSize); (ly_SB ly, kStoreBlockSize); (ly_C ly, 256); (ly_D ly, 4096);
(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly]) by reflexivity
| false =>
assert (SPLIT : static_extents ly = [(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv); (ly_T ly, kThreadObjSize)] ++
(ly_F ly, kFakeStackSize) :: [(if (ly_NB ly =? 0)%Z then (4096, 0) else (ly_NB ly, kNodesBlockSize));
(if (ly_SB ly =? 0)%Z then (4096, 0) else (ly_SB ly, kStoreBlockSize)); (ly_C ly, 256); (ly_D ly, 4096);
(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly]) by reflexivity
end.
rewrite SPLIT in He. apply in_app_iff in He as [He|[He|He]].
- exact (pairwise_In zdisjoint _ e (ly_F ly, kFakeStackSize) _ _ SPLIT D He ltac:(left; reflexivity)).
- exfalso. exact (Hne (eq_sym He)).
- apply zdisjoint_sym. rewrite SPLIT in D. apply pairwise_app_inv in D as (_ & D & _). cbn [pairwise] in D. destruct D as [D _].
exact (proj1 (Forall_forall _ _) D e He).
Qed.
Lemma nf_prim : forall ly a, layout_ok ly -> ly_prim ly <= a < ly_prim ly + kPrimResvSize -> nf ly a.
Proof.
intros ly a LO Ha. eapply (nf_static_ext ly (ly_prim ly, kPrimResvSize)); [exact LO | unfold static_extents, owned_extents; cbn; tauto | | exact Ha].
intros E. pose proof (f_equal snd E) as E2. cbn in E2. unfold kPrimResvSize, kFakeStackSize in E2. lia.
Qed.
Lemma nf_sec : forall ly S rd e a, ARm B ly S rd -> In e (sec_extents ly S) -> fst e <= a < fst e + snd e -> nf ly a.
Proof.
intros ly S rd e a M He Ha. pose proof (am_layout _ _ _ _ M) as LO. eapply nf_of_disjoint; [exact LO | | |exact Ha].
- exact (pairwise_In zdisjoint _ e (ly_F ly, kFakeStackSize) (sec_extents ly S) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) He
ltac:(unfold static_extents, owned_extents; cbn; tauto)).
- pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) _ He) as (_ & [I0 I1] & _). lia.
Qed.
Lemma nf_img : forall ly S rd a, ARm B ly S rd -> in_zr a (ly_img ly) -> nf ly a.
Proof.
intros ly S rd a M Ha. pose proof (am_layout _ _ _ _ M) as LO. pose proof (lo_img _ LO) as (I0 & I1 & I2 & I3). unfold in_zr in Ha.
eapply (nf_static_ext ly (ly_img ly)); [exact LO | unfold static_extents; apply in_app_iff; right; right; left; reflexivity | | exact Ha].
intros E. pose proof (f_equal snd E) as E2. cbn in E2. unfold kImgLo, kImgEnd, kFakeStackSize in *. lia.
Qed.
Lemma nf_static : forall ly S rd a, ARm B ly S rd -> Exists (in_zr a) (as_owned_static B) -> nf ly a.
Proof.
intros ly S rd a M H. apply Exists_exists in H as (r & Hr & [H1 H2]).
pose proof (proj1 (Forall_forall _ _) (am_static_img _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hr)) as [S1 S2].
eapply nf_img; [exact M|]. unfold in_zr. lia.
Qed.
Lemma nf_area : forall ly S rd r a, ARm B ly S rd -> In r (asyms_areas B) -> fst r <= a < fst r + snd r -> nf ly a.
Proof.
intros ly S rd r a M Hr Ha. pose proof (proj1 (Forall_forall _ _) (aso_cover _ (am_syms _ _ _ _ M)) r Hr) as X.
apply Exists_exists in X as (r' & Hr' & [X1 X2]). eapply nf_static; [exact M|]. apply Exists_exists. exists r'. split; [exact Hr'|]. unfold in_zr. lia.
Qed.
Lemma nf_core : forall ly S rd e a, ARm B ly S rd -> In e (core_extents ly) -> fst e <= a < fst e + snd e -> nf ly a.
Proof.
intros ly S rd e a M He Ha. pose proof (am_layout _ _ _ _ M) as LO. eapply nf_static_ext; [exact LO | | | exact Ha].
- unfold core_extents in He. unfold static_extents, owned_extents. cbn in He |- *. intuition.
- intros ->. unfold core_extents in He. cbn in He.
lazymatch eval cbv in depot_has_trace with
| true => destruct He as [E|[E|[E|[E|[E|[E|[]]]]]]]; pose proof (f_equal snd E) as E2; cbn in E2; unfold kPtrArrayResv, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kFakeStackSize in E2; lia
| false => destruct He as [E|[E|[E|[E|[E|[E|[]]]]]]]; revert E; repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  intros E; pose proof (f_equal snd E) as E2; cbn in E2; unfold kPtrArrayResv, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kFakeStackSize in E2; lia
end.
Qed.
Lemma nf_rinfo : forall ly S rd a, ARm B ly S rd -> ly_space ly + kRegionInfoOff <= a < ly_space ly + kRegionInfoOff + 4096 -> nf ly a.
Proof.
intros ly S rd a M Ha. pose proof (am_layout _ _ _ _ M) as LO. pose proof (lo_space_in _ LO) as [S1 S2]. unfold kRegionInfoOff, kSpaceSize in *.
apply (nf_prim ly a LO). lia.
Qed.
Lemma nf_F_low : forall ly S rd a, ARm B ly S rd -> ly_F ly + 88 <= a < ly_F ly + kFakeFlagsOff -> nf ly a.
Proof.
intros ly S rd a M Ha. pose proof (am_layout _ _ _ _ M) as LO. destruct (F_app ly LO) as (F0 & FZ & _). unfold nf. split; [right; lia |].
apply (nf2_app ly a LO). unfold kFakeFlagsOff, kFakeStackSize in *. lia.
Qed.
Lemma nf_meta : forall ly S rd k a, ARm B ly S rd -> In k (st_chunks S) ->
ck_base B ly k - (match ck_beg k with PSec _ _ => kPage | _ => 0 end) <= a < ck_base B ly k + ck_rz k -> nf ly a.
Proof.
intros ly S rd k a M Hk Ha. pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal).
pose proof (region_in_prim ly (prim_class o) (am_layout _ _ _ _ M) ltac:(lia)) as (R1 & R2 & _).
apply (nf_prim ly a (am_layout _ _ _ _ M)). lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
eapply (nf_sec ly S rd (ly_sec ly r, sec_map_size (ck_req k))); [exact M | exact Gin |]. cbn [fst snd]. unfold kPage in *. lia.
Qed.
Lemma nf_batch : forall ly S rd b a, ARm B ly S rd -> In b (all_batches S) ->
ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> nf ly a.
Proof.
intros ly S rd b a M Hb Ha. pose proof (am_wf _ _ _ _ M) as WF. pose proof (am_layout _ _ _ _ M) as LO.
pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; auto).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL. pose proof (mapped_user_bound (as_universe B) 0 0 0 S kBatchClass WF ltac:(unfold kBatchClass; lia)) as MB.
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5).
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2.
unfold kBatchBytes, kUserMapSize, EV_MAX in *.
assert (BX : ly_space ly + b_self b = region_base ly kBatchClass + x) by (unfold region_base; subst x; lia).
apply (nf_prim ly a LO). lia.
Qed.
Lemma hull_below_F : forall ly, layout_ok ly -> fst (ly_img ly) + snd (ly_img ly) <= ly_F ly.
Proof.
intros ly LO. pose proof (lo_img _ LO) as (I0 & I1 & I2 & I3). destruct (F_app ly LO) as (F0 & _ & _).
pose proof (pairwise_In zdisjoint (static_extents ly) (ly_F ly, kFakeStackSize) (ly_img ly) (owned_extents ly) [_; _] eq_refl (lo_disj _ LO)
ltac:(unfold owned_extents; cbn; tauto) (or_intror (or_introl eq_refl))) as DF.
unfold zdisjoint in DF. cbn [fst snd] in DF. unfold kImgLo, kFakeStackSize in *. lia.
Qed.
Lemma nf_shadow_hull : forall ly a, layout_ok ly ->
shadow_addr (fst (ly_img ly)) <= a < shadow_addr (fst (ly_img ly)) + snd (ly_img ly) / 8 -> nf ly a.
Proof.
intros ly a LO Ha. pose proof (lo_img _ LO) as (I0 & I1 & I2 & I3). pose proof (hull_below_F ly LO) as HF. destruct (F_app ly LO) as (F0 & FZ & _).
rewrite I0 in *. unfold kImgLo in *.
assert (A1 : SHADOW_OFF + 8192 <= a < SHADOW_OFF + 8192 + snd (ly_img ly) / 8) by (unfold shadow_addr in Ha; change (65536 / 8) with 8192 in Ha; lia).
assert (D8 : snd (ly_img ly) / 8 <= (ly_F ly - 65536) / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.mul_div_le (ly_F ly - 65536) 8 ltac:(lia)) as M8.
split.
- left. apply (nf1_band ly a LO). unfold SHADOW_OFF, kHighMemBeg, kImgEnd in *. lia.
- left. unfold shadow_addr, SHADOW_OFF in *. pose proof (Z.mul_div_le (ly_F ly) 8 ltac:(lia)). pose proof (Z_div_mod_eq_full (ly_F ly) 8).
assert ((ly_F ly - 65536) / 8 = ly_F ly / 8 - 8192) by (replace (ly_F ly - 65536) with (ly_F ly + (-8192) * 8) by lia; rewrite Z.div_add by lia; lia). lia.
Qed.
Lemma nf_shadow_static : forall ly S rd r a, ARm B ly S rd -> In r (as_owned_static B) ->
shadow_addr (fst r) <= a < shadow_addr (fst r) + (snd r + 7) / 8 -> nf ly a.
Proof.
intros ly S rd r a M Hr Ha. pose proof (am_layout _ _ _ _ M) as LO. apply (nf_shadow_hull ly a LO).
pose proof (lo_img _ LO) as (I0 & I1 & I2 & I3).
pose proof (proj1 (Forall_forall _ _) (am_static_img _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hr)) as [R1 R2].
pose proof (proj1 (Forall_forall _ _) (aso_static _ (am_syms _ _ _ _ M)) r Hr) as (T1 & T2 & T3).
unfold shadow_addr in *.
pose proof (Z.div_le_mono (fst (ly_img ly)) (fst r) 8 ltac:(lia) ltac:(lia)).
unfold page_aligned in I3. apply Z.mod_divide in I3 as [q Hq]; [|lia]. rewrite I0 in *. unfold kImgLo in *. change (65536 / 8) with 8192 in *.
assert (E2 : snd (ly_img ly) / 8 = q * 512) by (rewrite Hq; replace (q * 4096) with ((q * 512) * 8) by lia; apply Z_div_mult; lia).
pose proof (Z_div_mod_eq_full (fst r) 8) as DM1. pose proof (Z.mod_pos_bound (fst r) 8 ltac:(lia)) as MB1.
pose proof (Z_div_mod_eq_full (snd r + 7) 8) as DM2. pose proof (Z.mod_pos_bound (snd r + 7) 8 ltac:(lia)) as MB2.
rewrite E2. lia.
Qed.
Ltac fcons' := apply Forall_cons; [cbn; lia|].
Lemma region_cells_nf : forall ly S rd c, ARm B ly S rd -> 1 <= c <= 31 -> Forall (cell_bytes_nf ly) (region_cells S c).
Proof.
intros ly S rd c M Hc. apply (Forall_cnf_of_range ly _ (ly_space ly + kRegionInfoOff) 4096); [intros a Ha; eapply nf_rinfo; [exact M | exact Ha]|].
unfold region_cells, kRegionInfoOff. repeat fcons'. apply Forall_nil.
Qed.
Lemma cache_cells_nf : forall ly S rd c, ARm B ly S rd -> 1 <= c <= 31 -> Forall (cell_bytes_nf ly) (cache_cells S c).
Proof.
intros ly S rd c M Hc.
assert (OR : nf_range ly (ly_T ly) kThreadObjSize).
{ intros a Ha. eapply (nf_core ly S rd (ly_T ly, kThreadObjSize)); [exact M | unfold core_extents; cbn; tauto | exact Ha]. }
apply (Forall_cnf_of_range ly _ (ly_T ly) kThreadObjSize OR).
pose proof (wf_classes _ _ _ _ _ (am_wf _ _ _ _ M) c Hc) as CL. pose proof (wr_cache _ _ _ _ _ _ CL) as WC. pose proof (class_ok c Hc) as (_ & _ & _ & K4 & _).
unfold cache_cells, t_cache, kThreadObjSize. destruct (st_cache_inited S).
- destruct WC as [PM PL]. repeat fcons'. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i v] & <- & Hiv). cbn [fst snd c_at c_w z4 c4 aeval aoff].
apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. lia.
- repeat fcons'. apply Forall_nil.
Qed.
Lemma chunk_cells_nf : forall ly S rd k, ARm B ly S rd -> In k (st_chunks S) -> Forall (cell_bytes_nf ly) (chunk_cells k).
Proof.
intros ly S rd k M Hk. pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
assert (OR : nf_range ly (ck_base B ly k) (ck_rz k)).
{ intros a Ha. eapply nf_meta; [exact M | exact Hk |]. destruct (ck_beg k); unfold kPage; lia. }
apply (Forall_cnf_of_range ly _ _ _ OR).
assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
{ intros d. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia. }
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
{ intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia. }
assert (EA0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
unfold chunk_cells, kChunkHeaderSize. apply Forall_app. split.
- repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil.
- destruct (Z.eqb_spec (ck_rz k) 16); [apply Forall_nil|].
assert (32 <= ck_rz k). { apply Z.mod_divide in G6 as [q Hq]; [|lia]. lia. }
repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil.
Qed.
Lemma area_nf_range : forall ly S rd r, ARm B ly S rd -> In r (asyms_areas B) -> nf_range ly (fst r) (snd r).
Proof. intros ly S rd r M Hr a Ha. eapply nf_area; eassumption. Qed.
Lemma inst_nf_range : forall ly S rd, ARm B ly S rd -> nf_range ly (as_inst B) 3632.
Proof. intros ly S rd M. apply (area_nf_range ly S rd (as_inst B, 3632) M). cbn. tauto. Qed.
Lemma sec_cells_nf : forall ly S rd, ARm B ly S rd -> Forall (cell_bytes_nf ly) (sec_cells S).
Proof.
intros ly S rd M. pose proof (wf_secondary _ _ _ _ _ (am_wf _ _ _ _ M)) as X. destruct X as [Snd Sac Sal Sres Sral].
unfold sec_cells.
apply Forall_cons; [eapply cnf_of_range; [exact (inst_nf_range ly S rd M) | cbn; unfold o_sec_reserved; lia | cbn; unfold o_sec_reserved; lia]|].
apply Forall_cons; [eapply cnf_of_range; [exact (inst_nf_range ly S rd M) | cbn; unfold o_sec_n; lia | cbn; unfold o_sec_n; lia]|].
apply Forall_cons; [eapply cnf_of_range; [exact (inst_nf_range ly S rd M) | cbn; unfold o_sec_mutex; lia | cbn; unfold o_sec_mutex; lia]|].
apply Forall_app. split.
- apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
eapply cnf_of_range; [intros a Ha; eapply (nf_core ly S rd (ly_Q ly, kPtrArrayResv)); [exact M | unfold core_extents; cbn; tauto | exact Ha] | cbn; lia |].
cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
- apply Forall_forall. intros c Hc. apply in_flat_map in Hc as (k & Hk & Hc).
pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg k) as [|o|r o|c' p] eqn:Eb; try solve [destruct Hc].
destruct GG as (-> & _ & Gbase & Gext & Gin & _).
assert (OR : nf_range ly (ly_sec ly r) kPage).
{ intros a Ha. eapply nf_meta; [exact M | exact Hk |]. rewrite Eb. unfold kPage in *. lia. }
unfold kPage in OR.
destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; (eapply cnf_of_range; [exact OR | cbn; lia | cbn; lia]).
Qed.
Lemma batch_cells_nf : forall ly S rd l, ARm B ly S rd -> incl l (all_batches S) -> Forall (cell_bytes_nf ly) (batch_cells l).
Proof.
intros ly S rd l M. induction l as [|b t IH]; intros Hincl; [apply Forall_nil|]. cbn [batch_cells].
pose proof (wq_batches _ (wf_quarantine _ _ _ _ _ (am_wf _ _ _ _ M))) as BL.
pose proof (proj1 (Forall_forall _ _) BL b (Hincl b (or_introl eq_refl))) as [L1 L2]. unfold kBatchSlots in L2.
assert (OR : nf_range ly (ly_space ly + b_self b) kBatchBytes) by (intros a Ha; eapply nf_batch; [exact M | apply Hincl; left; reflexivity | exact Ha]).
unfold kBatchBytes in OR.
apply Forall_cons; [eapply cnf_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cnf_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cnf_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_app. split.
- apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i k] & <- & Hik). apply in_combine_l in Hik. apply in_seq in Hik.
eapply cnf_of_range; [exact OR | cbn; lia | cbn; lia].
- apply IH. intros x Hx. apply Hincl. right. exact Hx.
Qed.
Lemma quar_cells_nf : forall ly S rd, ARm B ly S rd -> Forall (cell_bytes_nf ly) (quar_cells S).
Proof.
intros ly S rd M.
assert (ORT : nf_range ly (ly_T ly) kThreadObjSize).
{ intros a Ha. eapply (nf_core ly S rd (ly_T ly, kThreadObjSize)); [exact M | unfold core_extents; cbn; tauto | exact Ha]. }
pose proof (inst_nf_range ly S rd M) as ORI. unfold kThreadObjSize in ORT.
unfold quar_cells, qc_cells, o_q_cmutex, o_q_rmutex, o_q_size, t_qc.
apply Forall_cons; [eapply cnf_of_range; [exact ORI | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cnf_of_range; [exact ORI | cbn; lia | cbn; lia]|].
apply Forall_app. split.
- do 4 (apply Forall_cons; [eapply cnf_of_range; [exact ORT | cbn; lia | cbn; lia]|]).
eapply batch_cells_nf; [exact M | intros b Hb; unfold all_batches; apply in_app_iff; left; exact Hb].
- do 4 (apply Forall_cons; [eapply cnf_of_range; [exact ORI | cbn; lia | cbn; lia]|]).
eapply batch_cells_nf; [exact M | intros b Hb; unfold all_batches; apply in_app_iff; right; exact Hb].
Qed.
Definition fs_hdr : list acell := [z8 (AF 88) kStackSizeLog; z1 (AF 96) 0].
Definition fs_hints (f : fakestack) : list acell :=
map (fun iv => z8 (AF (8 * Z.of_nat (fst iv))) (snd iv)) (combine (seq 0 11) (fs_hint f)).
Lemma fs_cells_split : forall S, fs_cells S = fs_hdr ++ fs_hints (st_fs S).
Proof. intros S. reflexivity. Qed.
Lemma fs_hdr_nf : forall ly S rd, ARm B ly S rd -> Forall (cell_bytes_nf ly) fs_hdr.
Proof.
intros ly S rd M. assert (OR : nf_range ly (ly_F ly + 88) (kFakeFlagsOff - 88)) by (intros a Ha; eapply nf_F_low; [exact M | lia]).
unfold kFakeFlagsOff in OR. unfold fs_hdr.
apply Forall_cons; [eapply cnf_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cnf_of_range; [exact OR | cbn; lia | cbn; lia]|]. apply Forall_nil.
Qed.
Lemma depot_cells_nf : forall ly S rd, ARm B ly S rd -> Forall (cell_bytes_nf ly) (depot_cells ly S).
Proof.
intros ly S rd M.
pose proof (area_nf_range ly S rd (as_depot B, 4 * 2 ^ 20 + 32) M ltac:(cbn; tauto)) as ORD.
pose proof (area_nf_range ly S rd (as_store B, 32) M ltac:(cbn; tauto)) as ORS. cbn [fst snd] in ORD, ORS.
unfold depot_cells, d_nuniq, d_map1, s_total, s_block0.
lazymatch eval cbv in depot_has_trace with
| true =>
apply Forall_cons; [eapply cnf_of_range; [exact ORD | cbn; lia | cbn; lia]|];
apply Forall_cons; [eapply cnf_of_range; [exact ORD | cbn; lia | cbn; lia]|];
apply Forall_cons; [eapply cnf_of_range; [exact ORS | cbn; lia | cbn; lia]|];
apply Forall_cons; [eapply cnf_of_range; [exact ORS | cbn; lia | cbn; lia]|]; apply Forall_nil
| false =>
(* Knock: the same cell addresses before and after the first Put (8 cells before, 5 after); only their values differ. All
   lie in the depot area (as_depot B, 4 MiB + 32) or the store area (as_store B, 32). *)
unfold d_mu, s_alloc, s_stored0, s_mtx0, d_map1; destruct (st_depot S);
repeat (apply Forall_cons; [first [eapply cnf_of_range; [exact ORD | cbn; lia | cbn; lia]
                                 | eapply cnf_of_range; [exact ORS | cbn; lia | cbn; lia]] |]); apply Forall_nil
end.
Qed.
Lemma ialloc_cells_nf : forall ly S rd, ARm B ly S rd -> Forall (cell_bytes_nf ly) (ialloc_cells B S).
Proof.
intros ly S rd M. pose proof (aso_ialloc _ (am_syms _ _ _ _ M)) as [I1 I2].
pose proof (area_nf_range ly S rd (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B) M ltac:(cbn; tauto)) as ORA.
pose proof (area_nf_range ly S rd (as_ialloc_flag B, 2) M ltac:(cbn; tauto)) as ORF. cbn [fst snd] in ORA, ORF.
unfold ialloc_cells.
apply Forall_cons; [eapply cnf_of_range; [exact ORF | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cnf_of_range; [exact ORF | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cnf_of_range; [exact ORA | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cnf_of_range; [exact ORA | cbn; lia | cbn; lia]|]. apply Forall_nil.
Qed.
Lemma thread_cells_nf : forall ly S rd, ARm B ly S rd -> Forall (cell_bytes_nf ly) thread_cells.
Proof.
intros ly S rd M. unfold thread_cells, t_unwinding. apply Forall_cons; [|apply Forall_nil].
eapply cnf_of_range; [intros a Ha; eapply (nf_core ly S rd (ly_T ly, kThreadObjSize)); [exact M | unfold core_extents; cbn; tauto | exact Ha] | cbn; lia | cbn; unfold kThreadObjSize; lia].
Qed.
Lemma Forall_flat_map'' : forall {X Y} (P : Y -> Prop) (f : X -> list Y) (l : list X),
(forall x, In x l -> Forall P (f x)) -> Forall P (flat_map f l).
Proof. intros X Y P f l H. apply Forall_forall. intros y Hy. apply in_flat_map in Hy as (x & Hx & Hy). exact (proj1 (Forall_forall _ _) (H x Hx) y Hy). Qed.
Lemma zseq_In' : forall lo n x, In x (zseq lo n) -> lo <= x < lo + Z.max n 0.
Proof. intros lo n x H. unfold zseq in H. apply in_map_iff in H as (k & <- & Hk). apply in_seq in Hk. lia. Qed.
Lemma const_cells_nf : forall ly S rd, ARm B ly S rd -> Forall (cell_bytes_nf ly) (as_const B ly).
Proof.
intros ly S rd M. eapply Forall_impl; [|exact (am_const_owned _ _ _ _ M)]. intros c Hc k Hk.
destruct (Hc k Hk) as [O|[O|O]].
- eapply nf_static; [exact M | exact O].
- apply Exists_exists in O as (e & He & Hin). eapply nf_core; [exact M | exact He | exact Hin].
- apply Exists_exists in O as (r & Hr & Hin). eapply nf_shadow_static; [exact M | exact Hr | exact Hin].
Qed.
Definition flags_apartb (c1 c2 : Z) : bool :=
(c1 =? c2) || (fs_flags_off c1 + fs_frames c1 <=? fs_flags_off c2) || (fs_flags_off c2 + fs_frames c2 <=? fs_flags_off c1).
Lemma flags_apart : forall c1 c2, 0 <= c1 <= 10 -> 0 <= c2 <= 10 ->
c1 = c2 \/ fs_flags_off c1 + fs_frames c1 <= fs_flags_off c2 \/ fs_flags_off c2 + fs_frames c2 <= fs_flags_off c1.
Proof.
assert (H : zall (Z.to_nat (10 - 0 + 1)) 0 (fun c1 => zall (Z.to_nat (10 - 0 + 1)) 0 (flags_apartb c1)) = true) by (vm_compute; reflexivity).
intros c1 c2 H1 H2. pose proof (zall_range 0 10 _ H c1 H1) as X. cbv beta in X. pose proof (zall_range 0 10 _ X c2 H2) as Y.
unfold flags_apartb in Y. apply orb_prop in Y as [Y|Y]; [apply orb_prop in Y as [Y|Y]|];
[left; apply Z.eqb_eq; exact Y | right; left; apply Z.leb_le; exact Y | right; right; apply Z.leb_le; exact Y].
Qed.
Lemma flag_addr_inj : forall ly c1 p1 c2 p2, 0 <= c1 <= 10 -> 0 <= p1 < fs_frames c1 -> 0 <= c2 <= 10 -> 0 <= p2 < fs_frames c2 ->
flag_addr ly c1 p1 = flag_addr ly c2 p2 -> c1 = c2 /\ p1 = p2.
Proof.
intros ly c1 p1 c2 p2 H1 Hp1 H2 Hp2 E. unfold flag_addr, fs_flag_off in E.
destruct (flags_apart c1 c2 H1 H2) as [Ec|[D|D]]; [subst c2; split; [reflexivity | lia] | exfalso; lia | exfalso; lia].
Qed.
Lemma mem_pos_app : forall l1 l2 cid pos, mem_pos (l1 ++ l2) cid pos = mem_pos l1 cid pos || mem_pos l2 cid pos.
Proof. induction l1 as [|[c q] t IH]; intros l2 cid pos; cbn; [reflexivity|]. rewrite IH. destruct ((c =? cid) && (q =? pos))%bool; reflexivity. Qed.
Lemma Forall_cell_holds_agree_nf : forall ly S rd rd' l,
(forall a, aowned B ly S a -> nf ly a -> rd' a = rd a) -> Forall (cell_bytes_owned B ly S) l -> Forall (cell_bytes_nf ly) l ->
Forall (cell_holds B ly rd) l -> Forall (cell_holds B ly rd') l.
Proof.
intros ly S rd rd' l AG OW NF H. apply Forall_forall. intros c Hc.
eapply cell_holds_agree; [exact (proj1 (Forall_forall _ _) H c Hc)|]. intros k Hk.
apply AG; [exact (proj1 (Forall_forall _ _) OW c Hc k Hk) | exact (proj1 (Forall_forall _ _) NF c Hc k Hk)].
Qed.
Lemma am_cells_set_fs : forall ly S rd rd' f,
ARm B ly S rd -> (forall a, aowned B ly S a -> nf ly a -> rd' a = rd a) ->
Forall (cell_holds B ly rd') (fs_hints f) ->
Forall (cell_holds B ly rd') (acells B ly (set_fs f S)).
Proof.
intros ly S rd rd' f M AGN HH. pose proof (am_cells _ _ _ _ M) as X. pose proof (acells_owned B ly S rd M) as OW.
unfold acells in X, OW |- *.
change (flat_map (region_cells (set_fs f S)) (zseq 1 31)) with (flat_map (region_cells S) (zseq 1 31)).
change (flat_map (cache_cells (set_fs f S)) (zseq 1 31)) with (flat_map (cache_cells S) (zseq 1 31)).
change (st_chunks (set_fs f S)) with (st_chunks S). change (sec_cells (set_fs f S)) with (sec_cells S).
change (quar_cells (set_fs f S)) with (quar_cells S). change (depot_cells ly (set_fs f S)) with (depot_cells ly S).
change (ialloc_cells B (set_fs f S)) with (ialloc_cells B S).
rewrite (fs_cells_split (set_fs f S)). change (st_fs (set_fs f S)) with f. rewrite (fs_cells_split S) in X, OW.
apply Forall_app in X as [XR X]. apply Forall_app in X as [XC X]. apply Forall_app in X as [XK X]. apply Forall_app in X as [XS X].
apply Forall_app in X as [XQ X]. apply Forall_app in X as [XF X]. apply Forall_app in X as [XD X]. apply Forall_app in X as [XI XT].
apply Forall_app in XF as [XFH _].
apply Forall_app in OW as [OWR OW]. apply Forall_app in OW as [OWC OW]. apply Forall_app in OW as [OWK OW]. apply Forall_app in OW as [OWS OW].
apply Forall_app in OW as [OWQ OW]. apply Forall_app in OW as [OWF OW]. apply Forall_app in OW as [OWD OW]. apply Forall_app in OW as [OWI OWT].
apply Forall_app in OWF as [OWFH _].
apply Forall_app; split.
{ exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWR (Forall_flat_map'' _ _ _ (fun c Hc => region_cells_nf ly S rd c M ltac:(pose proof (zseq_In' 1 31 c Hc); lia))) XR). }
apply Forall_app; split.
{ exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWC (Forall_flat_map'' _ _ _ (fun c Hc => cache_cells_nf ly S rd c M ltac:(pose proof (zseq_In' 1 31 c Hc); lia))) XC). }
apply Forall_app; split.
{ exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWK (Forall_flat_map'' _ _ _ (fun k Hk => chunk_cells_nf ly S rd k M Hk)) XK). }
apply Forall_app; split. { exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWS (sec_cells_nf ly S rd M) XS). }
apply Forall_app; split. { exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWQ (quar_cells_nf ly S rd M) XQ). }
apply Forall_app; split.
{ apply Forall_app; split; [exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWFH (fs_hdr_nf ly S rd M) XFH) | exact HH]. }
apply Forall_app; split. { exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWD (depot_cells_nf ly S rd M) XD). }
apply Forall_app; split. { exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWI (ialloc_cells_nf ly S rd M) XI). }
exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWT (thread_cells_nf ly S rd M) XT).
Qed.
Lemma zshadow_range_facts : forall ly S rd r, ARm B ly S rd -> In r (zero_shadow_ranges B ly) ->
fst r mod 8 = 0 /\ 0 <= fst r /\ 0 <= snd r /\ fst r + snd r <= kHighMemEnd /\ zdisjoint r (ly_F ly, kFakeStackSize).
Proof.
intros ly S rd [lo len] M Hin. cbn [fst snd]. pose proof (am_layout _ _ _ _ M) as LO.
unfold zero_shadow_ranges in Hin. destruct Hin as [E|Hin].
- injection E as <- <-. pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). unfold page_aligned in T5.
splits.
+ apply Z.mod_divide; [lia|]. apply Z.mod_divide in T5 as [q Hq]; [|lia]. exists (q * 512). lia.
+ unfold kHighMemBeg in T7. lia.
+ lia.
+ lia.
+ apply zdisjoint_sym. eapply (pairwise_In zdisjoint (static_extents ly) _ _ (owned_extents ly) [_; _]); [unfold static_extents; reflexivity | exact (lo_disj _ LO) | unfold owned_extents; cbn; tauto | left; reflexivity].
- pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (am_syms _ _ _ _ M)) _ Hin) as (Z1 & Z2 & Z3 & Z4 & Z5). cbn [fst snd] in *.
pose proof (proj1 (Forall_forall _ _) (am_static_img _ _ _ _ M) (lo, len) ltac:(apply in_app_iff; right; exact Hin)) as [R1 R2]. cbn [fst snd] in R1, R2.
pose proof (hull_below_F ly LO) as HF.
splits; [exact Z3 | exact Z1 | exact Z2 | unfold kLowMemEnd, kHighMemEnd in *; lia |]. unfold zdisjoint. cbn [fst snd]. left. lia.
Qed.
Lemma zshadow_low : forall ly S rd r i, ARm B ly S rd -> In r (zero_shadow_ranges B ly) -> 0 <= i < snd r / 8 ->
SHADOW_OFF <= shadow_addr (fst r) + i < kHighMemBeg.
Proof.
intros ly S rd r i M Hr Hi. destruct (zshadow_range_facts ly S rd r M Hr) as (A1 & A2 & A3 & A4 & A5).
assert (DM : snd r / 8 <= (snd r + 7) / 8) by (apply Z.div_le_mono; lia).
pose proof (shadow_range_below (fst r) (snd r) A2 A3 A4). pose proof (proj1 (shadow_addr_bounds (fst r) A2)). lia.
Qed.
Lemma zshadow_not_frame_shadow : forall ly S rd r i cid pos, ARm B ly S rd -> In r (zero_shadow_ranges B ly) -> 0 <= i < snd r / 8 ->
0 <= cid <= 10 -> 0 <= pos < fs_frames cid ->
~ in_zr (shadow_addr (fst r) + i) (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8).
Proof.
intros ly S rd r i cid pos M Hr Hi Hc Hp IN. unfold in_zr in IN. cbn [fst snd] in IN.
destruct (zshadow_range_facts ly S rd r M Hr) as (A1 & A2 & A3 & A4 & D). unfold zdisjoint in D. cbn [fst snd] in D.
pose proof (am_layout _ _ _ _ M) as LO. pose proof (frame_off_bounds cid pos Hc Hp) as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (lo_F_al _ LO) as FAL. unfold page_aligned in FAL. unfold frame_addr, shadow_addr in *.
apply Z.mod_divide in FAL as [qf Hqf]; [|lia]. apply Z.mod_divide in B3 as [qo Hqo]; [|lia]. apply Z.mod_divide in B5 as [qb Hqb]; [|lia].
apply Z.mod_divide in A1 as [qr Hqr]; [|lia].
assert (E1 : (ly_F ly + fs_frame_off cid pos) / 8 = qf * 512 + qo * 8) by (rewrite Hqf, Hqo; symmetry; apply (Z.div_unique _ 8 _ 0); lia).
assert (E2 : fs_frame_bytes cid / 8 = qb * 8) by (rewrite Hqb; symmetry; apply (Z.div_unique _ 8 _ 0); lia).
assert (E3 : fst r / 8 = qr) by (rewrite Hqr; symmetry; apply (Z.div_unique _ 8 _ 0); lia).
rewrite E1, E2, E3 in IN. pose proof (Z.div_le_upper_bound (snd r) 8 (snd r) ltac:(lia) ltac:(lia)) as DU.
assert (DL : 8 * (snd r / 8) <= snd r) by (apply Z.mul_div_le; lia).
clear - IN D B1 B2 B6 Hqf Hqo Hqb Hqr B4 Hc Hi DL. unfold kFakeFramesOff in *. nia.
Qed.
Lemma ashadow_app : forall ly S rd g v, ARm B ly S rd -> ashadow B ly S g = Some v -> 4096 <= g /\ g + 7 <= kHighMemEnd.
Proof.
intros ly S rd g v M H. pose proof (am_layout _ _ _ _ M) as LO. pose proof (lo_high _ LO) as [P1 P2].
unfold ashadow in H. destruct (find_chunk_at B ly (st_chunks S) g) as [k|] eqn:F.
- apply find_chunk_at_In in F as [Hk Hg]. pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & _).
assert (ck_extent k mod 8 = 0 /\ ck_base B ly k mod 8 = 0) as [E1 E2].
{ pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & G3 & _ & _ & _ & G7 & _ & GG). split; [|apply Z.mod_divide in G3 as [q Hq]; [|lia]; rewrite Hq; replace (q * 16) with ((q * 2) * 8) by lia; apply Z_mod_mult].
destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & -> & _). pose proof (class_ok (prim_class o) ltac:(lia)) as (_ & K2 & _).
apply Z.mod_divide in K2 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((q * 4) * 8) by lia. apply Z_mod_mult.
- destruct GG as (_ & Gp & _ & -> & _). pose proof (secondary_geometry (ck_req k) ltac:(lia) Gp) as (_ & _ & _ & _ & SM & _).
apply Z.mod_divide in SM as [q Hq]; [|unfold kPage; lia]. rewrite Hq. unfold kPage. replace (q * 4096 - 4096) with ((q * 512 - 512) * 8) by lia. apply Z_mod_mult. }
apply Z.mod_divide in E1 as [q1 Hq1]; [|lia]. apply Z.mod_divide in E2 as [q2 Hq2]; [|lia]. destruct G1 as [G0 _].
ceil; unfold ASAN_CEIL, kHighMemEnd in *. split; [lia|]. clear - Hg Hq1 Hq2 G2 CR0. nia.
- destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:R; [|discriminate].
apply in_rangesb_true in R as (lo & len & Hin & Hg). unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
+ apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
pose proof (region_in_prim ly c LO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wf_classes _ _ _ _ _ (am_wf _ _ _ _ M) c ltac:(lia)) as CL.
pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_fa _ _ _ _ _ _ CL) as [A2 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as A3. pose proof (wr_mapped_al _ _ _ _ _ _ CL) as A4.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S c (am_wf _ _ _ _ M) ltac:(lia)) as MB. unfold kUserMapSize, EV_MAX, kFreeArrayMax in *.
unfold fa_base, kFreeArrayOffset in Hin. unfold region_base in *.
apply Z.mod_divide in R3 as [q3 Hq3]; [|lia]. apply Z.mod_divide in A4 as [q4 Hq4]; [|lia].
ceil; unfold ASAN_CEIL, kHighMemEnd, kHighMemBeg, kPrimResvSize in *.
destruct Hin as [E|[E|[]]]; injection E as <- <-; (split; [lia | nia]).
+ pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) _ Hin) as (PA & [I1 I2] & I3). cbn [fst snd] in PA, I1, I2, I3.
ceil; unfold YG0f.page_aligned, ASAN_CEIL, kHighMemEnd, kHighMemBeg, kLowShadowBeg in *.
apply Z.mod_divide in PA as [q Hq]; [|lia]. split; [lia | clear - Hg Hq I2 I3 CR0; nia].
Qed.
Lemma ashadow_low : forall ly S rd g v, ARm B ly S rd -> ashadow B ly S g = Some v -> SHADOW_OFF <= shadow_addr g < kHighMemBeg.
Proof.
intros ly S rd g v M H. destruct (ashadow_app ly S rd g v M H) as [Ga Gb].
destruct (shadow_addr_bounds g ltac:(lia)) as [X Y]. split; [exact X | exact (Y Gb)].
Qed.
Theorem astack_free_law_ok : astack_free_law segs B.
Proof.
intros ly S W mem md mem' md' cid pos (M & L & BUD & MW & HS) Hin HF0 AGR VIS Hvm Hlz He HK.
set (S' := stack_free_state cid pos S).
set (rd := aview segs (w_H W) mem) in *. set (rd' := aview segs (w_H W) mem') in *.
pose proof (am_wf _ _ _ _ M) as WF. pose proof (am_layout _ _ _ _ M) as LO. pose proof (wf_fakestack _ _ _ _ _ WF) as [[LH FH] ND LV].
destruct (del_pos_spec _ _ _ ND Hin) as (l1 & l2 & EL & ED).
assert (FR' : frames S' = l1 ++ l2) by (unfold frames, S', stack_free_state; cbn; exact ED).
assert (FR : frames S = l1 ++ (cid, pos) :: l2) by exact EL.
pose proof (proj1 (Forall_forall _ _) LV (cid, pos) Hin) as [Hc Hp]. cbn [fst snd] in Hc, Hp.
pose proof (flag_off_bounds cid pos Hc Hp) as FB.
assert (AG : forall a, aowned B ly S a -> a <> flag_addr ly cid pos -> rd' a = rd a).
{ intros a Ha Hne. apply AGR; [|exact Ha|exact Hne]. pose proof (AR_owned_low_law_ok segs B ly S W mem md a (conj M (conj L (conj BUD (conj MW HS)))) Ha).
ceil. unfold ASAN_CEIL in *. lia. }
assert (AGN : forall a, aowned B ly S a -> nf ly a -> rd' a = rd a).
{ intros a Ha Hn. apply AG; [exact Ha|]. intros ->. unfold nf, flag_addr in Hn. pose proof FB as FB2. unfold kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in Hn, FB2. lia. }
assert (Ecells : acells B ly S' = acells B ly S) by reflexivity.
assert (Ejunk : ajunk B ly S' = ajunk B ly S) by reflexivity.
assert (Eareas : aareas S' = aareas S) by reflexivity.
assert (CL : forall a, aclient_byte B ly S' a -> aclient_byte B ly S a).
{ intros a [X|(cp & Hcp & X)]; [left; exact X | right]. exists cp. split; [|exact X]. rewrite FR' in Hcp. rewrite FR.
apply in_app_iff in Hcp as [Hcp|Hcp]; apply in_app_iff; [left; exact Hcp | right; right; exact Hcp]. }
assert (L' : ALedger segs ly S' md').
{ destruct L; constructor; rewrite ?Hvm, ?Hlz, ?He; assumption. }
destruct (F_app ly LO) as (FH0 & FHZ & _).
assert (AGF : forall g, g mod 8 = 0 -> in_app g 8 -> hfree ly S g -> w_H W (w64 (shadow_addr g)) = false ->
rd' (shadow_addr g) = rd (shadow_addr g)).
{ intros g Hg HA HFg Hh. apply AG; [eapply hfree_shadow_owned; [exact M | exact Hg | exact HA | exact HFg] |].
pose proof (shadow_addr_band_rw g HA) as SB. intros E. unfold flag_addr in E. clear - SB FH0 FHZ FB E.
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kFakeStackSize, kFakeFlagsOff, kFakeFramesOff in *. lia. }
split; [|split; [exact L' | split; [exact BUD | split; [exact (amwf_same md md' Hvm Hlz MW) |
exact (ahs_transfer segs B ly S S' (w_H W) mem mem' (al_img_env segs ly S md LO L) M HS VIS HK (fun a _ C => CL a C) eq_refl AGF)]]]].
pose proof M as M0. destruct M as [Xwf Xuni Xsyms Xlay Xplaced Xconst Xcowned Xcells Xfa Xflags Xdepot Xshadow Xzsh Xjunk Xareas Xclient Xzero Xtsd Ximg].
constructor; try assumption.
-   exact (proj1 (stack_free_ok _ S cid pos Xwf Hin)).
-   exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN (const_cells_owned B ly S rd M0) (const_cells_nf ly S rd M0) Xconst).
-
unfold S', stack_free_state. apply (am_cells_set_fs ly S rd rd' _ M0 AGN). cbn [fs_hint].
pose proof Xcells as XC. unfold acells in XC. rewrite (fs_cells_split S) in XC.
do 5 (apply Forall_app in XC as [_ XC]). apply Forall_app in XC as [XF _]. apply Forall_app in XF as [_ XH].
pose proof (acells_owned B ly S rd M0) as OW. unfold acells in OW. rewrite (fs_cells_split S) in OW.
do 5 (apply Forall_app in OW as [_ OW]). apply Forall_app in OW as [OWF _]. apply Forall_app in OWF as [_ OWH].
apply Forall_forall. intros c Hcin. eapply cell_holds_agree; [exact (proj1 (Forall_forall _ _) XH c Hcin)|]. intros kk Hkk.
apply AG; [exact (proj1 (Forall_forall _ _) OWH c Hcin kk Hkk)|].
unfold fs_hints in Hcin. apply in_map_iff in Hcin as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih.
cbn [c_at c_w z8 c8 aeval aoff] in Hkk |- *. unfold flag_addr. pose proof FB as FB3. clear - Hkk Hih FB3. cbn [fst snd]. unfold kFakeFlagsOff in *. lia.
-
intros c i v Hc' Hi Hv k Hk. change (reg S' c) with (reg S c) in *.
pose proof (wf_classes _ _ _ _ _ Xwf c Hc') as CLS. pose proof (wr_fa_len _ _ _ _ _ _ CLS) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CLS) as FB'.
rewrite AGN; [exact (Xfa c i v Hc' Hi Hv k Hk) | eapply own_fa; [exact M0 | exact Hc' | lia] |].
apply (nf_prim ly _ Xlay). pose proof (region_in_prim ly c Xlay Hc') as (R1 & R2 & _). unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax, kPrimResvSize, kSpaceSize in *.
pose proof (lo_space_in _ Xlay) as [S1 S2]. rewrite region_off_eq in * by lia. unfold kPrimResvSize, kSpaceSize in *. nia.
-
intros c q Hc' Hq. destruct (Z.eq_dec (flag_addr ly c q) (flag_addr ly cid pos)) as [E|NE].
+ destruct (flag_addr_inj ly c q cid pos Hc' Hq Hc Hp E) as [-> ->]. unfold rd' in HF0 |- *. rewrite HF0. f_equal.
rewrite FR'. assert (ND' : List.NoDup (l1 ++ (cid, pos) :: l2)) by (rewrite <- FR; exact ND).
destruct (mem_pos (l1 ++ l2) cid pos) eqn:MP; [|reflexivity]. exfalso.
apply mem_pos_spec in MP. exact (List.NoDup_remove_2 _ _ _ ND' MP).
+ rewrite AG; [| pose proof (flag_off_bounds c q Hc' Hq) as FB''; unfold flag_addr, kFakeFlagsOff in *; eapply own_F_low; [exact M0 | lia] | exact NE].
rewrite (Xflags c q Hc' Hq). f_equal. rewrite FR', FR. rewrite !mem_pos_app. cbn [mem_pos].
destruct (Z.eqb_spec cid c) as [Ec|Ec]; destruct (Z.eqb_spec pos q) as [Eq|Eq]; cbn [andb orb];
[exfalso; apply NE; subst c q; reflexivity | | |]; destruct (mem_pos l1 c q), (mem_pos l2 c q); reflexivity.
-
lazymatch eval cbv in depot_has_trace with
| true =>
destruct Xdepot as (heads & links & D1 & D2 & D3); exists heads, links; split; [|split; [|exact D3]];
[ intros b Hb; destruct (D1 b Hb) as [H1 H2]; split; [exact H1|]; intros k Hk; change (depot_traces ly S') with (depot_traces ly S) in *;
rewrite AGN; [exact (H2 k Hk) | eapply (own_area B ly S rd (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | cbn; tauto | cbn; unfold d_tab_words in Hb; lia] |];
eapply (nf_area ly S rd (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | cbn; tauto | cbn; unfold d_tab_words in Hb; lia]
| intros id Hid; change (depot_ids S') with (depot_ids S) in Hid; destruct (D2 id Hid) as (H1 & H2 & H3); split; [exact H1|];
assert (NB : depot_ids S <= 4097) by (unfold depot_ids; pose proof (wf_depot _ _ _ _ _ Xwf) as [ND' INC]; pose proof (NoDup_incl_length ND' INC); destruct Xuni as (U1 & _); unfold DEPOT_MAX in U1; lia);
assert (OR : forall k, 0 <= k < 16 -> rd' (ly_NB ly + 16 * id + k) = rd (ly_NB ly + 16 * id + k)) by (intros k Hk; apply AGN;
[ eapply (own_core B ly S rd (ly_NB ly, kNodesBlockSize)); [exact M0 | unfold core_extents; cbn; tauto | cbn; unfold kNodesBlockSize; lia]
| eapply (nf_core ly S rd (ly_NB ly, kNodesBlockSize)); [exact M0 | unfold core_extents; cbn; tauto | cbn; unfold kNodesBlockSize; lia] ]);
split; intros k Hk; [rewrite OR by lia; exact (H2 k Hk)|];
replace (ly_NB ly + 16 * id + 8 + Z.of_nat k) with (ly_NB ly + 16 * id + (8 + Z.of_nat k)) by lia; rewrite OR by lia;
replace (ly_NB ly + 16 * id + (8 + Z.of_nat k)) with (ly_NB ly + 16 * id + 8 + Z.of_nat k) by lia; exact (H3 k Hk) ]
| false =>
(* Knock: before the first Put no node is read, so only the table words (owned depot area) must agree; after it, the
   one-trace argument, with the node bytes owned through core_extents_set (both blocks mapped). *)
revert Xdepot; unfold depot_ok; change (st_depot S') with (st_depot S); destruct (st_depot S) as [|t0 ts]; intro Xdepot;
[ destruct Xdepot as (E0 & T0 & I0 & A0); split; [exact E0 |]; split; [| split; [exact I0 | exact A0]];
  intros b Hb k Hk; rewrite AGN; [exact (T0 b Hb k Hk) | eapply (own_area B ly S rd (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | cbn; tauto | cbn; unfold d_tab_words in Hb; lia] |];
  eapply (nf_area ly S rd (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | cbn; tauto | cbn; unfold d_tab_words in Hb; lia]
| destruct Xdepot as (MNB & MSB & heads & links & D1 & D2 & D3); split; [exact MNB|]; split; [exact MSB|];
  exists heads, links; split; [|split; [|exact D3]];
  [ intros b Hb; destruct (D1 b Hb) as [H1 H2]; split; [exact H1|]; intros k Hk; change (depot_traces ly S') with (depot_traces ly S) in *;
    rewrite AGN; [exact (H2 k Hk) | eapply (own_area B ly S rd (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | cbn; tauto | cbn; unfold d_tab_words in Hb; lia] |];
    eapply (nf_area ly S rd (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | cbn; tauto | cbn; unfold d_tab_words in Hb; lia]
  | intros id Hid; change (depot_ids S') with (depot_ids S) in Hid; destruct (D2 id Hid) as (H1 & H2 & H3); split; [exact H1|];
    assert (NB : depot_ids S <= 4097) by (unfold depot_ids; pose proof (wf_depot _ _ _ _ _ Xwf) as [ND' INC]; pose proof (NoDup_incl_length ND' INC); destruct Xuni as (U1 & _); unfold DEPOT_MAX in U1; lia);
    assert (OR : forall k, 0 <= k < 16 -> rd' (ly_NB ly + 16 * id + k) = rd (ly_NB ly + 16 * id + k)) by (intros k Hk; apply AGN;
    [ eapply (own_core B ly S rd (ly_NB ly, kNodesBlockSize)); [exact M0 | rewrite (core_extents_set ly MNB MSB); cbn; tauto | cbn; unfold kNodesBlockSize; lia]
    | eapply (nf_core ly S rd (ly_NB ly, kNodesBlockSize)); [exact M0 | rewrite (core_extents_set ly MNB MSB); cbn; tauto | cbn; unfold kNodesBlockSize; lia] ]);
    split; intros k Hk; [rewrite OR by lia; exact (H2 k Hk)|];
    replace (ly_NB ly + 16 * id + 8 + Z.of_nat k) with (ly_NB ly + 16 * id + (8 + Z.of_nat k)) by lia; rewrite OR by lia;
    replace (ly_NB ly + 16 * id + (8 + Z.of_nat k)) with (ly_NB ly + 16 * id + 8 + Z.of_nat k) by lia; exact (H3 k Hk) ] ]
end.
-
intros g v Hg Hv0. change (ashadow B ly S' g) with (ashadow B ly S g) in Hv0.
rewrite AG; [exact (Xshadow g v Hg Hv0) | eapply ashadow_owned; [exact M0 | exact Hv0] |].
pose proof (ashadow_low ly S rd g v M0 Hv0) as SL. unfold flag_addr. pose proof FB as FB4. clear - SL FH0 FHZ FB4.
unfold SHADOW_OFF, kHighMemBeg, kLowShadowBeg, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. lia.
-
unfold zshadow_ok in *. apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
pose proof (proj1 (Forall_forall _ _) Xzsh r Hr i Hi) as Z0. unfold shadow_of_addr in Z0. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)) in Z0.
rewrite AG; [exact Z0 | eapply own_shadow_zero; [exact M0 | exact Hr | exact Hi] |].
pose proof (zshadow_low ly S rd r i M0 Hr Hi) as SL. unfold flag_addr. pose proof FB as FB4. clear - SL FH0 FHZ FB4.
unfold SHADOW_OFF, kHighMemBeg, kLowShadowBeg, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. lia.
- rewrite Ejunk. eapply Forall_range_vis_keep; [exact VIS | exact Xjunk].
- rewrite Eareas. eapply Forall_range_vis_keep; [exact VIS | exact Xareas].
-
eapply Forall_range_vis_keep; [exact VIS|]. apply Forall_forall. intros r Hr. apply (proj1 (Forall_forall _ _) Xclient).
unfold aclient in Hr |- *. change (st_chunks S') with (st_chunks S) in Hr. rewrite FR' in Hr. rewrite FR. rewrite !in_app_iff in Hr |- *. rewrite !in_map_iff in Hr |- *.
destruct Hr as [Hr|[(cp & E & Hcp)|(cp & E & Hcp)]]; [left; exact Hr | right; left | right; right]; exists cp; split; [exact E| |exact E|];
apply in_app_iff in Hcp as [Hcp|Hcp]; apply in_app_iff; [left; exact Hcp | right; right; exact Hcp | left; exact Hcp | right; right; exact Hcp].
-
apply Forall_forall. intros r Hr i Hi. pose proof (aso_ialloc _ Xsyms) as [I1 I2].
assert (RG : forall z, as_ialloc_lo B <= z < as_ialloc_hi B -> rd' z = rd z).
{ intros z Hz. apply AGN.
- eapply (own_area B ly S rd (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact M0 | cbn; tauto | cbn [fst snd]; lia].
- eapply (nf_area ly S rd (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact M0 | cbn; tauto | cbn [fst snd]; lia]. }
rewrite RG; [exact (proj1 (Forall_forall _ _) Xzero r Hr i Hi)|].
unfold ialloc_zero in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; lia.
Qed.
Definition astack_malloc_law : Prop := forall ly S W mem md mem' md' cid pos hint',
AR segs B ly S W mem md -> 0 <= cid <= 10 ->
fs_probe (Z.to_nat (fs_frames cid)) (fs_live (st_fs S)) cid (znth 0 cid (fs_hint (st_fs S))) = Some (pos, hint') ->
let S' := set_fs (mkFS (zupd cid hint' (fs_hint (st_fs S))) ((cid, pos) :: fs_live (st_fs S))) S in
(forall k, (k < 8)%nat -> aview segs (w_H W) mem' (ly_F ly + 8 * cid + Z.of_nat k) = Some (le_byte hint' 8 k)) ->
aview segs (w_H W) mem' (flag_addr ly cid pos) = Some 1 ->
(forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> ~ (ly_F ly + 8 * cid <= a < ly_F ly + 8 * cid + 8) -> a <> flag_addr ly cid pos ->
~ in_zr a (frame_addr ly cid pos, fs_frame_bytes cid) -> ~ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
(forall a, aview segs (w_H W) mem a <> None -> aview segs (w_H W) mem' a <> None) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
AR segs B ly S' W mem' md'.
Lemma ashadow_app_zone : forall ly S rd g v, ARm B ly S rd -> ashadow B ly S g = Some v ->
(ly_prim ly <= g < ly_prim ly + kPrimResvSize) \/ (exists m len, In (m, len) (sec_extents ly S) /\ m <= g < m + len).
Proof.
intros ly S rd g v M H. unfold ashadow in H.
destruct (find_chunk_at B ly (st_chunks S) g) as [k|] eqn:F.
- apply find_chunk_at_In in F as [Hk Hg].
destruct (extent_zone B ly S rd k M Hk) as [[X1 X2]|(m & len & Hin & X1 & X2)].
+ left. lia.
+ right. exists m, len. split; [exact Hin|]. unfold kPage in *. lia.
- destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:R; [|discriminate].
apply in_rangesb_true in R as (lo & len & Hin & Hg). unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
+ apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
pose proof (region_in_prim ly c (am_layout _ _ _ _ M) ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wf_classes _ _ _ _ _ (am_wf _ _ _ _ M) c ltac:(lia)) as CL.
pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_fa _ _ _ _ _ _ CL) as [A2 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as A3.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S c (am_wf _ _ _ _ M) ltac:(lia)) as MB. unfold kUserMapSize, EV_MAX, kFreeArrayMax in *.
left. unfold fa_base, kFreeArrayOffset in Hin. unfold region_base in *. unfold kPrimResvSize, kSpaceSize in *.
pose proof (lo_space_in _ (am_layout _ _ _ _ M)) as [S1 S2]. rewrite region_off_eq in * by lia. unfold kPrimResvSize, kSpaceSize in *.
destruct Hin as [E|[E|[]]]; injection E as <- <-; nia.
+ right. exists lo, len. split; [exact Hin | exact Hg].
Qed.
Lemma ashadow_not_frame_shadow : forall ly S rd g v cid pos, ARm B ly S rd -> ashadow B ly S g = Some v ->
0 <= cid <= 10 -> 0 <= pos < fs_frames cid ->
~ in_zr (shadow_addr g) (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8).
Proof.
intros ly S rd g v cid pos M H Hc Hp IN. unfold in_zr in IN. cbn [fst snd] in IN.
pose proof (am_layout _ _ _ _ M) as LO. pose proof (frame_off_bounds cid pos Hc Hp) as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (lo_F_al _ LO) as FAL. unfold page_aligned in FAL.
assert (GF : ~ (ly_F ly <= g < ly_F ly + kFakeStackSize)).
{ pose proof (lo_disj _ LO) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & _). do 2 (apply Forall_cons_iff in DP as [_ DP]). apply Forall_cons_iff in DP as [PF _]. unfold zdisjoint in PF. cbn [fst snd] in PF.
destruct (ashadow_app_zone ly S rd g v M H) as [X|(m & len & Hin & X)]; [lia|].
pose proof (pairwise_In zdisjoint _ (m, len) (ly_F ly, kFakeStackSize) (sec_extents ly S) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) Hin
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia. }
unfold frame_addr, shadow_addr in *.
apply Z.mod_divide in FAL as [qf Hqf]; [|lia]. apply Z.mod_divide in B3 as [qo Hqo]; [|lia]. apply Z.mod_divide in B5 as [qb Hqb]; [|lia].
assert (E1 : (ly_F ly + fs_frame_off cid pos) / 8 = qf * 512 + qo * 8) by (rewrite Hqf, Hqo; symmetry; apply (Z.div_unique _ 8 _ 0); lia).
assert (E2 : fs_frame_bytes cid / 8 = qb * 8) by (rewrite Hqb; symmetry; apply (Z.div_unique _ 8 _ 0); lia).
rewrite E1, E2 in IN. pose proof (Z.div_mod g 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound g 8 ltac:(lia)) as MB.
set (g8 := g / 8) in *. set (gm := g mod 8) in *. clearbody g8 gm. clear - IN DM MB GF B1 B2 B6 Hqf Hqo Hqb B4 Hc. unfold kFakeFramesOff in *. lia.
Qed.
Lemma ahs_transfer_grow : forall ly S S' (H : word -> bool) mem mem',
(forall sg, In sg segs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd) ->
ahs B ly S H mem ->
(forall a, aview segs H mem a <> None -> aview segs H mem' a <> None) ->
(forall a, in_band_rw a -> H (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
(forall a, in_band_rw a -> aclient_byte B ly S a -> aclient_byte B ly S' a) ->
sec_extents ly S' = sec_extents ly S ->
(forall g, g mod 8 = 0 -> in_app g 8 -> hfree ly S g -> H (w64 (shadow_addr g)) = false ->
aview segs H mem' (shadow_addr g) = aview segs H mem (shadow_addr g)) ->
ahs B ly S' H mem'.
Proof.
intros ly S S' H mem mem' IMG [HA HZ] VIS HK CL SE AG. split.
- intros a Ha NC HV.
assert (NC0 : ~ aclient_byte B ly S a) by (intros C; exact (NC (CL a Ha C))).
pose proof (HA a Ha NC0 HV) as M0.
destruct (H (w64 a)) eqn:Hh.
+ pose proof (HK a Ha Hh) as E. unfold w64, YG0n.w64 in *. rewrite E. exact M0.
+ apply (proj1 (aview_band segs H mem' a IMG Ha Hh)). apply VIS. apply (proj2 (aview_band segs H mem a IMG Ha Hh)). exact M0.
- exact (ahz_transfer segs ly S S' H mem mem' IMG HZ SE HK AG).
Qed.
Lemma in_combine_seq_iff : forall {A} (l : list A) s i x, In (i, x) (combine (seq s (length l)) l) <-> (s <= i)%nat /\ nth_error l (i - s) = Some x.
Proof.
intros A l. induction l as [|y t IH]; intros s i x; cbn [length seq combine].
- split; [intros [] | intros [_ E]; destruct (i - s)%nat; discriminate E].
- split.
+ intros [E|H]; [injection E as <- <-; split; [lia | rewrite Nat.sub_diag; reflexivity]|].
apply IH in H as [H1 H2]. split; [lia|]. replace (i - s)%nat with (S (i - S s))%nat by lia. exact H2.
+ intros [H1 H2]. destruct (Nat.eq_dec i s) as [->|Hne].
* left. rewrite Nat.sub_diag in H2. injection H2 as ->. reflexivity.
* right. apply IH. split; [lia|]. replace (i - S s)%nat with (Nat.pred (i - s)) by lia. destruct (i - s)%nat eqn:E; [lia|]. cbn. exact H2.
Qed.
Theorem astack_malloc_law_ok : astack_malloc_law.
Proof.
intros ly S W mem md mem' md' cid pos hint' (M & L & BUD & MW & HS) Hc HP S' HW HF1 AGR VIS Hvm Hlz He HK.
set (rd := aview segs (w_H W) mem) in *. set (rd' := aview segs (w_H W) mem') in *.
pose proof (am_wf _ _ _ _ M) as WF. pose proof (am_layout _ _ _ _ M) as LO. pose proof (wf_fakestack _ _ _ _ _ WF) as [[LH FH] ND LV].
pose proof (fs_frames_pos cid Hc) as HN.
destruct (fs_probe_some _ _ _ _ _ _ HN HP) as (h & Hh1 & Eh' & Epos & NM).
assert (Hp : 0 <= pos < fs_frames cid) by (rewrite Epos; apply Z.mod_pos_bound; exact HN).
assert (NIN : ~ In (cid, pos) (frames S)) by (unfold frames; apply mem_pos_false; exact NM).
pose proof (flag_off_bounds cid pos Hc Hp) as FB. pose proof (frame_off_bounds cid pos Hc Hp) as (FO1 & FO2 & FO3 & FO4 & FO5 & FO6).
destruct (F_app ly LO) as (FH0 & FHZ & _). ceil.
assert (FR2 : ly_F ly + kFakeStackSize <= SHADOW_OFF \/ kHighMemBeg <= ly_F ly) by (clear - FHZ; unfold kLowShadowBeg, SHADOW_OFF in *; lia).
assert (F64 : ly_F ly + kFakeStackSize < 2 ^ 64) by (clear - FHZ CR; unfold kLowShadowBeg, ASAN_CEIL in *; lia).
assert (FR' : frames S' = (cid, pos) :: frames S) by reflexivity.
assert (FSL : shadow_addr (ly_F ly + fs_frame_off cid pos) + fs_frame_bytes cid / 8 <= kHighMemBeg).
{ apply shadow_range_below; [unfold kFakeFramesOff in FO1; lia | lia | clear - FHZ FO2 FO6 CR; unfold ASAN_CEIL, kHighMemEnd, kLowShadowBeg in *; lia]. }
pose proof (proj1 (shadow_addr_bounds (ly_F ly + fs_frame_off cid pos) ltac:(unfold kFakeFramesOff in FO1; lia))) as FSLO.
assert (AGN : forall a, aowned B ly S a -> nf ly a -> rd' a = rd a).
{ intros a Ha [Hn Hb]. apply AGR; [| exact Ha | | | |].
- pose proof (AR_owned_low_law_ok segs B ly S W mem md a (conj M (conj L (conj BUD (conj MW HS)))) Ha). ceil. unfold ASAN_CEIL in *. lia.
- unfold kFakeStackSize, kFakeFlagsOff in Hn. lia.
- intros ->. unfold flag_addr in Hn. unfold kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in Hn, FB. lia.
- unfold in_zr, frame_addr. cbn [fst snd]. unfold kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in Hn, FO1, FO2, FO6. lia.
-
unfold in_zr, frame_addr. cbn [fst snd]. intros [R1 R2].
pose proof (lo_F_al _ LO) as FAL. unfold page_aligned in FAL. apply Z.mod_divide in FAL as [qf Hqf]; [|lia].
pose proof FO3 as FO3'. apply Z.mod_divide in FO3' as [qo Hqo]; [|lia]. pose proof FO5 as FO5'. apply Z.mod_divide in FO5' as [qb Hqb]; [|lia].
assert (E1 : (ly_F ly + fs_frame_off cid pos) / 8 = qf * 512 + qo * 8) by (rewrite Hqf, Hqo; replace (qf * 4096 + qo * 64) with ((qf * 512 + qo * 8) * 8) by lia; apply Z_div_mult; lia).
assert (E2 : ly_F ly / 8 = qf * 512) by (rewrite Hqf; replace (qf * 4096) with ((qf * 512) * 8) by lia; apply Z_div_mult; lia).
assert (E3 : fs_frame_bytes cid / 8 = qb * 8) by (rewrite Hqb; replace (qb * 64) with ((qb * 8) * 8) by lia; apply Z_div_mult; lia).
unfold shadow_addr in Hb, R1, R2. rewrite E1 in R1, R2. rewrite E3 in R2. rewrite E2 in Hb. change (kFakeStackSize / 8) with 1446400 in Hb.
clear - Hb R1 R2 Hqo Hqb FO2 FO6 FO1 Hc. unfold kFakeFramesOff, kFakeStackSize in *. nia. }
assert (CL : forall a, aclient_byte B ly S a -> aclient_byte B ly S' a).
{ intros a [X|(cp & Hcp & X)]; [left; exact X | right]. exists cp. split; [rewrite FR'; right; exact Hcp | exact X]. }
assert (L' : ALedger segs ly S' md').
{ destruct L; constructor; rewrite ?Hvm, ?Hlz, ?He; assumption. }
assert (AGF : forall g, g mod 8 = 0 -> in_app g 8 -> hfree ly S g -> w_H W (w64 (shadow_addr g)) = false ->
rd' (shadow_addr g) = rd (shadow_addr g)).
{ intros g Hg HA HFg _. pose proof (shadow_addr_band_rw g HA) as SB. pose proof HA as [HA0 HAZ].
pose proof (shadow_addr_bounds g ltac:(lia)) as [SB1 SB2']. pose proof (SB2' ltac:(clear - HAZ CR; unfold ASAN_CEIL, kHighMemEnd, kLowShadowBeg in *; lia)) as SB2.
pose proof (proj1 (Forall_forall _ _) HFg (ly_F ly, kFakeStackSize)
ltac:(unfold hfree; rewrite !in_app_iff; left; unfold static_extents, owned_extents; rewrite in_app_iff; left; cbn; tauto)) as XF. cbn [fst snd] in XF.
apply AGR; [| eapply hfree_shadow_owned; [exact M | exact Hg | exact HA | exact HFg] | | | |].
- clear - SB1 SB2. unfold SHADOW_OFF, kHighMemBeg in *. lia.
- clear - SB1 SB2 FR2 Hc. unfold SHADOW_OFF, kHighMemBeg, kFakeStackSize in *. lia.
- intros E. unfold flag_addr in E. clear - SB1 SB2 FR2 FB E. unfold SHADOW_OFF, kHighMemBeg, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. lia.
- unfold in_zr, frame_addr. cbn [fst snd]. clear - SB1 SB2 FR2 FO1 FO2 FO6 Hc. unfold SHADOW_OFF, kHighMemBeg, kFakeFramesOff, kFakeStackSize in *. lia.
- unfold in_zr, frame_addr. cbn [fst snd]. intros [R1 R2].
apply Z.mod_divide in Hg as [q Hq]; [|lia].
assert (F8 : (ly_F ly + fs_frame_off cid pos) mod 8 = 0).
{ pose proof (lo_F_al _ LO) as FAL. unfold page_aligned in FAL. apply Z.mod_divide; [lia|].
apply Z.mod_divide in FAL as [qf Hqf]; [|lia]. apply Z.mod_divide in FO3 as [qo Hqo]; [|lia]. exists (qf * 512 + qo * 8). lia. }
apply Z.mod_divide in F8 as [qa Hqa]; [|lia]. apply Z.mod_divide in FO5 as [qb Hqb]; [|lia].
unfold shadow_addr, SHADOW_OFF in R1, R2. rewrite Hq, Hqa, Hqb in *. rewrite !Z.div_mul in R1, R2 by lia.
replace (qb * 64 / 8) with (qb * 8) in R2 by (symmetry; replace (qb * 64) with (qb * 8 * 8) by lia; apply Z.div_mul; lia).
unfold kFakeFramesOff, kFakeStackSize in *. nia. }
split; [|split; [exact L' | split; [exact BUD | split; [exact (amwf_same md md' Hvm Hlz MW) |
exact (ahs_transfer_grow ly S S' (w_H W) mem mem' (al_img_env segs ly S md LO L) HS VIS HK (fun a _ C => CL a C) eq_refl AGF)]]]].
pose proof M as M0. destruct M as [Xwf Xuni Xsyms Xlay Xplaced Xconst Xcowned Xcells Xfa Xflags Xdepot Xshadow Xzsh Xjunk Xareas Xclient Xzero Xtsd Ximg].
constructor; try assumption.
-   unfold S'. apply Wf_push_frame; [exact Xwf | exact Hc | exact Hp | | exact NIN].
rewrite Eh'. assert (Hh0 : 0 <= znth 0 cid (fs_hint (st_fs S))); [|lia].
unfold znth. destruct (nth_in_or_default (Z.to_nat cid) (fs_hint (st_fs S)) 0) as [Hin| ->]; [exact (proj1 (Forall_forall _ _) FH _ Hin) | lia].
-   exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN (const_cells_owned B ly S rd M0) (const_cells_nf ly S rd M0) Xconst).
-
unfold S'. apply (am_cells_set_fs ly S rd rd' _ M0 AGN). cbn [fs_hint].
pose proof Xcells as XC. unfold acells in XC. rewrite (fs_cells_split S) in XC.
do 5 (apply Forall_app in XC as [_ XC]). apply Forall_app in XC as [XF _]. apply Forall_app in XF as [_ XH].
pose proof (acells_owned B ly S rd M0) as OW. unfold acells in OW. rewrite (fs_cells_split S) in OW.
do 5 (apply Forall_app in OW as [_ OW]). apply Forall_app in OW as [OWF _]. apply Forall_app in OWF as [_ OWH].
unfold fs_hints in XH, OWH |- *. cbn [fs_hint] in XH, OWH.
apply Forall_forall. intros c Hcin. apply in_map_iff in Hcin as ([i hv] & <- & Hih).
pose proof (in_combine_l _ _ _ _ Hih) as Hi. apply in_seq in Hi.
assert (LZ : length (zupd cid hint' (fs_hint (st_fs S))) = 11%nat) by (rewrite zupd_length; exact LH).
rewrite <- LZ in Hih. apply (proj1 (in_combine_seq_iff _ _ _ _)) in Hih as [_ Hih]. rewrite Nat.sub_0_r in Hih. unfold zupd in Hih.
destruct (Nat.eq_dec i (Z.to_nat cid)) as [->|Hne].
+
rewrite nth_error_lupd_same in Hih by (rewrite LH; lia). injection Hih as <-.
cbn [cell_holds c_at c_val c_w z8 c8 aeval aoff fst snd]. intros kk Hkk.
rewrite Z2Nat.id by lia. unfold rd'. exact (HW kk Hkk).
+
rewrite nth_error_lupd_other in Hih by (intros E; exact (Hne (eq_sym E))).
assert (OLD : In (i, hv) (combine (seq 0 11) (fs_hint (st_fs S)))).
{ rewrite <- LH. apply (proj2 (in_combine_seq_iff _ _ _ _)). split; [lia|]. rewrite Nat.sub_0_r. exact Hih. }
assert (INC : In (z8 (AF (8 * Z.of_nat (fst (i, hv)))) (snd (i, hv))) (map (fun iv : nat * Z => z8 (AF (8 * Z.of_nat (fst iv))) (snd iv)) (combine (seq 0 11) (fs_hint (st_fs S))))).
{ apply in_map_iff. exists (i, hv). split; [reflexivity | exact OLD]. }
eapply cell_holds_agree; [exact (proj1 (Forall_forall _ _) XH _ INC)|].
intros kk Hkk. cbn [c_at c_w z8 c8 aeval aoff fst snd] in Hkk |- *.
apply AGR.
* clear - Hkk Hi FH0 F64. unfold kFakeStackSize in *. lia.
* exact (proj1 (Forall_forall _ _) OWH _ INC kk Hkk).
* intros X. apply Hne. lia.
* unfold flag_addr. unfold kFakeFlagsOff in FB. lia.
* unfold in_zr, frame_addr. cbn [fst snd]. unfold kFakeFramesOff in FO1. lia.
* unfold in_zr, frame_addr. cbn [fst snd]. clear - Hkk Hi FR2 FSL FSLO. unfold SHADOW_OFF, kHighMemBeg, kFakeStackSize in *. lia.
-
intros c i v Hc' Hi Hv k Hk. change (reg S' c) with (reg S c) in *.
pose proof (wf_classes _ _ _ _ _ Xwf c Hc') as CLS. pose proof (wr_fa_len _ _ _ _ _ _ CLS) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CLS) as FB'.
rewrite AGN; [exact (Xfa c i v Hc' Hi Hv k Hk) | eapply own_fa; [exact M0 | exact Hc' | lia] |].
apply (nf_prim ly _ Xlay). pose proof (region_in_prim ly c Xlay Hc') as (R1 & R2 & _). unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax, kPrimResvSize, kSpaceSize in *.
pose proof (lo_space_in _ Xlay) as [S1 S2]. rewrite region_off_eq in * by lia. unfold kPrimResvSize, kSpaceSize in *. nia.
-
intros c q Hc' Hq. rewrite FR'. cbn [mem_pos].
destruct (Z.eq_dec (flag_addr ly c q) (flag_addr ly cid pos)) as [E|NE].
+ destruct (flag_addr_inj ly c q cid pos Hc' Hq Hc Hp E) as [-> ->]. unfold rd' in HF1 |- *. rewrite HF1. rewrite !Z.eqb_refl. reflexivity.
+ pose proof (flag_off_bounds c q Hc' Hq) as FB''.
rewrite AGR; [| clear - FB'' FH0 F64; unfold flag_addr, kFakeStackSize, kFakeFramesOff, kFakeFlagsOff in *; lia
| eapply own_F_low; [exact M0 | clear - FB''; unfold flag_addr, kFakeFlagsOff, kFakeFramesOff in *; lia]
| clear - FB'' Hc; unfold flag_addr; unfold kFakeFlagsOff in FB''; lia | exact NE
| clear - FO1 FB'' Hc; unfold in_zr, frame_addr, flag_addr; cbn [fst snd]; unfold kFakeFramesOff in FO1, FB''; lia
| clear - FR2 FSL FSLO FB''; unfold in_zr, frame_addr, flag_addr; cbn [fst snd]; unfold SHADOW_OFF, kHighMemBeg, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *; lia ].
rewrite (Xflags c q Hc' Hq). f_equal.
destruct (Z.eqb_spec cid c) as [Ec|Ec]; destruct (Z.eqb_spec pos q) as [Eq|Eq]; cbn [andb orb]; [exfalso; apply NE; subst c q; reflexivity | | |]; reflexivity.
-
lazymatch eval cbv in depot_has_trace with
| true =>
destruct Xdepot as (heads & links & D1 & D2 & D3); exists heads, links; split; [|split; [|exact D3]];
[ intros b Hb; destruct (D1 b Hb) as [H1 H2]; split; [exact H1|]; intros k Hk; change (depot_traces ly S') with (depot_traces ly S) in *;
rewrite AGN; [exact (H2 k Hk) | eapply (own_area B ly S rd (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | cbn; tauto | cbn; unfold d_tab_words in Hb; lia] |];
eapply (nf_area ly S rd (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | cbn; tauto | cbn; unfold d_tab_words in Hb; lia]
| intros id Hid; change (depot_ids S') with (depot_ids S) in Hid; destruct (D2 id Hid) as (H1 & H2 & H3); split; [exact H1|];
assert (NB : depot_ids S <= 4097) by (unfold depot_ids; pose proof (wf_depot _ _ _ _ _ Xwf) as [ND' INC]; pose proof (NoDup_incl_length ND' INC); destruct Xuni as (U1 & _); unfold DEPOT_MAX in U1; lia);
assert (OR : forall k, 0 <= k < 16 -> rd' (ly_NB ly + 16 * id + k) = rd (ly_NB ly + 16 * id + k)) by (intros k Hk; apply AGN;
[ eapply (own_core B ly S rd (ly_NB ly, kNodesBlockSize)); [exact M0 | unfold core_extents; cbn; tauto | cbn; unfold kNodesBlockSize; lia]
| eapply (nf_core ly S rd (ly_NB ly, kNodesBlockSize)); [exact M0 | unfold core_extents; cbn; tauto | cbn; unfold kNodesBlockSize; lia] ]);
split; intros k Hk; [rewrite OR by lia; exact (H2 k Hk)|];
replace (ly_NB ly + 16 * id + 8 + Z.of_nat k) with (ly_NB ly + 16 * id + (8 + Z.of_nat k)) by lia; rewrite OR by lia;
replace (ly_NB ly + 16 * id + (8 + Z.of_nat k)) with (ly_NB ly + 16 * id + 8 + Z.of_nat k) by lia; exact (H3 k Hk) ]
| false =>
(* Knock: before the first Put no node is read, so only the table words (owned depot area) must agree; after it, the
   one-trace argument, with the node bytes owned through core_extents_set (both blocks mapped). *)
revert Xdepot; unfold depot_ok; change (st_depot S') with (st_depot S); destruct (st_depot S) as [|t0 ts]; intro Xdepot;
[ destruct Xdepot as (E0 & T0 & I0 & A0); split; [exact E0 |]; split; [| split; [exact I0 | exact A0]];
  intros b Hb k Hk; rewrite AGN; [exact (T0 b Hb k Hk) | eapply (own_area B ly S rd (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | cbn; tauto | cbn; unfold d_tab_words in Hb; lia] |];
  eapply (nf_area ly S rd (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | cbn; tauto | cbn; unfold d_tab_words in Hb; lia]
| destruct Xdepot as (MNB & MSB & heads & links & D1 & D2 & D3); split; [exact MNB|]; split; [exact MSB|];
  exists heads, links; split; [|split; [|exact D3]];
  [ intros b Hb; destruct (D1 b Hb) as [H1 H2]; split; [exact H1|]; intros k Hk; change (depot_traces ly S') with (depot_traces ly S) in *;
    rewrite AGN; [exact (H2 k Hk) | eapply (own_area B ly S rd (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | cbn; tauto | cbn; unfold d_tab_words in Hb; lia] |];
    eapply (nf_area ly S rd (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | cbn; tauto | cbn; unfold d_tab_words in Hb; lia]
  | intros id Hid; change (depot_ids S') with (depot_ids S) in Hid; destruct (D2 id Hid) as (H1 & H2 & H3); split; [exact H1|];
    assert (NB : depot_ids S <= 4097) by (unfold depot_ids; pose proof (wf_depot _ _ _ _ _ Xwf) as [ND' INC]; pose proof (NoDup_incl_length ND' INC); destruct Xuni as (U1 & _); unfold DEPOT_MAX in U1; lia);
    assert (OR : forall k, 0 <= k < 16 -> rd' (ly_NB ly + 16 * id + k) = rd (ly_NB ly + 16 * id + k)) by (intros k Hk; apply AGN;
    [ eapply (own_core B ly S rd (ly_NB ly, kNodesBlockSize)); [exact M0 | rewrite (core_extents_set ly MNB MSB); cbn; tauto | cbn; unfold kNodesBlockSize; lia]
    | eapply (nf_core ly S rd (ly_NB ly, kNodesBlockSize)); [exact M0 | rewrite (core_extents_set ly MNB MSB); cbn; tauto | cbn; unfold kNodesBlockSize; lia] ]);
    split; intros k Hk; [rewrite OR by lia; exact (H2 k Hk)|];
    replace (ly_NB ly + 16 * id + 8 + Z.of_nat k) with (ly_NB ly + 16 * id + (8 + Z.of_nat k)) by lia; rewrite OR by lia;
    replace (ly_NB ly + 16 * id + (8 + Z.of_nat k)) with (ly_NB ly + 16 * id + 8 + Z.of_nat k) by lia; exact (H3 k Hk) ] ]
end.
-
intros g v Hg Hv0. change (ashadow B ly S' g) with (ashadow B ly S g) in Hv0.
pose proof (ashadow_low ly S rd g v M0 Hv0) as SL.
pose proof (proj1 (ashadow_app ly S rd g v M0 Hv0)) as G0.
rewrite AGR; [exact (Xshadow g v Hg Hv0) | | eapply ashadow_owned; [exact M0 | exact Hv0] | | | | exact (ashadow_not_frame_shadow ly S rd g v cid pos M0 Hv0 Hc Hp)].
+ clear - SL. unfold SHADOW_OFF, kHighMemBeg in *. lia.
+ clear - SL FR2 Hc. unfold SHADOW_OFF, kHighMemBeg, kFakeStackSize in *. lia.
+ clear - SL FR2 FB Hc. unfold flag_addr, SHADOW_OFF, kHighMemBeg, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. lia.
+ clear - SL FR2 FO1 FO2 FO6 Hc. unfold in_zr, frame_addr, SHADOW_OFF, kHighMemBeg, kFakeFramesOff, kFakeStackSize in *. cbn [fst snd]. lia.
-
unfold zshadow_ok in *. apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
pose proof (proj1 (Forall_forall _ _) Xzsh r Hr i Hi) as Z0. unfold shadow_of_addr in Z0. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)) in Z0.
pose proof (zshadow_low ly S rd r i M0 Hr Hi) as SL.
rewrite AGR; [exact Z0 | | eapply own_shadow_zero; [exact M0 | exact Hr | exact Hi] | | | | exact (zshadow_not_frame_shadow ly S rd r i cid pos M0 Hr Hi Hc Hp)].
+ clear - SL. unfold SHADOW_OFF, kHighMemBeg in *. lia.
+ clear - SL FR2 Hc. unfold SHADOW_OFF, kHighMemBeg, kFakeStackSize in *. lia.
+ clear - SL FR2 FB Hc. unfold flag_addr, SHADOW_OFF, kHighMemBeg, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. lia.
+ clear - SL FR2 FO1 FO2 FO6 Hc. unfold in_zr, frame_addr, SHADOW_OFF, kHighMemBeg, kFakeFramesOff, kFakeStackSize in *. cbn [fst snd]. lia.
- eapply Forall_range_vis_keep; [exact VIS | exact Xjunk].
- eapply Forall_range_vis_keep; [exact VIS | exact Xareas].
-
eapply Forall_range_vis_keep; [exact VIS|]. apply Forall_forall. intros r Hr.
unfold aclient in Hr. change (st_chunks S') with (st_chunks S) in Hr. rewrite FR' in Hr. cbn [map] in Hr. rewrite !in_app_iff in Hr. cbn [In fst snd] in Hr.
assert (AF_vis : forall e len, In (e, len) (aareas S) -> forall i, 0 <= i < len -> rd (aeval B ly e + i) <> None).
{ intros e len Hin. exact (proj1 (Forall_forall _ _) Xareas _ Hin). }
assert (IN_F : In (AF 0, kFakeStackSize) (aareas S)) by (unfold aareas; rewrite !in_app_iff; do 3 right; cbn; tauto).
assert (IN_FS : In (ASh (AF kFakeFramesOff), (kFakeStackSize - kFakeFramesOff) / 8) (aareas S)) by (unfold aareas; rewrite !in_app_iff; do 3 right; cbn; tauto).
destruct Hr as [Hr|[[<-|Hr]|[<-|Hr]]].
+ apply (proj1 (Forall_forall _ _) Xclient). unfold aclient. rewrite !in_app_iff. left. exact Hr.
+ intros i Hi. cbn [fst snd aeval] in Hi |- *. replace (ly_F ly + fs_frame_off cid pos + i) with (aeval B ly (AF 0) + (fs_frame_off cid pos + i)) by (cbn; lia).
apply (AF_vis _ _ IN_F). unfold kFakeFramesOff in FO1. lia.
+ apply (proj1 (Forall_forall _ _) Xclient). unfold aclient. rewrite !in_app_iff. right; left. exact Hr.
+ intros i Hi. cbn [fst snd aeval] in Hi |- *.
pose proof (lo_F_al _ Xlay) as FAL. unfold page_aligned in FAL.
apply Z.mod_divide in FAL as [qf Hqf]; [|lia]. pose proof FO3 as FO3'. apply Z.mod_divide in FO3' as [qo Hqo]; [|lia]. pose proof FO5 as FO5'. apply Z.mod_divide in FO5' as [qb Hqb]; [|lia].
assert (E1 : shadow_addr (ly_F ly + fs_frame_off cid pos) = SHADOW_OFF + qf * 512 + qo * 8).
{ unfold shadow_addr. rewrite Hqf, Hqo. replace (qf * 4096 + qo * 64) with ((qf * 512 + qo * 8) * 8) by lia. rewrite Z_div_mult by lia. lia. }
assert (E0 : shadow_addr (ly_F ly + kFakeFramesOff) = SHADOW_OFF + qf * 512 + 4608).
{ unfold shadow_addr, kFakeFramesOff. rewrite Hqf. replace (qf * 4096 + (4096 + 32768)) with ((qf * 512 + 4608) * 8) by lia. rewrite Z_div_mult by lia. lia. }
assert (EB : fs_frame_bytes cid / 8 = qb * 8) by (rewrite Hqb; replace (qb * 64) with ((qb * 8) * 8) by lia; rewrite Z_div_mult by lia; reflexivity).
rewrite EB in Hi. rewrite E1.
replace (SHADOW_OFF + qf * 512 + qo * 8 + i) with (aeval B ly (ASh (AF kFakeFramesOff)) + (qo * 8 - 4608 + i)) by (cbn [aeval]; rewrite E0; lia).
apply (AF_vis _ _ IN_FS). unfold kFakeFramesOff, kFakeStackSize in *.
replace ((11571200 - (4096 + 32768)) / 8) with 1441792 by reflexivity. nia.
+ apply (proj1 (Forall_forall _ _) Xclient). unfold aclient. rewrite !in_app_iff. right; right. exact Hr.
-
apply Forall_forall. intros r Hr i Hi. pose proof (aso_ialloc _ Xsyms) as [I1 I2].
assert (RG : forall z, as_ialloc_lo B <= z < as_ialloc_hi B -> rd' z = rd z).
{ intros z Hz. apply AGN.
- eapply (own_area B ly S rd (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact M0 | cbn; tauto | cbn [fst snd]; lia].
- eapply (nf_area ly S rd (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact M0 | cbn; tauto | cbn [fst snd]; lia]. }
rewrite RG; [exact (proj1 (Forall_forall _ _) Xzero r Hr i Hi)|].
unfold ialloc_zero in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; lia.
Qed.
End u.
End j.
