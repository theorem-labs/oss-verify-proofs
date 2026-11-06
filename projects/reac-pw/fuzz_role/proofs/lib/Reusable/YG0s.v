(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG0s.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YG0s.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_role. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG0f YG0v YG0n YG0d DepotCfg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := let H := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Ltac show := match goal with |- ?g => idtac g end.
Lemma le_byte_8 : forall v k, le_byte v 8 k = (v mod 2 ^ 64) / 2 ^ (8 * Z.of_nat k) mod 256.
Proof. intros v k. unfold le_byte. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma le_bytes8 : forall v, 0 <= v < 2 ^ 64 ->
le_byte v 8 0 + 256 * (le_byte v 8 1 + 256 * (le_byte v 8 2 + 256 * (le_byte v 8 3 + 256 * (le_byte v 8 4 + 256 * (le_byte v 8 5
+ 256 * (le_byte v 8 6 + 256 * le_byte v 8 7)))))) = v.
Proof.
intros v Hv. rewrite !le_byte_8. rewrite (Z.mod_small v (2 ^ 64)) by lia.
replace (2 ^ (8 * Z.of_nat 0)) with 1 by reflexivity. rewrite Z.div_1_r.
replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity.
replace (2 ^ (8 * Z.of_nat 2)) with (256 * 256) by reflexivity.
replace (2 ^ (8 * Z.of_nat 3)) with (256 * 256 * 256) by reflexivity.
replace (2 ^ (8 * Z.of_nat 4)) with (256 * 256 * 256 * 256) by reflexivity.
replace (2 ^ (8 * Z.of_nat 5)) with (256 * 256 * 256 * 256 * 256) by reflexivity.
replace (2 ^ (8 * Z.of_nat 6)) with (256 * 256 * 256 * 256 * 256 * 256) by reflexivity.
replace (2 ^ (8 * Z.of_nat 7)) with (256 * 256 * 256 * 256 * 256 * 256 * 256) by reflexivity.
rewrite <- !Z.div_div by lia.
set (v1 := v / 256). set (v2 := v1 / 256). set (v3 := v2 / 256). set (v4 := v3 / 256). set (v5 := v4 / 256). set (v6 := v5 / 256). set (v7 := v6 / 256).
assert (E7 : v7 mod 256 = v7).
{ apply Z.mod_small. subst v7 v6 v5 v4 v3 v2 v1.
split; [repeat (apply Z.div_pos; [|lia]); lia|].
repeat (apply Z.div_lt_upper_bound; [lia|]). change (2 ^ 64) with (256 * (256 * (256 * (256 * (256 * (256 * (256 * 256))))))) in Hv. lia. }
rewrite E7.
assert (R : forall x, x mod 256 = x - 256 * (x / 256)) by (intros x; pose proof (Z.div_mod x 256 ltac:(lia)); lia).
rewrite (R v), (R v1), (R v2), (R v3), (R v4), (R v5), (R v6). subst v7 v6 v5 v4 v3 v2 v1. lia.
Qed.
Section m.
Variable segs : list Segment.
Variable B : asyms.
Lemma rdword_cell : forall ly rd a v, 0 <= v < 2 ^ 64 -> cell_holds B ly rd (z8 (ANum a) v) -> rdword rd a = Some v.
Proof.
intros ly rd a v Hv Hc. unfold cell_holds in Hc. cbn [c_at c_val c_w z8 c8 aeval] in Hc.
unfold rdword.
pose proof (Hc 0%nat ltac:(lia)) as H0. pose proof (Hc 1%nat ltac:(lia)) as H1. pose proof (Hc 2%nat ltac:(lia)) as H2.
pose proof (Hc 3%nat ltac:(lia)) as H3. pose proof (Hc 4%nat ltac:(lia)) as H4. pose proof (Hc 5%nat ltac:(lia)) as H5.
pose proof (Hc 6%nat ltac:(lia)) as H6. pose proof (Hc 7%nat ltac:(lia)) as H7.
cbv [Z.of_nat Pos.of_succ_nat Pos.succ] in H0, H1, H2, H3, H4, H5, H6, H7. rewrite Z.add_0_r in H0.
rewrite H0, H1, H2, H3, H4, H5, H6, H7. f_equal. apply le_bytes8. exact Hv.
Qed.
Lemma asyms_area_bound : forall r, asyms_ok B -> In r (asyms_areas B) -> 4096 <= fst r /\ fst r + snd r <= kImgEnd.
Proof.
intros r HB Hr. pose proof (proj1 (Forall_forall _ _) (aso_cover _ HB) r Hr) as X.
apply Exists_exists in X as (r' & Hr' & [S1 S2]). pose proof (proj1 (Forall_forall _ _) (aso_static _ HB) r' Hr') as (T1 & T2 & T3). lia.
Qed.
Theorem AR_wle_law_ok : AR_wle_law segs B.
Proof. intros ly S W W' mem md. apply AR_wle. Qed.
Theorem AR_zshadow_law_ok : AR_zshadow_law segs B.
Proof.
intros ly S W mem md r (M & _ & _) Hr. exact (proj1 (Forall_forall _ _) (am_zshadow _ _ _ _ M) r Hr).
Qed.
Theorem AR_const_law_ok : AR_const_law segs B.
Proof.
intros ly S W mem md (M & _ & _).
pose proof (am_const _ _ _ _ M) as C. pose proof (aso_const_law _ (am_syms _ _ _ _ M) ly) as (I1 & I2 & I3 & I4).
pose proof (asyms_area_bound (as_shadow_cell B, 8) (am_syms _ _ _ _ M) ltac:(cbn; tauto)) as [A1 A2].
pose proof (asyms_area_bound (as_uar_cell B, 4) (am_syms _ _ _ _ M) ltac:(cbn; tauto)) as [A3 A4]. cbn [fst snd] in A1, A2, A3, A4.
assert (F := fun c (H : In c (as_const B ly)) => proj1 (Forall_forall _ _) C c H).
unfold SHADOW_OFF, kImgEnd in *. splits.
- eapply rdword_cell; [lia | exact (F _ I1)].
- pose proof (F _ I2) as H2. unfold cell_holds in H2. cbn [c_at c_val c_w z4 c4 aeval] in H2. intros k Hk. exact (H2 k Hk).
- eapply rdword_cell; [lia | exact (F _ I3)].
- eapply rdword_cell; [lia | exact (F _ I4)].
Qed.
Lemma pairwise_app_inv : forall {X} (R : X -> X -> Prop) l1 l2,
pairwise R (l1 ++ l2) -> pairwise R l1 /\ pairwise R l2 /\ forall x y, In x l1 -> In y l2 -> R x y.
Proof.
intros X R l1. induction l1 as [|x t IH]; intros l2 H; cbn in *.
- splits; auto. intros x y [].
- destruct H as [F P]. apply Forall_app in F as [F1 F2]. destruct (IH l2 P) as (P1 & P2 & P3).
splits; auto. intros x' y [<-|Hx'] Hy; [exact (proj1 (Forall_forall _ _) F2 y Hy) | exact (P3 x' y Hx' Hy)].
Qed.
Lemma pairwise_In : forall {X} (R : X -> X -> Prop) l x y l1 l2, l = l1 ++ l2 -> pairwise R l -> In x l1 -> In y l2 -> R x y.
Proof. intros X R l x y l1 l2 -> H Hx Hy. exact (proj2 (proj2 (pairwise_app_inv R l1 l2 H)) x y Hx Hy). Qed.
Lemma shadow_addr_bounds : forall x, 0 <= x -> SHADOW_OFF <= shadow_addr x /\ (x + 7 <= kHighMemEnd -> shadow_addr x < kHighMemBeg) .
Proof.
intros x Hx. unfold shadow_addr, SHADOW_OFF, kHighMemEnd, kHighMemBeg. split; [pose proof (Z.div_pos x 8); lia|].
intros H. assert (x / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma sec_extents_len : forall ly S rd, ARm B ly S rd -> Forall (fun e => 4096 < snd e) (sec_extents ly S).
Proof.
intros ly S rd M. pose proof (wf_chunks _ _ _ _ _ (am_wf _ _ _ _ M)) as CK. unfold sec_extents.
apply Forall_forall. intros e He. apply in_flat_map in He as (k & Hk & He).
pose proof (proj1 (Forall_forall _ _) CK k Hk) as [Hn C]. destruct (ck_beg k) as [|o|r o|c p]; try destruct He as [<-|[]]; try destruct He.
cbn [snd]. destruct C as (Hp & _). pose proof (secondary_geometry (ck_req k) ltac:(lia) Hp) as (G1 & G2 & G3 & G4 & _).
pose proof (req_size_bounds (ck_req k) ltac:(lia)). unfold kPage, kSecRz in *. lia.
Qed.
Lemma shadow_range_below : forall x len, 0 <= x -> 0 <= len -> x + len <= kHighMemEnd -> shadow_addr x + len / 8 <= kHighMemBeg.
Proof.
intros x len Hx Hl H. unfold shadow_addr, SHADOW_OFF, kHighMemEnd, kHighMemBeg in *.
assert (L : (x + len) / 8 <= 140737488355328 / 8) by (apply Z.div_le_mono; lia). change (140737488355328 / 8) with 17592186044416 in L.
assert (x / 8 + len / 8 <= (x + len) / 8); [|lia].
apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le x 8 ltac:(lia)). pose proof (Z.mul_div_le len 8 ltac:(lia)). lia.
Qed.
Lemma owned_shadow_ranges : forall ly S rd, ARm B ly S rd ->
Forall (fun r => 0 <= fst r /\ 0 <= snd r /\ fst r + snd r <= kHighMemEnd) (static_extents ly ++ sec_extents ly S ++ zero_shadow_ranges B ly ++ as_owned_static B ++ [hm_zone; lm_zone]).
Proof.
intros ly S rd M. pose proof (am_layout _ _ _ _ M) as LO. pose proof (am_placed _ _ _ _ M) as [PL _]. pose proof (am_syms _ _ _ _ M) as SY.
pose proof (lo_top _ LO) as TOP. pose proof (lo_app _ LO) as HI. pose proof (lo_img _ LO) as IMG. pose proof ASAN_CEIL_range as [CR _].
unfold kHighMemEnd, kHighMemBeg, kLowMemEnd, kImgLo, kImgEnd in *.
apply Forall_app. split; [|apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split; [|constructor; [unfold hm_zone; cbn; unfold kHighMemBeg, kHighMemEnd; lia | constructor; [unfold lm_zone; cbn; unfold kLowMemEnd, kHighMemEnd; lia | constructor]]]]]].
- unfold static_extents. apply Forall_app. split.
+ apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) HI e He) as [H1 H2].
assert (Hs : 0 <= snd e).
{ unfold owned_extents in He. unfold kPrimResvSize, kPtrArrayResv, kThreadObjSize, kFakeStackSize, kNodesBlockSize, kStoreBlockSize in He.
lazymatch eval cbv in depot_has_trace with
| true => repeat (destruct He as [<-|He]; [cbn; lia|]); destruct He
| false => repeat (destruct He as [<-|He]; [repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn; lia|]); destruct He
end. }
unfold kLowShadowBeg, kHighMemBeg in H2. lia.
+ constructor; [cbn; lia | constructor; [cbn [fst snd]; unfold page_aligned in IMG; lia | constructor]].
- apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) PL e He) as (_ & [H1 H2] & H3).
pose proof (proj1 (Forall_forall _ _) (sec_extents_len ly S rd M) e He) as H4. cbv beta in H4. unfold kLowShadowBeg, kHighMemBeg in *. lia.
- unfold zero_shadow_ranges. constructor; [cbn; lia|]. eapply Forall_impl; [|exact (aso_zshadow _ SY)]. cbv beta. intros r Hr. unfold kLowMemEnd in Hr. lia.
- eapply Forall_impl; [|exact (aso_static _ SY)]. cbv beta. intros r Hr. unfold kImgEnd in Hr. lia.
Qed.
Lemma owned_static_bound : forall a, asyms_ok B -> Exists (in_zr a) (as_owned_static B) -> 4096 <= a < kImgEnd.
Proof.
intros a SY H. apply Exists_exists in H as (r & Hr & [H1 H2]). pose proof (proj1 (Forall_forall _ _) (aso_static _ SY) r Hr) as (T1 & T2 & T3). lia.
Qed.
Lemma owned_extents_bound : forall ly a, layout_ok ly -> Exists (in_zr a) (owned_extents ly) ->
app_addr a /\ ~ (ly_stk_lo ly <= a < ly_stk_hi ly) /\ ~ in_zr a (ly_img ly).
Proof.
intros ly a LO H. apply Exists_exists in H as (e & He & [H1 H2]).
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) e He) as K.
pose proof (pairwise_In zdisjoint (static_extents ly) e (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) (owned_extents ly) [_; _] eq_refl (lo_disj _ LO) He (or_introl eq_refl)) as D.
pose proof (pairwise_In zdisjoint (static_extents ly) e (ly_img ly) (owned_extents ly) [_; _] eq_refl (lo_disj _ LO) He (or_intror (or_introl eq_refl))) as D2.
unfold zdisjoint, in_zr in *. cbn [fst snd] in D. split; [exact (in_app_addr _ _ _ K (conj H1 H2)) | lia].
Qed.
Lemma owned_sec_bound : forall ly S rd a, ARm B ly S rd -> Exists (in_zr a) (sec_extents ly S) ->
app_addr a /\ ~ (ly_stk_lo ly <= a < ly_stk_hi ly) /\ ~ in_zr a (ly_img ly).
Proof.
intros ly S rd a M H. apply Exists_exists in H as (e & He & [H1 H2]). pose proof (am_placed _ _ _ _ M) as [PL PD].
pose proof (proj1 (Forall_forall _ _) PL e He) as (_ & K & K3).
pose proof (pairwise_In zdisjoint _ e (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) (sec_extents ly S) (static_extents ly) eq_refl PD He
ltac:(unfold static_extents; apply in_app_iff; right; left; reflexivity)) as D.
pose proof (pairwise_In zdisjoint _ e (ly_img ly) (sec_extents ly S) (static_extents ly) eq_refl PD He
ltac:(unfold static_extents; apply in_app_iff; right; right; left; reflexivity)) as D2.
unfold zdisjoint, in_zr in *. cbn [fst snd] in D. split; [exact (in_app_addr _ _ _ K (conj H1 H2)) | lia].
Qed.
Lemma owned_shadow_bound : forall ly S rd a, ARm B ly S rd ->
Exists (fun r => in_zr a (shadow_addr (fst r), (snd r + 7) / 8)) (static_extents ly ++ sec_extents ly S ++ zero_shadow_ranges B ly ++ as_owned_static B ++ [hm_zone; lm_zone]) ->
SHADOW_OFF <= a < kHighMemBeg.
Proof.
intros ly S rd a M H. apply Exists_exists in H as (r & Hr & [H1 H2]). cbn [fst snd] in H1, H2.
pose proof (proj1 (Forall_forall _ _) (owned_shadow_ranges ly S rd M) r Hr) as (K1 & K2 & K3).
pose proof (shadow_addr_bounds (fst r) K1) as [P1 _].
unfold shadow_addr, SHADOW_OFF, kHighMemEnd, kHighMemBeg in *.
assert (fst r / 8 + (snd r + 7) / 8 <= 17592186044416); [|lia].
assert (L : (fst r + snd r + 7) / 8 <= 140737488355335 / 8) by (apply Z.div_le_mono; lia).
change (140737488355335 / 8) with 17592186044416 in L.
assert (fst r / 8 + (snd r + 7) / 8 <= (fst r + snd r + 7) / 8); [|lia].
apply Z.div_le_lower_bound; [lia|].
pose proof (Z.mul_div_le (fst r) 8 ltac:(lia)). pose proof (Z.mul_div_le (snd r + 7) 8 ltac:(lia)). lia.
Qed.
Theorem AR_stack_law_ok : AR_stack_law segs B.
Proof.
intros ly S W mem md a (M & _ & _) Ha [OW _]. pose proof (am_layout _ _ _ _ M) as LO. pose proof (lo_top _ LO) as TOP.
destruct OW as [O|[O|[O|[O|O]]]].
- pose proof (owned_static_bound a (am_syms _ _ _ _ M) O). unfold kImgEnd, kHighMemBeg in *. lia.
- exact (proj1 (proj2 (owned_extents_bound ly a LO O)) Ha).
- apply (proj1 (proj2 (owned_extents_bound ly a LO ltac:(apply Exists_exists; exists (ly_C ly, 256); split; [unfold owned_extents; cbn; tauto | exact O]))) Ha).
- exact (proj1 (proj2 (owned_sec_bound ly S _ a M O)) Ha).
- pose proof (owned_shadow_bound ly S _ a M O). lia.
Qed.
Theorem AR_owned_low_law_ok : AR_owned_low_law segs B.
Proof.
intros ly S W mem md a (M & _ & _) [OW _]. pose proof (am_layout _ _ _ _ M) as LO.
pose proof ASAN_CEIL_range as [CR _]. ceil; unfold ASAN_CEIL in CR.
destruct OW as [O|[O|[O|[O|O]]]].
- pose proof (owned_static_bound a (am_syms _ _ _ _ M) O). unfold kImgEnd in *. lia.
- pose proof (app_addr_below_ceil a (proj1 (owned_extents_bound ly a LO O))). ceil; unfold ASAN_CEIL in *. lia.
- pose proof (app_addr_below_ceil a (proj1 (owned_extents_bound ly a LO ltac:(apply Exists_exists; exists (ly_C ly, 256); split; [unfold owned_extents; cbn; tauto | exact O])))).
ceil; unfold ASAN_CEIL in *. lia.
- pose proof (app_addr_below_ceil a (proj1 (owned_sec_bound ly S _ a M O))). ceil; unfold ASAN_CEIL in *. lia.
- pose proof (owned_shadow_bound ly S _ a M O). unfold SHADOW_OFF, kHighMemBeg in *. lia.
Qed.
Lemma region_off_eq : forall c, 0 <= c -> region_off c = c * 2 ^ 32.
Proof. intros c Hc. unfold region_off. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.
Lemma sptr_addr_padd : forall ly p d, match p with PPrim _ | PSec _ _ => True | _ => False end ->
sptr_addr B ly (padd p d) = sptr_addr B ly p + d.
Proof. intros ly p d Hp. destruct p; try destruct Hp; unfold sptr_addr; cbn; lia. Qed.
Lemma region_in_prim : forall ly c, layout_ok ly -> 1 <= c <= 31 ->
ly_prim ly <= region_base ly c /\ region_base ly c + 2 ^ 32 <= ly_prim ly + kPrimResvSize /\
region_base ly c mod 65536 = 0 /\ kHighMemBeg <= region_base ly c /\ region_base ly c + 2 ^ 32 <= ASAN_CEIL.
Proof.
intros ly c LO Hc. pose proof (lo_space_in _ LO) as [S1 S2]. pose proof (lo_space_al _ LO) as SA.
pose proof (lo_high _ LO) as [H1 H2].
unfold region_base. rewrite region_off_eq by lia. ceil; unfold kSpaceSize, kPrimResvSize, ASAN_CEIL, kHighMemBeg in *.
splits; try nia.
all: rewrite Z.add_mod, SA by lia; replace (c * 2 ^ 32) with ((c * 65536) * 65536) by lia; rewrite Z.mod_mul, Z.mod_0_l by lia; reflexivity.
Qed.
Lemma am_noholes : forall ly S rd c, ARm B ly S rd -> 1 <= c <= 31 -> rg_holes (reg S c) = [].
Proof. intros ly S rd c M Hc. exact (wf_noholes _ _ _ _ _ _ (am_wf _ _ _ _ M) Hc). Qed.
Lemma wf_no_prim_hole : forall U pp cc bb s ly a, WfP U pp cc bb s -> ~ prim_hole_at ly s a.
Proof.
intros U pp cc bb s ly a W (c & h & Hc & Hin & _). rewrite (wf_noholes _ _ _ _ _ _ W Hc) in Hin. exact Hin.
Qed.
Lemma am_no_prim_hole : forall ly S rd a, ARm B ly S rd -> ~ prim_hole_at ly S a.
Proof. intros ly S rd a M. exact (wf_no_prim_hole _ _ _ _ _ ly a (am_wf _ _ _ _ M)). Qed.
Lemma al_prim_covered : forall ly S rd md a, ARm B ly S rd -> ALedger segs ly S md -> ly_prim ly <= a < ly_prim ly + kPrimResvSize ->
exists e, In e (vm_maps (m_vmmaps md)) /\ bv_unsigned (fst e) <= a < bv_unsigned (fst e) + bv_unsigned (snd e).
Proof.
intros ly S rd md a M L Ha. destruct (al_prim _ _ _ _ L) as (pieces & (_ & _ & COV) & PCS).
pose proof (proj2 (COV a Ha) (am_no_prim_hole ly S rd a M)) as Hx.
apply Exists_exists in Hx as (q & Hq & HQ). destruct (proj1 (PCS q) Hq) as (Hin & Hpos & Hlo & Hhi).
pose proof (lo_high _ (am_layout _ _ _ _ M)) as [K1 K2].
cbn [fst snd] in K1, K2.
exists (wiv q). split; [exact Hin|]. unfold wiv, w64. cbn [fst snd]. destruct HQ as [Q1 Q2].
rewrite !Z_to_bv_unsigned, !bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); ceil; unfold in_high, kPrimResvSize, ASAN_CEIL, kHighMemBeg in *; lia). lia.
Qed.
(* The whole primary reservation is taken (git-lead's B2 premise over first_put_avoid): al_prim_covered covers every byte. *)
Lemma prim_takes : forall ly S rd md, ARm B ly S rd -> ALedger segs ly S md -> vm_takes md (ly_prim ly, kPrimResvSize).
Proof.
intros ly S rd md M L. left. split; [unfold kPrimResvSize; cbn [snd]; lia|].
intros a Ha. unfold in_zr in Ha. cbn [fst snd] in Ha. destruct (al_prim_covered ly S rd md a M L Ha) as (e & He & R).
apply Exists_exists. exists e. split; [apply in_or_app; right; exact He | exact R].
Qed.
(* The stack is taken through the page floor of alloc_top: al_top says alloc_ceiling = page_floor (alloc_top), and the
   stack starts at or above alloc_ceiling. *)
Lemma stack_takes : forall ly S md, ALedger segs ly S md -> alloc_ceiling <= ly_stk_lo ly ->
vm_takes md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly).
Proof.
intros ly S md L H. right. cbn [fst]. pose proof (al_top _ _ _ _ L) as T. unfold YM05.ceil_of_top in T. rewrite <- T. exact H.
Qed.
Definition cfacts (ly : alayout) (S : astate) (k : chunk) : Prop :=
in_app (ck_base B ly k) (ck_extent k) /\ ck_base B ly k + ck_extent k <= ASAN_CEIL /\ ck_base B ly k mod 16 = 0 /\
sptr_addr B ly (ck_user k) = ck_base B ly k + ck_rz k /\ 16 <= ck_rz k <= 2048 /\ ck_rz k mod 16 = 0 /\
0 <= ck_req k < MALLOC_MAX /\ ck_rz k + req_size (ck_req k) <= ck_extent k /\
match ck_beg k with
| PPrim off => let c := prim_class off in let x := off - region_off c in
1 <= c <= 30 /\ from_primary (ck_req k) = true /\ chunk_class (ck_req k) = c /\ ck_extent k = class_size c /\
ck_base B ly k = region_base ly c + x /\ 0 <= x /\ x mod class_size c = 0 /\ x + class_size c <= rg_alloc_user (reg S c) /\
rg_alloc_user (reg S c) <= rg_mapped_user (reg S c) <= 2 ^ 31
| PSec r o => o = kPage /\ from_primary (ck_req k) = false /\ ck_base B ly k = ly_sec ly r + kPage /\
ck_extent k = sec_map_size (ck_req k) - kPage /\ In (ly_sec ly r, sec_map_size (ck_req k)) (sec_extents ly S) /\
page_aligned (ly_sec ly r) /\ (r < length (st_secs S))%nat
| _ => False
end.
Lemma chunk_facts : forall ly S rd k, ARm B ly S rd -> In k (st_chunks S) -> cfacts ly S k.
Proof.
intros ly S rd k M Hk. pose proof (am_wf _ _ _ _ M) as W. pose proof (am_layout _ _ _ _ M) as LO. pose proof (am_placed _ _ _ _ M) as [PL PD].
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ W) k Hk) as [Hn CK].
pose proof (rz_size_bounds (ck_req k)) as [RZ1 RZ2]. pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
unfold cfacts, ck_base, ck_user, ck_rz.
destruct (ck_beg k) as [|off|r o|c p] eqn:Eb; try solve [destruct CK].
-
destruct CK as (Hp & Hc & Hoff).
pose proof (prim_chunk_off (as_universe B) 0 0 0 S k off W Hk Eb) as (G1 & G2 & G3 & G4 & G5 & G6). cbv zeta in *.
set (c := prim_class off) in *. set (x := off - region_off c) in *.
pose proof (primary_geometry (ck_req k) ltac:(lia) Hp) as (P1 & P2 & P3 & P4 & P5). rewrite <- G2 in P2, P3, P4, P5.
pose proof (class_ok c ltac:(lia)) as (K1 & K2 & K3 & _).
pose proof (region_in_prim ly c LO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wf_classes _ _ _ _ _ W c ltac:(lia)) as CL. pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_alloc_al _ _ _ _ _ _ CL) as A2.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S c W ltac:(lia)) as MB. unfold kUserMapSize, EV_MAX in MB.
assert (XA : 0 <= x < rg_alloc_user (reg S c)).
{ pose proof (In_chunk_offs S k off Hk Eb) as IN. fold c x in IN.
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) x) as E.
exact (proj1 (E ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact IN))). }
assert (XS : x + class_size c <= rg_alloc_user (reg S c)).
{ pose proof G6 as G6'. apply Z.mod_divide in G6' as [qx Hqx]; [|lia]. pose proof A2 as A2'. apply Z.mod_divide in A2' as [qa Hqa]; [|lia].
assert (Hq : qx < qa) by (apply (Z.mul_lt_mono_pos_r (class_size c)); lia).
pose proof (Z.mul_le_mono_nonneg_r (qx + 1) qa (class_size c) ltac:(lia) ltac:(lia)). lia. }
assert (EXT : ck_extent k = class_size c) by (unfold ck_extent; rewrite Hp, G2; reflexivity).
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
destruct CK as (Hp & -> & sm & Hsm & Hlive & Hsz & Hlen).
pose proof (secondary_geometry (ck_req k) ltac:(lia) Hp) as (S1 & S2 & S3 & S4 & S5 & S6).
assert (INE : In (ly_sec ly r, sec_map_size (ck_req k)) (sec_extents ly S)).
{ unfold sec_extents. apply in_flat_map. exists k. split; [exact Hk|]. rewrite Eb. left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) PL _ INE) as (PA & [I1 I2] & I3). cbn [fst snd] in PA, I1, I2, I3.
assert (EXT : ck_extent k = sec_map_size (ck_req k) - kPage) by (unfold ck_extent; rewrite Hp; reflexivity).
rewrite EXT. unfold sptr_addr. cbn [sptr_exp aeval padd]. ceil; unfold page_aligned, kPage, kSecRz, ASAN_CEIL, kHighMemBeg in *.
split; [eapply in_app_sub; [exact (conj I1 I2) | lia | lia | lia] |].
assert (I2' : ly_sec ly r + sec_map_size (ck_req k) <= alloc_ceiling) by exact I3.
splits; try lia; try assumption; try reflexivity; try (eapply nth_error_lt; exact Hsm).
all: apply Z.mod_divide; [lia|]; apply Z.mod_divide in PA as [q Hq]; [|lia]; exists (q * 256 + 256); lia.
Qed.
Lemma chunk_apart : forall ly S rd k a, ARm B ly S rd -> In k (st_chunks S) ->
ck_base B ly k <= a < ck_base B ly k + ck_extent k -> ~ in_zr a (ly_img ly) /\ ~ (ly_stk_lo ly <= a < ly_stk_hi ly).
Proof.
intros ly S rd k a M Hk Ha. pose proof (am_layout _ _ _ _ M) as LO.
pose proof (chunk_facts ly S _ k M Hk) as (G1 & G2 & _ & G4 & G5 & _ & _ & G8 & GG).
destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal).
pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1 & R2 & _).
destruct (owned_extents_bound ly a LO ltac:(apply Exists_exists; exists (ly_prim ly, kPrimResvSize); split; [unfold owned_extents; cbn; tauto | unfold in_zr; cbn [fst snd]; lia])) as (_ & NS & NI). tauto.
- destruct GG as (_ & _ & Gbase & Gext & Gin & _).
destruct (owned_sec_bound ly S _ a M ltac:(apply Exists_exists; exists (ly_sec ly r, sec_map_size (ck_req k)); split; [exact Gin | unfold in_zr; cbn [fst snd]; unfold kPage in *; lia])) as (_ & NS & NI). tauto.
Qed.
Lemma pairwise_app : forall {X} (R : X -> X -> Prop) l1 l2,
pairwise R l1 -> pairwise R l2 -> (forall x y, In x l1 -> In y l2 -> R x y) -> pairwise R (l1 ++ l2).
Proof.
intros X R l1. induction l1 as [|x t IH]; intros l2 P1 P2 H; cbn in *; [exact P2|].
destruct P1 as [F P]. split.
- apply Forall_app. split; [exact F|]. apply Forall_forall. intros y Hy. apply H; auto.
- apply IH; [exact P | exact P2 | intros x' y Hx' Hy; apply H; auto].
Qed.
Lemma pairwise_map : forall {X Y} (R : X -> X -> Prop) (R' : Y -> Y -> Prop) (f : X -> Y) l,
(forall x y, In x l -> In y l -> R x y -> R' (f x) (f y)) -> pairwise R l -> pairwise R' (map f l).
Proof.
intros X Y R R' f l. induction l as [|x t IH]; intros H P; cbn in *; [exact I|]. destruct P as [F P]. split.
- apply Forall_forall. intros y Hy. apply in_map_iff in Hy as (x' & <- & Hx'). apply H; auto. exact (proj1 (Forall_forall _ _) F x' Hx').
- apply IH; [intros x' y Hx' Hy; apply H; auto | exact P].
Qed.
Lemma pairwise_of_keys : forall {X K} (key : X -> K) (R : X -> X -> Prop) l,
List.NoDup (map key l) -> (forall x y, In x l -> In y l -> key x <> key y -> R x y) -> pairwise R l.
Proof.
intros X K key R l. induction l as [|x t IH]; intros ND H; cbn in *; [exact I|]. inversion ND as [|k0 l0 Hni ND']; subst. split.
- apply Forall_forall. intros y Hy. apply H; auto. intros E. apply Hni. rewrite E. apply in_map_iff. exists y. auto.
- apply IH; [exact ND' | intros x' y Hx' Hy; apply H; auto].
Qed.
Lemma NoDup_map_filter : forall {X K} (key : X -> K) (p : X -> bool) l, List.NoDup (map key l) -> List.NoDup (map key (List.filter p l)).
Proof.
intros X K key p l. induction l as [|x t IH]; intros ND; cbn in *; [constructor|]. inversion ND as [|k0 l0 Hni ND']; subst.
destruct (p x); cbn; [|apply IH; exact ND']. constructor; [|apply IH; exact ND'].
intros Hin. apply Hni. apply in_map_iff in Hin as (y & E & Hy). pose proof (proj1 (List.filter_In p y t) Hy) as [Hy' _]. rewrite <- E. apply in_map_iff. exists y. auto.
Qed.
Lemma zdisjoint_sym : forall a b, zdisjoint a b -> zdisjoint b a.
Proof. intros a b. unfold zdisjoint. lia. Qed.
Lemma zdisjoint_sub : forall a b a' b', zdisjoint a b ->
fst a <= fst a' -> fst a' + snd a' <= fst a + snd a -> fst b <= fst b' -> fst b' + snd b' <= fst b + snd b -> 0 <= snd a' -> 0 <= snd b' ->
zdisjoint a' b'.
Proof. intros a b a' b'. unfold zdisjoint. lia. Qed.
Lemma sec_extents_split : forall ly S l1 k l2, st_chunks S = l1 ++ k :: l2 ->
sec_extents ly S = sec_extents ly (set_chunks l1 S) ++ sec_extents ly (set_chunks [k] S) ++ sec_extents ly (set_chunks l2 S).
Proof.
intros ly S l1 k l2 E. unfold sec_extents. cbn [st_chunks set_chunks]. rewrite E. change (k :: l2) with ([k] ++ l2).
rewrite !flat_map_app. reflexivity.
Qed.
Lemma chunks_disjoint : forall ly S rd k1 k2, ARm B ly S rd -> In k1 (st_chunks S) -> In k2 (st_chunks S) -> ck_beg k1 <> ck_beg k2 ->
zdisjoint (ck_base B ly k1, ck_extent k1) (ck_base B ly k2, ck_extent k2).
Proof.
intros ly S rd k1 k2 M H1 H2 Hne.
pose proof (am_layout _ _ _ _ M) as LO. pose proof (am_placed _ _ _ _ M) as [PL PD]. pose proof (am_wf _ _ _ _ M) as W.
pose proof (chunk_facts ly S rd k1 M H1) as F1. pose proof (chunk_facts ly S rd k2 M H2) as F2.
unfold cfacts in F1, F2.
destruct F1 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & C1). destruct F2 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & C2).
assert (PRIMSEC : forall ka kb oa rb ob, In ka (st_chunks S) -> In kb (st_chunks S) -> ck_beg ka = PPrim oa -> ck_beg kb = PSec rb ob ->
cfacts ly S ka -> cfacts ly S kb -> zdisjoint (ck_base B ly ka, ck_extent ka) (ck_base B ly kb, ck_extent kb)).
{ intros ka kb oa rb ob Ha Hb Ea Eb (X1 & X2 & _ & _ & _ & _ & _ & _ & Xa) (Y1 & Y2 & _ & _ & _ & _ & _ & _ & Yb). rewrite Ea in Xa. rewrite Eb in Yb.
cbv zeta in Xa. destruct Xa as (Xc & _ & _ & Xext & Xbase & Xx & _ & Xxs & Xal). destruct Yb as (_ & _ & Ybase & Yext & Yin & _).
pose proof (region_in_prim ly (prim_class oa) LO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (pairwise_In zdisjoint _ (ly_sec ly rb, sec_map_size (ck_req kb)) (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly)
eq_refl PD Yin ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
unfold zdisjoint in D |- *. cbn [fst snd] in D |- *. unfold kPage in *. lia. }
destruct (ck_beg k1) as [|o1|r1 q1|c1 p1] eqn:E1; try solve [destruct C1]; destruct (ck_beg k2) as [|o2|r2 q2|c2 p2] eqn:E2; try solve [destruct C2].
-
cbv zeta in C1, C2. destruct C1 as (Xc & _ & _ & Xext & Xbase & Xx & Xxm & Xxs & Xal). destruct C2 as (Yc & _ & _ & Yext & Ybase & Yx & Yxm & Yxs & Yal).
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
- exact (PRIMSEC k1 k2 o1 r2 q2 H1 H2 E1 E2 (chunk_facts ly S rd k1 M H1) (chunk_facts ly S rd k2 M H2)).
- apply zdisjoint_sym. exact (PRIMSEC k2 k1 o2 r1 q1 H2 H1 E2 E1 (chunk_facts ly S rd k2 M H2) (chunk_facts ly S rd k1 M H1)).
-
destruct C1 as (-> & _ & Xbase & Xext & Xin & _). destruct C2 as (-> & _ & Ybase & Yext & Yin & _).
rewrite Xbase, Ybase, Xext, Yext.
destruct (In_split_beg _ _ H1 (wf_chunks_nodup _ _ _ _ _ W)) as (l1 & l2 & E & N1 & N2).
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
Lemma fs_frames_eq : forall cid, 0 <= cid <= 10 -> fs_frames cid = 2 ^ (14 - cid).
Proof. intros cid H. unfold fs_frames, kStackSizeLog. rewrite Z.shiftl_1_l. f_equal; lia. Qed.
Lemma fs_frame_bytes_eq : forall cid, 0 <= cid -> fs_frame_bytes cid = 64 * 2 ^ cid.
Proof. intros cid H. unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.
Lemma frame_off_bounds : forall cid pos, 0 <= cid <= 10 -> 0 <= pos < fs_frames cid ->
kFakeFramesOff + cid * 2 ^ 20 <= fs_frame_off cid pos /\ fs_frame_off cid pos + fs_frame_bytes cid <= kFakeFramesOff + (cid + 1) * 2 ^ 20 /\
fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0 /\
kFakeFramesOff + (cid + 1) * 2 ^ 20 <= kFakeStackSize.
Proof.
intros cid pos Hc Hp. rewrite fs_frames_eq in Hp by lia. unfold fs_frame_off. rewrite fs_frame_bytes_eq by lia.
unfold kStackSizeLog. rewrite Z.shiftl_1_l.
pose proof (Z.pow_pos_nonneg 2 cid ltac:(lia) ltac:(lia)) as P1.
assert (E14 : 2 ^ (14 - cid) * 2 ^ cid = 2 ^ 14) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
assert (PB : (pos + 1) * (64 * 2 ^ cid) <= 2 ^ 20).
{ pose proof (Z.mul_le_mono_nonneg_r (pos + 1) (2 ^ (14 - cid)) (64 * 2 ^ cid) ltac:(lia) ltac:(lia)) as H.
replace (2 ^ (14 - cid) * (64 * 2 ^ cid)) with (64 * (2 ^ (14 - cid) * 2 ^ cid)) in H by lia. rewrite E14 in H. change (2 ^ 14) with 16384 in H. change (2 ^ 20) with 1048576. lia. }
unfold kFakeFramesOff, kFakeStackSize. change (2 ^ 20) with 1048576 in *.
pose proof (Z.mul_nonneg_nonneg pos (64 * 2 ^ cid) ltac:(lia) ltac:(lia)).
splits; try lia.
all: try (apply Z.mod_divide; [lia|]; exists (576 + cid * 16384 + pos * 2 ^ cid); lia).
all: try (apply Z.mod_divide; [lia|]; exists (2 ^ cid); lia).
Qed.
Lemma frames_apart : forall c1 p1 c2 p2, 0 <= c1 <= 10 -> 0 <= p1 < fs_frames c1 -> 0 <= c2 <= 10 -> 0 <= p2 < fs_frames c2 ->
(c1, p1) <> (c2, p2) -> zdisjoint (fs_frame_off c1 p1, fs_frame_bytes c1) (fs_frame_off c2 p2, fs_frame_bytes c2).
Proof.
intros c1 p1 c2 p2 H1 P1 H2 P2 Hne.
pose proof (frame_off_bounds c1 p1 H1 P1) as (A1 & A2 & _). pose proof (frame_off_bounds c2 p2 H2 P2) as (B1 & B2 & _).
unfold zdisjoint. cbn [fst snd].
destruct (Z.eq_dec c1 c2) as [<-|Hc].
- assert (p1 <> p2) by (intros ->; apply Hne; reflexivity).
unfold fs_frame_off in *. rewrite fs_frame_bytes_eq in * by lia. pose proof (Z.pow_pos_nonneg 2 c1 ltac:(lia) ltac:(lia)).
destruct (Z.lt_ge_cases p1 p2).
+ left. pose proof (Z.mul_le_mono_nonneg_r (p1 + 1) p2 (64 * 2 ^ c1) ltac:(lia) ltac:(lia)). lia.
+ right. pose proof (Z.mul_le_mono_nonneg_r (p2 + 1) p1 (64 * 2 ^ c1) ltac:(lia) ltac:(lia)). lia.
- destruct (Z.lt_ge_cases c1 c2).
+ left. pose proof (Z.mul_le_mono_nonneg_r (c1 + 1) c2 (2 ^ 20) ltac:(lia) ltac:(lia)). lia.
+ right. pose proof (Z.mul_le_mono_nonneg_r (c2 + 1) c1 (2 ^ 20) ltac:(lia) ltac:(lia)). lia.
Qed.
Definition flags_okb (cid : Z) : bool := (0 <=? fs_flags_off cid) && (fs_flags_off cid + fs_frames cid <=? 32768).
Lemma flags_ok : forall cid, 0 <= cid <= 10 -> 0 <= fs_flags_off cid /\ fs_flags_off cid + fs_frames cid <= 32768.
Proof.
assert (H : zall (Z.to_nat (10 - 0 + 1)) 0 flags_okb = true) by (vm_compute; reflexivity).
intros cid Hc. pose proof (zall_range 0 10 flags_okb H cid Hc) as Hb. unfold flags_okb in Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma flag_off_bounds : forall cid pos, 0 <= cid <= 10 -> 0 <= pos < fs_frames cid ->
kFakeFlagsOff <= fs_flag_off cid pos < kFakeFramesOff.
Proof. intros cid pos Hc Hp. pose proof (flags_ok cid Hc). unfold fs_flag_off, kFakeFlagsOff, kFakeFramesOff. lia. Qed.
Lemma frame_facts : forall ly S rd cid pos, ARm B ly S rd -> In (cid, pos) (frames S) ->
0 <= cid <= 10 /\ 0 <= pos < fs_frames cid /\
in_app (ly_F ly) kFakeStackSize /\ ~ (exists a, in_zr a (ly_F ly, kFakeStackSize) /\ (in_zr a (ly_img ly) \/ ly_stk_lo ly <= a < ly_stk_hi ly)) /\ page_aligned (ly_F ly) /\
kFakeFramesOff + cid * 2 ^ 20 <= fs_frame_off cid pos /\ fs_frame_off cid pos + fs_frame_bytes cid <= kFakeStackSize /\
fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0 /\
kFakeFlagsOff <= fs_flag_off cid pos < kFakeFramesOff.
Proof.
intros ly S rd cid pos M Hin. pose proof (am_layout _ _ _ _ M) as LO.
pose proof (wfs_live _ (wf_fakestack _ _ _ _ _ (am_wf _ _ _ _ M))) as LV. unfold frames in Hin.
pose proof (proj1 (Forall_forall _ _) LV _ Hin) as [H1 H2]. cbn [fst snd] in H1, H2.
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as F1. cbn [fst snd] in F1.
pose proof (frame_off_bounds cid pos H1 H2) as (A1 & A2 & A3 & A4 & A5 & A6). pose proof (flag_off_bounds cid pos H1 H2) as A7.
splits; try assumption; try lia; [| exact (lo_F_al _ LO)].
intros (a & Ha & Hbad). destruct (owned_extents_bound ly a LO ltac:(apply Exists_exists; exists (ly_F ly, kFakeStackSize); split; [unfold owned_extents; cbn; tauto | exact Ha])) as (_ & NS & NI). tauto.
Qed.
Lemma seg_rom_in_img : forall a, 0 <= a < 2 ^ 64 -> seg_rom segs (Z_to_bv 64 a) <> None -> in_img segs a.
Proof.
intros a Ha H. unfold seg_rom, memory_read in H.
rewrite Z_to_bv_unsigned, bv_wrap_small in H by (change (bv_modulus 64) with (2 ^ 64); lia). cbn [Z.of_N] in H.
destruct (find_segment segs a 1) as [sg|] eqn:E; [|exfalso; apply H; reflexivity].
apply find_segment_some_spec in E as (Hin & H1 & H2). exists sg. split; [exact Hin | lia].
Qed.
Lemma aview_present : forall ly S md H mem a, ALedger segs ly S md -> 0 <= a < 2 ^ 64 -> ~ in_zr a (ly_img ly) ->
aview segs H mem a <> None -> apresent H mem a.
Proof.
intros ly S md H mem a L Ha Himg Hv. unfold aview, mbyte, mrestrict in Hv. unfold apresent.
assert (NIMG : seg_rom segs (Z_to_bv 64 a) = None).
{ destruct (seg_rom segs (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
destruct (seg_rom_in_img a Ha ltac:(rewrite E; discriminate)) as (sg & Hsg & Hr). pose proof (al_img _ _ _ _ L sg Hsg). apply Himg. unfold in_zr. lia. }
destruct (H (Z_to_bv 64 a)) eqn:EH; [rewrite NIMG in Hv; exfalso; apply Hv; reflexivity|].
destruct (mem (Z_to_bv 64 a)) as [b|] eqn:EM; [split; [reflexivity | exists b; reflexivity]|].
rewrite NIMG in Hv. exfalso. apply Hv. reflexivity.
Qed.
Theorem AR_frames_law_ok : AR_frames_law segs B.
Proof.
intros ly S W mem md cid pos (M & L & _) Hin.
pose proof (frame_facts ly S _ cid pos M Hin) as (C1 & C2 & F1 & F2 & FA & O1 & O2 & O3 & O4 & O5 & O6).
pose proof (lo_img _ (am_layout _ _ _ _ M)) as IMG.
assert (IA : in_app (ly_F ly + fs_frame_off cid pos) (fs_frame_bytes cid)).
{ eapply in_app_sub; [exact F1 | | |]; unfold kFakeFramesOff, kFakeStackSize in *; pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)); lia. }
ceil; unfold frame_addr, in_app, page_aligned, ASAN_CEIL, kHighMemBeg, kLowShadowBeg, kImgLo, kImgEnd, kFakeFramesOff, kFakeStackSize, kFakeFlagsOff in *.
pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)).
assert (VIS1 : forall i, 0 <= i < fs_frame_bytes cid -> aview segs (w_H W) mem (ly_F ly + fs_frame_off cid pos + i) <> None).
{ intros i Hi. pose proof (proj1 (Forall_forall _ _) (am_client _ _ _ _ M) (AF (fs_frame_off cid pos), fs_frame_bytes cid)) as V.
unfold aclient in V. specialize (V ltac:(apply in_app_iff; right; apply in_app_iff; left; apply in_map_iff; exists (cid, pos); split; [reflexivity | exact Hin])).
exact (V i Hi). }
assert (VIS2 : forall i, 0 <= i < fs_frame_bytes cid / 8 -> aview segs (w_H W) mem (shadow_addr (ly_F ly + fs_frame_off cid pos) + i) <> None).
{ intros i Hi. pose proof (proj1 (Forall_forall _ _) (am_client _ _ _ _ M) (ASh (AF (fs_frame_off cid pos)), fs_frame_bytes cid / 8)) as V.
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
eapply aview_present; [exact L | lia | apply NI1; lia | apply VIS1; lia].
+ intros [_ NC]. apply NC. right. exists (cid, pos). split; [exact Hin|]. left. unfold in_zr, frame_addr. cbn [fst snd]. lia.
- intros i Hi. split.
+ eapply aview_present; [exact L | lia | apply NI2; lia | apply VIS2; exact Hi].
+ intros [_ NC]. apply NC. right. exists (cid, pos). split; [exact Hin|]. right. unfold in_zr, frame_addr. cbn [fst snd]. lia.
Qed.
Theorem AR_flag_law_ok : AR_flag_law segs B.
Proof.
intros ly S W mem md cid pos (M & L & _) Hin.
pose proof (frame_facts ly S _ cid pos M Hin) as (C1 & C2 & F1 & F2 & FA & O1 & O2 & O3 & O4 & O5 & O6).
pose proof (am_flags _ _ _ _ M cid pos C1 C2) as FL.
pose proof (am_layout _ _ _ _ M) as LO. pose proof (lo_img _ LO) as IMG.
assert (IA : in_app (ly_F ly + fs_flag_off cid pos) 1).
{ eapply in_app_sub; [exact F1 | | |]; unfold kFakeFramesOff, kFakeFlagsOff, kFakeStackSize in *; lia. }
pose proof (app_addr_below_ceil _ (in_app_addr _ _ (ly_F ly + fs_flag_off cid pos) IA ltac:(lia))) as AC.
assert (NI : ~ in_zr (ly_F ly + fs_flag_off cid pos) (ly_img ly)).
{ intros Hi. apply F2. exists (ly_F ly + fs_flag_off cid pos). split; [unfold in_zr, kFakeFramesOff, kFakeFlagsOff, kFakeStackSize in *; cbn [fst snd]; lia | left; exact Hi]. }
ceil; unfold flag_addr, in_app, kHighMemBeg, kLowShadowBeg, ASAN_CEIL, kImgEnd, kFakeFramesOff, kFakeFlagsOff, kFakeStackSize in *.
split; [|split; [|split; [exact IA | exact (proj2 AC)]]].
- eapply aview_present; [exact L | lia | exact NI | unfold flag_addr in FL; rewrite FL; discriminate].
- split.
+ right. left. apply Exists_exists. exists (ly_F ly, kFakeStackSize). split; [unfold owned_extents; cbn; tauto | unfold in_zr, kFakeStackSize; cbn; lia].
+ intros [(k & Hk & Hst & Hr)|(cp & Hcp & [Hr|Hr])].
*
pose proof (chunk_facts ly S _ k M Hk) as (G1 & G2 & _ & G4 & G5 & _ & _ & G8 & GG).
assert (D : zdisjoint (ck_base B ly k, ck_extent k) (ly_F ly, kFakeStackSize)).
{ destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal).
pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1 & R2 & _).
pose proof (pairwise_In zdisjoint (static_extents ly) (ly_prim ly, kPrimResvSize) (ly_F ly, kFakeStackSize) [_] _
ltac:(unfold static_extents, owned_extents; reflexivity) (lo_disj _ LO) (or_introl eq_refl) ltac:(cbn; tauto)) as D.
unfold zdisjoint in D |- *. cbn [fst snd] in D |- *. lia.
- destruct GG as (_ & _ & Gbase & Gext & Gin & _).
pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req k)) (ly_F ly, kFakeStackSize) _ (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) Gin
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
unfold zdisjoint in D |- *. cbn [fst snd] in D |- *. unfold kPage in *. lia. }
unfold zdisjoint, kFakeStackSize, ck_n in *. cbn [fst snd] in D. lia.
* destruct cp as [c2 p2]. cbn [fst snd] in Hr. unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr.
pose proof (frame_facts ly S _ c2 p2 M Hcp) as (Q1 & _ & _ & _ & _ & P1 & P2 & _). unfold kFakeFramesOff, kFakeStackSize in P1, P2.
pose proof (Z.mul_nonneg_nonneg c2 (2 ^ 20) ltac:(lia) ltac:(lia)). lia.
* destruct cp as [c2 p2]. cbn [fst snd] in Hr. unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr.
pose proof (frame_facts ly S _ c2 p2 M Hcp) as (Q1 & _ & _ & _ & _ & P1 & P2 & P3 & P4 & _). unfold kFakeFramesOff, kFakeStackSize in P1, P2.
pose proof (Z.mul_nonneg_nonneg c2 (2 ^ 20) ltac:(lia) ltac:(lia)).
pose proof (shadow_range_below (ly_F ly + fs_frame_off c2 p2) (fs_frame_bytes c2) ltac:(lia) ltac:(lia)) as SB.
pose proof (shadow_addr_bounds (ly_F ly + fs_frame_off c2 p2) ltac:(lia)) as [SB0 _].
unfold kHighMemEnd, kHighMemBeg, SHADOW_OFF in SB, SB0. lia.
Qed.
Lemma chunk_vs_F : forall ly S rd k, ARm B ly S rd -> In k (st_chunks S) -> zdisjoint (ck_base B ly k, ck_extent k) (ly_F ly, kFakeStackSize).
Proof.
intros ly S rd k M Hk. pose proof (am_layout _ _ _ _ M) as LO.
pose proof (chunk_facts ly S _ k M Hk) as (G1 & G2 & _ & G4 & G5 & _ & _ & G8 & GG).
destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal).
pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1 & R2 & _).
pose proof (pairwise_In zdisjoint (static_extents ly) (ly_prim ly, kPrimResvSize) (ly_F ly, kFakeStackSize) [_] _
ltac:(unfold static_extents, owned_extents; reflexivity) (lo_disj _ LO) (or_introl eq_refl) ltac:(cbn; tauto)) as D.
unfold zdisjoint in D |- *. cbn [fst snd] in D |- *. lia.
- destruct GG as (_ & _ & Gbase & Gext & Gin & _).
pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req k)) (ly_F ly, kFakeStackSize) _ (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) Gin
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
unfold zdisjoint in D |- *. cbn [fst snd] in D |- *. unfold kPage in *. lia.
Qed.
Lemma In_ablocks : forall ly S p n, In (p, n) (ablocks B ly S) <->
exists k, In k (st_chunks S) /\ ck_state k = CAllocated /\ sptr_addr B ly (ck_user k) = p /\ ck_req k = n.
Proof.
intros ly S p n. unfold ablocks. rewrite in_map_iff. split.
- intros ([p' n'] & E & Hin). cbn in E. injection E as <- <-. apply In_blocks in Hin as (k & Hk & Hs & Hu & Hr). exists k. rewrite Hu. auto.
- intros (k & Hk & Hs & Hu & Hr). exists (ck_user k, ck_req k). cbn. rewrite Hu, Hr. split; [reflexivity|]. apply In_blocks. exists k. auto.
Qed.
Definition brange (ly : alayout) (k : chunk) : Z * Z := (sptr_addr B ly (ck_user k), req_size (ck_req k)).
Definition frange (ly : alayout) (f : Z * Z) : Z * Z := (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f)).
Lemma blocks_ranges_eq : forall ly S,
map (fun b => (fst b, req_size (snd b))) (ablocks B ly S) = map (brange ly) (List.filter is_alloc (st_chunks S)).
Proof. intros ly S. unfold ablocks, blocks. rewrite !map_map. reflexivity. Qed.
Lemma blocks_pairwise : forall ly S rd, ARm B ly S rd -> pairwise zdisjoint (map (brange ly) (List.filter is_alloc (st_chunks S))).
Proof.
intros ly S rd M.
apply (pairwise_map (fun k1 k2 => ck_beg k1 <> ck_beg k2) zdisjoint (brange ly)).
- intros x y Hx Hy Hne. apply filter_In in Hx as [Hx _]. apply filter_In in Hy as [Hy _].
pose proof (chunks_disjoint ly S rd x y M Hx Hy Hne) as D.
pose proof (chunk_facts ly S rd x M Hx) as (_ & _ & _ & X4 & X5 & _ & X7 & X8 & _).
pose proof (chunk_facts ly S rd y M Hy) as (_ & _ & _ & Y4 & Y5 & _ & Y7 & Y8 & _).
pose proof (req_size_bounds (ck_req x) ltac:(lia)). pose proof (req_size_bounds (ck_req y) ltac:(lia)).
unfold brange, zdisjoint in *. cbn [fst snd] in *. lia.
- apply (pairwise_of_keys ck_beg). { apply NoDup_map_filter. exact (wf_chunks_nodup _ _ _ _ _ (am_wf _ _ _ _ M)). }
intros x y _ _ Hne. exact Hne.
Qed.
Lemma frames_pairwise : forall ly S rd, ARm B ly S rd -> pairwise zdisjoint (map (frange ly) (frames S)).
Proof.
intros ly S rd M. pose proof (wfs_nodup _ (wf_fakestack _ _ _ _ _ (am_wf _ _ _ _ M))) as ND. unfold frames.
apply (pairwise_map (fun f1 f2 => f1 <> f2) zdisjoint (frange ly)).
- intros [c1 p1] [c2 p2] H1 H2 Hne.
pose proof (frame_facts ly S rd c1 p1 M H1) as (A1 & A2 & _). pose proof (frame_facts ly S rd c2 p2 M H2) as (B1 & B2 & _).
pose proof (frames_apart c1 p1 c2 p2 A1 A2 B1 B2 Hne) as D. unfold frange, frame_addr, zdisjoint in *. cbn [fst snd] in *. lia.
- apply (pairwise_of_keys (fun f : Z * Z => f)); [rewrite map_id; exact ND|]. intros x y _ _ Hne. exact Hne.
Qed.
Theorem AR_sep_law_ok : AR_sep_law segs B.
Proof.
intros ly S W mem md (M & L & _). split.
- rewrite blocks_ranges_eq. change (fun f : Z * Z => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) with (frange ly).
apply pairwise_app; [eapply blocks_pairwise; exact M | eapply frames_pairwise; exact M |].
intros x y Hx Hy. apply in_map_iff in Hx as (k & <- & Hk). apply filter_In in Hk as [Hk _]. apply in_map_iff in Hy as ([cid pos] & <- & Hf).
pose proof (chunk_vs_F ly S _ k M Hk) as D. pose proof (chunk_facts ly S _ k M Hk) as (_ & _ & _ & X4 & X5 & _ & X7 & X8 & _).
pose proof (frame_facts ly S _ cid pos M Hf) as (Fc & _ & _ & _ & _ & P1 & P2 & _). pose proof (req_size_bounds (ck_req k) ltac:(lia)).
unfold brange, frange, frame_addr, zdisjoint, kFakeFramesOff, kFakeStackSize in *. cbn [fst snd] in *. pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)). lia.
- apply Forall_forall. intros [cid pos] Hf. cbn [fst snd].
pose proof (frame_facts ly S _ cid pos M Hf) as (C1 & _ & F1 & F2 & _ & P1 & P2 & _).
ceil; unfold frame_addr, in_app, kHighMemBeg, kLowShadowBeg, ASAN_CEIL, kFakeFramesOff, kFakeStackSize in *.
pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)). lia.
Qed.
Theorem AR_blocks_law_ok : AR_blocks_law segs B.
Proof.
intros ly S W mem md p n (M & L & _) Hin. pose proof Hin as Hin0.
apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hr). subst p n.
pose proof (chunk_facts ly S _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG). rewrite G4.
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
assert (IA : in_app (ck_base B ly k + ck_rz k) (req_size (ck_req k))) by (eapply in_app_sub; [exact G1 | lia | lia | lia]).
ceil; unfold in_app, kHighMemBeg, kLowShadowBeg, ASAN_CEIL in *.
splits; try lia.
all: try (apply Z.mod_divide; [lia|]; apply Z.mod_divide in G3 as [q Hq]; [|lia]; apply Z.mod_divide in G6 as [q' Hq']; [|lia]; exists (q + q'); lia).
- intros a Ha. split.
+ pose proof (proj1 (Forall_forall _ _) (am_client _ _ _ _ M) (sptr_exp (ck_user k), ck_n k)) as V. unfold aclient in V.
specialize (V ltac:(apply in_app_iff; left; apply in_flat_map; exists k; split; [exact Hk | unfold chunk_user; rewrite Hst; left; reflexivity])).
unfold range_vis in V. cbn [fst snd] in V. fold (sptr_addr B ly (ck_user k)) in V. rewrite G4 in V.
replace a with (ck_base B ly k + ck_rz k + (a - (ck_base B ly k + ck_rz k))) by lia.
destruct (chunk_apart ly S _ k (ck_base B ly k + ck_rz k + (a - (ck_base B ly k + ck_rz k))) M Hk ltac:(clear - Ha G5 G8; lia)) as [NI _].
eapply aview_present; [exact L | lia | exact NI | apply V; unfold ck_n; lia].
+ intros [_ NC]. apply NC. left. exists k. rewrite G4. unfold ck_n. auto.
- rewrite blocks_ranges_eq. eapply blocks_pairwise. exact M.
Qed.
Lemma client_byte_not_img : forall ly S rd a, ARm B ly S rd -> aclient_byte B ly S a -> ~ in_zr a (ly_img ly).
Proof.
intros ly S rd a M C. pose proof (am_layout _ _ _ _ M) as LO. pose proof (lo_img _ LO) as IMG.
destruct C as [(k & Hk & Hst & Hr)|(cp & Hcp & Hr)].
- pose proof (chunk_facts ly S rd k M Hk) as (G1 & _ & _ & G4 & G5 & _ & G7 & G8 & _). pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
apply (proj1 (chunk_apart ly S rd k a M Hk ltac:(rewrite G4 in Hr; unfold ck_n in Hr; lia))).
- destruct cp as [cid pos]. cbn [fst snd] in Hr. pose proof (frame_facts ly S rd cid pos M Hcp) as (C1 & _ & F1 & F2 & _ & P1 & P2 & _).
pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)).
destruct Hr as [Hr|Hr].
+ intros Hi. apply F2. exists a. split; [unfold in_zr, frame_addr, kFakeFramesOff, kFakeStackSize in *; cbn [fst snd] in *; lia | left; exact Hi].
+ unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr. unfold in_app, kFakeFramesOff in *.
pose proof (shadow_addr_bounds (ly_F ly + fs_frame_off cid pos) ltac:(lia)) as [SB _].
unfold SHADOW_OFF, in_zr, kImgLo, kImgEnd, page_aligned in *. cbn [fst snd] in *. lia.
Qed.
(* ===== Knock (DepotCfg.depot_has_trace = false): the kernel half of git-lead's depot_first_put_pre (AD3j). An empty
   depot's AR gives the words the first Put reads as 0, and every extent and byte the first Put's two maps must miss is
   taken in the model (vm_takes). In a one-trace unit the statement is True. ===== *)
Lemma in_app_small : forall lo len, in_app lo len -> 0 <= len -> 0 <= lo /\ lo + len < 2 ^ 64.
Proof. intros lo len [H0 H] Hl. pose proof ASAN_CEIL_range as [CR _]. unfold kLowShadowBeg, kHighMemBeg in H. lia. Qed.
Lemma map_takes : forall md z, In (wiv z) (vm_maps (m_vmmaps md)) -> 0 < snd z -> 0 <= fst z -> fst z + snd z < 2 ^ 64 ->
vm_takes md z.
Proof.
intros md z Hin P A1 A2. left. split; [exact P|]. intros a Ha. apply Exists_exists. exists (wiv z).
split; [apply in_or_app; right; exact Hin|]. unfold wiv, w64. cbn [fst snd].
rewrite !Z_to_bv_unsigned, !bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). unfold in_zr in Ha. exact Ha.
Qed.
Lemma vm_takes_range : forall md e e', vm_takes md e -> fst e <= fst e' -> fst e' + snd e' <= fst e + snd e -> 0 < snd e' ->
vm_takes md e'.
Proof.
intros md e e' [[P C]|T] H1 H2 H3.
- left. split; [exact H3|]. intros a Ha. apply C. unfold in_zr in *. lia.
- right. lia.
Qed.
Lemma perm_in : forall ly z, z = (ly_T ly, kThreadObjSize) \/ z = (ly_F ly, kFakeStackSize) \/ z = (ly_C ly, kCtxMapSize) \/
z = (ly_D ly, 4096) \/ In z (ly_extra ly) -> In z (depot_pick (perm_maps ly) (perm_live ly)).
Proof.
intros ly z H. lazymatch eval cbv in depot_has_trace with
| true => unfold perm_maps; destruct H as [->|[->|[->|[->|H]]]]; cbn; tauto
| false => unfold perm_live; destruct (ly_NB ly =? 0), (ly_SB ly =? 0); destruct H as [->|[->|[->|[->|H]]]]; cbn; tauto
end.
Qed.
Lemma perm_takes : forall ly S md z, ALedger segs ly S md -> (z = (ly_T ly, kThreadObjSize) \/ z = (ly_F ly, kFakeStackSize) \/
z = (ly_C ly, kCtxMapSize) \/ z = (ly_D ly, 4096) \/ In z (ly_extra ly)) -> 0 < snd z -> 0 <= fst z -> fst z + snd z < 2 ^ 64 ->
vm_takes md z.
Proof. intros ly S md z L H P A1 A2. exact (map_takes md z (al_perm _ _ _ _ L z (perm_in ly z H)) P A1 A2). Qed.
Lemma owned_in_app : forall ly e, layout_ok ly -> In e (owned_extents ly) -> in_app (fst e) (snd e).
Proof. intros ly e LO He. exact (proj1 (Forall_forall _ _) (lo_app _ LO) e He). Qed.
Lemma sec_extent_facts : forall ly S rd e, ARm B ly S rd -> In e (sec_extents ly S) -> 0 < snd e /\ in_app (fst e) (snd e).
Proof.
intros ly S rd e M He. pose proof (am_placed _ _ _ _ M) as [PL _].
pose proof (proj1 (Forall_forall _ _) PL e He) as (_ & IA & _). split; [|exact IA].
unfold sec_extents in He. apply in_flat_map in He as (k & Hk & Hin).
pose proof (chunk_facts ly S rd k M Hk) as (_ & _ & _ & _ & G5 & _ & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
revert Hin GG. destruct (ck_beg k) as [|off|r o|c p]; intros Hin GG; cbn in Hin; try contradiction.
destruct Hin as [<-|[]]. cbn [snd]. destruct GG as (_ & _ & _ & GE & _). unfold kPage in *. lia.
Qed.
Lemma band_takes : forall ly S md a, ALedger segs ly S md -> kLowShadowBeg <= a < kHighShadowEnd -> vm_takes md (a, 1).
Proof.
intros ly S md a L Ha.
assert (BT : forall z, In z band_maps -> vm_takes md z).
{ intros z Hz. apply map_takes; [exact (al_band _ _ _ _ L z Hz) | | |];
  unfold band_maps in Hz; cbn in Hz; destruct Hz as [<-|[<-|[<-|[]]]]; cbn [fst snd];
  unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd; lia. }
destruct (Z_lt_le_dec a kLowShadowEnd) as [H1|H1]; [|destruct (Z_lt_le_dec a kHighShadowBeg) as [H2|H2]].
- eapply vm_takes_range; [apply BT; unfold band_maps; left; reflexivity | cbn [fst snd]; lia | cbn [fst snd]; lia | cbn; lia].
- eapply vm_takes_range; [apply BT; unfold band_maps; right; left; reflexivity | cbn [fst snd]; lia | cbn [fst snd]; lia | cbn; lia].
- eapply vm_takes_range; [apply BT; unfold band_maps; right; right; left; reflexivity | cbn [fst snd]; lia | cbn [fst snd]; lia | cbn; lia].
Qed.
Lemma aclient_takes : forall ly S rd md a, ARm B ly S rd -> ALedger segs ly S md -> aclient_byte B ly S a -> vm_takes md (a, 1).
Proof.
intros ly S rd md a M L C. pose proof (am_layout _ _ _ _ M) as LO.
destruct C as [(k & Hk & Hst & Hr)|((cid, pos) & Hcp & Hr)].
- pose proof (chunk_facts ly S rd k M Hk) as (G1 & G2 & _ & G4 & G5 & _ & G7 & G8 & GG).
  pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
  assert (HA : ck_base B ly k <= a < ck_base B ly k + ck_extent k) by (rewrite G4 in Hr; unfold ck_n in Hr; lia).
  revert GG. destruct (ck_beg k) as [|off|r o|c p]; intros GG; try contradiction.
  + cbv zeta in GG. destruct GG as (C1 & _ & _ & CE & CB & X0 & _ & XS & MU).
    pose proof (region_in_prim ly (prim_class off) LO ltac:(lia)) as (R1 & R2 & _).
    eapply vm_takes_range; [exact (prim_takes ly S rd md M L) | cbn [fst snd]; lia | cbn [fst snd]; lia | cbn [snd]; lia].
  + destruct GG as (_ & _ & CB & CE & IN & _).
    pose proof (sec_extent_facts ly S rd _ M IN) as [P IA]. cbn [fst snd] in P, IA.
    pose proof (in_app_small _ _ IA ltac:(lia)) as [A1 A2].
    eapply vm_takes_range; [exact (map_takes md _ (al_sec _ _ _ _ L _ IN) P A1 A2) | cbn [fst snd]; unfold kPage in *; lia
    | cbn [fst snd]; unfold kPage in *; lia | cbn [snd]; lia].
- cbn [fst snd] in Hr. pose proof (frame_facts ly S rd cid pos M Hcp) as (C1 & C2 & F1 & _ & FA & P1 & P2 & _).
  pose proof (in_app_small _ _ F1 ltac:(unfold kFakeStackSize; lia)) as [A1 A2].
  pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)).
  destruct Hr as [Hr|Hr].
  + assert (FM : vm_takes md (ly_F ly, kFakeStackSize)).
    { apply (perm_takes ly S md _ L); [right; left; reflexivity | unfold kFakeStackSize; cbn; lia | exact A1 | exact A2]. }
    unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr.
    eapply vm_takes_range; [exact FM | cbn [fst snd]; unfold kFakeFramesOff in *; lia | cbn [fst snd]; lia | cbn [snd]; lia].
  + apply (band_takes ly S md a L). unfold in_zr, frame_addr, shadow_addr, SHADOW_OFF in Hr. cbn [fst snd] in Hr.
    pose proof ASAN_CEIL_range as [CR _]. destruct F1 as [F0 [FB|[FB1 FB2]]];
    unfold kLowShadowBeg, kHighShadowEnd, kHighMemBeg, kFakeStackSize, kFakeFramesOff in *; Z.div_mod_to_equations; lia.
Qed.
(* The takes part (every configuration): what a fresh map placed by the kernel's mmap model must miss is taken. *)
Lemma AR_avoid_takes : forall ly S rd md, ARm B ly S rd -> ALedger segs ly S md ->
Forall (vm_takes md) (kd_avoid ly S) /\ (forall a, aclient_byte B ly S a -> vm_takes md (a, 1)) /\ vm_takes md (ly_img ly).
Proof.
intros ly S rd md M L. pose proof (am_layout _ _ _ _ M) as LO.
assert (IMG : vm_takes md (ly_img ly)) by exact (img_takes segs ly S md L (proj1 (proj2 (lo_img _ LO)))).
split; [|split; [intros a Ha; exact (aclient_takes ly S _ md a M L Ha) | exact IMG]].
unfold kd_avoid; apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split]].
- pose proof (owned_in_app ly (ly_Q ly, kPtrArrayResv) LO ltac:(unfold owned_extents; cbn; tauto)) as IQ.
  pose proof (owned_in_app ly (ly_T ly, kThreadObjSize) LO ltac:(unfold owned_extents; cbn; tauto)) as IT.
  pose proof (owned_in_app ly (ly_F ly, kFakeStackSize) LO ltac:(unfold owned_extents; cbn; tauto)) as IF.
  pose proof (owned_in_app ly (ly_C ly, 256) LO ltac:(unfold owned_extents; cbn; tauto)) as IC.
  pose proof (owned_in_app ly (ly_D ly, 4096) LO ltac:(unfold owned_extents; cbn; tauto)) as ID.
  cbn [fst snd] in IQ, IT, IF, IC, ID.
  pose proof ASAN_CEIL_range as [CR _].
  apply Forall_cons; [exact (prim_takes ly S _ md M L)|].
  apply Forall_cons; [destruct (in_app_small _ _ IQ ltac:(unfold kPtrArrayResv; lia)) as [A1 A2];
    exact (map_takes md _ (al_Q _ _ _ _ L) ltac:(unfold kPtrArrayResv; cbn; lia) A1 A2)|].
  apply Forall_cons; [destruct (in_app_small _ _ IT ltac:(unfold kThreadObjSize; lia)) as [A1 A2];
    apply (perm_takes ly S md _ L); [left; reflexivity | unfold kThreadObjSize; cbn; lia | exact A1 | exact A2]|].
  apply Forall_cons; [destruct (in_app_small _ _ IF ltac:(unfold kFakeStackSize; lia)) as [A1 A2];
    apply (perm_takes ly S md _ L); [right; left; reflexivity | unfold kFakeStackSize; cbn; lia | exact A1 | exact A2]|].
  apply Forall_cons; [destruct (in_app_small _ _ IC ltac:(lia)) as [A1 A2];
    apply (vm_takes_range md (ly_C ly, kCtxMapSize)); [| cbn; lia | cbn; unfold kCtxMapSize; lia | cbn; lia];
    apply (perm_takes ly S md _ L); [right; right; left; reflexivity | unfold kCtxMapSize; cbn; lia | cbn; lia
    | cbn; destruct IC as [_ [IC|[_ IC]]]; unfold kCtxMapSize, kLowShadowBeg in *; lia]|].
  apply Forall_cons; [destruct (in_app_small _ _ ID ltac:(lia)) as [A1 A2];
    apply (perm_takes ly S md _ L); [right; right; right; left; reflexivity | cbn; lia | exact A1 | exact A2]|].
  apply Forall_cons; [exact (stack_takes ly S md L (lo_stk_ceil _ LO))|].
  apply Forall_cons; [exact IMG|]. apply Forall_nil.
- apply Forall_forall. intros z Hz. destruct (lo_extra _ LO) as (_ & EX & _).
  pose proof (proj1 (Forall_forall _ _) EX z Hz) as (_ & [P1 P2] & P3 & P4 & _). pose proof ASAN_CEIL_range as [CR _].
  apply (perm_takes ly S md _ L); [right; right; right; right; exact Hz | lia | lia | lia].
- apply Forall_forall. intros e He. destruct (sec_extent_facts ly S _ e M He) as [P IA].
  destruct (in_app_small _ _ IA ltac:(lia)) as [A1 A2]. exact (map_takes md e (al_sec _ _ _ _ L e He) P A1 A2).
- apply Forall_forall. intros z Hz. apply map_takes; [exact (al_band _ _ _ _ L z Hz) | | |];
  unfold band_maps in Hz; cbn in Hz; destruct Hz as [<-|[<-|[<-|[]]]]; cbn [fst snd];
  unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd; lia.
Qed.
(* The kernel half of depot_first_put_pre: the pre-Put zero words (nodes-map mutex, blocks_[0].stored_ / .mtx_) and
   allocated_ = 0, plus AR_avoid_takes. True in a one-trace unit. *)
Lemma AR_first_put_facts : forall ly S W mem md, AR segs B ly S W mem md -> st_depot S = [] ->
depot_pick True
(Forall (cell_holds B ly (aview segs (w_H W) mem))
  [ z4 (ADepot d_mu) 0; z4 (AStore s_stored0) 0; z4 (AStore s_mtx0) 0; z8 (AStore s_alloc) 0 ] /\
 Forall (vm_takes md) (kd_avoid ly S) /\ (forall a, aclient_byte B ly S a -> vm_takes md (a, 1)) /\ vm_takes md (ly_img ly)).
Proof.
intros ly S W mem md (M & L & _) E. lazymatch eval cbv in depot_has_trace with
| true => exact I
| false =>
assert (CELLS : Forall (cell_holds B ly (aview segs (w_H W) mem)) (depot_cells ly S)) by
  (pose proof (am_cells _ _ _ _ M) as AC; unfold acells in AC;
   do 6 (apply Forall_app in AC as [_ AC]); apply Forall_app in AC as [AC _]; exact AC);
rewrite (depot_cells_pre ly S E) in CELLS; do 4 (apply Forall_cons_iff in CELLS as [_ CELLS]);
exact (conj CELLS (AR_avoid_takes ly S _ md M L))
end.
Qed.
Theorem AR_client_img_law_ok : AR_client_img_law segs B.
Proof.
intros ly S W mem md a (M & L & _) HC.
assert (NZ : ~ in_zr a (ly_img ly)).
{ destruct HC as [(p & n & Hin & Hr)|[(cid & pos & Hin & Hr)|(cid & pos & Hin & ->)]].
- apply (client_byte_not_img ly S _ a M).
apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hn). subst p n. left. exists k. split; [exact Hk|]. split; [exact Hst|].
unfold ck_n. exact Hr.
- apply (client_byte_not_img ly S _ a M).
right. exists (cid, pos). split; [exact Hin|]. left. unfold in_zr. cbn [fst snd]. exact Hr.
-
pose proof (frame_facts ly S _ cid pos M Hin) as (Fc & Fp & F1 & F2 & _). pose proof (flag_off_bounds cid pos Fc Fp) as FB.
intros IN. apply F2. exists (flag_addr ly cid pos).
split; [unfold in_zr, flag_addr; cbn [fst snd]; unfold kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *; lia | left; exact IN]. }
split; [exact NZ|]. intros (sg & Hsg & Ha). apply NZ. pose proof (al_img _ _ _ _ L sg Hsg) as [I1 I2]. unfold in_zr. lia.
Qed.
Theorem AR_owned_image_law_ok : AR_owned_image_law segs B.
Proof.
intros ly S W mem md a (M & L & _) (sg & Hsg & Ha). pose proof (al_img _ _ _ _ L sg Hsg) as [I1 I2]. pose proof (am_layout _ _ _ _ M) as LO.
pose proof (lo_img _ LO) as IMG.
assert (AI : in_zr a (ly_img ly)) by (unfold in_zr; lia).
split.
- intros [[O|[O|[O|[O|O]]]] _]; [exact O | exfalso ..].
+ exact (proj2 (proj2 (owned_extents_bound ly a LO O)) AI).
+ exact (proj2 (proj2 (owned_extents_bound ly a LO ltac:(apply Exists_exists; exists (ly_C ly, 256); split; [unfold owned_extents; cbn; tauto | exact O]))) AI).
+ exact (proj2 (proj2 (owned_sec_bound ly S _ a M O)) AI).
+ pose proof (owned_shadow_bound ly S _ a M O). unfold SHADOW_OFF, in_zr, kImgLo, kImgEnd, page_aligned in *. cbn [fst snd] in *. lia.
- intros O. split; [left; exact O|]. intros C. exact (client_byte_not_img ly S _ a M C AI).
Qed.
Lemma sptr_addr_le : forall ly ly' n p, layout_le n ly ly' -> match p with PSec r _ => (r < n)%nat | _ => True end ->
sptr_addr B ly' p = sptr_addr B ly p.
Proof.
intros ly ly' n p LE Hp. destruct LE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & ED & EI & E15).
destruct p; unfold sptr_addr; cbn; rewrite ?E2, ?E6; try reflexivity. rewrite E15 by exact Hp. reflexivity.
Qed.
Lemma sec_extents_le : forall ly ly' S U pp cc bb, layout_le (length (st_secs S)) ly ly' -> WfP U pp cc bb S ->
sec_extents ly' S = sec_extents ly S.
Proof.
intros ly ly' S U pp cc bb LE W. destruct LE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & ED & EI & E15).
unfold sec_extents. pose proof (wf_chunks _ _ _ _ _ W) as CK.
induction (st_chunks S) as [|k t IH]; [reflexivity|]. inversion CK as [|k0 t0 [Hn C] CKt]; subst. cbn [flat_map].
rewrite (IH CKt). destruct (ck_beg k) as [|o|r o|c p]; try reflexivity. destruct C as (_ & _ & sm & Hsm & _).
rewrite E15 by (eapply nth_error_lt; exact Hsm). reflexivity.
Qed.
Theorem AR_layout_law_ok : AR_layout_law segs B.
Proof.
intros ly S W mem md ly' (M & L & _) LE. pose proof (am_wf _ _ _ _ M) as WF.
pose proof LE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & ED & EI & E15).
assert (USR : forall k, In k (st_chunks S) -> sptr_addr B ly' (ck_user k) = sptr_addr B ly (ck_user k)).
{ intros k Hk. apply (sptr_addr_le ly ly' (length (st_secs S))); [exact LE|].
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) k Hk) as [_ C]. unfold ck_user.
destruct (ck_beg k) as [|o|r o|c p]; cbn; try exact I. destruct C as (_ & _ & sm & Hsm & _). eapply nth_error_lt. exact Hsm. }
assert (FR : forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos) by (intros; unfold frame_addr; rewrite E6; reflexivity).
splits.
- unfold ablocks, blocks. rewrite !map_map. apply map_ext_in. intros k Hk. apply filter_In in Hk as [Hk _]. cbn [fst snd]. rewrite (USR k Hk). reflexivity.
- exact FR.
- intros a. unfold aowned, aclient_byte.
rewrite (sec_extents_le ly ly' S _ _ _ _ LE WF).
assert (EO : owned_extents ly' = owned_extents ly) by (unfold owned_extents; rewrite E1, E3, E4, E5, E6, E7, E8, ED; reflexivity).
assert (ES : static_extents ly' = static_extents ly) by (unfold static_extents; rewrite EO, E10, E11, EI; reflexivity).
assert (EZ : zero_shadow_ranges B ly' = zero_shadow_ranges B ly) by (unfold zero_shadow_ranges; rewrite E10, E11; reflexivity).
rewrite EO, ES, EZ, E5.
assert (CB : (exists k, In k (st_chunks S) /\ ck_state k = CAllocated /\ sptr_addr B ly' (ck_user k) <= a < sptr_addr B ly' (ck_user k) + ck_n k) <->
(exists k, In k (st_chunks S) /\ ck_state k = CAllocated /\ sptr_addr B ly (ck_user k) <= a < sptr_addr B ly (ck_user k) + ck_n k)).
{ split; intros (k & Hk & Hs & Hr); exists k; rewrite ?(USR k Hk) in *; auto. }
assert (CF : forall cp, (in_zr a (frame_addr ly' (fst cp) (snd cp), fs_frame_bytes (fst cp)) \/ in_zr a (shadow_addr (frame_addr ly' (fst cp) (snd cp)), fs_frame_bytes (fst cp) / 8)) <->
(in_zr a (frame_addr ly (fst cp) (snd cp), fs_frame_bytes (fst cp)) \/ in_zr a (shadow_addr (frame_addr ly (fst cp) (snd cp)), fs_frame_bytes (fst cp) / 8))).
{ intros cp. rewrite !FR. tauto. }
split; intros [O NC]; (split; [exact O|]); intros C; apply NC; destruct C as [C|(cp & Hcp & C)].
+ left. apply CB. exact C.
+ right. exists cp. split; [exact Hcp|]. apply CF. exact C.
+ left. apply CB. exact C.
+ right. exists cp. split; [exact Hcp|]. apply CF. exact C.
Qed.
Lemma In_zseq : forall lo n x, lo <= x < lo + n -> In x (zseq lo n).
Proof.
intros lo n x H. unfold zseq. apply in_map_iff. exists (Z.to_nat (x - lo)). split; [lia|]. apply in_seq. lia.
Qed.
Lemma in_rangesb_In : forall g l lo len, In (lo, len) l -> lo <= g < lo + len -> in_rangesb g l = true.
Proof.
intros g l lo len Hin Hg. induction l as [|[lo' len'] t IH]; [destruct Hin|]. cbn [in_rangesb].
destruct Hin as [E|Hin]; [injection E as -> ->|].
- replace (lo <=? g) with true by (symmetry; apply Z.leb_le; lia). replace (g <? lo + len) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
- rewrite (IH Hin). apply Bool.orb_true_r.
Qed.
Lemma ashadow_total : forall ly S g lo len, In (lo, len) (fa_poison_ranges ly S) -> lo <= g < lo + len -> exists v, ashadow B ly S g = Some v.
Proof.
intros ly S g lo len Hin Hg. unfold ashadow. destruct (find_chunk_at B ly (st_chunks S) g); [eexists; reflexivity|].
rewrite (in_rangesb_In g _ lo len Hin Hg). eexists. reflexivity.
Qed.
Lemma find_chunk_at_hit : forall ly S rd l k g, ARm B ly S rd -> incl l (st_chunks S) -> List.NoDup (map ck_beg l) -> In k l ->
ck_base B ly k <= g < ck_base B ly k + ck_extent k -> find_chunk_at B ly l g = Some k.
Proof.
intros ly S rd l k g M. induction l as [|k' t IH]; intros Hincl ND Hk Hg; [destruct Hk|]. cbn [find_chunk_at].
inversion ND as [|b0 l0 Hni ND']; subst.
destruct (andb (ck_base B ly k' <=? g) (g <? ck_base B ly k' + ck_extent k')) eqn:E.
- apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. f_equal.
destruct (sptr_eqb (ck_beg k') (ck_beg k)) eqn:Ebq; [apply sptr_eqb_spec in Ebq as Eb | assert (Nb : ck_beg k' <> ck_beg k) by (intros E'; apply sptr_eqb_spec in E'; congruence)].
+ destruct Hk as [->|Hk]; [reflexivity|]. exfalso. apply Hni. rewrite Eb. apply in_map_iff. exists k. auto.
+ exfalso. pose proof (chunks_disjoint ly S rd k' k M (Hincl k' (or_introl eq_refl)) (Hincl k ltac:(exact (or_introl eq_refl) || (destruct Hk as [->|Hk]; [left; reflexivity | right; exact Hk]))) Nb) as D.
unfold zdisjoint in D. cbn [fst snd] in D.
pose proof (chunk_facts ly S rd k M (Hincl k ltac:(destruct Hk as [->|Hk]; [left; reflexivity | right; exact Hk]))) as (_ & _ & _ & _ & X5 & _ & X7 & X8 & _).
pose proof (req_size_bounds (ck_req k) ltac:(lia)). lia.
- destruct Hk as [->|Hk].
+ exfalso. apply Bool.andb_false_iff in E as [E|E]; [apply Z.leb_gt in E | apply Z.ltb_ge in E]; lia.
+ apply IH; [intros x Hx; apply Hincl; right; exact Hx | exact ND' | exact Hk | exact Hg].
Qed.
Lemma hull_inside : forall lo hi x n s, lo mod 64 = 0 -> hi mod 64 = 0 -> 0 <= lo -> lo <= x -> x + n <= hi -> 1 <= n ->
shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 ->
exists g, g mod 8 = 0 /\ lo <= g < hi /\ s = shadow_addr g.
Proof.
intros lo hi x n s Hlo Hhi Hlo0 Hx Hn Hn1 Hs. unfold shadow_addr, SHADOW_OFF in *.
apply Z.mod_divide in Hlo as [qlo Hqlo]; [|lia]. apply Z.mod_divide in Hhi as [qhi Hqhi]; [|lia].
exists ((s - 2147450880) * 8).
assert (D1 : (2147450880 + x / 8) / 8 = 268431360 + x / 8 / 8).
{ replace (2147450880 + x / 8) with (x / 8 + 268431360 * 8) by lia. rewrite Z.div_add by lia. lia. }
assert (D2 : (2147450880 + (x + n - 1) / 8) / 8 = 268431360 + (x + n - 1) / 8 / 8).
{ replace (2147450880 + (x + n - 1) / 8) with ((x + n - 1) / 8 + 268431360 * 8) by lia. rewrite Z.div_add by lia. lia. }
rewrite D1, D2 in Hs. rewrite !Z.div_div in Hs by lia. change (8 * 8) with 64 in Hs.
assert (L1 : qlo <= x / 64). { apply Z.div_le_lower_bound; lia. }
assert (L2 : (x + n - 1) / 64 < qhi). { apply Z.div_lt_upper_bound; lia. }
splits.
- apply Z_mod_mult.
- lia.
- lia.
- rewrite Z.div_mul by lia. lia.
Qed.
Theorem AR_shadow_law_ok : AR_shadow_law segs B.
Proof.
intros ly S W mem md p n (M & L & _) Hin. apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hr). subst p n.
pose proof (am_shadow _ _ _ _ M) as SH. pose proof (am_layout _ _ _ _ M) as LO. pose proof (am_wf _ _ _ _ M) as WF.
pose proof (chunk_facts ly S _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG). rewrite G4.
pose proof (proj1 G1) as G1lo.
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
assert (RNG : exists lo len, In (lo, len) (fa_poison_ranges ly S) /\ lo mod 64 = 0 /\ len mod 64 = 0 /\ 0 <= lo /\
lo <= ck_base B ly k /\ ck_base B ly k + ck_extent k <= lo + len).
{ destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal).
pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wr_mapped_al _ _ _ _ _ _ (wf_classes _ _ _ _ _ WF (prim_class o) ltac:(lia))) as MA.
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
pose proof (wf_chunks_nodup _ _ _ _ _ WF) as ND.
split.
-
unfold block_shadow. splits; [|lia|].
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in G3 as [q Hq]; [|lia]. apply Z.mod_divide in G6 as [q' Hq']; [|lia]. exists (2 * q + 2 * q'). lia. }
intros i Hi.
assert (I8 : 8 * ((req_size (ck_req k) + 7) / 8) <= req_size (ck_req k) + 7) by (apply Z.mul_div_le; lia).
set (g := ck_base B ly k + ck_rz k + 8 * i).
assert (Eg : shadow_of_addr SHADOW_OFF (ck_base B ly k + ck_rz k) + i = shadow_addr g).
{ unfold shadow_of_addr, shadow_addr. subst g.
apply Z.mod_divide in G3 as [q Hq]; [|lia]. apply Z.mod_divide in G6 as [q' Hq']; [|lia].
replace (ck_base B ly k + ck_rz k) with ((2 * q + 2 * q') * 8) by lia.
replace ((2 * q + 2 * q') * 8 + 8 * i) with ((2 * q + 2 * q' + i) * 8) by lia. rewrite !Z.div_mul by lia. lia. }
rewrite Eg. apply SH.
{ subst g. apply Z.mod_divide; [lia|]. apply Z.mod_divide in G3 as [q Hq]; [|lia]. apply Z.mod_divide in G6 as [q' Hq']; [|lia]. exists (2 * q + 2 * q' + i). lia. }
unfold ashadow. rewrite (find_chunk_at_hit ly S _ (st_chunks S) k g M ltac:(intros x Hx; exact Hx) ND Hk) by (subst g; lia).
f_equal. unfold chunk_granule. rewrite Hst.
replace ((g - ck_base B ly k) / 8) with (ck_rz k / 8 + i).
2:{ subst g. replace (ck_base B ly k + ck_rz k + 8 * i - ck_base B ly k) with (ck_rz k + i * 8) by lia. rewrite Z.div_add by lia. lia. }
unfold ck_n.
destruct (Z.ltb_spec (ck_rz k / 8 + i) (ck_rz k / 8)); [lia|].
destruct (Z.ltb_spec i (req_size (ck_req k) / 8)) as [Hlt|Hge].
+ replace (ck_rz k / 8 + i <? ck_rz k / 8 + req_size (ck_req k) / 8) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
+ replace (ck_rz k / 8 + i <? ck_rz k / 8 + req_size (ck_req k) / 8) with false by (symmetry; apply Z.ltb_ge; lia).
pose proof (Z.div_mod (req_size (ck_req k)) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (req_size (ck_req k)) 8 ltac:(lia)) as MB.
assert (i = req_size (ck_req k) / 8) as ->.
{ assert ((req_size (ck_req k) + 7) / 8 < req_size (ck_req k) / 8 + 2); [|lia].
apply Z.div_lt_upper_bound; [lia|]. lia. }
rewrite Z.eqb_refl. destruct (Z.eqb_spec (req_size (ck_req k) mod 8) 0) as [E0|NE]; cbn [andb negb]; [|reflexivity].
exfalso. assert ((req_size (ck_req k) + 7) / 8 < req_size (ck_req k) / 8 + 1); [|lia]. apply Z.div_lt_upper_bound; [lia|]. lia.
-
intros sa Hs.
destruct (hull_inside lo (lo + len) (ck_base B ly k + ck_rz k) (req_size (ck_req k)) sa Rlo ltac:(rewrite Z.add_mod, Rlo, Rlen by lia; reflexivity) Rlo0
ltac:(lia) ltac:(lia) ltac:(lia) Hs) as (g & Hg8 & Hgr & ->).
destruct (ashadow_total ly S g lo len RIn ltac:(lia)) as [v Hv]. rewrite (SH g v Hg8 Hv). discriminate.
Qed.
End m.
End j.
