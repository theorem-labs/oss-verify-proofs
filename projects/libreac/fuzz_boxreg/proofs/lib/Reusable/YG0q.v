(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG0q.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := let H := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Ltac show := match goal with |- ?g => idtac g end.
Section s.
Variable segs : list Segment.
Variable B : asyms.
Definition owned_range (ly : alayout) (S : astate) (lo len : Z) : Prop :=
forall a, lo <= a < lo + len -> aowned B ly S a.
Lemma nc_img : forall ly S rd a, ARm B ly S rd -> in_zr a (ly_img ly) -> ~ aclient_byte B ly S a.
Proof. intros ly S rd a M Ha C. exact (client_byte_not_img B ly S rd a M C Ha). Qed.
Lemma nc_static : forall ly S rd a, ARm B ly S rd -> Exists (in_zr a) (as_owned_static B ++ as_zero_shadow B) -> ~ aclient_byte B ly S a.
Proof.
intros ly S rd a M H. eapply nc_img; [exact M|]. apply Exists_exists in H as (r & Hr & [H1 H2]).
pose proof (proj1 (Forall_forall _ _) (am_static_img _ _ _ _ M) r Hr) as [S1 S2]. unfold in_zr. lia.
Qed.
Lemma nc_app : forall ly S rd a, ARm B ly S rd -> app_addr a ->
(forall k, In k (st_chunks S) -> ck_state k = CAllocated -> ~ (ck_base B ly k + ck_rz k <= a < ck_base B ly k + ck_rz k + req_size (ck_req k))) ->
~ (ly_F ly + kFakeFramesOff <= a < ly_F ly + kFakeStackSize) ->
~ aclient_byte B ly S a.
Proof.
intros ly S rd a M Ha NB NF [(k & Hk & Hst & Hr)|(cp & Hcp & [Hr|Hr])].
- pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & _ & G4 & _). rewrite G4 in Hr. unfold ck_n in Hr. exact (NB k Hk Hst Hr).
- destruct cp as [cid pos]. cbn [fst snd] in Hr. unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr.
pose proof (frame_facts B ly S rd cid pos M Hcp) as (C1 & _ & _ & _ & _ & P1 & P2 & _). pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)). lia.
- destruct cp as [cid pos]. cbn [fst snd] in Hr. unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr.
pose proof (frame_facts B ly S rd cid pos M Hcp) as (C1 & _ & F1 & F2 & _ & P1 & P2 & P3 & P4 & _). pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)).
ceil; unfold app_addr, in_app, kFakeFramesOff, kFakeStackSize, ASAN_CEIL, kHighMemBeg, kLowShadowBeg in *.
pose proof (shadow_range_below (ly_F ly + fs_frame_off cid pos) (fs_frame_bytes cid) ltac:(lia) ltac:(lia) ltac:(unfold kHighMemEnd; lia)) as SB.
pose proof (shadow_addr_bounds (ly_F ly + fs_frame_off cid pos) ltac:(lia)) as [SB0 _].
unfold kHighMemBeg, SHADOW_OFF in SB, SB0. lia.
Qed.
Lemma nc_high : forall ly S rd a, ARm B ly S rd -> kHighMemBeg <= a < ASAN_CEIL ->
(forall k, In k (st_chunks S) -> ck_state k = CAllocated -> ~ (ck_base B ly k + ck_rz k <= a < ck_base B ly k + ck_rz k + req_size (ck_req k))) ->
~ (ly_F ly + kFakeFramesOff <= a < ly_F ly + kFakeStackSize) ->
~ aclient_byte B ly S a.
Proof. intros ly S rd a M Ha. apply (nc_app ly S rd a M). unfold app_addr, kHighMemBeg in *. lia. Qed.
Lemma nc_shadow : forall ly S rd a lo len, ARm B ly S rd -> lo mod 8 = 0 -> 0 <= lo -> lo + len <= kHighMemEnd ->
zdisjoint (lo, len) (ly_F ly, kFakeStackSize) ->
shadow_addr lo <= a < shadow_addr lo + (len + 7) / 8 -> ~ aclient_byte B ly S a.
Proof.
intros ly S rd a lo len M Hlo8 Hlo0 Hhi D Ha [(k & Hk & Hst & Hr)|(cp & Hcp & [Hr|Hr])].
- pose proof (chunk_facts B ly S rd k M Hk) as (G1 & _ & _ & G4 & G5 & _ & _ & G8 & _). rewrite G4 in Hr.
unfold in_app, kLowShadowBeg, ck_n in G1, Hr.
pose proof (shadow_range_below lo (len + 7) Hlo0 ltac:(lia)) as SB. unfold kHighMemBeg, kHighMemEnd in *.
assert ((len + 7) / 8 <= (len + 7) / 8) by lia.
pose proof (shadow_addr_bounds lo Hlo0) as [SB0 _]. unfold SHADOW_OFF in SB0.
assert (shadow_addr lo + (len + 7) / 8 <= 17594333495296); [|lia].
unfold shadow_addr, SHADOW_OFF in *.
assert (L : (lo + len + 7) / 8 <= 140737488355335 / 8) by (apply Z.div_le_mono; lia). change (140737488355335 / 8) with 17592186044416 in L.
assert (lo / 8 + (len + 7) / 8 <= (lo + len + 7) / 8); [|lia].
apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le lo 8 ltac:(lia)). pose proof (Z.mul_div_le (len + 7) 8 ltac:(lia)). lia.
- destruct cp as [cid pos]. cbn [fst snd] in Hr. unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr.
pose proof (frame_facts B ly S rd cid pos M Hcp) as (C1 & _ & F1 & _ & _ & P1 & P2 & _). pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)).
ceil; unfold in_app, kLowShadowBeg, ASAN_CEIL, kFakeFramesOff, kFakeStackSize, kHighMemBeg, kHighMemEnd, shadow_addr, SHADOW_OFF in *.
assert (L : (lo + len + 7) / 8 <= 140737488355335 / 8) by (apply Z.div_le_mono; lia). change (140737488355335 / 8) with 17592186044416 in L.
assert (lo / 8 + (len + 7) / 8 <= (lo + len + 7) / 8); [|lia].
apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le lo 8 ltac:(lia)). pose proof (Z.mul_div_le (len + 7) 8 ltac:(lia)). lia.
-
destruct cp as [cid pos]. cbn [fst snd] in Hr. unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr.
pose proof (frame_facts B ly S rd cid pos M Hcp) as (C1 & _ & F1 & F2 & FA & P1 & P2 & P3 & P4 & P5 & _). pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)).
set (f := ly_F ly + fs_frame_off cid pos) in *.
assert (F8 : f mod 8 = 0).
{ subst f. unfold page_aligned in FA. apply Z.mod_divide; [lia|]. apply Z.mod_divide in FA as [q Hq]; [|lia]. apply Z.mod_divide in P3 as [q' Hq']; [|lia]. exists (q * 512 + q' * 8). lia. }
apply Z.mod_divide in F8 as [qf Hqf]; [|lia]. apply Z.mod_divide in Hlo8 as [ql Hql]; [|lia]. apply Z.mod_divide in P5 as [qb Hqb]; [|lia].
unfold shadow_addr, SHADOW_OFF, zdisjoint, kFakeFramesOff, kFakeStackSize in *. cbn [fst snd] in D.
rewrite Hqf, Hql, Hqb in *. rewrite !Z.div_mul in Hr by lia. rewrite Z.div_mul in Ha by lia.
replace (qb * 64 / 8) with (qb * 8) in Hr by (symmetry; replace (qb * 64) with (qb * 8 * 8) by lia; apply Z.div_mul; lia).
assert (8 * ((len + 7) / 8) <= len + 7) by (apply Z.mul_div_le; lia).
assert (0 <= (len + 7) / 8) by (apply Z.div_pos; lia).
destruct D as [D|D]; nia.
Qed.
Lemma user_in_extent : forall ly S rd k a, ARm B ly S rd -> In k (st_chunks S) ->
ck_base B ly k + ck_rz k <= a < ck_base B ly k + ck_rz k + req_size (ck_req k) -> ck_base B ly k <= a < ck_base B ly k + ck_extent k.
Proof. intros ly S rd k a M Hk Ha. pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & _ & _ & G5 & _ & _ & G8 & _). lia. Qed.
Lemma extent_zone : forall ly S rd k, ARm B ly S rd -> In k (st_chunks S) ->
(ly_prim ly <= ck_base B ly k /\ ck_base B ly k + ck_extent k <= ly_prim ly + kPrimResvSize) \/
(exists m len, In (m, len) (sec_extents ly S) /\ m + kPage = ck_base B ly k /\ len = ck_extent k + kPage).
Proof.
intros ly S rd k M Hk. pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & _ & _ & _ & _ & _ & _ & GG).
destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG].
- left. cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal).
pose proof (region_in_prim ly (prim_class o) (am_layout _ _ _ _ M) ltac:(lia)) as (R1 & R2 & _). lia.
- right. destruct GG as (_ & _ & Gbase & Gext & Gin & _). exists (ly_sec ly r), (sec_map_size (ck_req k)). unfold kPage in *. splits; [exact Gin | lia | lia].
Qed.
Lemma own_static : forall ly S rd a, ARm B ly S rd -> Exists (in_zr a) (as_owned_static B) -> aowned B ly S a.
Proof.
intros ly S rd a M H. split; [left; exact H|]. eapply nc_static; [exact M|].
apply Exists_exists in H as (r & Hr & Ha). apply Exists_exists. exists r. split; [apply in_app_iff; left; exact Hr | exact Ha].
Qed.
Lemma own_area : forall ly S rd r a, ARm B ly S rd -> In r (asyms_areas B) -> fst r <= a < fst r + snd r -> aowned B ly S a.
Proof.
intros ly S rd r a M Hr Ha. eapply own_static; [exact M|].
pose proof (proj1 (Forall_forall _ _) (aso_cover _ (am_syms _ _ _ _ M)) r Hr) as X. apply Exists_exists in X as (r' & Hr' & [S1 S2]).
apply Exists_exists. exists r'. split; [exact Hr'|]. unfold in_zr. lia.
Qed.
Lemma own_ext : forall ly S rd a, ARm B ly S rd ->
(Exists (in_zr a) (owned_extents ly) \/ Exists (in_zr a) (sec_extents ly S)) ->
(forall k, In k (st_chunks S) -> ck_state k = CAllocated -> ~ (ck_base B ly k + ck_rz k <= a < ck_base B ly k + ck_rz k + req_size (ck_req k))) ->
~ (ly_F ly + kFakeFramesOff <= a < ly_F ly + kFakeStackSize) -> aowned B ly S a.
Proof.
intros ly S rd a M Z NB NF.
assert (AA : app_addr a).
{ destruct Z as [Z|Z]; [exact (proj1 (owned_extents_bound ly a (am_layout _ _ _ _ M) Z)) | exact (proj1 (owned_sec_bound B ly S rd a M Z))]. }
split; [|eapply nc_app; eassumption].
destruct Z as [Z|Z]; [right; left; exact Z | right; right; right; left; exact Z].
Qed.
Lemma own_high : forall ly S rd a, ARm B ly S rd -> kHighMemBeg <= a ->
(Exists (in_zr a) (owned_extents ly) \/ Exists (in_zr a) (sec_extents ly S)) ->
(forall k, In k (st_chunks S) -> ck_state k = CAllocated -> ~ (ck_base B ly k + ck_rz k <= a < ck_base B ly k + ck_rz k + req_size (ck_req k))) ->
~ (ly_F ly + kFakeFramesOff <= a < ly_F ly + kFakeStackSize) -> aowned B ly S a.
Proof. intros ly S rd a M _ Z NB NF. exact (own_ext ly S rd a M Z NB NF). Qed.
Lemma own_core : forall ly S rd e a, ARm B ly S rd -> In e (core_extents ly) -> fst e <= a < fst e + snd e -> aowned B ly S a.
Proof.
intros ly S rd e a M He Ha. pose proof (am_layout _ _ _ _ M) as LO. pose proof (am_placed _ _ _ _ M) as [PL PD].
assert (HeO : In e (owned_extents ly)) by (unfold core_extents in He; unfold owned_extents; cbn in He |- *; tauto).
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) e HeO) as H1.
assert (DP : zdisjoint (ly_prim ly, kPrimResvSize) e /\ zdisjoint e (ly_F ly, kFakeStackSize)).
{ pose proof (lo_disj _ LO) as D. unfold static_extents, owned_extents in D. cbn [pairwise app] in D.
destruct D as (D0 & D1 & D2 & D3 & D4 & D5 & D6 & _).
repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H; clear H; subst end.
unfold core_extents in He. cbn in He.
destruct He as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; (split; [assumption | first [assumption | apply zdisjoint_sym; assumption]]). }
destruct DP as [DP DF].
assert (NF : ~ (ly_F ly + kFakeFramesOff <= a < ly_F ly + kFakeStackSize)).
{ unfold zdisjoint, kFakeFramesOff in *. cbn [fst snd] in *. lia. }
eapply own_ext; [exact M | left; apply Exists_exists; exists e; split; [exact HeO | exact Ha] | | exact NF].
intros k Hk Hst Hr. pose proof (user_in_extent ly S rd k a M Hk Hr) as HE.
destruct (extent_zone ly S rd k M Hk) as [[X1 X2]|(m & len & Hin & X1 & X2)].
- unfold zdisjoint in DP. cbn [fst snd] in DP. lia.
- pose proof (pairwise_In zdisjoint _ (m, len) e (sec_extents ly S) (static_extents ly) eq_refl PD Hin ltac:(unfold static_extents; apply in_app_iff; left; exact HeO)) as D.
unfold zdisjoint, kPage in *. cbn [fst snd] in D. lia.
Qed.
Lemma secmaps_disjoint : forall ly S rd k1 k2 r1 o1 r2 o2, ARm B ly S rd -> In k1 (st_chunks S) -> In k2 (st_chunks S) ->
ck_beg k1 = PSec r1 o1 -> ck_beg k2 = PSec r2 o2 -> ck_beg k1 <> ck_beg k2 ->
zdisjoint (ly_sec ly r1, sec_map_size (ck_req k1)) (ly_sec ly r2, sec_map_size (ck_req k2)).
Proof.
intros ly S rd k1 k2 r1 o1 r2 o2 M H1 H2 E1 E2 Hne. pose proof (am_wf _ _ _ _ M) as WF. pose proof (proj2 (am_placed _ _ _ _ M)) as PD.
destruct (In_split_beg _ _ H1 (wf_chunks_nodup _ _ _ _ _ WF)) as (l1 & l2 & E & N1 & N2).
assert (E1in : In (ly_sec ly r1, sec_map_size (ck_req k1)) (sec_extents ly (set_chunks [k1] S))).
{ unfold sec_extents. cbn. rewrite E1. left. reflexivity. }
assert (H2' : In k2 l1 \/ In k2 l2).
{ rewrite E in H2. apply in_app_iff in H2 as [?|[E12|?]]; [left; assumption | exfalso; subst k2; exact (Hne eq_refl) | right; assumption]. }
pose proof (sec_extents_split ly S l1 k1 l2 E) as SE. rewrite SE in PD.
destruct H2' as [H2'|H2'].
- apply zdisjoint_sym. rewrite <- !app_assoc in PD.
eapply (pairwise_In zdisjoint _ _ _ (sec_extents ly (set_chunks l1 S))); [reflexivity | exact PD | | apply in_app_iff; left; exact E1in].
unfold sec_extents. apply in_flat_map. exists k2. split; [exact H2'|]. rewrite E2. left. reflexivity.
- rewrite <- !app_assoc in PD. rewrite (app_assoc (sec_extents ly (set_chunks l1 S))) in PD.
eapply (pairwise_In zdisjoint _ _ _ (sec_extents ly (set_chunks l1 S) ++ sec_extents ly (set_chunks [k1] S))); [reflexivity | exact PD | apply in_app_iff; right; exact E1in |].
apply in_app_iff. left. unfold sec_extents. apply in_flat_map. exists k2. split; [exact H2'|]. rewrite E2. left. reflexivity.
Qed.
Lemma prim_vs_secmap : forall ly S rd k o e, ARm B ly S rd -> In k (st_chunks S) -> ck_beg k = PPrim o -> In e (sec_extents ly S) ->
zdisjoint (ck_base B ly k, ck_extent k) e.
Proof.
intros ly S rd k o e M Hk Hb He. pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & _ & _ & _ & _ & _ & _ & GG). rewrite Hb in GG.
cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal).
pose proof (region_in_prim ly (prim_class o) (am_layout _ _ _ _ M) ltac:(lia)) as (R1 & R2 & _).
pose proof (pairwise_In zdisjoint _ e (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) He
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
unfold zdisjoint in D |- *. cbn [fst snd] in D |- *. lia.
Qed.
Lemma own_prim_nonuser : forall ly S rd a, ARm B ly S rd -> ly_prim ly <= a < ly_prim ly + kPrimResvSize ->
(forall k, In k (st_chunks S) -> ck_state k = CAllocated -> ~ (ck_base B ly k + ck_rz k <= a < ck_base B ly k + ck_rz k + req_size (ck_req k))) ->
aowned B ly S a.
Proof.
intros ly S rd a M Ha NB. pose proof (am_layout _ _ _ _ M) as LO.
pose proof (lo_high _ LO) as [H1 H2].
pose proof (pairwise_In zdisjoint (static_extents ly) (ly_prim ly, kPrimResvSize) (ly_F ly, kFakeStackSize) [_] _
ltac:(unfold static_extents, owned_extents; reflexivity) (lo_disj _ LO) (or_introl eq_refl) ltac:(cbn; tauto)) as D.
eapply own_high; [exact M | lia | left; apply Exists_exists; exists (ly_prim ly, kPrimResvSize); split; [unfold owned_extents; cbn; tauto | unfold in_zr; cbn; lia] | exact NB |].
unfold zdisjoint, kFakeFramesOff in *. cbn [fst snd] in D. lia.
Qed.
Lemma own_meta : forall ly S rd k a, ARm B ly S rd -> In k (st_chunks S) ->
ck_base B ly k - (match ck_beg k with PSec _ _ => kPage | _ => 0 end) <= a < ck_base B ly k + ck_rz k -> aowned B ly S a.
Proof.
intros ly S rd k a M Hk Ha. pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
assert (NB : forall k', In k' (st_chunks S) -> ck_state k' = CAllocated ->
~ (ck_base B ly k' + ck_rz k' <= a < ck_base B ly k' + ck_rz k' + req_size (ck_req k'))).
{ intros k' Hk' Hst' Hr. pose proof (user_in_extent ly S rd k' a M Hk' Hr) as HE.
destruct (sptr_eqb (ck_beg k') (ck_beg k)) eqn:Eq.
- apply sptr_eqb_spec in Eq. destruct (In_split_beg _ _ Hk (wf_chunks_nodup _ _ _ _ _ (am_wf _ _ _ _ M))) as (l1 & l2 & E & N1 & N2).
assert (k' = k).
{ rewrite E in Hk'. apply in_app_iff in Hk' as [X|[<-|X]]; [exfalso; apply N1 | reflexivity | exfalso; apply N2]; rewrite <- Eq; apply in_map_iff; exists k'; auto. }
subst k'. destruct (ck_beg k); lia.
- assert (Hne : ck_beg k' <> ck_beg k) by (intros E'; apply sptr_eqb_spec in E'; congruence).
destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try solve [destruct GG].
+ pose proof (chunks_disjoint B ly S rd k' k M Hk' Hk ltac:(rewrite Eb; exact Hne)) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
+ destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (chunk_facts B ly S rd k' M Hk') as (_ & _ & _ & _ & _ & _ & _ & _ & GG').
destruct (ck_beg k') as [|o'|r' o'|c' p'] eqn:Eb'; try solve [destruct GG'].
* pose proof (prim_vs_secmap ly S rd k' o' _ M Hk' Eb' Gin) as D. unfold zdisjoint in D. cbn [fst snd] in D. unfold kPage in *. lia.
* destruct GG' as (-> & _ & Gbase' & Gext' & _).
pose proof (secmaps_disjoint ly S rd k' k r' kPage r kPage M Hk' Hk Eb' Eb ltac:(rewrite ?Eb', ?Eb in Hne; rewrite ?Eb', ?Eb; exact Hne)) as D.
unfold zdisjoint, kPage in *. cbn [fst snd] in D. lia. }
destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal).
pose proof (region_in_prim ly (prim_class o) (am_layout _ _ _ _ M) ltac:(lia)) as (R1 & R2 & _).
eapply own_prim_nonuser; [exact M | lia | exact NB].
- destruct GG as (-> & _ & Gbase & Gext & Gin & Gal & _).
pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) _ Gin) as (_ & [I1 I2] & _). cbn [fst snd] in I1, I2.
pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req k)) (ly_F ly, kFakeStackSize) _ (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) Gin
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
eapply own_ext; [exact M | right; apply Exists_exists; exists (ly_sec ly r, sec_map_size (ck_req k)); split; [exact Gin | unfold in_zr, kPage in *; cbn; lia] | exact NB |].
unfold zdisjoint, kFakeFramesOff, kPage in *. cbn [fst snd] in D. lia.
Qed.
Lemma own_batch : forall ly S rd b a, ARm B ly S rd -> In b (all_batches S) ->
ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> aowned B ly S a.
Proof.
intros ly S rd b a M Hb Ha. pose proof (am_wf _ _ _ _ M) as WF. pose proof (am_layout _ _ _ _ M) as LO.
pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; auto).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wr_nodup _ _ _ _ _ _ CL) as ND. rewrite app_assoc in ND. apply NoDup_app_iff in ND as (_ & ND & _). apply NoDup_app_iff in ND as (_ & _ & NDx).
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL. pose proof (mapped_user_bound (as_universe B) 0 0 0 S kBatchClass WF ltac:(unfold kBatchClass; lia)) as MB.
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5).
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2.
unfold kBatchBytes, kUserMapSize, EV_MAX in *.
assert (BX : ly_space ly + b_self b = region_base ly kBatchClass + x) by (unfold region_base; subst x; lia).
eapply own_prim_nonuser; [exact M | lia |].
intros k Hk Hst Hr. pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & Gxm & Gxs & Gal).
destruct (Z.eq_dec (prim_class o) kBatchClass) as [Ec|Hc].
+ pose proof (In_chunk_offs S k o Hk Eb) as IK. rewrite Ec in *. rewrite CS in *. set (xk := o - region_off kBatchClass) in *.
assert (xk <> x). { intros E. apply (NDx xk); [exact IK | rewrite E; exact INB]. }
apply Z.mod_divide in Gxm as [q1 Hq1]; [|lia]. apply Z.mod_divide in X2 as [q2 Hq2]; [|lia].
assert (q1 <> q2) by (intros E; subst; lia). nia.
+ pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1' & R2' & _).
unfold region_base in *. rewrite !region_off_eq in * by (unfold kBatchClass; lia). unfold kBatchClass in *.
destruct (Z.lt_ge_cases (prim_class o) 24).
* pose proof (Z.mul_le_mono_nonneg_r (prim_class o + 1) 24 (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
* pose proof (Z.mul_le_mono_nonneg_r (24 + 1) (prim_class o) (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req k)) (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) Gin
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
unfold zdisjoint, kPage in *. cbn [fst snd] in D. lia.
Qed.
Lemma own_F_low : forall ly S rd a, ARm B ly S rd -> ly_F ly <= a < ly_F ly + kFakeFramesOff -> aowned B ly S a.
Proof.
intros ly S rd a M Ha. pose proof (am_layout _ _ _ _ M) as LO.
unfold kFakeFramesOff, kFakeStackSize in *.
eapply own_ext; [exact M | left; apply Exists_exists; exists (ly_F ly, kFakeStackSize); split; [unfold owned_extents; cbn; tauto | unfold in_zr, kFakeStackSize; cbn; lia] | | unfold kFakeFramesOff; lia].
intros k Hk Hst Hr. pose proof (user_in_extent ly S rd k a M Hk Hr) as HE. pose proof (chunk_vs_F B ly S rd k M Hk) as D.
unfold zdisjoint, kFakeStackSize in D. cbn [fst snd] in D. lia.
Qed.
Lemma own_rinfo : forall ly S rd a, ARm B ly S rd -> ly_space ly + kRegionInfoOff <= a < ly_space ly + kRegionInfoOff + 4096 -> aowned B ly S a.
Proof.
intros ly S rd a M Ha. pose proof (am_layout _ _ _ _ M) as LO. pose proof (lo_space_in _ LO) as [S1 S2]. unfold kRegionInfoOff, kSpaceSize in *.
eapply own_prim_nonuser; [exact M | lia |].
intros k Hk Hst Hr. pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & Gxm & Gxs & Gal).
unfold region_base in *. rewrite !region_off_eq in * by lia.
pose proof (Z.mul_le_mono_nonneg_r (prim_class o + 1) 32 (2 ^ 32) ltac:(lia) ltac:(lia)). change (32 * 2 ^ 32) with (2 ^ 37) in H. lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req k)) (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) Gin
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
unfold zdisjoint, kPage, kPrimResvSize in *. cbn [fst snd] in D. lia.
Qed.
Lemma own_fa : forall ly S rd c a, ARm B ly S rd -> 1 <= c <= 31 -> fa_base ly c <= a < fa_base ly c + kFreeArrayMax -> aowned B ly S a.
Proof.
intros ly S rd c a M Hc Ha. pose proof (am_layout _ _ _ _ M) as LO.
pose proof (region_in_prim ly c LO Hc) as (R1 & R2 & R3 & R4 & R5). unfold fa_base, kFreeArrayOffset, kFreeArrayMax in *.
assert (E32 : region_base ly c = ly_space ly + region_off c) by reflexivity.
eapply own_prim_nonuser; [exact M | lia |].
intros k Hk Hst Hr. pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
destruct (ck_beg k) as [|o|r o|c' p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & Gxm & Gxs & Gal).
destruct (Z.eq_dec (prim_class o) c) as [Ec|Hne].
+ rewrite Ec in *. unfold region_base in *. lia.
+ pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1' & R2' & _).
unfold region_base in *. rewrite !region_off_eq in * by lia.
destruct (Z.lt_ge_cases (prim_class o) c).
* pose proof (Z.mul_le_mono_nonneg_r (prim_class o + 1) c (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
* pose proof (Z.mul_le_mono_nonneg_r (c + 1) (prim_class o) (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req k)) (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) Gin
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
unfold zdisjoint, kPage in *. cbn [fst snd] in D. lia.
Qed.
Lemma own_shadow : forall ly S rd lo len a, ARm B ly S rd ->
In (lo, len) (static_extents ly ++ sec_extents ly S ++ zero_shadow_ranges B ly ++ as_owned_static B ++ [hm_zone; lm_zone]) -> lo mod 8 = 0 ->
zdisjoint (lo, len) (ly_F ly, kFakeStackSize) ->
shadow_addr lo <= a < shadow_addr lo + (len + 7) / 8 -> aowned B ly S a.
Proof.
intros ly S rd lo len a M Hin Hlo D Ha.
pose proof (proj1 (Forall_forall _ _) (owned_shadow_ranges B ly S rd M) _ Hin) as (K1 & K2 & K3). cbn [fst snd] in K1, K2, K3.
split.
- right. right. right. right. apply Exists_exists. exists (lo, len). split; [exact Hin|]. unfold in_zr. cbn [fst snd]. exact Ha.
- eapply nc_shadow; [exact M | exact Hlo | exact K1 | exact K3 | exact D | exact Ha].
Qed.
Lemma shadow_addr_in : forall lo len g, lo mod 8 = 0 -> 0 <= lo -> lo <= g < lo + len ->
shadow_addr lo <= shadow_addr g < shadow_addr lo + (len + 7) / 8.
Proof.
intros lo len g Hlo Hlo0 Hg. unfold shadow_addr. apply Z.mod_divide in Hlo as [q Hq]; [|lia]. subst lo.
rewrite Z.div_mul by lia.
assert (q <= g / 8) by (apply Z.div_le_lower_bound; lia).
assert (g / 8 < q + (len + 7) / 8); [|lia].
assert ((g - q * 8) / 8 < (len + 7) / 8 + 0); [|].
{ apply (Z.lt_le_trans _ ((len - 1) / 8 + 1)); [|].
- assert ((g - q * 8) / 8 <= (len - 1) / 8) by (apply Z.div_le_mono; lia). lia.
- replace (len + 7) with (len - 1 + 1 * 8) by lia. rewrite Z.div_add by lia. lia. }
replace g with ((g - q * 8) + q * 8) at 1 by lia. rewrite Z.div_add by lia. lia.
Qed.
Lemma own_shadow_prim : forall ly S rd g, ARm B ly S rd -> ly_prim ly <= g < ly_prim ly + kPrimResvSize -> aowned B ly S (shadow_addr g).
Proof.
intros ly S rd g M Hg. pose proof (am_layout _ _ _ _ M) as LO.
pose proof (lo_high _ LO) as [H1 H2].
pose proof (lo_prim_al _ LO) as PA. unfold page_aligned in PA.
assert (P8 : ly_prim ly mod 8 = 0). { apply Z.mod_divide; [lia|]. apply Z.mod_divide in PA as [q Hq]; [|lia]. exists (q * 512). lia. }
eapply (own_shadow ly S rd (ly_prim ly) kPrimResvSize); [exact M | | exact P8 | |].
- apply in_app_iff. left. unfold static_extents, owned_extents. cbn. tauto.
- eapply (pairwise_In zdisjoint (static_extents ly) _ _ [_] _); [unfold static_extents, owned_extents; reflexivity | exact (lo_disj _ LO) | left; reflexivity | cbn; tauto].
- apply shadow_addr_in; [exact P8 | unfold kHighMemBeg in H1; lia | exact Hg].
Qed.
Lemma own_shadow_sec : forall ly S rd m len g, ARm B ly S rd -> In (m, len) (sec_extents ly S) -> m <= g < m + len -> aowned B ly S (shadow_addr g).
Proof.
intros ly S rd m len g M Hin Hg. pose proof (am_placed _ _ _ _ M) as [PL PD].
pose proof (proj1 (Forall_forall _ _) PL _ Hin) as (PA & [I1 I2] & I3). cbn [fst snd] in PA, I1, I2, I3. unfold page_aligned in PA.
assert (P8 : m mod 8 = 0). { apply Z.mod_divide; [lia|]. apply Z.mod_divide in PA as [q Hq]; [|lia]. exists (q * 512). lia. }
eapply (own_shadow ly S rd m len); [exact M | | exact P8 | |].
- apply in_app_iff. right. apply in_app_iff. left. exact Hin.
- eapply (pairwise_In zdisjoint _ _ _ (sec_extents ly S) (static_extents ly)); [reflexivity | exact PD | exact Hin | unfold static_extents, owned_extents; cbn; tauto].
- apply shadow_addr_in; [exact P8 | unfold kHighMemBeg in I1; lia | exact Hg].
Qed.
Lemma own_shadow_zero : forall ly S rd r i, ARm B ly S rd -> In r (zero_shadow_ranges B ly) -> 0 <= i < snd r / 8 -> aowned B ly S (shadow_addr (fst r) + i).
Proof.
intros ly S rd [lo len] i M Hin Hi. cbn [fst snd] in *. pose proof (am_layout _ _ _ _ M) as LO.
assert (P8 : lo mod 8 = 0 /\ 0 <= lo /\ zdisjoint (lo, len) (ly_F ly, kFakeStackSize)).
{ unfold zero_shadow_ranges in Hin. destruct Hin as [E|Hin].
- injection E as <- <-. pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). unfold page_aligned in T5.
splits.
+ apply Z.mod_divide; [lia|]. apply Z.mod_divide in T5 as [q Hq]; [|lia]. exists (q * 512). lia.
+ unfold kHighMemBeg in T7. lia.
+ apply zdisjoint_sym. eapply (pairwise_In zdisjoint (static_extents ly) _ _ (owned_extents ly) [_; _]); [unfold static_extents; reflexivity | exact (lo_disj _ LO) | unfold owned_extents; cbn; tauto | left; reflexivity].
- pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (am_syms _ _ _ _ M)) _ Hin) as (Z1 & Z2 & Z3 & Z4 & Z5). cbn [fst snd] in *.
pose proof (proj1 (Forall_forall _ _) (am_static_img _ _ _ _ M) (lo, len) ltac:(apply in_app_iff; right; exact Hin)) as [I1 I2]. cbn [fst snd] in I1, I2.
pose proof (pairwise_In zdisjoint (static_extents ly) (ly_F ly, kFakeStackSize) (ly_img ly) (owned_extents ly) [_; _] eq_refl (lo_disj _ LO)
ltac:(unfold owned_extents; cbn; tauto) (or_intror (or_introl eq_refl))) as DF.
splits; [exact Z3 | exact Z1 |]. unfold zdisjoint in *. cbn [fst snd] in *. lia. }
destruct P8 as (P8 & P0 & D).
eapply (own_shadow ly S rd lo len); [exact M | apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact Hin | exact P8 | exact D |].
assert (len / 8 <= (len + 7) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
Lemma own_shadow_static : forall ly S rd r a, ARm B ly S rd -> In r (as_owned_static B) ->
shadow_addr (fst r) <= a < shadow_addr (fst r) + (snd r + 7) / 8 -> aowned B ly S a.
Proof.
intros ly S rd r a M Hin Ha. pose proof (proj1 (Forall_forall _ _) (aso_static _ (am_syms _ _ _ _ M)) r Hin) as (T1 & T2 & T3).
split.
- right. right. right. right. apply Exists_exists. exists r. split; [rewrite !in_app_iff; tauto | unfold in_zr; cbn [fst snd]; exact Ha].
-
pose proof (am_layout _ _ _ _ M) as LO. pose proof (lo_img _ LO) as (I0 & I1 & I2 & I3).
pose proof (proj1 (Forall_forall _ _) (am_static_img _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hin)) as [R1 R2].
pose proof (pairwise_In zdisjoint (static_extents ly) (ly_F ly, kFakeStackSize) (ly_img ly) (owned_extents ly) [_; _] eq_refl (lo_disj _ LO)
ltac:(unfold owned_extents; cbn; tauto) (or_intror (or_introl eq_refl))) as DF.
eapply (nc_shadow ly S rd a (fst (ly_img ly)) (snd (ly_img ly)) M).
+ rewrite I0. reflexivity.
+ rewrite I0. unfold kImgLo. lia.
+ unfold kImgLo, kImgEnd, kHighMemEnd in *. lia.
+ apply zdisjoint_sym. exact DF.
+ unfold shadow_addr, SHADOW_OFF in *. cbn [fst snd] in *.
pose proof (Z.div_le_mono (fst (ly_img ly)) (fst r) 8 ltac:(lia) ltac:(lia)).
assert ((fst r) / 8 + (snd r + 7) / 8 <= fst (ly_img ly) / 8 + (snd (ly_img ly) + 7) / 8); [|lia].
unfold page_aligned in I3. rewrite I0 in *. unfold kImgLo in *.
apply Z.mod_divide in I3 as [q Hq]; [|lia].
assert (X : (snd (ly_img ly) + 7) / 8 = q * 512) by (rewrite Hq; replace (q * 4096 + 7) with (7 + (q * 512) * 8) by lia; rewrite Z.div_add, Z.div_small by lia; lia).
rewrite X. change (65536 / 8) with 8192.
assert ((fst r) / 8 + (snd r + 7) / 8 <= (fst r + snd r + 7) / 8).
{ apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le (fst r) 8 ltac:(lia)). pose proof (Z.mul_div_le (snd r + 7) 8 ltac:(lia)). lia. }
assert ((fst r + snd r + 7) / 8 <= (65536 + q * 4096 + 7) / 8) by (apply Z.div_le_mono; lia).
replace ((65536 + q * 4096 + 7) / 8) with (8192 + q * 512) in * by (symmetry; replace (65536 + q * 4096 + 7) with (7 + (8192 + q * 512) * 8) by lia; rewrite Z.div_add, Z.div_small by lia; lia).
lia.
Qed.
Definition cell_bytes_owned (ly : alayout) (S : astate) (c : acell) : Prop :=
forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> aowned B ly S (aeval B ly (c_at c) + k).
Lemma cbo_of_range : forall ly S c lo len, owned_range ly S lo len ->
lo <= aeval B ly (c_at c) -> aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len -> cell_bytes_owned ly S c.
Proof. intros ly S c lo len OR H1 H2 k Hk. apply OR. lia. Qed.
Lemma Forall_cbo_of_range : forall ly S l lo len, owned_range ly S lo len ->
Forall (fun c => lo <= aeval B ly (c_at c) /\ aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len) l -> Forall (cell_bytes_owned ly S) l.
Proof. intros ly S l lo len OR H. eapply Forall_impl; [|exact H]. intros c [H1 H2]. eapply cbo_of_range; eauto. Qed.
Ltac fcons := apply Forall_cons; [cbn; lia|].
Lemma region_cells_owned : forall ly S rd c, ARm B ly S rd -> 1 <= c <= 31 -> Forall (cell_bytes_owned ly S) (region_cells S c).
Proof.
intros ly S rd c M Hc. apply (Forall_cbo_of_range ly S _ (ly_space ly + kRegionInfoOff) 4096); [intros a Ha; eapply own_rinfo; [exact M | exact Ha]|].
unfold region_cells, kRegionInfoOff. repeat fcons. apply Forall_nil.
Qed.
Lemma cache_cells_owned : forall ly S rd c, ARm B ly S rd -> 1 <= c <= 31 -> Forall (cell_bytes_owned ly S) (cache_cells S c).
Proof.
intros ly S rd c M Hc.
assert (OR : owned_range ly S (ly_T ly) kThreadObjSize).
{ intros a Ha. eapply (own_core ly S rd (ly_T ly, kThreadObjSize)); [exact M | unfold core_extents; cbn; tauto | exact Ha]. }
apply (Forall_cbo_of_range ly S _ (ly_T ly) kThreadObjSize OR).
pose proof (wf_classes _ _ _ _ _ (am_wf _ _ _ _ M) c Hc) as CL. pose proof (wr_cache _ _ _ _ _ _ CL) as WC. pose proof (class_ok c Hc) as (_ & _ & _ & K4 & _).
unfold cache_cells, t_cache, kThreadObjSize. destruct (st_cache_inited S).
- destruct WC as [PM PL]. repeat fcons. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i v] & <- & Hiv). cbn [fst snd c_at c_w z4 c4 aeval aoff].
apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. lia.
- repeat fcons. apply Forall_nil.
Qed.
Lemma chunk_cells_owned : forall ly S rd k, ARm B ly S rd -> In k (st_chunks S) -> Forall (cell_bytes_owned ly S) (chunk_cells k).
Proof.
intros ly S rd k M Hk. pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
assert (OR : owned_range ly S (ck_base B ly k) (ck_rz k)).
{ intros a Ha. eapply own_meta; [exact M | exact Hk |]. destruct (ck_beg k); unfold kPage; lia. }
apply (Forall_cbo_of_range ly S _ _ _ OR).
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
Lemma area_owned_range : forall ly S rd r, ARm B ly S rd -> In r (asyms_areas B) -> owned_range ly S (fst r) (snd r).
Proof. intros ly S rd r M Hr a Ha. eapply own_area; eassumption. Qed.
Lemma inst_owned_range : forall ly S rd, ARm B ly S rd -> owned_range ly S (as_inst B) 3632.
Proof. intros ly S rd M. apply (area_owned_range ly S rd (as_inst B, 3632) M). cbn. tauto. Qed.
Lemma sec_cells_owned : forall ly S rd, ARm B ly S rd -> Forall (cell_bytes_owned ly S) (sec_cells S).
Proof.
intros ly S rd M. pose proof (wf_secondary _ _ _ _ _ (am_wf _ _ _ _ M)) as X. destruct X as [Snd Sac Sal Sres Sral].
unfold sec_cells.
apply Forall_cons; [eapply cbo_of_range; [exact (inst_owned_range ly S rd M) | cbn; unfold o_sec_reserved; lia | cbn; unfold o_sec_reserved; lia]|].
apply Forall_cons; [eapply cbo_of_range; [exact (inst_owned_range ly S rd M) | cbn; unfold o_sec_n; lia | cbn; unfold o_sec_n; lia]|].
apply Forall_cons; [eapply cbo_of_range; [exact (inst_owned_range ly S rd M) | cbn; unfold o_sec_mutex; lia | cbn; unfold o_sec_mutex; lia]|].
apply Forall_app. split.
- apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
eapply cbo_of_range; [intros a Ha; eapply (own_core ly S rd (ly_Q ly, kPtrArrayResv)); [exact M | unfold core_extents; cbn; tauto | exact Ha] | cbn; lia |].
cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
- apply Forall_forall. intros c Hc. apply in_flat_map in Hc as (k & Hk & Hc).
pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg k) as [|o|r o|c' p] eqn:Eb; try solve [destruct Hc].
destruct GG as (-> & _ & Gbase & Gext & Gin & _).
assert (OR : owned_range ly S (ly_sec ly r) kPage).
{ intros a Ha. eapply own_meta; [exact M | exact Hk |]. rewrite Eb. unfold kPage in *. lia. }
unfold kPage in OR.
destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; (eapply cbo_of_range; [exact OR | cbn; lia | cbn; lia]).
Qed.
Lemma batch_cells_owned : forall ly S rd l, ARm B ly S rd -> incl l (all_batches S) -> Forall (cell_bytes_owned ly S) (batch_cells l).
Proof.
intros ly S rd l M. induction l as [|b t IH]; intros Hincl; [apply Forall_nil|]. cbn [batch_cells].
pose proof (wq_batches _ (wf_quarantine _ _ _ _ _ (am_wf _ _ _ _ M))) as BL.
pose proof (proj1 (Forall_forall _ _) BL b (Hincl b (or_introl eq_refl))) as [L1 L2]. unfold kBatchSlots in L2.
assert (OR : owned_range ly S (ly_space ly + b_self b) kBatchBytes) by (intros a Ha; eapply own_batch; [exact M | apply Hincl; left; reflexivity | exact Ha]).
unfold kBatchBytes in OR.
apply Forall_cons; [eapply cbo_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbo_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbo_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_app. split.
- apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i k] & <- & Hik). apply in_combine_l in Hik. apply in_seq in Hik.
eapply cbo_of_range; [exact OR | cbn; lia | cbn; lia].
- apply IH. intros x Hx. apply Hincl. right. exact Hx.
Qed.
Lemma quar_cells_owned : forall ly S rd, ARm B ly S rd -> Forall (cell_bytes_owned ly S) (quar_cells S).
Proof.
intros ly S rd M.
assert (ORT : owned_range ly S (ly_T ly) kThreadObjSize).
{ intros a Ha. eapply (own_core ly S rd (ly_T ly, kThreadObjSize)); [exact M | unfold core_extents; cbn; tauto | exact Ha]. }
pose proof (inst_owned_range ly S rd M) as ORI. unfold kThreadObjSize in ORT.
unfold quar_cells, qc_cells, o_q_cmutex, o_q_rmutex, o_q_size, t_qc.
apply Forall_cons; [eapply cbo_of_range; [exact ORI | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbo_of_range; [exact ORI | cbn; lia | cbn; lia]|].
apply Forall_app. split.
- do 4 (apply Forall_cons; [eapply cbo_of_range; [exact ORT | cbn; lia | cbn; lia]|]).
eapply batch_cells_owned; [exact M | intros b Hb; unfold all_batches; apply in_app_iff; left; exact Hb].
- do 4 (apply Forall_cons; [eapply cbo_of_range; [exact ORI | cbn; lia | cbn; lia]|]).
eapply batch_cells_owned; [exact M | intros b Hb; unfold all_batches; apply in_app_iff; right; exact Hb].
Qed.
Lemma fs_cells_owned : forall ly S rd, ARm B ly S rd -> Forall (cell_bytes_owned ly S) (fs_cells S).
Proof.
intros ly S rd M. assert (OR : owned_range ly S (ly_F ly) kFakeFramesOff) by (intros a Ha; eapply own_F_low; eassumption).
unfold kFakeFramesOff in OR. unfold fs_cells.
apply Forall_cons; [eapply cbo_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbo_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih.
eapply cbo_of_range; [exact OR | cbn; lia | cbn; lia].
Qed.
Lemma depot_cells_owned : forall ly S rd, ARm B ly S rd -> Forall (cell_bytes_owned ly S) (depot_cells ly S).
Proof.
intros ly S rd M.
pose proof (area_owned_range ly S rd (as_depot B, 4 * 2 ^ 20 + 32) M ltac:(cbn; tauto)) as ORD.
pose proof (area_owned_range ly S rd (as_store B, 32) M ltac:(cbn; tauto)) as ORS. cbn [fst snd] in ORD, ORS.
unfold depot_cells, d_nuniq, d_map1, s_total, s_block0.
apply Forall_cons; [eapply cbo_of_range; [exact ORD | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbo_of_range; [exact ORD | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbo_of_range; [exact ORS | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbo_of_range; [exact ORS | cbn; lia | cbn; lia]|]. apply Forall_nil.
Qed.
Lemma ialloc_cells_owned : forall ly S rd, ARm B ly S rd -> Forall (cell_bytes_owned ly S) (ialloc_cells B S).
Proof.
intros ly S rd M. pose proof (aso_ialloc _ (am_syms _ _ _ _ M)) as [I1 I2].
pose proof (area_owned_range ly S rd (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B) M ltac:(cbn; tauto)) as ORA.
pose proof (area_owned_range ly S rd (as_ialloc_flag B, 2) M ltac:(cbn; tauto)) as ORF. cbn [fst snd] in ORA, ORF.
unfold ialloc_cells.
apply Forall_cons; [eapply cbo_of_range; [exact ORF | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbo_of_range; [exact ORF | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbo_of_range; [exact ORA | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbo_of_range; [exact ORA | cbn; lia | cbn; lia]|]. apply Forall_nil.
Qed.
Lemma thread_cells_owned : forall ly S rd, ARm B ly S rd -> Forall (cell_bytes_owned ly S) thread_cells.
Proof.
intros ly S rd M. unfold thread_cells, t_unwinding. apply Forall_cons; [|apply Forall_nil].
eapply cbo_of_range; [intros a Ha; eapply (own_core ly S rd (ly_T ly, kThreadObjSize)); [exact M | unfold core_extents; cbn; tauto | exact Ha] | cbn; lia | cbn; unfold kThreadObjSize; lia].
Qed.
Lemma Forall_flat_map' : forall {X Y} (P : Y -> Prop) (f : X -> list Y) (l : list X),
(forall x, In x l -> Forall P (f x)) -> Forall P (flat_map f l).
Proof. intros X Y P f l H. apply Forall_forall. intros y Hy. apply in_flat_map in Hy as (x & Hx & Hy). exact (proj1 (Forall_forall _ _) (H x Hx) y Hy). Qed.
Lemma zseq_In : forall lo n x, In x (zseq lo n) -> lo <= x < lo + Z.max n 0.
Proof. intros lo n x H. unfold zseq in H. apply in_map_iff in H as (k & <- & Hk). apply in_seq in Hk. lia. Qed.
Lemma acells_owned : forall ly S rd, ARm B ly S rd -> Forall (cell_bytes_owned ly S) (acells B ly S).
Proof.
intros ly S rd M. unfold acells.
apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split;
[|apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split]]]]]]].
- apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc. eapply region_cells_owned; [exact M | lia].
- apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc. eapply cache_cells_owned; [exact M | lia].
- apply Forall_flat_map'. intros k Hk. eapply chunk_cells_owned; eassumption.
- eapply sec_cells_owned; exact M.
- eapply quar_cells_owned; exact M.
- eapply fs_cells_owned; exact M.
- eapply depot_cells_owned; exact M.
- eapply ialloc_cells_owned; exact M.
- eapply thread_cells_owned; exact M.
Qed.
Lemma const_cells_owned : forall ly S rd, ARm B ly S rd -> Forall (cell_bytes_owned ly S) (as_const B ly).
Proof.
intros ly S rd M. eapply Forall_impl; [|exact (am_const_owned _ _ _ _ M)]. intros c Hc k Hk.
destruct (Hc k Hk) as [O|[O|O]].
- eapply own_static; [exact M | exact O].
- apply Exists_exists in O as (e & He & Hin). eapply own_core; [exact M | exact He | exact Hin].
- apply Exists_exists in O as (r & Hr & Hin). eapply own_shadow_static; [exact M | exact Hr | exact Hin].
Qed.
Lemma cell_holds_agree : forall ly rd rd' c, cell_holds B ly rd c ->
(forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> rd' (aeval B ly (c_at c) + k) = rd (aeval B ly (c_at c) + k)) -> cell_holds B ly rd' c.
Proof.
intros ly rd rd' c Hc Hag. unfold cell_holds in *. destruct (c_val c) as [e|m v].
- intros k Hk. rewrite Hag by lia. exact (Hc k Hk).
- destruct Hc as (b & Hb & Hm). exists b. split; [|exact Hm]. specialize (Hag 0 ltac:(lia)). rewrite Z.add_0_r in Hag. rewrite Hag. exact Hb.
Qed.
Lemma Forall_cell_holds_agree : forall ly S rd rd' l,
(forall a, aowned B ly S a -> rd' a = rd a) -> Forall (cell_bytes_owned ly S) l -> Forall (cell_holds B ly rd) l -> Forall (cell_holds B ly rd') l.
Proof.
intros ly S rd rd' l AG OW H. apply Forall_forall. intros c Hc.
eapply cell_holds_agree; [exact (proj1 (Forall_forall _ _) H c Hc)|]. intros k Hk. apply AG. exact (proj1 (Forall_forall _ _) OW c Hc k Hk).
Qed.
Lemma Forall_range_vis_keep : forall ly rd rd' l, (forall a, rd a <> None -> rd' a <> None) ->
Forall (range_vis B ly rd) l -> Forall (range_vis B ly rd') l.
Proof. intros ly rd rd' l K H. apply Forall_forall. intros r Hr i Hi. apply K. exact (proj1 (Forall_forall _ _) H r Hr i Hi). Qed.
Lemma find_chunk_at_In : forall ly l g k, find_chunk_at B ly l g = Some k -> In k l /\ ck_base B ly k <= g < ck_base B ly k + ck_extent k.
Proof.
intros ly l g k. induction l as [|k' t IH]; intros H; [discriminate|]. cbn [find_chunk_at] in H.
destruct (andb (ck_base B ly k' <=? g) (g <? ck_base B ly k' + ck_extent k')) eqn:E.
- injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. split; [left; reflexivity | lia].
- destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.
Lemma in_rangesb_true : forall g l, in_rangesb g l = true -> exists lo len, In (lo, len) l /\ lo <= g < lo + len.
Proof.
intros g l. induction l as [|[lo len] t IH]; intros H; [discriminate|]. cbn [in_rangesb] in H.
apply Bool.orb_true_iff in H as [H|H].
- apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists lo, len. split; [left; reflexivity | lia].
- destruct (IH H) as (lo' & len' & H1 & H2). exists lo', len'. split; [right; exact H1 | exact H2].
Qed.
Lemma ashadow_owned : forall ly S rd g v, ARm B ly S rd -> ashadow B ly S g = Some v -> aowned B ly S (shadow_addr g).
Proof.
intros ly S rd g v M H. unfold ashadow in H.
destruct (find_chunk_at B ly (st_chunks S) g) as [k|] eqn:F.
- apply find_chunk_at_In in F as [Hk Hg].
destruct (extent_zone ly S rd k M Hk) as [[X1 X2]|(m & len & Hin & X1 & X2)].
+ eapply own_shadow_prim; [exact M | lia].
+ eapply own_shadow_sec; [exact M | exact Hin | unfold kPage in *; lia].
- destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:R; [|discriminate].
apply in_rangesb_true in R as (lo & len & Hin & Hg). unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
+ apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
pose proof (region_in_prim ly c (am_layout _ _ _ _ M) ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wf_classes _ _ _ _ _ (am_wf _ _ _ _ M) c ltac:(lia)) as CL.
pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_fa _ _ _ _ _ _ CL) as [A2 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as A3.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S c (am_wf _ _ _ _ M) ltac:(lia)) as MB. unfold kUserMapSize, EV_MAX, kFreeArrayMax in *.
eapply own_shadow_prim; [exact M|]. unfold fa_base, kFreeArrayOffset in Hin. unfold region_base in *.
destruct Hin as [E|[E|[]]]; injection E as <- <-; lia.
+ eapply own_shadow_sec; [exact M | exact Hin | exact Hg].
Qed.
Lemma al_img_env : forall ly S md, layout_ok ly -> ALedger segs ly S md ->
forall sg, In sg segs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd.
Proof.
intros ly S md LO L sg Hsg. pose proof (al_img _ _ _ _ L sg Hsg) as [I1 I2]. pose proof (lo_img _ LO) as (J0 & J1 & J2 & J3).
unfold kImgLo, kImgEnd in *. lia.
Qed.
Lemma seg_rom_none_above : forall a,
(forall sg, In sg segs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd) ->
kImgEnd <= a < 2 ^ 64 -> seg_rom segs (w64 a) = None.
Proof.
intros a IMG Ha. unfold seg_rom, memory_read. unfold kImgEnd in *.
assert (FS : find_segment segs (bv_unsigned (w64 a)) 1 = None).
{ unfold w64. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
clear - IMG Ha. induction segs as [|sg t IH]; [reflexivity|]. cbn [find_segment].
destruct (IMG sg (or_introl eq_refl)) as [G1 G2].
destruct (Z.leb_spec (Z.of_N (seg_base sg)) a); destruct (Z.leb_spec (a + 1) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg))); cbn [andb]; try lia.
all: apply IH; intros sg' Hin; apply IMG; right; exact Hin. }
change (Z.of_N 1) with 1. rewrite FS. reflexivity.
Qed.
Lemma aview_band : forall H mem a,
(forall sg, In sg segs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd) ->
in_band_rw a -> H (w64 a) = false ->
(aview segs H mem a <> None <-> mem (w64 a) <> None).
Proof.
intros H mem a IMG Ha Hh. unfold aview, mbyte, mrestrict. unfold w64 in *. rewrite Hh.
destruct (mem (Z_to_bv 64 a)) as [b|] eqn:E; cbn.
- split; intros _; discriminate.
- change (Z_to_bv 64 a) with (w64 a). rewrite (seg_rom_none_above a IMG) by (unfold in_band_rw, kImgEnd, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia). cbn. split; intros X; exfalso; exact (X eq_refl).
Qed.
Lemma aview_band_hidden : forall H mem a,
(forall sg, In sg segs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd) ->
in_band_rw a -> H (w64 a) = true -> aview segs H mem a = None.
Proof.
intros H mem a IMG Ha Hh. unfold aview, mbyte, mrestrict. unfold w64 in *. rewrite Hh.
change (Z_to_bv 64 a) with (w64 a). rewrite (seg_rom_none_above a IMG) by (unfold in_band_rw, kImgEnd, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia). reflexivity.
Qed.
Lemma client_band_vis : forall ly S rd a, ARm B ly S rd -> in_band_rw a -> aclient_byte B ly S a -> rd a <> None.
Proof.
intros ly S rd a M Ha [(k & Hk & Hst & Hr)|(cp & Hcp & [Hr|Hr])].
- exfalso. pose proof (chunk_facts B ly S rd k M Hk) as (G1 & _ & _ & G4 & G5 & _ & _ & G8 & _). rewrite G4 in Hr.
ceil; unfold in_app, ASAN_CEIL, ck_n, in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. lia.
- exfalso. pose proof (am_layout _ _ _ _ M) as LO.
pose proof (proj1 (Forall_forall _ _) (lo_app _ LO) (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as H1. cbn [fst snd] in H1.
pose proof (proj1 (Forall_forall _ _) (wfs_live _ (wf_fakestack _ _ _ _ _ (am_wf _ _ _ _ M))) cp Hcp) as [Hc Hp]. cbn [fst snd] in Hc, Hp.
pose proof (frame_off_bounds (fst cp) (snd cp) Hc Hp) as FB. unfold in_zr, frame_addr in Hr. cbn [fst snd] in Hr.
ceil; unfold in_app, ASAN_CEIL, in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kFakeFramesOff, kFakeStackSize in *. lia.
- destruct cp as [cid pos]. cbn [fst snd] in Hr. unfold in_zr in Hr. cbn [fst snd] in Hr.
pose proof (proj1 (Forall_forall _ _) (am_client _ _ _ _ M) (ASh (AF (fs_frame_off cid pos)), fs_frame_bytes cid / 8)
ltac:(unfold aclient; rewrite !in_app_iff; right; right; apply in_map_iff; exists (cid, pos); auto)) as V.
specialize (V (a - shadow_addr (frame_addr ly cid pos)) ltac:(cbn [snd]; lia)). cbn [fst aeval] in V. unfold frame_addr in V |- *.
replace (shadow_addr (ly_F ly + fs_frame_off cid pos) + (a - shadow_addr (ly_F ly + fs_frame_off cid pos))) with a in V by lia. exact V.
Qed.
Lemma ahs_pres_transfer : forall ly S S' H mem mem',
(forall sg, In sg segs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd) ->
ARm B ly S (aview segs H mem) -> ahs_pres B ly S H mem ->
(forall a, aview segs H mem a <> None -> aview segs H mem' a <> None) ->
(forall a, in_band_rw a -> H (w64 a) = true -> mem (w64 a) <> None -> mem' (w64 a) <> None) ->
(forall a, in_band_rw a -> aclient_byte B ly S' a -> aclient_byte B ly S a) ->
ahs_pres B ly S' H mem'.
Proof.
intros ly S S' H mem mem' IMG M HA VIS HK CL a Ha NC HV.
destruct (H (w64 a)) eqn:Hh.
-
assert (NCS : ~ aclient_byte B ly S a).
{ intros C. apply (client_band_vis ly S _ a M Ha C). apply aview_band_hidden; assumption. }
exact (HK a Ha Hh (HA a Ha NCS (or_introl Hh))).
-
destruct (aview segs H mem a) as [v|] eqn:AV.
+ apply (proj1 (aview_band H mem' a IMG Ha Hh)). apply VIS. rewrite AV. discriminate.
+ assert (NCS : ~ aclient_byte B ly S a) by (intros C; exact (client_band_vis ly S _ a M Ha C AV)).
exfalso. apply (proj2 (aview_band H mem a IMG Ha Hh)); [|exact AV].
apply (HA a Ha NCS). destruct HV as [Hv|Hv]; [exfalso; change (YG0n.w64 a) with (w64 a) in Hv; rewrite Hv in Hh; discriminate | right; exact Hv].
Qed.
Lemma hfree_shadow_owned : forall ly S rd g, ARm B ly S rd -> g mod 8 = 0 -> in_app g 8 ->
hfree ly S g -> aowned B ly S (shadow_addr g).
Proof.
intros ly S rd g M Hg HA HF. pose proof HA as [H0 HLH]. split.
- right. right. right. right. apply Exists_exists.
destruct HLH as [HL | [HH1 HH2]].
+ exists lm_zone. split; [rewrite !in_app_iff; right; right; right; right; right; left; reflexivity|].
unfold in_zr, lm_zone. cbn [fst snd]. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kLowMemEnd in *.
apply Z.mod_divide in Hg as [q Hq]; [|lia]. subst g. rewrite Z.div_mul by lia.
change (0 / 8) with 0. change ((2147450880 + 7) / 8) with 268431360. lia.
+ exists hm_zone. split; [rewrite !in_app_iff; right; right; right; right; left; reflexivity|].
unfold in_zr, hm_zone. cbn [fst snd]. ceil; unfold shadow_addr, SHADOW_OFF, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *.
apply Z.mod_divide in Hg as [q Hq]; [|lia]. subst g. rewrite Z.div_mul by lia.
change (17594333495296 / 8) with 2199291686912. change ((140737488355328 - 17594333495296 + 7) / 8) with 15392894357504. lia.
- eapply (nc_shadow ly S rd _ g 8 M Hg); [lia | ceil; unfold ASAN_CEIL, kHighMemEnd, kLowShadowBeg, kHighMemBeg in *; lia | |].
+ unfold hfree in HF. pose proof (proj1 (Forall_forall _ _) HF (ly_F ly, kFakeStackSize)
ltac:(rewrite !in_app_iff; left; unfold static_extents, owned_extents; rewrite in_app_iff; left; cbn; tauto)) as X.
cbn [fst snd] in X. unfold zdisjoint. cbn [fst snd]. lia.
+ change ((8 + 7) / 8) with 1. lia.
Qed.
Lemma ahz_transfer : forall ly S S' H mem mem',
(forall sg, In sg segs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd) ->
ahz ly S mem -> sec_extents ly S' = sec_extents ly S ->
(forall a, in_band_rw a -> H (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
(forall g, g mod 8 = 0 -> in_app g 8 -> hfree ly S g -> H (w64 (shadow_addr g)) = false ->
aview segs H mem' (shadow_addr g) = aview segs H mem (shadow_addr g)) ->
ahz ly S' mem'.
Proof.
intros ly S S' H mem mem' IMG HZ SE HK AG. apply (ahz_keep ly S S' mem mem'); [|exact HZ].
intros g Hg HA HF. assert (HF0 : hfree ly S g) by (unfold hfree in *; rewrite SE in HF; exact HF). split; [exact HF0|].
pose proof (shadow_addr_band_rw g HA) as Hb.
destruct (H (w64 (shadow_addr g))) eqn:Hh; [exact (HK _ Hb Hh)|].
pose proof (AG g Hg HA HF0 Hh) as E. pose proof (HZ g Hg HA HF0) as Z0.
unfold aview, mbyte, mrestrict in E. unfold w64, YG0n.w64 in *. rewrite Hh in E. rewrite Z0 in E.
destruct (mem' (Z_to_bv 64 (shadow_addr g))) as [b|] eqn:Eb.
- cbn in E. injection E as E. rewrite Z0. f_equal. apply bv_eq. exact E.
- exfalso. pose proof (seg_rom_none_above (shadow_addr g) IMG ltac:(unfold in_band_rw, kImgEnd, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia)) as R.
unfold w64, YG0n.w64 in R. rewrite R in E. cbn in E. discriminate E.
Qed.
Lemma hfree_off_extent : forall ly S rd k g, ARm B ly S rd -> In k (st_chunks S) ->
g mod 8 = 0 -> hfree ly S g -> g + 8 <= ck_base B ly k \/ ck_base B ly k + ck_extent k <= g.
Proof.
intros ly S rd k g M Hk Hg HF. unfold hfree in HF.
destruct (extent_zone ly S rd k M Hk) as [[P1 P2] | (m & len & Hin & E1 & E2)].
- pose proof (proj1 (Forall_forall _ _) HF (ly_prim ly, kPrimResvSize)
ltac:(rewrite !in_app_iff; left; unfold static_extents, owned_extents; rewrite in_app_iff; left; cbn; tauto)) as X.
cbn [fst snd] in X. lia.
- pose proof (proj1 (Forall_forall _ _) HF (m, len) ltac:(rewrite !in_app_iff; right; right; exact Hin)) as X. cbn [fst snd] in X. unfold kPage in *. lia.
Qed.
Lemma hfree_shadow_off_range : forall ly S rd k lo len g, ARm B ly S rd -> In k (st_chunks S) ->
ck_base B ly k <= lo -> lo + len <= ck_base B ly k + ck_extent k -> lo mod 8 = 0 -> 0 <= len ->
g mod 8 = 0 -> hfree ly S g ->
~ (shadow_addr lo <= shadow_addr g < shadow_addr lo + (len + 7) / 8).
Proof.
intros ly S rd k lo len g M Hk H1 H2 Hlo Hlen Hg HF [R1 R2].
pose proof (hfree_off_extent ly S rd k g M Hk Hg HF) as X.
apply Z.mod_divide in Hg as [q Hq]; [|lia]. apply Z.mod_divide in Hlo as [ql Hql]; [|lia]. subst g lo.
unfold shadow_addr, SHADOW_OFF in R1, R2. rewrite !Z.div_mul in R1, R2 by lia.
pose proof (Z.mul_div_le (len + 7) 8 ltac:(lia)) as M1. pose proof (Z.div_pos (len + 7) 8 ltac:(lia) ltac:(lia)) as M2.
assert (M3 : len <= 8 * ((len + 7) / 8)) by (pose proof (Z.div_mod (len + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (len + 7) 8 ltac:(lia)); lia).
destruct X as [X|X]; [nia|].
assert (q - ql < (len + 7) / 8) by lia. assert (len <= 8 * (q - ql)) by lia.
assert ((len + 7) / 8 <= q - ql) by (apply Z.div_le_upper_bound; lia). lia.
Qed.
Lemma ahs_transfer : forall ly S S' H mem mem',
(forall sg, In sg segs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd) ->
ARm B ly S (aview segs H mem) -> ahs B ly S H mem ->
(forall a, aview segs H mem a <> None -> aview segs H mem' a <> None) ->
(forall a, in_band_rw a -> H (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
(forall a, in_band_rw a -> aclient_byte B ly S' a -> aclient_byte B ly S a) ->
sec_extents ly S' = sec_extents ly S ->
(forall g, g mod 8 = 0 -> in_app g 8 -> hfree ly S g -> H (w64 (shadow_addr g)) = false ->
aview segs H mem' (shadow_addr g) = aview segs H mem (shadow_addr g)) ->
ahs B ly S' H mem'.
Proof.
intros ly S S' H mem mem' IMG M [HA HZ] VIS HK CL SE AG. split.
- apply (ahs_pres_transfer ly S S' H mem mem' IMG M HA VIS); [|exact CL]. intros a Ha Hh Hm. rewrite (HK a Ha Hh). exact Hm.
- exact (ahz_transfer ly S S' H mem mem' IMG HZ SE HK AG).
Qed.
Theorem AR_frame_law_ok : AR_frame_law segs B.
Proof.
intros ly S W mem md mem' md' (M & L & BUD & MW & HS) AGR VIS Hvm Hlz He HK.
set (rd := aview segs (w_H W) mem) in *. set (rd' := aview segs (w_H W) mem') in *.
assert (AG : forall a, aowned B ly S a -> rd' a = rd a).
{ intros a Ha. apply AGR; [|exact Ha]. pose proof (AR_owned_low_law_ok segs B ly S W mem md a (conj M (conj L (conj BUD (conj MW HS)))) Ha).
pose proof ASAN_CEIL_range as [CR _]. unfold ASAN_CEIL in CR. lia. }
split; [|split; [eapply ALedger_same; eassumption | split; [exact BUD | split; [exact (amwf_same md md' Hvm Hlz MW) |
exact (ahs_transfer ly S S (w_H W) mem mem' (al_img_env ly S md (am_layout _ _ _ _ M) L) M HS VIS HK ltac:(intros a _ C; exact C) eq_refl
ltac:(intros g Hg HA HF _; apply AG; eapply hfree_shadow_owned; [exact M | exact Hg | exact HA | exact HF]))]]]].
pose proof M as M0. destruct M as [Xwf Xuni Xsyms Xlay Xplaced Xconst Xcowned Xcells Xfa Xflags Xdepot Xshadow Xzsh Xjunk Xareas Xclient Xzero].
constructor; try assumption.
- eapply Forall_cell_holds_agree; [exact AG | eapply const_cells_owned; exact M0 | assumption].
- eapply Forall_cell_holds_agree; [exact AG | eapply acells_owned; exact M0 | assumption].
-
intros c i v Hc Hi Hv k Hk. rewrite AG; [exact (Xfa c i v Hc Hi Hv k Hk)|].
pose proof (wf_classes _ _ _ _ _ Xwf c Hc) as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
eapply own_fa; [exact M0 | exact Hc | lia].
-
intros cid pos Hc Hp. rewrite AG; [exact (Xflags cid pos Hc Hp)|].
pose proof (flag_off_bounds cid pos Hc Hp) as FB. unfold flag_addr, kFakeFlagsOff in *. eapply own_F_low; [exact M0 | lia].
-
destruct Xdepot as (heads & links & D1 & D2 & D3). exists heads, links. split; [|split; [|exact D3]].
+ intros b Hb. destruct (D1 b Hb) as [H1 H2]. split; [exact H1|]. intros k Hk. rewrite AG; [exact (H2 k Hk)|].
eapply (own_area ly S rd (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | cbn; tauto | cbn; unfold d_tab_words in Hb; lia].
+ intros id Hid. destruct (D2 id Hid) as (H1 & H2 & H3). split; [exact H1|].
assert (NB : depot_ids S <= 4097).
{ unfold depot_ids. pose proof (wf_depot _ _ _ _ _ Xwf) as [ND INC]. pose proof (NoDup_incl_length ND INC). destruct Xuni as (U1 & _). unfold DEPOT_MAX in U1. lia. }
assert (OR : forall k, 0 <= k < 16 -> aowned B ly S (ly_NB ly + 16 * id + k)).
{ intros k Hk. eapply (own_core ly S rd (ly_NB ly, kNodesBlockSize)); [exact M0 | unfold core_extents; cbn; tauto | cbn; unfold kNodesBlockSize; lia]. }
split; intros k Hk; rewrite AG; auto; [apply OR; lia|]. replace (ly_NB ly + 16 * id + 8 + Z.of_nat k) with (ly_NB ly + 16 * id + (8 + Z.of_nat k)) by lia. apply OR. lia.
-
intros g v Hg Hv0. rewrite AG; [exact (Xshadow g v Hg Hv0)|]. eapply ashadow_owned; [exact M0 | exact Hv0].
-
unfold zshadow_ok in *. apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. fold (shadow_addr (fst r)).
change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)). rewrite AG; [exact (proj1 (Forall_forall _ _) Xzsh r Hr i Hi)|].
eapply own_shadow_zero; [exact M0 | exact Hr | exact Hi].
- eapply Forall_range_vis_keep; [exact VIS | assumption].
- eapply Forall_range_vis_keep; [exact VIS | assumption].
- eapply Forall_range_vis_keep; [exact VIS | assumption].
-
apply Forall_forall. intros r Hr i Hi. rewrite AG; [exact (proj1 (Forall_forall _ _) Xzero r Hr i Hi)|].
pose proof (aso_ialloc _ Xsyms) as [I1 I2].
eapply (own_area ly S rd (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact M0 | cbn; tauto |].
unfold ialloc_zero in Hr. cbn [fst snd]. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; lia.
Qed.
Theorem AR_laws_ok : AR_laws segs B.
Proof.
constructor.
- apply AR_blocks_law_ok.
- apply AR_shadow_law_ok.
- apply AR_zshadow_law_ok.
- apply AR_frame_law_ok.
- apply AR_frames_law_ok.
- apply AR_flag_law_ok.
- apply AR_const_law_ok.
- apply AR_stack_law_ok.
- apply AR_wle_law_ok.
- apply AR_layout_law_ok.
- apply AR_owned_low_law_ok.
- apply AR_owned_image_law_ok.
- apply AR_sep_law_ok.
- apply AR_client_img_law_ok.
Qed.
End s.
End j.
