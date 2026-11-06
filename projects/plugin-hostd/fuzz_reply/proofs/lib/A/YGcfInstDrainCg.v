(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the generic cf instance layer, lane F2b: the MODEL side of F11, the free-array growth arm of
   SizeClassAllocator64LocalCache::Deallocate (ReturnToAllocator -> EnsureFreeArraySpace -> a KMapFreeArray grant).
   rule 24: no function proved (kind: model-level facts of ensure_free_array's grant step).

   On a full cache whose free array lacks room for the drained half (rg_mapped_fa < 4 * (fa_len + max_cached / 2)),
   YG00.ensure_free_array asks the kernel for one more free-array map (KMapFreeArray c fa kFreeArrayMapSize).  On a
   grant the region's rg_mapped_fa grows by kFreeArrayMapSize and the hole at the new map is removed; nothing else in
   the state changes.  [cgX] is that state.  After it the free array has the room (cg_room), so the rest of the call is
   F12's no-growth step at [cgX] (YGcfInstDrainCm.cd_step_cf with X := cgX); F11 is the relation's transport across
   the grant itself, whose memory half takes the walk's grant post.  This file gives the grant's state facts:
   [cg_ensure] (the model's grant branch ends at cgX), [cg_WfR] (the cut invariant WfR_cf at cgX, from
   YG03cf.ensure_free_array_ok_y3), [cg_room], and the fields the relation reads ([cg_reg_other], [cg_reg_c],
   [cg_chunks] .. [cg_xs], [cg_prim_committed] / [cg_abudget]: the budget grows by exactly the new map's bytes).
   Image-free and event-free (no event-count term, no event regime and no event-keyed budget appears). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YP09 YO0d YK08 YP03.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YGcfTok YG03cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfXs ImgBase YG0h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstDrainR YGcfInstDrainRL.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* The closure now carries YGcfInstBase (through YGcfInstDrainX), which leaves lia's euclidean-division flag
   off; this file's proofs were written with it on. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section U. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section G.
Variable ly : alayout.
Variable X : astate.
Variable c : Z.
Hypothesis Hc : 1 <= c <= 30.
Hypothesis Hlenr : (Z.to_nat c < length (st_regions X))%nat.

Definition cgr : region :=
let r := reg X c in
mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_mapped_fa r + kFreeArrayMapSize) (rg_free r)
  (del_hole (kFreeArrayOffset + rg_mapped_fa r) (rg_holes r)).
Definition cgX : astate := upd_reg c cgr X.

(* The model's grant branch: when the free array lacks the room for [need] and one more map gives it, a grant ends
   ensure_free_array at cgX (YG00.v:258-275). *)
Lemma cg_ensure : forall need sof, rg_mapped_fa (reg X c) < 4 * need ->
round_up (4 * need) kFreeArrayMapSize = rg_mapped_fa (reg X c) + kFreeArrayMapSize ->
rg_mapped_fa (reg X c) + kFreeArrayMapSize <= kFreeArrayMax ->
exists k, ensure_free_array c need sof X = IAsk (KMapFreeArray c (rg_mapped_fa (reg X c)) kFreeArrayMapSize) X k /\
  (forall z, aGranted z = true -> k z = IRet (true, cgX)).
Proof.
intros need sof Hlt Hru Hmax. unfold ensure_free_array, get_region, set_region. unfold bind, get, ret, put, modify, askz.
cbn [ibind]. fold (reg X c).
destruct (Z.leb_spec (4 * need) (rg_mapped_fa (reg X c))) as [Hle|_]; [lia|]. cbn [ibind].
rewrite Hru. replace (rg_mapped_fa (reg X c) + kFreeArrayMapSize <=? kFreeArrayMax) with true by (symmetry; apply Z.leb_le; exact Hmax).
cbn [mcheck ibind]. replace (rg_mapped_fa (reg X c) + kFreeArrayMapSize - rg_mapped_fa (reg X c)) with kFreeArrayMapSize by lia.
eexists. split; [reflexivity|]. intros z Hz. cbn. rewrite Hz. reflexivity.
Qed.


(* The cut invariant at the grant state (YG03cf.ensure_free_array_ok_y3 read off at the granted answer). *)
Lemma cg_WfR : forall U pp cc bb need, WfR_cf U pp cc bb X ->
fa_len (rg_free (reg X c)) <= need -> rg_mapped_fa (reg X c) < 4 * need ->
4 * need <= rg_mapped_fa (reg X c) + kFreeArrayMapSize -> 4 * need <= kFreeArrayMax ->
round_up (4 * need) kFreeArrayMapSize = rg_mapped_fa (reg X c) + kFreeArrayMapSize ->
rg_mapped_fa (reg X c) + kFreeArrayMapSize <= kFreeArrayMax ->
WfR_cf U pp cc bb cgX.
Proof.
intros U pp cc bb need W Hlen Hlt H1 H2 Hru Hmax.
destruct (cg_ensure need true Hlt Hru Hmax) as (k & E & K).
pose proof (ensure_free_array_ok_y3 U pp cc bb X c need true true W ltac:(lia) Hlen H1 H2) as OK.
rewrite E in OK. cbn [atok] in OK. destruct OK as [_ OK].
specialize (OK 1 ltac:(cbn; right; reflexivity)). rewrite (K 1 eq_refl) in OK. cbn [atok] in OK.
destruct OK as (r' & E' & W' & _). exact W'.
Qed.

(* After the grant the drained half fits: F12's room holds at cgX. *)
Lemma cg_room : 4 * fa_len (rg_free (reg X c)) <= rg_mapped_fa (reg X c) -> max_cached c <= 16 ->
4 * (fa_len (rg_free (reg cgX c)) + max_cached c / 2) <= rg_mapped_fa (reg cgX c).
Proof.
intros H1 H2. unfold cgX. rewrite reg_upd_reg by (lia || exact Hlenr). unfold cgr. cbn [rg_free rg_mapped_fa].
unfold kFreeArrayMapSize. pose proof (Z.div_le_mono (max_cached c) 16 2 ltac:(lia) H2). lia.
Qed.

(* What the relation reads: only class [c]'s mapped free array and holes change. *)
Lemma cg_reg_other : forall c', 0 <= c' -> c' <> c -> reg cgX c' = reg X c'.
Proof. intros c' H1 H2. unfold cgX. apply reg_upd_reg_other; lia. Qed.
Lemma cg_reg_c : reg cgX c = cgr.
Proof. unfold cgX. apply reg_upd_reg; [lia | exact Hlenr]. Qed.
Lemma cg_chunks : st_chunks cgX = st_chunks X. Proof. reflexivity. Qed.
Lemma cg_secs : st_secs cgX = st_secs X. Proof. reflexivity. Qed.
Lemma cg_sec_arr : st_sec_arr cgX = st_sec_arr X. Proof. reflexivity. Qed.
Lemma cg_sec_res : st_sec_reserved cgX = st_sec_reserved X. Proof. reflexivity. Qed.
Lemma cg_qthread : st_qthread cgX = st_qthread X. Proof. reflexivity. Qed.
Lemma cg_qglobal : st_qglobal cgX = st_qglobal X. Proof. reflexivity. Qed.
Lemma cg_fs : st_fs cgX = st_fs X. Proof. reflexivity. Qed.
Lemma cg_depot : st_depot cgX = st_depot X. Proof. reflexivity. Qed.
Lemma cg_cache : st_cache cgX = st_cache X. Proof. reflexivity. Qed.
Lemma cg_cinit : st_cache_inited cgX = st_cache_inited X. Proof. reflexivity. Qed.
Lemma cg_sec_extents : sec_extents ly cgX = sec_extents ly X. Proof. reflexivity. Qed.
Lemma cg_xs : xs_cf ly cgX = xs_cf ly X. Proof. reflexivity. Qed.

Lemma cg_prim_committed : prim_committed cgX = prim_committed X + kFreeArrayMapSize.
Proof.
unfold cgX, upd_reg. rewrite prim_committed_set_region by (lia || exact Hlenr). unfold cgr. cbn [rg_mapped_user rg_mapped_fa].
unfold reg. lia.
Qed.

(* The budget at the grant: abudget_cf carries prim_committed / 8 (the primary's shadow, layer ae2fa80b0325), so a
   free-array grant raises it by the map AND its shadow (lane F2b's second hand measured the text). *)
Lemma cg_abudget : abudget_cf cgX = abudget_cf X + kFreeArrayMapSize + kFreeArrayMapSize / 8.
Proof.
(* the hull term is the unit's cf_hull, kept by its frame law (the grant changes neither st_secs nor the chunks) *)
assert (HH : cf_hull cgX = cf_hull X) by (apply cf_hull_frame; reflexivity).
unfold abudget_cf, sec_live_bytes, errb_cap_cf, errb_e. rewrite cg_prim_committed, HH.
assert (KF : kFreeArrayMapSize = 32768 * 8) by reflexivity.
assert (D : (prim_committed X + kFreeArrayMapSize) / 8 = prim_committed X / 8 + kFreeArrayMapSize / 8).
{ rewrite KF. rewrite Z.div_add by lia. rewrite Z.div_mul by lia. reflexivity. }
rewrite D. cbn. lia.
Qed.

End G.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The growth premises EnsureFreeArraySpace asks at its call (the walk's FGtN.efa_pre_lk, its growth clause), from the
   drain's cut relation at CacheDealloc's entry.  The byte budget is NOT derivable from the cut relation: it carries no
   room conjunct, and the cf meter (YG0ncf.mroom_cf) bounds E_BASE + abudget_cf but not the eager part (cgif's meter
   adds it, YG08.meter_room; YG08cf does not restate it).  It is the named OPEN premise [FREE_ROOM_cf] of the free side,
   per grant (one Deallocate can reach several grants: Enqueue's batch refill, and one per class the drain grows). *)
Lemma pairwise_nth_g : forall {A} (R : A -> A -> Prop) l i j x y, pairwise R l -> (i < j)%nat ->
nth_error l i = Some x -> nth_error l j = Some y -> R x y.
Proof.
intros A R l. induction l as [|h t IH]; intros i j x y HP Hij Hi Hj; [destruct i; discriminate|].
destruct HP as [HF HP]. destruct i as [|i]; destruct j as [|j]; try lia.
- cbn in Hi, Hj. injection Hi as <-. exact (proj1 (Forall_forall _ _) HF y (nth_error_In _ _ Hj)).
- cbn in Hi, Hj. exact (IH i j x y HP ltac:(lia) Hi Hj).
Qed.

Section P. Context {IM : AImg}.
Definition FREE_ROOM_cf (md : Model) (W : world im_segs) : Prop :=
eager_used md + A_bytes (w_A W) + 2 * kUserMapSize + 32768 <= vm_limit (m_vmmaps md).

Variables (B : asyms) (ly : alayout) (X : astate) (Hp : list Z) (W : world im_segs) (mem : word -> option byte) (md : Model).
Variable c : Z.
Hypothesis MR : ARcfR im_segs B ly X Hp W mem md.
Hypothesis Hc : 1 <= c <= 30.
(* cd_model's growth clause: one more map fits under the free array's bound *)
Hypothesis Hgrow : rg_mapped_fa (reg X c) + kFreeArrayMapSize <= kFreeArrayMax.
Local Notation mf := (rg_mapped_fa (reg X c)).
Local Notation fadr := (fa_base ly c + rg_mapped_fa (reg X c)).

Lemma cgp_M : ARmcfR B ly X Hp (aview im_segs (w_H W) mem). Proof. exact (proj1 MR). Qed.
Lemma cgp_LO : layout_ok ly. Proof. exact (amr_layout _ _ _ _ _ cgp_M). Qed.
Lemma cgp_LED : ALedger_cf im_segs ly X md. Proof. exact (proj1 (proj2 MR)). Qed.
Lemma cmSXg : forall i j x y, (i < j)%nat -> nth_error (static_extents ly) i = Some x -> nth_error (static_extents ly) j = Some y -> zdisjoint x y.
Proof. intros i j x y Hij Hi Hj. exact (pairwise_nth_g zdisjoint _ i j x y (lo_disj _ cgp_LO) Hij Hi Hj). Qed.


Lemma cgp_fa : 0 <= mf <= kFreeArrayMax /\ mf mod kFreeArrayMapSize = 0.
Proof.
pose proof (wfr_classes _ _ _ _ _ (amr_wfr _ _ _ _ _ cgp_M) c ltac:(lia)) as CL.
pose proof (wrc_fa _ _ _ _ _ _ CL) as [F1 F2]. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as F3. split; [lia | exact F2].
Qed.

Lemma cgp_slot : ly_prim ly <= fadr /\ fadr + kUserMapSize <= ly_prim ly + kPrimResvSize /\ kHighMemBeg <= fadr.
Proof.
pose proof cgp_fa as [[F0 F1] _]. pose proof (region_in_prim ly c cgp_LO ltac:(lia)) as (R1 & R2 & _ & R4 & _).
unfold fa_base, region_base in *. unfold kFreeArrayOffset, kFreeArrayMax, kUserMapSize, kFreeArrayMapSize in *. lia.
Qed.

(* The next free-array slot is not reserved by the image: only the image's segments are reserved (alc_reserved). *)
Lemma cgp_reserved : region_free (vm_reserved (m_vmmaps md)) (w64 fadr) (w64 kUserMapSize) = true.
Proof.
rewrite (alc_reserved _ _ _ _ cgp_LED). pose proof cgp_slot as (S1 & S2 & S3). 
apply region_free_reserved; [exact (RL.al_img_env_cf im_segs ly X md cgp_LO cgp_LED) | | unfold kUserMapSize; lia |].
- unfold kImgEnd, kHighMemBeg in *. lia.
- pose proof (lo_high _ cgp_LO) as IP. unfold in_high in IP. cbn [fst snd] in IP. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
  unfold ASAN_CEIL in *. lia.
Qed.


(* No byte of the primary reserve is a hole at cf: every hole is the zero-length marker (EXH_HOLE, 0). *)
Lemma cgp_nohole : forall a, ~ prim_hole_at ly X a.
Proof.
intros a (c' & h & Hc' & Hh & Ha). pose proof (wfr_classes _ _ _ _ _ (amr_wfr _ _ _ _ _ cgp_M) c' Hc') as CL.
pose proof (wrc_holes _ _ _ _ _ _ CL) as [HH _]. rewrite (proj1 (Forall_forall _ _) HH h Hh) in Ha.
unfold in_zr in Ha. cbn [fst snd] in Ha. lia.
Qed.

(* Every cut point above the slot's start is at or above its end: cut points sit on 2 ^ 18 boundaries of their
   region (kFreeArrayOffset is one) and regions are 2 ^ 32 apart. *)
Lemma cgp_cut_above : forall x, cut_ok ly X x -> fadr < x -> fadr + kUserMapSize <= x.
Proof.
intros x Hx Hlt. pose proof cgp_slot as (S1 & S2 & S3). pose proof cgp_fa as [[F0 F1] Fal].
apply Z.mod_divide in Fal as [m Hm]; [|unfold kFreeArrayMapSize; lia].
destruct Hx as [->|[->|(c' & Hc' & [(k & -> & K1 & K2)|(k & -> & K1 & K2)])]].
- lia.
- lia.
- unfold fa_base, region_base in *. rewrite !region_off_eq in * by lia.
  unfold kFreeArrayOffset, kUserMapSize, kFreeArrayMapSize in *. nia.
- unfold fa_base, region_base in *. rewrite !region_off_eq in * by lia.
  unfold kFreeArrayOffset, kUserMapSize, kFreeArrayMapSize in *. nia.
Qed.

Lemma cg_map_contains_intro : forall l (lo n : word) b s, In (b, s) l -> bv_unsigned b <= bv_unsigned lo ->
bv_unsigned lo + bv_unsigned n <= bv_unsigned b + bv_unsigned s -> map_contains l lo n = true.
Proof.
intros l lo n b s Hin H1 H2. unfold map_contains. apply existsb_exists. exists (b, s). split; [exact Hin|].
cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

(* The slot lies inside one of the model's maps (alc_prim: the pieces cover the primary reserve, which has no holes,
   and a piece ends only at a cut point). *)
Lemma cgp_mapped : map_contains (vm_maps (m_vmmaps md)) (w64 fadr) (w64 kUserMapSize) = true.
Proof.
pose proof cgp_slot as (S1 & S2 & S3).
destruct (alc_prim _ _ _ _ cgp_LED) as (pieces & (PF & PD & PH) & PI).
assert (EX : Exists (in_zr fadr) pieces) by (apply (proj2 (PH fadr ltac:(unfold kUserMapSize in *; lia))); apply cgp_nohole).
apply Exists_exists in EX as (p & Hpp & Hin). unfold in_zr in Hin.
destruct (proj1 (PI p) Hpp) as (Hm & Hpos & P1 & P2).
pose proof (proj1 (Forall_forall _ _) PF p Hpp) as (_ & _ & CE).
pose proof (cgp_cut_above _ CE ltac:(lia)) as HE.
pose proof (lo_high _ cgp_LO) as IP. unfold in_high in IP. cbn [fst snd] in IP. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
unfold ASAN_CEIL, kHighMemBeg in *.
assert (B1 : 0 <= fst p < 2 ^ 64) by lia.
assert (B2 : 0 <= snd p < 2 ^ 64) by lia.
assert (B3 : 0 <= fa_base ly c + rg_mapped_fa (reg X c) < 2 ^ 64) by lia.
assert (B4 : 0 <= kUserMapSize < 2 ^ 64) by (unfold kUserMapSize; lia).
apply (cg_map_contains_intro _ _ _ (w64 (fst p)) (w64 (snd p)) Hm); try unfold YG0n.w64; try unfold w64; cbv [w64] in *;
  rewrite ?(unsigned_lit_small _ B1), ?(unsigned_lit_small _ B2), ?(unsigned_lit_small _ B3), ?(unsigned_lit_small _ B4);
  lia.
Qed.


(* The slot is 8-aligned (the space base is 65536-aligned; kFreeArrayOffset and mf are multiples of 2 ^ 18). *)
Lemma cgp_al8 : exists q, fadr = 8 * q.
Proof.
pose proof (lo_space_al _ cgp_LO) as SA. pose proof cgp_fa as [_ Fal].
apply Z.mod_divide in SA as [s Hs]; [|lia]. apply Z.mod_divide in Fal as [m Hm]; [|unfold kFreeArrayMapSize; lia].
unfold fa_base, region_base. rewrite region_off_eq by lia. rewrite Hs, Hm.
unfold kFreeArrayOffset, kFreeArrayMapSize. exists (8192 * s + c * 536870912 + 469762048 + 32768 * m). lia.
Qed.

(* A zone apart from the slot has its shadow apart from the slot's shadow. *)
Lemma cgp_zone_apart : forall z a, 0 <= fst z -> 0 < snd z -> zdisjoint z (fadr, kUserMapSize) ->
shadow_addr (fst z) <= a <= shadow_addr (fst z + snd z - 1) -> ~ (shadow_addr fadr <= a < shadow_addr fadr + 32768).
Proof.
intros z a Z0 Z1 DJ Ha Hs. destruct cgp_al8 as [q Hq].
unfold shadow_addr in *. rewrite Hq in Hs. rewrite Z.mul_comm, Z_div_mult in Hs by lia.
unfold zdisjoint, kUserMapSize in DJ. cbn [fst snd] in DJ. destruct DJ as [D|D].
- assert ((fst z + snd z - 1) / 8 < q) by (apply Z.div_lt_upper_bound; lia). lia.
- assert (q + 32768 <= fst z / 8) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

(* Every zone of vis0_zones is apart from the new map: the static extents by lo_disj, the region-info page because
   the slot is below it (c <= 30), the image because it is low, and ly_extra by lo_extra's pairwise disjointness. *)
Lemma cgp_zones_apart : forall z, In z (vis0_zones ly) -> 0 <= fst z /\ 0 < snd z /\ zdisjoint z (fadr, kUserMapSize).
Proof.
intros z Hz. pose proof cgp_slot as (S1 & S2 & S3). pose proof cgp_fa as [[F0 F1] _].
pose proof (lo_high _ cgp_LO) as HIP. unfold in_high in HIP. cbn [fst snd] in HIP.
pose proof (lo_space_in _ cgp_LO) as [SP1 SP2]. pose proof (region_off_eq c ltac:(lia)) as RO.
pose proof (lo_app _ cgp_LO) as APPF.
assert (SLOT : ly_space ly + c * 2 ^ 32 + kFreeArrayOffset <= fadr /\ fadr + kUserMapSize < ly_space ly + kRegionInfoOff).
{ unfold fa_base, region_base in *. rewrite RO in *.
  unfold kFreeArrayOffset, kFreeArrayMax, kUserMapSize, kRegionInfoOff in *. split; [lia|]. nia. }
(* every static extent other than the primary reserve is apart from the slot, by lo_disj alone *)
assert (ST : forall j e, nth_error (static_extents ly) j = Some e -> (j <> 0)%nat -> zdisjoint e (fadr, kUserMapSize)).
{ intros j e Hj Hj0. pose proof (cmSXg 0%nat j _ _ ltac:(lia) eq_refl Hj) as D. unfold zdisjoint in *.
  cbn [fst snd] in *. unfold kUserMapSize in *. lia. }
(* the owned extents start above the image *)
assert (POS : forall e, In e (owned_extents ly) -> 4096 <= fst e).
{ intros e He. pose proof (proj1 (Forall_forall _ _) APPF e He) as IA. unfold in_app in IA. lia. }
unfold vis0_zones in Hz. apply in_app_iff in Hz as [Hz|Hz].
- cbn [In] in Hz. pose proof (lo_img _ cgp_LO) as (I1 & I2 & I3 & _).
  assert (OWN : forall e, In e (owned_extents ly) -> 0 <= fst e) by (intros e He; pose proof (POS e He); lia).
  destruct Hz as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; cbn [fst snd].
  + split; [pose proof (OWN (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as PT; cbn [fst] in PT; lia|]. split; [unfold kThreadObjSize; lia | exact (ST 2%nat _ eq_refl ltac:(lia))].
  + split; [pose proof (OWN (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as PT; cbn [fst] in PT; lia|]. split; [unfold kFakeStackSize; lia | exact (ST 3%nat _ eq_refl ltac:(lia))].
  + split; [pose proof (OWN (ly_NB ly, kNodesBlockSize) ltac:(unfold owned_extents; cbn; tauto)) as PT; cbn [fst] in PT; lia|]. split; [unfold kNodesBlockSize; lia | exact (ST 4%nat _ eq_refl ltac:(lia))].
  + split; [pose proof (OWN (ly_SB ly, kStoreBlockSize) ltac:(unfold owned_extents; cbn; tauto)) as PT; cbn [fst] in PT; lia|]. split; [unfold kStoreBlockSize; lia | exact (ST 5%nat _ eq_refl ltac:(lia))].
  + split; [pose proof (OWN (ly_C ly, 256) ltac:(unfold owned_extents; cbn; tauto)) as PT; cbn [fst] in PT; lia|]. split; [unfold kCtxMapSize; lia|].
    pose proof (lo_ctx _ cgp_LO) as DC. unfold zdisjoint in DC |- *. cbn [fst snd] in DC |- *.
    unfold kCtxMapSize, kPrimResvSize, kUserMapSize in *. lia.
  + split; [pose proof (OWN (ly_D ly, 4096) ltac:(unfold owned_extents; cbn; tauto)) as PT; cbn [fst] in PT; lia|]. split; [lia | exact (ST 7%nat _ eq_refl ltac:(lia))].
  + split; [pose proof (OWN (ly_Q ly, kPtrArrayResv) ltac:(unfold owned_extents; cbn; tauto)) as PT; cbn [fst] in PT; lia|]. split; [unfold kPtrArrayResv; lia | exact (ST 1%nat _ eq_refl ltac:(lia))].
  + unfold kRegionInfoOff, kHighMemBeg in *. split; [lia|]. split; [lia|]. unfold zdisjoint. cbn [fst snd]. lia.
  + rewrite I1. split; [unfold kImgLo; lia|]. split; [lia|]. unfold zdisjoint. cbn [fst snd].
    unfold kImgLo, kImgEnd, kHighMemBeg in *. lia.
- pose proof (proj1 (proj2 (lo_extra _ cgp_LO))) as EF.
  pose proof (proj1 (Forall_forall _ _) EF z Hz) as EZ.
  assert (DJ : zdisjoint z (ly_prim ly, kPrimResvSize)).
  { pose proof (proj2 (proj2 (lo_extra _ cgp_LO))) as PW.
    apply (pairwise_In zdisjoint _ z (ly_prim ly, kPrimResvSize) (ly_extra ly) (static_extents ly) eq_refl PW Hz).
    unfold static_extents, owned_extents. cbn. tauto. }
  unfold in_app in EZ. unfold zdisjoint in DJ. cbn [fst snd] in DJ.
  split; [lia|]. split; [lia|]. unfold zdisjoint. cbn [fst snd]. unfold kUserMapSize in *. lia.
Qed.

Lemma cgp_not_vis0 : forall a, shadow_addr fadr <= a < shadow_addr fadr + 32768 -> ~ in_vis0 ly a.
Proof.
intros a Ha IV. unfold in_vis0 in IV. apply Exists_exists in IV as (v & Hv & Hav).
pose proof (proj1 (Forall_forall _ _) (lo_vis0 _ cgp_LO) v Hv) as EX.
apply Exists_exists in EX as (z & Hz & [V1 V2]).
destruct (cgp_zones_apart z Hz) as (Z0 & Z1 & DJ).
unfold in_zr in Hav. exact (cgp_zone_apart z a Z0 Z1 DJ ltac:(lia) Ha).
Qed.

(* The new map's shadow bytes are present (FGtN.v:95). *)
Lemma cgp_shadow : forall a, shadow_addr fadr <= a < shadow_addr fadr + 32768 -> mem (w64 a) <> None.
Proof.
intros a Ha. pose proof cgp_slot as (S1 & S2 & S3). destruct cgp_al8 as [q Hq].
pose proof (proj2 (proj2 (proj2 (proj2 MR)))) as [HP _].
assert (APP : in_app fadr kUserMapSize).
{ pose proof (lo_high _ cgp_LO) as IP. unfold in_high in IP. cbn [fst snd] in IP. unfold in_app, kHighMemBeg in *. lia. }
assert (BAND : in_band_rw a).
{ replace a with (shadow_addr (fadr + 8 * (a - shadow_addr fadr))).
  - apply (shadow_addr_in_band fadr kUserMapSize); [exact APP|]. unfold shadow_addr in Ha |- *. rewrite Hq in Ha |- *.
    rewrite (Z.mul_comm 8 q), Z_div_mult in Ha |- * by lia. unfold kUserMapSize. lia.
  - unfold shadow_addr. rewrite Hq.
    replace (8 * q + 8 * (a - (SHADOW_OFF + 8 * q / 8))) with ((a - SHADOW_OFF) * 8)
      by (rewrite (Z.mul_comm 8 q), Z_div_mult by lia; lia).
    rewrite Z_div_mult by lia. lia. }
apply HP; [exact BAND| |right; exact (cgp_not_vis0 a Ha)].
intros CB.
assert (A1 : fadr mod 8 = 0) by (rewrite Hq; apply Z.mod_divide; [lia | exists q; lia]).
assert (A2 : 0 <= fadr) by (unfold kHighMemBeg in *; lia).
assert (A3 : fadr + kUserMapSize <= kHighMemEnd).
{ pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. pose proof (lo_high _ cgp_LO) as IP. unfold in_high in IP.
  cbn [fst snd] in IP. unfold ASAN_CEIL, kHighMemEnd, kUserMapSize, kHighMemBeg in *. lia. }
assert (A4 : zdisjoint (fadr, kUserMapSize) (ly_F ly, kFakeStackSize)).
{ pose proof (cmSXg 0%nat 3%nat _ _ ltac:(lia) eq_refl eq_refl) as D. unfold zdisjoint in D |- *. cbn [fst snd] in D |- *.
  unfold kFakeStackSize, kUserMapSize in *. lia. }
assert (A5 : shadow_addr fadr <= a < shadow_addr fadr + (kUserMapSize + 7) / 8).
{ unfold kUserMapSize. replace ((262144 + 7) / 8) with 32768 by (vm_compute; reflexivity). lia. }
exact (RL.nc_shadow_cf B ly X Hp _ a fadr kUserMapSize cgp_M A1 A2 A3 A4 A5 CB).
Qed.

Lemma cgp_amwf : amwf md. Proof. exact (proj1 (proj2 (proj2 (proj2 MR)))). Qed.
Lemma cgp_top : YM05.ceil_of_top (alloc_top (m_vmmaps md)). Proof. exact (alc_top _ _ _ _ cgp_LED). Qed.

(* The growth arm's premise side, as H3 asks it (DMcdR.rd_grow, commit 74b7ca9a0cc): everything but the byte budget,
   which is the named OPEN premise FREE_ROOM_cf. *)
Lemma cgp_rd_grow : FREE_ROOM_cf md W ->
region_free (vm_reserved (m_vmmaps md)) (w64 fadr) (w64 kUserMapSize) = true /\
map_contains (vm_maps (m_vmmaps md)) (w64 fadr) (w64 kUserMapSize) = true /\
amwf md /\ YM05.ceil_of_top (alloc_top (m_vmmaps md)) /\
eager_used md + A_bytes (w_A W) + 2 * kUserMapSize + 32768 <= vm_limit (m_vmmaps md) /\
(forall a, shadow_addr fadr <= a < shadow_addr fadr + 32768 -> mem (w64 a) <> None).
Proof.
intros HR. split; [exact cgp_reserved|]. split; [exact cgp_mapped|]. split; [exact cgp_amwf|].
split; [exact cgp_top|]. split; [exact HR | exact cgp_shadow].
Qed.
End P.
End U.
