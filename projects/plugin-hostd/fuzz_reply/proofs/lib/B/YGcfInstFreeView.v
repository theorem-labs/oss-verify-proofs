(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (lane F2a, a working branch): the generic cf layer's Deallocate interface, its VIEW
   fields (DGif0.di_view_n, di_view; and the big arm's DGbigIF.dbg_view) over the cf relation ARcf.  rule 24: no
   function proved (kind: interface-instance discharge: facts of the allocator relation at the cf instance).

   The cf twin of c5's DGif1.v:145-663 (view_n_cgif, view_cgif, dbview_room_cgif and their section facts), re-proved
   over YG0ncf.ARmcf / ARcf with YG0scf / YG0qcf / YG03cf's _cf lemmas in place of YG0s / YG0q / YG03's, and with every
   image fact taken from the image classes ImgBase.AImg / ImgBaseDG.DImg through the named premises of section 0:
   - YGcfDIface.IMG_COVER (the image window from the ledger; the layer's one name for that fact),
   - FV_TSD (the layout's TSD slot is the image's),
   - FQ_CONST (the Quarantine object's four constant cells: max_size_, max_cache_size_, min_size_, the bytes after
     the cache mutex; used here and by YGcfInstFreeQ),
   - FV_IAL (DImg's dg_ial_post is the internal allocator's initialized cells at the symbol table's addresses),
   - FV_ZONE3 (DImg's dg_zone3 holds of every application range apart from the image window; cgif YF0x.zone3_intro).
   The geometry the cgif proofs take from YF* image files (YFf0 / YFfl / YFfu) is re-proved here over ARmcf and the
   model's constants; the class bound is YG01cf.mapped_bound_cf (kFreeArrayOffset), never an event bound.
   The block size: free_cf's size test (YG00cf.free_cf) splits the blocks at kQuarantineMax; [view_cf] gives
   DGif0.dview (dv_zone's bound is kQuarantineMax's value, a working branch 002b8cc32f7) on the enqueue side,
   [view_big_cf] gives DGbigIF.dview_big (kQuarantineMax < req_size n, req_size n + 15 <= 2 ^ 30 by
   YG08cf.cf_malloc_max_bound) on the recycle side.
   Generic over CfImg / CfParams / AImg / DImg; no numeral of any image; no event term. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf YG0qcf YG03cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG DGif0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YFfl.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfDIface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG08cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DGbigIF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfImgRows.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac ceil := let H := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H.
Ltac dsplits := repeat match goal with |- _ /\ _ => split end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.
Variable B : asyms.

(* ================================================================================================================ *)
(* 0. The image premises, over the classes' fields and the symbol table only.                                      *)
(* (the image window from the ledger is YGcfDIface.IMG_COVER) *)
Definition FV_TSD : Prop := as_tsd B = im_tsd.
(* A constant cell of the image at address [a] (its address expression may be absolute or instance-relative). *)
Definition const_at (ly : alayout) (a : Z) (w : nat) (v : Z) : Prop :=
  exists e, In (ACell e w (AV (ANum v))) (as_const B ly) /\ aeval B ly e = a.
Definition FQ_CONST : Prop :=
  forall ly, const_at ly (as_inst B + o_q_max) 8 kQuarantineMax /\ const_at ly (as_inst B + o_q_maxcache) 8 kQuarantineCacheMax /\
             const_at ly (as_inst B + o_q_min) 8 kQuarantineMin /\ const_at ly (as_inst B + o_q_cmutex + 2) 2 0.
(* The internal allocator's initialized cells, at the symbol table's addresses (cgif DGgi.IAL_POST's text with
   TFIB_IAL_* replaced by the asyms fields that TfibSyms equates them to). *)
Definition ial_post_cf (W : world im_segs) (m : word -> option byte) : Prop :=
  let m' := mrestrict (w_H W) m in
  val_mem im_segs m' (as_ialloc_flag B) 1 1 /\ val_mem im_segs m' (as_ialloc_flag B + 1) 1 0 /\
  val_mem im_segs m' (as_ialloc_w B) 8 4096 /\ val_mem im_segs m' (as_ialloc_w B + 8) 8 (as_ialloc_w B + 16) /\
  (forall a, as_ialloc_lo B <= a < as_ialloc_w B \/ as_ialloc_w B + 16 <= a < as_ialloc_hi B ->
     mbyte im_segs m' a = Some (Z_to_bv 8 0)).
Definition FV_IAL : Prop := forall W m, dg_ial_post W m <-> ial_post_cf W m.
Definition FV_ZONE3 : Prop :=
  forall ly x sz, im_img_cover ly -> 0 <= sz -> in_app x sz -> zdisjoint (x, sz) (ly_img ly) -> dg_zone3 x sz.

(* ================================================================================================================ *)
(* 1. Byte helpers over im_segs.                                                                                    *)
Lemma aview_some_cf : forall H mem a v,
aview im_segs H mem a = Some v <-> exists b, mbyte im_segs (mrestrict H mem) a = Some b /\ bv_unsigned b = v.
Proof.
intros H mem a v. unfold aview. destruct (mbyte im_segs (mrestrict H mem) a) as [b|]; cbn.
- split; [intros E; injection E as <-; exists b; auto | intros (b' & E & <-); congruence].
- split; [discriminate | intros (b & E & _); discriminate].
Qed.
Lemma aview_byte_cf : forall H mem a v,
aview im_segs H mem a = Some v -> mbyte im_segs (mrestrict H mem) a = Some (Z_to_bv 8 v).
Proof.
intros H mem a v Hv. apply aview_some_cf in Hv as (b & E & <-). rewrite Z_to_bv_bv_unsigned. exact E.
Qed.
Lemma aview_vis_byte_cf : forall H mem a, aview im_segs H mem a <> None ->
exists b, aview im_segs H mem a = Some b /\ 0 <= b < 256 /\ mbyte im_segs (mrestrict H mem) a = Some (Z_to_bv 8 b).
Proof.
intros H mem a Hv. destruct (aview im_segs H mem a) as [b|] eqn:E; [|exfalso; exact (Hv eq_refl)].
exists b. split; [reflexivity|]. pose proof E as E'. apply aview_some_cf in E as (b8 & Hb & <-).
pose proof (bv_unsigned_in_range 8 b8) as R. change (bv_modulus 8) with 256 in R. split; [lia|]. exact (aview_byte_cf _ _ _ _ E').
Qed.
Lemma val_mem_vis_cf : forall H mem a (w : nat) v i, val_mem im_segs (mrestrict H mem) a w v -> 0 <= i < Z.of_nat w ->
aview im_segs H mem (a + i) <> None.
Proof.
intros H mem a w v i Hv Hi. unfold aview. replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite (Hv (Z.to_nat i) ltac:(lia)). discriminate.
Qed.
(* A constant cell holds in the memory of an ARmcf view. *)
Lemma const_at_val : forall ly S Hp (W : world im_segs) mem a (w : nat) v,
ARmcf B ly S Hp (aview im_segs (w_H W) mem) -> const_at ly a w v -> val_mem im_segs (mrestrict (w_H W) mem) a w v.
Proof.
intros ly S Hp W mem a w v M (e & Hin & Ea). rewrite <- Ea.
exact (cell_holds_val_mem im_segs B ly (w_H W) mem e w (ANum v) (proj1 (Forall_forall _ _) (amc_const _ _ _ _ _ M) _ Hin)).
Qed.

(* ================================================================================================================ *)
(* 2. Geometry of ARmcf (the cf twins of YFf0 / YFfl's section facts).                                              *)
Section g.
Variables (ly : alayout) (S : astate) (Hp : list Z) (rd : reader).
Hypothesis M : ARmcf B ly S Hp rd.

Lemma EA_cf : forall y d, In y (st_chunks S) -> aeval B ly (aoff (sptr_exp (ck_beg y)) d) = ck_base B ly y + d.
Proof.
intros y d Hy. pose proof (chunk_facts_cf B ly S Hp rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia.
Qed.
Lemma EA2_cf : forall y d d', In y (st_chunks S) -> aeval B ly (aoff (aoff (sptr_exp (ck_beg y)) d) d') = ck_base B ly y + d + d'.
Proof.
intros y d d' Hy. pose proof (chunk_facts_cf B ly S Hp rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia.
Qed.

Lemma ext_rounded_cf : forall k, In k (st_chunks S) ->
ck_rz k + (ck_n k + 7) / 8 * 8 <= ck_extent k /\ 1 <= ck_n k /\ 0 <= (ck_n k + 7) / 8 /\
ck_n k <= (ck_n k + 7) / 8 * 8 < ck_n k + 8.
Proof.
intros k Hk. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (_ & _ & _ & _ & G5 & _ & G7 & G8 & GG). unfold ck_n.
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
pose proof (rounded_size_bounds (ck_req k) ltac:(lia)) as [R1 R2].
assert (DV : (req_size (ck_req k) + 7) / 8 * 8 <= rounded_size (ck_req k) /\ req_size (ck_req k) <= (req_size (ck_req k) + 7) / 8 * 8 < req_size (ck_req k) + 8).
{ pose proof (Z.div_mod (req_size (ck_req k) + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (req_size (ck_req k) + 7) 8 ltac:(lia)).
  apply Z.mod_divide in R2 as [q Hq]; [|lia]. nia. }
assert (RZX : ck_rz k + rounded_size (ck_req k) <= ck_extent k).
{ unfold ck_extent, ck_rz. destruct (from_primary (ck_req k)) eqn:P.
  - pose proof (primary_geometry (ck_req k) ltac:(lia) P) as (_ & [_ P2] & _). unfold needed_size in P2. rewrite P in P2. unfold needed_primary in P2. lia.
  - pose proof (secondary_geometry (ck_req k) ltac:(lia) P) as (_ & S2 & _ & [S4 _] & _). unfold needed_primary in S2.
    pose proof (rz_size_bounds (ck_req k)). lia. }
pose proof (Z.div_pos (req_size (ck_req k) + 7) 8). lia.
Qed.

Lemma u_al8_cf : forall k, In k (st_chunks S) ->
sptr_addr B ly (ck_user k) mod 8 = 0 /\ ck_base B ly k mod 8 = 0 /\ ck_rz k mod 8 = 0.
Proof.
intros k Hk. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (_ & _ & G3 & G4 & _ & G6 & _). rewrite G4.
apply Z.mod_divide in G3 as [q Hq]; [|lia]. apply Z.mod_divide in G6 as [q' Hq']; [|lia]. rewrite Hq, Hq'.
dsplits; apply Z.mod_divide; try lia; [exists (2 * q + 2 * q') | exists (2 * q) | exists (2 * q')]; lia.
Qed.

Lemma batch_geom_cf : forall b2, In b2 (all_batches S) ->
exists x, ly_space ly + b_self b2 = region_base ly kBatchClass + x /\ 0 <= x /\ x mod kBatchBytes = 0 /\
x + kBatchBytes <= rg_alloc_user (reg S kBatchClass) /\
rg_alloc_user (reg S kBatchClass) <= rg_mapped_user (reg S kBatchClass) <= kFreeArrayOffset /\
In x (batch_offs S kBatchClass).
Proof.
intros b2 Hb2. pose proof (amc_wf _ _ _ _ _ M) as WF.
pose proof (wfc_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (x := b_self b2 - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b2; auto).
pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wrc_alloc _ _ _ _ _ _ CL) as AL. pose proof (wrc_alloc_al _ _ _ _ _ _ CL) as AA.
pose proof (mapped_bound_cf (as_universe B) 0 0 0 S kBatchClass WF ltac:(unfold kBatchClass; lia)) as MB.
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2, AA. unfold kBatchBytes.
assert (XB : x + 8192 <= rg_alloc_user (reg S kBatchClass)).
{ apply Z.mod_divide in X2 as [q Hq]; [|lia]. apply Z.mod_divide in AA as [q' Hq']; [|lia]. assert (q < q') by nia. nia. }
exists x. dsplits; try assumption; try lia. unfold region_base. subst x. lia.
Qed.

Lemma SX_cf : forall i j x y, nth_error (static_extents ly) i = Some x -> nth_error (static_extents ly) j = Some y -> i <> j ->
zdisjoint x y.
Proof.
intros i j x y Hi Hj Hne. pose proof (amc_layout _ _ _ _ _ M) as LO. destruct (Nat.lt_ge_cases i j).
- exact (YFfl.pairwise_nth zdisjoint _ i j x y (lo_disj _ LO) Hi Hj H).
- apply zdisjoint_sym. apply (YFfl.pairwise_nth zdisjoint _ j i y x (lo_disj _ LO) Hj Hi). lia.
Qed.
Lemma SECX_cf : forall e j y, In e (sec_extents ly S) -> nth_error (static_extents ly) j = Some y -> zdisjoint e y.
Proof.
intros e j y He Hj. eapply (pairwise_In zdisjoint _ e y (sec_extents ly S) (static_extents ly) eq_refl (proj2 (amc_placed _ _ _ _ _ M)) He).
eapply nth_error_In. exact Hj.
Qed.
Lemma ext_zone_cf : forall y, In y (st_chunks S) ->
(exists c, 1 <= c <= 30 /\ region_base ly c <= ck_base B ly y /\ ck_base B ly y + ck_extent y <= region_base ly c + 2 ^ 32 /\
  ly_prim ly <= region_base ly c /\ region_base ly c + 2 ^ 32 <= ly_prim ly + kPrimResvSize) \/
(exists r, ck_beg y = PSec r kPage /\ ck_base B ly y = ly_sec ly r + kPage /\ In (ly_sec ly r, ck_extent y + kPage) (sec_extents ly S)).
Proof.
intros y Hy. pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (chunk_facts_cf B ly S Hp rd y M Hy) as (G1 & G2 & _ & _ & _ & _ & _ & _ & GG).
destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG].
- left. cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal & Gm).
  pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1 & R2 & _). exists (prim_class o).
  unfold kFreeArrayOffset in Gm. dsplits; lia.
- right. destruct GG as (-> & _ & Gbase & Gext & Gin & _). exists r. dsplits; [reflexivity | lia |].
  replace (ck_extent y + kPage) with (sec_map_size (ck_req y)) by lia. exact Gin.
Qed.
Lemma anyX_cf : forall y j e, In y (st_chunks S) -> nth_error (static_extents ly) j = Some e -> (j <> 0)%nat ->
zdisjoint (ck_base B ly y, ck_extent y) e.
Proof.
intros y j e Hy Hj Hne. destruct (ext_zone_cf y Hy) as [(c & Hc & X1 & X2 & X3 & X4)|(r & Ebk & Xb & Xin)].
- pose proof (SX_cf 0 j _ e eq_refl Hj ltac:(lia)) as DJ. unfold zdisjoint in DJ |- *. cbn [fst snd] in DJ |- *. lia.
- pose proof (SECX_cf _ j e Xin Hj) as DJ. unfold zdisjoint, kPage in *. cbn [fst snd] in DJ |- *. lia.
Qed.

Lemma batch_vs_chunk_cf : forall b2 x, In b2 (all_batches S) -> In x (st_chunks S) ->
zdisjoint (ly_space ly + b_self b2, kBatchBytes) (ck_base B ly x, ck_extent x).
Proof.
intros b2 x Hb2 Hx. pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (amc_layout _ _ _ _ _ M) as LO.
destruct (batch_geom_cf b2 Hb2) as (xb & Eb & Pb & Ab & Ub & [AU MU] & INB).
pose proof (chunk_facts_cf B ly S Hp rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (wfc_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
pose proof (wrc_nodup _ _ _ _ _ _ CL) as ND. rewrite app_assoc in ND. apply NoDup_app_iff in ND as (_ & ND & _).
apply NoDup_app_iff in ND as (_ & _ & NDx).
unfold zdisjoint. cbn [fst snd]. rewrite Eb.
destruct (ck_beg x) as [|o|r o|c p] eqn:Ebx; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & Gxm & Gxs & Gal).
  destruct (Z.eq_dec (prim_class o) kBatchClass) as [Ec|Hc].
  + pose proof (In_chunk_offs S x o Hx Ebx) as IK. rewrite Ec in *. set (xk := o - region_off kBatchClass) in *.
    assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in *.
    assert (xk <> xb). { intros E. apply (NDx xk); [exact IK | rewrite E; exact INB]. }
    unfold kBatchBytes in *. apply Z.mod_divide in Gxm as [q1 Hq1]; [|lia]. apply Z.mod_divide in Ab as [q2 Hq2]; [|lia].
    assert (q1 <> q2) by (intros E; subst; lia). nia.
  + pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1' & R2' & _).
    unfold region_base, kBatchBytes, kFreeArrayOffset in *. rewrite !region_off_eq in * by (unfold kBatchClass; lia). unfold kBatchClass in *.
    destruct (Z.lt_ge_cases (prim_class o) 24).
    * pose proof (Z.mul_le_mono_nonneg_r (prim_class o + 1) 24 (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
    * pose proof (Z.mul_le_mono_nonneg_r (24 + 1) (prim_class o) (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
  pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & _).
  pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req x)) (ly_prim ly, kPrimResvSize) (sec_extents ly S)
    (static_extents ly) eq_refl (proj2 (amc_placed _ _ _ _ _ M)) Gin
    ltac:(unfold static_extents, owned_extents; cbn; tauto)) as DJ.
  unfold zdisjoint, kPage, kBatchBytes, kFreeArrayOffset in *. cbn [fst snd] in DJ. unfold region_base in *. lia.
Qed.
End g.

(* A byte off the image window that the view shows is present (the ledger puts every segment in the window). *)
Lemma vis_present_cf : forall ly S md H mem a, ALedger_cf im_segs ly S md -> layout_ok ly -> 0 <= a < 2 ^ 64 ->
(a < kImgLo \/ kImgEnd <= a) -> aview im_segs H mem a <> None -> apresent H mem a.
Proof.
intros ly S md H mem a L LO Ha Hoff Hv. apply (aview_present_cf im_segs ly S md H mem a L Ha); [|exact Hv].
pose proof (lo_img _ LO) as (I1 & I2 & I3 & _). unfold in_zr. lia.
Qed.

(* ================================================================================================================ *)
(* 3. The view section (DGif1.v:158-582 over ARmcf).                                                                *)
Section c.
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world im_segs) (mem : word -> option byte) (md : Model).
Local Notation rd0 := (aview im_segs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation q := (st_qthread S).

Lemma cell_state_cf : ARmcf B ly S Hp rd0 -> forall c e (w : nat) e', In c (acells_cf B ly S) -> c = ACell e w (AV e') ->
val_mem im_segs m0 (aeval B ly e) w (aeval B ly e').
Proof.
intros M c e w e' Hin ->. apply (cell_holds_val_mem im_segs B ly (w_H W) mem e w e').
exact (proj1 (Forall_forall _ _) (amc_cells _ _ _ _ _ M) _ Hin).
Qed.
Lemma cell_stateZ_cf : ARmcf B ly S Hp rd0 -> forall c e (w : nat) x, In c (acells_cf B ly S) -> c = ACell e w (AV (ANum x)) ->
val_mem im_segs m0 (aeval B ly e) w x.
Proof. intros M c e w x Hin E. exact (cell_state_cf M c e w (ANum x) Hin E). Qed.
Lemma vis_range_cf : ARmcf B ly S Hp rd0 -> forall e len i,
In (e, len) (ajunk_cf B ly S) \/ In (e, len) (aareas S) \/ In (e, len) (aclient S) ->
0 <= i < len -> rd0 (aeval B ly e + i) <> None.
Proof.
intros M e len i Hin Hi. destruct Hin as [Hin|[Hin|Hin]].
- exact (proj1 (Forall_forall _ _) (amc_junk _ _ _ _ _ M) _ Hin i Hi).
- exact (proj1 (Forall_forall _ _) (amc_areas _ _ _ _ _ M) _ Hin i Hi).
- exact (proj1 (Forall_forall _ _) (amc_client _ _ _ _ _ M) _ Hin i Hi).
Qed.
Lemma quar_In_cf : forall c, In c (quar_cells S) -> In c (acells_cf B ly S).
Proof. intros c Hc. unfold acells_cf. rewrite !in_app_iff. do 4 right. left. exact Hc. Qed.

(* dn_unw *)
Lemma unw_cf : ARmcf B ly S Hp rd0 -> val_mem im_segs m0 (T + t_unwinding) 1 0.
Proof.
intros M. replace (T + t_unwinding) with (aeval B ly (AT t_unwinding)) by reflexivity.
eapply (cell_stateZ_cf M); [|reflexivity]. unfold acells_cf. rewrite !in_app_iff. do 8 right. left. reflexivity.
Qed.

(* dn_ial: the internal allocator's cells at st_internal_inited S = true *)
Lemma ial_post_of_ARm_cf : ARmcf B ly S Hp rd0 -> st_internal_inited S = true -> ial_post_cf W mem.
Proof.
intros M HI.
assert (IN : forall c, In c (ialloc_cells B S) -> In c (acells_cf B ly S))
  by (intros c Hc; unfold acells_cf; rewrite !in_app_iff; do 7 right; left; exact Hc).
unfold ialloc_cells in IN. rewrite HI in IN. cbv zeta in IN.
unfold ial_post_cf. cbv zeta. dsplits.
- replace (as_ialloc_flag B) with (aeval B ly (ANum (as_ialloc_flag B))) at 1 by reflexivity.
  eapply (cell_stateZ_cf M); [apply IN; left; reflexivity | reflexivity].
- replace (as_ialloc_flag B + 1) with (aeval B ly (ANum (as_ialloc_flag B + 1))) by reflexivity.
  eapply (cell_stateZ_cf M); [apply IN; right; left; reflexivity | reflexivity].
- replace (as_ialloc_w B) with (aeval B ly (AIal (as_ialloc_w B - as_ialloc_lo B))) at 1 by (cbn; lia).
  eapply (cell_stateZ_cf M); [apply IN; do 2 right; left; reflexivity | reflexivity].
- replace (as_ialloc_w B + 8) with (aeval B ly (AIal (as_ialloc_w B - as_ialloc_lo B + 8))) by (cbn; lia).
  replace (as_ialloc_w B + 16) with (aeval B ly (AIal (as_ialloc_w B - as_ialloc_lo B + 16))) by (cbn; lia).
  eapply (cell_state_cf M); [apply IN; do 3 right; left; reflexivity | reflexivity].
- intros a Ha. pose proof (amc_zero _ _ _ _ _ M) as ZR. unfold ialloc_zero in ZR. cbv zeta in ZR.
  apply Forall_cons_iff in ZR as [Z1 ZR]. apply Forall_cons_iff in ZR as [Z2 _].
  assert (R : rd0 a = Some 0).
  { destruct Ha as [Ha|Ha].
    - replace a with (aeval B ly (AIal 0) + (a - as_ialloc_lo B)) by (cbn; lia). apply Z1. cbn [snd]. lia.
    - replace a with (aeval B ly (AIal (as_ialloc_w B - as_ialloc_lo B + 16)) + (a - (as_ialloc_w B + 16))) by (cbn; lia).
      apply Z2. cbn [snd]. lia. }
  exact (aview_byte_cf _ _ _ _ R).
Qed.

(* dn_inst: the instance's two quarantine bounds are constant cells *)
Lemma inst_cf : FQ_CONST -> ARmcf B ly S Hp rd0 ->
val_mem im_segs m0 (as_inst B + o_q_max) 8 kQuarantineMax /\ val_mem im_segs m0 (as_inst B + o_q_maxcache) 8 kQuarantineCacheMax.
Proof.
intros HI M. destruct (HI ly) as (C1 & C2 & _ & _).
split; [exact (const_at_val ly S Hp W mem _ _ _ M C1) | exact (const_at_val ly S Hp W mem _ _ _ M C2)].
Qed.

(* dv_junk: the thread's stats words are thread junk; the thread object is an owned extent, off the image *)
Lemma junk_pres_cf : ARmcf B ly S Hp rd0 -> ALedger_cf im_segs ly S md ->
forall a, T + t_stats + 24 <= a < T + t_stats + 40 -> apresent (w_H W) mem a.
Proof.
intros M L a Ha. pose proof (amc_layout _ _ _ _ _ M) as LO.
assert (OW : Exists (in_zr a) (owned_extents ly)).
{ apply Exists_exists. exists (ly_T ly, kThreadObjSize). split; [unfold owned_extents; cbn; tauto|].
  unfold in_zr, t_stats, kThreadObjSize in *. cbn [fst snd]. lia. }
destruct (owned_extents_bound ly a LO OW) as (AA & _ & NI).
apply (aview_present_cf im_segs ly S md (w_H W) mem a L ltac:(pose proof (app_addr_below_ceil a AA); ceil; unfold ASAN_CEIL in *; lia) NI).
replace a with (aeval B ly (AT t_stats) + (a - (T + t_stats))) by (cbn; lia).
apply (vis_range_cf M (AT t_stats) (t_unwinding - t_stats)); [|unfold t_stats, t_unwinding in *; lia].
left. unfold ajunk_cf. right. right. do 5 (apply in_or_app; right). apply in_or_app. left. unfold thread_junk. cbn. tauto.
Qed.

(* The quarantine's byte sums (Wf_cf's quarantine part). *)
Lemma items_n_pos_cf : ARmcf B ly S Hp rd0 -> forall b x, In b (all_batches S) -> In x (b_items b) -> 1 <= ck_n x.
Proof.
intros M b x Hb Hx. pose proof (amc_wf _ _ _ _ _ M) as WF.
pose proof (proj1 (Forall_forall _ _) (wq_items _ (wfc_quarantine _ _ _ _ _ WF)) x ltac:(unfold q_items; apply in_flat_map; exists b; auto)) as [X1 _].
pose proof (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ WF) x X1) as [N _]. unfold ck_n. pose proof (req_size_bounds (ck_req x) ltac:(lia)). lia.
Qed.
Lemma b_bytes_ge_cf : ARmcf B ly S Hp rd0 -> forall b, In b (all_batches S) -> kBatchBytes <= b_bytes b.
Proof.
intros M b Hb. unfold b_bytes.
assert (G : forall l, incl l (b_items b) -> 0 <= fold_right (fun k acc => ck_n k + acc) 0 l).
{ induction l as [|x t IH]; intros Hl; cbn; [lia|]. pose proof (items_n_pos_cf M b x Hb (Hl x (or_introl eq_refl))).
  pose proof (IH ltac:(intros y Hy; apply Hl; right; exact Hy)). lia. }
pose proof (G (b_items b) ltac:(intros y Hy; exact Hy)). lia.
Qed.
Lemma sum_bytes_ge_cf : ARmcf B ly S Hp rd0 -> forall l, incl l (all_batches S) -> 0 <= sum_bytes l.
Proof.
intros M. induction l as [|b t IH]; intros Hl; cbn; [unfold sum_bytes; cbn; lia|]. unfold sum_bytes in *. cbn.
pose proof (b_bytes_ge_cf M b (Hl b (or_introl eq_refl))). pose proof (IH ltac:(intros y Hy; apply Hl; right; exact Hy)).
unfold kBatchBytes in *. lia.
Qed.
Lemma sum_len_cf : ARmcf B ly S Hp rd0 -> forall l, incl l (all_batches S) -> 8192 * Z.of_nat (length l) <= sum_bytes l.
Proof.
intros M. induction l as [|b t IH]; intros Hl; [cbn; unfold sum_bytes; cbn; lia|].
pose proof (b_bytes_ge_cf M b (Hl b (or_introl eq_refl))) as Hb. pose proof (IH ltac:(intros y Hy; apply Hl; right; exact Hy)) as Ht.
unfold sum_bytes in *. cbn [fold_right length]. unfold kBatchBytes in Hb. lia.
Qed.
(* dv_qb, from qtight (the Deallocate premise's meter) *)
Lemma qb_cf : ARmcf B ly S Hp rd0 -> qtight S -> 0 <= qc_bytes q <= kQuarantineCacheMax.
Proof.
intros M QT. pose proof (amc_wf _ _ _ _ _ M) as WF.
pose proof (wq_bytes_t _ (wfc_quarantine _ _ _ _ _ WF)) as QE.
pose proof (sum_bytes_ge_cf M (qc_list q) ltac:(intros y Hy; unfold all_batches; apply in_app_iff; left; exact Hy)) as S1.
pose proof (proj1 QT). lia.
Qed.

(* The geometry of a batch. *)
Lemma batch_range_cf : ARmcf B ly S Hp rd0 -> forall b, In b (all_batches S) ->
ly_space ly <= ly_space ly + b_self b /\ ly_space ly + b_self b + kBatchBytes <= ly_space ly + kSpaceSize /\
(ly_space ly + b_self b) mod 8192 = 0 /\ kHighMemBeg <= ly_space ly + b_self b /\ ly_space ly + b_self b + kBatchBytes <= ASAN_CEIL.
Proof.
intros M b Hb. pose proof (amc_layout _ _ _ _ _ M) as LO.
destruct (batch_geom_cf ly S Hp rd0 M b Hb) as (x & Ex & Px & Ax & Ux & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5).
assert (RB : region_base ly kBatchClass = ly_space ly + 24 * 2 ^ 32).
{ unfold region_base. rewrite region_off_eq by (unfold kBatchClass; lia). unfold kBatchClass. lia. }
rewrite RB in Ex, R3, R4, R5.
dsplits.
- lia.
- unfold kBatchBytes, kSpaceSize, kFreeArrayOffset in *. lia.
- rewrite Ex. apply Z.mod_divide in R3 as [c Hc]; [|lia]. apply Z.mod_divide in Ax as [c' Hc']; [|unfold kBatchBytes; lia].
  rewrite Hc, Hc'. unfold kBatchBytes. apply Z.mod_divide; [lia|]. exists (c * 8 + c'). lia.
- lia.
- unfold kBatchBytes, kFreeArrayOffset in *. lia.
Qed.
Lemma qf_range_cf : ARmcf B ly S Hp rd0 -> 0 <= DGgiC.QFv ly q < 2 ^ 64.
Proof.
intros M. unfold DGgiC.QFv. destruct (qc_list q) as [|b0 t] eqn:E; [lia|].
assert (Hb0 : In b0 (all_batches S)) by (unfold all_batches; rewrite E; left; reflexivity).
pose proof (batch_range_cf M b0 Hb0) as (_ & _ & _ & H4 & H5). ceil. unfold kHighMemBeg, kBatchBytes, ASAN_CEIL in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The block [p] of size [n] and its chunk [k].                                                                    *)
Variables (p : sptr) (n : Z) (k : chunk).
Local Notation pa := (sptr_addr B ly p).
Local Notation nn := (req_size n).
Definition KVc : Prop :=
ARmcf B ly S Hp rd0 /\ ALedger_cf im_segs ly S md /\ In k (st_chunks S) /\ ck_state k = CAllocated /\ ck_user k = p /\ ck_req k = n.
Lemma Epa_cf : KVc -> pa = ck_base B ly k + ck_rz k.
Proof.
intros (M & _ & Hk & _ & Hu & _). pose proof (chunk_facts_cf B ly S Hp rd0 k M Hk) as (_ & _ & _ & G4 & _). rewrite <- Hu. exact G4.
Qed.
Lemma Enn_cf : KVc -> nn = ck_n k.
Proof. intros (_ & _ & _ & _ & _ & Hr). unfold ck_n. rewrite Hr. reflexivity. Qed.
Lemma hdr_In_cf : KVc -> forall c, In c (chunk_cells k) -> In c (acells_cf B ly S).
Proof.
intros (_ & _ & Hk & _) c Hc. unfold acells_cf. rewrite !in_app_iff. do 2 right. left. apply in_flat_map. exists k.
split; [exact Hk | exact Hc].
Qed.
(* dv_nonnull *)
Lemma nonnull_cf : KVc -> p <> PNull.
Proof.
intros (M & _ & Hk & _ & Hu & _) E. pose proof (chunk_facts_cf B ly S Hp rd0 k M Hk) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
rewrite <- Hu in E. unfold ck_user, padd in E. destruct (ck_beg k); try discriminate E. destruct GG.
Qed.
Definition hb1c : Z := match rd0 (pa - 15) with Some b => b | None => 0 end.
Lemma hb1_facts_cf : KVc -> rd0 (pa - 15) = Some hb1c /\ 0 <= hb1c < 256 /\ Z.land hb1c 127 = 17.
Proof.
intros HK. pose proof HK as (M & _ & Hk & Hst & _).
assert (C : cell_holds B ly rd0 (ACell (aoff (aoff (sptr_exp (ck_beg k)) (ck_rz k - kChunkHeaderSize)) 1) 1 (AVmask 127 17))).
{ apply (proj1 (Forall_forall _ _) (amc_cells _ _ _ _ _ M)). apply (hdr_In_cf HK). unfold chunk_cells. apply in_app_iff. left. cbn. tauto. }
cbn [cell_holds c_at c_val c_w] in C. rewrite (EA2_cf ly S Hp rd0 M k _ _ Hk) in C. unfold kChunkHeaderSize in C.
replace (ck_base B ly k + (ck_rz k - 16) + 1) with (pa - 15) in C by (rewrite (Epa_cf HK); lia).
destruct C as (b & Hb & Hm). unfold hb1c. rewrite Hb.
destruct (aview_vis_byte_cf (w_H W) mem (pa - 15) ltac:(rewrite Hb; discriminate)) as (b' & E' & R' & _).
rewrite Hb in E'. injection E' as <-. auto.
Qed.
Lemma hw_val_cf : KVc -> val_mem im_segs m0 (pa - 16) 4 (2 + 256 * hb1c) /\ val_mem im_segs m0 (pa - 12) 4 nn.
Proof.
intros HK. pose proof HK as (M & _ & Hk & Hst & _). pose proof (hb1_facts_cf HK) as (HB & HR & _).
pose proof (Epa_cf HK) as EP. pose proof (Enn_cf HK) as EN.
assert (EH : aeval B ly (aoff (sptr_exp (ck_beg k)) (ck_rz k - kChunkHeaderSize)) = pa - 16).
{ rewrite (EA_cf ly S Hp rd0 M k _ Hk). rewrite EP. unfold kChunkHeaderSize. lia. }
assert (EH2 : forall d, aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) (ck_rz k - kChunkHeaderSize)) d) = pa - 16 + d).
{ intros d. rewrite (EA2_cf ly S Hp rd0 M k _ _ Hk). rewrite EP. unfold kChunkHeaderSize. lia. }
assert (V0 : val_mem im_segs m0 (pa - 16) 1 2).
{ rewrite <- EH. eapply (cell_stateZ_cf M); [apply (hdr_In_cf HK); unfold chunk_cells; apply in_app_iff; left; left; reflexivity|].
  unfold z1, c1, hdr_state. rewrite Hst. reflexivity. }
assert (V2 : val_mem im_segs m0 (pa - 14) 2 0).
{ replace (pa - 14) with (pa - 16 + 2) by lia. rewrite <- (EH2 2).
  eapply (cell_stateZ_cf M); [apply (hdr_In_cf HK); unfold chunk_cells; apply in_app_iff; left; do 2 right; left; reflexivity|]. reflexivity. }
assert (V4 : val_mem im_segs m0 (pa - 12) 4 (ck_n k)).
{ replace (pa - 12) with (pa - 16 + 4) by lia. rewrite <- (EH2 4).
  eapply (cell_stateZ_cf M); [apply (hdr_In_cf HK); unfold chunk_cells; apply in_app_iff; left; do 3 right; left; reflexivity|]. reflexivity. }
split; [|rewrite EN; exact V4].
intros i Hi.
assert (LB : forall v (w j : nat), YO0f.le_byte v w j = (v mod 2 ^ (8 * Z.of_nat w)) / 2 ^ (8 * Z.of_nat j) mod 256).
{ intros v w j. unfold YO0f.le_byte. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
destruct i as [|[|[|[|i]]]]; [| | | |lia].
- rewrite (V0 0%nat ltac:(lia)). do 2 f_equal. rewrite !LB. change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
  change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite !Z.div_1_r. Z.div_mod_to_equations. nia.
- change (Z.of_nat 1) with 1. replace (pa - 16 + 1) with (pa - 15) by lia. rewrite (aview_byte_cf _ _ _ _ HB). do 2 f_equal.
  rewrite !LB. change (2 ^ (8 * Z.of_nat 4)) with 4294967296. change (2 ^ (8 * Z.of_nat 1)) with 256. Z.div_mod_to_equations. nia.
- replace (pa - 16 + Z.of_nat 2) with (pa - 14 + Z.of_nat 0) by lia. rewrite (V2 0%nat ltac:(lia)). do 2 f_equal.
  rewrite !LB. change (2 ^ (8 * Z.of_nat 4)) with 4294967296. change (2 ^ (8 * Z.of_nat 2)) with 65536. change (2 ^ (8 * Z.of_nat 0)) with 1.
  rewrite !Z.div_1_r. Z.div_mod_to_equations. nia.
- replace (pa - 16 + Z.of_nat 3) with (pa - 14 + Z.of_nat 1) by lia. rewrite (V2 1%nat ltac:(lia)). do 2 f_equal.
  rewrite !LB. change (2 ^ (8 * Z.of_nat 4)) with 4294967296. change (2 ^ (8 * Z.of_nat 2)) with 65536.
  change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ (8 * Z.of_nat 3)) with 16777216. Z.div_mod_to_equations. nia.
Qed.
(* dv_hdr *)
Lemma hdr_cf : KVc -> exists hb1, 0 <= hb1 < 256 /\ Z.land hb1 127 = 17 /\
val_mem im_segs m0 (pa - 16) 4 (2 + 256 * hb1) /\ val_mem im_segs m0 (pa - 12) 4 nn.
Proof.
intros HK. pose proof (hb1_facts_cf HK) as (_ & HR & HM). pose proof (hw_val_cf HK) as [W1 W2].
exists hb1c. exact (conj HR (conj HM (conj W1 W2))).
Qed.
Lemma user_vis_cf : KVc -> forall a, pa <= a < pa + 8 -> rd0 a <> None.
Proof.
intros HK a Ha. pose proof HK as (M & _ & Hk & Hst & Hu & _). pose proof (Enn_cf HK) as EN. pose proof (Epa_cf HK) as EP.
pose proof (ext_rounded_cf ly S Hp rd0 M k Hk) as (ER & NN1 & NN2 & NN3). rewrite <- EN in ER, NN1, NN2, NN3.
destruct (Z_lt_le_dec a (pa + nn)) as [L|L].
- replace a with (aeval B ly (sptr_exp (ck_user k)) + (a - pa)) by (rewrite Hu; unfold sptr_addr; lia).
  apply (vis_range_cf M _ (ck_n k)); [|rewrite <- EN; lia]. do 2 right. unfold aclient. apply in_app_iff. left.
  apply in_flat_map. exists k. split; [exact Hk|]. unfold chunk_user. rewrite Hst. left. reflexivity.
- replace a with (aeval B ly (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k)) + (a - pa - nn))
    by (rewrite (EA_cf ly S Hp rd0 M k _ Hk), EP, EN; lia).
  apply (vis_range_cf M _ (ck_extent k - ck_rz k - ck_n k)); [|rewrite <- EN; lia].
  left. unfold ajunk_cf. right. right. rewrite !in_app_iff. do 2 right. left. apply in_flat_map. exists k. split; [exact Hk|].
  unfold chunk_junk. rewrite !in_app_iff. do 3 right. left. reflexivity.
Qed.
Lemma meta_vis_cf : KVc -> forall a, pa - 16 <= a < pa -> rd0 a <> None.
Proof.
intros HK a Ha. pose proof HK as (M & _ & Hk & _). pose proof (hw_val_cf HK) as [V1 V2]. pose proof (Epa_cf HK) as EP.
destruct (Z_lt_le_dec a (pa - 12)) as [L1|L1].
{ replace a with (pa - 16 + (a - (pa - 16))) by lia. exact (val_mem_vis_cf _ _ _ _ _ (a - (pa - 16)) V1 ltac:(lia)). }
destruct (Z_lt_le_dec a (pa - 8)) as [L2|L2].
{ replace a with (pa - 12 + (a - (pa - 12))) by lia. exact (val_mem_vis_cf _ _ _ _ _ (a - (pa - 12)) V2 ltac:(lia)). }
replace a with (aeval B ly (aoff (sptr_exp (ck_beg k)) (ck_rz k - 8)) + (a - (pa - 8))) by (rewrite (EA_cf ly S Hp rd0 M k _ Hk), EP; lia).
apply (vis_range_cf M _ 8); [|lia]. left. unfold ajunk_cf. right. right. rewrite !in_app_iff. do 2 right. left.
apply in_flat_map. exists k. split; [exact Hk|].
unfold chunk_junk. rewrite !in_app_iff. right. left. left. reflexivity.
Qed.
Lemma shadow_vis_cf : KVc -> forall i, 0 <= i < DGgiC.CNT8v nn -> exists v, rd0 (DGgiC.SPv pa + i) = Some v.
Proof.
intros HK i Hi. pose proof HK as (M & _ & Hk & _ & Hu & _). pose proof (Enn_cf HK) as EN. pose proof (Epa_cf HK) as EP.
pose proof (amc_wf _ _ _ _ _ M) as WF.
pose proof (ext_rounded_cf ly S Hp rd0 M k Hk) as (ER & NN1 & NN2 & NN3).
pose proof (u_al8_cf ly S Hp rd0 M k Hk) as (U8 & B8 & R8).
pose proof (chunk_facts_cf B ly S Hp rd0 k M Hk) as (G1 & G2 & G3 & G4 & G5 & _).
unfold DGgiC.CNT8v, DGgiC.N8v in Hi. rewrite Z_div_mult in Hi by lia. rewrite <- EN in ER, NN1, NN2, NN3.
set (g := pa + 8 * i).
assert (FC : find_chunk_at B ly (st_chunks S) g = Some k).
{ apply (find_chunk_at_hit_cf B ly S Hp rd0 (st_chunks S) k g M ltac:(intros x Hx; exact Hx) (wfc_chunks_nodup _ _ _ _ _ WF) Hk).
  subst g. clear - EP Hi ER NN2 G5. rewrite EP. lia. }
assert (SH : ashadow B ly S g = Some (chunk_granule k ((g - ck_base B ly k) / 8))) by (unfold ashadow; rewrite FC; reflexivity).
assert (PC : exists c, pa = c * 8). { apply Z.mod_divide in U8 as [c Hc]; [|lia]. exists c. rewrite <- Hu. exact Hc. }
destruct PC as [c Hc].
pose proof (amc_shadow _ _ _ _ _ M g _ ltac:(subst g; rewrite Hc; replace (c * 8 + 8 * i) with ((c + i) * 8) by lia; apply Z_mod_mult) SH) as R.
eexists. rewrite <- R. f_equal. unfold shadow_addr, DGgiC.SPv. subst g.
rewrite Hc. replace (c * 8 + 8 * i) with ((c + i) * 8) by lia. rewrite !Z_div_mult by lia. lia.
Qed.
Lemma p_zone_cf : YGcfDIface.IMG_COVER -> FV_ZONE3 -> KVc -> dg_zone3 (pa - 16) (DGgiC.N8v nn + 16).
Proof.
intros HIMG HZ HK. pose proof HK as (M & L & Hk & _). pose proof (Enn_cf HK) as EN. pose proof (Epa_cf HK) as EP.
pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (chunk_facts_cf B ly S Hp rd0 k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (ext_rounded_cf ly S Hp rd0 M k Hk) as (ER & NN1 & NN2 & NN3). rewrite <- EN in ER, NN1, NN2, NN3.
apply (HZ ly); [exact (HIMG ly S md L) | unfold DGgiC.N8v; lia | |].
- unfold DGgiC.N8v. eapply in_app_sub; [exact G1 | lia | lia | lia].
- apply YFfl.zdisjoint_of_pointwise; [unfold DGgiC.N8v; lia | exact (proj1 (proj2 (lo_img _ LO))) |].
  intros y Hy. apply (proj1 (chunk_apart_cf B ly S Hp rd0 k y M Hk ltac:(unfold DGgiC.N8v in Hy; lia))).
Qed.
Lemma p_al_cf : KVc -> pa mod 16 = 0.
Proof.
intros HK. pose proof HK as (M & _ & Hk & _). pose proof (Epa_cf HK) as EP.
pose proof (chunk_facts_cf B ly S Hp rd0 k M Hk) as (_ & _ & G3 & _ & _ & G6 & _).
rewrite EP. apply Z.mod_divide in G3 as [c Hc]; [|lia]. apply Z.mod_divide in G6 as [c' Hc']; [|lia]. rewrite Hc, Hc'.
apply Z.mod_divide; [lia|]. exists (c + c'). lia.
Qed.
(* the request bound: the cf instance's chunk_ok_cf, never a literal; and the block fits below the ceiling *)
Lemma nn_range_cf : KVc -> 1 <= nn /\ 0 <= n < cf_malloc_max /\ nn < 2 ^ 47.
Proof.
intros HK. pose proof HK as (M & _ & Hk & _ & _ & Hr).
pose proof (chunk_facts_cf B ly S Hp rd0 k M Hk) as (G1 & G2 & _ & _ & G5 & _ & G7 & G8 & _).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3). rewrite Hr in Q1, Q2, Q3, G7, G8.
ceil. unfold in_app, ASAN_CEIL in *. lia.
Qed.
Lemma pstatic_cf : KVc -> DGgiC.PSTATIC ly pa nn.
Proof.
intros HK. pose proof HK as (M & _ & Hk & _). pose proof (Enn_cf HK) as EN. pose proof (Epa_cf HK) as EP.
pose proof (chunk_facts_cf B ly S Hp rd0 k M Hk) as (G1 & G2 & G3 & G4 & G5 & _).
pose proof (ext_rounded_cf ly S Hp rd0 M k Hk) as (ER & NN1 & NN2 & NN3). rewrite <- EN in ER, NN1, NN2, NN3.
pose proof (anyX_cf ly S Hp rd0 M k 8 _ Hk eq_refl ltac:(lia)) as D7. pose proof (anyX_cf ly S Hp rd0 M k 2 _ Hk eq_refl ltac:(lia)) as D2.
pose proof (anyX_cf ly S Hp rd0 M k 6 _ Hk eq_refl ltac:(lia)) as D6. pose proof (anyX_cf ly S Hp rd0 M k 4 _ Hk eq_refl ltac:(lia)) as D4.
pose proof (anyX_cf ly S Hp rd0 M k 5 _ Hk eq_refl ltac:(lia)) as D5. pose proof (anyX_cf ly S Hp rd0 M k 7 _ Hk eq_refl ltac:(lia)) as DD.
unfold zdisjoint in D7, D2, D6, D4, D5, DD. cbn [fst snd] in D7, D2, D6, D4, D5, DD.
unfold DGgiC.PSTATIC. cbv zeta. intros a Ha.
clear - Ha D7 D2 D6 D4 D5 DD EP ER G5. unfold DGgiC.N8v in *. dsplits; lia.
Qed.
(* dv_pres *)
Lemma pres_cf : KVc -> forall a, pa - 16 <= a < pa + 8 -> apresent (w_H W) mem a.
Proof.
intros HK a Ha. pose proof (Enn_cf HK) as EN. pose proof (Epa_cf HK) as EP. pose proof HK as (M & L & Hk & _).
pose proof (ext_rounded_cf ly S Hp rd0 M k Hk) as (ER & NN1 & NN2 & NN3). rewrite <- EN in ER, NN1, NN2, NN3.
pose proof (chunk_facts_cf B ly S Hp rd0 k M Hk) as (G1 & G2 & _ & _ & G5 & _).
destruct (chunk_apart_cf B ly S Hp rd0 k a M Hk ltac:(rewrite EP in Ha; lia)) as [NI _].
apply (aview_present_cf im_segs ly S md (w_H W) mem a L ltac:(unfold in_app in G1; ceil; unfold ASAN_CEIL in *; lia) NI).
destruct (Z_lt_le_dec a pa); [apply (meta_vis_cf HK); lia | apply (user_vis_cf HK); lia].
Qed.
(* The block's shadow is in the shadow region. *)
Lemma sh_range_cf : KVc -> SHADOW_OFF + 514 <= DGgiC.SPv pa /\ DGgiC.SPv pa + DGgiC.CNT8v nn <= kHighMemBeg.
Proof.
intros HK. pose proof HK as (M & _ & Hk & _). pose proof (Enn_cf HK) as EN. pose proof (Epa_cf HK) as EP.
pose proof (chunk_facts_cf B ly S Hp rd0 k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (ext_rounded_cf ly S Hp rd0 M k Hk) as (ER & NN1 & NN2 & NN3). rewrite <- EN in ER, NN1, NN2, NN3.
assert (LO16 : 4096 <= ck_base B ly k) by (clear - G1; unfold in_app in G1; lia).
unfold DGgiC.SPv, DGgiC.CNT8v, DGgiC.N8v. rewrite Z_div_mult by lia.
pose proof (Z.div_le_mono 4112 pa 8 ltac:(lia) ltac:(lia)) as S1. change (4112 / 8) with 514 in S1.
assert (HE : pa + (nn + 7) / 8 * 8 - 8 + 8 <= kHighMemEnd) by (ceil; unfold kHighMemEnd, ASAN_CEIL in *; lia).
assert (S2 : shadow_addr (pa + ((nn + 7) / 8 - 1) * 8) < kHighMemBeg).
{ unfold shadow_addr, SHADOW_OFF, kHighMemBeg, kHighMemEnd in *.
  pose proof (Z.div_le_mono (pa + ((nn + 7) / 8 - 1) * 8) (kHighMemEnd - 8) 8 ltac:(lia) ltac:(unfold kHighMemEnd; lia)). unfold kHighMemEnd in *. lia. }
unfold shadow_addr in S2. rewrite Z.div_add in S2 by lia.
split; lia.
Qed.
(* dv_shpres *)
Lemma shpres_cf : KVc -> forall a, dshadow pa nn a -> apresent (w_H W) mem a.
Proof.
intros HK a Ha. unfold dshadow in Ha. pose proof (sh_range_cf HK) as [S1 S2]. pose proof HK as (M & L & _).
pose proof (amc_layout _ _ _ _ _ M) as LO.
destruct (shadow_vis_cf HK (a - DGgiC.SPv pa) ltac:(lia)) as [v Hv]. replace (DGgiC.SPv pa + (a - DGgiC.SPv pa)) with a in Hv by lia.
apply (vis_present_cf ly S md (w_H W) mem a L LO); [unfold SHADOW_OFF, kHighMemBeg in *; lia | unfold SHADOW_OFF, kImgEnd in *; lia | rewrite Hv; discriminate].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The last batch of the thread's quarantine cache.                                                                 *)
Variables (lastb : batch) (initr : list batch).
Definition BVc : Prop := ARmcf B ly S Hp rd0 /\ ALedger_cf im_segs ly S md /\ rev (qc_list q) = lastb :: initr.
Lemma qlist0_cf : BVc -> qc_list q = rev initr ++ [lastb].
Proof. intros (_ & _ & Hrev). rewrite <- (rev_involutive (qc_list q)), Hrev. reflexivity. Qed.
Lemma lastb_in_cf : BVc -> In lastb (all_batches S).
Proof. intros HB. unfold all_batches. rewrite (qlist0_cf HB), !in_app_iff. left. right. left. reflexivity. Qed.
(* db_qc *)
Lemma qc_vals_cf : BVc -> val_mem im_segs m0 (T + t_qc) 8 (DGgiC.QSv q) /\ val_mem im_segs m0 (T + t_qc + 8) 8 (DGgiC.QFv ly q) /\
val_mem im_segs m0 (T + t_qc + 16) 8 (DGgiC.Bv ly lastb) /\ val_mem im_segs m0 (T + t_qc + 24) 8 (DGgiC.QBv q).
Proof.
intros (M & _ & Hrev).
assert (IN : forall c, In c (qc_cells (AT t_qc) q) -> In c (acells_cf B ly S)).
{ intros c Hc. apply quar_In_cf. unfold quar_cells. right. right. apply in_app_iff. left. exact Hc. }
unfold qc_cells in IN. dsplits.
- replace (T + t_qc) with (aeval B ly (AT t_qc)) by reflexivity. eapply (cell_stateZ_cf M); [apply IN; left; reflexivity | reflexivity].
- replace (T + t_qc + 8) with (aeval B ly (aoff (AT t_qc) 8)) by (cbn; lia).
  replace (DGgiC.QFv ly q) with (aeval B ly (match qc_list q with [] => ANum 0 | b :: _ => batch_exp b end))
    by (unfold DGgiC.QFv; destruct (qc_list q); reflexivity).
  eapply (cell_state_cf M); [apply IN; right; left; reflexivity | reflexivity].
- replace (T + t_qc + 16) with (aeval B ly (aoff (AT t_qc) 16)) by (cbn; lia).
  replace (DGgiC.Bv ly lastb) with (aeval B ly (match rev (qc_list q) with [] => ANum 0 | b :: _ => batch_exp b end))
    by (rewrite Hrev; reflexivity).
  eapply (cell_state_cf M); [apply IN; do 2 right; left; reflexivity | reflexivity].
- replace (T + t_qc + 24) with (aeval B ly (aoff (AT t_qc) 24)) by (cbn; lia).
  eapply (cell_stateZ_cf M); [apply IN; do 3 right; left; reflexivity | reflexivity].
Qed.
(* db_b *)
Lemma batch_vals_cf : BVc -> val_mem im_segs m0 (DGgiC.Bv ly lastb + 8) 8 (DGgiC.BBv lastb) /\
val_mem im_segs m0 (DGgiC.Bv ly lastb + 16) 8 (DGgiC.BCv lastb).
Proof.
intros HB. pose proof HB as (M & _). pose proof (qlist0_cf HB) as QL.
destruct (YFfl.batch_cells_snoc (rev initr) lastb lastb eq_refl) as (P & EP & _ & _).
assert (IN : forall c, In c (batch_cells [lastb]) -> In c (acells_cf B ly S)).
{ intros c Hc. apply quar_In_cf. unfold quar_cells. right. right. apply in_app_iff. left. unfold qc_cells. do 4 right.
  rewrite QL, EP. apply in_app_iff. right. exact Hc. }
cbn [batch_cells app] in IN. split.
- replace (DGgiC.Bv ly lastb + 8) with (aeval B ly (aoff (batch_exp lastb) 8)) by (unfold DGgiC.Bv; cbn; lia).
  eapply (cell_stateZ_cf M); [apply IN; right; left; reflexivity | reflexivity].
- replace (DGgiC.Bv ly lastb + 16) with (aeval B ly (aoff (batch_exp lastb) 16)) by (unfold DGgiC.Bv; cbn; lia).
  eapply (cell_stateZ_cf M); [apply IN; do 2 right; left; reflexivity | reflexivity].
Qed.
(* db_pres, the byte count and item count words *)
Lemma bcell_pres_cf : BVc -> forall a, DGgiC.Bv ly lastb + 8 <= a < DGgiC.Bv ly lastb + 24 -> apresent (w_H W) mem a.
Proof.
intros HB a Ha. pose proof HB as (M & L & _). pose proof (lastb_in_cf HB) as LB. pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (batch_range_cf M lastb LB) as (_ & _ & _ & H4 & H5). pose proof (batch_vals_cf HB) as [V5 V6].
apply (vis_present_cf ly S md (w_H W) mem a L LO);
  [ceil; unfold DGgiC.Bv, kHighMemBeg, ASAN_CEIL, kBatchBytes in *; lia | unfold DGgiC.Bv, kHighMemBeg, kImgEnd in *; lia|].
destruct (Z_lt_le_dec a (DGgiC.Bv ly lastb + 16)).
+ replace a with (DGgiC.Bv ly lastb + 8 + (a - (DGgiC.Bv ly lastb + 8))) by lia. eapply val_mem_vis_cf; [exact V5 | lia].
+ replace a with (DGgiC.Bv ly lastb + 16 + (a - (DGgiC.Bv ly lastb + 16))) by lia. eapply val_mem_vis_cf; [exact V6 | lia].
Qed.
(* db_pres, the slot word: batch_junk of a last batch with room *)
Lemma slot_pres_cf : BVc -> DGgiC.BCv lastb < kBatchSlots ->
forall a, DGgiC.SLOTv ly lastb <= a < DGgiC.SLOTv ly lastb + 8 -> apresent (w_H W) mem a.
Proof.
intros HB ROOM a Ha. pose proof HB as (M & L & _). pose proof (lastb_in_cf HB) as LB. pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (batch_range_cf M lastb LB) as (_ & _ & _ & H4 & H5).
unfold DGgiC.SLOTv, DGgiC.Bv, DGgiC.BCv, kBatchSlots in *.
apply (vis_present_cf ly S md (w_H W) mem a L LO);
  [ceil; unfold kHighMemBeg, ASAN_CEIL, kBatchBytes in *; lia | unfold kHighMemBeg, kImgEnd in *; lia|].
replace a with (aeval B ly (aoff (batch_exp lastb) (24 + 8 * Z.of_nat (length (b_items lastb))))
  + (a - (ly_space ly + b_self lastb + 24 + 8 * Z.of_nat (length (b_items lastb))))) by (cbn; lia).
apply (vis_range_cf M _ (kBatchBytes - 24 - 8 * Z.of_nat (length (b_items lastb)))); [|unfold kBatchBytes; lia].
left. unfold ajunk_cf. right. right. rewrite !in_app_iff. do 4 right. left. unfold quar_junk. apply in_flat_map.
exists lastb. split; [exact LB | left; reflexivity].
Qed.
(* db_range *)
Lemma brange_cf : BVc -> ly_space ly <= DGgiC.Bv ly lastb /\ DGgiC.Bv ly lastb + kBatchBytes <= ly_space ly + kSpaceSize /\
0 <= DGgiC.QFv ly q < 2 ^ 64 /\ DGgiC.Bv ly lastb mod 8192 = 0.
Proof.
intros HB. pose proof HB as (M & _). pose proof (lastb_in_cf HB) as LB.
pose proof (batch_range_cf M lastb LB) as (H1 & H2 & H3 & _). pose proof (qf_range_cf M) as QF.
unfold DGgiC.Bv. dsplits; first [assumption | lia].
Qed.
(* db_bounds: the byte sums of Wf_cf and qtight *)
Lemma bb_cf : BVc -> qtight S ->
0 <= DGgiC.BBv lastb /\ DGgiC.BBv lastb <= kQuarantineCacheMax /\ 8192 * DGgiC.QSv q <= kQuarantineCacheMax.
Proof.
intros HB QT. pose proof HB as (M & _). pose proof (qlist0_cf HB) as QL. pose proof (lastb_in_cf HB) as LB.
pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (wq_bytes_t _ (wfc_quarantine _ _ _ _ _ WF)) as QE.
pose proof (proj1 QT) as QT1.
assert (SUM : qc_bytes q = sum_bytes (rev initr) + b_bytes lastb).
{ rewrite QE, QL, sum_bytes_app. unfold sum_bytes at 2. cbn [fold_right]. lia. }
pose proof (sum_bytes_ge_cf M (rev initr) ltac:(intros y Hy; unfold all_batches; rewrite QL, !in_app_iff; tauto)) as S1.
pose proof (b_bytes_ge_cf M lastb LB) as S2.
pose proof (sum_len_cf M (qc_list q) ltac:(intros y Hy; unfold all_batches; apply in_app_iff; left; exact Hy)) as S3.
unfold DGgiC.BBv, DGgiC.QSv. unfold kBatchBytes in S2. lia.
Qed.
(* db_slots *)
Lemma slots_cf : BVc -> DGgiC.BCv lastb <= kBatchSlots.
Proof.
intros HB. pose proof HB as (M & _). pose proof (lastb_in_cf HB) as LB. pose proof (amc_wf _ _ _ _ _ M) as WF.
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wfc_quarantine _ _ _ _ _ WF)) lastb LB) as [_ H2].
unfold DGgiC.BCv. apply Nat2Z.inj_le in H2. rewrite Z2Nat.id in H2 by (unfold kBatchSlots; lia). exact H2.
Qed.
(* db_disj *)
Lemma pbdisj_cf : KVc -> rev (qc_list q) = lastb :: initr -> DGgiC.PBDISJ ly pa nn lastb.
Proof.
intros HK Hrev. pose proof HK as (M & L & Hk & _). pose proof (Enn_cf HK) as EN. pose proof (Epa_cf HK) as EP.
pose proof (lastb_in_cf (conj M (conj L Hrev))) as LB.
pose proof (chunk_facts_cf B ly S Hp rd0 k M Hk) as (G1 & G2 & G3 & G4 & G5 & _).
pose proof (ext_rounded_cf ly S Hp rd0 M k Hk) as (ER & NN1 & NN2 & NN3). rewrite <- EN in ER, NN1, NN2, NN3.
pose proof (batch_vs_chunk_cf ly S Hp rd0 M lastb k LB Hk) as D. unfold zdisjoint in D. cbn [fst snd] in D.
clear - D EP ER G5. unfold DGgiC.PBDISJ, DGgiC.N8v, DGgiC.Bv, kBatchBytes in *. lia.
Qed.
End c.

(* ================================================================================================================ *)
(* 4. The view records from ARcf at the Deallocate premise.                                                         *)
Section v.
Hypothesis HIMG : YGcfDIface.IMG_COVER.
Hypothesis HTSD : FV_TSD.
Hypothesis HINST : FQ_CONST.
Hypothesis HIAL : FV_IAL.
Hypothesis HZ3 : FV_ZONE3.

Lemma view_n_cf : forall ly S Hp W mem md, ARcf im_segs B ly S Hp W mem md -> st_internal_inited S = true ->
dview_n B W ly (as_inst B) mem.
Proof.
intros ly S Hp W mem md HAR HI.
pose proof (proj1 HAR) as M. pose proof (proj1 (proj2 HAR)) as L. pose proof (amc_layout _ _ _ _ _ M) as LY.
constructor.
- exact LY.
- exact (HIMG ly S md L).
- rewrite (amc_tsd _ _ _ _ _ M). exact HTSD.
- exact (amc_const _ _ _ _ _ M).
- exact (inst_cf ly S Hp W mem HINST M).
- apply (proj2 (HIAL W mem)). exact (ial_post_of_ARm_cf ly S Hp W mem M HI).
- exact (unw_cf ly S Hp W mem M).
Qed.

Lemma dbview_room_cf : forall ly S Hp W mem md p n lastb initr, ARcf im_segs B ly S Hp W mem md -> qtight S ->
In (p, n) (blocks S) -> rev (qc_list (st_qthread S)) = lastb :: initr ->
(1 <= req_size n /\ n < cf_malloc_max) /\ dbview W ly mem (st_qthread S) lastb (sptr_addr B ly p) (req_size n).
Proof.
intros ly S Hp W mem md p n lastb initr HAR HQ HBLK Hrev.
pose proof (proj1 HAR) as M. pose proof (proj1 (proj2 HAR)) as L.
pose proof (find_user_block_cf _ 0 0 0 S p n (WfR_of_WfP_cf _ _ _ _ _ (amc_wf _ _ _ _ _ M)) HBLK) as (k & _ & Hk & Hst & Hu & Hr).
assert (HK : KVc ly S Hp W mem md p n k) by exact (conj M (conj L (conj Hk (conj Hst (conj Hu Hr))))).
assert (HB : BVc ly S Hp W mem md lastb initr) by exact (conj M (conj L Hrev)).
pose proof (nn_range_cf _ _ _ _ _ _ _ _ _ HK) as (NR1 & NR2 & NR3).
pose proof (bb_cf _ _ _ _ _ _ _ _ HB HQ) as (BB1 & BB2 & BB3).
split; [split; [exact NR1 | lia]|].
constructor.
- exact (qc_vals_cf _ _ _ _ _ _ _ _ HB).
- exact (batch_vals_cf _ _ _ _ _ _ _ _ HB).
- intros a [Ha|[ROOM Ha]]; [exact (bcell_pres_cf _ _ _ _ _ _ _ _ HB a Ha) | exact (slot_pres_cf _ _ _ _ _ _ _ _ HB ROOM a Ha)].
- exact (brange_cf _ _ _ _ _ _ _ _ HB).
- exact (pbdisj_cf _ _ _ _ _ _ _ _ _ _ _ HK Hrev).
- change (0 <= DGgiC.BBv lastb /\ DGgiC.BBv lastb + req_size n < 2 ^ 48 /\ DGgiC.QSv (st_qthread S) < 2 ^ 48).
  unfold kQuarantineCacheMax in *. dsplits; lia.
- exact (slots_cf _ _ _ _ _ _ _ _ HB).
Qed.

(* di_view's record on the enqueue side of free_cf's size test (req_size n <= kQuarantineMax, DGif0.dv_zone's
   bound). *)
Lemma view_cf : forall ly S Hp W mem md p n, ARcf im_segs B ly S Hp W mem md -> st_internal_inited S = true -> qtight S ->
In (p, n) (blocks S) -> req_size n <= kQuarantineMax -> dview B W ly (as_inst B) mem S p n.
Proof.
intros ly S Hp W mem md p n HAR HI HQ HBLK HSM.
pose proof (view_n_cf ly S Hp W mem md HAR HI) as VN.
pose proof (proj1 HAR) as M. pose proof (proj1 (proj2 HAR)) as L.
pose proof (find_user_block_cf _ 0 0 0 S p n (WfR_of_WfP_cf _ _ _ _ _ (amc_wf _ _ _ _ _ M)) HBLK) as (k & Hf & Hk & Hst & Hu & Hr).
assert (HK : KVc ly S Hp W mem md p n k) by exact (conj M (conj L (conj Hk (conj Hst (conj Hu Hr))))).
pose proof (nn_range_cf _ _ _ _ _ _ _ _ _ HK) as (NR1 & NR2 & NR3).
constructor.
- exact VN.
- exact (nonnull_cf _ _ _ _ _ _ _ _ _ HK).
- exists k. exact (conj Hf (conj Hst (conj Hu Hr))).
- exact (hdr_cf _ _ _ _ _ _ _ _ _ HK).
- exact (pres_cf _ _ _ _ _ _ _ _ _ HK).
- exact (shpres_cf _ _ _ _ _ _ _ _ _ HK).
- exact (junk_pres_cf ly S Hp W mem md M L).
- split; [exact (p_zone_cf _ _ _ _ _ _ _ _ _ HIMG HZ3 HK)|]. split; [exact (pstatic_cf _ _ _ _ _ _ _ _ _ HK)|].
  split; [exact (p_al_cf _ _ _ _ _ _ _ _ _ HK)|]. unfold kQuarantineMax in HSM. lia.
- exact (qb_cf ly S Hp W mem M HQ).
- intros lastb initr ER. exact (proj2 (dbview_room_cf ly S Hp W mem md p n lastb initr HAR HQ HBLK ER)).
Qed.

(* The big arm's view (DGbigIF.dview_big) on the recycle side (kQuarantineMax < req_size n): the chunk's address is
   its base plus its redzone (chunk_facts_cf), and the size bound comes from YG08cf.cf_malloc_max_bound. *)
Lemma view_big_cf : forall ly S Hp W mem md p n, ARcf im_segs B ly S Hp W mem md -> st_internal_inited S = true -> qtight S ->
In (p, n) (blocks S) -> kQuarantineMax < req_size n -> DGbigIF.dview_big B W ly (as_inst B) mem S p n.
Proof.
intros ly S Hp W mem md p n HAR HI HQ HBLK HBG.
pose proof (view_n_cf ly S Hp W mem md HAR HI) as VN.
pose proof (proj1 HAR) as M. pose proof (proj1 (proj2 HAR)) as L. pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (find_user_block_cf _ 0 0 0 S p n (WfR_of_WfP_cf _ _ _ _ _ (amc_wf _ _ _ _ _ M)) HBLK) as (k & Hf & Hk & Hst & Hu & Hr).
assert (HK : KVc ly S Hp W mem md p n k) by exact (conj M (conj L (conj Hk (conj Hst (conj Hu Hr))))).
pose proof (nn_range_cf _ _ _ _ _ _ _ _ _ HK) as (NR1 & NR2 & NR3).
pose proof (Epa_cf _ _ _ _ _ _ _ _ _ HK) as EP.
pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
rewrite Hr in G8.
pose proof YG08cf.cf_malloc_max_bound as MMB.
constructor.
- exact VN.
- exact (nonnull_cf _ _ _ _ _ _ _ _ _ HK).
- exists k. split; [exact Hf|]. split; [exact Hst|]. split; [exact Hu|]. split; [exact Hr|]. rewrite <- Hu. exact (eq_sym G4).
- exact (hdr_cf _ _ _ _ _ _ _ _ _ HK).
- exact (pres_cf _ _ _ _ _ _ _ _ _ HK).
- exact (junk_pres_cf ly S Hp W mem md M L).
- split; [exact (p_zone_cf _ _ _ _ _ _ _ _ _ HIMG HZ3 HK)|]. split; [exact (pstatic_cf _ _ _ _ _ _ _ _ _ HK)|].
  split; [exact (p_al_cf _ _ _ _ _ _ _ _ _ HK)|]. split; [exact HBG|]. unfold req_size in *. destruct (n =? 0); lia.
- exact (qb_cf ly S Hp W mem M HQ).
Qed.
End v.

(* ================================================================================================================ *)
(* 5. The relation's machine cells (ARmcf's amc_exh_cell / amc_errb_cells, field round 2): the per-class exhausted  *)
(*    bytes sit in the primary reserve past the space, the error-buffer object in the owned static data inside the   *)
(*    image window; both by the image rows ARmcf carries (amc_cells_owned: YGcfImgRows.EXH_OFF_t, errb_obj_owned_t). *)
(*    Both are owned, and both are apart from the thread object, the stack, every chunk extent, every batch object   *)
(*    and every chunk's shadow band.                                                                                 *)
Definition XC (ly : alayout) (a : Z) : Prop :=
  (exists c, 1 <= c <= 31 /\ a = aeval B ly (aoff (ASp (kRegionInfoOff + 128 * c)) cf_exh_off)) \/
  (cf_errbuf_obj <= a < cf_errbuf_obj + 56).

Section x.
Variables (ly : alayout) (S : astate) (Hp : list Z) (rd : reader).
Hypothesis M : ARmcf B ly S Hp rd.
(* the two image rows the cells' ownership needs, from the relation (ARmcf's amc_cells_owned) *)
Lemma x_rows : 0 <= cf_exh_off < 128 /\ errb_obj_owned_t B.
Proof. destruct (amc_cells_owned _ _ _ _ _ M) as [E [O _]]. exact (conj (YGcfImgRows.EXH_OFF_bound E) O). Qed.

Lemma x_where : forall a, XC ly a ->
  (ly_space ly + kRegionInfoOff <= a < ly_space ly + kRegionInfoOff + 4096 /\ ly_prim ly <= a < ly_prim ly + kPrimResvSize)
  \/ in_zr a (ly_img ly).
Proof.
intros a [(c & Hc & ->)|Ha].
- left. pose proof (lo_space_in _ (amc_layout _ _ _ _ _ M)) as [S1 S2]. pose proof (proj1 x_rows) as HEXH.
  cbn [aoff aeval]. unfold kRegionInfoOff, kSpaceSize in *. lia.
- right. pose proof (proj2 x_rows a Ha) as OS. apply Exists_exists in OS as (r & Hr & Hin).
  pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ M) r ltac:(apply in_or_app; left; exact Hr)) as [Z1 Z2].
  unfold in_zr in *. lia.
Qed.

Lemma x_static_apart : forall i e a, nth_error (static_extents ly) i = Some e -> (0 < i < 9)%nat -> XC ly a -> ~ in_zr a e.
Proof.
intros i e a Hi Hr X. pose proof (lo_disj _ (amc_layout _ _ _ _ _ M)) as PD.
pose proof (YFfl.pairwise_nth zdisjoint _ 0 i _ e PD eq_refl Hi ltac:(lia)) as D0.
pose proof (YFfl.pairwise_nth zdisjoint _ i 9 e _ PD Hi eq_refl ltac:(lia)) as D9.
destruct (x_where a X) as [(E1 & E2)|E]; unfold zdisjoint, in_zr in *; cbn [fst snd] in D0, D9; lia.
Qed.

Lemma x_T : forall a, XC ly a -> ~ (ly_T ly <= a < ly_T ly + kThreadObjSize).
Proof. intros a X H. exact (x_static_apart 2 _ a eq_refl ltac:(lia) X H). Qed.

Lemma x_S : forall a sp, XC ly a -> ly_stk_lo ly + DGbaseC.DFSTACK <= sp <= ly_stk_hi ly -> ~ (sp - DGbaseC.DFSTACK <= a < sp).
Proof.
intros a sp X Hsp H. apply (x_static_apart 8 _ a eq_refl ltac:(lia) X). unfold in_zr. cbn [fst snd].
unfold DGbaseC.DFSTACK in *. lia.
Qed.

Lemma x_NB : forall a, XC ly a -> ~ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize).
Proof. intros a X H. exact (x_static_apart 4 _ a eq_refl ltac:(lia) X H). Qed.
Lemma x_SB : forall a, XC ly a -> ~ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).
Proof. intros a X H. exact (x_static_apart 5 _ a eq_refl ltac:(lia) X H). Qed.

Lemma x_exh_where : forall c a, 1 <= c <= 31 -> a = aeval B ly (aoff (ASp (kRegionInfoOff + 128 * c)) cf_exh_off) ->
  ly_space ly + kRegionInfoOff <= a < ly_space ly + kRegionInfoOff + 4096 /\ ly_prim ly <= a < ly_prim ly + kPrimResvSize.
Proof.
intros c a Hc ->. pose proof (lo_space_in _ (amc_layout _ _ _ _ _ M)) as [S1 S2]. pose proof (proj1 x_rows) as HEXH.
cbn [aoff aeval]. unfold kRegionInfoOff, kSpaceSize in *. lia.
Qed.

(* an exhausted byte is not owned static data (the image part of the depot zone and the internal allocator's zone) *)
Lemma x_exh_nstatic : forall c a, 1 <= c <= 31 -> a = aeval B ly (aoff (ASp (kRegionInfoOff + 128 * c)) cf_exh_off) ->
  ~ Exists (in_zr a) (as_owned_static B).
Proof.
intros c a Hc Ea OS.
apply Exists_exists in OS as (r & Hr & Hin).
pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ M) r ltac:(apply in_or_app; left; exact Hr)) as [Z1 Z2].
pose proof (lo_disj _ (amc_layout _ _ _ _ _ M)) as PD.
pose proof (YFfl.pairwise_nth zdisjoint _ 0 9 _ _ PD eq_refl eq_refl ltac:(lia)) as D9.
pose proof (x_exh_where c a Hc Ea) as [E1 E2].
unfold zdisjoint, in_zr in *. cbn [fst snd] in D9. lia.
Qed.

Lemma x_K : forall y a, In y (st_chunks S) -> XC ly a -> ~ (ck_base B ly y <= a < ck_base B ly y + ck_extent y).
Proof.
intros y a Hy X H. pose proof (lo_disj _ (amc_layout _ _ _ _ _ M)) as PD.
pose proof (YFfl.pairwise_nth zdisjoint _ 0 9 _ _ PD eq_refl eq_refl ltac:(lia)) as D09.
unfold zdisjoint in D09. cbn [fst snd] in D09.
destruct (ext_zone_cf ly S Hp rd M y Hy) as [(c & Hc & X1 & X2 & X3 & X4)|(r & Eb & Xb & Xin)].
- unfold region_base in X1, X2, X3, X4. rewrite region_off_eq in X1, X2, X3, X4 by lia.
  destruct (x_where a X) as [(E1 & E2)|E]; unfold in_zr in *; unfold kRegionInfoOff in *; nia.
- pose proof (SECX_cf ly S Hp rd M _ 0 _ Xin eq_refl) as DP. pose proof (SECX_cf ly S Hp rd M _ 9 _ Xin eq_refl) as DIg.
  unfold zdisjoint, kPage in *. cbn [fst snd] in DP, DIg.
  destruct (x_where a X) as [(E1 & E2)|E]; unfold in_zr in *; lia.
Qed.

Lemma x_B : forall b a, In b (all_batches S) -> XC ly a ->
  ~ (ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes).
Proof.
intros b a Hb X H. pose proof (amc_layout _ _ _ _ _ M) as LO.
destruct (batch_geom_cf ly S Hp rd M b Hb) as (x & Ex & Px & Ax & Ux & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & _).
pose proof (YFfl.pairwise_nth zdisjoint _ 0 9 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as D09.
unfold zdisjoint in D09. cbn [fst snd] in D09.
unfold region_base in *. rewrite region_off_eq in * by (unfold kBatchClass; lia). unfold kBatchClass in *.
destruct (x_where a X) as [(E1 & E2)|E]; unfold in_zr in *; unfold kRegionInfoOff, kBatchBytes, kFreeArrayOffset in *; lia.
Qed.

(* the shadow band of an aligned range inside a chunk *)
Lemma x_H : forall y a u n, In y (st_chunks S) -> XC ly a -> u mod 8 = 0 -> ck_base B ly y <= u -> 0 <= n ->
  u + n <= ck_base B ly y + ck_extent y -> ~ (shadow_addr u <= a < shadow_addr u + (n + 7) / 8).
Proof.
intros y a u n Hy X U8 L1 L2 L3 H. pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (chunk_facts_cf B ly S Hp rd y M Hy) as (G1 & G2 & _).
pose proof (lo_high _ LO) as [HH1 HH2]. ceil.
pose proof (YFfl.pairwise_nth zdisjoint _ 0 9 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as D09.
pose proof (lo_img _ LO) as (I0 & I1 & I2 & _).
unfold zdisjoint in D09. cbn [fst snd] in D09.
assert (SB : SHADOW_OFF <= shadow_addr u /\ shadow_addr u + (n + 7) / 8 <= kHighMemBeg).
{ unfold shadow_addr. apply Z.mod_divide in U8 as [q Hq]; [|lia]. subst u. rewrite Z_div_mult by lia.
  unfold in_app in G1. unfold ASAN_CEIL, SHADOW_OFF, kHighMemBeg in *. Z.div_mod_to_equations. lia. }
unfold SHADOW_OFF, kHighMemBeg, kImgEnd in *.
destruct (x_where a X) as [(E1 & E2)|E]; unfold in_zr in *; lia.
Qed.

(* both kinds of byte are owned *)
Lemma x_owned : forall a, XC ly a -> 0 <= a < 2 ^ 64 /\ aowned B ly S a.
Proof.
intros a X. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (lo_high _ LO) as [HH1 HH2]. ceil.
pose proof (lo_img _ LO) as (I0 & I1 & I2 & _).
split.
- destruct (x_where a X) as [(E1 & E2)|E]; unfold in_zr in *; unfold ASAN_CEIL, kHighMemBeg, kImgLo, kImgEnd in *; lia.
- destruct X as [(c & Hc & Ea)|Ha].
  + pose proof (x_exh_where c a Hc Ea) as [E1 E2].
    apply (own_prim_nonuser_cf B ly S Hp rd a M E2). intros y Hy _ Hu.
    exact (x_K y a Hy (or_introl (ex_intro _ c (conj Hc Ea))) (user_in_extent_cf B ly S Hp rd y a M Hy Hu)).
  + exact (own_static_cf B ly S Hp rd a M (proj2 x_rows a Ha)).
Qed.

(* the forms the walks' write sets take *)
Lemma x_win : forall a o w, XC ly a -> 0 <= o -> o + w <= kThreadObjSize -> ~ (ly_T ly + o <= a < ly_T ly + o + w).
Proof. intros a o w X Ho Hw H. apply (x_T a X). lia. Qed.

Lemma x_kwords : forall k a, In k (st_chunks S) -> XC ly a ->
  ~ ((sptr_addr B ly (ck_user k) - 16 <= a < sptr_addr B ly (ck_user k) - 8) \/
     (sptr_addr B ly (ck_user k) <= a < sptr_addr B ly (ck_user k) + 8)).
Proof.
intros k a Hk X H. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (_ & _ & _ & G4 & G5 & _).
pose proof (ext_rounded_cf ly S Hp rd M k Hk) as (ER & NN1 & NN2 & NN3).
apply (x_K k a Hk X). rewrite G4 in H. lia.
Qed.

Lemma x_kshadow : forall k a, In k (st_chunks S) -> XC ly a ->
  ~ (shadow_addr (sptr_addr B ly (ck_user k)) <= a < shadow_addr (sptr_addr B ly (ck_user k)) + (ck_n k + 7) / 8).
Proof.
intros k a Hk X. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (_ & _ & _ & G4 & G5 & _).
pose proof (ext_rounded_cf ly S Hp rd M k Hk) as (ER & NN1 & NN2 & NN3).
pose proof (u_al8_cf ly S Hp rd M k Hk) as (U8 & _ & _).
apply (x_H k a _ (ck_n k) Hk X U8); rewrite ?G4; lia.
Qed.

Lemma x_bcells : forall b a, In b (all_batches S) -> Z.of_nat (length (b_items b)) < kBatchSlots -> XC ly a ->
  ~ ((ly_space ly + b_self b + 8 <= a < ly_space ly + b_self b + 24) \/
     (ly_space ly + b_self b + 24 + 8 * Z.of_nat (length (b_items b)) <= a <
      ly_space ly + b_self b + 24 + 8 * Z.of_nat (length (b_items b)) + 8)).
Proof. intros b a Hb Hn X H. apply (x_B b a Hb X). unfold kBatchSlots, kBatchBytes in *. lia. Qed.
End x.
End a.
