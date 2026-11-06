(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfInstDrainX.v, with its module paths changed. *)
(* Theorem Labs, 2026-10: the generic cf instance layer, lane F2b: the relation at the drain's two
   cuts from the cut memory, and the re-quarantine fields di_requar_x / di_requar_r at the cf instance.
   rule 24: no function proved (kind: interface-instance discharge of DMiface's re-quarantine fields; relation-level
   facts about the cut memory DMiface.dmem_q).

   The cf twin of cgif's DGif1dq.requar_AR (DGif1dq.v:476) over YFey.drain_fin_ARm (YFey.v:708), restated over the
   event-free relation: from ARcf at the drain's entry state X, the cut memory relation DMiface.dmem_q (mem' differs from
   mem only on the stack window below sp0, the quarantine header words and the batch cells; the cut state's quarantine
   cells hold in mem'), the cut state S1 := set_qglobal g' (set_qthread qc0 X) (the transfer, then the merge and the
   pop, change the quarantine lists only), and every batch of S1 and of the temp list P having one of X's batch
   objects, [ARcfR_S1] gives ARcfR at S1 over mem' (YGcfInstDrainR.v) at any WfR_cf state.  Each field of ARmcf is
   carried as YG0qcf.AR_frame_law_ok_cf carries it, with two more facts per byte besides ownership ([okq]: not a
   quarantine header word, not in one of X's batch objects); the shadow bands are apart from every changed word
   ([band_same]); the quarantine's cells and the cut's visibility come from dmem_q ([qcells], [VISq]); the cut state's
   batch junk is visible because X's batch objects are ([xbatch_vis]).
   - [di_requar_x_cf]: Drain's return without recycling: ARX_cf at the transfer state (Wf_cf whole: the transfer moves
     no class record, YGcfInstDrainR.drain_xfer_Wf_cf); any L24 and QB;
   - [di_requar_r_cf]: Recycle's call of DoRecycle: ARXr_cf and DRq_cf (YGcfInstDrainR.drain_recyc_DRq_cf) at the cut,
     at QB := QB_cf NMAXD (its quar_n <= queued_n) and any L24; [recyc_hb] maps the cut's batches to X's (mres_cf).
   Both keep xs_mapped_cf (same secondaries, same maps) and the owned set (aowned reads no quarantine field).
   Image premises (named, over ImgBase.AImg's fields and the symbol table only):
   - [IMG_QAPART]: the instance's quarantine header words are apart from the depot / store / internal-allocator areas
     of the symbol table (cgif: by its numerals, YFey.v:578 / :585 / :638);
   - [ERRB_QAPART] (YGcfImgRows): the error-message buffer's object is apart from the instance object (cgif:
     ERRB_QAPART_cgif, YGcfInstHitcgif.v:61 @ cf-hit 76362ece943);
   - [CONST_APART]: each constant cell of the image is the two zero bytes after the mutex word (dmem_q pins them) or
     lies off the quarantine header words and off the primary reserve, for every layout with Base's
     YGcfInstBase.ly_img_ok (layout_ok, the TSD slot at the image's, the owned static inside ly_img: the stated row
     over bare layout_ok was refuted at reply's image A, ReplyImg_constapart.v @ 507bcceac8e, by layouts that put
     ly_tsd elsewhere) (cgif: YFev.Tfib_const_locd, DGif1dq.v:419-461);
   - [EXH_OFF_t] (YGcfImgRows, the unit row cf_exh_off = 68), from which the layer derives EXH_OFF_OK;
   - [errb_obj_owned_t]: Base's row (the error-message buffer's object is owned static);
   - [IOK_inst]: Base's YGcfInstBase.IOK_ok (the unit's instance predicate names the symbol table's instance object).
   Image-free otherwise and event-free (no event-count term, no event regime, no event-keyed budget appears). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d YK08 YP03.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0k YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf YG0qcf YG0tcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfTok YG03cf YG03dcf YGcfBatch.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseDG DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfImgRows YGcfInstBase YGcfInstDrainR.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.
Ltac ceil := let H := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H.

Section U. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The image premises.                                                                                              *)
Definition qhdr_inst (B : asyms) (a : Z) : Prop :=
(as_inst B + o_quar + 152 <= a < as_inst B + o_quar + 156) \/ (as_inst B + o_quar + 160 <= a < as_inst B + o_quar + 192).

Definition IMG_QAPART : Prop :=
forall B, im_syms B -> forall a, qhdr_inst B a ->
~ (as_depot B <= a < as_depot B + 4 * 2 ^ 20 + 32) /\ ~ (as_store B <= a < as_store B + 32) /\
~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2).

(* ERRB_QAPART (the buffer's object apart from the instance object: the drain's walks write the instance's quarantine
   header words and the secondary recycle's four further instance words) is the class-free unit row of
   YGcfImgRows.v (taken by path from a working branch 76362ece943; cgif: ERRB_QAPART_cgif, YGcfInstHitcgif.v:61).
   It is the first clause of YGcfErrbSep.ERRB_SEP_t. *)

(* EXH_OFF_OK is a LAYER fact, derived from the one unit row YGcfImgRows.EXH_OFF_t (cf_exh_off = 68):
   the per-class exhausted byte lies inside its class's 128-byte RegionInfo record and off every RegionInfo word the
   drain's walks write: CacheDealloc's three (the count, the freed total and the free-array length, YGcfInstDrainCm
   cmWRG: +0, +16, +80, eight bytes each) and the free-array growth's (H3's WING1: +24 .. +32, +64 .. +68,
   +69 .. +128, whose one gap is the byte itself).  cgif: cf_exh_off = 68, in that gap (YGcfImgcgif.v:83). *)
Definition EXH_OFF_OK : Prop :=
8 <= cf_exh_off < 128 /\ ~ (16 <= cf_exh_off < 24) /\ ~ (24 <= cf_exh_off < 32) /\
~ (64 <= cf_exh_off < 68) /\ cf_exh_off < 69 /\ ~ (80 <= cf_exh_off < 88).

Lemma EXH_OFF_OK_of_t : EXH_OFF_t -> EXH_OFF_OK.
Proof. unfold EXH_OFF_t, EXH_OFF_OK. intros ->. lia. Qed.

Definition CONST_APART : Prop :=
forall B ly c, im_syms B -> ly_img_ok B ly -> In c (im_const ly) ->
(aeval B ly (c_at c) = as_inst B + o_q_cmutex + 2 /\ c_w c = 2%nat /\ c_val c = AV (ANum 0)) \/
(forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
 ~ qhdr (as_inst B) ly (aeval B ly (c_at c) + k) /\ ~ (ly_prim ly <= aeval B ly (c_at c) + k < ly_prim ly + kPrimResvSize)).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Generic helpers.                                                                                                 *)
Lemma pairwise_nth_f : forall {A} (R : A -> A -> Prop) l i j x y, pairwise R l -> (i < j)%nat ->
nth_error l i = Some x -> nth_error l j = Some y -> R x y.
Proof.
intros A R l. induction l as [|h t IH]; intros i j x y HP Hij Hi Hj; [destruct i; discriminate|].
destruct HP as [HF HP]. destruct i as [|i]; destruct j as [|j]; try lia.
- cbn in Hi, Hj. injection Hi as <-. exact (proj1 (Forall_forall _ _) HF y (nth_error_In _ _ Hj)).
- cbn in Hi, Hj. exact (IH i j x y HP ltac:(lia) Hi Hj).
Qed.

Lemma aview_mem_eq : forall segs H (mem mem' : word -> option byte) a, mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) ->
aview segs H mem' a = aview segs H mem a.
Proof. intros segs H mem mem' a E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.

Lemma ch_some_x : forall B ly (rd0 : reader) e (w : nat) v a, cell_holds B ly rd0 (ACell e w (AV v)) ->
aeval B ly e <= a < aeval B ly e + Z.of_nat w -> rd0 a <> None.
Proof.
intros B ly rd0 e w v a H Ha. replace a with (aeval B ly e + Z.of_nat (Z.to_nat (a - aeval B ly e))) by lia.
unfold cell_holds in H. cbn [c_at c_val c_w] in H. rewrite (H (Z.to_nat (a - aeval B ly e)) ltac:(lia)). discriminate.
Qed.

Lemma val_mem_vis : forall segs H mem a (w : nat) v x, val_mem segs (mrestrict H mem) a w v -> a <= x < a + Z.of_nat w ->
aview segs H mem x <> None.
Proof.
intros segs H mem a w v x Hv Hx. replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
unfold aview. rewrite (Hv (Z.to_nat (x - a)) ltac:(lia)). discriminate.
Qed.

Lemma val_mem_zero2 : forall segs H mem a, val_mem segs (mrestrict H mem) a 2 0 -> forall (k : nat), (k < 2)%nat ->
aview segs H mem (a + Z.of_nat k) = Some (le_byte 0 2 k).
Proof.
intros segs H mem a Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map].
assert (E : le_byte 0 2 k = 0) by (destruct k as [|[|k]]; [reflexivity | reflexivity | lia]).
assert (E' : YO0f.le_byte 0 2 k = 0) by (destruct k as [|[|k]]; [reflexivity | reflexivity | lia]).
rewrite E, E'. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The cut.                                                                                                         *)
Section Q.
Variable B : asyms.
Variable ly : alayout.
Variable X : astate.
Variable g' : qcache.
Variable W : world im_segs.
Variables (mem mem' : word -> option byte) (md : Model) (sp0 : Z) (P : list batch) (Hp : list Z).
Local Notation S1 := (set_qglobal g' (set_qthread qc0 X)).
Local Notation rd := (aview im_segs (w_H W) mem).
Local Notation rd' := (aview im_segs (w_H W) mem').
Hypothesis HAR : ARcf im_segs B ly X Hp W mem md.
Hypothesis HB : forall b, In b (all_batches S1 ++ P) ->
  In (b_self b) (map b_self (all_batches X)) /\ (length (b_items b) <= Z.to_nat kBatchSlots)%nat.
Hypothesis HSP : ly_stk_lo ly + YFeuC.DSTACK <= sp0 <= ly_stk_hi ly.
Hypothesis DQ : dmem_q B W (as_inst B) ly sp0 X S1 P mem mem'.
(* the cut's queues only LOSE items (the transfer moves them, the merge regroups them, the pop drops them), which is
   what keeps the shadow's exemption set from growing *)
Hypothesis HQS : forall b, In b (map ck_beg (q_items S1)) -> In b (map ck_beg (q_items X)).
Hypothesis TS : im_syms B.
Hypothesis IQA : IMG_QAPART.
Hypothesis EAP : ERRB_QAPART.
Hypothesis CA : CONST_APART.

Lemma qM : ARmcf B ly X Hp rd. Proof. exact (proj1 HAR). Qed.
Lemma qLO : layout_ok ly. Proof. exact (amc_layout _ _ _ _ _ qM). Qed.
Lemma qIMG : ly_img_ok B ly. Proof. exact (ly_img_ok_of_ARmcf B ly X Hp rd qM). Qed.
Lemma qWF : Wf_cf (as_universe B) X. Proof. exact (amc_wf _ _ _ _ _ qM). Qed.
Lemma qSY : asyms_ok B. Proof. exact (amc_syms _ _ _ _ _ qM). Qed.
Lemma qLED : ALedger_cf im_segs ly X md. Proof. exact (proj1 (proj2 HAR)). Qed.

(* the static extents: 0 prim, 1 Q, 2 T, 3 F, 4 NB, 5 SB, 6 C, 7 D, 8 stack, 9 image *)
Lemma SX : forall i j x y, (i < j)%nat -> nth_error (static_extents ly) i = Some x -> nth_error (static_extents ly) j = Some y ->
zdisjoint x y.
Proof. intros i j x y Hij Hi Hj. exact (pairwise_nth_f zdisjoint _ i j x y (lo_disj _ qLO) Hij Hi Hj). Qed.
Ltac sx i j := let D := fresh "DJ" in pose proof (SX i j _ _ ltac:(lia) eq_refl eq_refl) as D; unfold zdisjoint in D; cbn [fst snd] in D.

Lemma img_area : forall r a, In r (asyms_areas B) -> fst r <= a < fst r + snd r -> in_zr a (ly_img ly).
Proof.
intros r a Hr Ha. pose proof (proj1 (Forall_forall _ _) (aso_cover _ qSY) r Hr) as E.
apply Exists_exists in E as (r' & Hr' & [Z1 Z2]).
pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ qM) r' ltac:(apply in_app_iff; left; exact Hr')) as [I1 I2].
unfold in_zr. lia.
Qed.
Lemma img_inst : forall a, as_inst B <= a < as_inst B + 3632 -> in_zr a (ly_img ly).
Proof. intros a Ha. apply (img_area (as_inst B, 3632)); [unfold asyms_areas; cbn; tauto | exact Ha]. Qed.
Lemma qhdr_zone : forall a, qhdr (as_inst B) ly a ->
(qhdr_inst B a /\ in_zr a (ly_img ly)) \/ (ly_T ly + t_qc <= a < ly_T ly + t_qc + 32).
Proof.
intros a [Hq|[Hq|Hq]].
- left. split; [left; exact Hq|]. apply img_inst. unfold o_quar in *. lia.
- left. split; [right; exact Hq|]. apply img_inst. unfold o_quar in *. lia.
- right. exact Hq.
Qed.

(* X's batch objects *)
Definition inXb (a : Z) : Prop :=
exists b, In b (all_batches X) /\ ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes.

Lemma batch_geom_x : forall b, In b (all_batches X) ->
exists x, ly_space ly + b_self b = region_base ly kBatchClass + x /\ 0 <= x /\ x mod kBatchBytes = 0 /\
x + kBatchBytes <= rg_alloc_user (reg X kBatchClass) /\
rg_alloc_user (reg X kBatchClass) <= rg_mapped_user (reg X kBatchClass) <= kFreeArrayOffset /\
In x (batch_offs X kBatchClass).
Proof.
intros b Hb. pose proof (wfc_classes _ _ _ _ _ qWF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs X kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; auto).
pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wrc_alloc _ _ _ _ _ _ CL) as AL. pose proof (wrc_alloc_al _ _ _ _ _ _ CL) as AA.
pose proof (wrc_mapped_bound _ _ _ _ _ _ CL) as MB.
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2, AA.
exists x. unfold kBatchBytes. split; [unfold region_base; subst x; lia|]. split; [lia|]. split; [exact X2|].
split; [|split; [lia | exact INB]].
apply Z.mod_divide in X2 as [q Hq]; [|lia]. apply Z.mod_divide in AA as [q' Hq']; [|lia]. nia.
Qed.

Lemma inXb_zone : forall a, inXb a -> region_base ly kBatchClass <= a < region_base ly kBatchClass + kFreeArrayOffset.
Proof.
intros a (b & Hb & Ha). destruct (batch_geom_x b Hb) as (x & E & X1 & _ & X3 & X4 & _). unfold kBatchBytes in *. lia.
Qed.

Lemma region24_in_prim :
ly_prim ly <= region_base ly kBatchClass /\ region_base ly kBatchClass + kFreeArrayOffset <= ly_prim ly + kPrimResvSize /\
kHighMemBeg <= region_base ly kBatchClass.
Proof.
pose proof (region_in_prim ly kBatchClass qLO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & _ & R4 & _).
unfold kFreeArrayOffset. lia.
Qed.

Lemma batch_vs_chunk_x : forall b k, In b (all_batches X) -> In k (st_chunks X) ->
zdisjoint (ly_space ly + b_self b, kBatchBytes) (ck_base B ly k, ck_extent k).
Proof.
intros b k Hb Hk. destruct (batch_geom_x b Hb) as (xb & Eb & Pb & Ab & Ub & [AU MU] & INB).
pose proof (chunk_facts_cf B ly X Hp _ k qM Hk) as CF. unfold cfacts_cf in CF.
destruct CF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (wfc_classes _ _ _ _ _ qWF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
pose proof (wrc_nodup _ _ _ _ _ _ CL) as ND. rewrite app_assoc in ND. apply NoDup_app_iff in ND as (_ & ND & _).
apply NoDup_app_iff in ND as (_ & _ & NDx).
unfold zdisjoint. cbn [fst snd]. rewrite Eb.
destruct (ck_beg k) as [|o|r o|c p] eqn:Ebx; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & Gxm & Gxs & Gal).
  destruct (Z.eq_dec (prim_class o) kBatchClass) as [Ec|Hc].
  + pose proof (In_chunk_offs X k o Hk Ebx) as IK. rewrite Ec in *. set (xk := o - region_off kBatchClass) in *.
    assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in *.
    assert (xk <> xb). { intros E. apply (NDx xk); [exact IK | rewrite E; exact INB]. }
    unfold kBatchBytes in *. apply Z.mod_divide in Gxm as [q1 Hq1]; [|lia]. apply Z.mod_divide in Ab as [q2 Hq2]; [|lia].
    assert (q1 <> q2) by (intros E; subst; lia). nia.
  + pose proof (region_in_prim ly (prim_class o) qLO ltac:(lia)) as (R1' & R2' & _).
    pose proof (region_in_prim ly kBatchClass qLO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & _).
    unfold region_base, kBatchBytes, kFreeArrayOffset in *. rewrite !region_off_eq in * by (unfold kBatchClass; lia).
    unfold kBatchClass in *.
    destruct (Z.lt_ge_cases (prim_class o) 24).
    * pose proof (Z.mul_le_mono_nonneg_r (prim_class o + 1) 24 (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
    * pose proof (Z.mul_le_mono_nonneg_r (24 + 1) (prim_class o) (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
  pose proof region24_in_prim as (R1 & R2 & _).
  pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req k)) (ly_prim ly, kPrimResvSize) (sec_extents ly X) (static_extents ly) eq_refl
    (proj2 (amc_placed _ _ _ _ _ qM)) Gin ltac:(unfold static_extents, owned_extents; cbn; tauto)) as DJ.
  unfold zdisjoint, kPage, kBatchBytes, kFreeArrayOffset in *. cbn [fst snd] in DJ. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Unchanged bytes.                                                                                                 *)
Lemma not_dwin : forall a, ~ (ly_stk_lo ly <= a < ly_stk_hi ly) -> ~ qhdr (as_inst B) ly a -> ~ inXb a ->
~ dwin_q (as_inst B) ly sp0 X S1 P a.
Proof.
intros a NS NQ NB [Hs|[Hq|Hb]].
- apply NS. unfold YFeuC.DSTACK in *. lia.
- exact (NQ Hq).
- destruct Hb as (b & Hb & Rg). apply NB.
  assert (LB : (length (b_items b) <= Z.to_nat kBatchSlots)%nat /\ exists b0, In b0 (all_batches X) /\ b_self b0 = b_self b).
  { apply in_app_iff in Hb as [HX|HO].
    - split; [exact (proj2 (proj1 (Forall_forall _ _) (wq_batches _ (wfc_quarantine _ _ _ _ _ qWF)) b HX)) | exists b; auto].
    - destruct (HB b HO) as [HS HL]. split; [exact HL|]. apply in_map_iff in HS as (b0 & E & H0). exists b0. auto. }
  destruct LB as [LB (b0 & Hb0 & E0)]. exists b0. split; [exact Hb0|]. rewrite E0.
  unfold kBatchSlots, kBatchBytes in *. lia.
Qed.

Lemma raw_out : forall a, 0 <= a < 2 ^ 64 -> ~ dwin_q (as_inst B) ly sp0 X S1 P a -> rd' a = rd a.
Proof.
intros a Ha Hn. apply aview_mem_eq. destruct DQ as (D1 & _). apply D1. rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.

Lemma AGq : forall a, aowned B ly X a -> ~ qhdr (as_inst B) ly a -> ~ inXb a -> rd' a = rd a.
Proof.
intros a Ho NQ NB. pose proof (AR_owned_low_law_ok_cf im_segs B ly X Hp W mem md a HAR Ho) as [L1 L2].
pose proof ASAN_CEIL_range as [CR _]. unfold ASAN_CEIL in CR.
apply raw_out; [lia|]. apply not_dwin; [|exact NQ | exact NB].
intros Hs. exact (AR_stack_law_ok_cf im_segs B ly X Hp W mem md a HAR Hs Ho).
Qed.

Definition okq (a : Z) : Prop := ~ qhdr (as_inst B) ly a /\ ~ inXb a.

Lemma cells_xfer : forall l, Forall (cell_bytes_owned B ly X) l ->
Forall (fun c => forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> okq (aeval B ly (c_at c) + k)) l ->
Forall (cell_holds B ly rd) l -> Forall (cell_holds B ly rd') l.
Proof.
intros l OW OK H. apply Forall_forall. intros c Hc.
eapply cell_holds_agree; [exact (proj1 (Forall_forall _ _) H c Hc)|]. intros k Hk.
destruct (proj1 (Forall_forall _ _) OK c Hc k Hk) as [NQ NB].
exact (AGq _ (proj1 (Forall_forall _ _) OW c Hc k Hk) NQ NB).
Qed.

(* Zones that are apart from the quarantine header words and from X's batch objects. *)
Lemma okq_far : forall a, ~ in_zr a (ly_img ly) -> ~ (ly_T ly + t_qc <= a < ly_T ly + t_qc + 32) ->
~ (region_base ly kBatchClass <= a < region_base ly kBatchClass + kFreeArrayOffset) -> okq a.
Proof.
intros a NI NT NR. split.
- intros Hq. destruct (qhdr_zone a Hq) as [[_ HI]|HT]; [exact (NI HI) | exact (NT HT)].
- intros Hb. exact (NR (inXb_zone a Hb)).
Qed.

Lemma okq_static : forall j e a, (3 <= j <= 7)%nat \/ j = 1%nat -> nth_error (static_extents ly) j = Some e ->
fst e <= a < fst e + snd e -> okq a.
Proof.
intros j e a Hj He Ha. pose proof region24_in_prim as (R1 & R2 & _).
apply okq_far.
- intros HI. pose proof (SX j 9 e (ly_img ly) ltac:(lia) He eq_refl) as D. unfold zdisjoint, in_zr in *. lia.
- intros HT. assert (j <> 2%nat) by lia. destruct (Nat.lt_ge_cases j 2).
  + pose proof (SX j 2 e _ H0 He eq_refl) as D. unfold zdisjoint, t_qc, kThreadObjSize in *. cbn [fst snd] in D. lia.
  + pose proof (SX 2 j _ e ltac:(lia) eq_refl He) as D. unfold zdisjoint, t_qc, kThreadObjSize in *. cbn [fst snd] in D. lia.
- intros HR. pose proof (SX 0 j _ e ltac:(lia) eq_refl He) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

Lemma okq_T : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> ~ (ly_T ly + t_qc <= a < ly_T ly + t_qc + 32) -> okq a.
Proof.
intros a Ha NT. pose proof region24_in_prim as (R1 & R2 & _). apply okq_far; [| exact NT |].
- intros HI. sx 2%nat 9%nat. unfold in_zr in HI. lia.
- intros HR. sx 0%nat 2%nat. lia.
Qed.

Lemma okq_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize ->
~ (region_base ly kBatchClass <= a < region_base ly kBatchClass + kFreeArrayOffset) -> okq a.
Proof.
intros a Ha NR. apply okq_far; [| | exact NR].
- intros HI. sx 0%nat 9%nat. unfold in_zr in HI. lia.
- intros HT. sx 0%nat 2%nat. unfold t_qc, kThreadObjSize in *. lia.
Qed.

Lemma okq_sec : forall e a, In e (sec_extents ly X) -> fst e <= a < fst e + snd e -> okq a.
Proof.
intros e a He Ha. pose proof region24_in_prim as (R1 & R2 & _).
assert (D : forall j y, nth_error (static_extents ly) j = Some y -> zdisjoint e y).
{ intros j y Hj. eapply (pairwise_In zdisjoint _ e y (sec_extents ly X) (static_extents ly) eq_refl (proj2 (amc_placed _ _ _ _ _ qM)) He).
  eapply nth_error_In. exact Hj. }
apply okq_far.
- intros HI. pose proof (D 9%nat _ eq_refl) as DJ. unfold zdisjoint, in_zr in *. cbn [fst snd] in *. lia.
- intros HT. pose proof (D 2%nat _ eq_refl) as DJ. unfold zdisjoint, t_qc, kThreadObjSize in *. cbn [fst snd] in *. lia.
- intros HR. pose proof (D 0%nat _ eq_refl) as DJ. unfold zdisjoint in *. cbn [fst snd] in *. lia.
Qed.

Lemma okq_img : forall a, in_zr a (ly_img ly) -> ~ qhdr_inst B a -> okq a.
Proof.
intros a HI NQ. pose proof region24_in_prim as (R1 & R2 & _). split.
- intros Hq. destruct (qhdr_zone a Hq) as [[HQ _]|HT]; [exact (NQ HQ)|]. sx 2%nat 9%nat. unfold in_zr, t_qc, kThreadObjSize in *. lia.
- intros Hb. pose proof (inXb_zone a Hb) as HR. sx 0%nat 9%nat. unfold in_zr in *. lia.
Qed.

Lemma okq_shadow : forall a, SHADOW_OFF <= a < kHighMemBeg -> okq a.
Proof.
intros a Ha. pose proof region24_in_prim as (R1 & R2 & R3).
apply okq_far; [| | intros HR; lia].
- intros HI. pose proof (lo_img _ qLO) as (I1 & I2 & I3 & _). unfold in_zr, SHADOW_OFF, kImgEnd, kImgLo in *. lia.
- intros HT. pose proof (proj1 (Forall_forall _ _) (lo_app _ qLO) (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as IA.
  unfold in_app, t_qc, kThreadObjSize, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. cbn [fst snd] in IA. lia.
Qed.

Lemma okq_chunk : forall k a, In k (st_chunks X) -> ck_base B ly k <= a < ck_base B ly k + ck_extent k -> okq a.
Proof.
intros k a Hk Ha. split.
- intros Hq. destruct (qhdr_zone a Hq) as [[_ HI]|HT].
  + exact (proj1 (chunk_apart_cf B ly X Hp _ k a qM Hk Ha) HI).
  + destruct (extent_zone_cf B ly X Hp _ k qM Hk) as [[P1 P2]|(m & len & Hin & E1 & E2)].
    * sx 0%nat 2%nat. unfold t_qc, kThreadObjSize in *. lia.
    * assert (DJ : zdisjoint (m, len) (ly_T ly, kThreadObjSize)).
      { eapply (pairwise_In zdisjoint _ (m, len) _ (sec_extents ly X) (static_extents ly) eq_refl (proj2 (amc_placed _ _ _ _ _ qM)) Hin).
        unfold static_extents, owned_extents. cbn. tauto. }
      unfold zdisjoint, kPage, t_qc, kThreadObjSize in *. cbn [fst snd] in DJ. lia.
- intros (b & Hb & Hab). pose proof (batch_vs_chunk_x b k Hb Hk) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The cells of the cut state.                                                                                      *)
Lemma oldc : forall c, In c (acells_cf B ly X) -> cell_holds B ly rd c.
Proof. intros c Hc. exact (proj1 (Forall_forall _ _) (amc_cells _ _ _ _ _ qM) c Hc). Qed.
Lemma ownc : forall c, In c (acells_cf B ly X) -> cell_bytes_owned B ly X c.
Proof. intros c Hc. exact (proj1 (Forall_forall _ _) (acells_owned_cf B ly X Hp _ qM) c Hc). Qed.

Ltac part n := apply Forall_forall; intros ? HIN; first [apply oldc | apply ownc]; unfold acells_cf; rewrite !in_app_iff;
  do n right; first [left | idtac]; first [exact HIN | (apply in_flat_map; eauto)].

Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells_cf X) (zseq 1 31)).
Proof.
apply cells_xfer.
- apply Forall_forall. intros c HIN. apply ownc. unfold acells_cf. rewrite !in_app_iff. left. exact HIN.
- apply Forall_forall. intros c Hc. apply in_flat_map in Hc as (cl & Hcl & Hc). apply zseq_In in Hcl.
  pose proof (lo_space_in _ qLO) as [S1' S2']. pose proof region24_in_prim as (R1 & R2 & _).
  unfold region_cells_cf, region_cells, z8, z1, c8, c1 in Hc. cbn [removelast] in Hc.
  assert (HA : ly_space ly + kRegionInfoOff + 128 * cl <= aeval B ly (c_at c) /\
    aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= ly_space ly + kRegionInfoOff + 128 * cl + 64).
  { destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn [c_at c_w aeval aoff]; lia. }
  intros k Hk. apply okq_prim; unfold region_base, kFreeArrayOffset, kRegionInfoOff, kSpaceSize, kPrimResvSize in *;
    rewrite ?region_off_eq by (unfold kBatchClass; lia); unfold kBatchClass in *; lia.
- apply Forall_forall. intros c HIN. apply oldc. unfold acells_cf. rewrite !in_app_iff. left. exact HIN.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Band bytes, the view, and the quarantine's header words after the cut.                                          *)
Lemma okq_band : forall a, in_band_rw a -> okq a.
Proof.
intros a Hb. pose proof region24_in_prim as (R1 & R2 & R3). apply okq_far.
- intros HI. pose proof (lo_img _ qLO) as (I1 & I2 & I3 & _). unfold in_zr in HI. rewrite I1 in HI.
  unfold in_band_rw, kImgEnd, kImgLo, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. lia.
- intros HT. pose proof (proj1 (Forall_forall _ _) (lo_app _ qLO) (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as IA.
  cbn [fst snd] in IA. unfold in_app, t_qc, kThreadObjSize, in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. lia.
- intros HR. unfold in_band_rw, kHighShadowEnd, kHighMemBeg, kLowShadowEnd, kHighShadowBeg, kLowShadowBeg in *. lia.
Qed.

Lemma stk_band : forall a, in_band_rw a -> ~ (ly_stk_lo ly <= a < ly_stk_hi ly).
Proof.
intros a Hb Hs. destruct (lo_top _ qLO) as (_ & _ & _ & _ & _ & _ & L7).
unfold in_band_rw, kHighShadowEnd, kHighMemBeg, kLowShadowEnd, kHighShadowBeg, kLowShadowBeg in *. lia.
Qed.

Lemma band_out : forall a, in_band_rw a -> ~ dwin_q (as_inst B) ly sp0 X S1 P a.
Proof. intros a Hb. apply not_dwin; [exact (stk_band a Hb) | exact (proj1 (okq_band a Hb)) | exact (proj2 (okq_band a Hb))]. Qed.

Lemma band_rng : forall a, in_band_rw a -> 0 <= a < 2 ^ 64.
Proof. intros a Hb. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hb. lia. Qed.

Lemma band_mem : forall a, in_band_rw a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros a Hb. destruct DQ as (D1 & _). apply D1. rewrite unsigned_lit_small by exact (band_rng a Hb). exact (band_out a Hb).
Qed.

Lemma band_same : forall a, in_band_rw a -> rd' a = rd a.
Proof. intros a Hb. exact (raw_out a (band_rng a Hb) (band_out a Hb)). Qed.

Lemma qcells : Forall (cell_holds B ly rd') (quar_cells S1). Proof. exact (proj1 (proj2 DQ)). Qed.

Lemma qc_vis : forall root q, (forall d, aeval B ly (aoff root d) = aeval B ly root + d) ->
Forall (cell_holds B ly rd') (qc_cells root q) -> forall a, aeval B ly root <= a < aeval B ly root + 32 -> rd' a <> None.
Proof.
intros root q E H a Ha. unfold qc_cells in H.
apply Forall_cons_iff in H as [H0 H]. apply Forall_cons_iff in H as [H8 H]. apply Forall_cons_iff in H as [H16 H].
apply Forall_cons_iff in H as [H24 _]. unfold z8, c8 in H0, H8, H16, H24.
destruct (Z_lt_le_dec a (aeval B ly root + 8)).
{ eapply (ch_some_x B ly rd' _ _ _ a H0). change (Z.of_nat 8) with 8. lia. }
destruct (Z_lt_le_dec a (aeval B ly root + 16)).
{ eapply (ch_some_x B ly rd' _ _ _ a H8). rewrite E. change (Z.of_nat 8) with 8. lia. }
destruct (Z_lt_le_dec a (aeval B ly root + 24)).
{ eapply (ch_some_x B ly rd' _ _ _ a H16). rewrite E. change (Z.of_nat 8) with 8. lia. }
eapply (ch_some_x B ly rd' _ _ _ a H24). rewrite E. change (Z.of_nat 8) with 8. lia.
Qed.

Lemma qhdr_vis : forall a, qhdr (as_inst B) ly a -> rd' a <> None.
Proof.
intros a Hq. pose proof qcells as C. unfold quar_cells in C.
apply Forall_cons_iff in C as [C1 C]. apply Forall_cons_iff in C as [C2 C]. apply Forall_app in C as [CT CG].
unfold z1, c1 in C1, C2.
destruct Hq as [Hq|[Hq|Hq]].
- unfold o_quar in Hq.
  destruct (Z.eq_dec a (as_inst B + o_q_cmutex)) as [E1|N1].
  + eapply (ch_some_x B ly rd' _ _ _ a C1). cbn [aeval]. change (Z.of_nat 1) with 1. lia.
  + destruct (Z.eq_dec a (as_inst B + o_q_rmutex)) as [E2|N2].
    * eapply (ch_some_x B ly rd' _ _ _ a C2). cbn [aeval]. change (Z.of_nat 1) with 1. lia.
    * destruct DQ as (_ & _ & _ & D4). apply (val_mem_vis im_segs (w_H W) mem' _ 2 0 a D4).
      unfold o_q_cmutex, o_q_rmutex in *. change (Z.of_nat 2) with 2. lia.
- apply (qc_vis (AInst o_q_size) _ (fun d => ltac:(cbn; lia)) CG). cbn [aeval]. unfold o_q_size, o_quar in *. lia.
- apply (qc_vis (AT t_qc) _ (fun d => ltac:(cbn; lia)) CT). cbn [aeval]. lia.
Qed.

Lemma VISq : forall a, rd a <> None -> rd' a <> None.
Proof.
intros a0 Hv0.
set (a := bv_unsigned (Z_to_bv 64 a0)).
assert (EA : Z_to_bv 64 a = Z_to_bv 64 a0) by apply Z_to_bv_bv_unsigned.
assert (RA : 0 <= a < 2 ^ 64).
{ pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a0)) as R. unfold bv_modulus in R. exact R. }
assert (RV : forall H (m : word -> option byte), aview im_segs H m a = aview im_segs H m a0)
  by (intros H m; unfold aview, mbyte, mrestrict; rewrite EA; reflexivity).
rewrite <- (RV (w_H W) mem) in Hv0. rewrite <- (RV (w_H W) mem'). clearbody a. clear RV EA.
rename Hv0 into Hv.
assert (D : qhdr (as_inst B) ly a \/ ~ qhdr (as_inst B) ly a) by (unfold qhdr; lia).
destruct D as [Q|NQ]; [exact (qhdr_vis a Q)|].
destruct DQ as (_ & _ & D3 & _). specialize (D3 a). try specialize (D3 RA). specialize (D3 NQ). unfold apresent in D3.
unfold aview, mbyte, mrestrict in *. revert Hv.
destruct (w_H W (Z_to_bv 64 a)) eqn:E; intros Hv; [exact Hv|]. revert Hv.
destruct (mem (Z_to_bv 64 a)) as [b|] eqn:Em; intros Hv.
- destruct (D3 (conj eq_refl (ex_intro _ b eq_refl))) as [_ [b' Eb']]. rewrite Eb'. discriminate.
- destruct (mem' (Z_to_bv 64 a)) as [b'|]; [discriminate | exact Hv].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The cell families of the cut state other than the quarantine's.                                                  *)
Lemma Forall_flat_map_in : forall {A C} (Q : C -> Prop) (f : A -> list C) l x, Forall Q (flat_map f l) -> In x l -> Forall Q (f x).
Proof. intros A C Q f l x H Hx. apply Forall_forall. intros y Hy. apply (proj1 (Forall_forall _ _) H). apply in_flat_map. exists x. auto. Qed.

Lemma cells_rng : forall lo len l, (forall a, lo <= a < lo + len -> okq a) ->
Forall (fun c => lo <= aeval B ly (c_at c) /\ aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len) l ->
Forall (cell_bytes_owned B ly X) l -> Forall (cell_holds B ly rd) l -> Forall (cell_holds B ly rd') l.
Proof.
intros lo len l OK R OW H. apply (cells_xfer l OW); [|exact H].
eapply Forall_impl; [|exact R]. intros c [R1 R2] k Hk. apply OK. lia.
Qed.

Lemma okq_area : forall r a, In r (asyms_areas B) -> fst r <= a < fst r + snd r -> ~ qhdr_inst B a -> okq a.
Proof. intros r a Hr Ha NQ. exact (okq_img a (img_area r a Hr Ha) NQ). Qed.
Lemma nq_depot : forall a, as_depot B <= a < as_depot B + 4 * 2 ^ 20 + 32 -> ~ qhdr_inst B a.
Proof. intros a Ha Hq. exact (proj1 (IQA B TS a Hq) Ha). Qed.
Lemma nq_store : forall a, as_store B <= a < as_store B + 32 -> ~ qhdr_inst B a.
Proof. intros a Ha Hq. exact (proj1 (proj2 (IQA B TS a Hq)) Ha). Qed.
Lemma nq_ialloc : forall a, as_ialloc_lo B <= a < as_ialloc_hi B -> ~ qhdr_inst B a.
Proof. intros a Ha Hq. exact (proj1 (proj2 (proj2 (IQA B TS a Hq))) Ha). Qed.
Lemma nq_iflag : forall a, as_ialloc_flag B <= a < as_ialloc_flag B + 2 -> ~ qhdr_inst B a.
Proof. intros a Ha Hq. exact (proj2 (proj2 (proj2 (IQA B TS a Hq))) Ha). Qed.
Lemma nq_errb : forall a, cf_errbuf_obj <= a < cf_errbuf_obj + 56 -> ~ qhdr_inst B a.
Proof.
intros a Ha Hq. apply (EAP B TS a Ha). unfold qhdr_inst, o_quar in Hq. lia.
Qed.

(* ARX_cf's two machine-cell conjuncts at the cut: the cut moves only the quarantine, and its writes (dmem_q) miss
   the exhausted bytes (RegionInfo, primary reserve) and the buffer's object (owned static, off the header words). *)
Lemma q_exh_errb : errb_obj_owned_t B -> EXH_OFF_OK ->
exh_cell_cf B ly X rd -> errb_cells_cf B ly X rd -> exh_cell_cf B ly S1 rd' /\ errb_cells_cf B ly S1 rd'.
Proof using B ly X g' W mem mem' md sp0 P Hp HAR HB HSP DQ HQS TS IQA EAP CA.
intros EOO EXO HE HEB. split.
- apply (exh_cell_cf_frame B ly ly X S1 rd rd' HE); [intros c; reflexivity|].
  intros c Hc. unfold EXH_OFF_OK in EXO.
  change (aeval B ly (aoff (ASp (kRegionInfoOff + 128 * c)) cf_exh_off)) with (ly_space ly + (kRegionInfoOff + 128 * c + cf_exh_off)).
  pose proof (lo_space_in _ qLO) as [S1' S2']. pose proof region24_in_prim as (R1 & R2 & _).
  assert (OK : okq (ly_space ly + (kRegionInfoOff + 128 * c + cf_exh_off))).
  { apply okq_prim; unfold region_base, kFreeArrayOffset, kRegionInfoOff, kSpaceSize, kPrimResvSize in *;
      rewrite ?region_off_eq by (unfold kBatchClass; lia); unfold kBatchClass in *; lia. }
  apply AGq; [apply (own_rinfo_cf B ly X Hp rd _ qM); lia | exact (proj1 OK) | exact (proj2 OK)].
- apply (errb_cells_cf_frame B ly ly X S1 rd rd' HEB); try reflexivity.
  + intros a Ha. pose proof (EOO a Ha) as OS.
    assert (OK : okq a).
    { apply okq_img; [|exact (nq_errb a Ha)].
      pose proof (amc_static_img _ _ _ _ _ qM) as SI. apply Exists_exists in OS as (r & Hr & Ha').
      pose proof (proj1 (Forall_forall _ _) SI r ltac:(apply in_app_iff; left; exact Hr)) as SUB.
      unfold zr_sub, in_zr in *. lia. }
    apply AGq; [exact (own_static_cf B ly X Hp rd a qM OS) | exact (proj1 OK) | exact (proj2 OK)].
  + exact VISq.
Qed.

(* Printf's two cells at the cut (field round 3): owned static, inside the image and apart from the instance object
   (pf_cells_owned_t), so off the header words the cut writes. *)
Lemma q_pf : pf_cells_owned_t B -> pf_cells_cf B ly rd -> pf_cells_cf B ly rd'.
Proof.
intros PO HP. apply (pf_cells_frame_cf B ly rd rd'); [|exact HP].
intros a Ha. destruct (proj1 PO a Ha) as [OS NI]. pose proof OS as OS'.
assert (OK : okq a).
{ apply okq_img.
  - pose proof (amc_static_img _ _ _ _ _ qM) as SI. apply Exists_exists in OS' as (r & Hr & Ha').
    pose proof (proj1 (Forall_forall _ _) SI r ltac:(apply in_app_iff; left; exact Hr)) as SUB.
    unfold zr_sub, in_zr in *. lia.
  - intros Hq. apply NI. unfold qhdr_inst, o_quar in Hq. unfold kInstObjSize. lia. }
apply AGq; [exact (own_static_cf B ly X Hp rd a qM OS) | exact (proj1 OK) | exact (proj2 OK)].
Qed.

Ltac fcons := apply Forall_cons; [cbn; lia|].

Lemma cells_cache : forall c, 1 <= c <= 31 -> Forall (cell_holds B ly rd) (cache_cells X c) -> Forall (cell_holds B ly rd') (cache_cells X c).
Proof.
intros c Hc O. apply (cells_rng (ly_T ly + t_cache) (kThreadObjSize - t_cache)); [| |exact (cache_cells_owned_cf B ly X Hp _ c qM Hc) | exact O].
- intros a Ha. apply okq_T; unfold t_cache, t_qc, kThreadObjSize in *; lia.
- pose proof (wfc_classes _ _ _ _ _ qWF c Hc) as CL. pose proof (wrc_cache _ _ _ _ _ _ CL) as WC. pose proof (class_ok c Hc) as (_ & _ & _ & K4 & _).
  unfold cache_cells, t_cache, kThreadObjSize. destruct (st_cache_inited X).
  + destruct WC as [PM PL]. repeat fcons. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i v] & <- & Hiv). cbn [fst snd c_at c_w z4 c4 aeval aoff].
    apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. lia.
  + repeat fcons. apply Forall_nil.
Qed.

Lemma cells_chunk : forall k, In k (st_chunks X) -> Forall (cell_holds B ly rd) (chunk_cells k) -> Forall (cell_holds B ly rd') (chunk_cells k).
Proof.
intros k Hk O. pose proof (chunk_facts_cf B ly X Hp _ k qM Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
apply (cells_rng (ck_base B ly k) (ck_rz k)); [| |exact (chunk_cells_owned_cf B ly X Hp _ k qM Hk) | exact O].
- intros a Ha. apply (okq_chunk k a Hk). pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (_ & Q1 & _). lia.
- assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
  { intros d. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia. }
  assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
  { intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia. }
  assert (EA0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
  unfold chunk_cells, kChunkHeaderSize. apply Forall_app. split.
  + repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil.
  + destruct (Z.eqb_spec (ck_rz k) 16); [apply Forall_nil|].
    assert (32 <= ck_rz k). { apply Z.mod_divide in G6 as [q Hq]; [|lia]. lia. }
    repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil.
Qed.

Lemma cells_sec : Forall (cell_holds B ly rd) (sec_cells X) -> Forall (cell_holds B ly rd') (sec_cells X).
Proof.
intros O. apply (cells_xfer _ (sec_cells_owned_cf B ly X Hp _ qM)); [|exact O].
pose proof (wfc_secondary _ _ _ _ _ qWF) as XS. destruct XS as [Snd Sac Sal Sres Sral].
assert (OI : forall d w, 0 <= d -> d + w <= 728 + 152 -> forall k, 0 <= k < w -> okq (as_inst B + d + k)).
{ intros d w Hd Hw k Hk. apply okq_img; [apply img_inst; lia | unfold qhdr_inst, o_quar; lia]. }
unfold sec_cells.
apply Forall_cons; [intros k Hk; cbn [c_at c_w aeval c8 z8] in *; unfold o_sec_reserved in *; apply (OI 112 8); lia|].
apply Forall_cons; [intros k Hk; cbn [c_at c_w aeval c8 z8] in *; unfold o_sec_n in *; apply (OI 120 8); lia|].
apply Forall_cons; [intros k Hk; cbn [c_at c_w aeval c1 z1] in *; unfold o_sec_mutex in *; apply (OI 680 1); lia|].
apply Forall_app. split.
- apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
  intros k Hk. cbn [c_at c_w aeval fst snd c8] in *.
  apply (okq_static 1 (ly_Q ly, kPtrArrayResv)); [right; reflexivity | reflexivity | cbn [fst snd]; unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *; lia].
- apply Forall_forall. intros c Hc. apply in_flat_map in Hc as (k0 & Hk0 & Hc).
  pose proof (chunk_facts_cf B ly X Hp _ k0 qM Hk0) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
  destruct (ck_beg k0) as [|o|r o|c' p] eqn:Eb; try solve [destruct Hc].
  destruct GG as (-> & _ & Gbase & Gext & Gin & _).
  assert (SM : 4096 + 17 <= sec_map_size (ck_req k0)) by (pose proof (req_size_bounds (ck_req k0) ltac:(lia)) as (_ & Q1 & _); unfold kPage in *; lia).
  destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; intros k Hk; cbn [c_at c_w aeval c8 z8] in *; apply (okq_sec _ _ Gin); cbn [fst snd]; lia.
Qed.

Lemma cells_fs : Forall (cell_holds B ly rd) (fs_cells X) -> Forall (cell_holds B ly rd') (fs_cells X).
Proof.
intros O. apply (cells_rng (ly_F ly) kFakeFramesOff); [| |exact (fs_cells_owned_cf B ly X Hp _ qM) | exact O].
- intros a Ha. apply (okq_static 3 (ly_F ly, kFakeStackSize)); [left; lia | reflexivity | cbn [fst snd]; unfold kFakeFramesOff, kFakeStackSize in *; lia].
- unfold fs_cells, kFakeFramesOff. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|].
  apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih. cbn. lia.
Qed.

Lemma cells_depot : Forall (cell_holds B ly rd) (depot_cells ly X) -> Forall (cell_holds B ly rd') (depot_cells ly X).
Proof.
intros O. apply (cells_xfer _ (depot_cells_owned_cf B ly X Hp _ qM)); [|exact O].
unfold depot_cells, d_nuniq, d_map1, s_total, s_block0.
apply Forall_cons; [intros k Hk; cbn [c_at c_w aeval c4 z4] in *;
  apply (okq_area (as_depot B, 4 * 2 ^ 20 + 32)); [cbn; tauto | cbn [fst snd]; lia | apply nq_depot; lia]|].
apply Forall_cons; [intros k Hk; cbn [c_at c_w aeval c8 z8] in *;
  apply (okq_area (as_depot B, 4 * 2 ^ 20 + 32)); [cbn; tauto | cbn [fst snd]; lia | apply nq_depot; lia]|].
apply Forall_cons; [intros k Hk; cbn [c_at c_w aeval c8 z8] in *;
  apply (okq_area (as_store B, 32)); [cbn; tauto | cbn [fst snd]; lia | apply nq_store; lia]|].
apply Forall_cons; [intros k Hk; cbn [c_at c_w aeval c8 z8] in *;
  apply (okq_area (as_store B, 32)); [cbn; tauto | cbn [fst snd]; lia | apply nq_store; lia]|].
apply Forall_nil.
Qed.

Lemma cells_ialloc : Forall (cell_holds B ly rd) (ialloc_cells B X) -> Forall (cell_holds B ly rd') (ialloc_cells B X).
Proof.
intros O. apply (cells_xfer _ (ialloc_cells_owned_cf B ly X Hp _ qM)); [|exact O].
pose proof (aso_ialloc _ qSY) as [I1 I2]. unfold ialloc_cells. cbv zeta.
apply Forall_cons; [intros k Hk; cbn [c_at c_w aeval c1 z1] in *;
  apply (okq_area (as_ialloc_flag B, 2)); [cbn; tauto | cbn [fst snd]; lia | apply nq_iflag; lia]|].
apply Forall_cons; [intros k Hk; cbn [c_at c_w aeval c1 z1] in *;
  apply (okq_area (as_ialloc_flag B, 2)); [cbn; tauto | cbn [fst snd]; lia | apply nq_iflag; lia]|].
apply Forall_cons; [intros k Hk; cbn [c_at c_w aeval c8 z8] in *;
  apply (okq_area (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [cbn; tauto | cbn [fst snd]; lia | apply nq_ialloc; lia]|].
apply Forall_cons; [intros k Hk; cbn [c_at c_w aeval c8 z8] in *;
  apply (okq_area (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [cbn; tauto | cbn [fst snd]; lia | apply nq_ialloc; lia]|].
apply Forall_nil.
Qed.

Lemma cells_thread : Forall (cell_holds B ly rd) thread_cells -> Forall (cell_holds B ly rd') thread_cells.
Proof.
intros O. apply (cells_xfer _ (thread_cells_owned_cf B ly X Hp _ qM)); [|exact O].
unfold thread_cells. apply Forall_cons; [|apply Forall_nil].
intros k Hk. cbn [c_at c_w aeval c1 z1] in *. apply okq_T; unfold t_unwinding, t_qc, kThreadObjSize in *; lia.
Qed.

Lemma cells_S1 : Forall (cell_holds B ly rd') (acells_cf B ly S1).
Proof.
pose proof (amc_cells _ _ _ _ _ qM) as C. unfold acells_cf in C. rewrite !Forall_app in C.
destruct C as (O1 & O2 & O3 & O4 & _ & O6 & O7 & O8 & O9).
unfold acells_cf. rewrite !Forall_app.
split; [exact cells_regions|].
split; [apply Forall_flat_map'; intros c Hc0; pose proof Hc0 as Hc; apply zseq_In in Hc;
  exact (cells_cache c ltac:(lia) (Forall_flat_map_in _ _ _ c O2 Hc0))|].
split; [apply Forall_flat_map'; intros k Hk; exact (cells_chunk k Hk (Forall_flat_map_in _ _ _ k O3 Hk))|].
split; [exact (cells_sec O4)|].
split; [exact qcells|].
split; [exact (cells_fs O6)|].
split; [exact (cells_depot O7)|].
split; [exact (cells_ialloc O8) | exact (cells_thread O9)].
Qed.

Lemma cells_const : Forall (cell_holds B ly rd') (as_const B ly).
Proof.
pose proof (amc_const _ _ _ _ _ qM) as O. pose proof (const_cells_owned_cf B ly X Hp _ qM) as OW.
apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) O c Hc) as Oc.
assert (Hc' : In c (im_const ly)) by (rewrite <- (im_const_eq B ly TS); exact Hc).
destruct (CA B ly c TS qIMG Hc') as [(E1 & E2 & E3)|NA].
- destruct c as [e w v]. cbn [c_at c_w c_val] in E1, E2, E3. subst w v.
  unfold cell_holds. cbn [c_at c_w c_val]. intros k Hk. rewrite E1.
  destruct DQ as (_ & _ & _ & D4). rewrite (val_mem_zero2 im_segs (w_H W) mem' _ D4 k Hk). cbn [aeval].
  destruct k as [|[|k]]; [reflexivity | reflexivity | lia].
- eapply cell_holds_agree; [exact Oc|]. intros k Hk. destruct (NA k Hk) as [NQ NP].
  apply AGq; [exact (proj1 (Forall_forall _ _) OW c Hc k Hk) | exact NQ |].
  intros Hb. apply NP. pose proof (inXb_zone _ Hb). pose proof region24_in_prim as (R1 & R2 & _). lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The entry state's batch objects are visible; the cut state's junk.                                              *)
Lemma in_combine_seq_nth : forall {A} (l : list A) s i x, nth_error l i = Some x -> In ((s + i)%nat, x) (combine (seq s (length l)) l).
Proof.
intros A l. induction l as [|y t IH]; intros s i x H; [destruct i; discriminate|].
destruct i as [|i]; cbn in H |- *.
- injection H as <-. left. f_equal. lia.
- right. replace (s + S i)%nat with (S s + i)%nat by lia. exact (IH (S s) i x H).
Qed.

Lemma batch_cells_cover : forall (rd0 : reader) l b a, In b l -> Forall (cell_holds B ly rd0) (batch_cells l) ->
ly_space ly + b_self b <= a < ly_space ly + b_self b + 24 + 8 * Z.of_nat (length (b_items b)) -> rd0 a <> None.
Proof.
intros rd0 l. induction l as [|b0 t IH]; intros b a Hb H Ha; [destruct Hb|]. cbn [batch_cells] in H.
apply Forall_cons_iff in H as [H0 H]. apply Forall_cons_iff in H as [H8 H]. apply Forall_cons_iff in H as [H16 H].
apply Forall_app in H as [HI HT].
destruct Hb as [<-|Hb]; [|exact (IH b a Hb HT Ha)].
unfold z8, c8, batch_exp in H0, H8, H16.
destruct (Z_lt_le_dec a (ly_space ly + b_self b0 + 8)).
{ eapply (ch_some_x B ly rd0 _ _ _ a H0). cbn [aeval]. change (Z.of_nat 8) with 8. lia. }
destruct (Z_lt_le_dec a (ly_space ly + b_self b0 + 16)).
{ eapply (ch_some_x B ly rd0 _ _ _ a H8). cbn [aeval aoff]. change (Z.of_nat 8) with 8. lia. }
destruct (Z_lt_le_dec a (ly_space ly + b_self b0 + 24)).
{ eapply (ch_some_x B ly rd0 _ _ _ a H16). cbn [aeval aoff]. change (Z.of_nat 8) with 8. lia. }
remember (a - (ly_space ly + b_self b0 + 24)) as d eqn:Ed.
pose proof (Z.div_mod d 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound d 8 ltac:(lia)) as MB.
assert (Q0 : 0 <= d / 8) by (apply Z.div_pos; lia).
assert (Q1 : d / 8 < Z.of_nat (length (b_items b0))) by lia.
remember (Z.to_nat (d / 8)) as i eqn:Ei0.
assert (Ei : Z.of_nat i = d / 8) by (subst i; apply Z2Nat.id; lia).
assert (Hi : (i < length (b_items b0))%nat) by lia.
destruct (nth_error (b_items b0) i) as [kk|] eqn:Ek; [|apply nth_error_None in Ek; lia].
pose proof (in_combine_seq_nth (b_items b0) 0 i kk Ek) as IC. cbn [Nat.add] in IC.
assert (IN : In (c8 (aoff (batch_exp b0) (24 + 8 * Z.of_nat i)) (sptr_exp (ck_hdr kk)))
  (map (fun iv => c8 (aoff (batch_exp b0) (24 + 8 * Z.of_nat (fst iv))) (sptr_exp (ck_hdr (snd iv))))
  (combine (seq 0 (length (b_items b0))) (b_items b0)))).
{ apply in_map_iff. exists (i, kk). split; [reflexivity | exact IC]. }
pose proof (proj1 (Forall_forall _ _) HI _ IN) as Hc. unfold c8, batch_exp in Hc.
eapply (ch_some_x B ly rd0 _ _ _ a Hc). cbn [aeval aoff]. change (Z.of_nat 8) with 8. lia.
Qed.

Lemma xbatch_vis : forall b, In b (all_batches X) -> forall a, ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes ->
rd a <> None.
Proof.
intros b Hb a Ha.
pose proof (amc_cells _ _ _ _ _ qM) as C. unfold acells_cf in C. rewrite !Forall_app in C. destruct C as (_ & _ & _ & _ & CQ & _).
pose proof (amc_junk _ _ _ _ _ qM) as J. unfold ajunk_cf in J. apply Forall_cons_iff in J as [_ J]. apply Forall_cons_iff in J as [_ J].
rewrite !Forall_app in J. destruct J as (_ & _ & _ & _ & JQ & _).
destruct (Z_lt_le_dec a (ly_space ly + b_self b + 24 + 8 * Z.of_nat (length (b_items b)))) as [Lc|Lj].
- unfold quar_cells, qc_cells in CQ. apply Forall_cons_iff in CQ as [_ CQ]. apply Forall_cons_iff in CQ as [_ CQ].
  apply Forall_app in CQ as [CT CG].
  do 4 (apply Forall_cons_iff in CT as [_ CT]). do 4 (apply Forall_cons_iff in CG as [_ CG]).
  unfold all_batches in Hb. apply in_app_iff in Hb as [Hb|Hb].
  + exact (batch_cells_cover rd _ b a Hb CT ltac:(lia)).
  + exact (batch_cells_cover rd _ b a Hb CG ltac:(lia)).
- assert (JB : range_vis B ly rd (aoff (batch_exp b) (24 + 8 * Z.of_nat (length (b_items b))),
    kBatchBytes - 24 - 8 * Z.of_nat (length (b_items b)))).
  { apply (proj1 (Forall_forall _ _) JQ). unfold quar_junk. apply in_flat_map. exists b. split; [exact Hb | left; reflexivity]. }
  specialize (JB (a - (ly_space ly + b_self b + 24 + 8 * Z.of_nat (length (b_items b))))). cbn [fst snd aeval aoff batch_exp] in JB.
  replace a with (ly_space ly + (b_self b + (24 + 8 * Z.of_nat (length (b_items b)))) +
    (a - (ly_space ly + b_self b + 24 + 8 * Z.of_nat (length (b_items b))))) by lia.
  apply JB. unfold kBatchBytes in *. lia.
Qed.

Lemma qjunk_S1 : Forall (range_vis B ly rd') (quar_junk S1).
Proof.
apply Forall_forall. intros r Hr. unfold quar_junk in Hr. apply in_flat_map in Hr as (b & Hb & Hr).
unfold batch_junk in Hr. destruct Hr as [<-|[]].
intros i Hi. cbn [fst snd aeval aoff batch_exp] in *. apply VISq.
destruct (HB b ltac:(apply in_app_iff; left; exact Hb)) as [HS HL].
apply in_map_iff in HS as (b0 & E0 & Hb0).
apply (xbatch_vis b0 Hb0). rewrite E0. unfold kBatchBytes in *. lia.
Qed.

Lemma junk_S1 : Forall (range_vis B ly rd') (ajunk_cf B ly S1).
Proof.
pose proof (amc_junk _ _ _ _ _ qM) as J. unfold ajunk_cf in J |- *.
apply Forall_cons_iff in J as [J1 J]. apply Forall_cons_iff in J as [J2 J]. rewrite !Forall_app in J.
destruct J as (J3 & J4 & J5 & J6 & _ & J8 & J9 & J10).
assert (K1 : forall r, range_vis B ly rd r -> range_vis B ly rd' r) by (intros r H i Hi; exact (VISq _ (H i Hi))).
assert (K : forall l, Forall (range_vis B ly rd) l -> Forall (range_vis B ly rd') l) by (intros l H; exact (Forall_impl _ K1 H)).
apply Forall_cons; [exact (K1 _ J1)|]. apply Forall_cons; [exact (K1 _ J2)|]. rewrite !Forall_app.
split; [exact (K _ J3)|]. split; [exact (K _ J4)|]. split; [exact (K _ J5)|]. split; [exact (K _ J6)|].
split; [exact qjunk_S1|]. split; [exact (K _ J8)|]. split; [exact (K _ J9) | exact (K _ J10)].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The cut record at the cut memory.                                                                                *)
Lemma okq_region : forall c a, 1 <= c <= 31 -> region_base ly c <= a < region_base ly c + 2 ^ 32 ->
(c = kBatchClass -> region_base ly c + kFreeArrayOffset <= a) -> okq a.
Proof.
intros c a Hc Ha H24. pose proof (region_in_prim ly c qLO Hc) as (R1 & R2 & _).
apply okq_prim; [lia|]. intros HR.
destruct (Z.eq_dec c kBatchClass) as [E|N]; [specialize (H24 E); subst c; lia|].
unfold region_base in *. rewrite !region_off_eq in * by (unfold kBatchClass; lia).
unfold kBatchClass, kFreeArrayOffset in *. lia.
Qed.

Lemma ARmcfR_S1 : WfR_cf (as_universe B) 0 0 0 S1 -> ARmcfR B ly S1 Hp rd'.
Proof.
intros HW. pose proof qM as M0.
destruct M0 as [Xwf Xuni Xsyms Xlay Xplaced Xconst Xcowned Xcells Xfa Xflags Xdepot Xshadow Xzsh Xjunk Xareas Xclient
  Xzero Xtsd Ximg Xhp Xxs Xexh Xerrb Xown Xpf Xpfo].
constructor.
- exact HW.
- exact Xuni.
- exact Xsyms.
- exact Xlay.
- exact Xplaced.
- exact cells_const.
- exact Xcowned.
- exact cells_S1.
- intros c i v Hc Hi Hv k Hk. change (reg S1 c) with (reg X c) in *.
  pose proof (wfc_classes _ _ _ _ _ Xwf c Hc) as CL. pose proof (wrc_fa_len _ _ _ _ _ _ CL) as FL.
  pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as FB.
  assert (FA : fa_base ly c <= fa_base ly c + 4 * i + Z.of_nat k < fa_base ly c + kFreeArrayMax) by lia.
  assert (OW : aowned B ly X (fa_base ly c + 4 * i + Z.of_nat k)) by (eapply own_fa_cf; [exact qM | exact Hc | lia]).
  assert (OK : okq (fa_base ly c + 4 * i + Z.of_nat k)).
  { apply (okq_region c); [exact Hc | unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax in *; lia |].
    intros _. unfold fa_base, region_base in *. lia. }
  rewrite (AGq _ OW (proj1 OK) (proj2 OK)). exact (Xfa c i v Hc Hi Hv k Hk).
- intros cid pos Hc Hpos. pose proof (flag_off_bounds cid pos Hc Hpos) as FB.
  assert (OW : aowned B ly X (flag_addr ly cid pos)) by (unfold flag_addr, kFakeFlagsOff in *; eapply own_F_low_cf; [exact qM | lia]).
  assert (OK : okq (flag_addr ly cid pos)) by (apply (okq_static 3 (ly_F ly, kFakeStackSize)); [left; lia | reflexivity |
    cbn [fst snd]; unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *; lia]).
  rewrite (AGq _ OW (proj1 OK) (proj2 OK)). exact (Xflags cid pos Hc Hpos).
- destruct Xdepot as (heads & links & D1 & D2 & D3). exists heads, links. split; [|split; [|exact D3]].
  + intros b Hb. destruct (D1 b Hb) as [H1 H2]. split; [exact H1|]. intros k Hk.
    assert (Ha : as_depot B <= as_depot B + 4 * b + Z.of_nat k < as_depot B + 4 * 2 ^ 20 + 32) by (unfold d_tab_words in Hb; lia).
    assert (OW : aowned B ly X (as_depot B + 4 * b + Z.of_nat k)) by
      (eapply (own_area_cf B ly X Hp _ (as_depot B, 4 * 2 ^ 20 + 32)); [exact qM | cbn; tauto | cbn [fst snd]; lia]).
    assert (OK : okq (as_depot B + 4 * b + Z.of_nat k)) by
      (apply (okq_area (as_depot B, 4 * 2 ^ 20 + 32)); [cbn; tauto | cbn [fst snd]; lia | apply nq_depot; lia]).
    rewrite (AGq _ OW (proj1 OK) (proj2 OK)). exact (H2 k Hk).
  + intros id Hid. change (depot_ids S1) with (depot_ids X) in Hid. destruct (D2 id Hid) as (H1 & H2 & H3). split; [exact H1|].
    assert (NB : depot_ids X <= 4097).
    { unfold depot_ids. pose proof (depot_len_bound _ _ Xuni (wfc_depot _ _ _ _ _ Xwf)) as DL. unfold DEPOT_MAX in DL. lia. }
    assert (OR : forall x, ly_NB ly + 16 * id <= x < ly_NB ly + 16 * id + 16 -> rd' x = rd x).
    { intros x Hx.
      assert (OW : aowned B ly X x) by
        (eapply (own_core_cf B ly X Hp _ (ly_NB ly, kNodesBlockSize)); [exact qM | unfold core_extents; cbn; tauto | cbn; unfold kNodesBlockSize; lia]).
      assert (OK : okq x) by (apply (okq_static 4 (ly_NB ly, kNodesBlockSize)); [left; lia | reflexivity | cbn [fst snd]; unfold kNodesBlockSize; lia]).
      exact (AGq _ OW (proj1 OK) (proj2 OK)). }
    split; intros k Hk; rewrite OR by lia; [exact (H2 k Hk) | exact (H3 k Hk)].
- (* the weak shadow transports: the chunks are the cut's, the queues only lose items (HQS), and every governed
     byte is owned and off the quarantine's header words *)
  apply (shadow_weak_ext_cf B ly X S1 Hp rd rd' eq_refl HQS (fun g => eq_refl)); [|exact (shadow_weak_of_ok_cf B ly Hp rd X Xshadow)].
  intros g v Hg Hv0. pose proof (ashadow_low_cf B ly X Hp _ g v qM Hv0) as SL. pose proof (okq_shadow _ SL) as OK.
  exact (AGq _ (ashadow_owned_cf B ly X Hp _ g v qM Hv0) (proj1 OK) (proj2 OK)).
- unfold zshadow_ok in *. apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. fold (shadow_addr (fst r)).
  change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
  pose proof (zshadow_low_cf B ly X Hp _ r i qM Hr Hi) as ZL. pose proof (okq_shadow _ ZL) as OK.
  rewrite (AGq _ (own_shadow_zero_cf B ly X Hp _ r i qM Hr Hi) (proj1 OK) (proj2 OK)). exact (proj1 (Forall_forall _ _) Xzsh r Hr i Hi).
- exact junk_S1.
- exact (Forall_range_vis_keep B ly rd rd' _ VISq Xareas).
- exact (Forall_range_vis_keep B ly rd rd' _ VISq Xclient).
- apply Forall_forall. intros r Hr i Hi. pose proof (aso_ialloc _ Xsyms) as [I1 I2].
  assert (Ha : as_ialloc_lo B <= aeval B ly (fst r) + i < as_ialloc_lo B + (as_ialloc_hi B - as_ialloc_lo B)).
  { unfold ialloc_zero in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; lia. }
  assert (OW : aowned B ly X (aeval B ly (fst r) + i)) by
    (eapply (own_area_cf B ly X Hp _ (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact qM | cbn; tauto | exact Ha]).
  assert (OK : okq (aeval B ly (fst r) + i)) by
    (apply (okq_area (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [cbn; tauto | exact Ha | apply nq_ialloc; lia]).
  rewrite (AGq _ OW (proj1 OK) (proj2 OK)). exact (proj1 (Forall_forall _ _) Xzero r Hr i Hi).
- exact Xtsd.
- exact Ximg.
- exact Xhp.
- exact Xxs.
- (* field round 2: the cut keeps the two machine cells (q_exh_errb), from the entry's own fields and rows *)
  exact (proj1 (q_exh_errb (proj1 (proj2 Xown)) (EXH_OFF_OK_of_t (proj1 Xown)) Xexh Xerrb)).
- exact (proj2 (q_exh_errb (proj1 (proj2 Xown)) (EXH_OFF_OK_of_t (proj1 Xown)) Xexh Xerrb)).
- exact Xown.
- exact (q_pf Xpfo Xpf).
- exact Xpfo.
Qed.

Lemma ARcfR_S1 : WfR_cf (as_universe B) 0 0 0 S1 -> forall md', m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md ->
eager_used md' = eager_used md -> ARcfR im_segs B ly S1 Hp W mem' md'.
Proof.
intros HW md' Ev El Ee. pose proof HAR as (M & LED & BUD & MW & HSH).
split; [exact (ARmcfR_S1 HW)|]. split; [|split; [|split]].
- assert (LED1 : ALedger_cf im_segs ly S1 md) by (destruct LED; constructor; assumption).
  eapply YG0qcf.ALedger_same_cf; [exact LED1 | exact Ev | exact El | exact Ee].
- (* the budget at the cut: the cut moves only the queues, so every term of abudget_cf is the entry's - the hull
     round's cf_hull by its frame law (st_secs and the chunks, hence sec_live_hulls, unchanged) *)
  destruct BUD as (BU1 & BU2 & BU3). split; [|split; [exact BU2 | exact BU3]].
  assert (HH : cf_hull S1 = cf_hull X) by (apply cf_hull_frame; reflexivity).
  unfold abudget_cf in *. rewrite HH. exact BU1.
- exact (amwf_same md md' Ev El MW).
- refine (ahs_transfer_cf im_segs B ly X Hp S1 (w_H W) mem mem' _ M HSH VISq _ _ _ _).
  + eapply al_img_env_cf; [exact qLO | exact LED].
  + intros a Ha _. exact (band_mem a Ha).
  + intros a _ C. exact C.
  + reflexivity.
  + intros g Hg Hga HF _. apply band_same. exact (shadow_addr_band_rw g Hga).
Qed.

End Q.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The re-quarantine fields at the cf instance.                                                                     *)
Section R.
Variable B : asyms.
Variable IOK : Z -> Prop.
Variable Hp : list Z.
Hypothesis IOK_inst : IOK_ok B IOK.
Hypothesis TS : im_syms B.
Hypothesis IQA : IMG_QAPART.
Hypothesis EAP : ERRB_QAPART.
Hypothesis CA : CONST_APART.
Hypothesis EOO : errb_obj_owned_t B.
Hypothesis EXO : EXH_OFF_t.

(* After the transfer every batch is one of the entry state's. *)
Lemma xfer_hb : forall X, Wf_cf (as_universe B) X ->
forall b, In b (all_batches (set_qglobal (YFeuC.transfer_g X) (set_qthread qc0 X)) ++ []) ->
In (b_self b) (map b_self (all_batches X)) /\ (length (b_items b) <= Z.to_nat kBatchSlots)%nat.
Proof.
intros X W b Hb. rewrite app_nil_r in Hb.
assert (Hb' : In b (all_batches X)).
{ unfold all_batches, YFeuC.transfer_g in *. cbn [st_qthread st_qglobal set_qglobal set_qthread qc_list qc0] in Hb.
  rewrite !in_app_iff in *. tauto. }
split; [apply in_map; exact Hb'|].
exact (proj2 (proj1 (Forall_forall _ _) (wq_batches _ (wfc_quarantine _ _ _ _ _ W)) b Hb')).
Qed.

(* After the merge and the pop, every batch of the cut state and of the temp list has one of the entry state's batch
   objects (mres_cf's permutation of the selves), and at most kBatchSlots items. *)
Lemma recyc_hb : forall X S' P, Wf_cf (as_universe B) X -> kQuarantineCacheMax < qc_bytes (st_qthread X) ->
drain_recyc X S' P ->
forall b, In b (all_batches S' ++ P) -> In (b_self b) (map b_self (all_batches X)) /\ (length (b_items b) <= Z.to_nat kBatchSlots)%nat.
Proof.
intros X S' P W HT (_ & gm & ex & g' & popped & EM & EP & -> & ->) b Hb.
pose proof (WfR_transfer_cf (as_universe B) 0 0 0 X (WfR_of_WfP_cf _ _ _ _ _ W) HT) as WT. cbv zeta in WT.
set (sT := set_qglobal _ (set_qthread qc0 X)) in WT.
assert (EMC : merge_choice_cf (st_qglobal sT) = (gm, ex)) by exact EM.
pose proof (merge_choice_mres_cf _ _ _ EMC) as MR. pose proof MR as (M1 & M2 & M3 & M4 & M5 & M6).
pose proof (RI_merge_cf (as_universe B) 0 0 0 sT gm ex WT MR) as RIM.
apply pop_batches_spec_cf in EP as (P0 & Epop & EL & EB). cbn [rev app] in Epop. subst popped.
assert (Hb' : In b (qc_list gm) \/ In b ex).
{ unfold all_batches in Hb. cbn [st_qthread st_qglobal set_qglobal set_qthread qc_list qc0] in Hb. rewrite EL.
  rewrite !in_app_iff in *. tauto. }
split.
- assert (HS : In (b_self b) (map b_self (qc_list (st_qglobal sT)))).
  { apply (Permutation_in _ (Permutation_sym M2)). rewrite in_app_iff. destruct Hb' as [H|H]; [left|right]; apply in_map; exact H. }
  unfold sT in HS. cbn [st_qglobal set_qglobal YFeuC.transfer_g qc_list] in HS. unfold all_batches. rewrite !map_app in *.
  rewrite !in_app_iff in *. tauto.
- destruct Hb' as [H|H].
  + pose proof (wq_batches _ (wfr_quarantine _ _ _ _ _ (proj1 RIM))) as BL.
    apply (proj2 (proj1 (Forall_forall _ _) BL b ltac:(unfold all_batches, sT; cbn [st_qthread st_qglobal set_qglobal set_qthread qc_list qc0];
      rewrite in_app_iff; right; exact H))).
  + rewrite (proj1 (Forall_forall _ _) M3 b H). cbn [length]. lia.
Qed.

(* The byte premise is the instance's QB_cf: its second conjunct (the quarantine is tight at the entry) is what
   says nothing is pending, which the walk's relation needs back at the transfer state. *)
Lemma di_requar_x_cf : forall L24 NMAXD, di_requar_x_t B (ARX_cf B IOK Hp) (aowned B) L24 (QB_cf NMAXD).
Proof.
intros L24 NMAXD inst ly X W mem md sp0 S' mem' md' (HI & HA & HX) (HT & (_ & HQX & _) & _) DX HS1 HS2 DQ Ev El Ee.
pose proof (IOK_inst _ HI) as ->. pose proof (amc_wf _ _ _ _ _ (proj1 HA)) as WX.
pose proof (drain_xfer_Wf_cf (as_universe B) X S' WX HT DX) as WF'.
pose proof (drain_xfer_q_sub_cf X S' DX) as HQS.
destruct DX as (_ & ->).
pose proof (ARcfR_S1 B ly X (YFeuC.transfer_g X) W mem mem' md sp0 [] Hp HA (xfer_hb X WX) (conj HS1 HS2) DQ HQS TS IQA EAP CA
  (WfR_of_WfP_cf _ _ _ _ _ WF') md' Ev El Ee) as AR'.
split; [split; [exact HI | split]|].
- (* nothing is pending after the transfer: it keeps the deficit (unq_transfer_cf) and the entry's is at most 0 *)
  assert (NP : no_pending_cf (set_qglobal (YFeuC.transfer_g X) (set_qthread qc0 X))).
  { apply (no_pending_of_tight_cf _ _ _ _ _ (WfR_of_WfP_cf _ _ _ _ _ WF')).
    pose proof (unq_transfer_cf X) as UQ. unfold YFeuC.transfer_g. unfold unq_cf in UQ. lia. }
  exact (ARcf_of_ARcfR im_segs B ly _ Hp W mem' md' AR' (wfc_compl0 _ _ _ _ _ WF') NP).
- intros e He. rewrite Ev. exact (HX e He).
- intros a Ha. exact Ha.
Qed.

Lemma di_requar_r_cf : forall NMAXD L24,
di_requar_r_t B (ARX_cf B IOK Hp) (ARXr_cf B IOK Hp) (aowned B) L24 (QB_cf NMAXD) (DRq_cf B kQuarantineMax).
Proof.
intros NMAXD L24 inst ly X W mem md sp0 tmp S' P mem' md' (HI & HA & HX) (HT & (HJ & HQ & _ & _ & HHO) & _) DR HS1 HS2 _ _ DQ _ Ev El Ee.
pose proof (IOK_inst _ HI) as ->. pose proof (amc_wf _ _ _ _ _ (proj1 HA)) as WX.
pose proof (drain_recyc_DRq_cf B X S' P WX HQ HT HJ HHO DR) as DRQ.
pose proof (recyc_hb X S' P WX HT DR) as HB.
pose proof (drain_recyc_q_sub_cf X S' P DR) as HQS.
destruct DR as (_ & gm & ex & g' & popped & _ & _ & ES & EP). subst S' P.
pose proof (ARcfR_S1 B ly X g' W mem mem' md sp0 (ex ++ popped) Hp HA HB (conj HS1 HS2) DQ HQS TS IQA EAP CA
  (proj1 (proj1 DRQ)) md' Ev El Ee) as AR'.
split; [split; [exact HI | split; [exact AR' |]] | split; [exact DRQ | intros a Ha; exact Ha]].
intros e He. rewrite Ev. exact (HX e He).
Qed.

End R.
End U.
