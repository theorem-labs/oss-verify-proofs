(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepJunkcf.v (commit f01d79f3fb5, cf refill round 3; file sha256 decb924d11f9) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code except at the by-hand acceptances named below (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair; 1 pair(s) carry a BY-HAND acceptance (accept.tsv, re-measured each run): _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm+0xb0 (lui-in-section: CONSTANT (size; enters a store base only as a scaled count into a runtime array): kUserMapSize = 0x40000)), and 1 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, the class-full report walk): the cf relation ARcf (YG0ncf.v) is kept by a
   write to one unpinned junk byte of the RegionInfo page, and moves with the exhausted byte's store.
   rule 24: proves no function (kind: invariant lemmas: the cf relation ARcf across a junk-byte write and across the
   class-full arm's store of 1 to the exhausted byte with the model's set_exh_cf).

   Field round 2 (dd8e46fd954): ARmcf pins the exhausted byte RegionInfo(c) + 68 (cf_exh_off) by its field amc_exh_cell
   (exh_cell_cf, YG0ncf.v), and region_junk_cf is cgif's region_junk, which skips offset 68: the byte is not junk.
   - In_junk_cf ly S a: [a] is in the RegionInfo page, in an entry of ajunk_cf, in no byte of a cell of acells_cf, and no
     class's exhausted byte.  ARcf_junk_write: ARcf holds again after a memory change at [a] alone that leaves [a]
     present.
   - ARcf_exh_set: PopulateFreeArray's class-full arm stores 1 to RI(c) + 68 (0x370a8) before the model's set_exh_cf
     (RepIFcf.v:9-11); the store and the model flag move together, to RepModelcf.exh_set c S.  c <> kBatchClass is
     needed: exh_cell_cf asks exh_mem_cf S kBatchClass = false and set_exh_cf adds the flag unguarded.

   Proof.  rj_ARcf_core: the relation at a state set_regions R S whose regions agree with S's on every field but the
   holes (cf holes are the zero-length sentinel only, so prim_hole_at is empty on both, rj_no_hole), over a memory
   changed at one RegionInfo byte [a] that no acells_cf cell covers, with the exhausted cells given at the new state.
   Every conjunct of ARcf other than ARmcf and ahs reads no memory.  Each read of ARmcf is at an owned address
   (YG0qcf.v's *_owned_cf lemmas, so 0 <= x < 2 ^ 64 by AR_owned_low_law_ok_cf) that is not [a]: the cells of acells_cf by
   premise; every other read is off the RegionInfo page (nri below): the free arrays and the primary chunks lie in the
   31 regions below the page, the batches in class 24's region, the secondary maps, the static extents and the image
   (with the errbuf object) are disjoint from the primary reservation, and the shadow bytes are below kHighMemBeg.  The
   range_vis conjuncts need only visibility, which the write keeps.  ahs reads the shadow band only, which is below the
   page.  The cells' footprint is YG0tcf.v:96-304 (cell_bytes_in) at P := nri, with the primary zone narrowed to the
   regions below the page. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09 YO0d YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0s YG0q YG0t.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG05cf YG0scf YG0qcf YG0tcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RepIFcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG06cf YGcfImgRows.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RepModelcf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The junk byte.                                                                                                *)
Definition In_junk_cf (ly : alayout) (S : astate) (a : Z) : Prop :=
  ly_space ly + kRegionInfoOff <= a < ly_space ly + kRegionInfoOff + 4096 /\
  Exists (fun r => aeval B ly (fst r) <= a < aeval B ly (fst r) + snd r) (ajunk_cf B ly S) /\
  Forall (fun cl => forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w cl)) -> aeval B ly (c_at cl) + k <> a) (acells_cf B ly S) /\
  (forall c, 1 <= c <= 31 -> a <> region_lock_addr ly c + 68).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. Addresses off the RegionInfo page.                                                                           *)
Definition nri (ly : alayout) (x : Z) : Prop :=
  x < ly_space ly + kRegionInfoOff \/ ly_space ly + kRegionInfoOff + 4096 <= x.

Lemma rj_kRI : kRegionInfoOff = 137438953472.
Proof. reflexivity. Qed.
Lemma rj_kSS : kSpaceSize = 137438953472.
Proof. reflexivity. Qed.
Lemma rj_region_base : forall ly c, 0 <= c -> region_base ly c = ly_space ly + c * 4294967296.
Proof. intros ly c Hc. unfold region_base. rewrite region_off_eq by lia. reflexivity. Qed.
Lemma rj_fa_below : forall ly c, 1 <= c <= 31 -> fa_base ly c + kFreeArrayMax <= ly_space ly + kRegionInfoOff.
Proof.
intros ly c Hc. unfold fa_base. rewrite region_off_eq by lia. rewrite rj_kRI. unfold kFreeArrayOffset, kFreeArrayMax.
change (2 ^ 32) with 4294967296. lia.
Qed.

Lemma nri_ne : forall ly a x, ly_space ly + kRegionInfoOff <= a < ly_space ly + kRegionInfoOff + 4096 -> nri ly x -> x <> a.
Proof. intros ly a x Ha Hx. unfold nri in Hx. lia. Qed.
Lemma nri_reg : forall ly x, x < ly_space ly + kRegionInfoOff -> nri ly x.
Proof. intros ly x Hx. left. exact Hx. Qed.
Lemma nri_out_prim : forall ly x, layout_ok ly -> x < ly_prim ly \/ ly_prim ly + kPrimResvSize <= x -> nri ly x.
Proof.
intros ly x LO Hx. pose proof (lo_space_in _ LO) as [S1 S2]. unfold nri. rewrite rj_kRI. rewrite rj_kSS in S2. lia.
Qed.
Lemma nri_low : forall ly x, layout_ok ly -> x < kHighMemBeg -> nri ly x.
Proof. intros ly x LO Hx. apply nri_out_prim; [exact LO|]. left. pose proof (lo_high _ LO) as [H1 _]. lia. Qed.
Lemma nri_static : forall ly e x, layout_ok ly -> In e (tl (static_extents ly)) -> fst e <= x < fst e + snd e -> nri ly x.
Proof.
intros ly e x LO He Hx. apply nri_out_prim; [exact LO|].
pose proof (lo_disj _ LO) as D. unfold static_extents, owned_extents in D, He. cbn [app pairwise tl] in D, He.
destruct D as [F _]. pose proof (proj1 (Forall_forall _ _) F e He) as Z. unfold zdisjoint in Z. cbn [fst snd] in Z. lia.
Qed.
Lemma nri_core : forall ly e x, layout_ok ly -> In e (core_extents ly) -> fst e <= x < fst e + snd e -> nri ly x.
Proof.
intros ly e x LO He Hx. apply (nri_static ly e x LO); [|exact Hx].
unfold core_extents in He. unfold static_extents, owned_extents. cbn [tl app]. cbn in He |- *. intuition.
Qed.
Lemma nri_F : forall ly x, layout_ok ly -> ly_F ly <= x < ly_F ly + kFakeStackSize -> nri ly x.
Proof.
intros ly x LO Hx. apply (nri_static ly (ly_F ly, kFakeStackSize) x LO); [|exact Hx].
unfold static_extents, owned_extents. cbn [tl app]. right. right. left. reflexivity.
Qed.
Lemma nri_img : forall ly x, layout_ok ly -> in_zr x (ly_img ly) -> nri ly x.
Proof.
intros ly x LO Hx. apply (nri_static ly (ly_img ly) x LO); [|exact Hx].
unfold static_extents, owned_extents. cbn [tl app]. do 8 right. left. reflexivity.
Qed.
Lemma nri_static_owned : forall ly S Hp rd x, ARmcf B ly S Hp rd -> Exists (in_zr x) (as_owned_static B) -> nri ly x.
Proof.
intros ly S Hp rd x M H. apply Exists_exists in H as (r & Hr & [H1 H2]).
pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hr)) as [S1 S2].
apply (nri_img ly x (amc_layout _ _ _ _ _ M)). unfold in_zr. lia.
Qed.
Lemma nri_area : forall ly S Hp rd r x, ARmcf B ly S Hp rd -> In r (asyms_areas B) -> fst r <= x < fst r + snd r -> nri ly x.
Proof.
intros ly S Hp rd r x M Hr Hx. pose proof (proj1 (Forall_forall _ _) (aso_cover _ (amc_syms _ _ _ _ _ M)) r Hr) as X.
apply Exists_exists in X as (r' & Hr' & [X1 X2]). eapply nri_static_owned; [exact M|].
apply Exists_exists. exists r'. split; [exact Hr'|]. unfold in_zr. lia.
Qed.
Lemma nri_sec : forall ly S Hp rd e x, ARmcf B ly S Hp rd -> In e (sec_extents ly S) -> fst e <= x < fst e + snd e -> nri ly x.
Proof.
intros ly S Hp rd e x M He Hx. apply nri_out_prim; [exact (amc_layout _ _ _ _ _ M)|].
pose proof (pairwise_In zdisjoint _ e (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl
  (proj2 (amc_placed _ _ _ _ _ M)) He ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.
Lemma nri_shadow_static : forall ly S Hp rd r x, ARmcf B ly S Hp rd -> In r (as_owned_static B) ->
  shadow_addr (fst r) <= x < shadow_addr (fst r) + (snd r + 7) / 8 -> nri ly x.
Proof.
intros ly S Hp rd r x M Hr Hx. apply (nri_low ly x (amc_layout _ _ _ _ _ M)).
assert (E : Exists (fun r0 => in_zr x (shadow_addr (fst r0), (snd r0 + 7) / 8))
  (static_extents ly ++ sec_extents ly S ++ zero_shadow_ranges B ly ++ as_owned_static B ++ [hm_zone; lm_zone])).
{ apply Exists_exists. exists r. split; [rewrite !in_app_iff; tauto | exact Hx]. }
exact (proj2 (owned_shadow_bound_cf B ly S Hp rd x M E)).
Qed.

(* A primary chunk's metadata is in its class's region, below the page; a secondary's is in its map. *)
Lemma meta_nri : forall ly S Hp rd k a, ARmcf B ly S Hp rd -> In k (st_chunks S) ->
  ck_base B ly k - (match ck_beg k with PSec _ _ => kPage | _ => 0 end) <= a < ck_base B ly k + ck_rz k -> nri ly a.
Proof.
intros ly S Hp rd k a M Hk Ha. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal). unfold kFreeArrayOffset in Gal.
  rewrite (rj_region_base ly (prim_class o)) in Gbase by lia.
  apply nri_reg. rewrite rj_kRI. lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
  apply (nri_sec ly S Hp rd (ly_sec ly r, sec_map_size (ck_req k)) a M Gin). cbn [fst snd]. unfold kPage in *. lia.
Qed.
(* A batch is a block of class 24 (kBatchClass), below the page. *)
Lemma batch_nri : forall ly S Hp rd b a, ARmcf B ly S Hp rd -> In b (all_batches S) ->
  ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> nri ly a.
Proof.
intros ly S Hp rd b a M Hb Ha. pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (wfc_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; auto).
pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wrc_alloc _ _ _ _ _ _ CL) as AL. pose proof (mapped_bound_cf (as_universe B) 0 0 0 S kBatchClass WF ltac:(unfold kBatchClass; lia)) as MB.
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2.
assert (BX : ly_space ly + b_self b = region_base ly kBatchClass + x) by (unfold region_base; subst x; lia).
rewrite (rj_region_base ly kBatchClass) in BX by (unfold kBatchClass; lia).
apply nri_reg. rewrite rj_kRI. clearbody x. unfold kBatchBytes, kFreeArrayOffset, kBatchClass in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The cells off the page: YG0tcf.v:179-304 at P := nri.                                                         *)
Ltac rj_fc := apply Forall_cons; [cbn; lia|].
Lemma cache_cells_nri : forall ly S Hp rd c, ARmcf B ly S Hp rd -> 1 <= c <= 31 -> Forall (cell_bytes_in B (nri ly) ly) (cache_cells S c).
Proof.
intros ly S Hp rd c M Hc.
assert (OR : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> nri ly a).
{ intros a Ha. apply (nri_core ly (ly_T ly, kThreadObjSize) a (amc_layout _ _ _ _ _ M)); [unfold core_extents; cbn; tauto | exact Ha]. }
apply (Forall_cbi_of_range B (nri ly) ly _ (ly_T ly) kThreadObjSize OR).
pose proof (wfc_classes _ _ _ _ _ (amc_wf _ _ _ _ _ M) c Hc) as CL. pose proof (wrc_cache _ _ _ _ _ _ CL) as WC. pose proof (class_ok c Hc) as (_ & _ & _ & K4 & _).
unfold cache_cells, t_cache, kThreadObjSize. destruct (st_cache_inited S).
- destruct WC as [PM PL]. repeat rj_fc. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i v] & <- & Hiv). cbn [fst snd c_at c_w z4 c4 aeval aoff].
  apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. lia.
- repeat rj_fc. apply Forall_nil.
Qed.
Lemma chunk_cells_nri : forall ly S Hp rd k, ARmcf B ly S Hp rd -> In k (st_chunks S) -> Forall (cell_bytes_in B (nri ly) ly) (chunk_cells k).
Proof.
intros ly S Hp rd k M Hk. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
assert (OR : forall a, ck_base B ly k <= a < ck_base B ly k + ck_rz k -> nri ly a).
{ intros a Ha. eapply meta_nri; [exact M | exact Hk |]. destruct (ck_beg k); unfold kPage; lia. }
apply (Forall_cbi_of_range B (nri ly) ly _ _ _ OR).
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
Lemma sec_cells_nri : forall ly S Hp rd, ARmcf B ly S Hp rd -> Forall (cell_bytes_in B (nri ly) ly) (sec_cells S).
Proof.
intros ly S Hp rd M. pose proof (wfc_secondary _ _ _ _ _ (amc_wf _ _ _ _ _ M)) as X. destruct X as [Snd Sac Sal Sres Sral].
assert (ORI : forall a, as_inst B <= a < as_inst B + 3632 -> nri ly a) by (intros a Ha; exact (nri_area ly S Hp rd (as_inst B, 3632) a M ltac:(cbn; tauto) Ha)).
unfold sec_cells.
apply Forall_cons; [eapply (cbi_of_range B); [exact ORI | cbn; unfold o_sec_reserved; lia | cbn; unfold o_sec_reserved; lia]|].
apply Forall_cons; [eapply (cbi_of_range B); [exact ORI | cbn; unfold o_sec_n; lia | cbn; unfold o_sec_n; lia]|].
apply Forall_cons; [eapply (cbi_of_range B); [exact ORI | cbn; unfold o_sec_mutex; lia | cbn; unfold o_sec_mutex; lia]|].
apply Forall_app. split.
- apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
  eapply (cbi_of_range B); [intros a Ha; apply (nri_core ly (ly_Q ly, kPtrArrayResv) a (amc_layout _ _ _ _ _ M)); [unfold core_extents; cbn; tauto | exact Ha] | cbn; lia |].
  cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
- apply Forall_forall. intros c Hc. apply in_flat_map in Hc as (k & Hk & Hc).
  pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
  destruct (ck_beg k) as [|o|r o|c' p] eqn:Eb; try solve [destruct Hc].
  destruct GG as (-> & _ & Gbase & Gext & Gin & _).
  assert (OR : forall a, ly_sec ly r <= a < ly_sec ly r + kPage -> nri ly a).
  { intros a Ha. eapply meta_nri; [exact M | exact Hk |]. rewrite Eb. unfold kPage in *. lia. }
  unfold kPage in OR.
  destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; (eapply (cbi_of_range B); [exact OR | cbn; lia | cbn; lia]).
Qed.
Lemma batch_cells_nri : forall ly S Hp rd l, ARmcf B ly S Hp rd -> incl l (all_batches S) -> Forall (cell_bytes_in B (nri ly) ly) (batch_cells l).
Proof.
intros ly S Hp rd l M. induction l as [|b t IH]; intros Hincl; [apply Forall_nil|]. cbn [batch_cells].
pose proof (wq_batches _ (wfc_quarantine _ _ _ _ _ (amc_wf _ _ _ _ _ M))) as BL.
pose proof (proj1 (Forall_forall _ _) BL b (Hincl b (or_introl eq_refl))) as [L1 L2]. unfold kBatchSlots in L2.
assert (OR : forall a, ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> nri ly a)
by (intros a Ha; eapply batch_nri; [exact M | apply Hincl; left; reflexivity | exact Ha]).
unfold kBatchBytes in OR.
apply Forall_cons; [eapply (cbi_of_range B); [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply (cbi_of_range B); [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply (cbi_of_range B); [exact OR | cbn; lia | cbn; lia]|].
apply Forall_app. split.
- apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i k] & <- & Hik). apply in_combine_l in Hik. apply in_seq in Hik.
  eapply (cbi_of_range B); [exact OR | cbn; lia | cbn; lia].
- apply IH. intros x Hx. apply Hincl. right. exact Hx.
Qed.
Lemma quar_cells_nri : forall ly S Hp rd, ARmcf B ly S Hp rd -> Forall (cell_bytes_in B (nri ly) ly) (quar_cells S).
Proof.
intros ly S Hp rd M.
assert (ORT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> nri ly a).
{ intros a Ha. apply (nri_core ly (ly_T ly, kThreadObjSize) a (amc_layout _ _ _ _ _ M)); [unfold core_extents; cbn; tauto | exact Ha]. }
assert (ORI : forall a, as_inst B <= a < as_inst B + 3632 -> nri ly a) by (intros a Ha; exact (nri_area ly S Hp rd (as_inst B, 3632) a M ltac:(cbn; tauto) Ha)).
unfold kThreadObjSize in ORT.
unfold quar_cells, qc_cells, o_q_cmutex, o_q_rmutex, o_q_size, t_qc.
apply Forall_cons; [eapply (cbi_of_range B); [exact ORI | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply (cbi_of_range B); [exact ORI | cbn; lia | cbn; lia]|].
apply Forall_app. split.
- do 4 (apply Forall_cons; [eapply (cbi_of_range B); [exact ORT | cbn; lia | cbn; lia]|]).
  eapply batch_cells_nri; [exact M | intros b Hb; unfold all_batches; apply in_app_iff; left; exact Hb].
- do 4 (apply Forall_cons; [eapply (cbi_of_range B); [exact ORI | cbn; lia | cbn; lia]|]).
  eapply batch_cells_nri; [exact M | intros b Hb; unfold all_batches; apply in_app_iff; right; exact Hb].
Qed.
Lemma fs_hdr_nri : forall ly, layout_ok ly -> Forall (cell_bytes_in B (nri ly) ly) fs_hdr.
Proof.
intros ly LO. assert (OR : forall a, ly_F ly + 88 <= a < ly_F ly + 88 + (kFakeFlagsOff - 88) -> nri ly a)
by (intros a Ha; apply (nri_F ly a LO); unfold kFakeFlagsOff, kFakeStackSize in *; lia).
unfold kFakeFlagsOff in OR. unfold fs_hdr.
apply Forall_cons; [eapply (cbi_of_range B); [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply (cbi_of_range B); [exact OR | cbn; lia | cbn; lia]|]. apply Forall_nil.
Qed.
Lemma depot_cells_nri : forall ly S Hp rd, ARmcf B ly S Hp rd -> Forall (cell_bytes_in B (nri ly) ly) (depot_cells ly S).
Proof.
intros ly S Hp rd M.
assert (ORD : forall a, as_depot B <= a < as_depot B + (4 * 2 ^ 20 + 32) -> nri ly a) by (intros a Ha; exact (nri_area ly S Hp rd (as_depot B, 4 * 2 ^ 20 + 32) a M ltac:(cbn; tauto) Ha)).
assert (ORS : forall a, as_store B <= a < as_store B + 32 -> nri ly a) by (intros a Ha; exact (nri_area ly S Hp rd (as_store B, 32) a M ltac:(cbn; tauto) Ha)).
unfold depot_cells, d_nuniq, d_map1, s_total, s_block0.
apply Forall_cons; [eapply (cbi_of_range B); [exact ORD | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply (cbi_of_range B); [exact ORD | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply (cbi_of_range B); [exact ORS | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply (cbi_of_range B); [exact ORS | cbn; lia | cbn; lia]|]. apply Forall_nil.
Qed.
Lemma ialloc_cells_nri : forall ly S Hp rd, ARmcf B ly S Hp rd -> Forall (cell_bytes_in B (nri ly) ly) (ialloc_cells B S).
Proof.
intros ly S Hp rd M. pose proof (aso_ialloc _ (amc_syms _ _ _ _ _ M)) as [I1 I2].
assert (ORA : forall a, as_ialloc_lo B <= a < as_ialloc_lo B + (as_ialloc_hi B - as_ialloc_lo B) -> nri ly a)
by (intros a Ha; exact (nri_area ly S Hp rd (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B) a M ltac:(cbn; tauto) Ha)).
assert (ORF : forall a, as_ialloc_flag B <= a < as_ialloc_flag B + 2 -> nri ly a)
by (intros a Ha; exact (nri_area ly S Hp rd (as_ialloc_flag B, 2) a M ltac:(cbn; tauto) Ha)).
unfold ialloc_cells.
apply Forall_cons; [eapply (cbi_of_range B); [exact ORF | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply (cbi_of_range B); [exact ORF | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply (cbi_of_range B); [exact ORA | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply (cbi_of_range B); [exact ORA | cbn; lia | cbn; lia]|]. apply Forall_nil.
Qed.
Lemma thread_cells_nri : forall ly, layout_ok ly -> Forall (cell_bytes_in B (nri ly) ly) thread_cells.
Proof.
intros ly LO. unfold thread_cells, t_unwinding. apply Forall_cons; [|apply Forall_nil].
eapply (cbi_of_range B); [intros a Ha; apply (nri_core ly (ly_T ly, kThreadObjSize) a LO); [unfold core_extents; cbn; tauto | exact Ha] | cbn; lia | cbn; unfold kThreadObjSize; lia].
Qed.
Lemma const_cells_nri : forall ly S Hp rd, ARmcf B ly S Hp rd -> Forall (cell_bytes_in B (nri ly) ly) (as_const B ly).
Proof.
intros ly S Hp rd M. eapply Forall_impl; [|exact (amc_const_owned _ _ _ _ _ M)]. intros c Hc k Hk.
destruct (Hc k Hk) as [O|[O|O]].
- eapply nri_static_owned; [exact M | exact O].
- apply Exists_exists in O as (e & He & Hin). exact (nri_core ly e _ (amc_layout _ _ _ _ _ M) He Hin).
- apply Exists_exists in O as (r & Hr & Hin). exact (nri_shadow_static ly S Hp rd r _ M Hr Hin).
Qed.
(* acells_cf without its region cells (YG0ncf.v:55-57). *)
Lemma rest_cells_nri : forall ly S Hp rd, ARmcf B ly S Hp rd ->
  Forall (cell_bytes_in B (nri ly) ly) (flat_map (cache_cells S) (zseq 1 31) ++ flat_map chunk_cells (st_chunks S)
    ++ sec_cells S ++ quar_cells S ++ fs_cells S ++ depot_cells ly S ++ ialloc_cells B S ++ thread_cells).
Proof.
intros ly S Hp rd M. pose proof (amc_layout _ _ _ _ _ M) as LO. rewrite (fs_cells_split S).
assert (HF : forall a, ly_F ly <= a < ly_F ly + 88 -> nri ly a) by (intros a Ha; apply (nri_F ly a LO); unfold kFakeStackSize; lia).
apply Forall_app; split; [exact (Forall_flat_map'' _ _ _ (fun c Hc => cache_cells_nri ly S Hp rd c M ltac:(pose proof (zseq_In' 1 31 c Hc); lia)))|].
apply Forall_app; split; [exact (Forall_flat_map'' _ _ _ (fun k Hk => chunk_cells_nri ly S Hp rd k M Hk))|].
apply Forall_app; split; [exact (sec_cells_nri ly S Hp rd M)|].
apply Forall_app; split; [exact (quar_cells_nri ly S Hp rd M)|].
apply Forall_app; split.
{ apply Forall_app; split; [exact (fs_hdr_nri ly LO)|]. unfold fs_hints. apply Forall_forall. intros c Hc.
  apply in_map_iff in Hc as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih.
  eapply (cbi_of_range B); [exact (fun a Ha => HF a Ha) | cbn; lia | cbn [c_at c_w z8 c8 aeval aoff fst snd]; cbn; lia]. }
apply Forall_app; split; [exact (depot_cells_nri ly S Hp rd M)|].
apply Forall_app; split; [exact (ialloc_cells_nri ly S Hp rd M)|].
exact (thread_cells_nri ly LO).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The general lemma.                                                                                            *)
(* Regions that agree on every field but the holes.                                                                 *)
Definition rj_rsame (r r' : region) : Prop :=
  rg_mapped_user r' = rg_mapped_user r /\ rg_alloc_user r' = rg_alloc_user r /\
  rg_mapped_fa r' = rg_mapped_fa r /\ rg_free r' = rg_free r.
Lemma rj_rsame_refl : forall r, rj_rsame r r.
Proof. intros r. repeat split. Qed.
Lemma rj_F2_refl : forall l, Forall2 rj_rsame l l.
Proof. induction l as [|h t IH]; constructor; [apply rj_rsame_refl | exact IH]. Qed.
Lemma rj_rsame_nth : forall l l' n, Forall2 rj_rsame l l' -> rj_rsame (nth n l region0) (nth n l' region0).
Proof.
intros l l' n F. revert n. induction F as [|r r' t t' Hr F IH]; intros [|n]; cbn [nth];
[apply rj_rsame_refl | apply rj_rsame_refl | exact Hr | exact (IH n)].
Qed.
Lemma rj_reg_same : forall S R c, Forall2 rj_rsame (st_regions S) R -> rj_rsame (reg S c) (reg (set_regions R S) c).
Proof. intros S R c F. unfold reg, znth. cbn [set_regions st_regions]. exact (rj_rsame_nth _ _ _ F). Qed.
Lemma rj_F2_lupd : forall l i v, (i < length l)%nat -> rj_rsame (nth i l region0) v -> Forall2 rj_rsame l (lupd l i v).
Proof.
induction l as [|h t IH]; intros [|i] v Hi Hr; cbn [lupd nth length] in *; try lia.
- constructor; [exact Hr | apply rj_F2_refl].
- constructor; [apply rj_rsame_refl | apply IH; [lia | exact Hr]].
Qed.
Lemma rj_fold_mapped : forall l l', Forall2 rj_rsame l l' ->
  fold_right (fun r acc => rg_mapped_user r + rg_mapped_fa r + acc) 0 l' =
  fold_right (fun r acc => rg_mapped_user r + rg_mapped_fa r + acc) 0 l.
Proof. intros l l' F. induction F as [|r r' t t' (E1 & _ & E3 & _) F IH]; cbn [fold_right]; [reflexivity|]. rewrite E1, E3, IH. reflexivity. Qed.
Lemma rj_prim_committed : forall S R, Forall2 rj_rsame (st_regions S) R -> prim_committed (set_regions R S) = prim_committed S.
Proof. intros S R F. unfold prim_committed. cbn [set_regions st_regions]. exact (rj_fold_mapped _ _ F). Qed.
Lemma rj_no_hole : forall U pp cc bb S ly a, WfP_cf U pp cc bb S -> ~ prim_hole_at ly S a.
Proof.
intros U pp cc bb S ly a W (c & h & Hc & Hh & Hin). pose proof (wfc_classes _ _ _ _ _ W c Hc) as C. unfold wf_class_cf in C.
destruct (wrc_holes _ _ _ _ _ _ C) as [HH _]. rewrite (proj1 (Forall_forall _ _) HH h Hh) in Hin. unfold in_zr in Hin. cbn [fst snd] in Hin. lia.
Qed.
Lemma rj_cut_ok : forall ly S S', (forall c, rg_mapped_user (reg S' c) = rg_mapped_user (reg S c) /\ rg_mapped_fa (reg S' c) = rg_mapped_fa (reg S c)) ->
  forall x, cut_ok ly S x -> cut_ok ly S' x.
Proof.
intros ly S S' E x [H|[H|(c & Hc & H)]]; [left; exact H | right; left; exact H |]. right; right. exists c. split; [exact Hc|].
destruct (E c) as [E1 E2]. rewrite E1, E2. exact H.
Qed.
Lemma rj_pieces : forall ly S S' pieces,
  (forall c, rg_mapped_user (reg S' c) = rg_mapped_user (reg S c) /\ rg_mapped_fa (reg S' c) = rg_mapped_fa (reg S c)) ->
  (forall a, ~ prim_hole_at ly S a) -> (forall a, ~ prim_hole_at ly S' a) -> prim_pieces_ok ly S pieces -> prim_pieces_ok ly S' pieces.
Proof.
intros ly S S' pieces E N N' (P1 & P2 & P3). split; [|split; [exact P2|]].
- eapply Forall_impl; [|exact P1]. intros p (Q1 & Q2 & Q3). split; [exact Q1|]. split; eapply rj_cut_ok; eassumption.
- intros a Ha. rewrite (P3 a Ha). split; intros _; [exact (N' a) | exact (N a)].
Qed.

Lemma rj_reg_mf : forall S R, Forall2 rj_rsame (st_regions S) R -> forall c,
  rg_mapped_user (reg (set_regions R S) c) = rg_mapped_user (reg S c) /\ rg_mapped_fa (reg (set_regions R S) c) = rg_mapped_fa (reg S c).
Proof. intros S R F c. destruct (rj_reg_same S R c F) as (E1 & _ & E3 & _). split; assumption. Qed.
Lemma rj_ledger : forall ly S R md, Forall2 rj_rsame (st_regions S) R ->
  Wf_cf (as_universe B) S -> Wf_cf (as_universe B) (set_regions R S) ->
  ALedger_cf tfibsegs ly S md -> ALedger_cf tfibsegs ly (set_regions R S) md.
Proof.
intros ly S R md F W0 W1 L.
destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15 L16 L17].
constructor; try assumption.
- destruct L4 as (pieces & PP & PI). exists pieces. split; [|exact PI].
  apply (rj_pieces ly S _ pieces (rj_reg_mf S R F)); [intros x; exact (rj_no_hole _ _ _ _ _ ly x W0) | intros x; exact (rj_no_hole _ _ _ _ _ ly x W1) | exact PP].
- unfold eager_cf in *. rewrite (rj_prim_committed S R F). exact L9.
Qed.
Lemma rj_budget : forall ly S R W, Forall2 rj_rsame (st_regions S) R ->
  abudget_ok_cf tfibsegs ly S W -> abudget_ok_cf tfibsegs ly (set_regions R S) W.
Proof.
intros ly S R W F (A1 & A2 & A3). split; [|split; [exact A2 | exact A3]].
unfold abudget_cf in *. rewrite (rj_prim_committed S R F), (cf_hull_frame S (set_regions R S) eq_refl eq_refl). exact A1.
Qed.
Lemma rj_acells : forall ly S R, Forall2 rj_rsame (st_regions S) R -> acells_cf B ly (set_regions R S) = acells_cf B ly S.
Proof.
intros ly S R F. unfold acells_cf.
assert (RC : forall c, region_cells_cf (set_regions R S) c = region_cells_cf S c).
{ intros c. unfold region_cells_cf, region_cells. cbv zeta. destruct (rj_reg_same S R c F) as (E1 & E2 & E3 & E4).
  rewrite E1, E2, E3, E4. reflexivity. }
rewrite (flat_map_ext (region_cells_cf (set_regions R S)) (region_cells_cf S) RC). reflexivity.
Qed.

Lemma rj_fa_poison : forall ly S R, Forall2 rj_rsame (st_regions S) R -> fa_poison_ranges ly (set_regions R S) = fa_poison_ranges ly S.
Proof.
intros ly S R F. unfold fa_poison_ranges. f_equal. apply flat_map_ext. intros c.
destruct (rj_reg_mf S R F c) as [E1 E2]. rewrite E1, E2. reflexivity.
Qed.
Lemma rj_ashadow : forall ly S R, Forall2 rj_rsame (st_regions S) R -> forall g, ashadow B ly (set_regions R S) g = ashadow B ly S g.
Proof. intros ly S R F g. unfold ashadow. rewrite (rj_fa_poison ly S R F). reflexivity. Qed.

Lemma rj_aareas : forall S R, Forall2 rj_rsame (st_regions S) R -> aareas (set_regions R S) = aareas S.
Proof.
intros S R F. unfold aareas. f_equal. apply flat_map_ext. intros c.
destruct (rj_reg_mf S R F c) as [E1 E2]. rewrite E1, E2. reflexivity.
Qed.

(* The relation at the new state, over a reader changed at [a] alone. *)
Lemma rj_ARmcf_core : forall ly S R Hp rd rd' a,
  ARmcf B ly S Hp rd ->
  ly_space ly + kRegionInfoOff <= a < ly_space ly + kRegionInfoOff + 4096 ->
  Forall (cell_bytes_in B (fun x => x <> a) ly) (acells_cf B ly S) ->
  (forall x, aowned B ly S x -> x <> a -> rd' x = rd x) ->
  (forall x, rd x <> None -> rd' x <> None) ->
  Forall2 rj_rsame (st_regions S) R -> Wf_cf (as_universe B) (set_regions R S) ->
  exh_cell_cf B ly (set_regions R S) rd' ->
  ARmcf B ly (set_regions R S) Hp rd'.
Proof.
intros ly S R Hp rd rd' a M JR JC AG VIS F W1 EX.
pose proof (amc_layout _ _ _ _ _ M) as LO.
destruct (amc_cells_owned _ _ _ _ _ M) as [HX HO].
assert (CNE : Forall (cell_bytes_in B (fun x => x <> a) ly) (as_const B ly)).
{ eapply Forall_impl; [|exact (const_cells_nri ly S Hp rd M)]. intros cl Hc k Hk. exact (nri_ne ly a _ JR (Hc k Hk)). }
pose proof M as M0.
destruct M as [Xwf Xuni Xsyms Xlay Xplaced Xconst Xcowned Xcells Xfa Xflags Xdepot Xshadow Xzsh Xjunk Xareas Xclient Xzero Xtsd Ximg Xhp Xxs Xexh Xerr Xown Xpf Xpfo].
constructor; try assumption.
- exact (Forall_cell_holds_agree_in B (fun x => x <> a) ly S rd rd' _ AG (const_cells_owned_cf B ly S Hp rd M0) CNE Xconst).
- rewrite (rj_acells ly S R F). exact (Forall_cell_holds_agree_in B (fun x => x <> a) ly S rd rd' _ AG (acells_owned_cf B ly S Hp rd M0) JC Xcells).
- intros c i v Hc Hi Hv k Hk. destruct (rj_reg_same S R c F) as (_ & _ & _ & EF). rewrite EF in Hi, Hv.
  pose proof (wfc_classes _ _ _ _ _ Xwf c Hc) as CL. pose proof (wrc_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as FB.
  pose proof (rj_fa_below ly c Hc) as FR.
  rewrite AG; [exact (Xfa c i v Hc Hi Hv k Hk) | eapply own_fa_cf; [exact M0 | exact Hc | lia] |].
  apply (nri_ne ly a _ JR). apply nri_reg. unfold kFreeArrayMax in *. lia.
- change (fs_flags_ok ly rd' S). intros cid pos Hc Hpos. pose proof (flag_off_bounds cid pos Hc Hpos) as FB.
  rewrite AG; [exact (Xflags cid pos Hc Hpos) | unfold flag_addr, kFakeFlagsOff in *; eapply own_F_low_cf; [exact M0 | lia] |].
  apply (nri_ne ly a _ JR). apply (nri_F ly _ LO). unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. lia.
- change (depot_ok B ly rd' S).
  destruct Xdepot as (heads & links & D1 & D2 & D3). exists heads, links. split; [|split; [|exact D3]].
  + intros b Hb. destruct (D1 b Hb) as [K1 K2]. split; [exact K1|]. intros k Hk.
    rewrite AG; [exact (K2 k Hk) | eapply (own_area_cf B ly S Hp rd (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | cbn; tauto | cbn; unfold d_tab_words in Hb; lia] |].
    apply (nri_ne ly a _ JR). apply (nri_area ly S Hp rd (as_depot B, 4 * 2 ^ 20 + 32) _ M0); [cbn; tauto | cbn; unfold d_tab_words in Hb; lia].
  + intros id Hid. destruct (D2 id Hid) as (K1 & K2 & K3). split; [exact K1|].
    assert (NB : depot_ids S <= 4097).
    { pose proof (depot_len_bound _ _ Xuni (wfc_depot _ _ _ _ _ Xwf)) as DL. unfold depot_ids, DEPOT_MAX in *. lia. }
    assert (OR : forall k, 0 <= k < 16 -> aowned B ly S (ly_NB ly + 16 * id + k) /\ ly_NB ly + 16 * id + k <> a).
    { intros k Hk. split.
      - eapply (own_core_cf B ly S Hp rd (ly_NB ly, kNodesBlockSize)); [exact M0 | unfold core_extents; cbn; tauto | cbn; unfold kNodesBlockSize; lia].
      - apply (nri_ne ly a _ JR). apply (nri_core ly (ly_NB ly, kNodesBlockSize) _ LO); [unfold core_extents; cbn; tauto | cbn; unfold kNodesBlockSize; lia]. }
    split; intros k Hk.
    * destruct (OR (Z.of_nat k) ltac:(lia)) as [O1 O2]. rewrite AG; [exact (K2 k Hk) | exact O1 | exact O2].
    * destruct (OR (8 + Z.of_nat k) ltac:(lia)) as [O1 O2].
      replace (ly_NB ly + 16 * id + 8 + Z.of_nat k) with (ly_NB ly + 16 * id + (8 + Z.of_nat k)) by lia.
      rewrite AG; [|exact O1 | exact O2].
      replace (ly_NB ly + 16 * id + (8 + Z.of_nat k)) with (ly_NB ly + 16 * id + 8 + Z.of_nat k) by lia. exact (K3 k Hk).
- intros g v Hg Hv0. rewrite (rj_ashadow ly S R F) in Hv0. rewrite AG; [exact (Xshadow g v Hg Hv0) | eapply ashadow_owned_cf; [exact M0 | exact Hv0] |].
  apply (nri_ne ly a _ JR). apply (nri_low ly _ LO). exact (proj2 (ashadow_low_cf B ly S Hp rd g v M0 Hv0)).
- unfold zshadow_ok in *. apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. fold (shadow_addr (fst r)).
  change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
  rewrite AG; [exact (proj1 (Forall_forall _ _) Xzsh r Hr i Hi) | eapply own_shadow_zero_cf; [exact M0 | exact Hr | exact Hi] |].
  apply (nri_ne ly a _ JR). apply (nri_low ly _ LO). exact (proj2 (zshadow_low_cf B ly S Hp rd r i M0 Hr Hi)).
- eapply Forall_range_vis_keep; [exact VIS | exact Xjunk].
- rewrite (rj_aareas S R F). eapply Forall_range_vis_keep; [exact VIS | exact Xareas].
- eapply Forall_range_vis_keep; [exact VIS | exact Xclient].
- apply Forall_forall. intros r Hr i Hi. pose proof (aso_ialloc _ Xsyms) as [I1 I2].
  assert (RR : as_ialloc_lo B <= aeval B ly (fst r) + i < as_ialloc_lo B + (as_ialloc_hi B - as_ialloc_lo B)).
  { unfold ialloc_zero in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; lia. }
  rewrite AG; [exact (proj1 (Forall_forall _ _) Xzero r Hr i Hi)
    | eapply (own_area_cf B ly S Hp rd (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact M0 | cbn; tauto | exact RR] |].
  apply (nri_ne ly a _ JR). exact (nri_area ly S Hp rd (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B) _ M0 ltac:(cbn; tauto) RR).
- exact (errb_cells_move_cf B ly S (set_regions R S) Hp rd rd' (fun x => x <> a) M0 (proj1 HO) eq_refl eq_refl eq_refl eq_refl AG VIS
    (fun x Hx => nri_ne ly a x JR (nri_static_owned ly S Hp rd x M0 (proj1 HO x Hx))) Xerr).
- (* field round 3: Printf's two cells, owned static bytes (amc_pf_owned), apart from the RegionInfo byte a *)
  destruct Xpf as [P1 P2].
  assert (G : forall x, (cf_toolname_cell <= x < cf_toolname_cell + 8 \/ cf_pfcb_cell <= x < cf_pfcb_cell + 8) -> rd' x = rd x).
  { intros x Hx. destruct (proj1 Xpfo x Hx) as [Ho _].
    apply AG; [exact (own_static_cf B ly S Hp rd x M0 Ho) | exact (nri_ne ly a x JR (nri_static_owned ly S Hp rd x M0 Ho))]. }
  split; [apply (YG0q.cell_holds_agree B ly rd rd' _ P1) | apply (YG0q.cell_holds_agree B ly rd rd' _ P2)];
    intros k Hk; cbn [c_w c_at z8 c8 aeval] in Hk |- *; cbn in Hk; apply G; [left | right]; lia.
Qed.

Lemma rj_agree : forall Hp ly S W mem mem' md a, ARcf tfibsegs B ly S Hp W mem md ->
  (forall x, bv_unsigned x <> a -> mem' x = mem x) ->
  forall x, aowned B ly S x -> x <> a -> aview tfibsegs (w_H W) mem' x = aview tfibsegs (w_H W) mem x.
Proof.
intros Hp ly S W mem mem' md a HAR HM x Hx Hne.
pose proof (AR_owned_low_law_ok_cf tfibsegs B ly S Hp W mem md x HAR Hx).
pose proof ASAN_CEIL_range as [CR _]. unfold ASAN_CEIL in CR.
unfold aview, mbyte, mrestrict. rewrite (HM (Z_to_bv 64 x)); [reflexivity|].
rewrite Z_to_bv_unsigned, bv_wrap_small; [exact Hne | change (bv_modulus 64) with (2 ^ 64); lia].
Qed.
Lemma rj_vis : forall (W : world tfibsegs) mem mem' a, 0 <= a < 2 ^ 64 ->
  (forall x, bv_unsigned x <> a -> mem' x = mem x) -> mem' (Z_to_bv 64 a) <> None ->
  forall x, aview tfibsegs (w_H W) mem x <> None -> aview tfibsegs (w_H W) mem' x <> None.
Proof.
intros W mem mem' a A64 HM HA x Hx. unfold aview, mbyte, mrestrict in Hx |- *.
destruct (Z.eq_dec (bv_unsigned (Z_to_bv 64 x)) a) as [E|NE].
- revert Hx. destruct (w_H W (Z_to_bv 64 x)) eqn:Hh; intros Hx; [exact Hx|].
  assert (EW : Z_to_bv 64 x = Z_to_bv 64 a).
  { apply bv_eq. rewrite E. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity | change (bv_modulus 64) with (2 ^ 64); lia]. }
  rewrite EW. destruct (mem' (Z_to_bv 64 a)) eqn:E'; [cbn; discriminate | exfalso; exact (HA eq_refl)].
- rewrite (HM _ NE). exact Hx.
Qed.
Lemma rj_page : forall ly a, layout_ok ly -> ly_space ly + kRegionInfoOff <= a < ly_space ly + kRegionInfoOff + 4096 ->
  0 <= a < 2 ^ 64 /\ kHighMemBeg <= a.
Proof.
intros ly a LO JR. pose proof (lo_space_in _ LO) as [S1 S2]. pose proof (lo_high _ LO) as [H1 H2].
pose proof ASAN_CEIL_range as [CR _]. rewrite rj_kRI in JR. rewrite rj_kSS in S2.
unfold ASAN_CEIL, kPrimResvSize, kHighMemBeg in *. split; lia.
Qed.
Lemma rj_ARcf_core : forall Hp ly S R W mem mem' md a,
  ARcf tfibsegs B ly S Hp W mem md ->
  ly_space ly + kRegionInfoOff <= a < ly_space ly + kRegionInfoOff + 4096 ->
  Forall (cell_bytes_in B (fun x => x <> a) ly) (acells_cf B ly S) ->
  (forall x, bv_unsigned x <> a -> mem' x = mem x) -> mem' (Z_to_bv 64 a) <> None ->
  Forall2 rj_rsame (st_regions S) R -> Wf_cf (as_universe B) (set_regions R S) ->
  exh_cell_cf B ly (set_regions R S) (aview tfibsegs (w_H W) mem') ->
  ARcf tfibsegs B ly (set_regions R S) Hp W mem' md.
Proof.
intros Hp ly S R W mem mem' md a HAR JR JC HM HA F W1 EX.
pose proof HAR as (M & L & BUD & MW & HS).
destruct (rj_page ly a (amc_layout _ _ _ _ _ M) JR) as [A64 AHI].
assert (BAND : forall x, in_band_rw x -> mem' (YG0n.w64 x) = mem (YG0n.w64 x)).
{ intros x Hx. apply HM. unfold YG0n.w64.
  unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hx.
  rewrite Z_to_bv_unsigned, bv_wrap_small; [|change (bv_modulus 64) with (2 ^ 64); lia]. unfold kHighMemBeg in AHI. lia. }
split; [exact (rj_ARmcf_core ly S R Hp _ _ a M JR JC (rj_agree Hp ly S W mem mem' md a HAR HM) (rj_vis W mem mem' a A64 HM HA) F W1 EX)|].
split; [exact (rj_ledger ly S R md F (amc_wf _ _ _ _ _ M) W1 L)|].
split; [exact (rj_budget ly S R W F BUD)|].
split; [exact MW|].
destruct HS as [HP HZ]. split.
- intros x Hx NC HV. rewrite (BAND x Hx). exact (HP x Hx NC HV).
- exact (ahz_keep_same ly S (set_regions R S) mem mem' eq_refl BAND HZ).
Qed.

Lemma ARcf_junk_write : forall Hp ly S W mem mem' md a, In_junk_cf ly S a -> ARcf tfibsegs B ly S Hp W mem md ->
  (forall x, bv_unsigned x <> a -> mem' x = mem x) -> mem' (Z_to_bv 64 a) <> None -> ARcf tfibsegs B ly S Hp W mem' md.
Proof.
intros Hp ly S W mem mem' md a (JR & _ & JC & JX) HAR HM HA.
pose proof (proj1 HAR) as M. destruct (amc_cells_owned _ _ _ _ _ M) as [HX _].
assert (ES : set_regions (st_regions S) S = S) by (destruct S; reflexivity).
rewrite <- ES. apply (rj_ARcf_core Hp ly S (st_regions S) W mem mem' md a HAR JR JC HM HA (rj_F2_refl _)); rewrite ES.
- exact (amc_wf _ _ _ _ _ M).
- apply (exh_cell_move_cf B ly S S Hp _ _ (fun x => x <> a) M HX (fun _ => eq_refl) (rj_agree Hp ly S W mem mem' md a HAR HM)).
  + intros c Hc. cbn [aoff aeval]. unfold EXH_OFF_t in HX. rewrite HX. pose proof (JX c Hc) as N. unfold region_lock_addr in N. lia.
  + exact (amc_exh_cell _ _ _ _ _ M).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 5. The exhausted byte RegionInfo(c) + 68 and the model's set_exh_cf.                                            *)
(* No region cell covers it: class c' pins bytes 0 .. 63 of its 128-byte RegionInfo, and 68 is not among them. *)

Lemma region_cells_cf_exh : forall ly S c, 1 <= c <= 31 ->
  Forall (cell_bytes_in B (fun x => x <> region_lock_addr ly c + 68) ly) (flat_map (region_cells_cf S) (zseq 1 31)).
Proof.
intros ly S c Hc. apply Forall_forall. intros cl Hcl. apply in_flat_map in Hcl as (c' & Hc' & Hcl).
apply zseq_In' in Hc'. unfold region_cells_cf, region_cells in Hcl. cbn [removelast] in Hcl. unfold region_lock_addr.
destruct Hcl as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; intros k Hk; cbn [c_at c_w z8 c8 aeval aoff] in *; cbn in Hk; lia.
Qed.
Lemma exh_not_cell : forall c ly S Hp rd, 1 <= c <= 31 -> ARmcf B ly S Hp rd ->
  Forall (cell_bytes_in B (fun x => x <> region_lock_addr ly c + 68) ly) (acells_cf B ly S).
Proof.
intros c ly S Hp rd Hc M. unfold acells_cf. apply Forall_app. split.
- exact (region_cells_cf_exh ly S c Hc).
- eapply Forall_impl; [|exact (rest_cells_nri ly S Hp rd M)]. intros cl Hcl k Hk. pose proof (Hcl k Hk) as N.
  unfold nri, region_lock_addr in *. lia.
Qed.

Lemma ARcf_exh_set : forall c Hp ly S W mem mem' md, 1 <= c <= 31 -> c <> kBatchClass ->
  ARcf tfibsegs B ly S Hp W mem md ->
  (forall x : word, bv_unsigned x <> region_lock_addr ly c + 68 -> mem' x = mem x) ->
  mem' (Z_to_bv 64 (region_lock_addr ly c + 68)) = Some (Z_to_bv 8 1) ->
  ARcf tfibsegs B ly (RepModelcf.exh_set c S) Hp W mem' md.
Proof.
intros c Hp ly S W mem mem' md Hc Hnb HAR HM HV.
pose proof HAR as (M & L & _).
pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (amc_layout _ _ _ _ _ M) as LO.
destruct (amc_cells_owned _ _ _ _ _ M) as [HX HO]. unfold EXH_OFF_t in HX.
set (a := region_lock_addr ly c + 68) in *.
assert (JR : ly_space ly + kRegionInfoOff <= a < ly_space ly + kRegionInfoOff + 4096) by (unfold a, region_lock_addr; lia).
destruct (rj_page ly a LO JR) as [A64 AHI].
pose proof (wfc_len_regions _ _ _ _ _ WF) as LEN.
set (r0 := reg S c).
set (R := zupd c (mkRegion (rg_mapped_user r0) (rg_alloc_user r0) (rg_mapped_fa r0) (rg_free r0)
                        (add_hole (EXH_HOLE, 0) (rg_holes r0))) (st_regions S)).
change (RepModelcf.exh_set c S) with (set_regions R S).
assert (F : Forall2 rj_rsame (st_regions S) R).
{ unfold R, zupd. apply rj_F2_lupd; [lia|]. unfold r0, reg, znth. repeat split. }
assert (W1 : Wf_cf (as_universe B) (set_regions R S)).
{ pose proof (set_exh_ret_cf_ok (as_universe B) 0 0 0 S c true WF Hc) as H.
  match type of H with atok _ ?t _ => change t with (@IRet astate (bool * astate) (false, set_regions R S)) in H end.
  cbn [atok] in H. unfold exh_post_cf in H. destruct H as [_ (r' & _ & W' & _)]. exact W'. }
assert (EM : forall c', exh_mem_cf (set_regions R S) c' = if c' =? c then true else exh_mem_cf S c').
{ intros c'. unfold exh_mem_cf, reg, znth. cbn [set_regions st_regions]. unfold R, zupd. destruct (Z.eqb_spec c' c) as [->|Hne].
  - rewrite YG04.nth_lupd_same by lia. cbn [rg_holes]. apply add_hole_exh.
  - rewrite YG04.nth_lupd_other by lia. reflexivity. }
pose proof (rj_agree Hp ly S W mem mem' md a HAR HM) as AGc.
assert (EX : exh_cell_cf B ly (set_regions R S) (aview tfibsegs (w_H W) mem')).
{ destruct (amc_exh_cell _ _ _ _ _ M) as [E1 E2]. split.
  - intros c' Hc'. rewrite EM. destruct (Z.eqb_spec c' c) as [->|Hne].
    + assert (VIS0 : aview tfibsegs (w_H W) mem a <> None).
      { pose proof (E1 c Hc) as C. unfold cell_holds in C. cbn [z1 c1 c_at c_val c_w aeval aoff] in C.
        specialize (C 0%nat ltac:(lia)). rewrite HX in C. unfold a, region_lock_addr. rewrite Z.add_0_r in C.
        replace (ly_space ly + kRegionInfoOff + 128 * c + 68) with (ly_space ly + (kRegionInfoOff + 128 * c + 68)) by lia.
        rewrite C. discriminate. }
      destruct (aview_present_cf tfibsegs ly S md (w_H W) mem a L A64
                  ltac:(intros Hi; pose proof (nri_img ly a LO Hi) as N; unfold nri in N; lia) VIS0) as [Hh _].
      unfold cell_holds. cbn [z1 c1 c_at c_val c_w aeval aoff]. intros k Hk. assert (k = 0%nat) by lia. subst k.
      rewrite HX, Z.add_0_r.
      replace (ly_space ly + (kRegionInfoOff + 128 * c + 68)) with a by (unfold a, region_lock_addr; lia).
      unfold aview, mbyte, mrestrict. rewrite Hh, HV. cbn [option_map]. rewrite Z_to_bv_unsigned. reflexivity.
    + apply (cell_holds_agree B ly _ _ _ (E1 c' Hc')). intros k Hk. cbn [c_w c_at z1 c1] in Hk |- *.
      assert (K0 : k = 0) by lia. subst k. rewrite Z.add_0_r.
      apply AGc; [exact (exh_byte_owned_cf B ly S Hp _ c' M HX Hc') |].
      cbn [aoff aeval]. rewrite HX. unfold a, region_lock_addr. lia.
  - rewrite EM. destruct (Z.eqb_spec kBatchClass c) as [E|_]; [exfalso; apply Hnb; symmetry; exact E | exact E2]. }
assert (JC : Forall (cell_bytes_in B (fun x => x <> a) ly) (acells_cf B ly S)) by exact (exh_not_cell c ly S Hp _ Hc M).
exact (rj_ARcf_core Hp ly S R W mem mem' md a HAR JR JC HM ltac:(rewrite HV; discriminate) F W1 EX).
Qed.


End a.
