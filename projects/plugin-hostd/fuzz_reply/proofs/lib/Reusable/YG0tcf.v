(* CARRIED from commit 7fb5e1d920f1a960ba591aa28cade9497d873d3c,
   proofs/cgif/cgif_file_fuzzer/lib/YG0tcf.v, sha256 f62aa1742b01a901f9259d6d78821012e554c696815d023afeb0fb237a73e5e5 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
*)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Taken by path from a working branch a0fed4266a1b, provisional. *)
(* Modified by Theorem Labs, 2026-10: module paths changed from fuzz_preset lib.Reusable to cgif_file_fuzzer lib; the text is otherwise unchanged. *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), the two STACK laws and the
   heap-head frame law.
   Source: cgif's YG0t.v (copied into this unit as lib/Reusable/YG0t.v), re-proved over the fresh record
   ARcf / ARmcf of YG0ncf.v. cgif's YG0t.v is NOT edited.
   The statements proved here are YG0dcf.v's astack_free_law_cf and astack_malloc_law_cf (adopted there from
   this file's first version, 47e01d3478d5): YG0d.v:301-309 and YG0t.v:577-589 with AR -> ARcf and the
   binder Hp after S, Hp unchanged. astack_malloc_law_cf is FCiface.v's astack_malloc_law_x at
   ARx := ARcf segs B (eq_refl). AR_head_frame_law_ok_cf proves YG0dcf.v's AR_head_frame_law_cf (from
   h-rw-man-5's YGcfHp.v:63, 29c8b46b1cef), the 15th field of AR_laws_cf; it has no cgif original.
   Every helper of YG0t.v that names ARm / AR / Wf / acells / ajunk / ALedger is restated with the suffix
   _cf and the naming contract's substitutions. Helpers of YG0t.v that name none of these are used from
   YG0t.v as they stand; the YG05.v steps over Wf_cf come from YG05cf.v. The cells' footprint (cgif's
   *_cells_nf family) is proved once over an address predicate (fp_zones, *_in_cf) and the cgif names are
   its instances at nf; the head law uses the same family at not chunk_shadow_cf.
   Changed beyond the substitutions: nothing in a statement. In the proofs, cgif's 2 GiB class bound
   (mapped_user_bound, kUserMapSize * EV_MAX) is YG01cf.v's mapped_bound_cf (kFreeArrayOffset), and the
   chunk facts are YG0scf.v's cfacts_cf. No address. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09 YO0d YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0s YG0q YG0t.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG05cf YG0scf YG0qcf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* ---------------------------------------------------------------------------- *)
(* The proofs. YG0t.v's Ltac ceil; YG0t.v's ARm-free helpers are used from YG0t.v. *)
Ltac ceil := let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold ASAN_CEIL in H2.
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Section u.
Variable segs : list Segment.
Variable B : asyms.
Local Abbreviation cell_bytes_nf := (YG0t.cell_bytes_nf B).
Local Abbreviation cnf_of_range := (YG0t.cnf_of_range B).
Local Abbreviation Forall_cnf_of_range := (YG0t.Forall_cnf_of_range B).
Local Abbreviation Forall_cell_holds_agree_nf := (YG0t.Forall_cell_holds_agree_nf B).
Local Abbreviation ahs_transfer_grow := (YG0t.ahs_transfer_grow segs B).
Lemma nf_sec_cf : forall ly S Hp rd e a, ARmcf B ly S Hp rd -> In e (sec_extents ly S) -> fst e <= a < fst e + snd e -> nf ly a.
Proof.
intros ly S Hp rd e a M He Ha. pose proof (amc_layout _ _ _ _ _ M) as LO. eapply nf_of_disjoint; [exact LO | | |exact Ha].
- exact (pairwise_In zdisjoint _ e (ly_F ly, kFakeStackSize) (sec_extents ly S) (static_extents ly) eq_refl (proj2 (amc_placed _ _ _ _ _ M)) He
ltac:(unfold static_extents, owned_extents; cbn; tauto)).
- pose proof (proj1 (Forall_forall _ _) (proj1 (amc_placed _ _ _ _ _ M)) _ He) as (_ & [I0 I1] & _). lia.
Qed.
Lemma nf_img_cf : forall ly S Hp rd a, ARmcf B ly S Hp rd -> in_zr a (ly_img ly) -> nf ly a.
Proof.
intros ly S Hp rd a M Ha. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (lo_img _ LO) as (I0 & I1 & I2 & I3). unfold in_zr in Ha.
eapply (nf_static_ext ly (ly_img ly)); [exact LO | unfold static_extents; apply in_app_iff; right; right; left; reflexivity | | exact Ha].
intros E. pose proof (f_equal snd E) as E2. cbn in E2. unfold kImgLo, kImgEnd, kFakeStackSize in *. lia.
Qed.
Lemma nf_core_cf : forall ly S Hp rd e a, ARmcf B ly S Hp rd -> In e (core_extents ly) -> fst e <= a < fst e + snd e -> nf ly a.
Proof.
intros ly S Hp rd e a M He Ha. pose proof (amc_layout _ _ _ _ _ M) as LO. eapply nf_static_ext; [exact LO | | | exact Ha].
- unfold core_extents in He. unfold static_extents, owned_extents. cbn in He |- *. intuition.
- intros ->. unfold core_extents in He. cbn in He.
destruct He as [E|[E|[E|[E|[E|[E|[]]]]]]]; pose proof (f_equal snd E) as E2; cbn in E2; unfold kPtrArrayResv, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kFakeStackSize in E2; lia.
Qed.
Lemma nf_F_low_cf : forall ly S Hp rd a, ARmcf B ly S Hp rd -> ly_F ly + 88 <= a < ly_F ly + kFakeFlagsOff -> nf ly a.
Proof.
intros ly S Hp rd a M Ha. pose proof (amc_layout _ _ _ _ _ M) as LO. destruct (F_app ly LO) as (F0 & FZ & _). unfold nf. split; [right; lia |].
apply (nf2_app ly a LO). unfold kFakeFlagsOff, kFakeStackSize in *. lia.
Qed.
Lemma nf_shadow_static_cf : forall ly S Hp rd r a, ARmcf B ly S Hp rd -> In r (as_owned_static B) ->
shadow_addr (fst r) <= a < shadow_addr (fst r) + (snd r + 7) / 8 -> nf ly a.
Proof.
intros ly S Hp rd r a M Hr Ha. pose proof (amc_layout _ _ _ _ _ M) as LO. apply (nf_shadow_hull ly a LO).
pose proof (lo_img _ LO) as (I0 & I1 & I2 & I3).
pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hr)) as [R1 R2].
pose proof (proj1 (Forall_forall _ _) (aso_static _ (amc_syms _ _ _ _ _ M)) r Hr) as (T1 & T2 & T3).
unfold shadow_addr in *.
pose proof (Z.div_le_mono (fst (ly_img ly)) (fst r) 8 ltac:(lia) ltac:(lia)).
unfold page_aligned in I3. apply Z.mod_divide in I3 as [q Hq]; [|lia]. rewrite I0 in *. unfold kImgLo in *. change (65536 / 8) with 8192 in *.
assert (E2 : snd (ly_img ly) / 8 = q * 512) by (rewrite Hq; replace (q * 4096) with ((q * 512) * 8) by lia; apply Z_div_mult; lia).
pose proof (Z_div_mod_eq_full (fst r) 8) as DM1. pose proof (Z.mod_pos_bound (fst r) 8 ltac:(lia)) as MB1.
pose proof (Z_div_mod_eq_full (snd r + 7) 8) as DM2. pose proof (Z.mod_pos_bound (snd r + 7) 8 ltac:(lia)) as MB2.
rewrite E2. lia.
Qed.

(* ----------------------------------------------------------------------------
   The cells' footprint, parametrised over the address predicate P that every byte a cell reads
   satisfies. cgif's YG0t.v:20-338 fixes P := nf ly (the bytes outside the fake stack and its
   shadow); the heap-head frame law below takes P := not chunk_shadow_cf (not the shadow byte of a
   chunk granule). fp_zones lists the address zones the cells live in; each _in_cf lemma is cgif's
   _nf proof with each nf point fact replaced by a zone, and cgif's _nf_cf names are the instances
   at P := nf ly. *)
Definition cell_bytes_in (P : Z -> Prop) (ly : alayout) (c : acell) : Prop :=
forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> P (aeval B ly (c_at c) + k).
Record fp_zones (P : Z -> Prop) (ly : alayout) (S : astate) : Prop := {
fz_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> P a;
fz_core : forall e a, In e (core_extents ly) -> fst e <= a < fst e + snd e -> P a;
fz_img : forall a, in_zr a (ly_img ly) -> P a;
fz_sec : forall e a, In e (sec_extents ly S) -> fst e <= a < fst e + snd e -> P a;
fz_F_low : forall a, ly_F ly + 88 <= a < ly_F ly + kFakeFlagsOff -> P a;
fz_shadow_static : forall r a, In r (as_owned_static B) -> shadow_addr (fst r) <= a < shadow_addr (fst r) + (snd r + 7) / 8 -> P a
}.
Lemma fp_zones_nf_cf : forall ly S Hp rd, ARmcf B ly S Hp rd -> fp_zones (nf ly) ly S.
Proof.
intros ly S Hp rd M. pose proof (amc_layout _ _ _ _ _ M) as LO. constructor.
- intros a Ha. exact (nf_prim ly a LO Ha).
- intros e a He Ha. exact (nf_core_cf ly S Hp rd e a M He Ha).
- intros a Ha. exact (nf_img_cf ly S Hp rd a M Ha).
- intros e a He Ha. exact (nf_sec_cf ly S Hp rd e a M He Ha).
- intros a Ha. exact (nf_F_low_cf ly S Hp rd a M Ha).
- intros r a Hr Ha. exact (nf_shadow_static_cf ly S Hp rd r a M Hr Ha).
Qed.
Lemma cbi_of_range : forall P ly c lo len, (forall a, lo <= a < lo + len -> P a) ->
lo <= aeval B ly (c_at c) -> aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len -> cell_bytes_in P ly c.
Proof. intros P ly c lo len OR H1 H2 k Hk. apply OR. lia. Qed.
Lemma Forall_cbi_of_range : forall P ly l lo len, (forall a, lo <= a < lo + len -> P a) ->
Forall (fun c => lo <= aeval B ly (c_at c) /\ aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len) l -> Forall (cell_bytes_in P ly) l.
Proof. intros P ly l lo len OR H. eapply Forall_impl; [|exact H]. intros c [H1 H2]. eapply cbi_of_range; eauto. Qed.
Lemma Forall_cell_holds_agree_in : forall P ly S rd rd' l,
(forall a, aowned B ly S a -> P a -> rd' a = rd a) -> Forall (cell_bytes_owned B ly S) l -> Forall (cell_bytes_in P ly) l ->
Forall (cell_holds B ly rd) l -> Forall (cell_holds B ly rd') l.
Proof.
intros P ly S rd rd' l AG OW NF H. apply Forall_forall. intros c Hc.
eapply cell_holds_agree; [exact (proj1 (Forall_forall _ _) H c Hc)|]. intros k Hk.
apply AG; [exact (proj1 (Forall_forall _ _) OW c Hc k Hk) | exact (proj1 (Forall_forall _ _) NF c Hc k Hk)].
Qed.
Lemma static_in_cf : forall P ly S Hp rd a, ARmcf B ly S Hp rd -> fp_zones P ly S -> Exists (in_zr a) (as_owned_static B) -> P a.
Proof.
intros P ly S Hp rd a M FZ H. apply Exists_exists in H as (r & Hr & [H1 H2]).
pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hr)) as [S1 S2].
apply (fz_img _ _ _ FZ). unfold in_zr. lia.
Qed.
Lemma area_in_cf : forall P ly S Hp rd r a, ARmcf B ly S Hp rd -> fp_zones P ly S -> In r (asyms_areas B) -> fst r <= a < fst r + snd r -> P a.
Proof.
intros P ly S Hp rd r a M FZ Hr Ha. pose proof (proj1 (Forall_forall _ _) (aso_cover _ (amc_syms _ _ _ _ _ M)) r Hr) as X.
apply Exists_exists in X as (r' & Hr' & [X1 X2]). eapply static_in_cf; [exact M | exact FZ |]. apply Exists_exists. exists r'. split; [exact Hr'|]. unfold in_zr. lia.
Qed.
Lemma rinfo_in_cf : forall P ly S Hp rd a, ARmcf B ly S Hp rd -> fp_zones P ly S -> ly_space ly + kRegionInfoOff <= a < ly_space ly + kRegionInfoOff + 4096 -> P a.
Proof.
intros P ly S Hp rd a M FZ Ha. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (lo_space_in _ LO) as [S1 S2]. unfold kRegionInfoOff, kSpaceSize in *.
apply (fz_prim _ _ _ FZ). lia.
Qed.
Lemma meta_in_cf : forall P ly S Hp rd k a, ARmcf B ly S Hp rd -> fp_zones P ly S -> In k (st_chunks S) ->
ck_base B ly k - (match ck_beg k with PSec _ _ => kPage | _ => 0 end) <= a < ck_base B ly k + ck_rz k -> P a.
Proof.
intros P ly S Hp rd k a M FZ Hk Ha. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal). unfold kFreeArrayOffset in Gal.
pose proof (region_in_prim ly (prim_class o) (amc_layout _ _ _ _ _ M) ltac:(lia)) as (R1 & R2 & _).
apply (fz_prim _ _ _ FZ). lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
apply (fz_sec _ _ _ FZ (ly_sec ly r, sec_map_size (ck_req k)) a Gin). cbn [fst snd]. unfold kPage in *. lia.
Qed.
Lemma batch_in_cf : forall P ly S Hp rd b a, ARmcf B ly S Hp rd -> fp_zones P ly S -> In b (all_batches S) ->
ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> P a.
Proof.
intros P ly S Hp rd b a M FZ Hb Ha. pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (wfc_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; auto).
pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wrc_alloc _ _ _ _ _ _ CL) as AL. pose proof (mapped_bound_cf (as_universe B) 0 0 0 S kBatchClass WF ltac:(unfold kBatchClass; lia)) as MB.
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5).
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2.
unfold kBatchBytes, kFreeArrayOffset in *.
assert (BX : ly_space ly + b_self b = region_base ly kBatchClass + x) by (unfold region_base; subst x; lia).
apply (fz_prim _ _ _ FZ). lia.
Qed.
Ltac fcons' := apply Forall_cons; [cbn; lia|].
Lemma region_cells_in_cf : forall P ly S Hp rd c, ARmcf B ly S Hp rd -> fp_zones P ly S -> 1 <= c <= 31 -> Forall (cell_bytes_in P ly) (region_cells S c).
Proof.
intros P ly S Hp rd c M FZ Hc. apply (Forall_cbi_of_range P ly _ (ly_space ly + kRegionInfoOff) 4096); [intros a Ha; eapply rinfo_in_cf; [exact M | exact FZ | exact Ha]|].
unfold region_cells, kRegionInfoOff. repeat fcons'. apply Forall_nil.
Qed.
Lemma cache_cells_in_cf : forall P ly S Hp rd c, ARmcf B ly S Hp rd -> fp_zones P ly S -> 1 <= c <= 31 -> Forall (cell_bytes_in P ly) (cache_cells S c).
Proof.
intros P ly S Hp rd c M FZ Hc.
assert (OR : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> P a).
{ intros a Ha. apply (fz_core _ _ _ FZ (ly_T ly, kThreadObjSize)); [unfold core_extents; cbn; tauto | exact Ha]. }
apply (Forall_cbi_of_range P ly _ (ly_T ly) kThreadObjSize OR).
pose proof (wfc_classes _ _ _ _ _ (amc_wf _ _ _ _ _ M) c Hc) as CL. pose proof (wrc_cache _ _ _ _ _ _ CL) as WC. pose proof (class_ok c Hc) as (_ & _ & _ & K4 & _).
unfold cache_cells, t_cache, kThreadObjSize. destruct (st_cache_inited S).
- destruct WC as [PM PL]. repeat fcons'. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i v] & <- & Hiv). cbn [fst snd c_at c_w z4 c4 aeval aoff].
apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. lia.
- repeat fcons'. apply Forall_nil.
Qed.
Lemma chunk_cells_in_cf : forall P ly S Hp rd k, ARmcf B ly S Hp rd -> fp_zones P ly S -> In k (st_chunks S) -> Forall (cell_bytes_in P ly) (chunk_cells k).
Proof.
intros P ly S Hp rd k M FZ Hk. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
assert (OR : forall a, ck_base B ly k <= a < ck_base B ly k + ck_rz k -> P a).
{ intros a Ha. eapply meta_in_cf; [exact M | exact FZ | exact Hk |]. destruct (ck_beg k); unfold kPage; lia. }
apply (Forall_cbi_of_range P ly _ _ _ OR).
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
Lemma sec_cells_in_cf : forall P ly S Hp rd, ARmcf B ly S Hp rd -> fp_zones P ly S -> Forall (cell_bytes_in P ly) (sec_cells S).
Proof.
intros P ly S Hp rd M FZ. pose proof (wfc_secondary _ _ _ _ _ (amc_wf _ _ _ _ _ M)) as X. destruct X as [Snd Sac Sal Sres Sral].
assert (ORI : forall a, as_inst B <= a < as_inst B + 3632 -> P a) by (intros a Ha; exact (area_in_cf P ly S Hp rd (as_inst B, 3632) a M FZ ltac:(cbn; tauto) Ha)).
unfold sec_cells.
apply Forall_cons; [eapply cbi_of_range; [exact ORI | cbn; unfold o_sec_reserved; lia | cbn; unfold o_sec_reserved; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORI | cbn; unfold o_sec_n; lia | cbn; unfold o_sec_n; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORI | cbn; unfold o_sec_mutex; lia | cbn; unfold o_sec_mutex; lia]|].
apply Forall_app. split.
- apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
eapply cbi_of_range; [intros a Ha; apply (fz_core _ _ _ FZ (ly_Q ly, kPtrArrayResv)); [unfold core_extents; cbn; tauto | exact Ha] | cbn; lia |].
cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
- apply Forall_forall. intros c Hc. apply in_flat_map in Hc as (k & Hk & Hc).
pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg k) as [|o|r o|c' p] eqn:Eb; try solve [destruct Hc].
destruct GG as (-> & _ & Gbase & Gext & Gin & _).
assert (OR : forall a, ly_sec ly r <= a < ly_sec ly r + kPage -> P a).
{ intros a Ha. eapply meta_in_cf; [exact M | exact FZ | exact Hk |]. rewrite Eb. unfold kPage in *. lia. }
unfold kPage in OR.
destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; (eapply cbi_of_range; [exact OR | cbn; lia | cbn; lia]).
Qed.
Lemma batch_cells_in_cf : forall P ly S Hp rd l, ARmcf B ly S Hp rd -> fp_zones P ly S -> incl l (all_batches S) -> Forall (cell_bytes_in P ly) (batch_cells l).
Proof.
intros P ly S Hp rd l M FZ. induction l as [|b t IH]; intros Hincl; [apply Forall_nil|]. cbn [batch_cells].
pose proof (wq_batches _ (wfc_quarantine _ _ _ _ _ (amc_wf _ _ _ _ _ M))) as BL.
pose proof (proj1 (Forall_forall _ _) BL b (Hincl b (or_introl eq_refl))) as [L1 L2]. unfold kBatchSlots in L2.
assert (OR : forall a, ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> P a)
by (intros a Ha; eapply batch_in_cf; [exact M | exact FZ | apply Hincl; left; reflexivity | exact Ha]).
unfold kBatchBytes in OR.
apply Forall_cons; [eapply cbi_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_app. split.
- apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i k] & <- & Hik). apply in_combine_l in Hik. apply in_seq in Hik.
eapply cbi_of_range; [exact OR | cbn; lia | cbn; lia].
- apply IH. intros x Hx. apply Hincl. right. exact Hx.
Qed.
Lemma quar_cells_in_cf : forall P ly S Hp rd, ARmcf B ly S Hp rd -> fp_zones P ly S -> Forall (cell_bytes_in P ly) (quar_cells S).
Proof.
intros P ly S Hp rd M FZ.
assert (ORT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> P a).
{ intros a Ha. apply (fz_core _ _ _ FZ (ly_T ly, kThreadObjSize)); [unfold core_extents; cbn; tauto | exact Ha]. }
assert (ORI : forall a, as_inst B <= a < as_inst B + 3632 -> P a) by (intros a Ha; exact (area_in_cf P ly S Hp rd (as_inst B, 3632) a M FZ ltac:(cbn; tauto) Ha)).
unfold kThreadObjSize in ORT.
unfold quar_cells, qc_cells, o_q_cmutex, o_q_rmutex, o_q_size, t_qc.
apply Forall_cons; [eapply cbi_of_range; [exact ORI | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORI | cbn; lia | cbn; lia]|].
apply Forall_app. split.
- do 4 (apply Forall_cons; [eapply cbi_of_range; [exact ORT | cbn; lia | cbn; lia]|]).
eapply batch_cells_in_cf; [exact M | exact FZ | intros b Hb; unfold all_batches; apply in_app_iff; left; exact Hb].
- do 4 (apply Forall_cons; [eapply cbi_of_range; [exact ORI | cbn; lia | cbn; lia]|]).
eapply batch_cells_in_cf; [exact M | exact FZ | intros b Hb; unfold all_batches; apply in_app_iff; right; exact Hb].
Qed.
Lemma fs_hdr_in_cf : forall P ly S, fp_zones P ly S -> Forall (cell_bytes_in P ly) fs_hdr.
Proof.
intros P ly S FZ. assert (OR : forall a, ly_F ly + 88 <= a < ly_F ly + 88 + (kFakeFlagsOff - 88) -> P a) by (intros a Ha; apply (fz_F_low _ _ _ FZ); lia).
unfold kFakeFlagsOff in OR. unfold fs_hdr.
apply Forall_cons; [eapply cbi_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact OR | cbn; lia | cbn; lia]|]. apply Forall_nil.
Qed.
Lemma depot_cells_in_cf : forall P ly S Hp rd, ARmcf B ly S Hp rd -> fp_zones P ly S -> Forall (cell_bytes_in P ly) (depot_cells ly S).
Proof.
intros P ly S Hp rd M FZ.
assert (ORD : forall a, as_depot B <= a < as_depot B + (4 * 2 ^ 20 + 32) -> P a) by (intros a Ha; exact (area_in_cf P ly S Hp rd (as_depot B, 4 * 2 ^ 20 + 32) a M FZ ltac:(cbn; tauto) Ha)).
assert (ORS : forall a, as_store B <= a < as_store B + 32 -> P a) by (intros a Ha; exact (area_in_cf P ly S Hp rd (as_store B, 32) a M FZ ltac:(cbn; tauto) Ha)).
unfold depot_cells, d_nuniq, d_map1, s_total, s_block0.
apply Forall_cons; [eapply cbi_of_range; [exact ORD | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORD | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORS | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORS | cbn; lia | cbn; lia]|]. apply Forall_nil.
Qed.
Lemma ialloc_cells_in_cf : forall P ly S Hp rd, ARmcf B ly S Hp rd -> fp_zones P ly S -> Forall (cell_bytes_in P ly) (ialloc_cells B S).
Proof.
intros P ly S Hp rd M FZ. pose proof (aso_ialloc _ (amc_syms _ _ _ _ _ M)) as [I1 I2].
assert (ORA : forall a, as_ialloc_lo B <= a < as_ialloc_lo B + (as_ialloc_hi B - as_ialloc_lo B) -> P a)
by (intros a Ha; exact (area_in_cf P ly S Hp rd (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B) a M FZ ltac:(cbn; tauto) Ha)).
assert (ORF : forall a, as_ialloc_flag B <= a < as_ialloc_flag B + 2 -> P a)
by (intros a Ha; exact (area_in_cf P ly S Hp rd (as_ialloc_flag B, 2) a M FZ ltac:(cbn; tauto) Ha)).
unfold ialloc_cells.
apply Forall_cons; [eapply cbi_of_range; [exact ORF | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORF | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORA | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORA | cbn; lia | cbn; lia]|]. apply Forall_nil.
Qed.
Lemma thread_cells_in_cf : forall P ly S, fp_zones P ly S -> Forall (cell_bytes_in P ly) thread_cells.
Proof.
intros P ly S FZ. unfold thread_cells, t_unwinding. apply Forall_cons; [|apply Forall_nil].
eapply cbi_of_range; [intros a Ha; apply (fz_core _ _ _ FZ (ly_T ly, kThreadObjSize)); [unfold core_extents; cbn; tauto | exact Ha] | cbn; lia | cbn; unfold kThreadObjSize; lia].
Qed.
Lemma const_cells_in_cf : forall P ly S Hp rd, ARmcf B ly S Hp rd -> fp_zones P ly S -> Forall (cell_bytes_in P ly) (as_const B ly).
Proof.
intros P ly S Hp rd M FZ. eapply Forall_impl; [|exact (amc_const_owned _ _ _ _ _ M)]. intros c Hc k Hk.
destruct (Hc k Hk) as [O|[O|O]].
- eapply static_in_cf; [exact M | exact FZ | exact O].
- apply Exists_exists in O as (e & He & Hin). exact (fz_core _ _ _ FZ e _ He Hin).
- apply Exists_exists in O as (r & Hr & Hin). exact (fz_shadow_static _ _ _ FZ r _ Hr Hin).
Qed.
(* Every cell of acells_cf, given P on the frame-hint words [F, F + 88) too. *)
Lemma acells_in_cf : forall P ly S Hp rd, ARmcf B ly S Hp rd -> fp_zones P ly S ->
(forall a, ly_F ly <= a < ly_F ly + 88 -> P a) -> Forall (cell_bytes_in P ly) (acells_cf B ly S).
Proof.
intros P ly S Hp rd M FZ HF. unfold acells_cf. rewrite (fs_cells_split S).
assert (RCF : forall c, In c (zseq 1 31) -> Forall (cell_bytes_in P ly) (region_cells_cf S c)).
{ intros c Hc. apply Forall_forall. intros x Hx.
apply (proj1 (Forall_forall _ _) (region_cells_in_cf P ly S Hp rd c M FZ ltac:(pose proof (zseq_In' 1 31 c Hc); lia))).
eapply region_cells_cf_incl. exact Hx. }
apply Forall_app; split; [exact (Forall_flat_map'' _ _ _ RCF)|].
apply Forall_app; split; [exact (Forall_flat_map'' _ _ _ (fun c Hc => cache_cells_in_cf P ly S Hp rd c M FZ ltac:(pose proof (zseq_In' 1 31 c Hc); lia)))|].
apply Forall_app; split; [exact (Forall_flat_map'' _ _ _ (fun k Hk => chunk_cells_in_cf P ly S Hp rd k M FZ Hk))|].
apply Forall_app; split; [exact (sec_cells_in_cf P ly S Hp rd M FZ)|].
apply Forall_app; split; [exact (quar_cells_in_cf P ly S Hp rd M FZ)|].
apply Forall_app; split.
{ apply Forall_app; split; [exact (fs_hdr_in_cf P ly S FZ)|]. unfold fs_hints. apply Forall_forall. intros c Hc.
apply in_map_iff in Hc as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih.
eapply cbi_of_range; [exact (fun a Ha => HF a Ha) | cbn; lia | cbn [c_at c_w z8 c8 aeval aoff fst snd]; cbn; lia]. }
apply Forall_app; split; [exact (depot_cells_in_cf P ly S Hp rd M FZ)|].
apply Forall_app; split; [exact (ialloc_cells_in_cf P ly S Hp rd M FZ)|].
exact (thread_cells_in_cf P ly S FZ).
Qed.
(* cgif's YG0t.v nf family: the instances at P := nf ly. *)
Lemma nf_static_cf : forall ly S Hp rd a, ARmcf B ly S Hp rd -> Exists (in_zr a) (as_owned_static B) -> nf ly a.
Proof. intros ly S Hp rd a M. exact (static_in_cf (nf ly) ly S Hp rd a M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma nf_area_cf : forall ly S Hp rd r a, ARmcf B ly S Hp rd -> In r (asyms_areas B) -> fst r <= a < fst r + snd r -> nf ly a.
Proof. intros ly S Hp rd r a M. exact (area_in_cf (nf ly) ly S Hp rd r a M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma nf_rinfo_cf : forall ly S Hp rd a, ARmcf B ly S Hp rd -> ly_space ly + kRegionInfoOff <= a < ly_space ly + kRegionInfoOff + 4096 -> nf ly a.
Proof. intros ly S Hp rd a M. exact (rinfo_in_cf (nf ly) ly S Hp rd a M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma nf_meta_cf : forall ly S Hp rd k a, ARmcf B ly S Hp rd -> In k (st_chunks S) ->
ck_base B ly k - (match ck_beg k with PSec _ _ => kPage | _ => 0 end) <= a < ck_base B ly k + ck_rz k -> nf ly a.
Proof. intros ly S Hp rd k a M. exact (meta_in_cf (nf ly) ly S Hp rd k a M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma nf_batch_cf : forall ly S Hp rd b a, ARmcf B ly S Hp rd -> In b (all_batches S) ->
ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> nf ly a.
Proof. intros ly S Hp rd b a M. exact (batch_in_cf (nf ly) ly S Hp rd b a M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma region_cells_nf_cf : forall ly S Hp rd c, ARmcf B ly S Hp rd -> 1 <= c <= 31 -> Forall (cell_bytes_nf ly) (region_cells S c).
Proof. intros ly S Hp rd c M. exact (region_cells_in_cf (nf ly) ly S Hp rd c M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma cache_cells_nf_cf : forall ly S Hp rd c, ARmcf B ly S Hp rd -> 1 <= c <= 31 -> Forall (cell_bytes_nf ly) (cache_cells S c).
Proof. intros ly S Hp rd c M. exact (cache_cells_in_cf (nf ly) ly S Hp rd c M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma chunk_cells_nf_cf : forall ly S Hp rd k, ARmcf B ly S Hp rd -> In k (st_chunks S) -> Forall (cell_bytes_nf ly) (chunk_cells k).
Proof. intros ly S Hp rd k M. exact (chunk_cells_in_cf (nf ly) ly S Hp rd k M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma area_nf_range_cf : forall ly S Hp rd r, ARmcf B ly S Hp rd -> In r (asyms_areas B) -> nf_range ly (fst r) (snd r).
Proof. intros ly S Hp rd r M Hr a Ha. eapply nf_area_cf; eassumption. Qed.
Lemma inst_nf_range_cf : forall ly S Hp rd, ARmcf B ly S Hp rd -> nf_range ly (as_inst B) 3632.
Proof. intros ly S Hp rd M. apply (area_nf_range_cf ly S Hp rd (as_inst B, 3632) M). cbn. tauto. Qed.
Lemma sec_cells_nf_cf : forall ly S Hp rd, ARmcf B ly S Hp rd -> Forall (cell_bytes_nf ly) (sec_cells S).
Proof. intros ly S Hp rd M. exact (sec_cells_in_cf (nf ly) ly S Hp rd M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma batch_cells_nf_cf : forall ly S Hp rd l, ARmcf B ly S Hp rd -> incl l (all_batches S) -> Forall (cell_bytes_nf ly) (batch_cells l).
Proof. intros ly S Hp rd l M. exact (batch_cells_in_cf (nf ly) ly S Hp rd l M (fp_zones_nf_cf ly S Hp rd M)). Qed.

(* The two machine cells (ARmcf's amc_exh_cell / amc_errb_cells, field round 2) move to a reader that agrees on the
   owned bytes in a zone family P (fp_zones: nf for the stack laws, the chunk-shadow exclusion for the head frame law),
   at a state with the same exhausted bits and buffer model values. Ownership of the cells' bytes comes from the rows
   ARmcf carries (amc_cells_owned): the exhausted byte is in the RegionInfo area, the errbuf object in the owned static
   data, and both are inside every zone family. *)
Lemma cells_move_fz_cf : forall P ly S S' Hp rd rd', ARmcf B ly S Hp rd -> fp_zones P ly S ->
(forall c, exh_mem_cf S' c = exh_mem_cf S c) ->
errb_mapped_cf S' = errb_mapped_cf S -> errb_data_cf ly S' = errb_data_cf ly S ->
errb_cap_cf S' = errb_cap_cf S -> errb_size_cf S' = errb_size_cf S ->
(forall a, aowned B ly S a -> P a -> rd' a = rd a) -> (forall a, rd a <> None -> rd' a <> None) ->
exh_cell_cf B ly S' rd' /\ errb_cells_cf B ly S' rd'.
Proof.
intros P ly S S' Hp rd rd' M FZ EX EM ED EC EZ AG VIS. destruct (amc_cells_owned _ _ _ _ _ M) as [HX [HO _]].
split.
- apply (exh_cell_move_cf B ly S S' Hp rd rd' P M HX EX AG); [|exact (amc_exh_cell _ _ _ _ _ M)].
  intros c Hc. apply (rinfo_in_cf P ly S Hp rd _ M FZ). exact (proj1 (exh_byte_where_cf B ly S Hp rd c M HX Hc)).
- apply (errb_cells_move_cf B ly S S' Hp rd rd' P M HO EM ED EC EZ AG VIS); [|exact (amc_errb_cells _ _ _ _ _ M)].
  intros a Ha. exact (static_in_cf P ly S Hp rd a M FZ (HO a Ha)).
Qed.
(* Printf's two cells (field round 3) move the same way: their bytes are owned static data (amc_pf_owned), inside
   every zone family. *)
Lemma pf_cells_move_fz_cf : forall P ly S Hp rd rd', ARmcf B ly S Hp rd -> fp_zones P ly S ->
(forall a, aowned B ly S a -> P a -> rd' a = rd a) -> pf_cells_cf B ly rd'.
Proof.
intros P ly S Hp rd rd' M FZ AG. pose proof (amc_pf_owned _ _ _ _ _ M) as HO.
apply (pf_cells_move_cf B ly S Hp rd rd' P M HO AG); [|exact (amc_pf_cells _ _ _ _ _ M)].
intros a Ha. exact (static_in_cf P ly S Hp rd a M FZ (proj1 (proj1 HO a Ha))).
Qed.
Lemma quar_cells_nf_cf : forall ly S Hp rd, ARmcf B ly S Hp rd -> Forall (cell_bytes_nf ly) (quar_cells S).
Proof. intros ly S Hp rd M. exact (quar_cells_in_cf (nf ly) ly S Hp rd M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma fs_hdr_nf_cf : forall ly S Hp rd, ARmcf B ly S Hp rd -> Forall (cell_bytes_nf ly) fs_hdr.
Proof. intros ly S Hp rd M. exact (fs_hdr_in_cf (nf ly) ly S (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma depot_cells_nf_cf : forall ly S Hp rd, ARmcf B ly S Hp rd -> Forall (cell_bytes_nf ly) (depot_cells ly S).
Proof. intros ly S Hp rd M. exact (depot_cells_in_cf (nf ly) ly S Hp rd M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma ialloc_cells_nf_cf : forall ly S Hp rd, ARmcf B ly S Hp rd -> Forall (cell_bytes_nf ly) (ialloc_cells B S).
Proof. intros ly S Hp rd M. exact (ialloc_cells_in_cf (nf ly) ly S Hp rd M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma thread_cells_nf_cf : forall ly S Hp rd, ARmcf B ly S Hp rd -> Forall (cell_bytes_nf ly) thread_cells.
Proof. intros ly S Hp rd M. exact (thread_cells_in_cf (nf ly) ly S (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma const_cells_nf_cf : forall ly S Hp rd, ARmcf B ly S Hp rd -> Forall (cell_bytes_nf ly) (as_const B ly).
Proof. intros ly S Hp rd M. exact (const_cells_in_cf (nf ly) ly S Hp rd M (fp_zones_nf_cf ly S Hp rd M)). Qed.
Lemma am_cells_set_fs_cf : forall ly S Hp rd rd' f,
ARmcf B ly S Hp rd -> (forall a, aowned B ly S a -> nf ly a -> rd' a = rd a) ->
Forall (cell_holds B ly rd') (fs_hints f) ->
Forall (cell_holds B ly rd') (acells_cf B ly (set_fs f S)).
Proof.
intros ly S Hp rd rd' f M AGN HH. pose proof (amc_cells _ _ _ _ _ M) as X. pose proof (acells_owned_cf B ly S Hp rd M) as OW.
unfold acells_cf in X, OW |- *.
change (flat_map (region_cells_cf (set_fs f S)) (zseq 1 31)) with (flat_map (region_cells_cf S) (zseq 1 31)).
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
assert (RCF : forall c, In c (zseq 1 31) -> Forall (cell_bytes_nf ly) (region_cells_cf S c)).
{ intros c Hc. apply Forall_forall. intros x Hx.
apply (proj1 (Forall_forall _ _) (region_cells_nf_cf ly S Hp rd c M ltac:(pose proof (zseq_In' 1 31 c Hc); lia))).
eapply region_cells_cf_incl. exact Hx. }
apply Forall_app; split.
{ exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWR (Forall_flat_map'' _ _ _ RCF) XR). }
apply Forall_app; split.
{ exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWC (Forall_flat_map'' _ _ _ (fun c Hc => cache_cells_nf_cf ly S Hp rd c M ltac:(pose proof (zseq_In' 1 31 c Hc); lia))) XC). }
apply Forall_app; split.
{ exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWK (Forall_flat_map'' _ _ _ (fun k Hk => chunk_cells_nf_cf ly S Hp rd k M Hk)) XK). }
apply Forall_app; split. { exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWS (sec_cells_nf_cf ly S Hp rd M) XS). }
apply Forall_app; split. { exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWQ (quar_cells_nf_cf ly S Hp rd M) XQ). }
apply Forall_app; split.
{ apply Forall_app; split; [exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWFH (fs_hdr_nf_cf ly S Hp rd M) XFH) | exact HH]. }
apply Forall_app; split. { exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWD (depot_cells_nf_cf ly S Hp rd M) XD). }
apply Forall_app; split. { exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWI (ialloc_cells_nf_cf ly S Hp rd M) XI). }
exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN OWT (thread_cells_nf_cf ly S Hp rd M) XT).
Qed.
Lemma zshadow_range_facts_cf : forall ly S Hp rd r, ARmcf B ly S Hp rd -> In r (zero_shadow_ranges B ly) ->
fst r mod 8 = 0 /\ 0 <= fst r /\ 0 <= snd r /\ fst r + snd r <= kHighMemEnd /\ zdisjoint r (ly_F ly, kFakeStackSize).
Proof.
intros ly S Hp rd [lo len] M Hin. cbn [fst snd]. pose proof (amc_layout _ _ _ _ _ M) as LO.
unfold zero_shadow_ranges in Hin. destruct Hin as [E|Hin].
- injection E as <- <-. pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). unfold page_aligned in T5.
splits.
+ apply Z.mod_divide; [lia|]. apply Z.mod_divide in T5 as [q Hq]; [|lia]. exists (q * 512). lia.
+ unfold kHighMemBeg in T7. lia.
+ lia.
+ lia.
+ apply zdisjoint_sym. eapply (pairwise_In zdisjoint (static_extents ly) _ _ (owned_extents ly) [_; _]); [unfold static_extents; reflexivity | exact (lo_disj _ LO) | unfold owned_extents; cbn; tauto | left; reflexivity].
- pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (amc_syms _ _ _ _ _ M)) _ Hin) as (Z1 & Z2 & Z3 & Z4 & Z5). cbn [fst snd] in *.
pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ M) (lo, len) ltac:(apply in_app_iff; right; exact Hin)) as [R1 R2]. cbn [fst snd] in R1, R2.
pose proof (hull_below_F ly LO) as HF.
splits; [exact Z3 | exact Z1 | exact Z2 | unfold kLowMemEnd, kHighMemEnd in *; lia |]. unfold zdisjoint. cbn [fst snd]. left. lia.
Qed.
Lemma zshadow_low_cf : forall ly S Hp rd r i, ARmcf B ly S Hp rd -> In r (zero_shadow_ranges B ly) -> 0 <= i < snd r / 8 ->
SHADOW_OFF <= shadow_addr (fst r) + i < kHighMemBeg.
Proof.
intros ly S Hp rd r i M Hr Hi. destruct (zshadow_range_facts_cf ly S Hp rd r M Hr) as (A1 & A2 & A3 & A4 & A5).
assert (DM : snd r / 8 <= (snd r + 7) / 8) by (apply Z.div_le_mono; lia).
pose proof (shadow_range_below (fst r) (snd r) A2 A3 A4). pose proof (proj1 (shadow_addr_bounds (fst r) A2)). lia.
Qed.
Lemma zshadow_not_frame_shadow_cf : forall ly S Hp rd r i cid pos, ARmcf B ly S Hp rd -> In r (zero_shadow_ranges B ly) -> 0 <= i < snd r / 8 ->
0 <= cid <= 10 -> 0 <= pos < fs_frames cid ->
~ in_zr (shadow_addr (fst r) + i) (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8).
Proof.
intros ly S Hp rd r i cid pos M Hr Hi Hc HpQ IN. unfold in_zr in IN. cbn [fst snd] in IN.
destruct (zshadow_range_facts_cf ly S Hp rd r M Hr) as (A1 & A2 & A3 & A4 & D). unfold zdisjoint in D. cbn [fst snd] in D.
pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (frame_off_bounds cid pos Hc HpQ) as (B1 & B2 & B3 & B4 & B5 & B6).
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
Lemma ashadow_app_cf : forall ly S Hp rd g v, ARmcf B ly S Hp rd -> ashadow B ly S g = Some v -> 4096 <= g /\ g + 7 <= kHighMemEnd.
Proof.
intros ly S Hp rd g v M H. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (lo_high _ LO) as [P1 P2].
unfold ashadow in H. destruct (find_chunk_at B ly (st_chunks S) g) as [k|] eqn:F.
- apply find_chunk_at_In in F as [Hk Hg]. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & _).
assert (ck_extent k mod 8 = 0 /\ ck_base B ly k mod 8 = 0) as [E1 E2].
{ pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (_ & _ & G3 & _ & _ & _ & G7 & _ & GG). split; [|apply Z.mod_divide in G3 as [q Hq]; [|lia]; rewrite Hq; replace (q * 16) with ((q * 2) * 8) by lia; apply Z_mod_mult].
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
pose proof (wfc_classes _ _ _ _ _ (amc_wf _ _ _ _ _ M) c ltac:(lia)) as CL.
pose proof (wrc_alloc _ _ _ _ _ _ CL) as A1. pose proof (wrc_fa _ _ _ _ _ _ CL) as [A2 _]. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as A3. pose proof (wrc_mapped_al _ _ _ _ _ _ CL) as A4.
pose proof (mapped_bound_cf (as_universe B) 0 0 0 S c (amc_wf _ _ _ _ _ M) ltac:(lia)) as MB. unfold kUserMapSize, kFreeArrayMax in *.
unfold fa_base, kFreeArrayOffset in Hin, MB. unfold region_base in *.
apply Z.mod_divide in R3 as [q3 Hq3]; [|lia]. apply Z.mod_divide in A4 as [q4 Hq4]; [|lia].
ceil; unfold ASAN_CEIL, kHighMemEnd, kHighMemBeg, kPrimResvSize in *.
destruct Hin as [E|[E|[]]]; injection E as <- <-; (split; [lia | nia]).
+ pose proof (proj1 (Forall_forall _ _) (proj1 (amc_placed _ _ _ _ _ M)) _ Hin) as (PA & [I1 I2] & I3). cbn [fst snd] in PA, I1, I2, I3.
ceil; unfold YG0f.page_aligned, ASAN_CEIL, kHighMemEnd, kHighMemBeg, kLowShadowBeg in *.
apply Z.mod_divide in PA as [q Hq]; [|lia]. split; [lia | clear - Hg Hq I2 I3 CR0; nia].
Qed.
Lemma ashadow_low_cf : forall ly S Hp rd g v, ARmcf B ly S Hp rd -> ashadow B ly S g = Some v -> SHADOW_OFF <= shadow_addr g < kHighMemBeg.
Proof.
intros ly S Hp rd g v M H. destruct (ashadow_app_cf ly S Hp rd g v M H) as [Ga Gb].
destruct (shadow_addr_bounds g ltac:(lia)) as [X Y]. split; [exact X | exact (Y Gb)].
Qed.
Theorem astack_free_law_ok_cf : astack_free_law_cf segs B.
Proof.
intros ly S Hp W mem md mem' md' cid pos (M & L & BUD & MW & HS) Hin HF0 AGR VIS Hvm Hlz He HK.
set (S' := stack_free_state cid pos S).
set (rd := aview segs (w_H W) mem) in *. set (rd' := aview segs (w_H W) mem') in *.
pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (wfc_fakestack _ _ _ _ _ WF) as [[LH FH] ND LV].
destruct (del_pos_spec _ _ _ ND Hin) as (l1 & l2 & EL & ED).
assert (FR' : frames S' = l1 ++ l2) by (unfold frames, S', stack_free_state; cbn; exact ED).
assert (FR : frames S = l1 ++ (cid, pos) :: l2) by exact EL.
pose proof (proj1 (Forall_forall _ _) LV (cid, pos) Hin) as [Hc HpQ]. cbn [fst snd] in Hc, HpQ.
pose proof (flag_off_bounds cid pos Hc HpQ) as FB.
assert (AG : forall a, aowned B ly S a -> a <> flag_addr ly cid pos -> rd' a = rd a).
{ intros a Ha Hne. apply AGR; [|exact Ha|exact Hne]. pose proof (AR_owned_low_law_ok_cf segs B ly S Hp W mem md a (conj M (conj L (conj BUD (conj MW HS)))) Ha).
ceil. unfold ASAN_CEIL in *. lia. }
assert (AGN : forall a, aowned B ly S a -> nf ly a -> rd' a = rd a).
{ intros a Ha Hn. apply AG; [exact Ha|]. intros ->. unfold nf, flag_addr in Hn. pose proof FB as FB2. unfold kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in Hn, FB2. lia. }
assert (Ecells : acells_cf B ly S' = acells_cf B ly S) by reflexivity.
assert (Ejunk : ajunk_cf B ly S' = ajunk_cf B ly S) by reflexivity.
assert (Eareas : aareas S' = aareas S) by reflexivity.
assert (CL : forall a, aclient_byte B ly S' a -> aclient_byte B ly S a).
{ intros a [X|(fp & Hcp & X)]; [left; exact X | right]. exists fp. split; [|exact X]. rewrite FR' in Hcp. rewrite FR.
apply in_app_iff in Hcp as [Hcp|Hcp]; apply in_app_iff; [left; exact Hcp | right; right; exact Hcp]. }
assert (L' : ALedger_cf segs ly S' md').
{ destruct L; constructor; unfold eager_cf in *; rewrite ?Hvm, ?Hlz, ?He; assumption. }
destruct (F_app ly LO) as (FH0 & FHZ & _).
assert (AGF : forall g, g mod 8 = 0 -> in_app g 8 -> hfree ly S g -> w_H W (w64 (shadow_addr g)) = false ->
rd' (shadow_addr g) = rd (shadow_addr g)).
{ intros g Hg HA HFg Hh. apply AG; [eapply hfree_shadow_owned_cf; [exact M | exact Hg | exact HA | exact HFg] |].
pose proof (shadow_addr_band_rw g HA) as SB. intros E. unfold flag_addr in E. clear - SB FH0 FHZ FB E.
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kFakeStackSize, kFakeFlagsOff, kFakeFramesOff in *. lia. }
split; [|split; [exact L' | split; [exact (abudget_ok_cf_frame segs ly S S' W eq_refl eq_refl eq_refl eq_refl BUD) |
split; [exact (amwf_same md md' Hvm Hlz MW) |
exact (ahs_transfer_cf segs B ly S Hp S' (w_H W) mem mem' (al_img_env_cf segs ly S md LO L) M HS VIS HK (fun a _ C => CL a C) eq_refl AGF)]]]].
pose proof M as M0. destruct M as [Xwf Xuni Xsyms Xlay Xplaced Xconst Xcowned Xcells Xfa Xflags Xdepot Xshadow Xzsh Xjunk Xareas Xclient Xzero Xtsd Ximg Xhp].
constructor; try assumption.
-   exact (proj1 (stack_free_ok_cf _ S cid pos Xwf Hin)).
-   exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN (const_cells_owned_cf B ly S Hp rd M0) (const_cells_nf_cf ly S Hp rd M0) Xconst).
-
unfold S', stack_free_state. apply (am_cells_set_fs_cf ly S Hp rd rd' _ M0 AGN). cbn [fs_hint].
pose proof Xcells as XC. unfold acells_cf in XC. rewrite (fs_cells_split S) in XC.
do 5 (apply Forall_app in XC as [_ XC]). apply Forall_app in XC as [XF _]. apply Forall_app in XF as [_ XH].
pose proof (acells_owned_cf B ly S Hp rd M0) as OW. unfold acells_cf in OW. rewrite (fs_cells_split S) in OW.
do 5 (apply Forall_app in OW as [_ OW]). apply Forall_app in OW as [OWF _]. apply Forall_app in OWF as [_ OWH].
apply Forall_forall. intros c Hcin. eapply cell_holds_agree; [exact (proj1 (Forall_forall _ _) XH c Hcin)|]. intros kk Hkk.
apply AG; [exact (proj1 (Forall_forall _ _) OWH c Hcin kk Hkk)|].
unfold fs_hints in Hcin. apply in_map_iff in Hcin as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih.
cbn [c_at c_w z8 c8 aeval aoff] in Hkk |- *. unfold flag_addr. pose proof FB as FB3. clear - Hkk Hih FB3. cbn [fst snd]. unfold kFakeFlagsOff in *. lia.
-
intros c i v Hc' Hi Hv k Hk. change (reg S' c) with (reg S c) in *.
pose proof (wfc_classes _ _ _ _ _ Xwf c Hc') as CLS. pose proof (wrc_fa_len _ _ _ _ _ _ CLS) as FL. pose proof (wrc_fa_bound _ _ _ _ _ _ CLS) as FB'.
rewrite AGN; [exact (Xfa c i v Hc' Hi Hv k Hk) | eapply own_fa_cf; [exact M0 | exact Hc' | lia] |].
apply (nf_prim ly _ Xlay). pose proof (region_in_prim ly c Xlay Hc') as (R1 & R2 & _). unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax, kPrimResvSize, kSpaceSize in *.
pose proof (lo_space_in _ Xlay) as [S1 S2]. rewrite region_off_eq in * by lia. unfold kPrimResvSize, kSpaceSize in *. nia.
-
intros c q Hc' Hq. destruct (Z.eq_dec (flag_addr ly c q) (flag_addr ly cid pos)) as [E|NE].
+ destruct (flag_addr_inj ly c q cid pos Hc' Hq Hc HpQ E) as [-> ->]. unfold rd' in HF0 |- *. rewrite HF0. f_equal.
rewrite FR'. assert (ND' : List.NoDup (l1 ++ (cid, pos) :: l2)) by (rewrite <- FR; exact ND).
destruct (mem_pos (l1 ++ l2) cid pos) eqn:MP; [|reflexivity]. exfalso.
apply mem_pos_spec in MP. exact (List.NoDup_remove_2 _ _ _ ND' MP).
+ rewrite AG; [| pose proof (flag_off_bounds c q Hc' Hq) as FB''; unfold flag_addr, kFakeFlagsOff in *; eapply own_F_low_cf; [exact M0 | lia] | exact NE].
rewrite (Xflags c q Hc' Hq). f_equal. rewrite FR', FR. rewrite !mem_pos_app. cbn [mem_pos].
destruct (Z.eqb_spec cid c) as [Ec|Ec]; destruct (Z.eqb_spec pos q) as [Eq|Eq]; cbn [andb orb];
[exfalso; apply NE; subst c q; reflexivity | | |]; destruct (mem_pos l1 c q), (mem_pos l2 c q); reflexivity.
-
destruct Xdepot as (heads & links & D1 & D2 & D3). exists heads, links. split; [|split; [|exact D3]].
+ intros b Hb. destruct (D1 b Hb) as [H1 H2]. split; [exact H1|]. intros k Hk. change (depot_traces ly S') with (depot_traces ly S) in *.
rewrite AGN; [exact (H2 k Hk) | eapply (own_area_cf B ly S Hp rd (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | cbn; tauto | cbn; unfold d_tab_words in Hb; lia] |].
eapply (nf_area_cf ly S Hp rd (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | cbn; tauto | cbn; unfold d_tab_words in Hb; lia].
+ intros id Hid. change (depot_ids S') with (depot_ids S) in Hid. destruct (D2 id Hid) as (H1 & H2 & H3). split; [exact H1|].
assert (NB : depot_ids S <= 4097).
{ pose proof (depot_len_bound _ _ Xuni (wfc_depot _ _ _ _ _ Xwf)) as DL. unfold depot_ids, DEPOT_MAX in *. lia. }
assert (OR : forall k, 0 <= k < 16 -> rd' (ly_NB ly + 16 * id + k) = rd (ly_NB ly + 16 * id + k)).
{ intros k Hk. apply AGN.
- eapply (own_core_cf B ly S Hp rd (ly_NB ly, kNodesBlockSize)); [exact M0 | unfold core_extents; cbn; tauto | cbn; unfold kNodesBlockSize; lia].
- eapply (nf_core_cf ly S Hp rd (ly_NB ly, kNodesBlockSize)); [exact M0 | unfold core_extents; cbn; tauto | cbn; unfold kNodesBlockSize; lia]. }
split; intros k Hk; [rewrite OR by lia; exact (H2 k Hk)|].
replace (ly_NB ly + 16 * id + 8 + Z.of_nat k) with (ly_NB ly + 16 * id + (8 + Z.of_nat k)) by lia. rewrite OR by lia.
replace (ly_NB ly + 16 * id + (8 + Z.of_nat k)) with (ly_NB ly + 16 * id + 8 + Z.of_nat k) by lia. exact (H3 k Hk).
-
intros g v Hg Hv0. change (ashadow B ly S' g) with (ashadow B ly S g) in Hv0.
rewrite AG; [exact (Xshadow g v Hg Hv0) | eapply ashadow_owned_cf; [exact M0 | exact Hv0] |].
pose proof (ashadow_low_cf ly S Hp rd g v M0 Hv0) as SL. unfold flag_addr. pose proof FB as FB4. clear - SL FH0 FHZ FB4.
unfold SHADOW_OFF, kHighMemBeg, kLowShadowBeg, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. lia.
-
unfold zshadow_ok in *. apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
pose proof (proj1 (Forall_forall _ _) Xzsh r Hr i Hi) as Z0. unfold shadow_of_addr in Z0. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)) in Z0.
rewrite AG; [exact Z0 | eapply own_shadow_zero_cf; [exact M0 | exact Hr | exact Hi] |].
pose proof (zshadow_low_cf ly S Hp rd r i M0 Hr Hi) as SL. unfold flag_addr. pose proof FB as FB4. clear - SL FH0 FHZ FB4.
unfold SHADOW_OFF, kHighMemBeg, kLowShadowBeg, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. lia.
- rewrite Ejunk. eapply Forall_range_vis_keep; [exact VIS | exact Xjunk].
- rewrite Eareas. eapply Forall_range_vis_keep; [exact VIS | exact Xareas].
-
eapply Forall_range_vis_keep; [exact VIS|]. apply Forall_forall. intros r Hr. apply (proj1 (Forall_forall _ _) Xclient).
unfold aclient in Hr |- *. change (st_chunks S') with (st_chunks S) in Hr. rewrite FR' in Hr. rewrite FR. rewrite !in_app_iff in Hr |- *. rewrite !in_map_iff in Hr |- *.
destruct Hr as [Hr|[(fp & E & Hcp)|(fp & E & Hcp)]]; [left; exact Hr | right; left | right; right]; exists fp; split; [exact E| |exact E|];
apply in_app_iff in Hcp as [Hcp|Hcp]; apply in_app_iff; [left; exact Hcp | right; right; exact Hcp | left; exact Hcp | right; right; exact Hcp].
-
apply Forall_forall. intros r Hr i Hi. pose proof (aso_ialloc _ Xsyms) as [I1 I2].
assert (RG : forall z, as_ialloc_lo B <= z < as_ialloc_hi B -> rd' z = rd z).
{ intros z Hz. apply AGN.
- eapply (own_area_cf B ly S Hp rd (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact M0 | cbn; tauto | cbn [fst snd]; lia].
- eapply (nf_area_cf ly S Hp rd (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact M0 | cbn; tauto | cbn [fst snd]; lia]. }
rewrite RG; [exact (proj1 (Forall_forall _ _) Xzero r Hr i Hi)|].
unfold ialloc_zero in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; lia.
- exact (proj1 (cells_move_fz_cf (nf ly) ly S S' Hp rd rd' M0 (fp_zones_nf_cf ly S Hp rd M0)
    (fun c => eq_refl) eq_refl eq_refl eq_refl eq_refl AGN VIS)).
- exact (proj2 (cells_move_fz_cf (nf ly) ly S S' Hp rd rd' M0 (fp_zones_nf_cf ly S Hp rd M0)
    (fun c => eq_refl) eq_refl eq_refl eq_refl eq_refl AGN VIS)).
- exact (pf_cells_move_fz_cf (nf ly) ly S Hp rd rd' M0 (fp_zones_nf_cf ly S Hp rd M0) AGN).
Qed.
Lemma ashadow_app_zone_cf : forall ly S Hp rd g v, ARmcf B ly S Hp rd -> ashadow B ly S g = Some v ->
(ly_prim ly <= g < ly_prim ly + kPrimResvSize) \/ (exists m len, In (m, len) (sec_extents ly S) /\ m <= g < m + len).
Proof.
intros ly S Hp rd g v M H. unfold ashadow in H.
destruct (find_chunk_at B ly (st_chunks S) g) as [k|] eqn:F.
- apply find_chunk_at_In in F as [Hk Hg].
destruct (extent_zone_cf B ly S Hp rd k M Hk) as [[X1 X2]|(m & len & Hin & X1 & X2)].
+ left. lia.
+ right. exists m, len. split; [exact Hin|]. unfold kPage in *. lia.
- destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:R; [|discriminate].
apply in_rangesb_true in R as (lo & len & Hin & Hg). unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
+ apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
pose proof (region_in_prim ly c (amc_layout _ _ _ _ _ M) ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wfc_classes _ _ _ _ _ (amc_wf _ _ _ _ _ M) c ltac:(lia)) as CL.
pose proof (wrc_alloc _ _ _ _ _ _ CL) as A1. pose proof (wrc_fa _ _ _ _ _ _ CL) as [A2 _]. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as A3.
pose proof (mapped_bound_cf (as_universe B) 0 0 0 S c (amc_wf _ _ _ _ _ M) ltac:(lia)) as MB. unfold kFreeArrayMax in *.
left. unfold fa_base, kFreeArrayOffset in Hin, MB. unfold region_base in *. unfold kPrimResvSize, kSpaceSize in *.
pose proof (lo_space_in _ (amc_layout _ _ _ _ _ M)) as [S1 S2]. rewrite region_off_eq in * by lia. unfold kPrimResvSize, kSpaceSize in *.
destruct Hin as [E|[E|[]]]; injection E as <- <-; nia.
+ right. exists lo, len. split; [exact Hin | exact Hg].
Qed.
Lemma ashadow_not_frame_shadow_cf : forall ly S Hp rd g v cid pos, ARmcf B ly S Hp rd -> ashadow B ly S g = Some v ->
0 <= cid <= 10 -> 0 <= pos < fs_frames cid ->
~ in_zr (shadow_addr g) (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8).
Proof.
intros ly S Hp rd g v cid pos M H Hc HpQ IN. unfold in_zr in IN. cbn [fst snd] in IN.
pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (frame_off_bounds cid pos Hc HpQ) as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (lo_F_al _ LO) as FAL. unfold page_aligned in FAL.
assert (GF : ~ (ly_F ly <= g < ly_F ly + kFakeStackSize)).
{ pose proof (lo_disj _ LO) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & _). do 2 (apply Forall_cons_iff in DP as [_ DP]). apply Forall_cons_iff in DP as [PF _]. unfold zdisjoint in PF. cbn [fst snd] in PF.
destruct (ashadow_app_zone_cf ly S Hp rd g v M H) as [X|(m & len & Hin & X)]; [lia|].
pose proof (pairwise_In zdisjoint _ (m, len) (ly_F ly, kFakeStackSize) (sec_extents ly S) (static_extents ly) eq_refl (proj2 (amc_placed _ _ _ _ _ M)) Hin
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia. }
unfold frame_addr, shadow_addr in *.
apply Z.mod_divide in FAL as [qf Hqf]; [|lia]. apply Z.mod_divide in B3 as [qo Hqo]; [|lia]. apply Z.mod_divide in B5 as [qb Hqb]; [|lia].
assert (E1 : (ly_F ly + fs_frame_off cid pos) / 8 = qf * 512 + qo * 8) by (rewrite Hqf, Hqo; symmetry; apply (Z.div_unique _ 8 _ 0); lia).
assert (E2 : fs_frame_bytes cid / 8 = qb * 8) by (rewrite Hqb; symmetry; apply (Z.div_unique _ 8 _ 0); lia).
rewrite E1, E2 in IN. pose proof (Z.div_mod g 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound g 8 ltac:(lia)) as MB.
set (g8 := g / 8) in *. set (gm := g mod 8) in *. clearbody g8 gm. clear - IN DM MB GF B1 B2 B6 Hqf Hqo Hqb B4 Hc. unfold kFakeFramesOff in *. lia.
Qed.
Theorem astack_malloc_law_ok_cf : astack_malloc_law_cf segs B.
Proof.
intros ly S Hp W mem md mem' md' cid pos hint' (M & L & BUD & MW & HS) Hc HP S' HW HF1 AGR VIS Hvm Hlz He HK.
set (rd := aview segs (w_H W) mem) in *. set (rd' := aview segs (w_H W) mem') in *.
pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (wfc_fakestack _ _ _ _ _ WF) as [[LH FH] ND LV].
pose proof (fs_frames_pos cid Hc) as HN.
destruct (fs_probe_some _ _ _ _ _ _ HN HP) as (h & Hh1 & Eh' & Epos & NM).
assert (HpQ : 0 <= pos < fs_frames cid) by (rewrite Epos; apply Z.mod_pos_bound; exact HN).
assert (NIN : ~ In (cid, pos) (frames S)) by (unfold frames; apply mem_pos_false; exact NM).
pose proof (flag_off_bounds cid pos Hc HpQ) as FB. pose proof (frame_off_bounds cid pos Hc HpQ) as (FO1 & FO2 & FO3 & FO4 & FO5 & FO6).
destruct (F_app ly LO) as (FH0 & FHZ & _). ceil.
assert (FR2 : ly_F ly + kFakeStackSize <= SHADOW_OFF \/ kHighMemBeg <= ly_F ly) by (clear - FHZ; unfold kLowShadowBeg, SHADOW_OFF in *; lia).
assert (F64 : ly_F ly + kFakeStackSize < 2 ^ 64) by (clear - FHZ CR; unfold kLowShadowBeg, ASAN_CEIL in *; lia).
assert (FR' : frames S' = (cid, pos) :: frames S) by reflexivity.
assert (FSL : shadow_addr (ly_F ly + fs_frame_off cid pos) + fs_frame_bytes cid / 8 <= kHighMemBeg).
{ apply shadow_range_below; [unfold kFakeFramesOff in FO1; lia | lia | clear - FHZ FO2 FO6 CR; unfold ASAN_CEIL, kHighMemEnd, kLowShadowBeg in *; lia]. }
pose proof (proj1 (shadow_addr_bounds (ly_F ly + fs_frame_off cid pos) ltac:(unfold kFakeFramesOff in FO1; lia))) as FSLO.
assert (AGN : forall a, aowned B ly S a -> nf ly a -> rd' a = rd a).
{ intros a Ha [Hn Hb]. apply AGR; [| exact Ha | | | |].
- pose proof (AR_owned_low_law_ok_cf segs B ly S Hp W mem md a (conj M (conj L (conj BUD (conj MW HS)))) Ha). ceil. unfold ASAN_CEIL in *. lia.
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
{ intros a [X|(fp & Hcp & X)]; [left; exact X | right]. exists fp. split; [rewrite FR'; right; exact Hcp | exact X]. }
assert (L' : ALedger_cf segs ly S' md').
{ destruct L; constructor; unfold eager_cf in *; rewrite ?Hvm, ?Hlz, ?He; assumption. }
assert (AGF : forall g, g mod 8 = 0 -> in_app g 8 -> hfree ly S g -> w_H W (w64 (shadow_addr g)) = false ->
rd' (shadow_addr g) = rd (shadow_addr g)).
{ intros g Hg HA HFg _. pose proof (shadow_addr_band_rw g HA) as SB. pose proof HA as [HA0 HAZ].
pose proof (shadow_addr_bounds g ltac:(lia)) as [SB1 SB2']. pose proof (SB2' ltac:(clear - HAZ CR; unfold ASAN_CEIL, kHighMemEnd, kLowShadowBeg in *; lia)) as SB2.
pose proof (proj1 (Forall_forall _ _) HFg (ly_F ly, kFakeStackSize)
ltac:(unfold hfree; rewrite !in_app_iff; left; unfold static_extents, owned_extents; rewrite in_app_iff; left; cbn; tauto)) as XF. cbn [fst snd] in XF.
apply AGR; [| eapply hfree_shadow_owned_cf; [exact M | exact Hg | exact HA | exact HFg] | | | |].
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
split; [|split; [exact L' | split; [exact (abudget_ok_cf_frame segs ly S S' W eq_refl eq_refl eq_refl eq_refl BUD) |
split; [exact (amwf_same md md' Hvm Hlz MW) |
exact (ahs_transfer_grow ly S S' (w_H W) mem mem' (al_img_env_cf segs ly S md LO L) HS VIS HK (fun a _ C => CL a C) eq_refl AGF)]]]].
pose proof M as M0. destruct M as [Xwf Xuni Xsyms Xlay Xplaced Xconst Xcowned Xcells Xfa Xflags Xdepot Xshadow Xzsh Xjunk Xareas Xclient Xzero Xtsd Ximg Xhp].
constructor; try assumption.
-   unfold S'. apply Wf_cf_push_frame; [exact Xwf | exact Hc | exact HpQ | | exact NIN].
rewrite Eh'. assert (Hh0 : 0 <= znth 0 cid (fs_hint (st_fs S))); [|lia].
unfold znth. destruct (nth_in_or_default (Z.to_nat cid) (fs_hint (st_fs S)) 0) as [Hin| ->]; [exact (proj1 (Forall_forall _ _) FH _ Hin) | lia].
-   exact (Forall_cell_holds_agree_nf ly S rd rd' _ AGN (const_cells_owned_cf B ly S Hp rd M0) (const_cells_nf_cf ly S Hp rd M0) Xconst).
-
unfold S'. apply (am_cells_set_fs_cf ly S Hp rd rd' _ M0 AGN). cbn [fs_hint].
pose proof Xcells as XC. unfold acells_cf in XC. rewrite (fs_cells_split S) in XC.
do 5 (apply Forall_app in XC as [_ XC]). apply Forall_app in XC as [XF _]. apply Forall_app in XF as [_ XH].
pose proof (acells_owned_cf B ly S Hp rd M0) as OW. unfold acells_cf in OW. rewrite (fs_cells_split S) in OW.
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
pose proof (wfc_classes _ _ _ _ _ Xwf c Hc') as CLS. pose proof (wrc_fa_len _ _ _ _ _ _ CLS) as FL. pose proof (wrc_fa_bound _ _ _ _ _ _ CLS) as FB'.
rewrite AGN; [exact (Xfa c i v Hc' Hi Hv k Hk) | eapply own_fa_cf; [exact M0 | exact Hc' | lia] |].
apply (nf_prim ly _ Xlay). pose proof (region_in_prim ly c Xlay Hc') as (R1 & R2 & _). unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax, kPrimResvSize, kSpaceSize in *.
pose proof (lo_space_in _ Xlay) as [S1 S2]. rewrite region_off_eq in * by lia. unfold kPrimResvSize, kSpaceSize in *. nia.
-
intros c q Hc' Hq. rewrite FR'. cbn [mem_pos].
destruct (Z.eq_dec (flag_addr ly c q) (flag_addr ly cid pos)) as [E|NE].
+ destruct (flag_addr_inj ly c q cid pos Hc' Hq Hc HpQ E) as [-> ->]. unfold rd' in HF1 |- *. rewrite HF1. rewrite !Z.eqb_refl. reflexivity.
+ pose proof (flag_off_bounds c q Hc' Hq) as FB''.
rewrite AGR; [| clear - FB'' FH0 F64; unfold flag_addr, kFakeStackSize, kFakeFramesOff, kFakeFlagsOff in *; lia
| eapply own_F_low_cf; [exact M0 | clear - FB''; unfold flag_addr, kFakeFlagsOff, kFakeFramesOff in *; lia]
| clear - FB'' Hc; unfold flag_addr; unfold kFakeFlagsOff in FB''; lia | exact NE
| clear - FO1 FB'' Hc; unfold in_zr, frame_addr, flag_addr; cbn [fst snd]; unfold kFakeFramesOff in FO1, FB''; lia
| clear - FR2 FSL FSLO FB''; unfold in_zr, frame_addr, flag_addr; cbn [fst snd]; unfold SHADOW_OFF, kHighMemBeg, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *; lia ].
rewrite (Xflags c q Hc' Hq). f_equal.
destruct (Z.eqb_spec cid c) as [Ec|Ec]; destruct (Z.eqb_spec pos q) as [Eq|Eq]; cbn [andb orb]; [exfalso; apply NE; subst c q; reflexivity | | |]; reflexivity.
-
destruct Xdepot as (heads & links & D1 & D2 & D3). exists heads, links. split; [|split; [|exact D3]].
+ intros b Hb. destruct (D1 b Hb) as [H1 H2]. split; [exact H1|]. intros k Hk. change (depot_traces ly S') with (depot_traces ly S) in *.
rewrite AGN; [exact (H2 k Hk) | eapply (own_area_cf B ly S Hp rd (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | cbn; tauto | cbn; unfold d_tab_words in Hb; lia] |].
eapply (nf_area_cf ly S Hp rd (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | cbn; tauto | cbn; unfold d_tab_words in Hb; lia].
+ intros id Hid. change (depot_ids S') with (depot_ids S) in Hid. destruct (D2 id Hid) as (H1 & H2 & H3). split; [exact H1|].
assert (NB : depot_ids S <= 4097).
{ pose proof (depot_len_bound _ _ Xuni (wfc_depot _ _ _ _ _ Xwf)) as DL. unfold depot_ids, DEPOT_MAX in *. lia. }
assert (OR : forall k, 0 <= k < 16 -> rd' (ly_NB ly + 16 * id + k) = rd (ly_NB ly + 16 * id + k)).
{ intros k Hk. apply AGN.
- eapply (own_core_cf B ly S Hp rd (ly_NB ly, kNodesBlockSize)); [exact M0 | unfold core_extents; cbn; tauto | cbn; unfold kNodesBlockSize; lia].
- eapply (nf_core_cf ly S Hp rd (ly_NB ly, kNodesBlockSize)); [exact M0 | unfold core_extents; cbn; tauto | cbn; unfold kNodesBlockSize; lia]. }
split; intros k Hk; [rewrite OR by lia; exact (H2 k Hk)|].
replace (ly_NB ly + 16 * id + 8 + Z.of_nat k) with (ly_NB ly + 16 * id + (8 + Z.of_nat k)) by lia. rewrite OR by lia.
replace (ly_NB ly + 16 * id + (8 + Z.of_nat k)) with (ly_NB ly + 16 * id + 8 + Z.of_nat k) by lia. exact (H3 k Hk).
-
intros g v Hg Hv0. change (ashadow B ly S' g) with (ashadow B ly S g) in Hv0.
pose proof (ashadow_low_cf ly S Hp rd g v M0 Hv0) as SL.
pose proof (proj1 (ashadow_app_cf ly S Hp rd g v M0 Hv0)) as G0.
rewrite AGR; [exact (Xshadow g v Hg Hv0) | | eapply ashadow_owned_cf; [exact M0 | exact Hv0] | | | | exact (ashadow_not_frame_shadow_cf ly S Hp rd g v cid pos M0 Hv0 Hc HpQ)].
+ clear - SL. unfold SHADOW_OFF, kHighMemBeg in *. lia.
+ clear - SL FR2 Hc. unfold SHADOW_OFF, kHighMemBeg, kFakeStackSize in *. lia.
+ clear - SL FR2 FB Hc. unfold flag_addr, SHADOW_OFF, kHighMemBeg, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. lia.
+ clear - SL FR2 FO1 FO2 FO6 Hc. unfold in_zr, frame_addr, SHADOW_OFF, kHighMemBeg, kFakeFramesOff, kFakeStackSize in *. cbn [fst snd]. lia.
-
unfold zshadow_ok in *. apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
pose proof (proj1 (Forall_forall _ _) Xzsh r Hr i Hi) as Z0. unfold shadow_of_addr in Z0. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)) in Z0.
pose proof (zshadow_low_cf ly S Hp rd r i M0 Hr Hi) as SL.
rewrite AGR; [exact Z0 | | eapply own_shadow_zero_cf; [exact M0 | exact Hr | exact Hi] | | | | exact (zshadow_not_frame_shadow_cf ly S Hp rd r i cid pos M0 Hr Hi Hc HpQ)].
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
- eapply (own_area_cf B ly S Hp rd (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact M0 | cbn; tauto | cbn [fst snd]; lia].
- eapply (nf_area_cf ly S Hp rd (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact M0 | cbn; tauto | cbn [fst snd]; lia]. }
rewrite RG; [exact (proj1 (Forall_forall _ _) Xzero r Hr i Hi)|].
unfold ialloc_zero in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; lia.
- exact (proj1 (cells_move_fz_cf (nf ly) ly S S' Hp rd rd' M0 (fp_zones_nf_cf ly S Hp rd M0)
    (fun c => eq_refl) eq_refl eq_refl eq_refl eq_refl AGN VIS)).
- exact (proj2 (cells_move_fz_cf (nf ly) ly S S' Hp rd rd' M0 (fp_zones_nf_cf ly S Hp rd M0)
    (fun c => eq_refl) eq_refl eq_refl eq_refl eq_refl AGN VIS)).
- exact (pf_cells_move_fz_cf (nf ly) ly S Hp rd rd' M0 (fp_zones_nf_cf ly S Hp rd M0) AGN).
Qed.
(* ---------------------------------------------------------------------------- *)
(* The heap-head frame law, YG0dcf.v's AR_head_frame_law_cf (the 15th field of     *)
(* AR_laws_cf). Its proof is cgif's AR_frame_law_ok (YG0q.v:757) with the owned     *)
(* bytes that change being the hidden-head shadow bytes of Hp ++ Hp'. Every such    *)
(* byte is the shadow byte of an 8-aligned granule inside a live chunk              *)
(* (hd_shadow_chunk_cf); no cell, fa entry, flag, depot word, zero-shadow byte,     *)
(* ialloc byte or free granule's shadow is one (the *_not_chunk_shadow_cf lemmas    *)
(* and fp_zones_ncs_cf, the footprint family above at P := ~ chunk_shadow_cf).      *)
Definition chunk_shadow_cf (ly : alayout) (S : astate) (a : Z) : Prop :=
exists g k, g mod 8 = 0 /\ a = shadow_addr g /\ In k (st_chunks S) /\ ck_base B ly k <= g < ck_base B ly k + ck_extent k.
Lemma shadow_addr_inj8_cf : forall g g', g mod 8 = 0 -> g' mod 8 = 0 -> shadow_addr g = shadow_addr g' -> g = g'.
Proof.
intros g g' Hg Hg' E. unfold shadow_addr in E. apply Z.mod_divide in Hg as [q Hq]; [|lia]. apply Z.mod_divide in Hg' as [q' Hq']; [|lia].
subst g g'. rewrite !Z.div_mul in E by lia. lia.
Qed.
Lemma hd_shadow_chunk_cf : forall ly S Hp rd L a, ARmcf B ly S Hp rd -> Forall (hp_live_cf B ly S) L -> hd_shadow L a -> chunk_shadow_cf ly S a.
Proof.
intros ly S Hp rd L a M HL (g & Hg & Hin & ->). unfold in_head in Hin. apply existsb_exists in Hin as (p & HpL & Hpg).
apply andb_prop in Hpg as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
destruct (proj1 (Forall_forall _ _) HL p HpL) as (k & Hk & Hst & Ep & Hn).
pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (_ & _ & _ & G4 & G5 & _ & _ & G8 & _).
exists g, k. split; [exact Hg|]. split; [reflexivity|]. split; [exact Hk|]. unfold ck_n in Hn. rewrite G4 in Ep. lia.
Qed.
Lemma app_not_chunk_shadow_cf : forall ly S Hp rd a, ARmcf B ly S Hp rd -> app_addr a -> ~ chunk_shadow_cf ly S a.
Proof.
intros ly S Hp rd a M HA (g & k & Hg & -> & Hk & Hgk).
pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & _).
pose proof (shadow_addr_in_band (ck_base B ly k) (ck_extent k) (g - ck_base B ly k) G1 ltac:(lia)) as SB.
replace (ck_base B ly k + (g - ck_base B ly k)) with g in SB by lia.
clear - HA SB. unfold app_addr, in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. lia.
Qed.
Lemma F_not_chunk_shadow_cf : forall ly S Hp rd a, ARmcf B ly S Hp rd -> ly_F ly <= a < ly_F ly + kFakeStackSize -> ~ chunk_shadow_cf ly S a.
Proof.
intros ly S Hp rd a M Ha. apply (app_not_chunk_shadow_cf ly S Hp rd a M).
destruct (F_app ly (amc_layout _ _ _ _ _ M)) as (F0 & FZ & _). unfold app_addr. lia.
Qed.
Lemma static_shadow_not_chunk_shadow_cf : forall ly S Hp rd r a, ARmcf B ly S Hp rd -> In r (as_owned_static B) ->
shadow_addr (fst r) <= a < shadow_addr (fst r) + (snd r + 7) / 8 -> ~ chunk_shadow_cf ly S a.
Proof.
intros ly S Hp rd r a M Hr Ha (g & k & Hg & -> & Hk & Hgk).
destruct (chunk_apart_cf B ly S Hp rd k g M Hk Hgk) as [NI _]. apply NI. clear NI.
pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (lo_img _ LO) as (I0 & I1 & I2 & I3).
pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hr)) as [R1 R2].
pose proof (proj1 (Forall_forall _ _) (aso_static _ (amc_syms _ _ _ _ _ M)) r Hr) as (T1 & T2 & T3).
unfold in_zr, shadow_addr in *. unfold page_aligned in I3. apply Z.mod_divide in I3 as [q Hq]; [|lia].
apply Z.mod_divide in Hg as [qg Hqg]; [|lia]. rewrite I0 in *. unfold kImgLo in *.
subst g. rewrite Z.div_mul in Ha by lia.
pose proof (Z_div_mod_eq_full (fst r) 8) as DM1. pose proof (Z.mod_pos_bound (fst r) 8 ltac:(lia)) as MB1.
pose proof (Z_div_mod_eq_full (snd r + 7) 8) as DM2. pose proof (Z.mod_pos_bound (snd r + 7) 8 ltac:(lia)) as MB2.
lia.
Qed.
Lemma zshadow_not_chunk_shadow_cf : forall ly S Hp rd r i, ARmcf B ly S Hp rd -> In r (zero_shadow_ranges B ly) -> 0 <= i < snd r / 8 ->
~ chunk_shadow_cf ly S (shadow_addr (fst r) + i).
Proof.
intros ly S Hp rd r i M Hr Hi (g & k & Hg & E & Hk & Hgk).
destruct (zshadow_range_facts_cf ly S Hp rd r M Hr) as (A1 & A2 & A3 & _ & _).
assert (EG : g = fst r + 8 * i).
{ unfold shadow_addr in E. apply Z.mod_divide in A1 as [q1 Hq1]; [|lia]. apply Z.mod_divide in Hg as [q2 Hq2]; [|lia].
rewrite Hq1, Hq2 in E. rewrite !Z.div_mul in E by lia. lia. }
assert (DL : 8 * (snd r / 8) <= snd r) by (apply Z.mul_div_le; lia).
destruct (chunk_apart_cf B ly S Hp rd k g M Hk Hgk) as [NI NS].
unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr].
- apply NS. cbn [fst snd] in *. lia.
- apply NI. pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ M) r ltac:(apply in_app_iff; right; exact Hr)) as [R1 R2].
unfold in_zr. lia.
Qed.
Lemma hfree_not_chunk_shadow_cf : forall ly S Hp rd g0, ARmcf B ly S Hp rd -> g0 mod 8 = 0 -> hfree ly S g0 -> ~ chunk_shadow_cf ly S (shadow_addr g0).
Proof.
intros ly S Hp rd g0 M Hg0 HF (g & k & Hg & E & Hk & Hgk).
pose proof (shadow_addr_inj8_cf g0 g Hg0 Hg E) as <-.
destruct (hfree_off_extent_cf B ly S Hp rd k g0 M Hk Hg0 HF); lia.
Qed.
Lemma fp_zones_ncs_cf : forall ly S Hp rd, ARmcf B ly S Hp rd -> fp_zones (fun a => ~ chunk_shadow_cf ly S a) ly S.
Proof.
intros ly S Hp rd M. pose proof (amc_layout _ _ _ _ _ M) as LO.
assert (OE : forall e a, In e (owned_extents ly) -> fst e <= a < fst e + snd e -> ~ chunk_shadow_cf ly S a).
{ intros e a He Ha. apply (app_not_chunk_shadow_cf ly S Hp rd a M).
exact (proj1 (owned_extents_bound ly a LO ltac:(apply Exists_exists; exists e; split; [exact He | exact Ha]))). }
constructor.
- intros a Ha. exact (OE (ly_prim ly, kPrimResvSize) a ltac:(unfold owned_extents; cbn; tauto) Ha).
- intros e a He Ha. apply (OE e a); [|exact Ha]. unfold core_extents in He. unfold owned_extents. cbn in He |- *. intuition.
- intros a Ha. apply (app_not_chunk_shadow_cf ly S Hp rd a M). pose proof (lo_img _ LO) as (I0 & I1 & I2 & I3).
unfold in_zr in Ha. unfold app_addr, kImgLo, kImgEnd, kLowShadowBeg in *. lia.
- intros e a He Ha. apply (app_not_chunk_shadow_cf ly S Hp rd a M).
exact (proj1 (owned_sec_bound_cf B ly S Hp rd a M ltac:(apply Exists_exists; exists e; split; [exact He | exact Ha]))).
- intros a Ha. apply (F_not_chunk_shadow_cf ly S Hp rd a M). unfold kFakeFlagsOff, kFakeStackSize in *. lia.
- intros r a Hr Ha. exact (static_shadow_not_chunk_shadow_cf ly S Hp rd r a M Hr Ha).
Qed.
Theorem AR_head_frame_law_ok_cf : AR_head_frame_law_cf segs B.
Proof.
intros ly S Hp Hp' W mem md mem' md' (M & L & BUD & MW & HS) HL' HV AGR VIS Hvm Hlz He HK.
set (rd := aview segs (w_H W) mem) in *. set (rd' := aview segs (w_H W) mem') in *.
assert (HLL : Forall (hp_live_cf B ly S) (Hp ++ Hp')) by (apply Forall_app; split; [exact (amc_hp_live _ _ _ _ _ M) | exact HL']).
assert (AG0 : forall a, aowned B ly S a -> ~ hd_shadow (Hp ++ Hp') a -> rd' a = rd a).
{ intros a Ha Hn. apply AGR; [| exact Ha | exact Hn].
pose proof (AR_owned_low_law_ok_cf segs B ly S Hp W mem md a (conj M (conj L (conj BUD (conj MW HS)))) Ha). ceil. unfold ASAN_CEIL in *. lia. }
assert (AGP : forall a, aowned B ly S a -> ~ chunk_shadow_cf ly S a -> rd' a = rd a).
{ intros a Ha Hn. apply AG0; [exact Ha|]. intros Hd. exact (Hn (hd_shadow_chunk_cf ly S Hp rd _ a M HLL Hd)). }
pose proof (fp_zones_ncs_cf ly S Hp rd M) as FZ.
split; [|split; [eapply ALedger_same_cf; eassumption | split; [exact BUD | split; [exact (amwf_same md md' Hvm Hlz MW) |
exact (ahs_transfer_cf segs B ly S Hp S (w_H W) mem mem' (al_img_env_cf segs ly S md (amc_layout _ _ _ _ _ M) L) M HS VIS HK ltac:(intros a _ C; exact C) eq_refl
ltac:(intros g Hg HA HF _; apply AGP; [eapply hfree_shadow_owned_cf; [exact M | exact Hg | exact HA | exact HF] | exact (hfree_not_chunk_shadow_cf ly S Hp rd g M Hg HF)]))]]]].
pose proof M as M0. destruct M as [Xwf Xuni Xsyms Xlay Xplaced Xconst Xcowned Xcells Xfa Xflags Xdepot Xshadow Xzsh Xjunk Xareas Xclient Xzero Xtsd Ximg Xhp].
(* the hp-live field is HL' (hp_live_cf is amc_hp_live's body), closed with the unchanged fields *)
constructor; try assumption; try exact HL'.
- exact (Forall_cell_holds_agree_in (fun a => ~ chunk_shadow_cf ly S a) ly S rd rd' _ AGP (const_cells_owned_cf B ly S Hp rd M0) (const_cells_in_cf (fun a => ~ chunk_shadow_cf ly S a) ly S Hp rd M0 FZ) Xconst).
- exact (Forall_cell_holds_agree_in (fun a => ~ chunk_shadow_cf ly S a) ly S rd rd' _ AGP (acells_owned_cf B ly S Hp rd M0)
(acells_in_cf (fun a => ~ chunk_shadow_cf ly S a) ly S Hp rd M0 FZ (fun a Ha => F_not_chunk_shadow_cf ly S Hp rd a M0 ltac:(unfold kFakeStackSize; lia))) Xcells).
-
intros c i v Hc' Hi Hv k Hk.
pose proof (wfc_classes _ _ _ _ _ Xwf c Hc') as CLS. pose proof (wrc_fa_len _ _ _ _ _ _ CLS) as FL. pose proof (wrc_fa_bound _ _ _ _ _ _ CLS) as FB'.
rewrite AGP; [exact (Xfa c i v Hc' Hi Hv k Hk) | eapply own_fa_cf; [exact M0 | exact Hc' | lia] |].
apply (fz_prim _ _ _ FZ). pose proof (region_in_prim ly c Xlay Hc') as (R1 & R2 & _). unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax, kPrimResvSize, kSpaceSize in *.
pose proof (lo_space_in _ Xlay) as [S1 S2]. rewrite region_off_eq in * by lia. unfold kPrimResvSize, kSpaceSize in *. nia.
-
intros cid pos Hc HpQ. pose proof (flag_off_bounds cid pos Hc HpQ) as FB.
rewrite AGP; [exact (Xflags cid pos Hc HpQ) | unfold flag_addr, kFakeFlagsOff in *; eapply own_F_low_cf; [exact M0 | lia] |].
apply (F_not_chunk_shadow_cf ly S Hp rd _ M0). unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. lia.
-
destruct Xdepot as (heads & links & D1 & D2 & D3). exists heads, links. split; [|split; [|exact D3]].
+ intros b Hb. destruct (D1 b Hb) as [H1 H2]. split; [exact H1|]. intros k Hk.
rewrite AGP; [exact (H2 k Hk) | eapply (own_area_cf B ly S Hp rd (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | cbn; tauto | cbn; unfold d_tab_words in Hb; lia] |].
eapply (area_in_cf (fun a => ~ chunk_shadow_cf ly S a) ly S Hp rd (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | exact FZ | cbn; tauto | cbn; unfold d_tab_words in Hb; lia].
+ intros id Hid. destruct (D2 id Hid) as (H1 & H2 & H3). split; [exact H1|].
assert (NB : depot_ids S <= 4097).
{ pose proof (depot_len_bound _ _ Xuni (wfc_depot _ _ _ _ _ Xwf)) as DL. unfold depot_ids, DEPOT_MAX in *. lia. }
assert (OR : forall k, 0 <= k < 16 -> rd' (ly_NB ly + 16 * id + k) = rd (ly_NB ly + 16 * id + k)).
{ intros k Hk. apply AGP.
- eapply (own_core_cf B ly S Hp rd (ly_NB ly, kNodesBlockSize)); [exact M0 | unfold core_extents; cbn; tauto | cbn; unfold kNodesBlockSize; lia].
- apply (fz_core _ _ _ FZ (ly_NB ly, kNodesBlockSize)); [unfold core_extents; cbn; tauto | cbn; unfold kNodesBlockSize; lia]. }
split; intros k Hk; [rewrite OR by lia; exact (H2 k Hk)|].
replace (ly_NB ly + 16 * id + 8 + Z.of_nat k) with (ly_NB ly + 16 * id + (8 + Z.of_nat k)) by lia. rewrite OR by lia.
replace (ly_NB ly + 16 * id + (8 + Z.of_nat k)) with (ly_NB ly + 16 * id + 8 + Z.of_nat k) by lia. exact (H3 k Hk).
-
intros g v Hg Hv0.
destruct (in_head Hp g || in_head Hp' g)%bool eqn:EH.
+ apply Bool.orb_true_iff in EH. exact (HV g v Hg Hv0 EH).
+ apply Bool.orb_false_iff in EH as [E1 E2]. rewrite E2. rewrite AG0.
* pose proof (Xshadow g v Hg Hv0) as X. rewrite E1 in X. exact X.
* eapply ashadow_owned_cf; [exact M0 | exact Hv0].
* intros (g' & Hg' & Hin & Eg). pose proof (shadow_addr_inj8_cf g g' Hg Hg' Eg) as <-.
unfold in_head in Hin, E1, E2. rewrite existsb_app, E1, E2 in Hin. cbn in Hin. discriminate.
-
unfold zshadow_ok in *. apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
pose proof (proj1 (Forall_forall _ _) Xzsh r Hr i Hi) as Z0. unfold shadow_of_addr in Z0. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)) in Z0.
rewrite AGP; [exact Z0 | eapply own_shadow_zero_cf; [exact M0 | exact Hr | exact Hi] | exact (zshadow_not_chunk_shadow_cf ly S Hp rd r i M0 Hr Hi)].
- eapply Forall_range_vis_keep; [exact VIS | exact Xjunk].
- eapply Forall_range_vis_keep; [exact VIS | exact Xareas].
- eapply Forall_range_vis_keep; [exact VIS | exact Xclient].
-
apply Forall_forall. intros r Hr i Hi. pose proof (aso_ialloc _ Xsyms) as [I1 I2].
assert (RG : forall z, as_ialloc_lo B <= z < as_ialloc_hi B -> rd' z = rd z).
{ intros z Hz. apply AGP.
- eapply (own_area_cf B ly S Hp rd (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact M0 | cbn; tauto | cbn [fst snd]; lia].
- eapply (area_in_cf (fun a => ~ chunk_shadow_cf ly S a) ly S Hp rd (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact M0 | exact FZ | cbn; tauto | cbn [fst snd]; lia]. }
rewrite RG; [exact (proj1 (Forall_forall _ _) Xzero r Hr i Hi)|].
unfold ialloc_zero in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; lia.
- exact (proj1 (cells_move_fz_cf (fun a => ~ chunk_shadow_cf ly S a) ly S S Hp rd rd' M0 FZ
    (fun c => eq_refl) eq_refl eq_refl eq_refl eq_refl AGP VIS)).
- exact (proj2 (cells_move_fz_cf (fun a => ~ chunk_shadow_cf ly S a) ly S S Hp rd rd' M0 FZ
    (fun c => eq_refl) eq_refl eq_refl eq_refl eq_refl AGP VIS)).
- exact (pf_cells_move_fz_cf (fun a => ~ chunk_shadow_cf ly S a) ly S Hp rd rd' M0 FZ AGP).
Qed.
End u.
End j.
