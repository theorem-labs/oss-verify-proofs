(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/RepRelXcf.v (commit 4d286b2e618d, file sha256 508f820a5d90) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 6 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepRelXcf.v (commit f01d79f3fb5, cf refill round 3; file sha256 e6145c46443f) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 6 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 6 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair); no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a prior worker, the class-full report walk, slice F4 / RepF4Append.ErrbRelRebuild's
   open piece; field round 2 re-fit, RepLayerMerge): errb_ARmcf_move / errb_rel_post, the relation at the end of an
   errbuf step when the bytes that change include the error-message buffer's object [cf_errbuf_obj,
   cf_errbuf_obj + 56) (= [0xa5ae8, 0xa5b20)), which ARcf owns (Tfib_owned_static's (0xa5ad0, ...), YF0m.v:280)
   and, since field round 2 (dd8e46fd954), pins through ARmcf's amc_errb_cells at the state.  So the cells are given
   at the end state, and the state moves with the memory in one step (errb_frame).
   rule 24: proves no function (kind: invariant lemma, no machine code runs in this file; the lane's reuse search is
   `proof-index UnmapOrDie internal_memset internal_memcpy internal_strlen GetNamedMappingFd IncreaseTotalMmap`,
   2026-10-30T02:55Z, 0 released lemmas).
   The proof is YG0qcf.v:669 AR_frame_law_ok_cf with every value-read byte shown outside the object, by YG0tcf.v's
   footprint family (cell_bytes_in over an address predicate, YG0tcf.v:96-326) at PW := not in the object.
   YG0tcf's fp_zones cannot be used as it stands: its fz_img asks the predicate on the whole image, and the
   object is in the image.  So the family is re-proved here over [fpz], whose fields are the zones the cells
   live in (prim, core, secondary extents, the fake stack, and the five image areas inst / depot / store /
   ialloc / ialloc flag by their addresses, TfibSyms); the constant cells are checked directly (the absolute
   and shadow ones by one boolean over Tfib_const_abs ++ Tfib_const_shadow, the symbolic ones by their zones).
   Every lemma body below marked "YG0tcf" is YG0tcf.v's with fp_zones -> fpz and area_in_cf -> the fpz field. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09 YO0d YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0s YG0q YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG05cf YG0scf YG0qcf YG0tcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG06bcf YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import RepRelcf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Ltac ceil := let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold ASAN_CEIL in H2.
(* the address predicate: not a byte of the errbuf object *)
Definition PW (a : Z) : Prop := ~ (0xaaf68 <= a < 0xaaf68 + 56).
(* the constant cells at absolute addresses that avoid the object *)
Definition win_free (c : acell) : bool :=
match c_at c with ANum z => (z + Z.max 1 (Z.of_nat (c_w c)) <=? 0xaaf68) || (0xaaf68 + 56 <=? z) | _ => false end.
Lemma win_free_abs : forallb win_free (Tfib_const_abs ++ Tfib_const_shadow) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rx_in_split_pairwise : forall (l1 l2 : list (Z * Z)) e y,
pairwise zdisjoint (l1 ++ l2) -> In e l1 -> In y l2 -> zdisjoint e y.
Proof.
intros l1 l2 e y PW0 He Hy. induction l1 as [|z t IH]; [destruct He|]. cbn [app pairwise] in PW0. destruct PW0 as [F PW0].
destruct He as [<-|He]; [| exact (IH PW0 He)]. exact (proj1 (Forall_forall _ _) F y ltac:(apply in_app_iff; right; exact Hy)).
Qed.
Lemma shadow_PW : forall g, 0 <= g -> PW (shadow_addr g).
Proof. intros g Hg. unfold PW, shadow_addr, SHADOW_OFF. pose proof (Z.div_pos g 8 Hg ltac:(lia)). lia. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.

(* Field round 3 (amc_pf_cells): Printf's two writable image cells lie apart from the errbuf object, the bytes the
   Append walk writes: the third conjunct of the layer's unit row YG0ncf.pf_cells_apart_t (not an ARmcf field; at cgif
   YGcfImgcgif.pf_cells_apart_cgif). *)
Lemma pf_errb_apart : pf_cells_apart_t B ->
  forall a, (cf_toolname_cell <= a < cf_toolname_cell + 8 \/ cf_pfcb_cell <= a < cf_pfcb_cell + 8) ->
  ~ (cf_errbuf_obj <= a < cf_errbuf_obj + 56).
Proof. intros H a Ha. exact (proj2 (proj2 (H a Ha))). Qed.

Lemma win_free_ok : forall ly c, win_free c = true -> cell_bytes_in B PW ly c.
Proof.
intros ly c H k Hk. unfold win_free in H. destruct (c_at c) eqn:E; try discriminate.
cbn [aeval]. apply Bool.orb_prop in H as [H|H]; [apply Z.leb_le in H | apply Z.leb_le in H]; unfold PW; lia.
Qed.

(* off the image [kImgLo, kImgLo + snd (ly_img ly)) means off the object (img_cover) *)
Lemma off_img_PW : forall ly a, layout_ok ly -> img_cover ly -> ~ in_zr a (ly_img ly) -> PW a.
Proof.
intros ly a LO [_ IC] H. pose proof (lo_img ly LO) as (J0 & _). unfold in_zr in H. rewrite J0 in H, IC.
unfold PW, kImgLo, TFIB_IMG_END in *. lia.
Qed.
Lemma owned_PW : forall ly e a, layout_ok ly -> img_cover ly -> In e (owned_extents ly) -> fst e <= a < fst e + snd e -> PW a.
Proof.
intros ly e a LO IC He Ha. apply (off_img_PW ly a LO IC). intros Hi.
pose proof (lo_disj ly LO) as PD. unfold static_extents in PD.
pose proof (rx_in_split_pairwise (owned_extents ly) _ e (ly_img ly) PD He ltac:(right; left; reflexivity)) as D.
unfold zdisjoint, in_zr in *. lia.
Qed.

Record fpz (ly : alayout) (S : astate) : Prop := {
fzx_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> PW a;
fzx_core : forall e a, In e (core_extents ly) -> fst e <= a < fst e + snd e -> PW a;
fzx_sec : forall e a, In e (sec_extents ly S) -> fst e <= a < fst e + snd e -> PW a;
fzx_F : forall a, ly_F ly <= a < ly_F ly + kFakeStackSize -> PW a;
fzx_inst : forall a, as_inst B <= a < as_inst B + 3632 -> PW a;
fzx_depot : forall a, as_depot B <= a < as_depot B + (4 * 2 ^ 20 + 32) -> PW a;
fzx_store : forall a, as_store B <= a < as_store B + 32 -> PW a;
fzx_ial : forall a, as_ialloc_lo B <= a < as_ialloc_lo B + (as_ialloc_hi B - as_ialloc_lo B) -> PW a;
fzx_flag : forall a, as_ialloc_flag B <= a < as_ialloc_flag B + 2 -> PW a
}.

Lemma fpz_ok : forall ly S Hp rd, ARmcf B ly S Hp rd -> img_cover ly -> TfibSyms B -> fpz ly S.
Proof.
intros ly S Hp rd M IC TS. pose proof (amc_layout _ _ _ _ _ M) as LO. constructor.
- intros a Ha. exact (owned_PW ly (ly_prim ly, kPrimResvSize) a LO IC ltac:(unfold owned_extents; cbn; tauto) Ha).
- intros e a He Ha. apply (owned_PW ly e a LO IC); [|exact Ha]. unfold core_extents in He. unfold owned_extents. cbn in He |- *. intuition.
- intros e a He Ha. apply (off_img_PW ly a LO IC). intros Hi. destruct (amc_placed _ _ _ _ _ M) as [_ PD].
  pose proof (rx_in_split_pairwise (sec_extents ly S) (static_extents ly) e (ly_img ly) PD He
    ltac:(unfold static_extents; apply in_app_iff; right; right; left; reflexivity)) as D.
  unfold zdisjoint, in_zr in *. lia.
- intros a Ha. exact (owned_PW ly (ly_F ly, kFakeStackSize) a LO IC ltac:(unfold owned_extents; cbn; tauto) Ha).
- intros a Ha. rewrite (ts_inst _ TS) in Ha. unfold PW, TFIB_INST in *. lia.
- intros a Ha. rewrite (ts_depot _ TS) in Ha. unfold PW, TFIB_DEPOT in *. lia.
- intros a Ha. rewrite (ts_store _ TS) in Ha. unfold PW, TFIB_STORE in *. lia.
- intros a Ha. rewrite (ts_ial_lo _ TS), (ts_ial_hi _ TS) in Ha. unfold PW, TFIB_IAL_LO, TFIB_IAL_HI in *. lia.
- intros a Ha. rewrite (ts_ial_flag _ TS) in Ha. unfold PW, TFIB_IAL_FLAG in *. lia.
Qed.

(* YG0tcf.v:141 rinfo_in_cf *)
Lemma rx_rinfo : forall ly S Hp rd a, ARmcf B ly S Hp rd -> fpz ly S -> ly_space ly + kRegionInfoOff <= a < ly_space ly + kRegionInfoOff + 4096 -> PW a.
Proof.
intros ly S Hp rd a M FZ Ha. pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (lo_space_in _ LO) as [S1 S2]. unfold kRegionInfoOff, kSpaceSize in *.
apply (fzx_prim _ _ FZ). lia.
Qed.
(* YG0tcf.v:146 meta_in_cf *)
Lemma rx_meta : forall ly S Hp rd k a, ARmcf B ly S Hp rd -> fpz ly S -> In k (st_chunks S) ->
ck_base B ly k - (match ck_beg k with PSec _ _ => kPage | _ => 0 end) <= a < ck_base B ly k + ck_rz k -> PW a.
Proof.
intros ly S Hp rd k a M FZ Hk Ha. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal). unfold kFreeArrayOffset in Gal.
pose proof (region_in_prim ly (prim_class o) (amc_layout _ _ _ _ _ M) ltac:(lia)) as (R1 & R2 & _).
apply (fzx_prim _ _ FZ). lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
apply (fzx_sec _ _ FZ (ly_sec ly r, sec_map_size (ck_req k)) a Gin). cbn [fst snd]. unfold kPage in *. lia.
Qed.
(* YG0tcf.v:158 batch_in_cf *)
Lemma rx_batch : forall ly S Hp rd b a, ARmcf B ly S Hp rd -> fpz ly S -> In b (all_batches S) ->
ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> PW a.
Proof.
intros ly S Hp rd b a M FZ Hb Ha. pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (wfc_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; auto).
pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wrc_alloc _ _ _ _ _ _ CL) as AL. pose proof (mapped_bound_cf (as_universe B) 0 0 0 S kBatchClass WF ltac:(unfold kBatchClass; lia)) as MB.
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5).
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2.
unfold kBatchBytes, kFreeArrayOffset in *.
assert (BX : ly_space ly + b_self b = region_base ly kBatchClass + x) by (unfold region_base; subst x; lia).
apply (fzx_prim _ _ FZ). lia.
Qed.
Local Ltac fcons' := apply Forall_cons; [cbn; lia|].
(* YG0tcf.v:174 region_cells_in_cf *)
Lemma rx_region_cells : forall ly S Hp rd c, ARmcf B ly S Hp rd -> fpz ly S -> 1 <= c <= 31 -> Forall (cell_bytes_in B PW ly) (region_cells S c).
Proof.
intros ly S Hp rd c M FZ Hc. apply (Forall_cbi_of_range B PW ly _ (ly_space ly + kRegionInfoOff) 4096); [intros a Ha; eapply rx_rinfo; [exact M | exact FZ | exact Ha]|].
unfold region_cells, kRegionInfoOff. repeat fcons'. apply Forall_nil.
Qed.
(* YG0tcf.v:179 cache_cells_in_cf *)
Lemma rx_cache_cells : forall ly S Hp rd c, ARmcf B ly S Hp rd -> fpz ly S -> 1 <= c <= 31 -> Forall (cell_bytes_in B PW ly) (cache_cells S c).
Proof.
intros ly S Hp rd c M FZ Hc.
assert (OR : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> PW a).
{ intros a Ha. apply (fzx_core _ _ FZ (ly_T ly, kThreadObjSize)); [unfold core_extents; cbn; tauto | exact Ha]. }
apply (Forall_cbi_of_range B PW ly _ (ly_T ly) kThreadObjSize OR).
pose proof (wfc_classes _ _ _ _ _ (amc_wf _ _ _ _ _ M) c Hc) as CL. pose proof (wrc_cache _ _ _ _ _ _ CL) as WC. pose proof (class_ok c Hc) as (_ & _ & _ & K4 & _).
unfold cache_cells, t_cache, kThreadObjSize. destruct (st_cache_inited S).
- destruct WC as [PM PL]. repeat fcons'. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i v] & <- & Hiv). cbn [fst snd c_at c_w z4 c4 aeval aoff].
apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. lia.
- repeat fcons'. apply Forall_nil.
Qed.
(* YG0tcf.v:191 chunk_cells_in_cf *)
Lemma rx_chunk_cells : forall ly S Hp rd k, ARmcf B ly S Hp rd -> fpz ly S -> In k (st_chunks S) -> Forall (cell_bytes_in B PW ly) (chunk_cells k).
Proof.
intros ly S Hp rd k M FZ Hk. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
assert (OR : forall a, ck_base B ly k <= a < ck_base B ly k + ck_rz k -> PW a).
{ intros a Ha. eapply rx_meta; [exact M | exact FZ | exact Hk |]. destruct (ck_beg k); unfold kPage; lia. }
apply (Forall_cbi_of_range B PW ly _ _ _ OR).
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
(* YG0tcf.v:208 sec_cells_in_cf *)
Lemma rx_sec_cells : forall ly S Hp rd, ARmcf B ly S Hp rd -> fpz ly S -> Forall (cell_bytes_in B PW ly) (sec_cells S).
Proof.
intros ly S Hp rd M FZ. pose proof (wfc_secondary _ _ _ _ _ (amc_wf _ _ _ _ _ M)) as X. destruct X as [Snd Sac Sal Sres Sral].
assert (ORI : forall a, as_inst B <= a < as_inst B + 3632 -> PW a) by (intros a Ha; exact (fzx_inst _ _ FZ a Ha)).
unfold sec_cells.
apply Forall_cons; [eapply cbi_of_range; [exact ORI | cbn; unfold o_sec_reserved; lia | cbn; unfold o_sec_reserved; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORI | cbn; unfold o_sec_n; lia | cbn; unfold o_sec_n; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORI | cbn; unfold o_sec_mutex; lia | cbn; unfold o_sec_mutex; lia]|].
apply Forall_app. split.
- apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
eapply cbi_of_range; [intros a Ha; apply (fzx_core _ _ FZ (ly_Q ly, kPtrArrayResv)); [unfold core_extents; cbn; tauto | exact Ha] | cbn; lia |].
cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
- apply Forall_forall. intros c Hc. apply in_flat_map in Hc as (k & Hk & Hc).
pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg k) as [|o|r o|c' p] eqn:Eb; try solve [destruct Hc].
destruct GG as (-> & _ & Gbase & Gext & Gin & _).
assert (OR : forall a, ly_sec ly r <= a < ly_sec ly r + kPage -> PW a).
{ intros a Ha. eapply rx_meta; [exact M | exact FZ | exact Hk |]. rewrite Eb. unfold kPage in *. lia. }
unfold kPage in OR.
destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; (eapply cbi_of_range; [exact OR | cbn; lia | cbn; lia]).
Qed.
(* YG0tcf.v:229 batch_cells_in_cf *)
Lemma rx_batch_cells : forall ly S Hp rd l, ARmcf B ly S Hp rd -> fpz ly S -> incl l (all_batches S) -> Forall (cell_bytes_in B PW ly) (batch_cells l).
Proof.
intros ly S Hp rd l M FZ. induction l as [|b t IH]; intros Hincl; [apply Forall_nil|]. cbn [batch_cells].
pose proof (wq_batches _ (wfc_quarantine _ _ _ _ _ (amc_wf _ _ _ _ _ M))) as BL.
pose proof (proj1 (Forall_forall _ _) BL b (Hincl b (or_introl eq_refl))) as [L1 L2]. unfold kBatchSlots in L2.
assert (OR : forall a, ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> PW a)
by (intros a Ha; eapply rx_batch; [exact M | exact FZ | apply Hincl; left; reflexivity | exact Ha]).
unfold kBatchBytes in OR.
apply Forall_cons; [eapply cbi_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_app. split.
- apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i k] & <- & Hik). apply in_combine_l in Hik. apply in_seq in Hik.
eapply cbi_of_range; [exact OR | cbn; lia | cbn; lia].
- apply IH. intros x Hx. apply Hincl. right. exact Hx.
Qed.
(* YG0tcf.v:245 quar_cells_in_cf *)
Lemma rx_quar_cells : forall ly S Hp rd, ARmcf B ly S Hp rd -> fpz ly S -> Forall (cell_bytes_in B PW ly) (quar_cells S).
Proof.
intros ly S Hp rd M FZ.
assert (ORT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> PW a).
{ intros a Ha. apply (fzx_core _ _ FZ (ly_T ly, kThreadObjSize)); [unfold core_extents; cbn; tauto | exact Ha]. }
assert (ORI : forall a, as_inst B <= a < as_inst B + 3632 -> PW a) by (intros a Ha; exact (fzx_inst _ _ FZ a Ha)).
unfold kThreadObjSize in ORT.
unfold quar_cells, qc_cells, o_q_cmutex, o_q_rmutex, o_q_size, t_qc.
apply Forall_cons; [eapply cbi_of_range; [exact ORI | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORI | cbn; lia | cbn; lia]|].
apply Forall_app. split.
- do 4 (apply Forall_cons; [eapply cbi_of_range; [exact ORT | cbn; lia | cbn; lia]|]).
eapply rx_batch_cells; [exact M | exact FZ | intros b Hb; unfold all_batches; apply in_app_iff; left; exact Hb].
- do 4 (apply Forall_cons; [eapply cbi_of_range; [exact ORI | cbn; lia | cbn; lia]|]).
eapply rx_batch_cells; [exact M | exact FZ | intros b Hb; unfold all_batches; apply in_app_iff; right; exact Hb].
Qed.
(* YG0tcf.v:261 fs_hdr_in_cf *)
Lemma rx_fs_hdr : forall ly S, fpz ly S -> Forall (cell_bytes_in B PW ly) fs_hdr.
Proof.
intros ly S FZ. assert (OR : forall a, ly_F ly + 88 <= a < ly_F ly + 88 + (kFakeFlagsOff - 88) -> PW a)
by (intros a Ha; apply (fzx_F _ _ FZ); unfold kFakeFlagsOff, kFakeStackSize in *; lia).
unfold kFakeFlagsOff in OR. unfold fs_hdr.
apply Forall_cons; [eapply cbi_of_range; [exact OR | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact OR | cbn; lia | cbn; lia]|]. apply Forall_nil.
Qed.
(* YG0tcf.v:268 depot_cells_in_cf *)
Lemma rx_depot_cells : forall ly S, fpz ly S -> Forall (cell_bytes_in B PW ly) (depot_cells ly S).
Proof.
intros ly S FZ.
assert (ORD : forall a, as_depot B <= a < as_depot B + (4 * 2 ^ 20 + 32) -> PW a) by (intros a Ha; exact (fzx_depot _ _ FZ a Ha)).
assert (ORS : forall a, as_store B <= a < as_store B + 32 -> PW a) by (intros a Ha; exact (fzx_store _ _ FZ a Ha)).
unfold depot_cells, d_nuniq, d_map1, s_total, s_block0.
apply Forall_cons; [eapply cbi_of_range; [exact ORD | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORD | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORS | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORS | cbn; lia | cbn; lia]|]. apply Forall_nil.
Qed.
(* YG0tcf.v:279 ialloc_cells_in_cf *)
Lemma rx_ialloc_cells : forall ly S Hp rd, ARmcf B ly S Hp rd -> fpz ly S -> Forall (cell_bytes_in B PW ly) (ialloc_cells B S).
Proof.
intros ly S Hp rd M FZ. pose proof (aso_ialloc _ (amc_syms _ _ _ _ _ M)) as [I1 I2].
assert (ORA : forall a, as_ialloc_lo B <= a < as_ialloc_lo B + (as_ialloc_hi B - as_ialloc_lo B) -> PW a) by (intros a Ha; exact (fzx_ial _ _ FZ a Ha)).
assert (ORF : forall a, as_ialloc_flag B <= a < as_ialloc_flag B + 2 -> PW a) by (intros a Ha; exact (fzx_flag _ _ FZ a Ha)).
unfold ialloc_cells.
apply Forall_cons; [eapply cbi_of_range; [exact ORF | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORF | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORA | cbn; lia | cbn; lia]|].
apply Forall_cons; [eapply cbi_of_range; [exact ORA | cbn; lia | cbn; lia]|]. apply Forall_nil.
Qed.
(* YG0tcf.v:292 thread_cells_in_cf *)
Lemma rx_thread_cells : forall ly S, fpz ly S -> Forall (cell_bytes_in B PW ly) thread_cells.
Proof.
intros ly S FZ. unfold thread_cells, t_unwinding. apply Forall_cons; [|apply Forall_nil].
eapply cbi_of_range; [intros a Ha; apply (fzx_core _ _ FZ (ly_T ly, kThreadObjSize)); [unfold core_extents; cbn; tauto | exact Ha] | cbn; lia | cbn; unfold kThreadObjSize; lia].
Qed.
(* YG0tcf.v:306 acells_in_cf *)
Lemma rx_acells : forall ly S Hp rd, ARmcf B ly S Hp rd -> fpz ly S -> Forall (cell_bytes_in B PW ly) (acells_cf B ly S).
Proof.
intros ly S Hp rd M FZ. unfold acells_cf. rewrite (fs_cells_split S).
assert (HF : forall a, ly_F ly <= a < ly_F ly + 88 -> PW a) by (intros a Ha; apply (fzx_F _ _ FZ); unfold kFakeStackSize; lia).
assert (RCF : forall c, In c (zseq 1 31) -> Forall (cell_bytes_in B PW ly) (region_cells_cf S c)).
{ intros c Hc. apply Forall_forall. intros x Hx.
apply (proj1 (Forall_forall _ _) (rx_region_cells ly S Hp rd c M FZ ltac:(pose proof (zseq_In' 1 31 c Hc); lia))).
eapply region_cells_cf_incl. exact Hx. }
apply Forall_app; split; [exact (Forall_flat_map'' _ _ _ RCF)|].
apply Forall_app; split; [exact (Forall_flat_map'' _ _ _ (fun c Hc => rx_cache_cells ly S Hp rd c M FZ ltac:(pose proof (zseq_In' 1 31 c Hc); lia)))|].
apply Forall_app; split; [exact (Forall_flat_map'' _ _ _ (fun k Hk => rx_chunk_cells ly S Hp rd k M FZ Hk))|].
apply Forall_app; split; [exact (rx_sec_cells ly S Hp rd M FZ)|].
apply Forall_app; split; [exact (rx_quar_cells ly S Hp rd M FZ)|].
apply Forall_app; split.
{ apply Forall_app; split; [exact (rx_fs_hdr ly S FZ)|]. unfold fs_hints. apply Forall_forall. intros c Hc.
apply in_map_iff in Hc as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih.
eapply cbi_of_range; [exact (fun a Ha => HF a Ha) | cbn; lia | cbn [c_at c_w z8 c8 aeval aoff fst snd]; cbn; lia]. }
apply Forall_app; split; [exact (rx_depot_cells ly S FZ)|].
apply Forall_app; split; [exact (rx_ialloc_cells ly S Hp rd M FZ)|].
exact (rx_thread_cells ly S FZ).
Qed.
(* the constant cells: the symbolic ones by their zones, the absolute and shadow ones by win_free_abs *)
Lemma rx_const_cells : forall ly S Hp rd, ARmcf B ly S Hp rd -> fpz ly S -> TfibSyms B -> Forall (cell_bytes_in B PW ly) (as_const B ly).
Proof.
intros ly S Hp rd M FZ TS. rewrite (ts_const _ TS ly). unfold Tfib_const.
pose proof (amc_tsd _ _ _ _ _ M) as TSD. rewrite (ts_tsd _ TS) in TSD.
assert (ORT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> PW a)
by (intros a Ha; apply (fzx_core _ _ FZ (ly_T ly, kThreadObjSize)); [unfold core_extents; cbn; tauto | exact Ha]).
assert (ORC : forall a, ly_C ly <= a < ly_C ly + 256 -> PW a)
by (intros a Ha; apply (fzx_core _ _ FZ (ly_C ly, 256)); [unfold core_extents; cbn; tauto | exact Ha]).
assert (ORD : forall a, ly_D ly <= a < ly_D ly + 4096 -> PW a)
by (intros a Ha; apply (fzx_core _ _ FZ (ly_D ly, 4096)); [unfold core_extents; cbn; tauto | exact Ha]).
assert (ORI : forall a, as_inst B <= a < as_inst B + 3632 -> PW a) by (intros a Ha; exact (fzx_inst _ _ FZ a Ha)).
assert (ORP : forall a, as_tp B - 88 <= a < as_tp B - 88 + 104 -> PW a)
by (intros a Ha; rewrite (ts_tp _ TS) in Ha; unfold PW, TFIB_TP in *; lia).
assert (ORS : forall a, ly_tsd ly <= a < ly_tsd ly + 8 -> PW a) by (intros a Ha; rewrite TSD in Ha; unfold PW, TFIB_TSD in *; lia).
apply Forall_app. split.
- unfold Tfib_const_sym.
  repeat (apply Forall_cons;
    [ first [ (eapply (cbi_of_range B PW ly _ (ly_T ly) kThreadObjSize ORT); cbn; unfold kThreadObjSize; lia)
            | (eapply (cbi_of_range B PW ly _ (ly_C ly) 256 ORC); cbn; lia)
            | (eapply (cbi_of_range B PW ly _ (ly_D ly) 4096 ORD); cbn; lia)
            | (eapply (cbi_of_range B PW ly _ (as_inst B) 3632 ORI); cbn; unfold o_space, o_rinfo, o_sec_chunks; lia)
            | (eapply (cbi_of_range B PW ly _ (as_tp B - 88) 104 ORP); cbn; lia)
            | (eapply (cbi_of_range B PW ly _ (ly_tsd ly) 8 ORS); cbn; lia) ] |]).
  apply Forall_nil.
- apply Forall_forall. intros c Hc. apply win_free_ok. exact (proj1 (forallb_forall _ _) win_free_abs c Hc).
Qed.

(* ARmcf at the end of an errbuf step: the state moves by an st_secs-only step (errb_frame), the reader keeps every
   owned byte outside the errbuf object (PW) and every visible byte outside the old errbuf extent, and the object's
   cells are given at the new state (field round 2: ARmcf's amc_errb_cells pins them).  The other fields read no byte
   of the object (the PW footprint above) and no byte of an errbuf extent (rr_vis_zf / rr_zf_apart). *)
Lemma errb_ARmcf_move : forall ly S S1 Hp rd rd', TfibSyms B -> img_cover ly -> cf_errbuf_obj = 0xaaf68 -> pf_cells_apart_t B ->
  ARmcf B ly S Hp rd -> errb_frame S S1 -> Wf_cf (as_universe B) S1 -> xs_placed_cf ly S1 ->
  (forall a, aowned B ly S a -> PW a -> rd' a = rd a) ->
  (forall a, 0 <= a < 2 ^ 64 -> Forall (fun e => ~ in_zr a e) (xs_cf ly S) -> rd a <> None -> rd' a <> None) ->
  errb_cells_cf B ly S1 rd' -> ARmcf B ly S1 Hp rd'.
Proof.
intros ly S S1 Hp rd rd' TS IC EO PFA M EF W1 X1 AGP VIS CELLS.
pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (fpz_ok ly S Hp rd M IC TS) as FZ.
destruct (amc_cells_owned _ _ _ _ _ M) as [HX HO].
assert (VZ : forall l, incl l (ajunk_cf B ly S ++ aareas S ++ aclient S) -> Forall (range_vis B ly rd) l -> Forall (range_vis B ly rd') l).
{ intros l INC F. apply Forall_forall. intros r Hr i Hi.
  pose proof (rr_vis_zf B ly S Hp rd TS IC M r i (INC r Hr) Hi) as Z.
  apply VIS; [exact (rr_zf_range B ly S Hp rd _ M Z) | | exact (proj1 (Forall_forall _ _) F r Hr i Hi)].
  apply Forall_forall. intros e He Hin.
  destruct (proj1 (Forall_forall _ _) (amc_xs_placed _ _ _ _ _ M) e He) as (_ & OA & _ & OD).
  pose proof (proj1 (Forall_app _ _ _) OD) as [ODc ODr]. pose proof (proj1 (Forall_app _ _ _) ODr) as [ODs _].
  destruct e as [d oc]. exact (rr_zf_apart ly S d oc _ OA ODs ODc Z Hin). }
unfold errb_frame in EF.
pose proof M as M0.
destruct M as [Xwf Xuni Xsyms Xlay Xplaced Xconst Xcowned Xcells Xfa Xflags Xdepot Xshadow Xzsh Xjunk Xareas Xclient Xzero Xtsd Ximg Xhp Xxs Xexh Xerr Xown Xpf Xpfo].
constructor.
- exact W1.
- exact Xuni.
- exact Xsyms.
- exact Xlay.
- rewrite EF. exact Xplaced.
- exact (Forall_cell_holds_agree_in B PW ly S rd rd' _ AGP (const_cells_owned_cf B ly S Hp rd M0) (rx_const_cells ly S Hp rd M0 FZ TS) Xconst).
- exact Xcowned.
- rewrite EF. change (Forall (cell_holds B ly rd') (acells_cf B ly S)).
  exact (Forall_cell_holds_agree_in B PW ly S rd rd' _ AGP (acells_owned_cf B ly S Hp rd M0) (rx_acells ly S Hp rd M0 FZ) Xcells).
- rewrite EF. change (fa_entries_ok ly rd' S).
  intros c i v Hc' Hi Hv k Hk.
  pose proof (wfc_classes _ _ _ _ _ Xwf c Hc') as CLS. pose proof (wrc_fa_len _ _ _ _ _ _ CLS) as FL. pose proof (wrc_fa_bound _ _ _ _ _ _ CLS) as FB'.
  rewrite AGP; [exact (Xfa c i v Hc' Hi Hv k Hk) | eapply own_fa_cf; [exact M0 | exact Hc' | lia] |].
  apply (fzx_prim _ _ FZ). pose proof (region_in_prim ly c Xlay Hc') as (R1 & R2 & _). unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax, kPrimResvSize, kSpaceSize in *.
  pose proof (lo_space_in _ Xlay) as [SP1 SP2]. rewrite region_off_eq in * by lia. unfold kPrimResvSize, kSpaceSize in *. nia.
- rewrite EF. change (fs_flags_ok ly rd' S).
  intros cid pos Hc HpQ. pose proof (flag_off_bounds cid pos Hc HpQ) as FB.
  rewrite AGP; [exact (Xflags cid pos Hc HpQ) | unfold flag_addr, kFakeFlagsOff in *; eapply own_F_low_cf; [exact M0 | lia] |].
  apply (fzx_F _ _ FZ). unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. lia.
- rewrite EF. change (depot_ok B ly rd' S).
  destruct Xdepot as (heads & links & D1 & D2 & D3). exists heads, links. split; [|split; [|exact D3]].
  + intros b Hb. destruct (D1 b Hb) as [H1 H2]. split; [exact H1|]. intros k Hk.
    rewrite AGP; [exact (H2 k Hk) | eapply (own_area_cf B ly S Hp rd (as_depot B, 4 * 2 ^ 20 + 32)); [exact M0 | cbn; tauto | cbn; unfold d_tab_words in Hb; lia] |].
    apply (fzx_depot _ _ FZ). unfold d_tab_words in Hb. lia.
  + intros id Hid. destruct (D2 id Hid) as (H1 & H2 & H3). split; [exact H1|].
    assert (NB : depot_ids S <= 4097).
    { pose proof (depot_len_bound _ _ Xuni (wfc_depot _ _ _ _ _ Xwf)) as DL. unfold depot_ids, DEPOT_MAX in *. lia. }
    assert (OR : forall k, 0 <= k < 16 -> rd' (ly_NB ly + 16 * id + k) = rd (ly_NB ly + 16 * id + k)).
    { intros k Hk. apply AGP.
      - eapply (own_core_cf B ly S Hp rd (ly_NB ly, kNodesBlockSize)); [exact M0 | unfold core_extents; cbn; tauto | cbn; unfold kNodesBlockSize; lia].
      - apply (fzx_core _ _ FZ (ly_NB ly, kNodesBlockSize)); [unfold core_extents; cbn; tauto | cbn; unfold kNodesBlockSize; lia]. }
    split; intros k Hk; [rewrite OR by lia; exact (H2 k Hk)|].
    replace (ly_NB ly + 16 * id + 8 + Z.of_nat k) with (ly_NB ly + 16 * id + (8 + Z.of_nat k)) by lia. rewrite OR by lia.
    replace (ly_NB ly + 16 * id + (8 + Z.of_nat k)) with (ly_NB ly + 16 * id + 8 + Z.of_nat k) by lia. exact (H3 k Hk).
- rewrite EF. change (shadow_ok_cf B ly Hp rd' S).
  intros g v Hg Hv0. rewrite AGP; [exact (Xshadow g v Hg Hv0) | eapply ashadow_owned_cf; [exact M0 | exact Hv0] |].
  destruct (ashadow_app_cf B ly S Hp rd g v M0 Hv0) as [Ga _]. apply shadow_PW. lia.
- unfold zshadow_ok in *. apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
  pose proof (proj1 (Forall_forall _ _) Xzsh r Hr i Hi) as Z0. unfold shadow_of_addr in Z0. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)) in Z0.
  rewrite AGP; [exact Z0 | eapply own_shadow_zero_cf; [exact M0 | exact Hr | exact Hi] |].
  destruct (zshadow_low_cf B ly S Hp rd r i M0 Hr Hi) as [Z1 _]. unfold PW, SHADOW_OFF in *. lia.
- rewrite EF. change (Forall (range_vis B ly rd') (ajunk_cf B ly S)).
  apply VZ; [intros x Hx; apply in_app_iff; left; exact Hx | exact Xjunk].
- rewrite EF. change (Forall (range_vis B ly rd') (aareas S)).
  apply VZ; [intros x Hx; rewrite !in_app_iff; right; left; exact Hx | exact Xareas].
- rewrite EF. change (Forall (range_vis B ly rd') (aclient S)).
  apply VZ; [intros x Hx; rewrite !in_app_iff; right; right; exact Hx | exact Xclient].
- apply Forall_forall. intros r Hr i Hi. pose proof (aso_ialloc _ Xsyms) as [I1 I2].
  assert (RG : forall z, as_ialloc_lo B <= z < as_ialloc_hi B -> rd' z = rd z).
  { intros z Hz. apply AGP.
    - eapply (own_area_cf B ly S Hp rd (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact M0 | cbn; tauto | cbn [fst snd]; lia].
    - apply (fzx_ial _ _ FZ). lia. }
  rewrite RG; [exact (proj1 (Forall_forall _ _) Xzero r Hr i Hi)|].
  unfold ialloc_zero in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; lia.
- exact Xtsd.
- exact Ximg.
- rewrite EF. exact Xhp.
- exact X1.
- apply (exh_cell_move_cf B ly S S1 Hp rd rd' PW M0 HX); [intros c; rewrite EF; reflexivity | exact AGP | | exact Xexh].
  intros c Hc. destruct (exh_byte_where_cf B ly S Hp rd c M0 HX Hc) as [E1 _]. exact (rx_rinfo ly S Hp rd _ M0 FZ E1).
- exact CELLS.
- exact Xown.
- (* field round 3: Printf's two cells are owned (amc_pf_owned) and apart from the object (pf_cells_apart_t) *)
  apply (pf_cells_move_cf B ly S Hp rd rd' PW M0 Xpfo AGP); [|exact Xpf].
  intros a Ha. pose proof (pf_errb_apart PFA a Ha) as N. rewrite EO in N. exact N.
- exact Xpfo.
Qed.

(* ahs_pres across a memory change, with visibility kept on the shadow band only (YG0qcf.ahs_pres_transfer_cf asks it
   everywhere; its proof reads it on the band). *)
Lemma rx_ahs_pres_transfer : forall ly S Hp S' H mem mem',
  (forall sg, In sg tfibsegs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd) ->
  ARmcf B ly S Hp (aview tfibsegs H mem) -> ahs_pres B ly S H mem ->
  (forall a, in_band_rw a -> aview tfibsegs H mem a <> None -> aview tfibsegs H mem' a <> None) ->
  (forall a, in_band_rw a -> H (YG0d.w64 a) = true -> mem (YG0d.w64 a) <> None -> mem' (YG0d.w64 a) <> None) ->
  (forall a, in_band_rw a -> aclient_byte B ly S' a -> aclient_byte B ly S a) ->
  ahs_pres B ly S' H mem'.
Proof.
intros ly S Hp S' H mem mem' IMG M HA VIS HK CL a Ha NC HV.
destruct (H (YG0d.w64 a)) eqn:Hh.
- assert (NCS : ~ aclient_byte B ly S a).
  { intros C. apply (client_band_vis_cf B ly S Hp _ a M Ha C). apply aview_band_hidden; assumption. }
  exact (HK a Ha Hh (HA a Ha NCS (or_introl Hh))).
- destruct (aview tfibsegs H mem a) as [v|] eqn:AV.
  + apply (proj1 (aview_band tfibsegs H mem' a IMG Ha Hh)). apply VIS; [exact Ha|]. rewrite AV. discriminate.
  + assert (NCS : ~ aclient_byte B ly S a) by (intros C; exact (client_band_vis_cf B ly S Hp _ a M Ha C AV)).
    exfalso. apply (proj2 (aview_band tfibsegs H mem a IMG Ha Hh)); [|exact AV].
    apply (HA a Ha NCS). destruct HV as [Hv|Hv]; [exfalso; change (YG0n.w64 a) with (YG0d.w64 a) in Hv; rewrite Hv in Hh; discriminate | right; exact Hv].
Qed.

(* ARcf at the end of an errbuf step (field round 2), from the relation split at the step (RepRelcf.rr_split: ARmcf
   and ahs at the entry state S over the entry memory, the ledger / budget / model at the step's state S1) and the
   end memory: it keeps every owned byte outside the errbuf object, every visible byte outside the old errbuf extent
   and every hidden shadow byte, and holds the object's cells at S1. *)
Lemma errb_rel_post : forall Hp ly S S1 (W : world tfibsegs) mem md mem' md',
  TfibSyms B -> img_cover ly -> cf_errbuf_obj = 0xaaf68 -> pf_cells_apart_t B ->
  rr_split B ly S S1 Hp W mem md -> errb_frame S S1 -> Wf_cf (as_universe B) S1 -> xs_placed_cf ly S1 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> PW a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  (forall a, 0 <= a < 2 ^ 64 -> Forall (fun e => ~ in_zr a e) (xs_cf ly S) -> aview tfibsegs (w_H W) mem a <> None -> aview tfibsegs (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (YG0d.w64 a) = true -> mem' (YG0d.w64 a) = mem (YG0d.w64 a)) ->
  errb_cells_cf B ly S1 (aview tfibsegs (w_H W) mem') ->
  ARcf tfibsegs B ly S1 Hp W mem' md'.
Proof.
intros Hp ly S S1 W mem md mem' md' TS IC EO PFA (M & HS & L & BU & MW) EF W1 X1 AGR VIS Hvm Hlz He HK CELLS.
pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (al_img_env_cf tfibsegs ly S1 md LO L) as IMG.
assert (AGP : forall a, aowned B ly S a -> PW a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hw. apply AGR; [|exact Ha | exact Hw]. exact (rr_zf_range B ly S Hp _ a M (rr_zf_owned B ly S Hp _ a M Ha)). }
split; [exact (errb_ARmcf_move ly S S1 Hp _ _ TS IC EO PFA M EF W1 X1 AGP VIS CELLS)|].
split; [eapply ALedger_same_cf; eassumption|].
split; [exact BU|].
split; [exact (amwf_same md md' Hvm Hlz MW)|].
destruct HS as [HP HZ]. split.
- apply (rx_ahs_pres_transfer ly S Hp S1 (w_H W) mem mem' IMG M HP).
  + intros a Ha Hv. apply VIS; [ | | exact Hv].
    { unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha. lia. }
    apply Forall_forall. intros e He' Hin.
    destruct (proj1 (Forall_forall _ _) (amc_xs_placed _ _ _ _ _ M) e He') as (_ & OA & _ & _).
    destruct e as [d oc]. unfold in_zr, in_app in *. cbn [fst snd] in *. pose proof ASAN_CEIL_range as [CR _].
    unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *. lia.
  + intros a Ha Hh Hm. rewrite (HK a Ha Hh). exact Hm.
  + intros a Ha C. unfold errb_frame in EF. rewrite EF in C. exact C.
- apply (ahz_transfer tfibsegs ly S S1 (w_H W) mem mem' IMG HZ).
  + unfold errb_frame in EF. rewrite EF. reflexivity.
  + exact HK.
  + intros g Hg HA HF _. apply AGP; [eapply hfree_shadow_owned_cf; [exact M | exact Hg | exact HA | exact HF] | destruct HA as [HA _]; apply shadow_PW; lia].
Qed.
End a.
