(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset.asan image A (pin d83eb25dbf0d, unstripped twin f0d2e8d40c7e). The allocator laws
   RTlaws (A/RGthinS.v) that the relocated thin realloc segments take, at the realloc record's relation
   ARX := ARXqA B Hp = YGcfInstBase.ARXq_cf B (fun i => i = as_inst B) at image A (every ghost set Hp, B with
   TfibSyms B; a Theorem Labs lane 2026-10-30 04:58Z: one call-site relation for malloc and realloc), for the owned set aowned B
   (rt_laws_aowned) and Allocate's owned set YGcfMallocCompose.AOXm_cf B (rt_laws_aoxm). The live-block facts come
   from the chunk of the block (YG0scf.v chunk_facts_cf, chunk_apart_cf, chunks_disjoint_cf), ARcf's block law
   (AR_blocks_law_ok_cf), the chunk header cells of acells_cf (WrapAKit.cf_cell_state) and the errbuf placement
   (YGcfXs.v block_not_xs_cf, cfx_pick); the stack facts from AR_stack_law_ok_cf and layout_ok; the REAL(memcpy) cells
   from Tfib_const (WrapAKit.cf_const_lookup); the write law from AR_frame_law_ok_cf (YG0qcf.v), with errno outside
   the owned set (Tfib_owned_static and the image window, WrapAKit.img_cover_of_ledger_cf). Nothing here is a
   function's proof (rule 24): the laws read the model state and memory only, and no machine code is walked. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf YG0qcf YG08cf YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YP03 YGcfMallocCompose YGcfInstBase YGcfXsMapped.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m AF0x WrapAKit RGthinK RGthinS.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require ADIfaceA AImgA.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.
Hypothesis TB : TfibSyms B.

Lemma rt_inst_eq : as_inst B = RT_INST.
Proof. rewrite (ts_inst _ TB). reflexivity. Qed.

(* The realloc walk's relation: the layer's call-site relation YGcfInstBase.ARXq_cf at image A (IM := AImg_A, so
   im_segs is tfibsegs) with the instance object of the symbol table. Its facts are read through YGcfInstBase's
   projections and built by ARXqA_intro (the one place that unfolds ARX_cf), so no other proof of A5 depends on the
   order of its conjuncts. *)
Definition ARXqA : YGcfMallocCompose.ARXh_t tfibsegs :=
  YGcfInstBase.ARXq_cf (IM := AImgA.AImg_A) B (fun i => i = as_inst B).

Lemma ARXqA_ARcf : forall Hp inst ly S W mem md, ARXqA Hp inst ly S W mem md -> ARcf tfibsegs B ly S Hp W mem md.
Proof. exact (YGcfInstBase.ARXq_cf_ARcf (IM := AImgA.AImg_A) B (fun i => i = as_inst B)). Qed.
Lemma ARXqA_inst : forall Hp inst ly S W mem md, ARXqA Hp inst ly S W mem md -> inst = as_inst B.
Proof. exact (YGcfInstBase.ARXq_cf_iok (IM := AImgA.AImg_A) B (fun i => i = as_inst B)). Qed.
Lemma ARXqA_xsm : forall Hp inst ly S W mem md, ARXqA Hp inst ly S W mem md -> xs_mapped_cf ly S md.
Proof. exact (YGcfInstBase.ARXq_cf_xsm (IM := AImgA.AImg_A) B (fun i => i = as_inst B)). Qed.
Lemma ARXqA_qtight : forall Hp inst ly S W mem md, ARXqA Hp inst ly S W mem md -> qtight S.
Proof. exact (YGcfInstBase.ARXq_cf_qtight (IM := AImgA.AImg_A) B (fun i => i = as_inst B)). Qed.
Lemma ARXqA_intro : forall Hp inst ly S W mem md, inst = as_inst B -> ARcf tfibsegs B ly S Hp W mem md ->
  xs_mapped_cf ly S md -> qtight S -> ARXqA Hp inst ly S W mem md.
Proof.
intros Hp inst ly S W mem md I A X Q. unfold ARXqA. apply (YGcfInstBase.ARXq_cf_intro (IM := AImgA.AImg_A)); [|exact Q].
unfold YGcfInstBase.ARX_cf. exact (conj I (conj A X)).
Qed.

Lemma nodup_map_eq {X Y : Type} (f : X -> Y) : forall (l : list X) x y,
List.NoDup (List.map f l) -> List.In x l -> List.In y l -> f x = f y -> x = y.
Proof.
intros l. induction l as [|h t IH]; intros x y ND Hx Hy E; [destruct Hx|].
cbn [List.map] in ND. apply List.NoDup_cons_iff in ND as [Hn ND].
destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
- reflexivity.
- exfalso. apply Hn. rewrite E. apply List.in_map. exact Hy.
- exfalso. apply Hn. rewrite <- E. apply List.in_map. exact Hx.
- exact (IH x y ND Hx Hy E).
Qed.

Lemma blocks_chunk : forall S p n, In (p, n) (blocks S) ->
exists k, In k (st_chunks S) /\ ck_state k = CAllocated /\ ck_user k = p /\ ck_req k = n.
Proof.
intros S p n H. unfold blocks in H. apply in_map_iff in H as (k & E & Hk). apply List.filter_In in Hk as [Hk Ha].
injection E as E1 E2. exists k. split; [exact Hk|]. split; [|split; assumption].
unfold is_alloc in Ha. destruct (ck_state k); cbn in Ha; first [reflexivity | discriminate Ha].
Qed.

Lemma aeval_sptr_off : forall ly p d, aeval B ly (aoff (sptr_exp p) d) = sptr_addr B ly p + d.
Proof. intros ly p d. destruct p; unfold sptr_addr; cbn [sptr_exp aoff aeval]; lia. Qed.

Lemma aeval_sptr_off2 : forall ly p d d', aeval B ly (aoff (aoff (sptr_exp p) d) d') = sptr_addr B ly p + d + d'.
Proof. intros ly p d d'. destruct p; unfold sptr_addr; cbn [sptr_exp aoff aeval]; lia. Qed.

Lemma aview_mem_eq : forall (H : word -> bool) (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof. intros H m m' a E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.

Lemma aview_wrap : forall (H : word -> bool) (m : word -> option byte) a,
aview tfibsegs H m a = aview tfibsegs H m (a mod 2 ^ 64).
Proof.
intros H m a.
assert (E : Z_to_bv 64 a = Z_to_bv 64 (a mod 2 ^ 64)).
{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Zmod_mod. reflexivity. }
unfold aview, mbyte, mrestrict. rewrite E. reflexivity.
Qed.

Lemma errno_not_owned : forall ly S G rd a, ARmcf B ly S G rd -> img_cover ly -> RT_ERRNO <= a < RT_ERRNO + 4 ->
~ aowned B ly S a.
Proof.
intros ly S G rd a M [I1 I2] Ha [OW _]. pose proof (amc_layout _ _ _ _ _ M) as LO.
unfold AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END, RT_ERRNO in *.
assert (AI : in_zr a (ly_img ly)) by (unfold in_zr; lia).
destruct OW as [O|[O|[O|[O|O]]]].
- rewrite (ts_owned _ TB) in O. apply Exists_exists in O as (r & Hr & Hz).
  assert (OWN : forallb (fun r : Z * Z => orb (fst r + snd r <=? 0x5dde4c) (0x5dde4c + 4 <=? fst r)) Tfib_owned_static = true)
    by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) OWN r Hr) as X. cbv beta in X.
  apply orb_prop in X as [X|X]; apply Z.leb_le in X; unfold in_zr in Hz; lia.
- exact (proj2 (proj2 (owned_extents_bound ly a LO O)) AI).
- exact (proj2 (proj2 (owned_extents_bound ly a LO ltac:(apply Exists_exists; exists (ly_C ly, 256); split;
    [unfold owned_extents; cbn; tauto | exact O]))) AI).
- exact (proj2 (proj2 (owned_sec_bound_cf B ly S G rd a M O)) AI).
- pose proof (owned_shadow_bound_cf B ly S G rd a M O). unfold SHADOW_OFF in *. lia.
Qed.

Lemma RTlaws_sub : forall ARX AOX AOX', RTlaws B ARX AOX -> (forall ly S a, AOX' ly S a -> AOX ly S a) -> RTlaws B ARX AOX'.
Proof.
intros ARX AOX AOX' L Hs. destruct L as [L1 L2 L3 L4 L5 L6 L7].
constructor; [| exact L2 | exact L3 | | exact L5 | exact L6 | exact L7].
- intros ly S W mem md p n H Hin. destruct (L1 ly S W mem md p n H Hin) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  refine (conj A1 (conj A2 (conj A3 (conj A4 (conj _ (conj A6 (conj A7 A8))))))).
  intros x Hx. destruct (A5 x Hx) as (P & NO & NE). refine (conj P (conj _ NE)). intros O. exact (NO (Hs _ _ _ O)).
- intros ly S W mem md a H Ha. destruct (L4 ly S W mem md a H Ha) as [NO C]. split; [|exact C].
  intros O. exact (NO (Hs _ _ _ O)).
Qed.

Section h.
Variable Hp : list Z.

Lemma rt_blk : forall ly S W mem md p n, ARXqA Hp RT_INST ly S W mem md -> In (p, n) (blocks S) ->
4096 + 16 <= sptr_addr B ly p /\ sptr_addr B ly p + req_size n <= ASAN_CEIL /\
(sptr_addr B ly p <= 0x10000 \/ 0x600000 + 16 <= sptr_addr B ly p) /\ 0 <= n < 2 ^ 30 /\
(forall x, sptr_addr B ly p <= x < sptr_addr B ly p + req_size n ->
  apresent (w_H W) mem x /\ ~ YGcfMallocCompose.AOXm_cf B ly S x /\ ~ (RT_ERRNO <= x < RT_ERRNO + 4)) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (sptr_addr B ly p - 16) 1 2 /\
val_mem tfibsegs (mrestrict (w_H W) mem) (sptr_addr B ly p - 14) 2 0 /\
val_mem tfibsegs (mrestrict (w_H W) mem) (sptr_addr B ly p - 12) 4 (req_size n).
Proof.
intros ly S W mem md p n HX Hin.
pose proof (ARXqA_ARcf _ _ _ _ _ _ _ HX) as AR. assert (XS : xs_placed_cf ly S) by (eapply xs_placed_of_ARcf; exact AR). pose proof AR as (M & L & _).
pose proof (img_cover_of_ledger_cf ly S md L) as [I1 I2].
assert (Hab : In (sptr_addr B ly p, n) (ablocks B ly S))
  by (unfold ablocks; apply in_map_iff; exists (p, n); split; [reflexivity | exact Hin]).
pose proof (AR_blocks_law_ok_cf tfibsegs B ly S Hp W mem md _ n AR Hab) as (_ & _ & _ & _ & PP & _ & _).
destruct (blocks_chunk S p n Hin) as (k & Hk & Hst & Hu & Hr). subst p n.
pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
pose proof cf_malloc_max_bound as CM.
assert (APART : forall a, ck_base B ly k <= a < ck_base B ly k + ck_extent k -> ~ in_zr a (ly_img ly))
  by (intros a Ha; exact (proj1 (chunk_apart_cf B ly S Hp _ k a M Hk Ha))).
unfold in_zr in APART. unfold in_app in G1. unfold AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END, RT_ERRNO in *.
rewrite G4 in PP, Hab |- *.
split; [lia|]. split; [lia|].
split.
{ assert (D : ck_base B ly k + ck_extent k <= 0x10000 \/ (ck_base B ly k < 0x10000 /\ 0x10000 < ck_base B ly k + ck_extent k) \/
    (0x10000 <= ck_base B ly k < 0x600000) \/ 0x600000 <= ck_base B ly k) by lia.
  destruct D as [D|[D|[D|D]]].
  - left. lia.
  - exfalso. apply (APART 0x10000); lia.
  - exfalso. apply (APART (ck_base B ly k)); lia.
  - right. lia. }
split; [lia|].
split.
{ intros x Hx. destruct (PP x Hx) as [P NO]. split; [exact P|]. split.
  - intros [O|O]; [exact (NO O)|]. exact (block_not_xs_cf tfibsegs B ly S Hp W mem md _ _ x AR XS Hab Hx O).
  - intros E. apply (APART x); lia. }
assert (HIN : forall c, In c (chunk_cells k) -> In c (acells_cf B ly S)).
{ intros c Hc. unfold acells_cf. rewrite !in_app_iff. right. right. left. apply in_flat_map. exists k. split; [exact Hk | exact Hc]. }
set (h := aoff (sptr_exp (ck_beg k)) (ck_rz k - kChunkHeaderSize)).
pose proof (cf_cell_state B ly S Hp (w_H W) mem M (z1 h (hdr_state k)) h 1%nat (ANum (hdr_state k))
  (HIN _ ltac:(unfold chunk_cells; apply in_app_iff; left; left; reflexivity)) eq_refl) as V0.
pose proof (cf_cell_state B ly S Hp (w_H W) mem M (z2 (aoff h 2) 0) (aoff h 2) 2%nat (ANum 0)
  (HIN _ ltac:(unfold chunk_cells; apply in_app_iff; left; do 2 right; left; reflexivity)) eq_refl) as V2.
pose proof (cf_cell_state B ly S Hp (w_H W) mem M (z4 (aoff h 4) (ck_n k)) (aoff h 4) 4%nat (ANum (ck_n k))
  (HIN _ ltac:(unfold chunk_cells; apply in_app_iff; left; do 3 right; left; reflexivity)) eq_refl) as V4.
subst h. rewrite aeval_sptr_off in V0. rewrite aeval_sptr_off2 in V2, V4. cbn [aeval] in V0, V2, V4.
unfold hdr_state in V0. rewrite Hst in V0. unfold ck_n in V4. fold (ck_base B ly k) in V0, V2, V4.
unfold kChunkHeaderSize in V0, V2, V4.
replace (ck_base B ly k + ck_rz k - 16) with (ck_base B ly k + (ck_rz k - 16)) by lia.
replace (ck_base B ly k + ck_rz k - 14) with (ck_base B ly k + (ck_rz k - 16) + 2) by lia.
replace (ck_base B ly k + ck_rz k - 12) with (ck_base B ly k + (ck_rz k - 16) + 4) by lia.
exact (conj V0 (conj V2 V4)).
Qed.

Lemma rt_disj : forall ly S W mem md p n q m, ARXqA Hp RT_INST ly S W mem md ->
In (p, n) (blocks S) -> In (q, m) (blocks S) -> p <> q ->
sptr_addr B ly p + req_size n <= sptr_addr B ly q \/ sptr_addr B ly q + req_size m <= sptr_addr B ly p.
Proof.
intros ly S W mem md p n q m HX Hpn Hqm Hne.
pose proof (ARXqA_ARcf _ _ _ _ _ _ _ HX) as (M & _). pose proof (amc_wf _ _ _ _ _ M) as WF.
destruct (blocks_chunk S p n Hpn) as (k1 & Hk1 & _ & Hu1 & Hr1).
destruct (blocks_chunk S q m Hqm) as (k2 & Hk2 & _ & Hu2 & Hr2). subst p n q m.
assert (Hb : ck_beg k1 <> ck_beg k2).
{ intros E. apply Hne. rewrite (nodup_map_eq ck_beg (st_chunks S) k1 k2 (wfc_chunks_nodup _ _ _ _ _ WF) Hk1 Hk2 E). reflexivity. }
pose proof (chunks_disjoint_cf B ly S Hp _ k1 k2 M Hk1 Hk2 Hb) as D.
pose proof (chunk_facts_cf B ly S Hp _ k1 M Hk1) as (_ & _ & _ & E4 & E5 & _ & E7 & E8 & _).
pose proof (chunk_facts_cf B ly S Hp _ k2 M Hk2) as (_ & _ & _ & F4 & F5 & _ & F7 & F8 & _).
pose proof (req_size_bounds (ck_req k1) ltac:(lia)) as (Q1 & Q2 & Q3).
pose proof (req_size_bounds (ck_req k2) ltac:(lia)) as (R1 & R2 & R3).
unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

Lemma rt_layout : forall ly S W mem md ly' p n, ARXqA Hp RT_INST ly S W mem md ->
layout_le (length (st_secs S)) ly ly' -> In (p, n) (blocks S) -> sptr_addr B ly' p = sptr_addr B ly p.
Proof.
intros ly S W mem md ly' p n HX LE Hin.
pose proof (ARXqA_ARcf _ _ _ _ _ _ _ HX) as (M & _). pose proof (amc_wf _ _ _ _ _ M) as WF.
destruct (blocks_chunk S p n Hin) as (k & Hk & _ & Hu & _). subst p.
apply (sptr_addr_le B ly ly' (length (st_secs S))); [exact LE|].
pose proof (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ WF) k Hk) as [_ C]. unfold ck_user.
destruct (ck_beg k) as [|o|r o|c q]; cbn; try exact I. destruct C as (_ & _ & sm & Hsm & _). eapply nth_error_lt. exact Hsm.
Qed.

Lemma rt_stack : forall ly S W mem md a, ARXqA Hp RT_INST ly S W mem md ->
ly_stk_lo ly <= a < ly_stk_hi ly -> ~ YGcfMallocCompose.AOXm_cf B ly S a /\ ASAN_CEIL <= a.
Proof.
intros ly S W mem md a HX Ha.
pose proof (ARXqA_ARcf _ _ _ _ _ _ _ HX) as AR. assert (XS : xs_placed_cf ly S) by (eapply xs_placed_of_ARcf; exact AR). pose proof AR as (M & _).
pose proof (lo_stk_ceil _ (amc_layout _ _ _ _ _ M)) as SC.
split; [|lia].
intros [O|O].
- exact (AR_stack_law_ok_cf tfibsegs B ly S Hp W mem md a AR Ha O).
- destruct (cfx_pick ly S a XS O) as (e & Hae & _ & _ & Hdis).
  apply (cfx_disj_out a e (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) Hae
    (Hdis _ ltac:(apply in_or_app; right; apply in_or_app; left; unfold static_extents; apply in_or_app; right; left; reflexivity))).
  unfold in_zr. cbn [fst snd]. lia.
Qed.

Lemma rt_stkhi : forall ly S W mem md, ARXqA Hp RT_INST ly S W mem md -> ly_stk_hi ly <= kHighMemEnd.
Proof.
intros ly S W mem md HX. pose proof (ARXqA_ARcf _ _ _ _ _ _ _ HX) as (M & _).
pose proof (lo_top _ (amc_layout _ _ _ _ _ M)) as (_ & _ & _ & T4 & _). exact T4.
Qed.

Lemma rt_const : forall ly S W mem md, ARXqA Hp RT_INST ly S W mem md ->
val_mem tfibsegs (mrestrict (w_H W) mem) RT_GOT_M 8 RT_REAL_M /\ val_mem tfibsegs (mrestrict (w_H W) mem) RT_REAL_M 8 RT_PCM.
Proof.
intros ly S W mem md HX. pose proof (ARXqA_ARcf _ _ _ _ _ _ _ HX) as (M & _). unfold RT_GOT_M, RT_REAL_M, RT_PCM.
split; apply (cf_const_lookup B TB ly S Hp (w_H W) mem M); vm_compute; reflexivity.
Qed.

Lemma rt_write : forall ly S W mem md mem' md', ARXqA Hp RT_INST ly S W mem md ->
(forall x : word, ~ (ly_stk_lo ly <= bv_unsigned x < ly_stk_hi ly) -> ~ (RT_ERRNO <= bv_unsigned x < RT_ERRNO + 4) ->
  ~ (exists p n, In (p, n) (blocks S) /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) -> mem' x = mem x) ->
(forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) mem a <> None -> aview tfibsegs (w_H W) mem' a <> None) ->
same_but_materialized md md' -> ARXqA Hp RT_INST ly S W mem' md'.
Proof.
intros ly S W mem md mem' md' HX FR VIS SBM.
pose proof (ARXqA_inst _ _ _ _ _ _ _ HX) as Hi. pose proof (ARXqA_xsm _ _ _ _ _ _ _ HX) as XM.
pose proof (ARXqA_qtight _ _ _ _ _ _ _ HX) as Q. pose proof (ARXqA_ARcf _ _ _ _ _ _ _ HX) as AR. pose proof AR as (M & L & _).
pose proof (img_cover_of_ledger_cf ly S md L) as IMG.
pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (lo_top _ LO) as (_ & _ & _ & _ & _ & _ & T7).
assert (BK : forall a, (exists p n, In (p, n) (blocks S) /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ->
  app_addr a /\ ~ aowned B ly S a).
{ intros a (p & n & Hin & Ha).
  assert (Hab : In (sptr_addr B ly p, n) (ablocks B ly S))
    by (unfold ablocks; apply in_map_iff; exists (p, n); split; [reflexivity | exact Hin]).
  destruct (AR_blocks_law_ok_cf tfibsegs B ly S Hp W mem md _ n AR Hab) as (_ & _ & _ & IA & PP & _ & _).
  split; [exact (in_app_addr _ _ a IA Ha) | exact (proj2 (PP a Ha))]. }
apply (ARXqA_intro _ _ _ _ _ _ _ Hi); [| exact (YGcfXsMapped.xs_mapped_cf_sbm _ _ _ _ XM SBM) | exact Q].
apply (AR_frame_law_ok_cf tfibsegs B ly S Hp W mem md mem' md' AR).
- intros a Ha O. apply aview_mem_eq. apply FR; rewrite YP03.unsigned_lit_small by lia.
  + intros Hs. exact (AR_stack_law_ok_cf tfibsegs B ly S Hp W mem md a AR Hs O).
  + intros He. exact (errno_not_owned ly S Hp _ a M IMG He O).
  + intros Hb. exact (proj2 (BK a Hb) O).
- intros a Hv. rewrite aview_wrap. rewrite aview_wrap in Hv. apply VIS; [apply Z.mod_pos_bound; lia | exact Hv].
- unfold same_but_materialized in SBM. rewrite SBM. reflexivity.
- unfold same_but_materialized in SBM. rewrite SBM. reflexivity.
- unfold same_but_materialized in SBM. rewrite SBM. reflexivity.
- intros a Hb _.
  assert (Ra : 0 <= a < 2 ^ 64) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hb; lia).
  apply FR; match goal with |- context [bv_unsigned ?w] =>
    replace (bv_unsigned w) with a by (symmetry; apply YP03.unsigned_lit_small; exact Ra) end.
  + intros Hs. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. lia.
  + intros He. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, RT_ERRNO in *. lia.
  + intros Hbk. destruct (BK a Hbk) as [AA _]. pose proof (proj1 ASAN_CEIL_range) as CR.
    unfold app_addr, in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. lia.
Qed.

End h.

Theorem rt_laws_aoxm : forall Hp, RTlaws B (fun inst ly S W mem md => ARXqA Hp inst ly S W mem md)
(YGcfMallocCompose.AOXm_cf B).
Proof.
intros Hp. constructor.
- exact (rt_blk Hp).
- exact (rt_disj Hp).
- exact (rt_layout Hp).
- exact (rt_stack Hp).
- exact (rt_stkhi Hp).
- exact (rt_const Hp).
- exact (rt_write Hp).
Qed.

Theorem rt_laws_aowned : forall Hp, RTlaws B (fun inst ly S W mem md => ARXqA Hp inst ly S W mem md)
(aowned B).
Proof.
intros Hp. apply (RTlaws_sub _ _ _ (rt_laws_aoxm Hp)). intros ly S a O. left. exact O.
Qed.

End a.
