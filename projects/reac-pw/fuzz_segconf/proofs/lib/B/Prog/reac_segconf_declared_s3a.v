(* Helpers of segment 3 of the image-B walk of reac_segconf_declared (reac_segconf_declared_s3.v): where the table and
   the count cell lie against the walk's own stack, frame and frame shadow (from the entry's declared_pre, carried to a
   cut state by the journal and dc_un), the premises of reac_declared_vlan_add at its call site 0x8a06c (add_pre,
   arodata_okP, the frame chain, the footprint inclusion), and the model steps of one pass that adds. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaDenot PaSB PaCall PaNoChain
PaLibG PaLibF PaCallRun SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
reac_declared_vlan_split_c reac_declared_vlan_add_c reac_segconf_declared_c reac_segconf_declared_d
reac_segconf_declared_lem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
(* ===================================== the model steps of one pass ===================================== *)
Lemma dcs3_res_split : forall c i ti added p v,
  (i < length (dc_segs c))%nat -> dc_loop c i ti added ->
  rs_ignore (nth i (dc_segs c) rseg_d) = false -> vlan_split (rs_name (nth i (dc_segs c) rseg_d)) = Some (p, v) ->
  dc_res c = if fst (vlan_add ti (x_max c) p v) <? 0 then (-1, snd (vlan_add ti (x_max c) p v))
    else r_decl_go (skipn (S i) (dc_segs c)) (snd (vlan_add ti (x_max c) p v)) (x_max c)
      (added + fst (vlan_add ti (x_max c) p v)).
Proof using.
intros c i ti added p v Hi [HL _] Hg Hs. unfold dc_res. rewrite <- HL. exact (dcl_go_split _ i ti (x_max c) added p v Hi Hg Hs).
Qed.
(* the table after this pass's add is no longer than the final table *)
Lemma dcs3_len_fin : forall c i ti added p v,
  (i < length (dc_segs c))%nat -> dc_loop c i ti added ->
  rs_ignore (nth i (dc_segs c) rseg_d) = false -> vlan_split (rs_name (nth i (dc_segs c) rseg_d)) = Some (p, v) ->
  Z.of_nat (length ti) <= x_max c ->
  (length (snd (vlan_add ti (x_max c) p v)) <= length (snd (dc_res c)))%nat.
Proof using.
intros c i ti added p v Hi HLp Hg Hs Hm. rewrite (dcs3_res_split c i ti added p v Hi HLp Hg Hs).
destruct (dcl_add_len ti (x_max c) p v Hm) as [L1 L2].
destruct (fst (vlan_add ti (x_max c) p v) <? 0); cbn [snd]; [lia|].
destruct (dcl_go_len (skipn (S i) (dc_segs c)) (snd (vlan_add ti (x_max c) p v)) (x_max c)
  (added + fst (vlan_add ti (x_max c) p v)) L2) as [G1 _]. exact G1.
Qed.
Lemma dcs3_loop_next : forall c i ti added p v,
  (i < length (dc_segs c))%nat -> dc_loop c i ti added ->
  rs_ignore (nth i (dc_segs c) rseg_d) = false -> vlan_split (rs_name (nth i (dc_segs c) rseg_d)) = Some (p, v) ->
  ~ fst (vlan_add ti (x_max c) p v) < 0 ->
  dc_loop c (S i) (snd (vlan_add ti (x_max c) p v)) (added + fst (vlan_add ti (x_max c) p v)).
Proof using.
intros c i ti added p v Hi HLp Hg Hs Hn. pose proof HLp as [HL Ha].
pose proof (dcs3_res_split c i ti added p v Hi HLp Hg Hs) as E.
pose proof (dcl_add_rv_nonneg ti (x_max c) p v Hn) as R.
replace (fst (vlan_add ti (x_max c) p v) <? 0) with false in E by (symmetry; apply Z.ltb_ge; lia).
split; [exact (eq_sym E)|]. lia.
Qed.
Lemma dcs3_res_neg : forall c i ti added p v,
  (i < length (dc_segs c))%nat -> dc_loop c i ti added ->
  rs_ignore (nth i (dc_segs c) rseg_d) = false -> vlan_split (rs_name (nth i (dc_segs c) rseg_d)) = Some (p, v) ->
  fst (vlan_add ti (x_max c) p v) < 0 ->
  dc_res c = (-1, snd (vlan_add ti (x_max c) p v)).
Proof using.
intros c i ti added p v Hi HLp Hg Hs Hn. rewrite (dcs3_res_split c i ti added p v Hi HLp Hg Hs).
replace (fst (vlan_add ti (x_max c) p v) <? 0) with true by (symmetry; apply Z.ltb_lt; exact Hn). reflexivity.
Qed.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* a range [q, q + len) of the table or the count cell: not in the shadow memory, below the allocator's ceiling or at
   or above the entry sp, apart from this call's class-1 frame, not in the image *)
Definition dcs3_far (c : dcx) (q len : Z) : Prop :=
  (q + len <= kLowShadowBeg \/ kHighShadowEnd <= q) /\
  (q + len <= alloc_ceiling \/ dc_sp0 c <= q) /\
  (q + len <= dc_F c \/ dc_F c + 128 <= q) /\
  (forall x, q <= x < q + len -> ~ in_img SEGS x).
(* the bytes this segment and the add call must keep or write: the real stack below the entry sp, the class-1 frame
   and its shadow *)
Definition dcs3_safe (c : dcx) (a : Z) : Prop :=
  (alloc_ceiling <= a < dc_sp0 c) \/ (dc_F c <= a < dc_F c + 128) \/ (SB + dc_F c / 8 <= a < SB + dc_F c / 8 + 16).
Lemma dcs3_safe_far : forall c q len a, in_app (dc_F c) 128 -> dcs3_far c q len -> dcs3_safe c a -> ~ (q <= a < q + len).
Proof using.
intros c q len a HF (N1 & N2 & N3 & _) [Ha | [Ha | Ha]] Hq.
- destruct N2; lia.
- destruct N3; lia.
- pose proof alloc_ceiling_val as [[CL CH] _].
  unfold in_app, kLowShadowBeg, kHighMemBeg, kHighShadowEnd, ASAN_CEIL, SB in *.
  set (F := dc_F c) in *. clearbody F.
  assert (HF8 : 0 <= F / 8 <= F / 8) by (split; [apply Z.div_pos|]; lia).
  destruct HF as [HF1 [HF2 | [HF2 HF3]]].
  + assert (F / 8 <= 0x7fff7000 / 8) by (apply Z.div_le_mono; lia). destruct N1; lia.
  + assert (F / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia). destruct N1; lia.
Qed.

Section e.
Variable B : asyms.
Variables RLO RHI GOTW GUARD : Z.
Hypothesis RO_IMG : dc_ro_imgP RLO RHI.
Context {RO : ro_below_ofl SEGS RLO RHI}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
#[local] Notation PRE := (dc_pre B DC_STK RLO RHI GOTW GUARD).
#[local] Notation JR c S3 W3 mem3 md3 k := (ajournal SEGS B DC_STK (dc_sp0 c) (dc_FP c) (x_ly c) (x_S c) (x_W c)
  (x_mem c) (x_md c) [(1, x_fpos c)] (x_ly c) S3 W3 mem3 md3 k).

(* the entry's stack facts *)
Lemma dcs3_stk : forall c, PRE c ->
  dc_sp0 c mod 16 = 0 /\ alloc_ceiling <= ly_stk_lo (x_ly c) /\ ly_stk_lo (x_ly c) + DC_STK <= dc_sp0 c /\
  dc_sp0 c <= ly_top (x_ly c) <= ly_stk_hi (x_ly c) /\ ly_stk_hi (x_ly c) <= 2 ^ 47 /\
  dc_s1 c mod 32 = 0 /\ (dc_s1 c = dc_sp0 c - 224 \/ dc_s1 c = dc_sp0 c - 240) /\ DC_STK = 12592 /\ DC_STK_ADD = 8304.
Proof using.
intros c HP. pose proof HP as [HAFN _ _ _ _ _ _ _ _ _ _ _ _].
pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _).
change (spZ (x_regs c)) with (dc_sp0 c) in Hstk.
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _ & Htop).
destruct (dc_sp1_facts (dc_sp0 c) Hal16) as (Hs1m & Hs1).
pose proof DC_STK_values as (_ & D2 & D3).
change (dc_sp1 (dc_sp0 c)) with (dc_s1 c) in Hs1m, Hs1. tauto.
Qed.
(* this call's class-1 frame at a cut state *)
Lemma dcs3_frame : forall c S3 W3 mem3 md3 k, JR c S3 W3 mem3 md3 k ->
  In (1, x_fpos c) (frames S3) /\ 4096 <= dc_F c /\ dc_F c + 128 <= alloc_ceiling /\ in_app (dc_F c) 128 /\
  dc_F c mod 64 = 0.
Proof using.
intros c S3 W3 mem3 md3 k HJ. pose proof HJ as (HAR3 & _ & _ & _ & _ & Hfrs & _).
assert (HinF : In (1, x_fpos c) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS (x_ly c) S3 W3 mem3 md3 1 (x_fpos c) HAR3 HinF) as (H0 & H1 & H2).
destruct (frame_al64 SEGS B (x_ly c) S3 W3 mem3 md3 1 (x_fpos c) HAR3 HinF) as (H3 & _).
assert (F128 : fs_frame_bytes 1 = 128) by (vm_compute; reflexivity). rewrite F128 in H1, H2.
unfold dc_F. tauto.
Qed.
(* the footprint is the table's entries below max and the count cell *)
Lemma dcs3_inFP : forall c, PRE c -> forall x, inFP (dc_FP c) x ->
  (x_tab c <= x < x_tab c + seg_spec.RVLAN_SIZE * (x_max c + 1)) \/ (x_n c <= x < x_n c + 4).
Proof using.
intros c HP x (r & Hr & Hx).
pose proof HP as [_ _ _ _ _ _ _ _ _ _ HDP _ _].
destruct HDP as (_ & _ & _ & _ & _ & HVT & _). destruct HVT as (_ & _ & _ & Htbm & _).
assert (L : (length (x_tb c) <= length (snd (dc_res c)))%nat /\ Z.of_nat (length (snd (dc_res c))) <= x_max c)
  by exact (dcl_go_len (rc_seg (x_rc c)) (x_tb c) (x_max c) 0 (proj1 Htbm)).
destruct L as [L1 L2].
unfold dc_FP, declared_W, vtab_W in Hr. apply in_app_or in Hr as [Hr | Hr].
- destruct Hr as [<- | []]. cbn [fst snd] in Hx. left. unfold seg_spec.RVLAN_SIZE in *. lia.
- destruct (length (x_tb c) <? length (snd (dc_res c)))%nat; [|destruct Hr].
  destruct Hr as [<- | []]. cbn [fst snd] in Hx. right. lia.
Qed.
(* the table block *)
Lemma dcs3_far_tab : forall c S3 W3 mem3 md3 k, PRE c -> JR c S3 W3 mem3 md3 k -> dc_un B c (x_ly c) S3 ->
  dcs3_far c (x_tab c) (seg_spec.RVLAN_SIZE * (x_max c + 1)) /\
  x_tab c + seg_spec.RVLAN_SIZE * (x_max c + 1) <= alloc_ceiling /\
  exists b m, In (b, m) (ablocks B (x_ly c) S3) /\ b <= x_tab c /\
    x_tab c + seg_spec.RVLAN_SIZE * (x_max c + 1) <= b + m /\ 0 <= m.
Proof using.
intros c S3 W3 mem3 md3 k HP HJ HU.
pose proof HP as [HAFN _ _ _ _ _ _ _ _ _ HDP _ _]. pose proof (proj1 HAFN) as HAR0.
destruct HDP as (_ & _ & _ & _ & _ & HVT & _). destruct HVT as (_ & _ & _ & _ & (b & m & Hin & Hb1 & Hb2) & _).
pose proof HU as [HPERM _ _].
assert (Hin3 : In (b, m) (ablocks B (x_ly c) S3)) by exact (Permutation_in _ (Permutation_sym HPERM) Hin).
pose proof HJ as (HAR3 & _).
destruct (dcs3_frame c S3 W3 mem3 md3 k HJ) as (HinF & HF0 & HFc & HFapp & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin) as (_ & H4096 & Hc & Happ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [Rm1 Rm2].
pose proof (sep_block_frame SEGS B LAWS (x_ly c) S3 W3 mem3 md3 b m 1 (x_fpos c) HAR3 Hin3 HinF) as Hdj.
assert (F128 : fs_frame_bytes 1 = 128) by (vm_compute; reflexivity). rewrite F128 in Hdj.
unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. fold (dc_F c) in Hdj.
split; [|split; [lia | exists b, m; split; [exact Hin3 | lia]]].
split; [|split; [|split]].
- unfold in_app, kLowShadowBeg, kHighMemBeg, kHighShadowEnd, ASAN_CEIL in *. lia.
- left. lia.
- lia.
- intros x Hx. apply (blk_img SEGS B LAWS (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) b m x HAR0 Hin). lia.
Qed.
(* the count cell: one of the three places sa_dst allows *)
Lemma dcs3_far_n : forall c S3 W3 mem3 md3 k, PRE c -> JR c S3 W3 mem3 md3 k -> dc_un B c (x_ly c) S3 ->
  dcs3_far c (x_n c) 4.
Proof using.
intros c S3 W3 mem3 md3 k HP HJ HU.
pose proof HP as [HAFN _ _ _ _ _ _ _ _ _ HDP _ _]. pose proof (proj1 HAFN) as HAR0.
destruct HDP as (_ & _ & _ & _ & _ & HVT & _).
destruct HVT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hndst & _).
pose proof HU as [HPERM _ _].
pose proof HJ as (HAR3 & _ & _ & _ & _ & Hfrs & _).
destruct (dcs3_frame c S3 W3 mem3 md3 k HJ) as (HinF & HF0 & HFc & HFapp & _).
destruct (dcs3_stk c HP) as (_ & Hceil & Hslo & Htop & H47 & _ & _ & DS & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hndst as [((cid & pos & Hfr & Hcid & Hf1 & Hf2) & _) | [((b & m & Hin & Hb1 & Hb2) & _) | (Hsp & Htp & _ & _)]].
- destruct (frames_bounds SEGS B LAWS (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) cid pos HAR0 Hfr) as (Hg0 & Hgc & Hgapp).
  destruct (in_split _ _ Hfr) as (l1 & l2 & El).
  pose proof (sep_frames_pos SEGS B LAWS (x_ly c) S3 W3 mem3 md3 (1, x_fpos c) (cid, pos) [] l1 l2 HAR3
    ltac:(rewrite Hfrs, El; reflexivity)) as Hdj.
  unfold zdisjoint, frame_rng in Hdj. cbn [fst snd] in Hdj. fold (dc_F c) in Hdj.
  assert (F128 : fs_frame_bytes 1 = 128) by (vm_compute; reflexivity). rewrite F128 in Hdj.
  split; [|split; [|split]].
  + unfold in_app, kLowShadowBeg, kHighMemBeg, kHighShadowEnd, ASAN_CEIL in *. lia.
  + left. lia.
  + lia.
  + intros x Hx. apply (frm_img SEGS B LAWS (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) cid pos x HAR0 Hfr). lia.
- assert (Hin3 : In (b, m) (ablocks B (x_ly c) S3)) by exact (Permutation_in _ (Permutation_sym HPERM) Hin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin) as (_ & H4096 & Hc & Happ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [Rm1 Rm2].
  pose proof (sep_block_frame SEGS B LAWS (x_ly c) S3 W3 mem3 md3 b m 1 (x_fpos c) HAR3 Hin3 HinF) as Hdj.
  assert (F128 : fs_frame_bytes 1 = 128) by (vm_compute; reflexivity). rewrite F128 in Hdj.
  unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. fold (dc_F c) in Hdj.
  split; [|split; [|split]].
  + unfold in_app, kLowShadowBeg, kHighMemBeg, kHighShadowEnd, ASAN_CEIL in *. lia.
  + left. lia.
  + lia.
  + intros x Hx. apply (blk_img SEGS B LAWS (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) b m x HAR0 Hin). lia.
- change (spZ (x_regs c)) with (dc_sp0 c) in Hsp.
  split; [|split; [|split]].
  + right. unfold kHighShadowEnd in *. lia.
  + right. exact Hsp.
  + right. lia.
  + intros x Hx Him. pose proof (pa_segs_low x Him). unfold kLowMemEnd in *. lia.
Qed.
Lemma dcs3_safe_FP : forall c S3 W3 mem3 md3 k a, PRE c -> JR c S3 W3 mem3 md3 k -> dc_un B c (x_ly c) S3 ->
  dcs3_safe c a -> ~ inFP (dc_FP c) a.
Proof using.
intros c S3 W3 mem3 md3 k a HP HJ HU Ha Hf.
destruct (dcs3_frame c S3 W3 mem3 md3 k HJ) as (_ & _ & _ & HFapp & _).
destruct (dcs3_far_tab c S3 W3 mem3 md3 k HP HJ HU) as (FT & _).
pose proof (dcs3_far_n c S3 W3 mem3 md3 k HP HJ HU) as FN.
destruct (dcs3_inFP c HP a Hf) as [Hx | Hx];
  [exact (dcs3_safe_far c _ _ a HFapp FT Ha Hx) | exact (dcs3_safe_far c _ _ a HFapp FN Ha Hx)].
Qed.
Lemma dcs3_safe_E : forall c S3 W3 mem3 md3 k a (t t' : list (list Z * Z)), PRE c -> JR c S3 W3 mem3 md3 k ->
  dc_un B c (x_ly c) S3 -> Z.of_nat (length t') <= x_max c -> dcs3_safe c a -> ~ vtab_E (x_tab c) (x_n c) t t' a.
Proof using.
intros c S3 W3 mem3 md3 k a t t' HP HJ HU Ht' Ha Hf.
destruct (dcs3_frame c S3 W3 mem3 md3 k HJ) as (_ & _ & _ & HFapp & _).
destruct (dcs3_far_tab c S3 W3 mem3 md3 k HP HJ HU) as (FT & _).
pose proof (dcs3_far_n c S3 W3 mem3 md3 k HP HJ HU) as FN.
destruct Hf as [Hx | Hx].
- apply (dcs3_safe_far c _ _ a HFapp FT Ha). unfold seg_spec.RVLAN_SIZE in *. lia.
- destruct (length t <? length t')%nat; [|destruct Hx]. exact (dcs3_safe_far c _ _ a HFapp FN Ha Hx).
Qed.

(* the stack's shadow is zero at every allocator state *)
Lemma dcs3_stack_shadow : forall ly S W mem md x n, AR SEGS B ly S W mem md ->
  ly_stk_lo ly <= x -> x + n <= ly_stk_hi ly -> 0 < n ->
  range_addressable (rdW W mem) SHADOW_OFF x n /\ shadow_hull_vis (rdW W mem) x n.
Proof using.
intros ly S W mem md x n HAR Hlo Hhi Hn.
pose proof (al_zshadow _ _ LAWS ly S W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR
  ltac:(unfold zero_shadow_ranges; left; reflexivity)) as HZ.
cbn [fst snd] in HZ.
pose proof (lo_top ly (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Pl & Ph & _).
unfold page_aligned in Pl, Ph.
set (lo := ly_stk_lo ly) in *. set (hi := ly_stk_hi ly) in *. clearbody lo hi.
assert (D : forall j, lo / 8 <= j < hi / 8 -> rdW W mem (SHADOW_OFF + j) = Some 0).
{ intros j Hj. pose proof (HZ (j - lo / 8)) as Hz. unfold shadow_of_addr in Hz.
  replace (SHADOW_OFF + lo / 8 + (j - lo / 8)) with (SHADOW_OFF + j) in Hz by lia. apply Hz.
  clear - Hj Pl Ph. Z.div_mod_to_equations. lia. }
split.
- intros y Hy. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr. apply D.
  clear - Hy Hlo Hhi Pl Ph. Z.div_mod_to_equations. lia.
- intros s Hs. unfold shadow_addr, SHADOW_OFF in Hs.
  replace s with (SHADOW_OFF + (s - SHADOW_OFF)) by lia. rewrite D; [discriminate|].
  unfold SHADOW_OFF. clear - Hs Hlo Hhi Hn Pl Ph. Z.div_mod_to_equations. lia.
Qed.

(* the stack above the entry sp stays present when the count cell is there (sa_dst's real-stack arm) *)
Lemma dcs3_apres : forall c S3 W3 mem3 md3 k ti, PRE c -> JR c S3 W3 mem3 md3 k -> dc_un B c (x_ly c) S3 ->
  dc_tab c ti W3 mem3 -> astack_pres (x_ly c) (w_H (x_W c)) (x_mem c) (dc_sp0 c) ->
  astack_pres (x_ly c) (w_H W3) mem3 (dc_sp0 c - DC_STK).
Proof using.
intros c S3 W3 mem3 md3 k ti HP HJ HU HT HA.
apply (astack_pres_journal SEGS B pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HA).
intros a Ha Hb. destruct (dcs3_far_tab c S3 W3 mem3 md3 k HP HJ HU) as (_ & Htc & _).
destruct (dcs3_stk c HP) as (_ & Hceil & Hslo & _ & _ & _ & _ & DS & _).
destruct (dcs3_inFP c HP a Ha) as [Hx | Hx].
{ exfalso. clear - Hx Htc Hceil Hslo Hb DS. unfold seg_spec.RVLAN_SIZE in *. lia. }
destruct HT as (_ & Hnv & _). specialize (Hnv (Z.to_nat (a - x_n c)) ltac:(lia)).
rewrite Z2Nat.id in Hnv by lia. replace (x_n c + (a - x_n c)) with a in Hnv by lia. rewrite Hnv. discriminate.
Qed.

(* vtab_pre at a cut state *)
Lemma dcs3_vtab : forall c S3 W3 mem3 md3 k ti (regsc : bvmap 5 word), PRE c -> JR c S3 W3 mem3 md3 k ->
  dc_un B c (x_ly c) S3 -> dc_tab c ti W3 mem3 -> spZ regsc = dc_s1 c ->
  vtab_pre SEGS B (x_ly c) S3 W3 mem3 regsc (x_tab c) (x_max c) (x_n c) ti.
Proof using.
intros c S3 W3 mem3 md3 k ti regsc HP HJ HU HT Hsp.
pose proof HP as [HAFN _ _ _ _ _ _ _ _ _ HDP _ _]. pose proof (proj1 HAFN) as HAR0.
destruct HDP as (_ & _ & _ & _ & _ & HVT & _).
destruct HVT as (Ht0 & Ht16 & _ & Htbm & _ & (Ta0 & Ta63 & Tam & _) & Htam & Hn0 & Hn4 & _ & Hndst &
  (Na0 & Na63 & Nam & Nra & _) & Hndj).
pose proof HT as (HTr & HTn & HTl & HTm).
pose proof HU as [HPERM _ _].
pose proof HJ as (HAR3 & _ & _ & _ & _ & Hfrs & _).
destruct (dcs3_far_tab c S3 W3 mem3 md3 k HP HJ HU) as (FT & Htc & b & m & Hin3 & Hb1 & Hb2 & Hm).
pose proof (dcs3_far_n c S3 W3 mem3 md3 k HP HJ HU) as FN.
destruct (dcs3_stk c HP) as (Hal16 & Hceil & Hslo & Htop & H47 & Hs1m & Hs1 & DS & _).
pose proof (req_size_pos m Hm) as [Rm1 Rm2].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HNS : forall x, inFP (dc_FP c) x -> x < kLowShadowBeg \/ kHighShadowEnd <= x).
{ intros x Hx. destruct FT as (T1 & _). destruct FN as (N1 & _).
  destruct (dcs3_inFP c HP x Hx) as [Hq | Hq]; [destruct T1 | destruct N1]; lia. }
unfold vtab_pre.
split; [exact Ht0|]. split; [exact Ht16|]. split; [exact HTr|]. split; [lia|].
split; [exists b, m; split; [exact Hin3 | lia]|].
split.
{ split; [exact Ta0|]. split; [exact Ta63|]. split; [exact Tam|].
  split; [apply (range_addressable_of_block SEGS B LAWS (x_ly c) S3 W3 mem3 md3 b m); [exact HAR3 | exact Hin3 | lia | unfold seg_spec.RVLAN_SIZE in *; lia]|].
  intros Hpos. apply (shadow_hull_vis_of_block SEGS B LAWS (x_ly c) S3 W3 mem3 md3 b m); [exact HAR3 | exact Hin3 | lia | unfold seg_spec.RVLAN_SIZE in *; lia | exact Hpos]. }
split; [exact Htam|]. split; [exact Hn0|]. split; [exact Hn4|]. split; [exact HTn|].
assert (HRA : range_addressable (rdW W3 mem3) SHADOW_OFF (x_n c) 4 /\ shadow_hull_vis (rdW W3 mem3) (x_n c) 4 /\
  sa_dst SEGS B (x_ly c) S3 W3 mem3 regsc (x_n c) 4).
{ destruct Hndst as [((cid & pos & Hfr & Hcid & Hf1 & Hf2) & Hra0) | [((b' & m' & Hin' & Hb1' & Hb2') & Hra0) | (Hsp0 & Htp0 & Hpr0 & Hap0)]].
  - destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR0 Hfr) as (Hf32 & _).
    assert (Hfr3 : In (cid, pos) (frames S3)) by (rewrite Hfrs; right; exact Hfr).
    assert (RA3 : range_addressable (rdW W3 mem3) SHADOW_OFF (x_n c) 4).
    { apply (range_addressable_entry_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cid pos _ _ HJ Hfr Hcid Hf1 Hf2
        ltac:(clear - Hf32; Z.div_mod_to_equations; lia) HNS HAR0 Hra0). }
    split; [exact RA3|]. split.
    + apply (shadow_hull_vis_of_frame SEGS B LAWS (x_ly c) S3 W3 mem3 md3 cid pos); [exact HAR3 | exact Hfr3 | exact Hf1 | exact Hf2 | lia].
    + left. split; [exists cid, pos; split; [exact Hfr3 | split; [exact Hcid | split; [exact Hf1 | exact Hf2]]] | exact RA3].
  - assert (Hin3' : In (b', m') (ablocks B (x_ly c) S3)) by exact (Permutation_in _ (Permutation_sym HPERM) Hin').
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin') as (_ & _ & _ & _ & _ & _ & Hm').
    pose proof (req_size_pos m' ltac:(lia)) as [Rm1' Rm2'].
    assert (RA3 : range_addressable (rdW W3 mem3) SHADOW_OFF (x_n c) 4)
      by (apply (range_addressable_of_block SEGS B LAWS (x_ly c) S3 W3 mem3 md3 b' m'); [exact HAR3 | exact Hin3' | lia | lia]).
    split; [exact RA3|]. split.
    + apply (shadow_hull_vis_of_block SEGS B LAWS (x_ly c) S3 W3 mem3 md3 b' m'); [exact HAR3 | exact Hin3' | lia | lia | lia].
    + right; left. split; [exists b', m'; split; [exact Hin3' | lia] | exact RA3].
  - change (spZ (x_regs c)) with (dc_sp0 c) in Hsp0, Hap0.
    pose proof (dcs3_apres c S3 W3 mem3 md3 k ti HP HJ HU HT Hap0) as HA3.
    destruct (dcs3_stack_shadow (x_ly c) S3 W3 mem3 md3 (x_n c) 4 HAR3 ltac:(lia) ltac:(lia) ltac:(lia)) as (RA3 & HV3).
    split; [exact RA3|]. split; [exact HV3|].
    right; right. rewrite Hsp. split; [lia|]. split; [exact Htp0|]. split.
    + intros i Hi. apply HA3. lia.
    + apply (astack_pres_mono (x_ly c) (w_H W3) mem3 (dc_sp0 c - DC_STK) (dc_s1 c) ltac:(lia) HA3). }
destruct HRA as (RA3 & HV3 & HDST).
split; [exact HDST|].
split; [split; [exact Na0 | split; [exact Na63 | split; [exact Nam | split; [exact RA3 | intros _; exact HV3]]]]|].
exact Hndj.
Qed.

(* the parent string at frame + 32 and the rest of add_pre *)
Lemma dcs3_add_pre : forall c S3 W3 mem3 md3 k ti p v (regsc : bvmap 5 word), PRE c -> JR c S3 W3 mem3 md3 k ->
  dc_un B c (x_ly c) S3 -> dc_tab c ti W3 mem3 -> spZ regsc = dc_s1 c ->
  sa_strz (rdW W3 mem3) (dc_F c + 32) p -> (length p <= 15)%nat ->
  rdW W3 mem3 (SB + dc_F c / 8 + 4) = Some 0 -> rdW W3 mem3 (SB + dc_F c / 8 + 5) = Some 0 -> 0 <= v < 65536 ->
  add_pre SEGS B (x_ly c) S3 W3 mem3 regsc (x_tab c) (x_max c) (x_n c) (dc_F c + 32) v ti p.
Proof using.
intros c S3 W3 mem3 md3 k ti p v regsc HP HJ HU HT Hsp HPZ Hp15 SH4 SH5 Hv.
pose proof HJ as (HAR3 & _).
destruct (dcs3_frame c S3 W3 mem3 md3 k HJ) as (HinF & HF0 & HFc & HFapp & HF64).
destruct (dcs3_far_tab c S3 W3 mem3 md3 k HP HJ HU) as ((_ & _ & T3 & _) & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR3 HinF) as (_ & _ & Hfp & _).
assert (F128 : fs_frame_bytes 1 = 128) by (vm_compute; reflexivity). rewrite F128 in Hfp.
change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c) in Hfp.
set (F := dc_F c) in *.
assert (HAM : forall o len, 0 <= o -> 0 <= len -> o + len <= 128 -> amem_range (F + o) len).
{ intros o len H1 H2 H3. unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *.
  pose proof alloc_ceiling_val as [[CL CH] _]. lia. }
unfold add_pre.
split; [exact (dcs3_vtab c S3 W3 mem3 md3 k ti regsc HP HJ HU HT Hsp)|].
split; [lia|].
split.
{ split; [exact HPZ|]. intros x Hx. apply (aview_some_of_apresent SEGS). apply (proj1 (Hfp x ltac:(clear - Hx Hp15 HF64; Z.div_mod_to_equations; lia))). }
split.
{ split; [lia|]. split; [pose proof alloc_ceiling_val as [[CL CH] _]; lia|]. split; [apply HAM; lia|].
  split; [|intros Hpos; apply (shadow_hull_vis_of_frame SEGS B LAWS (x_ly c) S3 W3 mem3 md3 1 (x_fpos c)); [exact HAR3 | exact HinF | change (frame_addr (x_ly c) 1 (x_fpos c)) with F; lia | rewrite F128; change (frame_addr (x_ly c) 1 (x_fpos c)) with F; lia | lia]].
  intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
  assert (Hq : x / 8 = F / 8 + 4 \/ x / 8 = F / 8 + 5) by (clear - Hx Hp15 HF64; Z.div_mod_to_equations; lia).
  unfold SB in SH4, SH5. unfold SHADOW_OFF.
  destruct Hq as [-> | ->]; [rewrite Z.add_assoc; exact SH4 | rewrite Z.add_assoc; exact SH5]. }
split; [lia|].
split; [apply HAM; lia|].
split; [right; left; exists 1, (x_fpos c); split; [exact HinF|]; split; [lia|]; rewrite F128; change (frame_addr (x_ly c) 1 (x_fpos c)) with F; lia|].
split.
{ unfold sa_disj, seg_spec.cstr_span.
  assert (0 <= (- (F + 32 + Z.of_nat (length p) + 1)) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  unfold seg_spec.RVLAN_SIZE in *. destruct T3; lia. }
exact Hv.
Qed.

(* arodata_okP at a cut state: the read-only bytes are image bytes the journal keeps *)
Lemma dcs3_rod : forall c S3 W3 mem3 md3 k, PRE c -> JR c S3 W3 mem3 md3 k -> dc_un B c (x_ly c) S3 ->
  arodata_okP SEGS RLO RHI B (rdW W3 mem3).
Proof using RO_IMG RO.
intros c S3 W3 mem3 md3 k HP HJ HU a Hro Hno Herr.
pose proof HP as [_ HROD _ _ _ _ _ _ _ _ _ _ _].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K3 & _).
assert (Himg : in_img SEGS a).
{ destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (RO_IMG a Hr)]. }
assert (Hnf : ~ inFP (dc_FP c) a).
{ intros Hf. destruct (dcs3_far_tab c S3 W3 mem3 md3 k HP HJ HU) as ((_ & _ & _ & T4) & _).
  destruct (dcs3_far_n c S3 W3 mem3 md3 k HP HJ HU) as (_ & _ & _ & N4).
  destruct (dcs3_inFP c HP a Hf) as [Hx | Hx]; [exact (T4 a Hx Himg) | exact (N4 a Hx Himg)]. }
rewrite (K3 a Himg Hno Herr (fp_spares_below (dc_FP c) a (ro_below_ofl_at a Hro) Hnf)).
exact (HROD a Hro Hno Herr).
Qed.

(* the frame chain at the call: the prologue's frame record (ra at sp0 - 8, s0 at sp0 - 16) on the entry's chain
   when the footprint lies below the allocator's ceiling (the count cell in a frame or a heap block) *)
Lemma dcs3_chain_low : forall c S3 W3 mem3 md3 k, PRE c -> JR c S3 W3 mem3 md3 k ->
  (forall x, inFP (dc_FP c) x -> x < alloc_ceiling) ->
  rdword (rdW W3 mem3) (dc_sp0 c - 8) = Some (bv_unsigned (getr (x_regs c) 1)) ->
  rdword (rdW W3 mem3) (dc_sp0 c - 16) = Some (bv_unsigned (getr (x_regs c) 8)) ->
  exists ch1, achain (x_ly c) (rdW W3 mem3) (dc_s1 c) (dc_sp0 c) ch1.
Proof using.
intros c S3 W3 mem3 md3 k HP HJ HLOW H8 H16.
pose proof HP as [HAFN _ _ _ _ _ _ _ _ _ _ _ _].
pose proof HAFN as (_ & _ & Hra4 & _ & _ & _ & _ & Hch & _).
change (spZ (x_regs c)) with (dc_sp0 c) in Hch.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & K1 & _).
destruct (dcs3_stk c HP) as (Hal16 & Hceil & Hslo & Htop & H47 & Hs1m & Hs1 & DS & _).
destruct (Z_lt_le_dec (dc_sp0 c) (ly_top (x_ly c) - 16)) as [Hlt | Hge].
- exists ((dc_sp0 c, raZ (x_regs c), s0Z (x_regs c)) :: x_ch c).
  apply (achain_push (x_ly c) (rdW (x_W c) (x_mem c)) (rdW W3 mem3) (dc_sp0 c) (s0Z (x_regs c)) (raZ (x_regs c))
    (x_ch c) (dc_s1 c) Hch).
  + lia.
  + intros a Ha. apply K1; [lia | lia | intros Hf; specialize (HLOW a Hf); lia].
  + exact H8.
  + exact H16.
  + exact Hra4.
  + lia.
  + clear - Hal16. Z.div_mod_to_equations. lia.
  + exact Hlt.
  + lia.
- exists []. left. split; [right; left; lia | reflexivity].
Qed.
(* the frame chain at the call, in all three places of the count cell *)
Lemma dcs3_chain : forall c S3 W3 mem3 md3 k ti, PRE c -> JR c S3 W3 mem3 md3 k -> dc_un B c (x_ly c) S3 ->
  dc_tab c ti W3 mem3 ->
  rdword (rdW W3 mem3) (dc_sp0 c - 8) = Some (bv_unsigned (getr (x_regs c) 1)) ->
  rdword (rdW W3 mem3) (dc_sp0 c - 16) = Some (bv_unsigned (getr (x_regs c) 8)) ->
  exists ch1, achain (x_ly c) (rdW W3 mem3) (dc_s1 c) (dc_sp0 c) ch1.
Proof using.
intros c S3 W3 mem3 md3 k ti HP HJ HU HT H8 H16.
pose proof HP as [HAFN _ _ _ _ _ _ _ _ _ HDP _ _]. pose proof (proj1 HAFN) as HAR0.
destruct HDP as (_ & _ & _ & _ & _ & HVT & _).
destruct HVT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hndst & _).
destruct (dcs3_stk c HP) as (Hal16 & Hceil & Hslo & Htop & H47 & Hs1m & Hs1 & DS & _).
destruct (dcs3_far_tab c S3 W3 mem3 md3 k HP HJ HU) as (_ & Htc & _).
assert (HLOW : x_n c + 4 <= alloc_ceiling -> forall x, inFP (dc_FP c) x -> x < alloc_ceiling).
{ intros Hn x Hx. destruct (dcs3_inFP c HP x Hx); lia. }
destruct Hndst as [((cid & pos & Hfr & _ & Hf1 & Hf2) & _) | [((b & m & Hin & Hb1 & Hb2) & _) | (Hsp0 & _ & _ & Hap0)]].
- destruct (frames_bounds SEGS B LAWS (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) cid pos HAR0 Hfr) as (_ & Hgc & _).
  exact (dcs3_chain_low c S3 W3 mem3 md3 k HP HJ (HLOW ltac:(lia)) H8 H16).
- destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin) as (_ & _ & Hc & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [Rm1 Rm2].
  exact (dcs3_chain_low c S3 W3 mem3 md3 k HP HJ (HLOW ltac:(lia)) H8 H16).
- change (spZ (x_regs c)) with (dc_sp0 c) in Hsp0, Hap0.
  pose proof (dcs3_apres c S3 W3 mem3 md3 k ti HP HJ HU HT Hap0) as HA3.
  pose proof (astack_rd_of_pres SEGS (x_ly c) (w_H W3) mem3 _ HA3) as HR.
  apply (achain_any (x_ly c) (rdW W3 mem3) (dc_s1 c) (dc_sp0 c)
    (astack_rd_mono (x_ly c) (rdW W3 mem3) (dc_sp0 c - DC_STK) (dc_s1 c) ltac:(lia) HR)).
  right; right; right. lia.
Qed.

(* the footprint of the add call lies in this call's footprint, where this call may write it *)
Lemma dcs3_awr : forall c S3 W3 mem3 md3 k (ti ti' : list (list Z * Z)) a, PRE c -> JR c S3 W3 mem3 md3 k ->
  dc_un B c (x_ly c) S3 -> (length (x_tb c) <= length ti)%nat -> (length ti' <= length (snd (dc_res c)))%nat ->
  Z.of_nat (length ti') <= x_max c -> inFP (vtab_W (x_tab c) (x_n c) ti ti') a ->
  awr_byte SEGS B DC_STK (dc_sp0 c) (dc_FP c) (ablocks B (x_ly c) (x_S c)) (ablocks B (x_ly c) S3) (frames (x_S c))
    (x_ly c) [(1, x_fpos c)] a.
Proof using.
intros c S3 W3 mem3 md3 k ti ti' a HP HJ HU Hl1 Hl2 Hl3 Hf.
pose proof HP as [HAFN _ _ _ _ _ _ _ _ _ HDP _ _]. pose proof (proj1 HAFN) as HAR0.
destruct HDP as (_ & _ & _ & _ & _ & HVT & _).
destruct HVT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hndst & _).
pose proof HU as [HPERM _ _].
assert (HFP : inFP (dc_FP c) a).
{ destruct Hf as (r & Hr & Hx). unfold vtab_W in Hr. apply in_app_or in Hr as [Hr | Hr].
  - destruct Hr as [<- | []]. cbn [fst snd] in Hx.
    exists (x_tab c + seg_spec.RVLAN_SIZE * Z.of_nat (length (x_tb c)),
      x_tab c + seg_spec.RVLAN_SIZE * Z.of_nat (length (snd (dc_res c)))).
    split; [unfold dc_FP, declared_W, vtab_W; apply in_or_app; left; left; reflexivity|].
    cbn [fst snd]. unfold seg_spec.RVLAN_SIZE in *. lia.
  - destruct (length ti <? length ti')%nat eqn:El; [|destruct Hr]. destruct Hr as [<- | []]. cbn [fst snd] in Hx.
    apply Nat.ltb_lt in El. exists (x_n c, x_n c + 4). split; [|cbn [fst snd]; lia].
    unfold dc_FP, declared_W, vtab_W. apply in_or_app. right.
    replace (length (x_tb c) <? length (snd (dc_res c)))%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    left. reflexivity. }
unfold awr_byte, awr_prog_or_caller.
destruct Hf as (r & Hr & Hx). unfold vtab_W in Hr. apply in_app_or in Hr as [Hr | Hr].
- destruct Hr as [<- | []]. cbn [fst snd] in Hx.
  destruct (dcs3_far_tab c S3 W3 mem3 md3 k HP HJ HU) as (_ & _ & b & m & Hin3 & Hb1 & Hb2 & Hm).
  pose proof (req_size_pos m Hm) as [Rm1 Rm2].
  right; left. split; [exact HFP|]. exists b, m. split; [exact Hin3|]. unfold seg_spec.RVLAN_SIZE in *. lia.
- destruct (length ti <? length ti')%nat; [|destruct Hr]. destruct Hr as [<- | []]. cbn [fst snd] in Hx.
  destruct Hndst as [((cid & pos & Hfr & _ & Hf1 & Hf2) & _) | [((b & m & Hin & Hb1 & Hb2) & _) | (Hsp0 & Htp0 & _ & _)]].
  + right; right; right; right; right; right. split; [exact HFP|]. exists cid, pos. split; [exact Hfr|].
    left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
  + assert (Hin3 : In (b, m) (ablocks B (x_ly c) S3)) by exact (Permutation_in _ (Permutation_sym HPERM) Hin).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin) as (_ & _ & _ & _ & _ & _ & Hm).
    pose proof (req_size_pos m ltac:(lia)) as [Rm1 Rm2].
    right; left. split; [exact HFP|]. exists b, m. split; [exact Hin3 | lia].
  + change (spZ (x_regs c)) with (dc_sp0 c) in Hsp0.
    right; right; right; right; right; left. split; [exact HFP | lia].
Qed.
(* no byte of the add call's footprint lies in this call's stack window *)
Lemma dcs3_vis : forall c S3 W3 mem3 md3 k (ti ti' : list (list Z * Z)) a, PRE c -> JR c S3 W3 mem3 md3 k ->
  dc_un B c (x_ly c) S3 -> Z.of_nat (length ti') <= x_max c -> inFP (vtab_W (x_tab c) (x_n c) ti ti') a ->
  dc_sp0 c - DC_STK <= a < dc_sp0 c -> False.
Proof using.
intros c S3 W3 mem3 md3 k ti ti' a HP HJ HU Hl3 Hf Ha.
destruct (dcs3_far_tab c S3 W3 mem3 md3 k HP HJ HU) as (_ & Htc & _).
destruct (dcs3_far_n c S3 W3 mem3 md3 k HP HJ HU) as (_ & N2 & _).
destruct (dcs3_stk c HP) as (Hal16 & Hceil & Hslo & _).
destruct Hf as (r & Hr & Hx). unfold vtab_W in Hr. apply in_app_or in Hr as [Hr | Hr].
- destruct Hr as [<- | []]. cbn [fst snd] in Hx. unfold seg_spec.RVLAN_SIZE in *. lia.
- destruct (length ti <? length ti')%nat; [|destruct Hr]. destruct Hr as [<- | []]. cbn [fst snd] in Hx.
  destruct N2; lia.
Qed.

(* the table, the count cell, a string and a value carried to a reader that agrees on their bytes *)
Lemma dcs3_tab_ext : forall c t (W W' : world SEGS) (m m' : word -> option byte),
  (forall x, (x_tab c <= x < x_tab c + seg_spec.RVLAN_SIZE * (x_max c + 1)) \/ (x_n c <= x < x_n c + 4) ->
    rdW W' m' x = rdW W m x) ->
  dc_tab c t W m -> dc_tab c t W' m'.
Proof using.
intros c t W W' m m' He ((bs & Hb & Henc) & H2 & H3 & H4).
pose proof Henc as (Hlen & _).
split; [|split; [|split; [exact H3 | exact H4]]].
- exists bs. split; [|exact Henc]. intros j Hj. rewrite He; [exact (Hb j Hj)|]. left.
  rewrite Hlen in Hj. unfold seg_spec.RVLAN_SIZE. lia.
- intros kk Hk. rewrite He; [exact (H2 kk Hk)|]. right. lia.
Qed.
Lemma dcs3_strz_ext : forall (rd rd' : reader) q s, (forall x, rd' x = rd x) -> sa_strz rd q s -> sa_strz rd' q s.
Proof using. intros rd rd' q s He [Hz Hn]. split; [|exact Hn]. intros j Hj. rewrite He. exact (Hz j Hj). Qed.
Lemma dcs3_val_ext : forall (rd rd' : reader) q n v, (forall x, rd' x = rd x) -> sa_val rd q n v -> sa_val rd' q n v.
Proof using. intros rd rd' q n v He Hv k Hk. rewrite He. exact (Hv k Hk). Qed.
Lemma dcs3_rdword_ext : forall (rd rd' : reader) a, (forall x, rd' x = rd x) -> rdword rd' a = rdword rd a.
Proof using. intros rd rd' a He. apply rdword_ext. intros k _. apply He. Qed.
End e.
End f.
End d.
