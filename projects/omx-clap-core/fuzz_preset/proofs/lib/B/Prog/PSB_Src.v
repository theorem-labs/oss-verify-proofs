(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_td.v, with its module paths, module names and numbers changed; 635 of its 665 lines of code are new or changed and 322 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S4_PsRet.v, with its module paths and module names changed; 242 of its 285 lines of code are new or changed and 622 lines of the source are left out. *)
(* fuzz_preset lib/B, parse_string on image B (asan-ubsan): THE TEXT ACROSS ONE CALL, shared by every stretch of the
   B walk that calls (PSB_Scan: fuzz_malloc; PSB_U / PSB_Tail: hex4, put_utf8, fuzz_free). The B twin of WalkS4's
   lib/A/Prog/S4_PsSrc.v (a working branch e8c3040757a): the same statements over image B's
   instances (PSB_Base.v's PSB_PrhImg / PSB_PAListing / PSB_PAImg); image B's fact prh_pst_not_ro proved by computation
   over PI_prog_B's segments and relro bounds.
   rule 24: proves no function (kind: segment lemma). The function is parse_string B (lane BParseString); its reuse
   search is the record file r24-index.txt (sha256 e7c12b08eeb1; internal record) (checker CONFIRM; donor none).
   parse_string's text is home (prhReader_home: a live harness block of Lam, a registered read-only global or image
   string (kept_at), or a live allocator block whose base is not a hidden head). Its BYTES survive a call by the
   callee's journal (block clause / image clause) when the callee's footprint misses them; its SHADOW, which no journal
   keeps, is re-read at the post state from the laws:
     a Lam block           AR_laws_x field 14 alx_hshadow (the user range after the hidden head);
     a non-harness block   alx_shadow (no hidden head inside the block);
     in_zs                 alx_zshadow over the image's zero-shadow range;
     kept_img              per granule: alx_zshadow, or the const-shadow cell kept by field 16 alx_const_cells.
   The hull of an image text is the image's shadow (psb_img_shadow_vis below, over the PER-INSTANCE bounds pa_lo /
   pa_hi that kept_at / kept_img state since decff67d721f; a Theorem Labs lane's img_shadow_vis_cf at the instance).
   FILE SET: every non-lane file as the kit's cut 7cdbb61b5fa0 carries it (YCbqG.v 219748197d6b, PRW_HShadow.v 2662d68ca36b);
   earlier the lane's base 4800805a954 (the kit walkkit 4eb03b7b7e8).
   IMAGE FACTS taken as Section hypotheses (BParseString's agreement, verbatim from S4_PsSrc.v:117 / :119): ZSA, the
   zero-shadow ranges are granule-aligned (asyms_ok's aso_zshadow, YG0f.v:191); IMGV, psb_img_shadow_vis (a Theorem Labs lane's
   img_shadow_vis_cf at image B's own bounds, a unit-supplied fact; owner a Theorem Labs lane, instance
   lib/AU/AImgShadowVisCfB.v in the cut; never YImgTop's IMG_LO / IMG_TOP, which are image A's).
   Numerals: 8 (LENGTH, a shadow granule), 64 (LENGTH, the image margin kept_at states); no ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PS_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PSB_Base.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

Section src. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
(* image B's instances (PSB_Base.v's), the ones every statement below names *)
#[local] Existing Instances PSB_PrhImg PSB_PAListing PSB_PAImg.
#[local] Notation segs := (@pa_segs _ B_prog_listing PSB_PAImg).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PSB_PAImg).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PSB_PAImg).
#[local] Notation PST := (prh_pst (PI := PSB_PrhImg)).

(* ---- image B: the program's statics are not read-only (computed over PI_prog_B's segments and relro bounds) ---- *)
Definition psbs_seg_hit (lo n : Z) (s : Segment) : bool :=
  negb (seg_writable s) && (Z.of_N (seg_base s) <? lo + n) && (lo <? Z.of_N (seg_base s) + Z.of_N (seg_size s)).
Definition psbs_ro_hit (lo n : Z) : bool :=
  existsb (psbs_seg_hit lo n) segs || ((RLO <? lo + n) && (lo <? RHI)).
Lemma psbs_pst_free : forallb (fun r => negb (psbs_ro_hit (fst r) (snd r))) PST = true.
Proof. vm_compute. reflexivity. Qed.
Lemma psb_pst_not_ro : forall a, Exists (in_zr a) PST -> ~ in_roP segs RLO RHI a.
Proof.
  intros a Ha Hro. apply Exists_exists in Ha as (r & Hr & Hin). unfold in_zr in Hin.
  pose proof (proj1 (forallb_forall _ _) psbs_pst_free r Hr) as H. apply negb_true_iff in H.
  unfold psbs_ro_hit in H. apply orb_false_iff in H as [H1 H2].
  destruct Hro as [(s & Hs & Hw & Hsr) | Hrr].
  - assert (Hx : psbs_seg_hit (fst r) (snd r) s = false).
    { destruct (psbs_seg_hit (fst r) (snd r) s) eqn:E; [|reflexivity]. exfalso.
      assert (existsb (psbs_seg_hit (fst r) (snd r)) segs = true) by (apply existsb_exists; exists s; split; [exact Hs | exact E]).
      congruence. }
    unfold psbs_seg_hit in Hx. rewrite Hw in Hx. cbn [negb andb] in Hx.
    apply andb_false_iff in Hx as [Hx|Hx]; [apply Z.ltb_ge in Hx | apply Z.ltb_ge in Hx]; lia.
  - apply andb_false_iff in H2 as [Hx|Hx]; apply Z.ltb_ge in Hx; lia.
Qed.
Lemma psbs_ro_img : forall a, in_roP segs RLO RHI a -> in_img segs a.
Proof.
  intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PSB_PAImg a Hr)].
Qed.

(* ---- shadow arithmetic (S4_PsSrc.v's psrc_hull_sub / psrc_hull_img / psrc_zs_byte) ---- *)
Lemma psbs_hull_sub : forall (rd : reader) p m d n, shadow_hull_vis rd p m -> p <= d -> d + n <= p + m -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
  intros rd p m d n Hh Hpd Hdn Hn s Hs. apply Hh.
  pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (p + m - 1) ltac:(lia)) as M2.
  assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8) by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
  pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.
Lemma psbs_hull_img : forall lo hi a n s, 0 < n -> lo + 64 <= a -> a + n + 64 <= hi ->
  shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
  s = shadow_addr (8 * (s - SHADOW_OFF)) /\ lo <= 8 * (s - SHADOW_OFF) < hi.
Proof.
  intros lo hi a n s Hn Hlo Hhi Hs.
  unfold shadow_addr in *.
  assert (Hdlo : a / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z.div_mod a 8 ltac:(lia)) as Ha8. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ha8b.
  pose proof (Z.div_mod (a + n - 1) 8 ltac:(lia)) as Hb8. pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)) as Hb8b.
  pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8b.
  pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8b.
  unfold SHADOW_OFF in *.
  split; [rewrite Z.mul_comm, Z.div_mul by lia; lia | lia].
Qed.
(* a zero-shadow range of the image, aligned: every granule of it reads 0 *)
Lemma psbs_zs_byte : forall (rd : reader) q m x, q mod 8 = 0 -> m mod 8 = 0 -> zero_shadow rd SHADOW_OFF q m ->
  q <= x < q + m -> rd (shadow_addr x) = Some 0.
Proof.
  intros rd q m x Hq Hm Hz Hx. unfold shadow_addr.
  replace (SHADOW_OFF + x / 8) with (shadow_of_addr SHADOW_OFF q + (x / 8 - q / 8)) by (unfold shadow_of_addr; lia).
  apply Hz. pose proof (Z.div_mod q 8 ltac:(lia)). pose proof (Z.div_mod m 8 ltac:(lia)).
  pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
Qed.

(* IMAGE FACT, PER INSTANCE (a Theorem Labs lane's rule 2026-10-29 18:56Z): the image's shadow bytes are present in the view at
   every address of the image's OWN bounds, here image B's listing instance's pa_lo / pa_hi (the bounds kept_at /
   kept_img state, PRH_Base.v, per-instance since decff67d721f). At the #102 instance it is img_shadow_vis_cf at B's
   CfImg, whose cf_img_lo / cf_img_top equal pa_lo / pa_hi by computation (PSB_Inst.v). It replaces PRW_HShadow.v's
   ARx_img_shadow_vis, which is stated over YImgTop's IMG_LO / IMG_TOP (image A's bounds, below B''s top on #102) *)
Definition psb_img_shadow_vis
  (ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop) : Prop :=
  forall ly S Hp (W : world segs) mem md a, ARx ly S Hp W mem md ->
    @pa_lo _ B_prog_listing PSB_PAImg <= a < @pa_hi _ B_prog_listing PSB_PAImg ->
    aview segs (w_H W) mem (shadow_addr a) <> None.

Section l.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
(* IMAGE FACT (asyms_ok's aso_zshadow, YG0f.v:191): the image's zero-shadow ranges are granule-aligned *)
Hypothesis ZSA : forall q m, In (q, m) (as_zero_shadow B) -> q mod 8 = 0 /\ m mod 8 = 0.
(* IMAGE FACT (a Theorem Labs lane's img_shadow_vis_cf at image B's own bounds, above): the image's shadow bytes are present *)
Hypothesis IMGV : psb_img_shadow_vis ARx.

(* the text's shadow at a state, from where it lives; the state's laws only *)
Lemma psb_src_shadow : forall ly S Hp W mem md Lam p n,
  ARx ly S Hp W mem md ->
  (forall b m, In (b, m) Lam -> 0 <= m /\ In (b - cf_head, m + cf_head) (ablocks B ly S) /\ In (b - cf_head) Hp) ->
  (forall h, In h Hp -> exists k, 0 <= k /\ In (h, k) (ablocks B ly S)) ->
  (kept_at B Lam p n \/ (exists b m, In (b, m) (ablocks B ly S) /\ ~ In b Hp /\ b <= p /\ p + n <= b + m)) ->
  0 <= n ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF p n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) p n).
Proof.
  intros ly S Hp W mem md Lam p n HAR HLam HHp Hhome Hn0.
  pose proof cf_head_nonneg as Hh0. pose proof cf_head_al as Hh8.
  destruct (Z_lt_le_dec 0 n) as [Hn|Hn]; [|split; [apply range_addressable_nil; lia | intros; lia]].
  destruct Hhome as [[(b & m & Hin & Hb & Hm) | [(Hzs & Hlo & Hhi & _) | (Hlo & Hhi & Hk)]] | (b & m & Hin & Hnh & Hb & Hm)].
  - (* a harness block of Lam: field 14 *)
    destruct (HLam b m Hin) as (Hm0 & Hab & Hhp).
    destruct (alx_hshadow segs B ARx LAWS ly S Hp W mem md (b - cf_head) (m + cf_head) HAR Hab Hhp) as [Hbs Hhu].
    pose proof (req_size_pos (m + cf_head) (Z.add_nonneg_nonneg _ _ Hm0 Hh0)) as [R1 R2].
    replace (b - cf_head + cf_head) with b in Hbs, Hhu by lia.
    split.
    + eapply block_shadow_range; [exact Hbs | lia | lia].
    + intros _. apply (psbs_hull_sub _ b (req_size (m + cf_head) - cf_head) p n); [apply Hhu; lia | lia | lia | lia].
  - (* a registered read-only global: the zero-shadow range *)
    destruct Hzs as (q & m & Hin & Hq & Hqm). destruct (ZSA q m Hin) as [Zq Zm].
    pose proof (alx_zshadow segs B ARx LAWS ly S Hp W mem md (q, m) HAR ltac:(unfold zero_shadow_ranges; right; exact Hin)) as Hz.
    cbn [fst snd] in Hz. split.
    + apply (range_addressable_sub _ SHADOW_OFF q m p n); [|exact Hq|exact Hqm].
      exact (zero_shadow_range _ SHADOW_OFF q m Zq Zm Hz).
    + intros _ s0 Hs. destruct (psbs_hull_img _ _ p n s0 Hn Hlo Hhi Hs) as [E Hr]. rewrite E.
      exact (IMGV ly S Hp W mem md _ HAR Hr).
  - (* an image string, granule by granule *)
    split.
    + intros x Hx. destruct (Hk x Hx) as (_ & _ & _ & [Hz | (v & Hc & Hv)]).
      * destruct Hz as (q & m & Hin & Hq & Hqm). destruct (ZSA q m Hin) as [Zq Zm].
        pose proof (alx_zshadow segs B ARx LAWS ly S Hp W mem md (q, m) HAR ltac:(unfold zero_shadow_ranges; right; exact Hin)) as Hz.
        cbn [fst snd] in Hz. exists 0. split; [|left; reflexivity].
        unfold shadow_of_addr. change (SHADOW_OFF + x / 8) with (shadow_addr x).
        apply (psbs_zs_byte _ q m x Zq Zm Hz).
        pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
      * pose proof (alx_const_cells segs B ARx LAWS ly S Hp W mem md HAR) as HC.
        pose proof (proj1 (Forall_forall _ _) HC _ (Hc ly)) as Hch.
        cbn [cell_holds z1 c1 c_at c_w c_val aeval] in Hch. specialize (Hch 0%nat ltac:(lia)).
        rewrite Z.add_0_r in Hch. exists v. split.
        -- unfold shadow_of_addr. change (SHADOW_OFF + x / 8) with (shadow_addr x). rewrite Hch. f_equal.
           unfold le_byte. cbn [Z.of_nat]. rewrite Z.shiftr_0_r. change (2 ^ (8 * 1)) with 256.
           rewrite Z.mod_mod by lia. apply Z.mod_small. lia.
        -- destruct Hv as [Hv|Hv]; [left; exact Hv | right; exact Hv].
    + intros _ s0 Hs. destruct (psbs_hull_img _ _ p n s0 Hn Hlo Hhi Hs) as [E Hr]. rewrite E.
      exact (IMGV ly S Hp W mem md _ HAR Hr).
  - (* a live allocator block whose base is not a hidden head: alx_shadow *)
    destruct (alx_shadow segs B ARx LAWS ly S Hp W mem md b m HAR Hin) as [Hbs Hhu].
    { intros h Hh Hr. destruct (HHp h Hh) as (k & Hk0 & Hk).
      destruct (Z.eq_dec h b) as [->|Hne]; [exact (Hnh Hh)|].
      assert (Hneq : (h, k) <> (b, m)) by (intros E; injection E as E1 _; exact (Hne E1)).
      pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md h k b m HAR Hk Hin Hneq) as Hd.
      pose proof (req_size_pos k Hk0) as Rk. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
    assert (Rm : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
    rewrite Rm in Hbs, Hhu.
    split.
    + eapply block_shadow_range; [exact Hbs | lia | lia].
    + intros _. apply (psbs_hull_sub _ b m p n Hhu); lia.
Qed.

Lemma psb_src_garr8 : forall (W W2 : world segs) mem mem2 p l,
  (forall j, (j < length l)%nat -> aview segs (w_H W2) mem2 (p + Z.of_nat j) = aview segs (w_H W) mem (p + Z.of_nat j)) ->
  garr8 segs (mrestrict (w_H W) mem) p l -> garr8 segs (mrestrict (w_H W2) mem2) p l.
Proof.
  intros W W2 mem mem2 p l HA H j Hj. destruct (H j Hj) as [V R]. split; [|exact R].
  intros k Hk. rewrite (mbyte_of_aview segs (w_H W) (w_H W2) mem mem2). { exact (V k Hk). }
  assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r. exact (HA j Hj).
Qed.

(* THE SHARED LEMMA: a text at its home before ONE program call is at its home after it, with its bytes and shadow.
   The call is the callee's journal (from the call state lyc Sc Hpc W memc mdc to the post state), as aj_call_x /
   aj_call_xW / fpostW_x_of_apost hand it to the caller. The caller supplies: the callee's footprint FP1 misses the text
   and opens no sink; every block of the call state that is not a harness block survives and stays unhidden; the
   harness blocks of Lam are live at both states and hidden after; and every hidden head after is a live block's base
   (all from the callee's post and the ledger the caller keeps). The block premise is asked only of blocks of
   non-negative size (the only ones a text can live in); psb_src_after_call below is the same with it for all. The
   journal is over ANY world relation R (fuzz_free's post is at wle' segs RZ_cf): the proof reads only its ARx, block
   and image conjuncts; psb_src_after_call_nn_w is its instance at wle. *)
Lemma psb_src_after_call_nn_wR : forall (R : world segs -> world segs -> Prop)
  STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS Lam text tb,
  ajournal_xwR (SK := SK) segs B PST ARx R STK1 sp1 FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS ->
  src_rd W memc text tb -> prhReader_home B lyc Sc Hpc Lam text (Z.of_nat (length tb)) ->
  (forall a, inFP FP1 a -> ~ (text <= a < text + Z.of_nat (length tb))) ->
  ~ YI16.sink_open_fp FP1 ->
  (forall p n, In (p, n) (ablocks B lyc Sc) -> ~ In p Hpc -> 0 <= n -> In (p, n) (ablocks B ly2 S2) /\ ~ In p Hp2) ->
  (forall b m, In (b, m) Lam -> In (b - cf_head, m + cf_head) (ablocks B lyc Sc)) ->
  (forall b m, In (b, m) Lam -> 0 <= m /\ In (b - cf_head, m + cf_head) (ablocks B ly2 S2) /\ In (b - cf_head) Hp2) ->
  (forall h, In h Hp2 -> exists k, 0 <= k /\ In (h, k) (ablocks B ly2 S2)) ->
  src_rd W2 mem2 text tb /\ prhReader_home B ly2 S2 Hp2 Lam text (Z.of_nat (length tb)).
Proof.
  intros R STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS Lam text tb HJ HSRC HHOME HFP HSNK HNB HL1
    HL2 HHp.
  pose proof (ajxR_ar HJ) as HAR2. pose proof (ajxR_blk HJ) as F2. pose proof (ajxR_img HJ) as F3.
  pose proof cf_head_nonneg as Hh0.
  set (len := Z.of_nat (length tb)) in *.
  destruct HSRC as (HB & H4096 & Hceil & Hamr & HRA & HHU).
  (* the home after *)
  assert (HOME2 : prhReader_home B ly2 S2 Hp2 Lam text len).
  { destruct HHOME as [Hk | (b & m & Hin & Hnh & Hb & Hm)]; [left; exact Hk|].
    right. destruct (HNB b m Hin Hnh ltac:(unfold len in *; lia)) as [Hin2 Hnh2]. exists b, m. auto. }
  (* the bytes, one by one *)
  assert (HBY : forall j, (j < length tb)%nat ->
    aview segs (w_H W2) mem2 (text + Z.of_nat j) = aview segs (w_H W) memc (text + Z.of_nat j)).
  { intros j Hj. assert (Ha : text <= text + Z.of_nat j < text + len) by (subst len; lia).
    assert (Hnf : ~ inFP FP1 (text + Z.of_nat j)) by (intros Hf; exact (HFP _ Hf Ha)).
    destruct HHOME as [[(b & m & Hin & Hb & Hm) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hin & Hnh & Hb & Hm)].
    - pose proof (req_size_pos (m + cf_head)) as Rq. destruct (HL2 b m Hin) as (Hm0 & Hab2 & _).
      specialize (Rq ltac:(lia)).
      replace (text + Z.of_nat j) with (b - cf_head + (text + Z.of_nat j - (b - cf_head))) by lia.
      apply (F2 (b - cf_head) (m + cf_head)); [exact (HL1 b m Hin) | exact Hab2 | lia |].
      replace (b - cf_head + (text + Z.of_nat j - (b - cf_head))) with (text + Z.of_nat j) by lia. exact Hnf.
    - destruct (Hro _ Ha) as (Hr & Hno & Her).
      apply F3; [exact (psbs_ro_img _ Hr) | exact Hno | exact Her | exact (fun Hx => psb_pst_not_ro _ Hx Hr) |].
      intros Hs. exfalso. exact (HSNK Hs).
    - destruct (Hro _ Ha) as (Hr & Hno & Her & _).
      apply F3; [exact (psbs_ro_img _ Hr) | exact Hno | exact Her | exact (fun Hx => psb_pst_not_ro _ Hx Hr) |].
      intros Hs. exfalso. exact (HSNK Hs).
    - destruct (HNB b m Hin Hnh ltac:(lia)) as [Hin2 _].
      assert (Rm : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
      replace (text + Z.of_nat j) with (b + (text + Z.of_nat j - b)) by lia.
      apply (F2 b m); [exact Hin | exact Hin2 | rewrite Rm; lia |].
      replace (b + (text + Z.of_nat j - b)) with (text + Z.of_nat j) by lia. exact Hnf. }
  assert (HSH : range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF text len /\
    (0 < len -> shadow_hull_vis (aview segs (w_H W2) mem2) text len)).
  { apply (psb_src_shadow ly2 S2 Hp2 W2 mem2 md2 Lam text len HAR2); [exact HL2 | exact HHp | exact HOME2 | subst len; lia]. }
  split; [|exact HOME2].
  split; [exact (psb_src_garr8 W W2 memc mem2 text tb HBY HB)|].
  split; [exact H4096|]. split; [exact Hceil|]. split; [exact Hamr|]. exact HSH.
Qed.
Lemma psb_src_after_call_nn_w : forall STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS Lam text tb,
  ajournal_xw (SK := SK) segs B PST ARx STK1 sp1 FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS ->
  src_rd W memc text tb -> prhReader_home B lyc Sc Hpc Lam text (Z.of_nat (length tb)) ->
  (forall a, inFP FP1 a -> ~ (text <= a < text + Z.of_nat (length tb))) ->
  ~ YI16.sink_open_fp FP1 ->
  (forall p n, In (p, n) (ablocks B lyc Sc) -> ~ In p Hpc -> 0 <= n -> In (p, n) (ablocks B ly2 S2) /\ ~ In p Hp2) ->
  (forall b m, In (b, m) Lam -> In (b - cf_head, m + cf_head) (ablocks B lyc Sc)) ->
  (forall b m, In (b, m) Lam -> 0 <= m /\ In (b - cf_head, m + cf_head) (ablocks B ly2 S2) /\ In (b - cf_head) Hp2) ->
  (forall h, In h Hp2 -> exists k, 0 <= k /\ In (h, k) (ablocks B ly2 S2)) ->
  src_rd W2 mem2 text tb /\ prhReader_home B ly2 S2 Hp2 Lam text (Z.of_nat (length tb)).
Proof. exact (psb_src_after_call_nn_wR (@wle segs)). Qed.
(* the WS = [] instance (the journal of a callee with no wild site), its statement unchanged *)
Lemma psb_src_after_call_nn : forall STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 Lam text tb,
  ajournal_x (SK := SK) segs B PST ARx STK1 sp1 FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  src_rd W memc text tb -> prhReader_home B lyc Sc Hpc Lam text (Z.of_nat (length tb)) ->
  (forall a, inFP FP1 a -> ~ (text <= a < text + Z.of_nat (length tb))) ->
  ~ YI16.sink_open_fp FP1 ->
  (forall p n, In (p, n) (ablocks B lyc Sc) -> ~ In p Hpc -> 0 <= n -> In (p, n) (ablocks B ly2 S2) /\ ~ In p Hp2) ->
  (forall b m, In (b, m) Lam -> In (b - cf_head, m + cf_head) (ablocks B lyc Sc)) ->
  (forall b m, In (b, m) Lam -> 0 <= m /\ In (b - cf_head, m + cf_head) (ablocks B ly2 S2) /\ In (b - cf_head) Hp2) ->
  (forall h, In h Hp2 -> exists k, 0 <= k /\ In (h, k) (ablocks B ly2 S2)) ->
  src_rd W2 mem2 text tb /\ prhReader_home B ly2 S2 Hp2 Lam text (Z.of_nat (length tb)).
Proof.
  intros STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 Lam text tb HJ.
  exact (psb_src_after_call_nn_w STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 [] Lam text tb HJ).
Qed.
(* THE SAME at ANY budget WS (the P'' engine since the batch kit: fuzz_free at the cursor hands a budgeted journal) and over ANY
   world relation R; psb_src_after_call_w is its instance at wle *)
Lemma psb_src_after_call_wR : forall (R : world segs -> world segs -> Prop)
  STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS Lam text tb,
  ajournal_xwR (SK := SK) segs B PST ARx R STK1 sp1 FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS ->
  src_rd W memc text tb -> prhReader_home B lyc Sc Hpc Lam text (Z.of_nat (length tb)) ->
  (forall a, inFP FP1 a -> ~ (text <= a < text + Z.of_nat (length tb))) ->
  ~ YI16.sink_open_fp FP1 ->
  (forall p n, In (p, n) (ablocks B lyc Sc) -> ~ In p Hpc -> In (p, n) (ablocks B ly2 S2) /\ ~ In p Hp2) ->
  (forall b m, In (b, m) Lam -> In (b - cf_head, m + cf_head) (ablocks B lyc Sc)) ->
  (forall b m, In (b, m) Lam -> 0 <= m /\ In (b - cf_head, m + cf_head) (ablocks B ly2 S2) /\ In (b - cf_head) Hp2) ->
  (forall h, In h Hp2 -> exists k, 0 <= k /\ In (h, k) (ablocks B ly2 S2)) ->
  src_rd W2 mem2 text tb /\ prhReader_home B ly2 S2 Hp2 Lam text (Z.of_nat (length tb)).
Proof.
  intros R STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS Lam text tb HJ HSRC HHOME HFP HSNK HNB.
  apply (psb_src_after_call_nn_wR R STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS Lam text tb HJ HSRC
    HHOME HFP HSNK). intros p n Hin Hnh _. exact (HNB p n Hin Hnh).
Qed.
Lemma psb_src_after_call_w : forall STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS Lam text tb,
  ajournal_xw (SK := SK) segs B PST ARx STK1 sp1 FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS ->
  src_rd W memc text tb -> prhReader_home B lyc Sc Hpc Lam text (Z.of_nat (length tb)) ->
  (forall a, inFP FP1 a -> ~ (text <= a < text + Z.of_nat (length tb))) ->
  ~ YI16.sink_open_fp FP1 ->
  (forall p n, In (p, n) (ablocks B lyc Sc) -> ~ In p Hpc -> In (p, n) (ablocks B ly2 S2) /\ ~ In p Hp2) ->
  (forall b m, In (b, m) Lam -> In (b - cf_head, m + cf_head) (ablocks B lyc Sc)) ->
  (forall b m, In (b, m) Lam -> 0 <= m /\ In (b - cf_head, m + cf_head) (ablocks B ly2 S2) /\ In (b - cf_head) Hp2) ->
  (forall h, In h Hp2 -> exists k, 0 <= k /\ In (h, k) (ablocks B ly2 S2)) ->
  src_rd W2 mem2 text tb /\ prhReader_home B ly2 S2 Hp2 Lam text (Z.of_nat (length tb)).
Proof. exact (psb_src_after_call_wR (@wle segs)). Qed.
Lemma psb_src_after_call : forall STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 Lam text tb,
  ajournal_x (SK := SK) segs B PST ARx STK1 sp1 FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  src_rd W memc text tb -> prhReader_home B lyc Sc Hpc Lam text (Z.of_nat (length tb)) ->
  (forall a, inFP FP1 a -> ~ (text <= a < text + Z.of_nat (length tb))) ->
  ~ YI16.sink_open_fp FP1 ->
  (forall p n, In (p, n) (ablocks B lyc Sc) -> ~ In p Hpc -> In (p, n) (ablocks B ly2 S2) /\ ~ In p Hp2) ->
  (forall b m, In (b, m) Lam -> In (b - cf_head, m + cf_head) (ablocks B lyc Sc)) ->
  (forall b m, In (b, m) Lam -> 0 <= m /\ In (b - cf_head, m + cf_head) (ablocks B ly2 S2) /\ In (b - cf_head) Hp2) ->
  (forall h, In h Hp2 -> exists k, 0 <= k /\ In (h, k) (ablocks B ly2 S2)) ->
  src_rd W2 mem2 text tb /\ prhReader_home B ly2 S2 Hp2 Lam text (Z.of_nat (length tb)).
Proof.
  intros STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 Lam text tb HJ HSRC HHOME HFP HSNK HNB.
  apply (psb_src_after_call_nn STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 Lam text tb HJ HSRC HHOME
    HFP HSNK). intros p n Hin Hnh _. exact (HNB p n Hin Hnh).
Qed.
End l.
End src.
