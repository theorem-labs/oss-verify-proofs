(* Made by a Theorem Labs lane (2026-10-30, a Theorem Labs lane's DRIVER_CF_B) as the image-B twin of lib/A/ReplyDriverCf.v
   (a Theorem Labs lane, commit 812d59abd29): the image-B DRIVER_CF plug for
   plugin-hostd/fuzz_reply.asan-ubsan, TFIB_B_T (lib/A/ReplyTFIB.v) from W8's ARx-generic entry composition at the cf
   instance (lib/B/W_LLVMFuzzerTestOneInput_top_x.v fr_contract_top_x, W8Entry-2 / W8Add commit
   72c6e75e6cc), through the B cf driver (lib/B/ReplyTFIBBcf.v, program slot lib/B/YD1w_cf.v fr_lib_contract_drvR at
   route R's relation wle' tfibsegs RZ_cf).
   A's text over lib/B's modules and _b names, with A's parameter record CfParams_reply (lib/A/CfParamsReply.v,
   the one record of both images: no field is an image address, as lib/B/W_LLVMFuzzerTestOneInput_top_x.v's ARX uses it) (CfImg_B, REPLYB_RO_LO / _HI, YCfn_cf's fr_live_pre_b /
   fr_live_post_b / fr_surv_b / fr_FP_b), YCbq / YCbqG / YE01 from lib/B as A2's YD1w_cf. One difference from A: no
   reply_handoff_cov. The B driver carries no start-up covered-range hypothesis: lib/B/YD1pcf.v closes it with
   a Theorem Labs lane's YStkCov.tfib_handoff_stk_up_cov. No image numeral beyond A's (0x7fff8000 in drv_ceil is A's constant
   and holds for both images through Reusable alloc_ceiling_val).
   proves no function (kind: composition). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0ncf YGcfNames YCbqG YG0lawscf YGcallcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp YM05 YG0dcf YGcfRoomLive.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCfn YCeg YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_cut_x W_LLVMFuzzerTestOneInput_G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyStartWitB ReplyImgRowsB ReplyImg_pfrowsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCfn_cf YD1w_cf YD1w_cf_fp YD1w_cf_br.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyTFIB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD1mcf YD1pcf ReplyTFIBBcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_top_x ReplyLSB ReplyRINVB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyKfMeterB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YG0dcfR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyRelroGeoB ReplyKeptAroStartB.
(* the zify flag as this file's own proofs expect it, whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Existing Instance YE2k.tfib_sink_head.
#[local] Existing Instance checksum_shape.

Section pl.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := tfibsegs.
Local Notation GF := (G_fr_c TfibB).
Local Notation ARX := (@W_LLVMFuzzerTestOneInput_top_x.ARX rc).
Local Notation ARC := (ARcf (ci := CfImg_B) (cp := CfParams_reply) tfibsegs TfibB).
Local Notation Goff a := (inGb GF (bv_unsigned (Z_to_bv 64 a)) = false).

Lemma drv_ARC_laws : AR_laws_x segs TfibB ARC (@cf_head CfParams_reply).
Proof. exact (AR_laws_x_cf (cp := CfParams_reply) segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)). Qed.

(* the program globals are image bytes *)
Lemma GF_img : forall a, inG GF a -> in_img segs a.
Proof. intros a Ha. exact (proj1 (@W_LLVMFuzzerTestOneInput_top_x.GX_ok rc a Ha)). Qed.

(* a word-range address off the image is off the globals *)
Lemma GF_off : forall a, 0 <= a < 2 ^ 64 -> ~ in_img segs a -> Goff a.
Proof.
  intros a Ha Hn. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  rewrite Z.mod_small by (cbn; lia). apply inGb_false. intros HG. exact (Hn (GF_img a HG)).
Qed.

Lemma drv_ceil : 0x7fff8000 <= alloc_ceiling < 2 ^ 64.
Proof. pose proof (@alloc_ceiling_val rc) as H. lia. Qed.

(* the five placement facts fr_post_bridge takes, at the pre state of a call *)
Lemma drv_HGP : forall a, in_img segs a -> ~ Exists (in_zr a) GF -> Goff a.
Proof.
  intros a Hi Hn. pose proof (tfib_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  rewrite Z.mod_small by (cbn; lia). apply inGb_false. exact Hn.
Qed.
Lemma drv_HGC : forall a, alloc_ceiling <= a < 2 ^ 64 -> Goff a.
Proof.
  intros a Ha. pose proof drv_ceil as Hc. apply GF_off; [lia|].
  intros Hi. pose proof (tfib_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl. lia.
Qed.
Lemma drv_HGB : forall ly S Hp (W : world segs) mem md, ARC ly S Hp W mem md ->
  forall p0 n0 i, In (p0, n0) (ablocks TfibB ly S) -> 0 <= i < req_size n0 -> Goff (p0 + i).
Proof.
  intros ly S Hp W mem md HA p0 n0 i Hin Hi.
  destruct (alx_blocks _ _ _ drv_ARC_laws ly S Hp W mem md p0 n0 HA Hin) as (_ & H4 & Hc & _).
  pose proof drv_ceil as Hc0. apply GF_off; [lia|].
  exact (blk_img_x segs TfibB ARC drv_ARC_laws ly S Hp W mem md p0 n0 (p0 + i) HA Hin ltac:(lia)).
Qed.
Lemma drv_HGF : forall ly S Hp (W : world segs) mem md, ARC ly S Hp W mem md ->
  forall cid pos a, In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  Goff a.
Proof.
  intros ly S Hp W mem md HA cid pos a Hin Hr.
  destruct (alx_sep _ _ _ drv_ARC_laws ly S Hp W mem md HA) as [_ HF].
  rewrite Forall_forall in HF. specialize (HF (cid, pos) Hin).
  cbn [fst snd] in HF. pose proof drv_ceil as Hc0.
  destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
  - apply GF_off; [lia|].
    exact (frm_img_x segs TfibB ARC drv_ARC_laws ly S Hp W mem md cid pos a HA Hin Hr).
  - unfold shadow_addr, SHADOW_OFF in Hr.
    pose proof (Z.div_mod (frame_addr ly cid pos) 8 ltac:(lia)) as D1.
    pose proof (Z.mod_pos_bound (frame_addr ly cid pos) 8 ltac:(lia)) as M1.
    pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as D2.
    pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)) as M2.
    apply GF_off; [lia|].
    intros Hi. pose proof (tfib_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl. lia.
Qed.
Lemma drv_HGE : forall ly S Hp (W : world segs) mem md, ARC ly S Hp W mem md ->
  forall a, Exists (in_zr a) (ly_extra ly) -> ~ (as_errno TfibB <= a < as_errno TfibB + 4) -> Goff a.
Proof.
  intros ly S Hp W mem md HA a Hx _.
  destruct (alx_extra _ _ _ drv_ARC_laws ly S Hp W mem md a HA Hx) as (_ & _ & _ & _ & Hni & _ & Happ).
  pose proof (app_addr_below_ceil a Happ) as Hb. unfold ASAN_CEIL in Hb. pose proof drv_ceil as Hc0.
  apply GF_off; [lia | exact Hni].
Qed.
End pl.

(* ---- the pre: the driver's call pre (AD1w_cf.v fr_lib_pre_drv) is W8's (cut_x fr_lib_pre_cf_x) at ARX: the ghost
   set is empty (the driver's `Hp = []`) and the RELRO bytes are the pre's last conjunct, so ARC is ARX (W1: ARX is
   ARcf /\ Hp = [] /\ arodata_ok_cf), and fr_LI is fr_gi with the call index ---- *)
Section br.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := tfibsegs.
Local Notation GF := (G_fr_c TfibB).
Local Notation ARX := (@W_LLVMFuzzerTestOneInput_top_x.ARX rc).
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables LIBROOM NP : astate -> Prop.

Lemma fr_pre_bridge : forall regs ly S Hp (W : world segs) mem md p n pl M ci0,
  fr_lib_pre_drv (ci := CfImg_B) (cp := CfParams_reply) TfibB MT XM_LIB RLO RHI LIBROOM NP regs ly S Hp W mem md p n pl M ci0 ->
  fr_lib_pre_cf_x TfibB MT XM_LIB RLO RHI fr_live_pre_b LIBROOM NP GF ARX regs ly S Hp W mem md p n pl M /\
  0 <= ci0 < 4.
Proof.
  intros regs ly S Hp W mem md p n pl M ci0
    ((HA & Hafn) & Hra & H10 & H11 & Hpn & Hlen & Hga & Hfr & Hp0 & Hlp & Hlr & Hnp & Hci & (_ & Hgi) & Hrv & Hro & Hsk
     & Hfd & Hsort & Hmeta & Hmo & Hstk & Hhb & Hxc & Hcap & Haro).
  split; [|exact Hci].
  refine (conj (conj (conj HA (conj Hp0 Haro)) Hafn) (conj Hra (conj H10 (conj H11 (conj Hpn (conj Hlen (conj Hga (conj Hfr
    (conj Hlp (conj Hlr (conj Hnp (conj Hgi (conj Hrv (conj Hro (conj Hsk (conj Hfd (conj Hsort (conj Hmeta
    (conj Hmo (conj Hstk (conj Hhb (conj Hxc Hcap)))))))))))))))))))))).
Qed.

(* ---- the contract: W8's at the driver's parameters gives the driver's program slot, at any world relation R (route
   R: cut_x's fr_lib_contract_cf_xR, whose library run can free, so its continuation gets only R W W'; the slot is
   YD1w_cf.v fr_lib_contract_drvR).  fr_drv_of_cf_x is its twin at wle. ---- *)
Theorem fr_drv_of_cf_xR : forall R : world segs -> world segs -> Prop,
  fr_lib_contract_cf_xR (fx := fx) (rc := rc) (SK := YE2k.tfib_sink_head) (LS := checksum_shape) TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre_b fr_live_post_b (fr_surv_b TfibB)
    LIBROOM NP GF fr_FP_b [] ARX R ->
  fr_lib_contract_drvR (fx := fx) (rc := rc) (LS := checksum_shape) (ci := CfImg_B) (cp := CfParams_reply) TfibB MT XM_LIB XN_LIB RLO RHI LIBROOM NP R.
Proof.
  intros R HC ly S Hp W regs mem md p n pl M K ci0 HAI Hpre HK.
  pose proof Hpre as ((HA & _) & _).
  destruct (fr_pre_bridge regs ly S Hp W mem md p n pl M ci0 Hpre) as [Hpx Hci].
  apply (HC ly S Hp W regs mem md p n pl M K HAI Hpx).
  intros l W' c' Hle HAI' (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & Hpost).
  apply (HK l W' c' Hle HAI'). exists ly', S', regs', mem', md', k. split; [exact Hc|].
  destruct Hpost as (HJ & Hlp & HNP & Hrp & Hr10 & Hsv & Hgi & Hrv & Hfd & Hfs & Hret & Hout & Hsort & Hsk & Hmeta
    & Hmo & Hin & Hhb' & Hxc' & Hcap').
  destruct HJ as (_ & _ & (memS & HJ & Hag) & _). rewrite !Z.add_0_r in HJ.
  (* the post's ARX at the return state (W1): ARcf, the empty ghost set and the RELRO bytes *)
  pose proof (proj1 HJ) as (HAR' & Hp'0 & Haro'). subst Hp'.
  eapply (fr_post_bridgeR (cp := CfParams_reply) TfibB MT XN_LIB NP).
  - exact drv_HGP.
  - exact drv_HGC.
  - exact (drv_HGB ly S Hp W mem md HA).
  - exact (drv_HGF ly S Hp W mem md HA).
  - exact (drv_HGE ly S Hp W mem md HA).
  - exact Hci.
  - exists memS. split; [exact (conj (conj HAR' eq_refl) (proj2 HJ)) | exact Hag].
  - exact Hlp.
  - exact HNP.
  - exact Hrp.
  - exact Hr10.
  - exact Hsv.
  - exact Hgi.
  - exact Hrv.
  - exact Hfd.
  - exact Hfs.
  - exact Hret.
  - exact Hout.
  - exact Hsort.
  - exact Hsk.
  - exact Hmeta.
  - exact Hmo.
  - exact Hin.
  - exact Hhb'.
  - exact Hxc'.
  - exact Hcap'.
  - exact Haro'.
Qed.
Theorem fr_drv_of_cf_x :
  fr_lib_contract_cf_x (fx := fx) (rc := rc) (SK := YE2k.tfib_sink_head) (LS := checksum_shape) TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre_b fr_live_post_b (fr_surv_b TfibB)
    LIBROOM NP GF fr_FP_b [] ARX ->
  fr_lib_contract_drv (fx := fx) (rc := rc) (LS := checksum_shape) (ci := CfImg_B) (cp := CfParams_reply) TfibB MT XM_LIB XN_LIB RLO RHI LIBROOM NP.
Proof. exact (fr_drv_of_cf_xR (@wle segs)). Qed.
End br.

(* ---- TFIB_B_T from W8's contract at the driver's parameters, for ANY meter MT with its per-call library budgets
   XM_LIB / XN_LIB and the meter's room at each call (MT_PRE of lib/B/YD1mcf.v; KF-COUNT #7 B, a Theorem Labs lane 09:33Z:
   generic in the meter, the instance picks MT_sec), at route R's relation wle' tfibsegs RZ_cf (the library run can
   free): LIBROOM := LIBROOM_fr, NP := room_live_cf (the cf instance's non-primary room, a8's laws under rl_param_ok,
   closed at CfParams_reply), the cf allocator's realizers (the free at the primed contract
   YG0dcfR.afree_realizes_cf_rh; the start-up covered range is closed inside lib/B/YD1pcf.v by YStkCov).
   ReplyTFIBBcf.v replyb_TFIB_B_T_of_cf_rl does the driver half.  The run count NS with its bound NRUN and per-call
   step bound XNMAX (MT_PRE's `NS S + XNMAX <= NRUN`,
   NS_MO, XN_BND of lib/B/YD1mcf.v, a Theorem Labs lane ddf9cf4d2f7), its steps at the driver's own mallocs and frees
   (nsec_malloc_cf / nsec_free_cf at NS) and the start budget NS_START at init_state (lib/B/YD2dcf.v, a Theorem Labs lane
   458a2b5da2a) are premises here, passed through.  Field rounds 2 and 3 (a Theorem Labs lane b63468a7a39 / edd47df3c77 on A):
   the conversion's two start witnesses (the two machine cells and Printf's two image cells, at the start-up hand-off)
   and the unit's image rows are plugged here (B/ReplyStartWitB.v start_cells_B / start_pf_B, B/ReplyImgRowsB.v
   exh_off_B / errb_obj_owned_B, a Theorem Labs lane's B/ReplyImg_pfrowsB.v errb_ial_apart_reply_B / pf_cells_owned_reply_B);
   the hull admission from the run count (HULL_NS, drv_pre's own conjunct) is a premise (part 3c: no memnorm);
   drv_pre's RELRO bytes are plugged here
   (relro_ok_B below, B/ReplyKeptAroStartB.v arodata_ho_B). ---- *)
(* field round 3 (Part A; part 3c): the cf driver's read-only image fact (B/YD1vcf.v relro_ok) at CfImg_B: the RELRO
   range and the five cf_ro_reads ranges each lie in one segment (ReplyRelroGeoB.relro_seg_reply_B) and below the
   driver's image windows (cf_relro_hi = 0x9f000 <= 0xa24f8, YD1ycf.DRVW_lo; the read ranges, ending by 0x20c00, by
   one vm_compute) *)
Lemma relro_ok_B : YD1vcf.relro_ok (ci := CfImg_B).
Proof. split; [exact ReplyRelroGeoB.relro_seg_reply_B | split; [cbn [cf_relro_hi CfImg_B]; lia | vm_compute; reflexivity]]. Qed.
Local Notation RLV := (@room_live_cf CfParams_reply).
Theorem replyb_tfib_b_of_top_x : forall (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (NS : astate -> Z) (NRUN XNMAX : Z),
  (forall S n, YG01cf.Wf_cf (cp := CfParams_reply) (as_universe TfibB) S -> qtight S -> blocks_bytes S <= DRV_LIVE -> RLV S ->
     NS S + XNMAX <= NRUN -> 0 <= n < 2 ^ 26 -> mo_ok MT S (XM_LIB n)) ->
  (forall S S' n, mo_le MT S S' (XN_LIB n) -> NS S' <= NS S + XN_LIB n) ->
  (forall n, 0 <= n < 2 ^ 26 -> 0 <= XN_LIB n <= XNMAX) ->
  (* field round 3: the call's hull admission from the run count's bound (ReplyTFIBBcf.v HULL_NS) *)
  (forall S, NS S <= NRUN -> @cf_hull_ok CfParams_reply S) ->
  (forall n tr s, YGcfXs.cfx_ipost (YG00cf.malloc_cf (ci := CfImg_B) n tr s)
     (fun r => NS (snd r) <= NS s + (if from_primary n then 0 else 1))) ->
  (forall p tr s, YGcfXs.cfx_ipost (YG00cf.free_cf p tr s) (fun r => NS (snd r) <= NS s)) ->
  NS init_state + 12 + 4 * XNMAX <= NRUN ->
  (* route R: W8's contract at R := wle' tfibsegs RZ_cf (cut_x fr_lib_contract_cf_xR: the library run can free, so
     its continuation gets only that relation); the driver runs at the same relation (B/YD1pcf.v Rcf) *)
  (forall (rc : YM05.RunCeil) (fx : YK11.FPState),
     fr_lib_contract_cf_xR (fx := fx) (rc := rc) (SK := YE2k.tfib_sink_head) (LS := checksum_shape) TfibB MT XM_LIB XN_LIB
       REPLYB_RO_LO REPLYB_RO_HI fr_live_pre_b fr_live_post_b (fr_surv_b TfibB) (LIBROOM_fr (cp := CfParams_reply)) RLV
       (G_fr_c TfibB) fr_FP_b [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc))) ->
  (forall (rc : YM05.RunCeil), @amalloc_realizes_cf YK11.fx0 rc CfImg_B CfParams_reply tfibsegs TfibB) ->
  (* ROW T (route R): the free at the primed contract, ReplyAllocTargetsB.afree_target_replyB's text at fx0 (primed at
     a Theorem Labs lane's 7c91d0cac15) *)
  (forall (rc : YM05.RunCeil), @YG0dcfR.afree_realizes_cf_rh YK11.fx0 rc CfImg_B CfParams_reply tfibsegs TfibB) ->
  (* field round 3 (part 3c: no memnorm): the hull admission is drv_pre's own conjunct, from the premise above, and
     drv_pre's RELRO bytes come from relro_ok_B and ReplyKeptAroStartB.arodata_ho_B *)
  TFIB_B_T.
Proof.
  intros MT XM XN NS NRUN XNMAX MP NSMO XNB HNS NSM NSF NSS TL AM AF.
  exact (@replyb_TFIB_B_T_of_cf_rl CfImg_B CfParams_reply reply_rl_param_ok MT XM XN NS NRUN XNMAX MP NSMO XNB HNS NSM NSF NSS
    (fun rc fx => @fr_drv_of_cf_xR fx rc MT XM XN REPLYB_RO_LO REPLYB_RO_HI _ RLV _ (TL rc fx)) AM AF
    (fun rc => ReplyStartWitB.start_cells_B) (fun rc => ReplyStartWitB.start_pf_B)
    (conj ReplyImgRowsB.exh_off_B (conj (ReplyImgRowsB.errb_obj_owned_B TfibB TfibB_syms)
       (ReplyImg_pfrowsB.errb_ial_apart_reply_B TfibB TfibB_syms)))
    (ReplyImg_pfrowsB.pf_cells_owned_reply_B TfibB TfibB_syms) relro_ok_B ReplyKeptAroStartB.arodata_ho_B).
Qed.
(* the corollary at KF-COUNT's meter MT_sec nsec KMAX, with the per-call library budget XN for both XM_LIB and XN_LIB
   and the run count NS := nsec at NRUN := KMAX, XNMAX := XN (A's reply_tfib_of_top_x_sec, a Theorem Labs lane 0d4f5b7d311): MT_PRE
   is MT_sec's own room, NS_MO its step, XN_BND `0 <= XN`; the count's steps at the driver's mallocs and frees and its
   start budget are premises (at the instance nsec := a Theorem Labs lane's nsec_cf, whose nsec_malloc_cf / nsec_free_cf prove them) *)
Section sec.
Theorem replyb_tfib_b_of_top_x_sec : forall (nsec : astate -> Z) (KMAX XN : Z),
  (forall n tr s, YGcfXs.cfx_ipost (YG00cf.malloc_cf (ci := CfImg_B) n tr s)
     (fun r => nsec (snd r) <= nsec s + (if from_primary n then 0 else 1))) ->
  (forall p tr s, YGcfXs.cfx_ipost (YG00cf.free_cf p tr s) (fun r => nsec (snd r) <= nsec s)) ->
  0 <= XN ->
  (* field round 3: the call's hull admission from the count's bound (at nsec := nsec_cf, KMAX := cf_kmax this is
     cf_hull_ok by conversion: YGcfAbudget.v section 6's reply instance) *)
  (forall S, nsec S <= KMAX -> @cf_hull_ok CfParams_reply S) ->
  nsec init_state + 12 + 4 * XN <= KMAX ->
  (* route R: W8's contract at R := wle' tfibsegs RZ_cf (cut_x fr_lib_contract_cf_xR: the library run can free, so
     its continuation gets only that relation); the driver runs at the same relation (B/YD1pcf.v Rcf) *)
  (forall (rc : YM05.RunCeil) (fx : YK11.FPState),
     fr_lib_contract_cf_xR (fx := fx) (rc := rc) (SK := YE2k.tfib_sink_head) (LS := checksum_shape) TfibB
       (ReplyKfMeterB.MT_sec nsec KMAX) (fun _ => XN) (fun _ => XN)
       REPLYB_RO_LO REPLYB_RO_HI fr_live_pre_b fr_live_post_b (fr_surv_b TfibB) (LIBROOM_fr (cp := CfParams_reply)) RLV
       (G_fr_c TfibB) fr_FP_b [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc))) ->
  (forall (rc : YM05.RunCeil), @amalloc_realizes_cf YK11.fx0 rc CfImg_B CfParams_reply tfibsegs TfibB) ->
  (* ROW T (route R): the free at the primed contract, ReplyAllocTargetsB.afree_target_replyB's text at fx0 (primed at
     a Theorem Labs lane's 7c91d0cac15) *)
  (forall (rc : YM05.RunCeil), @YG0dcfR.afree_realizes_cf_rh YK11.fx0 rc CfImg_B CfParams_reply tfibsegs TfibB) ->
  TFIB_B_T.
Proof.
  intros nsec KMAX XN NSM NSF HXN HHULL NSS TL AM AF.
  refine (replyb_tfib_b_of_top_x (ReplyKfMeterB.MT_sec nsec KMAX) (fun _ => XN) (fun _ => XN) nsec KMAX XN
    _ _ _ HHULL NSM NSF NSS TL AM AF).
  - intros S n _ _ _ _ H _. cbn [mo_ok ReplyKfMeterB.MT_sec]. exact H.
  - intros S S' n H. cbn [mo_le ReplyKfMeterB.MT_sec] in H. exact H.
  - intros n _. lia.
Qed.
End sec.
