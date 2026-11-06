(* The image-A DRIVER_CF plug for plugin-hostd/fuzz_reply.asan: TFIB_T (lib/A/ReplyTFIB.v) from W8's ARx-generic entry
   composition at the cf instance (lib/A/W_LLVMFuzzerTestOneInput_top_x.v fr_contract_top_x: cut_x's
   fr_lib_contract_cf_x at ARx := ARX = ARcf /\ Hp = [], PST := [], G := G_fr_c TfibB), through the cf driver
   (lib/A/ReplyTFIBcf.v, whose program slot is lib/A/AD1w_cf.v fr_lib_contract_drv).
   ReplyATop.v's DRIVER_CF is stated over W8's AR-form contract (W_LLVMFuzzerTestOneInput_cut.v fr_lib_contract_cf),
   which the cf driver does not consume; the route here replaces it.  Three parts:
   - the five placement facts of the post bridge (AD1w_cf_br.v fr_post_bridge, ATopKeeper): the program globals
     G_fr_c TfibB are image bytes (GX_ok), and every place the journal's kept clauses read the start memory (the
     space above alloc_ceiling, a live block, a live frame or its shadow, an extra range) is off the image (ARcf's laws
     at the pre state, and tfib_segs_low for the shadow);
   - fr_pre_bridge: the driver's pre (fr_lib_pre_drv) is W8's pre (fr_lib_pre_cf_x) at ARX, LIBROOM, NP, the
     harness-block clause (HB, cut.v:193) included; the post's HB (cut.v:207) passes to the driver's post;
   - fr_drv_of_cf_xR: the contract bridge (any meter, any world relation R: cut_x's fr_lib_contract_cf_xR to the
     driver's fr_lib_contract_drvR; fr_drv_of_cf_x is its twin at wle), and reply_tfib_of_top_x_sec: TFIB_T from W8's
     contract at route R's relation wle' tfibsegs RZ_cf (the library run can free), at KF-COUNT's meter
     ReplyKfMeter.MT_sec nsec KMAX (both per-call budgets one constant XN) and the driver's parameters
     (ACfn_cf.v's fr_live_pre / fr_live_post / fr_surv / fr_FP, LIBROOM_fr, NP := room_live_cf), the cf allocator's
     realizers (the free at the primed contract YG0dcfR.afree_realizes_cf_rh), the hull admission from the count's
     bound and drv_pre's read-only facts at CfImg_A (relro_ok_A, ReplyKeptAroStart.arodata_ho_A; a Theorem Labs lane's part 3c: no
     memnorm fact);
     the start-up covered range is closed by a Theorem Labs lane's AStkCov.entry_stk_cov (reply_handoff_cov).
     rl_param_ok is CfParamsReply.reply_rl_param_ok.
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0ncf YGcfNames YCbqG YG0lawscf YGcallcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp YM05 YG0dcf YGcfRoomLive.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn ACeg AD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_cut_x W_LLVMFuzzerTestOneInput_G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfImgA CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyStartWitA ReplyImgRowsA ReplyImg_pfrows.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn_cf AD1w_cf AD1w_cf_fp AD1w_cf_br.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyTFIB AD1mcf AD1pcf ReplyTFIBcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_top_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AStkCov.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyImg_pfrows.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyKfMeter ReplyLSsec ReplyKfC.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YG0dcfR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfRehidePost.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyRelroGeoA ReplyKeptAroStart.
(* the zify flag as this file's own proofs expect it, whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Existing Instance AE2k.tfib_sink_head.
#[local] Existing Instance checksum_shape.

Section pl.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := tfibsegs.
Local Notation GF := (G_fr_c TfibB).
Local Notation ARX := (@W_LLVMFuzzerTestOneInput_top_x.ARX rc).
Local Notation ARC := (ARcf (ci := CfImg_A) (cp := CfParams_reply) tfibsegs TfibB).
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
  fr_lib_pre_drv (ci := CfImg_A) (cp := CfParams_reply) TfibB MT XM_LIB RLO RHI LIBROOM NP regs ly S Hp W mem md p n pl M ci0 ->
  fr_lib_pre_cf_x TfibB MT XM_LIB RLO RHI fr_live_pre LIBROOM NP GF ARX regs ly S Hp W mem md p n pl M /\
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
   AD1w_cf.v fr_lib_contract_drvR).  fr_drv_of_cf_x is its twin at wle. ---- *)
Theorem fr_drv_of_cf_xR : forall R : world segs -> world segs -> Prop,
  @fr_lib_contract_cf_xR fx rc checksum_shape TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post (fr_surv TfibB)
    LIBROOM NP GF fr_FP [] ARX R ->
  @fr_lib_contract_drvR fx rc checksum_shape CfImg_A CfParams_reply TfibB MT XM_LIB XN_LIB RLO RHI LIBROOM NP R.
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
  @fr_lib_contract_cf_x fx rc checksum_shape TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post (fr_surv TfibB)
    LIBROOM NP GF fr_FP [] ARX ->
  @fr_lib_contract_drv fx rc checksum_shape CfImg_A CfParams_reply TfibB MT XM_LIB XN_LIB RLO RHI LIBROOM NP.
Proof. exact (fr_drv_of_cf_xR (@wle segs)). Qed.
End br.

(* ---- TFIB_T from W8's contract at ReplyATopX.v's parameters: LIBROOM := LIBROOM_fr, NP := room_live_cf (the cf
   instance's non-primary room, a8's laws under rl_param_ok, closed at CfParams_reply), the cf allocator's realizers;
   the start-up covered range is reply_handoff_cov.  ReplyTFIBcf.v reply_TFIB_T_of_cf_rl does the driver half. ---- *)
(* the start-up covered range (AD1pcf.v handoff_cov) is a Theorem Labs lane's AStkCov.entry_stk_cov (B4a, a working branch
   f9031cc9018, file taken by path): the same statement *)
Lemma reply_handoff_cov : handoff_cov.
Proof.
  intros sp rdraw brk inp h ch E R FULL model Hsp Hva Hve Hfit Hch HC HE HM a Ha.
  exact (AStkCov.entry_stk_cov sp rdraw brk inp Hsp Hva Hve Hfit h ch E R FULL model Hch HC HE HM a Ha).
Qed.

(* field round 3 (Part A; part 3c): the cf driver's read-only image fact (A/AD1vcf.v relro_ok) at CfImg_A: the RELRO
   range and the five cf_ro_reads ranges each lie in one segment (ReplyRelroGeoA.relro_seg_reply_A) and below the
   driver's image windows (cf_relro_hi = 0x9f000 <= 0xa1f78, AD1ycf.DRVW_lo; the read ranges, ending by 0x20c00, by
   one vm_compute) *)
Lemma relro_ok_A : AD1vcf.relro_ok (ci := CfImg_A).
Proof. split; [exact ReplyRelroGeoA.relro_seg_reply_A | split; [cbn [cf_relro_hi CfImg_A]; lia | vm_compute; reflexivity]]. Qed.
Local Notation RLV := (@room_live_cf CfParams_reply).
(* ---- TFIB_T at the counting meter MT := ReplyKfMeter.MT_sec nsec KMAX (KF-COUNT #6 / #7), with both per-call
   budgets XM_LIB = XN_LIB := fun _ => XN, the run count NS := nsec, its bound NRUN := KMAX and its per-call step
   XNMAX := XN.  The driver's call room MT_PRE (A/AD1mcf.v, premise NS S + XNMAX <= NRUN) is then its own conclusion
   (mo_ok MT_sec S XN is nsec S + XN <= KMAX), and NS_MO is mo_le MT_sec itself.  What stays a premise: the count's
   two step facts at the driver's own mallocs / frees (A/CfRBridgeRules.v's texts at nsec; YGcfNsec proves them at
   nsec_cf), 0 <= XN, and the start budget NS_START at init_state (A/AD2dcf.v), here with NRUN := KMAX. ---- *)
Section sec.
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_reply.
Theorem reply_tfib_of_top_x_sec : forall (nsec : astate -> Z) (KMAX XN : Z),
  (forall n tr s,
     YGcfXs.cfx_ipost (YG00cf.malloc_cf n tr s) (fun r => nsec (snd r) <= nsec s + (if from_primary n then 0 else 1))) ->
  (forall p tr s, YGcfXs.cfx_ipost (YG00cf.free_cf p tr s) (fun r => nsec (snd r) <= nsec s)) ->
  0 <= XN ->
  (* field round 3: the call's hull admission from the count's bound (at nsec := nsec_cf, KMAX := cf_kmax this is
     cf_hull_ok by conversion: YGcfAbudget.v section 6's reply instance) *)
  (forall S, nsec S <= KMAX -> cf_hull_ok S) ->
  nsec init_state + 12 + 4 * XN <= KMAX ->
  (* route R: W8's contract at R := wle' tfibsegs RZ_cf (cut_x fr_lib_contract_cf_xR: the library run can free, so
     its continuation gets only that relation); the driver runs at the same relation (A/AD1pcf.v Rcf) *)
  (forall (rc : YM05.RunCeil) (fx : YK11.FPState),
     @fr_lib_contract_cf_xR fx rc checksum_shape TfibB (ReplyKfMeter.MT_sec nsec KMAX) (fun _ => XN) (fun _ => XN)
       REPLY_RO_LO REPLY_RO_HI fr_live_pre fr_live_post (fr_surv TfibB) (LIBROOM_fr (cp := CfParams_reply)) RLV
       (G_fr_c TfibB) fr_FP [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc))) ->
  (forall (rc : YM05.RunCeil), @amalloc_realizes_cf YK11.fx0 rc CfImg_A CfParams_reply tfibsegs TfibB) ->
  (* ROW T (route R): the free at the primed contract, ReplyAllocTargets.afree_target_reply's text at fx0 *)
  (forall (rc : YM05.RunCeil), @YG0dcfR.afree_realizes_cf_rh YK11.fx0 rc CfImg_A CfParams_reply tfibsegs TfibB) ->
  TFIB_T.
Proof.
  intros nsec KMAX XN NSM NSF HXN HHULL NSS TL AM AF. pose proof reply_handoff_cov as HS.
  refine (@reply_TFIB_T_of_cf_rl CfImg_A CfParams_reply reply_rl_param_ok (ReplyKfMeter.MT_sec nsec KMAX)
    (fun _ => XN) (fun _ => XN) nsec KMAX XN _ _ _ HHULL NSM NSF NSS
    (fun rc fx => @fr_drv_of_cf_xR fx rc (ReplyKfMeter.MT_sec nsec KMAX) (fun _ => XN) (fun _ => XN)
       REPLY_RO_LO REPLY_RO_HI _ RLV _ (TL rc fx)) AM AF HS
    (fun rc => ReplyStartWitA.start_cells_A)
    (fun rc => ReplyStartWitA.start_pf_A)
    (conj ReplyImgRowsA.exh_off_A (conj (ReplyImgRowsA.errb_obj_owned_A TfibB TfibB_syms)
      (ReplyImg_pfrows.errb_ial_apart_reply_A TfibB TfibB_syms)))
    (ReplyImg_pfrows.pf_cells_owned_reply_A TfibB TfibB_syms) relro_ok_A ReplyKeptAroStart.arodata_ho_A).
  - intros S n _ _ _ _ H _. cbn [mo_ok ReplyKfMeter.MT_sec]. exact H.
  - intros S S' n H. cbn [mo_le ReplyKfMeter.MT_sec] in H. exact H.
  - intros n _. lia.
Qed.
End sec.

(* FIT CHECK, at the strict relation: W8's fr_contract_top_x concludes the text of reply_tfib_of_top_x_sec's contract
   premise at R := wle (fr_lib_contract_cf_x = fr_lib_contract_cf_xR wle, cut_x's _wle lemma) and ReplyATopX.v's
   parameters (MT_sec nsec KMAX, XM_LIB = XN_LIB := SEC_CALL KF_KC, ReplyTFIBcf's read-only range, ACfn_cf.v's
   definitions, LIBROOM_fr, room_live_cf); the premise itself is at R := wle' tfibsegs RZ_cf, which top_x at route R
   concludes.  The eapply fails if the two texts differ. *)
Goal forall (nsec : astate -> Z) (KMAX : Z) (rc : YM05.RunCeil) (fx : YK11.FPState),
  @fr_lib_contract_cf_x fx rc checksum_shape TfibB (ReplyKfMeter.MT_sec nsec KMAX)
    (fun _ => ReplyLSsec.SEC_CALL ReplyKfC.KF_KC) (fun _ => ReplyLSsec.SEC_CALL ReplyKfC.KF_KC) REPLY_RO_LO REPLY_RO_HI
    fr_live_pre fr_live_post (fr_surv TfibB) (LIBROOM_fr (cp := CfParams_reply)) RLV (G_fr_c TfibB) fr_FP []
    (@W_LLVMFuzzerTestOneInput_top_x.ARX rc).
Proof. intros nsec KMAX rc fx. eapply W_LLVMFuzzerTestOneInput_top_x.fr_contract_top_x. Abort.
