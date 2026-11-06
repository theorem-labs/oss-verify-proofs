(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: segment C1 of pj_set's image-A' walk (fuzz_preset asan, A 0x8685c; the cuts of
   lib/A/Prog/pj_setA_defs.v): from the cut pjsA_C1 at the `jal pj_get` (+0x38) through pj_get's STATED text (the contract's
   tpj_get_specX, pjs_texts' first conjunct) to the cut pjsA_RET at the `beqz a0` (+0x3c), whose segment
   statement (pjsA_seg_ret) is a premise.
     +0x38  jal pj_get       (obj, key): YCbqGcallW.v aj_call_xW at the callee window e1 = 0, pj_get's m-form post
                             (fpostm = fpost of fQmn) read as fpostW_x by YCbqGcallW.v fpostW_x_of_apost (the core's
                             adapter, in the role of the handoff's pjs_fpost_W0)
   The callee's journal is widened to the caller's window (pj_setA_vis.v pjsA_aj_widen), so pj_setA_seg_epi.v's keep
   statement (pjsA_frame_kept_stmt) gives pj_set's frame; pj_get writes no footprint (FP = []), so the object's place,
   val's slot, the key (pj_setA_vis.v pjsA_datac_kept), val's tree (pjsA_tree_kept) and the object's header ride the
   callee's journal, and pj_get's post gives the object's tree, the ledger, the result and S' = S (RET's S = jsA_S en).
   The memnorm keep at RET is pjsA_inv's at C1 composed with fQmn's keep of pj_get's post.
   proves no function (kind: segment lemma).
   Numerals: 48 (LENGTH: pj_set's frame); 56 (LENGTH: the struct); 4 (DERIVED: the pc offset of the return);
   register numbers 1, 8, 9, 10, 11, 18, 20 (WORD). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YCbqGcall YCbqGcallW FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRhLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA pj_setA_defs pj_setA_glue pj_setA_steps pj_setA_vis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_set_trans.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_A.

Section c1. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := prh_img_A)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis VIS : pjsA_g_vis B ARx.

Theorem pjsA_seg_c1_holds : forall CTX0 dd,
  pjsA_texts B ARx CTX0 dd -> pjsA_frame_kept_stmt B ARx dd -> pjsA_seg_ret B ARx CTX0 dd ->
  pjsA_seg_c1 B ARx CTX0 dd.
Proof.
intros CTX0 dd TXT KEEP HRET en regs mem md k HPRE HCUT.
destruct TXT as (PJGET & _ & _ & _ & _ & _).
pose proof HPRE as HPRE0.
pose proof (@pa_segs_low _ A_prog_listing PA) as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as Hh0.
unfold pjsA_pre in HPRE. cbv zeta in HPRE.
destruct HPRE as (HFPRE & _ & _ & _ & _ & _ & _ & _ & _ & HFWIN & _ & _ & _ & _ & _ & _ & HWC & _).
pose proof HFPRE as ((_ & _ & _ & Hgp0 & Htp0 & Hstk0 & _ & _ & _) & _ & HSTKHI0).
(* the kit-FRM0-ENTRY: the entry's rounding mode, which every callee's fpre asks of the same fx *)
assert (HFRM : YK0o.frm_zero (@YK11.fp_csr fx)) by (destruct HFPRE as (_ & _ & _ & _ & H); exact H).
pose proof Hstk0 as (Hal0 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop0 & Htop20).
pose proof HFWIN as (Hd0 & Hd16 & Hdtop & _).
destruct HCUT as (HINV & HDATA & H10 & H11 & H9 & HNODE & HHDR & HNODEW & HAGR & HAGRW).
pose proof HINV as (HJ & HWIN & Hsp & Hra & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & H8 & H18 & H20 & HKEPT & HPRES & HROD & HMN).
destruct HDATA as (HROOM & HSLOTO & HSLOTW & HCS & HKA & HLED).
unfold jsA_sp0 in *.
assert (HSTKG : 0 <= STK_pj_get) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HSTKB : STK_pj_get + 48 <= STK_pj_set dd).
{ unfold STK_pj_set, zmaxl. cbn [fold_right].
  replace (pi_frame F_pj_set) with 48 by (vm_compute; reflexivity). lia. }
assert (HO4096 : 4096 <= jsA_o en) by (destruct HSLOTO as (H & _); exact H).
assert (HW4096 : 4096 <= jsA_w en) by (destruct HSLOTW as (H & _); exact H).
(* ======== +0x38  jal pj_get ======== *)
unfold pjsA_cfg.
(* C1 is before any free: the stretch and pj_get's call run plainly, the cut RET's SRr' statement takes the goal *)
apply YGcfRhLift.ra_rh_of_SRr.
pjsA_fd PJSA_C1 Hl1 Hd1.
eapply (pjsA_step_jal (jsA_W en) _ mem _ _ PJSA_C1 _ _ _ (1%bv : bv 5) (Z_to_bv 64 (BASE + PJSA_RET))
  (Z_to_bv 64 (@pa_sigma _ A_prog_listing PA AS_pj_get)) Hl1 Hd1).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X1.
pose proof (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1 HJ) as HJ1.
pose proof (ajx_ar HJ1) as HARc.
lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ =>
  remember r as regsc eqn:Eregsc; set (mdc := m) in * end.
assert (HSPC : spZ regsc = jsA_sp1 en).
{ unfold YG0d.spZ at 1. rewrite Eregsc, !getr_other by pjsA_regne. exact Hsp. }
assert (HS0LOW : s0Z regsc < YM05.alloc_ceiling).
{ unfold YG0d.s0Z. rewrite Eregsc, !getr_other by pjsA_regne. rewrite H8. unfold w64.
  rewrite unsigned_lit_small by lia. lia. }
assert (HGP : getr regsc 3 = w64 (as_gp B)).
{ rewrite Eregsc, !getr_other by pjsA_regne. rewrite (HKEPT 3%bv) by (unfold PJSA_KEPT; left; reflexivity).
  exact Hgp0. }
assert (HTP : getr regsc 4 = w64 (as_tp B)).
{ rewrite Eregsc, !getr_other by pjsA_regne. rewrite (HKEPT 4%bv) by (unfold PJSA_KEPT; right; left; reflexivity).
  exact Htp0. }
assert (HRA1 : getr regsc 1 = Z_to_bv 64 (BASE + PJSA_RET))
  by (rewrite Eregsc; apply getr_same; pjsA_regne).
assert (HRAW : YK0s.ret_ok (Z_to_bv 64 (BASE + PJSA_RET))).
{ apply (YC1fP.ret_ok_codeptr_v (PI := PA));
  [split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity | vm_compute; reflexivity]. }
assert (HRA4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + PJSA_RET)))
  by (apply Z.leb_le; vm_compute; reflexivity).
assert (HSPO : spZ regsc = spZ (jsA_regs en) + jsA_d en + (- 48 - jsA_d en))
  by (rewrite HSPC; unfold jsA_sp1, jsA_sp0, PJSA_FR; lia).
assert (Ea0 : getr regsc 10 = w64 (jsA_o en)) by (rewrite Eregsc, getr_other by pjsA_regne; exact H10).
assert (Ea1 : getr regsc 11 = w64 (jsA_k en)) by (rewrite Eregsc, getr_other by pjsA_regne; exact H11).
(* the object as pj_get reads it: a live block, a fake frame or the caller's real stack above sp *)
assert (HRSLOT : prhPj_rslot (PA := PA) B STK_pj_get (jsA_ly en) (jsA_S en) (jsA_W en) regsc mem (jsA_o en)).
{ destruct HSLOTO as (H4096 & Hat & _ & Hamr & Hown & Hra' & Hhull).
  split; [exact H4096|].
  split.
  { destruct Hat as [(a & kk & Hin & H1 & H2) | [(b & m & Hbm & _ & H1 & H2) | [Hf | (H1 & H2)]]].
    - left. pose proof HLED as (_ & _ & HLF & _).
      pose proof (proj1 (Forall_forall _ _) HLF (a, kk) Hin) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
      pose proof (pjsA_req (kk + @cf_head cp) ltac:(lia)) as (Rq & _).
      exists (a - cf_head), (kk + cf_head). split; [exact Hab | lia].
    - left. pose proof (pjsA_req m ltac:(lia)) as (Rq & _). exists b, m. split; [exact Hbm | lia].
    - right; left. exact Hf.
    - right; right. rewrite HSPC. unfold jsA_sp1, jsA_sp0, PJSA_FR. unfold jsA_sp0 in *. split; lia. }
  split; [exact Hamr|].
  split; [intros a Ha; rewrite HSPC; unfold jsA_sp1, jsA_sp0, PJSA_FR; intros Hc;
          apply (proj2 (Hown a Ha)); lia|].
  split; [exact Hra' | exact Hhull]. }
(* ======== the call: pj_get's text at the callee window e1 = 0 ======== *)
eapply SRr_bind.
{ eapply (aj_call_xW (fx := fx) (SK := SK) SEGS B PST ARx LAWS Hsegs (jsA_W en) regsc mem
    (@pa_sigma _ A_prog_listing PA AS_pj_get)
    (STK_pj_set dd + jsA_d en) (spZ (jsA_regs en) + jsA_d en) (pjsA_FP en)
    (jsA_ly en) (jsA_S en) (jsA_Hp en) (jsA_W en) (jsA_mem en) (jsA_md en) [] (jsA_ly en) (jsA_S en) (jsA_Hp en) mdc k
    STK_pj_get 0 [] (- 48 - jsA_d en) (Z_to_bv 64 (BASE + PJSA_RET)) []
    _ HJ1 HSPO ltac:(lia) ltac:(lia) HSTKG ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    HGP HTP HRA1 HRAW HRA4 (achain_low _ _ _ _ HS0LOW)).
  - intros HPRE1 _.
    eapply SRr_mono.
    + apply (PJGET (jsA_ly en) (jsA_S en) (jsA_Hp en) (jsA_W en) regsc mem mdc [] (jsA_o en) (jsA_k en) (jsA_kname en)
        (PjTree.JObj (jsA_ms en)) (jsA_D en) (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)).
      * split; [exact HPRE1|]. split; [exact HROD|].
        split; [rewrite HSPC; unfold jsA_sp1, jsA_sp0, PJSA_FR; lia|].
        split; [|exact HFRM].
        (* fpre's return-address bound, from the jal's own return pc (a listing literal) *)
        unfold YG0d.raZ. rewrite HRA1. pose proof (@YM05.alloc_ceiling_value rc) as [[ACm _] _].
        assert (EB : bv_unsigned (Z_to_bv 64 (BASE + PJSA_RET)) < 2 ^ 40)
          by (apply Z.ltb_lt; vm_compute; reflexivity).
        lia.
      * exact Ea0.
      * exact Ea1.
      * right. split; [exact HNODE | exact HRSLOT].
      * exact HCS.
      * exact HLED.
    + intros W' c' _ Hap. unfold fpostm in Hap.
      exact (fpostW_x_of_apost (SK := SK) SEGS B PST ARx STK_pj_get [] regsc (jsA_ly en) (jsA_S en) (jsA_Hp en)
        (jsA_W en) mem mdc _ W' c' Hap).
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2' & HJc & _ & HP2 & HK).
unfold fQmn in HK. cbv beta in HK.
destruct HK as ((EHp & ES2 & Eab & HLED2 & HROOMI & [(Ho0 & _) | (_ & HNODE2 & z & Hz & Hres)]) & HMN2);
  [exfalso; lia|].
replace (STK_pj_get + 0) with STK_pj_get in HJc by lia.
replace (spZ (jsA_regs en) + jsA_d en + (- 48 - jsA_d en) + 0) with (jsA_sp1 en) in HJc
  by (unfold jsA_sp1, jsA_sp0, PJSA_FR; lia).
(* the caller's window and pj_set's frame are present after the call (the walk's own journal) *)
pose proof (ajx_pres HJ2') as HPRES2.
assert (HPRW : forall a, jsA_sp1 en <= a < spZ (jsA_regs en) + jsA_d en -> apresent (w_H W2) mem2 a).
{ intros a Ha. apply HPRES2. pose proof HSTKB. unfold jsA_sp1, jsA_sp0, PJSA_FR in Ha. lia. }
(* the callee's journal at pj_set's widened window *)
destruct (pjsA_aj_widen B ARx STK_pj_get (jsA_sp1 en) [] (jsA_ly en) (jsA_S en) (jsA_Hp en) (jsA_W en) mem mdc []
  ly2 S2 Hp2 W2 mem2 md2 k1 (48 + jsA_d en) HJc ltac:(lia)
  ltac:(unfold astk_ok, jsA_sp1, jsA_sp0, PJSA_FR; repeat split; lia)
  ltac:(intros a Ha; apply HPRW; unfold jsA_sp1, jsA_sp0, PJSA_FR in *; lia)) as (HJcW & HXW).
replace (jsA_sp1 en + (48 + jsA_d en)) with (jsA_sp0 en + jsA_d en) in HJcW by (unfold jsA_sp1, jsA_sp0, PJSA_FR; lia).
destruct (KEEP en (jsA_ly en) (jsA_S en) (jsA_Hp en) (jsA_W en) regsc mem mdc k STK_pj_get [] ly2 S2 Hp2 W2 mem2 md2 k1
  ltac:(split; [exact HJ1|]; split; [exact HWIN|];
        split; [exact HSPC|]; split; [exact Hra|]; split; [exact Hs0|]; split; [exact Hs1|];
        split; [exact Hs2|]; split; [exact Hs3|]; split; [exact Hs4|];
        split; [rewrite Eregsc, !getr_other by pjsA_regne; exact H8|];
        split; [rewrite Eregsc, !getr_other by pjsA_regne; exact H18|];
        split; [rewrite Eregsc, !getr_other by pjsA_regne; exact H20|];
        split; [intros r Hr; rewrite Eregsc, !getr_other by pjsA_kept_ne; exact (HKEPT r Hr)|];
        split; [exact HPRES|]; split; [exact HROD | exact HMN])
  HJcW
  ltac:(intros a Ha Hf; apply HXW; [unfold jsA_sp1, jsA_sp0, PJSA_FR in *; lia | exact Hf])
  ltac:(intros a _ Hf; exact (inFP_nil a Hf))
  ltac:(intros a _ _ Hf; exact (inFP_nil a Hf))
  HSTKG Hd0 sink_closed_nil) as (KW & KRA & KS0 & KS1 & KS2 & KS3 & KS4 & KPR & KROD).
(* ======== the cut RET ======== *)
apply SRr_ret. cbv beta.
apply (HRET en ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) HPRE0).
(* the data after the call *)
assert (HDATA2 : pjsA_data_c B dd en ly2 S2 (jsA_Lam en) W2 mem2).
{ apply (pjsA_datac_kept B ARx LAWS VIS dd en (jsA_ly en) (jsA_S en) (jsA_Hp en) (jsA_W en) mem mdc
    (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en) STK_pj_get (jsA_sp1 en) [] ly2 S2 Hp2 W2 mem2 md2 k1
    (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en) HARc HJc HLED HLED2).
  - intros x Hx. exfalso. exact (inFP_nil x Hx).
  - exact sink_closed_nil.
  - intros x _ Hx. exact (inFP_nil x Hx).
  - unfold jsA_sp0. lia.
  - unfold jsA_sp0. lia.
  - intros a Ha. apply HPRW. unfold jsA_sp1, jsA_sp0, PJSA_FR in *. lia.
  - unfold jsA_sp0. lia.
  - intros a kk p _ Hin _ _. exact Hin.
  - intros b m p _ Hbm HnL _ _. rewrite Eab. split; [exact Hbm | exact HnL].
  - intros a kk Hin _ _. exact Hin.
  - exact (HROOMI HROOM).
  - split; [exact HROOM|]. split; [exact (pjsA_place_of_slot B dd en _ _ _ _ _ _ HSLOTO)|].
    split; [exact HSLOTW|]. split; [exact HCS | exact HKA]. }
assert (HSB : forall b m, In (b, m) (ablocks B (jsA_ly en) (jsA_S en)) -> In (b, m) (ablocks B ly2 S2))
  by (intros b m Hbm; rewrite Eab; exact Hbm).
split.
{ (* the invariant at RET *)
  split; [exact HJ2'|].
  split; [exact KW|].
  split; [rewrite (pjsA_pres_sp regsc regs2 HP2); exact HSPC|].
  split; [exact KRA|]. split; [exact KS0|]. split; [exact KS1|]. split; [exact KS2|]. split; [exact KS3|].
  split; [exact KS4|].
  split; [rewrite (pjsA_pres regsc regs2 (8%bv : bv 5) HP2 ltac:(pjsA_cs));
          rewrite Eregsc, !getr_other by pjsA_regne; exact H8|].
  split; [rewrite (pjsA_pres regsc regs2 (18%bv : bv 5) HP2 ltac:(pjsA_cs));
          rewrite Eregsc, !getr_other by pjsA_regne; exact H18|].
  split; [rewrite (pjsA_pres regsc regs2 (20%bv : bv 5) HP2 ltac:(pjsA_cs));
          rewrite Eregsc, !getr_other by pjsA_regne; exact H20|].
  split.
  { intros r Hr.
    assert (Hcs : acallee_saved (bv_unsigned r)).
    { unfold PJSA_KEPT in Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [pjsA_cs |]). destruct Hr. }
    rewrite (pjsA_pres regsc regs2 r HP2 Hcs). rewrite Eregsc, !getr_other by pjsA_kept_ne. exact (HKEPT r Hr). }
  split; [exact KPR|]. split; [exact KROD|].
  intros H0. exact (HMN2 (HMN H0)). }
split; [exact HDATA2|].
split; [exact HLED2|].
split; [exact Eab|].
split; [exact EHp|].
split; [exact ES2|].
split; [rewrite (pjsA_pres regsc regs2 (9%bv : bv 5) HP2 ltac:(pjsA_cs));
        rewrite Eregsc, !getr_other by pjsA_regne; exact H9|].
split; [exact HNODE2|].
split.
{ (* the object's header: pj_get writes no footprint *)
  destruct HDATA2 as (_ & (_ & _ & Hrw2 & _) & _).
  destruct HSLOTO as (_ & Hat & _).
  apply (pj_hdrR_frame SEGS (mrestrict (w_H (jsA_W en)) mem)); [exact HHDR|].
  apply (pjsA_agree (jsA_W en) W2 mem mem2).
  - intros x Hx. exact (pjsA_at_bytes B ARx (jsA_ly en) (jsA_S en) (jsA_Hp en) (jsA_W en) mem mdc STK_pj_get
      (jsA_sp1 en) [] ly2 S2 Hp2 W2 mem2 md2 k1 (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
      (jsA_regs en) (jsA_d en) (jsA_o en) HJc HLED ltac:(unfold jsA_sp1, jsA_sp0, PJSA_FR; lia) ltac:(lia)
      (fun b m Hbm _ _ => HSB b m Hbm) Hat x Hx (inFP_nil x)).
  - intros x Hx _. exact (proj2 Hrw2 x Hx). }
split.
{ (* val's tree *)
  destruct HDATA2 as (_ & _ & (_ & _ & Hrw2 & _) & _).
  destruct HSLOTW as (_ & Hat & _).
  apply (pjsA_tree_kept B ARx LAWS (jsA_ly en) (jsA_S en) (jsA_Hp en) (jsA_W en) mem mdc (jsA_Lam en) (jsA_peak en)
    (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en) STK_pj_get (jsA_sp1 en) [] ly2 S2 Hp2 W2 mem2 md2 k1
    (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en) (jsA_regs en) (jsA_d en) (jsA_w en) (jsA_tv en) (jsA_Dw en)
    HJc HLED HLED2 ltac:(unfold jsA_sp1, jsA_sp0, PJSA_FR; lia) ltac:(lia) (fun b m Hbm _ _ => HSB b m Hbm) Hat Hrw2).
  - intros a kk Hin. exact (pjst_node_lblk SEGS (jsA_tv en) _ _ _ _ HNODEW a kk Hin).
  - intros x _ Hx. exact (inFP_nil x Hx).
  - exact HNODEW. }
split.
{ (* the object's footprint: as at C1 (pj_get writes no footprint), so as at the entry *)
  pose proof HDATA2 as (_ & (_ & _ & Hrw2 & _) & _).
  pose proof HSLOTO as (_ & Hat & _).
  pose proof (ajx_ar HJc) as HAR2.
  pose proof HLED2 as (_ & _ & HLF2 & _).
  apply (pjsA_agree_trans _ (mrestrict (w_H (jsA_W en)) mem)); [exact HAGR|].
  apply (pjsA_agree (jsA_W en) W2 mem mem2).
  - intros x [Hx | ((a, kk) & Hb & Hx)].
    + exact (pjsA_at_bytes B ARx (jsA_ly en) (jsA_S en) (jsA_Hp en) (jsA_W en) mem mdc STK_pj_get
        (jsA_sp1 en) [] ly2 S2 Hp2 W2 mem2 md2 k1 (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
        (jsA_regs en) (jsA_d en) (jsA_o en) HJc HLED ltac:(unfold jsA_sp1, jsA_sp0, PJSA_FR; lia) ltac:(lia)
        (fun b m Hbm _ _ => HSB b m Hbm) Hat x Hx (inFP_nil x)).
    + pose proof (pjst_node_lblk SEGS _ _ _ _ _ HNODE a kk Hb) as HinL. unfold prh_lin in HinL.
      unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
      exact (pjsA_lam_bytes B ARx (jsA_ly en) (jsA_S en) (jsA_Hp en) (jsA_W en) mem mdc STK_pj_get (jsA_sp1 en) []
        ly2 S2 Hp2 W2 mem2 md2 k1 (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
        (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en) a kk x HJc HLED HLED2 HinL HinL Hx (inFP_nil x)).
  - intros x [Hx | ((a, kk) & Hb & Hx)] _.
    + exact (proj2 Hrw2 x Hx).
    + pose proof (pjst_node_lblk SEGS _ _ _ _ _ HNODE a kk Hb) as HinL. unfold prh_lin in HinL.
      unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
      pose proof (proj1 (Forall_forall _ _) HLF2 (a, kk) HinL) as (Hk0 & Hab2 & _). cbn [fst snd] in Hk0, Hab2.
      pose proof (pjsA_req (kk + @cf_head cp) ltac:(lia)) as (Rq & _).
      exact (pjsA_blk_writable B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ x HAR2 Hab2 ltac:(lia)). }
split.
{ (* val's footprint: as at C1 (pj_get writes no footprint), so as at the entry *)
  pose proof HDATA2 as (_ & _ & (_ & _ & Hrw2 & _) & _).
  pose proof HSLOTW as (_ & Hat & _).
  pose proof (ajx_ar HJc) as HAR2.
  pose proof HLED2 as (_ & _ & HLF2 & _).
  apply (pjsA_agree_trans _ (mrestrict (w_H (jsA_W en)) mem)); [exact HAGRW|].
  apply (pjsA_agree (jsA_W en) W2 mem mem2).
  - intros x [Hx | ((a, kk) & Hb & Hx)].
    + exact (pjsA_at_bytes B ARx (jsA_ly en) (jsA_S en) (jsA_Hp en) (jsA_W en) mem mdc STK_pj_get
        (jsA_sp1 en) [] ly2 S2 Hp2 W2 mem2 md2 k1 (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
        (jsA_regs en) (jsA_d en) (jsA_w en) HJc HLED ltac:(unfold jsA_sp1, jsA_sp0, PJSA_FR; lia) ltac:(lia)
        (fun b m Hbm _ _ => HSB b m Hbm) Hat x Hx (inFP_nil x)).
    + pose proof (pjst_node_lblk SEGS _ _ _ _ _ HNODEW a kk Hb) as HinL. unfold prh_lin in HinL.
      unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
      exact (pjsA_lam_bytes B ARx (jsA_ly en) (jsA_S en) (jsA_Hp en) (jsA_W en) mem mdc STK_pj_get (jsA_sp1 en) []
        ly2 S2 Hp2 W2 mem2 md2 k1 (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
        (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en) a kk x HJc HLED HLED2 HinL HinL Hx (inFP_nil x)).
  - intros x [Hx | ((a, kk) & Hb & Hx)] _.
    + exact (proj2 Hrw2 x Hx).
    + pose proof (pjst_node_lblk SEGS _ _ _ _ _ HNODEW a kk Hb) as HinL. unfold prh_lin in HinL.
      unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
      pose proof (proj1 (Forall_forall _ _) HLF2 (a, kk) HinL) as (Hk0 & Hab2 & _). cbn [fst snd] in Hk0, Hab2.
      pose proof (pjsA_req (kk + @cf_head cp) ltac:(lia)) as (Rq & _).
      exact (pjsA_blk_writable B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ x HAR2 Hab2 ltac:(lia)). }
exists z. split; [exact Hz | exact Hres].
Qed.
End c1.
