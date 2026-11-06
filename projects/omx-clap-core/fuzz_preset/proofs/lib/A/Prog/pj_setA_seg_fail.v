(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: segment FAIL of pj_set's image-A' walk (fuzz_preset asan, A 0x8685c; the cuts of
   lib/A/Prog/pj_setA_defs.v): the refusal path both the grow branch (+0x78) and the strdup branch (+0x100) jump to,
   from PJSA_FAIL (+0x7c) to the epilogue PJSA_EPI.
     +0x7c  mv a0, s0        a0 := val
     +0x80  jal pj_free      tpj_free_specX CTX0 dd (lib/A/PRH_FnPj.v; the
                             POST-IMPLICATION form: no entry position, no run premise; it concludes at the re-hiding
                             relation, YA0nH.SRr' at RZ_cf over fpostWmR at WR) by YCbqGcallW.v aj_call_xWR at WR at
                             the callee window e1 = 48 + d (v = val <> 0, D = Dw, Lam = the arm's Lam2, F = val's free
                             order from its pj_fdR by PRH_PjOrder.v pj_fdR_foR); its room premise
                             (v <> 0 -> ccnt24 S <= L24 + DRV) is the cut's pjsA_PB S, its hull budget
                             (v <> 0 -> hull_budget S []) the cut's last conjunct, its head premise prh_head_wide is
                             pjsA_pre's cf_head = PresetReqAt.HEAD (pj_setA_defs.v pjsA_head_wide), its fpre's frm_zero
                             (fp_csr fx) the entry's (pjsA_pre's fpre: pj_set never changes the float state)
     +0x84  li a0, -1
   then pjsA_seg_epi (a premise). pj_free's text is CITED, never unfolded; its post is read BY NAME (its top-level
   conjunctions split and picked by type, pjsfA_split below).
   proves no function (kind: segment lemma). The three instructions are stepped concretely (the step lemmas of
   lib/A/Prog/pj_setA_steps.v, each plain stretch under YGcfRhLift.ra_rh_of_SRr: a step keeps the world); the cut is
   past grow, so its journal is at WR and the call is bound at WR (YSRrG.SRr'_bind); the frame is kept by
   pjsA_frame_kept_stmtR at WR; the call's own premises come from the cut, and its post (room_live_cf S', the position
   implication, unused here because the contract's third pj_set arm states no position, and Lam' with Lam2 ~ Dw ++ Lam') gives the
   third arm of pjsA_Q (the contract's post): Lam' = Lam3, so Lam3 ~ Do ++ Lr; the outcome cell prh_oks is the cut's, unchanged;
   the cut's failure is the CHOSEN one (cnt + (c - 1) = fail, every earlier outcome granted), so prh_granted ok cnt
   fail c holds and the refusal peak is 0 (PRH_Base.prh_refused_peak_granted): the peak cell is the cut's
   Z.max peak (lsum Lam2) with lsum Lam2 = lsum Lam3 + lsum Dw; res = -1, the run-position clause is vacuous
   (res <> 0), and both window clauses (the prh_granted one and DEAD-PJSET) are vacuous because the window
   contradicts cnt + (c - 1) = fail with 1 <= c <= |trace|; the object's pj_fdR is the cut's obligation. The memnorm
   keep composes: the cut's (pjsA_invR) with pj_free's fQmn keep.
   Numerals: 48 / 56 (LENGTH: frame, struct); 4 / 8 (DERIVED pc offsets); registers 0, 1, 8, 10 (WORD).
   No ADDRESS literal. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost YGcfRhLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA pj_setA_defs pj_setA_glue pj_setA_steps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_A.

Section fl. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := prh_img_A)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
#[local] Notation WR := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.

(* the top-level conjunctions of a hypothesis, split (in the shape of the unit's ec_conj_split): a callee post is
   read by picking its conjuncts BY TYPE after this, never by position *)
Local Ltac pjsfA_split H :=
  lazymatch type of H with
  | _ /\ _ =>
    let H1 := fresh "Ef" in let H2 := fresh "Ef" in destruct H as [H1 H2]; pjsfA_split H1; pjsfA_split H2
  | _ => idtac
  end.

Theorem pjsA_seg_fail_holds : forall CTX0 dd,
  pjsA_texts B ARx CTX0 dd -> pjsA_frame_kept_stmtR B ARx WR dd -> pjsA_seg_epi B ARx CTX0 dd ->
  pjsA_seg_fail B ARx CTX0 dd.
Proof.
intros CTX0 dd TXT KEEP HEPI en ly S Hp W regs mem md k HPRE HCUT.
destruct TXT as (_ & PJFREE & _ & _ & _ & _).
pose proof HPRE as HPRE0.
pose proof (@pa_segs_low _ A_prog_listing PA) as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold pjsA_pre in HPRE. cbv zeta in HPRE.
destruct HPRE as (HFPRE & HUNIV & HROOM0 & _ & _ & _ & _ & _ & _ & HFWIN & _ & _ & _ & _ & _ & _ & HWC & _ & _ & _ & _ &
  HDEPV & _ & _ & _ & HLED0 & _ & _ & _ & _ & _ & _ & HHEAD & _).
pose proof HFPRE as ((HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & Hqt0) & HROD0 & HSTKHI0 & _).
(* the kit-FRM0-ENTRY: the entry's rounding mode, which pj_free's fpre asks of the same fx *)
assert (HFRM : YK0o.frm_zero (@YK11.fp_csr fx)) by (destruct HFPRE as (_ & _ & _ & _ & H); exact H).
pose proof Hstk0 as (Hal0 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop0 & Htop20).
pose proof HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
destruct HCUT as (HINV & HROOM & Lam2 & peak2 & fail2 & ran2 & c & ok & Do & Lr & HLED & Hoks & Hfa & HpLam &
  HpLam2 & HBLK & HNI & Hcr & Hnth & Hbefore & Hchosen & Hpeak2 & HPB & HDold & HOBJ & HNODEW & HSLOTW & HHB).
pose proof HINV as (HJ & HWIN & Hsp & Hra & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & H8 & H18 & H20 & HKEPT & HPRES & HROD &
  HMN).
(* val's free order: its pj_fdR to depth dd (glue) has an order list F (the kit's PRH_PjOrder.v) *)
assert (HFDW : pj_fdR SEGS (mrestrict (w_H W) mem) (prh_lin Lam2) dd (jsA_w en) (jsA_Dw en)).
{ destruct pjsA_glue_holds as (Hfd & _).
  exact (Hfd SEGS (mrestrict (w_H W) mem) (prh_lin Lam2) (jsA_tv en) (jsA_w en) (jsA_Dw en) dd HNODEW HDEPV). }
destruct (PRH_PjOrder.pj_fdR_foR SEGS (mrestrict (w_H W) mem) (prh_lin Lam2) dd (jsA_w en) (jsA_Dw en) HFDW)
  as (Fw & HFOW).
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_ly HJ) as Hly.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HSTKF : 0 <= STK_pj_free dd) by (unfold STK_pj_free, zmaxl; cbn [fold_right];
  pose proof (pi_frame_nonneg F_pj_free); lia).
assert (HSTKB : STK_pj_free dd + 48 <= STK_pj_set dd).
{ unfold STK_pj_set, zmaxl. cbn [fold_right].
  replace (pi_frame F_pj_set) with 48 by (vm_compute; reflexivity). lia. }
assert (HW4096 : 4096 <= jsA_w en) by (destruct HSLOTW as (H & _); exact H).
assert (Hne0 : (jsA_w en =? 0) = false) by (apply Z.eqb_neq; lia).
set (FP1 := if jsA_w en =? 0 then [] else (jsA_w en, jsA_w en + 56) :: ablocks_fp (prhPj_hbl (jsA_Dw en))).
(* ======== +0x7c  mv a0, s0 ======== *)
unfold pjsA_cfg.
apply YGcfRhLift.ra_rh_of_SRr.
pjsA_fd PJSA_FAIL Hl1 Hd1.
eapply (pjsA_step_addi W regs mem md _ PJSA_FAIL _ _ _ _ (10%bv : bv 5) (getr regs (8%bv : bv 5)) Hl1 Hd1).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ lazymatch goal with |- v_addi (getr _ ?rs) (bv_signed ?im) = _ =>
    replace rs with (8%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
    replace (bv_signed im) with 0 by (vm_compute; reflexivity) end.
  unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. }
intros X1.
pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1 HJ) as HJ1.
replace (v_addi (Z_to_bv 64 (BASE + PJSA_FAIL)) 4) with (Z_to_bv 64 (BASE + (PJSA_FAIL + 4)))
  by (apply bv_eq; vm_compute; reflexivity).
(* ======== +0x80  jal pj_free ======== *)
pjsA_fd (PJSA_FAIL + 4) Hl2 Hd2.
eapply (pjsA_step_jal W _ mem _ _ (PJSA_FAIL + 4) _ _ _ (1%bv : bv 5) (Z_to_bv 64 (BASE + (PJSA_FAIL + 8)))
  (Z_to_bv 64 (@pa_sigma _ A_prog_listing PA AS_pj_free)) Hl2 Hd2).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X2.
pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X2 HJ1) as HJ2.
lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ =>
  remember r as regsc eqn:Eregsc; set (mdc := m) in * end.
assert (HSPC : spZ regsc = jsA_sp1 en).
{ unfold YG0d.spZ at 1. rewrite Eregsc, !getr_other by pjsA_regne. exact Hsp. }
assert (HS0LOW : s0Z regsc < YM05.alloc_ceiling).
{ unfold YG0d.s0Z. rewrite Eregsc, !getr_other by pjsA_regne. rewrite H8. unfold w64.
  rewrite unsigned_lit_small by lia. lia. }
assert (HGP : getr regsc 3 = w64 (as_gp B)).
{ rewrite Eregsc, !getr_other by pjsA_regne. rewrite (HKEPT 3%bv) by (unfold PJSA_KEPT; left; reflexivity). exact Hgp0. }
assert (HTP : getr regsc 4 = w64 (as_tp B)).
{ rewrite Eregsc, !getr_other by pjsA_regne. rewrite (HKEPT 4%bv) by (unfold PJSA_KEPT; right; left; reflexivity).
  exact Htp0. }
assert (HRA1 : getr regsc 1 = Z_to_bv 64 (BASE + (PJSA_FAIL + 8)))
  by (rewrite Eregsc; apply getr_same; pjsA_regne).
assert (HRAW : YK0s.ret_ok (Z_to_bv 64 (BASE + (PJSA_FAIL + 8)))).
{ apply (YC1fP.ret_ok_codeptr_v (PI := PA));
  [split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity | vm_compute; reflexivity]. }
assert (HRA4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + (PJSA_FAIL + 8))))
  by (apply Z.leb_le; vm_compute; reflexivity).
assert (HSPO : spZ regsc = jsA_sp0 en + jsA_d en + (- 48 - jsA_d en))
  by (rewrite HSPC; unfold jsA_sp1, PJSA_FR; lia).
(* ======== the call: pj_free's text at the callee window e1 = 48 + d, bound at WR ======== *)
apply SRr_ret. cbv beta.
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ eapply (aj_call_xWR (fx := fx) (SK := SK) SEGS B PST ARx LAWS Hsegs WR
    (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) W regsc mem
    (@pa_sigma _ A_prog_listing PA AS_pj_free)
    (STK_pj_set dd + jsA_d en) (jsA_sp0 en + jsA_d en) (pjsA_FP en)
    (jsA_ly en) (jsA_S en) (jsA_Hp en) (jsA_W en) (jsA_mem en) (jsA_md en) [] ly S Hp mdc k
    (STK_pj_free dd) (48 + jsA_d en) FP1 (- 48 - jsA_d en) (Z_to_bv 64 (BASE + (PJSA_FAIL + 8))) []
    _ HJ2 HSPO ltac:(lia) ltac:(lia) HSTKF ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    HGP HTP HRA1 HRAW HRA4 (achain_low _ _ _ _ HS0LOW)).
  - (* the callee: tpj_free_specX CTX0 dd (post-implication, no position) at d = 48 + d, v = val,
       D = Dw, F = Fw, Lam = Lam2 *)
    intros HPRE1 HWIN1. unfold fpostW_xR.
    eapply (PJFREE (jsA_most en) (jsA_own en) ly S Hp W regsc mem _ [] (48 + jsA_d en) (jsA_w en) (jsA_Dw en) Fw
      Lam2 peak2 (jsA_cnt en + Z.of_nat c) fail2 ran2).
    + split; [exact HPRE1|]. split; [exact HROD|].
      split; [rewrite HSPC, Eshi; unfold jsA_sp1, jsA_sp0, PJSA_FR; lia|].
      split; [|exact HFRM].
      (* the return address is the jal's own return pc, a text address below the ceiling *)
      unfold raZ. rewrite HRA1. eapply Z.lt_le_trans; [|apply (proj1 C1)]. apply Z.ltb_lt. vm_compute. reflexivity.
    + exact HUNIV.
    + exact HROOM.
    + (* the class-24 bound at entry: the cut's pjsA_PB *)
      intros _. exact HPB.
    + (* the hull budget at entry: the cut's *)
      intros _. exact HHB.
    + rewrite Eregsc, getr_other by pjsA_regne. rewrite getr_same by pjsA_regne. exact H8.
    + exact HWIN1.
    + right. split; [lia|]. split; [exact HWC|].
      split; [exact HFOW|].
      destruct HSLOTW as (H4096 & Hat & Hrw & Hamr & Hown & Hra' & Hhull).
      split; [exact H4096|].
      split.
      { destruct Hat as [Hb | [Hb | [Hb | (Hw1 & Hw2)]]];
        [left; exact Hb | right; left; exact Hb | right; right; left; exact Hb |].
        right; right; right. rewrite HSPC. unfold jsA_sp1, jsA_sp0, PJSA_FR. unfold jsA_sp0 in *. split; lia. }
      split; [exact Hrw|]. split; [exact Hamr|].
      split; [intros a Ha; split; [exact (proj1 (Hown a Ha))|];
              intros Hc; destruct (Hown a Ha) as (_ & Hn); apply Hn;
              rewrite HSPC in Hc; unfold jsA_sp1, jsA_sp0, PJSA_FR in *; lia|].
      split; [exact Hra' | exact Hhull].
    + (* the head is a word wide: pjsA_pre's cf_head = PresetReqAt.HEAD *)
      exact (pjsA_head_wide HHEAD).
    + exact HLED.
  - (* the footprint: val's header and its blocks are pj_set's own *)
    intros a Ha. unfold FP1 in Ha. rewrite Hne0 in Ha.
    change (inFP ((jsA_w en, jsA_w en + 56) :: ablocks_fp (prhPj_hbl (jsA_Dw en))) a) in Ha.
    apply inFP_cons in Ha. destruct Ha as [Ha | Ha].
    + left. exists (jsA_w en, jsA_w en + 56). split; [right; left; reflexivity | cbn [fst snd]; lia].
    + left. destruct Ha as (r & Hr & Hra'). exists r. split; [|exact Hra'].
      unfold pjsA_FP. right. right.
      unfold ablocks_fp, prhPj_hbl in Hr |- *. rewrite map_map in Hr |- *.
      apply in_map_iff in Hr as ((a' & k') & <- & Hin). apply in_map_iff. exists (a', k').
      split; [reflexivity | apply in_or_app; right; exact Hin]. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2' & HJc & HX & HP2 & HK).
unfold fQmn in HK. cbv beta in HK.
(* the contract's post, BY NAME: room, the position implication (unused: the contract's third pj_set arm states no position), then Lam3
   with its block move, its ledger and val's zeroed header *)
destruct HK as [HK HMNc]. pjsfA_split HK.
lazymatch goal with H : room_live_cf S2 |- _ => rename H into HROOM2 end.
lazymatch goal with H : exists L, Permutation Lam2 (jsA_Dw en ++ L) /\ @?Q L |- _ => destruct H as (Lam3 & HK3) end.
pjsfA_split HK3.
lazymatch goal with H : Permutation Lam2 (_ ++ Lam3) |- _ => rename H into HpF end.
lazymatch goal with H : Permutation (ablocks _ ly S) (prhPj_hbl _ ++ ablocks _ ly2 S2) |- _ =>
  rename H into HabF end.
lazymatch goal with H : prh_ledger _ ly2 S2 Hp2 W2 mem2 Lam3 _ _ _ _ _ _ |- _ => rename H into HLEDF end.
lazymatch goal with H : jsA_w en <> 0 -> pj_zeroR _ _ _ |- _ => rename H into HZ end.
(* ======== +0x84  li a0, -1 (a plain step) ======== *)
apply YGcfRhLift.ra_rh_of_SRr.
pjsA_fd (PJSA_FAIL + 8) Hl3 Hd3.
eapply (pjsA_step_addi W2 regs2 mem2 md2 _ (PJSA_FAIL + 8) _ _ _ _ (10%bv : bv 5) (w64 (-1)) Hl3 Hd3).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ lazymatch goal with |- v_addi (getr _ ?rs) (bv_signed ?im) = _ =>
    replace rs with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
    replace (bv_signed im) with (-1) by (vm_compute; reflexivity) end.
  rewrite getr_zero. unfold v_addi, w64. reflexivity. }
intros X3.
replace (v_addi (Z_to_bv 64 (BASE + (PJSA_FAIL + 8))) 4) with (Z_to_bv 64 (BASE + PJSA_EPI))
  by (apply bv_eq; vm_compute; reflexivity).
(* ======== the epilogue ======== *)
apply SRr_ret. cbv beta.
apply (HEPI en ly2 S2 Hp2 W2 (regupd regs2 (10%bv : bv 5) (w64 (-1))) mem2
  (with_vm_backing (m_vm_lazy md2) X3 md2) (k + k1) HPRE0).
(* what pj_set's frame keeps across the call *)
replace (jsA_sp0 en + jsA_d en + (- 48 - jsA_d en) + (48 + jsA_d en)) with (jsA_sp0 en + jsA_d en) in HJc, HX
  by (unfold jsA_sp1, jsA_sp0, PJSA_FR; lia).
replace (jsA_sp0 en + jsA_d en + (- 48 - jsA_d en)) with (jsA_sp1 en) in HX by (unfold jsA_sp1, PJSA_FR; lia).
assert (HSINK : ~ YI16.sink_open_fp FP1).
{ unfold FP1. rewrite Hne0.
  change (~ YI16.sink_open_fp ((jsA_w en, jsA_w en + 56) :: ablocks_fp (prhPj_hbl (jsA_Dw en)))).
  apply sink_closed_cons; [cbn [fst]; lia|]. apply sink_closed_pos. apply Forall_forall.
  intros r Hr. unfold ablocks_fp, prhPj_hbl in Hr. rewrite map_map in Hr.
  apply in_map_iff in Hr as ((a' & k') & <- & Hin). cbn [fst].
  assert (Hin2 : In (a', k') Lam2) by (eapply Permutation_in; [exact (Permutation_sym HpLam2)|];
    apply in_or_app; right; apply in_or_app; left; exact Hin).
  destruct (prh_ledger_hblock B ly S Hp W mem Lam2 peak2 (jsA_cnt en + Z.of_nat c) fail2 ran2 a' k'
    (jsA_most en) (jsA_own en) HLED Hin2)
    as (_ & Hab & _).
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HARc Hab) as (_ & H4096 & _). lia. }
assert (HFPFR : forall a, jsA_sp1 en <= a < jsA_sp0 en -> ~ inFP FP1 a).
{ intros a Ha Hin. unfold FP1 in Hin. rewrite Hne0 in Hin.
  change (inFP ((jsA_w en, jsA_w en + 56) :: ablocks_fp (prhPj_hbl (jsA_Dw en))) a) in Hin.
  apply inFP_cons in Hin. destruct Hin as [Hw | Hb].
  - destruct HSLOTW as (_ & _ & _ & _ & Hown & _). destruct (Hown a ltac:(lia)) as (_ & Hn).
    apply Hn. unfold jsA_sp1, jsA_sp0, PJSA_FR in *. lia.
  - destruct Hb as (r & Hr & Hra'). unfold ablocks_fp, prhPj_hbl in Hr. rewrite map_map in Hr.
    apply in_map_iff in Hr as ((a' & k') & <- & Hin). cbn [fst snd] in Hra'.
    assert (Hin2 : In (a', k') Lam2) by (eapply Permutation_in; [exact (Permutation_sym HpLam2)|];
      apply in_or_app; right; apply in_or_app; left; exact Hin).
    destruct (prh_ledger_hblock B ly S Hp W mem Lam2 peak2 (jsA_cnt en + Z.of_nat c) fail2 ran2 a' k'
      (jsA_most en) (jsA_own en) HLED Hin2)
      as (Hk0 & Hab & _).
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HARc Hab) as (_ & H4096 & Hcl & _).
    pose proof (@cf_head_nonneg cp) as Hh0.
    unfold jsA_sp1, jsA_sp0, PJSA_FR in *. lia. }
assert (HFPWIN : forall a, jsA_sp0 en <= a < jsA_sp0 en + jsA_d en -> ~ inFP (pjsA_FP en) a -> ~ inFP FP1 a).
{ intros a Ha Hnf Hin. apply Hnf. unfold FP1 in Hin. rewrite Hne0 in Hin.
  change (inFP ((jsA_w en, jsA_w en + 56) :: ablocks_fp (prhPj_hbl (jsA_Dw en))) a) in Hin.
  apply inFP_cons in Hin. destruct Hin as [Hw | Hb].
  - exists (jsA_w en, jsA_w en + 56). split; [right; left; reflexivity | cbn [fst snd]; lia].
  - destruct Hb as (r & Hr & Hra'). unfold ablocks_fp, prhPj_hbl in Hr. rewrite map_map in Hr.
    apply in_map_iff in Hr as ((a' & k') & <- & Hin).
    eexists. split; [|exact Hra'].
    unfold pjsA_FP. right. right. unfold ablocks_fp, prhPj_hbl. rewrite map_map.
    apply in_map_iff. exists (a', k'). split; [reflexivity | apply in_or_app; right; exact Hin]. }
destruct (KEEP en ly S Hp W regsc mem mdc k (STK_pj_free dd) FP1 ly2 S2 Hp2 W2 mem2 md2 k1
  ltac:(split; [exact HJ2|]; split; [exact HWIN|];
        split; [exact HSPC|]; split; [exact Hra|]; split; [exact Hs0|]; split; [exact Hs1|];
        split; [exact Hs2|]; split; [exact Hs3|]; split; [exact Hs4|];
        split; [rewrite Eregsc, !getr_other by pjsA_regne; exact H8|];
        split; [rewrite Eregsc, !getr_other by pjsA_regne; exact H18|];
        split; [rewrite Eregsc, !getr_other by pjsA_regne; exact H20|];
        split; [intros r Hr; rewrite Eregsc, !getr_other by pjsA_kept_ne; exact (HKEPT r Hr)|];
        split; [exact HPRES|]; split; [exact HROD | exact HMN])
  HJc HX HFPFR HFPWIN HSTKF Hd0 HSINK) as (KW & KRA & KS0 & KS1 & KS2 & KS3 & KS4 & KPR & KROD).
split.
- (* the invariant at the epilogue *)
  split; [exact (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X3 HJ2')|].
  split; [intros a Ha Hfp; rewrite <- (KW a Ha Hfp); reflexivity|].
  split; [unfold spZ at 1; rewrite getr_other by pjsA_regne;
          rewrite (pjsA_pres regsc regs2 (2%bv : bv 5) HP2 ltac:(pjsA_cs)); exact HSPC|].
  split; [exact KRA|]. split; [exact KS0|]. split; [exact KS1|]. split; [exact KS2|]. split; [exact KS3|].
  split; [exact KS4|].
  split; [rewrite getr_other by pjsA_regne; rewrite (pjsA_pres regsc regs2 (8%bv : bv 5) HP2 ltac:(pjsA_cs));
          rewrite Eregsc, !getr_other by pjsA_regne; exact H8|].
  split; [rewrite getr_other by pjsA_regne; rewrite (pjsA_pres regsc regs2 (18%bv : bv 5) HP2 ltac:(pjsA_cs));
          rewrite Eregsc, !getr_other by pjsA_regne; exact H18|].
  split; [rewrite getr_other by pjsA_regne; rewrite (pjsA_pres regsc regs2 (20%bv : bv 5) HP2 ltac:(pjsA_cs));
          rewrite Eregsc, !getr_other by pjsA_regne; exact H20|].
  split.
  { intros r Hr.
    assert (Hcs : acallee_saved (bv_unsigned r)).
    { unfold PJSA_KEPT in Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [pjsA_cs |]). destruct Hr. }
    rewrite getr_other by pjsA_kept_ne. rewrite (pjsA_pres regsc regs2 r HP2 Hcs).
    rewrite Eregsc, !getr_other by pjsA_kept_ne. exact (HKEPT r Hr). }
  split; [exact KPR|]. split; [exact KROD|].
  (* the memnorm keep: the cut's, then pj_free's (fQmn) *)
  intros Hm. exact (HMNc (HMN Hm)).
- (* the contract's post: the third arm, with val's blocks freed *)
  split; [exact HROOM2|].
  exists Lam3, peak2, fail2, ran2, (-1), c, ok, Lr, Do.
  split; [apply getr_same; pjsA_regne|].
  split; [exact HLEDF|].
  split; [exact Hoks|].
  split; [exact Hfa|].
  split; [exact HpLam|].
  split.
  { (* Lam3 ~ Do ++ Lr: pj_free took exactly Dw out of Lam2 *)
    apply (Permutation_app_inv_l (jsA_Dw en)).
    apply (Permutation_trans (Permutation_sym HpF)). apply (Permutation_trans HpLam2).
    rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
  split.
  { (* the allocator blocks: the arm's move, then pj_free's *)
    destruct HBLK as (other & Hb1 & Hb2). exists other. split; [exact Hb1|].
    apply (Permutation_app_inv_l (prhPj_hbl (jsA_Dw en))).
    apply (Permutation_trans (Permutation_sym HabF)).
    apply (Permutation_trans Hb2).
    rewrite app_assoc. unfold prhPj_hbl. rewrite <- map_app.
    apply Permutation_app_tail. apply Permutation_map. exact HpF. }
  split; [exact (HZ ltac:(lia))|].
  split; [intros Hres; discriminate Hres|].
  (* the chosen failure: cnt + (c - 1) = fail with 1 <= c <= |trace| lies inside the window, so both window clauses
     are vacuous *)
  assert (HWINF : ~ (jsA_fail en < jsA_cnt en \/
    jsA_cnt en + Z.of_nat (length (prhPj_set_trace (jsA_n en) (jsA_cap en) (jsA_kname en))) <= jsA_fail en)) by lia.
  split; [intros Hout; exfalso; exact (HWINF Hout)|].
  split; [intros Hout; exfalso; exact (HWINF Hout)|].
  right. right.
  split; [exact HNI|].
  split; [exact Hcr|]. split; [exact Hnth|]. split; [exact Hbefore|].
  split; [reflexivity|].
  split.
  { (* the peak cell: no refusal (the c-th outcome is the chosen failure, the earlier ones granted), so the refusal
       peak is 0 (prh_refused_peak_granted); pj_free gave Dw's bytes back, so the cut's sum lsum Lam2 is the final
       sum plus them *)
    assert (HGR : prh_granted ok (jsA_cnt en) (jsA_fail en) c).
    { intros i Hi Hf. destruct (Nat.lt_ge_cases i (c - 1)) as [Hlt | Hge].
      - rewrite (Hbefore i Hlt) in Hf. discriminate Hf.
      - replace i with (c - 1)%nat by lia. exact Hchosen. }
    rewrite (prh_refused_peak_granted _ _ _ _ _ HGR).
    assert (EL : Ledger.lsum Lam2 = Ledger.lsum Lam3 + Ledger.lsum (jsA_Dw en))
      by (rewrite (pjsA_lsum_perm Lam2 (jsA_Dw en ++ Lam3) HpF), pjsA_lsum_app; lia).
    pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HLED) as (Hlp & _).
    rewrite Hpeak2, <- EL. lia. }
  split; [exact HDold|].
  assert (HJcE : ajournal_xR (SK := SK) SEGS B PST ARx WR (STK_pj_free dd + (48 + jsA_d en)) (jsA_sp0 en + jsA_d en)
    ((jsA_w en, jsA_w en + 56) :: ablocks_fp (prhPj_hbl (jsA_Dw en))) ly S Hp W mem mdc [] ly2 S2 Hp2 W2 mem2 md2 k1).
  { unfold FP1 in HJc. rewrite Hne0 in HJc. exact HJc. }
  assert (HXE : forall a, jsA_sp1 en <= a < jsA_sp0 en + jsA_d en ->
    ~ inFP ((jsA_w en, jsA_w en + 56) :: ablocks_fp (prhPj_hbl (jsA_Dw en))) a ->
    aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
  { intros a Ha Hf. apply HX; [exact Ha|]. unfold FP1. rewrite Hne0. exact Hf. }
  destruct (HOBJ mdc ly2 S2 Hp2 W2 mem2 md2 k1 Lam3 HJcE HXE
    ltac:(apply (Permutation_app_inv_l (jsA_Dw en));
          apply (Permutation_trans (Permutation_sym HpF)); apply (Permutation_trans HpLam2);
          rewrite !app_assoc; apply Permutation_app_tail; apply Permutation_app_comm)) as (HFREE & HNODEo).
  split; [exact HFREE | exact HNODEo].
Qed.

End fl.
