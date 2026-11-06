(* fuzz_preset, slice S5b, lane A2Loop (a Theorem Labs lane, 2026-10-30): the ASSEMBLY of parse_items (image A, the ASan build;
   entry VrdIPro.PI_ENTRY) against the RECORD text lib/A/PRH_FnParse.v (the kit's cut 7cdbb61b5fa0, blob f0d92dcec7e9):
   parse_items' text at
   nesting d from parse_value's text at d + 1, and the depth boundary.
   rule 24: proves no function (kind: segment lemma). The function's segments are other lanes' lemmas; this file
   composes them and states every step it does not prove as a named Section hypothesis.

   THE COMPOSITION (port of the SHAPE of the released plain build's lib/Prog/parse_items.v / ParseUnit.v, none of
   their image facts):
   - the prologue, VrdIPro.v vrd_ipro_ok_inv (lane A2Ipro): from the text's premises (vrd_ipre, the text's premises
     verbatim) parse_items reaches the loop head vrd_ielem_a (VrdIElem.v) at a call chain ch2 it chooses, or returns
     with the text's post body (vrd_ipost = fpostWFb at the budget wbudget CW 0 at VrdIElem.vrd_items_q);
   - the loop (vrd_iloop_run): from the loop head the four step Props of VrdIElem.v in their _G form - the key path
     (tvrd_ikey_aG), the element step with the parse_value call (tvrd_ival_aG), the capacity step (tvrd_igrow_aG) back
     to the loop head with one more element, and the epilogue (tvrd_iexit_aG) from every exit - by YSRrG.SRr'_loop on
     the measure 2 ^ 54 - ip_n (vrd_inode: ip_cap <= 2 ^ 54; the loop head: ip_n < ip_cap; ikey and igrow keep ip_n,
     ival adds 1);
   - the memory invariant (a Theorem Labs lane's GENERIC INVARIANT rule, 2026-10-29T12:19Z): REASON, quoted as that rule asks:
     "an SRr post is opaque once Qed, so an end-state memory invariant must be in the segment's STATEMENT; the generic
     SRr_memnorm was measured NOT provable (a Theorem Labs lane), so it cannot be added afterwards." Every segment above is
     generic in Pm; it is instantiated ONCE, here, as `fun m => memnorm segs mem -> memnorm segs m` (the entry memory
     mem), with its laws from YSRrMemnorm.v (srr_inv_laws_imp over srr_inv_laws_memnorm_k, srr_inv_call_imp, and
     srr_inv_mn_imp from the text's entry memnorm premise). Pm of the returned memory is then exactly fQmn's keep, so
     the budgeted post fpostWFb becomes the text's fpostWFbm (vrd_fpostWFbm_of; the kit's cut).

   THE CONTEXT LIST. The loop runs at the call's OWN context list vrd_ictx regs ch ch2 (VrdIPro.v
   vrd_ient_ok_of_ipre, from vrd_ipre at ANY list): the row-231 parse_value call is at `A_IPC 6164 :: spine ch2`,
   with ch2 the chain at the cursor the prologue produces, and tparse_items_specX says nothing of it beyond
   `In (raZ regs :: spine ch) CTX`. So vrd_items_at takes parse_value's text at EVERY context list and gives
   parse_items' text at every context list. Every proof of the four step Props is `forall CTX`, so the Section takes
   them at every list.

   No Axiom, Parameter, admitted proof or Abort; no Hypothesis outside a Section. No numeral that is an address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i
YCbn YP0b YP0a YN3v YI04 YG0s YP07 YI00 YI16 YK04 YA0i YA0n YA0o YCbm YA0q YG0v YG00 YG0a YG01 YG0f YG0n YG0d YCbq
YM05 YG0p YK06 YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP YCbqG YC80x YC1fPx YC80xf YGcfNames YGcfRoomPre YGcfRoomKeep
YG0dcf YN0d YSRrMemnorm YC80xf_inv.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
(* the re-hiding move's SRr' and its loop and bind rules (YA0nH, YSRrG), preset's zone (YGcfRehidePost.RZ_cf); the
   text's hull budget premise *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Img PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse VrdIElem VrdIPro.
(* for the check-1 section at the end only: the four step proofs and the real instance (qualified, not imported) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnAlloc CfParamsPreset VrdPro VrdIStep VrdIVal
  VrdIKeyB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* VrdIPro.v loads PRW_StepKit, whose YF0v.v sets Zify's euclidean-division flag off GLOBALLY (VrdIPro.v :90-92) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section l.
Context {rc : YM05.RunCeil} {fx : YK11.FPState} {ci : CfImg} {cp : CfParams} {PIm : PrhImg} {RL : PrhRoomLive}.
#[local] Abbreviation segs := (@pa_segs _ _ PI_prog_A).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {HL : Z}.
(* ---- VrdIPro.v Section a's hypotheses, the same names and statements (vrd_ipro_ok_inv / vrd_ipro_depth_inv take
   them): the engine laws, the image binding of B, three image numbers, grow's PUBLISHED text, the instance's head,
   the program statics, s0 inside parse_items and grow, and IelemE's after-call image facts ---- *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis PAL : PALib (L := A_prog_listing) (PI := PI_prog_A) B.
Hypothesis H_img : pi_frame F_parse_items = PI_FRAME /\ 0 <= pi_frame F_parse_value /\ 0 <= STK_grow.
Variable CTX0 : list (list Z).
Variable CW : list (list Z).
Hypothesis H_grow : tgrow_specX B ARx SK CTX0.
Hypothesis H_head8 : 8 <= cf_head.
Hypothesis H_pst_img : forall a, Exists (in_zr a) prh_pst -> in_img segs a.
Hypothesis HI_head : cf_head = PresetReqAt.HEAD.
Hypothesis H_s0 : pi_s0cur F_parse_items = Some 0.
Hypothesis H_s0g : pi_s0cur F_grow = Some 48.
Hypothesis H_HL : HL = cf_head.
Hypothesis H_zsal : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).
Hypothesis H_imgvis : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO <= a < IMG_TOP ->
  aview segs (w_H W) mem (shadow_addr a) <> None.
Hypothesis H_pst_ro : forall a, Exists (in_zr a) prh_pst -> ~ in_roP segs pa_relro_lo pa_relro_hi a.
(* ---- THE FOUR STEP PROPS of VrdIElem.v, in the _G form that file fixes, at EVERY context list (each proof is
   `forall CTX`): vrd_ikey_okG (lib/A/VrdIKeyB.v, Qed), vrd_ival_okG (lib/A/VrdIVal.v),
   vi_igrow_okG and vi_iexit_okG (lib/A/VrdIStep.v) ---- *)
Hypothesis H_ikey : forall CTX : list (list Z), tvrd_ikey_aG B ARx SK CTX CTX0 CW.
Hypothesis H_ival : forall CTX : list (list Z), tvrd_ival_aG B ARx SK CTX CTX0 CW.
Hypothesis H_igrow : forall CTX : list (list Z), tvrd_igrow_aG B ARx SK CTX CTX0 CW.
Hypothesis H_iexit : forall CTX : list (list Z), tvrd_iexit_aG B ARx SK CTX CTX0 CW.

(* the m-form post (PRH_Base.fpostWFm = fpostWF at fQmn) from the plain post and the keep on the returned memory *)
Lemma vrd_fpostWFm_of : forall STK e FP regs ly S Hp (W : world segs) mem md
    (Qb : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
    (W' : world segs) (c' : config),
  fpostWF B ARx SK STK e FP regs ly S Hp W mem md Qb W' c' ->
  (YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs (ms_mem (cfg_ms c'))) ->
  fpostWFm B ARx SK STK e FP regs ly S Hp W mem md Qb W' c'.
Proof.
  intros STK e FP regs ly S Hp W mem md Qb W' c'
    (fx' & ly' & S' & Hp' & regs' & mem' & md' & k & -> & H1 & H2 & H3 & H4 & H5 & HQ) HK.
  unfold fpostWFm, fpostWF, fQmn.
  exists fx', ly', S', Hp', regs', mem', md', k.
  split; [reflexivity|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [exact H5|]. split; [exact HQ | exact HK].
Qed.

(* the same for the kit's cut's BUDGETED post (PRH_Base.fpostWFbm = fpostWFb at fQmn, tparse_items_specX's post): the m-form
   from the budgeted post and the keep on the returned memory *)
Lemma vrd_fpostWFbm_of : forall (Pb : list (list Z) -> Prop) STK e FP regs ly S Hp (W : world segs) mem md
    (Qb : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
    (W' : world segs) (c' : config),
  fpostWFb B ARx SK Pb STK e FP regs ly S Hp W mem md Qb W' c' ->
  (YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs (ms_mem (cfg_ms c'))) ->
  fpostWFbm B ARx SK Pb STK e FP regs ly S Hp W mem md Qb W' c'.
Proof.
  intros Pb STK e FP regs ly S Hp W mem md Qb W' c'
    (fx' & ly' & S' & Hp' & regs' & mem' & md' & k & WS & -> & H1 & H2 & H3 & H4 & H5 & H6 & HQ) HK.
  unfold fpostWFbm, fQmn.
  exists fx', ly', S', Hp', regs', mem', md', k, WS.
  split; [reflexivity|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [exact H5|]. split; [exact H6|]. split; [exact HQ | exact HK].
Qed.

(* ---- THE LOOP: from the loop head, for a memory invariant Pm with the three laws, the epilogue's post and Pm of
   the returned memory, by SRr'_loop on 2 ^ 54 - ip_n (the step Props conclude SRr' at preset's zone RZ_cf) ---- *)
Lemma vrd_iloop_run : forall (Pm : (word -> option byte) -> Prop),
  srr_inv_laws segs Pm -> srr_inv_call segs Pm -> srr_inv_mn segs Pm ->
  forall (CTX : list (list Z)) (E : vrd_ient),
  vrd_ient_ok B ARx CTX CTX0 CW E ->
  (forall fx' : YK11.FPState,
     @tparse_value_specX fx' rc ci cp PIm RL A_prog_listing PI_prog_A B ARx SK (S (ie_d E)) CTX CTX0 CW) ->
  forall P, vrd_ielem_a B ARx SK E P -> Pm (ip_mem P) ->
  SRr' segs YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg A_IELEM_SLOT P)
    (fun W2 c2 =>
       fpostWFb B ARx SK (YCbqGwild.wbudget CW 0) (STK_parse_items (ie_d E)) (ie_e E) (rd_fp (ie_q E) (ie_v E))
         (ie_regs E)
         (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E)
         (vrd_items_q B (ie_d E) (ie_o E) (ie_q E) (ie_v E) (ie_text E) (ie_len E) (ie_p E) (ie_tb E) (ie_ly E)
            (ie_S E) (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E) (ie_own E)) W2 c2 /\
       Pm (ms_mem (cfg_ms c2))).
Proof.
  intros Pm PLAW PCALL PMN CTX E HEN HPV.
  set (Qx := fun (W2 : world segs) (c2 : config) =>
       fpostWFb B ARx SK (YCbqGwild.wbudget CW 0) (STK_parse_items (ie_d E)) (ie_e E) (rd_fp (ie_q E) (ie_v E))
         (ie_regs E)
         (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E)
         (vrd_items_q B (ie_d E) (ie_o E) (ie_q E) (ie_v E) (ie_text E) (ie_len E) (ie_p E) (ie_tb E) (ie_ly E)
            (ie_S E) (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E) (ie_own E)) W2 c2 /\
       Pm (ms_mem (cfg_ms c2))).
  intros P HEL HPM.
  refine (SRr'_loop segs YGcfRehidePost.RZ_cf vrd_ipos (fun P0 => Z.to_nat (2 ^ 54 - ip_n P0))
           (fun P0 W0 c0 => W0 = ip_W P0 /\ c0 = vrd_cfg A_IELEM_SLOT P0 /\ vrd_ielem_a B ARx SK E P0 /\
                            Pm (ip_mem P0))
           Qx _ P (ip_W P) (vrd_cfg A_IELEM_SLOT P) (conj eq_refl (conj eq_refl (conj HEL HPM)))).
  clear P HEL HPM. intros P W c (-> & -> & HEL & HPM).
  (* the exit arms, in the loop's own post shape *)
  assert (HXl : forall P' res, vrd_iexit_a B ARx SK E P' res -> Pm (ip_mem P') ->
            SRr' segs YGcfRehidePost.RZ_cf (ip_W P') (vrd_cfg A_IEPI_SLOT P')
              (fun W' c' => Qx W' c' \/
                 exists x', (Z.to_nat (2 ^ 54 - ip_n x') < Z.to_nat (2 ^ 54 - ip_n P))%nat /\
                   (W' = ip_W x' /\ c' = vrd_cfg A_IELEM_SLOT x' /\ vrd_ielem_a B ARx SK E x' /\ Pm (ip_mem x')))).
  { intros P' res HXA HPM'. eapply SRr'_mono; [exact (H_iexit CTX Pm PLAW E P' res HEN HXA HPM')|].
    intros W' c' _ HQ. left. exact HQ. }
  (* 1. the key path *)
  apply (SRr'_bind _ _ _ _ _ _ (H_ikey CTX Pm PLAW PCALL E P HEN HEL HPM)).
  intros W1 c1 _ ([(P1 & nm & -> & -> & HS1 & Hn1) | (P1 & res & -> & -> & HX1)] & HPM1);
    [| exact (HXl P1 res HX1 HPM1)].
  (* 2. the element step: parse_value at S (ie_d E) *)
  apply (SRr'_bind _ _ _ _ _ _ (H_ival CTX Pm PLAW PCALL PMN E P1 nm HPV HEN HS1 HPM1)).
  intros W2 c2 _ ([(P2 & -> & -> & HC2 & Hn2) | (P2 & res & -> & -> & HX2)] & HPM2);
    [| exact (HXl P2 res HX2 HPM2)].
  (* 3. the capacity step, back to the loop head *)
  apply (SRr'_bind _ _ _ _ _ _ (H_igrow CTX Pm PLAW PCALL E P2 HEN HC2 HPM2)).
  intros W3 c3 _ ([(P3 & -> & -> & HE3 & Hn3) | (P3 & res & -> & -> & HX3)] & HPM3);
    [| exact (HXl P3 res HX3 HPM3)].
  apply SRr'_ret. right. exists P3.
  split; [| exact (conj eq_refl (conj eq_refl (conj HE3 HPM3)))].
  pose proof HEL as (_ & _ & (_ & _ & Hcap & _) & _ & _ & _ & Hlt & _).
  pose proof HE3 as (_ & _ & (_ & _ & Hcap3 & _) & _ & _ & _ & Hlt3 & _).
  apply Z2Nat.inj_lt; lia.
Qed.

(* the text's premises, as VrdIPro.v's vrd_ipre (the same conjuncts in the same order, except the two the kit's cut added
   for the cursor set CW - prh_cw_entry and the wild room - and the text's hull budget, which vrd_ipre carries in ONE
   trailing slot) *)
Lemma vrd_ipre_of_text : forall d CTX ly S Hp W regs mem md ch e q text len p (tb : list Z) v (o : bool)
    Lam peak cnt fail ran most own,
  fpre B ARx (STK_parse_items d) ly S Hp W regs mem md ch ->
  YAkMemnorm.memnorm segs mem ->
  In (raZ regs :: spine ch) CTX ->
  prh_univ_closure B CTX0 ->
  prh_cur_entry W mem regs q ->
  prh_cw_entry B CW W mem regs q ->
  (exists ch', achain ly (aview segs (w_H W) mem) (spZ regs) (s0Z regs) ch' /\ spine ch' = spine ch) ->
  ((spZ regs <= q < spZ regs + 16) \/
   (spZ regs + 16 <= q /\ exists ch', achain ly (aview segs (w_H W) mem) (spZ regs) (prh_s0 F_parse_string q) ch')) ->
  getr regs 10 = w64 q -> getr regs 11 = w64 v -> getr regs 12 = w64 (if o then 1 else 0) ->
  rd_pre B (STK_parse_items d) ly S Hp W regs mem Lam peak cnt fail ran most own e q text len p d tb v ->
  p < text + len -> nth_error tb (Z.to_nat (p - text)) = Some (if o then 123 else 91) ->
  rd_room S (prhPi_gtrace d o (rest_atR tb text p)) ->
  YCbqGwild.wild_room (as_universe B) CW 0 (st_depot S) ->
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p)))) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p)))) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  PresetHullBudget.hull_budget S (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p))) ->
  (exists ch, achain ly (aview segs (w_H W) mem) (spZ regs - pi_frame F_parse_items) (prh_s0 F_parse_items q) ch) ->
  Z.of_nat (length (frames S)) + Z.of_nat (PjGrammar.MAXD - d) <= fs_frames 0 ->
  vrd_ipre B ARx CTX0 CW d CTX o ly S Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v.
Proof.
  intros d CTX ly S Hp W regs mem md ch e q text len p tb v o Lam peak cnt fail ran most own
    HFP HMN HCTX HUC HCE HCW HCH HQCH H10 H11 H12 HRD Hpe Hop HROOM HWR HPKS HPKL HHB HFU HFR.
  exact (conj HFP (conj HMN (conj HCTX (conj HUC (conj HCE (conj HCH (conj HQCH (conj H10 (conj H11 (conj H12
    (conj HRD (conj Hpe (conj Hop (conj HROOM (conj HPKS (conj HPKL (conj HFU (conj HFR (conj HCW (conj HWR HHB)))))))))))))))))))).
Qed.

(* ==== parse_items' TEXT at nesting d, from parse_value's text at d + 1 (at every float state and context list) ==== *)
Theorem vrd_items_at : forall d : nat,
  (forall (CTX' : list (list Z)) (fx' : YK11.FPState),
     @tparse_value_specX fx' rc ci cp PIm RL A_prog_listing PI_prog_A B ARx SK (S d) CTX' CTX0 CW) ->
  forall CTX : list (list Z),
  @tparse_items_specX fx rc ci cp PIm RL A_prog_listing PI_prog_A B ARx SK d CTX CTX0 CW.
Proof.
  intros d HPV CTX. unfold tparse_items_specX.
  intros ly S Hp W regs mem md ch e q text len p tb v o Lam peak cnt fail ran most own
    HFP HMN HCTX HUC HCE HCW HCH HQCH H10 H11 H12 HRD Hpe Hop HROOM HWR HPKS HPKL HHB HFU HFR.
  pose proof (vrd_ipre_of_text d CTX ly S Hp W regs mem md ch e q text len p tb v o Lam peak cnt fail ran most own
    HFP HMN HCTX HUC HCE HCW HCH HQCH H10 H11 H12 HRD Hpe Hop HROOM HWR HPKS HPKL HHB HFU HFR) as HPRE.
  pose proof (srr_inv_laws_imp segs (YAkMemnorm.memnorm segs) mem (srr_inv_laws_memnorm_k segs)) as PLAW.
  pose proof (srr_inv_call_imp segs mem) as PCALL.
  pose proof (srr_inv_mn_imp segs mem HMN) as PMN.
  apply (SRr'_bind _ _ _ _ _ _
    (vrd_ipro_ok_inv B ARx SK LAWS PAL H_img CTX0 CW H_grow H_head8 H_pst_img HI_head H_s0 H_s0g H_HL H_zsal
       H_imgvis H_pst_ro _ PLAW PCALL d CTX ly S Hp W regs mem md ch e q text len p tb v o Lam peak cnt fail ran
       most own HPRE (fun h => h))).
  intros W' c' _ [[(ch2 & P & -> & -> & HEL) | HPOST] HPM].
  - (* the loop head: the loop, at the call's own context list *)
    pose proof (vrd_ient_ok_of_ipre B ARx CTX0 CW d CTX o ly S Hp W regs mem md ch Lam peak cnt fail ran most own
      e q text len p tb v ch2 HPRE) as HEN.
    eapply SRr'_mono;
      [exact (vrd_iloop_run _ PLAW PCALL PMN (vrd_ictx regs ch ch2)
                (vrd_ient_of CW d o ly S Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v ch2)
                HEN (fun fx' => HPV (vrd_ictx regs ch ch2) fx') P HEL HPM)|].
    intros W2 c2 _ (HQ & HP2).
    exact (vrd_fpostWFbm_of (YCbqGwild.wbudget CW 0) (STK_parse_items d) e (rd_fp q v) regs ly S Hp W mem md
             (vrd_items_q B d o q v text len p tb ly S Lam peak cnt fail ran most own) W2 c2 HQ HP2).
  - (* a return of the prologue: the post already *)
    apply SRr'_ret.
    exact (vrd_fpostWFbm_of (YCbqGwild.wbudget CW 0) (STK_parse_items d) e (rd_fp q v) regs ly S Hp W mem md
             (vrd_items_q B d o q v text len p tb ly S Lam peak cnt fail ran most own) W' c' HPOST HPM).
Qed.

(* ==== THE DEPTH BOUNDARY: at d = MAXD the prologue refuses at row 39 (vrd_ipro_depth_inv) before any call, so
   parse_items' text holds with NO premise about parse_value and no step Prop. The prologue's run concludes SRr (no
   call, no free), which lifts to the text's SRr' (YA0nH.SRr_SRr') ==== *)
Theorem vrd_items_max : forall CTX : list (list Z),
  @tparse_items_specX fx rc ci cp PIm RL A_prog_listing PI_prog_A B ARx SK PjGrammar.MAXD CTX CTX0 CW.
Proof.
  intros CTX. unfold tparse_items_specX.
  intros ly S Hp W regs mem md ch e q text len p tb v o Lam peak cnt fail ran most own
    HFP HMN HCTX HUC HCE HCW HCH HQCH H10 H11 H12 HRD Hpe Hop HROOM HWR HPKS HPKL HHB HFU HFR.
  pose proof (vrd_ipre_of_text PjGrammar.MAXD CTX ly S Hp W regs mem md ch e q text len p tb v o Lam peak cnt fail
    ran most own HFP HMN HCTX HUC HCE HCW HCH HQCH H10 H11 H12 HRD Hpe Hop HROOM HWR HPKS HPKL HHB HFU HFR) as HPRE.
  pose proof (srr_inv_laws_imp segs (YAkMemnorm.memnorm segs) mem (srr_inv_laws_memnorm_k segs)) as PLAW.
  apply (SRr_SRr' segs YGcfRehidePost.RZ_cf).
  eapply SRr_mono;
    [exact (vrd_ipro_depth_inv B ARx SK LAWS PAL H_img CTX0 CW H_head8 H_pst_img _ PLAW PjGrammar.MAXD CTX o ly S
              Hp W regs mem md ch Lam peak cnt fail ran most own e q text len p tb v HPRE eq_refl (fun h => h))|].
  intros W' c' _ (HPOST & HPM).
  exact (vrd_fpostWFbm_of (YCbqGwild.wbudget CW 0) (STK_parse_items PjGrammar.MAXD) e (rd_fp q v) regs ly S Hp W mem md
           (vrd_items_q B PjGrammar.MAXD o q v text len p tb ly S Lam peak cnt fail ran most own) W' c' HPOST HPM).
Qed.

(* no reader call is deeper than MAXD (rd_pre's `(d <= MAXD)%nat`), so parse_value's text holds vacuously beyond it:
   vrd_items_at's premise at d = MAXD, where the descending induction starts *)
Lemma vrd_pv_beyond : forall d : nat, (PjGrammar.MAXD < d)%nat ->
  forall (CTX : list (list Z)) (fx' : YK11.FPState),
  @tparse_value_specX fx' rc ci cp PIm RL A_prog_listing PI_prog_A B ARx SK d CTX CTX0 CW.
Proof.
  intros d Hd CTX fx'. unfold tparse_value_specX.
  intros ly S Hp W regs mem md ch e q text len p tb v Lam peak cnt fail ran most own
    _HFP _HMN _HCTX _HUC _HCE _HCW _HCH _HQCH _H10 _H11 HRD.
  exfalso. destruct HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HdM & _). lia.
Qed.

End l.

(* ==== CHECK 1 OF VERIFY 21:4xZ (satisfiable, not vacuous) for the texts this file hands on ====
   (a) the four step-Prop hypotheses are EXACTLY what the four Qed proofs give: vrd_items_at with H_ikey / H_ival /
       H_igrow / H_iexit instantiated by VrdIKeyB.vrd_ikey_okG, VrdIVal.vrd_ival_okG, VrdIStep.vi_igrow_okG and
       VrdIStep.vi_iexit_okG. Every other hypothesis of vrd_items_at_steps is one of those proofs' own (the callee
       texts parse_string, fuzz_free and grow at every float state, the checked memset, the image facts) or one of
       VrdIPro.v Section a's. A consumer may cite this form directly.
   (b) the image and instance hypotheses at the REAL instance (prh_img_A, CfParams_preset), by computation;
   (c) vrd_items_at's premise at d = MAXD at the real instance (vrd_pv_beyond), closed. *)
Section chk.
Context {rc : YM05.RunCeil} {fx : YK11.FPState} {ci : CfImg} {cp : CfParams} {PIm : PrhImg} {RL : PrhRoomLive}.
#[local] Abbreviation segs := (@pa_segs _ _ PI_prog_A).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis PAL : PALib (L := A_prog_listing) (PI := PI_prog_A) B.
Hypothesis H_img : pi_frame F_parse_items = PI_FRAME /\ 0 <= pi_frame F_parse_value /\ 0 <= STK_grow.
Variable CTX0 : list (list Z).
Variable CW : list (list Z).
Hypothesis H_grow_all : forall fxg : YK11.FPState, tgrow_specX (fx := fxg) B ARx SK CTX0.
Hypothesis H_head8 : 8 <= cf_head.
Hypothesis H_pst_img : forall a, Exists (in_zr a) prh_pst -> in_img segs a.
Hypothesis HI_head : cf_head = PresetReqAt.HEAD.
Hypothesis H_s0 : pi_s0cur F_parse_items = Some 0.
Hypothesis H_s0g : pi_s0cur F_grow = Some 48.
Hypothesis H_HL : HL = cf_head.
Hypothesis H_zsal : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).
Hypothesis H_imgvis : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO <= a < IMG_TOP ->
  aview segs (w_H W) mem (shadow_addr a) <> None.
Hypothesis H_pst_ro : forall a, Exists (in_zr a) prh_pst -> ~ in_roP segs pa_relro_lo pa_relro_hi a.
(* the four step proofs' own further hypotheses, by their names there *)
Hypothesis H_s0s : pi_s0cur F_parse_string = Some 0.
Hypothesis H_fuzz_free : forall fxP : YK11.FPState, PRH_FnAlloc.tfuzz_free_specX (fx := fxP) B ARx SK.
Hypothesis H_ffret : In (A_IPC 6241) (prh_free_sites F_parse_items).
Hypothesis H_parse_string : forall fxP : YK11.FPState, tparse_string_specX (fx := fxP) B ARx SK CTX0 CW.
Hypothesis H_checked_memset : forall fx' : YK11.FPState,
  YGcallMxmn.aintrin_realizes_xm (fx := fx') segs B ARx OSet (pa_sigma AS___asan_memset).

Theorem vrd_items_at_steps : forall d : nat,
  (forall (CTX' : list (list Z)) (fx' : YK11.FPState),
     @tparse_value_specX fx' rc ci cp PIm RL A_prog_listing PI_prog_A B ARx SK (S d) CTX' CTX0 CW) ->
  forall CTX : list (list Z),
  @tparse_items_specX fx rc ci cp PIm RL A_prog_listing PI_prog_A B ARx SK d CTX CTX0 CW.
Proof.
  exact (vrd_items_at B ARx SK LAWS PAL H_img CTX0 CW (H_grow_all fx) H_head8 H_pst_img HI_head H_s0 H_s0g H_HL
    H_zsal H_imgvis H_pst_ro
    (fun CTX => VrdIKeyB.vrd_ikey_okG B ARx SK LAWS H_head8 H_pst_img H_pst_ro H_HL H_zsal H_imgvis (proj1 H_img) H_s0
                  H_s0s HI_head H_fuzz_free H_ffret CTX CTX0 CW H_parse_string)
    (fun CTX => VrdIVal.vrd_ival_okG B ARx SK LAWS (conj (proj1 H_img) (conj H_s0 (proj1 (proj2 H_img))))
                  H_checked_memset (conj H_head8 H_HL) H_pst_img H_s0s H_zsal H_imgvis H_pst_ro CTX CTX0 CW)
    (VrdIStep.vi_igrow_okG B ARx SK LAWS H_HL H_zsal H_imgvis H_pst_ro CTX0 CW H_grow_all (proj1 H_img) H_s0g H_s0
       HI_head)
    (fun CTX => VrdIStep.vi_iexit_okG B ARx SK LAWS CTX CTX0 CW)).
Qed.
End chk.

Section real.
#[local] Existing Instance prh_img_A.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
Lemma vrd_loop_H_img_A : pi_frame F_parse_items = PI_FRAME /\ 0 <= pi_frame F_parse_value /\ 0 <= STK_grow.
Proof. split; [reflexivity|]. split; vm_compute; congruence. Qed.
Lemma vrd_loop_H_s0_A : pi_s0cur F_parse_items = Some 0.
Proof. reflexivity. Qed.
Lemma vrd_loop_H_s0g_A : pi_s0cur F_grow = Some 48.
Proof. reflexivity. Qed.
Lemma vrd_loop_H_s0s_A : pi_s0cur F_parse_string = Some 0.
Proof. reflexivity. Qed.
Lemma vrd_loop_H_head8_preset : 8 <= cf_head.
Proof. vm_compute. congruence. Qed.
Lemma vrd_loop_HI_head_preset : cf_head = PresetReqAt.HEAD.
Proof. exact VrdPro.vrd_HI_head_preset. Qed.
(* parse_items' own fuzz_free return site (listing slot 6240 + 1) is the one prh_img_A lists *)
Lemma vrd_loop_H_ffret_A : In (A_IPC 6241) (prh_free_sites F_parse_items).
Proof. vm_compute. repeat (first [left; reflexivity | right]). Qed.
End real.

Lemma vrd_loop_pv_beyond_real : forall (rc : YM05.RunCeil) (ci : CfImg) B ARx SK CTX0 CW (CTX : list (list Z))
    (fx' : YK11.FPState),
  @tparse_value_specX fx' rc ci CfParamsPreset.CfParams_preset prh_img_A
    (prh_room_live_a8 (cp := CfParamsPreset.CfParams_preset)) A_prog_listing PI_prog_A B ARx SK (S PjGrammar.MAXD)
    CTX CTX0 CW.
Proof.
  intros rc ci B ARx SK CTX0 CW CTX fx'.
  exact (vrd_pv_beyond (ci := ci) (cp := CfParamsPreset.CfParams_preset) (PIm := prh_img_A)
           (RL := prh_room_live_a8 (cp := CfParamsPreset.CfParams_preset)) B ARx SK CTX0 CW (S PjGrammar.MAXD)
           (Nat.lt_succ_diag_r _) CTX fx').
Qed.

Print Assumptions vrd_items_at.
Print Assumptions vrd_items_max.
Print Assumptions vrd_pv_beyond.
Print Assumptions vrd_items_at_steps.
Print Assumptions vrd_loop_H_img_A.
Print Assumptions vrd_loop_H_head8_preset.
Print Assumptions vrd_loop_pv_beyond_real.
Print Assumptions vrd_loop_H_ffret_A.
