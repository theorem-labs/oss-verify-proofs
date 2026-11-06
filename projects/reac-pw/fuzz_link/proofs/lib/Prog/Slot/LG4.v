(* ARM 4 (op_decide) at the SR level: LC45Arms' five evt segments of op_decide chained through its four
   allocator-facing calls into LGlue's ARM 4.
     loop head --c45_decide_head--> text_of (0x13aa4) --lfr_text_of--> 0x13aa8 (own1, k1)
       --c45_decide_to2--> text_of (0x13ab4) --lfr_text_of--> 0x13ab8 (own2, k2)
       --c45_decide_mid--> free(own1) (0x13ae8) --lfr_free / lfr_free_null--> 0x13aec
       --c45_decide_fr2--> free(own2) (0x13af0) --lfr_free / lfr_free_null--> 0x13af4
       --c45_decide_end--> next loop head or the exit (cut_evt_or).
   hb: the loop head's, then opt_hb own1 k1 hb, then opt_hb own2 k2 (opt_hb own1 k1 hb); free(own1) leaves
   opt_hb own2 k2 hb and free(own2) the loop head's hb again. Between the two text_of calls the kind string
   in own1's block is carried by the segment's footprint (LG4Lib.lg4_x1). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss MState.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem text_of_c
  model_decide_c check_verdict_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LFr LFrRun LFrAl LFrLo LFrTx LGlue
  LC45Defs LC45Arms LG4Lib LG4Ad.
Import ListNotations.
Local Open Scope Z_scope.

Section G4.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.
Local Notation segs := (ms_segs B).

Hypothesis TOF : forall fx' : YK11.FPState, @text_of_contract fx' rc B API.
Hypothesis RSD : reac_served_decide_contract.
Hypothesis MDC : model_decide_contract.
Hypothesis CVC : check_verdict_contract.

Theorem glue_arm4 : ARM B API 4.
Proof.
  intros g md mk hb T i c OK HI Hi HC.
  pose proof (cut_T B API g L_LH hb T _ c HC) as HT.
  pose proof (cut_lgv B API g L_LH hb T _ c HC) as HV.
  destruct (lg4_pay B API FF g md mk HV OK) as (Hn & Hp0 & Hlen & _).
  destruct (lg4_md_in g (lg_E g md mk) hb T HI) as [Hmd Hmk].
  destruct (lg4_room0 g (lg_E g md mk) hb T HI HT) as [HL0 HB0].
  set (E := lg_E g md mk) in *.
  assert (HS : e_S E = lg_S g) by reflexivity.
  assert (KP : forall hb', incl hb hb' -> forall x, lh_reg E x -> lkeep B g hb' x).
  { intros hb' Hinc x Hx. exact (lg4_keep B API FF g md mk hb hb' T x HV OK HI Hinc Hx). }

  (* 1. the loop head to the call of text_of at 0x13aa4 *)
  eapply SR_bind.
  { apply (cut_evt B API FF g L_LH hb T (c45_hp E) _ TEXT_OF (c45_13aa4 E i (lg_gp g)) c HC
             (lg4_hp g E hb hb T HI HT (incl_refl hb))).
    - intros ms (HL & HO). exact (c45_decide_head E i (lg_gp g) ms OK HL HO).
    - exact (lg4_form_aa4 E i (lg_gp g)). }
  intros c1 HC1.

  (* 2. text_of (kind): own1 in the ok cell, k1 its block's size *)
  eapply SR_bind.
  { apply (lfr_text_of B API FF TOF g hb T C45_TO1_RA (c45_sp E + FO_P) (c45_sp E + FO_B256)
             (c45_13aa4 E i (lg_gp g))
             (fun own k => eqv_cl (fun ms => (c45_13aa8 E i (lg_gp g) own ms /\ lg4_x1 own k (ms_mem ms)) /\
                                             (own <> 0 -> 1 <= k <= 320 /\ lfresh B g hb own k))) c1).
    - exact (lg4_room_hb0 hb HL0 HB0).
    - unfold C45_TO1_RA. lia.
    - reflexivity.
    - unfold c45_sp, FO_P, SLOT_FRAME. rewrite HS. lia.
    - unfold c45_sp, FO_P, SLOT_FRAME. rewrite HS. lia.
    - unfold c45_sp, FO_B256, SLOT_FRAME. rewrite HS. lia.
    - unfold c45_sp, FO_B256, SLOT_FRAME. rewrite HS. lia.
    - unfold FO_P, FO_B256. lia.
    - exact HC1.
    - intros ms H.
      destruct (lg4_pre_aa4 E i (lg_gp g) ms OK H)
        as (R1 & R2 & R4 & R10 & R11 & c0 & c1' & Hc & Hw & Hinp & Hlo & Hhi).
      rewrite Hp0 in Hlo. rewrite Hp0, Hlen in Hhi.
      split; [exact R1|]. split; [exact R2|]. split; [exact R4|]. split; [exact R10|]. split; [exact R11|].
      exists c0, c1'. split; [exact Hc|]. split; [exact Hw|]. split; [exact Hinp|].
      split; [exact Hn|]. split; [exact Hlo | exact Hhi].
    - intros R F fc m regs' m' c0 c1' own k s t sl HP Hc RP G10 Hs C LP Ht Htl Hsl Hsll A1 A2 A3 A4 A5
        Hown Hadv Hz Hnz.
      destruct LP as (M1 & M2 & M3 & M4 & M5).
      cbv beta. apply lg4_eqv_canon. split.
      + apply (lg4_ad_to1 E i (lg_gp g) (lkeep B g hb) R F fc m regs' m' c0 c1' own k s t OK
                 (KP hb (incl_refl hb)) HP Hc RP G10 Hs C M1 M2 M3 M4 M5 Ht Hown Hadv).
        * intros H0. destruct (Hz H0) as (_ & Z1 & Z2). split; [exact Z1 | exact Z2].
        * intros H0. destruct (Hnz H0) as (Es & Hk & Hkt & Hf).
          destruct (lg4_fresh_out B g hb own k Hf) as [F1 F2].
          split; [exact Es|]. split; [exact Hk|]. split; [exact Hkt|]. split; [exact F1 | exact F2].
      + intros H0. destruct (Hnz H0) as (_ & Hk & _ & Hf). split; [exact Hk | exact Hf]. }
  intros c2 (own1 & k1 & HC2).
  apply (lg4_cut_eqv B API) in HC2.
  destruct (lg4_cut_pure B API g C45_TO1_RA (opt_hb own1 k1 hb) T
              (fun ms => c45_13aa8 E i (lg_gp g) own1 ms /\ lg4_x1 own1 k1 (ms_mem ms))
              (own1 <> 0 -> 1 <= k1 <= 320 /\ lfresh B g hb own1 k1) c2 HC2) as [HP1 HC2'].
  clear HC2.
  assert (HK1 : own1 <> 0 -> 0 <= k1 <= 320) by (intros H; destruct (HP1 H) as [Hk _]; lia).
  assert (HB1 : own1 <> 0 -> 1 <= k1 <= 320 /\ 4096 <= own1 /\ own1 + k1 <= e_S E - SLOT_STACK_Z /\
                  (forall x, own1 <= x < own1 + k1 -> lkeep B g (opt_hb own1 k1 hb) x)).
  { intros H. destruct (HP1 H) as [Hk Hf]. destruct (lg4_fresh_out B g hb own1 k1 Hf) as [F1 F2].
    split; [exact Hk|]. split; [exact F1|]. split; [exact F2|].
    intros x Hx. right; right; left. exists own1, k1.
    split; [rewrite (lg4_opt_nz own1 k1 hb H); left; reflexivity | exact Hx]. }

  (* 3. from the first text_of's return to the second's call, the kind string kept *)
  eapply SR_bind.
  { apply (lg4_seg B API FF g E C45_TO1_RA (opt_hb own1 k1 hb) T (c45_13aa8 E i (lg_gp g) own1) TEXT_OF
             (c45_13ab4 E i (lg_gp g) own1) (lg4_x1 own1 k1) c2 HS HC2'
             (lg4_hp g E hb _ T HI HT (lg4_opt_incl own1 k1 hb))).
    - intros ms H. exact (c45_decide_to2 E i (lg_gp g) own1 ms OK H).
    - intros m m' Hfp HX.
      exact (lg4_x1_fp B API FF g E hb own1 k1 m m' HS Hmd Hmk (fun H => proj2 (HP1 H)) Hfp HX).
    - exact (lg4_form_ab4 E i (lg_gp g) own1). }
  intros c3 HC3.

  (* 4. text_of (alias): own2 in the oa cell, k2 its block's size *)
  eapply SR_bind.
  { apply (lfr_text_of B API FF TOF g (opt_hb own1 k1 hb) T C45_TO2_RA (c45_sp E + FO_P) (c45_sp E + FO_B40)
             (fun ms => c45_13ab4 E i (lg_gp g) own1 ms /\ lg4_x1 own1 k1 (ms_mem ms))
             (fun own k => eqv_cl (fun ms => c45_13ab8 E i (lg_gp g) own1 own ms /\
                                             (own <> 0 -> 1 <= k <= 320 /\ lfresh B g (opt_hb own1 k1 hb) own k)))
             c3).
    - exact (proj1 (lg4_room1 hb own1 k1 HL0 HB0 HK1)).
    - unfold C45_TO2_RA. lia.
    - reflexivity.
    - unfold c45_sp, FO_P, SLOT_FRAME. rewrite HS. lia.
    - unfold c45_sp, FO_P, SLOT_FRAME. rewrite HS. lia.
    - unfold c45_sp, FO_B40, SLOT_FRAME. rewrite HS. lia.
    - unfold c45_sp, FO_B40, SLOT_FRAME. rewrite HS. lia.
    - unfold FO_P, FO_B40. lia.
    - exact HC3.
    - intros ms (H & _).
      destruct (lg4_pre_ab4 E i (lg_gp g) own1 ms OK H)
        as (R1 & R2 & R4 & R10 & R11 & c0 & c1' & Hc & Hw & Hinp & Hlo & Hhi).
      rewrite Hp0 in Hlo. rewrite Hp0, Hlen in Hhi.
      split; [exact R1|]. split; [exact R2|]. split; [exact R4|]. split; [exact R10|]. split; [exact R11|].
      exists c0, c1'. split; [exact Hc|]. split; [exact Hw|]. split; [exact Hinp|].
      split; [exact Hn|]. split; [exact Hlo | exact Hhi].
    - intros R F fc m regs' m' c0 c1' own k s t sl HP Hc RP G10 Hs C LP Ht Htl Hsl Hsll A1 A2 A3 A4 A5
        Hown Hadv Hz Hnz.
      destruct HP as [HP HX]. destruct LP as (M1 & M2 & M3 & M4 & M5).
      cbv beta. apply lg4_eqv_canon. split.
      + apply (lg4_ad_to2 E i (lg_gp g) own1 k1 (lkeep B g (opt_hb own1 k1 hb)) R F fc m regs' m' c0 c1' own k s t
                 OK (KP _ (lg4_opt_incl own1 k1 hb)) HB1 HP HX Hc RP G10 Hs C M1 M2 M3 M4 M5 Ht Hown Hadv).
        * intros H0. destruct (Hz H0) as (_ & Z1 & Z2). split; [exact Z1 | exact Z2].
        * intros H0. destruct (Hnz H0) as (Es & Hk & Hkt & Hf).
          destruct (lg4_fresh_out B g _ own k Hf) as [F1 F2].
          split; [exact Es|]. split; [exact Hk|]. split; [exact Hkt|]. split; [exact F1 | exact F2].
      + intros H0. destruct (Hnz H0) as (_ & Hk & _ & Hf). split; [exact Hk | exact Hf]. }
  intros c4 (own2 & k2 & HC4).
  apply (lg4_cut_eqv B API) in HC4.
  destruct (lg4_cut_pure B API g C45_TO2_RA (opt_hb own2 k2 (opt_hb own1 k1 hb)) T
              (c45_13ab8 E i (lg_gp g) own1 own2)
              (own2 <> 0 -> 1 <= k2 <= 320 /\ lfresh B g (opt_hb own1 k1 hb) own2 k2) c4 HC4) as [HP2 HC4'].
  clear HC4.

  (* 5. from the second text_of's return over the three deciders to the call of free(own1) *)
  eapply SR_bind.
  { apply (cut_evt B API FF g C45_TO2_RA (opt_hb own2 k2 (opt_hb own1 k1 hb)) T (c45_hp E) _ LLVM_FREE
             (c45_13ae8 E i (lg_gp g) own1 own2) c4 HC4'
             (lg4_hp g E hb _ T HI HT (incl_tran (lg4_opt_incl own1 k1 hb) (lg4_opt_incl own2 k2 _)))).
    - intros ms H. exact (c45_decide_mid RSD MDC CVC E i (lg_gp g) own1 own2 ms OK H).
    - exact (lg4_form_ae8 E i (lg_gp g) own1 own2). }
  intros c5 HC5.

  (* 6. free(own1): own1's block leaves hb (or free(NULL)) *)
  assert (F1 : SR segs c5 (CUT B API g C45_FR1_RA (opt_hb own2 k2 hb) T (c45_13aec E i (lg_gp g) own1 own2))).
  { destruct (Z.eq_dec own1 0) as [E1|E1].
    - subst own1. change (opt_hb own2 k2 (opt_hb 0 k1 hb)) with (opt_hb own2 k2 hb) in HC5.
      apply (lfr_free_null B API FF g (opt_hb own2 k2 hb) T C45_FR1_RA (c45_13ae8 E i (lg_gp g) 0 own2)
               (c45_13aec E i (lg_gp g) 0 own2) c5).
      + unfold C45_FR1_RA. lia.
      + reflexivity.
      + exact HC5.
      + intros ms H. destruct (lg4_pre_ae8 E i (lg_gp g) 0 own2 ms H) as (R1 & _ & _ & R10).
        split; [exact R1 | exact R10].
      + intros R F fc m H. exact (lg4_ad_fn1 E i (lg_gp g) own2 R F fc m H).
    - rewrite (lg4_opt_nz own1 k1 hb E1), (lg4_opt_app own2 k2 ((own1, k1) :: hb)) in HC5.
      rewrite (lg4_opt_app own2 k2 hb).
      eapply SR_mono.
      + apply (lfr_free B API FF g (opt_hb own2 k2 []) own1 k1 hb T C45_FR1_RA (c45_13ae8 E i (lg_gp g) own1 own2)
                 (eqv_cl (c45_13aec E i (lg_gp g) own1 own2)) c5).
        * apply (lg4_not_T T own1 k1 HT). destruct (HP1 E1) as [Hk _]. lia.
        * unfold C45_FR1_RA. lia.
        * reflexivity.
        * exact HC5.
        * intros ms H. exact (lg4_pre_ae8 E i (lg_gp g) own1 own2 ms H).
        * intros R F fc m regs' m' H RP C LP. destruct LP as (M1 & M2 & M3 & M4 & M5).
          apply lg4_eqv_canon.
          exact (lg4_ad_fr1 E i (lg_gp g) own1 own2 _ R F fc m regs' m' OK
                   (KP _ (fun t Ht => in_or_app _ _ _ (or_intror Ht))) H RP C M1 M2 M3 M4 M5).
      + intros c' H. exact (lg4_cut_eqv B API g _ _ _ _ c' H). }
  eapply SR_bind; [exact F1|]. intros c6 HC6. clear F1.

  (* 7. from free(own1)'s return to the call of free(own2) *)
  eapply SR_bind.
  { apply (cut_evt B API FF g C45_FR1_RA (opt_hb own2 k2 hb) T (c45_hp E) _ LLVM_FREE
             (c45_13af0 E i (lg_gp g) own1 own2) c6 HC6 (lg4_hp g E hb _ T HI HT (lg4_opt_incl own2 k2 hb))).
    - intros ms H. exact (c45_decide_fr2 E i (lg_gp g) own1 own2 ms OK H).
    - exact (lg4_form_af0 E i (lg_gp g) own1 own2). }
  intros c7 HC7.

  (* 8. free(own2): hb is the loop head's again *)
  assert (F2 : SR segs c7 (CUT B API g C45_FR2_RA hb T (c45_13af4 E i (lg_gp g) own1 own2))).
  { destruct (Z.eq_dec own2 0) as [E2|E2].
    - subst own2. change (opt_hb 0 k2 hb) with hb in HC7.
      apply (lfr_free_null B API FF g hb T C45_FR2_RA (c45_13af0 E i (lg_gp g) own1 0)
               (c45_13af4 E i (lg_gp g) own1 0) c7).
      + unfold C45_FR2_RA. lia.
      + reflexivity.
      + exact HC7.
      + intros ms H. destruct (lg4_pre_af0 E i (lg_gp g) own1 0 ms H) as (R1 & _ & _ & R10).
        split; [exact R1 | exact R10].
      + intros R F fc m H. exact (lg4_ad_fn2 E i (lg_gp g) own1 R F fc m H).
    - rewrite (lg4_opt_nz own2 k2 hb E2) in HC7.
      eapply SR_mono.
      + apply (lfr_free B API FF g [] own2 k2 hb T C45_FR2_RA (c45_13af0 E i (lg_gp g) own1 own2)
                 (eqv_cl (c45_13af4 E i (lg_gp g) own1 own2)) c7).
        * apply (lg4_not_T T own2 k2 HT). destruct (HP2 E2) as [Hk _]. lia.
        * unfold C45_FR2_RA. lia.
        * reflexivity.
        * exact HC7.
        * intros ms H. exact (lg4_pre_af0 E i (lg_gp g) own1 own2 ms H).
        * intros R F fc m regs' m' H RP C LP. destruct LP as (M1 & M2 & M3 & M4 & M5).
          apply lg4_eqv_canon.
          exact (lg4_ad_fr2 E i (lg_gp g) own1 own2 _ R F fc m regs' m' OK (KP _ (incl_refl hb))
                   H RP C M1 M2 M3 M4 M5).
      + intros c' H. exact (lg4_cut_eqv B API g _ _ _ _ c' H). }
  eapply SR_bind; [exact F2|]. intros c8 HC8. clear F2.

  (* 9. from free(own2)'s return to the next loop head or the exit *)
  eapply SR_mono.
  - apply (cut_evt_or B API FF g C45_FR2_RA hb T (c45_hp E) _ L_LH
             (fun ms => i < 47 /\ lh_ms E (i + 1) (lg_gp g) ms) L_EXIT (ex_ms E (lg_gp g)) c8 HC8
             (lg4_hp g E hb hb T HI HT (incl_refl hb))).
    + intros ms H. exact (c45_decide_end E i (lg_gp g) own1 own2 ms OK H).
    + intros ms' (_ & H). exact (lg4_lh_pc _ _ _ _ H).
    + intros ms' H. exact (lg4_ex_pc _ _ _ H).
  - intros c' [H1 | H2]; unfold arm_post; exists hb, T; split; try exact HI.
    + left. split.
      * destruct H1 as (fx' & L & A & regs & mem & md' & _ & _ & _ & (c0 & (Hlt & _) & _)). exact Hlt.
      * exact (cut_mono B API g L_LH hb T _ _ c' (fun ms H => proj2 H) H1).
    + right. exact H2.
Qed.

End G4.

About glue_arm4.
Print Assumptions glue_arm4.
