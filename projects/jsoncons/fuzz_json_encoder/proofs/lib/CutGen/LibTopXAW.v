(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm4L5DefsA PmHeapIfaceA IcptIfaceA PmIcptIfaceA LibIface PmLibIfaceA PmLibIfaceAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmLibSpecsXA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA CutL5A.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import TopKitXA HnKitXA PmTopSpecsXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibSpecsW PmRef PmLibSpecsXAW PmTopSpecsXAW.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module LTXAW.
(* [comment removed for export] *)
Lemma txt_range_of_bytes : forall payload : list byte, Forall (fun b => 0 <= b <= 255) (map bv_unsigned payload).
Proof.
  intros p. apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (b & <- & _).
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256%Z in R. clear - R. lia.
Qed.
Section LibTop.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Abbreviation IC := PMLA.C_xasan.
(* [comment removed for export] *)
Variable VIS_SCRA : Z.
Variable benc : PMES.eghost -> Z.
Definition PC_LIB : Z := 722256.        (* [comment removed for export] *)
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis TPV : hl_tp L = 6938576.                                               (* [comment removed for export] *)
(* [comment removed for export] *)
Variable PHI : list byte -> Prop.
Hypothesis PHIW : TPSXAW.phiwP PHI.
Hypothesis HAS : TPSXAW.harness_chainXAW L ar HI IC benc PC_LIB 0 false.
Hypothesis HAL : TPSXAW.harness_chainXAW L ar HI IC benc PC_LIB 0 true.
Hypothesis HBS : TPSXAW.harness_chainXAW L ar HI IC benc PC_LIB 16 false.
Hypothesis HBL : TPSXAW.harness_chainXAW L ar HI IC benc PC_LIB 16 true.

Theorem lib_call_okw : forall Lay : lib_layoutA,
  TPSXA.pm_layout_okxA L IC VIS_SCRA benc Lay -> lla_stack Lay = TPSXA.HARN_SCRXA -> lla_entry Lay = PC_LIB -> lla_empty Lay = TPSXA.EMPTY_X ->
  PmLibIfaceAW.lib_call_okAW Lay ar SCFG HI (TPSXA.pm_staticsxA L IC) PHI.
Proof.
  intros Lay LOK HST HEN HEM. pose proof LOK as (HL & _ & _ & HFOOT & HJUNK & HFR & HCR & _).
  unfold PmLibIfaceAW.lib_call_okAW. intros fx g LB FF LK cr A sp ptr ra payload R M model K Hfp HPHI PRE HH Hh HMI HK CONT.
  destruct PRE as [Pra Prok Psp Pgp Ptp Pa0 Pa1 Plen Pptr Ppay Ppaysh Pstk Pcr Pffroom Pffrs Pstksh Pst].
  rewrite HL in Ptp, Ppay. rewrite HST in Pstk, Pstksh. unfold PmLibIfaceA.lib_cfgA in CONT |- *. rewrite HL, HEN. rewrite HL in CONT.
  destruct Pstk as (S1 & S2 & S3 & S4 & S5 & S6). unfold TPSXA.HARN_SCRXA in *.
  set (txt := map bv_unsigned payload). set (n := Z.of_nat (length payload)) in *.
  assert (Hlen : length txt = length payload) by (subst txt; apply length_map).
  assert (N0 : 0 <= n) by (subst n; clear; lia).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf L ar _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). pose proof (CHA.wf_top _ _ _ _ _ _ _ _ WF) as STT.
  (* [comment removed for export] *)
  assert (CH : exists aln lng, TPSXAW.harness_chainXAW L ar HI IC benc PC_LIB aln lng /\ sp mod 32 = aln /\ HNK.len_class lng txt).
  { assert (A2 : sp mod 32 = 0 \/ sp mod 32 = 16).
    { pose proof (Z.mod_pos_bound sp 32 ltac:(clear; lia)) as B32. pose proof (Z_div_mod_eq_full sp 32) as D32. pose proof (Z_div_mod_eq_full sp 16) as D16. rewrite S1 in D16. clear - B32 D32 D16. lia. }
    destruct (le_dec 23 (length txt)) as [LL|LL]; destruct A2 as [AA|AA].
    - exists 0, true. split; [exact HAL | split; [exact AA | exact LL]].
    - exists 16, true. split; [exact HBL | split; [exact AA | exact LL]].
    - exists 0, false. split; [exact HAS | split; [exact AA | cbn; clear - LL; lia]].
    - exists 16, false. split; [exact HBS | split; [exact AA | cbn; clear - LL; lia]]. }
  destruct CH as (aln & lng & HC & HALN & HLEN).
  (* [comment removed for export] *)
  assert (PAY : ((txt = [] /\ ptr = TPSXA.EMPTY_X) \/ (0 < n /\ In (ptr, n) LB)) /\ L5.bytes_at (hl_segs L) M ptr txt /\ L5.defined M ptr n).
  { destruct Pptr as [(P0 & P1)|(P0 & PIN)].
    - assert (T0 : txt = []) by (subst txt; destruct payload; [reflexivity | discriminate P0]).
      rewrite T0. split; [left; split; [reflexivity | rewrite P1; exact HEM]|]. split; [intros i Hi; exfalso; cbn in Hi; clear - Hi; lia|].
      intros i Hi. exfalso. subst n. rewrite P0 in Hi. clear - Hi. cbn in Hi. lia.
    - destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WF (ptr, n) PIN) as ((B0 & _ & _ & _ & B4 & (B5 & _ & B7)) & BD & _). cbn [fst snd] in B0, B4, B5, B7, BD.
      split; [right; exact (conj P0 PIN)|]. split; [|exact BD].
      subst txt. apply (L5C.rdn_bytes_at (hl_segs L) M payload ptr B5); [fold n; clear - B7; lia | exact Ppay]. }
  destruct PAY as (PPTR & PBY & PDEF).
  unfold TPSXAW.harness_chainXAW, PMSA.cps_asan in HC.
  apply (HC LB FF LK cr A sp ra ptr txt g HALN HLEN (txt_range_of_bytes payload) (PHIW payload HPHI) fx R M model K HH (conj Hh HMI) HK Hfp Pra Prok Psp Ptp).
  - unfold CHA.astk. exact (conj S1 (conj S2 (conj S3 (conj S4 (conj S5 S6))))).
  - unfold CHA.ffroom. intros k Hk. destruct (HFR k Hk) as [FRk _]. specialize (Pffroom k Hk). rewrite FRk in Pffroom. exact Pffroom.
  - exact Pffrs.
  - (* [comment removed for export] *)
    unfold TPSXA.harness_preX, PMSA.a0, PMSA.a1, PMSA.stksh, PMLA.stksh. cbv zeta. rewrite Hlen. fold n.
    split; [exact Pa0|]. split; [exact Pa1|]. split; [exact Plen|]. split; [exact S1|]. split; [exact Pstksh|].
    split; [exact PPTR|]. split; [exact PBY|]. split; [exact PDEF|]. split; [exact Ppaysh|]. split; [exact Pst|].
    rewrite (HCR n) in Pcr. unfold credit_le in Pcr. exact Pcr.
  - (* [comment removed for export] *)
    intros fx' R' M' model' LB' cr' LBk W LK' A' Hfp' (g' & Qa0 & Qst & Qg & -> & -> & QC1 & QC2 & ->) HRP HP Hrt HA' [Hh' HMI'] HLK' HH'.
    rewrite Hlen in QC2. fold n in QC2. pose proof HP as (HP1 & HP2 & HP3).
    apply (CONT fx' g' R' M' model' cr' LK' A' Hfp'); [| exact Hrt | exact HA' | exact Hh' | exact HMI' | | exact HH'].
    + constructor.
      * exact Qa0.
      * exact HRP.
      * unfold credit_le, credit_sub. rewrite (HCR (Z.of_nat (length payload))). unfold TPSXA.pm_creditxA in QC1, QC2 |- *. cbn [fst snd] in QC1, QC2 |- *. subst n. clear - QC1 QC2. split; lia.
      * intros a Ha Hcl Hnf Hnj. rewrite HST, HL in Hcl. apply HP1. split; [exact Ha|]. split; [exact Hcl|].
        intros w Hw Hr. apply in_app_or in Hw as [Hw|[<-|[]]].
        -- apply Hnf. unfold LibIface.in_foot. cbn [ll_foot PmLibIfaceA.lib_view]. rewrite HFOOT. unfold PMLA.FOOTX.
           unfold TPSXA.foot_rangesX, PMSA.foot_ranges in Hw. apply in_app_or in Hw as [Hw|[<-|[]]].
           ++ apply in_map_iff in Hw as (iv & <- & Hiv). unfold L5.in_rng in Hr. cbn [fst snd] in Hr. exists iv. split; [apply in_or_app; left; exact Hiv | clear - Hr; lia].
           ++ unfold L5.in_rng in Hr. cbn [fst snd] in Hr. exists (PMLA.LIT_LO IC, PMLA.LIT_HI IC). split; [apply in_or_app; right; left; reflexivity | cbn [fst snd]; clear - Hr; lia].
        -- apply Hnj. unfold PmLibIfaceA.in_junk. rewrite HJUNK. exists (hl_tp L - 164, hl_tp L - 160). split; [left; reflexivity|]. unfold L5.in_rng in Hr. cbn [fst snd] in Hr |- *. clear - Hr. lia.
      * rewrite HST. exact HP2.
      * intros a Ha Hcl. rewrite HST, HL in Hcl. exact (HP3 a Ha Hcl).
      * rewrite HST. apply (PTA.stksh_ag ar M M' sp 18432); [|exact Pstksh]. intros a Hq.
        assert (SPA : (sp - 18432) mod 8 = 0) by (clear - S1; apply Z.mod_divide in S1; [|lia]; destruct S1 as [q Hq']; rewrite Hq'; replace (q * 16 - 18432) with ((2 * q - 2304) * 8) by lia; apply Z_mod_mult).
        destruct (PTA.stksh_rng ar sp 18432 a ltac:(clear - S2; lia) SPA C8 ltac:(clear - S4; lia) STT ltac:(clear - CL; lia) Hq) as (G1 & G2).
        pose proof (CHA.shadow_range (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a ltac:(clear - CL; lia) ltac:(clear - S2 S3 S4; lia) ltac:(clear; lia) G2) as SRa.
        apply HP1. split; [exact G1|]. split; [do 4 right; left; exact G2|].
        intros w Hw Hr. apply in_app_or in Hw as [Hw|[<-|[]]].
        -- unfold TPSXA.foot_rangesX, PMSA.foot_ranges in Hw. apply in_app_or in Hw as [Hw|[<-|[]]]; [|unfold L5.in_rng, PMLA.LIT_LO, PMLA.LIT_HI in Hr; cbn in Hr; clear - Hr SRa; lia].
           apply in_map_iff in Hw as (iv & <- & Hiv). unfold L5.in_rng in Hr. cbn [fst snd] in Hr. cbn [PMLA.FOOT PMLA.C_xasan] in Hiv.
           repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; clear - Hr SRa; lia|]). destruct Hiv.
        -- unfold L5.in_rng in Hr. cbn [fst snd] in Hr. rewrite TPV in Hr. clear - Hr SRa. lia.
      * exact Qst.
    + intros k Hk. rewrite (proj2 (HFR k Hk)). destruct (CHA.wf_nodup L ar _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH')) as [_ ND].
      pose proof (CHA.ff_count_incl k LK' LK HLK' (CHA.nodup_of_map_app_r FF LK' ND)). clear - H. lia.
Qed.

Corollary lib_specxAW_ok : forall Lay : lib_layoutA, lla_stack Lay = TPSXA.HARN_SCRXA -> lla_entry Lay = PC_LIB -> lla_empty Lay = TPSXA.EMPTY_X -> TPSXAW.lib_specxAW L ar HI IC VIS_SCRA benc PHI Lay.
Proof. intros Lay H1 H2 H3 LOK. exact (lib_call_okw Lay LOK H1 H2 H3). Qed.
Print Assumptions lib_specxAW_ok.
End LibTop.
End LTXAW.
