(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Mem Cells Step Frame FP RunConst.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import AsanEmbed AsanCtrl.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg ABase AMalloc_iface AU_iface AFake_iface AInstanceW2 AClientRtW.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AHM AGLS NUMA_lm NUMA_sl NUMA_sb SLOWG.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require SLOWAB_vcs SLOWABN_vcs SLOWABF_vcs SLOWAG1_vcok SLOWAGN_vcok SLOWAGF_vcok.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require SLOWA_sum PWFA_defs PWFA_cert PWFA_sum SFPA_defs SFPA_cert SFPCA_defs SFPCA_cert
  PFFA_defs PFFA_cert PFFCA_defs PFFCA_cert SFPA_sum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Module NTOP.
Section G.
Context {rc : runConstT}.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis HSM4 : stack_malloc_4_stmt1 AI fflag rng_fs.
Hypothesis HSM5 : stack_malloc_5_stmt1 AI fflag rng_fs.
Hypothesis HSF5 : stack_free_5_stmt AI fflag.
Hypothesis HFF : forall L RNG st LB m cls F N,
  AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
  rw_cells asegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
  /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
  /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
  /\ ~ in_ranges CI (fflag L cls F).
Hypothesis HFR : forall L RNG st LB m cls F N,
  AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
  AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
Variables (L : alayout) (RNGh : footprint) (st : astate).
Hypothesis HFS : rng_fs L RNGh.
Hypothesis HIMG : rng_aimg RNGh.
Local Notation SG := asegs.
Local Notation GP0 := NLM.GP0.
Local Notation hmH LB := (AHM.hmH AI L RNGh st LB).
Local Notation hmA LB := (AHM.hmA AI LB).
Local Notation hmC LB := (AHM.hmC AI LB).
Local Notation sok GP LB S := (SP.summ_okHSC SG GP (hmH LB) (hmA LB) (hmC LB) AHM.hmR (AHM.hmF RNGh) (AHM.hmS L RNGh) S).
Local Notation U5 LB0 := (forall F1 n1 F2 n2, In (mkABlock (ABFake 5) F1 n1) LB0 -> In (mkABlock (ABFake 5) F2 n2) LB0 -> F1 = F2).

Definition GPS := SNG.sng_gp SG.
Lemma GV1 : Forall (SG.vc_holds SG GPS) SLOWAB_vcs.SLOWAG1_GV. Proof. exact SLOWAG1_vcok.SLOWAG1_GV_ok. Qed.
Lemma GVN : Forall (SG.vc_holds SG GPS) SLOWABN_vcs.SLOWAGN_GV. Proof. exact SLOWAGN_vcok.SLOWAGN_GV_ok. Qed.
Lemma GVF : Forall (SG.vc_holds SG GPS) SLOWABF_vcs.SLOWAGF_GV. Proof. exact SLOWAGF_vcok.SLOWAGF_GV_ok. Qed.

(* [comment removed for export] *)
Lemma slsa_gen : forall LB, (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) -> U5 LB -> sok GP0 LB SLOWA_sum.SLSA.
Proof.
  intros LB H4 H5.
  exact (NSL.slsa_ok AI IMG_CI fflag rng_fs HSM4 L RNGh st LB H4 H5 HFS HIMG HFF HFR
           (fun LB0 U4 U5 => NSB.sbody_ok AI IMG_CI fflag rng_fs HSM4 HSM5 HSF5 L RNGh st HFS HIMG HFF HFR GV1 GVN GVF LB0 U4 U5)).
Qed.

(* [comment removed for export] *)
Lemma pwfsa_gen : forall LB, (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) -> U5 LB -> sok GP0 LB PWFA_sum.PWFSA.
Proof.
  intros LB H4 H5.
  exact (SP.summ_of_pcheckHSC SG GP0 _ _ (NLM.GP0_frame _) NLM.GP0_vc (hmH LB) (hmA LB) (hmC LB) AHM.hmR (AHM.HMC_sub AI LB)
           (AHM.HMF AI L RNGh st LB) (AHM.hmF RNGh) (AHM.hmS L RNGh) (AHM.HMS_mono L RNGh)
           PWFA_defs.PWFA PWFA_defs.PWFA_IT _ _ _ PWFA_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ PWFA_cert.pwfa_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA []) ltac:(intros S0 [<-|[]]; exact (slsa_gen LB H4 H5))
           ltac:(cbn; tauto)).
Qed.

(* [comment removed for export] *)
Ltac entry_summ P IT T0 C H4 H5 :=
  exact (SP.summ_of_pcheckHSC SG GP0 _ _ (NLM.GP0_frame _) NLM.GP0_vc (hmH _) (hmA _) (hmC _) AHM.hmR (AHM.HMC_sub AI _)
           (AHM.HMF AI L RNGh st _) (AHM.hmF RNGh) (AHM.hmS L RNGh) (AHM.HMS_mono L RNGh)
           P IT _ _ _ T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ C)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA []) ltac:(intros S0 [<-|[]]; exact (pwfsa_gen _ H4 H5))
           ltac:(cbn; tauto)).
Lemma sfpas_gen : forall LB, (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) -> U5 LB -> sok GP0 LB SFPA_sum.SFPAS.
Proof. intros LB H4 H5. entry_summ SFPA_defs.SFPA SFPA_defs.SFPA_IT SFPA_defs.T0 SFPA_cert.sfpa_cert H4 H5. Qed.
Lemma sfpcas_gen : forall LB, (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) -> U5 LB -> sok GP0 LB SFPA_sum.SFPCAS.
Proof. intros LB H4 H5. entry_summ SFPCA_defs.SFPCA SFPCA_defs.SFPCA_IT SFPCA_defs.T0 SFPCA_cert.sfpca_cert H4 H5. Qed.
Lemma pffas_gen : forall LB, (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) -> U5 LB -> sok GP0 LB SFPA_sum.PFFAS.
Proof. intros LB H4 H5. entry_summ PFFA_defs.PFFA PFFA_defs.PFFA_IT PFFA_defs.T0 PFFA_cert.pffa_cert H4 H5. Qed.
Lemma pffcas_gen : forall LB, (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) -> U5 LB -> sok GP0 LB SFPA_sum.PFFCAS.
Proof. intros LB H4 H5. entry_summ PFFCA_defs.PFFCA PFFCA_defs.PFFCA_IT PFFCA_defs.T0 PFFCA_cert.pffca_cert H4 H5. Qed.

(* [comment removed for export] *)
Lemma ghostfree_any : forall GP LB S, sok GP0 LB S -> ST.t_ghost (SP.sm_pre S) = [] -> Forall (fun X => ST.t_ghost X = []) (SP.sm_post S) ->
  sok GP LB S.
Proof. intros GP LB S H H0 HX. exact (AGS.summ_ghostfree SG GP0 GP _ _ _ _ _ _ S H0 HX H). Qed.

End G.

(* [comment removed for export] *)
Section W.
Context {rc : runConstT}.
Local Notation SG := asegs.
Local Notation FB5 F := (mkABlock (ABFake 5) F 2048).
Local Notation sokW GP L RNG st LB S :=
  (SP.summ_okHSC SG GP (AHM.hmH AI_W L RNG st LB) (AHM.hmA AI_W LB) (AHM.hmC AI_W LB) AHM.hmR (AHM.hmF RNG) (AHM.hmS L RNG) S).

(* [comment removed for export] *)
Lemma u5_fb5 : forall F LB, (forall FA FN, ~ In (mkABlock (ABFake 5) FA FN) LB) ->
  forall F1 n1 F2 n2, In (mkABlock (ABFake 5) F1 n1) (FB5 F :: LB) -> In (mkABlock (ABFake 5) F2 n2) (FB5 F :: LB) -> F1 = F2.
Proof.
  intros F LB NO5 F1 n1 F2 n2 [E1|H1] [E2|H2].
  - injection E1 as <- _. injection E2 as <- _. reflexivity.
  - exfalso. exact (NO5 F2 n2 H2).
  - exfalso. exact (NO5 F1 n1 H1).
  - exfalso. exact (NO5 F1 n1 H1).
Qed.
Lemma no4_fb5 : forall F LB, (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) ->
  forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) (FB5 F :: LB).
Proof. intros F LB NO4 FA FN [E|H]; [discriminate E | exact (NO4 FA FN H)]. Qed.
Lemma u5_hb : forall p COPY n F LB, (forall FA FN, ~ In (mkABlock (ABFake 5) FA FN) LB) ->
  forall F1 n1 F2 n2, In (mkABlock (ABFake 5) F1 n1) (HB p COPY n :: FB5 F :: LB) ->
    In (mkABlock (ABFake 5) F2 n2) (HB p COPY n :: FB5 F :: LB) -> F1 = F2.
Proof.
  intros p COPY n F LB NO5 F1 n1 F2 n2 [E1|H1] [E2|H2]; try discriminate E1; try discriminate E2; exact (u5_fb5 F LB NO5 F1 n1 F2 n2 H1 H2).
Qed.
Lemma no4_hb : forall p COPY n F LB, (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) ->
  forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) (HB p COPY n :: FB5 F :: LB).
Proof. intros p COPY n F LB NO4 FA FN [E|H]; [discriminate E | exact (no4_fb5 F LB NO4 FA FN H)]. Qed.

(* [comment removed for export] *)
Theorem sumw_sfpa : forall (GP : nat -> list word -> (word -> option byte) -> Prop) (L : alayout) (RNG : footprint) (st : astate)
  (LB : list ablock) (F : Z),
  (forall FA FN, ~ In (mkABlock (ABFake 5) FA FN) LB) -> (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) ->
  rng_aimg RNG -> afake_rng L RNG -> sokW GP L RNG st (FB5 F :: LB) SFPA_sum.SFPAS.
Proof.
  intros GP L RNG st LB F N5 N4 HI HF.
  apply (NTOP.ghostfree_any AI_W L RNG st); [| reflexivity | repeat constructor].
  exact (NTOP.sfpas_gen AI_W crtW_IMG_CI fflag afake_rng crtW_sm4_1 crtW_sm5_1 crtW_sf5 crtW_fake_flag crtW_fake_release L RNG st HF HI
           (FB5 F :: LB) (no4_fb5 F LB N4) (u5_fb5 F LB N5)).
Qed.
Theorem sumw_pffa : forall (GP : nat -> list word -> (word -> option byte) -> Prop) (L : alayout) (RNG : footprint) (st : astate)
  (LB : list ablock) (F : Z),
  (forall FA FN, ~ In (mkABlock (ABFake 5) FA FN) LB) -> (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) ->
  rng_aimg RNG -> afake_rng L RNG -> sokW GP L RNG st (FB5 F :: LB) SFPA_sum.PFFAS.
Proof.
  intros GP L RNG st LB F N5 N4 HI HF.
  apply (NTOP.ghostfree_any AI_W L RNG st); [| reflexivity | repeat constructor].
  exact (NTOP.pffas_gen AI_W crtW_IMG_CI fflag afake_rng crtW_sm4_1 crtW_sm5_1 crtW_sf5 crtW_fake_flag crtW_fake_release L RNG st HF HI
           (FB5 F :: LB) (no4_fb5 F LB N4) (u5_fb5 F LB N5)).
Qed.
(* [comment removed for export] *)
Theorem sumc_sfpca : forall (GP : nat -> list word -> (word -> option byte) -> Prop) (L : alayout) (RNG : footprint) (st : astate)
  (LB : list ablock) (F : Z) (p : AsanCtrl.aptr) (COPY n : Z),
  (forall FA FN, ~ In (mkABlock (ABFake 5) FA FN) LB) -> (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) ->
  rng_aimg RNG -> afake_rng L RNG -> sokW GP L RNG st (HB p COPY n :: FB5 F :: LB) SFPA_sum.SFPCAS.
Proof.
  intros GP L RNG st LB F p COPY n N5 N4 HI HF.
  apply (NTOP.ghostfree_any AI_W L RNG st); [| reflexivity | repeat constructor].
  exact (NTOP.sfpcas_gen AI_W crtW_IMG_CI fflag afake_rng crtW_sm4_1 crtW_sm5_1 crtW_sf5 crtW_fake_flag crtW_fake_release L RNG st HF HI
           (HB p COPY n :: FB5 F :: LB) (no4_hb p COPY n F LB N4) (u5_hb p COPY n F LB N5)).
Qed.
Theorem sumc_pffca : forall (GP : nat -> list word -> (word -> option byte) -> Prop) (L : alayout) (RNG : footprint) (st : astate)
  (LB : list ablock) (F : Z) (p : AsanCtrl.aptr) (COPY n : Z),
  (forall FA FN, ~ In (mkABlock (ABFake 5) FA FN) LB) -> (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) ->
  rng_aimg RNG -> afake_rng L RNG -> sokW GP L RNG st (HB p COPY n :: FB5 F :: LB) SFPA_sum.PFFCAS.
Proof.
  intros GP L RNG st LB F p COPY n N5 N4 HI HF.
  apply (NTOP.ghostfree_any AI_W L RNG st); [| reflexivity | repeat constructor].
  exact (NTOP.pffcas_gen AI_W crtW_IMG_CI fflag afake_rng crtW_sm4_1 crtW_sm5_1 crtW_sf5 crtW_fake_flag crtW_fake_release L RNG st HF HI
           (HB p COPY n :: FB5 F :: LB) (no4_hb p COPY n F LB N4) (u5_hb p COPY n F LB N5)).
Qed.
End W.
End NTOP.
Print Assumptions NTOP.sumw_sfpa.
Print Assumptions NTOP.sumc_pffca.
