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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg ABase AMalloc_iface AU_iface AFake_iface AInstanceW2 AClientRtW.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AHMB AGLS NUMB_lm NUMB_sl NUMB_sb SLOWG.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require SLOWBB_vcs SLOWBBN_vcs SLOWBBF_vcs SLOWBG1_vcok SLOWBGN_vcok SLOWBGF_vcok.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require SLOWB_sum PWFB_defs PWFB_cert PWFB_sum SFPBP_defs SFPBP_cert SFPCBP_defs SFPCBP_cert
  PFFBP_defs PFFBP_cert PFFCBP_defs PFFCBP_cert SFPB_sum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Module NTOPB.
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
  rw_cells bsegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
  /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
  /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
  /\ ~ in_ranges CI (fflag L cls F).
Hypothesis HFR : forall L RNG st LB m cls F N,
  AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
  AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
Variables (L : alayout) (RNGh : footprint) (st : astate).
Hypothesis HFS : rng_fs L RNGh.
Hypothesis HIMG : rng_aimg RNGh.
Local Notation SG := bsegs.
Local Notation GP0 := NLMB.GP0.
Local Notation hmH LB := (AHMB.hmH AI L RNGh st LB).
Local Notation hmA LB := (AHMB.hmA AI LB).
Local Notation hmC LB := (AHMB.hmC AI LB).
Local Notation sok GP LB S := (SP.summ_okHSC SG GP (hmH LB) (hmA LB) (hmC LB) AHMB.hmR (AHMB.hmF RNGh) (AHMB.hmS L RNGh) S).
Local Notation U5 LB0 := (forall F1 n1 F2 n2, In (mkABlock (ABFake 5) F1 n1) LB0 -> In (mkABlock (ABFake 5) F2 n2) LB0 -> F1 = F2).

Definition GPS := SNG.sng_gp SG.
Lemma GV1 : Forall (SG.vc_holds SG GPS) SLOWBB_vcs.SLOWBG1_GV. Proof. exact SLOWBG1_vcok.SLOWBG1_GV_ok. Qed.
Lemma GVN : Forall (SG.vc_holds SG GPS) SLOWBBN_vcs.SLOWBGN_GV. Proof. exact SLOWBGN_vcok.SLOWBGN_GV_ok. Qed.
Lemma GVF : Forall (SG.vc_holds SG GPS) SLOWBBF_vcs.SLOWBGF_GV. Proof. exact SLOWBGF_vcok.SLOWBGF_GV_ok. Qed.

(* [comment removed for export] *)
Lemma slsb_gen : forall LB, (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) -> U5 LB -> sok GP0 LB SLOWB_sum.SLSB.
Proof.
  intros LB H4 H5.
  exact (NSLB.slsb_ok AI IMG_CI fflag rng_fs HSM4 L RNGh st LB H4 H5 HFS HIMG HFF HFR
           (fun LB0 U4 U5 => NSBB.sbody_ok AI IMG_CI fflag rng_fs HSM4 HSM5 HSF5 L RNGh st HFS HIMG HFF HFR GV1 GVN GVF LB0 U4 U5)).
Qed.

(* [comment removed for export] *)
Lemma pwfsb_gen : forall LB, (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) -> U5 LB -> sok GP0 LB PWFB_sum.PWFSB.
Proof.
  intros LB H4 H5.
  exact (SP.summ_of_pcheckHSC SG GP0 _ _ (NLMB.GP0_frame _) NLMB.GP0_vc (hmH LB) (hmA LB) (hmC LB) AHMB.hmR (AHMB.HMC_sub AI LB)
           (AHMB.HMF AI L RNGh st LB) (AHMB.hmF RNGh) (AHMB.hmS L RNGh) (AHMB.HMS_mono L RNGh)
           PWFB_defs.PWFB PWFB_defs.PWFB_IT _ _ _ PWFB_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ PWFB_cert.pwfb_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA []) ltac:(intros S0 [<-|[]]; exact (slsb_gen LB H4 H5))
           ltac:(cbn; tauto)).
Qed.

(* [comment removed for export] *)
Ltac entry_summ P IT T0 C H4 H5 :=
  lazymatch goal with |- SP.summ_okHSC _ _ _ _ _ _ _ _ ?S =>
    replace S with (SP.SUMY (SP.p_G P) T0 (SP.p_ex P) (SP.p_W P) (SP.p_A P) (SP.p_PS P) false (SP.p_CR P)) by (vm_compute; reflexivity) end;
  exact (SP.summ_of_pcheckHSC SG GP0 _ _ (NLMB.GP0_frame _) NLMB.GP0_vc (hmH _) (hmA _) (hmC _) AHMB.hmR (AHMB.HMC_sub AI _)
           (AHMB.HMF AI L RNGh st _) (AHMB.hmF RNGh) (AHMB.hmS L RNGh) (AHMB.HMS_mono L RNGh)
           P IT _ _ _ T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ C)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA []) ltac:(intros S0 [<-|[]]; exact (pwfsb_gen _ H4 H5))
           ltac:(cbn; tauto)).
Lemma sfpbs_gen : forall LB, (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) -> U5 LB -> sok GP0 LB SFPB_sum.SFPBS.
Proof. intros LB H4 H5. entry_summ SFPBP_defs.SFPBP SFPBP_defs.SFPBP_IT SFPBP_defs.T0 SFPBP_cert.sfpbp_cert H4 H5. Qed.
Lemma sfpcbs_gen : forall LB, (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) -> U5 LB -> sok GP0 LB SFPB_sum.SFPCBS.
Proof. intros LB H4 H5. entry_summ SFPCBP_defs.SFPCBP SFPCBP_defs.SFPCBP_IT SFPCBP_defs.T0 SFPCBP_cert.sfpcbp_cert H4 H5. Qed.
Lemma pffbs_gen : forall LB, (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) -> U5 LB -> sok GP0 LB SFPB_sum.PFFBS.
Proof. intros LB H4 H5. entry_summ PFFBP_defs.PFFBP PFFBP_defs.PFFBP_IT PFFBP_defs.T0 PFFBP_cert.pffbp_cert H4 H5. Qed.
Lemma pffcbs_gen : forall LB, (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) -> U5 LB -> sok GP0 LB SFPB_sum.PFFCBS.
Proof. intros LB H4 H5. entry_summ PFFCBP_defs.PFFCBP PFFCBP_defs.PFFCBP_IT PFFCBP_defs.T0 PFFCBP_cert.pffcbp_cert H4 H5. Qed.

(* [comment removed for export] *)
Lemma ghostfree_any : forall GP LB S, sok GP0 LB S -> ST.t_ghost (SP.sm_pre S) = [] -> Forall (fun X => ST.t_ghost X = []) (SP.sm_post S) ->
  sok GP LB S.
Proof. intros GP LB S H H0 HX. exact (AGS.summ_ghostfree SG GP0 GP _ _ _ _ _ _ S H0 HX H). Qed.

End G.

(* [comment removed for export] *)
Section W.
Context {rc : runConstT}.
Local Notation SG := bsegs.
Local Notation FB5 F := (mkABlock (ABFake 5) F 2048).
Local Notation sokW GP L RNG st LB S :=
  (SP.summ_okHSC SG GP (AHMB.hmH AI_W L RNG st LB) (AHMB.hmA AI_W LB) (AHMB.hmC AI_W LB) AHMB.hmR (AHMB.hmF RNG) (AHMB.hmS L RNG) S).

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
Theorem sumw_sfpb : forall (GP : nat -> list word -> (word -> option byte) -> Prop) (L : alayout) (RNG : footprint) (st : astate)
  (LB : list ablock) (F : Z),
  (forall FA FN, ~ In (mkABlock (ABFake 5) FA FN) LB) -> (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) ->
  rng_aimg RNG -> afake_rng L RNG -> sokW GP L RNG st (FB5 F :: LB) SFPB_sum.SFPBS.
Proof.
  intros GP L RNG st LB F N5 N4 HI HF.
  apply (NTOPB.ghostfree_any AI_W L RNG st); [| reflexivity | repeat constructor].
  exact (NTOPB.sfpbs_gen AI_W crtW_IMG_CI fflag afake_rng crtW_sm4_1 crtW_sm5_1 crtW_sf5 crtW_fake_flag crtW_fake_release L RNG st HF HI
           (FB5 F :: LB) (no4_fb5 F LB N4) (u5_fb5 F LB N5)).
Qed.
Theorem sumw_pffb : forall (GP : nat -> list word -> (word -> option byte) -> Prop) (L : alayout) (RNG : footprint) (st : astate)
  (LB : list ablock) (F : Z),
  (forall FA FN, ~ In (mkABlock (ABFake 5) FA FN) LB) -> (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) ->
  rng_aimg RNG -> afake_rng L RNG -> sokW GP L RNG st (FB5 F :: LB) SFPB_sum.PFFBS.
Proof.
  intros GP L RNG st LB F N5 N4 HI HF.
  apply (NTOPB.ghostfree_any AI_W L RNG st); [| reflexivity | repeat constructor].
  exact (NTOPB.pffbs_gen AI_W crtW_IMG_CI fflag afake_rng crtW_sm4_1 crtW_sm5_1 crtW_sf5 crtW_fake_flag crtW_fake_release L RNG st HF HI
           (FB5 F :: LB) (no4_fb5 F LB N4) (u5_fb5 F LB N5)).
Qed.
(* [comment removed for export] *)
Theorem sumc_sfpcb : forall (GP : nat -> list word -> (word -> option byte) -> Prop) (L : alayout) (RNG : footprint) (st : astate)
  (LB : list ablock) (F : Z) (p : AsanCtrl.aptr) (COPY n : Z),
  (forall FA FN, ~ In (mkABlock (ABFake 5) FA FN) LB) -> (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) ->
  rng_aimg RNG -> afake_rng L RNG -> sokW GP L RNG st (HB p COPY n :: FB5 F :: LB) SFPB_sum.SFPCBS.
Proof.
  intros GP L RNG st LB F p COPY n N5 N4 HI HF.
  apply (NTOPB.ghostfree_any AI_W L RNG st); [| reflexivity | repeat constructor].
  exact (NTOPB.sfpcbs_gen AI_W crtW_IMG_CI fflag afake_rng crtW_sm4_1 crtW_sm5_1 crtW_sf5 crtW_fake_flag crtW_fake_release L RNG st HF HI
           (HB p COPY n :: FB5 F :: LB) (no4_hb p COPY n F LB N4) (u5_hb p COPY n F LB N5)).
Qed.
Theorem sumc_pffcb : forall (GP : nat -> list word -> (word -> option byte) -> Prop) (L : alayout) (RNG : footprint) (st : astate)
  (LB : list ablock) (F : Z) (p : AsanCtrl.aptr) (COPY n : Z),
  (forall FA FN, ~ In (mkABlock (ABFake 5) FA FN) LB) -> (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) ->
  rng_aimg RNG -> afake_rng L RNG -> sokW GP L RNG st (HB p COPY n :: FB5 F :: LB) SFPB_sum.PFFCBS.
Proof.
  intros GP L RNG st LB F p COPY n N5 N4 HI HF.
  apply (NTOPB.ghostfree_any AI_W L RNG st); [| reflexivity | repeat constructor].
  exact (NTOPB.pffcbs_gen AI_W crtW_IMG_CI fflag afake_rng crtW_sm4_1 crtW_sm5_1 crtW_sf5 crtW_fake_flag crtW_fake_release L RNG st HF HI
           (HB p COPY n :: FB5 F :: LB) (no4_hb p COPY n F LB N4) (u5_hb p COPY n F LB N5)).
Qed.
End W.
End NTOPB.
