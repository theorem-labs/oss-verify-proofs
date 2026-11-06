(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec StoreOk AxSymExec3 AxSymExec3Sound AsanPlanCore AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec FP Image RunConst.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import AsanEmbed AsanCtrl.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg ABase AMalloc_iface AU_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegCall SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AHM AGLS AMEMH ABR_mem ABR_mv SLOWG NUMA_lm NUMA_nd.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require PMA_defs PMA_cert PMA_sum PDCA_defs PDCA_cert PDCA_sum P5A_sum NDCA_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require SLOWAB_defs SLOWAB_cert SLOWAB_vcs SLOWABN_defs SLOWABN_cert SLOWABN_vcs
  SLOWABF_defs SLOWABF_cert SLOWABF_vcs SLOWABE_defs SLOWABE_cert SLOWABCN_defs SLOWABCN_cert SLOWABCF_defs SLOWABCF_cert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Module NSB.
Section SB.
Context {rc : runConstT}.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis HSM4 : stack_malloc_4_stmt1 AI fflag rng_fs.
Hypothesis HSM5 : stack_malloc_5_stmt1 AI fflag rng_fs.
Hypothesis HSF5 : stack_free_5_stmt AI fflag.
Variables (L : alayout) (RNGh : footprint) (st : astate).
Hypothesis HFS : rng_fs L RNGh.
Hypothesis HIMG : rng_aimg RNGh.
Hypothesis HFF : forall L RNG st LB m cls F N,
  AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
  rw_cells asegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
  /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
  /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
  /\ ~ in_ranges CI (fflag L cls F).
Hypothesis HFR : forall L RNG st LB m cls F N,
  AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
  AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
Local Notation SG := asegs.
Local Notation GP0 := NLM.GP0.
Definition GPS := SNG.sng_gp SG.
Hypothesis GV1 : Forall (SG.vc_holds SG GPS) SLOWAB_vcs.SLOWAG1_GV.
Hypothesis GVN : Forall (SG.vc_holds SG GPS) SLOWABN_vcs.SLOWAGN_GV.
Hypothesis GVF : Forall (SG.vc_holds SG GPS) SLOWABF_vcs.SLOWAGF_GV.
Local Notation hmH LB := (AHM.hmH AI L RNGh st LB).
Local Notation hmA LB := (AHM.hmA AI LB).
Local Notation hmC LB := (AHM.hmC AI LB).
Local Notation sok GP LB S := (SP.summ_okHSC SG GP (hmH LB) (hmA LB) (hmC LB) AHM.hmR (AHM.hmF RNGh) (AHM.hmS L RNGh) S).
Local Notation summ_of P T := (SP.SUMY (SP.p_G P) T (SP.p_ex P) (SP.p_W P) (SP.p_A P) (SP.p_PS P) false (SP.p_CR P)).
Local Notation U5 LB0 := (forall F1 n1 F2 n2, In (mkABlock (ABFake 5) F1 n1) LB0 -> In (mkABlock (ABFake 5) F2 n2) LB0 -> F1 = F2).
Local Notation U4 LB0 := (forall F1 n1 F2 n2, In (mkABlock (ABFake 4) F1 n1) LB0 -> In (mkABlock (ABFake 4) F2 n2) LB0 -> F1 = F2).

Ltac msag := apply (NLM.summ_okH_HSC AI L RNGh st); first [ apply ABR.msag_ok; lia | apply ABR.msah_ok; lia | apply ABRV.mvah_ok; lia ].

(* [comment removed for export] *)
Lemma pmsa_summ : forall LB0, sok GP0 LB0 PMA_sum.PMSA.
Proof.
  intros LB0.
  exact (SP.summ_of_pcheckHSC SG GP0 _ _ (NLM.GP0_frame _) NLM.GP0_vc (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR (AHM.HMC_sub AI LB0)
           (AHM.HMF AI L RNGh st LB0) (AHM.hmF RNGh) (AHM.hmS L RNGh) (AHM.HMS_mono L RNGh)
           PMA_defs.PMA PMA_defs.PMA_IT _ _ _ PMA_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ PMA_cert.pma_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA []) ltac:(intros S0 []) ltac:(cbn; tauto)).
Qed.
Lemma pdsa_summ : forall LB0, U5 LB0 -> sok GP0 LB0 PDCA_sum.PDSA.
Proof.
  intros LB0 H5.
  exact (SP.summ_of_pcheckHSC SG GP0 _ _ (NLM.GP0_frame _) NLM.GP0_vc (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR (AHM.HMC_sub AI LB0)
           (AHM.HMF AI L RNGh st LB0) (AHM.hmF RNGh) (AHM.hmS L RNGh) (AHM.HMS_mono L RNGh)
           PDCA_defs.PDCA PDCA_defs.PDCA_IT _ _ _ PDCA_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ PDCA_cert.pdca_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA [])
           ltac:(intros S0 [<-|[<-|[<-|[]]]];
                 first [ exact (NND.p5sa_summ AI IMG_CI fflag rng_fs HSM5 HSF5 L RNGh st HFS HIMG LB0 H5) | msag ])
           ltac:(cbn; tauto)).
Qed.

(* [comment removed for export] *)
Lemma slab_summ : forall LB0, sok GPS LB0 (summ_of SLOWAB_defs.SLOWAB SLOWAB_defs.T0).
Proof.
  intros LB0.
  exact (SP.summ_of_pcheckHSC SG GPS _ _ (SNG.sng_frame SG) (fun c H => SG.gvc_list_ok SG GPS SLOWAB_vcs.SLOWAG1_GV c GV1 H)
           (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR (AHM.HMC_sub AI LB0)
           (AHM.HMF AI L RNGh st LB0) (AHM.hmF RNGh) (AHM.hmS L RNGh) (AHM.HMS_mono L RNGh)
           SLOWAB_defs.SLOWAB SLOWAB_defs.SLOWAB_IT _ _ _ SLOWAB_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ SLOWAB_cert.slowab_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA [])
           ltac:(intros S0 HS0; cbn [SP.p_cs SLOWAB_defs.SLOWAB SP.PGCA] in HS0;
                 repeat (destruct HS0 as [<-|HS0]; [msag|]); destruct HS0)
           ltac:(cbn; tauto)).
Qed.
Lemma slabn_summ : forall LB0, sok GPS LB0 (summ_of SLOWABN_defs.SLOWABN SLOWABN_defs.T0).
Proof.
  intros LB0.
  exact (SP.summ_of_pcheckHSC SG GPS _ _ (SNG.sng_frame SG) (fun c H => SG.gvc_list_ok SG GPS SLOWABN_vcs.SLOWAGN_GV c GVN H)
           (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR (AHM.HMC_sub AI LB0)
           (AHM.HMF AI L RNGh st LB0) (AHM.hmF RNGh) (AHM.hmS L RNGh) (AHM.HMS_mono L RNGh)
           SLOWABN_defs.SLOWABN SLOWABN_defs.SLOWABN_IT _ _ _ SLOWABN_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ SLOWABN_cert.slowabn_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA []) ltac:(intros S0 []) ltac:(cbn; tauto)).
Qed.
Lemma slabf_summ : forall LB0, sok GPS LB0 (summ_of SLOWABF_defs.SLOWABF SLOWABF_defs.T0).
Proof.
  intros LB0.
  exact (SP.summ_of_pcheckHSC SG GPS _ _ (SNG.sng_frame SG) (fun c H => SG.gvc_list_ok SG GPS SLOWABF_vcs.SLOWAGF_GV c GVF H)
           (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR (AHM.HMC_sub AI LB0)
           (AHM.HMF AI L RNGh st LB0) (AHM.hmF RNGh) (AHM.hmS L RNGh) (AHM.HMS_mono L RNGh)
           SLOWABF_defs.SLOWABF SLOWABF_defs.SLOWABF_IT _ _ _ SLOWABF_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ SLOWABF_cert.slowabf_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA [])
           ltac:(intros S0 HS0; cbn [SP.p_cs SLOWABF_defs.SLOWABF SP.PGCA] in HS0;
                 repeat (destruct HS0 as [<-|HS0]; [msag|]); destruct HS0)
           ltac:(cbn; tauto)).
Qed.
Lemma slabe_summ : forall LB0, sok GP0 LB0 (summ_of SLOWABE_defs.SLOWABE SLOWABE_defs.T0).
Proof.
  intros LB0.
  exact (SP.summ_of_pcheckHSC SG GP0 _ _ (NLM.GP0_frame _) NLM.GP0_vc (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR (AHM.HMC_sub AI LB0)
           (AHM.HMF AI L RNGh st LB0) (AHM.hmF RNGh) (AHM.hmS L RNGh) (AHM.HMS_mono L RNGh)
           SLOWABE_defs.SLOWABE SLOWABE_defs.SLOWABE_IT _ _ _ SLOWABE_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ SLOWABE_cert.slowabe_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA []) ltac:(intros S0 []) ltac:(cbn; tauto)).
Qed.
Lemma slabcn_summ : forall LB0, U4 LB0 -> U5 LB0 -> sok GP0 LB0 (summ_of SLOWABCN_defs.SLOWABCN SLOWABCN_defs.T0).
Proof.
  intros LB0 H4 H5.
  exact (SP.summ_of_pcheckHSC SG GP0 _ _ (NLM.GP0_frame _) NLM.GP0_vc (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR (AHM.HMC_sub AI LB0)
           (AHM.HMF AI L RNGh st LB0) (AHM.hmF RNGh) (AHM.hmS L RNGh) (AHM.HMS_mono L RNGh)
           SLOWABCN_defs.SLOWABCN SLOWABCN_defs.SLOWABCN_IT _ _ _ SLOWABCN_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ SLOWABCN_cert.slowabcn_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA [])
           ltac:(intros S0 [<-|[<-|[<-|[<-|[]]]]];
                 first [ exact (pmsa_summ LB0) | exact (pdsa_summ LB0 H5)
                       | exact (NND.ndsa_ok AI IMG_CI fflag rng_fs HSM4 HSM5 HSF5 L RNGh st LB0 H4 H5 HFS HIMG HFF HFR) | msag ])
           ltac:(cbn; tauto)).
Qed.
Lemma slabcf_summ : forall LB0, U4 LB0 -> U5 LB0 -> sok GP0 LB0 (summ_of SLOWABCF_defs.SLOWABCF SLOWABCF_defs.T0).
Proof.
  intros LB0 H4 H5.
  exact (SP.summ_of_pcheckHSC SG GP0 _ _ (NLM.GP0_frame _) NLM.GP0_vc (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR (AHM.HMC_sub AI LB0)
           (AHM.HMF AI L RNGh st LB0) (AHM.hmF RNGh) (AHM.hmS L RNGh) (AHM.HMS_mono L RNGh)
           SLOWABCF_defs.SLOWABCF SLOWABCF_defs.SLOWABCF_IT _ _ _ SLOWABCF_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ SLOWABCF_cert.slowabcf_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA [])
           ltac:(intros S0 [<-|[<-|[<-|[<-|[]]]]];
                 first [ exact (pmsa_summ LB0) | exact (pdsa_summ LB0 H5)
                       | exact (NND.ndsa_ok AI IMG_CI fflag rng_fs HSM4 HSM5 HSF5 L RNGh st LB0 H4 H5 HFS HIMG HFF HFR) | msag ])
           ltac:(cbn; tauto)).
Qed.

(* [comment removed for export] *)
Definition CRC : list SP.win := SP.p_CR SLOWABCN_defs.SLOWABCN.
Definition PSB : option expr := Some SLOWAB_defs.vSP.
Definition XSS : ST.tmpl := SLOWABE_defs.XSS.
Definition SBODY : SP.summ :=
  SP.SUMY (SP.p_G SLOWAB_defs.SLOWAB) SLOWAB_defs.T0 [XSS] (SP.p_W SLOWAB_defs.SLOWAB) (SP.p_A SLOWAB_defs.SLOWAB) PSB false CRC.

Lemma gf_ok : forall LB0 S, sok GP0 LB0 S -> ST.t_ghost (SP.sm_pre S) = [] -> Forall (fun X => ST.t_ghost X = []) (SP.sm_post S) ->
  sok GPS LB0 S.
Proof. intros LB0 S H H0 HX. exact (AGS.summ_ghostfree SG GP0 GPS _ _ _ _ _ _ S H0 HX H). Qed.

Ltac side := first [ reflexivity | (vm_compute; reflexivity) | (left; reflexivity) | (right; reflexivity) | apply incl_refl
                   | (intros ? []) ].

Lemma sn_ok : forall LB0, U4 LB0 -> U5 LB0 ->
  sok GPS LB0 (SP.SUMY (SP.p_G SLOWABN_defs.SLOWABN) SLOWABN_defs.T0 [XSS] (SP.p_W SLOWABN_defs.SLOWABN) (SP.p_A SLOWABN_defs.SLOWABN) PSB false CRC).
Proof.
  intros LB0 H4 H5.
  pose proof (AGS.summ_seq SG GPS _ _ _ _ _ _ (summ_of SLOWABN_defs.SLOWABN SLOWABN_defs.T0) (summ_of SLOWABE_defs.SLOWABE SLOWABE_defs.T0)
                SLOWABN_defs.XCLN PSB CRC [SLOWABN_defs.XCF; XSS] (slabn_summ LB0) (gf_ok LB0 _ (slabe_summ LB0) eq_refl ltac:(repeat constructor))
                ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side)
                ltac:(side) ltac:(side) ltac:(side) ltac:(side)
                ltac:(intros Y [<-|[<-|[]]]; [left; reflexivity | right; left; reflexivity])
                ltac:(intros Y [<-|[]]; right; left; reflexivity)) as S1.
  exact (AGS.summ_seq SG GPS _ _ _ _ _ _ _ (summ_of SLOWABCN_defs.SLOWABCN SLOWABCN_defs.T0)
           SLOWABN_defs.XCF PSB CRC [XSS] S1 (gf_ok LB0 _ (slabcn_summ LB0 H4 H5) eq_refl ltac:(repeat constructor))
           ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side)
           ltac:(side) ltac:(side) ltac:(side) ltac:(side)
           ltac:(intros Y [<-|[<-|[]]]; [left; reflexivity | right; left; reflexivity])
           ltac:(intros Y [<-|[]]; left; vm_compute; reflexivity)).
Qed.

Lemma sf_ok : forall LB0, U4 LB0 -> U5 LB0 ->
  sok GPS LB0 (SP.SUMY (SP.p_G SLOWABF_defs.SLOWABF) SLOWABF_defs.T0 [XSS] (SP.p_W SLOWABF_defs.SLOWABF) (SP.p_A SLOWABF_defs.SLOWABF) PSB false CRC).
Proof.
  intros LB0 H4 H5.
  pose proof (AGS.summ_seq SG GPS _ _ _ _ _ _ (summ_of SLOWABF_defs.SLOWABF SLOWABF_defs.T0) (summ_of SLOWABE_defs.SLOWABE SLOWABE_defs.T0)
                SLOWABF_defs.XCLN PSB CRC [SLOWABF_defs.XCF; XSS] (slabf_summ LB0) (gf_ok LB0 _ (slabe_summ LB0) eq_refl ltac:(repeat constructor))
                ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side)
                ltac:(side) ltac:(side) ltac:(side) ltac:(side)
                ltac:(intros Y [<-|[<-|[]]]; [left; reflexivity | right; left; reflexivity])
                ltac:(intros Y [<-|[]]; right; left; reflexivity)) as S1.
  exact (AGS.summ_seq SG GPS _ _ _ _ _ _ _ (summ_of SLOWABCF_defs.SLOWABCF SLOWABCF_defs.T0)
           SLOWABF_defs.XCF PSB CRC [XSS] S1 (gf_ok LB0 _ (slabcf_summ LB0 H4 H5) eq_refl ltac:(repeat constructor))
           ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side)
           ltac:(side) ltac:(side) ltac:(side) ltac:(side)
           ltac:(intros Y [<-|[<-|[]]]; [left; reflexivity | right; left; reflexivity])
           ltac:(intros Y [<-|[]]; left; vm_compute; reflexivity)).
Qed.

Theorem sbody_ok : forall LB0, U4 LB0 -> U5 LB0 -> sok GP0 LB0 SBODY.
Proof.
  intros LB0 H4 H5.
  pose proof (AGS.summ_seq SG GPS _ _ _ _ _ _ (summ_of SLOWAB_defs.SLOWAB SLOWAB_defs.T0) _
                SLOWAB_defs.XN PSB CRC [SLOWAB_defs.XF; SLOWAB_defs.XE; XSS] (slab_summ LB0) (sn_ok LB0 H4 H5)
                ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side)
                ltac:(side) ltac:(side) ltac:(side) ltac:(side)
                ltac:(intros Y [<-|[<-|[<-|[]]]]; [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity])
                ltac:(intros Y [<-|[]]; right; right; left; reflexivity)) as S1.
  pose proof (AGS.summ_seq SG GPS _ _ _ _ _ _ _ _
                SLOWAB_defs.XF PSB CRC [SLOWAB_defs.XE; XSS] S1 (sf_ok LB0 H4 H5)
                ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side)
                ltac:(side) ltac:(side) ltac:(side) ltac:(side)
                ltac:(intros Y [<-|[<-|[<-|[]]]]; [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity])
                ltac:(intros Y [<-|[]]; right; left; reflexivity)) as S2.
  pose proof (AGS.summ_seq SG GPS _ _ _ _ _ _ _ (summ_of SLOWABE_defs.SLOWABE SLOWABE_defs.T0)
                SLOWAB_defs.XE PSB CRC [XSS] S2 (gf_ok LB0 _ (slabe_summ LB0) eq_refl ltac:(repeat constructor))
                ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side)
                ltac:(side) ltac:(side) ltac:(side) ltac:(side)
                ltac:(intros Y [<-|[<-|[]]]; [left; reflexivity | right; left; reflexivity])
                ltac:(intros Y [<-|[]]; left; reflexivity)) as S3.
  refine (AGS.summ_ghostfree SG GPS GP0 _ _ _ _ _ _ SBODY eq_refl _ S3). repeat constructor.
Qed.

End SB.
End NSB.
