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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg ABase AMalloc_iface AU_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegCall SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AHMB AGLS AMEMHB AMEMHBN AMEMHBS ABR_memB ABR_memBS ABR_mvB ABR_mvBN SLOWG NRMG NRMC NRCB
  NUMB_lm NUMB_lmn NUMB_nd.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require PMBN_defs PMBN_cert PMBN_sum PDCB_defs PDCB_cert PDCB_sum P5BN_defs P5BN_cert P5BN_sum
  SHLBN_defs SHLBN_cert SHLBN_sum HI64B_defs HI64B_cert HI64B_sum LMBN_sum NDCB_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require SLOWBB_defs SLOWBB_cert SLOWBB_vcs SLOWBBN_defs SLOWBBN_cert SLOWBBN_vcs
  SLOWBBF_defs SLOWBBF_cert SLOWBBF_vcs SLOWBBE_defs SLOWBBE_cert SLOWBBCN_defs SLOWBBCN_cert SLOWBBCF_defs SLOWBBCF_cert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Module NSBB.
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
  rw_cells bsegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
  /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
  /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
  /\ ~ in_ranges CI (fflag L cls F).
Hypothesis HFR : forall L RNG st LB m cls F N,
  AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
  AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
Local Notation SG := bsegs.
Local Notation GP0 := NLMB.GP0.
Local Notation GPN := NLMBN.GPN.
Definition GPS := SNG.sng_gp SG.
Hypothesis GV1 : Forall (SG.vc_holds SG GPS) SLOWBB_vcs.SLOWBG1_GV.
Hypothesis GVN : Forall (SG.vc_holds SG GPS) SLOWBBN_vcs.SLOWBGN_GV.
Hypothesis GVF : Forall (SG.vc_holds SG GPS) SLOWBBF_vcs.SLOWBGF_GV.
Local Notation hmH LB := (AHMB.hmH AI L RNGh st LB).
Local Notation hmA LB := (AHMB.hmA AI LB).
Local Notation hmC LB := (AHMB.hmC AI LB).
Local Notation sok GP LB S := (SP.summ_okHSC SG GP (hmH LB) (hmA LB) (hmC LB) AHMB.hmR (AHMB.hmF RNGh) (AHMB.hmS L RNGh) S).
Local Notation summ_of P T := (SP.SUMY (SP.p_G P) T (SP.p_ex P) (SP.p_W P) (SP.p_A P) (SP.p_PS P) false (SP.p_CR P)).
Local Notation U5 LB0 := (forall F1 n1 F2 n2, In (mkABlock (ABFake 5) F1 n1) LB0 -> In (mkABlock (ABFake 5) F2 n2) LB0 -> F1 = F2).
Local Notation U4 LB0 := (forall F1 n1 F2 n2, In (mkABlock (ABFake 4) F1 n1) LB0 -> In (mkABlock (ABFake 4) F2 n2) LB0 -> F1 = F2).

Lemma GPNB_vc : forall c, NRCB.nrcb_ok SG c = true -> SG.vc_holds SG GPN c.
Proof. intros c H. exact (NRCB.nrcb_ok_sound SG c H). Qed.

(* [comment removed for export] *)
Ltac msag := apply (NLMB.summ_okH_HSC AI L RNGh st);
  first [ apply ABRB.msag_ok; lia | apply ABRB.msah_ok; lia | apply ABRBS.msags_ok; lia | apply ABRVB.mvah_ok; lia ].

(* [comment removed for export] *)
Lemma hi64sb_summ : forall LB0, sok GPN LB0 HI64B_sum.HI64SB.
Proof.
  intros LB0.
  exact (SP.summ_of_pcheckHSC SG GPN _ _ NLMBN.GPN_frame NLMBN.GPN_vc (hmH LB0) (hmA LB0) (hmC LB0) AHMB.hmR (AHMB.HMC_sub AI LB0)
           (AHMB.HMF AI L RNGh st LB0) (AHMB.hmF RNGh) (AHMB.hmS L RNGh) (AHMB.HMS_mono L RNGh)
           HI64B_defs.HI64B HI64B_defs.HI64B_IT _ _ _ HI64B_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ HI64B_cert.hi64b_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA []) ltac:(intros S0 []) ltac:(cbn; tauto)).
Qed.
Lemma shlsbn_summ : forall LB0, sok GPN LB0 SHLBN_sum.SHLSBN.
Proof.
  intros LB0.
  exact (SP.summ_of_pcheckHSC SG GPN _ _ NLMBN.GPN_frame GPNB_vc (hmH LB0) (hmA LB0) (hmC LB0) AHMB.hmR (AHMB.HMC_sub AI LB0)
           (AHMB.HMF AI L RNGh st LB0) (AHMB.hmF RNGh) (AHMB.hmS L RNGh) (AHMB.HMS_mono L RNGh)
           SHLBN_defs.SHLBN SHLBN_defs.SHLBN_IT _ _ _ SHLBN_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ SHLBN_cert.shlbn_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA [])
           ltac:(intros S0 [<-|[]]; apply (NLMB.summ_okH_HSC AI L RNGh st LB0); apply ABRVBN.mvahn_ok; lia)
           ltac:(cbn; tauto)).
Qed.
Lemma p5sbn_summ : forall LB0, U5 LB0 -> sok GPN LB0 P5BN_sum.P5SBN.
Proof.
  intros LB0 H5.
  exact (SP.summ_of_pcheckHSC SG GPN _ _ NLMBN.GPN_frame NLMBN.GPN_vc (hmH LB0) (hmA LB0) (hmC LB0) AHMB.hmR (AHMB.HMC_sub AI LB0)
           (AHMB.HMF AI L RNGh st LB0) (AHMB.hmF RNGh) (AHMB.hmS L RNGh) (AHMB.HMS_mono L RNGh)
           P5BN_defs.P5BN P5BN_defs.P5BN_IT _ _ _ P5BN_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ P5BN_cert.p5bn_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA [])
           ltac:(intros S0 [<-|[]]; exact (NLMBN.lmsbn_ok AI IMG_CI fflag rng_fs HSM5 HSF5 L RNGh st LB0 H5 HFS HIMG))
           ltac:(cbn; tauto)).
Qed.
Lemma pdsb_summ : forall LB0, U5 LB0 -> sok GPN LB0 PDCB_sum.PDSB.
Proof.
  intros LB0 H5.
  exact (SP.summ_of_pcheckHSC SG GPN _ _ NLMBN.GPN_frame GPNB_vc (hmH LB0) (hmA LB0) (hmC LB0) AHMB.hmR (AHMB.HMC_sub AI LB0)
           (AHMB.HMF AI L RNGh st LB0) (AHMB.hmF RNGh) (AHMB.hmS L RNGh) (AHMB.HMS_mono L RNGh)
           PDCB_defs.PDCB PDCB_defs.PDCB_IT _ _ _ PDCB_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ PDCB_cert.pdcb_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA [])
           ltac:(intros S0 [<-|[<-|[<-|[]]]];
                 first [ exact (p5sbn_summ LB0 H5) | exact (shlsbn_summ LB0) | exact (hi64sb_summ LB0) ])
           ltac:(cbn; tauto)).
Qed.
Lemma pmsbn_summ : forall LB0, sok GPN LB0 PMBN_sum.PMSBN.
Proof.
  intros LB0.
  exact (SP.summ_of_pcheckHSC SG GPN _ _ NLMBN.GPN_frame GPNB_vc (hmH LB0) (hmA LB0) (hmC LB0) AHMB.hmR (AHMB.HMC_sub AI LB0)
           (AHMB.HMF AI L RNGh st LB0) (AHMB.hmF RNGh) (AHMB.hmS L RNGh) (AHMB.HMS_mono L RNGh)
           PMBN_defs.PMBN PMBN_defs.PMBN_IT _ _ _ PMBN_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ PMBN_cert.pmbn_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA []) ltac:(intros S0 []) ltac:(cbn; tauto)).
Qed.
Lemma ndsb_n : forall LB0, U4 LB0 -> U5 LB0 -> sok GPN LB0 NDCB_sum.NDSB.
Proof.
  intros LB0 H4 H5.
  exact (AGS.summ_ghostfree SG GP0 GPN _ _ _ _ _ _ NDCB_sum.NDSB eq_refl ltac:(repeat constructor)
           (NNDB.ndsb_ok AI IMG_CI fflag rng_fs HSM4 HSM5 HSF5 L RNGh st LB0 H4 H5 HFS HIMG HFF HFR)).
Qed.

(* [comment removed for export] *)
Lemma slab_summ : forall LB0, sok GPS LB0 (summ_of SLOWBB_defs.SLOWBB SLOWBB_defs.T0).
Proof.
  intros LB0.
  exact (SP.summ_of_pcheckHSC SG GPS _ _ (SNG.sng_frame SG) (fun c H => SG.gvc_list_ok SG GPS SLOWBB_vcs.SLOWBG1_GV c GV1 H)
           (hmH LB0) (hmA LB0) (hmC LB0) AHMB.hmR (AHMB.HMC_sub AI LB0)
           (AHMB.HMF AI L RNGh st LB0) (AHMB.hmF RNGh) (AHMB.hmS L RNGh) (AHMB.HMS_mono L RNGh)
           SLOWBB_defs.SLOWBB SLOWBB_defs.SLOWBB_IT _ _ _ SLOWBB_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ SLOWBB_cert.slowbb_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA [])
           ltac:(intros S0 HS0; cbn [SP.p_cs SLOWBB_defs.SLOWBB SP.PGCA] in HS0;
                 repeat (destruct HS0 as [<-|HS0]; [msag|]); destruct HS0)
           ltac:(cbn; tauto)).
Qed.
Lemma slabn_summ : forall LB0, sok GPS LB0 (summ_of SLOWBBN_defs.SLOWBBN SLOWBBN_defs.T0).
Proof.
  intros LB0.
  exact (SP.summ_of_pcheckHSC SG GPS _ _ (SNG.sng_frame SG) (fun c H => SG.gvc_list_ok SG GPS SLOWBBN_vcs.SLOWBGN_GV c GVN H)
           (hmH LB0) (hmA LB0) (hmC LB0) AHMB.hmR (AHMB.HMC_sub AI LB0)
           (AHMB.HMF AI L RNGh st LB0) (AHMB.hmF RNGh) (AHMB.hmS L RNGh) (AHMB.HMS_mono L RNGh)
           SLOWBBN_defs.SLOWBBN SLOWBBN_defs.SLOWBBN_IT _ _ _ SLOWBBN_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ SLOWBBN_cert.slowbbn_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA []) ltac:(intros S0 []) ltac:(cbn; tauto)).
Qed.
Lemma slabf_summ : forall LB0, sok GPS LB0 (summ_of SLOWBBF_defs.SLOWBBF SLOWBBF_defs.T0).
Proof.
  intros LB0.
  exact (SP.summ_of_pcheckHSC SG GPS _ _ (SNG.sng_frame SG) (fun c H => SG.gvc_list_ok SG GPS SLOWBBF_vcs.SLOWBGF_GV c GVF H)
           (hmH LB0) (hmA LB0) (hmC LB0) AHMB.hmR (AHMB.HMC_sub AI LB0)
           (AHMB.HMF AI L RNGh st LB0) (AHMB.hmF RNGh) (AHMB.hmS L RNGh) (AHMB.HMS_mono L RNGh)
           SLOWBBF_defs.SLOWBBF SLOWBBF_defs.SLOWBBF_IT _ _ _ SLOWBBF_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ SLOWBBF_cert.slowbbf_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA [])
           ltac:(intros S0 HS0; cbn [SP.p_cs SLOWBBF_defs.SLOWBBF SP.PGCA] in HS0;
                 repeat (destruct HS0 as [<-|HS0]; [msag|]); destruct HS0)
           ltac:(cbn; tauto)).
Qed.
Lemma slabe_summ : forall LB0, sok GP0 LB0 (summ_of SLOWBBE_defs.SLOWBBE SLOWBBE_defs.T0).
Proof.
  intros LB0.
  exact (SP.summ_of_pcheckHSC SG GP0 _ _ (NLMB.GP0_frame _) NLMB.GP0_vc (hmH LB0) (hmA LB0) (hmC LB0) AHMB.hmR (AHMB.HMC_sub AI LB0)
           (AHMB.HMF AI L RNGh st LB0) (AHMB.hmF RNGh) (AHMB.hmS L RNGh) (AHMB.HMS_mono L RNGh)
           SLOWBBE_defs.SLOWBBE SLOWBBE_defs.SLOWBBE_IT _ _ _ SLOWBBE_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ SLOWBBE_cert.slowbbe_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA []) ltac:(intros S0 []) ltac:(cbn; tauto)).
Qed.
Lemma slabcn_summ : forall LB0, U4 LB0 -> U5 LB0 -> sok GPN LB0 (summ_of SLOWBBCN_defs.SLOWBBCN SLOWBBCN_defs.T0).
Proof.
  intros LB0 H4 H5.
  exact (SP.summ_of_pcheckHSC SG GPN _ _ NLMBN.GPN_frame GPNB_vc (hmH LB0) (hmA LB0) (hmC LB0) AHMB.hmR (AHMB.HMC_sub AI LB0)
           (AHMB.HMF AI L RNGh st LB0) (AHMB.hmF RNGh) (AHMB.hmS L RNGh) (AHMB.HMS_mono L RNGh)
           SLOWBBCN_defs.SLOWBBCN SLOWBBCN_defs.SLOWBBCN_IT _ _ _ SLOWBBCN_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ SLOWBBCN_cert.slowbbcn_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA [])
           ltac:(intros S0 [<-|[<-|[<-|[<-|[]]]]];
                 first [ exact (pmsbn_summ LB0) | exact (pdsb_summ LB0 H5) | exact (ndsb_n LB0 H4 H5) | msag ])
           ltac:(cbn; tauto)).
Qed.
Lemma slabcf_summ : forall LB0, U4 LB0 -> U5 LB0 -> sok GPN LB0 (summ_of SLOWBBCF_defs.SLOWBBCF SLOWBBCF_defs.T0).
Proof.
  intros LB0 H4 H5.
  exact (SP.summ_of_pcheckHSC SG GPN _ _ NLMBN.GPN_frame GPNB_vc (hmH LB0) (hmA LB0) (hmC LB0) AHMB.hmR (AHMB.HMC_sub AI LB0)
           (AHMB.HMF AI L RNGh st LB0) (AHMB.hmF RNGh) (AHMB.hmS L RNGh) (AHMB.HMS_mono L RNGh)
           SLOWBBCF_defs.SLOWBBCF SLOWBBCF_defs.SLOWBBCF_IT _ _ _ SLOWBBCF_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ SLOWBBCF_cert.slowbbcf_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA [])
           ltac:(intros S0 [<-|[<-|[<-|[<-|[]]]]];
                 first [ exact (pmsbn_summ LB0) | exact (pdsb_summ LB0 H5) | exact (ndsb_n LB0 H4 H5) | msag ])
           ltac:(cbn; tauto)).
Qed.

(* [comment removed for export] *)
Definition CRC : list SP.win := SP.p_CR SLOWBBCN_defs.SLOWBBCN.
Definition PSB : option expr := Some SLOWBB_defs.vSP.
Definition XSS : ST.tmpl := SLOWBBE_defs.XSS.
Definition SBODY : SP.summ :=
  SP.SUMY (SP.p_G SLOWBB_defs.SLOWBB) SLOWBB_defs.T0 [XSS] (SP.p_W SLOWBB_defs.SLOWBB) (SP.p_A SLOWBB_defs.SLOWBB) PSB false CRC.

Lemma gf_ok : forall LB0 S, sok GP0 LB0 S -> ST.t_ghost (SP.sm_pre S) = [] -> Forall (fun X => ST.t_ghost X = []) (SP.sm_post S) ->
  sok GPS LB0 S.
Proof. intros LB0 S H H0 HX. exact (AGS.summ_ghostfree SG GP0 GPS _ _ _ _ _ _ S H0 HX H). Qed.
Lemma gfn_ok : forall LB0 S, sok GPN LB0 S -> ST.t_ghost (SP.sm_pre S) = [] -> Forall (fun X => ST.t_ghost X = []) (SP.sm_post S) ->
  sok GPS LB0 S.
Proof. intros LB0 S H H0 HX. exact (AGS.summ_ghostfree SG GPN GPS _ _ _ _ _ _ S H0 HX H). Qed.

Ltac side := first [ reflexivity | (vm_compute; reflexivity) | (left; reflexivity) | (right; reflexivity) | apply incl_refl
                   | (intros ? []) ].

Lemma sn_ok : forall LB0, U4 LB0 -> U5 LB0 ->
  sok GPS LB0 (SP.SUMY (SP.p_G SLOWBBN_defs.SLOWBBN) SLOWBBN_defs.T0 [XSS] (SP.p_W SLOWBBN_defs.SLOWBBN) (SP.p_A SLOWBBN_defs.SLOWBBN) PSB false CRC).
Proof.
  intros LB0 H4 H5.
  pose proof (AGS.summ_seq SG GPS _ _ _ _ _ _ (summ_of SLOWBBN_defs.SLOWBBN SLOWBBN_defs.T0) (summ_of SLOWBBE_defs.SLOWBBE SLOWBBE_defs.T0)
                SLOWBBN_defs.XCLN PSB CRC [SLOWBBN_defs.XCF; XSS] (slabn_summ LB0) (gf_ok LB0 _ (slabe_summ LB0) eq_refl ltac:(repeat constructor))
                ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side)
                ltac:(side) ltac:(side) ltac:(side) ltac:(side)
                ltac:(intros Y [<-|[<-|[]]]; [left; reflexivity | right; left; reflexivity])
                ltac:(intros Y [<-|[]]; right; left; reflexivity)) as S1.
  exact (AGS.summ_seq SG GPS _ _ _ _ _ _ _ (summ_of SLOWBBCN_defs.SLOWBBCN SLOWBBCN_defs.T0)
           SLOWBBN_defs.XCF PSB CRC [XSS] S1 (gfn_ok LB0 _ (slabcn_summ LB0 H4 H5) eq_refl ltac:(repeat constructor))
           ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side)
           ltac:(side) ltac:(side) ltac:(side) ltac:(side)
           ltac:(intros Y [<-|[<-|[]]]; [left; reflexivity | right; left; reflexivity])
           ltac:(intros Y [<-|[]]; left; vm_compute; reflexivity)).
Qed.

Lemma sf_ok : forall LB0, U4 LB0 -> U5 LB0 ->
  sok GPS LB0 (SP.SUMY (SP.p_G SLOWBBF_defs.SLOWBBF) SLOWBBF_defs.T0 [XSS] (SP.p_W SLOWBBF_defs.SLOWBBF) (SP.p_A SLOWBBF_defs.SLOWBBF) PSB false CRC).
Proof.
  intros LB0 H4 H5.
  pose proof (AGS.summ_seq SG GPS _ _ _ _ _ _ (summ_of SLOWBBF_defs.SLOWBBF SLOWBBF_defs.T0) (summ_of SLOWBBE_defs.SLOWBBE SLOWBBE_defs.T0)
                SLOWBBF_defs.XCLN PSB CRC [SLOWBBF_defs.XCF; XSS] (slabf_summ LB0) (gf_ok LB0 _ (slabe_summ LB0) eq_refl ltac:(repeat constructor))
                ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side)
                ltac:(side) ltac:(side) ltac:(side) ltac:(side)
                ltac:(intros Y [<-|[<-|[]]]; [left; reflexivity | right; left; reflexivity])
                ltac:(intros Y [<-|[]]; right; left; reflexivity)) as S1.
  exact (AGS.summ_seq SG GPS _ _ _ _ _ _ _ (summ_of SLOWBBCF_defs.SLOWBBCF SLOWBBCF_defs.T0)
           SLOWBBF_defs.XCF PSB CRC [XSS] S1 (gfn_ok LB0 _ (slabcf_summ LB0 H4 H5) eq_refl ltac:(repeat constructor))
           ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side)
           ltac:(side) ltac:(side) ltac:(side) ltac:(side)
           ltac:(intros Y [<-|[<-|[]]]; [left; reflexivity | right; left; reflexivity])
           ltac:(intros Y [<-|[]]; left; vm_compute; reflexivity)).
Qed.

Theorem sbody_ok : forall LB0, U4 LB0 -> U5 LB0 -> sok GP0 LB0 SBODY.
Proof.
  intros LB0 H4 H5.
  pose proof (AGS.summ_seq SG GPS _ _ _ _ _ _ (summ_of SLOWBB_defs.SLOWBB SLOWBB_defs.T0) _
                SLOWBB_defs.XN PSB CRC [SLOWBB_defs.XF; SLOWBB_defs.XE; XSS] (slab_summ LB0) (sn_ok LB0 H4 H5)
                ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side)
                ltac:(side) ltac:(side) ltac:(side) ltac:(side)
                ltac:(intros Y [<-|[<-|[<-|[]]]]; [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity])
                ltac:(intros Y [<-|[]]; right; right; left; reflexivity)) as S1.
  pose proof (AGS.summ_seq SG GPS _ _ _ _ _ _ _ _
                SLOWBB_defs.XF PSB CRC [SLOWBB_defs.XE; XSS] S1 (sf_ok LB0 H4 H5)
                ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side)
                ltac:(side) ltac:(side) ltac:(side) ltac:(side)
                ltac:(intros Y [<-|[<-|[<-|[]]]]; [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity])
                ltac:(intros Y [<-|[]]; right; left; reflexivity)) as S2.
  pose proof (AGS.summ_seq SG GPS _ _ _ _ _ _ _ (summ_of SLOWBBE_defs.SLOWBBE SLOWBBE_defs.T0)
                SLOWBB_defs.XE PSB CRC [XSS] S2 (gf_ok LB0 _ (slabe_summ LB0) eq_refl ltac:(repeat constructor))
                ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side) ltac:(side)
                ltac:(side) ltac:(side) ltac:(side) ltac:(side)
                ltac:(intros Y [<-|[<-|[]]]; [left; reflexivity | right; left; reflexivity])
                ltac:(intros Y [<-|[]]; left; reflexivity)) as S3.
  refine (AGS.summ_ghostfree SG GPS GP0 _ _ _ _ _ _ SBODY eq_refl _ S3). repeat constructor.
Qed.

End SB.
End NSBB.
