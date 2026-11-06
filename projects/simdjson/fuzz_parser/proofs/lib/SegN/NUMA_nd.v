(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec StoreOk AxSymExec3 AxSymExec3Sound AsanPlanCore AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec FP Image RunConst InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import AsanEmbed AsanCtrl.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg ABase AMalloc_iface AU_iface AU_fuzz_kit RtCells AU_setsh.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegCall SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA Require Import SegLibBr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AHM AGLUE AGLR AGLX AGLC AGLF AGLM AMEMH ABR_mem ABR_mv NUMA_lm.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require LMA_sum P5A_defs P5A_cert P5A_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require NDCAS_defs NDCAE_defs NDCAE_cert NDCAB_defs NDCAB_cert NDCAF_defs NDCAF_cert NDCA_sum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Module NND.
Section ND.
Context {rc : runConstT}.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis HSM4 : stack_malloc_4_stmt1 AI fflag rng_fs.
Hypothesis HSM5 : stack_malloc_5_stmt1 AI fflag rng_fs.
Hypothesis HSF5 : stack_free_5_stmt AI fflag.
Variables (L : alayout) (RNGh : footprint) (st : astate) (LB : list ablock).
Hypothesis HC4 : forall F1 n1 F2 n2, In (mkABlock (ABFake 4) F1 n1) LB -> In (mkABlock (ABFake 4) F2 n2) LB -> F1 = F2.
Hypothesis HC5 : forall F1 n1 F2 n2, In (mkABlock (ABFake 5) F1 n1) LB -> In (mkABlock (ABFake 5) F2 n2) LB -> F1 = F2.
Hypothesis HFS : rng_fs L RNGh.
Hypothesis HIMG : rng_aimg RNGh.
(* [comment removed for export] *)
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
Local Notation hmH LB := (AHM.hmH AI L RNGh st LB).
Local Notation hmA LB := (AHM.hmA AI LB).
Local Notation hmC LB := (AHM.hmC AI LB).
Local Notation FB4 F := (mkABlock (ABFake 4) F 1024).

(* [comment removed for export] *)
Lemma c5_cons4 : forall F LB0, (forall F1 n1 F2 n2, In (mkABlock (ABFake 5) F1 n1) LB0 -> In (mkABlock (ABFake 5) F2 n2) LB0 -> F1 = F2) ->
  forall F1 n1 F2 n2, In (mkABlock (ABFake 5) F1 n1) (FB4 F :: LB0) -> In (mkABlock (ABFake 5) F2 n2) (FB4 F :: LB0) -> F1 = F2.
Proof.
  intros F LB0 H F1 n1 F2 n2 [E1|H1] [E2|H2]; try discriminate; try (injection E1; intros; discriminate);
    try (injection E2; intros; discriminate); exact (H F1 n1 F2 n2 H1 H2).
Qed.

(* [comment removed for export] *)
Lemma p5sa_summ : forall LB0, (forall F1 n1 F2 n2, In (mkABlock (ABFake 5) F1 n1) LB0 -> In (mkABlock (ABFake 5) F2 n2) LB0 -> F1 = F2) ->
  SP.summ_okHSC SG GP0 (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR (AHM.hmF RNGh) (AHM.hmS L RNGh) P5A_sum.P5SA.
Proof.
  intros LB0 H5.
  exact (SP.summ_of_pcheckHSC SG GP0 _ _ (NLM.GP0_frame _) NLM.GP0_vc (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR (AHM.HMC_sub AI LB0)
           (AHM.HMF AI L RNGh st LB0) (AHM.hmF RNGh) (AHM.hmS L RNGh) (AHM.HMS_mono L RNGh)
           P5A_defs.P5A P5A_defs.P5A_IT _ _ _ P5A_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ P5A_cert.p5a_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA [])
           ltac:(intros S0 [<-|[]]; exact (NLM.lmsa_ok AI IMG_CI fflag rng_fs HSM5 HSF5 L RNGh st LB0 H5 HFS HIMG))
           ltac:(cbn; tauto)).
Qed.

(* [comment removed for export] *)
Lemma ndae_summ : forall LB0, SP.summ_okHSC SG GP0 (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR (AHM.hmF RNGh) (AHM.hmS L RNGh)
  (SP.SUMY (SP.p_G NDCAE_defs.NDCAE) NDCAE_defs.T0 (SP.p_ex NDCAE_defs.NDCAE) (SP.p_W NDCAE_defs.NDCAE) (SP.p_A NDCAE_defs.NDCAE)
     (SP.p_PS NDCAE_defs.NDCAE) false (SP.p_CR NDCAE_defs.NDCAE)).
Proof.
  intros LB0.
  exact (SP.summ_of_pcheckHSC SG GP0 _ _ (NLM.GP0_frame _) NLM.GP0_vc (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR (AHM.HMC_sub AI LB0)
           (AHM.HMF AI L RNGh st LB0) (AHM.hmF RNGh) (AHM.hmS L RNGh) (AHM.HMS_mono L RNGh)
           NDCAE_defs.NDCAE NDCAE_defs.NDCAE_IT _ _ _ NDCAE_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ NDCAE_cert.ndcae_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA []) ltac:(intros S0 []) ltac:(cbn; tauto)).
Qed.

Lemma ndab_summ : forall LB0, (forall F1 n1 F2 n2, In (mkABlock (ABFake 5) F1 n1) LB0 -> In (mkABlock (ABFake 5) F2 n2) LB0 -> F1 = F2) ->
  SP.summ_okHSC SG GP0 (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR (AHM.hmF RNGh) (AHM.hmS L RNGh)
  (SP.SUMY (SP.p_G NDCAB_defs.NDCAB) NDCAB_defs.T0 (SP.p_ex NDCAB_defs.NDCAB) (SP.p_W NDCAB_defs.NDCAB) (SP.p_A NDCAB_defs.NDCAB)
     (SP.p_PS NDCAB_defs.NDCAB) false (SP.p_CR NDCAB_defs.NDCAB)).
Proof.
  intros LB0 H5.
  exact (SP.summ_of_pcheckHSC SG GP0 _ _ (NLM.GP0_frame _) NLM.GP0_vc (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR (AHM.HMC_sub AI LB0)
           (AHM.HMF AI L RNGh st LB0) (AHM.hmF RNGh) (AHM.hmS L RNGh) (AHM.HMS_mono L RNGh)
           NDCAB_defs.NDCAB NDCAB_defs.NDCAB_IT _ _ _ NDCAB_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ NDCAB_cert.ndcab_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA [])
           ltac:(intros S0 [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
                 first [ exact (p5sa_summ LB0 H5)
                       | apply (NLM.summ_okH_HSC AI L RNGh st LB0); first [ apply ABR.msah_ok; lia | apply ABRV.mvah_ok; lia ] ])
           ltac:(cbn; tauto)).
Qed.

(* [comment removed for export] *)
Lemma nd_step_e : forall E M rom ms,
  AHM.hmR rom -> SX.aw_genuine E (SP.p_A NDCAS_defs.NDCAS) -> SP.wins_client (hmC LB) E (SP.p_W NDCAS_defs.NDCAS) ->
  hmH LB M -> ST.tm_okF SG NDCAS_defs.T0 E M rom ms ->
  exists ms1 E1 M1 R1 F1 fc1, ExecF.mstepsF SG (SP.fpu (AHM.hmF RNGh) (SP.p_A NDCAS_defs.NDCAS) E) ms ms1
    /\ ms1 = MS R1 F1 (Z_to_bv 64 0x50668) fc1 None M1 rom /\ frm0 fc1 /\ rfull R1
    /\ regs_ok E1 (ST.t_regs NDCAE_defs.XSM) R1 /\ know_ok SG E1 M1 (ST.t_know NDCAE_defs.XSM)
    /\ SP.gagree 21 E E1 /\ eb E1 = eb E /\ hmH LB M1
    /\ (forall x : word, SP.outside_wins E (SP.p_W NDCAS_defs.NDCAS) (bv_unsigned x) -> M1 x = M x).
Proof.
  intros E M rom ms HR HA HW HH HT.
  destruct (ndae_summ LB E M rom ms HR HA HW I ltac:(intros w []) HH HT ltac:(constructor))
    as (ms1 & X1 & E1 & M1 & Hms1 & HX1 & HT1 & _ & Hg1 & Hb1 & HH1 & FR1).
  cbn [SP.sm_post NDCAE_defs.NDCAE SP.PGCA SP.p_ex In] in HX1. destruct HX1 as [<-|[]].
  destruct HT1 as (HZ1 & HF1 & (R1 & Hms1' & HR1 & _ & HK1)).
  cbn [ST.tstate s_pc s_regs s_log s_know mem_denot] in Hms1', HR1, HK1.
  exists ms1, E1, M1, R1, (ms_fregs ms1), (ms_fcsr ms1).
  split; [exact Hms1|]. split; [rewrite Hms1' at 1; destruct ms1; reflexivity|].
  split; [exact HZ1|]. split; [rewrite Hms1' in HF1; exact HF1|]. split; [exact HR1|]. split; [exact HK1|].
  split; [exact Hg1|]. split; [exact Hb1|]. split; [exact HH1|]. exact FR1.
Qed.

(* [comment removed for export] *)
Definition SPAxn : expr := EAlu ALU_SUB (EVar 1) (EAlu ALU_ADD (ELit 160) (EVar 22)).
Definition sg1n : list expr := map EVar (seq 0 21) ++ [EVar 37; EVar 38; SPAxn; EVar 21] ++ map EVar (seq 39 14).
Definition PR1n : list SC.wn := [SP.stack_win SPAxn; SP.stack_shwin (EAlu ALU_SUB (EVar 1) (ELit 4624))] ++ SP.p_CR NDCAS_defs.NDCAS ++ NLM.TABS.
Definition postregs1n : list expr :=
  [ELit 0; ELit 0xc50bc; SPAxn; EVar 2; EVar 3; EVar 39; EVar 40; EVar 41; EVar 1; SPAxn;
   EMd M_MUL (ELit 1024) (EVar 37); EVar 42; EVar 43; EVar 44; EVar 45; EVar 46; EVar 47; EVar 48;
   EVar 6; EVar 19; EVar 8; EVar 18; EMd M_MUL (ELit 8) (EVar 16); EVar 11; EVar 20; EVar 13; EVar 14; ELit 2147450880;
   EVar 49; EVar 50; EVar 51; EVar 52].
Definition knP1n : list kentry := Eval vm_compute in
  let surv := List.filter (AGL.survR (ST.t_know NDCAE_defs.XSM) PR1n PR1n) (ST.t_know NDCAE_defs.XSM) in
  List.filter (fun K => negb (ST.kimplied SG surv K)) (map (ST.ksub sg1n) (ST.t_know NDCAB_defs.T0)).
Lemma nd_b1_regs : ST.regs_match (List.filter (AGL.survR (ST.t_know NDCAE_defs.XSM) PR1n PR1n) (ST.t_know NDCAE_defs.XSM) ++ knP1n)
  postregs1n (map (ST.esub sg1n) (ST.t_regs NDCAB_defs.T0)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma nd_b1_kn : AGL.bridge_ok SG (ST.t_know NDCAE_defs.XSM) PR1n PR1n knP1n sg1n (ST.t_know NDCAB_defs.T0) = true.
Proof. vm_compute. reflexivity. Qed.


Lemma nd_glue4 : forall E rom ms1 E1 M1 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) F1 fc1,
  AHM.hmR rom -> SX.aw_genuine E (SP.p_A NDCAS_defs.NDCAS) -> SP.wins_client (hmC LB) E (SP.p_W NDCAS_defs.NDCAS) ->
  AHM.hmS L RNGh (bv_unsigned (ev E1 1)) 4624 -> SP.crs_law (hmA LB) E (SP.p_CR NDCAS_defs.NDCAS) ->
  ms1 = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F1 (Z_to_bv 64 0x50668) fc1 None M1 rom -> frm0 fc1 ->
  regs_ok E1 (ST.t_regs NDCAE_defs.XSM) (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) -> know_ok SG E1 M1 (ST.t_know NDCAE_defs.XSM) ->
  SP.gagree 21 E E1 -> eb E1 = eb E -> hmH LB M1 ->
  exists ms2 E2 M2 F,
    ExecF.mstepsF SG RNGh ms1 ms2 /\ ST.tm_okF SG NDCAB_defs.T0 E2 M2 rom ms2
    /\ SP.gagree 21 E E2 /\ eb E = eb E2
    /\ AHEAP AI L RNGh st (FB4 F :: LB) M2 /\ mem_inv SG M2
    /\ F mod 1024 = 0 /\ ablk F (F + 1024) /\ F + 1024 <= ATOP /\ rng RNGh F 1024 /\ rng RNGh (shad F) 128
    /\ (forall a, aclient_addr CI LB (bv_unsigned x2) a -> a < shad F \/ shad F + 128 <= a)
    /\ AGLR.rt_pres AI LB (bv_unsigned x2) M1 M2
    /\ ev E2 21 = Z_to_bv 64 (F / 1024) /\ ev E2 22 = Z_to_bv 64 (fflag L 4 F)
    /\ bv_unsigned (ev E2 23) = bv_unsigned x2
    /\ bv_unsigned x2 = bv_unsigned (ev E1 1) - 160 - bv_unsigned (ev E1 22) /\ bv_unsigned (ev E1 22) <= 31
    /\ SX.aw_genuine E2 (SP.p_A NDCAB_defs.NDCAB) /\ SP.wins_client (hmC (FB4 F :: LB)) E2 (SP.p_W NDCAB_defs.NDCAB).
Proof.
  intros E rom ms1 E1 M1 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F1 fc1 HR HA HW HS0 HCR Hms1e HZ1 HR1 HK1 Hg1 Hb1 HH1. subst ms1.
  pose proof (NLM.regs_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HR1) as ER1.
  cbn [rkeys map NDCAE_defs.XSM ST.t_regs NDCAE_defs.XSM_regs] in ER1. vm_compute sr_get in ER1.
  injection ER1 as E_ra E_sp E_gp E_tp E_t0 E_t1 E_t2 E_s0 E_s1 E_a0 E_a1 E_a2 E_a3 E_a4 E_a5 E_a6 E_a7 E_s2 E_s3 E_s4 E_s5 E_s6 E_s7
                   E_s8 E_s9 E_s10 E_s11 E_t3 E_t4 E_t5 E_t6.
  (* [comment removed for export] *)
  assert (KPQ : kentry_ok SG E1 M1 (KRange (EVar 22) 0 31)) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  assert (KTP : kentry_ok SG E1 M1 (KRange (EVar 3) 0x642e70 0x642e70)) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  assert (KSP : kentry_ok SG E1 M1 (KRange (EVar 1) 140728898425360 0x800000000000)) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  assert (KWS : kentry_ok SG E1 M1 (KWr (SA (EVar 1) (-4624)) (ELit 4624))) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  assert (KUS : kentry_ok SG E1 M1 (KUnk (SA (EVar 1) (-4624)) (ELit 4624))) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  cbn [kentry_ok edenot] in KPQ, KTP, KSP.
  destruct HS0 as (HS1 & HS2 & HS3).
  set (SP := bv_unsigned (ev E1 1)) in *. set (PQ := bv_unsigned (ev E1 22)) in *.
  assert (ESPA : bv_unsigned x2 = SP - 160 - PQ).
  { rewrite E_sp. cbn [edenot]. apply NLM.u_sub_lit_add; unfold SP, PQ in *; lia. }
  set (lo := SP - 4624).
  assert (STK1 : stk SG M1 lo (bv_unsigned x2)).
  { pose proof (SLB.kn_stk SG E1 M1 _ _ _ KWS KUS) as H. cbn [edenot] in H. rewrite u_lit64a in H.
    rewrite (Z.mod_small 4624 (2^64)) in H by lia. fold SP in H.
    destruct (stk_split SG M1 (SP + -4624) (bv_unsigned x2) (SP + -4624 + 4624) H ltac:(lia)) as [H1 _].
    replace lo with (SP + -4624) by (unfold lo; lia). exact H1. }
  assert (ETP : x4 = Z_to_bv 64 ATP).
  { rewrite E_tp. cbn [edenot]. apply bv_eq. rewrite u_lit64a. unfold ATP. rewrite (Z.mod_small 0x642e70 (2^64)) by lia. lia. }
  pose proof (HSM4 L RNGh x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
                F1 fc1 M1 st LB lo (proj1 HH1) HC4 (proj2 HH1) STK1 ltac:(unfold lo; lia) ltac:(unfold lo, SM4_STACK; lia)
                ltac:(lia) ETP ltac:(replace lo with (SP - 4624) by reflexivity; exact HS3) HIMG HFS) as HSM.
  unfold ASTKMALLOC4 in HSM. rewrite <- HR in HSM.
  destruct HSM as (ms2 & Hms2 & (F & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & M2 & j0 & j1 & j2 & junk &
                   -> & MI2 & STK2 & PRES & AH2 & HFm & HFb & HFt & HFc & HFs & RF1 & RF2 & BSH & B5)).
  set (E1' := SLB.env_ext E1 37 [Z_to_bv 64 (F / 1024); Z_to_bv 64 (fflag L 4 F); t0; t1; t2; a1; a2; a3; a4; a5; a6; a7; t3; t4; t5; t6]).
  (* [comment removed for export] *)
  pose proof atop_range as AT.
  assert (HF0 : 0x665000 <= F /\ F + 1024 <= 0x7FFFFF800000).
  { destruct HFb as [[B1 B2]|[B1 B2]]; unfold AIMG_HI, KLS in *; lia. }
  assert (VLT : forall k, (k < 37)%nat -> ev E1' k = ev E1 k) by (intros k Hk; apply SLB.env_ext_lt; exact Hk).
  assert (V37 : ev E1' 37 = Z_to_bv 64 (F / 1024)) by reflexivity.
  assert (V38 : ev E1' 38 = Z_to_bv 64 (fflag L 4 F)) by reflexivity.
  assert (UF : bv_unsigned (mul_div M_MUL (Z_to_bv 64 1024) (ev E1' 37)) = F).
  { rewrite V37, u_mul64, !u_lit64a. rewrite (Z.mod_small 1024 (2^64)) by lia.
    rewrite (Z.mod_small (F / 1024) (2^64)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite Z.mod_small; [|split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|]].
    - clear - HFm. Z.div_mod_to_equations. lia.
    - assert (1024 * (F / 1024) <= F) by (apply Z.mul_div_le; lia). lia. }
  assert (USF : bv_unsigned (mul_div M_MUL (Z_to_bv 64 128) (ev E1' 37)) = F / 8).
  { rewrite V37, u_mul64, !u_lit64a. rewrite (Z.mod_small 128 (2^64)) by lia.
    rewrite (Z.mod_small (F / 1024) (2^64)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (E8 : F / 8 = 128 * (F / 1024)) by (clear - HFm; Z.div_mod_to_equations; lia).
    rewrite <- E8. apply Z.mod_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (U37 : bv_unsigned (ev E1' 37) = F / 1024).
  { rewrite V37. apply u_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  (* [comment removed for export] *)
  assert (KX8 : kentry_ok SG E1 M1 (KRange (EVar 16) 0xcca04 0xfffffeffff7)) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  assert (KXH : kentry_ok SG E1 M1 (KRange (EAlu ALU_SUB (EVar 16) (EMd M_MUL (ELit 8) (EVar 17))) 4 4))
    by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  cbn [kentry_ok edenot] in KX8, KXH. set (X8 := bv_unsigned (ev E1 16)) in *. set (XH := bv_unsigned (ev E1 17)) in *.
  assert (KXHr : kentry_ok SG E1 M1 (KRange (EVar 17) 0x19940 0x1fffffdfffe)) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  cbn [kentry_ok edenot] in KXHr. fold XH in KXHr.
  assert (EXH : X8 = 8 * XH + 4).
  { rewrite u_sub64, u_mul64, u_lit64a in KXH. fold XH in KXH. fold X8 in KXH.
    rewrite (Z.mod_small 8 (2^64)) in KXH by lia. rewrite (Z.mod_small (8 * XH) (2^64)) in KXH by lia.
    rewrite Z.mod_small in KXH by lia. lia. }
  (* [comment removed for export] *)
  assert (CRX : forall z, 8 * X8 <= z < 8 * X8 + 498 -> AHM.hmA AI LB z).
  { intros z Hz. apply (HCR (EMd M_MUL (ELit 8) (EVar 16), 0, ELit 498) ltac:(vm_compute; left; reflexivity) z).
    cbn [SP.win_den edenot fst snd]. rewrite u_mul64, !u_lit64a. rewrite (Hg1 16%nat ltac:(lia)). fold X8.
    rewrite (Z.mod_small 8 (2^64)) by lia. rewrite (Z.mod_small 498 (2^64)) by lia.
    rewrite (Z.mod_small (8 * X8) (2^64)) by lia. lia. }
  assert (KXB : kentry_ok SG E1 M1 (KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA (EMd M_MUL (ELit 8) (EVar 16)) 0) (ELit 504)))
    by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  cbn [kentry_ok] in KXB. unfold estart, elenZ in KXB. cbn [a_base a_off edenot] in KXB. rewrite u_mul64, !u_lit64a in KXB. fold X8 in KXB.
  rewrite (Z.mod_small 8 (2^64)), (Z.mod_small 0 (2^64)), (Z.mod_small 504 (2^64)), (Z.mod_small 0x100000001000 (2^64)),
    (Z.mod_small (8 * X8) (2^64)) in KXB by lia.
  assert (XF : 8 * X8 + 498 <= F \/ F + 1024 <= 8 * X8 \/ 498 <= 0).
  { apply (AGLR.fresh_apart AI L RNGh st LB M2 4 F 1024 (8 * X8) 498 AH2 CRX); unfold AIMG_HI; lia. }
  assert (XF' : 8 * X8 + 504 <= F \/ F + 1024 <= 8 * X8).
  { clear - XF HFm EXH. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (USP1 : bv_unsigned (ev E1' 1) = SP) by (rewrite (VLT 1%nat) by lia; reflexivity).
  assert (U22 : bv_unsigned (ev E1' 22) = PQ) by (rewrite (VLT 22%nat) by lia; reflexivity).
  assert (U16 : bv_unsigned (ev E1' 16) = X8) by (rewrite (VLT 16%nat) by lia; reflexivity).
  assert (U17 : bv_unsigned (ev E1' 17) = XH) by (rewrite (VLT 17%nat) by lia; reflexivity).
  assert (USPA : bv_unsigned (alu64 ALU_SUB (ev E1' 1) (alu64 ALU_ADD (Z_to_bv 64 160) (ev E1' 22))) = SP - 160 - PQ).
  { rewrite u_sub64, u_add64, u_lit64a, USP1, U22. rewrite (Z.mod_small 160 (2^64)) by lia.
    rewrite (Z.mod_small (160 + PQ) (2^64)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (UX : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (ev E1' 16)) = 8 * X8).
  { rewrite u_mul64, u_lit64a, U16. rewrite (Z.mod_small 8 (2^64)) by lia. apply Z.mod_small. lia. }
  assert (UXH : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (ev E1' 17)) = 8 * XH).
  { rewrite u_mul64, u_lit64a, U17. rewrite (Z.mod_small 8 (2^64)) by lia. apply Z.mod_small. lia. }
  assert (UF2 : bv_unsigned (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 1024) (ev E1' 37)) (Z_to_bv 64 1024)) = F + 1024).
  { rewrite u_add64, UF, u_lit64a. rewrite (Z.mod_small 1024 (2^64)) by lia. apply Z.mod_small. lia. }
  assert (ESH : shad F = F / 8 + 2147450880).
  { unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. }
  assert (F8 : F / 8 < 2^44 /\ 0 <= F / 8) by (split; [apply Z.div_lt_upper_bound | apply Z.div_pos]; lia).
  (* [comment removed for export] *)
  assert (STKS1 : stk SG M1 (bv_unsigned x2) SP).
  { pose proof (SLB.kn_stk SG E1 M1 _ _ _ KWS KUS) as H. cbn [edenot] in H. rewrite u_lit64a in H.
    rewrite (Z.mod_small 4624 (2^64)) in H by lia. fold SP in H.
    destruct (stk_split SG M1 (SP + -4624) (bv_unsigned x2) (SP + -4624 + 4624) H ltac:(lia)) as [_ H2].
    replace (SP + -4624 + 4624) with SP in H2 by lia. exact H2. }
  assert (KEEP : forall a, bv_unsigned x2 <= a < SP -> M2 (wa a) = M1 (wa a) /\ (wview SG M1 (wa a) <> None -> wview SG M2 (wa a) <> None)).
  { intros a Ha. apply (PRES a ltac:(lia)). left. lia. }
  pose proof (AGX.stk_join SG M1 M2 lo (bv_unsigned x2) SP STK2 STKS1 KEEP) as STKM2.
  assert (RO2 : forall x, lo <= x < SP -> seg_rom SG (Z_to_bv 64 x) = None).
  { intros x Hx. apply ref_seg_rom_none. rewrite u_small by lia. lia. }
  assert (KP1 : know_ok SG E1' M2 knP1n).
  { unfold knP1n. repeat apply Forall_cons.
    (* [comment removed for export] *)
    - apply AGX.kx_range. cbn [edenot]. rewrite U37. split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia.
    (* [comment removed for export] *)
    - apply (AGX.kx_cells_wr SG E1' M2 _ _ [C8 j0; C8 j1; C8 j2; CB 992 junk; C8 (Z_to_bv 64 (fflag L 4 F))]).
      + unfold estart. cbn [a_base a_off edenot]. rewrite UF, Z.add_0_r. exact HFc.
      + unfold elenZ. cbn [edenot cells_size csize]. rewrite u_lit64a. reflexivity.
      + unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite UF, u_lit64a. rewrite (Z.mod_small 1024 (2^64)) by lia. lia.
    (* [comment removed for export] *)
    - apply AGLR.unk_of_wr.
      + unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite UF, u_lit64a. rewrite (Z.mod_small 1024 (2^64)) by lia. lia.
      + unfold estart. cbn [a_base a_off edenot]. rewrite UF. lia.
      + unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UF, u_lit64a, Z.add_0_r. rewrite (Z.mod_small 1024 (2^64)) by lia.
        exact (proj2 HFc).
    (* [comment removed for export] *)
    - apply (AGX.kx_word_cells SG E1' M2 _ _ _ F [C8 j0; C8 j1; C8 j2; CB 992 junk; C8 (Z_to_bv 64 (fflag L 4 F))] 1016
               (C8 (Z_to_bv 64 (fflag L 4 F))) HFc); [reflexivity | | | reflexivity | | lia].
      + unfold estart. cbn [a_base a_off edenot]. rewrite UF. lia.
      + unfold flat, estart. cbn [a_base a_off edenot]. rewrite UF. lia.
      + cbn [cbytes edenot]. rewrite V38. reflexivity.
    (* [comment removed for export] *)
    - apply (AGX.kx_cells_wr SG E1' M2 _ _ (repeat (C8 (Z_to_bv 64 0)) 16)).
      + unfold estart. cbn [a_base a_off edenot]. rewrite USF. rewrite <- ESH. exact HFs.
      + unfold elenZ. cbn [edenot]. rewrite u_lit64a. reflexivity.
      + unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, u_lit64a. rewrite (Z.mod_small 128 (2^64)) by lia. lia.
    (* [comment removed for export] *)
    - apply AGLR.unk_of_wr.
      + unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, u_lit64a. rewrite (Z.mod_small 128 (2^64)) by lia. lia.
      + unfold estart. cbn [a_base a_off edenot]. rewrite USF. lia.
      + unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, u_lit64a. rewrite (Z.mod_small 128 (2^64)) by lia.
        rewrite <- ESH. exact (proj2 HFs).
    (* [comment removed for export] *)
    - apply AGX.kx_range. cbn [edenot]. rewrite UF2. lia.
    (* [comment removed for export] *)
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UF, !u_lit64a.
      rewrite (Z.mod_small 0 (2^64)), (Z.mod_small 0x100000001000 (2^64)), (Z.mod_small 1024 (2^64)) by lia.
      destruct HFb as [[B1 B2]|[B1 B2]]; unfold AIMG_HI, KLS in *; lia.
    (* [comment removed for export] *)
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UF, USP1, !u_lit64a.
      rewrite (Z.mod_small 4624 (2^64)), (Z.mod_small 1024 (2^64)) by lia. lia.
    (* [comment removed for export] *)
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UF, UX, !u_lit64a.
      rewrite (Z.mod_small 504 (2^64)), (Z.mod_small 1024 (2^64)) by lia. lia.
    (* [comment removed for export] *)
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, U16, !u_lit64a.
      rewrite (Z.mod_small 128 (2^64)), (Z.mod_small 63 (2^64)) by lia. clear - XF' EXH HFm. Z.div_mod_to_equations. lia.
    (* [comment removed for export] *)
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, UXH, !u_lit64a.
      rewrite (Z.mod_small 128 (2^64)), (Z.mod_small 72 (2^64)) by lia. clear - XF' EXH HFm. Z.div_mod_to_equations. lia.
    (* [comment removed for export] *)
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, USP1, !u_lit64a.
      rewrite (Z.mod_small 4624 (2^64)), (Z.mod_small 128 (2^64)) by lia. lia.
    (* [comment removed for export] *)
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UF, USF, !u_lit64a.
      rewrite (Z.mod_small 1024 (2^64)), (Z.mod_small 128 (2^64)) by lia.
      destruct HFb as [[B1 B2]|[B1 B2]]; unfold AIMG_HI, KLS in *; [left | right]; clear - B1 B2 HF0; Z.div_mod_to_equations; lia.
    (* [comment removed for export] *)
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, UX, !u_lit64a.
      rewrite (Z.mod_small 128 (2^64)), (Z.mod_small 504 (2^64)) by lia. lia.
    (* [comment removed for export] *)
    - apply AGX.kx_zero.
      + unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, u_lit64a. rewrite (Z.mod_small 128 (2^64)) by lia. lia.
      + unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, u_lit64a. rewrite (Z.mod_small 128 (2^64)) by lia.
        intros i Hi. rewrite <- ESH. exact (AGLR.zero_cellsN M2 (shad F) 16 HFs ltac:(lia) ltac:(cbn; lia) i ltac:(cbn; lia)).
    (* [comment removed for export] *)
    - apply (AGX.kx_stk_wr SG E1' M2 _ _ lo SP STKM2); unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?USPA, ?u_lit64a;
        rewrite ?(Z.mod_small 4592 (2^64)) by lia; unfold lo; lia.
    - apply (AGX.kx_stk_unk SG E1' M2 _ _ lo SP STKM2 RO2); unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?USPA, ?u_lit64a;
        rewrite ?(Z.mod_small 4592 (2^64)) by lia; unfold lo; lia.
    (* [comment removed for export] *)
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UF, USPA, !u_lit64a.
      rewrite (Z.mod_small 4592 (2^64)), (Z.mod_small 1024 (2^64)) by lia. lia.
    (* [comment removed for export] *)
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, USPA, !u_lit64a.
      rewrite (Z.mod_small 4592 (2^64)), (Z.mod_small 128 (2^64)) by lia. lia.
    (* [comment removed for export] *)
    - apply (AGX.kx_stk_wr SG E1' M2 _ _ lo SP STKM2); unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?USP1, ?u_lit64a;
        rewrite ?(Z.mod_small 4624 (2^64)) by lia; unfold lo; lia.
    - apply (AGX.kx_stk_unk SG E1' M2 _ _ lo SP STKM2 RO2); unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?USP1, ?u_lit64a;
        rewrite ?(Z.mod_small 4624 (2^64)) by lia; unfold lo; lia.
    (* [comment removed for export] *)
    - apply AGX.kx_img; [lia | lia | exact MI2 |]. intros a Ha. rewrite a_ro_addr. apply andb_true_intro.
      split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
    (* [comment removed for export] *)
    - destruct (AI_rtcells AI _ _ _ _ _ AH2) as (_ & GOT & _).
      apply (AGX.kx_word_cells SG E1' M2 _ _ _ 0x1072f0 _ 16 (C8 (Z_to_bv 64 0x10faf8)) GOT); [reflexivity | | | reflexivity | reflexivity | lia];
        unfold flat, estart; cbn [a_base a_off edenot]; rewrite u_lit64a; rewrite (Z.mod_small 0 (2^64)) by lia; lia.
    - destruct (AI_rtcells AI _ _ _ _ _ AH2) as (_ & _ & _ & _ & SHB & _).
      apply (AGX.kx_word_cells SG E1' M2 _ _ _ 0x10faf8 _ 0 (C8 (Z_to_bv 64 0x7fff8000)) SHB); [reflexivity | | | reflexivity | reflexivity | lia];
        unfold flat, estart; cbn [a_base a_off edenot]; rewrite u_lit64a; rewrite (Z.mod_small 0 (2^64)) by lia; lia.
    - pose proof (client_got_of_aheap AI _ _ _ _ _ AH2 MI2) as SUARG.
      apply (AGX.kx_word_cells SG E1' M2 _ _ _ AGOT_SUAR _ 0 (C8 (Z_to_bv 64 ASUAR)) SUARG); [reflexivity | | | reflexivity | reflexivity | lia];
        unfold flat, estart, AGOT_SUAR; cbn [a_base a_off edenot]; rewrite u_lit64a; rewrite (Z.mod_small 0 (2^64)) by lia; lia.
    - destruct (AI_rtcells AI _ _ _ _ _ AH2) as (_ & _ & _ & _ & _ & SUAR & _).
      apply (AGX.kx_word_cells SG E1' M2 _ _ _ 0x10fb00 _ 0 (C4 (Z_to_bv 64 1)) SUAR); [reflexivity | | | reflexivity | vm_compute; reflexivity | lia];
        unfold flat, estart; cbn [a_base a_off edenot]; rewrite u_lit64a; rewrite (Z.mod_small 0 (2^64)) by lia; lia.
    - constructor. }
  assert (ER2 : regs_ok E1' postregs1n (mkR x1 x2 x3 x4 t0 t1 t2 x8 x9 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7
                                         x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)).
  { apply AGC.regs_ok_tl; [reflexivity|]. unfold postregs1n. cbn [tl map edenot].
    change (ev E1' 39) with t0. change (ev E1' 40) with t1. change (ev E1' 41) with t2.
    change (ev E1' 42) with a1. change (ev E1' 43) with a2. change (ev E1' 44) with a3. change (ev E1' 45) with a4.
    change (ev E1' 46) with a5. change (ev E1' 47) with a6. change (ev E1' 48) with a7.
    change (ev E1' 49) with t3. change (ev E1' 50) with t4. change (ev E1' 51) with t5. change (ev E1' 52) with t6.
    rewrite E_ra, E_sp, E_gp, E_tp, E_s0, E_s1, E_s2, E_s3, E_s4, E_s5, E_s6, E_s7, E_s8, E_s9, E_s10, E_s11.
    cbn [edenot]. rewrite ?(VLT 1%nat), ?(VLT 2%nat), ?(VLT 3%nat), ?(VLT 6%nat), ?(VLT 7%nat), ?(VLT 8%nat), ?(VLT 10%nat),
      ?(VLT 11%nat), ?(VLT 12%nat), ?(VLT 13%nat), ?(VLT 14%nat), ?(VLT 15%nat), ?(VLT 16%nat), ?(VLT 18%nat), ?(VLT 19%nat), ?(VLT 20%nat), ?(VLT 22%nat) by lia.
    assert (EA0 : mul_div M_MUL (Z_to_bv 64 1024) (ev E1' 37) = Z_to_bv 64 F).
    { apply bv_eq. rewrite UF. rewrite u_small by lia. reflexivity. }
    rewrite EA0. reflexivity. }
  (* [comment removed for export] *)
  assert (TABIN : forall lo' hi', In (lo', hi') IMG_TABS -> In (lo', hi') CI).
  { intros lo' hi' H. apply IMG_CI. unfold client_ranges. apply in_or_app. right. exact H. }
  assert (RK1 : AGL.rt_keep SG E1' PR1n PR1n M1 M2).
  { apply (AGLR.rt_keep_cls AI LB (bv_unsigned x2) lo M1 M2 E1' PR1n (conj PRES BSH)
             (AGLR.shw_of_aheap AI L RNGh st LB _ M2 AH2 (fun b H => or_intror H)) ltac:(unfold lo; lia) ltac:(lia)).
    unfold PR1n. cbn [app SP.p_CR NDCAS_defs.NDCAS SP.PGH]. unfold NLM.TABS.
    cbv [NDCAS_defs.vX NDCAS_defs.vX8 NDCAS_defs.vXH NDCAS_defs.mul NDCAS_defs.V].
    repeat apply Forall_cons.
    - intros x Hin Hx. left. pose proof (AGLR.in_stack_win E1' SPAxn x) as H. unfold SPAxn in H. cbn [edenot] in H.
      rewrite USPA in H. specialize (H ltac:(lia) Hin). lia.
    - intros x Hin Hx. right; left. pose proof (SP.shwin_sh_above E1' (EAlu ALU_SUB (EVar 1) (ELit 4624)) x) as H.
      cbn [edenot] in H. rewrite u_sub64, USP1, u_lit64a in H. rewrite (Z.mod_small 4624 (2^64)) in H by lia.
      rewrite (Z.mod_small (SP - 4624) (2^64)) in H by lia.
      destruct (H ltac:(lia) Hin) as (a & Ha & ->). exists a. split; [unfold lo; lia|]. unfold SP.sh_of, shad, ASHOFF. reflexivity.
    - intros x Hin Hx. right; right; left. apply (HCR (EMd M_MUL (ELit 8) (EVar 16), 0, ELit 498) ltac:(vm_compute; left; reflexivity)).
      unfold SC.in_win, SG.win_den in Hin. cbn [edenot] in Hin. rewrite UX, u_lit64a in Hin.
      rewrite (Z.mod_small 498 (2^64)) in Hin by lia.
      assert (WE : SP.win_den E (EMd M_MUL (ELit 8) (EVar 16), 0, ELit 498) = (8 * X8 + 0, 8 * X8 + 0 + 498)).
      { cbn [SP.win_den edenot]. rewrite u_mul64, !u_lit64a, (Hg1 16%nat ltac:(lia)). fold X8.
        rewrite (Z.mod_small 8 (2^64)), (Z.mod_small 498 (2^64)) by lia. rewrite (Z.mod_small (8 * X8) (2^64)) by lia. reflexivity. }
      rewrite WE. cbn [fst snd]. lia.
    - intros x Hin Hx. right; right; left. apply (HCR (EVar 16, 2147450880, ELit 63) ltac:(vm_compute; right; left; reflexivity)).
      unfold SC.in_win, SG.win_den in Hin. cbn [edenot] in Hin. rewrite U16, u_lit64a in Hin.
      rewrite (Z.mod_small 63 (2^64)) in Hin by lia.
      assert (WE : SP.win_den E (EVar 16, 2147450880, ELit 63) = (X8 + 2147450880, X8 + 2147450880 + 63)).
      { cbn [SP.win_den edenot]. rewrite !u_lit64a, (Hg1 16%nat ltac:(lia)). fold X8.
        rewrite (Z.mod_small 63 (2^64)) by lia. reflexivity. }
      rewrite WE. cbn [fst snd]. lia.
    - intros x Hin Hx. right; right; left.
      apply (HCR (EMd M_MUL (ELit 8) (EVar 17), 2147450880, ELit 72) ltac:(vm_compute; right; right; left; reflexivity)).
      unfold SC.in_win, SG.win_den in Hin. cbn [edenot] in Hin. rewrite UXH, u_lit64a in Hin.
      rewrite (Z.mod_small 72 (2^64)) in Hin by lia.
      assert (WE : SP.win_den E (EMd M_MUL (ELit 8) (EVar 17), 2147450880, ELit 72) = (8 * XH + 2147450880, 8 * XH + 2147450880 + 72)).
      { cbn [SP.win_den edenot]. rewrite u_mul64, !u_lit64a, (Hg1 17%nat ltac:(lia)). fold XH.
        rewrite (Z.mod_small 8 (2^64)), (Z.mod_small 72 (2^64)) by lia. rewrite (Z.mod_small (8 * XH) (2^64)) by lia. reflexivity. }
      rewrite WE. cbn [fst snd]. lia.
    - intros x Hin Hx. right; right; right; right. unfold SC.in_win, SG.win_den in Hin. cbn [edenot] in Hin.
      rewrite !u_lit64a in Hin. rewrite (Z.mod_small 0 (2^64)), (Z.mod_small 1324 (2^64)) in Hin by lia.
      exists (8 * (x - 2147450880)). split.
      + exists (0x283c0, 0x2ad20). split; [apply TABIN; vm_compute; tauto | cbn [fst snd]; lia].
      + unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mul_comm, Z.div_mul by lia. lia.
    - intros x Hin Hx. right; right; right; right. unfold SC.in_win, SG.win_den in Hin. cbn [edenot] in Hin.
      rewrite !u_lit64a in Hin. rewrite (Z.mod_small 0 (2^64)), (Z.mod_small 80 (2^64)) in Hin by lia.
      exists (8 * (x - 2147450880)). split.
      + exists (0x2ad40, 0x2afc0). split; [apply TABIN; vm_compute; tauto | cbn [fst snd]; lia].
      + unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mul_comm, Z.div_mul by lia. lia.
    - constructor. }
  (* [comment removed for export] *)
  assert (HKX1 : know_ok SG E1' M1 (ST.t_know NDCAE_defs.XSM)).
  { apply (AxSymRun3.know_ok_agree SG 37 E1 E1' M1 _); [| vm_compute; reflexivity | exact HK1].
    split; [intros k Hk; symmetry; apply VLT; exact Hk | reflexivity]. }
  assert (HRP : ret_pc x1 = Z_to_bv 64 (ST.t_pc NDCAB_defs.T0)) by (apply bv_eq; rewrite E_ra; vm_compute; reflexivity).
  lazymatch type of Hms2 with ExecF.mstepsF _ _ _ ?m => set (ms2 := m) in * end.
  pose proof (AGL.bridge_tm SG E1' M1 M2 _ PR1n PR1n knP1n postregs1n sg1n NDCAB_defs.T0 _ F1 fc1 rom ms2 HKX1 RK1 KP1 ER2 nd_b1_regs nd_b1_kn
                ltac:(unfold ms2; rewrite HRP, HR; reflexivity) HZ1 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) as HT2.
  (* [comment removed for export] *)
  set (E2 := ST.senv E1' sg1n) in *.
  assert (VE2 : forall k, (k < 21)%nat -> ev E2 k = ev E1 k).
  { intros k Hk. unfold E2. rewrite SP.senv_nth. unfold sg1n. rewrite app_nth1 by (rewrite length_map, length_seq; lia).
    rewrite (nth_indep _ (ELit 0) (EVar 0)) by (rewrite length_map, length_seq; lia). rewrite map_nth, seq_nth by lia.
    cbn [edenot]. apply VLT. lia. }
  assert (VE18 : ev E2 21 = Z_to_bv 64 (F / 1024)) by (unfold E2; rewrite SP.senv_nth; reflexivity).
  assert (VE21 : bv_unsigned (ev E2 23) = SP - 160 - PQ) by (unfold E2; rewrite SP.senv_nth; exact USPA).
  pose proof HT2 as (_ & _ & (R2' & _ & _ & _ & HK2)). cbn [ST.tstate s_know mem_denot] in HK2.
  assert (GE2 : SP.gagree 21 E E2) by (intros k Hk; rewrite VE2 by exact Hk; apply Hg1; exact Hk).
  assert (BE2 : eb E = eb E2) by (unfold E2, E1', ST.senv, SLB.env_ext; cbn; symmetry; exact Hb1).
  assert (HA2 : SX.aw_genuine E2 (SP.p_A NDCAB_defs.NDCAB)).
  { cbn [SP.p_A NDCAB_defs.NDCAB SP.PGCA]. apply (AGC.aw_gen_mix SG E E2 M2 _ _ _ 21 HK2 HA GE2 BE2). vm_compute. reflexivity. }
  assert (UF2' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 1024) (ev E2 21)) = F) by (rewrite VE18, <- V37; exact UF).
  assert (USF2 : bv_unsigned (mul_div M_MUL (Z_to_bv 64 128) (ev E2 21)) = F / 8) by (rewrite VE18, <- V37; exact USF).
  assert (HW2 : SP.wins_client (hmC (FB4 F :: LB)) E2 (SP.p_W NDCAB_defs.NDCAB)).
  { cbn [SP.p_W NDCAB_defs.NDCAB SP.PGCA]. unfold SP.wins_client in HW |- *. cbn [SP.p_W NDCAS_defs.NDCAS SP.PGH] in HW.
    pose proof (Forall_inv HW) as HW1. pose proof (Forall_inv (Forall_inv_tail HW)) as HW2'.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HW))) as HW3. cbv beta in HW1, HW2', HW3.
    repeat apply Forall_cons.
    - match goal with |- context [SP.win_den E2 ?w] => rewrite <- (SP.win_den_gagree 21 E E2 w GE2 BE2 eq_refl) end. unfold AHM.hmC in *.
      apply (AGLR.acr_mono AI LB); [exact HW1 | intros b Hb; right; exact Hb].
    - match goal with |- context [SP.win_den E2 ?w] => rewrite <- (SP.win_den_gagree 21 E E2 w GE2 BE2 eq_refl) end. unfold AHM.hmC in *.
      apply (AGLR.acr_mono AI LB); [exact HW2' | intros b Hb; right; exact Hb].
    - match goal with |- context [SP.win_den E2 ?w] => rewrite <- (SP.win_den_gagree 21 E E2 w GE2 BE2 eq_refl) end. unfold AHM.hmC in *.
      apply (AGLR.acr_mono AI LB); [exact HW3 | intros b Hb; right; exact Hb].
    - unfold AHM.hmC. cbv [NDCAB_defs.vF NDCAB_defs.mul NDCAB_defs.vF10 NDCAB_defs.V]. cbn [SP.win_den edenot fst snd]. rewrite UF2', u_lit64a.
      rewrite (Z.mod_small 1024 (2^64)) by lia. apply (AGLR.acr_fake AI _ _ 4 F 1024); [left; reflexivity | lia | lia].
    - unfold AHM.hmC. cbv [NDCAB_defs.mul NDCAB_defs.vF10 NDCAB_defs.V]. cbn [SP.win_den edenot fst snd]. rewrite USF2, u_lit64a.
      rewrite (Z.mod_small 128 (2^64)) by lia. apply (AGLR.acr_fake_shadow AI _ _ 4 F 1024); [left; reflexivity | |];
        unfold ASHOFF; clear - HFm; Z.div_mod_to_equations; lia.
    - unfold AHM.hmC. cbv [NDCAB_defs.vSPA NDCAB_defs.V]. cbn [SP.win_den edenot fst snd]. rewrite VE21, u_lit64a.
      rewrite (Z.mod_small 4592 (2^64)) by lia. apply (AGLR.acr_stack AI); lia.
    - constructor. }
  assert (V19 : ev E2 22 = Z_to_bv 64 (fflag L 4 F)) by (unfold E2; rewrite SP.senv_nth; exact V38).
  exists ms2, E2, M2, F.
  split; [exact Hms2|]. split; [exact HT2|]. split; [exact GE2|]. split; [exact BE2|]. split; [exact AH2|]. split; [exact MI2|].
  split; [exact HFm|]. split; [exact HFb|]. split; [exact HFt|]. split; [exact RF1|]. split; [exact RF2|]. split; [exact B5|].
  split; [exact (conj PRES BSH)|]. split; [exact VE18|]. split; [exact V19|]. split; [rewrite VE21; symmetry; exact ESPA|].
  split; [exact ESPA|]. split; [fold PQ; lia|]. split; [exact HA2 | exact HW2].
Qed.

(* [comment removed for export] *)
Definition sxs : sentry := {| e_addr := SA (EMd M_MUL (ELit 128) (EVar 21)) 2147450880; e_width := 128%nat; e_val := ELit 0 |}.
Definition sg2n : list expr := map EVar (seq 0 23) ++ [EVar 24; EVar 25; EVar 26; ELit 0xc58dc; EVar 23; EVar 46; EVar 47; EVar 48; EVar 23;
  EAlu ALU_ADD (EMd M_MUL (ELit 128) (EVar 21)) (ELit 2147450880)] ++ map EVar (seq 49 7) ++
  [EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; ELit 2147450880] ++ map EVar (seq 56 4).
Definition postregs2n : list expr :=
  [ELit 0; ELit 0xc58dc; EVar 23; EVar 2; EVar 3; EVar 46; EVar 47; EVar 48; EVar 1; EVar 23;
   EAlu ALU_ADD (EMd M_MUL (ELit 128) (EVar 21)) (ELit 2147450880); EVar 49; EVar 50; EVar 51; EVar 52; EVar 53; EVar 54; EVar 55;
   EMd M_MUL (ELit 1024) (EVar 21); EVar 26; EVar 36; EVar 25; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41; ELit 2147450880;
   EVar 56; EVar 57; EVar 58; EVar 59].
Definition knP2n : list kentry := Eval vm_compute in
  let surv := List.filter (AGM.survM (ST.t_know NDCAB_defs.XSS) sxs) (ST.t_know NDCAB_defs.XSS) in
  List.filter (fun K => negb (ST.kimplied SG surv K)) (map (ST.ksub sg2n) (ST.t_know NDCAF_defs.T0)).
Lemma nd_b2_regs : ST.regs_match (List.filter (AGM.survM (ST.t_know NDCAB_defs.XSS) sxs) (ST.t_know NDCAB_defs.XSS) ++ knP2n)
  postregs2n (map (ST.esub sg2n) (ST.t_regs NDCAF_defs.T0)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma nd_b2_kn : AGM.bridge_okM SG (ST.t_know NDCAB_defs.XSS) sxs knP2n sg2n (ST.t_know NDCAF_defs.T0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma nd_setsh : forall E rom ms3 E1 E3 M3 F,
  AHM.hmR rom -> SP.crs_law (hmA LB) E (SP.p_CR NDCAS_defs.NDCAS) -> SP.gagree 21 E E1 ->
  AHM.hmS L RNGh (bv_unsigned (ev E1 1)) 4624 ->
  ST.tm_okF SG NDCAB_defs.XSS E3 M3 rom ms3 -> hmH (FB4 F :: LB) M3 ->
  (forall k, (k < 21)%nat -> ev E3 k = ev E1 k) -> ev E3 21 = Z_to_bv 64 (F / 1024) -> ev E3 22 = Z_to_bv 64 (fflag L 4 F) ->
  bv_unsigned (ev E3 23) = bv_unsigned (ev E1 1) - 160 - bv_unsigned (ev E1 22) -> bv_unsigned (ev E1 22) <= 31 ->
  F mod 1024 = 0 -> ablk F (F + 1024) -> rng RNGh (shad F) 128 ->
  exists ms4 E4 M4, ExecF.mstepsF SG RNGh ms3 ms4 /\ ST.tm_okF SG NDCAF_defs.T0 E4 M4 rom ms4
    /\ (forall k, (k < 23)%nat -> ev E4 k = ev E3 k) /\ eb E4 = eb E3
    /\ AHEAP AI L RNGh st (FB4 F :: LB) M4 /\ mem_inv SG M4 /\ munch [(shad F, shad F + 128)] M3 M4 /\ wmono SG M3 M4.
Proof.
  intros E rom ms3 E1 E3 M3 F HR HCR Hg1 HS0 HT3 HH3 VE31 V3_21 V3_22 V3_23 HPQ HFm HFb HRS.
  destruct HS0 as (HS1 & HS2 & HS3).
  pose proof (bv_unsigned_in_range 64 (ev E1 22)) as RPQ. change (bv_modulus 64) with (2^64) in RPQ.
  set (SP := bv_unsigned (ev E1 1)) in *. set (PQ := bv_unsigned (ev E1 22)) in *.
  pose proof atop_range as AT.
  assert (HF0 : 0x665000 <= F /\ F + 1024 <= 0x7FFFFF800000).
  { destruct HFb as [[B1 B2]|[B1 B2]]; unfold AIMG_HI, KLS in *; lia. }
  destruct HT3 as (HZ3 & HF3 & (R3 & Hms3' & HR3 & _ & HK3)).
  cbn [ST.tstate s_pc s_regs s_log s_know mem_denot] in Hms3', HR3, HK3.
  assert (Hms3e : ms3 = MS R3 (ms_fregs ms3) (Z_to_bv 64 0x69720) (ms_fcsr ms3) None M3 rom)
    by (rewrite Hms3' at 1; destruct ms3; reflexivity).
  assert (HF3' : PIosRegs.rfull R3) by (rewrite Hms3e in HF3; exact HF3). clear HF3.
  destruct HF3' as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20 & y21
                   & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & ->).
  pose proof (NLM.regs_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HR3) as ER3.
  cbn [rkeys map NDCAB_defs.XSS ST.t_regs NDCAB_defs.XSS_regs] in ER3. vm_compute sr_get in ER3.
  injection ER3 as Y_ra Y_sp Y_gp Y_tp Y_t0 Y_t1 Y_t2 Y_s0 Y_s1 Y_a0 Y_a1 Y_a2 Y_a3 Y_a4 Y_a5 Y_a6 Y_a7 Y_s2 Y_s3 Y_s4 Y_s5 Y_s6 Y_s7
                   Y_s8 Y_s9 Y_s10 Y_s11 Y_t3 Y_t4 Y_t5 Y_t6.
  assert (U3_1 : bv_unsigned (ev E3 1) = SP) by (rewrite (VE31 1%nat) by lia; reflexivity).
  assert (KSP : kentry_ok SG E3 M3 (KRange (EVar 1) 140728898425360 0x800000000000)) by (apply (ST.kin_ok SG E3 M3 _ _ HK3); vm_compute; reflexivity).
  cbn [kentry_ok edenot] in KSP. rewrite U3_1 in KSP.
  assert (U3_21 : bv_unsigned (ev E3 21) = F / 1024).
  { rewrite V3_21. apply u_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (USH3 : bv_unsigned (mul_div M_MUL (Z_to_bv 64 128) (ev E3 21)) = F / 8).
  { rewrite u_mul64, u_lit64a, U3_21. rewrite (Z.mod_small 128 (2^64)) by lia.
    assert (E8 : F / 8 = 128 * (F / 1024)) by (clear - HFm; Z.div_mod_to_equations; lia).
    rewrite <- E8. apply Z.mod_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (ESH : shad F = F / 8 + 2147450880).
  { unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. }
  assert (F8 : F / 8 < 2^44 /\ 0 <= F / 8) by (split; [apply Z.div_lt_upper_bound | apply Z.div_pos]; lia).
  assert (EA0 : bv_unsigned y10 = shad F).
  { rewrite Y_a0. transitivity (bv_unsigned (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 128) (ev E3 21)) (Z_to_bv 64 2147450880)));
      [reflexivity|]. rewrite u_add64, USH3, u_lit64a. rewrite (Z.mod_small 2147450880 (2^64)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (EA1 : bv_unsigned y11 = 128) by (rewrite Y_a1; cbn [edenot]; rewrite u_lit64a; reflexivity).
  (* [comment removed for export] *)
  assert (KWSH : kentry_ok SG E3 M3 (KWr (SA (EMd M_MUL (ELit 128) (EVar 21)) 2147450880) (ELit 128)))
    by (apply (ST.kin_ok SG E3 M3 _ _ HK3); vm_compute; reflexivity).
  assert (KUSH : kentry_ok SG E3 M3 (KUnk (SA (EMd M_MUL (ELit 128) (EVar 21)) 2147450880) (ELit 128)))
    by (apply (ST.kin_ok SG E3 M3 _ _ HK3); vm_compute; reflexivity).
  destruct (SLB.kn_rw_CB SG E3 M3 _ _ _ KWSH KUSH) as (junk & RWJ).
  cbn [edenot] in RWJ. rewrite USH3, u_lit64a in RWJ. rewrite <- ESH in RWJ. change (Z.to_nat (128 mod 2^64)) with 128%nat in RWJ.
  destruct HH3 as [AH3 MI3].
  (* [comment removed for export] *)
  assert (SC3 : setsh_cells M3).
  { split.
    - pose proof (AI_relro AI L RNGh st _ M3 AH3) as R. unfold ARELRO_LO, ARELRO_HI in R.
      eapply rw_cells_recast; [apply (rw_cells_image0 SG _ 0x107320 (le8 (Z_to_bv 64 0x109248)));
        [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
        | vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity].
    - destruct (AI_rtcells AI _ _ _ _ _ AH3) as (_ & _ & _ & RM & _). exact RM. }
  pose proof (set_shadow_f5_spec RNGh y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
                y28 y29 y30 y31 (ms_fregs ms3) (ms_fcsr ms3) M3 junk MI3 SC3 ltac:(rewrite EA0, EA1; exact RWJ)
                ltac:(rewrite EA0, EA1; exact HRS) HIMG) as HSS.
  unfold ASETSH_F5 in HSS. rewrite <- HR in HSS. rewrite <- Hms3e in HSS.
  destruct HSS as (ms4 & Hms4 & (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & M4 & -> & MU & WM & MI4 & RW4)).
  rewrite EA0, EA1 in MU, RW4.
  (* [comment removed for export] *)
  assert (AH4 : AHEAP AI L RNGh st (FB4 F :: LB) M4).
  { apply (AI_frame AI L RNGh st (FB4 F :: LB) M3 M4 [(shad F, shad F + 128)] AH3 MU WM).
    constructor; [|constructor]. cbn [fst snd]. replace (shad F + 128 - shad F) with 128 by lia.
    apply (AGLR.acr_fake_shadow AI _ _ 4 F 1024); [left; reflexivity | |]; rewrite ESH; unfold ASHOFF; clear - HFm; Z.div_mod_to_equations; lia. }
  (* [comment removed for export] *)
  set (E3' := SLB.env_ext E3 46 [u0; u1; u2; b1; b2; b3; b4; b5; b6; b7; u3; u4; u5; u6]).
  assert (VLT3 : forall k, (k < 46)%nat -> ev E3' k = ev E3 k) by (intros k Hk; apply SLB.env_ext_lt; exact Hk).
  assert (ER4 : regs_ok E3' postregs2n (mkR y1 y2 y3 y4 u0 u1 u2 y8 y9 y10 b1 b2 b3 b4 b5 b6 b7
                                          y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 u3 u4 u5 u6)).
  { apply AGC.regs_ok_tl; [reflexivity|]. unfold postregs2n. cbn [tl map edenot].
    change (ev E3' 46) with u0. change (ev E3' 47) with u1. change (ev E3' 48) with u2.
    change (ev E3' 49) with b1. change (ev E3' 50) with b2. change (ev E3' 51) with b3. change (ev E3' 52) with b4.
    change (ev E3' 53) with b5. change (ev E3' 54) with b6. change (ev E3' 55) with b7.
    change (ev E3' 56) with u3. change (ev E3' 57) with u4. change (ev E3' 58) with u5. change (ev E3' 59) with u6.
    rewrite Y_ra, Y_sp, Y_gp, Y_tp, Y_s0, Y_s1, Y_a0, Y_s2, Y_s3, Y_s4, Y_s5, Y_s6, Y_s7, Y_s8, Y_s9, Y_s10, Y_s11.
    cbn [edenot]. rewrite ?(VLT3 1%nat), ?(VLT3 2%nat), ?(VLT3 3%nat), ?(VLT3 21%nat), ?(VLT3 23%nat), ?(VLT3 25%nat), ?(VLT3 26%nat),
      ?(VLT3 36%nat), ?(VLT3 37%nat), ?(VLT3 38%nat), ?(VLT3 39%nat), ?(VLT3 40%nat), ?(VLT3 41%nat) by lia. reflexivity. }
  assert (MK : AGM.munch_keep SG (estart E3' (e_addr sxs)) (estart E3' (e_addr sxs) + elenZ E3' (elen (e_width sxs))) M3 M4).
  { assert (ES : estart E3' (e_addr sxs) = shad F).
    { unfold estart. cbn [sxs e_addr a_base a_off edenot]. rewrite (VLT3 21%nat) by lia. rewrite USH3. lia. }
    assert (EL : elenZ E3' (elen (e_width sxs)) = 128) by (unfold elenZ; cbn [sxs e_width elen edenot]; rewrite u_lit64a; reflexivity).
    rewrite ES, EL. split; [|exact WM]. intros x Hx. apply MU. cbn [outside]. split; [|exact I]. lia. }
  assert (HKX3 : know_ok SG E3' M3 (ST.t_know NDCAB_defs.XSS)).
  { apply (AxSymRun3.know_ok_agree SG 46 E3 E3' M3 _); [| vm_compute; reflexivity | exact HK3].
    split; [intros k Hk; symmetry; apply VLT3; exact Hk | reflexivity]. }
  assert (KP2 : know_ok SG E3' M4 knP2n).
  { destruct (HFF L RNGh st (FB4 F :: LB) M4 4 F 1024 AH4 (or_introl eq_refl)) as (RWC & RNGF & ABLKF & TOPF & OUTB & NCI).
    set (fl := fflag L 4 F) in *.
    assert (FLR : 0x665000 <= fl /\ fl + 1 <= 0x7FFFFF800000) by (destruct ABLKF as [[B1 B2]|[B1 B2]]; unfold AIMG_HI, KLS in *; lia).
    assert (UFL : bv_unsigned (ev E3' 22) = fl) by (rewrite (VLT3 22%nat) by lia; rewrite V3_22; apply u_small; lia).
    assert (U16' : bv_unsigned (ev E3' 16) = bv_unsigned (ev E1 16)) by (rewrite (VLT3 16%nat), (VE31 16%nat) by lia; reflexivity).
    assert (KX8 : kentry_ok SG E3 M3 (KRange (EVar 16) 0xcca04 0xfffffeffff7)) by (apply (ST.kin_ok SG E3 M3 _ _ HK3); vm_compute; reflexivity).
    cbn [kentry_ok edenot] in KX8. rewrite (VE31 16%nat) in KX8 by lia. set (X8 := bv_unsigned (ev E1 16)) in *.
    assert (UX' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (ev E3' 16)) = 8 * X8).
    { rewrite u_mul64, u_lit64a, U16'. rewrite (Z.mod_small 8 (2^64)) by lia. apply Z.mod_small. lia. }
    unfold knP2n. repeat apply Forall_cons.
    - apply AGX.kx_range. cbn [edenot]. rewrite UFL. lia.
    - apply AGX.kx_wr.
      + unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite UFL, u_lit64a. rewrite (Z.mod_small 1 (2^64)) by lia. lia.
      + unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UFL, u_lit64a, Z.add_0_r. rewrite (Z.mod_small 1 (2^64)) by lia.
        exact (proj2 RWC).
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UFL, (VLT3 1%nat), U3_1, !u_lit64a by lia.
      rewrite (Z.mod_small 4624 (2^64)), (Z.mod_small 1 (2^64)) by lia. lia.
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UFL, !u_lit64a.
      rewrite (Z.mod_small 0 (2^64)), (Z.mod_small 0x100000001000 (2^64)), (Z.mod_small 1 (2^64)) by lia.
      destruct ABLKF as [[B1 B2]|[B1 B2]]; unfold AIMG_HI, KLS in *; lia.
    - (* [comment removed for export] *)
      apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UFL, UX', !u_lit64a.
      rewrite (Z.mod_small 1 (2^64)), (Z.mod_small 498 (2^64)) by lia.
      destruct (Z_lt_ge_dec fl (8 * X8)) as [Hlt|Hge]; [left; lia|].
      destruct (Z_lt_ge_dec fl (8 * X8 + 498)) as [Hlt2|Hge2]; [|right; lia]. exfalso.
      assert (HX : AHM.hmA AI LB fl).
      { apply (HCR (EMd M_MUL (ELit 8) (EVar 16), 0, ELit 498) ltac:(vm_compute; left; reflexivity)).
        cbn [SP.win_den edenot fst snd]. rewrite u_mul64, !u_lit64a, (Hg1 16%nat ltac:(lia)). fold X8.
        rewrite (Z.mod_small 8 (2^64)), (Z.mod_small 498 (2^64)) by lia. rewrite (Z.mod_small (8 * X8) (2^64)) by lia. lia. }
      apply (AGLF.flag_out AI L RNGh st (FB4 F :: LB) M4 fl ATOP fl AH4 ABLKF TOPF OUTB NCI);
        [lia | right; right; exact (AGLF.hmA_cons AI (FB4 F) LB fl HX) | reflexivity].
    - constructor. }
  assert (HRP2 : ret_pc y1 = Z_to_bv 64 (ST.t_pc NDCAF_defs.T0)) by (apply bv_eq; rewrite Y_ra; vm_compute; reflexivity).
  lazymatch type of Hms4 with ExecF.mstepsF _ _ _ ?m => set (ms4 := m) in * end.
  pose proof (AGM.bridge_tmM SG E3' M3 M4 _ sxs knP2n postregs2n sg2n NDCAF_defs.T0 _ (ms_fregs ms3) (ms_fcsr ms3) rom ms4 HKX3 MK KP2 ER4
                nd_b2_regs nd_b2_kn ltac:(unfold ms4; rewrite HRP2, HR; reflexivity) HZ3
                (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) as HT4.
  exists ms4, (ST.senv E3' sg2n), M4.
  split; [exact Hms4|]. split; [exact HT4|].
  split.
  { intros k Hk. rewrite SP.senv_nth. unfold sg2n. rewrite app_nth1 by (rewrite length_map, length_seq; lia).
    rewrite (nth_indep _ (ELit 0) (EVar 0)) by (rewrite length_map, length_seq; lia). rewrite map_nth, seq_nth by lia.
    cbn [edenot]. apply VLT3. lia. }
  split; [reflexivity|]. split; [exact AH4|]. split; [exact MI4|]. split; [exact MU | exact WM].
Qed.

(* [comment removed for export] *)
Lemma HMF_F : forall (M0 : word -> option byte) E (W : list SP.win) M M', SP.wins_client (fun _ _ => True) E W ->
  (mem_inv SG M /\ wmono SG M0 M) -> PIosRegs.wrel SG M M' -> (forall x : word, SP.outside_wins E W (bv_unsigned x) -> M' x = M x) ->
  mem_inv SG M' /\ wmono SG M0 M'.
Proof.
  intros M0 E W M M' _ [MI WM] HW _. split; [exact (wrel_mem_inv SG _ _ HW MI)|].
  exact (wmono_trans SG _ _ _ WM (wrel_wmono SG _ _ HW)).
Qed.

Lemma ndaf_summ : forall M0, SP.summ_okHSC SG GP0 (fun M => mem_inv SG M /\ wmono SG M0 M) (fun _ => False) (fun _ _ => True) AHM.hmR
  (AHM.hmF RNGh) (AHM.hmS L RNGh)
  (SP.SUMY (SP.p_G NDCAF_defs.NDCAF) NDCAF_defs.T0 (SP.p_ex NDCAF_defs.NDCAF) (SP.p_W NDCAF_defs.NDCAF) (SP.p_A NDCAF_defs.NDCAF)
     (SP.p_PS NDCAF_defs.NDCAF) false (SP.p_CR NDCAF_defs.NDCAF)).
Proof.
  intros M0.
  exact (SP.summ_of_pcheckHSC SG GP0 _ _ (NLM.GP0_frame _) NLM.GP0_vc (fun M => mem_inv SG M /\ wmono SG M0 M) (fun _ => False)
           (fun _ _ => True) AHM.hmR (fun _ _ _ _ _ _ _ => I) (HMF_F M0) (AHM.hmF RNGh) (AHM.hmS L RNGh) (AHM.HMS_mono L RNGh)
           NDCAF_defs.NDCAF NDCAF_defs.NDCAF_IT _ _ _ NDCAF_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ NDCAF_cert.ndcaf_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA []) ltac:(intros S0 []) ltac:(cbn; tauto)).
Qed.

(* [comment removed for export] *)
Definition sgX : list expr := map EVar (seq 0 21) ++ map EVar (seq 23 16).
Lemma ndx_regs : ST.regs_match (ST.t_know NDCAF_defs.XRF) (ST.t_regs NDCAF_defs.XRF) (map (ST.esub sgX) (ST.t_regs NDCAS_defs.XR)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ndx_kn : forallb (ST.kimplied SG (ST.t_know NDCAF_defs.XRF)) (map (ST.ksub sgX) (ST.t_know NDCAS_defs.XR)) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem ndsa_ok : SP.summ_okHSC SG GP0 (hmH LB) (hmA LB) (hmC LB) AHM.hmR (AHM.hmF RNGh) (AHM.hmS L RNGh) NDCA_sum.NDSA.
Proof.
  intros E M rom ms HR HA HW HS HCR HH HT HG.
  cbn [SP.sm_pre SP.sm_post SP.sm_W SP.sm_A SP.sm_PS SP.sm_CR SP.sm_G NDCA_sum.NDSA] in *.
  (* [comment removed for export] *)
  destruct (nd_step_e E M rom ms HR HA HW HH HT) as (ms1 & E1 & M1 & R1 & F1 & fc1 & Hms1 & Hms1e & HZ1 & HF1 & HR1 & HK1 & Hg1 & Hb1 & HH1 & FR1).
  destruct HF1 as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ->).
  unfold SP.hs_ok in HS. change (SP.dstk (Some NDCAS_defs.vSP) (SP.p_W NDCAS_defs.NDCAS)) with (Some (NDCAS_defs.vSP, 4624)) in HS.
  cbv beta iota in HS. change (edenot E NDCAS_defs.vSP) with (ev E 1) in HS. rewrite (Hg1 1%nat ltac:(lia)) in HS.
  (* [comment removed for export] *)
  destruct (nd_glue4 E rom ms1 E1 M1 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F1 fc1 HR HA HW HS HCR Hms1e HZ1 HR1 HK1 Hg1 Hb1 HH1)
    as (ms2 & E2 & M2 & F & Hms2 & HT2 & GE2 & BE2 & AH2 & MI2 & HFm & HFb & HFt & RF1 & RF2 & B5 & RP12 & VE21 & V22 & VE23x & ESPA & HPQ & HA2 & HW2).
  (* [comment removed for export] *)
  assert (HS2 : SP.hs_ok (AHM.hmS L RNGh) E2 (SP.p_PS NDCAB_defs.NDCAB) (SP.p_W NDCAB_defs.NDCAB)).
  { unfold SP.hs_ok. change (SP.dstk (SP.p_PS NDCAB_defs.NDCAB) (SP.p_W NDCAB_defs.NDCAB)) with (Some (NDCAB_defs.vSP, 4624)).
    cbv beta iota. change (edenot E2 NDCAB_defs.vSP) with (ev E2 1). rewrite <- (GE2 1%nat) by lia. rewrite (Hg1 1%nat) by lia. exact HS. }
  pose proof atop_range as AT.
  assert (HF0 : 0x665000 <= F /\ F + 1024 <= 0x7FFFFF800000) by (destruct HFb as [[B1 B2]|[B1 B2]]; unfold AIMG_HI, KLS in *; lia).
  assert (UF2' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 1024) (ev E2 21)) = F).
  { rewrite VE21, u_mul64, !u_lit64a. rewrite (Z.mod_small 1024 (2^64)) by lia.
    rewrite (Z.mod_small (F / 1024) (2^64)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite Z.mod_small; [|split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|]].
    - clear - HFm. Z.div_mod_to_equations. lia.
    - assert (1024 * (F / 1024) <= F) by (apply Z.mul_div_le; lia). lia. }
  assert (USF2 : bv_unsigned (mul_div M_MUL (Z_to_bv 64 128) (ev E2 21)) = F / 8).
  { rewrite VE21, u_mul64, !u_lit64a. rewrite (Z.mod_small 128 (2^64)) by lia.
    rewrite (Z.mod_small (F / 1024) (2^64)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (E8 : F / 8 = 128 * (F / 1024)) by (clear - HFm; Z.div_mod_to_equations; lia).
    rewrite <- E8. apply Z.mod_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (ESH : shad F = F / 8 + 2147450880).
  { unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. }
  assert (HCR2 : SP.crs_law (hmA (FB4 F :: LB)) E2 (SP.p_CR NDCAB_defs.NDCAB)).
  { intros w Hw z Hz. cbn [SP.p_CR NDCAB_defs.NDCAB SP.PGH In] in Hw.
    destruct Hw as [<-|[<-|[<-|[<-|[<-|[]]]]]].
    - apply AGLF.hmA_cons. rewrite <- (SP.win_den_gagree 21 E E2 (NDCAB_defs.vX, 0, ELit 498) GE2 BE2 eq_refl) in Hz.
      exact (HCR (NDCAS_defs.vX, 0, ELit 498) ltac:(vm_compute; left; reflexivity) z Hz).
    - apply AGLF.hmA_cons. rewrite <- (SP.win_den_gagree 21 E E2 (NDCAB_defs.vX8, 2147450880, ELit 63) GE2 BE2 eq_refl) in Hz.
      exact (HCR (NDCAS_defs.vX8, 2147450880, ELit 63) ltac:(vm_compute; right; left; reflexivity) z Hz).
    - apply AGLF.hmA_cons. rewrite <- (SP.win_den_gagree 21 E E2 (NDCAB_defs.mul 8 NDCAB_defs.vXH, 2147450880, ELit 72) GE2 BE2 eq_refl) in Hz.
      exact (HCR (NDCAS_defs.mul 8 NDCAS_defs.vXH, 2147450880, ELit 72) ltac:(vm_compute; right; right; left; reflexivity) z Hz).
    - (* [comment removed for export] *)
      cbn [SP.win_den edenot fst snd] in Hz. cbv [NDCAB_defs.vF NDCAB_defs.mul NDCAB_defs.vF10 NDCAB_defs.V] in Hz.
      cbn [edenot] in Hz. rewrite UF2', u_lit64a in Hz. rewrite (Z.mod_small 1024 (2^64)) in Hz by lia.
      apply (AHM.hmA_of_block AI (FB4 F :: LB) (FB4 F) z (or_introl eq_refl)). cbn [ab_addr ab_size]. lia.
    - (* [comment removed for export] *)
      cbn [SP.win_den edenot fst snd] in Hz. cbv [NDCAB_defs.mul NDCAB_defs.vF10 NDCAB_defs.V] in Hz.
      cbn [edenot] in Hz. rewrite USF2, u_lit64a in Hz. rewrite (Z.mod_small 128 (2^64)) in Hz by lia.
      replace z with (shad (8 * (z - ASHOFF))) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8;
        rewrite Z.mul_comm, Z.div_mul by lia; lia).
      apply AHM.hmA_of_fake_shadow. exists 4, F, 1024. split; [left; reflexivity|]. unfold ASHOFF.
      clear - Hz HFm. Z.div_mod_to_equations. lia. }
  destruct (ndab_summ (FB4 F :: LB) (c5_cons4 F LB HC5) E2 M2 rom ms2 HR HA2 HW2 HS2 HCR2 (conj AH2 MI2) HT2 ltac:(constructor))
    as (ms3 & X3 & E3 & M3 & Hms3 & HX3 & HT3 & _ & Hg3 & Hb3 & HH3 & FR3).
  cbn [SP.sm_post SP.p_ex NDCAB_defs.NDCAB SP.PGH In] in HX3. destruct HX3 as [<-|[]].
  cbn [SP.sm_A SP.sm_G SP.sm_W SP.sm_PS] in Hms3, Hg3, FR3. change (SP.p_G NDCAB_defs.NDCAB) with 24%nat in Hg3.
  assert (VE31 : forall k, (k < 21)%nat -> ev E3 k = ev E1 k).
  { intros k Hk. rewrite <- (Hg3 k) by lia. rewrite <- (GE2 k) by lia. apply Hg1. exact Hk. }
  assert (V3_21 : ev E3 21 = Z_to_bv 64 (F / 1024)) by (rewrite <- (Hg3 21%nat) by lia; exact VE21).
  assert (V3_22 : ev E3 22 = Z_to_bv 64 (fflag L 4 F)) by (rewrite <- (Hg3 22%nat) by lia; exact V22).
  assert (V3_23 : bv_unsigned (ev E3 23) = bv_unsigned (ev E1 1) - 160 - bv_unsigned (ev E1 22))
    by (rewrite <- (Hg3 23%nat) by lia; rewrite VE23x; exact ESPA).
  (* [comment removed for export] *)
  destruct (nd_setsh E rom ms3 E1 E3 M3 F HR HCR Hg1 HS HT3 HH3 VE31 V3_21 V3_22 V3_23 HPQ HFm HFb RF2)
    as (ms4 & E4 & M4 & Hms4 & HT4 & VE4 & Hb4 & AH4 & MI4 & MU4 & WM4).
  (* [comment removed for export] *)
  assert (GE4 : SP.gagree 21 E E4) by (intros k Hk; rewrite VE4 by lia; rewrite VE31 by exact Hk; apply Hg1; exact Hk).
  assert (BE4 : eb E = eb E4) by (rewrite Hb4, Hb3; exact BE2).
  pose proof HT4 as (_ & _ & (R4' & _ & _ & _ & HK4)). cbn [ST.tstate s_know mem_denot] in HK4.
  assert (HA4 : SX.aw_genuine E4 (SP.p_A NDCAF_defs.NDCAF)).
  { cbn [SP.p_A NDCAF_defs.NDCAF SP.PGCA]. apply (AGC.aw_gen_mix SG E E4 M4 _ _ _ 21 HK4 HA GE4 BE4). vm_compute. reflexivity. }
  assert (HW4 : SP.wins_client (fun _ _ => True) E4 (SP.p_W NDCAF_defs.NDCAF)).
  { unfold SP.wins_client. apply Forall_forall. intros w _. exact I. }
  destruct (ndaf_summ M4 E4 M4 rom ms4 HR HA4 HW4 I ltac:(intros w []) (conj MI4 (wmono_refl SG M4)) HT4 ltac:(constructor))
    as (ms5 & X5 & E5 & M5 & Hms5 & HX5 & HT5 & _ & Hg5 & Hb5 & (MI5 & WM5) & FR5).
  cbn [SP.sm_post SP.p_ex NDCAF_defs.NDCAF SP.PGCA In] in HX5. destruct HX5 as [<-|[]].
  cbn [SP.sm_A SP.sm_G SP.sm_W SP.sm_PS] in Hms5, Hg5, FR5. change (SP.p_G NDCAF_defs.NDCAF) with 23%nat in Hg5.
  cbn [SP.frame_ok SP.p_PS NDCAF_defs.NDCAF SP.PGCA] in FR5.
  (* [comment removed for export] *)
  pose proof HS as (HSa & HSb & HSc).
  pose proof (bv_unsigned_in_range 64 (ev E1 22)) as RPQ. change (bv_modulus 64) with (2^64) in RPQ.
  set (SP := bv_unsigned (ev E1 1)) in *. set (PQ := bv_unsigned (ev E1 22)) in *.
  destruct (HFF L RNGh st (FB4 F :: LB) M4 4 F 1024 AH4 (or_introl eq_refl)) as (RWC & RNGF & ABLKF & TOPF & OUTB & NCI).
  set (fl := fflag L 4 F) in *.
  assert (FLR : 0x665000 <= fl /\ fl + 1 <= 0x7FFFFF800000) by (destruct ABLKF as [[B1 B2]|[B1 B2]]; unfold AIMG_HI, KLS in *; lia).
  (* [comment removed for export] *)
  pose proof HT5 as (_ & _ & (R5' & _ & _ & _ & HK5)). cbn [ST.tstate s_know mem_denot] in HK5.
  assert (KFZ : kentry_ok SG E5 M5 (KZero (SA (EVar 22) 0) (ELit 1))) by (apply (ST.kin_ok SG E5 M5 _ _ HK5); vm_compute; reflexivity).
  assert (UFL5 : bv_unsigned (ev E5 22) = fl).
  { rewrite <- (Hg5 22%nat) by lia. rewrite VE4 by lia. rewrite V3_22. apply u_small. lia. }
  assert (MFL : M5 (wa fl) = Some (Z_to_bv 8 0)).
  { destruct KFZ as [_ KZ]. specialize (KZ 0 ltac:(unfold elenZ; cbn [edenot]; rewrite u_lit64a; cbn; lia)).
    unfold estart in KZ. cbn [a_base a_off edenot] in KZ. rewrite UFL5, !Z.add_0_r in KZ. exact KZ. }
  (* [comment removed for export] *)
  assert (AHR := HFR L RNGh st LB M4 4 F 1024 AH4). fold fl in AHR.
  assert (CLW : forallb (SP.win_closed 21) (SP.p_W NDCAS_defs.NDCAS) = true) by (vm_compute; reflexivity).
  assert (EWF : SP.p_W NDCAF_defs.NDCAF = SP.p_W NDCAS_defs.NDCAS ++ [(EVar 22, 0, ELit 1)]) by (vm_compute; reflexivity).
  assert (OUTF : forall x : word, SP.outside_wins E (SP.p_W NDCAS_defs.NDCAS) (bv_unsigned x) -> bv_unsigned x <> fl ->
                   SP.outside_wins E4 (SP.p_W NDCAF_defs.NDCAF) (bv_unsigned x)).
  { intros x Hx Hne. rewrite EWF. unfold SP.outside_wins. apply Forall_app. split.
    - exact (SP.outside_wins_gagree 21 E E4 _ _ GE4 BE4 CLW Hx).
    - constructor; [|constructor]. cbn [SP.win_den edenot]. rewrite VE4 by lia. rewrite V3_22, !u_lit64a.
      rewrite !Z.mod_small by lia. lia. }
  assert (AH5 : AHEAP AI L RNGh st LB M5).
  { apply (AI_frame AI L RNGh st LB _ M5 (map (SP.win_den E) (SP.p_W NDCAS_defs.NDCAS)) AHR).
    - intros x Hx. destruct (Z.eq_dec (bv_unsigned x) fl) as [Hfl|Hfl].
      + replace x with (wa fl) by (unfold wa; rewrite <- Hfl; apply Z_to_bv_bv_unsigned). rewrite MFL.
        cbn [write_to_mem]. unfold wa. rewrite bv_eqb_refl. reflexivity.
      + rewrite (FR5 x (OUTF x ltac:(unfold SP.outside_wins; clear - Hx; induction (SP.p_W NDCAS_defs.NDCAS) as [|w W IH]; [constructor|];
                                      cbn [map outside] in Hx; destruct (SP.win_den E w) as [lo hi] eqn:Ew; destruct Hx as [H1 H2];
                                      constructor; [rewrite Ew; lia | exact (IH H2)]) Hfl)).
        cbn [write_to_mem]. destruct (bv_eqb x (wa fl)) eqn:Q; [|reflexivity].
        unfold bv_eqb in Q. apply Z.eqb_eq in Q. exfalso. apply Hfl. rewrite Q. unfold wa. rewrite u_small by lia. reflexivity.
    - intros x Hx. destruct (Z.eq_dec (bv_unsigned x) fl) as [Hfl|Hfl].
      + unfold wview. replace x with (wa fl) by (unfold wa; rewrite <- Hfl; apply Z_to_bv_bv_unsigned). rewrite MFL. discriminate.
      + apply WM5. unfold wview in Hx |- *. cbn [write_to_mem] in Hx. destruct (bv_eqb x (wa fl)) eqn:Q.
        * unfold bv_eqb in Q. apply Z.eqb_eq in Q. exfalso. apply Hfl. rewrite Q. unfold wa. rewrite u_small by lia. reflexivity.
        * exact Hx.
    - unfold SP.wins_client in HW. apply Forall_map. eapply Forall_impl; [|exact HW]. intros w Hw. exact Hw. }
  (* [comment removed for export] *)
  pose proof (AGC.tm_rename SG NDCAF_defs.XRF NDCAS_defs.XR sgX E5 M5 rom ms5 HT5 eq_refl ndx_regs ndx_kn) as HT6.
  exists ms5, NDCAS_defs.XR, (ST.senv E5 sgX), M5.
  assert (VE23 : bv_unsigned (ev E2 23) = SP - 160 - PQ) by (rewrite VE23x; exact ESPA).
  assert (UF4 : bv_unsigned (mul_div M_MUL (Z_to_bv 64 1024) (ev E4 21)) = F).
  { rewrite VE4 by lia. rewrite V3_21, <- VE21. exact UF2'. }
  assert (UFL4 : bv_unsigned (ev E4 22) = fl).
  { rewrite VE4 by lia. rewrite V3_22. apply u_small. lia. }
  (* [comment removed for export] *)
  assert (FPB : forall b j, SP.fpu (AHM.hmF RNGh) (SP.p_A NDCAB_defs.NDCAB) E2 b j -> SP.fpu (AHM.hmF RNGh) (SP.p_A NDCAS_defs.NDCAS) E b j).
  { apply (AGLF.fpu_mix (AHM.hmF RNGh) E E2 _ _). apply (AGLF.fp_mix3 E E2 _ _ 21 _ GE2 BE2).
    intros w Hw. vm_compute in Hw. destruct Hw as [<-|[<-|[<-|[]]]]; intros b j Hw1 Hw2; cbn [SX.awin_den edenot fst snd] in Hw1, Hw2.
    - right. rewrite UF2' in Hw1, Hw2. rewrite u_lit64a in Hw2. rewrite (Z.mod_small 1024 (2^64)) in Hw2 by lia.
      destruct RF1 as (_ & _ & RF). apply RF; lia.
    - right. rewrite USF2 in Hw1, Hw2. rewrite u_lit64a in Hw2. rewrite (Z.mod_small 128 (2^64)) in Hw2 by lia.
      destruct RF2 as (_ & _ & RF). apply RF; rewrite ESH; lia.
    - left. rewrite VE23 in Hw1, Hw2. rewrite u_lit64a in Hw2. rewrite (Z.mod_small 4592 (2^64)) in Hw2 by lia.
      exists (EVar 1, -4624, ELit 4624). split; [vm_compute; left; reflexivity|]. cbn [SX.awin_den edenot fst snd].
      rewrite u_lit64a, (Z.mod_small 4624 (2^64)) by lia. rewrite (Hg1 1%nat) by lia. fold SP. lia. }
  assert (FPF : forall b j, SP.fpu (AHM.hmF RNGh) (SP.p_A NDCAF_defs.NDCAF) E4 b j -> SP.fpu (AHM.hmF RNGh) (SP.p_A NDCAS_defs.NDCAS) E b j).
  { apply (AGLF.fpu_mix (AHM.hmF RNGh) E E4 _ _). apply (AGLF.fp_mix3 E E4 _ _ 21 _ GE4 BE4).
    intros w Hw. vm_compute in Hw. destruct Hw as [<-|[<-|[]]]; intros b j Hw1 Hw2; cbn [SX.awin_den edenot fst snd] in Hw1, Hw2.
    - right. rewrite UF4 in Hw1, Hw2. rewrite u_lit64a in Hw2. rewrite (Z.mod_small 1024 (2^64)) in Hw2 by lia.
      destruct RF1 as (_ & _ & RF). apply RF; lia.
    - right. rewrite UFL4 in Hw1, Hw2. rewrite u_lit64a in Hw2. rewrite (Z.mod_small 1 (2^64)) in Hw2 by lia.
      destruct RNGF as (_ & _ & RF). apply RF; lia. }
  split.
  { eapply ExecF.mstepsF_trans; [exact Hms1|].
    eapply ExecF.mstepsF_trans; [exact (ExecF.mstepsF_weaken SG _ _ _ _ (fun b j Hb => or_intror Hb) Hms2)|].
    eapply ExecF.mstepsF_trans; [exact (ExecF.mstepsF_weaken SG _ _ _ _ FPB Hms3)|].
    eapply ExecF.mstepsF_trans; [exact (ExecF.mstepsF_weaken SG _ _ _ _ (fun b j Hb => or_intror Hb) Hms4)|].
    exact (ExecF.mstepsF_weaken SG _ _ _ _ FPF Hms5). }
  split; [left; reflexivity|].
  split; [exact HT6|].
  split; [constructor|].
  split.
  { intros k Hk0. assert (Hk : (k < 21)%nat) by exact Hk0. clear Hk0.
    rewrite SP.senv_nth. unfold sgX. rewrite app_nth1 by (rewrite length_map, length_seq; lia).
    rewrite (nth_indep _ (ELit 0) (EVar 0)) by (rewrite length_map, length_seq; lia). rewrite map_nth, seq_nth by lia.
    cbn [edenot Nat.add]. rewrite <- (Hg5 k) by lia. exact (GE4 k Hk). }
  split; [cbn [ST.senv eb]; rewrite Hb5; symmetry; exact BE4|].
  split; [exact (conj AH5 MI5)|].
  (* [comment removed for export] *)
  cbn [SP.frame_ok]. intros x Hout Hcls.
  change (edenot E NDCAS_defs.vSP) with (ev E 1) in Hcls. rewrite (Hg1 1%nat ltac:(lia)) in Hcls. fold SP in Hcls.
  assert (KC : AGLF.keep_cls AI LB SP (bv_unsigned x)) by exact Hcls.
  pose proof (bv_unsigned_in_range 64 x) as Rx; change (bv_modulus 64) with (2^64) in Rx.
  assert (CLS : forallb (SP.win_closed 21) (SP.p_W NDCAS_defs.NDCAS) = true) by (vm_compute; reflexivity).
  (* [comment removed for export] *)
  assert (Hnf : bv_unsigned x <> fl).
  { exact (AGLF.flag_out AI L RNGh st LB M fl SP (bv_unsigned x) (proj1 HH) ABLKF TOPF (fun b Hb => OUTB b (or_intror Hb)) NCI ltac:(lia) KC). }
  rewrite (FR5 x (OUTF x Hout Hnf)).
  (* [comment removed for export] *)
  destruct (AGLF.fresh_out AI L RNGh st LB M2 4 F 1024 (bv_unsigned x2) SP (bv_unsigned x) AH2 B5
              ltac:(clear - HFm; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) HFb HFt ltac:(lia) KC) as [OF OS].
  change (1024 / 8) with 128 in OS.
  rewrite (MU4 x (conj OS I)).
  (* [comment removed for export] *)
  cbn [SP.frame_ok SP.p_PS NDCAB_defs.NDCAB SP.PGH] in FR3.
  rewrite (FR3 x).
  2:{ cbn [SP.p_W NDCAB_defs.NDCAB SP.PGH]. unfold SP.outside_wins.
      pose proof (SP.outside_wins_gagree 21 E E2 _ _ GE2 BE2 CLS Hout) as HO2. unfold SP.outside_wins in HO2.
      cbn [SP.p_W NDCAS_defs.NDCAS SP.PGH] in HO2.
      pose proof (AGLF.stack_out AI L RNGh st LB M SP (SP - 160 - PQ - 4432) (SP - PQ) (bv_unsigned x) (proj1 HH) ltac:(lia) ltac:(lia) KC) as OSt.
      apply Forall_cons; [exact (Forall_inv HO2)|]. apply Forall_cons; [exact (Forall_inv (Forall_inv_tail HO2))|].
      apply Forall_cons; [exact (Forall_inv (Forall_inv_tail (Forall_inv_tail HO2)))|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|constructor]]].
      - cbv [NDCAB_defs.vF NDCAB_defs.mul NDCAB_defs.vF10 NDCAB_defs.V]. cbn [SP.win_den edenot].
        rewrite UF2', u_lit64a, (Z.mod_small 1024 (2^64)) by lia. intros [H1 H2]. apply OF. lia.
      - cbv [NDCAB_defs.mul NDCAB_defs.vF10 NDCAB_defs.V]. cbn [SP.win_den edenot].
        rewrite USF2, u_lit64a, (Z.mod_small 128 (2^64)) by lia. intros [H1 H2]. apply OS. rewrite ESH. lia.
      - cbv [NDCAB_defs.vSPA NDCAB_defs.V]. cbn [SP.win_den edenot].
        rewrite VE23, u_lit64a, (Z.mod_small 4592 (2^64)) by lia. intros [H1 H2]. apply OSt. lia. }
  2:{ change (edenot E2 NDCAB_defs.vSP) with (ev E2 1). rewrite <- (GE2 1%nat) by lia. rewrite (Hg1 1%nat) by lia. fold SP.
      exact (AGLF.keep_cls_cons AI (FB4 F) LB SP (bv_unsigned x) KC). }
  (* [comment removed for export] *)
  pose proof (AGLF.keep_rt AI LB (bv_unsigned x2) SP M1 M2 (bv_unsigned x) RP12 ltac:(lia) ltac:(lia) Rx KC) as K2.
  unfold wa in K2. rewrite Z_to_bv_bv_unsigned in K2. rewrite K2.
  (* [comment removed for export] *)
  exact (FR1 x Hout).
Qed.


End ND.
End NND.
