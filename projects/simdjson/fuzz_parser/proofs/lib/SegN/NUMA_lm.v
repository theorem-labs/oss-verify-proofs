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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg ABase AMalloc_iface AU_iface AU_fuzz_kit RtCells.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegCall SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA Require Import SegLibBr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AHM AGLUE AGLR AGLX AGLC AGLF AMEMH ABR_mem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require LMAB_cert LMAF_cert.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require LMAS_defs LMAE_defs LMAE_cert LMAB_defs LMAB_cert LMAF_defs LMAF_cert LMA_sum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Module NLM.
Section LM.
Context {rc : runConstT}.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis HSM5 : stack_malloc_5_stmt1 AI fflag rng_fs.
Hypothesis HSF5 : stack_free_5_stmt AI fflag.
Variables (L : alayout) (RNGh : footprint) (st : astate) (LB : list ablock).
Hypothesis HC5 : forall F1 n1 F2 n2, In (mkABlock (ABFake 5) F1 n1) LB -> In (mkABlock (ABFake 5) F2 n2) LB -> F1 = F2.
Hypothesis HFS : rng_fs L RNGh.
Hypothesis HIMG : rng_aimg RNGh.
Local Notation SG := asegs.
Definition GP0 : nat -> list word -> (word -> option byte) -> Prop := fun _ _ _ => True.

Local Notation hmH LB := (AHM.hmH AI L RNGh st LB).
Local Notation hmA LB := (AHM.hmA AI LB).
Local Notation hmC LB := (AHM.hmC AI LB).
Local Notation FB5 F := (mkABlock (ABFake 5) F 2048).

Lemma GP0_frame : forall gfp, SG.gp_frameP GP0 gfp. Proof. intros gfp id args E M M' _ _. exact I. Qed.
Lemma GP0_vc : forall c, (fun _ : SG.vc => false) c = true -> SG.vc_holds SG GP0 c. Proof. intros c H. discriminate H. Qed.

(* [comment removed for export] *)
Lemma lmae_summ : forall LB0, SP.summ_okHSC SG GP0 (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR (AHM.hmF RNGh) (AHM.hmS L RNGh)
  (SP.SUMY (SP.p_G LMAE_defs.LMAE) LMAE_defs.T0 (SP.p_ex LMAE_defs.LMAE) (SP.p_W LMAE_defs.LMAE) (SP.p_A LMAE_defs.LMAE)
     (SP.p_PS LMAE_defs.LMAE) false (SP.p_CR LMAE_defs.LMAE)).
Proof.
  intros LB0.
  exact (SP.summ_of_pcheckHSC SG GP0 _ _ (GP0_frame _) GP0_vc (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR (AHM.HMC_sub AI LB0)
           (AHM.HMF AI L RNGh st LB0) (AHM.hmF RNGh) (AHM.hmS L RNGh) (AHM.HMS_mono L RNGh)
           LMAE_defs.LMAE LMAE_defs.LMAE_IT _ _ _ LMAE_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ LMAE_cert.lmae_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA []) ltac:(intros S0 []) ltac:(cbn; tauto)).
Qed.

Lemma u_sub_lit_add : forall (sp pq : word) (c : Z), 0 <= c -> c + bv_unsigned pq <= bv_unsigned sp ->
  bv_unsigned (sp - (Z_to_bv 64 c + pq))%bv = bv_unsigned sp - c - bv_unsigned pq.
Proof.
  intros sp pq c H0 H1. pose proof (bv_unsigned_in_range 64 sp) as R1. pose proof (bv_unsigned_in_range 64 pq) as R2.
  change (bv_modulus 64) with (2^64) in R1, R2.
  rewrite bv_sub_unsigned, bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite (Z.mod_small c (2^64)) by lia. rewrite (Z.mod_small (c + bv_unsigned pq) (2^64)) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma summ_okH_HSC : forall LB0 GP S, SP.summ_okH SG GP (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR S ->
  SP.summ_okHSC SG GP (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR (AHM.hmF RNGh) (AHM.hmS L RNGh) S.
Proof.
  intros LB0 GP S H E M rom ms H1 H2 H3 _ _ H4 H5 H6. destruct (H E M rom ms H1 H2 H3 H4 H5 H6) as (ms' & X & E' & M' & Hm & R).
  exists ms', X, E', M'. split; [exact (SP.fpu_of SG (AHM.hmF RNGh) _ _ _ _ Hm) | exact R].
Qed.

Lemma lmab_summ : forall LB0, SP.summ_okHSC SG GP0 (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR (AHM.hmF RNGh) (AHM.hmS L RNGh)
  (SP.SUMY (SP.p_G LMAB_defs.LMAB) LMAB_defs.T0 (SP.p_ex LMAB_defs.LMAB) (SP.p_W LMAB_defs.LMAB) (SP.p_A LMAB_defs.LMAB)
     (SP.p_PS LMAB_defs.LMAB) false (SP.p_CR LMAB_defs.LMAB)).
Proof.
  intros LB0.
  exact (SP.summ_of_pcheckHSC SG GP0 _ _ (GP0_frame _) GP0_vc (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR (AHM.HMC_sub AI LB0)
           (AHM.HMF AI L RNGh st LB0) (AHM.hmF RNGh) (AHM.hmS L RNGh) (AHM.HMS_mono L RNGh)
           LMAB_defs.LMAB LMAB_defs.LMAB_IT _ _ _ LMAB_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ LMAB_cert.lmab_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA [])
           ltac:(intros S0 [<-|[<-|[<-|[]]]]; apply summ_okH_HSC;
                 first [ apply ABR.mcah_ok; lia | apply ABR.msah_ok; lia ])
           ltac:(cbn; tauto)).
Qed.

Lemma lmaf_summ : forall LB0, SP.summ_okHSC SG GP0 (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR (AHM.hmF RNGh) (AHM.hmS L RNGh)
  (SP.SUMY (SP.p_G LMAF_defs.LMAF) LMAF_defs.T0 (SP.p_ex LMAF_defs.LMAF) (SP.p_W LMAF_defs.LMAF) (SP.p_A LMAF_defs.LMAF)
     (SP.p_PS LMAF_defs.LMAF) false (SP.p_CR LMAF_defs.LMAF)).
Proof.
  intros LB0.
  exact (SP.summ_of_pcheckHSC SG GP0 _ _ (GP0_frame _) GP0_vc (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR (AHM.HMC_sub AI LB0)
           (AHM.HMF AI L RNGh st LB0) (AHM.hmF RNGh) (AHM.hmS L RNGh) (AHM.HMS_mono L RNGh)
           LMAF_defs.LMAF LMAF_defs.LMAF_IT _ _ _ LMAF_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ LMAF_cert.lmaf_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA []) ltac:(intros S0 []) ltac:(cbn; tauto)).
Qed.

(* [comment removed for export] *)
Lemma lm_step_e : forall E M rom ms,
  AHM.hmR rom -> SX.aw_genuine E (SP.p_A LMAS_defs.LMAS) -> SP.wins_client (hmC LB) E (SP.p_W LMAS_defs.LMAS) ->
  hmH LB M -> ST.tm_okF SG LMAS_defs.T0 E M rom ms ->
  exists ms1 E1 M1 R1 F1 fc1, ExecF.mstepsF SG (SP.fpu (AHM.hmF RNGh) (SP.p_A LMAS_defs.LMAS) E) ms ms1
    /\ ms1 = MS R1 F1 (Z_to_bv 64 0x50834) fc1 None M1 rom /\ frm0 fc1 /\ rfull R1
    /\ regs_ok E1 (ST.t_regs LMAE_defs.XSM) R1 /\ know_ok SG E1 M1 (ST.t_know LMAE_defs.XSM)
    /\ SP.gagree 18 E E1 /\ eb E1 = eb E /\ hmH LB M1
    /\ (forall x : word, SP.outside_wins E (SP.p_W LMAS_defs.LMAS) (bv_unsigned x) -> M1 x = M x).
Proof.
  intros E M rom ms HR HA HW HH HT.
  destruct (lmae_summ LB E M rom ms HR HA HW I ltac:(intros w []) HH HT ltac:(constructor))
    as (ms1 & X1 & E1 & M1 & Hms1 & HX1 & HT1 & _ & Hg1 & Hb1 & HH1 & FR1).
  cbn [SP.sm_post LMAE_defs.LMAE SP.PGCA SP.p_ex In] in HX1. destruct HX1 as [<-|[]].
  destruct HT1 as (HZ1 & HF1 & (R1 & Hms1' & HR1 & _ & HK1)).
  cbn [ST.tstate s_pc s_regs s_log s_know mem_denot] in Hms1', HR1, HK1.
  exists ms1, E1, M1, R1, (ms_fregs ms1), (ms_fcsr ms1).
  split; [exact Hms1|]. split; [rewrite Hms1' at 1; destruct ms1; reflexivity|].
  split; [exact HZ1|]. split; [rewrite Hms1' in HF1; exact HF1|]. split; [exact HR1|]. split; [exact HK1|].
  split; [exact Hg1|]. split; [exact Hb1|]. split; [exact HH1|]. exact FR1.
Qed.

(* [comment removed for export] *)
Definition SPAx : expr := EAlu ALU_SUB (EVar 1) (EAlu ALU_ADD (ELit 256) (EVar 19)).
Definition sg1 : list expr := map EVar (seq 0 18) ++ [EVar 34; EVar 35; EVar 18; SPAx] ++ map EVar (seq 36 14).
Definition TABS : list SC.wn := [(ELit 0, 20600 + 2147450880, ELit 1324); (ELit 0, 21928 + 2147450880, ELit 80)].
Definition PR1 : list SC.wn := [SP.stack_win SPAx; SP.stack_shwin (EAlu ALU_SUB (EVar 1) (ELit 4384))] ++ SP.p_CR LMAS_defs.LMAS ++ TABS.
Definition postregs1 : list expr :=
  [ELit 0; ELit 0xc5cb4; SPAx; EVar 2; EVar 3; EVar 36; EVar 37; EVar 38; EVar 1; SPAx;
   EMd M_MUL (ELit 2048) (EVar 34); EVar 39; EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45;
   EVar 6; EVar 7; EVar 8; ELit 175424; EVar 10; EVar 11; EVar 12; ELit 5; ELit 2147450880; EVar 15;
   EVar 46; EVar 47; EVar 48; EVar 49].
Definition knP1 : list kentry := Eval vm_compute in
  let surv := List.filter (AGL.survR (ST.t_know LMAE_defs.XSM) PR1 PR1) (ST.t_know LMAE_defs.XSM) in
  List.filter (fun K => negb (ST.kimplied SG surv K)) (map (ST.ksub sg1) (ST.t_know LMAB_defs.T0)).
Lemma lm_b1_regs : ST.regs_match (List.filter (AGL.survR (ST.t_know LMAE_defs.XSM) PR1 PR1) (ST.t_know LMAE_defs.XSM) ++ knP1)
  postregs1 (map (ST.esub sg1) (ST.t_regs LMAB_defs.T0)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lm_b1_kn : AGL.bridge_ok SG (ST.t_know LMAE_defs.XSM) PR1 PR1 knP1 sg1 (ST.t_know LMAB_defs.T0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lm_b1_len : length knP1 = 25%nat. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma regs_mkR : forall E sr x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  regs_ok E sr (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) ->
  [x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15;x16;x17;x18;x19;x20;x21;x22;x23;x24;x25;x26;x27;x28;x29;x30;x31]
  = map (fun k => edenot E (sr_get sr (Z_to_bv 5 k))) rkeys.
Proof.
  intros E sr x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 HR.
  unfold rkeys. cbn [map]. rewrite <- !(HR _). reflexivity.
Qed.

(* [comment removed for export] *)
Definition sg2 : list expr := map EVar (seq 0 18) ++ [EVar 22; EVar 23; ELit 0xc6bf4; EVar 21; EVar 44; EVar 45; EVar 46; EVar 21] ++
  map EVar (seq 47 8) ++ [EVar 33; EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 18)) (ELit 2147450880); EVar 34; EVar 35; EVar 36; EVar 37;
  EVar 38; ELit 2147450880; EVar 39] ++ map EVar (seq 55 4).
Definition PR2 : list SC.wn := [SP.stack_win (EVar 21); SP.stack_shwin (EAlu ALU_SUB (EVar 1) (ELit 4384))] ++ SP.p_CR LMAS_defs.LMAS ++ TABS.
Definition postregs2 : list expr :=
  [ELit 0; ELit 0xc6bf4; EVar 21; EVar 2; EVar 3; EVar 44; EVar 45; EVar 46; EVar 1; EVar 21;
   EVar 47; EVar 48; EVar 49; EVar 50; EVar 51; EVar 52; EVar 53; EVar 54;
   EVar 33; EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 18)) (ELit 2147450880); EVar 34; EVar 35; EVar 23; EVar 36; EVar 37; EVar 38;
   ELit 2147450880; EVar 39; EVar 55; EVar 56; EVar 57; EVar 58].
Definition knP2 : list kentry := Eval vm_compute in
  let surv := List.filter (AGL.survR (ST.t_know LMAB_defs.XSF) PR2 PR2) (ST.t_know LMAB_defs.XSF) in
  List.filter (fun K => negb (ST.kimplied SG surv K)) (map (ST.ksub sg2) (ST.t_know LMAF_defs.T0)).
Lemma lm_b2_regs : ST.regs_match (List.filter (AGL.survR (ST.t_know LMAB_defs.XSF) PR2 PR2) (ST.t_know LMAB_defs.XSF) ++ knP2)
  postregs2 (map (ST.esub sg2) (ST.t_regs LMAF_defs.T0)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lm_b2_kn : AGL.bridge_ok SG (ST.t_know LMAB_defs.XSF) PR2 PR2 knP2 sg2 (ST.t_know LMAF_defs.T0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lm_b2_len : length knP2 = 7%nat. Proof. vm_compute. reflexivity. Qed.


(* [comment removed for export] *)
Lemma lm_glue5 : forall E rom ms1 E1 M1 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) F1 fc1,
  AHM.hmR rom -> SX.aw_genuine E (SP.p_A LMAS_defs.LMAS) -> SP.wins_client (hmC LB) E (SP.p_W LMAS_defs.LMAS) ->
  AHM.hmS L RNGh (bv_unsigned (ev E1 1)) 4384 -> SP.crs_law (hmA LB) E (SP.p_CR LMAS_defs.LMAS) ->
  ms1 = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F1 (Z_to_bv 64 0x50834) fc1 None M1 rom -> frm0 fc1 ->
  regs_ok E1 (ST.t_regs LMAE_defs.XSM) (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) -> know_ok SG E1 M1 (ST.t_know LMAE_defs.XSM) ->
  SP.gagree 18 E E1 -> eb E1 = eb E -> hmH LB M1 ->
  exists ms2 E2 M2 F,
    ExecF.mstepsF SG RNGh ms1 ms2 /\ ST.tm_okF SG LMAB_defs.T0 E2 M2 rom ms2
    /\ SP.gagree 18 E E2 /\ eb E = eb E2
    /\ AHEAP AI L RNGh st (FB5 F :: LB) M2 /\ mem_inv SG M2
    /\ F mod 2048 = 0 /\ ablk F (F + 2048) /\ F + 2048 <= ATOP /\ rng RNGh F 2048 /\ rng RNGh (shad F) 256
    /\ (forall a, aclient_addr CI LB (bv_unsigned x2) a -> a < shad F \/ shad F + 256 <= a)
    /\ AGLR.rt_pres AI LB (bv_unsigned x2) M1 M2
    /\ ev E2 18 = Z_to_bv 64 (F / 2048) /\ ev E2 19 = Z_to_bv 64 (fflag L 5 F)
    /\ bv_unsigned (ev E2 21) = bv_unsigned x2
    /\ bv_unsigned x2 = bv_unsigned (ev E1 1) - 256 - bv_unsigned (ev E1 19) /\ bv_unsigned (ev E1 19) <= 31
    /\ SX.aw_genuine E2 (SP.p_A LMAB_defs.LMAB) /\ SP.wins_client (hmC (FB5 F :: LB)) E2 (SP.p_W LMAB_defs.LMAB).
Proof.
  intros E rom ms1 E1 M1 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F1 fc1 HR HA HW HS0 HCR Hms1e HZ1 HR1 HK1 Hg1 Hb1 HH1. subst ms1.
  pose proof (regs_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HR1) as ER1.
  cbn [rkeys map LMAE_defs.XSM ST.t_regs LMAE_defs.XSM_regs] in ER1. vm_compute sr_get in ER1.
  injection ER1 as E_ra E_sp E_gp E_tp E_t0 E_t1 E_t2 E_s0 E_s1 E_a0 E_a1 E_a2 E_a3 E_a4 E_a5 E_a6 E_a7 E_s2 E_s3 E_s4 E_s5 E_s6 E_s7
                   E_s8 E_s9 E_s10 E_s11 E_t3 E_t4 E_t5 E_t6.
  (* [comment removed for export] *)
  assert (KPQ : kentry_ok SG E1 M1 (KRange (EVar 19) 0 31)) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  assert (KTP : kentry_ok SG E1 M1 (KRange (EVar 3) 0x642e70 0x642e70)) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  assert (KSP : kentry_ok SG E1 M1 (KRange (EVar 1) 140728898425120 0x800000000000)) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  assert (KWS : kentry_ok SG E1 M1 (KWr (SA (EVar 1) (-4384)) (ELit 4384))) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  assert (KUS : kentry_ok SG E1 M1 (KUnk (SA (EVar 1) (-4384)) (ELit 4384))) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  cbn [kentry_ok edenot] in KPQ, KTP, KSP.
  destruct HS0 as (HS1 & HS2 & HS3).
  set (SP := bv_unsigned (ev E1 1)) in *. set (PQ := bv_unsigned (ev E1 19)) in *.
  assert (ESPA : bv_unsigned x2 = SP - 256 - PQ).
  { rewrite E_sp. cbn [edenot]. apply u_sub_lit_add; unfold SP, PQ in *; lia. }
  set (lo := SP - 4384).
  assert (STK1 : stk SG M1 lo (bv_unsigned x2)).
  { pose proof (SLB.kn_stk SG E1 M1 _ _ _ KWS KUS) as H. cbn [edenot] in H. rewrite u_lit64a in H.
    rewrite (Z.mod_small 4384 (2^64)) in H by lia. fold SP in H.
    destruct (stk_split SG M1 (SP + -4384) (bv_unsigned x2) (SP + -4384 + 4384) H ltac:(lia)) as [H1 _].
    replace lo with (SP + -4384) by (unfold lo; lia). exact H1. }
  assert (ETP : x4 = Z_to_bv 64 ATP).
  { rewrite E_tp. cbn [edenot]. apply bv_eq. rewrite u_lit64a. unfold ATP. rewrite (Z.mod_small 0x642e70 (2^64)) by lia. lia. }
  pose proof (HSM5 L RNGh x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
                F1 fc1 M1 st LB lo (proj1 HH1) HC5 (proj2 HH1) STK1 ltac:(unfold lo; lia) ltac:(unfold lo, SM5_STACK; lia)
                ltac:(lia) ETP ltac:(replace lo with (SP - 4384) by reflexivity; exact HS3) HIMG HFS) as HSM.
  unfold ASTKMALLOC5 in HSM. rewrite <- HR in HSM.
  destruct HSM as (ms2 & Hms2 & (F & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & M2 & j0 & j1 & j2 & junk &
                   -> & MI2 & STK2 & PRES & AH2 & HFm & HFb & HFt & HFc & HFs & RF1 & RF2 & BSH & B5)).
  set (E1' := SLB.env_ext E1 34 [Z_to_bv 64 (F / 2048); Z_to_bv 64 (fflag L 5 F); t0; t1; t2; a1; a2; a3; a4; a5; a6; a7; t3; t4; t5; t6]).
  (* [comment removed for export] *)
  pose proof atop_range as AT.
  assert (HF0 : 0x665000 <= F /\ F + 2048 <= 0x7FFFFF800000).
  { destruct HFb as [[B1 B2]|[B1 B2]]; unfold AIMG_HI, KLS in *; lia. }
  assert (VLT : forall k, (k < 34)%nat -> ev E1' k = ev E1 k) by (intros k Hk; apply SLB.env_ext_lt; exact Hk).
  assert (V34 : ev E1' 34 = Z_to_bv 64 (F / 2048)) by reflexivity.
  assert (V35 : ev E1' 35 = Z_to_bv 64 (fflag L 5 F)) by reflexivity.
  assert (UF : bv_unsigned (mul_div M_MUL (Z_to_bv 64 2048) (ev E1' 34)) = F).
  { rewrite V34, u_mul64, !u_lit64a. rewrite (Z.mod_small 2048 (2^64)) by lia.
    rewrite (Z.mod_small (F / 2048) (2^64)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite Z.mod_small; [|split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|]].
    - clear - HFm. Z.div_mod_to_equations. lia.
    - assert (2048 * (F / 2048) <= F) by (apply Z.mul_div_le; lia). lia. }
  assert (USF : bv_unsigned (mul_div M_MUL (Z_to_bv 64 256) (ev E1' 34)) = F / 8).
  { rewrite V34, u_mul64, !u_lit64a. rewrite (Z.mod_small 256 (2^64)) by lia.
    rewrite (Z.mod_small (F / 2048) (2^64)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (E8 : F / 8 = 256 * (F / 2048)) by (clear - HFm; Z.div_mod_to_equations; lia).
    rewrite <- E8. apply Z.mod_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (U34 : bv_unsigned (ev E1' 34) = F / 2048).
  { rewrite V34. apply u_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
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
  assert (XF : 8 * X8 + 498 <= F \/ F + 2048 <= 8 * X8 \/ 498 <= 0).
  { apply (AGLR.fresh_apart AI L RNGh st LB M2 5 F 2048 (8 * X8) 498 AH2 CRX); unfold AIMG_HI; lia. }
  assert (XF' : 8 * X8 + 504 <= F \/ F + 2048 <= 8 * X8).
  { clear - XF HFm EXH. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (USP1 : bv_unsigned (ev E1' 1) = SP) by (rewrite (VLT 1%nat) by lia; reflexivity).
  assert (U19 : bv_unsigned (ev E1' 19) = PQ) by (rewrite (VLT 19%nat) by lia; reflexivity).
  assert (U16 : bv_unsigned (ev E1' 16) = X8) by (rewrite (VLT 16%nat) by lia; reflexivity).
  assert (U17 : bv_unsigned (ev E1' 17) = XH) by (rewrite (VLT 17%nat) by lia; reflexivity).
  assert (USPA : bv_unsigned (alu64 ALU_SUB (ev E1' 1) (alu64 ALU_ADD (Z_to_bv 64 256) (ev E1' 19))) = SP - 256 - PQ).
  { rewrite u_sub64, u_add64, u_lit64a, USP1, U19. rewrite (Z.mod_small 256 (2^64)) by lia.
    rewrite (Z.mod_small (256 + PQ) (2^64)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (UX : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (ev E1' 16)) = 8 * X8).
  { rewrite u_mul64, u_lit64a, U16. rewrite (Z.mod_small 8 (2^64)) by lia. apply Z.mod_small. lia. }
  assert (UXH : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (ev E1' 17)) = 8 * XH).
  { rewrite u_mul64, u_lit64a, U17. rewrite (Z.mod_small 8 (2^64)) by lia. apply Z.mod_small. lia. }
  assert (UF2 : bv_unsigned (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 2048) (ev E1' 34)) (Z_to_bv 64 2048)) = F + 2048).
  { rewrite u_add64, UF, u_lit64a. rewrite (Z.mod_small 2048 (2^64)) by lia. apply Z.mod_small. lia. }
  assert (ESH : shad F = F / 8 + 2147450880).
  { unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. }
  assert (F8 : F / 8 < 2^44 /\ 0 <= F / 8) by (split; [apply Z.div_lt_upper_bound | apply Z.div_pos]; lia).
  (* [comment removed for export] *)
  assert (STKS1 : stk SG M1 (bv_unsigned x2) SP).
  { pose proof (SLB.kn_stk SG E1 M1 _ _ _ KWS KUS) as H. cbn [edenot] in H. rewrite u_lit64a in H.
    rewrite (Z.mod_small 4384 (2^64)) in H by lia. fold SP in H.
    destruct (stk_split SG M1 (SP + -4384) (bv_unsigned x2) (SP + -4384 + 4384) H ltac:(lia)) as [_ H2].
    replace (SP + -4384 + 4384) with SP in H2 by lia. exact H2. }
  assert (KEEP : forall a, bv_unsigned x2 <= a < SP -> M2 (wa a) = M1 (wa a) /\ (wview SG M1 (wa a) <> None -> wview SG M2 (wa a) <> None)).
  { intros a Ha. apply (PRES a ltac:(lia)). left. lia. }
  pose proof (AGX.stk_join SG M1 M2 lo (bv_unsigned x2) SP STK2 STKS1 KEEP) as STKM2.
  assert (RO2 : forall x, lo <= x < SP -> seg_rom SG (Z_to_bv 64 x) = None).
  { intros x Hx. apply ref_seg_rom_none. rewrite u_small by lia. lia. }
  assert (KP1 : know_ok SG E1' M2 knP1).
  { unfold knP1. repeat apply Forall_cons.
    (* [comment removed for export] *)
    - apply AGX.kx_range. cbn [edenot]. rewrite U34. split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia.
    (* [comment removed for export] *)
    - apply (AGX.kx_cells_wr SG E1' M2 _ _ [C8 j0; C8 j1; C8 j2; CB 2016 junk; C8 (Z_to_bv 64 (fflag L 5 F))]).
      + unfold estart. cbn [a_base a_off edenot]. rewrite UF, Z.add_0_r. exact HFc.
      + unfold elenZ. cbn [edenot cells_size csize]. rewrite u_lit64a. reflexivity.
      + unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite UF, u_lit64a. rewrite (Z.mod_small 2048 (2^64)) by lia. lia.
    (* [comment removed for export] *)
    - apply AGLR.unk_of_wr.
      + unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite UF, u_lit64a. rewrite (Z.mod_small 2048 (2^64)) by lia. lia.
      + unfold estart. cbn [a_base a_off edenot]. rewrite UF. lia.
      + unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UF, u_lit64a, Z.add_0_r. rewrite (Z.mod_small 2048 (2^64)) by lia.
        exact (proj2 HFc).
    (* [comment removed for export] *)
    - apply (AGX.kx_word_cells SG E1' M2 _ _ _ F [C8 j0; C8 j1; C8 j2; CB 2016 junk; C8 (Z_to_bv 64 (fflag L 5 F))] 2040
               (C8 (Z_to_bv 64 (fflag L 5 F))) HFc); [reflexivity | | | reflexivity | | lia].
      + unfold estart. cbn [a_base a_off edenot]. rewrite UF. lia.
      + unfold flat, estart. cbn [a_base a_off edenot]. rewrite UF. lia.
      + cbn [cbytes edenot]. rewrite V35. reflexivity.
    (* [comment removed for export] *)
    - apply (AGX.kx_cells_wr SG E1' M2 _ _ (repeat (C8 (Z_to_bv 64 0)) 32)).
      + unfold estart. cbn [a_base a_off edenot]. rewrite USF. rewrite <- ESH. exact HFs.
      + unfold elenZ. cbn [edenot]. rewrite u_lit64a. reflexivity.
      + unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, u_lit64a. rewrite (Z.mod_small 256 (2^64)) by lia. lia.
    (* [comment removed for export] *)
    - apply AGLR.unk_of_wr.
      + unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, u_lit64a. rewrite (Z.mod_small 256 (2^64)) by lia. lia.
      + unfold estart. cbn [a_base a_off edenot]. rewrite USF. lia.
      + unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, u_lit64a. rewrite (Z.mod_small 256 (2^64)) by lia.
        rewrite <- ESH. exact (proj2 HFs).
    (* [comment removed for export] *)
    - apply AGX.kx_range. cbn [edenot]. rewrite UF2. lia.
    (* [comment removed for export] *)
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UF, !u_lit64a.
      rewrite (Z.mod_small 0 (2^64)), (Z.mod_small 0x100000001000 (2^64)), (Z.mod_small 2048 (2^64)) by lia.
      destruct HFb as [[B1 B2]|[B1 B2]]; unfold AIMG_HI, KLS in *; lia.
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UF, USP1, !u_lit64a.
      rewrite (Z.mod_small 4384 (2^64)), (Z.mod_small 2048 (2^64)) by lia. lia.
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UF, UX, !u_lit64a.
      rewrite (Z.mod_small 504 (2^64)), (Z.mod_small 2048 (2^64)) by lia. lia.
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, U16, !u_lit64a.
      rewrite (Z.mod_small 256 (2^64)), (Z.mod_small 63 (2^64)) by lia. clear - XF' EXH HFm. Z.div_mod_to_equations. lia.
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, UXH, !u_lit64a.
      rewrite (Z.mod_small 256 (2^64)), (Z.mod_small 72 (2^64)) by lia. clear - XF' EXH HFm. Z.div_mod_to_equations. lia.
    (* [comment removed for export] *)
    - apply AGX.kx_zero.
      + unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, u_lit64a. rewrite (Z.mod_small 256 (2^64)) by lia. lia.
      + unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, u_lit64a. rewrite (Z.mod_small 256 (2^64)) by lia.
        intros i Hi. rewrite <- ESH. exact (AGLR.zero_cellsN M2 (shad F) 32 HFs ltac:(lia) ltac:(cbn; lia) i ltac:(cbn; lia)).
    (* [comment removed for export] *)
    - apply (AGX.kx_stk_wr SG E1' M2 _ _ lo SP STKM2); unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?USPA, ?u_lit64a;
        rewrite ?(Z.mod_small 4352 (2^64)) by lia; unfold lo; lia.
    - apply (AGX.kx_stk_unk SG E1' M2 _ _ lo SP STKM2 RO2); unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?USPA, ?u_lit64a;
        rewrite ?(Z.mod_small 4352 (2^64)) by lia; unfold lo; lia.
    (* [comment removed for export] *)
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UF, USPA, !u_lit64a.
      rewrite (Z.mod_small 4352 (2^64)), (Z.mod_small 2048 (2^64)) by lia. lia.
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, USP1, !u_lit64a.
      rewrite (Z.mod_small 4384 (2^64)), (Z.mod_small 256 (2^64)) by lia. lia.
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, USPA, !u_lit64a.
      rewrite (Z.mod_small 4352 (2^64)), (Z.mod_small 256 (2^64)) by lia. lia.
    (* [comment removed for export] *)
    - apply (AGX.kx_stk_wr SG E1' M2 _ _ lo SP STKM2); unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?USP1, ?u_lit64a;
        rewrite ?(Z.mod_small 4384 (2^64)) by lia; unfold lo; lia.
    - apply (AGX.kx_stk_unk SG E1' M2 _ _ lo SP STKM2 RO2); unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?USP1, ?u_lit64a;
        rewrite ?(Z.mod_small 4384 (2^64)) by lia; unfold lo; lia.
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
  (* [comment removed for export] *)
  assert (ER2 : regs_ok E1' postregs1 (mkR x1 x2 x3 x4 t0 t1 t2 x8 x9 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7
                                         x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)).
  { apply AGC.regs_ok_tl; [reflexivity|]. unfold postregs1. cbn [tl map edenot].
    change (ev E1' 36) with t0. change (ev E1' 37) with t1. change (ev E1' 38) with t2.
    change (ev E1' 39) with a1. change (ev E1' 40) with a2. change (ev E1' 41) with a3. change (ev E1' 42) with a4.
    change (ev E1' 43) with a5. change (ev E1' 44) with a6. change (ev E1' 45) with a7.
    change (ev E1' 46) with t3. change (ev E1' 47) with t4. change (ev E1' 48) with t5. change (ev E1' 49) with t6.
    rewrite E_ra, E_sp, E_gp, E_tp, E_s0, E_s1, E_s2, E_s3, E_s4, E_s5, E_s6, E_s7, E_s8, E_s9, E_s10, E_s11.
    cbn [edenot]. rewrite ?(VLT 1%nat), ?(VLT 2%nat), ?(VLT 3%nat), ?(VLT 6%nat), ?(VLT 7%nat), ?(VLT 8%nat), ?(VLT 10%nat),
      ?(VLT 11%nat), ?(VLT 12%nat), ?(VLT 15%nat), ?(VLT 19%nat) by lia.
    assert (EA0 : mul_div M_MUL (Z_to_bv 64 2048) (ev E1' 34) = Z_to_bv 64 F).
    { apply bv_eq. rewrite UF. rewrite u_small by lia. reflexivity. }
    rewrite EA0. reflexivity. }
  (* [comment removed for export] *)
  assert (TABIN : forall lo' hi', In (lo', hi') IMG_TABS -> In (lo', hi') CI).
  { intros lo' hi' H. apply IMG_CI. unfold client_ranges. apply in_or_app. right. exact H. }
  assert (RK1 : AGL.rt_keep SG E1' PR1 PR1 M1 M2).
  { apply (AGLR.rt_keep_cls AI LB (bv_unsigned x2) lo M1 M2 E1' PR1 (conj PRES BSH)
             (AGLR.shw_of_aheap AI L RNGh st LB _ M2 AH2 (fun b H => or_intror H)) ltac:(unfold lo; lia) ltac:(lia)).
    unfold PR1. cbn [app SP.p_CR LMAS_defs.LMAS SP.PGH]. unfold TABS.
    cbv [LMAS_defs.vX LMAS_defs.vX8 LMAS_defs.vXH LMAS_defs.mul LMAS_defs.V].
    repeat apply Forall_cons.
    - intros x Hin Hx. left. pose proof (AGLR.in_stack_win E1' SPAx x) as H. unfold SPAx in H. cbn [edenot] in H.
      rewrite USPA in H. specialize (H ltac:(lia) Hin). lia.
    - intros x Hin Hx. right; left. pose proof (SP.shwin_sh_above E1' (EAlu ALU_SUB (EVar 1) (ELit 4384)) x) as H.
      cbn [edenot] in H. rewrite u_sub64, USP1, u_lit64a in H. rewrite (Z.mod_small 4384 (2^64)) in H by lia.
      rewrite (Z.mod_small (SP - 4384) (2^64)) in H by lia.
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
  assert (HKX1 : know_ok SG E1' M1 (ST.t_know LMAE_defs.XSM)).
  { apply (AxSymRun3.know_ok_agree SG 34 E1 E1' M1 _); [| vm_compute; reflexivity | exact HK1].
    split; [intros k Hk; symmetry; apply VLT; exact Hk | reflexivity]. }
  assert (HRP : ret_pc x1 = Z_to_bv 64 (ST.t_pc LMAB_defs.T0)) by (apply bv_eq; rewrite E_ra; vm_compute; reflexivity).
  lazymatch type of Hms2 with ExecF.mstepsF _ _ _ ?m => set (ms2 := m) in * end.
  pose proof (AGL.bridge_tm SG E1' M1 M2 _ PR1 PR1 knP1 postregs1 sg1 LMAB_defs.T0 _ F1 fc1 rom ms2 HKX1 RK1 KP1 ER2 lm_b1_regs lm_b1_kn
                ltac:(unfold ms2; rewrite HRP, HR; reflexivity) HZ1 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) as HT2.
  (* [comment removed for export] *)
  set (E2 := ST.senv E1' sg1) in *.
  assert (VE2 : forall k, (k < 18)%nat -> ev E2 k = ev E1 k).
  { intros k Hk. unfold E2. rewrite SP.senv_nth. unfold sg1. rewrite app_nth1 by (rewrite length_map, length_seq; lia).
    rewrite (nth_indep _ (ELit 0) (EVar 0)) by (rewrite length_map, length_seq; lia). rewrite map_nth, seq_nth by lia.
    cbn [edenot]. apply VLT. lia. }
  assert (VE18 : ev E2 18 = Z_to_bv 64 (F / 2048)) by (unfold E2; rewrite SP.senv_nth; reflexivity).
  assert (VE21 : bv_unsigned (ev E2 21) = SP - 256 - PQ) by (unfold E2; rewrite SP.senv_nth; exact USPA).
  pose proof HT2 as (_ & _ & (R2' & _ & _ & _ & HK2)). cbn [ST.tstate s_know mem_denot] in HK2.
  assert (GE2 : SP.gagree 18 E E2) by (intros k Hk; rewrite VE2 by exact Hk; apply Hg1; exact Hk).
  assert (BE2 : eb E = eb E2) by (unfold E2, E1', ST.senv, SLB.env_ext; cbn; symmetry; exact Hb1).
  assert (HA2 : SX.aw_genuine E2 (SP.p_A LMAB_defs.LMAB)).
  { cbn [SP.p_A LMAB_defs.LMAB SP.PGCA]. apply (AGC.aw_gen_mix SG E E2 M2 _ _ _ 18 HK2 HA GE2 BE2). vm_compute. reflexivity. }
  assert (UF2' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 2048) (ev E2 18)) = F) by (rewrite VE18, <- V34; exact UF).
  assert (USF2 : bv_unsigned (mul_div M_MUL (Z_to_bv 64 256) (ev E2 18)) = F / 8) by (rewrite VE18, <- V34; exact USF).
  assert (HW2 : SP.wins_client (hmC (FB5 F :: LB)) E2 (SP.p_W LMAB_defs.LMAB)).
  { cbn [SP.p_W LMAB_defs.LMAB SP.PGCA]. unfold SP.wins_client in HW |- *. cbn [SP.p_W LMAS_defs.LMAS SP.PGH] in HW.
    pose proof (Forall_inv HW) as HW1. pose proof (Forall_inv (Forall_inv_tail HW)) as HW2'.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HW))) as HW3. cbv beta in HW1, HW2', HW3.
    repeat apply Forall_cons.
    - match goal with |- context [SP.win_den E2 ?w] => rewrite <- (SP.win_den_gagree 18 E E2 w GE2 BE2 eq_refl) end. unfold AHM.hmC in *.
      apply (AGLR.acr_mono AI LB); [exact HW1 | intros b Hb; right; exact Hb].
    - match goal with |- context [SP.win_den E2 ?w] => rewrite <- (SP.win_den_gagree 18 E E2 w GE2 BE2 eq_refl) end. unfold AHM.hmC in *.
      apply (AGLR.acr_mono AI LB); [exact HW2' | intros b Hb; right; exact Hb].
    - match goal with |- context [SP.win_den E2 ?w] => rewrite <- (SP.win_den_gagree 18 E E2 w GE2 BE2 eq_refl) end. unfold AHM.hmC in *.
      apply (AGLR.acr_mono AI LB); [exact HW3 | intros b Hb; right; exact Hb].
    - unfold AHM.hmC. cbv [LMAB_defs.vF LMAB_defs.mul LMAB_defs.vF11 LMAB_defs.V]. cbn [SP.win_den edenot fst snd]. rewrite UF2', u_lit64a.
      rewrite (Z.mod_small 2048 (2^64)) by lia. apply (AGLR.acr_fake AI _ _ 5 F 2048); [left; reflexivity | lia | lia].
    - unfold AHM.hmC. cbv [LMAB_defs.mul LMAB_defs.vF11 LMAB_defs.V]. cbn [SP.win_den edenot fst snd]. rewrite USF2, u_lit64a.
      rewrite (Z.mod_small 256 (2^64)) by lia. apply (AGLR.acr_fake_shadow AI _ _ 5 F 2048); [left; reflexivity | |];
        unfold ASHOFF; clear - HFm; Z.div_mod_to_equations; lia.
    - unfold AHM.hmC. cbv [LMAB_defs.vSPA LMAB_defs.V]. cbn [SP.win_den edenot fst snd]. rewrite VE21, u_lit64a.
      rewrite (Z.mod_small 4352 (2^64)) by lia. apply (AGLR.acr_stack AI); lia.
    - constructor. }
  assert (V19 : ev E2 19 = Z_to_bv 64 (fflag L 5 F)) by (unfold E2; rewrite SP.senv_nth; exact V35).
  exists ms2, E2, M2, F.
  split; [exact Hms2|]. split; [exact HT2|]. split; [exact GE2|]. split; [exact BE2|]. split; [exact AH2|]. split; [exact MI2|].
  split; [exact HFm|]. split; [exact HFb|]. split; [exact HFt|]. split; [exact RF1|]. split; [exact RF2|]. split; [exact B5|].
  split; [exact (conj PRES BSH)|]. split; [exact VE18|]. split; [exact V19|]. split; [rewrite VE21; symmetry; exact ESPA|].
  split; [exact ESPA|]. split; [fold PQ; lia|]. split; [exact HA2 | exact HW2].
Qed.


(* [comment removed for export] *)
Lemma lm_free5 : forall E rom ms3 E1 E3 M3 F,
  AHM.hmR rom -> SP.crs_law (hmA LB) E (SP.p_CR LMAS_defs.LMAS) -> SP.gagree 18 E E1 ->
  AHM.hmS L RNGh (bv_unsigned (ev E1 1)) 4384 ->
  ST.tm_okF SG LMAB_defs.XSF E3 M3 rom ms3 -> hmH (FB5 F :: LB) M3 ->
  (forall k, (k < 18)%nat -> ev E3 k = ev E1 k) -> ev E3 18 = Z_to_bv 64 (F / 2048) -> ev E3 19 = Z_to_bv 64 (fflag L 5 F) ->
  bv_unsigned (ev E3 21) = bv_unsigned (ev E1 1) - 256 - bv_unsigned (ev E1 19) -> bv_unsigned (ev E1 19) <= 31 ->
  F mod 2048 = 0 -> ablk F (F + 2048) ->
  exists ms4 E4 M4, ExecF.mstepsF SG RNGh ms3 ms4 /\ ST.tm_okF SG LMAF_defs.T0 E4 M4 rom ms4
    /\ (forall k, (k < 18)%nat -> ev E4 k = ev E1 k) /\ eb E4 = eb E3
    /\ AHEAP AI L RNGh st LB M4 /\ mem_inv SG M4 /\ AGLR.rt_pres AI LB (bv_unsigned (ev E3 21)) M3 M4.
Proof.
  intros E rom ms3 E1 E3 M3 F HR HCR Hg1 HS0 HT3 HH3 VE31 V3_18 V3_19 V3_21 HPQ HFm HFb.
  destruct HS0 as (HS1 & HS2 & HS3).
  pose proof (bv_unsigned_in_range 64 (ev E1 19)) as RPQ. change (bv_modulus 64) with (2^64) in RPQ.
  set (SP := bv_unsigned (ev E1 1)) in *. set (PQ := bv_unsigned (ev E1 19)) in *. set (lo := SP - 4384).
  pose proof atop_range as AT.
  assert (HF0 : 0x665000 <= F /\ F + 2048 <= 0x7FFFFF800000).
  { destruct HFb as [[B1 B2]|[B1 B2]]; unfold AIMG_HI, KLS in *; lia. }
  assert (TABIN : forall lo' hi', In (lo', hi') IMG_TABS -> In (lo', hi') CI).
  { intros lo' hi' H. apply IMG_CI. unfold client_ranges. apply in_or_app. right. exact H. }
  (* [comment removed for export] *)
  destruct HT3 as (HZ3 & HF3 & (R3 & Hms3' & HR3 & _ & HK3)).
  cbn [ST.tstate s_pc s_regs s_log s_know mem_denot] in Hms3', HR3, HK3.
  assert (Hms3e : ms3 = MS R3 (ms_fregs ms3) (Z_to_bv 64 0x50a40) (ms_fcsr ms3) None M3 rom)
    by (rewrite Hms3' at 1; destruct ms3; reflexivity).
  assert (HF3' : PIosRegs.rfull R3) by (rewrite Hms3e in HF3; exact HF3). clear HF3.
  destruct HF3' as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20 & y21
                   & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & ->).
  pose proof (regs_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HR3) as ER3.
  cbn [rkeys map LMAB_defs.XSF ST.t_regs LMAB_defs.XSF_regs] in ER3. vm_compute sr_get in ER3.
  injection ER3 as Y_ra Y_sp Y_gp Y_tp Y_t0 Y_t1 Y_t2 Y_s0 Y_s1 Y_a0 Y_a1 Y_a2 Y_a3 Y_a4 Y_a5 Y_a6 Y_a7 Y_s2 Y_s3 Y_s4 Y_s5 Y_s6 Y_s7
                   Y_s8 Y_s9 Y_s10 Y_s11 Y_t3 Y_t4 Y_t5 Y_t6.
  assert (U3_21 : bv_unsigned (ev E3 21) = SP - 256 - PQ) by exact V3_21.
  assert (U3_1 : bv_unsigned (ev E3 1) = SP) by (rewrite (VE31 1%nat) by lia; reflexivity).
  assert (KSP : kentry_ok SG E3 M3 (KRange (EVar 1) 140728898425120 0x800000000000)) by (apply (ST.kin_ok SG E3 M3 _ _ HK3); vm_compute; reflexivity).
  cbn [kentry_ok edenot] in KSP. rewrite U3_1 in KSP.
  assert (UF3 : bv_unsigned (mul_div M_MUL (Z_to_bv 64 2048) (ev E3 18)) = F).
  { rewrite V3_18, u_mul64, !u_lit64a. rewrite (Z.mod_small 2048 (2^64)) by lia.
    rewrite (Z.mod_small (F / 2048) (2^64)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite Z.mod_small; [|split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|]].
    - clear - HFm. Z.div_mod_to_equations. lia.
    - assert (2048 * (F / 2048) <= F) by (apply Z.mul_div_le; lia). lia. }
  assert (KX8 : kentry_ok SG E3 M3 (KRange (EVar 16) 0xcca04 0xfffffeffff7)) by (apply (ST.kin_ok SG E3 M3 _ _ HK3); vm_compute; reflexivity).
  assert (KXH : kentry_ok SG E3 M3 (KRange (EAlu ALU_SUB (EVar 16) (EMd M_MUL (ELit 8) (EVar 17))) 4 4))
    by (apply (ST.kin_ok SG E3 M3 _ _ HK3); vm_compute; reflexivity).
  assert (KXHr : kentry_ok SG E3 M3 (KRange (EVar 17) 0x19940 0x1fffffdfffe)) by (apply (ST.kin_ok SG E3 M3 _ _ HK3); vm_compute; reflexivity).
  cbn [kentry_ok edenot] in KX8, KXH, KXHr. rewrite (VE31 16%nat) in KX8, KXH by lia. rewrite (VE31 17%nat) in KXH, KXHr by lia.
  set (X8 := bv_unsigned (ev E1 16)) in *. set (XH := bv_unsigned (ev E1 17)) in *.
  assert (EXH : X8 = 8 * XH + 4).
  { rewrite u_sub64, u_mul64, u_lit64a in KXH. fold XH in KXH. fold X8 in KXH.
    rewrite (Z.mod_small 8 (2^64)) in KXH by lia. rewrite (Z.mod_small (8 * XH) (2^64)) in KXH by lia.
    rewrite Z.mod_small in KXH by lia. lia. }
  assert (RO2 : forall x, lo <= x < SP -> seg_rom SG (Z_to_bv 64 x) = None).
  { intros x Hx. apply ref_seg_rom_none. rewrite u_small by lia. lia. }
  assert (USPA3 : bv_unsigned y2 = SP - 256 - PQ) by (rewrite Y_sp; cbn [edenot]; exact U3_21).
  assert (KWS3 : kentry_ok SG E3 M3 (KWr (SA (EVar 1) (-4384)) (ELit 4384))) by (apply (ST.kin_ok SG E3 M3 _ _ HK3); vm_compute; reflexivity).
  assert (KUS3 : kentry_ok SG E3 M3 (KUnk (SA (EVar 1) (-4384)) (ELit 4384))) by (apply (ST.kin_ok SG E3 M3 _ _ HK3); vm_compute; reflexivity).
  assert (KFG3 : kentry_ok SG E3 M3 (KWord (SA (EMd M_MUL (ELit 2048) (EVar 18)) 2040) 8 (EVar 19)))
    by (apply (ST.kin_ok SG E3 M3 _ _ HK3); vm_compute; reflexivity).
  assert (KWF3 : kentry_ok SG E3 M3 (KWr (SA (EMd M_MUL (ELit 2048) (EVar 18)) 0) (ELit 2048)))
    by (apply (ST.kin_ok SG E3 M3 _ _ HK3); vm_compute; reflexivity).
  assert (STK3F : stk SG M3 lo SP).
  { pose proof (SLB.kn_stk SG E3 M3 _ _ _ KWS3 KUS3) as H. cbn [edenot] in H. rewrite u_lit64a in H.
    rewrite (Z.mod_small 4384 (2^64)) in H by lia. rewrite U3_1 in H.
    replace (SP + -4384 + 4384) with SP in H by lia. replace (SP + -4384) with lo in H by (unfold lo; lia). exact H. }
  assert (STK3 : stk SG M3 lo (bv_unsigned y2)).
  { rewrite USPA3. destruct (stk_split SG M3 lo (SP - 256 - PQ) SP STK3F ltac:(unfold lo; lia)) as [H1 _]. exact H1. }
  assert (STKS3 : stk SG M3 (bv_unsigned y2) SP).
  { rewrite USPA3. destruct (stk_split SG M3 lo (SP - 256 - PQ) SP STK3F ltac:(unfold lo; lia)) as [_ H2]. exact H2. }
  assert (EA0 : y10 = Z_to_bv 64 F).
  { rewrite Y_a0. apply bv_eq. transitivity (bv_unsigned (mul_div M_MUL (Z_to_bv 64 2048) (ev E3 18))); [reflexivity|].
    rewrite UF3. rewrite u_small by lia. reflexivity. }
  assert (RWF : rw_cells SG M3 (F + 2040) [C8 (Z_to_bv 64 (fflag L 5 F))]).
  { pose proof (AGC.kword8_rw SG E3 M3 _ _ _ _ _ KFG3 KWF3) as H.
    unfold estart in H. cbn [a_base a_off edenot] in H. rewrite UF3, u_lit64a in H. rewrite (Z.mod_small 2048 (2^64)) in H by lia.
    rewrite V3_19 in H. apply H; lia. }
  assert (RNG3 : rng RNGh lo (bv_unsigned y2 - lo)).
  { rewrite USPA3. apply (rng_sub RNGh (SP - 4384) (al_top L - (SP - 4384))); [exact HS3 | unfold lo; lia | unfold lo; lia]. }
  pose proof (HSF5 L RNGh y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
                (ms_fregs ms3) (ms_fcsr ms3) M3 st LB lo F (proj1 HH3) (proj2 HH3) STK3 ltac:(unfold lo; lia)
                ltac:(unfold SF5_STACK; rewrite USPA3; unfold lo; lia) EA0 RWF RNG3) as HSF.
  unfold ASTKFREE5 in HSF. rewrite <- HR in HSF. rewrite <- Hms3e in HSF.
  destruct HSF as (ms4 & Hms4 & (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & M4 & -> & MI4 & STK4 & PRES4 & AH4 & BSH4)).
  (* [comment removed for export] *)
  set (E3' := SLB.env_ext E3 44 [u0; u1; u2; b0; b1; b2; b3; b4; b5; b6; b7; u3; u4; u5; u6]).
  assert (VLT3 : forall k, (k < 44)%nat -> ev E3' k = ev E3 k) by (intros k Hk; apply SLB.env_ext_lt; exact Hk).
  assert (VX3 : forall k, (k < 18)%nat -> ev E3' k = ev E1 k) by (intros k Hk; rewrite VLT3, VE31 by lia; reflexivity).
  assert (ER4 : regs_ok E3' postregs2 (mkR y1 y2 y3 y4 u0 u1 u2 y8 y9 b0 b1 b2 b3 b4 b5 b6 b7
                                          y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 u3 u4 u5 u6)).
  { apply AGC.regs_ok_tl; [reflexivity|]. unfold postregs2. cbn [tl map edenot].
    change (ev E3' 44) with u0. change (ev E3' 45) with u1. change (ev E3' 46) with u2.
    change (ev E3' 47) with b0. change (ev E3' 48) with b1. change (ev E3' 49) with b2. change (ev E3' 50) with b3.
    change (ev E3' 51) with b4. change (ev E3' 52) with b5. change (ev E3' 53) with b6. change (ev E3' 54) with b7.
    change (ev E3' 55) with u3. change (ev E3' 56) with u4. change (ev E3' 57) with u5. change (ev E3' 58) with u6.
    rewrite Y_ra, Y_sp, Y_gp, Y_tp, Y_s0, Y_s1, Y_s2, Y_s3, Y_s4, Y_s5, Y_s6, Y_s7, Y_s8, Y_s9, Y_s10, Y_s11.
    cbn [edenot]. rewrite ?(VLT3 1%nat), ?(VLT3 2%nat), ?(VLT3 3%nat), ?(VLT3 18%nat), ?(VLT3 21%nat), ?(VLT3 23%nat), ?(VLT3 33%nat),
      ?(VLT3 34%nat), ?(VLT3 35%nat), ?(VLT3 36%nat), ?(VLT3 37%nat), ?(VLT3 38%nat), ?(VLT3 39%nat) by lia. reflexivity. }
  assert (U16' : bv_unsigned (ev E3' 16) = X8) by (rewrite (VX3 16%nat) by lia; reflexivity).
  assert (U17' : bv_unsigned (ev E3' 17) = XH) by (rewrite (VX3 17%nat) by lia; reflexivity).
  assert (UX' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (ev E3' 16)) = 8 * X8).
  { rewrite u_mul64, u_lit64a, U16'. rewrite (Z.mod_small 8 (2^64)) by lia. apply Z.mod_small. lia. }
  assert (UXH' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (ev E3' 17)) = 8 * XH).
  { rewrite u_mul64, u_lit64a, U17'. rewrite (Z.mod_small 8 (2^64)) by lia. apply Z.mod_small. lia. }
  assert (RK2 : AGL.rt_keep SG E3' PR2 PR2 M3 M4).
  { apply (AGLR.rt_keep_cls AI LB (bv_unsigned y2) lo M3 M4 E3' PR2 (conj PRES4 BSH4)
             (AGLR.shw_of_aheap AI L RNGh st LB _ M4 AH4 (fun b H => H)) ltac:(unfold lo; lia) ltac:(lia)).
    unfold PR2. cbn [app SP.p_CR LMAS_defs.LMAS SP.PGH]. unfold TABS.
    cbv [LMAS_defs.vX LMAS_defs.vX8 LMAS_defs.vXH LMAS_defs.mul LMAS_defs.V].
    repeat apply Forall_cons.
    - intros x Hin Hx. left. pose proof (AGLR.in_stack_win E3' (EVar 21) x) as H. cbn [edenot] in H.
      rewrite (VLT3 21%nat), U3_21 in H by lia. specialize (H ltac:(lia) Hin). rewrite USPA3. lia.
    - intros x Hin Hx. right; left. pose proof (SP.shwin_sh_above E3' (EAlu ALU_SUB (EVar 1) (ELit 4384)) x) as H.
      cbn [edenot] in H. rewrite u_sub64, (VLT3 1%nat), U3_1, u_lit64a in H by lia. rewrite (Z.mod_small 4384 (2^64)) in H by lia.
      rewrite (Z.mod_small (SP - 4384) (2^64)) in H by lia.
      destruct (H ltac:(lia) Hin) as (a & Ha & ->). exists a. split; [unfold lo; lia|]. unfold SP.sh_of, shad, ASHOFF. reflexivity.
    - intros x Hin Hx. right; right; left. apply (HCR (EMd M_MUL (ELit 8) (EVar 16), 0, ELit 498) ltac:(vm_compute; left; reflexivity)).
      unfold SC.in_win, SG.win_den in Hin. cbn [edenot] in Hin. rewrite UX', u_lit64a in Hin.
      rewrite (Z.mod_small 498 (2^64)) in Hin by lia.
      assert (WE : SP.win_den E (EMd M_MUL (ELit 8) (EVar 16), 0, ELit 498) = (8 * X8 + 0, 8 * X8 + 0 + 498)).
      { cbn [SP.win_den edenot]. rewrite u_mul64, !u_lit64a, (Hg1 16%nat ltac:(lia)). fold X8.
        rewrite (Z.mod_small 8 (2^64)), (Z.mod_small 498 (2^64)) by lia. rewrite (Z.mod_small (8 * X8) (2^64)) by lia. reflexivity. }
      rewrite WE. cbn [fst snd]. lia.
    - intros x Hin Hx. right; right; left. apply (HCR (EVar 16, 2147450880, ELit 63) ltac:(vm_compute; right; left; reflexivity)).
      unfold SC.in_win, SG.win_den in Hin. cbn [edenot] in Hin. rewrite U16', u_lit64a in Hin.
      rewrite (Z.mod_small 63 (2^64)) in Hin by lia.
      assert (WE : SP.win_den E (EVar 16, 2147450880, ELit 63) = (X8 + 2147450880, X8 + 2147450880 + 63)).
      { cbn [SP.win_den edenot]. rewrite !u_lit64a, (Hg1 16%nat ltac:(lia)). fold X8.
        rewrite (Z.mod_small 63 (2^64)) by lia. reflexivity. }
      rewrite WE. cbn [fst snd]. lia.
    - intros x Hin Hx. right; right; left.
      apply (HCR (EMd M_MUL (ELit 8) (EVar 17), 2147450880, ELit 72) ltac:(vm_compute; right; right; left; reflexivity)).
      unfold SC.in_win, SG.win_den in Hin. cbn [edenot] in Hin. rewrite UXH', u_lit64a in Hin.
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
  assert (HKX3 : know_ok SG E3' M3 (ST.t_know LMAB_defs.XSF)).
  { apply (AxSymRun3.know_ok_agree SG 44 E3 E3' M3 _); [| vm_compute; reflexivity | exact HK3].
    split; [intros k Hk; symmetry; apply VLT3; exact Hk | reflexivity]. }
  assert (USP4 : bv_unsigned (ev E3' 1) = SP) by (rewrite (VX3 1%nat) by lia; reflexivity).
  assert (KEEP2 : forall a, bv_unsigned y2 <= a < SP -> M4 (wa a) = M3 (wa a) /\ (wview SG M3 (wa a) <> None -> wview SG M4 (wa a) <> None)).
  { intros a Ha. apply (PRES4 a ltac:(lia)). left. lia. }
  pose proof (AGX.stk_join SG M3 M4 lo (bv_unsigned y2) SP STK4 STKS3 KEEP2) as STKM4.
  assert (KP2 : know_ok SG E3' M4 knP2).
  { unfold knP2. repeat apply Forall_cons.
    - apply (AGX.kx_stk_wr SG E3' M4 _ _ lo SP STKM4); unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?USP4, ?u_lit64a;
        rewrite ?(Z.mod_small 4384 (2^64)) by lia; unfold lo; lia.
    - apply (AGX.kx_stk_unk SG E3' M4 _ _ lo SP STKM4 RO2); unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?USP4, ?u_lit64a;
        rewrite ?(Z.mod_small 4384 (2^64)) by lia; unfold lo; lia.
    - apply AGX.kx_img; [lia | lia | exact MI4 |]. intros a Ha. rewrite a_ro_addr. apply andb_true_intro.
      split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
    - destruct (AI_rtcells AI _ _ _ _ _ AH4) as (_ & GOT & _).
      apply (AGX.kx_word_cells SG E3' M4 _ _ _ 0x1072f0 _ 16 (C8 (Z_to_bv 64 0x10faf8)) GOT); [reflexivity | | | reflexivity | reflexivity | lia];
        unfold flat, estart; cbn [a_base a_off edenot]; rewrite u_lit64a; rewrite (Z.mod_small 0 (2^64)) by lia; lia.
    - destruct (AI_rtcells AI _ _ _ _ _ AH4) as (_ & _ & _ & _ & SHB & _).
      apply (AGX.kx_word_cells SG E3' M4 _ _ _ 0x10faf8 _ 0 (C8 (Z_to_bv 64 0x7fff8000)) SHB); [reflexivity | | | reflexivity | reflexivity | lia];
        unfold flat, estart; cbn [a_base a_off edenot]; rewrite u_lit64a; rewrite (Z.mod_small 0 (2^64)) by lia; lia.
    - pose proof (client_got_of_aheap AI _ _ _ _ _ AH4 MI4) as SUARG.
      apply (AGX.kx_word_cells SG E3' M4 _ _ _ AGOT_SUAR _ 0 (C8 (Z_to_bv 64 ASUAR)) SUARG); [reflexivity | | | reflexivity | reflexivity | lia];
        unfold flat, estart, AGOT_SUAR; cbn [a_base a_off edenot]; rewrite u_lit64a; rewrite (Z.mod_small 0 (2^64)) by lia; lia.
    - destruct (AI_rtcells AI _ _ _ _ _ AH4) as (_ & _ & _ & _ & _ & SUAR & _).
      apply (AGX.kx_word_cells SG E3' M4 _ _ _ 0x10fb00 _ 0 (C4 (Z_to_bv 64 1)) SUAR); [reflexivity | | | reflexivity | vm_compute; reflexivity | lia];
        unfold flat, estart; cbn [a_base a_off edenot]; rewrite u_lit64a; rewrite (Z.mod_small 0 (2^64)) by lia; lia.
    - constructor. }
  assert (HRP2 : ret_pc y1 = Z_to_bv 64 (ST.t_pc LMAF_defs.T0)) by (apply bv_eq; rewrite Y_ra; vm_compute; reflexivity).
  lazymatch type of Hms4 with ExecF.mstepsF _ _ _ ?m => set (ms4 := m) in * end.
  pose proof (AGL.bridge_tm SG E3' M3 M4 _ PR2 PR2 knP2 postregs2 sg2 LMAF_defs.T0 _ (ms_fregs ms3) (ms_fcsr ms3) rom ms4 HKX3 RK2 KP2 ER4
                lm_b2_regs lm_b2_kn ltac:(unfold ms4; rewrite HRP2, HR; reflexivity) HZ3
                (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) as HT4.
  exists ms4, (ST.senv E3' sg2), M4.
  split; [exact Hms4|]. split; [exact HT4|].
  split.
  { intros k Hk. rewrite SP.senv_nth. unfold sg2. rewrite app_nth1 by (rewrite length_map, length_seq; lia).
    rewrite (nth_indep _ (ELit 0) (EVar 0)) by (rewrite length_map, length_seq; lia). rewrite map_nth, seq_nth by lia.
    cbn [edenot]. apply VX3. lia. }
  split; [reflexivity|]. split; [exact AH4|]. split; [exact MI4|].
  replace (ev E3 21) with y2 by (rewrite Y_sp; reflexivity). exact (conj PRES4 BSH4).
Qed.


Theorem lmsa_ok : SP.summ_okHSC SG GP0 (hmH LB) (hmA LB) (hmC LB) AHM.hmR (AHM.hmF RNGh) (AHM.hmS L RNGh) LMA_sum.LMSA.
Proof.
  intros E M rom ms HR HA HW HS HCR HH HT HG.
  cbn [SP.sm_pre SP.sm_post SP.sm_W SP.sm_A SP.sm_PS SP.sm_CR SP.sm_G LMA_sum.LMSA] in *.
  (* [comment removed for export] *)
  destruct (lm_step_e E M rom ms HR HA HW HH HT) as (ms1 & E1 & M1 & R1 & F1 & fc1 & Hms1 & Hms1e & HZ1 & HF1 & HR1 & HK1 & Hg1 & Hb1 & HH1 & FR1).
  destruct HF1 as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ->).
  unfold SP.hs_ok in HS. change (SP.dstk (Some LMAS_defs.vSP) (SP.p_W LMAS_defs.LMAS)) with (Some (LMAS_defs.vSP, 4384)) in HS.
  cbv beta iota in HS. change (edenot E LMAS_defs.vSP) with (ev E 1) in HS. rewrite (Hg1 1%nat ltac:(lia)) in HS.
  (* [comment removed for export] *)
  destruct (lm_glue5 E rom ms1 E1 M1 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F1 fc1 HR HA HW HS HCR Hms1e HZ1 HR1 HK1 Hg1 Hb1 HH1)
    as (ms2 & E2 & M2 & F & Hms2 & HT2 & GE2 & BE2 & AH2 & MI2 & HFm & HFb & HFt & RF1 & RF2 & B5 & RP12 & VE18 & V19 & VE21x & ESPA & HPQ & HA2 & HW2).
  (* [comment removed for export] *)
  destruct (lmab_summ (FB5 F :: LB) E2 M2 rom ms2 HR HA2 HW2 I ltac:(intros w []) (conj AH2 MI2) HT2 ltac:(constructor))
    as (ms3 & X3 & E3 & M3 & Hms3 & HX3 & HT3 & _ & Hg3 & Hb3 & HH3 & FR3).
  cbn [SP.sm_post SP.p_ex LMAB_defs.LMAB SP.PGCA In] in HX3. destruct HX3 as [<-|[]].
  cbn [SP.sm_A SP.sm_G SP.sm_W SP.sm_PS] in Hms3, Hg3, FR3. change (SP.p_G LMAB_defs.LMAB) with 22%nat in Hg3.
  assert (VE31 : forall k, (k < 18)%nat -> ev E3 k = ev E1 k).
  { intros k Hk. rewrite <- (Hg3 k) by lia. rewrite <- (GE2 k) by lia. apply Hg1. exact Hk. }
  assert (V3_18 : ev E3 18 = Z_to_bv 64 (F / 2048)) by (rewrite <- (Hg3 18%nat) by lia; exact VE18).
  assert (V3_19 : ev E3 19 = Z_to_bv 64 (fflag L 5 F)) by (rewrite <- (Hg3 19%nat) by lia; exact V19).
  assert (V3_21 : bv_unsigned (ev E3 21) = bv_unsigned (ev E1 1) - 256 - bv_unsigned (ev E1 19))
    by (rewrite <- (Hg3 21%nat) by lia; rewrite VE21x; exact ESPA).
  (* [comment removed for export] *)
  destruct (lm_free5 E rom ms3 E1 E3 M3 F HR HCR Hg1 HS HT3 HH3 VE31 V3_18 V3_19 V3_21 HPQ HFm HFb)
    as (ms4 & E4 & M4 & Hms4 & HT4 & VE4 & Hb4 & AH4 & MI4 & RP34).
  (* [comment removed for export] *)
  assert (GE4 : SP.gagree 18 E E4) by (intros k Hk; rewrite VE4 by exact Hk; apply Hg1; exact Hk).
  assert (BE4 : eb E = eb E4) by (rewrite Hb4, Hb3; exact BE2).
  pose proof HT4 as (_ & _ & (R4' & _ & _ & _ & HK4)). cbn [ST.tstate s_know mem_denot] in HK4.
  assert (HA4 : SX.aw_genuine E4 (SP.p_A LMAF_defs.LMAF)).
  { cbn [SP.p_A LMAF_defs.LMAF SP.PGCA]. apply (AGC.aw_gen_mix SG E E4 M4 _ _ _ 18 HK4 HA GE4 BE4). vm_compute. reflexivity. }
  assert (HW4 : SP.wins_client (hmC LB) E4 (SP.p_W LMAF_defs.LMAF)).
  { assert (EW : SP.p_W LMAF_defs.LMAF = SP.p_W LMAS_defs.LMAS) by (vm_compute; reflexivity). rewrite EW.
    assert (CL : forallb (SP.win_closed 18) (SP.p_W LMAS_defs.LMAS) = true) by (vm_compute; reflexivity).
    unfold SP.wins_client in *. apply Forall_forall. intros w Hw.
    rewrite <- (SP.win_den_gagree 18 E E4 w GE4 BE4 (proj1 (forallb_forall _ _) CL w Hw)).
    exact (proj1 (Forall_forall _ _) HW w Hw). }
  destruct (lmaf_summ LB E4 M4 rom ms4 HR HA4 HW4 I ltac:(intros w []) (conj AH4 MI4) HT4 ltac:(constructor))
    as (ms5 & X5 & E5 & M5 & Hms5 & HX5 & HT5 & _ & Hg5 & Hb5 & HH5 & FR5).
  cbn [SP.sm_post SP.p_ex LMAF_defs.LMAF SP.PGCA In] in HX5. destruct HX5 as [<-|[]].
  cbn [SP.sm_A SP.sm_G SP.sm_W SP.sm_PS] in Hms5, Hg5, FR5.
  (* [comment removed for export] *)
  pose proof HS as (HS1 & HS2 & HS3).
  pose proof (bv_unsigned_in_range 64 (ev E1 19)) as RPQ. change (bv_modulus 64) with (2^64) in RPQ.
  set (SP := bv_unsigned (ev E1 1)) in *. set (PQ := bv_unsigned (ev E1 19)) in *.
  assert (HF0 : 0x665000 <= F /\ F + 2048 <= 0x7FFFFF800000) by (destruct HFb as [[B1 B2]|[B1 B2]]; unfold AIMG_HI, KLS in *; lia).
  assert (UF2' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 2048) (ev E2 18)) = F).
  { rewrite VE18, u_mul64, !u_lit64a. rewrite (Z.mod_small 2048 (2^64)) by lia.
    rewrite (Z.mod_small (F / 2048) (2^64)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite Z.mod_small; [|split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|]].
    - clear - HFm. Z.div_mod_to_equations. lia.
    - assert (2048 * (F / 2048) <= F) by (apply Z.mul_div_le; lia). lia. }
  assert (USF2 : bv_unsigned (mul_div M_MUL (Z_to_bv 64 256) (ev E2 18)) = F / 8).
  { rewrite VE18, u_mul64, !u_lit64a. rewrite (Z.mod_small 256 (2^64)) by lia.
    rewrite (Z.mod_small (F / 2048) (2^64)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (E8 : F / 8 = 256 * (F / 2048)) by (clear - HFm; Z.div_mod_to_equations; lia).
    rewrite <- E8. apply Z.mod_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (ESH : shad F = F / 8 + 2147450880).
  { unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. }
  assert (VE21 : bv_unsigned (ev E2 21) = SP - 256 - PQ) by (rewrite VE21x; exact ESPA).
  (* [comment removed for export] *)
  exists ms5, LMAF_defs.XR, E5, M5.
  assert (FPB : forall b j, SP.fpu (AHM.hmF RNGh) (SP.p_A LMAB_defs.LMAB) E2 b j -> SP.fpu (AHM.hmF RNGh) (SP.p_A LMAS_defs.LMAS) E b j).
  { apply (AGLF.fpu_mix (AHM.hmF RNGh) E E2 _ _). apply (AGLF.fp_mix3 E E2 _ _ 18 _ GE2 BE2).
    intros w Hw. vm_compute in Hw. destruct Hw as [<-|[<-|[<-|[]]]]; intros b j Hw1 Hw2; cbn [SX.awin_den edenot fst snd] in Hw1, Hw2.
    - right. rewrite UF2' in Hw1, Hw2. rewrite u_lit64a in Hw2. rewrite (Z.mod_small 2048 (2^64)) in Hw2 by lia.
      destruct RF1 as (_ & _ & RF). apply RF; lia.
    - right. rewrite USF2 in Hw1, Hw2. rewrite u_lit64a in Hw2. rewrite (Z.mod_small 256 (2^64)) in Hw2 by lia.
      destruct RF2 as (_ & _ & RF). apply RF; rewrite ESH; lia.
    - left. rewrite VE21 in Hw1, Hw2. rewrite u_lit64a in Hw2. rewrite (Z.mod_small 4352 (2^64)) in Hw2 by lia.
      exists (EVar 1, -4384, ELit 4384). split; [vm_compute; left; reflexivity|]. cbn [SX.awin_den edenot fst snd].
      rewrite u_lit64a, (Z.mod_small 4384 (2^64)) by lia. rewrite (Hg1 1%nat) by lia. fold SP. lia. }
  assert (EA5 : SP.p_A LMAF_defs.LMAF = SP.p_A LMAS_defs.LMAS) by (vm_compute; reflexivity).
  rewrite EA5 in Hms5.
  assert (FPF : forall b j, SP.fpu (AHM.hmF RNGh) (SP.p_A LMAS_defs.LMAS) E4 b j -> SP.fpu (AHM.hmF RNGh) (SP.p_A LMAS_defs.LMAS) E b j)
    by (apply (SP.fpu_gagree (AHM.hmF RNGh) 18 E E4 _ GE4 BE4); vm_compute; reflexivity).
  split.
  { eapply ExecF.mstepsF_trans; [exact Hms1|].
    eapply ExecF.mstepsF_trans; [exact (ExecF.mstepsF_weaken SG _ _ _ _ (fun b j Hb => or_intror Hb) Hms2)|].
    eapply ExecF.mstepsF_trans; [exact (ExecF.mstepsF_weaken SG _ _ _ _ FPB Hms3)|].
    eapply ExecF.mstepsF_trans; [exact (ExecF.mstepsF_weaken SG _ _ _ _ (fun b j Hb => or_intror Hb) Hms4)|].
    exact (ExecF.mstepsF_weaken SG _ _ _ _ FPF Hms5). }
  split; [left; vm_compute; reflexivity|].
  split; [exact HT5|].
  split; [constructor|].
  split; [exact (SP.gagree_trans 18 E E4 E5 GE4 Hg5)|].
  split; [rewrite Hb5; symmetry; exact BE4|].
  split; [exact HH5|].
  (* [comment removed for export] *)
  cbn [SP.frame_ok]. intros x Hout Hcls.
  change (edenot E LMAS_defs.vSP) with (ev E 1) in Hcls. rewrite (Hg1 1%nat ltac:(lia)) in Hcls. fold SP in Hcls.
  assert (KC : AGLF.keep_cls AI LB SP (bv_unsigned x)) by exact Hcls.
  pose proof (bv_unsigned_in_range 64 x) as Rx; change (bv_modulus 64) with (2^64) in Rx.
  assert (CLS : forallb (SP.win_closed 18) (SP.p_W LMAS_defs.LMAS) = true) by (vm_compute; reflexivity).
  assert (EWF : SP.p_W LMAF_defs.LMAF = SP.p_W LMAS_defs.LMAS) by (vm_compute; reflexivity).
  cbn [SP.frame_ok SP.p_PS LMAF_defs.LMAF SP.PGCA] in FR5. rewrite EWF in FR5.
  rewrite (FR5 x (SP.outside_wins_gagree 18 E E4 _ _ GE4 BE4 CLS Hout)).
  pose proof (AGLF.keep_rt AI LB (bv_unsigned (ev E3 21)) SP M3 M4 (bv_unsigned x) RP34 ltac:(lia) ltac:(lia) Rx KC) as K4.
  unfold wa in K4. rewrite Z_to_bv_bv_unsigned in K4. rewrite K4.
  cbn [SP.frame_ok SP.p_PS LMAB_defs.LMAB SP.PGCA] in FR3.
  rewrite (FR3 x).
  2:{ cbn [SP.p_W LMAB_defs.LMAB SP.PGCA]. unfold SP.outside_wins.
      pose proof (SP.outside_wins_gagree 18 E E2 _ _ GE2 BE2 CLS Hout) as HO2. unfold SP.outside_wins in HO2.
      cbn [SP.p_W LMAS_defs.LMAS SP.PGH] in HO2.
      destruct (AGLF.fresh_out AI L RNGh st LB M2 5 F 2048 (bv_unsigned x2) SP (bv_unsigned x) AH2 B5
                  ltac:(clear - HFm; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) HFb HFt ltac:(lia) KC) as [OF OS].
      pose proof (AGLF.stack_out AI L RNGh st LB M SP (SP - 256 - PQ - 4096) (SP - PQ) (bv_unsigned x) (proj1 HH) ltac:(lia) ltac:(lia) KC) as OSt.
      apply Forall_cons; [exact (Forall_inv HO2)|]. apply Forall_cons; [exact (Forall_inv (Forall_inv_tail HO2))|].
      apply Forall_cons; [exact (Forall_inv (Forall_inv_tail (Forall_inv_tail HO2)))|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|constructor]]].
      - cbv [LMAB_defs.vF LMAB_defs.mul LMAB_defs.vF11 LMAB_defs.V]. cbn [SP.win_den edenot].
        rewrite UF2', u_lit64a, (Z.mod_small 2048 (2^64)) by lia. intros [H1 H2]. apply OF. lia.
      - cbv [LMAB_defs.mul LMAB_defs.vF11 LMAB_defs.V]. cbn [SP.win_den edenot].
        rewrite USF2, u_lit64a, (Z.mod_small 256 (2^64)) by lia. intros [H1 H2]. apply OS. rewrite ESH. change (2048 / 8) with 256. lia.
      - cbv [LMAB_defs.vSPA LMAB_defs.V]. cbn [SP.win_den edenot].
        rewrite VE21, u_lit64a, (Z.mod_small 4352 (2^64)) by lia. intros [H1 H2]. apply OSt. lia. }
  pose proof (AGLF.keep_rt AI LB (bv_unsigned x2) SP M1 M2 (bv_unsigned x) RP12 ltac:(lia) ltac:(lia) Rx KC) as K2.
  unfold wa in K2. rewrite Z_to_bv_bv_unsigned in K2. rewrite K2.
  exact (FR1 x Hout).
Qed.


End LM.
End NLM.
