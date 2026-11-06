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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AHM AGLUE AGLR AGLX AGLC AGLF AGLM AMEMH NUMA_lm NUMA_nd.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require SLOWAS_defs SLOWAE_defs SLOWAE_cert SLOWAB_defs SLOWABE_defs SLOWABCN_defs
  SLOWAF_defs SLOWAF_cert SLOWA_sum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Module NSL.

(* [comment removed for export] *)
Definition SBODY : SP.summ :=
  SP.SUMY (SP.p_G SLOWAB_defs.SLOWAB) SLOWAB_defs.T0 [SLOWABE_defs.XSS] (SP.p_W SLOWAB_defs.SLOWAB) (SP.p_A SLOWAB_defs.SLOWAB)
    (Some SLOWAB_defs.vSP) false (SP.p_CR SLOWABCN_defs.SLOWABCN).

(* [comment removed for export] *)
Definition eF : expr := EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 16)) (EVar 17).
Definition eV : expr := EMd M_MUL (ELit 8) (EVar 20).
Definition vSPe : expr := EMd M_MUL (ELit 16) (EVar 1).

(* [comment removed for export] *)
Lemma disj_pw : forall A n B m, 0 < n -> 0 < m -> (forall z, B <= z < B + m -> ~ (A <= z < A + n)) -> A + n <= B \/ B + m <= A.
Proof.
  intros A n B m Hn Hm H. destruct (Z_le_gt_dec (A + n) B) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (B + m) A) as [H2|H2]; [right; exact H2|].
  exfalso. apply (H (Z.max A B)); lia.
Qed.

Section SL.
Context {rc : runConstT}.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis HSM4 : stack_malloc_4_stmt1 AI fflag rng_fs.
Variables (L : alayout) (RNGh : footprint) (st : astate) (LB : list ablock).
Hypothesis NO4 : forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB.
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
Hypothesis HBODY : forall LB0,
  (forall F1 n1 F2 n2, In (mkABlock (ABFake 4) F1 n1) LB0 -> In (mkABlock (ABFake 4) F2 n2) LB0 -> F1 = F2) ->
  (forall F1 n1 F2 n2, In (mkABlock (ABFake 5) F1 n1) LB0 -> In (mkABlock (ABFake 5) F2 n2) LB0 -> F1 = F2) ->
  SP.summ_okHSC SG GP0 (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR (AHM.hmF RNGh) (AHM.hmS L RNGh) SBODY.

Lemma u4_cons : forall F, forall F1 n1 F2 n2, In (mkABlock (ABFake 4) F1 n1) (FB4 F :: LB) -> In (mkABlock (ABFake 4) F2 n2) (FB4 F :: LB) -> F1 = F2.
Proof.
  intros F F1 n1 F2 n2 [E1|H1] [E2|H2].
  - injection E1 as <- _. injection E2 as <- _. reflexivity.
  - exfalso. exact (NO4 F2 n2 H2).
  - exfalso. exact (NO4 F1 n1 H1).
  - exfalso. exact (NO4 F1 n1 H1).
Qed.

(* [comment removed for export] *)
Lemma slae_summ : forall LB0, SP.summ_okHSC SG GP0 (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR (AHM.hmF RNGh) (AHM.hmS L RNGh)
  (SP.SUMY (SP.p_G SLOWAE_defs.SLOWAE) SLOWAE_defs.T0 (SP.p_ex SLOWAE_defs.SLOWAE) (SP.p_W SLOWAE_defs.SLOWAE) (SP.p_A SLOWAE_defs.SLOWAE)
     (SP.p_PS SLOWAE_defs.SLOWAE) false (SP.p_CR SLOWAE_defs.SLOWAE)).
Proof.
  intros LB0.
  exact (SP.summ_of_pcheckHSC SG GP0 _ _ (NLM.GP0_frame _) NLM.GP0_vc (hmH LB0) (hmA LB0) (hmC LB0) AHM.hmR (AHM.HMC_sub AI LB0)
           (AHM.HMF AI L RNGh st LB0) (AHM.hmF RNGh) (AHM.hmS L RNGh) (AHM.HMS_mono L RNGh)
           SLOWAE_defs.SLOWAE SLOWAE_defs.SLOWAE_IT _ _ _ SLOWAE_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ SLOWAE_cert.slowae_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA []) ltac:(intros S0 []) ltac:(cbn; tauto)).
Qed.

Lemma slaf_summ : forall M0, SP.summ_okHSC SG GP0 (fun M => mem_inv SG M /\ wmono SG M0 M) (fun _ => False) (fun _ _ => True) AHM.hmR
  (AHM.hmF RNGh) (AHM.hmS L RNGh)
  (SP.SUMY (SP.p_G SLOWAF_defs.SLOWAF) SLOWAF_defs.T0 (SP.p_ex SLOWAF_defs.SLOWAF) (SP.p_W SLOWAF_defs.SLOWAF) (SP.p_A SLOWAF_defs.SLOWAF)
     (SP.p_PS SLOWAF_defs.SLOWAF) false (SP.p_CR SLOWAF_defs.SLOWAF)).
Proof.
  intros M0.
  exact (SP.summ_of_pcheckHSC SG GP0 _ _ (NLM.GP0_frame _) NLM.GP0_vc (fun M => mem_inv SG M /\ wmono SG M0 M) (fun _ => False)
           (fun _ _ => True) AHM.hmR (fun _ _ _ _ _ _ _ => I) (NND.HMF_F M0) (AHM.hmF RNGh) (AHM.hmS L RNGh) (AHM.HMS_mono L RNGh)
           SLOWAF_defs.SLOWAF SLOWAF_defs.SLOWAF_IT _ _ _ SLOWAF_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ SLOWAF_cert.slowaf_cert)
           (SP.itab_ranges_sound SG _) eq_refl ltac:(intros TA []) ltac:(intros S0 []) ltac:(cbn; tauto)).
Qed.

(* [comment removed for export] *)
Lemma sl_step_e : forall E M rom ms,
  AHM.hmR rom -> SX.aw_genuine E (SP.p_A SLOWAS_defs.SLOWAS) -> SP.wins_client (hmC LB) E (SP.p_W SLOWAS_defs.SLOWAS) ->
  hmH LB M -> ST.tm_okF SG SLOWAS_defs.T0 E M rom ms ->
  exists ms1 E1 M1 R1 F1 fc1, ExecF.mstepsF SG (SP.fpu (AHM.hmF RNGh) (SP.p_A SLOWAS_defs.SLOWAS) E) ms ms1
    /\ ms1 = MS R1 F1 (Z_to_bv 64 0x50668) fc1 None M1 rom /\ frm0 fc1 /\ rfull R1
    /\ regs_ok E1 (ST.t_regs SLOWAE_defs.XSM) R1 /\ know_ok SG E1 M1 (ST.t_know SLOWAE_defs.XSM)
    /\ SP.gagree 21 E E1 /\ eb E1 = eb E /\ hmH LB M1
    /\ (forall x : word, SP.outside_wins E (SP.p_W SLOWAS_defs.SLOWAS) (bv_unsigned x) -> M1 x = M x).
Proof.
  intros E M rom ms HR HA HW HH HT.
  destruct (slae_summ LB E M rom ms HR HA HW I ltac:(intros w []) HH HT ltac:(constructor))
    as (ms1 & X1 & E1 & M1 & Hms1 & HX1 & HT1 & _ & Hg1 & Hb1 & HH1 & FR1).
  cbn [SP.sm_post SLOWAE_defs.SLOWAE SP.PGCA SP.p_ex In] in HX1. destruct HX1 as [<-|[]].
  destruct HT1 as (HZ1 & HF1 & (R1 & Hms1' & HR1 & _ & HK1)).
  cbn [ST.tstate s_pc s_regs s_log s_know mem_denot] in Hms1', HR1, HK1.
  exists ms1, E1, M1, R1, (ms_fregs ms1), (ms_fcsr ms1).
  split; [exact Hms1|]. split; [rewrite Hms1' at 1; destruct ms1; reflexivity|].
  split; [exact HZ1|]. split; [rewrite Hms1' in HF1; exact HF1|]. split; [exact HR1|]. split; [exact HK1|].
  split; [exact Hg1|]. split; [exact Hb1|]. split; [exact HH1|]. exact FR1.
Qed.

(* [comment removed for export] *)
Definition SPAx : expr := EAlu ALU_SUB vSPe (EAlu ALU_ADD (ELit 192) (EVar 21)).
Definition SPAb : expr := EAlu ALU_SUB vSPe (EAlu ALU_ADD (ELit 192) (EMd M_MUL (ELit 16) (EVar 38))).
Definition sg1 : list expr := map EVar (seq 0 21) ++ [EVar 36; EVar 37; EVar 38] ++ map EVar (seq 39 14).
Definition FMINW : SC.wn := (ELit 0, 0x10b978, ELit 4).
Definition PR1 : list SC.wn := [SP.stack_win SPAx; SP.stack_shwin (EAlu ALU_SUB vSPe (ELit 4848))] ++ SP.p_CR SLOWAS_defs.SLOWAS ++ [FMINW] ++ NLM.TABS.
Definition postregs1 : list expr :=
  [ELit 0; ELit 0xc0b70; SPAb; EVar 2; EVar 3; EVar 39; EVar 40; EVar 41;
   vSPe; SPAb; EMd M_MUL (ELit 1024) (EVar 36); EVar 42; EVar 43; EVar 44; EVar 45; EVar 46; EVar 47; EVar 48;
   ELit 0xa0000002e; ELit 53; EVar 8; EVar 9; SLOWAE_defs.vF; EAlu ALU_ADD SLOWAE_defs.vF SLOWAE_defs.vN; SLOWAE_defs.vV;
   ELit 2147450880; ELit 1; EVar 15; EVar 49; EVar 50; EVar 51; EVar 52].
Definition knP1 : list kentry := Eval vm_compute in
  let surv := List.filter (AGL.survR (ST.t_know SLOWAE_defs.XSM) PR1 PR1) (ST.t_know SLOWAE_defs.XSM) in
  List.filter (fun K => negb (ST.kimplied SG surv K)) (map (ST.ksub sg1) (ST.t_know SLOWAB_defs.T0)).
Lemma sl_b1_regs : ST.regs_match (List.filter (AGL.survR (ST.t_know SLOWAE_defs.XSM) PR1 PR1) (ST.t_know SLOWAE_defs.XSM) ++ knP1)
  postregs1 (map (ST.esub sg1) (ST.t_regs SLOWAB_defs.T0)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sl_b1_kn : AGL.bridge_ok SG (ST.t_know SLOWAE_defs.XSM) PR1 PR1 knP1 sg1 (ST.t_know SLOWAB_defs.T0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sl_glue4 : forall E rom ms1 E1 M1 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) F1 fc1,
  AHM.hmR rom -> SX.aw_genuine E (SP.p_A SLOWAS_defs.SLOWAS) -> SP.wins_client (hmC LB) E (SP.p_W SLOWAS_defs.SLOWAS) ->
  AHM.hmS L RNGh (16 * bv_unsigned (ev E1 1)) 4848 -> SP.crs_law (hmA LB) E (SP.p_CR SLOWAS_defs.SLOWAS) ->
  ms1 = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F1 (Z_to_bv 64 0x50668) fc1 None M1 rom -> frm0 fc1 ->
  regs_ok E1 (ST.t_regs SLOWAE_defs.XSM) (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) -> know_ok SG E1 M1 (ST.t_know SLOWAE_defs.XSM) ->
  SP.gagree 21 E E1 -> eb E1 = eb E -> hmH LB M1 ->
  exists ms2 E2 M2 F,
    ExecF.mstepsF SG RNGh ms1 ms2 /\ ST.tm_okF SG SLOWAB_defs.T0 E2 M2 rom ms2
    /\ SP.gagree 21 E E2 /\ eb E = eb E2
    /\ AHEAP AI L RNGh st (FB4 F :: LB) M2 /\ mem_inv SG M2
    /\ F mod 1024 = 0 /\ ablk F (F + 1024) /\ F + 1024 <= ATOP /\ rng RNGh F 1024 /\ rng RNGh (shad F) 128
    /\ (forall a, aclient_addr CI LB (bv_unsigned x2) a -> a < shad F \/ shad F + 128 <= a)
    /\ AGLR.rt_pres AI LB (bv_unsigned x2) M1 M2
    /\ ev E2 21 = Z_to_bv 64 (F / 1024) /\ ev E2 22 = Z_to_bv 64 (fflag L 4 F)
    /\ 16 * bv_unsigned (ev E2 23) = bv_unsigned (ev E1 21)
    /\ bv_unsigned x2 = 16 * bv_unsigned (ev E1 1) - 192 - bv_unsigned (ev E1 21) /\ bv_unsigned (ev E1 21) <= 31
    /\ SX.aw_genuine E2 (SP.p_A SLOWAB_defs.SLOWAB) /\ SP.wins_client (hmC (FB4 F :: LB)) E2 (SP.p_W SLOWAB_defs.SLOWAB).
Proof.
  intros E rom ms1 E1 M1 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F1 fc1 HR HA HW HS0 HCR Hms1e HZ1 HR1 HK1 Hg1 Hb1 HH1. subst ms1.
  pose proof (NLM.regs_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HR1) as ER1.
  cbn [rkeys map SLOWAE_defs.XSM ST.t_regs SLOWAE_defs.XSM_regs] in ER1. vm_compute sr_get in ER1.
  injection ER1 as E_ra E_sp E_gp E_tp E_t0 E_t1 E_t2 E_s0 E_s1 E_a0 E_a1 E_a2 E_a3 E_a4 E_a5 E_a6 E_a7 E_s2 E_s3 E_s4 E_s5 E_s6 E_s7
                   E_s8 E_s9 E_s10 E_s11 E_t3 E_t4 E_t5 E_t6.
  (* [comment removed for export] *)
  assert (KPQ : kentry_ok SG E1 M1 (KRange (EVar 21) 0 31)) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  assert (KAQ : kentry_ok SG E1 M1 (KAlign (EVar 21) 16)) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  assert (KTP : kentry_ok SG E1 M1 (KRange (EVar 3) 0x642e70 0x642e70)) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  assert (KSP : kentry_ok SG E1 M1 (KRange (EVar 1) 8795556151599 0x80000000000)) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  assert (KWS : kentry_ok SG E1 M1 (KWr (SA vSPe (-4848)) (ELit 4848))) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  assert (KUS : kentry_ok SG E1 M1 (KUnk (SA vSPe (-4848)) (ELit 4848))) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  cbn [kentry_ok edenot] in KPQ, KAQ, KTP, KSP.
  destruct HS0 as (HS1 & HS2 & HS3).
  set (SP16 := bv_unsigned (ev E1 1)) in *. set (PQ := bv_unsigned (ev E1 21)) in *.
  assert (USP : bv_unsigned (mul_div M_MUL (Z_to_bv 64 16) (ev E1 1)) = 16 * SP16).
  { rewrite u_mul64, u_lit64a. fold SP16. rewrite (Z.mod_small 16 (2^64)) by lia. apply Z.mod_small. lia. }
  set (SP := 16 * SP16) in *. assert (ESP : SP = 16 * SP16) by reflexivity. clearbody SP.
  assert (ESPA : bv_unsigned x2 = SP - 192 - PQ).
  { rewrite E_sp.
    change (bv_unsigned (alu64 ALU_SUB (mul_div M_MUL (Z_to_bv 64 16) (ev E1 1)) (alu64 ALU_ADD (Z_to_bv 64 192) (ev E1 21))) = SP - 192 - PQ).
    rewrite u_sub64, u_add64, u_lit64a, USP. fold PQ.
    rewrite (Z.mod_small 192 (2^64)) by lia. rewrite (Z.mod_small (192 + PQ) (2^64)) by lia. rewrite Z.mod_small by lia. lia. }
  set (lo := SP - 4848).
  assert (STK1 : stk SG M1 lo (bv_unsigned x2)).
  { pose proof (SLB.kn_stk SG E1 M1 _ _ _ KWS KUS) as H. cbn [edenot vSPe] in H. rewrite USP, u_lit64a in H.
    rewrite (Z.mod_small 4848 (2^64)) in H by lia.
    destruct (stk_split SG M1 (SP + -4848) (bv_unsigned x2) (SP + -4848 + 4848) H ltac:(lia)) as [H1 _].
    replace lo with (SP + -4848) by (unfold lo; lia). exact H1. }
  assert (ETP : x4 = Z_to_bv 64 ATP).
  { rewrite E_tp. cbn [edenot]. apply bv_eq. rewrite u_lit64a. unfold ATP. rewrite (Z.mod_small 0x642e70 (2^64)) by lia. lia. }
  pose proof (HSM4 L RNGh x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
                F1 fc1 M1 st LB lo (proj1 HH1) (fun F1 n1 F2 n2 H1 _ => False_ind _ (NO4 F1 n1 H1)) (proj2 HH1) STK1
                ltac:(unfold lo; lia) ltac:(unfold lo, SM4_STACK; lia)
                ltac:(lia) ETP ltac:(replace lo with (SP - 4848) by reflexivity; exact HS3) HIMG HFS) as HSM.
  unfold ASTKMALLOC4 in HSM. rewrite <- HR in HSM.
  destruct HSM as (ms2 & Hms2 & (F & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & M2 & j0 & j1 & j2 & junk &
                   -> & MI2 & STK2 & PRES & AH2 & HFm & HFb & HFt & HFc & HFs & RF1 & RF2 & BSH & B5)).
  set (E1' := SLB.env_ext E1 36 [Z_to_bv 64 (F / 1024); Z_to_bv 64 (fflag L 4 F); Z_to_bv 64 (PQ / 16); t0; t1; t2; a1; a2; a3; a4; a5; a6; a7; t3; t4; t5; t6]).
  (* [comment removed for export] *)
  pose proof atop_range as AT.
  assert (HF0 : 0x665000 <= F /\ F + 1024 <= 0x7FFFFF800000).
  { destruct HFb as [[B1 B2]|[B1 B2]]; unfold AIMG_HI, KLS in *; lia. }
  assert (VLT : forall k, (k < 36)%nat -> ev E1' k = ev E1 k) by (intros k Hk; apply SLB.env_ext_lt; exact Hk).
  assert (V36 : ev E1' 36 = Z_to_bv 64 (F / 1024)) by reflexivity.
  assert (V37 : ev E1' 37 = Z_to_bv 64 (fflag L 4 F)) by reflexivity.
  assert (V38 : ev E1' 38 = Z_to_bv 64 (PQ / 16)) by reflexivity.
  assert (PQ16 : PQ = 16 * (PQ / 16)) by (clear - KAQ; Z.div_mod_to_equations; lia).
  assert (PB01 : 0 <= PQ / 16 <= 1) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  assert (U38 : bv_unsigned (ev E1' 38) = PQ / 16) by (rewrite V38; apply u_small; lia).
  assert (UF : bv_unsigned (mul_div M_MUL (Z_to_bv 64 1024) (ev E1' 36)) = F).
  { rewrite V36, u_mul64, !u_lit64a. rewrite (Z.mod_small 1024 (2^64)) by lia.
    rewrite (Z.mod_small (F / 1024) (2^64)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite Z.mod_small; [|split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|]].
    - clear - HFm. Z.div_mod_to_equations. lia.
    - assert (1024 * (F / 1024) <= F) by (apply Z.mul_div_le; lia). lia. }
  assert (USF : bv_unsigned (mul_div M_MUL (Z_to_bv 64 128) (ev E1' 36)) = F / 8).
  { rewrite V36, u_mul64, !u_lit64a. rewrite (Z.mod_small 128 (2^64)) by lia.
    rewrite (Z.mod_small (F / 1024) (2^64)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (E8 : F / 8 = 128 * (F / 1024)) by (clear - HFm; Z.div_mod_to_equations; lia).
    rewrite <- E8. apply Z.mod_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (U36 : bv_unsigned (ev E1' 36) = F / 1024).
  { rewrite V36. apply u_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  (* [comment removed for export] *)
  assert (KF8 : kentry_ok SG E1 M1 (KRange (EVar 16) 0xcca00 0xfffffefffff)) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  assert (KFO : kentry_ok SG E1 M1 (KRange (EVar 17) 0 7)) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  assert (KN : kentry_ok SG E1 M1 (KRange (EVar 18) 1 1048576)) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  assert (KFG : kentry_ok SG E1 M1 (KRange (EVar 19) 1 0x200000)) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  assert (KV8 : kentry_ok SG E1 M1 (KRange (EVar 20) 0xfffc0000000 0xffffffffffe)) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  assert (KFN : kentry_ok SG E1 M1 (KRange (EAlu ALU_ADD eF (EVar 18)) 0x665000 0x7fffff800000))
    by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  assert (KFGR : kentry_ok SG E1 M1 (KRange (EAlu ALU_SUB (EMd M_MUL (ELit 8) (EVar 19)) (EAlu ALU_ADD (EVar 17) (EVar 18))) 48 55))
    by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  assert (KVS : kentry_ok SG E1 M1 (KRange (EAlu ALU_SUB eV vSPe) 8 8)) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  assert (KINB : kentry_ok SG E1 M1 (KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA eF 0) (EVar 18)))
    by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  cbn [kentry_ok edenot] in KF8, KFO, KN, KFG, KV8.
  set (F8 := bv_unsigned (ev E1 16)) in *. set (FO := bv_unsigned (ev E1 17)) in *. set (N := bv_unsigned (ev E1 18)) in *.
  set (FG := bv_unsigned (ev E1 19)) in *. set (V8 := bv_unsigned (ev E1 20)) in *.
  set (FIN := 8 * F8 + FO) in *. set (V := 8 * V8) in *.
  assert (EFIN : FIN = 8 * F8 + FO) by reflexivity. assert (EV : V = 8 * V8) by reflexivity. clearbody FIN V.
  assert (UIN1 : bv_unsigned (edenot E1 eF) = FIN).
  { cbn [edenot eF]. rewrite u_add64, u_mul64, u_lit64a. fold F8. fold FO. rewrite (Z.mod_small 8 (2^64)) by lia.
    rewrite (Z.mod_small (8 * F8) (2^64)) by lia. rewrite EFIN. apply Z.mod_small. lia. }
  cbn [kentry_ok edenot eF] in KFN.
  assert (KFN' : 0x665000 <= FIN + N <= 0x7fffff800000).
  { revert KFN. rewrite u_add64, u_add64, u_mul64, u_lit64a. fold F8 FO N.
    rewrite (Z.mod_small 8 (2^64)) by lia. rewrite (Z.mod_small (8 * F8) (2^64)) by lia. rewrite (Z.mod_small (8 * F8 + FO) (2^64)) by lia.
    rewrite Z.mod_small by lia. rewrite EFIN. lia. }
  clear KFN.
  assert (KFGR' : 48 <= 8 * FG - (FO + N) <= 55).
  { cbn [kentry_ok edenot] in KFGR. revert KFGR. rewrite u_sub64, u_mul64, u_add64, u_lit64a. fold FG FO N.
    rewrite (Z.mod_small 8 (2^64)) by lia. rewrite (Z.mod_small (8 * FG) (2^64)) by lia. rewrite (Z.mod_small (FO + N) (2^64)) by lia.
    intros H. clear - H KFG KFO KN. lia. }
  clear KFGR.
  assert (KVS' : V = SP + 8).
  { cbn [kentry_ok edenot eV vSPe] in KVS. revert KVS.
    rewrite u_sub64, !u_mul64, !u_lit64a. fold V8 SP16. rewrite (Z.mod_small 8 (2^64)), (Z.mod_small 16 (2^64)) by lia.
    rewrite (Z.mod_small (8 * V8) (2^64)), (Z.mod_small (16 * SP16) (2^64)) by lia.
    intros H. rewrite EV, ESP. clear - H KV8 KSP. lia. }
  clear KVS.
  assert (KINB' : FIN + N <= 0x7fff7000 \/ 0x7fff7000 + 0x100000001000 <= FIN).
  { cbn [kentry_ok] in KINB. unfold estart, elenZ in KINB. cbn [a_base a_off edenot] in KINB.
    rewrite UIN1, !u_lit64a in KINB. fold N in KINB.
    rewrite (Z.mod_small 0 (2^64)), (Z.mod_small 0x100000001000 (2^64)) in KINB by lia. lia. }
  clear KINB.
  (* [comment removed for export] *)
  assert (CRIN : forall z, FIN <= z < FIN + N -> AHM.hmA AI LB z).
  { intros z Hz. apply (HCR (SLOWAS_defs.vF, 0, SLOWAS_defs.vN) ltac:(vm_compute; left; reflexivity) z).
    assert (WE : SP.win_den E (SLOWAS_defs.vF, 0, SLOWAS_defs.vN) = (FIN + 0, FIN + 0 + N)).
    { cbn [SP.win_den]. rewrite (SP.edenot_gagree 21 E E1 SLOWAS_defs.vF Hg1 (eq_sym Hb1) eq_refl).
      rewrite (SP.edenot_gagree 21 E E1 SLOWAS_defs.vN Hg1 (eq_sym Hb1) eq_refl).
      change (edenot E1 SLOWAS_defs.vF) with (edenot E1 eF). rewrite UIN1. reflexivity. }
    rewrite WE. cbn [fst snd]. lia. }
  assert (CRSH : forall z, F8 + 2147450880 <= z < F8 + 2147450880 + FG -> AHM.hmA AI LB z).
  { intros z Hz. apply (HCR (SLOWAS_defs.vF8, 2147450880, SLOWAS_defs.vFG) ltac:(vm_compute; right; left; reflexivity) z).
    assert (WE : SP.win_den E (SLOWAS_defs.vF8, 2147450880, SLOWAS_defs.vFG) = (F8 + 2147450880, F8 + 2147450880 + FG)).
    { cbn [SP.win_den SLOWAS_defs.vF8 SLOWAS_defs.vFG SLOWAS_defs.V edenot]. rewrite (Hg1 16%nat ltac:(lia)), (Hg1 19%nat ltac:(lia)).
      reflexivity. }
    rewrite WE. cbn [fst snd]. lia. }
  (* [comment removed for export] *)
  assert (USP1 : bv_unsigned (mul_div M_MUL (Z_to_bv 64 16) (ev E1' 1)) = SP) by (rewrite (VLT 1%nat) by lia; exact USP).
  assert (U21 : bv_unsigned (ev E1' 21) = PQ) by (rewrite (VLT 21%nat) by lia; reflexivity).
  assert (USPA : bv_unsigned (alu64 ALU_SUB (mul_div M_MUL (Z_to_bv 64 16) (ev E1' 1))
                                (alu64 ALU_ADD (Z_to_bv 64 192) (mul_div M_MUL (Z_to_bv 64 16) (ev E1' 38)))) = SP - 192 - PQ).
  { rewrite u_sub64, u_add64, USP1, u_mul64, !u_lit64a, U38. rewrite (Z.mod_small 192 (2^64)), (Z.mod_small 16 (2^64)) by lia.
    rewrite (Z.mod_small (16 * (PQ / 16)) (2^64)) by lia. rewrite <- PQ16.
    rewrite (Z.mod_small (192 + PQ) (2^64)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (UIN : bv_unsigned (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 8) (ev E1' 16)) (ev E1' 17)) = FIN).
  { rewrite (VLT 16%nat), (VLT 17%nat) by lia. exact UIN1. }
  assert (UN : bv_unsigned (ev E1' 18) = N) by (rewrite (VLT 18%nat) by lia; reflexivity).
  assert (UF8 : bv_unsigned (ev E1' 16) = F8) by (rewrite (VLT 16%nat) by lia; reflexivity).
  assert (UFG : bv_unsigned (ev E1' 19) = FG) by (rewrite (VLT 19%nat) by lia; reflexivity).
  assert (UV8 : bv_unsigned (ev E1' 20) = V8) by (rewrite (VLT 20%nat) by lia; reflexivity).
  assert (UV : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (ev E1' 20)) = V).
  { rewrite u_mul64, u_lit64a, UV8. rewrite (Z.mod_small 8 (2^64)) by lia. rewrite EV. apply Z.mod_small. lia. }
  assert (USS : bv_unsigned (mul_div M_MUL (Z_to_bv 64 2) (ev E1' 1)) = 2 * SP16).
  { rewrite (VLT 1%nat) by lia. rewrite u_mul64, u_lit64a. fold SP16. rewrite (Z.mod_small 2 (2^64)) by lia. apply Z.mod_small. lia. }
  assert (UF2 : bv_unsigned (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 1024) (ev E1' 36)) (Z_to_bv 64 1024)) = F + 1024).
  { rewrite u_add64, UF, u_lit64a. rewrite (Z.mod_small 1024 (2^64)) by lia. apply Z.mod_small. lia. }
  assert (ESH : shad F = F / 8 + 2147450880).
  { unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. }
  assert (F8' : F / 8 < 2^44 /\ 0 <= F / 8) by (split; [apply Z.div_lt_upper_bound | apply Z.div_pos]; lia).
  assert (EF8 : F / 8 * 8 = F) by (clear - HFm; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  assert (FRO : forall z, AHM.hmA AI LB z -> ~ (F <= z < F + 1024) /\ ~ (shad F <= z < shad F + 1024 / 8)).
  { intros z Hz. apply (AGLF.fresh_out AI L RNGh st LB M2 4 F 1024 (bv_unsigned x2) ATOP z AH2 B5
                          ltac:(clear - HFm; Z.div_mod_to_equations; lia) eq_refl ltac:(lia) HFb HFt (Z.le_refl _)).
    right; right; exact Hz. }
  change (1024 / 8) with 128 in FRO.
  (* [comment removed for export] *)
  assert (STKS1 : stk SG M1 (bv_unsigned x2) SP).
  { pose proof (SLB.kn_stk SG E1 M1 _ _ _ KWS KUS) as H. cbn [edenot vSPe] in H. rewrite USP, u_lit64a in H.
    rewrite (Z.mod_small 4848 (2^64)) in H by lia.
    destruct (stk_split SG M1 (SP + -4848) (bv_unsigned x2) (SP + -4848 + 4848) H ltac:(lia)) as [_ H2].
    replace (SP + -4848 + 4848) with SP in H2 by lia. exact H2. }
  assert (KEEP : forall a, bv_unsigned x2 <= a < SP -> M2 (wa a) = M1 (wa a) /\ (wview SG M1 (wa a) <> None -> wview SG M2 (wa a) <> None)).
  { intros a Ha. apply (PRES a ltac:(lia)). left. lia. }
  pose proof (AGX.stk_join SG M1 M2 lo (bv_unsigned x2) SP STK2 STKS1 KEEP) as STKM2.
  assert (RO2 : forall x, lo <= x < SP -> seg_rom SG (Z_to_bv 64 x) = None).
  { intros x Hx. apply ref_seg_rom_none. rewrite u_small by (unfold lo; lia). unfold lo; lia. }
  assert (KP1 : know_ok SG E1' M2 knP1).
  { unfold knP1. repeat apply Forall_cons.
    (* [comment removed for export] *)
    - apply AGX.kx_range. cbn [edenot]. rewrite U36. split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia.
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
      + cbn [cbytes edenot]. rewrite V37. reflexivity.
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
      rewrite (Z.mod_small 4848 (2^64)), (Z.mod_small 1024 (2^64)) by lia. lia.
    (* [comment removed for export] *)
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UF, UIN, UN, !u_lit64a.
      rewrite (Z.mod_small 1024 (2^64)) by lia. rewrite !Z.add_0_r.
      apply (disj_pw F 1024 FIN N ltac:(lia) ltac:(lia)). intros z Hz. exact (proj1 (FRO z (CRIN z Hz))).
    (* [comment removed for export] *)
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UF, UV, !u_lit64a.
      rewrite (Z.mod_small 1024 (2^64)), (Z.mod_small 8 (2^64)) by lia. lia.
    (* [comment removed for export] *)
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, UF8, UFG, !u_lit64a.
      rewrite (Z.mod_small 128 (2^64)) by lia. rewrite <- ESH.
      apply (disj_pw (shad F) 128 (F8 + 2147450880) FG ltac:(lia) ltac:(lia)). intros z Hz. exact (proj2 (FRO z (CRSH z Hz))).
    (* [comment removed for export] *)
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, USP1, !u_lit64a.
      rewrite (Z.mod_small 4848 (2^64)), (Z.mod_small 128 (2^64)) by lia. lia.
    (* [comment removed for export] *)
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UF, USF, !u_lit64a.
      rewrite (Z.mod_small 1024 (2^64)), (Z.mod_small 128 (2^64)) by lia.
      destruct HFb as [[B1 B2]|[B1 B2]]; unfold AIMG_HI, KLS in *; [left | right]; clear - B1 B2 HF0; Z.div_mod_to_equations; lia.
    (* [comment removed for export] *)
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, UV8, !u_lit64a.
      rewrite (Z.mod_small 128 (2^64)), (Z.mod_small 1 (2^64)) by lia. left. clear - KVS' EV ESP HFt AT EF8 HS1. lia.
    (* [comment removed for export] *)
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, USS, !u_lit64a.
      rewrite (Z.mod_small 128 (2^64)), (Z.mod_small 606 (2^64)) by lia. left. clear - ESP HFt AT EF8 HS1. lia.
    (* [comment removed for export] *)
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UF, UF8, UFG, !u_lit64a.
      rewrite (Z.mod_small 1024 (2^64)) by lia.
      destruct HFb as [[B1 B2]|[B1 B2]]; unfold AIMG_HI, KLS in *; [left | right]; lia.
    (* [comment removed for export] *)
    - apply AGX.kx_zero.
      + unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, u_lit64a. rewrite (Z.mod_small 128 (2^64)) by lia. lia.
      + unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite USF, u_lit64a. rewrite (Z.mod_small 128 (2^64)) by lia.
        intros i Hi. rewrite <- ESH. exact (AGLR.zero_cellsN M2 (shad F) 16 HFs ltac:(lia) ltac:(cbn; lia) i ltac:(cbn; lia)).
    (* [comment removed for export] *)
    - apply AGX.kx_range. cbn [edenot]. rewrite U38. lia.
    (* [comment removed for export] *)
    - apply (AGX.kx_stk_wr SG E1' M2 _ _ lo SP STKM2); unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?USP1, ?u_lit64a;
        rewrite ?(Z.mod_small 4848 (2^64)) by lia; unfold lo; lia.
    - apply (AGX.kx_stk_unk SG E1' M2 _ _ lo SP STKM2 RO2); unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?USP1, ?u_lit64a;
        rewrite ?(Z.mod_small 4848 (2^64)) by lia; unfold lo; lia.
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
  assert (EPB : mul_div M_MUL (Z_to_bv 64 16) (ev E1' 38) = ev E1 21).
  { apply bv_eq. rewrite u_mul64, u_lit64a, U38. rewrite (Z.mod_small 16 (2^64)) by lia. rewrite Z.mod_small by lia. fold PQ. lia. }
  assert (ER2 : regs_ok E1' postregs1 (mkR x1 x2 x3 x4 t0 t1 t2 x8 x9 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7
                                         x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)).
  { apply AGC.regs_ok_tl; [reflexivity|]. unfold postregs1, SPAb, vSPe. cbn [tl map edenot].
    change (ev E1' 39) with t0. change (ev E1' 40) with t1. change (ev E1' 41) with t2.
    change (ev E1' 42) with a1. change (ev E1' 43) with a2. change (ev E1' 44) with a3. change (ev E1' 45) with a4.
    change (ev E1' 46) with a5. change (ev E1' 47) with a6. change (ev E1' 48) with a7.
    change (ev E1' 49) with t3. change (ev E1' 50) with t4. change (ev E1' 51) with t5. change (ev E1' 52) with t6.
    rewrite E_ra, E_sp, E_gp, E_tp, E_s0, E_s1, E_s2, E_s3, E_s4, E_s5, E_s6, E_s7, E_s8, E_s9, E_s10, E_s11.
    cbn [edenot SLOWAE_defs.vF SLOWAE_defs.vN SLOWAE_defs.vV SLOWAE_defs.vSP SLOWAE_defs.add SLOWAE_defs.sub SLOWAE_defs.mul SLOWAE_defs.V
         SLOWAE_defs.vF8 SLOWAE_defs.vFO SLOWAE_defs.vV8 SLOWAE_defs.vSP16 SLOWAE_defs.vGP SLOWAE_defs.vTP SLOWAE_defs.vS4 SLOWAE_defs.vS5
         SLOWAE_defs.vS11].
    rewrite EPB.
    rewrite ?(VLT 1%nat), ?(VLT 2%nat), ?(VLT 3%nat), ?(VLT 8%nat), ?(VLT 9%nat), ?(VLT 15%nat), ?(VLT 16%nat), ?(VLT 17%nat),
      ?(VLT 18%nat), ?(VLT 20%nat) by lia.
    assert (EA0 : mul_div M_MUL (Z_to_bv 64 1024) (ev E1' 36) = Z_to_bv 64 F).
    { apply bv_eq. rewrite UF. rewrite u_small by lia. reflexivity. }
    rewrite EA0. reflexivity. }
  (* [comment removed for export] *)
  assert (TABIN : forall lo' hi', In (lo', hi') IMG_TABS -> In (lo', hi') CI).
  { intros lo' hi' H. apply IMG_CI. unfold client_ranges. apply in_or_app. right. exact H. }
  assert (RK1 : AGL.rt_keep SG E1' PR1 PR1 M1 M2).
  { apply (AGLR.rt_keep_cls AI LB (bv_unsigned x2) lo M1 M2 E1' PR1 (conj PRES BSH)
             (AGLR.shw_of_aheap AI L RNGh st LB _ M2 AH2 (fun b H => or_intror H)) ltac:(unfold lo; lia) ltac:(lia)).
    unfold PR1. cbn [app SP.p_CR SLOWAS_defs.SLOWAS SP.PGH]. unfold NLM.TABS, FMINW.
    cbv [SLOWAS_defs.vF SLOWAS_defs.vN SLOWAS_defs.vF8 SLOWAS_defs.vFO SLOWAS_defs.vFG SLOWAS_defs.add SLOWAS_defs.mul SLOWAS_defs.V].
    repeat apply Forall_cons.
    - intros x Hin Hx. left. pose proof (AGLR.in_stack_win E1' SPAx x) as H. unfold SPAx, vSPe in H. cbn [edenot] in H.
      assert (USPAx : bv_unsigned (alu64 ALU_SUB (mul_div M_MUL (Z_to_bv 64 16) (ev E1' 1)) (alu64 ALU_ADD (Z_to_bv 64 192) (ev E1' 21)))
                      = SP - 192 - PQ).
      { rewrite u_sub64, u_add64, u_lit64a, USP1, U21. rewrite (Z.mod_small 192 (2^64)) by lia.
        rewrite (Z.mod_small (192 + PQ) (2^64)) by lia. rewrite Z.mod_small by lia. lia. }
      rewrite USPAx in H. specialize (H ltac:(lia) Hin). lia.
    - intros x Hin Hx. right; left. pose proof (SP.shwin_sh_above E1' (EAlu ALU_SUB vSPe (ELit 4848)) x) as H.
      unfold vSPe in H. cbn [edenot] in H. rewrite u_sub64, USP1, u_lit64a in H. rewrite (Z.mod_small 4848 (2^64)) in H by lia.
      rewrite (Z.mod_small (SP - 4848) (2^64)) in H by lia.
      destruct (H ltac:(lia) Hin) as (a & Ha & ->). exists a. split; [unfold lo; lia|]. unfold SP.sh_of, shad, ASHOFF. reflexivity.
    - intros x Hin Hx. right; right; left. apply CRIN.
      unfold SC.in_win, SG.win_den in Hin. cbn [edenot] in Hin. rewrite UIN, UN in Hin. lia.
    - intros x Hin Hx. right; right; left. apply CRSH.
      unfold SC.in_win, SG.win_den in Hin. cbn [edenot] in Hin. rewrite UF8, UFG in Hin. lia.
    - intros x Hin Hx. right; right; right; left. unfold SC.in_win, SG.win_den in Hin. cbn [edenot] in Hin.
      rewrite !u_lit64a in Hin. rewrite (Z.mod_small 0 (2^64)), (Z.mod_small 4 (2^64)) in Hin by lia.
      exists (0x10b978, 0x10b97c). split; [apply IMG_CI; vm_compute; tauto | cbn [fst snd]; lia].
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
  assert (HKX1 : know_ok SG E1' M1 (ST.t_know SLOWAE_defs.XSM)).
  { apply (AxSymRun3.know_ok_agree SG 36 E1 E1' M1 _); [| vm_compute; reflexivity | exact HK1].
    split; [intros k Hk; symmetry; apply VLT; exact Hk | reflexivity]. }
  assert (HRP : ret_pc x1 = Z_to_bv 64 (ST.t_pc SLOWAB_defs.T0)) by (apply bv_eq; rewrite E_ra; vm_compute; reflexivity).
  lazymatch type of Hms2 with ExecF.mstepsF _ _ _ ?m => set (ms2 := m) in * end.
  pose proof (AGL.bridge_tm SG E1' M1 M2 _ PR1 PR1 knP1 postregs1 sg1 SLOWAB_defs.T0 _ F1 fc1 rom ms2 HKX1 RK1 KP1 ER2 sl_b1_regs sl_b1_kn
                ltac:(unfold ms2; rewrite HRP, HR; reflexivity) HZ1 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) as HT2.
  (* [comment removed for export] *)
  set (E2 := ST.senv E1' sg1) in *.
  assert (VE2 : forall k, (k < 21)%nat -> ev E2 k = ev E1 k).
  { intros k Hk. unfold E2. rewrite SP.senv_nth. unfold sg1. rewrite app_nth1 by (rewrite length_map, length_seq; lia).
    rewrite (nth_indep _ (ELit 0) (EVar 0)) by (rewrite length_map, length_seq; lia). rewrite map_nth, seq_nth by lia.
    cbn [edenot]. apply VLT. lia. }
  assert (VE21 : ev E2 21 = Z_to_bv 64 (F / 1024)) by (unfold E2; rewrite SP.senv_nth; reflexivity).
  assert (VE22 : ev E2 22 = Z_to_bv 64 (fflag L 4 F)) by (unfold E2; rewrite SP.senv_nth; exact V37).
  assert (VE23 : ev E2 23 = Z_to_bv 64 (PQ / 16)) by (unfold E2; rewrite SP.senv_nth; exact V38).
  pose proof HT2 as (_ & _ & (R2' & _ & _ & _ & HK2)). cbn [ST.tstate s_know mem_denot] in HK2.
  assert (GE2 : SP.gagree 21 E E2) by (intros k Hk; rewrite VE2 by exact Hk; apply Hg1; exact Hk).
  assert (BE2 : eb E = eb E2) by (unfold E2, E1', ST.senv, SLB.env_ext; cbn; symmetry; exact Hb1).
  assert (HA2 : SX.aw_genuine E2 (SP.p_A SLOWAB_defs.SLOWAB)).
  { cbn [SP.p_A SLOWAB_defs.SLOWAB SP.PGCA]. apply (AGC.aw_gen_mix SG E E2 M2 _ _ _ 21 HK2 HA GE2 BE2). vm_compute. reflexivity. }
  assert (UF2' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 1024) (ev E2 21)) = F) by (rewrite VE21, <- V36; exact UF).
  assert (USF2 : bv_unsigned (mul_div M_MUL (Z_to_bv 64 128) (ev E2 21)) = F / 8) by (rewrite VE21, <- V36; exact USF).
  assert (HW2 : SP.wins_client (hmC (FB4 F :: LB)) E2 (SP.p_W SLOWAB_defs.SLOWAB)).
  { cbn [SP.p_W SLOWAB_defs.SLOWAB SP.PGCA]. unfold SP.wins_client in HW |- *. cbn [SP.p_W SLOWAS_defs.SLOWAS SP.PGH] in HW.
    pose proof (Forall_inv HW) as HW1. pose proof (Forall_inv (Forall_inv_tail HW)) as HW2'. cbv beta in HW1, HW2'.
    repeat apply Forall_cons.
    - match goal with |- context [SP.win_den E2 ?w] => rewrite <- (SP.win_den_gagree 21 E E2 w GE2 BE2 eq_refl) end. unfold AHM.hmC in *.
      apply (AGLR.acr_mono AI LB); [exact HW1 | intros b Hb; right; exact Hb].
    - match goal with |- context [SP.win_den E2 ?w] => rewrite <- (SP.win_den_gagree 21 E E2 w GE2 BE2 eq_refl) end. unfold AHM.hmC in *.
      apply (AGLR.acr_mono AI LB); [exact HW2' | intros b Hb; right; exact Hb].
    - unfold AHM.hmC. cbv [SLOWAB_defs.vFK SLOWAB_defs.mul SLOWAB_defs.vF10 SLOWAB_defs.V]. cbn [SP.win_den edenot fst snd]. rewrite UF2', u_lit64a.
      rewrite (Z.mod_small 1024 (2^64)) by lia. apply (AGLR.acr_fake AI _ _ 4 F 1024); [left; reflexivity | lia | lia].
    - unfold AHM.hmC. cbv [SLOWAB_defs.mul SLOWAB_defs.vF10 SLOWAB_defs.V]. cbn [SP.win_den edenot fst snd]. rewrite USF2, u_lit64a.
      rewrite (Z.mod_small 128 (2^64)) by lia. apply (AGLR.acr_fake_shadow AI _ _ 4 F 1024); [left; reflexivity | |];
        unfold ASHOFF; clear - HFm; Z.div_mod_to_equations; lia.
    - constructor. }
  exists ms2, E2, M2, F.
  split; [exact Hms2|]. split; [exact HT2|]. split; [exact GE2|]. split; [exact BE2|]. split; [exact AH2|]. split; [exact MI2|].
  split; [exact HFm|]. split; [exact HFb|]. split; [exact HFt|]. split; [exact RF1|]. split; [exact RF2|]. split; [exact B5|].
  split; [exact (conj PRES BSH)|]. split; [exact VE21|]. split; [exact VE22|].
  split; [rewrite VE23, u_small by lia; fold PQ; lia|].
  split; [exact ESPA|]. split; [fold PQ; lia|]. split; [exact HA2 | exact HW2].
Qed.

(* [comment removed for export] *)
Definition sxs : sentry := {| e_addr := SA (EMd M_MUL (ELit 128) (EVar 21)) 2147450880; e_width := 128%nat; e_val := ELit 0 |}.
Definition vSPAx : expr := EAlu ALU_SUB (EMd M_MUL (ELit 16) (EVar 1)) (EAlu ALU_ADD (ELit 192) (EMd M_MUL (ELit 16) (EVar 23))).
Definition SHFEx : expr := EAlu ALU_ADD (EMd M_MUL (ELit 128) (EVar 21)) (ELit 2147450880).
Definition vFKx : expr := EMd M_MUL (ELit 1024) (EVar 21).
Definition sg2 : list expr := map EVar (seq 0 23) ++ [EVar 25; EVar 24] ++
  [ELit 0xc2b8c; vSPAx; EVar 44; EVar 45; EVar 46; vSPAx; SHFEx] ++ map EVar (seq 47 7) ++
  [vFKx; SHFEx; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39] ++ map EVar (seq 54 4).
Definition postregs2 : list expr :=
  [ELit 0; ELit 0xc2b8c; vSPAx; EVar 2; EVar 3; EVar 44; EVar 45; EVar 46; EMd M_MUL (ELit 16) (EVar 1); vSPAx;
   SHFEx] ++ map EVar (seq 47 7) ++ [vFKx; vFKx; SHFEx; EVar 24; EVar 25; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39] ++ map EVar (seq 54 4).
Definition knP2 : list kentry := Eval vm_compute in
  let surv := List.filter (AGM.survM (ST.t_know SLOWABE_defs.XSS) sxs) (ST.t_know SLOWABE_defs.XSS) in
  List.filter (fun K => negb (ST.kimplied SG surv K)) (map (ST.ksub sg2) (ST.t_know SLOWAF_defs.T0)).
Lemma sl_b2_regs : ST.regs_match (List.filter (AGM.survM (ST.t_know SLOWABE_defs.XSS) sxs) (ST.t_know SLOWABE_defs.XSS) ++ knP2)
  postregs2 (map (ST.esub sg2) (ST.t_regs SLOWAF_defs.T0)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sl_b2_kn : AGM.bridge_okM SG (ST.t_know SLOWABE_defs.XSS) sxs knP2 sg2 (ST.t_know SLOWAF_defs.T0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sl_setsh : forall E rom ms3 E1 E3 M3 F,
  AHM.hmR rom -> SP.crs_law (hmA LB) E (SP.p_CR SLOWAS_defs.SLOWAS) -> SP.gagree 21 E E1 ->
  AHM.hmS L RNGh (16 * bv_unsigned (ev E1 1)) 4848 ->
  ST.tm_okF SG SLOWABE_defs.XSS E3 M3 rom ms3 -> hmH (FB4 F :: LB) M3 ->
  (forall k, (k < 21)%nat -> ev E3 k = ev E1 k) -> ev E3 21 = Z_to_bv 64 (F / 1024) -> ev E3 22 = Z_to_bv 64 (fflag L 4 F) ->
  F mod 1024 = 0 -> ablk F (F + 1024) -> rng RNGh (shad F) 128 ->
  exists ms4 E4 M4, ExecF.mstepsF SG RNGh ms3 ms4 /\ ST.tm_okF SG SLOWAF_defs.T0 E4 M4 rom ms4
    /\ (forall k, (k < 23)%nat -> ev E4 k = ev E3 k) /\ eb E4 = eb E3
    /\ AHEAP AI L RNGh st (FB4 F :: LB) M4 /\ mem_inv SG M4 /\ munch [(shad F, shad F + 128)] M3 M4 /\ wmono SG M3 M4.
Proof.
  intros E rom ms3 E1 E3 M3 F HR HCR Hg1 HS0 HT3 HH3 VE31 V3_21 V3_22 HFm HFb HRS.
  destruct HS0 as (HS1 & HS2 & HS3).
  set (SP16 := bv_unsigned (ev E1 1)) in *.
  set (SP := 16 * SP16) in *. assert (ESP : SP = 16 * SP16) by reflexivity. clearbody SP.
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
  cbn [rkeys map SLOWABE_defs.XSS ST.t_regs SLOWABE_defs.XSS_regs] in ER3. vm_compute sr_get in ER3.
  injection ER3 as Y_ra Y_sp Y_gp Y_tp Y_t0 Y_t1 Y_t2 Y_s0 Y_s1 Y_a0 Y_a1 Y_a2 Y_a3 Y_a4 Y_a5 Y_a6 Y_a7 Y_s2 Y_s3 Y_s4 Y_s5 Y_s6 Y_s7
                   Y_s8 Y_s9 Y_s10 Y_s11 Y_t3 Y_t4 Y_t5 Y_t6.
  assert (U3_1 : bv_unsigned (ev E3 1) = SP16) by (rewrite (VE31 1%nat) by lia; reflexivity).
  assert (KSP : kentry_ok SG E3 M3 (KRange (EVar 1) 8795556151599 0x80000000000)) by (apply (ST.kin_ok SG E3 M3 _ _ HK3); vm_compute; reflexivity).
  cbn [kentry_ok edenot] in KSP. rewrite U3_1 in KSP.
  assert (U3_21 : bv_unsigned (ev E3 21) = F / 1024).
  { rewrite V3_21. apply u_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (USH3 : bv_unsigned (mul_div M_MUL (Z_to_bv 64 128) (ev E3 21)) = F / 8).
  { rewrite u_mul64, u_lit64a, U3_21. rewrite (Z.mod_small 128 (2^64)) by lia.
    assert (E8 : F / 8 = 128 * (F / 1024)) by (clear - HFm; Z.div_mod_to_equations; lia).
    rewrite <- E8. apply Z.mod_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (ESH : shad F = F / 8 + 2147450880).
  { unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. }
  assert (HF8b : F / 8 < 2^44 /\ 0 <= F / 8) by (split; [apply Z.div_lt_upper_bound | apply Z.div_pos]; lia).
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
  set (E3' := SLB.env_ext E3 44 [u0; u1; u2; b1; b2; b3; b4; b5; b6; b7; u3; u4; u5; u6]).
  assert (VLT3 : forall k, (k < 44)%nat -> ev E3' k = ev E3 k) by (intros k Hk; apply SLB.env_ext_lt; exact Hk).
  assert (ER4 : regs_ok E3' postregs2 (mkR y1 y2 y3 y4 u0 u1 u2 y8 y9 y10 b1 b2 b3 b4 b5 b6 b7
                                          y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 u3 u4 u5 u6)).
  { apply AGC.regs_ok_tl; [reflexivity|]. unfold postregs2, vSPAx, SHFEx, vFKx. cbn [tl map app seq edenot].
    change (ev E3' 44) with u0. change (ev E3' 45) with u1. change (ev E3' 46) with u2.
    change (ev E3' 47) with b1. change (ev E3' 48) with b2. change (ev E3' 49) with b3. change (ev E3' 50) with b4.
    change (ev E3' 51) with b5. change (ev E3' 52) with b6. change (ev E3' 53) with b7.
    change (ev E3' 54) with u3. change (ev E3' 55) with u4. change (ev E3' 56) with u5. change (ev E3' 57) with u6.
    rewrite Y_ra, Y_sp, Y_gp, Y_tp, Y_s0, Y_s1, Y_a0, Y_s2, Y_s3, Y_s4, Y_s5, Y_s6, Y_s7, Y_s8, Y_s9, Y_s10, Y_s11.
    cbn [edenot]. rewrite ?(VLT3 1%nat), ?(VLT3 2%nat), ?(VLT3 3%nat), ?(VLT3 21%nat), ?(VLT3 23%nat), ?(VLT3 24%nat), ?(VLT3 25%nat),
      ?(VLT3 35%nat), ?(VLT3 36%nat), ?(VLT3 37%nat), ?(VLT3 38%nat), ?(VLT3 39%nat) by lia. reflexivity. }
  assert (MK : AGM.munch_keep SG (estart E3' (e_addr sxs)) (estart E3' (e_addr sxs) + elenZ E3' (elen (e_width sxs))) M3 M4).
  { assert (ES : estart E3' (e_addr sxs) = shad F).
    { unfold estart. cbn [sxs e_addr a_base a_off edenot]. rewrite (VLT3 21%nat) by lia. rewrite USH3. lia. }
    assert (EL : elenZ E3' (elen (e_width sxs)) = 128) by (unfold elenZ; cbn [sxs e_width elen edenot]; rewrite u_lit64a; reflexivity).
    rewrite ES, EL. split; [|exact WM]. intros x Hx. apply MU. cbn [outside]. split; [|exact I]. lia. }
  assert (HKX3 : know_ok SG E3' M3 (ST.t_know SLOWABE_defs.XSS)).
  { apply (AxSymRun3.know_ok_agree SG 44 E3 E3' M3 _); [| vm_compute; reflexivity | exact HK3].
    split; [intros k Hk; symmetry; apply VLT3; exact Hk | reflexivity]. }
  assert (KP2 : know_ok SG E3' M4 knP2).
  { destruct (HFF L RNGh st (FB4 F :: LB) M4 4 F 1024 AH4 (or_introl eq_refl)) as (RWC & RNGF & ABLKF & TOPF & OUTB & NCI).
    set (fl := fflag L 4 F) in *.
    assert (FLR : 0x665000 <= fl /\ fl + 1 <= 0x7FFFFF800000) by (destruct ABLKF as [[B1 B2]|[B1 B2]]; unfold AIMG_HI, KLS in *; lia).
    assert (UFL : bv_unsigned (ev E3' 22) = fl) by (rewrite (VLT3 22%nat) by lia; rewrite V3_22; apply u_small; lia).
    assert (USP3 : bv_unsigned (mul_div M_MUL (Z_to_bv 64 16) (ev E3' 1)) = SP).
    { rewrite (VLT3 1%nat) by lia. rewrite u_mul64, u_lit64a, U3_1. rewrite (Z.mod_small 16 (2^64)) by lia. rewrite ESP. apply Z.mod_small. lia. }
    (* [comment removed for export] *)
    assert (KF8 : kentry_ok SG E3 M3 (KRange (EVar 16) 0xcca00 0xfffffefffff)) by (apply (ST.kin_ok SG E3 M3 _ _ HK3); vm_compute; reflexivity).
    assert (KFO : kentry_ok SG E3 M3 (KRange (EVar 17) 0 7)) by (apply (ST.kin_ok SG E3 M3 _ _ HK3); vm_compute; reflexivity).
    assert (KN : kentry_ok SG E3 M3 (KRange (EVar 18) 1 1048576)) by (apply (ST.kin_ok SG E3 M3 _ _ HK3); vm_compute; reflexivity).
    assert (KV8 : kentry_ok SG E3 M3 (KRange (EVar 20) 0xfffc0000000 0xffffffffffe)) by (apply (ST.kin_ok SG E3 M3 _ _ HK3); vm_compute; reflexivity).
    assert (KVS : kentry_ok SG E3 M3 (KRange (EAlu ALU_SUB eV vSPe) 8 8)) by (apply (ST.kin_ok SG E3 M3 _ _ HK3); vm_compute; reflexivity).
    assert (KUV : kentry_ok SG E3 M3 (KUnk (SA eV 0) (ELit 8))) by (apply (ST.kin_ok SG E3 M3 _ _ HK3); vm_compute; reflexivity).
    cbn [kentry_ok edenot] in KF8, KFO, KN, KV8.
    rewrite (VE31 16%nat) in KF8 by lia. rewrite (VE31 17%nat) in KFO by lia. rewrite (VE31 18%nat) in KN by lia. rewrite (VE31 20%nat) in KV8 by lia.
    set (F8 := bv_unsigned (ev E1 16)) in *. set (FO := bv_unsigned (ev E1 17)) in *. set (N := bv_unsigned (ev E1 18)) in *.
    set (V8 := bv_unsigned (ev E1 20)) in *.
    assert (UV8 : bv_unsigned (ev E3 20) = V8) by (rewrite (VE31 20%nat) by lia; reflexivity).
    assert (KVS' : 8 * V8 = SP + 8).
    { cbn [kentry_ok edenot eV vSPe] in KVS. revert KVS.
      rewrite u_sub64, !u_mul64, !u_lit64a, UV8, U3_1. rewrite (Z.mod_small 8 (2^64)), (Z.mod_small 16 (2^64)) by lia.
      rewrite (Z.mod_small (8 * V8) (2^64)), (Z.mod_small (16 * SP16) (2^64)) by lia.
      intros H. rewrite ESP. clear - H KV8 KSP. lia. }
    assert (UIN : bv_unsigned (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 8) (ev E3' 16)) (ev E3' 17)) = 8 * F8 + FO).
    { rewrite (VLT3 16%nat), (VLT3 17%nat), (VE31 16%nat), (VE31 17%nat) by lia.
      rewrite u_add64, u_mul64, u_lit64a. fold F8 FO. rewrite (Z.mod_small 8 (2^64)) by lia.
      rewrite (Z.mod_small (8 * F8) (2^64)) by lia. apply Z.mod_small. lia. }
    assert (UN3 : bv_unsigned (ev E3' 18) = N) by (rewrite (VLT3 18%nat), (VE31 18%nat) by lia; reflexivity).
    assert (UV : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (ev E3' 20)) = 8 * V8).
    { rewrite (VLT3 20%nat) by lia. rewrite u_mul64, u_lit64a, UV8. rewrite (Z.mod_small 8 (2^64)) by lia. apply Z.mod_small. lia. }
    unfold knP2. repeat apply Forall_cons.
    - apply AGX.kx_range. cbn [edenot]. rewrite UFL. lia.
    - apply AGX.kx_wr.
      + unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite UFL, u_lit64a. rewrite (Z.mod_small 1 (2^64)) by lia. lia.
      + unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UFL, u_lit64a, Z.add_0_r. rewrite (Z.mod_small 1 (2^64)) by lia.
        exact (proj2 RWC).
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UFL, USP3, !u_lit64a.
      rewrite (Z.mod_small 4848 (2^64)), (Z.mod_small 1 (2^64)) by lia. lia.
    - apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UFL, !u_lit64a.
      rewrite (Z.mod_small 0 (2^64)), (Z.mod_small 0x100000001000 (2^64)), (Z.mod_small 1 (2^64)) by lia.
      destruct ABLKF as [[B1 B2]|[B1 B2]]; unfold AIMG_HI, KLS in *; lia.
    - (* [comment removed for export] *)
      apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UFL, UIN, UN3, !u_lit64a.
      rewrite (Z.mod_small 1 (2^64)) by lia. rewrite !Z.add_0_r.
      destruct (Z_lt_ge_dec fl (8 * F8 + FO)) as [Hlt|Hge]; [left; lia|].
      destruct (Z_lt_ge_dec fl (8 * F8 + FO + N)) as [Hlt2|Hge2]; [|right; lia]. exfalso.
      assert (HX : AHM.hmA AI LB fl).
      { apply (HCR (SLOWAS_defs.vF, 0, SLOWAS_defs.vN) ltac:(vm_compute; left; reflexivity)).
        cbn [SP.win_den SLOWAS_defs.vF SLOWAS_defs.vN SLOWAS_defs.add SLOWAS_defs.mul SLOWAS_defs.vF8 SLOWAS_defs.vFO SLOWAS_defs.V edenot fst snd].
        rewrite u_add64, u_mul64, !u_lit64a, (Hg1 16%nat ltac:(lia)), (Hg1 17%nat ltac:(lia)), (Hg1 18%nat ltac:(lia)). fold F8 FO N.
        rewrite (Z.mod_small 8 (2^64)) by lia. rewrite (Z.mod_small (8 * F8) (2^64)) by lia. rewrite (Z.mod_small (8 * F8 + FO) (2^64)) by lia. lia. }
      apply (AGLF.flag_out AI L RNGh st (FB4 F :: LB) M4 fl ATOP fl AH4 ABLKF TOPF OUTB NCI);
        [lia | right; right; exact (AGLF.hmA_cons AI (FB4 F) LB fl HX) | reflexivity].
    - (* [comment removed for export] *)
      apply AGX.kx_disj. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UFL, UV, !u_lit64a.
      rewrite (Z.mod_small 1 (2^64)), (Z.mod_small 8 (2^64)) by lia. left. lia.
    - (* [comment removed for export] *)
      apply AGX.kx_unk.
      + unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite UV, u_lit64a. rewrite (Z.mod_small 8 (2^64)) by lia. lia.
      + unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite UV, u_lit64a, Z.add_0_r. rewrite (Z.mod_small 8 (2^64)) by lia.
        intros i Hi. destruct KUV as [_ KU]. unfold estart, elenZ in KU. cbn [a_base a_off edenot eV] in KU.
        rewrite u_mul64, !u_lit64a, UV8, Z.add_0_r in KU. rewrite (Z.mod_small 8 (2^64)) in KU by lia.
        rewrite (Z.mod_small (8 * V8) (2^64)) in KU by lia. rewrite MU; [exact (KU i Hi)|].
        cbn [outside]. split; [|exact I]. rewrite u_small by lia. rewrite ESH. lia.
    - constructor. }
  assert (HRP2 : ret_pc y1 = Z_to_bv 64 (ST.t_pc SLOWAF_defs.T0)) by (apply bv_eq; rewrite Y_ra; vm_compute; reflexivity).
  lazymatch type of Hms4 with ExecF.mstepsF _ _ _ ?m => set (ms4 := m) in * end.
  pose proof (AGM.bridge_tmM SG E3' M3 M4 _ sxs knP2 postregs2 sg2 SLOWAF_defs.T0 _ (ms_fregs ms3) (ms_fcsr ms3) rom ms4 HKX3 MK KP2 ER4
                sl_b2_regs sl_b2_kn ltac:(unfold ms4; rewrite HRP2, HR; reflexivity) HZ3
                (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) as HT4.
  exists ms4, (ST.senv E3' sg2), M4.
  split; [exact Hms4|]. split; [exact HT4|].
  split.
  { intros k Hk. rewrite SP.senv_nth. unfold sg2. rewrite app_nth1 by (rewrite length_map, length_seq; lia).
    rewrite (nth_indep _ (ELit 0) (EVar 0)) by (rewrite length_map, length_seq; lia). rewrite map_nth, seq_nth by lia.
    cbn [edenot]. apply VLT3. lia. }
  split; [reflexivity|]. split; [exact AH4|]. split; [exact MI4|]. split; [exact MU | exact WM].
Qed.

(* [comment removed for export] *)
Definition sgX : list expr := map EVar (seq 0 21) ++ map EVar (seq 23 15).
Lemma slx_regs : ST.regs_match (ST.t_know SLOWAF_defs.XRF) (ST.t_regs SLOWAF_defs.XRF) (map (ST.esub sgX) (ST.t_regs SLOWAS_defs.XR)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma slx_kn : forallb (ST.kimplied SG (ST.t_know SLOWAF_defs.XRF)) (map (ST.ksub sgX) (ST.t_know SLOWAS_defs.XR)) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem slsa_ok : SP.summ_okHSC SG GP0 (hmH LB) (hmA LB) (hmC LB) AHM.hmR (AHM.hmF RNGh) (AHM.hmS L RNGh) SLOWA_sum.SLSA.
Proof.
  intros E M rom ms HR HA HW HS HCR HH HT HG.
  cbn [SP.sm_pre SP.sm_post SP.sm_W SP.sm_A SP.sm_PS SP.sm_CR SP.sm_G SLOWA_sum.SLSA] in *.
  (* [comment removed for export] *)
  destruct (sl_step_e E M rom ms HR HA HW HH HT) as (ms1 & E1 & M1 & R1 & F1 & fc1 & Hms1 & Hms1e & HZ1 & HF1 & HR1 & HK1 & Hg1 & Hb1 & HH1 & FR1).
  destruct HF1 as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ->).
  assert (KSP1 : kentry_ok SG E1 M1 (KRange (EVar 1) 8795556151599 0x80000000000)) by (apply (ST.kin_ok SG E1 M1 _ _ HK1); vm_compute; reflexivity).
  cbn [kentry_ok edenot] in KSP1.
  assert (USPE : bv_unsigned (edenot E SLOWAS_defs.vSP) = 16 * bv_unsigned (ev E1 1)).
  { cbn [SLOWAS_defs.vSP SLOWAS_defs.mul SLOWAS_defs.vSP16 SLOWAS_defs.V edenot]. rewrite (Hg1 1%nat) by lia.
    rewrite u_mul64, u_lit64a. rewrite (Z.mod_small 16 (2^64)) by lia. apply Z.mod_small. lia. }
  unfold SP.hs_ok in HS. change (SP.dstk (Some SLOWAS_defs.vSP) (SP.p_W SLOWAS_defs.SLOWAS)) with (Some (SLOWAS_defs.vSP, 4848)) in HS.
  cbv beta iota in HS. rewrite USPE in HS.
  (* [comment removed for export] *)
  destruct (sl_glue4 E rom ms1 E1 M1 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F1 fc1 HR HA HW HS HCR Hms1e HZ1 HR1 HK1 Hg1 Hb1 HH1)
    as (ms2 & E2 & M2 & F & Hms2 & HT2 & GE2 & BE2 & AH2 & MI2 & HFm & HFb & HFt & RF1 & RF2 & B5 & RP12 & VE21 & V22 & VPB & ESPA & HPQ & HA2 & HW2).
  (* [comment removed for export] *)
  assert (HS2 : SP.hs_ok (AHM.hmS L RNGh) E2 (SP.sm_PS SBODY) (SP.sm_W SBODY)).
  { unfold SP.hs_ok. change (SP.dstk (SP.sm_PS SBODY) (SP.sm_W SBODY)) with (Some (SLOWAB_defs.vSP, 4848)).
    cbv beta iota. change (edenot E2 SLOWAB_defs.vSP) with (edenot E2 SLOWAS_defs.vSP).
    rewrite <- (SP.edenot_gagree 21 E E2 SLOWAS_defs.vSP GE2 BE2 eq_refl). rewrite USPE. exact HS. }
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
  assert (HCR2 : SP.crs_law (hmA (FB4 F :: LB)) E2 (SP.sm_CR SBODY)).
  { intros w Hw z Hz. cbn [SP.sm_CR SBODY SP.p_CR SLOWABCN_defs.SLOWABCN SP.PGH In] in Hw.
    destruct Hw as [<-|[<-|[<-|[]]]].
    - (* [comment removed for export] *)
      cbn [SP.win_den edenot fst snd] in Hz. cbv [SLOWABCN_defs.vFK SLOWABCN_defs.mul SLOWABCN_defs.vF10 SLOWABCN_defs.V] in Hz.
      cbn [edenot] in Hz. rewrite UF2', u_lit64a in Hz. rewrite (Z.mod_small 1024 (2^64)) in Hz by lia.
      apply (AHM.hmA_of_block AI (FB4 F :: LB) (FB4 F) z (or_introl eq_refl)). cbn [ab_addr ab_size]. lia.
    - (* [comment removed for export] *)
      cbn [SP.win_den edenot fst snd] in Hz. cbv [SLOWABCN_defs.mul SLOWABCN_defs.vF10 SLOWABCN_defs.V] in Hz.
      cbn [edenot] in Hz. rewrite USF2, u_lit64a in Hz. rewrite (Z.mod_small 128 (2^64)) in Hz by lia.
      replace z with (shad (8 * (z - ASHOFF))) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8;
        rewrite Z.mul_comm, Z.div_mul by lia; lia).
      apply AHM.hmA_of_fake_shadow. exists 4, F, 1024. split; [left; reflexivity|]. unfold ASHOFF.
      clear - Hz HFm. Z.div_mod_to_equations. lia.
    - (* [comment removed for export] *)
      cbn [SP.win_den edenot fst snd] in Hz. rewrite !u_lit64a in Hz. rewrite (Z.mod_small 0 (2^64)), (Z.mod_small 4 (2^64)) in Hz by lia.
      apply (AHM.hmA_of_ci AI (FB4 F :: LB) (0x10b978, 0x10b97c) z); [apply IMG_CI; vm_compute; tauto | cbn [fst snd]; lia]. }
  destruct (HBODY (FB4 F :: LB) (u4_cons F) (NND.c5_cons4 F LB HC5) E2 M2 rom ms2 HR HA2 HW2 HS2 HCR2 (conj AH2 MI2) HT2 ltac:(constructor))
    as (ms3 & X3 & E3 & M3 & Hms3 & HX3 & HT3 & _ & Hg3 & Hb3 & HH3 & FR3).
  cbn [SP.sm_post SBODY In] in HX3. destruct HX3 as [<-|[]].
  cbn [SP.sm_A SP.sm_G SP.sm_W SP.sm_PS SBODY] in Hms3, Hg3, FR3. change (SP.p_G SLOWAB_defs.SLOWAB) with 24%nat in Hg3.
  assert (VE31 : forall k, (k < 21)%nat -> ev E3 k = ev E1 k).
  { intros k Hk. rewrite <- (Hg3 k) by lia. rewrite <- (GE2 k) by lia. apply Hg1. exact Hk. }
  assert (V3_21 : ev E3 21 = Z_to_bv 64 (F / 1024)) by (rewrite <- (Hg3 21%nat) by lia; exact VE21).
  assert (V3_22 : ev E3 22 = Z_to_bv 64 (fflag L 4 F)) by (rewrite <- (Hg3 22%nat) by lia; exact V22).
  (* [comment removed for export] *)
  destruct (sl_setsh E rom ms3 E1 E3 M3 F HR HCR Hg1 HS HT3 HH3 VE31 V3_21 V3_22 HFm HFb RF2)
    as (ms4 & E4 & M4 & Hms4 & HT4 & VE4 & Hb4 & AH4 & MI4 & MU4 & WM4).
  (* [comment removed for export] *)
  assert (GE4 : SP.gagree 21 E E4) by (intros k Hk; rewrite VE4 by lia; rewrite VE31 by exact Hk; apply Hg1; exact Hk).
  assert (BE4 : eb E = eb E4) by (rewrite Hb4, Hb3; exact BE2).
  pose proof HT4 as (_ & _ & (R4' & _ & _ & _ & HK4)). cbn [ST.tstate s_know mem_denot] in HK4.
  assert (HA4 : SX.aw_genuine E4 (SP.p_A SLOWAF_defs.SLOWAF)).
  { cbn [SP.p_A SLOWAF_defs.SLOWAF SP.PGCA]. apply (AGC.aw_gen_mix SG E E4 M4 _ _ _ 21 HK4 HA GE4 BE4). vm_compute. reflexivity. }
  assert (HW4 : SP.wins_client (fun _ _ => True) E4 (SP.p_W SLOWAF_defs.SLOWAF)).
  { unfold SP.wins_client. apply Forall_forall. intros w _. exact I. }
  destruct (slaf_summ M4 E4 M4 rom ms4 HR HA4 HW4 I ltac:(intros w []) (conj MI4 (wmono_refl SG M4)) HT4 ltac:(constructor))
    as (ms5 & X5 & E5 & M5 & Hms5 & HX5 & HT5 & _ & Hg5 & Hb5 & (MI5 & WM5) & FR5).
  cbn [SP.sm_post SP.p_ex SLOWAF_defs.SLOWAF SP.PGCA In] in HX5. destruct HX5 as [<-|[]].
  cbn [SP.sm_A SP.sm_G SP.sm_W SP.sm_PS] in Hms5, Hg5, FR5. change (SP.p_G SLOWAF_defs.SLOWAF) with 23%nat in Hg5.
  cbn [SP.frame_ok SP.p_PS SLOWAF_defs.SLOWAF SP.PGCA] in FR5.
  (* [comment removed for export] *)
  pose proof HS as (HSa & HSb & HSc).
  set (SP16 := bv_unsigned (ev E1 1)) in *.
  set (SP := 16 * SP16) in *. assert (ESP : SP = 16 * SP16) by reflexivity. clearbody SP.
  pose proof (bv_unsigned_in_range 64 (ev E1 21)) as RPQ. change (bv_modulus 64) with (2^64) in RPQ.
  set (PQ := bv_unsigned (ev E1 21)) in *.
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
  assert (CLW : forallb (SP.win_closed 21) (SP.p_W SLOWAS_defs.SLOWAS) = true) by (vm_compute; reflexivity).
  assert (EWF : SP.p_W SLOWAF_defs.SLOWAF = SP.p_W SLOWAS_defs.SLOWAS ++ [(EVar 22, 0, ELit 1)]) by (vm_compute; reflexivity).
  assert (OUTF : forall x : word, SP.outside_wins E (SP.p_W SLOWAS_defs.SLOWAS) (bv_unsigned x) -> bv_unsigned x <> fl ->
                   SP.outside_wins E4 (SP.p_W SLOWAF_defs.SLOWAF) (bv_unsigned x)).
  { intros x Hx Hne. rewrite EWF. unfold SP.outside_wins. apply Forall_app. split.
    - exact (SP.outside_wins_gagree 21 E E4 _ _ GE4 BE4 CLW Hx).
    - constructor; [|constructor]. cbn [SP.win_den edenot]. rewrite VE4 by lia. rewrite V3_22, !u_lit64a.
      rewrite !Z.mod_small by lia. lia. }
  assert (AH5 : AHEAP AI L RNGh st LB M5).
  { apply (AI_frame AI L RNGh st LB _ M5 (map (SP.win_den E) (SP.p_W SLOWAS_defs.SLOWAS)) AHR).
    - intros x Hx. destruct (Z.eq_dec (bv_unsigned x) fl) as [Hfl|Hfl].
      + replace x with (wa fl) by (unfold wa; rewrite <- Hfl; apply Z_to_bv_bv_unsigned). rewrite MFL.
        cbn [write_to_mem]. unfold wa. rewrite bv_eqb_refl. reflexivity.
      + rewrite (FR5 x (OUTF x ltac:(unfold SP.outside_wins; clear - Hx; induction (SP.p_W SLOWAS_defs.SLOWAS) as [|w W IH]; [constructor|];
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
  pose proof (AGC.tm_rename SG SLOWAF_defs.XRF SLOWAS_defs.XR sgX E5 M5 rom ms5 HT5 eq_refl slx_regs slx_kn) as HT6.
  exists ms5, SLOWAS_defs.XR, (ST.senv E5 sgX), M5.
  assert (UF4 : bv_unsigned (mul_div M_MUL (Z_to_bv 64 1024) (ev E4 21)) = F).
  { rewrite VE4 by lia. rewrite V3_21, <- VE21. exact UF2'. }
  assert (UFL4 : bv_unsigned (ev E4 22) = fl).
  { rewrite VE4 by lia. rewrite V3_22. apply u_small. lia. }
  (* [comment removed for export] *)
  assert (FPB : forall b j, SP.fpu (AHM.hmF RNGh) (SP.p_A SLOWAB_defs.SLOWAB) E2 b j -> SP.fpu (AHM.hmF RNGh) (SP.p_A SLOWAS_defs.SLOWAS) E b j).
  { apply (AGLF.fpu_mix (AHM.hmF RNGh) E E2 _ _). apply (AGLF.fp_mix3 E E2 _ _ 21 _ GE2 BE2).
    intros w Hw. vm_compute in Hw. destruct Hw as [<-|[<-|[]]]; intros b j Hw1 Hw2; cbn [SX.awin_den edenot fst snd] in Hw1, Hw2.
    - right. rewrite UF2' in Hw1, Hw2. rewrite u_lit64a in Hw2. rewrite (Z.mod_small 1024 (2^64)) in Hw2 by lia.
      destruct RF1 as (_ & _ & RF). apply RF; lia.
    - right. rewrite USF2 in Hw1, Hw2. rewrite u_lit64a in Hw2. rewrite (Z.mod_small 128 (2^64)) in Hw2 by lia.
      destruct RF2 as (_ & _ & RF). apply RF; rewrite ESH; lia. }
  assert (FPF : forall b j, SP.fpu (AHM.hmF RNGh) (SP.p_A SLOWAF_defs.SLOWAF) E4 b j -> SP.fpu (AHM.hmF RNGh) (SP.p_A SLOWAS_defs.SLOWAS) E b j).
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
  rewrite USPE in Hcls.
  assert (KC : AGLF.keep_cls AI LB SP (bv_unsigned x)) by exact Hcls.
  pose proof (bv_unsigned_in_range 64 x) as Rx; change (bv_modulus 64) with (2^64) in Rx.
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
  cbn [SP.frame_ok] in FR3.
  rewrite (FR3 x).
  2:{ cbn [SP.p_W SLOWAB_defs.SLOWAB SP.PGCA]. unfold SP.outside_wins.
      pose proof (SP.outside_wins_gagree 21 E E2 _ _ GE2 BE2 CLW Hout) as HO2. unfold SP.outside_wins in HO2.
      cbn [SP.p_W SLOWAS_defs.SLOWAS SP.PGH] in HO2.
      apply Forall_cons; [exact (Forall_inv HO2)|]. apply Forall_cons; [exact (Forall_inv (Forall_inv_tail HO2))|].
      apply Forall_cons; [|apply Forall_cons; [|constructor]].
      - cbv [SLOWAB_defs.vFK SLOWAB_defs.mul SLOWAB_defs.vF10 SLOWAB_defs.V]. cbn [SP.win_den edenot].
        rewrite UF2', u_lit64a, (Z.mod_small 1024 (2^64)) by lia. intros [H1 H2]. apply OF. lia.
      - cbv [SLOWAB_defs.mul SLOWAB_defs.vF10 SLOWAB_defs.V]. cbn [SP.win_den edenot].
        rewrite USF2, u_lit64a, (Z.mod_small 128 (2^64)) by lia. intros [H1 H2]. apply OS. rewrite ESH. lia. }
  2:{ change (edenot E2 SLOWAB_defs.vSP) with (edenot E2 SLOWAS_defs.vSP).
      rewrite <- (SP.edenot_gagree 21 E E2 SLOWAS_defs.vSP GE2 BE2 eq_refl). rewrite USPE.
      exact (AGLF.keep_cls_cons AI (FB4 F) LB SP (bv_unsigned x) KC). }
  (* [comment removed for export] *)
  pose proof (AGLF.keep_rt AI LB (bv_unsigned x2) SP M1 M2 (bv_unsigned x) RP12 ltac:(lia) ltac:(lia) Rx KC) as K2.
  unfold wa in K2. rewrite Z_to_bv_bv_unsigned in K2. rewrite K2.
  (* [comment removed for export] *)
  exact (FR1 x Hout).
Qed.

End SL.
End NSL.
