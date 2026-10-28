(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep PmFrame PmParSpecs PmParKit PmCertKitG PgSrc PgV8.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnModelFacts PnStatics PnKeep PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj PnBrKit PnBrKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnBrKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrGrow.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSBdocP_u PnSBdocG_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSBDR.
Import PMS.
Abbreviation AN := PnLayoutS_u.NADDR_S.
Abbreviation mem := (word -> option byte).
Abbreviation bparser_at := (PNM.bparser_at RSEGS AD PMSP.T3 PMSP.T4 (pa_vp_parser AD)).
Abbreviation BENT := PNBK.BENT.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KH := PNBKS.kh_S L HI LY HIok.
Let KL := PMKS.klayout_S L LY.
Abbreviation brel := (PNBK.brel RSEGS AD AN L HI 7).
Abbreviation gw := (PNBG.gw RSEGS AD AN L HI 7).
Abbreviation pot := (PNR.pot_bparser L).
Abbreviation bd_ctx := (PNSBDG.bd_ctx L).
Abbreviation bd_kont := (PNSBDG.bd_kont L HI).
Abbreviation bd_saved := PNSBDG.bd_saved.

Hypothesis OPN : PMS.opnew_spec L HI.
Hypothesis OPD : PMS.opdel_spec L HI.

Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac fd P := PMK.feed P ltac:(first [PMK.sc | apply PNSBDG.bvu | unfold PNSBDP.aligned; PMK.sc]).

(* [comment removed for export] *)
Lemma bd_grow K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax
      (fx1 : FPState) R1 (M1 : mem) model1 cr1 s1 sm1 ax1 (m lenv : Z) :
  bd_ctx K LBX sp r fb str R cr s -> bd_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M1 model1 cr1 s1 sm1 ax1) ->
  PNR.binv s1 -> PNM.b_stk s1 = PNM.b_stk s -> PNM.b_bb s1 = PNM.b_bb s -> 2 ^ PNM.b_sk s1 = m -> Z.of_nat (length (PNM.b_stk s1)) = m -> m <= 1024 ->
  PMSP.ec_at RSEGS M1 (fb + 16) e cat -> PM.unread (PNM.b_src s1) sm1 + 4 <= PM.unread (PNM.b_src s) sm -> 0 <= lenv < 2 ^ 64 ->
  getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 64) -> getr R1 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R1 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R1 (PMK.reg 8) = Z_to_bv 64 (fb + 40) -> getr R1 (PMK.reg 9) = Z_to_bv 64 (fb + 16) ->
  getr R1 (PMK.reg 18) = Z_to_bv 64 (fb + 464) -> getr R1 (PMK.reg 19) = Z_to_bv 64 lenv ->
  (forall k, In k [20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (PMK.reg k) = getr R (PMK.reg k)) ->
  L5.u32_at RSEGS M1 (sp - 64) 2 -> L5.u32_at RSEGS M1 (sp - 60) lenv -> L5.u64_at RSEGS M1 (sp - 56) 4 -> bd_saved R M1 sp r ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x37064 M1 model1) K.
Proof.
  intros CTX KONT BR1 INV1 ESTK EBB Hm HL Hm10 EC1 UNR4 Hlenv X2 X3 X4 X8 X9 X18 X19 XK E64 E60 E56 SV1.
  pose proof CTX as (K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED). pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2.
  pose proof RAok as (Hr1 & Hr2).
  set (E0 := BENT M model cr s sm ax) in *.
  destruct (PNBG.gw_of_brel RSEGS AD AN L HI KH 7 LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR1) as (GW1 & PA1 & GR1 & CK1).
  unfold E0 in CK1. cbn [PNBK.be_cr PNBK.be_s] in CK1.
  set (LB1 := PNM.bparser_own s1 ++ LBX) in *.
  pose proof GW1 as (_ & _ & _ & BASE1 & _ & _ & _ & _ & _ & HH1 & STK1 & MOK1 & _).
  change (PMSP.pm_scr 7) with 26624 in STK1. pose proof STK1 as (A16 & SLO & SHI & STOP & SDEF1).
  pose proof (L5C.stk_writable RSEGS _ M1 sp 26624 STK1) as WR1. pose proof BASE1 as (IMG1 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG1.
  assert (BRG1 : PMFR.brange L LB1) by (apply (PMFR.brange_of_heap L HI HIok LB1 LB1 cr1 M1 _ HH1); apply incl_refl).
  pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SV1' & _). unfold PNM.OFF_STK in SV1'.
  pose proof SV1' as (V0 & V8 & V16 & Hk & Hlen & Hal & DB1 & _). clear SV1'. unfold PNM.BSZ in V8, V16, Hlen, DB1.
  set (b := PNM.b_sb s1) in *. set (k := PNM.b_sk s1) in *. set (stk1 := PNM.b_stk s1) in *.
  rewrite HL in V8. rewrite Hm in V16, DB1.
  pose proof INV1 as (_ & (L1 & _)).
  assert (Hm1 : 1 <= m) by lia.
  assert (Bs : In (b, 40 * m) (PNM.bparser_own s1)).
  { rewrite <- Hm. unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own, PNM.BSZ, b, k. apply in_or_app. right. left. reflexivity. }
  assert (OWNB : forall B n, In (B, n) (PNM.bparser_own s1) -> 4096 <= B /\ B + n <= hl_sptop L - 8388608).
  { intros B n Hin. destruct (BRG1 B n ltac:(unfold LB1; apply in_or_app; left; exact Hin)) as (Q0 & _ & Q4). unfold hl_ceil in Q4. lia. }
  destruct (OWNB _ _ Bs) as (Hb0 & Hb4).
  pose proof SV1 as (S8 & S16 & S24 & S32 & S40).
  (* [comment removed for export] *)
  let gcase CONC := (
    pose proof (CONC fx1 R1 M1 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 36%nat => r | 19%nat => lenv
                 | 37%nat => bv_unsigned (getr R (PMK.reg 8)) | 38%nat => bv_unsigned (getr R (PMK.reg 9)) | 39%nat => bv_unsigned (getr R (PMK.reg 18))
                 | 40%nat => bv_unsigned (getr R (PMK.reg 19)) | 41%nat => b | _ => 0 end)) as P; cbn beta iota in P;
    fd P;
    pvz_hg ltac:(idtac; destruct P as (fx2 & R2 & M2 & pvzP); PMK.pvz_lin pvzP;
                  destruct pvzP as (MG2 & _ & FRZ2 & MS2 & KS2 & Y1 & Y2 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y18 & Y19
                     & G192 & G184 & G112 & G120 & G168 & G160 & G152 & G104 & G96 & G88 & G80 & G72 & C2 & C3 & C4 & C5 & C6 & G64 & G60 & G56)); PMK.pvz_clrT;
    apply (PNBG.gw_piece RSEGS AD AN L HI KH 7 LBX sp fb str E0 LB1 M1 model1 cr1 (PNM.b_src s1) sm1 ax1 fx1 fx2 R1 R2 0x37064 0xb03b8 M2
             (fun a => sp - 224 <= a < sp - 224 + 224) K ltac:(lia) GW1 FOK INCS MS2 MG2 FRZ2 ltac:(intros a; apply PMK.rng_dec)
             ltac:(intros a Pa; cbn beta in Pa; left; change (PMSP.pm_scr 7) with 26624; clear -Pa; lia));
    intros GW2;
    assert (PA2 : bparser_at M2 (fb + 40) (fb + 472) s1)
      by (apply (PNMF.bparser_at_agree RSEGS AD (pa_vp_parser AD) M1 M2 (fb + 40) (fb + 472) s1); unfold PNM.PSIZE; [lia|lia| intros i Hi; apply FRZ2; lia| | exact PA1];
          intros B n Hin; destruct (OWNB B n Hin) as (Q0 & Q4); split; [lia|]; split; [lia|]; intros i Hi; apply FRZ2; lia);
    assert (EC2 : PMSP.ec_at RSEGS M2 (fb + 16) e cat) by (apply (PNSBDG.ec_agree M1 M2); [intros i Hi; apply FRZ2; lia|lia|lia| exact EC1]);
    apply (PNSBDG.bd_gtail L HI LY HIok OPN OPD K LBX sp r fb cat e str R M model cr s sm ax fx2 R2 M2 model1 cr1 s1 sm1 ax1 _ lenv CTX KONT GW2 PA2 GR1 CK1 INV1 ESTK EBB Hm HL
             ltac:(lia) EC2 UNR4 Hlenv Y1 Y2 ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.sc) ltac:(PMK.sc) ltac:(PMK.sc) ltac:(PMK.rk) ltac:(PMK.rk)
             ltac:(intros j Hj; rewrite (KS2 j) by (revert Hj; clear; intros Hj; cbn in Hj |- *; tauto); apply XK; exact Hj) ltac:(unfold PNSBDG.bd_gcells; repeat split; PMK.sc)
             ltac:(split; [exact C2| split; [exact C3| split; [exact C4| split; [exact C5| exact C6]]]]))) in
  destruct (PNSBDG.pow2_cases k m ltac:(lia) Hm Hm10) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]];
  [ gcase PNSBDP.bbdG0_conc | gcase PNSBDP.bbdG1_conc | gcase PNSBDP.bbdG2_conc | gcase PNSBDP.bbdG3_conc | gcase PNSBDP.bbdG4_conc | gcase PNSBDP.bbdG5_conc
  | gcase PNSBDP.bbdG6_conc | gcase PNSBDP.bbdG7_conc | gcase PNSBDP.bbdG8_conc | gcase PNSBDP.bbdG9_conc | gcase PNSBDP.bbdG10_conc ].
Qed.

End WithHeap.
End PNSBDR.
