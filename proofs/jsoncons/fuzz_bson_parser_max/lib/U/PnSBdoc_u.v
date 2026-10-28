(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep PmFrame PmParSpecs PmParKit PmCertKitG PgSrc PgV8.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnModelFacts PnStatics PnKeep PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj PnBrKit PnBrKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnBrKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrGrow PnSzKit.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSBdocP_u PnSBdocG_u PnSBdocR_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSBD.
Import PMS.
Abbreviation AN := PnLayoutS_u.NADDR_S.
Abbreviation mem := (word -> option byte).
Abbreviation bparser_at := (PNM.bparser_at RSEGS AD PMSP.T3 PMSP.T4 (pa_vp_parser AD)).
Abbreviation BENT := PNBK.BENT.

Lemma bax_cat_add ax : PNST.bax_cat (PNST.bax_add_cat ax) = true.
Proof. destruct ax; reflexivity. Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KH := PNBKS.kh_S L HI LY HIok.
Let KL := PMKS.klayout_S L LY.
Abbreviation brel := (PNBK.brel RSEGS AD AN L HI 7).
Abbreviation pot := (PNR.pot_bparser L).
Abbreviation bd_ctx := (PNSBDG.bd_ctx L).
Abbreviation bd_kont := (PNSBDG.bd_kont L HI).
Abbreviation bd_saved := PNSBDG.bd_saved.

Hypothesis SRD : PNRS.src_read_spec L HI.
Hypothesis MKE : PNRS.make_ec_spec L HI.
Hypothesis OPN : PMS.opnew_spec L HI.
Hypothesis OPD : PMS.opdel_spec L HI.

Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac fd P := PMK.feed P ltac:(first [PMK.sc | apply PNSBDG.bvu | unfold PNSBDP.aligned; PMK.sc]).
Local Ltac ks_step KS Hj := rewrite (KS _) by (revert Hj; clear; intros Hj; cbn in Hj |- *; tauto).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bd_err K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax
      (fx2 : FPState) R2 (M2 : mem) model1 cr1 s1 sm1 ax1 (v : Z) :
  bd_ctx K LBX sp r fb str R cr s -> bd_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M2 model1 cr1 s1 sm1 ax1) ->
  PNR.binv s1 -> PNM.b_stk s1 = PNM.b_stk s -> PNM.b_bb s1 = PNM.b_bb s -> PMSP.ec_at RSEGS M2 (fb + 16) e cat -> 1 <= v <= 64 ->
  getr R2 (PMK.reg 1) = Z_to_bv 64 0x370c4 -> getr R2 (PMK.reg 2) = Z_to_bv 64 (sp - 64) ->
  getr R2 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R2 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R2 (PMK.reg 8) = Z_to_bv 64 (fb + 40) -> getr R2 (PMK.reg 9) = Z_to_bv 64 (fb + 16) ->
  getr R2 (PMK.reg 10) = Z_to_bv 64 (fb + 16) -> getr R2 (PMK.reg 11) = Z_to_bv 64 v ->
  (forall k, In k [20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (PMK.reg k) = getr R (PMK.reg k)) ->
  bd_saved R M2 sp r ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0x36ee4 M2 model1) K.
Proof.
  intros CTX KONT BR2 INV1 ESTK EBB EC2 Hv Y1 Y2 Y3 Y4 Y8 Y9 Y10 Y11 YK2 SV2.
  pose proof CTX as (K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED). pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2.
  pose proof RAok as (Hr1 & Hr2).
  set (E0 := BENT M model cr s sm ax) in *.
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 7 LBX sp fb str E0 M2 model1 cr1 s1 sm1 ax1 BR2) as (PA2 & _ & _ & _ & STK2 & _).
  change (PMSP.pm_scr 7) with 26624 in STK2. pose proof STK2 as (A16 & SLO & SHI & STOP & _).
  assert (X18 : getr R2 (PMK.reg 18) = Z_to_bv 64 (bv_unsigned (getr R2 (PMK.reg 18)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (ED2 : L5.defined M2 (fb + 16) 16) by (destruct EC2 as (_ & _ & ED); exact ED).
  unfold PNRS.make_ec_spec in MKE.
  apply (PNBK.brel_make_ec RSEGS AD AN L HI KH 7 LBX sp fb str E0 M2 model1 cr1 s1 sm1 ax1 fx2 R2 (sp - 64) 0x370c4 v K MKE ltac:(lia) K0 BR2 FOK INCS
           Y1 ltac:(split; [lia| reflexivity]) Y2 Y3 Y4 Y10 Y11 Hv ltac:(lia) ltac:(unfold PMSP.pm_scr; lia)
           ltac:(replace (sp - 64) with (sp + (-4) * 16) by lia; apply PNSBDG.mod16_off; exact A16) ED2).
  intros fx3 R3 M3 RP23 EC3 BR3 AG23.
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 7 LBX sp fb str E0 M3 model1 cr1 s1 sm1 _ BR3) as (PA3 & _ & _ & _ & STK3 & _).
  change (PMSP.pm_scr 7) with 26624 in STK3. pose proof (L5C.stk_writable RSEGS _ M3 sp 26624 STK3) as WR3.
  assert (WP3 : L5.writable RSEGS M3 (fb + 40) 416) by (destruct PA3 as (_ & D & _); apply (L5C.writable_of_defined RSEGS); [exact D|lia|lia]).
  assert (SV3 : bd_saved R M3 sp r) by (apply (PNSBDG.bd_saved_agree R M2 M3 sp r); [intros a n H1 H2; apply AG23; lia|lia|lia| exact SV2]).
  pose proof SV3 as (S8 & S16 & S24 & S32 & S40).
  LeanFeed.pfeed P (PNSBDP.bbdE_conc fx3 R3 M3 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => bv_unsigned (getr R2 (PMK.reg 18)) | 35%nat => fb + 16 | 36%nat => r
               | 37%nat => bv_unsigned (getr R (PMK.reg 8)) | 38%nat => bv_unsigned (getr R (PMK.reg 9)) | 39%nat => bv_unsigned (getr R (PMK.reg 18))
               | 40%nat => bv_unsigned (getr R (PMK.reg 19)) | _ => 0 end)) ltac:(first [PMK.sc | apply PNSBDG.bvu | unfold PNSBDP.aligned; PMK.sc]).
  pvz_hg ltac:(idtac; destruct P as (fx4 & R4 & M4 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG4 & _ & FRZ4 & MS4 & KS4 & Z1 & Z2 & Z8 & Z9 & Z18 & Z19 & MO4)); PMK.pvz_clrT.
  apply (PNBK2.brel_piece_more RSEGS AD AN L HI KH 7 LBX sp fb str E0 M3 model1 cr1 s1 sm1 _ fx3 fx4 R3 R4 0x370c4 0x370ac M4
           (fun a => fb + 40 + 8 <= a < fb + 40 + 8 + 1) 0 K ltac:(lia) BR3 FOK INCS MS4 MG4 FRZ4 ltac:(intros a; apply PMK.rng_dec)
           ltac:(intros a Pa; cbn beta in Pa; right; clear -Pa; lia) ltac:(replace (fb + 48) with (fb + 40 + 8) by lia; exact MO4) ltac:(left; reflexivity)).
  intros BR4.
  apply (PNSBDG.bd_fin L HI 0x370ac K LBX sp r fb cat e str R M model cr s sm ax fx4 R4 M4 model1 cr1 _ sm1 _ (PNSBDG.bd_ret r) CTX KONT BR4 Z1 Z2);
    [PMK.rk| PMK.rk| exact Z8| exact Z9| exact Z18| exact Z19| | | cbn [PNBO.set_more PNM.b_bb]; exact EBB].
  { intros j Hj. ks_step KS4 Hj. rewrite (PMK.cs_of_preserved R2 R3 j RP23) by (revert Hj; clear; intros Hj; cbn in Hj |- *; tauto). apply YK2. exact Hj. }
  left. split; [| split; [reflexivity|]; split; [apply bax_cat_add|]; split; [cbn [PNBO.set_more PNM.b_stk]; rewrite ESTK; lia| destruct INV1 as (ID' & SH'); split; [exact ID'| exact SH']]].
  exists v. split; [exact Hv|]. apply (PNSBDG.ec_agree M3 M4); [intros i Hi; apply FRZ4; lia|lia|lia| exact EC3].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem begin_document_ok : PNRS.begin_document_spec L HI.
Proof.
  unfold PNRS.begin_document_spec, PNR.begin_document_spec, PNR.brun_spec.
  intros fx R M model K LBX cr sp r fb cat e s str sm ax HH MOK K0 ENT FOK ARGS RPRE INCS INV EC0 He UNR CRED KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2.
  pose proof MOK as (Mh & Ml & Mm). change (PMSP.pm_scr 7) with 26624 in STK. pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  destruct ARGS as (A10 & A11 & A12). rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
  unfold PNR.o_p, PNR.o_ec, PNR.o_v, PMSP.o_p, PMSP.o_ec, PMSP.o_v in A10, A11, A12, EC0. cbn [pa_off_p pa_off_ec pa_off_v AD PnLayoutS_u.ADDR_S] in A10, A11, A12, EC0.
  pose proof (L5C.stk_writable RSEGS _ M sp 26624 STK) as WR.
  pose proof (PNBK.brel_init RSEGS AD AN L HI 7 LBX sp fb str M model cr s sm ax ltac:(lia) RPRE HH STK MOK) as BR0.
  set (E0 := BENT M model cr s sm ax) in *.
  assert (CTX : bd_ctx K LBX sp r fb str R cr s).
  { split; [exact K0|]. split; [exact FOK|]. split; [exact INCS|]. split; [exact RAok|]. split; [exact Rsp|]. split; [exact Rgp|]. split; [exact Rtp| exact CRED]. }
  assert (KONT' : bd_kont K LBX sp r fb cat e str R M model cr s sm ax) by exact KONT.
  unfold PNRS.src_read_spec, PNR.src_read_spec in SRD.
  pose proof RPRE as (PA0 & _ & VIS0 & _ & BASE0 & _). unfold PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at in PA0, VIS0.
  cbn [pa_off_p pa_off_is pa_off_v pa_vp_visitor AD PnLayoutS_u.ADDR_S] in PA0, VIS0.
  pose proof BASE0 as (IMG0 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG0.
  pose proof PA0 as (_ & PD0 & _ & _ & _ & CM0 & _ & _ & _ & ML0 & _ & _ & _ & _ & SV0 & _). unfold PNM.OFF_STK, PNM.MAX_DEPTH in SV0, ML0.
  pose proof SV0 as (V0 & V8 & V16 & Hk & Hlen & Hal & DB & _). unfold PNM.BSZ in V8, V16, Hlen, DB.
  assert (WP : L5.writable RSEGS M (fb + 40) 416) by (apply (L5C.writable_of_defined RSEGS); [exact PD0|lia|lia]).
  destruct (PNBK2.brel_blocks RSEGS AD AN L HI KH 7 LBX sp fb str E0 M model cr s sm ax BR0) as (BRG & OWNB & _).
  pose proof INV as (ID & SH). pose proof SH as (L1 & L2 & _). unfold PNM.MAX_DEPTH in L2.
  set (b := PNM.b_sb s) in *. set (k := PNM.b_sk s) in *. set (stk := PNM.b_stk s) in *. set (n := Z.of_nat (length stk)) in *.
  set (mm := 2 ^ k) in *.
  assert (Hmm1 : 1 <= mm) by (pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)) as X; unfold mm; lia).
  assert (Hmm2 : mm <= 2048) by (unfold mm; change 2048 with (2 ^ 11); apply Z.pow_le_mono_r; lia).
  assert (Bs : In (b, 40 * mm) (PNM.bparser_own s)) by (unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own, PNM.BSZ, b, mm, k; apply in_or_app; right; left; reflexivity).
  destruct (OWNB _ _ Bs) as (Hb0 & Hb4). unfold hl_ceil in Hb4.
  assert (ALb : b mod 8 = 0) by (apply PMPK.m16_8; exact Hal).
  assert (ALn : (40 * n) mod 8 = 0) by (replace (40 * n) with (0 + 8 * (5 * n)) by lia; apply PMPK.m8_add; reflexivity).
  unfold PMSP.cfg. cbn [PNL.pn_begin_document AN PnLayoutS_u.NADDR_S].
  destruct (Z.le_gt_cases n 1024) as [NLE|NGT].
  - (* [comment removed for export] *)
    LeanFeed.pfeed P (PNSBDP.bbdA_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 41%nat => b | 42%nat => 40 * n | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSBDP.aligned; PMK.sc | rewrite (PNSZ.size32 _ n eq_refl ltac:(lia)); lia]).
    pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
                  destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & X1 & X2 & X8 & X9 & X10 & X11 & X12 & X13 & X18 & X19 & C40 & C32 & C24 & C16 & C8)); PMK.pvz_clrT.
    rewrite Rra, (L5.unsigned_lit r) in C8 by lia.
    apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 7 LBX sp fb str E0 M model cr s sm ax fx fx1 R R1 0x36f7c 0x370d0 M1 (fun a => sp - 96 <= a < sp - 96 + 96) K
             ltac:(lia) BR0 FOK INCS MS1 MG1 FRZ1 ltac:(intros a; apply PMK.rng_dec) ltac:(intros a Pa; cbn beta in Pa; change (PMSP.pm_scr 7) with 26624; clear -Pa; lia)).
    intros BR1.
    assert (EC1 : PMSP.ec_at RSEGS M1 (fb + 16) e cat) by (apply (PNSBDG.ec_agree M M1); [intros i Hi; apply FRZ1; lia|lia|lia| exact EC0]).
    apply (PNBK.brel_src_read RSEGS AD AN L HI KH 7 LBX sp fb str E0 M1 model cr s sm ax fx1 R1 (sp - 64) 0x36fd8 (sp - 44) 4 K SRD
             ltac:(lia) K0 BR1 FOK INCS X1 ltac:(split; [lia| reflexivity]) X2 ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.sc) X11 X12
             ltac:(lia) ltac:(unfold PMSP.pm_scr; lia) ltac:(replace (sp - 64) with (sp + (-4) * 16) by lia; apply PNSBDG.mod16_off; exact A16) ltac:(lia) ltac:(lia) ltac:(lia)).
    intros fx2 R2 M2 src2 sm2 d RP12 Y10 Hd UNR2 DEFc BR2 AG12.
    assert (SV2 : bd_saved R M2 sp r).
    { apply (PNSBDG.bd_saved_agree R M1 M2 sp r); [intros a m H1 H2; apply AG12; lia| lia| lia|]. split; [exact C8|]. split; [exact C16|]. split; [exact C24|]. split; [exact C32| exact C40]. }
    assert (EC2 : PMSP.ec_at RSEGS M2 (fb + 16) e cat) by (apply (PNSBDG.ec_agree M1 M2); [apply AG12; lia|lia|lia| exact EC1]).
    pose proof EC2 as (EU2 & _).
    set (s1 := PNM.with_srcB s src2) in *.
    assert (INV1 : PNR.binv s1) by exact INV.
    assert (ESTK : PNM.b_stk s1 = PNM.b_stk s) by reflexivity.
    destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 7 LBX sp fb str E0 M2 model cr s1 sm2 ax BR2) as (PA2 & _ & _ & _ & STK2 & _).
    change (PMSP.pm_scr 7) with 26624 in STK2. pose proof (L5C.stk_writable RSEGS _ M2 sp 26624 STK2) as WR2.
    pose proof PA2 as (_ & PD2 & _ & _ & H9_2 & CM2 & _ & _ & _ & ML2 & _ & _ & _ & _ & SV2' & _ & D01). unfold PNM.OFF_STK, PNM.MAX_DEPTH in SV2', ML2.
    pose proof SV2' as (W0 & W8 & W16 & _ & _ & _ & DB2 & _). clear SV2'. unfold PNM.BSZ in W8, W16, DB2.
    cbn [s1 PNM.with_srcB PNM.b_sb PNM.b_sk PNM.b_stk PNM.b_done] in W0, W8, W16, DB2, H9_2, D01. fold b k stk mm in W0, W8, W16, DB2. fold n in W8.
    assert (WP2 : L5.writable RSEGS M2 (fb + 40) 416) by (apply (L5C.writable_of_defined RSEGS); [exact PD2|lia|lia]).
    assert (VIS2 : L5.u64_at RSEGS M2 (fb + 464) 726280).
    { pose proof BR2 as ((_ & _ & VIS & _) & _). unfold PNR.o_v, PMSP.o_v, PMSP.visitor_at in VIS. cbn [pa_off_v pa_vp_visitor AD PnLayoutS_u.ADDR_S] in VIS. exact VIS. }
    assert (IMG2 : L5.img_clear M2 65536 754672).
    { pose proof BR2 as ((_ & _ & _ & _ & BASE2 & _) & _). destruct BASE2 as (I2 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in I2. exact I2. }
    pose proof SV2 as (S8 & S16 & S24 & S32 & S40).
    destruct (Z.eq_dec d 4) as [Ed|NEd].
    + subst d.
      destruct (Z.lt_ge_cases n mm) as [LT|GE].
      * (* [comment removed for export] *)
        assert (DE2 : L5.defined M2 (b + 40 * n + 8) 8) by (apply (L5.defined_sub M2 b (40 * mm)); [exact DB2| lia| lia]).
        LeanFeed.pfeed P (PNSBDP.bbdRf_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 36%nat => r
                     | 37%nat => bv_unsigned (getr R (PMK.reg 8)) | 38%nat => bv_unsigned (getr R (PMK.reg 9)) | 39%nat => bv_unsigned (getr R (PMK.reg 18))
                     | 40%nat => bv_unsigned (getr R (PMK.reg 19)) | 45%nat => b + 40 * n | 48%nat => 40 * mm - 40 * n | 50%nat => e | _ => 0 end)) ltac:(first [PMK.sc | apply PNSBDG.bvu | unfold PNSBDP.aligned; PMK.sc
                               | unfold PNSBDP.aligned; replace (b + 40 * n) with (b + 8 * (5 * n)) by lia; apply PMPK.m8_add; exact ALb
                               | apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M2 b (40 * mm)); [exact DB2|lia|lia]|lia|lia] ]).
        pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP;
                      destruct pvzP as (MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z2 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14 & Z18 & Z19 & CE & CT & CP & CM & CI & MO3 & T8 & T16 & T24 & T32 & T40)); PMK.pvz_clrT.
        destruct (PMCG.u64_of_defined RSEGS M3 (b + 40 * n + 8) ltac:(lia) ltac:(lia) (L5.defined_grows M2 M3 _ _ MG3 DE2)) as (w & Hw & CL).
        set (c := PNM.BS 2 w 4 0 0).
        apply (PNBK2.brel_piece_hdstk RSEGS AD AN L HI KH 7 LBX sp fb str E0 M2 model cr s1 sm2 ax fx2 fx3 R2 R3 0x36fd8 0x370ac M3
                 (fun a => (sp - 96 <= a < sp - 96 + 96) \/ (fb + 40 + 8 <= a < fb + 40 + 8 + 1) \/ (fb + 40 + 400 <= a < fb + 40 + 400 + 8) \/ (b + 40 * n + 0 <= a < b + 40 * n + 0 + 40))
                 1 (PNM.b_done s1) stk [] [c] K ltac:(lia) BR2 FOK INCS MS3 MG3
                 ltac:(intros a Ha N; apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; left; exact X
                                                  | intros X; apply N; right; right; left; exact X| intros X; apply N; right; right; right; exact X])
                 ltac:(intros a; repeat (apply PMK.or_dec; [apply PMK.rng_dec|]); apply PMK.rng_dec));
          cbn [s1 PNM.with_srcB PNM.b_stk PNM.b_sb PNM.b_sk PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_ng PNM.b_tg PNM.b_bg]; fold b k stk mm.
        { rewrite app_nil_r. reflexivity. }
        { intros a [X|[X|[X|X]]]; [left; change (PMSP.pm_scr 7) with 26624; lia| right; left; lia| right; right; left; lia| right; right; right; unfold n in X; lia]. }
        { replace (fb + 48) with (fb + 40 + 8) by lia. exact MO3. }
        { replace (fb + 49) with (fb + 40 + 9) by lia. apply (L5C.u8_at_agree RSEGS M2 M3); [intros i Hi; apply FRZ3; lia|lia|lia| exact H9_2]. }
        { right. reflexivity. }
        { exact D01. }
        { rewrite length_app. cbn [length]. replace (b + 40 * Z.of_nat (length stk + 1)) with (b + 40 * n + 40) by (unfold n; lia). replace (fb + 440) with (fb + 40 + 400) by lia. exact CE. }
        { intros i Hi. cbn in Hi. destruct i as [|i]; [|lia]. cbn [nth]. rewrite Nat.add_0_r. fold n.
          unfold PNM.bstate_at. cbn [c PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx].
          split; [exact CM|]. split; [exact CL|]. split; [exact CP|]. split; [exact CT| exact CI]. }
        { rewrite length_app. cbn [length]. unfold n in LT. lia. }
        intros BR3.
        apply (PNSBDG.bd_fin L HI 0x370ac K LBX sp r fb cat e str R M model cr s sm ax fx3 R3 M3 model cr _ sm2 ax (PNSBDG.bd_ret r) CTX KONT' BR3 Z1 Z2);
          [PMK.rk| PMK.rk| exact Z8| exact Z9| exact Z18| exact Z19| | | reflexivity].
        { intros j Hj. ks_step KS3 Hj. rewrite (PMK.cs_of_preserved R1 R2 j RP12) by (revert Hj; clear; intros Hj; cbn in Hj |- *; tauto). ks_step KS1 Hj. reflexivity. }
        right. split; [apply (PNSBDG.ec_agree M2 M3); [intros i Hi; apply FRZ3; lia|lia|lia| exact EC2]|].
        split.
        { unfold PNR.binv. cbn [PNM.b_done PNM.b_stk]. split; [exact ID|].
          apply (PNSBDG.bstack_shape_push stk c SH); [unfold PNM.MAX_DEPTH; unfold n in NLE; lia| unfold PNM.bstate_ok; cbn; lia| unfold PNR.bmode_cont; cbn; lia]. }
        unfold PNR.bprog_value, PNR.bpush_rel. right. exists c. cbn [PNM.b_stk PNM.b_src].
        split; [reflexivity|]. split; [unfold PNM.bstate_ok; cbn; lia|]. split; [unfold PNR.bmode_cont; cbn; lia|]. split; [reflexivity| lia].
      * (* [comment removed for export] *)
        assert (EQn : n = mm) by lia.
        rewrite EQn in W8.
        LeanFeed.pfeed P (PNSBDP.bbdRs_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 36%nat => r
                     | 37%nat => bv_unsigned (getr R (PMK.reg 8)) | 38%nat => bv_unsigned (getr R (PMK.reg 9)) | 39%nat => bv_unsigned (getr R (PMK.reg 18))
                     | 40%nat => bv_unsigned (getr R (PMK.reg 19)) | 45%nat => b + 40 * mm | 50%nat => e | _ => 0 end)) ltac:(first [PMK.sc | apply PNSBDG.bvu | unfold PNSBDP.aligned; PMK.sc]).
        pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP;
                      destruct pvzP as (MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z10 & Z11 & Z12 & Z13 & Z14 & E64 & MO3 & E60 & E56 & T8 & T16 & T24 & T32 & T40)); PMK.pvz_clrT.
        apply (PNBK2.brel_piece_more RSEGS AD AN L HI KH 7 LBX sp fb str E0 M2 model cr s1 sm2 ax fx2 fx3 R2 R3 0x36fd8 0x37064 M3
                 (fun a => (sp - 96 <= a < sp - 96 + 96) \/ (fb + 40 + 8 <= a < fb + 40 + 8 + 1)) 1 K ltac:(lia) BR2 FOK INCS MS3 MG3
                 ltac:(intros a Ha N; apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X])
                 ltac:(intros a; apply PMK.or_dec; apply PMK.rng_dec)
                 ltac:(intros a Pa; cbn beta in Pa; change (PMSP.pm_scr 7) with 26624; clear -Pa; lia) ltac:(replace (fb + 48) with (fb + 40 + 8) by lia; exact MO3) ltac:(right; reflexivity)).
        intros BR3.
        apply (PNSBDR.bd_grow L HI LY HIok OPN OPD K LBX sp r fb cat e str R M model cr s sm ax fx3 R3 M3 model cr (PNBO.set_more s1 1) sm2 ax mm (bv_unsigned (getr R3 (PMK.reg 19)))
                 CTX KONT' BR3 INV1 ESTK eq_refl eq_refl ltac:(cbn [PNBO.set_more PNM.b_stk s1 PNM.with_srcB]; fold stk n; exact EQn) ltac:(lia)
                 ltac:(apply (PNSBDG.ec_agree M2 M3); [intros i Hi; apply FRZ3; lia|lia|lia| exact EC2])
                 ltac:(cbn [PNBO.set_more PNM.b_src s1 PNM.with_srcB]; lia) (PNSBDG.bvu _));
          cbn [PNBO.set_more PNM.b_sb s1 PNM.with_srcB]; fold b; [PMK.rk| PMK.rk| PMK.rk| PMK.rk| PMK.rk| PMK.rk| symmetry; apply Z_to_bv_bv_unsigned| | exact E64| exact E60| exact E56| ].
        { intros j Hj. ks_step KS3 Hj. rewrite (PMK.cs_of_preserved R1 R2 j RP12) by (revert Hj; clear; intros Hj; cbn in Hj |- *; tauto). ks_step KS1 Hj. reflexivity. }
        { split; [exact T8|]. split; [exact T16|]. split; [exact T24|]. split; [exact T32| exact T40]. }
    + (* [comment removed for export] *)
      LeanFeed.pfeed P (PNSBDP.bbdRe_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 46%nat => d | _ => 0 end)) ltac:(first [PMK.sc | apply PNSBDG.bvu | unfold PNSBDP.aligned; PMK.sc]).
      pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z10 & Z11)); PMK.pvz_clrT.
      apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 7 LBX sp fb str E0 M2 model cr s1 sm2 ax fx2 fx3 R2 R3 0x36fd8 0x36ee4 M3 (fun a => sp - 56 <= a < sp - 56 + 8) K
               ltac:(lia) BR2 FOK INCS MS3 MG3 FRZ3 ltac:(intros a; apply PMK.rng_dec) ltac:(intros a Pa; cbn beta in Pa; change (PMSP.pm_scr 7) with 26624; clear -Pa; lia)).
      intros BR3.
      assert (EQ3 : forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 56 <= i < sp - 56 + 8) -> M3 (Z_to_bv 64 i) = M2 (Z_to_bv 64 i)) by exact FRZ3.
      apply (bd_err K LBX sp r fb cat e str R M model cr s sm ax fx3 R3 M3 model cr s1 sm2 ax 1 CTX KONT' BR3 INV1 ESTK eq_refl
               ltac:(apply (PNSBDG.ec_agree M2 M3); [intros i Hi; apply EQ3; lia|lia|lia| exact EC2]) ltac:(lia) Z1);
        [PMK.rk| PMK.rk| PMK.rk| PMK.rk| PMK.rk| exact Z10| exact Z11| |].
      { intros j Hj. ks_step KS3 Hj. rewrite (PMK.cs_of_preserved R1 R2 j RP12) by (revert Hj; clear; intros Hj; cbn in Hj |- *; tauto). ks_step KS1 Hj. reflexivity. }
      { apply (PNSBDG.bd_saved_agree R M2 M3 sp r); [intros a m H1 H2 i Hi; apply EQ3; lia| lia| lia| exact SV2]. }
  - (* [comment removed for export] *)
    assert (EQn : n = 1025) by (unfold n in *; lia).
    LeanFeed.pfeed P (PNSBDP.bbdAx_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 41%nat => b | 42%nat => 40 * n | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSBDP.aligned; PMK.sc | rewrite (PNSZ.size32 _ n eq_refl ltac:(lia)); lia]).
    pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
                  destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & X1 & X2 & X8 & X9 & X10 & X11 & X13 & C40 & C32 & C24 & C16 & C8)); PMK.pvz_clrT.
    rewrite Rra, (L5.unsigned_lit r) in C8 by lia.
    apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 7 LBX sp fb str E0 M model cr s sm ax fx fx1 R R1 0x36f7c 0x36ee4 M1 (fun a => sp - 96 <= a < sp - 96 + 96) K
             ltac:(lia) BR0 FOK INCS MS1 MG1 FRZ1 ltac:(intros a; apply PMK.rng_dec) ltac:(intros a Pa; cbn beta in Pa; change (PMSP.pm_scr 7) with 26624; clear -Pa; lia)).
    intros BR1.
    apply (bd_err K LBX sp r fb cat e str R M model cr s sm ax fx1 R1 M1 model cr s sm ax 4 CTX KONT' BR1 INV eq_refl eq_refl
             ltac:(apply (PNSBDG.ec_agree M M1); [intros i Hi; apply FRZ1; lia|lia|lia| exact EC0]) ltac:(lia) X1 X2);
      [PMK.rk| PMK.rk| exact X8| exact X9| exact X10| exact X11| |].
    { intros j Hj. ks_step KS1 Hj. reflexivity. }
    { split; [exact C8|]. split; [exact C16|]. split; [exact C24|]. split; [exact C32| exact C40]. }
Qed.

End WithHeap.
End PNSBD.
