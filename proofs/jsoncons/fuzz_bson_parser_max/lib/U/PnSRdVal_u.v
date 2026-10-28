(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Znumtheory FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep PmFrame PmParSpecs PmParKit PmCertKitG PgSrc PgV8.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnModelFacts PnStatics PnKeep PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj PnBrKit PnBrKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnBrKitS_u
     PnSRvK_u PnSRvA_u PnSRvS_u PnSRvX_u PnSRvB_u PnSRvO_u PnSRvD_u PnSRvEP_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSRVL.
Import PMS.
Abbreviation AN := PnLayoutS_u.NADDR_S.
Abbreviation mem := (word -> option byte).
Abbreviation bparser_at := (PNM.bparser_at RSEGS AD PMSP.T3 PMSP.T4 (pa_vp_parser AD)).
Abbreviation BENT := PNBK.BENT.

Lemma tsplit t : 0 <= t < 256 ->
  t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7 \/ t = 8 \/ t = 9 \/ t = 10 \/ t = 11 \/ t = 12 \/ t = 13 \/ t = 14 \/ t = 15
  \/ t = 16 \/ t = 17 \/ t = 18 \/ t = 19 \/ t = 127 \/ t = 255 \/ t = 0 \/ (20 <= t <= 126) \/ (128 <= t <= 254).
Proof. intros Ht. lia. Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KH := PNBKS.kh_S L HI LY HIok.
Let KL := PMKS.klayout_S L LY.
Abbreviation brel := (PNBK.brel RSEGS AD AN L HI 8).
Abbreviation pot := (PNR.pot_bparser L).

Local Ltac fd P := PMK.feed P ltac:(first [PMK.sc | unfold PNSRVEP.aligned; PMK.sc]).

Theorem read_value_ok :
  PNRS.make_ec_spec L HI -> PNRS.src_read_spec L HI -> PNRS.read_string_spec L HI -> PMS.validate_spec L -> PNRS.read_cstring_spec L HI ->
  PNRS.str_push_back_spec L HI -> PNRS.read_span_v_spec L HI -> PMS.str_resize_spec L HI -> PNRS.dec128_spec L HI ->
  PNRS.begin_document_spec L HI -> PNRS.begin_array_spec L HI ->
  PNRS.read_value_spec L HI.
Proof.
  intros MKE SRD RSTR VAL RCS PB RSP RSZ DEC BDOC BARR.
  unfold PNRS.read_value_spec, PNR.read_value_spec, PNR.brun_spec.
  intros fx R M model K LBX cr sp r fb cat e s str sm ax HH MOK K0 ENT FOK ARGS RPRE INCS INV EC0 He UNR CRED KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2.
  pose proof MOK as (Mh & Ml & Mm). change (PMSP.pm_scr 8) with 28672 in STK. pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  destruct ARGS as (A10 & A11 & A13 & (t & Ht & A12) & ROOM). rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl13 in A13. rewrite L5K.rl12 in A12.
  unfold PNR.o_p, PNR.o_ec, PNR.o_v, PMSP.o_p, PMSP.o_ec, PMSP.o_v in A10, A11, A13, EC0. cbn [pa_off_p pa_off_ec pa_off_v AD PnLayoutS_u.ADDR_S] in A10, A11, A13, EC0.
  pose proof (L5C.stk_writable RSEGS _ M sp 28672 STK) as WR.
  pose proof (PNBK.brel_init RSEGS AD AN L HI 8 LBX sp fb str M model cr s sm ax ltac:(lia) RPRE HH STK MOK) as BR0.
  assert (CTX : PNSRVK.rv_ctx L t K LBX sp r fb e str R cr s sm).
  { split; [exact Ht|]. split; [exact K0|]. split; [exact FOK|]. split; [exact INCS|]. split; [exact RAok|].
    split; [exact Rsp|]. split; [exact Rgp|]. split; [exact Rtp|]. split; [exact CRED|]. split; [exact INV|]. split; [exact UNR|]. split; [exact He| exact ROOM]. }
  assert (KONT' : PNSRVK.rv_kont L HI K LBX sp r fb cat e str R M model cr s sm ax) by exact KONT.
  unfold PMSP.cfg. cbn [PNL.pn_read_value AN PnLayoutS_u.NADDR_S].
  LeanFeed.pfeed P (PNSRVEP.vlE_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => t | 36%nat => fb + 16 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSRVEP.aligned; PMK.sc]).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & X2 & X8 & X9 & X11 & X13 & X18 & T20 & T19 & T18 & T9 & T8 & T1).
  change (mkCfg (@mkst fx R (Z_to_bv 64 0x375ec) M (seg_rom RSEGS)) model) with (@PMSP.cfg RSEGS fx R 0x375ec M model).
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M model cr s sm ax fx fx1 R R1 _ _ M1 (fun a => sp - 48 <= a < sp - 48 + 48) K
           ltac:(lia) BR0 FOK INCS MS1 MG1 FRZ1 ltac:(intros a; apply PMK.rng_dec) ltac:(intros a Pa; cbn beta in Pa; unfold PMSP.pm_scr; clear - Pa; lia)).
  intros BR1.
  assert (MID1 : PNSRVK.rv_mid R R1 M1 sp r fb).
  { apply (PNSRVK.rv_mid_intro R R1 M1 sp r fb X2); [rewrite (KS1 3%nat) by PMK.inl; exact Rgp| rewrite (KS1 4%nat) by PMK.inl; exact Rtp| exact X8| exact X9| exact X18| |].
    - rewrite Rra in T1. rewrite L5.unsigned_lit in T1 by lia.
      exact (PNSRVK.rv_saved_intro R M1 sp r T1 T8 T9 T18 T19 T20).
    - intros k Hk. apply KS1. revert Hk. clear. intros Hk. cbn in Hk |- *. tauto. }
  pose proof MID1 as (W2 & W3 & W4 & W8 & W9 & W18 & SV1 & SX1).
  assert (EC1 : PMSP.ec_at RSEGS M1 (fb + 16) e cat) by (apply (PNSRVK.ec_agree M M1); [intros i Hi; apply FRZ1; lia|lia|lia| exact EC0]).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ _ _ _ _ _ _ BR1) as (PA1 & _ & _ & _ & STK1 & _).
  change (PMSP.pm_scr 8) with 28672 in STK1. pose proof (L5C.stk_writable RSEGS _ _ sp 28672 STK1) as WR1.
  pose proof BR1 as ((_ & _ & _ & _ & BASE1 & _) & _). cbn [PNBK.be_M] in BASE1. pose proof BASE1 as (IMG1 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG1.
  (* [comment removed for export] *)
  assert (ARM : forall (fx2 : FPState) R2 pc,
            msteps RSEGS (@mkst fx1 R1 (Z_to_bv 64 0x3761c) M1 (seg_rom RSEGS)) (@mkst fx2 R2 (Z_to_bv 64 pc) M1 (seg_rom RSEGS)) ->
            (forall k, In k [2; 3; 4; 8; 9; 18; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (PMK.reg k) = getr R1 (PMK.reg k)) ->
            (PNSRVA.arm_stmt L HI pc \/ pc = 0x376f4) ->
            srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3761c M1 model) K).
  { intros fx2 R2 pc MS2 KS2 WHICH.
    apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M1 model cr s sm ax fx1 fx2 R1 R2 _ _ M1 (fun _ => False) K
             ltac:(lia) BR1 FOK INCS MS2 (mem_grows_refl M1) ltac:(intros a Ha _; reflexivity) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
    intros BR2.
    assert (MID2 : PNSRVK.rv_mid R R2 M1 sp r fb) by (apply (PNSRVK.rv_mid_xfer R R1 R2 M1 M1 sp r fb _ MID1 KS2); [intros k Hk; exact Hk| intros a n _ _ i Hi; reflexivity| lia| lia]).
    destruct WHICH as [ARMS| ->].
    - exact (ARMS t K LBX sp r fb cat e str R M model cr s sm ax fx2 R2 M1 model cr ax CTX KONT' BR2 MID2 EC1).
    - apply (PNSRVK.rv_err L HI LY HIok MKE 0x376f4 14 t K LBX sp r fb cat e str R M model cr s sm ax fx2 R2 M1 model cr s sm ax
               ltac:(right; right; right; split; reflexivity) CTX KONT' BR2 MID2); [destruct EC1 as (_ & _ & ED); exact ED| lia| exact INV]. }
  let disp CONC LEM :=
    (let P := fresh "P" in
     first [rewrite Et in A12, X11 | idtac];
     pose proof (CONC fx1 R1 M1 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => t | 36%nat => fb + 16 | _ => 0 end)) as P; cbn beta iota in P;
     PMK.feed P ltac:(first [PMK.sc | unfold PNSRVEP.aligned; PMK.sc | rewrite X11; apply bv_eq; vm_compute; reflexivity]);
     let fx2 := fresh "fx2" in let R2 := fresh "R2" in let M2 := fresh "M2" in let MS2 := fresh "MS2" in let KS2 := fresh "KS2" in let EQw := fresh "EQw" in
     destruct P as (fx2 & R2 & M2 & _ & EQw & _ & MS2 & KS2 & _);
     (replace M2 with M1 in MS2 by (symmetry; apply functional_extensionality; exact EQw));
     apply (ARM fx2 R2 _ MS2); [intros k Hk; apply KS2; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| LEM]) in
  destruct (tsplit t Ht) as [Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|[Et|Et]]]]]]]]]]]]]]]]]]]]]]];
  [ disp PNSRVEP.vlJ1_conc ltac:(left; exact (PNSRVA.arm1 L HI LY HIok MKE SRD))
  | disp PNSRVEP.vlJ2_conc ltac:(left; exact (PNSRVS.armS2 L HI LY HIok MKE RSTR VAL))
  | disp PNSRVEP.vlJ3_conc ltac:(left; exact (PNSRVA.armC3 L HI LY HIok BDOC))
  | disp PNSRVEP.vlJ4_conc ltac:(left; exact (PNSRVA.armC4 L HI LY HIok BARR))
  | disp PNSRVEP.vlJ5_conc ltac:(left; exact (PNSRVB.armBin L HI LY HIok MKE SRD RSP))
  | disp PNSRVEP.vlJ6_conc ltac:(left; exact (PNSRVA.arm6 L HI LY HIok))
  | disp PNSRVEP.vlJ7_conc ltac:(left; exact (PNSRVO.armOid L HI LY HIok MKE SRD RSZ))
  | disp PNSRVEP.vlJ8_conc ltac:(left; exact (PNSRVA.arm8 L HI LY HIok MKE SRD))
  | disp PNSRVEP.vlJ9_conc ltac:(left; exact (PNSRVA.arm9 L HI LY HIok MKE SRD))
  | disp PNSRVEP.vlJ10_conc ltac:(left; exact (PNSRVA.arm10 L HI LY HIok))
  | disp PNSRVEP.vlJ11_conc ltac:(left; exact (PNSRVX.armX L HI LY HIok RCS PB))
  | disp PNSRVEP.vlJ12_conc ltac:(right; reflexivity)
  | disp PNSRVEP.vlJ13_conc ltac:(left; exact (PNSRVS.armS13 L HI LY HIok MKE RSTR VAL))
  | disp PNSRVEP.vlJ14_conc ltac:(left; exact (PNSRVS.armS2 L HI LY HIok MKE RSTR VAL))
  | disp PNSRVEP.vlJ15_conc ltac:(right; reflexivity)
  | disp PNSRVEP.vlJ16_conc ltac:(left; exact (PNSRVA.arm16 L HI LY HIok MKE SRD))
  | disp PNSRVEP.vlJ17_conc ltac:(left; exact (PNSRVA.arm17 L HI LY HIok MKE SRD))
  | disp PNSRVEP.vlJ18_conc ltac:(left; exact (PNSRVA.arm18 L HI LY HIok MKE SRD))
  | disp PNSRVEP.vlJ19_conc ltac:(left; exact (PNSRVD.armDec L HI LY HIok MKE SRD RSZ DEC))
  | disp PNSRVEP.vlJ127_conc ltac:(left; exact (PNSRVS.armS2 L HI LY HIok MKE RSTR VAL))
  | disp PNSRVEP.vlJ255_conc ltac:(left; exact (PNSRVS.armS2 L HI LY HIok MKE RSTR VAL))
  | disp PNSRVEP.vlJz_conc ltac:(right; reflexivity)
  | disp PNSRVEP.vlJr1_conc ltac:(right; reflexivity)
  | disp PNSRVEP.vlJr2_conc ltac:(right; reflexivity) ].
Qed.

End WithHeap.
End PNSRVL.
