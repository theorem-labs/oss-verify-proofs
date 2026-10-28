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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnModelFacts PnStatics PnKeep PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj PnBrKit PnBrKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnBrKitS_u PnSRvK_u PnSRvA_u PnSRvSP_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSRVS.
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
Abbreviation brel := (PNBK.brel RSEGS AD AN L HI 8).
Abbreviation pot := (PNR.pot_bparser L).
Abbreviation rv_ctx := (PNSRVK.rv_ctx L).
Abbreviation rv_kont := (PNSRVK.rv_kont L HI).

Hypothesis MKE : PNRS.make_ec_spec L HI.
Hypothesis RSTR : PNRS.read_string_spec L HI.
Hypothesis VAL : PMS.validate_spec L.

Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac fd P := PMK.feed P ltac:(first [PMK.sc | unfold PNSRVSP.aligned; PMK.sc]).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma armS2 : PNSRVA.arm_stmt L HI 0x376bc.
Proof.
  intros t K LBX sp r fb cat e str R M model cr s sm ax fx5 R5 M5 model5 cr5 ax5 CTX KONT BR5 MID EC5.
  pose proof MID as (X2 & X3 & X4 & X8 & X9 & X18 & SV5 & SX5).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 BR5) as (PA5 & IA5 & GR5 & UN5 & STK5 & MOK5).
  change (PMSP.pm_scr 8) with 28672 in STK5. pose proof STK5 as (A16 & SLO & SHI & STOP & SDEF5). pose proof MOK5 as (Mh5 & Ml5 & Mm5).
  pose proof (L5C.stk_writable RSEGS _ M5 sp 28672 STK5) as WR5.
  (let T := type of (PNSRVSP.vlS2a_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVSP.vlS2a_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVSP.aligned; PMK.sc])).
  destruct P as (fx6 & R6 & M6 & MG6 & EQ6w & EQ6 & MS6 & KS6 & Y1 & Y10 & Y11).
  assert (EM6 : M6 = M5) by (apply functional_extensionality; exact EQ6w). subst M6.
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx5 fx6 R5 R6 _ _ M5 (fun _ => False) K
           ltac:(lia) BR5 FOK INCS MS6 MG6 ltac:(intros a Ha _; apply EQ6; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
  intros BR6.
  assert (MID6 : PNSRVK.rv_mid R R6 M5 sp r fb).
  { apply (PNSRVK.rv_mid_xfer R R5 R6 M5 M5 sp r fb _ MID KS6); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n _ _ i Hi; reflexivity| lia| lia]. }
  (* [comment removed for export] *)
  change (@PMSP.cfg RSEGS fx6 R6 0x3871c M5 model5) with (@PMSP.cfg RSEGS fx6 R6 (PNL.pn_read_string AN) M5 model5).
  pose proof RSTR as RSTR'. unfold PNRS.read_string_spec, PNR.read_string_spec in RSTR'.
  apply (PNSRVK.brel_call_fb L HI LY HIok false _ 7 (PNR.bargs_rs AD) (PNR.bprog_rs AD fb) LBX sp fb str _ M5 model5 cr5 s sm ax5 fx6 R6 (sp - 96) _ cat e K
           (RSTR' fb) ltac:(lia) K0 BR6 FOK INCS CRED Y1 ltac:(split; [lia| reflexivity])); [rewrite (KS6 2%nat) by PMK.inl; exact X2| rewrite (KS6 3%nat) by PMK.inl; exact X3| rewrite (KS6 4%nat) by PMK.inl; exact X4
    | lia| unfold PMSP.pm_scr; lia| exact (PNSRVK.mod16_sub176 sp A16)| | exact INV0| exact EC5| exact He| exact UNR0|].
  { unfold PNR.bargs_rs, PNR.o_p, PNR.o_ec, PMSP.o_p, PMSP.o_ec. cbn [pa_off_p pa_off_ec AD PnLayoutS_u.ADDR_S]. rewrite L5K.rl10, L5K.rl11. split; [exact Y10| exact Y11]. }
  intros fx7 R7 M7 model7 s7 sm7 ax7 cr7 RP67 POST BR7 AG67.
  assert (MID7 : PNSRVK.rv_mid R R7 M7 sp r fb) by (apply (PNSRVK.rv_mid_pres R R6 R7 M5 M7 sp r fb MID6 RP67); [intros a n H1 H2; apply AG67; lia| lia| lia]).
  pose proof MID7 as (W2 & W3 & W4 & W8 & W9 & W18 & SV7 & SX7).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model7 cr7 s7 sm7 ax7 BR7) as (PA7 & IA7 & GR7 & UN7 & STK7 & MOK7).
  change (PMSP.pm_scr 8) with 28672 in STK7. pose proof STK7 as (_ & _ & _ & _ & SDEF7). pose proof MOK7 as (Mh7 & Ml7 & Mm7).
  pose proof (L5C.stk_writable RSEGS _ M7 sp 28672 STK7) as WR7.
  pose proof POST as (_ & STEP7 & _ & DISJ & BBP). unfold PNR.o_ec, PMSP.o_ec in DISJ. cbn [pa_off_ec AD PnLayoutS_u.ADDR_S] in DISJ. cbn [PNR.bb_post] in BBP.
  pose proof (bv_unsigned_in_range _ (getr R7 (PMK.reg 10))) as BUR7_10. pose proof (bv_unsigned_in_range _ (getr R7 (PMK.reg 11))) as BUR7_11.
  (* [comment removed for export] *)
  assert (ECV : exists ecv, 0 <= ecv <= 64 /\ L5.u32_at RSEGS M7 (fb + 16) ecv /\ L5.defined M7 (fb + 16) 16
            /\ PNR.binv s7 /\ (length (PNM.b_stk s) <= length (PNM.b_stk s7))%nat
            /\ PNSRVK.rv_post fb cat e s sm R7 M7 s7 sm7 ax7
            /\ (ecv = 0 -> PMSP.ec_at RSEGS M7 (fb + 16) e cat /\ PNR.bprog_rs AD fb R7 M7 s s7 sm sm7)).
  { destruct DISJ as [(v & Hv & (E1 & E2 & E3) & MO & CAT & LEN & INV7)|(E0 & INV7 & PROG)].
    - exists v. split; [lia|]. split; [exact E1|]. split; [exact E3|]. split; [exact INV7|]. split; [exact LEN|].
      split; [| intros ->; lia]. split; [left; split; [exists v; split; [exact Hv| split; [exact E1| split; [exact E2| exact E3]]]|]; split; [exact MO|]; split; [exact CAT|]; split; [exact LEN| exact INV7]|].
      intros _ M1. rewrite MO in M1. lia.
    - exists e. pose proof E0 as (E1 & E2 & E3). split; [exact He|]. split; [exact E1|]. split; [exact E3|]. split; [exact INV7|].
      pose proof PROG as (TP & LE5 & _).
      assert (LEN : (length (PNM.b_stk s) <= length (PNM.b_stk s7))%nat) by (destruct TP as (l0 & c0 & c0' & Ea & Eb & _); rewrite Ea, Eb, !length_app; cbn; lia).
      split; [exact LEN|]. split; [| intros _; split; [exact E0| exact PROG]].
      split; [right; split; [exact E0|]; split; [exact INV7| left; exact TP]|].
      intros R0 _. unfold PNR.bb_room in *. rewrite BBP. apply (PGV8.v8_room_mono _ (PM.unread (PNM.b_src s) sm)); [lia| exact R0]. }
  destruct ECV as (ecv & Hecv & U32 & ED7 & INV7 & LEN7 & RVP7 & OKP).
  (let T := type of (PNSRVSP.vlS2b_conc fx7 R7 M7 (PNSRVK.tv sp r fb R (fun j => match j with 53%nat => bv_unsigned (getr R7 (PMK.reg 10)) | 54%nat => bv_unsigned (getr R7 (PMK.reg 11)) | 60%nat => ecv | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVSP.vlS2b_conc fx7 R7 M7 (PNSRVK.tv sp r fb R (fun j => match j with 53%nat => bv_unsigned (getr R7 (PMK.reg 10)) | 54%nat => bv_unsigned (getr R7 (PMK.reg 11)) | 60%nat => ecv | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVSP.aligned; PMK.sc | symmetry; apply Z_to_bv_bv_unsigned])).
  destruct P as (fx8 & R8 & M8 & MG8 & _ & FRZ8 & [(MS8 & KS8 & _ & LT & _ & _)|(MS8 & KS8 & Z1 & _ & LT & _ & _)]).
  - (* [comment removed for export] *)
    apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model7 cr7 s7 sm7 ax7 fx7 fx8 R7 R8 _ _ M8 (fun a => sp - 64 <= a < sp - 64 + 16) K
             ltac:(lia) BR7 FOK INCS MS8 MG8 FRZ8 ltac:(intros a; apply PMK.rng_dec) ltac:(intros a Pa; cbn beta in Pa; unfold PMSP.pm_scr; clear - Pa; lia)).
    intros BR8.
    assert (MID8 : PNSRVK.rv_mid R R8 M8 sp r fb).
    { apply (PNSRVK.rv_mid_xfer R R7 R8 M7 M8 sp r fb _ MID7 KS8); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n H1 H2 i Hi; apply FRZ8; lia| lia| lia]. }
    pose proof MID8 as (V2 & V3 & V4 & V8 & V9 & V18 & SV8 & SX8).
    apply (PNSRVK.rv_epi L HI LY HIok t K LBX sp r fb cat e str R M model cr s sm ax fx8 R8 M8 model7 cr7 s7 sm7 ax7 CTX KONT BR8 V2 V3 V4 V8 V9 V18 SV8 SX8).
    destruct RVP7 as (D7 & B7). split; [| exact B7].
    destruct D7 as [((v & Hv & E1) & REST)|(E0 & REST)].
    + left. split; [exists v; split; [exact Hv| apply (PNSRVK.ec_agree M7 M8); [intros i Hi; apply FRZ8; lia|lia|lia| exact E1]]| exact REST].
    + right. split; [apply (PNSRVK.ec_agree M7 M8); [intros i Hi; apply FRZ8; lia|lia|lia| exact E0]| exact REST].
  - (* [comment removed for export] *)
    rewrite Z.sub_0_r, Z.mod_small in LT by lia. destruct (OKP ltac:(lia)) as (EC7 & TP7 & LE7 & ptr & n & Q10 & Q11 & Hn & DEF7 & LOC). clear OKP.
    rewrite L5K.rl10 in Q10. rewrite L5K.rl11 in Q11. rewrite Q10, Q11 in *. rewrite !L5.unsigned_lit in * by lia.
    apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model7 cr7 s7 sm7 ax7 fx7 fx8 R7 R8 _ _ M8 (fun a => sp - 64 <= a < sp - 64 + 16) K
             ltac:(lia) BR7 FOK INCS MS8 MG8 FRZ8 ltac:(intros a; apply PMK.rng_dec) ltac:(intros a Pa; cbn beta in Pa; unfold PMSP.pm_scr; clear - Pa; lia)).
    intros BR8.
    assert (AG78 : forall a m, (a + m <= sp - 64 \/ sp - 48 <= a) -> 0 <= a -> a + m <= 2 ^ 64 -> L5C.agree_on M7 M8 a m) by (intros a m H0 H1 H2 i Hi; apply FRZ8; lia).
    assert (MID8 : PNSRVK.rv_mid R R8 M8 sp r fb).
    { apply (PNSRVK.rv_mid_xfer R R7 R8 M7 M8 sp r fb _ MID7 KS8); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a m H1 H2; apply AG78; lia| lia| lia]. }
    destruct (PNBK2.brel_blocks RSEGS AD AN L HI KH 8 LBX sp fb str _ M8 model7 cr7 s7 sm7 ax7 BR8) as (_ & OWNB8 & _).
    pose proof BR8 as ((_ & _ & _ & _ & BASE8 & _) & _ & _ & _ & _ & _ & HH8 & STK8 & _). cbn [PNBK.be_M PNBK.be_s PNBK.be_cr PNBK.be_model] in BASE8, HH8, STK8.
    change (PMSP.pm_scr 8) with 28672 in STK8.
    (* [comment removed for export] *)
    assert (PLOC : (n = 0 \/ 0 < ptr) /\ ptr + n <= 2 ^ 47 /\ 0 <= ptr /\ (n = 0 \/ sp - 96 <= ptr \/ ptr + n <= sp - 96 - 12288) /\ (ptr + n <= sp - 64 \/ sp - 48 <= ptr \/ n = 0)).
    { destruct LOC as [(-> & ->)|[(B & m & Hin & HB1 & HB2)|(T1 & T2)]]; [lia| | unfold PNR.o_tb, PNR.o_p, PMSP.o_p in T1, T2; cbn [pa_off_p AD PnLayoutS_u.ADDR_S] in T1, T2; unfold PNM.OFF_TB in *; lia].
      cbn [PNBO.set_stk PNM.with_srcB] in Hin. destruct (OWNB8 B m Hin) as (B0 & B4). unfold hl_ceil in B4. pose proof STK8 as (_ & SLO8 & _). lia. }
    destruct PLOC as (P1 & P2 & P3 & P4 & P5).
    assert (DEF8 : L5.defined M8 ptr n) by (destruct (Z.eq_dec n 0) as [->|Nn]; [intros i Hi; lia| apply (L5C.defined_agree M7 M8 ptr n); [apply AG78; lia| exact DEF7]]).
    change (@PMSP.cfg RSEGS fx8 R8 0x384bc M8 model7) with (@PMSP.cfg RSEGS fx8 R8 (pa_validate AD) M8 model7).
    pose proof VAL as VAL'. unfold PMS.validate_spec, PMSP.validate_spec, PMSP.scan_spec in VAL'.
    apply (VAL' fx8 R8 M8 model7 K ptr n (sp - 96) 0x376dc Mh7 Ml7 K0).
    { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact Z1|]. split; [split; [lia| reflexivity]|].
      split; [rewrite (KS8 2%nat) by PMK.inl; exact W2|]. split; [rewrite (KS8 3%nat) by PMK.inl; exact W3|]. split; [rewrite (KS8 4%nat) by PMK.inl; exact W4|].
      apply (PMK.stk_call L M8 sp 28672 (sp - 96) (PMSP.pm_scr 0) STK8); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia| exact (PNSRVK.mod16_sub176 sp A16)]. }
    { rewrite L5K.rl10. rewrite (KS8 10%nat) by PMK.inl. exact Q10. } { rewrite L5K.rl11. rewrite (KS8 11%nat) by PMK.inl. exact Q11. }
    { exact Hn. } { exact P3. } { exact P1. } { exact P2. } { exact DEF8. } { exact P4. } { exact BASE8. }
    intros fx9 R9 M9 RP89 FB9 MG9.
    assert (FRZ9 : forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 96 - 12288 <= i < sp - 96) -> M9 (Z_to_bv 64 i) = M8 (Z_to_bv 64 i)).
    { intros i Hi N. apply FB9. rewrite L5.unsigned_lit by exact Hi. intros r0 [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. apply N. unfold PMSP.pm_scr in Hr. lia. }
    pose proof (PNBK.brel_stack_only RSEGS AD AN L HI KH 8 LBX sp fb str _ M8 model7 cr7 s7 sm7 ax7 M9 (fun a => sp - 96 - 12288 <= a < sp - 96)
                  ltac:(lia) BR8 FOK INCS MG9 FRZ9 ltac:(intros a; apply PMK.rng_dec) ltac:(intros a Pa; cbn beta in Pa; unfold PMSP.pm_scr; clear -Pa; lia)) as BR9.
    assert (MID9 : PNSRVK.rv_mid R R9 M9 sp r fb) by (apply (PNSRVK.rv_mid_pres R R8 R9 M8 M9 sp r fb MID8 RP89); [intros a m H1 H2 i Hi; apply FRZ9; lia| lia| lia]).
    pose proof MID9 as (V2 & V3 & V4 & V8 & V9 & V18 & SV9 & SX9).
    destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M9 model7 cr7 s7 sm7 ax7 BR9) as (PA9 & _ & _ & _ & STK9 & _).
    change (PMSP.pm_scr 8) with 28672 in STK9. pose proof (L5C.stk_writable RSEGS _ M9 sp 28672 STK9) as WR9.
    pose proof PA9 as (_ & PD9 & _ & _ & _ & CM9 & _).
    pose proof BR9 as ((_ & _ & VIS9 & _ & BASE9 & _) & _). cbn [PNBK.be_M] in VIS9, BASE9.
    unfold PNR.o_v, PMSP.o_v, PMSP.visitor_at in VIS9. cbn [pa_off_v pa_vp_visitor AD PnLayoutS_u.ADDR_S] in VIS9.
    pose proof BASE9 as (IMG9 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG9.
    assert (EC9 : PMSP.ec_at RSEGS M9 (fb + 16) e cat).
    { apply (PNSRVK.ec_agree M8 M9); [intros i Hi; apply FRZ9; lia|lia|lia|]. apply (PNSRVK.ec_agree M7 M8); [apply AG78; lia|lia|lia| exact EC7]. }
    (* [comment removed for export] *)
    idtac. pose proof (bv_unsigned_in_range _ (getr R9 (PMK.reg 11))) as BUR9_11.
    (let T := type of (PNSRVSP.vlS2c_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 55%nat => bv_unsigned (getr R9 (PMK.reg 11)) | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVSP.vlS2c_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 55%nat => bv_unsigned (getr R9 (PMK.reg 11)) | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVSP.aligned; PMK.sc | symmetry; apply Z_to_bv_bv_unsigned])).
    destruct P as (fx10 & R10 & M10 & MG10 & EQ10w & EQ10 & [(MS10 & KS10)|(MS10 & KS10 & _ & Y10' & _)]);
      assert (EM10 : M10 = M9) by (apply functional_extensionality; exact EQ10w); subst M10.
    + (* [comment removed for export] *)
      apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M9 model7 cr7 s7 sm7 ax7 fx9 fx10 R9 R10 _ _ M9 (fun _ => False) K
               ltac:(lia) BR9 FOK INCS MS10 MG10 ltac:(intros a Ha _; apply EQ10; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
      intros BR10.
      apply (PNSRVK.rv_err L HI LY HIok MKE 0x37da0 3 t K LBX sp r fb cat e str R M model cr s sm ax fx10 R10 M9 model7 cr7 s7 sm7 ax7 ltac:(right; left; split; reflexivity) CTX KONT BR10);
        [| destruct EC9 as (_ & _ & ED9); exact ED9| exact LEN7| exact INV7].
      apply (PNSRVK.rv_mid_xfer R R9 R10 M9 M9 sp r fb _ MID9 KS10); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a m _ _ i Hi; reflexivity| lia| lia].
    + (* [comment removed for export] *)
      apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M9 model7 cr7 s7 sm7 ax7 fx9 fx10 R9 R10 _ _ M9 (fun _ => False) K
               ltac:(lia) BR9 FOK INCS MS10 MG10 ltac:(intros a Ha _; apply EQ10; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
      intros BR10.
      apply (PNSRVK.rv_sbmore L HI LY HIok t K LBX sp r fb cat e str R M model cr s sm ax fx10 R10 M9 model7 cr7 s7 sm7 ax7 1 CTX KONT BR10); [| exact Y10'|].
      * apply (PNSRVK.rv_mid_xfer R R9 R10 M9 M9 sp r fb _ MID9 KS10); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a m _ _ i Hi; reflexivity| lia| lia].
      * right. split; [reflexivity|]. split; [exact EC9|]. split; [exact INV7|]. split; [left; exact TP7|].
        intros R0. unfold PNR.bb_room in *. rewrite BBP. apply (PGV8.v8_room_mono _ (PM.unread (PNM.b_src s) sm)); [lia| exact R0].
Qed.

(* [comment removed for export] *)
Lemma armS13 : PNSRVA.arm_stmt L HI 0x37858.
Proof.
  intros t K LBX sp r fb cat e str R M model cr s sm ax fx5 R5 M5 model5 cr5 ax5 CTX KONT BR5 MID EC5.
  pose proof MID as (X2 & X3 & X4 & X8 & X9 & X18 & SV5 & SX5).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 BR5) as (PA5 & IA5 & GR5 & UN5 & STK5 & MOK5).
  change (PMSP.pm_scr 8) with 28672 in STK5. pose proof STK5 as (A16 & SLO & SHI & STOP & SDEF5). pose proof MOK5 as (Mh5 & Ml5 & Mm5).
  pose proof (L5C.stk_writable RSEGS _ M5 sp 28672 STK5) as WR5.
  (let T := type of (PNSRVSP.vlS13a_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVSP.vlS13a_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVSP.aligned; PMK.sc])).
  destruct P as (fx6 & R6 & M6 & MG6 & EQ6w & EQ6 & MS6 & KS6 & Y1 & Y10 & Y11).
  assert (EM6 : M6 = M5) by (apply functional_extensionality; exact EQ6w). subst M6.
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx5 fx6 R5 R6 _ _ M5 (fun _ => False) K
           ltac:(lia) BR5 FOK INCS MS6 MG6 ltac:(intros a Ha _; apply EQ6; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
  intros BR6.
  assert (MID6 : PNSRVK.rv_mid R R6 M5 sp r fb).
  { apply (PNSRVK.rv_mid_xfer R R5 R6 M5 M5 sp r fb _ MID KS6); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n _ _ i Hi; reflexivity| lia| lia]. }
  (* [comment removed for export] *)
  change (@PMSP.cfg RSEGS fx6 R6 0x3871c M5 model5) with (@PMSP.cfg RSEGS fx6 R6 (PNL.pn_read_string AN) M5 model5).
  pose proof RSTR as RSTR'. unfold PNRS.read_string_spec, PNR.read_string_spec in RSTR'.
  apply (PNSRVK.brel_call_fb L HI LY HIok false _ 7 (PNR.bargs_rs AD) (PNR.bprog_rs AD fb) LBX sp fb str _ M5 model5 cr5 s sm ax5 fx6 R6 (sp - 96) _ cat e K
           (RSTR' fb) ltac:(lia) K0 BR6 FOK INCS CRED Y1 ltac:(split; [lia| reflexivity])); [rewrite (KS6 2%nat) by PMK.inl; exact X2| rewrite (KS6 3%nat) by PMK.inl; exact X3| rewrite (KS6 4%nat) by PMK.inl; exact X4
    | lia| unfold PMSP.pm_scr; lia| exact (PNSRVK.mod16_sub176 sp A16)| | exact INV0| exact EC5| exact He| exact UNR0|].
  { unfold PNR.bargs_rs, PNR.o_p, PNR.o_ec, PMSP.o_p, PMSP.o_ec. cbn [pa_off_p pa_off_ec AD PnLayoutS_u.ADDR_S]. rewrite L5K.rl10, L5K.rl11. split; [exact Y10| exact Y11]. }
  intros fx7 R7 M7 model7 s7 sm7 ax7 cr7 RP67 POST BR7 AG67.
  assert (MID7 : PNSRVK.rv_mid R R7 M7 sp r fb) by (apply (PNSRVK.rv_mid_pres R R6 R7 M5 M7 sp r fb MID6 RP67); [intros a n H1 H2; apply AG67; lia| lia| lia]).
  pose proof MID7 as (W2 & W3 & W4 & W8 & W9 & W18 & SV7 & SX7).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model7 cr7 s7 sm7 ax7 BR7) as (PA7 & IA7 & GR7 & UN7 & STK7 & MOK7).
  change (PMSP.pm_scr 8) with 28672 in STK7. pose proof STK7 as (_ & _ & _ & _ & SDEF7). pose proof MOK7 as (Mh7 & Ml7 & Mm7).
  pose proof (L5C.stk_writable RSEGS _ M7 sp 28672 STK7) as WR7.
  pose proof POST as (_ & STEP7 & _ & DISJ & BBP). unfold PNR.o_ec, PMSP.o_ec in DISJ. cbn [pa_off_ec AD PnLayoutS_u.ADDR_S] in DISJ. cbn [PNR.bb_post] in BBP.
  pose proof (bv_unsigned_in_range _ (getr R7 (PMK.reg 10))) as BUR7_10. pose proof (bv_unsigned_in_range _ (getr R7 (PMK.reg 11))) as BUR7_11.
  (* [comment removed for export] *)
  assert (ECV : exists ecv, 0 <= ecv <= 64 /\ L5.u32_at RSEGS M7 (fb + 16) ecv /\ L5.defined M7 (fb + 16) 16
            /\ PNR.binv s7 /\ (length (PNM.b_stk s) <= length (PNM.b_stk s7))%nat
            /\ PNSRVK.rv_post fb cat e s sm R7 M7 s7 sm7 ax7
            /\ (ecv = 0 -> PMSP.ec_at RSEGS M7 (fb + 16) e cat /\ PNR.bprog_rs AD fb R7 M7 s s7 sm sm7)).
  { destruct DISJ as [(v & Hv & (E1 & E2 & E3) & MO & CAT & LEN & INV7)|(E0 & INV7 & PROG)].
    - exists v. split; [lia|]. split; [exact E1|]. split; [exact E3|]. split; [exact INV7|]. split; [exact LEN|].
      split; [| intros ->; lia]. split; [left; split; [exists v; split; [exact Hv| split; [exact E1| split; [exact E2| exact E3]]]|]; split; [exact MO|]; split; [exact CAT|]; split; [exact LEN| exact INV7]|].
      intros _ M1. rewrite MO in M1. lia.
    - exists e. pose proof E0 as (E1 & E2 & E3). split; [exact He|]. split; [exact E1|]. split; [exact E3|]. split; [exact INV7|].
      pose proof PROG as (TP & LE5 & _).
      assert (LEN : (length (PNM.b_stk s) <= length (PNM.b_stk s7))%nat) by (destruct TP as (l0 & c0 & c0' & Ea & Eb & _); rewrite Ea, Eb, !length_app; cbn; lia).
      split; [exact LEN|]. split; [| intros _; split; [exact E0| exact PROG]].
      split; [right; split; [exact E0|]; split; [exact INV7| left; exact TP]|].
      intros R0 _. unfold PNR.bb_room in *. rewrite BBP. apply (PGV8.v8_room_mono _ (PM.unread (PNM.b_src s) sm)); [lia| exact R0]. }
  destruct ECV as (ecv & Hecv & U32 & ED7 & INV7 & LEN7 & RVP7 & OKP).
  (let T := type of (PNSRVSP.vlS13b_conc fx7 R7 M7 (PNSRVK.tv sp r fb R (fun j => match j with 53%nat => bv_unsigned (getr R7 (PMK.reg 10)) | 54%nat => bv_unsigned (getr R7 (PMK.reg 11)) | 60%nat => ecv | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVSP.vlS13b_conc fx7 R7 M7 (PNSRVK.tv sp r fb R (fun j => match j with 53%nat => bv_unsigned (getr R7 (PMK.reg 10)) | 54%nat => bv_unsigned (getr R7 (PMK.reg 11)) | 60%nat => ecv | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVSP.aligned; PMK.sc | symmetry; apply Z_to_bv_bv_unsigned])).
  destruct P as (fx8 & R8 & M8 & MG8 & _ & FRZ8 & [(MS8 & KS8 & _ & LT & _ & _)|(MS8 & KS8 & Z1 & _ & LT & _ & _)]).
  - (* [comment removed for export] *)
    apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model7 cr7 s7 sm7 ax7 fx7 fx8 R7 R8 _ _ M8 (fun a => sp - 64 <= a < sp - 64 + 16) K
             ltac:(lia) BR7 FOK INCS MS8 MG8 FRZ8 ltac:(intros a; apply PMK.rng_dec) ltac:(intros a Pa; cbn beta in Pa; unfold PMSP.pm_scr; clear - Pa; lia)).
    intros BR8.
    assert (MID8 : PNSRVK.rv_mid R R8 M8 sp r fb).
    { apply (PNSRVK.rv_mid_xfer R R7 R8 M7 M8 sp r fb _ MID7 KS8); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n H1 H2 i Hi; apply FRZ8; lia| lia| lia]. }
    pose proof MID8 as (V2 & V3 & V4 & V8 & V9 & V18 & SV8 & SX8).
    apply (PNSRVK.rv_epi L HI LY HIok t K LBX sp r fb cat e str R M model cr s sm ax fx8 R8 M8 model7 cr7 s7 sm7 ax7 CTX KONT BR8 V2 V3 V4 V8 V9 V18 SV8 SX8).
    destruct RVP7 as (D7 & B7). split; [| exact B7].
    destruct D7 as [((v & Hv & E1) & REST)|(E0 & REST)].
    + left. split; [exists v; split; [exact Hv| apply (PNSRVK.ec_agree M7 M8); [intros i Hi; apply FRZ8; lia|lia|lia| exact E1]]| exact REST].
    + right. split; [apply (PNSRVK.ec_agree M7 M8); [intros i Hi; apply FRZ8; lia|lia|lia| exact E0]| exact REST].
  - (* [comment removed for export] *)
    rewrite Z.sub_0_r, Z.mod_small in LT by lia. destruct (OKP ltac:(lia)) as (EC7 & TP7 & LE7 & ptr & n & Q10 & Q11 & Hn & DEF7 & LOC). clear OKP.
    rewrite L5K.rl10 in Q10. rewrite L5K.rl11 in Q11. rewrite Q10, Q11 in *. rewrite !L5.unsigned_lit in * by lia.
    apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model7 cr7 s7 sm7 ax7 fx7 fx8 R7 R8 _ _ M8 (fun a => sp - 64 <= a < sp - 64 + 16) K
             ltac:(lia) BR7 FOK INCS MS8 MG8 FRZ8 ltac:(intros a; apply PMK.rng_dec) ltac:(intros a Pa; cbn beta in Pa; unfold PMSP.pm_scr; clear - Pa; lia)).
    intros BR8.
    assert (AG78 : forall a m, (a + m <= sp - 64 \/ sp - 48 <= a) -> 0 <= a -> a + m <= 2 ^ 64 -> L5C.agree_on M7 M8 a m) by (intros a m H0 H1 H2 i Hi; apply FRZ8; lia).
    assert (MID8 : PNSRVK.rv_mid R R8 M8 sp r fb).
    { apply (PNSRVK.rv_mid_xfer R R7 R8 M7 M8 sp r fb _ MID7 KS8); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a m H1 H2; apply AG78; lia| lia| lia]. }
    destruct (PNBK2.brel_blocks RSEGS AD AN L HI KH 8 LBX sp fb str _ M8 model7 cr7 s7 sm7 ax7 BR8) as (_ & OWNB8 & _).
    pose proof BR8 as ((_ & _ & _ & _ & BASE8 & _) & _ & _ & _ & _ & _ & HH8 & STK8 & _). cbn [PNBK.be_M PNBK.be_s PNBK.be_cr PNBK.be_model] in BASE8, HH8, STK8.
    change (PMSP.pm_scr 8) with 28672 in STK8.
    (* [comment removed for export] *)
    assert (PLOC : (n = 0 \/ 0 < ptr) /\ ptr + n <= 2 ^ 47 /\ 0 <= ptr /\ (n = 0 \/ sp - 96 <= ptr \/ ptr + n <= sp - 96 - 12288) /\ (ptr + n <= sp - 64 \/ sp - 48 <= ptr \/ n = 0)).
    { destruct LOC as [(-> & ->)|[(B & m & Hin & HB1 & HB2)|(T1 & T2)]]; [lia| | unfold PNR.o_tb, PNR.o_p, PMSP.o_p in T1, T2; cbn [pa_off_p AD PnLayoutS_u.ADDR_S] in T1, T2; unfold PNM.OFF_TB in *; lia].
      cbn [PNBO.set_stk PNM.with_srcB] in Hin. destruct (OWNB8 B m Hin) as (B0 & B4). unfold hl_ceil in B4. pose proof STK8 as (_ & SLO8 & _). lia. }
    destruct PLOC as (P1 & P2 & P3 & P4 & P5).
    assert (DEF8 : L5.defined M8 ptr n) by (destruct (Z.eq_dec n 0) as [->|Nn]; [intros i Hi; lia| apply (L5C.defined_agree M7 M8 ptr n); [apply AG78; lia| exact DEF7]]).
    change (@PMSP.cfg RSEGS fx8 R8 0x384bc M8 model7) with (@PMSP.cfg RSEGS fx8 R8 (pa_validate AD) M8 model7).
    pose proof VAL as VAL'. unfold PMS.validate_spec, PMSP.validate_spec, PMSP.scan_spec in VAL'.
    apply (VAL' fx8 R8 M8 model7 K ptr n (sp - 96) 0x37878 Mh7 Ml7 K0).
    { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact Z1|]. split; [split; [lia| reflexivity]|].
      split; [rewrite (KS8 2%nat) by PMK.inl; exact W2|]. split; [rewrite (KS8 3%nat) by PMK.inl; exact W3|]. split; [rewrite (KS8 4%nat) by PMK.inl; exact W4|].
      apply (PMK.stk_call L M8 sp 28672 (sp - 96) (PMSP.pm_scr 0) STK8); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia| exact (PNSRVK.mod16_sub176 sp A16)]. }
    { rewrite L5K.rl10. rewrite (KS8 10%nat) by PMK.inl. exact Q10. } { rewrite L5K.rl11. rewrite (KS8 11%nat) by PMK.inl. exact Q11. }
    { exact Hn. } { exact P3. } { exact P1. } { exact P2. } { exact DEF8. } { exact P4. } { exact BASE8. }
    intros fx9 R9 M9 RP89 FB9 MG9.
    assert (FRZ9 : forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 96 - 12288 <= i < sp - 96) -> M9 (Z_to_bv 64 i) = M8 (Z_to_bv 64 i)).
    { intros i Hi N. apply FB9. rewrite L5.unsigned_lit by exact Hi. intros r0 [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. apply N. unfold PMSP.pm_scr in Hr. lia. }
    pose proof (PNBK.brel_stack_only RSEGS AD AN L HI KH 8 LBX sp fb str _ M8 model7 cr7 s7 sm7 ax7 M9 (fun a => sp - 96 - 12288 <= a < sp - 96)
                  ltac:(lia) BR8 FOK INCS MG9 FRZ9 ltac:(intros a; apply PMK.rng_dec) ltac:(intros a Pa; cbn beta in Pa; unfold PMSP.pm_scr; clear -Pa; lia)) as BR9.
    assert (MID9 : PNSRVK.rv_mid R R9 M9 sp r fb) by (apply (PNSRVK.rv_mid_pres R R8 R9 M8 M9 sp r fb MID8 RP89); [intros a m H1 H2 i Hi; apply FRZ9; lia| lia| lia]).
    pose proof MID9 as (V2 & V3 & V4 & V8 & V9 & V18 & SV9 & SX9).
    destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M9 model7 cr7 s7 sm7 ax7 BR9) as (PA9 & _ & _ & _ & STK9 & _).
    change (PMSP.pm_scr 8) with 28672 in STK9. pose proof (L5C.stk_writable RSEGS _ M9 sp 28672 STK9) as WR9.
    pose proof PA9 as (_ & PD9 & _ & _ & _ & CM9 & _).
    pose proof BR9 as ((_ & _ & VIS9 & _ & BASE9 & _) & _). cbn [PNBK.be_M] in VIS9, BASE9.
    unfold PNR.o_v, PMSP.o_v, PMSP.visitor_at in VIS9. cbn [pa_off_v pa_vp_visitor AD PnLayoutS_u.ADDR_S] in VIS9.
    pose proof BASE9 as (IMG9 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG9.
    assert (EC9 : PMSP.ec_at RSEGS M9 (fb + 16) e cat).
    { apply (PNSRVK.ec_agree M8 M9); [intros i Hi; apply FRZ9; lia|lia|lia|]. apply (PNSRVK.ec_agree M7 M8); [apply AG78; lia|lia|lia| exact EC7]. }
    (* [comment removed for export] *)
    idtac. pose proof (bv_unsigned_in_range _ (getr R9 (PMK.reg 11))) as BUR9_11.
    (let T := type of (PNSRVSP.vlS13c_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 55%nat => bv_unsigned (getr R9 (PMK.reg 11)) | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVSP.vlS13c_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 55%nat => bv_unsigned (getr R9 (PMK.reg 11)) | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVSP.aligned; PMK.sc | symmetry; apply Z_to_bv_bv_unsigned])).
    destruct P as (fx10 & R10 & M10 & MG10 & EQ10w & EQ10 & [(MS10 & KS10)|(MS10 & KS10 & _ & Y10' & _)]);
      assert (EM10 : M10 = M9) by (apply functional_extensionality; exact EQ10w); subst M10.
    + (* [comment removed for export] *)
      apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M9 model7 cr7 s7 sm7 ax7 fx9 fx10 R9 R10 _ _ M9 (fun _ => False) K
               ltac:(lia) BR9 FOK INCS MS10 MG10 ltac:(intros a Ha _; apply EQ10; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
      intros BR10.
      apply (PNSRVK.rv_err L HI LY HIok MKE 0x37da0 3 t K LBX sp r fb cat e str R M model cr s sm ax fx10 R10 M9 model7 cr7 s7 sm7 ax7 ltac:(right; left; split; reflexivity) CTX KONT BR10);
        [| destruct EC9 as (_ & _ & ED9); exact ED9| exact LEN7| exact INV7].
      apply (PNSRVK.rv_mid_xfer R R9 R10 M9 M9 sp r fb _ MID9 KS10); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a m _ _ i Hi; reflexivity| lia| lia].
    + (* [comment removed for export] *)
      apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M9 model7 cr7 s7 sm7 ax7 fx9 fx10 R9 R10 _ _ M9 (fun _ => False) K
               ltac:(lia) BR9 FOK INCS MS10 MG10 ltac:(intros a Ha _; apply EQ10; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
      intros BR10.
      apply (PNSRVK.rv_sbmore L HI LY HIok t K LBX sp r fb cat e str R M model cr s sm ax fx10 R10 M9 model7 cr7 s7 sm7 ax7 1 CTX KONT BR10); [| exact Y10'|].
      * apply (PNSRVK.rv_mid_xfer R R9 R10 M9 M9 sp r fb _ MID9 KS10); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a m _ _ i Hi; reflexivity| lia| lia].
      * right. split; [reflexivity|]. split; [exact EC9|]. split; [exact INV7|]. split; [left; exact TP7|].
        intros R0. unfold PNR.bb_room in *. rewrite BBP. apply (PGV8.v8_room_mono _ (PM.unread (PNM.b_src s) sm)); [lia| exact R0].
Qed.

End WithHeap.
End PNSRVS.
