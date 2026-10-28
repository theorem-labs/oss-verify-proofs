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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnModelFacts PnStatics PnKeep PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj PnBrKit PnBrKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnBrKitS_u PnSRvK_u PnSRvAP_u PnSRvCP_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSRVA.
Import PMS.
Abbreviation AN := PnLayoutS_u.NADDR_S.
Abbreviation mem := (word -> option byte).
Abbreviation bparser_at := (PNM.bparser_at RSEGS AD PMSP.T3 PMSP.T4 (pa_vp_parser AD)).
Abbreviation BENT := PNBK.BENT.

Lemma lt_of_mod d k : 0 <= d <= k -> k < 2 ^ 63 -> 1 <= (d - k) mod 2 ^ 64 -> d < k.
Proof. intros H1 H2 H3. destruct (Z.eq_dec d k) as [E|N]; [| lia]. subst d. rewrite Z.sub_diag in H3. rewrite Z.mod_0_l in H3 by lia. lia. Qed.
Lemma eq_of_mod d k : 0 <= d <= k -> k < 2 ^ 63 -> (d - k) mod 2 ^ 64 < 1 -> d = k.
Proof.
  intros H1 H2 H3. destruct (Z.eq_dec d k) as [E|N]; [exact E|]. exfalso.
  rewrite <- (Z.mod_add (d - k) 1 (2 ^ 64)) in H3 by lia. rewrite Z.mod_small in H3 by lia. lia.
Qed.

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
Hypothesis SRD : PNRS.src_read_spec L HI.

Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac fd P := PMK.feed P ltac:(first [PMK.sc | unfold PNSRVAP.aligned; PMK.sc]).
Local Ltac ktac KS := intros k Hk; apply KS; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto.

(* [comment removed for export] *)
Definition arm_stmt (pc : Z) : Prop :=
  forall t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax (fx5 : FPState) R5 (M5 : mem) model5 cr5 ax5,
  rv_ctx t K LBX sp r fb e str R cr s sm -> rv_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M5 model5 cr5 s sm ax5) ->
  PNSRVK.rv_mid R R5 M5 sp r fb -> PMSP.ec_at RSEGS M5 (fb + 16) e cat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 pc M5 model5) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma arm1 : arm_stmt 0x3763c.
Proof.
  intros t K LBX sp r fb cat e str R M model cr s sm ax fx5 R5 M5 model5 cr5 ax5 CTX KONT BR5 MID EC5.
  pose proof MID as (X2 & X3 & X4 & X8 & X9 & X18 & SV5 & SX5).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 BR5) as (PA5 & IA5 & GR5 & UN5 & STK5 & MOK5).
  change (PMSP.pm_scr 8) with 28672 in STK5. pose proof STK5 as (A16 & SLO & SHI & STOP & SDEF5). pose proof MOK5 as (Mh5 & Ml5 & Mm5).
  pose proof (L5C.stk_writable RSEGS _ M5 sp 28672 STK5) as WR5.
  (let T := type of (PNSRVAP.vlA1_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVAP.vlA1_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVAP.aligned; PMK.sc])).
  destruct P as (fx6 & R6 & M6 & MG6 & EQ6w & EQ6 & MS6 & KS6 & Y1 & Y10 & Y11 & Y12).
  assert (EM6 : M6 = M5) by (apply functional_extensionality; exact EQ6w). subst M6.
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx5 fx6 R5 R6 _ _ M5 (fun _ => False) K
           ltac:(lia) BR5 FOK INCS MS6 MG6 ltac:(intros a Ha _; apply EQ6; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
  intros BR6.
  (* [comment removed for export] *)
  change (@PMSP.cfg RSEGS fx6 R6 0x370d0 M5 model5) with (@PMSP.cfg RSEGS fx6 R6 (pa_src_read AD) M5 model5).
  pose proof SRD as SRD'. unfold PNRS.src_read_spec, PNR.src_read_spec in SRD'.
  apply (PNBK.brel_src_read RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx6 R6 (sp - 96) _ (sp - 64) 8 K SRD' ltac:(lia) K0 BR6 FOK INCS Y1
           ltac:(split; [lia| reflexivity])); [rewrite (KS6 2%nat) by PMK.inl; exact X2| rewrite (KS6 3%nat) by PMK.inl; exact X3| rewrite (KS6 4%nat) by PMK.inl; exact X4
    | replace (fb + 56) with (fb + 40 + 16) by lia; exact Y10| exact Y11| exact Y12| lia| unfold PMSP.pm_scr; lia| exact (PNSRVK.mod16_sub176 sp A16)| lia| lia| lia|].
  intros fx7 R7 M7 src7 sm7 d RP67 Z10 Hd UNR7 DEF7 BR7 AG67.
  set (s7 := PNM.with_srcB s src7) in *.
  assert (MID7 : PNSRVK.rv_mid R R7 M7 sp r fb).
  { apply (PNSRVK.rv_mid_pres R R6 R7 M5 M7 sp r fb); [| exact RP67| intros a n H1 H2; apply AG67; lia| lia| lia].
    apply (PNSRVK.rv_mid_xfer R R5 R6 M5 M5 sp r fb _ MID KS6); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n _ _ i Hi; reflexivity| lia| lia]. }
  pose proof MID7 as (W2 & W3 & W4 & W8 & W9 & W18 & SV7 & SX7).
  assert (EC7 : PMSP.ec_at RSEGS M7 (fb + 16) e cat) by (apply (PNSRVK.ec_agree M5 M7); [apply AG67; lia|lia|lia| exact EC5]).
  assert (INV7 : PNR.binv s7) by (destruct INV0 as (ID & SH); split; [exact ID| exact SH]).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model5 cr5 s7 sm7 ax5 BR7) as (PA7 & IA7 & GR7 & UN7 & STK7 & MOK7).
  change (PMSP.pm_scr 8) with 28672 in STK7. pose proof STK7 as (_ & _ & _ & _ & SDEF7).
  pose proof (L5C.stk_writable RSEGS _ M7 sp 28672 STK7) as WR7.
  pose proof PA7 as (_ & PD7 & VIS7' & _ & _ & CM7 & _).
  pose proof BR7 as ((_ & _ & VIS7 & _ & BASE7 & _) & _). cbn [PNBK.be_M] in VIS7, BASE7.
  unfold PNR.o_v, PMSP.o_v, PMSP.visitor_at in VIS7. cbn [pa_off_v pa_vp_visitor AD PnLayoutS_u.ADDR_S] in VIS7.
  pose proof BASE7 as (IMG7 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG7.
  destruct (PNSRVK.rv_top L HI LY HIok LBX sp fb str _ M7 model5 cr5 s7 sm7 ax5 BR7 INV7) as (l & c & ES & OKc & UE & UP & WP & E0 & E1 & EI & EA).
  cbn [s7 PNM.with_srcB PNM.b_stk PNM.b_sb] in ES, UE, UP, WP, E0, E1, EI, EA.
  set (et := PNM.b_sb s + 40 * Z.of_nat (length l)) in *.
  pose proof OKc as (_ & _ & POS & _).
  assert (DEFB : L5.defined M7 (sp - 64) 8) by (apply (L5.defined_sub M7 (sp - 28672) 28672); [exact SDEF7| lia| lia]).
  assert (OKc' : PNM.bstate_ok (PNM.BS (PNM.bs_mode c) (PNM.bs_len c) ((d + PNM.bs_pos c) mod 2 ^ 64) (PNM.bs_type c) (PNM.bs_idx c)))
    by (unfold PNM.bstate_ok in OKc |- *; cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx]; pose proof (Z.mod_pos_bound (d + PNM.bs_pos c) (2 ^ 64) ltac:(lia)); lia).
  (let T := type of (PNSRVAP.vlB1_conc fx7 R7 M7 (PNSRVK.tv sp r fb R (fun j => match j with 50%nat => d | 51%nat => et + 40 | 52%nat => PNM.bs_pos c | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVAP.vlB1_conc fx7 R7 M7 (PNSRVK.tv sp r fb R (fun j => match j with 50%nat => d | 51%nat => et + 40 | 52%nat => PNM.bs_pos c | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVAP.aligned; PMK.sc])).
  destruct P as (fx8 & R8 & M8 & MG8 & _ & FRZ8 & [(MS8 & KS8 & _ & _ & _ & LT & CP8)|(MS8 & KS8 & Y1' & Y10' & _ & _ & _ & _ & LT & CP8)]).
  - (* [comment removed for export] *)
    pose proof (lt_of_mod d 8 Hd ltac:(lia) LT) as Hd8.
    apply (PNBK2.brel_piece_pos RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model5 cr5 s7 sm7 ax5 fx7 fx8 R7 R8 _ _ M8
             (fun a => et + 40 - 24 <= a < et + 40 - 24 + 8) l c ((d + PNM.bs_pos c) mod 2 ^ 64) K ltac:(lia) BR7 FOK INCS MS8 MG8 FRZ8 ltac:(intros a; apply PMK.rng_dec) ES);
      [intros a Pa; right; cbn [s7 PNM.with_srcB PNM.b_sb]; unfold et in Pa; clear - Pa; lia
      | cbn [s7 PNM.with_srcB PNM.b_sb]; replace (PNM.b_sb s + 40 * Z.of_nat (length l) + 16) with (et + 40 - 24) by (unfold et; lia); exact CP8
      | apply Z.mod_pos_bound; lia |].
    intros BR8.
    apply (PNSRVK.rv_err L HI LY HIok MKE 0x37d98 1 t K LBX sp r fb cat e str R M model cr s sm ax fx8 R8 M8 model5 cr5 _ sm7 ax5 ltac:(left; split; reflexivity) CTX KONT BR8).
    + apply (PNSRVK.rv_mid_xfer R R7 R8 M7 M8 sp r fb _ MID7 KS8); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| | lia| lia].
      intros a n H1 H2 i Hi. apply FRZ8; lia.
    + destruct EC7 as (_ & _ & ED7). apply (L5C.defined_agree M7 M8 (fb + 16) 16); [intros i Hi; apply FRZ8; lia| exact ED7].
    + cbn [PNBO.set_stk PNM.b_stk s7 PNM.with_srcB]. rewrite ES, !length_app. cbn. lia.
    + apply (PNBK2.binv_set_stk_top _ l c); [exact INV7| exact ES| exact OKc'| reflexivity].
  - (* [comment removed for export] *)
    pose proof (eq_of_mod d 8 Hd ltac:(lia) LT) as Hd8.
    apply (PNBK2.brel_piece_pos RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model5 cr5 s7 sm7 ax5 fx7 fx8 R7 R8 _ _ M8
             (fun a => et + 40 - 24 <= a < et + 40 - 24 + 8) l c ((d + PNM.bs_pos c) mod 2 ^ 64) K ltac:(lia) BR7 FOK INCS MS8 MG8 FRZ8 ltac:(intros a; apply PMK.rng_dec) ES);
      [intros a Pa; right; cbn [s7 PNM.with_srcB PNM.b_sb]; unfold et in Pa; clear - Pa; lia
      | cbn [s7 PNM.with_srcB PNM.b_sb]; replace (PNM.b_sb s + 40 * Z.of_nat (length l) + 16) with (et + 40 - 24) by (unfold et; lia); exact CP8
      | apply Z.mod_pos_bound; lia |].
    intros BR8.
    apply (PNSRVK.rv_sbmore L HI LY HIok t K LBX sp r fb cat e str R M model cr s sm ax fx8 R8 M8 model5 cr5 _ sm7 ax5 1 CTX KONT BR8); [| exact Y10'|].
    + apply (PNSRVK.rv_mid_xfer R R7 R8 M7 M8 sp r fb _ MID7 KS8); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| | lia| lia].
      intros a n H1 H2 i Hi. apply FRZ8; lia.
    + right. split; [reflexivity|].
      split; [apply (PNSRVK.ec_agree M7 M8); [intros i Hi; apply FRZ8; lia|lia|lia| exact EC7]|].
      split; [apply (PNBK2.binv_set_stk_top _ l c); [exact INV7| exact ES| exact OKc'| reflexivity]|].
      split.
      * left. exists l, c, (PNM.BS (PNM.bs_mode c) (PNM.bs_len c) ((d + PNM.bs_pos c) mod 2 ^ 64) (PNM.bs_type c) (PNM.bs_idx c)). cbn [PNBO.set_stk PNM.b_stk s7 PNM.with_srcB].
        split; [exact ES|]. split; [reflexivity|]. split; [exact OKc'|]. cbn [PNM.bs_mode PNM.bs_len PNM.bs_type PNM.bs_idx]. repeat split; reflexivity.
      * intros R0. unfold PNR.bb_room in *. cbn [PNBO.set_stk PNM.b_bb PNM.b_src s7 PNM.with_srcB]. apply (PGV8.v8_room_mono _ (PM.unread (PNM.b_src s) sm)); [lia| exact R0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma arm9 : arm_stmt 0x37804.
Proof.
  intros t K LBX sp r fb cat e str R M model cr s sm ax fx5 R5 M5 model5 cr5 ax5 CTX KONT BR5 MID EC5.
  pose proof MID as (X2 & X3 & X4 & X8 & X9 & X18 & SV5 & SX5).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 BR5) as (PA5 & IA5 & GR5 & UN5 & STK5 & MOK5).
  change (PMSP.pm_scr 8) with 28672 in STK5. pose proof STK5 as (A16 & SLO & SHI & STOP & SDEF5). pose proof MOK5 as (Mh5 & Ml5 & Mm5).
  pose proof (L5C.stk_writable RSEGS _ M5 sp 28672 STK5) as WR5.
  (let T := type of (PNSRVAP.vlA9_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVAP.vlA9_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVAP.aligned; PMK.sc])).
  destruct P as (fx6 & R6 & M6 & MG6 & EQ6w & EQ6 & MS6 & KS6 & Y1 & Y10 & Y11 & Y12).
  assert (EM6 : M6 = M5) by (apply functional_extensionality; exact EQ6w). subst M6.
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx5 fx6 R5 R6 _ _ M5 (fun _ => False) K
           ltac:(lia) BR5 FOK INCS MS6 MG6 ltac:(intros a Ha _; apply EQ6; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
  intros BR6.
  (* [comment removed for export] *)
  change (@PMSP.cfg RSEGS fx6 R6 0x370d0 M5 model5) with (@PMSP.cfg RSEGS fx6 R6 (pa_src_read AD) M5 model5).
  pose proof SRD as SRD'. unfold PNRS.src_read_spec, PNR.src_read_spec in SRD'.
  apply (PNBK.brel_src_read RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx6 R6 (sp - 96) _ (sp - 64) 8 K SRD' ltac:(lia) K0 BR6 FOK INCS Y1
           ltac:(split; [lia| reflexivity])); [rewrite (KS6 2%nat) by PMK.inl; exact X2| rewrite (KS6 3%nat) by PMK.inl; exact X3| rewrite (KS6 4%nat) by PMK.inl; exact X4
    | replace (fb + 56) with (fb + 40 + 16) by lia; exact Y10| exact Y11| exact Y12| lia| unfold PMSP.pm_scr; lia| exact (PNSRVK.mod16_sub176 sp A16)| lia| lia| lia|].
  intros fx7 R7 M7 src7 sm7 d RP67 Z10 Hd UNR7 DEF7 BR7 AG67.
  set (s7 := PNM.with_srcB s src7) in *.
  assert (MID7 : PNSRVK.rv_mid R R7 M7 sp r fb).
  { apply (PNSRVK.rv_mid_pres R R6 R7 M5 M7 sp r fb); [| exact RP67| intros a n H1 H2; apply AG67; lia| lia| lia].
    apply (PNSRVK.rv_mid_xfer R R5 R6 M5 M5 sp r fb _ MID KS6); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n _ _ i Hi; reflexivity| lia| lia]. }
  pose proof MID7 as (W2 & W3 & W4 & W8 & W9 & W18 & SV7 & SX7).
  assert (EC7 : PMSP.ec_at RSEGS M7 (fb + 16) e cat) by (apply (PNSRVK.ec_agree M5 M7); [apply AG67; lia|lia|lia| exact EC5]).
  assert (INV7 : PNR.binv s7) by (destruct INV0 as (ID & SH); split; [exact ID| exact SH]).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model5 cr5 s7 sm7 ax5 BR7) as (PA7 & IA7 & GR7 & UN7 & STK7 & MOK7).
  change (PMSP.pm_scr 8) with 28672 in STK7. pose proof STK7 as (_ & _ & _ & _ & SDEF7).
  pose proof (L5C.stk_writable RSEGS _ M7 sp 28672 STK7) as WR7.
  pose proof PA7 as (_ & PD7 & VIS7' & _ & _ & CM7 & _).
  pose proof BR7 as ((_ & _ & VIS7 & _ & BASE7 & _) & _). cbn [PNBK.be_M] in VIS7, BASE7.
  unfold PNR.o_v, PMSP.o_v, PMSP.visitor_at in VIS7. cbn [pa_off_v pa_vp_visitor AD PnLayoutS_u.ADDR_S] in VIS7.
  pose proof BASE7 as (IMG7 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG7.
  destruct (PNSRVK.rv_top L HI LY HIok LBX sp fb str _ M7 model5 cr5 s7 sm7 ax5 BR7 INV7) as (l & c & ES & OKc & UE & UP & WP & E0 & E1 & EI & EA).
  cbn [s7 PNM.with_srcB PNM.b_stk PNM.b_sb] in ES, UE, UP, WP, E0, E1, EI, EA.
  set (et := PNM.b_sb s + 40 * Z.of_nat (length l)) in *.
  pose proof OKc as (_ & _ & POS & _).
  assert (DEFB : L5.defined M7 (sp - 64) 8) by (apply (L5.defined_sub M7 (sp - 28672) 28672); [exact SDEF7| lia| lia]).
  assert (OKc' : PNM.bstate_ok (PNM.BS (PNM.bs_mode c) (PNM.bs_len c) ((d + PNM.bs_pos c) mod 2 ^ 64) (PNM.bs_type c) (PNM.bs_idx c)))
    by (unfold PNM.bstate_ok in OKc |- *; cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx]; pose proof (Z.mod_pos_bound (d + PNM.bs_pos c) (2 ^ 64) ltac:(lia)); lia).
  (let T := type of (PNSRVAP.vlB9_conc fx7 R7 M7 (PNSRVK.tv sp r fb R (fun j => match j with 50%nat => d | 51%nat => et + 40 | 52%nat => PNM.bs_pos c | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVAP.vlB9_conc fx7 R7 M7 (PNSRVK.tv sp r fb R (fun j => match j with 50%nat => d | 51%nat => et + 40 | 52%nat => PNM.bs_pos c | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVAP.aligned; PMK.sc])).
  destruct P as (fx8 & R8 & M8 & MG8 & _ & FRZ8 & [(MS8 & KS8 & _ & _ & _ & LT & CP8)|(MS8 & KS8 & Y1' & Y10' & _ & _ & _ & _ & _ & LT & CP8)]).
  - (* [comment removed for export] *)
    pose proof (lt_of_mod d 8 Hd ltac:(lia) LT) as Hd8.
    apply (PNBK2.brel_piece_pos RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model5 cr5 s7 sm7 ax5 fx7 fx8 R7 R8 _ _ M8
             (fun a => et + 40 - 24 <= a < et + 40 - 24 + 8) l c ((d + PNM.bs_pos c) mod 2 ^ 64) K ltac:(lia) BR7 FOK INCS MS8 MG8 FRZ8 ltac:(intros a; apply PMK.rng_dec) ES);
      [intros a Pa; right; cbn [s7 PNM.with_srcB PNM.b_sb]; unfold et in Pa; clear - Pa; lia
      | cbn [s7 PNM.with_srcB PNM.b_sb]; replace (PNM.b_sb s + 40 * Z.of_nat (length l) + 16) with (et + 40 - 24) by (unfold et; lia); exact CP8
      | apply Z.mod_pos_bound; lia |].
    intros BR8.
    apply (PNSRVK.rv_err L HI LY HIok MKE 0x37d98 1 t K LBX sp r fb cat e str R M model cr s sm ax fx8 R8 M8 model5 cr5 _ sm7 ax5 ltac:(left; split; reflexivity) CTX KONT BR8).
    + apply (PNSRVK.rv_mid_xfer R R7 R8 M7 M8 sp r fb _ MID7 KS8); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| | lia| lia].
      intros a n H1 H2 i Hi. apply FRZ8; lia.
    + destruct EC7 as (_ & _ & ED7). apply (L5C.defined_agree M7 M8 (fb + 16) 16); [intros i Hi; apply FRZ8; lia| exact ED7].
    + cbn [PNBO.set_stk PNM.b_stk s7 PNM.with_srcB]. rewrite ES, !length_app. cbn. lia.
    + apply (PNBK2.binv_set_stk_top _ l c); [exact INV7| exact ES| exact OKc'| reflexivity].
  - (* [comment removed for export] *)
    pose proof (eq_of_mod d 8 Hd ltac:(lia) LT) as Hd8.
    apply (PNBK2.brel_piece_pos RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model5 cr5 s7 sm7 ax5 fx7 fx8 R7 R8 _ _ M8
             (fun a => et + 40 - 24 <= a < et + 40 - 24 + 8) l c ((d + PNM.bs_pos c) mod 2 ^ 64) K ltac:(lia) BR7 FOK INCS MS8 MG8 FRZ8 ltac:(intros a; apply PMK.rng_dec) ES);
      [intros a Pa; right; cbn [s7 PNM.with_srcB PNM.b_sb]; unfold et in Pa; clear - Pa; lia
      | cbn [s7 PNM.with_srcB PNM.b_sb]; replace (PNM.b_sb s + 40 * Z.of_nat (length l) + 16) with (et + 40 - 24) by (unfold et; lia); exact CP8
      | apply Z.mod_pos_bound; lia |].
    intros BR8.
    apply (PNSRVK.rv_sbmore L HI LY HIok t K LBX sp r fb cat e str R M model cr s sm ax fx8 R8 M8 model5 cr5 _ sm7 ax5 1 CTX KONT BR8); [| exact Y10'|].
    + apply (PNSRVK.rv_mid_xfer R R7 R8 M7 M8 sp r fb _ MID7 KS8); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| | lia| lia].
      intros a n H1 H2 i Hi. apply FRZ8; lia.
    + right. split; [reflexivity|].
      split; [apply (PNSRVK.ec_agree M7 M8); [intros i Hi; apply FRZ8; lia|lia|lia| exact EC7]|].
      split; [apply (PNBK2.binv_set_stk_top _ l c); [exact INV7| exact ES| exact OKc'| reflexivity]|].
      split.
      * left. exists l, c, (PNM.BS (PNM.bs_mode c) (PNM.bs_len c) ((d + PNM.bs_pos c) mod 2 ^ 64) (PNM.bs_type c) (PNM.bs_idx c)). cbn [PNBO.set_stk PNM.b_stk s7 PNM.with_srcB].
        split; [exact ES|]. split; [reflexivity|]. split; [exact OKc'|]. cbn [PNM.bs_mode PNM.bs_len PNM.bs_type PNM.bs_idx]. repeat split; reflexivity.
      * intros R0. unfold PNR.bb_room in *. cbn [PNBO.set_stk PNM.b_bb PNM.b_src s7 PNM.with_srcB]. apply (PGV8.v8_room_mono _ (PM.unread (PNM.b_src s) sm)); [lia| exact R0].
Qed.

(* [comment removed for export] *)
Lemma arm16 : arm_stmt 0x37b34.
Proof.
  intros t K LBX sp r fb cat e str R M model cr s sm ax fx5 R5 M5 model5 cr5 ax5 CTX KONT BR5 MID EC5.
  pose proof MID as (X2 & X3 & X4 & X8 & X9 & X18 & SV5 & SX5).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 BR5) as (PA5 & IA5 & GR5 & UN5 & STK5 & MOK5).
  change (PMSP.pm_scr 8) with 28672 in STK5. pose proof STK5 as (A16 & SLO & SHI & STOP & SDEF5). pose proof MOK5 as (Mh5 & Ml5 & Mm5).
  pose proof (L5C.stk_writable RSEGS _ M5 sp 28672 STK5) as WR5.
  (let T := type of (PNSRVAP.vlA16_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVAP.vlA16_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVAP.aligned; PMK.sc])).
  destruct P as (fx6 & R6 & M6 & MG6 & EQ6w & EQ6 & MS6 & KS6 & Y1 & Y10 & Y11 & Y12).
  assert (EM6 : M6 = M5) by (apply functional_extensionality; exact EQ6w). subst M6.
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx5 fx6 R5 R6 _ _ M5 (fun _ => False) K
           ltac:(lia) BR5 FOK INCS MS6 MG6 ltac:(intros a Ha _; apply EQ6; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
  intros BR6.
  (* [comment removed for export] *)
  change (@PMSP.cfg RSEGS fx6 R6 0x370d0 M5 model5) with (@PMSP.cfg RSEGS fx6 R6 (pa_src_read AD) M5 model5).
  pose proof SRD as SRD'. unfold PNRS.src_read_spec, PNR.src_read_spec in SRD'.
  apply (PNBK.brel_src_read RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx6 R6 (sp - 96) _ (sp - 64) 4 K SRD' ltac:(lia) K0 BR6 FOK INCS Y1
           ltac:(split; [lia| reflexivity])); [rewrite (KS6 2%nat) by PMK.inl; exact X2| rewrite (KS6 3%nat) by PMK.inl; exact X3| rewrite (KS6 4%nat) by PMK.inl; exact X4
    | replace (fb + 56) with (fb + 40 + 16) by lia; exact Y10| exact Y11| exact Y12| lia| unfold PMSP.pm_scr; lia| exact (PNSRVK.mod16_sub176 sp A16)| lia| lia| lia|].
  intros fx7 R7 M7 src7 sm7 d RP67 Z10 Hd UNR7 DEF7 BR7 AG67.
  set (s7 := PNM.with_srcB s src7) in *.
  assert (MID7 : PNSRVK.rv_mid R R7 M7 sp r fb).
  { apply (PNSRVK.rv_mid_pres R R6 R7 M5 M7 sp r fb); [| exact RP67| intros a n H1 H2; apply AG67; lia| lia| lia].
    apply (PNSRVK.rv_mid_xfer R R5 R6 M5 M5 sp r fb _ MID KS6); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n _ _ i Hi; reflexivity| lia| lia]. }
  pose proof MID7 as (W2 & W3 & W4 & W8 & W9 & W18 & SV7 & SX7).
  assert (EC7 : PMSP.ec_at RSEGS M7 (fb + 16) e cat) by (apply (PNSRVK.ec_agree M5 M7); [apply AG67; lia|lia|lia| exact EC5]).
  assert (INV7 : PNR.binv s7) by (destruct INV0 as (ID & SH); split; [exact ID| exact SH]).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model5 cr5 s7 sm7 ax5 BR7) as (PA7 & IA7 & GR7 & UN7 & STK7 & MOK7).
  change (PMSP.pm_scr 8) with 28672 in STK7. pose proof STK7 as (_ & _ & _ & _ & SDEF7).
  pose proof (L5C.stk_writable RSEGS _ M7 sp 28672 STK7) as WR7.
  pose proof PA7 as (_ & PD7 & VIS7' & _ & _ & CM7 & _).
  pose proof BR7 as ((_ & _ & VIS7 & _ & BASE7 & _) & _). cbn [PNBK.be_M] in VIS7, BASE7.
  unfold PNR.o_v, PMSP.o_v, PMSP.visitor_at in VIS7. cbn [pa_off_v pa_vp_visitor AD PnLayoutS_u.ADDR_S] in VIS7.
  pose proof BASE7 as (IMG7 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG7.
  destruct (PNSRVK.rv_top L HI LY HIok LBX sp fb str _ M7 model5 cr5 s7 sm7 ax5 BR7 INV7) as (l & c & ES & OKc & UE & UP & WP & E0 & E1 & EI & EA).
  cbn [s7 PNM.with_srcB PNM.b_stk PNM.b_sb] in ES, UE, UP, WP, E0, E1, EI, EA.
  set (et := PNM.b_sb s + 40 * Z.of_nat (length l)) in *.
  pose proof OKc as (_ & _ & POS & _).
  assert (DEFB : L5.defined M7 (sp - 64) 4) by (apply (L5.defined_sub M7 (sp - 28672) 28672); [exact SDEF7| lia| lia]).
  assert (OKc' : PNM.bstate_ok (PNM.BS (PNM.bs_mode c) (PNM.bs_len c) ((d + PNM.bs_pos c) mod 2 ^ 64) (PNM.bs_type c) (PNM.bs_idx c)))
    by (unfold PNM.bstate_ok in OKc |- *; cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx]; pose proof (Z.mod_pos_bound (d + PNM.bs_pos c) (2 ^ 64) ltac:(lia)); lia).
  (let T := type of (PNSRVAP.vlB16_conc fx7 R7 M7 (PNSRVK.tv sp r fb R (fun j => match j with 50%nat => d | 51%nat => et + 40 | 52%nat => PNM.bs_pos c | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVAP.vlB16_conc fx7 R7 M7 (PNSRVK.tv sp r fb R (fun j => match j with 50%nat => d | 51%nat => et + 40 | 52%nat => PNM.bs_pos c | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVAP.aligned; PMK.sc])).
  destruct P as (fx8 & R8 & M8 & MG8 & _ & FRZ8 & [(MS8 & KS8 & _ & _ & _ & LT & CP8)|(MS8 & KS8 & Y1' & Y10' & _ & _ & _ & _ & _ & LT & CP8)]).
  - (* [comment removed for export] *)
    pose proof (lt_of_mod d 4 Hd ltac:(lia) LT) as Hd8.
    apply (PNBK2.brel_piece_pos RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model5 cr5 s7 sm7 ax5 fx7 fx8 R7 R8 _ _ M8
             (fun a => et + 40 - 24 <= a < et + 40 - 24 + 8) l c ((d + PNM.bs_pos c) mod 2 ^ 64) K ltac:(lia) BR7 FOK INCS MS8 MG8 FRZ8 ltac:(intros a; apply PMK.rng_dec) ES);
      [intros a Pa; right; cbn [s7 PNM.with_srcB PNM.b_sb]; unfold et in Pa; clear - Pa; lia
      | cbn [s7 PNM.with_srcB PNM.b_sb]; replace (PNM.b_sb s + 40 * Z.of_nat (length l) + 16) with (et + 40 - 24) by (unfold et; lia); exact CP8
      | apply Z.mod_pos_bound; lia |].
    intros BR8.
    apply (PNSRVK.rv_err L HI LY HIok MKE 0x37d98 1 t K LBX sp r fb cat e str R M model cr s sm ax fx8 R8 M8 model5 cr5 _ sm7 ax5 ltac:(left; split; reflexivity) CTX KONT BR8).
    + apply (PNSRVK.rv_mid_xfer R R7 R8 M7 M8 sp r fb _ MID7 KS8); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| | lia| lia].
      intros a n H1 H2 i Hi. apply FRZ8; lia.
    + destruct EC7 as (_ & _ & ED7). apply (L5C.defined_agree M7 M8 (fb + 16) 16); [intros i Hi; apply FRZ8; lia| exact ED7].
    + cbn [PNBO.set_stk PNM.b_stk s7 PNM.with_srcB]. rewrite ES, !length_app. cbn. lia.
    + apply (PNBK2.binv_set_stk_top _ l c); [exact INV7| exact ES| exact OKc'| reflexivity].
  - (* [comment removed for export] *)
    pose proof (eq_of_mod d 4 Hd ltac:(lia) LT) as Hd8.
    apply (PNBK2.brel_piece_pos RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model5 cr5 s7 sm7 ax5 fx7 fx8 R7 R8 _ _ M8
             (fun a => et + 40 - 24 <= a < et + 40 - 24 + 8) l c ((d + PNM.bs_pos c) mod 2 ^ 64) K ltac:(lia) BR7 FOK INCS MS8 MG8 FRZ8 ltac:(intros a; apply PMK.rng_dec) ES);
      [intros a Pa; right; cbn [s7 PNM.with_srcB PNM.b_sb]; unfold et in Pa; clear - Pa; lia
      | cbn [s7 PNM.with_srcB PNM.b_sb]; replace (PNM.b_sb s + 40 * Z.of_nat (length l) + 16) with (et + 40 - 24) by (unfold et; lia); exact CP8
      | apply Z.mod_pos_bound; lia |].
    intros BR8.
    apply (PNSRVK.rv_sbmore L HI LY HIok t K LBX sp r fb cat e str R M model cr s sm ax fx8 R8 M8 model5 cr5 _ sm7 ax5 1 CTX KONT BR8); [| exact Y10'|].
    + apply (PNSRVK.rv_mid_xfer R R7 R8 M7 M8 sp r fb _ MID7 KS8); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| | lia| lia].
      intros a n H1 H2 i Hi. apply FRZ8; lia.
    + right. split; [reflexivity|].
      split; [apply (PNSRVK.ec_agree M7 M8); [intros i Hi; apply FRZ8; lia|lia|lia| exact EC7]|].
      split; [apply (PNBK2.binv_set_stk_top _ l c); [exact INV7| exact ES| exact OKc'| reflexivity]|].
      split.
      * left. exists l, c, (PNM.BS (PNM.bs_mode c) (PNM.bs_len c) ((d + PNM.bs_pos c) mod 2 ^ 64) (PNM.bs_type c) (PNM.bs_idx c)). cbn [PNBO.set_stk PNM.b_stk s7 PNM.with_srcB].
        split; [exact ES|]. split; [reflexivity|]. split; [exact OKc'|]. cbn [PNM.bs_mode PNM.bs_len PNM.bs_type PNM.bs_idx]. repeat split; reflexivity.
      * intros R0. unfold PNR.bb_room in *. cbn [PNBO.set_stk PNM.b_bb PNM.b_src s7 PNM.with_srcB]. apply (PGV8.v8_room_mono _ (PM.unread (PNM.b_src s) sm)); [lia| exact R0].
Qed.

(* [comment removed for export] *)
Lemma arm17 : arm_stmt 0x37b84.
Proof.
  intros t K LBX sp r fb cat e str R M model cr s sm ax fx5 R5 M5 model5 cr5 ax5 CTX KONT BR5 MID EC5.
  pose proof MID as (X2 & X3 & X4 & X8 & X9 & X18 & SV5 & SX5).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 BR5) as (PA5 & IA5 & GR5 & UN5 & STK5 & MOK5).
  change (PMSP.pm_scr 8) with 28672 in STK5. pose proof STK5 as (A16 & SLO & SHI & STOP & SDEF5). pose proof MOK5 as (Mh5 & Ml5 & Mm5).
  pose proof (L5C.stk_writable RSEGS _ M5 sp 28672 STK5) as WR5.
  (let T := type of (PNSRVAP.vlA17_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVAP.vlA17_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVAP.aligned; PMK.sc])).
  destruct P as (fx6 & R6 & M6 & MG6 & EQ6w & EQ6 & MS6 & KS6 & Y1 & Y10 & Y11 & Y12).
  assert (EM6 : M6 = M5) by (apply functional_extensionality; exact EQ6w). subst M6.
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx5 fx6 R5 R6 _ _ M5 (fun _ => False) K
           ltac:(lia) BR5 FOK INCS MS6 MG6 ltac:(intros a Ha _; apply EQ6; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
  intros BR6.
  (* [comment removed for export] *)
  change (@PMSP.cfg RSEGS fx6 R6 0x370d0 M5 model5) with (@PMSP.cfg RSEGS fx6 R6 (pa_src_read AD) M5 model5).
  pose proof SRD as SRD'. unfold PNRS.src_read_spec, PNR.src_read_spec in SRD'.
  apply (PNBK.brel_src_read RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx6 R6 (sp - 96) _ (sp - 64) 8 K SRD' ltac:(lia) K0 BR6 FOK INCS Y1
           ltac:(split; [lia| reflexivity])); [rewrite (KS6 2%nat) by PMK.inl; exact X2| rewrite (KS6 3%nat) by PMK.inl; exact X3| rewrite (KS6 4%nat) by PMK.inl; exact X4
    | replace (fb + 56) with (fb + 40 + 16) by lia; exact Y10| exact Y11| exact Y12| lia| unfold PMSP.pm_scr; lia| exact (PNSRVK.mod16_sub176 sp A16)| lia| lia| lia|].
  intros fx7 R7 M7 src7 sm7 d RP67 Z10 Hd UNR7 DEF7 BR7 AG67.
  set (s7 := PNM.with_srcB s src7) in *.
  assert (MID7 : PNSRVK.rv_mid R R7 M7 sp r fb).
  { apply (PNSRVK.rv_mid_pres R R6 R7 M5 M7 sp r fb); [| exact RP67| intros a n H1 H2; apply AG67; lia| lia| lia].
    apply (PNSRVK.rv_mid_xfer R R5 R6 M5 M5 sp r fb _ MID KS6); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n _ _ i Hi; reflexivity| lia| lia]. }
  pose proof MID7 as (W2 & W3 & W4 & W8 & W9 & W18 & SV7 & SX7).
  assert (EC7 : PMSP.ec_at RSEGS M7 (fb + 16) e cat) by (apply (PNSRVK.ec_agree M5 M7); [apply AG67; lia|lia|lia| exact EC5]).
  assert (INV7 : PNR.binv s7) by (destruct INV0 as (ID & SH); split; [exact ID| exact SH]).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model5 cr5 s7 sm7 ax5 BR7) as (PA7 & IA7 & GR7 & UN7 & STK7 & MOK7).
  change (PMSP.pm_scr 8) with 28672 in STK7. pose proof STK7 as (_ & _ & _ & _ & SDEF7).
  pose proof (L5C.stk_writable RSEGS _ M7 sp 28672 STK7) as WR7.
  pose proof PA7 as (_ & PD7 & VIS7' & _ & _ & CM7 & _).
  pose proof BR7 as ((_ & _ & VIS7 & _ & BASE7 & _) & _). cbn [PNBK.be_M] in VIS7, BASE7.
  unfold PNR.o_v, PMSP.o_v, PMSP.visitor_at in VIS7. cbn [pa_off_v pa_vp_visitor AD PnLayoutS_u.ADDR_S] in VIS7.
  pose proof BASE7 as (IMG7 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG7.
  destruct (PNSRVK.rv_top L HI LY HIok LBX sp fb str _ M7 model5 cr5 s7 sm7 ax5 BR7 INV7) as (l & c & ES & OKc & UE & UP & WP & E0 & E1 & EI & EA).
  cbn [s7 PNM.with_srcB PNM.b_stk PNM.b_sb] in ES, UE, UP, WP, E0, E1, EI, EA.
  set (et := PNM.b_sb s + 40 * Z.of_nat (length l)) in *.
  pose proof OKc as (_ & _ & POS & _).
  assert (DEFB : L5.defined M7 (sp - 64) 8) by (apply (L5.defined_sub M7 (sp - 28672) 28672); [exact SDEF7| lia| lia]).
  assert (OKc' : PNM.bstate_ok (PNM.BS (PNM.bs_mode c) (PNM.bs_len c) ((d + PNM.bs_pos c) mod 2 ^ 64) (PNM.bs_type c) (PNM.bs_idx c)))
    by (unfold PNM.bstate_ok in OKc |- *; cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx]; pose proof (Z.mod_pos_bound (d + PNM.bs_pos c) (2 ^ 64) ltac:(lia)); lia).
  (let T := type of (PNSRVAP.vlB17_conc fx7 R7 M7 (PNSRVK.tv sp r fb R (fun j => match j with 50%nat => d | 51%nat => et + 40 | 52%nat => PNM.bs_pos c | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVAP.vlB17_conc fx7 R7 M7 (PNSRVK.tv sp r fb R (fun j => match j with 50%nat => d | 51%nat => et + 40 | 52%nat => PNM.bs_pos c | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVAP.aligned; PMK.sc])).
  destruct P as (fx8 & R8 & M8 & MG8 & _ & FRZ8 & [(MS8 & KS8 & _ & _ & _ & LT & CP8)|(MS8 & KS8 & Y1' & Y10' & _ & _ & _ & _ & _ & LT & CP8)]).
  - (* [comment removed for export] *)
    pose proof (lt_of_mod d 8 Hd ltac:(lia) LT) as Hd8.
    apply (PNBK2.brel_piece_pos RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model5 cr5 s7 sm7 ax5 fx7 fx8 R7 R8 _ _ M8
             (fun a => et + 40 - 24 <= a < et + 40 - 24 + 8) l c ((d + PNM.bs_pos c) mod 2 ^ 64) K ltac:(lia) BR7 FOK INCS MS8 MG8 FRZ8 ltac:(intros a; apply PMK.rng_dec) ES);
      [intros a Pa; right; cbn [s7 PNM.with_srcB PNM.b_sb]; unfold et in Pa; clear - Pa; lia
      | cbn [s7 PNM.with_srcB PNM.b_sb]; replace (PNM.b_sb s + 40 * Z.of_nat (length l) + 16) with (et + 40 - 24) by (unfold et; lia); exact CP8
      | apply Z.mod_pos_bound; lia |].
    intros BR8.
    apply (PNSRVK.rv_err L HI LY HIok MKE 0x37d98 1 t K LBX sp r fb cat e str R M model cr s sm ax fx8 R8 M8 model5 cr5 _ sm7 ax5 ltac:(left; split; reflexivity) CTX KONT BR8).
    + apply (PNSRVK.rv_mid_xfer R R7 R8 M7 M8 sp r fb _ MID7 KS8); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| | lia| lia].
      intros a n H1 H2 i Hi. apply FRZ8; lia.
    + destruct EC7 as (_ & _ & ED7). apply (L5C.defined_agree M7 M8 (fb + 16) 16); [intros i Hi; apply FRZ8; lia| exact ED7].
    + cbn [PNBO.set_stk PNM.b_stk s7 PNM.with_srcB]. rewrite ES, !length_app. cbn. lia.
    + apply (PNBK2.binv_set_stk_top _ l c); [exact INV7| exact ES| exact OKc'| reflexivity].
  - (* [comment removed for export] *)
    pose proof (eq_of_mod d 8 Hd ltac:(lia) LT) as Hd8.
    apply (PNBK2.brel_piece_pos RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model5 cr5 s7 sm7 ax5 fx7 fx8 R7 R8 _ _ M8
             (fun a => et + 40 - 24 <= a < et + 40 - 24 + 8) l c ((d + PNM.bs_pos c) mod 2 ^ 64) K ltac:(lia) BR7 FOK INCS MS8 MG8 FRZ8 ltac:(intros a; apply PMK.rng_dec) ES);
      [intros a Pa; right; cbn [s7 PNM.with_srcB PNM.b_sb]; unfold et in Pa; clear - Pa; lia
      | cbn [s7 PNM.with_srcB PNM.b_sb]; replace (PNM.b_sb s + 40 * Z.of_nat (length l) + 16) with (et + 40 - 24) by (unfold et; lia); exact CP8
      | apply Z.mod_pos_bound; lia |].
    intros BR8.
    apply (PNSRVK.rv_sbmore L HI LY HIok t K LBX sp r fb cat e str R M model cr s sm ax fx8 R8 M8 model5 cr5 _ sm7 ax5 1 CTX KONT BR8); [| exact Y10'|].
    + apply (PNSRVK.rv_mid_xfer R R7 R8 M7 M8 sp r fb _ MID7 KS8); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| | lia| lia].
      intros a n H1 H2 i Hi. apply FRZ8; lia.
    + right. split; [reflexivity|].
      split; [apply (PNSRVK.ec_agree M7 M8); [intros i Hi; apply FRZ8; lia|lia|lia| exact EC7]|].
      split; [apply (PNBK2.binv_set_stk_top _ l c); [exact INV7| exact ES| exact OKc'| reflexivity]|].
      split.
      * left. exists l, c, (PNM.BS (PNM.bs_mode c) (PNM.bs_len c) ((d + PNM.bs_pos c) mod 2 ^ 64) (PNM.bs_type c) (PNM.bs_idx c)). cbn [PNBO.set_stk PNM.b_stk s7 PNM.with_srcB].
        split; [exact ES|]. split; [reflexivity|]. split; [exact OKc'|]. cbn [PNM.bs_mode PNM.bs_len PNM.bs_type PNM.bs_idx]. repeat split; reflexivity.
      * intros R0. unfold PNR.bb_room in *. cbn [PNBO.set_stk PNM.b_bb PNM.b_src s7 PNM.with_srcB]. apply (PGV8.v8_room_mono _ (PM.unread (PNM.b_src s) sm)); [lia| exact R0].
Qed.

(* [comment removed for export] *)
Lemma arm18 : arm_stmt 0x37708.
Proof.
  intros t K LBX sp r fb cat e str R M model cr s sm ax fx5 R5 M5 model5 cr5 ax5 CTX KONT BR5 MID EC5.
  pose proof MID as (X2 & X3 & X4 & X8 & X9 & X18 & SV5 & SX5).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 BR5) as (PA5 & IA5 & GR5 & UN5 & STK5 & MOK5).
  change (PMSP.pm_scr 8) with 28672 in STK5. pose proof STK5 as (A16 & SLO & SHI & STOP & SDEF5). pose proof MOK5 as (Mh5 & Ml5 & Mm5).
  pose proof (L5C.stk_writable RSEGS _ M5 sp 28672 STK5) as WR5.
  (let T := type of (PNSRVAP.vlA18_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVAP.vlA18_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVAP.aligned; PMK.sc])).
  destruct P as (fx6 & R6 & M6 & MG6 & EQ6w & EQ6 & MS6 & KS6 & Y1 & Y10 & Y11 & Y12).
  assert (EM6 : M6 = M5) by (apply functional_extensionality; exact EQ6w). subst M6.
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx5 fx6 R5 R6 _ _ M5 (fun _ => False) K
           ltac:(lia) BR5 FOK INCS MS6 MG6 ltac:(intros a Ha _; apply EQ6; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
  intros BR6.
  (* [comment removed for export] *)
  change (@PMSP.cfg RSEGS fx6 R6 0x370d0 M5 model5) with (@PMSP.cfg RSEGS fx6 R6 (pa_src_read AD) M5 model5).
  pose proof SRD as SRD'. unfold PNRS.src_read_spec, PNR.src_read_spec in SRD'.
  apply (PNBK.brel_src_read RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx6 R6 (sp - 96) _ (sp - 64) 8 K SRD' ltac:(lia) K0 BR6 FOK INCS Y1
           ltac:(split; [lia| reflexivity])); [rewrite (KS6 2%nat) by PMK.inl; exact X2| rewrite (KS6 3%nat) by PMK.inl; exact X3| rewrite (KS6 4%nat) by PMK.inl; exact X4
    | replace (fb + 56) with (fb + 40 + 16) by lia; exact Y10| exact Y11| exact Y12| lia| unfold PMSP.pm_scr; lia| exact (PNSRVK.mod16_sub176 sp A16)| lia| lia| lia|].
  intros fx7 R7 M7 src7 sm7 d RP67 Z10 Hd UNR7 DEF7 BR7 AG67.
  set (s7 := PNM.with_srcB s src7) in *.
  assert (MID7 : PNSRVK.rv_mid R R7 M7 sp r fb).
  { apply (PNSRVK.rv_mid_pres R R6 R7 M5 M7 sp r fb); [| exact RP67| intros a n H1 H2; apply AG67; lia| lia| lia].
    apply (PNSRVK.rv_mid_xfer R R5 R6 M5 M5 sp r fb _ MID KS6); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n _ _ i Hi; reflexivity| lia| lia]. }
  pose proof MID7 as (W2 & W3 & W4 & W8 & W9 & W18 & SV7 & SX7).
  assert (EC7 : PMSP.ec_at RSEGS M7 (fb + 16) e cat) by (apply (PNSRVK.ec_agree M5 M7); [apply AG67; lia|lia|lia| exact EC5]).
  assert (INV7 : PNR.binv s7) by (destruct INV0 as (ID & SH); split; [exact ID| exact SH]).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model5 cr5 s7 sm7 ax5 BR7) as (PA7 & IA7 & GR7 & UN7 & STK7 & MOK7).
  change (PMSP.pm_scr 8) with 28672 in STK7. pose proof STK7 as (_ & _ & _ & _ & SDEF7).
  pose proof (L5C.stk_writable RSEGS _ M7 sp 28672 STK7) as WR7.
  pose proof PA7 as (_ & PD7 & VIS7' & _ & _ & CM7 & _).
  pose proof BR7 as ((_ & _ & VIS7 & _ & BASE7 & _) & _). cbn [PNBK.be_M] in VIS7, BASE7.
  unfold PNR.o_v, PMSP.o_v, PMSP.visitor_at in VIS7. cbn [pa_off_v pa_vp_visitor AD PnLayoutS_u.ADDR_S] in VIS7.
  pose proof BASE7 as (IMG7 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG7.
  destruct (PNSRVK.rv_top L HI LY HIok LBX sp fb str _ M7 model5 cr5 s7 sm7 ax5 BR7 INV7) as (l & c & ES & OKc & UE & UP & WP & E0 & E1 & EI & EA).
  cbn [s7 PNM.with_srcB PNM.b_stk PNM.b_sb] in ES, UE, UP, WP, E0, E1, EI, EA.
  set (et := PNM.b_sb s + 40 * Z.of_nat (length l)) in *.
  pose proof OKc as (_ & _ & POS & _).
  assert (DEFB : L5.defined M7 (sp - 64) 8) by (apply (L5.defined_sub M7 (sp - 28672) 28672); [exact SDEF7| lia| lia]).
  assert (OKc' : PNM.bstate_ok (PNM.BS (PNM.bs_mode c) (PNM.bs_len c) ((d + PNM.bs_pos c) mod 2 ^ 64) (PNM.bs_type c) (PNM.bs_idx c)))
    by (unfold PNM.bstate_ok in OKc |- *; cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx]; pose proof (Z.mod_pos_bound (d + PNM.bs_pos c) (2 ^ 64) ltac:(lia)); lia).
  (let T := type of (PNSRVAP.vlB18_conc fx7 R7 M7 (PNSRVK.tv sp r fb R (fun j => match j with 50%nat => d | 51%nat => et + 40 | 52%nat => PNM.bs_pos c | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVAP.vlB18_conc fx7 R7 M7 (PNSRVK.tv sp r fb R (fun j => match j with 50%nat => d | 51%nat => et + 40 | 52%nat => PNM.bs_pos c | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVAP.aligned; PMK.sc])).
  destruct P as (fx8 & R8 & M8 & MG8 & _ & FRZ8 & [(MS8 & KS8 & _ & _ & _ & LT & CP8)|(MS8 & KS8 & Y1' & Y10' & _ & _ & _ & _ & _ & LT & CP8)]).
  - (* [comment removed for export] *)
    pose proof (lt_of_mod d 8 Hd ltac:(lia) LT) as Hd8.
    apply (PNBK2.brel_piece_pos RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model5 cr5 s7 sm7 ax5 fx7 fx8 R7 R8 _ _ M8
             (fun a => et + 40 - 24 <= a < et + 40 - 24 + 8) l c ((d + PNM.bs_pos c) mod 2 ^ 64) K ltac:(lia) BR7 FOK INCS MS8 MG8 FRZ8 ltac:(intros a; apply PMK.rng_dec) ES);
      [intros a Pa; right; cbn [s7 PNM.with_srcB PNM.b_sb]; unfold et in Pa; clear - Pa; lia
      | cbn [s7 PNM.with_srcB PNM.b_sb]; replace (PNM.b_sb s + 40 * Z.of_nat (length l) + 16) with (et + 40 - 24) by (unfold et; lia); exact CP8
      | apply Z.mod_pos_bound; lia |].
    intros BR8.
    apply (PNSRVK.rv_err L HI LY HIok MKE 0x37d98 1 t K LBX sp r fb cat e str R M model cr s sm ax fx8 R8 M8 model5 cr5 _ sm7 ax5 ltac:(left; split; reflexivity) CTX KONT BR8).
    + apply (PNSRVK.rv_mid_xfer R R7 R8 M7 M8 sp r fb _ MID7 KS8); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| | lia| lia].
      intros a n H1 H2 i Hi. apply FRZ8; lia.
    + destruct EC7 as (_ & _ & ED7). apply (L5C.defined_agree M7 M8 (fb + 16) 16); [intros i Hi; apply FRZ8; lia| exact ED7].
    + cbn [PNBO.set_stk PNM.b_stk s7 PNM.with_srcB]. rewrite ES, !length_app. cbn. lia.
    + apply (PNBK2.binv_set_stk_top _ l c); [exact INV7| exact ES| exact OKc'| reflexivity].
  - (* [comment removed for export] *)
    pose proof (eq_of_mod d 8 Hd ltac:(lia) LT) as Hd8.
    apply (PNBK2.brel_piece_pos RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model5 cr5 s7 sm7 ax5 fx7 fx8 R7 R8 _ _ M8
             (fun a => et + 40 - 24 <= a < et + 40 - 24 + 8) l c ((d + PNM.bs_pos c) mod 2 ^ 64) K ltac:(lia) BR7 FOK INCS MS8 MG8 FRZ8 ltac:(intros a; apply PMK.rng_dec) ES);
      [intros a Pa; right; cbn [s7 PNM.with_srcB PNM.b_sb]; unfold et in Pa; clear - Pa; lia
      | cbn [s7 PNM.with_srcB PNM.b_sb]; replace (PNM.b_sb s + 40 * Z.of_nat (length l) + 16) with (et + 40 - 24) by (unfold et; lia); exact CP8
      | apply Z.mod_pos_bound; lia |].
    intros BR8.
    apply (PNSRVK.rv_sbmore L HI LY HIok t K LBX sp r fb cat e str R M model cr s sm ax fx8 R8 M8 model5 cr5 _ sm7 ax5 1 CTX KONT BR8); [| exact Y10'|].
    + apply (PNSRVK.rv_mid_xfer R R7 R8 M7 M8 sp r fb _ MID7 KS8); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| | lia| lia].
      intros a n H1 H2 i Hi. apply FRZ8; lia.
    + right. split; [reflexivity|].
      split; [apply (PNSRVK.ec_agree M7 M8); [intros i Hi; apply FRZ8; lia|lia|lia| exact EC7]|].
      split; [apply (PNBK2.binv_set_stk_top _ l c); [exact INV7| exact ES| exact OKc'| reflexivity]|].
      split.
      * left. exists l, c, (PNM.BS (PNM.bs_mode c) (PNM.bs_len c) ((d + PNM.bs_pos c) mod 2 ^ 64) (PNM.bs_type c) (PNM.bs_idx c)). cbn [PNBO.set_stk PNM.b_stk s7 PNM.with_srcB].
        split; [exact ES|]. split; [reflexivity|]. split; [exact OKc'|]. cbn [PNM.bs_mode PNM.bs_len PNM.bs_type PNM.bs_idx]. repeat split; reflexivity.
      * intros R0. unfold PNR.bb_room in *. cbn [PNBO.set_stk PNM.b_bb PNM.b_src s7 PNM.with_srcB]. apply (PGV8.v8_room_mono _ (PM.unread (PNM.b_src s) sm)); [lia| exact R0].
Qed.

(* [comment removed for export] *)
Lemma arm8 : arm_stmt 0x37aa4.
Proof.
  intros t K LBX sp r fb cat e str R M model cr s sm ax fx5 R5 M5 model5 cr5 ax5 CTX KONT BR5 MID EC5.
  pose proof MID as (X2 & X3 & X4 & X8 & X9 & X18 & SV5 & SX5).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 BR5) as (PA5 & IA5 & GR5 & UN5 & STK5 & MOK5).
  change (PMSP.pm_scr 8) with 28672 in STK5. pose proof STK5 as (A16 & SLO & SHI & STOP & SDEF5). pose proof MOK5 as (Mh5 & Ml5 & Mm5).
  pose proof (L5C.stk_writable RSEGS _ M5 sp 28672 STK5) as WR5.
  (let T := type of (PNSRVAP.vlA8_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVAP.vlA8_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVAP.aligned; PMK.sc])).
  destruct P as (fx6 & R6 & M6 & MG6 & EQ6w & EQ6 & MS6 & KS6 & Y1 & Y10 & Y11 & Y12).
  assert (EM6 : M6 = M5) by (apply functional_extensionality; exact EQ6w). subst M6.
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx5 fx6 R5 R6 _ _ M5 (fun _ => False) K
           ltac:(lia) BR5 FOK INCS MS6 MG6 ltac:(intros a Ha _; apply EQ6; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
  intros BR6.
  (* [comment removed for export] *)
  change (@PMSP.cfg RSEGS fx6 R6 0x370d0 M5 model5) with (@PMSP.cfg RSEGS fx6 R6 (pa_src_read AD) M5 model5).
  pose proof SRD as SRD'. unfold PNRS.src_read_spec, PNR.src_read_spec in SRD'.
  apply (PNBK.brel_src_read RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx6 R6 (sp - 96) _ (sp - 64) 1 K SRD' ltac:(lia) K0 BR6 FOK INCS Y1
           ltac:(split; [lia| reflexivity])); [rewrite (KS6 2%nat) by PMK.inl; exact X2| rewrite (KS6 3%nat) by PMK.inl; exact X3| rewrite (KS6 4%nat) by PMK.inl; exact X4
    | replace (fb + 56) with (fb + 40 + 16) by lia; exact Y10| exact Y11| exact Y12| lia| unfold PMSP.pm_scr; lia| exact (PNSRVK.mod16_sub176 sp A16)| lia| lia| lia|].
  intros fx7 R7 M7 src7 sm7 d RP67 Z10 Hd UNR7 DEF7 BR7 AG67.
  set (s7 := PNM.with_srcB s src7) in *.
  assert (MID7 : PNSRVK.rv_mid R R7 M7 sp r fb).
  { apply (PNSRVK.rv_mid_pres R R6 R7 M5 M7 sp r fb); [| exact RP67| intros a n H1 H2; apply AG67; lia| lia| lia].
    apply (PNSRVK.rv_mid_xfer R R5 R6 M5 M5 sp r fb _ MID KS6); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n _ _ i Hi; reflexivity| lia| lia]. }
  pose proof MID7 as (W2 & W3 & W4 & W8 & W9 & W18 & SV7 & SX7).
  assert (EC7 : PMSP.ec_at RSEGS M7 (fb + 16) e cat) by (apply (PNSRVK.ec_agree M5 M7); [apply AG67; lia|lia|lia| exact EC5]).
  assert (INV7 : PNR.binv s7) by (destruct INV0 as (ID & SH); split; [exact ID| exact SH]).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model5 cr5 s7 sm7 ax5 BR7) as (PA7 & IA7 & GR7 & UN7 & STK7 & MOK7).
  change (PMSP.pm_scr 8) with 28672 in STK7. pose proof STK7 as (_ & _ & _ & _ & SDEF7).
  pose proof (L5C.stk_writable RSEGS _ M7 sp 28672 STK7) as WR7.
  pose proof PA7 as (_ & PD7 & VIS7' & _ & _ & CM7 & _).
  pose proof BR7 as ((_ & _ & VIS7 & _ & BASE7 & _) & _). cbn [PNBK.be_M] in VIS7, BASE7.
  unfold PNR.o_v, PMSP.o_v, PMSP.visitor_at in VIS7. cbn [pa_off_v pa_vp_visitor AD PnLayoutS_u.ADDR_S] in VIS7.
  pose proof BASE7 as (IMG7 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG7.
  destruct (PNSRVK.rv_top L HI LY HIok LBX sp fb str _ M7 model5 cr5 s7 sm7 ax5 BR7 INV7) as (l & c & ES & OKc & UE & UP & WP & E0 & E1 & EI & EA).
  cbn [s7 PNM.with_srcB PNM.b_stk PNM.b_sb] in ES, UE, UP, WP, E0, E1, EI, EA.
  set (et := PNM.b_sb s + 40 * Z.of_nat (length l)) in *.
  pose proof OKc as (_ & _ & POS & _).
  assert (DEFB : L5.defined M7 (sp - 64) 1) by (apply (L5.defined_sub M7 (sp - 28672) 28672); [exact SDEF7| lia| lia]).
  assert (OKc' : PNM.bstate_ok (PNM.BS (PNM.bs_mode c) (PNM.bs_len c) ((d + PNM.bs_pos c) mod 2 ^ 64) (PNM.bs_type c) (PNM.bs_idx c)))
    by (unfold PNM.bstate_ok in OKc |- *; cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx]; pose proof (Z.mod_pos_bound (d + PNM.bs_pos c) (2 ^ 64) ltac:(lia)); lia).
  (let T := type of (PNSRVAP.vlB8_conc fx7 R7 M7 (PNSRVK.tv sp r fb R (fun j => match j with 50%nat => d | 51%nat => et + 40 | 52%nat => PNM.bs_pos c | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVAP.vlB8_conc fx7 R7 M7 (PNSRVK.tv sp r fb R (fun j => match j with 50%nat => d | 51%nat => et + 40 | 52%nat => PNM.bs_pos c | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVAP.aligned; PMK.sc])).
  destruct P as (fx8 & R8 & M8 & MG8 & _ & FRZ8 & [(MS8 & KS8 & _ & _ & _ & LT & CP8)|(MS8 & KS8 & Y1' & Y10' & _ & _ & _ & _ & _ & LT & CP8)]).
  - (* [comment removed for export] *)
    pose proof (lt_of_mod d 1 Hd ltac:(lia) LT) as Hd8.
    apply (PNBK2.brel_piece_pos RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model5 cr5 s7 sm7 ax5 fx7 fx8 R7 R8 _ _ M8
             (fun a => et + 40 - 24 <= a < et + 40 - 24 + 8) l c ((d + PNM.bs_pos c) mod 2 ^ 64) K ltac:(lia) BR7 FOK INCS MS8 MG8 FRZ8 ltac:(intros a; apply PMK.rng_dec) ES);
      [intros a Pa; right; cbn [s7 PNM.with_srcB PNM.b_sb]; unfold et in Pa; clear - Pa; lia
      | cbn [s7 PNM.with_srcB PNM.b_sb]; replace (PNM.b_sb s + 40 * Z.of_nat (length l) + 16) with (et + 40 - 24) by (unfold et; lia); exact CP8
      | apply Z.mod_pos_bound; lia |].
    intros BR8.
    apply (PNSRVK.rv_err L HI LY HIok MKE 0x37d98 1 t K LBX sp r fb cat e str R M model cr s sm ax fx8 R8 M8 model5 cr5 _ sm7 ax5 ltac:(left; split; reflexivity) CTX KONT BR8).
    + apply (PNSRVK.rv_mid_xfer R R7 R8 M7 M8 sp r fb _ MID7 KS8); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| | lia| lia].
      intros a n H1 H2 i Hi. apply FRZ8; lia.
    + destruct EC7 as (_ & _ & ED7). apply (L5C.defined_agree M7 M8 (fb + 16) 16); [intros i Hi; apply FRZ8; lia| exact ED7].
    + cbn [PNBO.set_stk PNM.b_stk s7 PNM.with_srcB]. rewrite ES, !length_app. cbn. lia.
    + apply (PNBK2.binv_set_stk_top _ l c); [exact INV7| exact ES| exact OKc'| reflexivity].
  - (* [comment removed for export] *)
    pose proof (eq_of_mod d 1 Hd ltac:(lia) LT) as Hd8.
    apply (PNBK2.brel_piece_pos RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model5 cr5 s7 sm7 ax5 fx7 fx8 R7 R8 _ _ M8
             (fun a => et + 40 - 24 <= a < et + 40 - 24 + 8) l c ((d + PNM.bs_pos c) mod 2 ^ 64) K ltac:(lia) BR7 FOK INCS MS8 MG8 FRZ8 ltac:(intros a; apply PMK.rng_dec) ES);
      [intros a Pa; right; cbn [s7 PNM.with_srcB PNM.b_sb]; unfold et in Pa; clear - Pa; lia
      | cbn [s7 PNM.with_srcB PNM.b_sb]; replace (PNM.b_sb s + 40 * Z.of_nat (length l) + 16) with (et + 40 - 24) by (unfold et; lia); exact CP8
      | apply Z.mod_pos_bound; lia |].
    intros BR8.
    apply (PNSRVK.rv_sbmore L HI LY HIok t K LBX sp r fb cat e str R M model cr s sm ax fx8 R8 M8 model5 cr5 _ sm7 ax5 1 CTX KONT BR8); [| exact Y10'|].
    + apply (PNSRVK.rv_mid_xfer R R7 R8 M7 M8 sp r fb _ MID7 KS8); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| | lia| lia].
      intros a n H1 H2 i Hi. apply FRZ8; lia.
    + right. split; [reflexivity|].
      split; [apply (PNSRVK.ec_agree M7 M8); [intros i Hi; apply FRZ8; lia|lia|lia| exact EC7]|].
      split; [apply (PNBK2.binv_set_stk_top _ l c); [exact INV7| exact ES| exact OKc'| reflexivity]|].
      split.
      * left. exists l, c, (PNM.BS (PNM.bs_mode c) (PNM.bs_len c) ((d + PNM.bs_pos c) mod 2 ^ 64) (PNM.bs_type c) (PNM.bs_idx c)). cbn [PNBO.set_stk PNM.b_stk s7 PNM.with_srcB].
        split; [exact ES|]. split; [reflexivity|]. split; [exact OKc'|]. cbn [PNM.bs_mode PNM.bs_len PNM.bs_type PNM.bs_idx]. repeat split; reflexivity.
      * intros R0. unfold PNR.bb_room in *. cbn [PNBO.set_stk PNM.b_bb PNM.b_src s7 PNM.with_srcB]. apply (PGV8.v8_room_mono _ (PM.unread (PNM.b_src s) sm)); [lia| exact R0].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma arm10 : arm_stmt 0x37b14.
Proof.
  intros t K LBX sp r fb cat e str R M model cr s sm ax fx5 R5 M5 model5 cr5 ax5 CTX KONT BR5 MID EC5.
  pose proof MID as (X2 & X3 & X4 & X8 & X9 & X18 & SV5 & SX5).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 BR5) as (PA5 & IA5 & GR5 & UN5 & STK5 & MOK5).
  change (PMSP.pm_scr 8) with 28672 in STK5. pose proof STK5 as (A16 & SLO & SHI & STOP & SDEF5). pose proof MOK5 as (Mh5 & Ml5 & Mm5).
  pose proof (L5C.stk_writable RSEGS _ M5 sp 28672 STK5) as WR5.
  pose proof PA5 as (_ & PD5 & VIS5' & _ & _ & CM5 & _).
  pose proof BR5 as ((_ & _ & VIS5 & _ & BASE5 & _) & _). cbn [PNBK.be_M] in VIS5, BASE5.
  unfold PNR.o_v, PMSP.o_v, PMSP.visitor_at in VIS5. cbn [pa_off_v pa_vp_visitor AD PnLayoutS_u.ADDR_S] in VIS5.
  pose proof BASE5 as (IMG5 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG5.
  (let T := type of (PNSRVAP.vlN10_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVAP.vlN10_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVAP.aligned; PMK.sc])).
  destruct P as (fx6 & R6 & M6 & MG6 & EQ6w & EQ6 & MS6 & KS6 & Y1 & Y10 & _).
  assert (EM6 : M6 = M5) by (apply functional_extensionality; exact EQ6w). subst M6.
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx5 fx6 R5 R6 _ _ M5 (fun _ => False) K
           ltac:(lia) BR5 FOK INCS MS6 MG6 ltac:(intros a Ha _; apply EQ6; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
  intros BR6.
  apply (PNSRVK.rv_sbmore L HI LY HIok t K LBX sp r fb cat e str R M model cr s sm ax fx6 R6 M5 model5 cr5 s sm ax5 1 CTX KONT BR6); [| exact Y10|].
  - apply (PNSRVK.rv_mid_xfer R R5 R6 M5 M5 sp r fb _ MID KS6); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n _ _ i Hi; reflexivity| lia| lia].
  - right. split; [reflexivity|]. split; [exact EC5|]. split; [exact INV0|]. split; [left; apply PNBK2.btop_pos_refl; exact INV0|]. intros R0; exact R0.
Qed.

(* [comment removed for export] *)
Lemma arm6 : arm_stmt 0x37a90.
Proof.
  intros t K LBX sp r fb cat e str R M model cr s sm ax fx5 R5 M5 model5 cr5 ax5 CTX KONT BR5 MID EC5.
  pose proof MID as (X2 & X3 & X4 & X8 & X9 & X18 & SV5 & SX5).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 BR5) as (PA5 & IA5 & GR5 & UN5 & STK5 & MOK5).
  change (PMSP.pm_scr 8) with 28672 in STK5. pose proof STK5 as (A16 & SLO & SHI & STOP & SDEF5). pose proof MOK5 as (Mh5 & Ml5 & Mm5).
  pose proof (L5C.stk_writable RSEGS _ M5 sp 28672 STK5) as WR5.
  pose proof PA5 as (_ & PD5 & VIS5' & _ & _ & CM5 & _).
  pose proof BR5 as ((_ & _ & VIS5 & _ & BASE5 & _) & _). cbn [PNBK.be_M] in VIS5, BASE5.
  unfold PNR.o_v, PMSP.o_v, PMSP.visitor_at in VIS5. cbn [pa_off_v pa_vp_visitor AD PnLayoutS_u.ADDR_S] in VIS5.
  pose proof BASE5 as (IMG5 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG5.
  (let T := type of (PNSRVAP.vlN6_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVAP.vlN6_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVAP.aligned; PMK.sc])).
  destruct P as (fx6 & R6 & M6 & MG6 & EQ6w & EQ6 & MS6 & KS6 & Y1 & Y10 & _).
  assert (EM6 : M6 = M5) by (apply functional_extensionality; exact EQ6w). subst M6.
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx5 fx6 R5 R6 _ _ M5 (fun _ => False) K
           ltac:(lia) BR5 FOK INCS MS6 MG6 ltac:(intros a Ha _; apply EQ6; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
  intros BR6.
  apply (PNSRVK.rv_sbmore L HI LY HIok t K LBX sp r fb cat e str R M model cr s sm ax fx6 R6 M5 model5 cr5 s sm ax5 1 CTX KONT BR6); [| exact Y10|].
  - apply (PNSRVK.rv_mid_xfer R R5 R6 M5 M5 sp r fb _ MID KS6); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n _ _ i Hi; reflexivity| lia| lia].
  - right. split; [reflexivity|]. split; [exact EC5|]. split; [exact INV0|]. split; [left; apply PNBK2.btop_pos_refl; exact INV0|]. intros R0; exact R0.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma armC3 : PNRS.begin_document_spec L HI -> arm_stmt 0x377d8.
Proof.
  intros BDOC t K LBX sp r fb cat e str R M model cr s sm ax fx5 R5 M5 model5 cr5 ax5 CTX KONT BR5 MID EC5.
  pose proof MID as (X2 & X3 & X4 & X8 & X9 & X18 & SV5 & SX5).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 BR5) as (PA5 & IA5 & GR5 & UN5 & STK5 & MOK5).
  change (PMSP.pm_scr 8) with 28672 in STK5. pose proof STK5 as (A16 & SLO & SHI & STOP & SDEF5). pose proof MOK5 as (Mh5 & Ml5 & Mm5).
  pose proof (L5C.stk_writable RSEGS _ M5 sp 28672 STK5) as WR5.
  pose proof (PNSRVK.rv_saved_cells R M5 sp r SV5) as (S8 & T8 & T9 & T18 & T19 & T20).
  pose proof (PNSRVK.rv_sx_words R R5 SX5) as (X21 & X22 & X23 & X24 & X25 & X26 & X27).
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 8))) as BUR_8. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 9))) as BUR_9.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 18))) as BUR_18. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 19))) as BUR_19.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 20))) as BUR_20. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 21))) as BUR_21.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 22))) as BUR_22. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 23))) as BUR_23.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 24))) as BUR_24. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 25))) as BUR_25.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 26))) as BUR_26. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 27))) as BUR_27.
  (let T := type of (PNSRVCP.vlC3_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVCP.vlC3_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVAP.aligned; PMK.sc])).
  pvz_hg ltac:(idtac; destruct P as (fx6 & R6 & M6 & pvzP); PMK.pvz_lin pvzP;
                destruct pvzP as (MG6 & EQ6w & EQ6 & MS6 & KS6 & Y1 & Y2 & Y8 & Y9 & Y10 & Y11 & Y12 & Y18 & Y19 & Y20)); PMK.pvz_clrT.
  assert (EM6 : M6 = M5) by (apply functional_extensionality; exact EQ6w). subst M6.
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx5 fx6 R5 R6 _ _ M5 (fun _ => False) K
           ltac:(lia) BR5 FOK INCS MS6 MG6 ltac:(intros a Ha _; apply EQ6; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
  intros BR6.
  unfold PNRS.begin_document_spec, PNR.begin_document_spec in BDOC. cbn [PNL.pn_begin_document AN PnLayoutS_u.NADDR_S] in BDOC.
  apply (PNSRVK.rv_tail L HI LY HIok _ t K LBX sp r fb cat e str R M model cr s sm ax fx6 R6 M5 model5 cr5 ax5 BDOC CTX KONT BR6); [| exact Y10| exact Y11| exact Y12| exact EC5].
  apply (PNSRVK.rv_restored_intro R R6 sp r Y1 Y2); [rewrite (KS6 3%nat) by PMK.inl; exact X3| rewrite (KS6 4%nat) by PMK.inl; exact X4
    | exact Y8| exact Y9| exact Y18| exact Y19| exact Y20| rewrite (KS6 21%nat) by PMK.inl; exact X21| rewrite (KS6 22%nat) by PMK.inl; exact X22
    | rewrite (KS6 23%nat) by PMK.inl; exact X23| rewrite (KS6 24%nat) by PMK.inl; exact X24| rewrite (KS6 25%nat) by PMK.inl; exact X25
    | rewrite (KS6 26%nat) by PMK.inl; exact X26| rewrite (KS6 27%nat) by PMK.inl; exact X27].
Qed.

Lemma armC4 : PNRS.begin_array_spec L HI -> arm_stmt 0x37894.
Proof.
  intros BARR t K LBX sp r fb cat e str R M model cr s sm ax fx5 R5 M5 model5 cr5 ax5 CTX KONT BR5 MID EC5.
  pose proof MID as (X2 & X3 & X4 & X8 & X9 & X18 & SV5 & SX5).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 BR5) as (PA5 & IA5 & GR5 & UN5 & STK5 & MOK5).
  change (PMSP.pm_scr 8) with 28672 in STK5. pose proof STK5 as (A16 & SLO & SHI & STOP & SDEF5). pose proof MOK5 as (Mh5 & Ml5 & Mm5).
  pose proof (L5C.stk_writable RSEGS _ M5 sp 28672 STK5) as WR5.
  pose proof (PNSRVK.rv_saved_cells R M5 sp r SV5) as (S8 & T8 & T9 & T18 & T19 & T20).
  pose proof (PNSRVK.rv_sx_words R R5 SX5) as (X21 & X22 & X23 & X24 & X25 & X26 & X27).
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 8))) as BUR_8. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 9))) as BUR_9.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 18))) as BUR_18. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 19))) as BUR_19.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 20))) as BUR_20. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 21))) as BUR_21.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 22))) as BUR_22. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 23))) as BUR_23.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 24))) as BUR_24. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 25))) as BUR_25.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 26))) as BUR_26. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 27))) as BUR_27.
  (let T := type of (PNSRVCP.vlC4_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVCP.vlC4_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVAP.aligned; PMK.sc])).
  pvz_hg ltac:(idtac; destruct P as (fx6 & R6 & M6 & pvzP); PMK.pvz_lin pvzP;
                destruct pvzP as (MG6 & EQ6w & EQ6 & MS6 & KS6 & Y1 & Y2 & Y8 & Y9 & Y10 & Y11 & Y12 & Y18 & Y19 & Y20)); PMK.pvz_clrT.
  assert (EM6 : M6 = M5) by (apply functional_extensionality; exact EQ6w). subst M6.
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx5 fx6 R5 R6 _ _ M5 (fun _ => False) K
           ltac:(lia) BR5 FOK INCS MS6 MG6 ltac:(intros a Ha _; apply EQ6; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
  intros BR6.
  unfold PNRS.begin_array_spec, PNR.begin_array_spec in BARR. cbn [PNL.pn_begin_array AN PnLayoutS_u.NADDR_S] in BARR.
  apply (PNSRVK.rv_tail L HI LY HIok _ t K LBX sp r fb cat e str R M model cr s sm ax fx6 R6 M5 model5 cr5 ax5 BARR CTX KONT BR6); [| exact Y10| exact Y11| exact Y12| exact EC5].
  apply (PNSRVK.rv_restored_intro R R6 sp r Y1 Y2); [rewrite (KS6 3%nat) by PMK.inl; exact X3| rewrite (KS6 4%nat) by PMK.inl; exact X4
    | exact Y8| exact Y9| exact Y18| exact Y19| exact Y20| rewrite (KS6 21%nat) by PMK.inl; exact X21| rewrite (KS6 22%nat) by PMK.inl; exact X22
    | rewrite (KS6 23%nat) by PMK.inl; exact X23| rewrite (KS6 24%nat) by PMK.inl; exact X24| rewrite (KS6 25%nat) by PMK.inl; exact X25
    | rewrite (KS6 26%nat) by PMK.inl; exact X26| rewrite (KS6 27%nat) by PMK.inl; exact X27].
Qed.

End WithHeap.
End PNSRVA.
