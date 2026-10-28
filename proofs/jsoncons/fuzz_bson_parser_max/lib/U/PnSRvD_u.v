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
     PnSRvK_u PnSRvKD_u PnSRvA_u PnSRvB_u PnSRvDP_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSRVD.
Import PMS.
Abbreviation AN := PnLayoutS_u.NADDR_S.
Abbreviation mem := (word -> option byte).
Abbreviation bparser_at := (PNM.bparser_at RSEGS AD PMSP.T3 PMSP.T4 (pa_vp_parser AD)).
Abbreviation BENT := PNBK.BENT.

Lemma tb0_short n : Z.testbit (2 * n) 0 = false.
Proof. apply Z.testbit_even_0. Qed.
Lemma tb0_long c : 0 <= c -> c mod 2 = 0 -> Z.testbit ((c + 1) mod 256) 0 = true.
Proof.
  intros Hc He. rewrite Z.testbit_true by lia. rewrite Z.pow_0_r, Z.div_1_r.
  rewrite (Z.mod_mod_divide (c + 1) 256 2) by (exists 128; reflexivity). rewrite <- Zplus_mod_idemp_l, He. reflexivity.
Qed.
Lemma mod8_of_16 sp k : sp mod 16 = 0 -> (sp - 8 * k) mod 8 = 0.
Proof.
  intros H. replace (sp - 8 * k) with (sp + (- k) * 8) by lia. rewrite Z.mod_add by lia.
  apply PMPK.m16_8. exact H.
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
Hypothesis RSZ : PMS.str_resize_spec L HI.
Hypothesis DEC : PNRS.dec128_spec L HI.

Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac fd P := PMK.feed P ltac:(first [PMK.sc | unfold PNSRVDP.aligned; PMK.sc | symmetry; apply Z_to_bv_bv_unsigned]).

(* [comment removed for export] *)
Lemma step3 t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax (fx9 : FPState) R9 (M9 : mem) model9 cr9 s9 sm9 ax9 :
  rv_ctx t K LBX sp r fb e str R cr s sm -> rv_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M9 model9 cr9 s9 sm9 ax9) ->
  PNSRVK.rv_mid R R9 M9 sp r fb -> PMSP.ec_at RSEGS M9 (fb + 16) e cat -> PNR.binv s9 -> PNR.btop_pos s s9 ->
  PNM.b_bb s9 = PNM.b_bb s -> PM.unread (PNM.b_src s9) sm9 <= PM.unread (PNM.b_src s) sm -> PM.vs_size (PNM.b_tb s9) = 42 ->
  getr R9 (PMK.reg 19) = Z_to_bv 64 (fb + 40 + 368) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx9 R9 0x37cc0 M9 model9) K.
Proof.
  intros CTX KONT BR9 MID9 EC9 INV9 TP9 EBB LEU SZ9 X19.
  pose proof MID9 as (X2 & X3 & X4 & X8 & X9 & X18 & SV9).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ _ _ _ _ _ _ BR9) as (PA9 & IA9 & GR9 & UN9 & STK9 & MOK9).
  change (PMSP.pm_scr 8) with 28672 in STK9. pose proof STK9 as (A16 & SLO & SHI & STOP & SDEF9). pose proof MOK9 as (Mh9 & Ml9 & Mm9).
  pose proof (L5C.stk_writable RSEGS _ _ sp 28672 STK9) as WR9.
  pose proof PA9 as (_ & PD9 & _ & _ & _ & CM9 & _).
  pose proof (PNSRVK.tb_facts M9 fb s9 PA9) as TBF.
  destruct (PNM.b_tb s9) as [n9|c9 n9 p9] eqn:ETB; [destruct TBF as (Hn9 & _); cbn [PM.vs_size] in SZ9; lia|].
  cbn [PM.vs_size] in SZ9. subst n9.
  destruct TBF as (B0 & U8 & U16 & Hn9 & Hc9 & He9 & Dp & U0 & D24).
  destruct (PNBK2.brel_blocks RSEGS AD AN L HI KH 8 LBX sp fb str _ _ _ _ _ _ _ BR9) as (BRG9 & OWNB9 & _).
  assert (TBIN : In (p9, c9) (PNM.bparser_own s9)).
  { unfold PNM.bparser_own, PNM.brest_own. rewrite ETB. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. cbn. auto. }
  destruct (OWNB9 p9 c9 TBIN) as (P0 & P4). unfold hl_ceil in P4.
  pose proof (Z.mod_pos_bound (c9 + 1) 256 ltac:(lia)) as MB9.
  (let T := type of (PNSRVDP.vlD3_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 56%nat => (c9 + 1) mod 256 | 57%nat => p9 | 58%nat => 42 | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVDP.vlD3_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 56%nat => (c9 + 1) mod 256 | 57%nat => p9 | 58%nat => 42 | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVDP.aligned; PMK.sc | apply tb0_long; lia])).
  destruct P as (fx10 & R10 & M10 & MG10 & EQ10w & EQ10 & MS10 & KS10 & Y1 & Y10 & Y11 & Y12).
  assert (EM10 : M10 = M9) by (apply functional_extensionality; exact EQ10w). subst M10.
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 fx9 fx10 R9 R10 _ _ M9 (fun _ => False) K
           ltac:(lia) BR9 FOK INCS MS10 MG10 ltac:(intros a Ha _; apply EQ10; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
  intros BR10.
  assert (MID10 : PNSRVK.rv_mid R R10 M9 sp r fb).
  { apply (PNSRVK.rv_mid_xfer R R9 R10 M9 M9 sp r fb _ MID9 KS10); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n _ _ i Hi; reflexivity| lia| lia]. }
  pose proof MID10 as (W2 & W3 & W4 & W8 & W9 & W18 & SV10).
  (* [comment removed for export] *)
  change (@PMSP.cfg RSEGS fx10 R10 0x38a78 M9 model9) with (@PMSP.cfg RSEGS fx10 R10 (PNL.pn_dec128 AN) M9 model9).
  apply (PNSRVKD.brel_dec128 L HI LY HIok LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 fx10 R10 (sp - 96) _ (sp - 80) c9 p9 K DEC K0 BR10 FOK INCS ETB Y1
           ltac:(split; [lia| reflexivity]) W2 W3 W4 Y10 Y11 Y12); [lia| unfold PMSP.pm_scr; lia| exact (PNSRVK.mod16_sub176 sp A16)| lia| lia| exact (mod8_of_16 sp 10 A16)|].
  intros fx12 R12 M12 ptr RP1012 Z10 Hptr BR12 AG1012.
  assert (MID12 : PNSRVK.rv_mid R R12 M12 sp r fb) by (apply (PNSRVK.rv_mid_pres R R10 R12 M9 M12 sp r fb MID10 RP1012); [intros a n H1 H2; apply AG1012; lia| lia| lia]).
  pose proof MID12 as (V2 & V3 & V4 & V8 & V9 & V18 & SV12).
  assert (EC12 : PMSP.ec_at RSEGS M12 (fb + 16) e cat) by (apply (PNSRVK.ec_agree M9 M12); [apply AG1012; lia|lia|lia| exact EC9]).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ _ _ _ _ _ _ BR12) as (PA12 & _ & _ & _ & STK12 & _).
  change (PMSP.pm_scr 8) with 28672 in STK12. pose proof (L5C.stk_writable RSEGS _ _ sp 28672 STK12) as WR12.
  pose proof PA12 as (_ & PD12 & _ & _ & _ & CM12 & _).
  pose proof BR12 as ((_ & _ & VIS12 & _ & BASE12 & _) & _). cbn [PNBK.be_M] in VIS12, BASE12.
  unfold PNR.o_v, PMSP.o_v, PMSP.visitor_at in VIS12. cbn [pa_off_v pa_vp_visitor AD PnLayoutS_u.ADDR_S] in VIS12.
  pose proof BASE12 as (IMG12 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG12.
  pose proof (PNSRVK.tb_facts M12 fb s9 PA12) as TBF12. rewrite ETB in TBF12. destruct TBF12 as (B0' & U8' & U16' & _).
  (let T := type of (PNSRVDP.vlD4_conc fx12 R12 M12 (PNSRVK.tv sp r fb R (fun j => match j with 56%nat => (c9 + 1) mod 256 | 57%nat => p9 | 61%nat => ptr | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVDP.vlD4_conc fx12 R12 M12 (PNSRVK.tv sp r fb R (fun j => match j with 56%nat => (c9 + 1) mod 256 | 57%nat => p9 | 61%nat => ptr | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVDP.aligned; PMK.sc | apply tb0_long; lia | rewrite <- L5K.rl10; exact Z10])).
  destruct P as (fx13 & R13 & M13 & MG13 & _ & FRZ13 & MS13 & KS13 & _ & Y10' & _).
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M12 model9 cr9 _ sm9 _ fx12 fx13 R12 R13 _ _ M13 (fun a => sp - 96 <= a < sp - 96 + 16) K
           ltac:(lia) BR12 FOK INCS MS13 MG13 FRZ13 ltac:(intros a; apply PMK.rng_dec) ltac:(intros a Pa; cbn beta in Pa; unfold PMSP.pm_scr; clear - Pa; lia)).
  intros BR13.
  apply (PNSRVK.rv_sbmore L HI LY HIok t K LBX sp r fb cat e str R M model cr s sm ax fx13 R13 M13 model9 cr9 _ sm9 _ 1 CTX KONT BR13); [| exact Y10'|].
  - apply (PNSRVK.rv_mid_xfer R R12 R13 M12 M13 sp r fb _ MID12 KS13); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n H1 H2 i Hi; apply FRZ13; lia| lia| lia].
  - right. split; [reflexivity|]. split; [apply (PNSRVK.ec_agree M12 M13); [intros i Hi; apply FRZ13; lia|lia|lia| exact EC12]|].
    split; [destruct INV9 as (ID & SH); split; [exact ID| exact SH]|].
    split; [left; destruct TP9 as (la & ca & cb & Ea & Eb & Q); exists la, ca, cb; split; [exact Ea|]; split; [exact Eb| exact Q]|].
    intros R0. unfold PNR.bb_room in *. rewrite EBB. apply (PGV8.v8_room_mono _ (PM.unread (PNM.b_src s) sm)); [exact LEU| exact R0].
Qed.

(* [comment removed for export] *)
Lemma step2 t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax (fx9 : FPState) R9 (M9 : mem) model9 cr9 s9 sm9 ax9 :
  rv_ctx t K LBX sp r fb e str R cr s sm -> rv_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M9 model9 cr9 s9 sm9 ax9) ->
  PNSRVK.rv_mid R R9 M9 sp r fb -> PMSP.ec_at RSEGS M9 (fb + 16) e cat -> PNR.binv s9 -> PNR.btop_pos s s9 ->
  PNM.b_bb s9 = PNM.b_bb s -> PM.unread (PNM.b_src s9) sm9 <= PM.unread (PNM.b_src s) sm ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx9 R9 0x37794 M9 model9) K.
Proof.
  intros CTX KONT BR9 MID9 EC9 INV9 TP9 EBB LEU.
  pose proof MID9 as (X2 & X3 & X4 & X8 & X9 & X18 & SV9).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ _ _ _ _ _ _ BR9) as (PA9 & IA9 & GR9 & UN9 & STK9 & MOK9).
  change (PMSP.pm_scr 8) with 28672 in STK9. pose proof STK9 as (A16 & SLO & SHI & STOP & SDEF9). pose proof MOK9 as (Mh9 & Ml9 & Mm9).
  pose proof (L5C.stk_writable RSEGS _ _ sp 28672 STK9) as WR9.
  pose proof PA9 as (_ & PD9 & _).
  assert (WP9 : L5.writable RSEGS M9 (fb + 40) 416) by (apply (L5C.writable_of_defined RSEGS); [exact PD9|lia|lia]).
  destruct (PNBK2.brel_blocks RSEGS AD AN L HI KH 8 LBX sp fb str _ _ _ _ _ _ _ BR9) as (_ & OWNB9 & _).
  pose proof (PNSRVK.tb_facts M9 fb s9 PA9) as TBF.
  assert (DEFB : L5.defined M9 (sp - 64) 16) by (apply (L5.defined_sub M9 (sp - 28672) 28672); [exact SDEF9| lia| lia]).
  (* [comment removed for export] *)
  assert (RSZC : forall (fx10 : FPState) R10 (M10 : mem) x,
            brel LBX sp fb str (BENT M model cr s sm ax) (BENT M10 model9 cr9 (PNBO.set_tb s9 x (PNM.b_tg s9)) sm9 ax9) ->
            (forall k, In k [2; 3; 4; 8; 9; 18; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R10 (PMK.reg k) = getr R9 (PMK.reg k)) ->
            getr R10 (PMK.reg 1) = Z_to_bv 64 0x37cc0 -> getr R10 (PMK.reg 10) = Z_to_bv 64 (fb + 40 + 368) -> getr R10 (PMK.reg 11) = Z_to_bv 64 42 ->
            getr R10 (PMK.reg 19) = Z_to_bv 64 (fb + 40 + 368) ->
            (forall a n, sp - 48 <= a -> a + n <= sp -> L5C.agree_on M9 M10 a n) -> PMSP.ec_at RSEGS M10 (fb + 16) e cat -> PM.vs_size x = 0 ->
            srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx10 R10 0x59000 M10 model9) K).
  { intros fx10 R10 M10 x BR10 KS10 Y1 Y10 Y11 Y19 AG910 EC10 SZx.
    assert (MID10 : PNSRVK.rv_mid R R10 M10 sp r fb) by (apply (PNSRVK.rv_mid_xfer R R9 R10 M9 M10 sp r fb _ MID9 KS10); [intros k Hk; exact Hk| exact AG910| lia| lia]).
    pose proof MID10 as (W2 & W3 & W4 & W8 & W9 & W18 & SV10).
    change (@PMSP.cfg RSEGS fx10 R10 0x59000 M10 model9) with (@PMSP.cfg RSEGS fx10 R10 (pa_str_resize AD) M10 model9).
    apply (PNSRVK.brel_str_resize_tb L HI LY HIok LBX sp fb str _ M10 model9 cr9 _ sm9 ax9 fx10 R10 (sp - 96) _ 42 K RSZ K0 BR10 FOK INCS CRED Y1 ltac:(split; [lia| reflexivity]) W2 W3 W4 Y10 Y11);
      [cbn [PNBO.set_tb PNM.b_tb]; rewrite SZx; unfold PM.CHUNK; lia| unfold PM.CHUNK; lia| lia| unfold PMSP.pm_scr; lia| exact (PNSRVK.mod16_sub176 sp A16)|].
    intros fx11 R11 M11 model11 x11 g11 cr11 RP1011 SZ11 _ BR11 AG1011.
    apply (step3 t K LBX sp r fb cat e str R M model cr s sm ax fx11 R11 M11 model11 cr11 _ sm9 ax9 CTX KONT BR11).
    - apply (PNSRVK.rv_mid_pres R R10 R11 M10 M11 sp r fb MID10 RP1011); [intros a m H1 H2; apply AG1011; lia| lia| lia].
    - apply (PNSRVK.ec_agree M10 M11); [apply AG1011; lia|lia|lia| exact EC10].
    - destruct INV9 as (ID & SH). split; [exact ID| exact SH].
    - destruct TP9 as (la & ca & cb & Ea & Eb & Q). exists la, ca, cb. cbn [PNBO.set_tb PNM.b_stk]. split; [exact Ea|]. split; [exact Eb| exact Q].
    - cbn [PNBO.set_tb PNM.b_bb]. exact EBB.
    - cbn [PNBO.set_tb PNM.b_src]. exact LEU.
    - cbn [PNBO.set_tb PNM.b_tb]. exact SZ11.
    - rewrite (PMK.cs_of_preserved R10 R11 19%nat RP1011) by PMK.inl. exact Y19. }
  destruct (PNM.b_tb s9) as [n9|c9 n9 p9] eqn:ETB.
  - (* [comment removed for export] *)
    destruct TBF as (Hn9 & B0 & D24).
    (let T := type of (PNSRVDP.vlD2S_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 56%nat => 2 * n9 | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVDP.vlD2S_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 56%nat => 2 * n9 | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVDP.aligned; PMK.sc | apply tb0_short])).
    destruct P as (fx10 & R10 & M10 & MG10 & _ & FRZ10 & MS10 & KS10 & Y1 & Y10 & Y11 & _ & Y19 & (TB0 & TB1)).
    apply (PNSRVK.brel_piece_tb L HI LY HIok LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 fx9 fx10 R9 R10 _ _ M10
             (fun a => (fb + 40 + 368 <= a < fb + 40 + 368 + 2) \/ (sp - 80 <= a < sp - 80 + 16)) (PM.VShort 0) K BR9 FOK INCS MS10 MG10
             ltac:(intros a Ha N; apply FRZ10; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X])
             ltac:(intros a; apply PMK.or_dec; apply PMK.rng_dec)); [| | rewrite ETB; reflexivity| rewrite ETB; reflexivity|].
    { intros a Pa. cbn beta in Pa. destruct Pa as [X|X]; [right; left; lia| left; unfold PMSP.pm_scr; lia]. }
    { unfold PM.vstr_at. split; [apply (L5.defined_grows M9 M10 _ _ MG10 D24)|]. split; [exact I|]. split; [lia|]. replace (fb + 408) with (fb + 40 + 368) by lia. exact TB0. }
    intros BR10.
    apply (RSZC fx10 R10 M10 (PM.VShort 0) BR10); [intros k Hk; apply KS10; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| exact Y1| exact Y10| exact Y11| exact Y19
      | intros a n H1 H2 i Hi; apply FRZ10; lia| apply (PNSRVK.ec_agree M9 M10); [intros i Hi; apply FRZ10; lia|lia|lia| exact EC9]| reflexivity].
  - (* [comment removed for export] *)
    destruct TBF as (B0 & U8 & U16 & Hn9 & Hc9 & He9 & Dp & U0 & D24).
    assert (Hp9 : 4096 <= p9 /\ p9 + c9 <= hl_sptop L - 2 ^ 23).
    { destruct (OWNB9 p9 c9) as (Q0 & Q4); [| unfold hl_ceil in Q4; lia].
      unfold PNM.bparser_own, PNM.brest_own. rewrite ETB. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. cbn. auto. }
    assert (WPp : L5.writable RSEGS M9 p9 c9) by (apply (L5C.writable_of_defined RSEGS); [exact Dp|lia|lia]).
    assert (WP1 : L5.writable RSEGS M9 p9 1) by (apply (L5.writable_sub RSEGS M9 p9 c9 p9 1 WPp); lia). clear WPp.
    pose proof (Z.mod_pos_bound (c9 + 1) 256 ltac:(lia)) as MB9.
    (let T := type of (PNSRVDP.vlD2L_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 56%nat => (c9 + 1) mod 256 | 57%nat => p9 | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVDP.vlD2L_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 56%nat => (c9 + 1) mod 256 | 57%nat => p9 | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVDP.aligned; PMK.sc | apply tb0_long; lia])).
    destruct P as (fx10 & R10 & M10 & MG10 & _ & FRZ10 & MS10 & KS10 & Y1 & Y10 & Y11 & _ & Y19 & SZ0 & PB0).
    apply (PNSRVK.brel_piece_tb L HI LY HIok LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 fx9 fx10 R9 R10 _ _ M10
             (fun a => (fb + 40 + 376 <= a < fb + 40 + 376 + 8) \/ (p9 + 0 <= a < p9 + 0 + 1) \/ (sp - 80 <= a < sp - 80 + 16)) (PM.VLong c9 0 p9) K BR9 FOK INCS MS10 MG10
             ltac:(intros a Ha N; apply FRZ10; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; left; exact X| intros X; apply N; right; right; exact X])
             ltac:(intros a; apply PMK.or_dec; [| apply PMK.or_dec]; apply PMK.rng_dec)); [| | rewrite ETB; reflexivity| rewrite ETB; reflexivity|].
    { intros a Pa. cbn beta in Pa. destruct Pa as [X|[X|X]]; [right; left; lia| | left; unfold PMSP.pm_scr; lia].
      right. right. rewrite ETB. exists (p9, c9). split; [cbn; auto| cbn [fst snd]; lia]. }
    { unfold PM.vstr_at. split; [apply (L5.defined_grows M9 M10 _ _ MG10 D24)|]. split; [exact I|].
      split; [apply (L5C.u64_at_agree RSEGS M9 M10); [intros i Hi; apply FRZ10; lia|lia|lia| exact U0]|].
      split; [replace (fb + 408 + 8) with (fb + 40 + 376) by lia; exact SZ0|].
      split; [apply (L5C.u64_at_agree RSEGS M9 M10); [intros i Hi; apply FRZ10; lia|lia|lia| replace (fb + 408 + 16) with (fb + 40 + 384) by lia; exact U16]|].
      split; [lia|]. split; [lia|]. split; [exact He9|]. split; [apply (L5.defined_grows M9 M10 _ _ MG10 Dp)| exact I]. }
    intros BR10.
    apply (RSZC fx10 R10 M10 (PM.VLong c9 0 p9) BR10); [intros k Hk; apply KS10; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| exact Y1| exact Y10| exact Y11| exact Y19
      | intros a n H1 H2 i Hi; apply FRZ10; lia| apply (PNSRVK.ec_agree M9 M10); [intros i Hi; apply FRZ10; lia|lia|lia| exact EC9]| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma step1 t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax (fx9 : FPState) R9 (M9 : mem) model9 cr9 s9 sm9 ax9 (d : Z) :
  rv_ctx t K LBX sp r fb e str R cr s sm -> rv_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M9 model9 cr9 s9 sm9 ax9) ->
  PNSRVK.rv_mid R R9 M9 sp r fb -> PMSP.ec_at RSEGS M9 (fb + 16) e cat -> PNR.binv s9 -> PNR.btop_pos s s9 ->
  PNM.b_bb s9 = PNM.b_bb s -> PM.unread (PNM.b_src s9) sm9 <= PM.unread (PNM.b_src s) sm ->
  getr R9 (PMK.reg 10) = Z_to_bv 64 d -> 0 <= d <= 16 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx9 R9 0x37764 M9 model9) K.
Proof.
  intros CTX KONT BR9 MID9 EC9 INV9 TP9 EBB LEU Q10 Hd.
  pose proof MID9 as (X2 & X3 & X4 & X8 & X9 & X18 & SV9).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ _ _ _ _ _ _ BR9) as (PA9 & IA9 & GR9 & UN9 & STK9 & MOK9).
  change (PMSP.pm_scr 8) with 28672 in STK9. pose proof STK9 as (A16 & SLO & SHI & STOP & SDEF9). pose proof MOK9 as (Mh9 & Ml9 & Mm9).
  pose proof (L5C.stk_writable RSEGS _ _ sp 28672 STK9) as WR9.
  destruct (PNSRVK.rv_top L HI LY HIok LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 BR9 INV9) as (l & c & ES & OKc & UE & UP & WP & E0 & E1 & EI & EA).
  set (et := PNM.b_sb s9 + 40 * Z.of_nat (length l)) in *.
  pose proof OKc as (_ & _ & POS & _).
  (let T := type of (PNSRVDP.vlD1_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 50%nat => d | 51%nat => et + 40 | 52%nat => PNM.bs_pos c | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVDP.vlD1_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 50%nat => d | 51%nat => et + 40 | 52%nat => PNM.bs_pos c | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVDP.aligned; PMK.sc | symmetry; apply Z_to_bv_bv_unsigned])).
  assert (OKc' : PNM.bstate_ok (PNM.BS (PNM.bs_mode c) (PNM.bs_len c) ((d + PNM.bs_pos c) mod 2 ^ 64) (PNM.bs_type c) (PNM.bs_idx c)))
    by (unfold PNM.bstate_ok in OKc |- *; cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx]; pose proof (Z.mod_pos_bound (d + PNM.bs_pos c) (2 ^ 64) ltac:(lia)); lia).
  destruct P as (fx10 & R10 & M10 & MG10 & _ & FRZ10 & [(MS10 & KS10 & Y1 & Y10 & Y11 & _ & _ & LT & CP10)|(MS10 & KS10 & _ & _ & _ & LT & CP10)]).
  - (* [comment removed for export] *)
    apply (PNSRVB.pos_mkec L HI LY HIok MKE t K LBX sp r fb cat e str R M model cr s sm ax fx9 fx10 R9 R10 M9 M10 model9 cr9 s9 sm9 ax9 _
             (fun a => et + 40 - 24 <= a < et + 40 - 24 + 8) l c ((d + PNM.bs_pos c) mod 2 ^ 64)
             CTX KONT BR9 MID9 EC9 INV9 TP9 MS10 MG10 FRZ10 ltac:(intros a; apply PMK.rng_dec) ES);
      [| unfold et in E1; exact E1| unfold et in CP10; replace (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 16) with (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 40 - 24) by lia; exact CP10
      | apply Z.mod_pos_bound; lia| intros k Hk; apply KS10; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| exact Y1| exact Y10| exact Y11].
    intros a Pa. cbn beta in Pa. unfold et in Pa. right; lia.
  - (* [comment removed for export] *)
    apply (PNBK2.brel_piece_pos RSEGS AD AN L HI KH 8 LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 fx9 fx10 R9 R10 _ _ M10
             (fun a => et + 40 - 24 <= a < et + 40 - 24 + 8) l c ((d + PNM.bs_pos c) mod 2 ^ 64) K ltac:(lia) BR9 FOK INCS MS10 MG10 FRZ10 ltac:(intros a; apply PMK.rng_dec) ES);
      [intros a Pa; cbn beta in Pa; unfold et in Pa; right; lia
      | unfold et in CP10; replace (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 16) with (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 40 - 24) by lia; exact CP10
      | apply Z.mod_pos_bound; lia |].
    intros BR10.
    assert (AG910 : forall a m, (a + m <= et + 16 \/ et + 24 <= a) -> 0 <= a -> a + m <= 2 ^ 64 -> L5C.agree_on M9 M10 a m) by (intros a m H0 H1 H2 i Hi; apply FRZ10; lia).
    apply (step2 t K LBX sp r fb cat e str R M model cr s sm ax fx10 R10 M10 model9 cr9 _ sm9 ax9 CTX KONT BR10).
    + apply (PNSRVK.rv_mid_xfer R R9 R10 M9 M10 sp r fb _ MID9 KS10); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a m H1 H2; apply AG910; unfold et; lia| lia| lia].
    + apply (PNSRVK.ec_agree M9 M10); [apply AG910; unfold et; lia|lia|lia| exact EC9].
    + apply (PNBK2.binv_set_stk_top _ l c); [exact INV9| exact ES| exact OKc'| reflexivity].
    + apply (PNBK2.btop_pos_trans s s9); [exact TP9|]. apply (PNBK2.btop_pos_set_stk _ l c); [exact ES| exact OKc'| reflexivity| reflexivity| reflexivity| reflexivity].
    + cbn [PNBO.set_stk PNM.b_bb]. exact EBB.
    + cbn [PNBO.set_stk PNM.b_src]. exact LEU.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma armDec : PNSRVA.arm_stmt L HI 0x37754.
Proof.
  intros t K LBX sp r fb cat e str R M model cr s sm ax fx5 R5 M5 model5 cr5 ax5 CTX KONT BR5 MID EC5.
  pose proof MID as (X2 & X3 & X4 & X8 & X9 & X18 & SV5).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 BR5) as (PA5 & IA5 & GR5 & UN5 & STK5 & MOK5).
  change (PMSP.pm_scr 8) with 28672 in STK5. pose proof STK5 as (A16 & SLO & SHI & STOP & SDEF5). pose proof MOK5 as (Mh5 & Ml5 & Mm5).
  pose proof (L5C.stk_writable RSEGS _ M5 sp 28672 STK5) as WR5.
  (let T := type of (PNSRVDP.vlD0_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVDP.vlD0_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVDP.aligned; PMK.sc | symmetry; apply Z_to_bv_bv_unsigned])).
  destruct P as (fx6 & R6 & M6 & MG6 & EQ6w & EQ6 & MS6 & KS6 & Y1 & Y10 & Y11 & Y12).
  assert (EM6 : M6 = M5) by (apply functional_extensionality; exact EQ6w). subst M6.
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx5 fx6 R5 R6 _ _ M5 (fun _ => False) K
           ltac:(lia) BR5 FOK INCS MS6 MG6 ltac:(intros a Ha _; apply EQ6; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
  intros BR6.
  change (@PMSP.cfg RSEGS fx6 R6 0x370d0 M5 model5) with (@PMSP.cfg RSEGS fx6 R6 (pa_src_read AD) M5 model5).
  pose proof SRD as SRD'. unfold PNRS.src_read_spec, PNR.src_read_spec in SRD'.
  apply (PNBK.brel_src_read RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx6 R6 (sp - 96) _ (sp - 64) 16 K SRD' ltac:(lia) K0 BR6 FOK INCS Y1
           ltac:(split; [lia| reflexivity])); [rewrite (KS6 2%nat) by PMK.inl; exact X2| rewrite (KS6 3%nat) by PMK.inl; exact X3| rewrite (KS6 4%nat) by PMK.inl; exact X4
    | replace (fb + 56) with (fb + 40 + 16) by lia; exact Y10| exact Y11| exact Y12| lia| unfold PMSP.pm_scr; lia| exact (PNSRVK.mod16_sub176 sp A16)| lia| lia| lia|].
  intros fx7 R7 M7 src7 sm7 d RP67 Z10 Hd UNR7 DEF7 BR7 AG67.
  apply (step1 t K LBX sp r fb cat e str R M model cr s sm ax fx7 R7 M7 model5 cr5 (PNM.with_srcB s src7) sm7 ax5 d CTX KONT BR7);
    [| apply (PNSRVK.ec_agree M5 M7); [apply AG67; lia|lia|lia| exact EC5]| destruct INV0 as (ID & SH); split; [exact ID| exact SH]
     | destruct (PNBK2.btop_pos_refl s INV0) as (la & ca & cb & Ea & Eb & Q); exists la, ca, cb; split; [exact Ea|]; split; [exact Eb| exact Q]
     | reflexivity| cbn [PNM.with_srcB PNM.b_src]; lia| exact Z10| exact Hd].
  apply (PNSRVK.rv_mid_pres R R6 R7 M5 M7 sp r fb); [| exact RP67| intros a n H1 H2; apply AG67; lia| lia| lia].
  apply (PNSRVK.rv_mid_xfer R R5 R6 M5 M5 sp r fb _ MID KS6); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n _ _ i Hi; reflexivity| lia| lia].
Qed.

End WithHeap.
End PNSRVD.
