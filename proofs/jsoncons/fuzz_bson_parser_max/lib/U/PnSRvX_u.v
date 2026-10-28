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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnModelFacts PnStatics PnKeep PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj PnBrKit PnBrKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnBrKitS_u PnSRvK_u PnSRvA_u PnSRvXP_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSRVX.
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
Hypothesis RCS : PNRS.read_cstring_spec L HI.
Hypothesis PB : PNRS.str_push_back_spec L HI.

Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac fd P := PMK.feed P ltac:(first [PMK.sc | unfold PNSRVXP.aligned; PMK.sc]).

(* [comment removed for export] *)
Lemma round t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax
      (fx6 : FPState) R6 (M6 : mem) model6 cr6 s6 sm6 ax6 (rpb rcs : Z) :
  ((rpb = 0x37bfc /\ rcs = 0x37c0c) \/ (rpb = 0x37c20 /\ rcs = 0x37c30)) ->
  rv_ctx t K LBX sp r fb e str R cr s sm ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M6 model6 cr6 s6 sm6 ax6) ->
  PNSRVK.rv_mid R R6 M6 sp r fb -> getr R6 (PMK.reg 19) = Z_to_bv 64 (fb + 40 + 368) ->
  getr R6 (PMK.reg 1) = Z_to_bv 64 rpb -> getr R6 (PMK.reg 10) = Z_to_bv 64 (fb + 40 + 368) -> getr R6 (PMK.reg 11) = Z_to_bv 64 47 ->
  PMSP.ec_at RSEGS M6 (fb + 16) e cat -> PNR.binv s6 -> PM.vs_size (PNM.b_tb s6) + PM.unread (PNM.b_src s6) sm6 + 1 <= 2 ^ 26 ->
  PM.unread (PNM.b_src s6) sm6 <= PM.unread (PNM.b_src s) sm ->
  (forall (fx9 : FPState) R9 (M9 : mem) model9 s8 s9 sm9 ax9 cr9,
      PNR.brun_post RSEGS AD AN false (PNR.bprog_cs 1) R9 M9 fb s8 s9 str sm6 sm9 ax6 ax9 cat e ->
      PNM.b_stk s8 = PNM.b_stk s6 -> PNM.b_src s8 = PNM.b_src s6 -> PNM.b_bb s8 = PNM.b_bb s6 -> PM.vs_size (PNM.b_tb s8) = PM.vs_size (PNM.b_tb s6) + 1 ->
      brel LBX sp fb str (BENT M model cr s sm ax) (BENT M9 model9 cr9 s9 sm9 ax9) ->
      PNSRVK.rv_mid R R9 M9 sp r fb -> getr R9 (PMK.reg 19) = Z_to_bv 64 (fb + 40 + 368) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx9 R9 rcs M9 model9) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0x58938 M6 model6) K.
Proof.
  intros HR CTX BR6 MID6 X19 Y1 Y10 Y11 EC6 INV6 SZ6 LE6 KONT.
  pose proof MID6 as (X2 & X3 & X4 & X8 & X9 & X18 & SV6).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M6 model6 cr6 s6 sm6 ax6 BR6) as (PA6 & IA6 & GR6 & UN6 & STK6 & MOK6).
  change (PMSP.pm_scr 8) with 28672 in STK6. pose proof STK6 as (A16 & SLO & SHI & STOP & SDEF6).
  assert (Hrpb : 0 <= rpb < 2 ^ 47 /\ rpb mod 2 = 0) by (destruct HR as [(-> & _)|(-> & _)]; (split; [lia| reflexivity])).
  change (@PMSP.cfg RSEGS fx6 R6 0x58938 M6 model6) with (@PMSP.cfg RSEGS fx6 R6 (PNL.pn_str_push_back AN) M6 model6).
  pose proof PB as PB'. unfold PNRS.str_push_back_spec in PB'.
  apply (PNBK.brel_push_back_tb RSEGS AD AN L HI KH 8 LBX sp fb str _ M6 model6 cr6 s6 sm6 ax6 fx6 R6 (sp - 96) rpb 47 K PB' ltac:(lia) K0 BR6 FOK INCS CRED Y1 Hrpb X2 X3 X4 Y10 Y11
           ltac:(lia) ltac:(lia) ltac:(unfold PMSP.pm_scr; lia) (PNSRVK.mod16_sub176 sp A16) ltac:(lia)).
  intros fx7 R7 M7 model7 x7 g7 cr7 RP67 SZ7 BR7 AG67.
  set (s7 := PNBO.set_tb s6 x7 g7) in *.
  assert (MID7 : PNSRVK.rv_mid R R7 M7 sp r fb) by (apply (PNSRVK.rv_mid_pres R R6 R7 M6 M7 sp r fb MID6 RP67); [intros a n H1 H2; apply AG67; lia| lia| lia]).
  pose proof MID7 as (W2 & W3 & W4 & W8 & W9 & W18 & SV7).
  assert (EC7 : PMSP.ec_at RSEGS M7 (fb + 16) e cat) by (apply (PNSRVK.ec_agree M6 M7); [apply AG67; lia|lia|lia| exact EC6]).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M7 model7 cr7 s7 sm6 ax6 BR7) as (PA7 & IA7 & GR7 & UN7 & STK7 & MOK7).
  change (PMSP.pm_scr 8) with 28672 in STK7. pose proof STK7 as (A16' & _ & _ & _ & SDEF7). pose proof MOK7 as (Mh7 & Ml7 & Mm7).
  pose proof (L5C.stk_writable RSEGS _ M7 sp 28672 STK7) as WR7.
  (* [comment removed for export] *)
  assert (STEP : exists (fx8 : FPState) R8, msteps RSEGS (@mkst fx7 R7 (Z_to_bv 64 rpb) M7 (seg_rom RSEGS)) (@mkst fx8 R8 (Z_to_bv 64 0x383f8) M7 (seg_rom RSEGS))
            /\ (forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R8 (PMK.reg k) = getr R7 (PMK.reg k))
            /\ getr R8 (PMK.reg 1) = Z_to_bv 64 rcs /\ getr R8 (PMK.reg 10) = Z_to_bv 64 (fb + 40)
            /\ getr R8 (PMK.reg 11) = Z_to_bv 64 (fb + 40 + 368) /\ getr R8 (PMK.reg 12) = Z_to_bv 64 (fb + 16)).
  { assert (X19' : getr R7 (PMK.reg 19) = Z_to_bv 64 (fb + 40 + 368)) by (rewrite (PMK.cs_of_preserved R6 R7 19%nat RP67) by PMK.inl; exact X19).
    destruct HR as [(-> & ->)|(-> & ->)].
    - (let T := type of (PNSRVXP.vlX1_conc fx7 R7 M7 (PNSRVK.tv sp r fb R (fun _ => 0))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVXP.vlX1_conc fx7 R7 M7 (PNSRVK.tv sp r fb R (fun _ => 0))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVXP.aligned; PMK.sc])).
      destruct P as (fx8 & R8 & M8 & MG8 & EQ8w & EQ8 & MS8 & KS8 & Z1 & Z10 & Z11 & Z12).
      assert (EM8 : M8 = M7) by (apply functional_extensionality; exact EQ8w). subst M8.
      exists fx8, R8. split; [exact MS8|]. split; [intros k Hk; apply KS8; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto|]. split; [exact Z1|]. split; [exact Z10|]. split; [exact Z11| exact Z12].
    - (let T := type of (PNSRVXP.vlX3_conc fx7 R7 M7 (PNSRVK.tv sp r fb R (fun _ => 0))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVXP.vlX3_conc fx7 R7 M7 (PNSRVK.tv sp r fb R (fun _ => 0))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVXP.aligned; PMK.sc])).
      destruct P as (fx8 & R8 & M8 & MG8 & EQ8w & EQ8 & MS8 & KS8 & Z1 & Z10 & Z11 & Z12).
      assert (EM8 : M8 = M7) by (apply functional_extensionality; exact EQ8w). subst M8.
      exists fx8, R8. split; [exact MS8|]. split; [intros k Hk; apply KS8; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto|]. split; [exact Z1|]. split; [exact Z10|]. split; [exact Z11| exact Z12]. }
  destruct STEP as (fx8 & R8 & MS8 & KS8 & Z1 & Z10 & Z11 & Z12).
  assert (Hrcs : 0 <= rcs < 2 ^ 47 /\ rcs mod 2 = 0) by (destruct HR as [(_ & ->)|(_ & ->)]; (split; [lia| reflexivity])).
  eapply (L5.cps_of_msteps RSEGS); [exact Mh7| exact Ml7| exact MS8|].
  change (mkCfg (@mkst fx8 R8 (Z_to_bv 64 0x383f8) M7 (seg_rom RSEGS)) model7) with (@PMSP.cfg RSEGS fx8 R8 (PNL.pn_read_cstring AN) M7 model7).
  pose proof RCS as RCS'. unfold PNRS.read_cstring_spec, PNR.read_cstring_spec in RCS'.
  apply (PNBK2.brel_call RSEGS AD AN L HI KH false _ 5 (PNR.bargs_cs AD 1) (PNR.bprog_cs 1) 8 LBX sp fb str _ M7 model7 cr7 s7 sm6 ax6 fx8 R8 (sp - 96) rcs cat e K
           (RCS' 1 (or_intror eq_refl)) ltac:(lia) ltac:(lia) K0 BR7 FOK INCS CRED Z1 Hrcs); [rewrite (KS8 2%nat) by PMK.inl; exact W2| rewrite (KS8 3%nat) by PMK.inl; exact W3| rewrite (KS8 4%nat) by PMK.inl; exact W4
    | lia| unfold PMSP.pm_scr; lia| exact (PNSRVK.mod16_sub176 sp A16)| | | exact EC7| exact He| cbn [s7 PNBO.set_tb PNM.b_src]; lia|].
  { unfold PNR.bargs_cs, PNR.o_p, PNR.o_ec, PMSP.o_p, PMSP.o_ec, PNR.bcs_off, PNR.bcs_str, PNM.OFF_TB. cbn [Z.eqb pa_off_p pa_off_ec AD PnLayoutS_u.ADDR_S s7 PNBO.set_tb PNM.b_tb PNM.b_src].
    rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact Z10|]. split; [exact Z11|]. split; [exact Z12| lia]. }
  { destruct INV6 as (ID & SH). split; [exact ID| exact SH]. }
  intros fx9 R9 M9 model9 s9 sm9 ax9 cr9 RP89 POST BR9 AG89.
  apply (KONT fx9 R9 M9 model9 s7 s9 sm9 ax9 cr9 POST eq_refl eq_refl eq_refl); [cbn [s7 PNBO.set_tb PNM.b_tb]; exact SZ7| exact BR9| |].
  - apply (PNSRVK.rv_mid_pres R R8 R9 M7 M9 sp r fb); [| exact RP89| intros a n H1 H2; apply AG89; lia| lia| lia].
    apply (PNSRVK.rv_mid_xfer R R7 R8 M7 M7 sp r fb _ MID7 KS8); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n _ _ i Hi; reflexivity| lia| lia].
  - rewrite (PMK.cs_of_preserved R8 R9 19%nat RP89) by PMK.inl. rewrite (KS8 19%nat) by PMK.inl. rewrite (PMK.cs_of_preserved R6 R7 19%nat RP67) by PMK.inl. exact X19.
Qed.

(* [comment removed for export] *)
Definition xst t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax (R9 : bvmap 5 word) (M9 : mem) model9 cr9 s9 sm9 ax9 : Prop :=
  rv_ctx t K LBX sp r fb e str R cr s sm /\ rv_kont K LBX sp r fb cat e str R M model cr s sm ax
  /\ brel LBX sp fb str (BENT M model cr s sm ax) (BENT M9 model9 cr9 s9 sm9 ax9)
  /\ PNSRVK.rv_mid R R9 M9 sp r fb /\ getr R9 (PMK.reg 19) = Z_to_bv 64 (fb + 40 + 368)
  /\ PNM.b_bb s9 = PNM.b_bb s /\ PM.unread (PNM.b_src s9) sm9 <= PM.unread (PNM.b_src s) sm.

(* [comment removed for export] *)
Lemma tail5 t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax (fx9 : FPState) R9 (M9 : mem) model9 cr9 s9 sm9 ax9 :
  xst t K LBX sp r fb cat e str R M model cr s sm ax R9 M9 model9 cr9 s9 sm9 ax9 ->
  PMSP.ec_at RSEGS M9 (fb + 16) e cat -> PNR.binv s9 -> PNR.btop_pos s s9 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx9 R9 0x37c38 M9 model9) K.
Proof.
  intros (CTX & KONT & BR9 & MID9 & X19 & EBB & LEU) EC9 INV9 TP9.
  pose proof MID9 as (X2 & X3 & X4 & X8 & X9 & X18 & SV9).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 BR9) as (PA9 & IA9 & GR9 & UN9 & STK9 & MOK9).
  change (PMSP.pm_scr 8) with 28672 in STK9. pose proof STK9 as (A16 & SLO & SHI & STOP & SDEF9).
  pose proof (L5C.stk_writable RSEGS _ M9 sp 28672 STK9) as WR9.
  pose proof PA9 as (_ & PD9 & _ & _ & _ & CM9 & _).
  assert (WP9 : L5.writable RSEGS M9 (fb + 40) 416) by (apply (L5C.writable_of_defined RSEGS); [exact PD9|lia|lia]).
  pose proof BR9 as ((_ & _ & VIS9 & _ & BASE9 & _) & _). cbn [PNBK.be_M] in VIS9, BASE9.
  unfold PNR.o_v, PMSP.o_v, PMSP.visitor_at in VIS9. cbn [pa_off_v pa_vp_visitor AD PnLayoutS_u.ADDR_S] in VIS9.
  pose proof BASE9 as (IMG9 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG9.
  destruct (PNBK2.brel_blocks RSEGS AD AN L HI KH 8 LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 BR9) as (_ & OWNB9 & _).
  pose proof (PNSRVK.tb_facts M9 fb s9 PA9) as TBF.
  assert (FIN : forall (fx10 : FPState) R10 (M10 : mem),
            msteps RSEGS (@mkst fx9 R9 (Z_to_bv 64 0x37c38) M9 (seg_rom RSEGS)) (@mkst fx10 R10 (Z_to_bv 64 0x37d74) M10 (seg_rom RSEGS)) -> mem_grows M9 M10 ->
            (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 64 <= i < sp - 64 + 16) -> M10 (Z_to_bv 64 i) = M9 (Z_to_bv 64 i)) ->
            (forall k, In k [2; 3; 4; 8; 9; 18; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R10 (PMK.reg k) = getr R9 (PMK.reg k)) -> getr R10 (PMK.reg 10) = Z_to_bv 64 1 ->
            srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx9 R9 0x37c38 M9 model9) K).
  { intros fx10 R10 M10 MS10 MG10 FRZ10 KS10 Y10.
    apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 fx9 fx10 R9 R10 _ _ M10 (fun a => sp - 64 <= a < sp - 64 + 16) K
             ltac:(lia) BR9 FOK INCS MS10 MG10 FRZ10 ltac:(intros a; apply PMK.rng_dec) ltac:(intros a Pa; cbn beta in Pa; unfold PMSP.pm_scr; clear - Pa; lia)).
    intros BR10.
    apply (PNSRVK.rv_sbmore L HI LY HIok t K LBX sp r fb cat e str R M model cr s sm ax fx10 R10 M10 model9 cr9 s9 sm9 ax9 1 CTX KONT BR10); [| exact Y10|].
    - apply (PNSRVK.rv_mid_xfer R R9 R10 M9 M10 sp r fb _ MID9 KS10); [intros k Hk; exact Hk| intros a n H1 H2 i Hi; apply FRZ10; lia| lia| lia].
    - right. split; [reflexivity|]. split; [apply (PNSRVK.ec_agree M9 M10); [intros i Hi; apply FRZ10; lia|lia|lia| exact EC9]|].
      split; [exact INV9|]. split; [left; exact TP9|].
      intros R0. unfold PNR.bb_room in *. rewrite EBB. apply (PGV8.v8_room_mono _ (PM.unread (PNM.b_src s) sm)); [exact LEU| exact R0]. }
  destruct (PNM.b_tb s9) as [n9|c9 n9 p9] eqn:ETB.
  - destruct TBF as (Hn9 & B0 & D24).
    (let T := type of (PNSRVXP.vlX5S_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 56%nat => 2 * n9 | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVXP.vlX5S_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 56%nat => 2 * n9 | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVXP.aligned; PMK.sc | apply tb0_short])).
    destruct P as (fx10 & R10 & M10 & MG10 & _ & FRZ10 & MS10 & KS10 & _ & Y10 & _).
    apply (FIN fx10 R10 M10 MS10 MG10 FRZ10); [intros k Hk; apply KS10; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| exact Y10].
  - destruct TBF as (B0 & U8 & U16 & Hn9 & Hc9 & He9 & Dp & U0 & D24).
    assert (Hp9 : 4096 <= p9 /\ p9 + c9 <= hl_sptop L - 2 ^ 23).
    { destruct (OWNB9 p9 c9) as (Q0 & Q4); [| unfold hl_ceil in Q4; lia].
      unfold PNM.bparser_own, PNM.brest_own. rewrite ETB. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. cbn. auto. }
    pose proof (Z.mod_pos_bound (c9 + 1) 256 ltac:(lia)) as MB9.
    (let T := type of (PNSRVXP.vlX5L_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 56%nat => (c9 + 1) mod 256 | 57%nat => p9 | 58%nat => n9 | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVXP.vlX5L_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 56%nat => (c9 + 1) mod 256 | 57%nat => p9 | 58%nat => n9 | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVXP.aligned; PMK.sc | apply tb0_long; lia])).
    destruct P as (fx10 & R10 & M10 & MG10 & _ & FRZ10 & MS10 & KS10 & _ & Y10 & _).
    apply (FIN fx10 R10 M10 MS10 MG10 FRZ10); [intros k Hk; apply KS10; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| exact Y10].
Qed.

(* [comment removed for export] *)
Definition xpost (fb cat e : Z) (s : PNM.bpst) (M9 : mem) (s9 : PNM.bpst) (sm9 : PM.strm) (ax9 : PNST.bax) : Prop :=
  (exists v, 1 <= v <= 64 /\ PMSP.ec_at RSEGS M9 (fb + 16) v (pa_errcat_obj AD) /\ PNM.b_more s9 = 0 /\ PNST.bax_cat ax9 = true
             /\ (length (PNM.b_stk s) <= length (PNM.b_stk s9))%nat /\ PNR.binv s9)
  \/ (PMSP.ec_at RSEGS M9 (fb + 16) e cat /\ PNR.binv s9 /\ PNR.btop_pos s s9 /\ PM.vs_size (PNM.b_tb s9) + PM.unread (PNM.b_src s9) sm9 + 1 <= 2 ^ 26).

Lemma xpost_ecv fb cat e s (sm : PM.strm) (M9 : mem) s9 (sm9 : PM.strm) ax9 (R9 : bvmap 5 word) :
  xpost fb cat e s M9 s9 sm9 ax9 -> 0 <= e <= 64 -> PNM.b_bb s9 = PNM.b_bb s -> PM.unread (PNM.b_src s9) sm9 <= PM.unread (PNM.b_src s) sm ->
  exists ecv, 0 <= ecv <= 64 /\ L5.u32_at RSEGS M9 (fb + 16) ecv /\ L5.defined M9 (fb + 16) 16
    /\ PNSRVK.rv_post fb cat e s sm R9 M9 s9 sm9 ax9
    /\ (ecv = 0 -> PMSP.ec_at RSEGS M9 (fb + 16) e cat /\ PNR.binv s9 /\ PNR.btop_pos s s9 /\ PM.vs_size (PNM.b_tb s9) + PM.unread (PNM.b_src s9) sm9 + 1 <= 2 ^ 26).
Proof.
  intros XP He EBB LEU.
  destruct XP as [(v & Hv & (E1 & E2 & E3) & MO & CAT & LEN & INV9)|((E1 & E2 & E3) & INV9 & TP & SZ)].
  - exists v. split; [lia|]. split; [exact E1|]. split; [exact E3|]. split; [| intros ->; lia].
    split; [left; split; [exists v; split; [exact Hv| split; [exact E1| split; [exact E2| exact E3]]]| split; [exact MO| split; [exact CAT| split; [exact LEN| exact INV9]]]]|].
    intros _ M1. rewrite MO in M1. lia.
  - exists e. split; [exact He|]. split; [exact E1|]. split; [exact E3|].
    split; [| intros _; split; [split; [exact E1| split; [exact E2| exact E3]]| split; [exact INV9| split; [exact TP| exact SZ]]]].
    split; [right; split; [split; [exact E1| split; [exact E2| exact E3]]| split; [exact INV9| left; exact TP]]|].
    intros R0 _. unfold PNR.bb_room in *. rewrite EBB. apply (PGV8.v8_room_mono _ (PM.unread (PNM.b_src s) sm)); [exact LEU| exact R0].
Qed.

(* [comment removed for export] *)
Lemma xpost_of_round fb cat e (str : PM.vstr) s (sm : PM.strm) (R9 : bvmap 5 word) (M9 : mem) s6 s8 s9 (sm6 sm9 : PM.strm) ax6 ax9 :
  PNR.brun_post RSEGS AD AN false (PNR.bprog_cs 1) R9 M9 fb s8 s9 str sm6 sm9 ax6 ax9 cat e ->
  PNM.b_stk s8 = PNM.b_stk s6 -> PNM.b_src s8 = PNM.b_src s6 -> PM.vs_size (PNM.b_tb s8) = PM.vs_size (PNM.b_tb s6) + 1 ->
  PNR.binv s6 -> PNR.btop_pos s s6 -> PM.vs_size (PNM.b_tb s6) + PM.unread (PNM.b_src s6) sm6 + 1 <= 2 ^ 26 ->
  xpost fb cat e s M9 s9 sm9 ax9 /\ PNM.b_bb s9 = PNM.b_bb s8 /\ PM.unread (PNM.b_src s9) sm9 <= PM.unread (PNM.b_src s6) sm6.
Proof.
  intros (RP & STEP & AXL & DISJ & BB) EK ES ET INV6 TP6 SZ6. cbn [PNR.bb_post] in BB.
  unfold PNR.o_ec, PMSP.o_ec in DISJ. cbn [pa_off_ec AD PnLayoutS_u.ADDR_S] in DISJ.
  destruct STEP as (_ & _ & _ & _ & LE). rewrite ES in LE.
  split; [| split; [exact BB| exact LE]].
  destruct DISJ as [(v & Hv & EC & MO & CAT & LEN & INV9)|(EC & INV9 & (TP & LT & SZ))].
  - left. exists v. split; [exact Hv|]. split; [exact EC|]. split; [exact MO|]. split; [exact CAT|]. split; [| exact INV9].
    rewrite EK in LEN. destruct TP6 as (l0 & c0 & c0' & Ea & Eb & _). rewrite Ea. rewrite Eb in LEN. rewrite !length_app in *. cbn [length] in *. lia.
  - right. split; [exact EC|]. split; [exact INV9|]. split.
    + apply (PNBK2.btop_pos_trans s s6 s9 TP6). destruct TP as (l0 & c0 & c0' & Ea & Eb & Q). exists l0, c0, c0'. rewrite <- EK. split; [exact Ea|]. split; [exact Eb| exact Q].
    + unfold PNR.bcs_str in SZ. cbn [Z.eqb] in SZ. rewrite ES, ET in SZ. lia.
Qed.

(* [comment removed for export] *)
Lemma after2 t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax (fx9 : FPState) R9 (M9 : mem) model9 cr9 s9 sm9 ax9 :
  xst t K LBX sp r fb cat e str R M model cr s sm ax R9 M9 model9 cr9 s9 sm9 ax9 -> xpost fb cat e s M9 s9 sm9 ax9 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx9 R9 0x37c30 M9 model9) K.
Proof.
  intros XS XP. pose proof XS as (CTX & KONT & BR9 & MID9 & X19 & EBB & LEU).
  pose proof MID9 as (X2 & X3 & X4 & X8 & X9 & X18 & SV9).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 BR9) as (PA9 & IA9 & GR9 & UN9 & STK9 & MOK9).
  change (PMSP.pm_scr 8) with 28672 in STK9. pose proof STK9 as (A16 & SLO & SHI & STOP & SDEF9).
  pose proof (L5C.stk_writable RSEGS _ M9 sp 28672 STK9) as WR9.
  destruct (xpost_ecv fb cat e s sm M9 s9 sm9 ax9 R9 XP He EBB LEU) as (ecv & Hecv & U32 & ED9 & RVP & OKP).
  (let T := type of (PNSRVXP.vlX4_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 60%nat => ecv | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVXP.vlX4_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 60%nat => ecv | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVXP.aligned; PMK.sc])).
  destruct P as (fx10 & R10 & M10 & MG10 & EQ10w & EQ10 & [(MS10 & KS10 & _ & LT)|(MS10 & KS10 & LT)]);
    assert (EM10 : M10 = M9) by (apply functional_extensionality; exact EQ10w); subst M10.
  - apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 fx9 fx10 R9 R10 _ _ M9 (fun _ => False) K
             ltac:(lia) BR9 FOK INCS MS10 MG10 ltac:(intros a Ha _; apply EQ10; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
    intros BR10.
    assert (MID10 : PNSRVK.rv_mid R R10 M9 sp r fb).
    { apply (PNSRVK.rv_mid_xfer R R9 R10 M9 M9 sp r fb _ MID9 KS10); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n _ _ i Hi; reflexivity| lia| lia]. }
    pose proof MID10 as (V2 & V3 & V4 & V8 & V9 & V18 & SV10 & SX10).
    exact (PNSRVK.rv_epi L HI LY HIok t K LBX sp r fb cat e str R M model cr s sm ax fx10 R10 M9 model9 cr9 s9 sm9 ax9 CTX KONT BR10 V2 V3 V4 V8 V9 V18 SV10 SX10 RVP).
  - rewrite Z.sub_0_r, Z.mod_small in LT by lia. destruct (OKP ltac:(lia)) as (EC9 & INV9 & TP9 & _).
    apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 fx9 fx10 R9 R10 _ _ M9 (fun _ => False) K
             ltac:(lia) BR9 FOK INCS MS10 MG10 ltac:(intros a Ha _; apply EQ10; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
    intros BR10.
    apply (tail5 t K LBX sp r fb cat e str R M model cr s sm ax fx10 R10 M9 model9 cr9 s9 sm9 ax9); [| exact EC9| exact INV9| exact TP9].
    split; [exact CTX|]. split; [exact KONT|]. split; [exact BR10|]. split.
    { apply (PNSRVK.rv_mid_xfer R R9 R10 M9 M9 sp r fb _ MID9 KS10); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n _ _ i Hi; reflexivity| lia| lia]. }
    split; [rewrite (KS10 19%nat) by PMK.inl; exact X19|]. split; [exact EBB| exact LEU].
Qed.

(* [comment removed for export] *)
Lemma after1 t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax (fx9 : FPState) R9 (M9 : mem) model9 cr9 s9 sm9 ax9 :
  xst t K LBX sp r fb cat e str R M model cr s sm ax R9 M9 model9 cr9 s9 sm9 ax9 -> xpost fb cat e s M9 s9 sm9 ax9 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx9 R9 0x37c0c M9 model9) K.
Proof.
  intros XS XP. pose proof XS as (CTX & KONT & BR9 & MID9 & X19 & EBB & LEU).
  pose proof MID9 as (X2 & X3 & X4 & X8 & X9 & X18 & SV9).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 BR9) as (PA9 & IA9 & GR9 & UN9 & STK9 & MOK9).
  change (PMSP.pm_scr 8) with 28672 in STK9. pose proof STK9 as (A16 & SLO & SHI & STOP & SDEF9).
  pose proof (L5C.stk_writable RSEGS _ M9 sp 28672 STK9) as WR9.
  destruct (xpost_ecv fb cat e s sm M9 s9 sm9 ax9 R9 XP He EBB LEU) as (ecv & Hecv & U32 & ED9 & RVP & OKP).
  (let T := type of (PNSRVXP.vlX2_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 60%nat => ecv | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVXP.vlX2_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 60%nat => ecv | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVXP.aligned; PMK.sc])).
  destruct P as (fx10 & R10 & M10 & MG10 & EQ10w & EQ10 & [(MS10 & KS10 & _ & LT)|(MS10 & KS10 & Z1 & Z10 & Z11 & LT)]);
    assert (EM10 : M10 = M9) by (apply functional_extensionality; exact EQ10w); subst M10.
  - apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 fx9 fx10 R9 R10 _ _ M9 (fun _ => False) K
             ltac:(lia) BR9 FOK INCS MS10 MG10 ltac:(intros a Ha _; apply EQ10; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
    intros BR10.
    assert (MID10 : PNSRVK.rv_mid R R10 M9 sp r fb).
    { apply (PNSRVK.rv_mid_xfer R R9 R10 M9 M9 sp r fb _ MID9 KS10); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n _ _ i Hi; reflexivity| lia| lia]. }
    pose proof MID10 as (V2 & V3 & V4 & V8 & V9 & V18 & SV10 & SX10).
    exact (PNSRVK.rv_epi L HI LY HIok t K LBX sp r fb cat e str R M model cr s sm ax fx10 R10 M9 model9 cr9 s9 sm9 ax9 CTX KONT BR10 V2 V3 V4 V8 V9 V18 SV10 SX10 RVP).
  - rewrite Z.sub_0_r, Z.mod_small in LT by lia. destruct (OKP ltac:(lia)) as (EC9 & INV9 & TP9 & SZ9).
    apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 fx9 fx10 R9 R10 _ _ M9 (fun _ => False) K
             ltac:(lia) BR9 FOK INCS MS10 MG10 ltac:(intros a Ha _; apply EQ10; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
    intros BR10.
    assert (MID10 : PNSRVK.rv_mid R R10 M9 sp r fb).
    { apply (PNSRVK.rv_mid_xfer R R9 R10 M9 M9 sp r fb _ MID9 KS10); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n _ _ i Hi; reflexivity| lia| lia]. }
    apply (round t K LBX sp r fb cat e str R M model cr s sm ax fx10 R10 M9 model9 cr9 s9 sm9 ax9 0x37c20 0x37c30 ltac:(right; split; reflexivity) CTX BR10 MID10);
      [rewrite (KS10 19%nat) by PMK.inl; exact X19| exact Z1| rewrite Z10; f_equal; lia| exact Z11| exact EC9| exact INV9| exact SZ9| exact LEU|].
    intros fx12 R12 M12 model12 s11 s12 sm12 ax12 cr12 POST12 EK ES EB ET BR12 MID12 W19.
    destruct (xpost_of_round fb cat e str s sm R12 M12 s9 s11 s12 sm9 sm12 ax9 ax12 POST12 EK ES ET INV9 TP9 SZ9) as (XP12 & BB12 & LE12).
    apply (after2 t K LBX sp r fb cat e str R M model cr s sm ax fx12 R12 M12 model12 cr12 s12 sm12 ax12); [| exact XP12].
    split; [exact CTX|]. split; [exact KONT|]. split; [exact BR12|]. split; [exact MID12|]. split; [exact W19|]. split; [rewrite BB12, EB; exact EBB| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma armX : PNSRVA.arm_stmt L HI 0x377c4.
Proof.
  intros t K LBX sp r fb cat e str R M model cr s sm ax fx5 R5 M5 model5 cr5 ax5 CTX KONT BR5 MID EC5.
  pose proof MID as (X2 & X3 & X4 & X8 & X9 & X18 & SV5).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  assert (AL40 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 BR5) as (PA5 & IA5 & GR5 & UN5 & STK5 & MOK5).
  change (PMSP.pm_scr 8) with 28672 in STK5. pose proof STK5 as (A16 & SLO & SHI & STOP & SDEF5). pose proof MOK5 as (Mh5 & Ml5 & Mm5).
  pose proof (L5C.stk_writable RSEGS _ M5 sp 28672 STK5) as WR5.
  pose proof PA5 as (_ & PD5 & _).
  assert (WP5 : L5.writable RSEGS M5 (fb + 40) 416) by (apply (L5C.writable_of_defined RSEGS); [exact PD5|lia|lia]).
  destruct (PNBK2.brel_blocks RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 BR5) as (_ & OWNB5 & _).
  pose proof (PNSRVK.tb_facts M5 fb s PA5) as TBF.
  (* [comment removed for export] *)
  assert (CLR : forall (fx6 : FPState) R6 (M6 : mem) x,
            brel LBX sp fb str (BENT M model cr s sm ax) (BENT M6 model5 cr5 (PNBO.set_tb s x (PNM.b_tg s)) sm ax5) ->
            (forall k, In k [2; 3; 4; 8; 9; 18; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R6 (PMK.reg k) = getr R5 (PMK.reg k)) ->
            getr R6 (PMK.reg 1) = Z_to_bv 64 0x37bfc -> getr R6 (PMK.reg 10) = Z_to_bv 64 (fb + 40 + 368) -> getr R6 (PMK.reg 11) = Z_to_bv 64 47 ->
            getr R6 (PMK.reg 19) = Z_to_bv 64 (fb + 40 + 368) ->
            (forall a n, sp - 48 <= a -> a + n <= sp -> L5C.agree_on M5 M6 a n) -> PMSP.ec_at RSEGS M6 (fb + 16) e cat -> PM.vs_size x = 0 ->
            srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0x58938 M6 model5) K).
  { intros fx6 R6 M6 x BR6 KS6 Y1 Y10 Y11 Y19 AG56 EC6 SZx.
    assert (MID6 : PNSRVK.rv_mid R R6 M6 sp r fb) by (apply (PNSRVK.rv_mid_xfer R R5 R6 M5 M6 sp r fb _ MID KS6); [intros k Hk; exact Hk| exact AG56| lia| lia]).
    assert (INV6 : PNR.binv (PNBO.set_tb s x (PNM.b_tg s))) by (destruct INV0 as (ID & SH); split; [exact ID| exact SH]).
    apply (round t K LBX sp r fb cat e str R M model cr s sm ax fx6 R6 M6 model5 cr5 _ sm ax5 0x37bfc 0x37c0c ltac:(left; split; reflexivity) CTX BR6 MID6 Y19 Y1 Y10 Y11 EC6 INV6);
      [cbn [PNBO.set_tb PNM.b_tb PNM.b_src]; rewrite SZx; lia| cbn [PNBO.set_tb PNM.b_src]; lia|].
    intros fx9 R9 M9 model9 s8 s9 sm9 ax9 cr9 POST EK ES EB ET BR9 MID9 W19.
    destruct (xpost_of_round fb cat e str s sm R9 M9 (PNBO.set_tb s x (PNM.b_tg s)) s8 s9 sm sm9 ax5 ax9 POST EK ES ET INV6 ltac:(destruct (PNBK2.btop_pos_refl s INV0) as (la & ca & cb & Ea & Eb & Q); exists la, ca, cb; cbn [PNBO.set_tb PNM.b_stk]; split; [exact Ea|]; split; [exact Eb| exact Q])
                ltac:(cbn [PNBO.set_tb PNM.b_tb PNM.b_src]; rewrite SZx; lia)) as (XP9 & BB9 & LE9).
    apply (after1 t K LBX sp r fb cat e str R M model cr s sm ax fx9 R9 M9 model9 cr9 s9 sm9 ax9); [| exact XP9].
    split; [exact CTX|]. split; [exact KONT|]. split; [exact BR9|]. split; [exact MID9|]. split; [exact W19|].
    split; [rewrite BB9, EB; reflexivity| cbn [PNBO.set_tb PNM.b_src] in LE9; exact LE9]. }
  destruct (PNM.b_tb s) as [n0|c0 n0 p0] eqn:ETB.
  - (* [comment removed for export] *)
    destruct TBF as (Hn0 & B0 & D24).
    (let T := type of (PNSRVXP.vlX0S_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun j => match j with 56%nat => 2 * n0 | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVXP.vlX0S_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun j => match j with 56%nat => 2 * n0 | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVXP.aligned; PMK.sc | apply tb0_short])).
    destruct P as (fx6 & R6 & M6 & MG6 & _ & FRZ6 & MS6 & KS6 & Y1 & Y10 & Y11 & Y19 & (TB0 & TB1)).
    apply (PNSRVK.brel_piece_tb L HI LY HIok LBX sp fb str _ M5 model5 cr5 s sm ax5 fx5 fx6 R5 R6 _ _ M6
             (fun a => fb + 40 + 368 <= a < fb + 40 + 368 + 2) (PM.VShort 0) K BR5 FOK INCS MS6 MG6 FRZ6 ltac:(intros a; apply PMK.rng_dec)
             ltac:(intros a Pa; cbn beta in Pa; right; left; clear -Pa; lia)); [| rewrite ETB; reflexivity| rewrite ETB; reflexivity|].
    { unfold PM.vstr_at. split; [apply (L5.defined_grows M5 M6 _ _ MG6 D24)|]. split; [exact I|]. split; [lia|]. replace (fb + 408) with (fb + 40 + 368) by lia. exact TB0. }
    intros BR6.
    apply (CLR fx6 R6 M6 (PM.VShort 0) BR6); [intros k Hk; apply KS6; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| exact Y1| exact Y10| exact Y11| exact Y19
      | intros a n H1 H2 i Hi; apply FRZ6; lia| apply (PNSRVK.ec_agree M5 M6); [intros i Hi; apply FRZ6; lia|lia|lia| exact EC5]| reflexivity].
  - (* [comment removed for export] *)
    destruct TBF as (B0 & U8 & U16 & Hn0 & Hc0 & He0 & Dp & U0 & D24).
    assert (Hp0 : 4096 <= p0 /\ p0 + c0 <= hl_sptop L - 2 ^ 23).
    { destruct (OWNB5 p0 c0) as (Q0 & Q4); [| unfold hl_ceil in Q4; lia].
      unfold PNM.bparser_own, PNM.brest_own. rewrite ETB. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. cbn. auto. }
    assert (WPp : L5.writable RSEGS M5 p0 c0) by (apply (L5C.writable_of_defined RSEGS); [exact Dp|lia|lia]).
    assert (WP1 : L5.writable RSEGS M5 p0 1) by (apply (L5.writable_sub RSEGS M5 p0 c0 p0 1 WPp); lia). clear WPp.
    pose proof (Z.mod_pos_bound (c0 + 1) 256 ltac:(lia)) as MB0.
    pose proof STK5 as (_ & SLO5 & _).
    (let T := type of (PNSRVXP.vlX0L_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun j => match j with 56%nat => (c0 + 1) mod 256 | 57%nat => p0 | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVXP.vlX0L_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun j => match j with 56%nat => (c0 + 1) mod 256 | 57%nat => p0 | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVXP.aligned; PMK.sc | apply tb0_long; lia])).
    destruct P as (fx6 & R6 & M6 & MG6 & _ & FRZ6 & MS6 & KS6 & Y1 & Y10 & Y11 & Y19 & SZ0 & PB0).
    apply (PNSRVK.brel_piece_tb L HI LY HIok LBX sp fb str _ M5 model5 cr5 s sm ax5 fx5 fx6 R5 R6 _ _ M6
             (fun a => (fb + 40 + 376 <= a < fb + 40 + 376 + 8) \/ (p0 + 0 <= a < p0 + 0 + 1)) (PM.VLong c0 0 p0) K BR5 FOK INCS MS6 MG6
             ltac:(intros a Ha N; apply FRZ6; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X])
             ltac:(intros a; apply PMK.or_dec; apply PMK.rng_dec)); [| | rewrite ETB; reflexivity| rewrite ETB; reflexivity|].
    { intros a Pa. cbn beta in Pa. destruct Pa as [X|X]; [right; left; lia|].
      right. right. rewrite ETB. exists (p0, c0). split; [cbn; auto| cbn [fst snd]; lia]. }
    { unfold PM.vstr_at. split; [apply (L5.defined_grows M5 M6 _ _ MG6 D24)|]. split; [exact I|].
      split; [apply (L5C.u64_at_agree RSEGS M5 M6); [intros i Hi; apply FRZ6; lia|lia|lia| exact U0]|].
      split; [replace (fb + 408 + 8) with (fb + 40 + 376) by lia; exact SZ0|].
      split; [apply (L5C.u64_at_agree RSEGS M5 M6); [intros i Hi; apply FRZ6; lia|lia|lia| replace (fb + 408 + 16) with (fb + 40 + 384) by lia; exact U16]|].
      split; [lia|]. split; [lia|]. split; [exact He0|]. split; [apply (L5.defined_grows M5 M6 _ _ MG6 Dp)| exact I]. }
    intros BR6.
    apply (CLR fx6 R6 M6 (PM.VLong c0 0 p0) BR6); [intros k Hk; apply KS6; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| exact Y1| exact Y10| exact Y11| exact Y19
      | intros a n H1 H2 i Hi; apply FRZ6; lia| apply (PNSRVK.ec_agree M5 M6); [intros i Hi; apply FRZ6; lia|lia|lia| exact EC5]| reflexivity].
Qed.

End WithHeap.
End PNSRVX.
