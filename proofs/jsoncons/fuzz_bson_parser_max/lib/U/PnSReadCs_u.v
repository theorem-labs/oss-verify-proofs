(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith Zwf List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep PmFrame PmParSpecs PmParKit PmCertKitG PgSrc PgV8.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnModelFacts PnStatics PnKeep PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj PnBrKit PnBrKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnBrKitS_u PnSReadCsP_u
     Bs0_code_373c4_373c8_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSCS.
Import PMS.
Abbreviation AN := PnLayoutS_u.NADDR_S.
Abbreviation mem := (word -> option byte).
Abbreviation bparser_at := (PNM.bparser_at RSEGS AD PMSP.T3 PMSP.T4 (pa_vp_parser AD)).
Abbreviation BENT := PNBK.BENT.

Lemma ec_agree (M M' : mem) o v c : L5C.agree_on M M' o 16 -> 0 <= o -> o + 16 <= 2 ^ 64 -> PMSP.ec_at RSEGS M o v c -> PMSP.ec_at RSEGS M' o v c.
Proof.
  intros AG H1 H2 (E0 & E8 & ED). split; [|split].
  - apply (PMF.u32_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact E0].
  - apply (L5C.u64_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact E8].
  - apply (L5C.defined_agree M M' o 16 AG ED).
Qed.

Lemma mod16_sub64 sp : sp mod 16 = 0 -> (sp - 64) mod 16 = 0.
Proof. intros H. replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact H. Qed.

(* [comment removed for export] *)
Definition cs_regs (R R1 : bvmap 5 word) (sp fb w : Z) : Prop :=
  getr R1 (PMK.reg 1) = Z_to_bv 64 0x38448 /\ getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 64)
  /\ getr R1 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) /\ getr R1 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD)
  /\ getr R1 (PMK.reg 8) = Z_to_bv 64 (fb + 40) /\ getr R1 (PMK.reg 9) = Z_to_bv 64 (fb + 16)
  /\ getr R1 (PMK.reg 10) = Z_to_bv 64 (fb + 56) /\ getr R1 (PMK.reg 11) = Z_to_bv 64 (sp - 57) /\ getr R1 (PMK.reg 12) = Z_to_bv 64 1
  /\ getr R1 (PMK.reg 18) = Z_to_bv 64 (fb + 40 + PNR.bcs_off w) /\ getr R1 (PMK.reg 19) = Z_to_bv 64 (fb + 56) /\ getr R1 (PMK.reg 20) = Z_to_bv 64 1
  /\ getr R1 (PMK.reg 21) = Z_to_bv 64 40
  /\ (forall k, In k [22; 23; 24; 25; 26; 27]%nat -> getr R1 (PMK.reg k) = getr R (PMK.reg k)).
Definition cs_saved (R : bvmap 5 word) (M1 : mem) (sp r : Z) : Prop :=
  L5.u64_at RSEGS M1 (sp - 8) r /\ L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))
  /\ L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) /\ L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))
  /\ L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 19))) /\ L5.u64_at RSEGS M1 (sp - 48) (bv_unsigned (getr R (PMK.reg 20)))
  /\ L5.u64_at RSEGS M1 (sp - 56) (bv_unsigned (getr R (PMK.reg 21))).
Definition cs_sz (w : Z) (s : PNM.bpst) (sm : PM.strm) : Z := PM.vs_size (PNR.bcs_str w s) + PM.unread (PNM.b_src s) sm.

Lemma cs_saved_agree R (M1 M2 : mem) sp r :
  (forall a n, sp - 56 <= a -> a + n <= sp -> L5C.agree_on M1 M2 a n) -> 0 <= sp - 64 -> sp <= 2 ^ 64 -> cs_saved R M1 sp r -> cs_saved R M2 sp r.
Proof.
  intros AG H1 H2 (S8 & S16 & S24 & S32 & S40 & S48 & S56). unfold cs_saved.
  repeat lazymatch goal with
  | |- _ /\ _ => split
  | |- L5.u64_at _ M2 ?a ?v => apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG; lia|lia|lia| assumption]
  end.
Qed.

(* [comment removed for export] *)
Definition set_cs (w : Z) (s : PNM.bpst) (x : PM.vstr) (g : Z) : PNM.bpst := if Z.eqb w 0 then PNBO.set_nb s x g else PNBO.set_tb s x g.
Lemma bcs_off_rng w : w = 0 \/ w = 1 -> 344 <= PNR.bcs_off w <= 368.
Proof. intros [->| ->]; unfold PNR.bcs_off, PNM.OFF_NB, PNM.OFF_TB; cbn; lia. Qed.
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
Abbreviation brel := (PNBK.brel RSEGS AD AN L HI 5).
Abbreviation pot := (PNR.pot_bparser L).

Hypothesis SRD : PNRS.src_read_spec L HI.
Hypothesis PB : PNRS.str_push_back_spec L HI.
Hypothesis MKE : PNRS.make_ec_spec L HI.

(* [comment removed for export] *)
Definition cs_kont (w : Z) (K : list event -> Prop) (LBX : list (Z * Z)) (sp r fb cat e : Z) (str : PM.vstr) (R : bvmap 5 word)
           (M : mem) (model : Model) (cr : credit) (s : PNM.bpst) (sm : PM.strm) (ax : PNST.bax) : Prop :=
  forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (s' : PNM.bpst) (sm' : PM.strm) (ax' : PNST.bax) (cr' : credit),
      regs_preserved R R' ->
      PNR.brun_post RSEGS AD AN false (PNR.bprog_cs w) R' M' fb s s' str sm sm' ax ax' cat e ->
      L5C.hpres L LBX sp (PMSP.pm_scr 5) (PNR.W_brun AD AN fb) M M' ->
      PMSP.credit_keep cr cr' (pot s) (pot s') ->
      model_but_vm model model' -> hi_heap HI (PNM.bparser_own s' ++ LBX) cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Definition cs_ctx (w : Z) (K : list event -> Prop) (LBX : list (Z * Z)) (sp r fb : Z) (str : PM.vstr) (R : bvmap 5 word) (cr : credit) (s : PNM.bpst) : Prop :=
  (w = 0 \/ w = 1) /\ K [] /\ PMSP.frame_ok AD L sp fb /\ incl (PM.vs_own str) LBX /\ L5.ra_ok r
  /\ getr R (PMK.reg 2) = Z_to_bv 64 sp /\ getr R (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) /\ getr R (PMK.reg 4) = Z_to_bv 64 (pa_tp AD)
  /\ PMSP.credit_le (pot s) cr.

(* [comment removed for export] *)
Definition cs_linv (w : Z) (LBX : list (Z * Z)) (sp r fb cat e : Z) (str : PM.vstr) (E0 : PNBK.bent) (R R1 : bvmap 5 word)
           (M1 : mem) (model1 : Model) (cr1 : credit) (s1 : PNM.bpst) (sm1 : PM.strm) (ax1 : PNST.bax) : Prop :=
  brel LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) /\ cs_regs R R1 sp fb w /\ cs_saved R M1 sp r
  /\ PNR.binv s1 /\ PMSP.ec_at RSEGS M1 (fb + 16) e cat /\ PNR.btop_pos (PNBK.be_s E0) s1
  /\ cs_sz w s1 sm1 <= cs_sz w (PNBK.be_s E0) (PNBK.be_sm E0) /\ cs_sz w s1 sm1 <= 2 ^ 26 /\ PNM.b_bb s1 = PNM.b_bb (PNBK.be_s E0).

(* [comment removed for export] *)
Lemma cs_fin w K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax
      (fx5 : FPState) R5 (M5 : mem) model5 cr5 s5 sm5 ax5 :
  cs_ctx w K LBX sp r fb str R cr s -> cs_kont w K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M5 model5 cr5 s5 sm5 ax5) ->
  getr R5 (PMK.reg 1) = Z_to_bv 64 r -> getr R5 (PMK.reg 2) = Z_to_bv 64 sp ->
  getr R5 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R5 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R5 (PMK.reg 8) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 8))) -> getr R5 (PMK.reg 9) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 9))) ->
  getr R5 (PMK.reg 18) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 18))) -> getr R5 (PMK.reg 19) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 19))) ->
  getr R5 (PMK.reg 20) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 20))) -> getr R5 (PMK.reg 21) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 21))) ->
  (forall k, In k [22; 23; 24; 25; 26; 27]%nat -> getr R5 (PMK.reg k) = getr R (PMK.reg k)) ->
  (   (PMSP.ec_at RSEGS M5 (fb + 16) 1 (pa_errcat_obj AD) /\ PNM.b_more s5 = 0 /\ PNST.bax_cat ax5 = true /\ (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat /\ PNR.binv s5)
   \/ (PMSP.ec_at RSEGS M5 (fb + 16) e cat /\ PNR.binv s5 /\ PNR.bprog_cs w R5 M5 s s5 sm sm5)) ->
  PNM.b_bb s5 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0x384b4 M5 model5) K.
Proof.
  intros (Hw & K0 & FOK & INCS & (Hr1 & Hr2) & Rsp & Rgp & Rtp & CRED) KONT BR Y1 Y2 Y3 Y4 Y8 Y9 Y18 Y19 Y20 Y21 YK POST BB.
  pose proof BR as (RP & STEP & AXL & HP & CK & MB & HH & STK & MOK). cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax] in *.
  pose proof MOK as (Mh & Ml & Mm).
  eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
  { apply (PMK.ret_to RSEGS fx5 R5 M5 0x384b4 W_37468 r F_37468 eq_refl D_37468); [exact Y1| lia| exact Hr2]. }
  apply (KONT fx5 R5 M5 model5 s5 sm5 ax5 cr5).
  - apply PMK.preserved_by_index. intros k Hk. cbn in Hk.
    destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
      first [ rewrite Y2, Rsp; reflexivity | rewrite Y3, Rgp; reflexivity | rewrite Y4, Rtp; reflexivity
            | rewrite Y8; apply Z_to_bv_bv_unsigned | rewrite Y9; apply Z_to_bv_bv_unsigned | rewrite Y18; apply Z_to_bv_bv_unsigned
            | rewrite Y19; apply Z_to_bv_bv_unsigned | rewrite Y20; apply Z_to_bv_bv_unsigned | rewrite Y21; apply Z_to_bv_bv_unsigned | apply YK; cbn; tauto ].
  - unfold PNR.brun_post. split; [exact RP|]. split; [exact STEP|]. split; [exact AXL|].
    unfold PNR.o_ec, PMSP.o_ec. cbn [pa_off_ec AD PnLayoutS_u.ADDR_S].
    split; [| exact BB].
    destruct POST as [(E1 & MO & CAT & LEN & INV')|(E0 & INV & PROG)].
    + left. exists 1. split; [lia|]. split; [exact E1|]. split; [exact MO|]. split; [exact CAT|]. split; [exact LEN| exact INV'].
    + right. split; [exact E0|]. split; [exact INV| exact PROG].
  - exact HP.
  - exact CK.
  - exact MB.
  - exact HH.
Qed.

(* [comment removed for export] *)
Lemma cs_top LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 :
  brel LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) -> PNR.binv s1 ->
  exists l c, PNM.b_stk s1 = l ++ [c] /\ PNM.bstate_ok c
    /\ L5.u64_at RSEGS M1 (fb + 40 + 400) (PNM.b_sb s1 + 40 * Z.of_nat (length l) + 40)
    /\ L5.u64_at RSEGS M1 (PNM.b_sb s1 + 40 * Z.of_nat (length l) + 16) (PNM.bs_pos c)
    /\ L5.writable RSEGS M1 (PNM.b_sb s1 + 40 * Z.of_nat (length l) + 16) 8
    /\ 4096 <= PNM.b_sb s1 + 40 * Z.of_nat (length l) /\ PNM.b_sb s1 + 40 * Z.of_nat (length l) + 40 <= sp - 22528
    /\ (PNM.b_sb s1 + 40 * Z.of_nat (length l) + 40) mod 8 = 0.
Proof.
  intros BR INV.
  destruct (PNBK2.brel_blocks RSEGS AD AN L HI KH 5 LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR) as (BRG & OWNB & APQ).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 5 LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR) as (PA1 & IA1 & GR1 & UN1 & STK & MOK).
  change (PMSP.pm_scr 5) with 22528 in STK. pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof INV as (_ & (L1 & _ & _ & _ & OKs)).
  destruct (exists_last (l := PNM.b_stk s1) ltac:(intros X; rewrite X in L1; cbn in L1; lia)) as (l & c & ES).
  exists l, c. split; [exact ES|].
  pose proof (OKs (length l) ltac:(rewrite ES, length_app; cbn; lia)) as OKc. rewrite ES, nth_middle in OKc. split; [exact OKc|].
  pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SV1 & _). unfold PNM.OFF_STK in SV1.
  pose proof SV1 as (V0 & V8 & _ & Hk & Hlen & Hal & DB & _ & _ & EL). unfold PNM.BSZ in *.
  rewrite ES, length_app in Hlen, EL, V8. cbn [length] in Hlen, EL, V8.
  set (b := PNM.b_sb s1) in *. set (k := PNM.b_sk s1) in *. set (n := Z.of_nat (length l)) in *.
  assert (Hn : 0 <= n /\ n + 1 <= 2 ^ k) by (unfold n; lia).
  assert (TOPIN : b + 40 * n + 40 <= b + 40 * 2 ^ k) by nia.
  assert (Bs : In (b, 40 * 2 ^ k) (PNM.bparser_own s1)).
  { unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own, b, k. apply in_or_app. right. cbn. auto. }
  destruct (OWNB _ _ Bs) as (S0 & S4). unfold hl_ceil in S4.
  split; [replace (b + 40 * n + 40) with (b + 40 * (Z.of_nat (length l + 1))) by (unfold n; lia); replace (fb + 40 + 400) with (fb + 40 + 392 + 8) by lia; exact V8|].
  pose proof (EL (length l) ltac:(lia)) as ET. rewrite nth_middle in ET. fold n in ET. destruct ET as (_ & _ & Tp & _ & _).
  split; [exact Tp|].
  split; [apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M1 b (40 * 2 ^ k)); [exact DB|lia|lia]|lia|lia]|].
  split; [lia|]. split; [lia|].
  replace (b + 40 * n + 40) with (b + 8 * (5 * n + 5)) by lia. apply PMPK.m8_add. apply PMPK.m16_8. exact Hal.
Qed.

Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac fd P := PMK.feed P ltac:(first [PMK.sc | unfold PNSCSP.aligned; PMK.sc]).

(* [comment removed for export] *)
Lemma brel_push_back_cs w LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 (fx1 : FPState) R1 (r' c : Z) K :
  (w = 0 \/ w = 1) -> K [] ->
  brel LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) ->
  PMSP.frame_ok AD L sp fb -> incl (PM.vs_own str) LBX -> PMSP.credit_le (pot (PNBK.be_s E0)) (PNBK.be_cr E0) ->
  getr R1 (PMK.reg 1) = Z_to_bv 64 r' -> L5.ra_ok r' -> getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 64) ->
  getr R1 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R1 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R1 (PMK.reg 10) = Z_to_bv 64 (fb + 40 + PNR.bcs_off w) -> getr R1 (PMK.reg 11) = Z_to_bv 64 c -> 0 <= c < 256 ->
  sp mod 16 = 0 -> PM.vs_size (PNR.bcs_str w s1) < 2 ^ 26 ->
  (forall (fx2 : FPState) R2 (M2 : mem) model2 x' g' cr2,
      regs_preserved R1 R2 -> PM.vs_size x' = PM.vs_size (PNR.bcs_str w s1) + 1 ->
      brel LBX sp fb str E0 (BENT M2 model2 cr2 (set_cs w s1 x' g') sm1 ax1) ->
      (forall a n, sp - 64 <= a -> a + n <= fb + 40 -> L5C.agree_on M1 M2 a n) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 r' M2 model2) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x58938 M1 model1) K.
Proof.
  intros Hw K0 BR FOK INCS CRED X1 RA X2 X3 X4 X10 X11 Hc A16 SZ KONT.
  unfold PNRS.str_push_back_spec in PB. change 0x58938 with (PNL.pn_str_push_back AN).
  destruct Hw as [->| ->]; unfold PNR.bcs_off, PNR.bcs_str, set_cs, PNM.OFF_NB, PNM.OFF_TB in *; cbn [Z.eqb] in *.
  - apply (PNBK.brel_push_back_nb RSEGS AD AN L HI KH 5 LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 fx1 R1 (sp - 64) r' c K PB ltac:(lia) K0 BR FOK INCS CRED
             X1 RA X2 X3 X4 X10 X11 Hc ltac:(lia) ltac:(unfold PMSP.pm_scr; lia) (mod16_sub64 sp A16) SZ KONT).
  - apply (PNBK.brel_push_back_tb RSEGS AD AN L HI KH 5 LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 fx1 R1 (sp - 64) r' c K PB ltac:(lia) K0 BR FOK INCS CRED
             X1 RA X2 X3 X4 X10 X11 Hc ltac:(lia) ltac:(unfold PMSP.pm_scr; lia) (mod16_sub64 sp A16) SZ KONT).
Qed.

(* [comment removed for export] *)
Lemma cs_tail w K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax
      (n : Z) (fx3 : FPState) R3 (M3 : mem) model3 cr3 s3 sm3 ax3 (cb : Z) :
  cs_ctx w K LBX sp r fb str R cr s -> cs_kont w K LBX sp r fb cat e str R M model cr s sm ax ->
  (forall (fx2 : FPState) R2 (M2 : mem) model2 cr2 s2 sm2 ax2,
      cs_linv w LBX sp r fb cat e str (BENT M model cr s sm ax) R R2 M2 model2 cr2 s2 sm2 ax2 -> 0 <= PM.unread (PNM.b_src s2) sm2 < n ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0x370d0 M2 model2) K) ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M3 model3 cr3 s3 sm3 ax3) ->
  getr R3 (PMK.reg 2) = Z_to_bv 64 (sp - 64) -> getr R3 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R3 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R3 (PMK.reg 8) = Z_to_bv 64 (fb + 40) -> getr R3 (PMK.reg 9) = Z_to_bv 64 (fb + 16) ->
  getr R3 (PMK.reg 18) = Z_to_bv 64 (fb + 40 + PNR.bcs_off w) -> getr R3 (PMK.reg 19) = Z_to_bv 64 (fb + 56) -> getr R3 (PMK.reg 20) = Z_to_bv 64 1 ->
  getr R3 (PMK.reg 21) = Z_to_bv 64 40 ->
  (forall k, In k [22; 23; 24; 25; 26; 27]%nat -> getr R3 (PMK.reg k) = getr R (PMK.reg k)) ->
  cs_saved R M3 sp r -> L5.u8_at RSEGS M3 (sp - 57) cb -> 0 <= cb < 256 ->
  PNR.binv s3 -> PMSP.ec_at RSEGS M3 (fb + 16) e cat -> PNR.btop_pos s s3 ->
  cs_sz w s3 sm3 + 1 <= cs_sz w s sm -> cs_sz w s3 sm3 + 1 <= 2 ^ 26 -> PNM.b_bb s3 = PNM.b_bb s ->
  0 <= PM.unread (PNM.b_src s3) sm3 < n -> PM.unread (PNM.b_src s3) sm3 < PM.unread (PNM.b_src s) sm ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0x38470 M3 model3) K.
Proof.
  intros CTX KONT IH BR3 X2 X3 X4 X8 X9 X18 X19 X20 X21 XK SV3 CB Hcb INV3 EC3 TP3 SZ1 SZ2 EBB3 UN3 LT3.
  pose proof CTX as (Hw & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof (bcs_off_rng w Hw) as HOFF.
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 5 LBX sp fb str _ M3 model3 cr3 s3 sm3 ax3 BR3) as (PA3 & IA3 & GR3 & _ & STK3 & MOK3).
  change (PMSP.pm_scr 5) with 22528 in STK3. pose proof STK3 as (A16 & SLO & SHI & STOP & SDEF3). pose proof MOK3 as (Mh3 & Ml3 & Mm3).
  pose proof (L5C.stk_floor _ M3 sp 22528 STK3) as SFL. pose proof (L5C.stk_writable RSEGS _ M3 sp 22528 STK3) as WR3.
  pose proof SV3 as (S8 & S16 & S24 & S32 & S40 & S48 & S56).
  destruct (Z.eq_dec cb 0) as [->|NZ].
  - (* [comment removed for export] *)
    idtac.
    pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 8))). pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 9))).
    pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 18))). pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 19))).
    pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 20))). pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 21))). pose proof RAok as (Hr1 & Hr2).
    LeanFeed.pfeed P (PNSCSP.bcsC0_conc fx3 R3 M3 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 16 | 35%nat => fb + 40 + PNR.bcs_off w
                 | 36%nat => r | 37%nat => bv_unsigned (getr R (PMK.reg 8)) | 38%nat => bv_unsigned (getr R (PMK.reg 9)) | 39%nat => bv_unsigned (getr R (PMK.reg 18))
                 | 40%nat => bv_unsigned (getr R (PMK.reg 19)) | 41%nat => bv_unsigned (getr R (PMK.reg 20)) | 44%nat => bv_unsigned (getr R (PMK.reg 21)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSCSP.aligned; PMK.sc]).
    pvz_hg ltac:(idtac; destruct P as (fx5 & R5 & M5 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG5 & _ & FRZ5 & MS5 & KS5 & Y1 & Y2 & Y8 & Y9 & Y11 & Y18 & Y19 & Y20 & Y21)); PMK.pvz_clrT.
    apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 5 LBX sp fb str _ M3 model3 cr3 s3 sm3 ax3 fx3 fx5 R3 R5 0x38470 0x384b4 M5 (fun _ => False) K
             ltac:(lia) BR3 FOK INCS MS5 MG5 ltac:(intros a Ha _; apply FRZ5; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
    intros BR5.
    apply (cs_fin w K LBX sp r fb cat e str R M model cr s sm ax fx5 R5 M5 model3 cr3 s3 sm3 ax3 CTX KONT BR5 Y1 Y2);
      [PMK.rk| PMK.rk| exact Y8| exact Y9| exact Y18| exact Y19| exact Y20| exact Y21| intros k Hk; rewrite (KS5 k) by (cbn in Hk; cbn; tauto); apply XK; exact Hk| | exact EBB3].
    right. split; [apply (ec_agree M3 M5); [intros i Hi; apply FRZ5; lia|lia|lia| exact EC3]|]. split; [exact INV3|].
    unfold PNR.bprog_cs. split; [exact TP3|]. unfold cs_sz in SZ1. split; [exact LT3| exact SZ1].
  - (* [comment removed for export] *)
    LeanFeed.pfeed P (PNSCSP.bcsC1_conc fx3 R3 M3 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 16 | 35%nat => fb + 40 + PNR.bcs_off w
                 | 45%nat => cb | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSCSP.aligned; PMK.sc]).
    pvz_hg ltac:(idtac; destruct P as (fx4 & R4 & M4 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG4 & _ & FRZ4 & MS4 & KS4 & Y1 & Y10 & Y11)); PMK.pvz_clrT.
    apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 5 LBX sp fb str _ M3 model3 cr3 s3 sm3 ax3 fx3 fx4 R3 R4 0x38470 0x58938 M4 (fun _ => False) K
             ltac:(lia) BR3 FOK INCS MS4 MG4 ltac:(intros a Ha _; apply FRZ4; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
    intros BR4.
    assert (EQ4 : forall i, 0 <= i < 2 ^ 64 -> M4 (Z_to_bv 64 i) = M3 (Z_to_bv 64 i)) by (intros i Hi; apply FRZ4; exact Hi).
    apply (brel_push_back_cs w LBX sp fb str _ M4 model3 cr3 s3 sm3 ax3 fx4 R4 0x38480 cb K Hw K0 BR4 FOK INCS CRED Y1 ltac:(split; [lia| reflexivity])
             ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) Y10 Y11 Hcb A16 ltac:(unfold cs_sz in SZ2; lia)).
    intros fx6 R6 M6 model6 x' g' cr6 RP46 SZ6 BR6 AG46.
    destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 5 LBX sp fb str _ M6 model6 cr6 _ sm3 ax3 BR6) as (PA6 & _ & _ & _ & STK6 & MOK6).
    change (PMSP.pm_scr 5) with 22528 in STK6. pose proof (L5C.stk_writable RSEGS _ M6 sp 22528 STK6) as WR6.
    LeanFeed.pfeed P (PNSCSP.bcsP_conc fx6 R6 M6 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 16 | 35%nat => fb + 40 + PNR.bcs_off w | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSCSP.aligned; PMK.sc]).
    pvz_hg ltac:(idtac; destruct P as (fx7 & R7 & M7 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG7 & _ & FRZ7 & MS7 & KS7 & Z1 & Z10 & Z11 & Z12)); PMK.pvz_clrT.
    apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 5 LBX sp fb str _ M6 model6 cr6 _ sm3 ax3 fx6 fx7 R6 R7 0x38480 0x370d0 M7 (fun _ => False) K
             ltac:(lia) BR6 FOK INCS MS7 MG7 ltac:(intros a Ha _; apply FRZ7; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
    intros BR7.
    assert (EQ7 : forall i, 0 <= i < 2 ^ 64 -> M7 (Z_to_bv 64 i) = M6 (Z_to_bv 64 i)) by (intros i Hi; apply FRZ7; exact Hi).
    assert (AG37 : forall a m, sp - 64 <= a -> a + m <= fb + 40 -> L5C.agree_on M3 M7 a m).
    { intros a m H1 H2 i Hi. rewrite EQ7 by lia. rewrite (AG46 a m H1 H2 i Hi). apply EQ4. lia. }
    apply (IH fx7 R7 M7 model6 cr6 (set_cs w s3 x' g') sm3 ax3); [| destruct Hw as [->| ->]; cbn; exact UN3].
    unfold cs_linv. cbn [PNBK.be_s PNBK.be_sm].
    split; [exact BR7|].
    split.
    { unfold cs_regs. split; [exact Z1|]. split; [PMK.rk|]. split; [PMK.rk|]. split; [PMK.rk|]. split; [PMK.rk|]. split; [PMK.rk|].
      split; [PMK.rk|]. split; [exact Z11|]. split; [exact Z12|]. split; [PMK.rk|]. split; [PMK.rk|]. split; [PMK.rk|]. split; [PMK.rk|].
      intros k Hk. rewrite (KS7 k) by (cbn in Hk; cbn; tauto). rewrite (PMK.cs_of_preserved R4 R6 k RP46) by (cbn in Hk; cbn; tauto).
      rewrite (KS4 k) by (cbn in Hk; cbn; tauto). apply XK. exact Hk. }
    split; [apply (cs_saved_agree R M3 M7 sp r); [intros a m H1 H2; apply AG37; lia|lia|lia| exact SV3]|].
    split; [destruct Hw as [->| ->]; exact INV3|].
    split; [apply (ec_agree M3 M7); [apply AG37; lia|lia|lia| exact EC3]|].
    split; [destruct Hw as [->| ->]; exact TP3|].
    refine (conj _ (conj _ _)); [| | destruct Hw as [->| ->]; exact EBB3];
    (clear - SZ1 SZ2 SZ6 UN3 Hw; unfold cs_sz in *; destruct Hw as [->| ->]; unfold set_cs, PNR.bcs_str in *; cbn [Z.eqb PNBO.set_nb PNBO.set_tb PNM.b_nb PNM.b_tb PNM.b_src] in *; lia).
Qed.

(* [comment removed for export] *)
Lemma cs_loop w K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax :
  cs_ctx w K LBX sp r fb str R cr s -> cs_kont w K LBX sp r fb cat e str R M model cr s sm ax ->
  forall n, 0 <= n -> forall (fx1 : FPState) R1 (M1 : mem) model1 cr1 s1 sm1 ax1,
    cs_linv w LBX sp r fb cat e str (BENT M model cr s sm ax) R R1 M1 model1 cr1 s1 sm1 ax1 -> PM.unread (PNM.b_src s1) sm1 = n ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x370d0 M1 model1) K.
Proof.
  intros CTX KONT. pose proof CTX as (Hw & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2). pose proof (bcs_off_rng w Hw) as HOFF.
  assert (AL40 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
  unfold PNRS.src_read_spec, PNR.src_read_spec in SRD. unfold PNRS.make_ec_spec in MKE.
  intros n. pattern n. apply (well_founded_ind (Zwf_well_founded 0)). clear n.
  intros n IHn Hn fx1 R1 M1 model1 cr1 s1 sm1 ax1 LI EN.
  assert (IH : forall (fx2 : FPState) R2 (M2 : mem) model2 cr2 s2 sm2 ax2,
             cs_linv w LBX sp r fb cat e str (BENT M model cr s sm ax) R R2 M2 model2 cr2 s2 sm2 ax2 -> 0 <= PM.unread (PNM.b_src s2) sm2 < n ->
             srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0x370d0 M2 model2) K).
  { intros fx2 R2 M2 model2 cr2 s2 sm2 ax2 LI2 LT2. exact (IHn (PM.unread (PNM.b_src s2) sm2) ltac:(unfold Zwf; lia) ltac:(lia) fx2 R2 M2 model2 cr2 s2 sm2 ax2 LI2 eq_refl). }
  clear IHn.
  destruct LI as (BR1 & RG1 & SV1 & INV1 & EC1 & TP1 & SZ1 & SZ2 & EBB1). cbn [PNBK.be_s PNBK.be_sm] in TP1, SZ1, EBB1.
  destruct RG1 as (X1 & X2 & X3 & X4 & X8 & X9 & X10 & X11 & X12 & X18 & X19 & X20 & X21 & XK).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 5 LBX sp fb str _ M1 model1 cr1 s1 sm1 ax1 BR1) as (PA1 & IA1 & GR1 & UN1 & STK1 & MOK1).
  change (PMSP.pm_scr 5) with 22528 in STK1. pose proof STK1 as (A16 & SLO & SHI & STOP & SDEF1).
  pose proof (L5C.stk_floor _ M1 sp 22528 STK1) as SFL.
  assert (LE1 : PM.unread (PNM.b_src s1) sm1 <= PM.unread (PNM.b_src s) sm) by (destruct BR1 as (_ & (_ & _ & _ & _ & X) & _); exact X).
  (* [comment removed for export] *)
  apply (PNBK.brel_src_read RSEGS AD AN L HI KH 5 LBX sp fb str _ M1 model1 cr1 s1 sm1 ax1 fx1 R1 (sp - 64) 0x38448 (sp - 57) 1 K SRD
           ltac:(lia) K0 BR1 FOK INCS X1 ltac:(split; [lia| reflexivity]) X2 X3 X4 X10 X11 X12
           ltac:(lia) ltac:(unfold PMSP.pm_scr; lia) (mod16_sub64 sp A16) ltac:(lia) ltac:(lia) ltac:(lia)).
  intros fx2 R2 M2 src2 sm2 d RP12 Y10 Hd UNR2 DEFc BR2 AG12.
  assert (SV2 : cs_saved R M2 sp r) by (apply (cs_saved_agree R M1 M2 sp r); [intros a m H1 H2; apply AG12; lia| lia| lia| exact SV1]).
  assert (EC2 : PMSP.ec_at RSEGS M2 (fb + 16) e cat) by (apply (ec_agree M1 M2); [apply AG12; lia|lia|lia| exact EC1]).
  assert (INV2 : PNR.binv (PNM.with_srcB s1 src2)) by exact INV1.
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 5 LBX sp fb str _ M2 model1 cr1 _ sm2 ax1 BR2) as (PA2 & IA2 & GR2 & UN2 & STK2 & MOK2).
  change (PMSP.pm_scr 5) with 22528 in STK2. pose proof (L5C.stk_writable RSEGS _ M2 sp 22528 STK2) as WR2. pose proof MOK2 as (Mh2 & Ml2 & Mm2).
  destruct (cs_top LBX sp fb str _ M2 model1 cr1 _ sm2 ax1 BR2 INV2) as (l & c & ES & OKc & VE & VP & WP & E0 & E1 & EAL).
  cbn [PNM.with_srcB PNM.b_sb PNM.b_stk PNM.b_src] in ES, VE, VP, WP, E0, E1, EAL, UNR2, UN2.
  set (et := PNM.b_sb s1 + 40 * Z.of_nat (length l)) in *.
  pose proof OKc as (OKm & OKl & POS & OKt & OKi).
  assert (Hd01 : d = 0 \/ d = 1) by lia. destruct Hd01 as [->| ->].
  - (* [comment removed for export] *)
    LeanFeed.pfeed P (PNSCSP.bcsR0_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 16 | 35%nat => fb + 40 + PNR.bcs_off w
                 | 42%nat => et + 40 | 43%nat => PNM.bs_pos c | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSCSP.aligned; PMK.sc]).
    pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Z10 & Y11 & Y12 & CP3)); PMK.pvz_clrT.
    apply (PNBK2.brel_piece_pos RSEGS AD AN L HI KH 5 LBX sp fb str _ M2 model1 cr1 _ sm2 ax1 fx2 fx3 R2 R3 0x38448 0x36ee4 M3
             (fun a => et + 40 - 24 <= a < et + 40 - 24 + 8) l c (PNM.bs_pos c) K ltac:(lia) BR2 FOK INCS MS3 MG3 FRZ3 ltac:(intros a; apply PMK.rng_dec) ES);
      [cbn [PNM.with_srcB PNM.b_sb]; intros a Pa; right; lia| cbn [PNM.with_srcB PNM.b_sb]; replace (PNM.b_sb s1 + 40 * Z.of_nat (length l) + 16) with (et + 40 - 24) by lia; exact CP3| lia|].
    intros BR3.
    assert (AG23 : forall a m, sp - 64 <= a -> a + m <= fb + 48 -> L5C.agree_on M2 M3 a m) by (intros a m H1 H2 i Hi; apply FRZ3; lia).
    assert (ED3 : L5.defined M3 (fb + 16) 16) by (destruct EC2 as (_ & _ & ED); apply (L5.defined_grows M2 M3 _ _ MG3 ED)).
    apply (PNBK.brel_make_ec RSEGS AD AN L HI KH 5 LBX sp fb str _ M3 model1 cr1 _ sm2 ax1 fx3 R3 (sp - 64) 0x38490 1 K MKE ltac:(lia) K0 BR3 FOK INCS
             Y1 ltac:(split; [lia| reflexivity]) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) Z10 Y11 ltac:(lia) ltac:(lia) ltac:(unfold PMSP.pm_scr; lia) (mod16_sub64 sp A16) ED3).
    intros fx4 R4 M4 RP34 EC4 BR4 AG34.
    destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 5 LBX sp fb str _ M4 model1 cr1 _ sm2 _ BR4) as (PA4 & _ & _ & _ & STK4 & MOK4).
    change (PMSP.pm_scr 5) with 22528 in STK4. pose proof (L5C.stk_writable RSEGS _ M4 sp 22528 STK4) as WR4.
    assert (WP4 : L5.writable RSEGS M4 (fb + 40) 416) by (destruct PA4 as (_ & D & _); apply (L5C.writable_of_defined RSEGS); [exact D|lia|lia]).
    assert (SV4 : cs_saved R M4 sp r).
    { apply (cs_saved_agree R M3 M4 sp r); [intros a m H1 H2; apply AG34; lia|lia|lia|].
      apply (cs_saved_agree R M2 M3 sp r); [intros a m H1 H2; apply AG23; lia|lia|lia| exact SV2]. }
    pose proof SV4 as (S8 & S16 & S24 & S32 & S40 & S48 & S56).
    pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 8))). pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 9))).
    pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 18))). pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 19))).
    pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 20))). pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 21))).
    LeanFeed.pfeed P (PNSCSP.bcsE_conc fx4 R4 M4 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 16 | 35%nat => fb + 40 + PNR.bcs_off w
                 | 36%nat => r | 37%nat => bv_unsigned (getr R (PMK.reg 8)) | 38%nat => bv_unsigned (getr R (PMK.reg 9)) | 39%nat => bv_unsigned (getr R (PMK.reg 18))
                 | 40%nat => bv_unsigned (getr R (PMK.reg 19)) | 41%nat => bv_unsigned (getr R (PMK.reg 20)) | 44%nat => bv_unsigned (getr R (PMK.reg 21)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSCSP.aligned; PMK.sc]).
    pvz_hg ltac:(idtac; destruct P as (fx5 & R5 & M5 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG5 & _ & FRZ5 & MS5 & KS5 & Y1' & Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & MO5)); PMK.pvz_clrT.
    apply (PNBK2.brel_piece_more RSEGS AD AN L HI KH 5 LBX sp fb str _ M4 model1 cr1 _ sm2 _ fx4 fx5 R4 R5 0x38490 0x384b4 M5
             (fun a => fb + 40 + 8 <= a < fb + 40 + 8 + 1) 0 K ltac:(lia) BR4 FOK INCS MS5 MG5 FRZ5 ltac:(intros a; apply PMK.rng_dec)
             ltac:(intros a Pa; cbn beta in Pa; right; clear -Pa; lia) ltac:(replace (fb + 48) with (fb + 40 + 8) by lia; exact MO5) ltac:(left; reflexivity)).
    intros BR5.
    apply (cs_fin w K LBX sp r fb cat e str R M model cr s sm ax fx5 R5 M5 model1 cr1 _ sm2 _ CTX KONT BR5 Y1' Y2);
      [PMK.rk| PMK.rk| exact Y8| exact Y9| exact Y18| exact Y19| exact Y20| exact Y21| intros k Hk; rewrite (KS5 k) by (cbn in Hk; cbn; tauto)|
      | cbn [PNBO.set_more PNBO.set_stk PNM.with_srcB PNM.b_bb]; exact EBB1].
    { rewrite (PMK.cs_of_preserved R3 R4 k RP34) by (cbn in Hk; cbn; tauto). rewrite (KS3 k) by (cbn in Hk; cbn; tauto).
      rewrite (PMK.cs_of_preserved R1 R2 k RP12) by (cbn in Hk; cbn; tauto). apply XK. exact Hk. }
    left. split; [| split; [reflexivity|]; split; [apply bax_cat_add|]].
    { unfold PNR.o_ec, PMSP.o_ec in EC4. cbn [pa_off_ec AD PnLayoutS_u.ADDR_S] in EC4.
      apply (ec_agree M4 M5); [intros i Hi; apply FRZ5; lia|lia|lia| exact EC4]. }
    split.
    { destruct TP1 as (l1 & c1 & c1' & TE1 & TE2 & _). cbn [PNBO.set_more PNBO.set_stk PNM.with_srcB PNM.b_stk]. rewrite TE1.
      assert (EL12 : length (l1 ++ [c1']) = length (l ++ [c])) by (rewrite <- TE2, ES; reflexivity). revert EL12. clear. intros EL12. rewrite !length_app in *. cbn [length] in *. lia. }
    pose proof (PNBK2.binv_set_stk_top (PNM.with_srcB s1 src2) l c (PNM.BS (PNM.bs_mode c) (PNM.bs_len c) (PNM.bs_pos c) (PNM.bs_type c) (PNM.bs_idx c)) INV2 ES ltac:(unfold PNM.bstate_ok; cbn; lia) eq_refl) as INV3.
    exact INV3.
  - (* [comment removed for export] *)
    destruct (PMCG.u8_of_defined RSEGS M2 (sp - 57) ltac:(lia) ltac:(lia) DEFc) as (cb & Hcb & CB).
    assert (TAIL : forall (fx3 : FPState) R3 (M3 : mem) pos',
               msteps RSEGS (@mkst fx2 R2 (Z_to_bv 64 0x38448) M2 (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 0x38470) M3 (seg_rom RSEGS)) ->
               mem_grows M2 M3 -> (forall i, 0 <= i < 2 ^ 64 -> ~ (et + 40 - 24 <= i < et + 40 - 24 + 8) -> M3 (Z_to_bv 64 i) = M2 (Z_to_bv 64 i)) ->
               (forall x, In x PNSCSP.KS_bcsR1 -> getr R3 (PMK.reg x) = getr R2 (PMK.reg x)) ->
               L5.u64_at RSEGS M3 (et + 40 - 24) pos' -> 0 <= pos' < 2 ^ 64 ->
               srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0x38448 M2 model1) K).
    { intros fx3 R3 M3 pos' MS3 MG3 FRZ3 KS3 CP3 Hp.
      apply (PNBK2.brel_piece_pos RSEGS AD AN L HI KH 5 LBX sp fb str _ M2 model1 cr1 _ sm2 ax1 fx2 fx3 R2 R3 0x38448 0x38470 M3
               (fun a => et + 40 - 24 <= a < et + 40 - 24 + 8) l c pos' K ltac:(lia) BR2 FOK INCS MS3 MG3 FRZ3 ltac:(intros a; apply PMK.rng_dec) ES);
        [cbn [PNM.with_srcB PNM.b_sb]; intros a Pa; right; lia| cbn [PNM.with_srcB PNM.b_sb]; replace (PNM.b_sb s1 + 40 * Z.of_nat (length l) + 16) with (et + 40 - 24) by lia; exact CP3| exact Hp|].
      intros BR3.
      assert (AG23 : forall a m, sp - 64 <= a -> a + m <= fb + 48 -> L5C.agree_on M2 M3 a m) by (intros a m H1 H2 i Hi; apply FRZ3; lia).
      apply (cs_tail w K LBX sp r fb cat e str R M model cr s sm ax n fx3 R3 M3 model1 cr1 _ sm2 ax1 cb CTX KONT IH BR3);
        [PMK.rk| PMK.rk| PMK.rk| PMK.rk| PMK.rk| PMK.rk| PMK.rk| PMK.rk| PMK.rk
        | intros k Hk; rewrite (KS3 k) by (cbn in Hk; cbn; tauto); rewrite (PMK.cs_of_preserved R1 R2 k RP12) by (cbn in Hk; cbn; tauto); apply XK; exact Hk
        | apply (cs_saved_agree R M2 M3 sp r); [intros a m H1 H2; apply AG23; lia|lia|lia| exact SV2]
        | apply (L5C.u8_at_agree RSEGS M2 M3); [apply AG23; lia|lia|lia| exact CB]
        | exact Hcb
        | apply (PNBK2.binv_set_stk_top _ l c); [exact INV2| exact ES| unfold PNM.bstate_ok; cbn; lia| reflexivity]
        | apply (ec_agree M2 M3); [apply AG23; lia|lia|lia| exact EC2]
        | apply (PNBK2.btop_pos_trans s (PNM.with_srcB s1 src2)); [exact TP1| apply (PNBK2.btop_pos_set_stk _ l c); [exact ES| unfold PNM.bstate_ok; cbn; lia| reflexivity| reflexivity| reflexivity| reflexivity]]
        | | | cbn [PNBO.set_stk PNM.with_srcB PNM.b_bb]; exact EBB1 | | ]; clear - SZ1 SZ2 UNR2 UN2 EN LE1 Hw; unfold cs_sz in *;
        destruct Hw as [->| ->]; unfold PNR.bcs_str in *; cbn [Z.eqb PNBO.set_stk PNM.with_srcB PNM.b_src PNM.b_nb PNM.b_tb] in *; lia. }
    destruct (Z.eq_dec (PNM.bs_pos c) (2 ^ 64 - 1)) as [PW|PNW].
    + idtac.
      rewrite PW in VP.
      LeanFeed.pfeed P (PNSCSP.bcsR1w_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 16 | 35%nat => fb + 40 + PNR.bcs_off w
                   | 42%nat => et + 40 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSCSP.aligned; PMK.sc]).
      pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & _ & FRZ3 & MS3 & KS3 & Y11 & Y12 & CP3)); PMK.pvz_clrT.
      apply (TAIL fx3 R3 M3 0 MS3 MG3 FRZ3); [| exact CP3| lia].
      intros x Hx. apply KS3. revert Hx. clear. intros Hx. cbn in Hx |- *. tauto.
    + LeanFeed.pfeed P (PNSCSP.bcsR1_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 16 | 35%nat => fb + 40 + PNR.bcs_off w
                   | 42%nat => et + 40 | 43%nat => PNM.bs_pos c | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSCSP.aligned; PMK.sc]).
      pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & _ & FRZ3 & MS3 & KS3 & Y11 & Y12 & CP3)); PMK.pvz_clrT.
      apply (TAIL fx3 R3 M3 (PNM.bs_pos c + 1) MS3 MG3 FRZ3 KS3 CP3 ltac:(lia)).
Qed.

(* [comment removed for export] *)
Theorem read_cstring_ok : PNRS.read_cstring_spec L HI.
Proof.
  unfold PNRS.read_cstring_spec, PNR.read_cstring_spec. intros w Hw. unfold PNR.brun_spec.
  intros fx R M model K LBX cr sp r fb cat e s str sm ax HH MOK K0 ENT FOK ARGS RPRE INCS INV EC0 He UNR CRED KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2.
  pose proof MOK as (Mh & Ml & Mm). change (PMSP.pm_scr 5) with 22528 in STK. pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  destruct ARGS as (A10 & A11 & A12 & SZB). rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
  unfold PNR.o_p, PNR.o_ec, PMSP.o_p, PMSP.o_ec in A10, A11, A12, EC0. cbn [pa_off_p pa_off_ec AD PnLayoutS_u.ADDR_S] in A10, A11, A12, EC0.
  pose proof (bcs_off_rng w Hw) as HOFF. pose proof (L5C.stk_floor _ M sp 22528 STK) as SFL. pose proof (L5C.stk_writable RSEGS _ M sp 22528 STK) as WR.
  pose proof (PNBK.brel_init RSEGS AD AN L HI 5 LBX sp fb str M model cr s sm ax ltac:(lia) RPRE HH STK MOK) as BR0.
  assert (CTX : cs_ctx w K LBX sp r fb str R cr s).
  { split; [exact Hw|]. split; [exact K0|]. split; [exact FOK|]. split; [exact INCS|]. split; [exact RAok|].
    split; [exact Rsp|]. split; [exact Rgp|]. split; [exact Rtp| exact CRED]. }
  assert (KONT' : cs_kont w K LBX sp r fb cat e str R M model cr s sm ax) by exact KONT.
  unfold PMSP.cfg. cbn [PNL.pn_read_cstring AN PnLayoutS_u.NADDR_S].
  LeanFeed.pfeed P (PNSCSP.bcsA_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 16 | 35%nat => fb + 40 + PNR.bcs_off w | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSCSP.aligned; PMK.sc]).
  pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
                destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & X1 & X2 & X8 & X9 & X10 & X11 & X12 & X18 & X19 & X20 & X21 & CFF & C56 & C48 & C40 & C32 & C24 & C16 & C8)); PMK.pvz_clrT.
  change (mkCfg (@mkst fx R (Z_to_bv 64 0x383f8) M (seg_rom RSEGS)) model) with (@PMSP.cfg RSEGS fx R 0x383f8 M model).
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 5 LBX sp fb str _ M model cr s sm ax fx fx1 R R1 0x383f8 0x370d0 M1 (fun a => sp - 64 <= a < sp - 64 + 64) K
           ltac:(lia) BR0 FOK INCS MS1 MG1 FRZ1 ltac:(intros a; apply PMK.rng_dec) ltac:(intros a Pa; cbn beta in Pa; unfold PMSP.pm_scr; clear -Pa; lia)).
  intros BR1.
  assert (AG01 : forall a m, sp <= a -> a + m <= 2 ^ 64 -> L5C.agree_on M M1 a m) by (intros a m H1 H2 i Hi; apply FRZ1; lia).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 5 LBX sp fb str _ M model cr s sm ax BR0) as (_ & _ & _ & UN0 & _).
  apply (cs_loop w K LBX sp r fb cat e str R M model cr s sm ax CTX KONT' (PM.unread (PNM.b_src s) sm) UN0 fx1 R1 M1 model cr s sm ax); [| reflexivity].
  unfold cs_linv. cbn [PNBK.be_s PNBK.be_sm].
  split; [exact BR1|].
  split.
  { unfold cs_regs. split; [exact X1|]. split; [exact X2|]. split; [PMK.rk|]. split; [PMK.rk|]. split; [exact X8|]. split; [exact X9|].
    split; [PMK.rk|]. split; [exact X11|]. split; [exact X12|]. split; [exact X18|]. split; [PMK.rk|]. split; [exact X20|]. split; [exact X21|].
    intros k Hk. apply KS1. revert Hk. clear. intros Hk. cbn in Hk |- *. tauto. }
  split.
  { unfold cs_saved. rewrite Rra in C8. rewrite L5.unsigned_lit in C8 by lia.
    split; [exact C8|]. split; [exact C16|]. split; [exact C24|]. split; [exact C32|]. split; [exact C40|]. split; [exact C48| exact C56]. }
  split; [exact INV|]. split; [apply (ec_agree M M1); [apply AG01; lia|lia|lia| exact EC0]|].
  split; [apply PNBK2.btop_pos_refl; exact INV|]. unfold cs_sz. split; [lia|]. split; [exact SZB| reflexivity].
Qed.

End WithHeap.
End PNSCS.
