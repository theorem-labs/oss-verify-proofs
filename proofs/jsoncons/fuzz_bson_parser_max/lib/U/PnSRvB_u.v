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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnModelFacts PnStatics PnKeep PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj PnBrKit PnBrKit2 PnBrKit3. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnBrKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnOwnerOk. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnOwnerOkS_u
     PnSRvK_u PnSRvA_u PnSRvBP_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSRVB.
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
Lemma eq_of_mod64 a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> (a - b) mod 2 ^ 64 < 1 -> a = b.
Proof.
  intros Ha Hb H. destruct (Z.eq_dec a b) as [E|N]; [exact E|]. exfalso.
  destruct (Z_lt_le_dec a b).
  - rewrite <- (Z.mod_add (a - b) 1 (2 ^ 64)) in H by lia. rewrite Z.mod_small in H by lia. lia.
  - rewrite Z.mod_small in H by lia. lia.
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
Hypothesis RSP : PNRS.read_span_v_spec L HI.

Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac fd P := PMK.feed P ltac:(first [PMK.sc | unfold PNSRVBP.aligned; PMK.sc | symmetry; apply Z_to_bv_bv_unsigned]).

Lemma vwok : PNBK3.vwok RSEGS AD L HI.
Proof. intros fb s H1 H2 H3 H4. apply (PNOKS.vec_owner_ok_S L HI LY HIok). unfold PNOKS.owok_pre. split; [exact H1|]. split; [exact H2|]. split; [exact H3| exact H4]. Qed.

(* [comment removed for export] *)
Definition bst t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax (R9 : bvmap 5 word) (M9 : mem) model9 cr9 s9 sm9 ax9 : Prop :=
  rv_ctx t K LBX sp r fb e str R cr s sm /\ rv_kont K LBX sp r fb cat e str R M model cr s sm ax
  /\ brel LBX sp fb str (BENT M model cr s sm ax) (BENT M9 model9 cr9 s9 sm9 ax9)
  /\ PNSRVK.rv_mid R R9 M9 sp r fb /\ getr R9 (PMK.reg 20) = Z_to_bv 64 (fb + 56)
  /\ PMSP.ec_at RSEGS M9 (fb + 16) e cat /\ PNR.binv s9 /\ PNR.btop_pos s s9
  /\ PNM.b_bb s9 = PNM.b_bb s /\ PM.unread (PNM.b_src s9) sm9 <= PM.unread (PNM.b_src s) sm.

(* [comment removed for export] *)
Lemma pos_err pce v t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax (fx9 fx10 : FPState) R9 R10 (M9 M10 : mem) model9 cr9 s9 sm9 ax9
      (pc9 : Z) (P : Z -> Prop) l c pv :
  PNSRVK.rv_errhead pce v ->
  rv_ctx t K LBX sp r fb e str R cr s sm -> rv_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M9 model9 cr9 s9 sm9 ax9) ->
  PNSRVK.rv_mid R R9 M9 sp r fb -> PMSP.ec_at RSEGS M9 (fb + 16) e cat -> PNR.binv s9 -> PNR.btop_pos s s9 ->
  msteps RSEGS (@mkst fx9 R9 (Z_to_bv 64 pc9) M9 (seg_rom RSEGS)) (@mkst fx10 R10 (Z_to_bv 64 pce) M10 (seg_rom RSEGS)) -> mem_grows M9 M10 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M10 (Z_to_bv 64 a) = M9 (Z_to_bv 64 a)) -> (forall a, {P a} + {~ P a}) ->
  PNM.b_stk s9 = l ++ [c] ->
  (forall a, P a -> (sp - PMSP.pm_scr 8 <= a < sp - 48) \/ (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 16 <= a < PNM.b_sb s9 + 40 * Z.of_nat (length l) + 24)) ->
  PNM.b_sb s9 + 40 * Z.of_nat (length l) + 40 <= sp - 28672 ->
  L5.u64_at RSEGS M10 (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 16) pv -> 0 <= pv < 2 ^ 64 ->
  (forall k, In k [2; 3; 4; 8; 9; 18; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R10 (PMK.reg k) = getr R9 (PMK.reg k)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx9 R9 pc9 M9 model9) K.
Proof.
  intros HD CTX KONT BR9 MID9 EC9 INV9 TP9 MS10 MG10 FRZ10 DEC ES PF ETOP U64 Hpv KS10.
  pose proof MID9 as (X2 & X3 & X4 & X8 & X9 & X18 & SV9).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ _ _ _ _ _ _ BR9) as (PA9 & IA9 & GR9 & UN9 & STK9 & MOK9).
  change (PMSP.pm_scr 8) with 28672 in STK9. pose proof STK9 as (A16 & SLO & SHI & STOP & SDEF9). pose proof MOK9 as (Mh9 & Ml9 & Mm9).
  pose proof (L5C.stk_writable RSEGS _ _ sp 28672 STK9) as WR9.
  pose proof INV9 as (_ & (_ & _ & _ & _ & OKs)). pose proof (OKs (length l) ltac:(rewrite ES, length_app; cbn; lia)) as OKc. rewrite ES, nth_middle in OKc.
  assert (OKc' : PNM.bstate_ok (PNM.BS (PNM.bs_mode c) (PNM.bs_len c) pv (PNM.bs_type c) (PNM.bs_idx c))) by (unfold PNM.bstate_ok in OKc |- *; cbn; lia).
  apply (PNBK2.brel_piece_pos RSEGS AD AN L HI KH 8 LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 fx9 fx10 R9 R10 _ _ M10 P l c pv K ltac:(lia) BR9 FOK INCS MS10 MG10 FRZ10 DEC ES);
    [intros a Pa; destruct (PF a Pa) as [X|X]; [left; lia| right; exact X]| exact U64| exact Hpv|].
  intros BR10.
  apply (PNSRVK.rv_err L HI LY HIok MKE pce v t K LBX sp r fb cat e str R M model cr s sm ax fx10 R10 M10 model9 cr9 _ sm9 ax9 HD CTX KONT BR10).
  - apply (PNSRVK.rv_mid_xfer R R9 R10 M9 M10 sp r fb _ MID9 KS10); [intros k Hk; exact Hk| | lia| lia].
    intros a n H1 H2 i Hi. apply FRZ10; [lia|]. intros Pi. destruct (PF i Pi); lia.
  - destruct EC9 as (_ & _ & ED9). apply (L5C.defined_agree M9 M10 (fb + 16) 16); [| exact ED9]. intros i Hi. apply FRZ10; [lia|]. intros Pi. destruct (PF i Pi); lia.
  - cbn [PNBO.set_stk PNM.b_stk]. destruct TP9 as (l0 & c0 & c0' & Ea & Eb & _). rewrite Ea. rewrite Eb in ES.
    rewrite !length_app. cbn [length]. apply (f_equal (fun x => length x)) in ES. rewrite !length_app in ES. cbn [length] in ES. lia.
  - apply (PNBK2.binv_set_stk_top _ l c); [exact INV9| exact ES| exact OKc'| reflexivity].
Qed.

Lemma pos_mkec t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax (fx9 fx10 : FPState) R9 R10 (M9 M10 : mem) model9 cr9 s9 sm9 ax9
      (pc9 : Z) (P : Z -> Prop) l c pv :
  rv_ctx t K LBX sp r fb e str R cr s sm -> rv_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M9 model9 cr9 s9 sm9 ax9) ->
  PNSRVK.rv_mid R R9 M9 sp r fb -> PMSP.ec_at RSEGS M9 (fb + 16) e cat -> PNR.binv s9 -> PNR.btop_pos s s9 ->
  msteps RSEGS (@mkst fx9 R9 (Z_to_bv 64 pc9) M9 (seg_rom RSEGS)) (@mkst fx10 R10 (Z_to_bv 64 (pa_make_ec AD)) M10 (seg_rom RSEGS)) -> mem_grows M9 M10 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M10 (Z_to_bv 64 a) = M9 (Z_to_bv 64 a)) -> (forall a, {P a} + {~ P a}) ->
  PNM.b_stk s9 = l ++ [c] ->
  (forall a, P a -> (sp - PMSP.pm_scr 8 <= a < sp - 48) \/ (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 16 <= a < PNM.b_sb s9 + 40 * Z.of_nat (length l) + 24)) ->
  PNM.b_sb s9 + 40 * Z.of_nat (length l) + 40 <= sp - 28672 ->
  L5.u64_at RSEGS M10 (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 16) pv -> 0 <= pv < 2 ^ 64 ->
  (forall k, In k [2; 3; 4; 8; 9; 18; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R10 (PMK.reg k) = getr R9 (PMK.reg k)) ->
  getr R10 (PMK.reg 1) = Z_to_bv 64 0x37700 -> getr R10 (PMK.reg 10) = Z_to_bv 64 (fb + 16) -> getr R10 (PMK.reg 11) = Z_to_bv 64 1 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx9 R9 pc9 M9 model9) K.
Proof.
  intros CTX KONT BR9 MID9 EC9 INV9 TP9 MS10 MG10 FRZ10 DEC ES PF ETOP U64 Hpv KS10 Y1 Y10 Y11.
  pose proof MID9 as (X2 & X3 & X4 & X8 & X9 & X18 & SV9 & SX9).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ _ _ _ _ _ _ BR9) as (PA9 & IA9 & GR9 & UN9 & STK9 & MOK9).
  change (PMSP.pm_scr 8) with 28672 in STK9. pose proof STK9 as (A16 & SLO & SHI & STOP & SDEF9). pose proof MOK9 as (Mh9 & Ml9 & Mm9).
  pose proof (L5C.stk_writable RSEGS _ _ sp 28672 STK9) as WR9.
  pose proof INV9 as (_ & (_ & _ & _ & _ & OKs)). pose proof (OKs (length l) ltac:(rewrite ES, length_app; cbn; lia)) as OKc. rewrite ES, nth_middle in OKc.
  assert (OKc' : PNM.bstate_ok (PNM.BS (PNM.bs_mode c) (PNM.bs_len c) pv (PNM.bs_type c) (PNM.bs_idx c))) by (unfold PNM.bstate_ok in OKc |- *; cbn; lia).
  apply (PNBK2.brel_piece_pos RSEGS AD AN L HI KH 8 LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 fx9 fx10 R9 R10 _ _ M10 P l c pv K ltac:(lia) BR9 FOK INCS MS10 MG10 FRZ10 DEC ES);
    [intros a Pa; destruct (PF a Pa) as [X|X]; [left; lia| right; exact X]| exact U64| exact Hpv|].
  intros BR10.
  cbn [pa_make_ec AD PnLayoutS_u.ADDR_S].
  apply (PNSRVK.rv_mkec L HI LY HIok MKE 1 t K LBX sp r fb cat e str R M model cr s sm ax fx10 R10 M10 model9 cr9 _ sm9 ax9 CTX KONT BR10).
  - apply (PNSRVK.rv_mid_xfer R R9 R10 M9 M10 sp r fb _ MID9 KS10); [intros k Hk; exact Hk| | lia| lia].
    intros a n H1 H2 i Hi. apply FRZ10; [lia|]. intros Pi. destruct (PF i Pi); lia.
  - destruct EC9 as (_ & _ & ED9). apply (L5C.defined_agree M9 M10 (fb + 16) 16); [| exact ED9]. intros i Hi. apply FRZ10; [lia|]. intros Pi. destruct (PF i Pi); lia.
  - exact Y1.
  - exact Y10.
  - exact Y11.
  - lia.
  - cbn [PNBO.set_stk PNM.b_stk]. destruct TP9 as (l0 & c0 & c0' & Ea & Eb & _). rewrite Ea. rewrite Eb in ES.
    rewrite !length_app. cbn [length]. apply (f_equal (fun x => length x)) in ES. rewrite !length_app in ES. cbn [length] in ES. lia.
  - apply (PNBK2.binv_set_stk_top _ l c); [exact INV9| exact ES| exact OKc'| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma step3 t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax (fx9 : FPState) R9 (M9 : mem) model9 cr9 s9 sm9 ax9 (ptr n len : Z) :
  rv_ctx t K LBX sp r fb e str R cr s sm -> rv_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M9 model9 cr9 s9 sm9 ax9) ->
  PNSRVK.rv_mid R R9 M9 sp r fb -> getr R9 (PMK.reg 20) = Z_to_bv 64 (fb + 56) ->
  PMSP.ec_at RSEGS M9 (fb + 16) e cat -> PNR.binv s9 -> PNR.btop_pos s s9 -> PM.unread (PNM.b_src s9) sm9 <= PM.unread (PNM.b_src s) sm ->
  getr R9 (PMK.reg 10) = Z_to_bv 64 ptr -> getr R9 (PMK.reg 11) = Z_to_bv 64 n -> getr R9 (PMK.reg 19) = Z_to_bv 64 len ->
  0 <= n < 2 ^ 26 -> 0 <= len < 2 ^ 64 -> 0 <= ptr < 2 ^ 64 -> (n = len -> PNR.bb_room s9 sm9) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx9 R9 0x3795c M9 model9) K.
Proof.
  intros CTX KONT BR9 MID9 X20 EC9 INV9 TP9 LEU Q10 Q11 Q19 Hn Hlen Hptr ROOMc.
  pose proof MID9 as (X2 & X3 & X4 & X8 & X9 & X18 & SV9).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ _ _ _ _ _ _ BR9) as (PA9 & IA9 & GR9 & UN9 & STK9 & MOK9).
  change (PMSP.pm_scr 8) with 28672 in STK9. pose proof STK9 as (A16 & SLO & SHI & STOP & SDEF9). pose proof MOK9 as (Mh9 & Ml9 & Mm9).
  pose proof (L5C.stk_writable RSEGS _ _ sp 28672 STK9) as WR9.
  pose proof PA9 as (_ & PD9 & _ & _ & _ & CM9 & _).
  pose proof BR9 as ((_ & _ & VIS9 & _ & BASE9 & _) & _). cbn [PNBK.be_M] in VIS9, BASE9.
  unfold PNR.o_v, PMSP.o_v, PMSP.visitor_at in VIS9. cbn [pa_off_v pa_vp_visitor AD PnLayoutS_u.ADDR_S] in VIS9.
  pose proof BASE9 as (IMG9 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG9.
  destruct (PNSRVK.rv_top L HI LY HIok LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 BR9 INV9) as (l & c & ES & OKc & UE & UP & WP & E0 & E1 & EI & EA).
  set (et := PNM.b_sb s9 + 40 * Z.of_nat (length l)) in *.
  pose proof OKc as (_ & _ & POS & _).
  assert (DEFB : L5.defined M9 (sp - 96) 1) by (apply (L5.defined_sub M9 (sp - 28672) 28672); [exact SDEF9| lia| lia]).
  (let T := type of (PNSRVBP.vlBi3_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 51%nat => et + 40 | 52%nat => PNM.bs_pos c | 59%nat => len | 61%nat => ptr | 62%nat => n | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVBP.vlBi3_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 51%nat => et + 40 | 52%nat => PNM.bs_pos c | 59%nat => len | 61%nat => ptr | 62%nat => n | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVBP.aligned; PMK.sc | symmetry; apply Z_to_bv_bv_unsigned])).
  destruct P as (fx10 & R10 & M10 & MG10 & _ & FRZ10 & [(MS10 & KS10 & Y1 & Y10 & Y11 & LT & CP10)|(MS10 & KS10 & _ & Y10 & _ & _ & _ & _ & _ & _ & _ & _ & CP10 & LT)]).
  - (* [comment removed for export] *)
    apply (pos_mkec t K LBX sp r fb cat e str R M model cr s sm ax fx9 fx10 R9 R10 M9 M10 model9 cr9 s9 sm9 ax9 _
             (fun a => (et + 40 - 24 <= a < et + 40 - 24 + 8) \/ (sp - 64 <= a < sp - 64 + 16) \/ (sp - 112 <= a < sp - 112 + 16)) l c (PNM.bs_pos c)
             CTX KONT BR9 MID9 EC9 INV9 TP9 MS10 MG10
             ltac:(intros a Ha N; apply FRZ10; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; left; exact X| intros X; apply N; right; right; exact X])
             ltac:(intros a; apply PMK.or_dec; [| apply PMK.or_dec]; apply PMK.rng_dec) ES); [| unfold et in E1; exact E1| unfold et in CP10; replace (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 16) with (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 40 - 24) by lia; exact CP10| lia| intros k Hk; apply KS10; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| exact Y1| exact Y10| exact Y11].
    intros a Pa. cbn beta in Pa. unfold et in Pa. unfold PMSP.pm_scr. destruct Pa as [X|[X|X]]; [right; lia| left; lia| left; lia].
  - (* [comment removed for export] *)
    pose proof (eq_of_mod64 n len ltac:(lia) Hlen LT) as Hnl.
    assert (OKc' : PNM.bstate_ok (PNM.BS (PNM.bs_mode c) (PNM.bs_len c) ((PNM.bs_pos c + len) mod 2 ^ 64) (PNM.bs_type c) (PNM.bs_idx c)))
      by (unfold PNM.bstate_ok in OKc |- *; cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx]; pose proof (Z.mod_pos_bound (PNM.bs_pos c + len) (2 ^ 64) ltac:(lia)); lia).
    apply (PNBK2.brel_piece_pos RSEGS AD AN L HI KH 8 LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 fx9 fx10 R9 R10 _ _ M10
             (fun a => (et + 40 - 24 <= a < et + 40 - 24 + 8) \/ (sp - 64 <= a < sp - 64 + 16) \/ (sp - 112 <= a < sp - 112 + 16)) l c ((PNM.bs_pos c + len) mod 2 ^ 64) K ltac:(lia) BR9 FOK INCS MS10 MG10
             ltac:(intros a Ha N; apply FRZ10; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; left; exact X| intros X; apply N; right; right; exact X])
             ltac:(intros a; apply PMK.or_dec; [| apply PMK.or_dec]; apply PMK.rng_dec) ES);
      [intros a Pa; cbn beta in Pa; unfold et in Pa; unfold PMSP.pm_scr; destruct Pa as [X|[X|X]]; [right; lia| left; lia| left; lia]
      | unfold et in CP10; replace (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 16) with (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 40 - 24) by lia; exact CP10
      | apply Z.mod_pos_bound; lia |].
    intros BR10.
    assert (AG910 : L5C.agree_on M9 M10 (fb + 16) 16) by (intros i Hi; apply FRZ10; unfold et; lia).
    apply (PNSRVK.rv_sbmore L HI LY HIok t K LBX sp r fb cat e str R M model cr s sm ax fx10 R10 M10 model9 cr9 _ sm9 ax9 1 CTX KONT BR10); [| exact Y10|].
    + apply (PNSRVK.rv_mid_xfer R R9 R10 M9 M10 sp r fb _ MID9 KS10); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| | lia| lia].
      intros a m H1 H2 i Hi. apply FRZ10; unfold et; lia.
    + right. split; [reflexivity|]. split; [apply (PNSRVK.ec_agree M9 M10 _ _ _ AG910 ltac:(lia) ltac:(lia) EC9)|].
      split; [apply (PNBK2.binv_set_stk_top _ l c); [exact INV9| exact ES| exact OKc'| reflexivity]|].
      split.
      * left. apply (PNBK2.btop_pos_trans s s9); [exact TP9|]. apply (PNBK2.btop_pos_set_stk _ l c); [exact ES| exact OKc'| reflexivity| reflexivity| reflexivity| reflexivity].
      * intros _. unfold PNR.bb_room in *. cbn [PNBO.set_stk PNM.b_bb PNM.b_src]. apply ROOMc. exact Hnl.
Qed.

(* [comment removed for export] *)
Lemma step2 t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax (fx9 : FPState) R9 (M9 : mem) model9 cr9 s9 sm9 ax9 (d : Z) :
  bst t K LBX sp r fb cat e str R M model cr s sm ax R9 M9 model9 cr9 s9 sm9 ax9 ->
  getr R9 (PMK.reg 10) = Z_to_bv 64 d -> 0 <= d <= 1 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx9 R9 0x3791c M9 model9) K.
Proof.
  intros BS Q10 Hd.
  pose proof BS as (CTX & KONT & BR9 & MID9 & X20 & EC9 & INV9 & TP9 & EBB & LEU).
  pose proof MID9 as (X2 & X3 & X4 & X8 & X9 & X18 & SV9).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ _ _ _ _ _ _ BR9) as (PA9 & IA9 & GR9 & UN9 & STK9 & MOK9).
  change (PMSP.pm_scr 8) with 28672 in STK9. pose proof STK9 as (A16 & SLO & SHI & STOP & SDEF9). pose proof MOK9 as (Mh9 & Ml9 & Mm9).
  pose proof (L5C.stk_writable RSEGS _ _ sp 28672 STK9) as WR9.
  destruct (PNSRVK.rv_top L HI LY HIok LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 BR9 INV9) as (l & c & ES & OKc & UE & UP & WP & E0 & E1 & EI & EA).
  set (et := PNM.b_sb s9 + 40 * Z.of_nat (length l)) in *.
  pose proof OKc as (_ & _ & POS & _).
  pose proof (bv_unsigned_in_range _ (getr R9 (PMK.reg 19))) as BUR9_19. change (bv_modulus 64) with (2 ^ 64) in BUR9_19. set (len := bv_unsigned (getr R9 (PMK.reg 19))) in *.
  (let T := type of (PNSRVBP.vlBi2_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 50%nat => d | 51%nat => et + 40 | 52%nat => PNM.bs_pos c | 59%nat => len | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVBP.vlBi2_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 50%nat => d | 51%nat => et + 40 | 52%nat => PNM.bs_pos c | 59%nat => len | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVBP.aligned; PMK.sc | symmetry; apply Z_to_bv_bv_unsigned])).
  destruct P as (fx10 & R10 & M10 & MG10 & _ & FRZ10 & [(MS10 & KS10 & Y1 & Y10 & Y11 & _ & _ & LT & CP10)|(MS10 & KS10 & Y1 & Y10 & Y11 & Y12 & _ & LT & CP10)]).
  - (* [comment removed for export] *)
    apply (pos_mkec t K LBX sp r fb cat e str R M model cr s sm ax fx9 fx10 R9 R10 M9 M10 model9 cr9 s9 sm9 ax9 _
             (fun a => et + 40 - 24 <= a < et + 40 - 24 + 8) l c ((d + PNM.bs_pos c) mod 2 ^ 64)
             CTX KONT BR9 MID9 EC9 INV9 TP9 MS10 MG10 FRZ10 ltac:(intros a; apply PMK.rng_dec) ES);
      [| unfold et in E1; exact E1| unfold et in CP10; replace (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 16) with (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 40 - 24) by lia; exact CP10
      | apply Z.mod_pos_bound; lia| intros k Hk; apply KS10; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| exact Y1| exact Y10| exact Y11].
    intros a Pa. cbn beta in Pa. unfold et in Pa. right; lia.
  - (* [comment removed for export] *)
    pose proof (eq_of_mod d 1 Hd ltac:(lia) LT) as Hd1.
    assert (OKc' : PNM.bstate_ok (PNM.BS (PNM.bs_mode c) (PNM.bs_len c) ((d + PNM.bs_pos c) mod 2 ^ 64) (PNM.bs_type c) (PNM.bs_idx c)))
      by (unfold PNM.bstate_ok in OKc |- *; cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx]; pose proof (Z.mod_pos_bound (d + PNM.bs_pos c) (2 ^ 64) ltac:(lia)); lia).
    apply (PNBK2.brel_piece_pos RSEGS AD AN L HI KH 8 LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 fx9 fx10 R9 R10 _ _ M10
             (fun a => et + 40 - 24 <= a < et + 40 - 24 + 8) l c ((d + PNM.bs_pos c) mod 2 ^ 64) K ltac:(lia) BR9 FOK INCS MS10 MG10 FRZ10 ltac:(intros a; apply PMK.rng_dec) ES);
      [intros a Pa; cbn beta in Pa; unfold et in Pa; right; lia
      | unfold et in CP10; replace (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 16) with (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 40 - 24) by lia; exact CP10
      | apply Z.mod_pos_bound; lia |].
    intros BR10.
    set (s10 := PNBO.set_stk s9 (l ++ [PNM.BS (PNM.bs_mode c) (PNM.bs_len c) ((d + PNM.bs_pos c) mod 2 ^ 64) (PNM.bs_type c) (PNM.bs_idx c)])) in *.
    assert (AG910 : forall a m, (a + m <= et + 16 \/ et + 24 <= a) -> 0 <= a -> a + m <= 2 ^ 64 -> L5C.agree_on M9 M10 a m) by (intros a m H0 H1 H2 i Hi; apply FRZ10; lia).
    assert (MID10 : PNSRVK.rv_mid R R10 M10 sp r fb).
    { apply (PNSRVK.rv_mid_xfer R R9 R10 M9 M10 sp r fb _ MID9 KS10); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a m H1 H2; apply AG910; unfold et; lia| lia| lia]. }
    pose proof MID10 as (W2 & W3 & W4 & W8 & W9 & W18 & SV10).
    assert (EC10 : PMSP.ec_at RSEGS M10 (fb + 16) e cat) by (apply (PNSRVK.ec_agree M9 M10); [apply AG910; unfold et; lia|lia|lia| exact EC9]).
    assert (INV10 : PNR.binv s10) by (apply (PNBK2.binv_set_stk_top _ l c); [exact INV9| exact ES| exact OKc'| reflexivity]).
    assert (TP10 : PNR.btop_pos s s10) by (apply (PNBK2.btop_pos_trans s s9); [exact TP9|]; apply (PNBK2.btop_pos_set_stk _ l c); [exact ES| exact OKc'| reflexivity| reflexivity| reflexivity| reflexivity]).
    change (@PMSP.cfg RSEGS fx10 R10 0x38984 M10 model9) with (@PMSP.cfg RSEGS fx10 R10 (PNL.pn_read_span_v AN) M10 model9).
    pose proof RSP as RSP'. unfold PNRS.read_span_v_spec, PNR.read_span_v_spec in RSP'.
    apply (PNBK3.brel_read_span_v RSEGS AD AN L HI KH 8 LBX sp fb str _ M10 model9 cr9 s10 sm9 ax9 fx10 R10 (sp - 96) _ len K vwok RSP' ltac:(lia) K0 BR10 FOK INCS CRED Y1 ltac:(split; [lia| reflexivity]) W2 W3 W4);
      [replace (fb + 56) with (fb + 40 + 16) by lia; exact Y10| exact Y11| exact Y12| lia| lia| unfold PMSP.pm_scr; lia| exact (PNSRVK.mod16_sub176 sp A16)
      | cbn [s10 PNBO.set_stk PNM.b_src]; lia| |].
    { unfold PNR.bb_room in *. cbn [s10 PNBO.set_stk PNM.b_bb PNM.b_src]. rewrite EBB. apply (PGV8.v8_room_mono _ (PM.unread (PNM.b_src s) sm)); [exact LEU| exact ROOM0]. }
    intros fx11 R11 M11 model11 src11 x11 g11 sm11 cr11 ptr n RP1011 Z10 Z11 Hn1 Hn2 UNR11 LOC DEF11 ROOMc BR11 AG1011.
    pose proof (bv_unsigned_in_range _ (getr R11 (PMK.reg 10))) as BUR11_10. change (bv_modulus 64) with (2 ^ 64) in BUR11_10.
    apply (step3 t K LBX sp r fb cat e str R M model cr s sm ax fx11 R11 M11 model11 cr11 (PNM.with_src_bb s10 src11 x11 g11) sm11 ax9 ptr n len CTX KONT BR11);
      [| rewrite (PMK.cs_of_preserved R10 R11 20%nat RP1011) by PMK.inl; rewrite (KS10 20%nat) by PMK.inl; exact X20| | destruct INV10 as (ID & SH); split; [exact ID| exact SH]
       | destruct TP10 as (la & ca & cb & Ea & Eb & Q); exists la, ca, cb; split; [exact Ea|]; split; [exact Eb| exact Q]
       | cbn [PNM.with_src_bb PNM.b_src]; cbn [s10 PNBO.set_stk PNM.b_src] in UNR11; lia
       | exact Z10| exact Z11| rewrite (PMK.cs_of_preserved R10 R11 19%nat RP1011) by PMK.inl; rewrite (KS10 19%nat) by PMK.inl; unfold len; symmetry; apply Z_to_bv_bv_unsigned
       | lia| unfold len; apply bv_unsigned_in_range| | exact ROOMc].
    + apply (PNSRVK.rv_mid_pres R R10 R11 M10 M11 sp r fb MID10 RP1011); [intros a m H1 H2; apply AG1011; lia| lia| lia].
    + apply (PNSRVK.ec_agree M10 M11); [apply AG1011; lia|lia|lia| exact EC10].
    + destruct LOC as [(-> & _)|(B & m & Hin & HB1 & HB2)]; [lia|].
      destruct (PNBK2.brel_blocks RSEGS AD AN L HI KH 8 LBX sp fb str _ _ _ _ _ _ _ BR11) as (_ & OWNB11 & _). destruct (OWNB11 B m Hin) as (B0 & B4). unfold hl_ceil in B4. lia.
Qed.

(* [comment removed for export] *)
Lemma step1 t K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax (fx9 : FPState) R9 (M9 : mem) model9 cr9 s9 sm9 ax9 (d : Z) :
  bst t K LBX sp r fb cat e str R M model cr s sm ax R9 M9 model9 cr9 s9 sm9 ax9 ->
  getr R9 (PMK.reg 10) = Z_to_bv 64 d -> 0 <= d <= 4 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx9 R9 0x378d4 M9 model9) K.
Proof.
  intros BS Q10 Hd.
  pose proof BS as (CTX & KONT & BR9 & MID9 & X20 & EC9 & INV9 & TP9 & EBB & LEU).
  pose proof MID9 as (X2 & X3 & X4 & X8 & X9 & X18 & SV9).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ _ _ _ _ _ _ BR9) as (PA9 & IA9 & GR9 & UN9 & STK9 & MOK9).
  change (PMSP.pm_scr 8) with 28672 in STK9. pose proof STK9 as (A16 & SLO & SHI & STOP & SDEF9). pose proof MOK9 as (Mh9 & Ml9 & Mm9).
  pose proof (L5C.stk_writable RSEGS _ _ sp 28672 STK9) as WR9.
  destruct (PNSRVK.rv_top L HI LY HIok LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 BR9 INV9) as (l & c & ES & OKc & UE & UP & WP & E0 & E1 & EI & EA).
  set (et := PNM.b_sb s9 + 40 * Z.of_nat (length l)) in *.
  pose proof OKc as (_ & _ & POS & _).
  assert (DEFB : L5.defined M9 (sp - 80) 4) by (apply (L5.defined_sub M9 (sp - 28672) 28672); [exact SDEF9| lia| lia]).
  (let T := type of (PNSRVBP.vlBi1_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 50%nat => d | 51%nat => et + 40 | 52%nat => PNM.bs_pos c | _ => 0 end))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVBP.vlBi1_conc fx9 R9 M9 (PNSRVK.tv sp r fb R (fun j => match j with 50%nat => d | 51%nat => et + 40 | 52%nat => PNM.bs_pos c | _ => 0 end))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVBP.aligned; PMK.sc | symmetry; apply Z_to_bv_bv_unsigned])).
  assert (OKc' : PNM.bstate_ok (PNM.BS (PNM.bs_mode c) (PNM.bs_len c) ((d + PNM.bs_pos c) mod 2 ^ 64) (PNM.bs_type c) (PNM.bs_idx c)))
    by (unfold PNM.bstate_ok in OKc |- *; cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx]; pose proof (Z.mod_pos_bound (d + PNM.bs_pos c) (2 ^ 64) ltac:(lia)); lia).
  destruct P as (fx10 & R10 & M10 & MG10 & _ & FRZ10 & [(MS10 & KS10 & Y1 & Y10 & Y11 & _ & _ & LT & CP10)|[(MS10 & KS10 & _ & _ & _ & LT & CP10)|(MS10 & KS10 & Y1 & Y10 & Y11 & Y12 & _ & LT & CP10)]]).
  - (* [comment removed for export] *)
    apply (pos_mkec t K LBX sp r fb cat e str R M model cr s sm ax fx9 fx10 R9 R10 M9 M10 model9 cr9 s9 sm9 ax9 _
             (fun a => et + 40 - 24 <= a < et + 40 - 24 + 8) l c ((d + PNM.bs_pos c) mod 2 ^ 64)
             CTX KONT BR9 MID9 EC9 INV9 TP9 MS10 MG10 FRZ10 ltac:(intros a; apply PMK.rng_dec) ES);
      [| unfold et in E1; exact E1| unfold et in CP10; replace (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 16) with (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 40 - 24) by lia; exact CP10
      | apply Z.mod_pos_bound; lia| intros k Hk; apply KS10; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| exact Y1| exact Y10| exact Y11].
    intros a Pa. cbn beta in Pa. unfold et in Pa. right; lia.
  - (* [comment removed for export] *)
    apply (pos_err 0x37da8 6 t K LBX sp r fb cat e str R M model cr s sm ax fx9 fx10 R9 R10 M9 M10 model9 cr9 s9 sm9 ax9 _
             (fun a => et + 40 - 24 <= a < et + 40 - 24 + 8) l c ((d + PNM.bs_pos c) mod 2 ^ 64)
             ltac:(right; right; left; split; reflexivity) CTX KONT BR9 MID9 EC9 INV9 TP9 MS10 MG10 FRZ10 ltac:(intros a; apply PMK.rng_dec) ES);
      [| unfold et in E1; exact E1| unfold et in CP10; replace (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 16) with (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 40 - 24) by lia; exact CP10
      | apply Z.mod_pos_bound; lia| intros k Hk; apply KS10; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto].
    intros a Pa. cbn beta in Pa. unfold et in Pa. right; lia.
  - (* [comment removed for export] *)
    apply (PNBK2.brel_piece_pos RSEGS AD AN L HI KH 8 LBX sp fb str _ M9 model9 cr9 s9 sm9 ax9 fx9 fx10 R9 R10 _ _ M10
             (fun a => et + 40 - 24 <= a < et + 40 - 24 + 8) l c ((d + PNM.bs_pos c) mod 2 ^ 64) K ltac:(lia) BR9 FOK INCS MS10 MG10 FRZ10 ltac:(intros a; apply PMK.rng_dec) ES);
      [intros a Pa; cbn beta in Pa; unfold et in Pa; right; lia
      | unfold et in CP10; replace (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 16) with (PNM.b_sb s9 + 40 * Z.of_nat (length l) + 40 - 24) by lia; exact CP10
      | apply Z.mod_pos_bound; lia |].
    intros BR10.
    set (s10 := PNBO.set_stk s9 (l ++ [PNM.BS (PNM.bs_mode c) (PNM.bs_len c) ((d + PNM.bs_pos c) mod 2 ^ 64) (PNM.bs_type c) (PNM.bs_idx c)])) in *.
    assert (AG910 : forall a m, (a + m <= et + 16 \/ et + 24 <= a) -> 0 <= a -> a + m <= 2 ^ 64 -> L5C.agree_on M9 M10 a m) by (intros a m H0 H1 H2 i Hi; apply FRZ10; lia).
    assert (MID10 : PNSRVK.rv_mid R R10 M10 sp r fb).
    { apply (PNSRVK.rv_mid_xfer R R9 R10 M9 M10 sp r fb _ MID9 KS10); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a m H1 H2; apply AG910; unfold et; lia| lia| lia]. }
    pose proof MID10 as (W2 & W3 & W4 & W8 & W9 & W18 & SV10).
    assert (EC10 : PMSP.ec_at RSEGS M10 (fb + 16) e cat) by (apply (PNSRVK.ec_agree M9 M10); [apply AG910; unfold et; lia|lia|lia| exact EC9]).
    assert (INV10 : PNR.binv s10) by (apply (PNBK2.binv_set_stk_top _ l c); [exact INV9| exact ES| exact OKc'| reflexivity]).
    assert (TP10 : PNR.btop_pos s s10) by (apply (PNBK2.btop_pos_trans s s9); [exact TP9|]; apply (PNBK2.btop_pos_set_stk _ l c); [exact ES| exact OKc'| reflexivity| reflexivity| reflexivity| reflexivity]).
    change (@PMSP.cfg RSEGS fx10 R10 0x370d0 M10 model9) with (@PMSP.cfg RSEGS fx10 R10 (pa_src_read AD) M10 model9).
    pose proof SRD as SRD'. unfold PNRS.src_read_spec, PNR.src_read_spec in SRD'.
    apply (PNBK.brel_src_read RSEGS AD AN L HI KH 8 LBX sp fb str _ M10 model9 cr9 s10 sm9 ax9 fx10 R10 (sp - 96) _ (sp - 96) 1 K SRD' ltac:(lia) K0 BR10 FOK INCS Y1
             ltac:(split; [lia| reflexivity]) W2 W3 W4); [replace (fb + 56) with (fb + 40 + 16) by lia; exact Y10| exact Y11| exact Y12| lia| unfold PMSP.pm_scr; lia| exact (PNSRVK.mod16_sub176 sp A16)| lia| lia| lia|].
    intros fx11 R11 M11 src11 sm11 d2 RP1011 Z10 Hd2 UNR11 DEF11 BR11 AG1011.
    apply (step2 t K LBX sp r fb cat e str R M model cr s sm ax fx11 R11 M11 model9 cr9 (PNM.with_srcB s10 src11) sm11 ax9 d2); [| exact Z10| exact Hd2].
    split; [exact CTX|]. split; [exact KONT|]. split; [exact BR11|]. split.
    { apply (PNSRVK.rv_mid_pres R R10 R11 M10 M11 sp r fb MID10 RP1011); [intros a m H1 H2; apply AG1011; lia| lia| lia]. }
    split; [rewrite (PMK.cs_of_preserved R10 R11 20%nat RP1011) by PMK.inl; rewrite (KS10 20%nat) by PMK.inl; exact X20|].
    split; [apply (PNSRVK.ec_agree M10 M11); [apply AG1011; lia|lia|lia| exact EC10]|].
    split; [destruct INV10 as (ID & SH); split; [exact ID| exact SH]|].
    split; [destruct TP10 as (la & ca & cb & Ea & Eb & Q); exists la, ca, cb; split; [exact Ea|]; split; [exact Eb| exact Q]|].
    split; [cbn [PNM.with_srcB PNM.b_bb s10 PNBO.set_stk]; exact EBB| cbn [PNM.with_srcB PNM.b_src]; cbn [s10 PNBO.set_stk PNM.b_src] in UNR11; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma armBin : PNSRVA.arm_stmt L HI 0x378c0.
Proof.
  intros t K LBX sp r fb cat e str R M model cr s sm ax fx5 R5 M5 model5 cr5 ax5 CTX KONT BR5 MID EC5.
  pose proof MID as (X2 & X3 & X4 & X8 & X9 & X18 & SV5).
  pose proof CTX as (Ht & K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & INV0 & UNR0 & He & ROOM0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 BR5) as (PA5 & IA5 & GR5 & UN5 & STK5 & MOK5).
  change (PMSP.pm_scr 8) with 28672 in STK5. pose proof STK5 as (A16 & SLO & SHI & STOP & SDEF5). pose proof MOK5 as (Mh5 & Ml5 & Mm5).
  pose proof (L5C.stk_writable RSEGS _ M5 sp 28672 STK5) as WR5.
  (let T := type of (PNSRVBP.vlBi0_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) in let T := eval cbv beta iota delta [PNSRVK.tv] in T in LeanFeed.pfeed_at P (PNSRVBP.vlBi0_conc fx5 R5 M5 (PNSRVK.tv sp r fb R (fun _ => 0))) T ltac:(cbv beta iota delta [PNSRVK.tv]) ltac:(first [PMK.sc | unfold PNSRVBP.aligned; PMK.sc | symmetry; apply Z_to_bv_bv_unsigned])).
  destruct P as (fx6 & R6 & M6 & MG6 & EQ6w & EQ6 & MS6 & KS6 & Y1 & Y10 & Y11 & Y12 & Y20).
  assert (EM6 : M6 = M5) by (apply functional_extensionality; exact EQ6w). subst M6.
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx5 fx6 R5 R6 _ _ M5 (fun _ => False) K
           ltac:(lia) BR5 FOK INCS MS6 MG6 ltac:(intros a Ha _; apply EQ6; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
  intros BR6.
  change (@PMSP.cfg RSEGS fx6 R6 0x370d0 M5 model5) with (@PMSP.cfg RSEGS fx6 R6 (pa_src_read AD) M5 model5).
  pose proof SRD as SRD'. unfold PNRS.src_read_spec, PNR.src_read_spec in SRD'.
  apply (PNBK.brel_src_read RSEGS AD AN L HI KH 8 LBX sp fb str _ M5 model5 cr5 s sm ax5 fx6 R6 (sp - 96) _ (sp - 80) 4 K SRD' ltac:(lia) K0 BR6 FOK INCS Y1
           ltac:(split; [lia| reflexivity])); [rewrite (KS6 2%nat) by PMK.inl; exact X2| rewrite (KS6 3%nat) by PMK.inl; exact X3| rewrite (KS6 4%nat) by PMK.inl; exact X4
    | replace (fb + 56) with (fb + 40 + 16) by lia; exact Y10| exact Y11| exact Y12| lia| unfold PMSP.pm_scr; lia| exact (PNSRVK.mod16_sub176 sp A16)| lia| lia| lia|].
  intros fx7 R7 M7 src7 sm7 d RP67 Z10 Hd UNR7 DEF7 BR7 AG67.
  apply (step1 t K LBX sp r fb cat e str R M model cr s sm ax fx7 R7 M7 model5 cr5 (PNM.with_srcB s src7) sm7 ax5 d); [| exact Z10| exact Hd].
  split; [exact CTX|]. split; [exact KONT|]. split; [exact BR7|]. split.
  { apply (PNSRVK.rv_mid_pres R R6 R7 M5 M7 sp r fb); [| exact RP67| intros a n H1 H2; apply AG67; lia| lia| lia].
    apply (PNSRVK.rv_mid_xfer R R5 R6 M5 M5 sp r fb _ MID KS6); [intros k Hk; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto| intros a n _ _ i Hi; reflexivity| lia| lia]. }
  split; [rewrite (PMK.cs_of_preserved R6 R7 20%nat RP67) by PMK.inl; replace (fb + 56) with (fb + 40 + 16) by lia; exact Y20|].
  split; [apply (PNSRVK.ec_agree M5 M7); [apply AG67; lia|lia|lia| exact EC5]|].
  split; [destruct INV0 as (ID & SH); split; [exact ID| exact SH]|].
  split; [destruct (PNBK2.btop_pos_refl s INV0) as (la & ca & cb & Ea & Eb & Q); exists la, ca, cb; split; [exact Ea|]; split; [exact Eb| exact Q]|].
  split; [reflexivity| cbn [PNM.with_srcB PNM.b_src]; lia].
Qed.

End WithHeap.
End PNSRVB.
