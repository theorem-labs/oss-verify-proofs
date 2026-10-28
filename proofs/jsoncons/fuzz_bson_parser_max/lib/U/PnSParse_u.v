(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith Zwf List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep PmFrame PmParSpecs PmParKit PmCertKitG PgSrc PgV8.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnModelFacts PnStatics PnKeep PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj PnBrKit PnBrKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnBrKitS_u PnSParseP_u
     Bs0_code_360b4_360b8_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSPA.
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
Lemma mod16_sub112 sp : sp mod 16 = 0 -> (sp - 112) mod 16 = 0.
Proof. intros H. replace (sp - 112) with (sp + (-7) * 16) by lia. rewrite Z.mod_add by lia. exact H. Qed.

(* [comment removed for export] *)
Lemma bflag_app l c : PNR.bflag (l ++ [c]) = (if (Z.eqb (PNM.bs_mode c) 0 || Z.eqb (PNM.bs_mode c) 4)%bool then 1 else 0).
Proof. unfold PNR.bflag. rewrite last_last. reflexivity. Qed.
Lemma bflag_range stk : 0 <= PNR.bflag stk <= 1.
Proof. unfold PNR.bflag. destruct (_ || _)%bool; lia. Qed.

(* [comment removed for export] *)
Lemma shape_bottom_nil l c : PNR.bstack_shape (l ++ [c]) -> PNR.bmode_bottom (PNM.bs_mode c) -> l = [].
Proof.
  intros (L1 & L2 & B0 & CT & OK) Hm. destruct l as [|x l']; [reflexivity|]. exfalso.
  pose proof (CT (length (x :: l')) ltac:(rewrite length_app; cbn; lia)) as X. rewrite nth_middle in X.
  unfold PNR.bmode_bottom in Hm. unfold PNR.bmode_cont in X. lia.
Qed.
Lemma shape_cont_cons l c : PNR.bstack_shape (l ++ [c]) -> PNR.bmode_cont (PNM.bs_mode c) -> l <> [].
Proof.
  intros (L1 & L2 & B0 & CT & OK) Hm E. subst l. cbn in B0. unfold PNR.bmode_bottom in B0. unfold PNR.bmode_cont in Hm. lia.
Qed.
(* [comment removed for export] *)
Lemma shape_top_mode l c c' :
  PNR.bstack_shape (l ++ [c]) -> PNM.bstate_ok c' ->
  (l = [] -> PNR.bmode_bottom (PNM.bs_mode c')) -> (l <> [] -> PNR.bmode_cont (PNM.bs_mode c')) -> PNR.bstack_shape (l ++ [c']).
Proof.
  intros (L1 & L2 & B0 & CT & OK) OK' HB HC. unfold PNR.bstack_shape. rewrite length_app in *. cbn [length] in *.
  split; [lia|]. split; [lia|].
  split.
  { destruct l as [|x l']; cbn in B0 |- *; [apply HB; reflexivity| exact B0]. }
  split.
  { intros i Hi. destruct (Nat.eq_dec i (length l)) as [->|NE].
    - rewrite nth_middle. apply HC. intros E. subst l. cbn in Hi. lia.
    - rewrite app_nth1 by lia. pose proof (CT i Hi) as X. rewrite app_nth1 in X by lia. exact X. }
  intros i Hi. destruct (Nat.eq_dec i (length l)) as [->|NE].
  - rewrite nth_middle. exact OK'.
  - rewrite app_nth1 by lia. pose proof (OK i Hi) as X. rewrite app_nth1 in X by lia. exact X.
Qed.

(* [comment removed for export] *)
Definition lp_regs (R R1 : bvmap 5 word) (sp fb : Z) : Prop :=
  getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 112) /\ getr R1 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) /\ getr R1 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD)
  /\ getr R1 (PMK.reg 8) = Z_to_bv 64 (fb + 40) /\ getr R1 (PMK.reg 9) = Z_to_bv 64 (fb + 16)
  /\ getr R1 (PMK.reg 18) = Z_to_bv 64 (fb + 464) /\ getr R1 (PMK.reg 19) = Z_to_bv 64 (fb + 56)
  /\ getr R1 (PMK.reg 20) = Z_to_bv 64 1 /\ getr R1 (PMK.reg 21) = Z_to_bv 64 40 /\ getr R1 (PMK.reg 22) = Z_to_bv 64 4
  /\ getr R1 (PMK.reg 23) = Z_to_bv 64 2 /\ getr R1 (PMK.reg 24) = Z_to_bv 64 79632 /\ getr R1 (PMK.reg 25) = Z_to_bv 64 256
  /\ (forall k, In k [26; 27]%nat -> getr R1 (PMK.reg k) = getr R (PMK.reg k)).
Definition lp_saved (R : bvmap 5 word) (M1 : mem) (sp r : Z) : Prop :=
  L5.u64_at RSEGS M1 (sp - 8) r /\ L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))
  /\ L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) /\ L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))
  /\ L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 19))) /\ L5.u64_at RSEGS M1 (sp - 48) (bv_unsigned (getr R (PMK.reg 20)))
  /\ L5.u64_at RSEGS M1 (sp - 56) (bv_unsigned (getr R (PMK.reg 21))) /\ L5.u64_at RSEGS M1 (sp - 64) (bv_unsigned (getr R (PMK.reg 22)))
  /\ L5.u64_at RSEGS M1 (sp - 72) (bv_unsigned (getr R (PMK.reg 23))) /\ L5.u64_at RSEGS M1 (sp - 80) (bv_unsigned (getr R (PMK.reg 24)))
  /\ L5.u64_at RSEGS M1 (sp - 88) (bv_unsigned (getr R (PMK.reg 25))).
Lemma lp_saved_agree R (M1 M2 : mem) sp r :
  (forall a n, sp - 88 <= a -> a + n <= sp -> L5C.agree_on M1 M2 a n) -> 0 <= sp - 112 -> sp <= 2 ^ 64 -> lp_saved R M1 sp r -> lp_saved R M2 sp r.
Proof.
  intros AG H1 H2 SV. unfold lp_saved in *.
  repeat lazymatch goal with
  | |- _ /\ _ => split
  | |- L5.u64_at _ M2 ?a ?v => apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG; lia|lia|lia| apply SV]
  end.
Qed.
Lemma lp_regs_pres R R1 R2 sp fb : lp_regs R R1 sp fb -> regs_preserved R1 R2 -> lp_regs R R2 sp fb.
Proof.
  intros RG RP. unfold lp_regs in *.
  repeat lazymatch goal with
  | |- _ /\ _ => split
  | |- getr R2 (PMK.reg ?k) = _ => rewrite (PMK.cs_of_preserved R1 R2 k RP) by PMK.inl; apply RG
  | |- forall k, _ => intros k Hk; rewrite (PMK.cs_of_preserved R1 R2 k RP) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto); apply RG; exact Hk
  end.
Qed.
(* [comment removed for export] *)
Definition ec_some (M : mem) (fb : Z) : Prop := exists e c, 0 <= e <= 64 /\ PMSP.ec_at RSEGS M (fb + 16) e c.
(* [comment removed for export] *)
Lemma bb_room_keep (s s' : PNM.bpst) sm sm' :
  PNM.b_bb s' = PNM.b_bb s -> PM.unread (PNM.b_src s') sm' <= PM.unread (PNM.b_src s) sm -> PNR.bb_room s sm -> PNR.bb_room s' sm'.
Proof. unfold PNR.bb_room. intros E LE H. rewrite E. exact (PGV8.v8_room_mono _ _ _ LE H). Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KH := PNBKS.kh_S L HI LY HIok.
Let KL := PMKS.klayout_S L LY.
Abbreviation brel := (PNBK.brel RSEGS AD AN L HI 10).
Abbreviation pot := (PNR.pot_bparser L).

Hypothesis BD : PNRS.begin_document_spec L HI.
Hypothesis REN : PNRS.read_e_name_spec L HI.
Hypothesis RV : PNRS.read_value_spec L HI.
Hypothesis ED : PNRS.end_document_spec L HI.
Hypothesis EA : PNRS.end_array_spec L HI.
Hypothesis SRD : PNRS.src_read_spec L HI.
Hypothesis MKE : PNRS.make_ec_spec L HI.

Definition lp_kont (K : list event -> Prop) (LBX : list (Z * Z)) (sp r fb : Z) (str : PM.vstr) (R : bvmap 5 word)
           (M : mem) (model : Model) (cr : credit) (s : PNM.bpst) (sm : PM.strm) (ax : PNST.bax) : Prop :=
  forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (s' : PNM.bpst) (sm' : PM.strm) (ax' : PNST.bax) (cr' : credit),
      regs_preserved R R' ->
      PNR.parse_post RSEGS AD AN M' fb s s' str sm sm' ax ax' ->
      L5C.hpres L LBX sp (PMSP.pm_scr 10) (PNR.W_brun AD AN fb) M M' ->
      PMSP.credit_keep cr cr' (pot s) PMSP.cr0 ->
      model_but_vm model model' -> hi_heap HI (PNM.bparser_own s' ++ LBX) cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.
Definition lp_ctx (K : list event -> Prop) (LBX : list (Z * Z)) (sp r fb : Z) (str : PM.vstr) (R : bvmap 5 word) (cr : credit) (s : PNM.bpst) (sm : PM.strm) : Prop :=
  K [] /\ PMSP.frame_ok AD L sp fb /\ incl (PM.vs_own str) LBX /\ L5.ra_ok r
  /\ getr R (PMK.reg 2) = Z_to_bv 64 sp /\ getr R (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) /\ getr R (PMK.reg 4) = Z_to_bv 64 (pa_tp AD)
  /\ PMSP.credit_le (pot s) cr /\ PM.unread (PNM.b_src s) sm < 2 ^ 26.
(* [comment removed for export] *)
Definition lp_linv (LBX : list (Z * Z)) (sp r fb : Z) (str : PM.vstr) (E0 : PNBK.bent) (R R1 : bvmap 5 word)
           (M1 : mem) (model1 : Model) (cr1 : credit) (s1 : PNM.bpst) (sm1 : PM.strm) (ax1 : PNST.bax) : Prop :=
  brel LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) /\ lp_regs R R1 sp fb /\ lp_saved R M1 sp r /\ ec_some M1 fb /\ PNR.binv s1
  /\ (PNM.b_more s1 = 1 -> PNR.bb_room s1 sm1).

Lemma pot_nonneg (M1 : mem) fb s1 : bparser_at M1 (fb + 40) (fb + 472) s1 -> PNM.bgrow_ok s1 -> 0 <= fst (pot s1) /\ 0 <= snd (pot s1).
Proof.
  intros PA (G1 & G2 & G3). pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & NB & TB & STK & _).
  pose proof STK as (_ & _ & _ & Hk & _).
  pose proof (PNBK.pot_bstack_nonneg RSEGS AD AN L HI KH (PNM.b_sk s1) Hk) as (A1 & A2).
  pose proof (PNBK.pot_text_nonneg RSEGS AD AN L HI KH M1 _ _ _ TB G2) as (B1 & B2).
  pose proof (PNBK.pot_text_nonneg RSEGS AD AN L HI KH M1 _ _ _ NB G1) as (C1 & C2).
  pose proof (PNBK.pot_v8_nonneg RSEGS AD AN L HI KH M1 _ _ _ BB G3) as (D1 & D2).
  unfold PNR.pot_bparser, PM.credit_add. cbn [fst snd]. lia.
Qed.

(* [comment removed for export] *)
Lemma lp_fin K LBX sp r fb str (R : bvmap 5 word) (M : mem) model cr s sm ax
      (fx5 : FPState) R5 (M5 : mem) model5 cr5 s5 sm5 ax5 :
  lp_ctx K LBX sp r fb str R cr s sm -> lp_kont K LBX sp r fb str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M5 model5 cr5 s5 sm5 ax5) -> ec_some M5 fb ->
  getr R5 (PMK.reg 1) = Z_to_bv 64 r -> getr R5 (PMK.reg 2) = Z_to_bv 64 sp ->
  getr R5 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R5 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R5 (PMK.reg 8) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 8))) -> getr R5 (PMK.reg 9) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 9))) ->
  getr R5 (PMK.reg 18) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 18))) -> getr R5 (PMK.reg 19) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 19))) ->
  getr R5 (PMK.reg 20) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 20))) -> getr R5 (PMK.reg 21) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 21))) ->
  getr R5 (PMK.reg 22) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 22))) -> getr R5 (PMK.reg 23) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 23))) ->
  getr R5 (PMK.reg 24) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 24))) -> getr R5 (PMK.reg 25) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 25))) ->
  (forall k, In k [26; 27]%nat -> getr R5 (PMK.reg k) = getr R (PMK.reg k)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0x36e54 M5 model5) K.
Proof.
  intros (K0 & FOK & INCS & (Hr1 & Hr2) & Rsp & Rgp & Rtp & CRED & UNR0) KONT BR (e5 & c5 & He5 & EC5) Y1 Y2 Y3 Y4 Y8 Y9 Y18 Y19 Y20 Y21 Y22 Y23 Y24 Y25 YK.
  pose proof BR as (RP & STEP & AXL & HP & CK & MB & HH & STK & MOK). cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax] in *.
  pose proof MOK as (Mh & Ml & Mm).
  eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
  { apply (PMK.ret_to RSEGS fx5 R5 M5 0x36e54 W_36158 r F_36158 eq_refl D_36158); [exact Y1| lia| exact Hr2]. }
  apply (KONT fx5 R5 M5 model5 s5 sm5 ax5 cr5).
  - apply PMK.preserved_by_index. intros k Hk. cbn in Hk.
    destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
      first [ rewrite Y2, Rsp; reflexivity | rewrite Y3, Rgp; reflexivity | rewrite Y4, Rtp; reflexivity
            | rewrite Y8; apply Z_to_bv_bv_unsigned | rewrite Y9; apply Z_to_bv_bv_unsigned | rewrite Y18; apply Z_to_bv_bv_unsigned
            | rewrite Y19; apply Z_to_bv_bv_unsigned | rewrite Y20; apply Z_to_bv_bv_unsigned | rewrite Y21; apply Z_to_bv_bv_unsigned
            | rewrite Y22; apply Z_to_bv_bv_unsigned | rewrite Y23; apply Z_to_bv_bv_unsigned | rewrite Y24; apply Z_to_bv_bv_unsigned
            | rewrite Y25; apply Z_to_bv_bv_unsigned | apply YK; cbn; tauto ].
  - unfold PNR.parse_post. split; [exact RP|]. split; [exact STEP|]. split; [exact AXL|].
    unfold PNR.o_ec, PMSP.o_ec. cbn [pa_off_ec AD PnLayoutS_u.ADDR_S]. destruct EC5 as (_ & _ & D). exact D.
  - exact HP.
  - destruct RP as (PA5 & _ & _ & _ & _ & _ & GR5). unfold PNR.o_p, PNR.o_is, PMSP.o_p, PMSP.o_is in PA5. cbn [pa_off_p pa_off_is AD PnLayoutS_u.ADDR_S] in PA5.
    pose proof (pot_nonneg M5 fb s5 PA5 GR5) as (P1 & P2). unfold PMSP.credit_keep, PMSP.cr0 in *. cbn [fst snd] in *. lia.
  - exact MB.
  - exact HH.
Qed.

(* [comment removed for export] *)
Lemma lp_top LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 :
  brel LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) -> PNR.binv s1 ->
  exists l c, PNM.b_stk s1 = l ++ [c] /\ PNM.bstate_ok c /\ PNR.bstack_shape (l ++ [c])
    /\ L5.u64_at RSEGS M1 (fb + 40 + 400) (PNM.b_sb s1 + 40 * Z.of_nat (length l) + 40)
    /\ PNM.bstate_at RSEGS M1 (PNM.b_sb s1 + 40 * Z.of_nat (length l)) c
    /\ L5.writable RSEGS M1 (PNM.b_sb s1 + 40 * Z.of_nat (length l)) 40
    /\ L5.defined M1 (PNM.b_sb s1) (40 * 2 ^ PNM.b_sk s1)
    /\ 4096 <= PNM.b_sb s1 /\ PNM.b_sb s1 + 40 * Z.of_nat (length l) + 40 <= PNM.b_sb s1 + 40 * 2 ^ PNM.b_sk s1
    /\ PNM.b_sb s1 + 40 * 2 ^ PNM.b_sk s1 <= hl_sptop L - 2 ^ 23
    /\ (PNM.b_sb s1 + 40 * Z.of_nat (length l) + 40) mod 8 = 0 /\ Z.of_nat (length l) + 1 <= 1025.
Proof.
  intros BR INV.
  destruct (PNBK2.brel_blocks RSEGS AD AN L HI KH 10 LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR) as (BRG & OWNB & APQ).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 10 LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR) as (PA1 & IA1 & GR1 & UN1 & STK & MOK).
  change (PMSP.pm_scr 10) with 32768 in STK. pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof INV as (_ & SH). pose proof SH as (L1 & L2 & _ & _ & OKs). unfold PNM.MAX_DEPTH in L2.
  destruct (exists_last (l := PNM.b_stk s1) ltac:(intros X; rewrite X in L1; cbn in L1; lia)) as (l & c & ES).
  exists l, c. split; [exact ES|].
  pose proof (OKs (length l) ltac:(rewrite ES, length_app; cbn; lia)) as OKc. rewrite ES, nth_middle in OKc. split; [exact OKc|].
  rewrite ES in SH. split; [exact SH|].
  pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SV1 & _). unfold PNM.OFF_STK in SV1.
  pose proof SV1 as (V0 & V8 & _ & Hk & Hlen & Hal & DB & _ & _ & EL). unfold PNM.BSZ in *.
  rewrite ES, length_app in Hlen, EL, V8, L2. cbn [length] in Hlen, EL, V8, L2.
  set (b := PNM.b_sb s1) in *. set (k := PNM.b_sk s1) in *. set (n := Z.of_nat (length l)) in *.
  assert (Hn : 0 <= n /\ n + 1 <= 2 ^ k) by (unfold n; lia).
  assert (TOPIN : b + 40 * n + 40 <= b + 40 * 2 ^ k) by nia.
  assert (Bs : In (b, 40 * 2 ^ k) (PNM.bparser_own s1)).
  { unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own, b, k. apply in_or_app. right. cbn. auto. }
  destruct (OWNB _ _ Bs) as (S0 & S4). unfold hl_ceil in S4.
  split; [replace (b + 40 * n + 40) with (b + 40 * Z.of_nat (length l + 1)) by (unfold n; lia); replace (fb + 40 + 400) with (fb + 40 + 392 + 8) by lia; exact V8|].
  pose proof (EL (length l) ltac:(lia)) as Ec. rewrite nth_middle in Ec. fold n in Ec. split; [exact Ec|].
  split; [apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M1 b (40 * 2 ^ k)); [exact DB|lia|lia]|lia|lia]|].
  split; [exact DB|]. split; [lia|]. split; [exact TOPIN|]. split; [lia|].
  split; [replace (b + 40 * n + 40) with (b + 8 * (5 * n + 5)) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact Hal| unfold n; lia].
Qed.

Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac fd P := PMK.feed P ltac:(first [PMK.sc | unfold PNSPAP.aligned; PMK.sc]).


Definition lp_IH (K : list event -> Prop) (LBX : list (Z * Z)) (sp r fb : Z) (str : PM.vstr) (R : bvmap 5 word)
           (M : mem) (model : Model) (cr : credit) (s : PNM.bpst) (sm : PM.strm) (ax : PNST.bax) (n : Z) : Prop :=
  forall (fx1 : FPState) R1 (M1 : mem) model1 cr1 s1 sm1 ax1,
    lp_linv LBX sp r fb str (BENT M model cr s sm ax) R R1 M1 model1 cr1 s1 sm1 ax1 ->
    (PNM.b_more s1 = 1 -> 0 <= PNR.bmu s1 sm1 < n) -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x36c58 M1 model1) K.

Local Ltac lpregs KS XK :=
  unfold lp_regs; repeat lazymatch goal with
  | |- _ /\ _ => split
  | |- getr _ (PMK.reg _) = _ => PMK.rk
  | |- forall k, In k _ -> _ => intros k Hk; rewrite (KS k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto); apply XK; exact Hk
  end.

(* [comment removed for export] *)
Lemma lp_X K LBX sp r fb str (R : bvmap 5 word) (M : mem) model cr s sm ax (n : Z)
      (fx2 : FPState) R2 (M2 : mem) model2 cr2 s2 sm2 ax2 :
  lp_ctx K LBX sp r fb str R cr s sm -> lp_kont K LBX sp r fb str R M model cr s sm ax -> lp_IH K LBX sp r fb str R M model cr s sm ax n ->
  lp_linv LBX sp r fb str (BENT M model cr s sm ax) R R2 M2 model2 cr2 s2 sm2 ax2 ->
  (PNM.b_more s2 = 1 -> 0 <= PNR.bmu s2 sm2 < n) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0x36e08 M2 model2) K.
Proof.
  intros CTX KONT IH LI MU. pose proof CTX as (K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & UNR0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct LI as (BR2 & RG2 & SV2 & ECS2 & INVm & BBRm).
  pose proof RG2 as (X2 & X3 & X4 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & XK).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 10 LBX sp fb str _ M2 model2 cr2 s2 sm2 ax2 BR2) as (PA2 & _ & _ & _ & STK2 & MOK2).
  change (PMSP.pm_scr 10) with 32768 in STK2. pose proof STK2 as (A16 & SLO & SHI & STOP & SDEF2). pose proof MOK2 as (Mh2 & Ml2 & Mm2).
  pose proof (L5C.stk_floor _ M2 sp 32768 STK2) as SFL. pose proof (L5C.stk_writable RSEGS _ M2 sp 32768 STK2) as WR2.
  assert (AL40 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
  pose proof PA2 as (_ & _ & _ & _ & DN2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D01). destruct D01 as [D0|D1]; rewrite ?D0, ?D1 in DN2.
  - (* [comment removed for export] *)
    LeanFeed.pfeed P (PNSPAP.bpaX0_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSPAP.aligned; PMK.sc]).
    destruct P as (fx3 & R3 & M3 & MG3 & EQ3w & EQ3 & MS3 & KS3 & Y10). assert (EM3 : M3 = M2) by (apply functional_extensionality; exact EQ3w). subst M3.
    apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 10 LBX sp fb str _ M2 model2 cr2 s2 sm2 ax2 fx2 fx3 R2 R3 0x36e08 0x36c58 M2 (fun _ => False) K
             ltac:(lia) BR2 FOK INCS MS3 MG3 ltac:(intros a Ha _; reflexivity) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
    intros BR3. apply (IH fx3 R3 M2 model2 cr2 s2 sm2 ax2); [| exact MU].
    split; [exact BR3|]. split; [lpregs KS3 XK|]. split; [exact SV2|]. split; [exact ECS2|]. split; [exact INVm| exact BBRm].
  - (* [comment removed for export] *)
    pose proof SV2 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88).
    pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 8))) as BU8. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 9))) as BU9.
    pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 18))) as BU18. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 19))) as BU19.
    pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 20))) as BU20. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 21))) as BU21.
    pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 22))) as BU22. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 23))) as BU23.
    pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 24))) as BU24. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 25))) as BU25.
    LeanFeed.pfeed P (PNSPAP.bpaX1_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 50%nat => r
                 | 51%nat => bv_unsigned (getr R (PMK.reg 8)) | 52%nat => bv_unsigned (getr R (PMK.reg 9)) | 53%nat => bv_unsigned (getr R (PMK.reg 18))
                 | 54%nat => bv_unsigned (getr R (PMK.reg 19)) | 55%nat => bv_unsigned (getr R (PMK.reg 20)) | 56%nat => bv_unsigned (getr R (PMK.reg 21))
                 | 57%nat => bv_unsigned (getr R (PMK.reg 22)) | 58%nat => bv_unsigned (getr R (PMK.reg 23)) | 59%nat => bv_unsigned (getr R (PMK.reg 24))
                 | 60%nat => bv_unsigned (getr R (PMK.reg 25)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSPAP.aligned; PMK.sc]).
    pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP;
                  destruct pvzP as (MG3 & EQ3w & EQ3 & MS3 & KS3 & Y1 & Y2 & Y8 & Y9 & Y10 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25)); PMK.pvz_clrT.
    assert (EM3 : M3 = M2) by (apply functional_extensionality; exact EQ3w). subst M3.
    apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 10 LBX sp fb str _ M2 model2 cr2 s2 sm2 ax2 fx2 fx3 R2 R3 0x36e08 0x36e54 M2 (fun _ => False) K
             ltac:(lia) BR2 FOK INCS MS3 MG3 ltac:(intros a Ha _; reflexivity) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
    intros BR3.
    apply (lp_fin K LBX sp r fb str R M model cr s sm ax fx3 R3 M2 model2 cr2 s2 sm2 ax2 CTX KONT BR3 ECS2 Y1 Y2);
      [PMK.rk| PMK.rk| exact Y8| exact Y9| exact Y18| exact Y19| exact Y20| exact Y21| exact Y22| exact Y23| exact Y24| exact Y25|].
    intros k Hk. rewrite (KS3 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). apply XK. exact Hk.
Qed.

(* [comment removed for export] *)
Lemma lp_headfacts K LBX sp r fb str (R : bvmap 5 word) (M : mem) model cr s sm ax (fx1 : FPState) R1 (M1 : mem) model1 cr1 s1 sm1 ax1 :
  lp_ctx K LBX sp r fb str R cr s sm -> lp_linv LBX sp r fb str (BENT M model cr s sm ax) R R1 M1 model1 cr1 s1 sm1 ax1 ->
  bparser_at M1 (fb + 40) (fb + 472) s1 /\ L5C.stk (hl_sptop L) M1 sp 32768 /\ PMSP.model_ok model1
  /\ PM.unread (PNM.b_src s1) sm1 <= PM.unread (PNM.b_src s) sm /\ 0 <= PM.unread (PNM.b_src s1) sm1
  /\ L5.u64_at RSEGS M1 (fb + 464) (pa_vp_visitor AD) /\ L5.img_clear M1 65536 (pa_rw_lo AD) /\ L5.writable RSEGS M1 (fb + 40) 416
  /\ (fb + 40) mod 8 = 0 /\ (fb + 464) mod 8 = 0.
Proof.
  intros (K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & UNR0) (BR1 & _).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2.
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 10 LBX sp fb str _ M1 model1 cr1 s1 sm1 ax1 BR1) as (PA1 & _ & _ & UN1 & STK1 & MOK1).
  change (PMSP.pm_scr 10) with 32768 in STK1. pose proof STK1 as (A16 & SLO & SHI & STOP & SDEF).
  pose proof BR1 as ((PA1' & _ & VIS1 & _ & BASE1 & _) & STEP & _). cbn [PNBK.be_M PNBK.be_s PNBK.be_sm] in VIS1, BASE1, STEP.
  unfold PNR.o_v, PMSP.o_v, PMSP.visitor_at in VIS1. cbn [pa_off_v AD PnLayoutS_u.ADDR_S] in VIS1.
  split; [exact PA1|]. split; [exact STK1|]. split; [exact MOK1|].
  split; [destruct STEP as (_ & _ & _ & _ & LE); exact LE|]. split; [exact UN1|].
  split; [exact VIS1|]. split; [destruct BASE1 as (IMG & _); exact IMG|].
  split; [destruct PA1 as (_ & D & _); apply (L5C.writable_of_defined RSEGS); [exact D|lia|lia]|].
  split; [replace (fb + 40) with (fb + 8 * 5) by lia| replace (fb + 464) with (fb + 8 * 58) by lia]; apply PMPK.m8_add; apply PMPK.m16_8; exact F3.
Qed.

(* [comment removed for export] *)
Lemma lp_mode4 K LBX sp r fb str (R : bvmap 5 word) (M : mem) model cr s sm ax (fx1 : FPState) R1 (M1 : mem) model1 cr1 s1 sm1 ax1 l c :
  lp_ctx K LBX sp r fb str R cr s sm -> lp_kont K LBX sp r fb str R M model cr s sm ax -> lp_IH K LBX sp r fb str R M model cr s sm ax (PNR.bmu s1 sm1) ->
  lp_linv LBX sp r fb str (BENT M model cr s sm ax) R R1 M1 model1 cr1 s1 sm1 ax1 -> PNM.b_more s1 = 1 ->
  PNM.b_stk s1 = l ++ [c] -> PNM.bs_mode c = 4 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x36c58 M1 model1) K.
Proof.
  intros CTX KONT IH LI MO1 ES Hm. pose proof CTX as (K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & UNR0).
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2. pose proof RAok as (Hr1 & Hr2).
  destruct (lp_headfacts K LBX sp r fb str R M model cr s sm ax fx1 R1 M1 model1 cr1 s1 sm1 ax1 CTX LI) as (PA1 & STK1 & MOK1 & LE1 & UN1 & VIS1 & IMG1 & WP1 & AL40 & AL464).
  pose proof STK1 as (A16 & SLO & SHI & STOP & SDEF1). pose proof MOK1 as (Mh1 & Ml1 & Mm1). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG1.
  pose proof (L5C.stk_floor _ M1 sp 32768 STK1) as SFL. pose proof (L5C.stk_writable RSEGS _ M1 sp 32768 STK1) as WR1.
  destruct LI as (BR1 & RG1 & SV1 & (e1 & c1 & He1 & EC1) & INV1 & BBR1).
  pose proof RG1 as (X2 & X3 & X4 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & XK).
  pose proof PA1 as (_ & _ & _ & MO1' & _). rewrite MO1 in MO1'.
  destruct (lp_top LBX sp fb str _ M1 model1 cr1 s1 sm1 ax1 BR1 INV1) as (l_ & c_ & ES_ & OKc & SH & VE & TOPC & WT & DB & Hb & TOPIN & S4 & EAL & Hn).
  rewrite ES in ES_. apply app_inj_tail in ES_. destruct ES_ as (<- & <-).
  set (b := PNM.b_sb s1) in *. set (n := Z.of_nat (length l)) in *.
  pose proof OKc as (OKm & OKl & OKp & OKt & OKi). destruct TOPC as (Tm & Tl & Tp & Tt & Ti). rewrite Hm in Tm.
  pose proof (shape_cont_cons l c SH ltac:(rewrite Hm; unfold PNR.bmode_cont; lia)) as NNIL.
  unfold PNRS.read_value_spec, PNR.read_value_spec in RV.
  LeanFeed.pfeed P (PNSPAP.bpaH4_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16
               | 44%nat => PNM.bs_type c | 45%nat => b + 40 * n + 40 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSPAP.aligned; PMK.sc]).
  pvz_hg ltac:(idtac; destruct P as (fx2 & R2 & M2 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG2 & _ & FRZ2 & MS2 & KS2 & Y1 & Y10 & Y11 & Y12 & Y13 & MD2)); PMK.pvz_clrT.
  set (c2 := PNM.BS 2 (PNM.bs_len c) (PNM.bs_pos c) (PNM.bs_type c) (PNM.bs_idx c)).
  apply (PNBK2.brel_piece_stk RSEGS AD AN L HI KH 10 LBX sp fb str _ M1 model1 cr1 s1 sm1 ax1 fx1 fx2 R1 R2 0x36c58 0x375ec M2
           (fun a => b + 40 * n + 40 - 40 <= a < b + 40 * n + 40 - 40 + 4) l [c] [c2] K ltac:(lia) BR1 FOK INCS MS2 MG2 FRZ2 ltac:(intros a; apply PMK.rng_dec) ES); fold b.
  { intros a Pa. cbn beta in Pa. right. right. clear -Pa Hn TOPIN. unfold n in *. lia. }
  { rewrite length_app. cbn [length]. apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply FRZ2; lia|lia|lia|].
    replace (b + 40 * Z.of_nat (length l + 1)) with (b + 40 * n + 40) by (unfold n; lia). replace (fb + 440) with (fb + 40 + 400) by lia. exact VE. }
  { intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia]. cbn [nth]. rewrite Nat.add_0_r. fold n.
    unfold PNM.bstate_at. cbn [c2 PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx].
    assert (AG : forall a m, b + 40 * n + 4 <= a -> a + m <= b + 40 * n + 40 -> L5C.agree_on M1 M2 a m) by (intros a m G1 G2 j Gj; apply FRZ2; lia).
    split; [replace (b + 40 * n) with (b + 40 * n + 40 - 40) by lia; exact MD2|].
    split; [apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG; lia|lia|lia| exact Tl]|].
    split; [apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG; lia|lia|lia| exact Tp]|].
    split; [apply (L5C.u8_at_agree RSEGS M1 M2); [apply AG; lia|lia|lia| exact Tt]|].
    apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG; lia|lia|lia| exact Ti]. }
  { rewrite length_app. cbn [length]. unfold n in Hn, TOPIN |- *. clear -Hn TOPIN. nia. }
  intros BR2.
  assert (AG12 : forall a m, sp - 112 <= a -> a + m <= 2 ^ 64 -> L5C.agree_on M1 M2 a m) by (intros a m G1 G2 j Gj; apply FRZ2; lia).
  assert (INV2 : PNR.binv (PNBO.set_stk s1 (l ++ [c2]))).
  { split; [destruct INV1 as (ID & _); exact ID|]. cbn [PNBO.set_stk PNM.b_stk]. apply (shape_top_mode l c c2 SH); [unfold PNM.bstate_ok; cbn; lia| intros E; destruct (NNIL E)| intros _; cbn; unfold PNR.bmode_cont; lia]. }
  apply (PNBK2.brel_call RSEGS AD AN L HI KH true _ 8 (PNR.bargs_rv AD) PNR.bprog_value 10 LBX sp fb str _ M2 model1 cr1 _ sm1 ax1 fx2 R2 (sp - 112) 0x36da4 c1 e1 K
           RV ltac:(lia) ltac:(lia) K0 BR2 FOK INCS CRED Y1 ltac:(split; [lia| reflexivity]) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(lia) ltac:(unfold PMSP.pm_scr; lia) (mod16_sub112 sp A16)).
  { unfold PNR.bargs_rv, PNR.o_p, PNR.o_ec, PNR.o_v, PMSP.o_p, PMSP.o_ec, PMSP.o_v. cbn [pa_off_p pa_off_ec pa_off_v AD PnLayoutS_u.ADDR_S].
    rewrite L5K.rl10, L5K.rl11, L5K.rl12, L5K.rl13. split; [exact Y10|]. split; [exact Y11|]. split; [exact Y13|]. split; [exists (PNM.bs_type c); split; [lia| exact Y12]| exact (BBR1 MO1)]. }
  { exact INV2. }
  { apply (ec_agree M1 M2); [apply AG12; lia|lia|lia| exact EC1]. }
  { exact He1. }
  { cbn [PNBO.set_stk PNM.b_src]. lia. }
  intros fx3 R3 M3 model3 s3 sm3 ax3 cr3 RP23 POST BR3 AG23.
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 10 LBX sp fb str _ M3 model3 cr3 s3 sm3 ax3 BR3) as (_ & _ & _ & UN3 & STK3 & MOK3).
  change (PMSP.pm_scr 10) with 32768 in STK3. pose proof (L5C.stk_writable RSEGS _ M3 sp 32768 STK3) as WR3. pose proof MOK3 as (Mh3 & Ml3 & _).
  LeanFeed.pfeed P (PNSPAP.bpaJ2c_conc fx3 R3 M3 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSPAP.aligned; PMK.sc]).
  destruct P as (fx4 & R4 & M4 & MG4 & EQ4w & EQ4 & MS4 & KS4). assert (EM4 : M4 = M3) by (apply functional_extensionality; exact EQ4w). subst M4.
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 10 LBX sp fb str _ M3 model3 cr3 s3 sm3 ax3 fx3 fx4 R3 R4 0x36da4 0x36e08 M3 (fun _ => False) K
           ltac:(lia) BR3 FOK INCS MS4 MG4 ltac:(intros a Ha _; reflexivity) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
  intros BR4.
  apply (lp_X K LBX sp r fb str R M model cr s sm ax (PNR.bmu s1 sm1) fx4 R4 M3 model3 cr3 s3 sm3 ax3 CTX KONT IH).
  - split; [exact BR4|].
    split; [apply (lp_regs_pres R R2 R4 sp fb); [lpregs KS2 XK| apply (PMK.regs_preserved_trans R2 R3 R4 RP23); apply PMK.preserved_by_index; intros k Hk; apply KS4; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto]|].
    split; [apply (lp_saved_agree R M1 M3 sp r); [intros a m G1 G2 j Gj; rewrite (AG23 a m ltac:(lia) ltac:(lia) j Gj); apply FRZ2; lia|lia|lia| exact SV1]|].
    destruct POST as (_ & _ & _ & [(v & Hv & Ev & MOv & _ & _ & INV3)|(Ee & INV3 & _)] & BBP); unfold PNR.o_ec, PMSP.o_ec in *; cbn [pa_off_ec AD PnLayoutS_u.ADDR_S] in *.
    + split; [exists v, (pa_errcat_obj AD); split; [lia| exact Ev]|]. split; [exact INV3| intros MO3; exact (BBP (BBR1 MO1) MO3)].
    + split; [exists e1, c1; split; [exact He1| exact Ee]|]. split; [exact INV3| intros MO3; exact (BBP (BBR1 MO1) MO3)].
  - intros MO3. destruct POST as (_ & STEP23 & _ & [(v & Hv & Ev & MOv & _)|(Ee & INV3 & PROG)] & _); [rewrite MOv in MO3; discriminate|].
    cbn [PNBO.set_stk PNM.b_src PNM.b_stk] in STEP23, PROG. destruct STEP23 as (_ & _ & _ & _ & LE23).
    unfold PNR.bmu. rewrite ES, bflag_app, Hm. cbn [Z.eqb Pos.eqb orb].
    pose proof (bflag_range (PNM.b_stk s3)) as FR.
    destruct PROG as [(l3 & c3 & c3' & G1 & G2 & _ & Gm & _)|(cn & G2 & _ & Gc & _ & LT)].
    + cbn [PNBO.set_stk PNM.b_src PNM.b_stk] in G1. apply app_inj_tail in G1. destruct G1 as (<- & <-). rewrite G2, bflag_app, Gm. cbn [c2 PNM.bs_mode Z.eqb Pos.eqb orb]. lia.
    + cbn [PNBO.set_stk PNM.b_src PNM.b_stk] in LT. lia.
Qed.


Local Ltac head_intro CTX LI :=
  pose proof CTX as (K0 & FOK & INCS & RAok & Rsp & Rgp & Rtp & CRED & UNR0);
  pose proof FOK as (F1 & F2 & F3); cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2; pose proof RAok as (Hr1 & Hr2).

(* [comment removed for export] *)
Lemma lp_mode0 K LBX sp r fb str (R : bvmap 5 word) (M : mem) model cr s sm ax (fx1 : FPState) R1 (M1 : mem) model1 cr1 s1 sm1 ax1 l c :
  lp_ctx K LBX sp r fb str R cr s sm -> lp_kont K LBX sp r fb str R M model cr s sm ax -> lp_IH K LBX sp r fb str R M model cr s sm ax (PNR.bmu s1 sm1) ->
  lp_linv LBX sp r fb str (BENT M model cr s sm ax) R R1 M1 model1 cr1 s1 sm1 ax1 -> PNM.b_more s1 = 1 ->
  PNM.b_stk s1 = l ++ [c] -> PNM.bs_mode c = 0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x36c58 M1 model1) K.
Proof.
  intros CTX KONT IH LI MO1 ES Hm. head_intro CTX LI.
  destruct (lp_headfacts K LBX sp r fb str R M model cr s sm ax fx1 R1 M1 model1 cr1 s1 sm1 ax1 CTX LI) as (PA1 & STK1 & MOK1 & LE1 & UN1 & VIS1 & IMG1 & WP1 & AL40 & AL464).
  pose proof STK1 as (A16 & SLO & SHI & STOP & SDEF1). pose proof MOK1 as (Mh1 & Ml1 & Mm1). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG1.
  pose proof (L5C.stk_floor _ M1 sp 32768 STK1) as SFL. pose proof (L5C.stk_writable RSEGS _ M1 sp 32768 STK1) as WR1.
  destruct LI as (BR1 & RG1 & SV1 & (e1 & c1 & He1 & EC1) & INV1 & BBR1).
  pose proof RG1 as (X2 & X3 & X4 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & XK).
  pose proof PA1 as (_ & _ & _ & MO1' & _). rewrite MO1 in MO1'.
  destruct (lp_top LBX sp fb str _ M1 model1 cr1 s1 sm1 ax1 BR1 INV1) as (l_ & c_ & ES_ & OKc & SH & VE & TOPC & WT & DB & Hb & TOPIN & S4 & EAL & Hn).
  rewrite ES in ES_. apply app_inj_tail in ES_. destruct ES_ as (<- & <-).
  pose proof (shape_bottom_nil l c SH ltac:(rewrite Hm; unfold PNR.bmode_bottom; lia)) as NIL.
  set (b := PNM.b_sb s1) in *. set (n := Z.of_nat (length l)) in *. assert (Hn0 : n = 0) by (unfold n; rewrite NIL; reflexivity).
  pose proof OKc as (OKm & OKl & OKp & OKt & OKi). destruct TOPC as (Tm & Tl & Tp & Tt & Ti). rewrite Hm in Tm.
  unfold PNRS.begin_document_spec, PNR.begin_document_spec in BD.
  LeanFeed.pfeed P (PNSPAP.bpaH0_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16
               | 45%nat => b + 40 * n + 40 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSPAP.aligned; PMK.sc]).
  pvz_hg ltac:(idtac; destruct P as (fx2 & R2 & M2 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG2 & _ & FRZ2 & MS2 & KS2 & Y1 & Y10 & Y11 & Y12 & MD2)); PMK.pvz_clrT.
  set (c2 := PNM.BS 1 (PNM.bs_len c) (PNM.bs_pos c) (PNM.bs_type c) (PNM.bs_idx c)).
  apply (PNBK2.brel_piece_stk RSEGS AD AN L HI KH 10 LBX sp fb str _ M1 model1 cr1 s1 sm1 ax1 fx1 fx2 R1 R2 0x36c58 0x36f7c M2
           (fun a => b + 40 * n + 40 - 40 <= a < b + 40 * n + 40 - 40 + 4) l [c] [c2] K ltac:(lia) BR1 FOK INCS MS2 MG2 FRZ2 ltac:(intros a; apply PMK.rng_dec) ES); fold b n.
  { intros a Pa. cbn beta in Pa. right. right. clear -Pa TOPIN Hn0. lia. }
  { rewrite length_app. cbn [length]. apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply FRZ2; lia|lia|lia|].
    replace (b + 40 * Z.of_nat (length l + 1)) with (b + 40 * n + 40) by (unfold n; lia). replace (fb + 440) with (fb + 40 + 400) by lia. exact VE. }
  { intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia]. cbn [nth]. rewrite Nat.add_0_r. fold n.
    unfold PNM.bstate_at. cbn [c2 PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx].
    assert (AG : forall a m, b + 40 * n + 4 <= a -> a + m <= b + 40 * n + 40 -> L5C.agree_on M1 M2 a m) by (intros a m G1 G2 j Gj; apply FRZ2; lia).
    split; [replace (b + 40 * n) with (b + 40 * n + 40 - 40) by lia; exact MD2|].
    split; [apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG; lia|lia|lia| exact Tl]|].
    split; [apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG; lia|lia|lia| exact Tp]|].
    split; [apply (L5C.u8_at_agree RSEGS M1 M2); [apply AG; lia|lia|lia| exact Tt]|].
    apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG; lia|lia|lia| exact Ti]. }
  { rewrite length_app. cbn [length]. unfold n in TOPIN |- *. clear -TOPIN. nia. }
  intros BR2.
  assert (AG12 : forall a m, sp - 112 <= a -> a + m <= 2 ^ 64 -> L5C.agree_on M1 M2 a m) by (intros a m G1 G2 j Gj; apply FRZ2; lia).
  assert (INV2 : PNR.binv (PNBO.set_stk s1 (l ++ [c2]))).
  { split; [destruct INV1 as (ID & _); exact ID|]. cbn [PNBO.set_stk PNM.b_stk]. apply (shape_top_mode l c c2 SH); [unfold PNM.bstate_ok; cbn; lia| intros _; cbn; unfold PNR.bmode_bottom; lia| intros E; destruct (E NIL)]. }
  apply (PNBK2.brel_call RSEGS AD AN L HI KH false _ 7 (PNR.bargs3 AD) PNR.bprog_value 10 LBX sp fb str _ M2 model1 cr1 _ sm1 ax1 fx2 R2 (sp - 112) 0x36cb0 c1 e1 K
           BD ltac:(lia) ltac:(lia) K0 BR2 FOK INCS CRED Y1 ltac:(split; [lia| reflexivity]) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(lia) ltac:(unfold PMSP.pm_scr; lia) (mod16_sub112 sp A16)).
  { unfold PNR.bargs3, PNR.o_p, PNR.o_ec, PNR.o_v, PMSP.o_p, PMSP.o_ec, PMSP.o_v. cbn [pa_off_p pa_off_ec pa_off_v AD PnLayoutS_u.ADDR_S].
    rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact Y10|]. split; [exact Y11| exact Y12]. }
  { exact INV2. }
  { apply (ec_agree M1 M2); [apply AG12; lia|lia|lia| exact EC1]. }
  { exact He1. }
  { cbn [PNBO.set_stk PNM.b_src]. lia. }
  intros fx3 R3 M3 model3 s3 sm3 ax3 cr3 RP23 POST BR3 AG23.
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 10 LBX sp fb str _ M3 model3 cr3 s3 sm3 ax3 BR3) as (_ & _ & _ & UN3 & STK3 & MOK3).
  change (PMSP.pm_scr 10) with 32768 in STK3. pose proof (L5C.stk_writable RSEGS _ M3 sp 32768 STK3) as WR3. pose proof MOK3 as (Mh3 & Ml3 & _).
  LeanFeed.pfeed P (PNSPAP.bpaJ74_conc fx3 R3 M3 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSPAP.aligned; PMK.sc]).
  destruct P as (fx4 & R4 & M4 & MG4 & EQ4w & EQ4 & MS4 & KS4). assert (EM4 : M4 = M3) by (apply functional_extensionality; exact EQ4w). subst M4.
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 10 LBX sp fb str _ M3 model3 cr3 s3 sm3 ax3 fx3 fx4 R3 R4 0x36cb0 0x36e08 M3 (fun _ => False) K
           ltac:(lia) BR3 FOK INCS MS4 MG4 ltac:(intros a Ha _; reflexivity) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
  intros BR4.
  apply (lp_X K LBX sp r fb str R M model cr s sm ax (PNR.bmu s1 sm1) fx4 R4 M3 model3 cr3 s3 sm3 ax3 CTX KONT IH).
  - split; [exact BR4|].
    split; [apply (lp_regs_pres R R2 R4 sp fb); [lpregs KS2 XK| apply (PMK.regs_preserved_trans R2 R3 R4 RP23); apply PMK.preserved_by_index; intros k Hk; apply KS4; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto]|].
    split; [apply (lp_saved_agree R M1 M3 sp r); [intros a m G1 G2 j Gj; rewrite (AG23 a m ltac:(lia) ltac:(lia) j Gj); apply FRZ2; lia|lia|lia| exact SV1]|].
    destruct POST as (_ & STEPc & _ & [(v & Hv & Ev & MOv & _ & _ & INV3)|(Ee & INV3 & _)] & BBP); unfold PNR.o_ec, PMSP.o_ec in *; cbn [pa_off_ec AD PnLayoutS_u.ADDR_S] in *;
      destruct STEPc as (_ & _ & _ & _ & LEc).
    + split; [exists v, (pa_errcat_obj AD); split; [lia| exact Ev]|]. split; [exact INV3| intros _; exact (bb_room_keep _ _ _ _ BBP LEc (BBR1 MO1))].
    + split; [exists e1, c1; split; [exact He1| exact Ee]|]. split; [exact INV3| intros _; exact (bb_room_keep _ _ _ _ BBP LEc (BBR1 MO1))].
  - intros MO3. destruct POST as (_ & STEP23 & _ & [(v & Hv & Ev & MOv & _)|(Ee & INV3 & PROG)] & _); [rewrite MOv in MO3; discriminate|].
    cbn [PNBO.set_stk PNM.b_src PNM.b_stk] in STEP23, PROG. destruct STEP23 as (_ & _ & _ & _ & LE23).
    unfold PNR.bmu. rewrite ES, bflag_app, Hm. cbn [Z.eqb Pos.eqb orb].
    pose proof (bflag_range (PNM.b_stk s3)) as FR.
    destruct PROG as [(l3 & c3 & c3' & G1 & G2 & _ & Gm & _)|(cn & G2 & _ & Gc & _ & LT)].
    + cbn [PNBO.set_stk PNM.b_src PNM.b_stk] in G1. apply app_inj_tail in G1. destruct G1 as (<- & <-). rewrite G2, bflag_app, Gm. cbn [c2 PNM.bs_mode Z.eqb Pos.eqb orb]. lia.
    + cbn [PNBO.set_stk PNM.b_src PNM.b_stk] in LT. lia.
Qed.

(* [comment removed for export] *)
Lemma lp_mode1 K LBX sp r fb str (R : bvmap 5 word) (M : mem) model cr s sm ax (fx1 : FPState) R1 (M1 : mem) model1 cr1 s1 sm1 ax1 l c :
  lp_ctx K LBX sp r fb str R cr s sm -> lp_kont K LBX sp r fb str R M model cr s sm ax ->
  lp_linv LBX sp r fb str (BENT M model cr s sm ax) R R1 M1 model1 cr1 s1 sm1 ax1 -> PNM.b_more s1 = 1 ->
  PNM.b_stk s1 = l ++ [c] -> PNM.bs_mode c = 1 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x36c58 M1 model1) K.
Proof.
  intros CTX KONT LI MO1 ES Hm. head_intro CTX LI.
  destruct (lp_headfacts K LBX sp r fb str R M model cr s sm ax fx1 R1 M1 model1 cr1 s1 sm1 ax1 CTX LI) as (PA1 & STK1 & MOK1 & LE1 & UN1 & VIS1 & IMG1 & WP1 & AL40 & AL464).
  pose proof STK1 as (A16 & SLO & SHI & STOP & SDEF1). pose proof MOK1 as (Mh1 & Ml1 & Mm1). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG1.
  pose proof (L5C.stk_floor _ M1 sp 32768 STK1) as SFL. pose proof (L5C.stk_writable RSEGS _ M1 sp 32768 STK1) as WR1.
  destruct LI as (BR1 & RG1 & SV1 & (e1 & c1 & He1 & EC1) & INV1 & BBR1).
  pose proof RG1 as (X2 & X3 & X4 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & XK).
  pose proof PA1 as (_ & _ & _ & MO1' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SV & _). rewrite MO1 in MO1'.
  unfold PNM.OFF_STK in SV. pose proof SV as (V0 & _).
  destruct (lp_top LBX sp fb str _ M1 model1 cr1 s1 sm1 ax1 BR1 INV1) as (l_ & c_ & ES_ & OKc & SH & VE & TOPC & WT & DB & Hb & TOPIN & S4 & EAL & Hn).
  rewrite ES in ES_. apply app_inj_tail in ES_. destruct ES_ as (<- & <-).
  pose proof (shape_bottom_nil l c SH ltac:(rewrite Hm; unfold PNR.bmode_bottom; lia)) as NIL.
  set (b := PNM.b_sb s1) in *. set (n := Z.of_nat (length l)) in *. assert (Hn0 : n = 0) by (unfold n; rewrite NIL; reflexivity).
  destruct TOPC as (Tm & _). rewrite Hm in Tm. replace (b + 40 * n) with b in Tm by lia. rewrite Hn0 in VE.
  pose proof SV1 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88).
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 8))) as BU8. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 9))) as BU9.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 18))) as BU18. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 19))) as BU19.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 20))) as BU20. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 21))) as BU21.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 22))) as BU22. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 23))) as BU23.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 24))) as BU24. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 25))) as BU25.
  LeanFeed.pfeed P (PNSPAP.bpaH1_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 40%nat => b | 50%nat => r
               | 51%nat => bv_unsigned (getr R (PMK.reg 8)) | 52%nat => bv_unsigned (getr R (PMK.reg 9)) | 53%nat => bv_unsigned (getr R (PMK.reg 18))
               | 54%nat => bv_unsigned (getr R (PMK.reg 19)) | 55%nat => bv_unsigned (getr R (PMK.reg 20)) | 56%nat => bv_unsigned (getr R (PMK.reg 21))
               | 57%nat => bv_unsigned (getr R (PMK.reg 22)) | 58%nat => bv_unsigned (getr R (PMK.reg 23)) | 59%nat => bv_unsigned (getr R (PMK.reg 24))
               | 60%nat => bv_unsigned (getr R (PMK.reg 25)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSPAP.aligned; PMK.sc | replace (b + 40) with (b + 40 * 0 + 40) by lia; PMK.sc]).
  pvz_hg ltac:(idtac; destruct P as (fx2 & R2 & M2 & pvzP); PMK.pvz_lin pvzP;
                destruct pvzP as (MG2 & _ & FRZ2 & MS2 & KS2 & Y1 & Y2 & Y8 & Y9 & Y10 & Y11 & _ & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & (MB0 & MB1) & VE2)); PMK.pvz_clrT.
  apply (PNBK2.brel_piece_hdstk RSEGS AD AN L HI KH 10 LBX sp fb str _ M1 model1 cr1 s1 sm1 ax1 fx1 fx2 R1 R2 0x36c58 0x36e54 M2
           (fun a => (fb + 40 + 8 <= a < fb + 40 + 8 + 2) \/ (fb + 40 + 400 <= a < fb + 40 + 400 + 8)) 0 1 l [c] [] K ltac:(lia) BR1 FOK INCS MS2 MG2
           ltac:(intros a Ha N; apply FRZ2; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X])
           ltac:(intros a; apply PMK.or_dec; apply PMK.rng_dec) ES); fold b.
  { intros a Pa. cbn beta in Pa. right. clear -Pa. lia. }
  { replace (fb + 48) with (fb + 40 + 8) by lia. exact MB0. }
  { replace (fb + 49) with (fb + 40 + 8 + 1) by lia. exact MB1. }
  { left. reflexivity. } { right. reflexivity. }
  { rewrite NIL. cbn [app length]. replace (b + 40 * Z.of_nat 0) with b by lia. replace (fb + 440) with (fb + 40 + 400) by lia. exact VE2. }
  { intros i Hi. cbn in Hi. lia. }
  { rewrite NIL. cbn [app length]. clear -TOPIN. lia. }
  intros BR2.
  apply (lp_fin K LBX sp r fb str R M model cr s sm ax fx2 R2 M2 model1 cr1 _ sm1 ax1 CTX KONT BR2); [| exact Y1| exact Y2| PMK.rk| PMK.rk| exact Y8| exact Y9| exact Y18| exact Y19| exact Y20| exact Y21| exact Y22| exact Y23| exact Y24| exact Y25|].
  { exists e1, c1. split; [exact He1|]. apply (ec_agree M1 M2); [intros i Hi; apply FRZ2; lia|lia|lia| exact EC1]. }
  intros k Hk. rewrite (KS2 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). apply XK. exact Hk.
Qed.

(* [comment removed for export] *)
Lemma lp_mode23 K LBX sp r fb str (R : bvmap 5 word) (M : mem) model cr s sm ax (fx1 : FPState) R1 (M1 : mem) model1 cr1 s1 sm1 ax1 l c (m : Z) :
  lp_ctx K LBX sp r fb str R cr s sm -> lp_kont K LBX sp r fb str R M model cr s sm ax -> lp_IH K LBX sp r fb str R M model cr s sm ax (PNR.bmu s1 sm1) ->
  lp_linv LBX sp r fb str (BENT M model cr s sm ax) R R1 M1 model1 cr1 s1 sm1 ax1 -> PNM.b_more s1 = 1 ->
  PNM.b_stk s1 = l ++ [c] -> PNM.bs_mode c = m -> (m = 2 \/ m = 3) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x36c58 M1 model1) K.
Proof.
  intros CTX KONT IH LI MO1 ES Hm Hm23. head_intro CTX LI.
  destruct (lp_headfacts K LBX sp r fb str R M model cr s sm ax fx1 R1 M1 model1 cr1 s1 sm1 ax1 CTX LI) as (PA1 & STK1 & MOK1 & LE1 & UN1 & VIS1 & IMG1 & WP1 & AL40 & AL464).
  pose proof STK1 as (A16 & SLO & SHI & STOP & SDEF1). pose proof MOK1 as (Mh1 & Ml1 & Mm1). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG1.
  pose proof (L5C.stk_floor _ M1 sp 32768 STK1) as SFL. pose proof (L5C.stk_writable RSEGS _ M1 sp 32768 STK1) as WR1.
  destruct LI as (BR1 & RG1 & SV1 & (e1 & c1 & He1 & EC1) & INV1 & BBR1).
  pose proof RG1 as (X2 & X3 & X4 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & XK).
  pose proof PA1 as (_ & _ & _ & MO1' & _). rewrite MO1 in MO1'.
  destruct (lp_top LBX sp fb str _ M1 model1 cr1 s1 sm1 ax1 BR1 INV1) as (l_ & c_ & ES_ & OKc & SH & VE & TOPC & WT & DB & Hb & TOPIN & S4 & EAL & Hn).
  rewrite ES in ES_. apply app_inj_tail in ES_. destruct ES_ as (<- & <-).
  set (b := PNM.b_sb s1) in *. set (n := Z.of_nat (length l)) in *.
  pose proof OKc as (OKm & OKl & OKp & OKt & OKi). destruct TOPC as (Tm & Tl & Tp & Tt & Ti). rewrite Hm in Tm.
  pose proof (shape_cont_cons l c SH ltac:(rewrite Hm; unfold PNR.bmode_cont; lia)) as NNIL.
  assert (LEN2 : (2 <= length (l ++ [c]))%nat) by (rewrite length_app; cbn; destruct l; [destruct (NNIL eq_refl)| cbn; lia]).
  unfold PNRS.src_read_spec, PNR.src_read_spec in SRD. unfold PNRS.make_ec_spec in MKE.
  unfold PNRS.end_document_spec, PNR.end_document_spec in ED. unfold PNRS.end_array_spec, PNR.end_array_spec in EA.
  unfold PNRS.read_e_name_spec, PNR.read_e_name_spec in REN. unfold PNRS.read_value_spec, PNR.read_value_spec in RV.
  (* [comment removed for export] *)
  assert (HEAD : exists (fx2 : FPState) R2, msteps RSEGS (@mkst fx1 R1 (Z_to_bv 64 0x36c58) M1 (seg_rom RSEGS)) (@mkst fx2 R2 (Z_to_bv 64 0x370d0) M1 (seg_rom RSEGS))
            /\ lp_regs R R2 sp fb /\ getr R2 (PMK.reg 1) = Z_to_bv 64 (if Z.eqb m 2 then 0x36cd0 else 0x36d4c)
            /\ getr R2 (PMK.reg 10) = Z_to_bv 64 (fb + 56) /\ getr R2 (PMK.reg 11) = Z_to_bv 64 (sp - 112) /\ getr R2 (PMK.reg 12) = Z_to_bv 64 1).
  { destruct Hm23 as [-> | ->].
    - LeanFeed.pfeed P (PNSPAP.bpaH2_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 45%nat => b + 40 * n + 40 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSPAP.aligned; PMK.sc]).
      destruct P as (fx2 & R2 & M2 & MG2 & EQ2w & EQ2 & MS2 & KS2 & Y1 & Y10 & Y11 & Y12). assert (EM2 : M2 = M1) by (apply functional_extensionality; exact EQ2w). subst M2.
      exists fx2, R2. split; [exact MS2|]. split; [lpregs KS2 XK|]. split; [exact Y1|]. split; [replace (fb + 56) with (fb + 40 + 16) by lia; exact Y10|]. split; [exact Y11| exact Y12].
    - LeanFeed.pfeed P (PNSPAP.bpaH3_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 45%nat => b + 40 * n + 40 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSPAP.aligned; PMK.sc]).
      destruct P as (fx2 & R2 & M2 & MG2 & EQ2w & EQ2 & MS2 & KS2 & Y1 & Y10 & Y11 & Y12). assert (EM2 : M2 = M1) by (apply functional_extensionality; exact EQ2w). subst M2.
      exists fx2, R2. split; [exact MS2|]. split; [lpregs KS2 XK|]. split; [exact Y1|]. split; [replace (fb + 56) with (fb + 40 + 16) by lia; exact Y10|]. split; [exact Y11| exact Y12]. }
  destruct HEAD as (fx2 & R2 & MS2 & RG2 & Y1 & Y10 & Y11 & Y12).
  pose proof RG2 as (Z2 & Z3 & Z4 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & ZK).
  eapply (L5.cps_of_msteps RSEGS); [exact Mh1| exact Ml1| exact MS2|].
  change (mkCfg (@mkst fx2 R2 (Z_to_bv 64 0x370d0) M1 (seg_rom RSEGS)) model1) with (@PMSP.cfg RSEGS fx2 R2 (pa_src_read AD) M1 model1).
  (* [comment removed for export] *)
  apply (PNBK.brel_src_read RSEGS AD AN L HI KH 10 LBX sp fb str _ M1 model1 cr1 s1 sm1 ax1 fx2 R2 (sp - 112) _ (sp - 112) 1 K SRD
           ltac:(lia) K0 BR1 FOK INCS Y1 ltac:(destruct Hm23 as [-> | ->]; cbn; (split; [lia| reflexivity])) Z2 Z3 Z4 Y10 Y11 Y12
           ltac:(lia) ltac:(unfold PMSP.pm_scr; lia) (mod16_sub112 sp A16) ltac:(lia) ltac:(lia) ltac:(lia)).
  intros fx3 R3 M3 src3 sm3 d RP23 W10 Hd UNR3 DEFc BR3 AG13.
  set (s3 := PNM.with_srcB s1 src3) in *.
  assert (BBR3 : PNR.bb_room s3 sm3) by (apply (bb_room_keep s1 s3 sm1 sm3); [reflexivity| cbn [s3 PNM.with_srcB PNM.b_src]; clear -UNR3 Hd; lia| exact (BBR1 MO1)]).
  assert (SV3 : lp_saved R M3 sp r) by (apply (lp_saved_agree R M1 M3 sp r); [intros a m' G1 G2; apply AG13; lia| lia| lia| exact SV1]).
  assert (EC3 : PMSP.ec_at RSEGS M3 (fb + 16) e1 c1) by (apply (ec_agree M1 M3); [apply AG13; lia|lia|lia| exact EC1]).
  assert (INV3 : PNR.binv s3) by exact INV1.
  assert (RG3 : lp_regs R R3 sp fb) by exact (lp_regs_pres R R2 R3 sp fb RG2 RP23).
  pose proof RG3 as (W2 & W3 & W4 & W8 & W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & WK).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 10 LBX sp fb str _ M3 model1 cr1 s3 sm3 ax1 BR3) as (PA3 & _ & _ & UN3 & STK3 & MOK3).
  change (PMSP.pm_scr 10) with 32768 in STK3. pose proof (L5C.stk_writable RSEGS _ M3 sp 32768 STK3) as WR3. pose proof MOK3 as (Mh3 & Ml3 & _).
  pose proof BR3 as ((_ & _ & VIS3 & _ & BASE3 & _) & _). cbn [PNBK.be_M] in VIS3, BASE3.
  unfold PNR.o_v, PMSP.o_v, PMSP.visitor_at in VIS3. cbn [pa_off_v pa_vp_visitor AD PnLayoutS_u.ADDR_S] in VIS3.
  pose proof BASE3 as (IMG3 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG3.
  destruct (lp_top LBX sp fb str _ M3 model1 cr1 s3 sm3 ax1 BR3 INV3) as (l_ & c_ & ES3 & _ & _ & VE3 & TOPC3 & WT3 & DB3 & _).
  cbn [s3 PNM.with_srcB PNM.b_stk PNM.b_sb PNM.b_sk] in ES3, VE3, TOPC3, WT3, DB3. rewrite ES in ES3. apply app_inj_tail in ES3. destruct ES3 as (<- & <-).
  fold b n in VE3, TOPC3, WT3. destruct TOPC3 as (Um & Ul & Up & Ut & Ui).
  cbn [s3 PNM.with_srcB PNM.b_src] in UNR3, UN3.
  assert (WP3 : L5.writable RSEGS M3 (fb + 40) 416) by (destruct PA3 as (_ & D & _); apply (L5C.writable_of_defined RSEGS); [exact D|lia|lia]).
  assert (WTP : L5.writable RSEGS M3 (b + 40 * n + 40 - 24) 8) by (apply (L5.writable_sub RSEGS M3 (b + 40 * n) 40); [exact WT3| lia| lia]).
  (* [comment removed for export] *)
  assert (POSUPD : forall (fx4 : FPState) R4 (M4 : mem) (pc4 : Z) Q,
            msteps RSEGS (@mkst fx3 R3 (Z_to_bv 64 (if Z.eqb m 2 then 0x36cd0 else 0x36d4c)) M3 (seg_rom RSEGS)) (@mkst fx4 R4 (Z_to_bv 64 pc4) M4 (seg_rom RSEGS)) ->
            mem_grows M3 M4 -> (forall i, 0 <= i < 2 ^ 64 -> ~ (b + 40 * n + 40 - 24 <= i < b + 40 * n + 40 - 24 + 8) -> M4 (Z_to_bv 64 i) = M3 (Z_to_bv 64 i)) ->
            (forall c', PNM.bstate_ok c' -> PNM.bs_mode c' = m -> PNM.bs_len c' = PNM.bs_len c -> PNM.bs_type c' = PNM.bs_type c -> PNM.bs_idx c' = PNM.bs_idx c ->
               brel LBX sp fb str (BENT M model cr s sm ax) (BENT M4 model1 cr1 (PNBO.set_stk s3 (l ++ [c'])) sm3 ax1) -> Q) ->
            (Q -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 pc4 M4 model1) K) ->
            srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 (if Z.eqb m 2 then 0x36cd0 else 0x36d4c) M3 model1) K).
  { intros fx4 R4 M4 pc4 Q MS4 MG4 FRZ4 HQ KQ.
    destruct (PMCG.u64_of_defined RSEGS M4 (b + 40 * n + 16) ltac:(lia) ltac:(lia)) as (v' & Hv' & CP4).
    { apply (L5.defined_grows M3 M4 _ _ MG4). apply (L5.defined_sub M3 b (40 * 2 ^ PNM.b_sk s1)); [exact DB3| lia| clear -Hn TOPIN; lia]. }
    apply (PNBK2.brel_piece_pos RSEGS AD AN L HI KH 10 LBX sp fb str _ M3 model1 cr1 s3 sm3 ax1 fx3 fx4 R3 R4 _ pc4 M4
             (fun a => b + 40 * n + 40 - 24 <= a < b + 40 * n + 40 - 24 + 8) l c v' K ltac:(lia) BR3 FOK INCS MS4 MG4 FRZ4 ltac:(intros a; apply PMK.rng_dec));
      cbn [s3 PNM.with_srcB PNM.b_sb PNM.b_stk]; fold b n.
    - exact ES.
    - intros a Pa. cbn beta in Pa. right. clear -Pa. lia.
    - exact CP4.
    - exact Hv'.
    - intros BR4. apply KQ. apply (HQ (PNM.BS (PNM.bs_mode c) (PNM.bs_len c) v' (PNM.bs_type c) (PNM.bs_idx c))); [unfold PNM.bstate_ok; cbn; lia| exact Hm| reflexivity| reflexivity| reflexivity| exact BR4]. }
  assert (Hd01 : d = 0 \/ d = 1) by lia. destruct Hd01 as [-> | ->].
  - (* [comment removed for export] *)
    assert (PE : exists (fx4 : FPState) R4 M4, msteps RSEGS (@mkst fx3 R3 (Z_to_bv 64 (if Z.eqb m 2 then 0x36cd0 else 0x36d4c)) M3 (seg_rom RSEGS)) (@mkst fx4 R4 (Z_to_bv 64 0x36ee4) M4 (seg_rom RSEGS))
              /\ mem_grows M3 M4 /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (b + 40 * n + 40 - 24 <= i < b + 40 * n + 40 - 24 + 8) -> M4 (Z_to_bv 64 i) = M3 (Z_to_bv 64 i))
              /\ lp_regs R R4 sp fb /\ getr R4 (PMK.reg 1) = Z_to_bv 64 0x36e20 /\ getr R4 (PMK.reg 10) = Z_to_bv 64 (fb + 16) /\ getr R4 (PMK.reg 11) = Z_to_bv 64 1).
    { destruct Hm23 as [-> | ->]; cbn [Z.eqb Pos.eqb].
      - LeanFeed.pfeed P (PNSPAP.bpaR2e_conc fx3 R3 M3 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 43%nat => PNM.bs_pos c | 45%nat => b + 40 * n + 40 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSPAP.aligned; PMK.sc]).
        pvz_hg ltac:(idtac; destruct P as (fx4 & R4 & M4 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG4 & _ & FRZ4 & MS4 & KS4 & Y1' & Y10' & Y11' & _)); PMK.pvz_clrT.
        exists fx4, R4, M4. split; [exact MS4|]. split; [exact MG4|]. split; [exact FRZ4|]. split; [lpregs KS4 WK|]. split; [exact Y1'|]. split; [exact Y10'| exact Y11'].
      - LeanFeed.pfeed P (PNSPAP.bpaR3e_conc fx3 R3 M3 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 43%nat => PNM.bs_pos c | 45%nat => b + 40 * n + 40 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSPAP.aligned; PMK.sc]).
        pvz_hg ltac:(idtac; destruct P as (fx4 & R4 & M4 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG4 & _ & FRZ4 & MS4 & KS4 & Y1' & Y10' & Y11' & _)); PMK.pvz_clrT.
        exists fx4, R4, M4. split; [exact MS4|]. split; [exact MG4|]. split; [exact FRZ4|]. split; [lpregs KS4 WK|]. split; [exact Y1'|]. split; [exact Y10'| exact Y11']. }
    destruct PE as (fx4 & R4 & M4 & MS4 & MG4 & FRZ4 & RG4 & V1 & V10 & V11).
    pose proof RG4 as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & QK).
    apply (POSUPD fx4 R4 M4 0x36ee4 (exists c', brel LBX sp fb str (BENT M model cr s sm ax) (BENT M4 model1 cr1 (PNBO.set_stk s3 (l ++ [c'])) sm3 ax1) /\ PNM.bstate_ok c' /\ PNM.bs_mode c' = m) MS4 MG4 FRZ4).
    { intros c' OK' Hm' _ _ _ BR4. exists c'. split; [exact BR4|]. split; [exact OK'| exact Hm']. }
    intros (c' & BR4 & OK' & Hm').
    assert (AG34 : forall a m', sp - 112 <= a -> a + m' <= 2 ^ 64 -> L5C.agree_on M3 M4 a m') by (intros a m' G1 G2 j Gj; apply FRZ4; lia).
    assert (ED4 : L5.defined M4 (fb + 16) 16) by (destruct EC3 as (_ & _ & D); apply (L5.defined_grows M3 M4 _ _ MG4 D)).
    apply (PNBK.brel_make_ec RSEGS AD AN L HI KH 10 LBX sp fb str _ M4 model1 cr1 _ sm3 ax1 fx4 R4 (sp - 112) 0x36e20 1 K MKE ltac:(lia) K0 BR4 FOK INCS
             V1 ltac:(split; [lia| reflexivity]) Q2 Q3 Q4 V10 V11 ltac:(lia) ltac:(lia) ltac:(unfold PMSP.pm_scr; lia) (mod16_sub112 sp A16) ED4).
    intros fx5 R5 M5 RP45 EC5 BR5 AG45.
    destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 10 LBX sp fb str _ M5 model1 cr1 _ sm3 _ BR5) as (PA5 & _ & _ & _ & STK5 & _).
    change (PMSP.pm_scr 10) with 32768 in STK5. pose proof (L5C.stk_writable RSEGS _ M5 sp 32768 STK5) as WR5.
    assert (WP5 : L5.writable RSEGS M5 (fb + 40) 416) by (destruct PA5 as (_ & D & _); apply (L5C.writable_of_defined RSEGS); [exact D|lia|lia]).
    assert (SV5 : lp_saved R M5 sp r).
    { apply (lp_saved_agree R M4 M5 sp r); [intros a m' G1 G2; apply AG45; lia|lia|lia|].
      apply (lp_saved_agree R M3 M4 sp r); [intros a m' G1 G2; apply AG34; lia|lia|lia| exact SV3]. }
    pose proof SV5 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88).
    pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 8))) as BU8. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 9))) as BU9.
    pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 18))) as BU18. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 19))) as BU19.
    pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 20))) as BU20. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 21))) as BU21.
    pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 22))) as BU22. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 23))) as BU23.
    pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 24))) as BU24. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 25))) as BU25.
    LeanFeed.pfeed P (PNSPAP.bpaME_conc fx5 R5 M5 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 50%nat => r
                 | 51%nat => bv_unsigned (getr R (PMK.reg 8)) | 52%nat => bv_unsigned (getr R (PMK.reg 9)) | 53%nat => bv_unsigned (getr R (PMK.reg 18))
                 | 54%nat => bv_unsigned (getr R (PMK.reg 19)) | 55%nat => bv_unsigned (getr R (PMK.reg 20)) | 56%nat => bv_unsigned (getr R (PMK.reg 21))
                 | 57%nat => bv_unsigned (getr R (PMK.reg 22)) | 58%nat => bv_unsigned (getr R (PMK.reg 23)) | 59%nat => bv_unsigned (getr R (PMK.reg 24))
                 | 60%nat => bv_unsigned (getr R (PMK.reg 25)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSPAP.aligned; PMK.sc]).
    pvz_hg ltac:(idtac; destruct P as (fx6 & R6 & M6 & pvzP); PMK.pvz_lin pvzP;
                  destruct pvzP as (MG6 & _ & FRZ6 & MS6 & KS6 & Y1' & Y2' & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & MO6)); PMK.pvz_clrT.
    apply (PNBK2.brel_piece_more RSEGS AD AN L HI KH 10 LBX sp fb str _ M5 model1 cr1 _ sm3 _ fx5 fx6 R5 R6 0x36e20 0x36e54 M6
             (fun a => fb + 40 + 8 <= a < fb + 40 + 8 + 1) 0 K ltac:(lia) BR5 FOK INCS MS6 MG6 FRZ6 ltac:(intros a; apply PMK.rng_dec)
             ltac:(intros a Pa; cbn beta in Pa; right; clear -Pa; lia) ltac:(replace (fb + 48) with (fb + 40 + 8) by lia; exact MO6) ltac:(left; reflexivity)).
    intros BR6.
    apply (lp_fin K LBX sp r fb str R M model cr s sm ax fx6 R6 M6 model1 cr1 _ sm3 _ CTX KONT BR6); [| exact Y1'| exact Y2'| PMK.rk| PMK.rk| exact Y8| exact Y9| exact Y18| exact Y19| exact Y20| exact Y21| exact Y22| exact Y23| exact Y24| exact Y25|].
    { exists 1, (pa_errcat_obj AD). split; [lia|]. unfold PNR.o_ec, PMSP.o_ec in EC5. cbn [pa_off_ec AD PnLayoutS_u.ADDR_S] in EC5.
      apply (ec_agree M5 M6); [intros i Hi; apply FRZ6; lia|lia|lia| exact EC5]. }
    intros k Hk. rewrite (KS6 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). rewrite (PMK.cs_of_preserved R4 R5 k RP45) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto).
    apply QK. exact Hk.
  - (* [comment removed for export] *)
    destruct (PMCG.u8_of_defined RSEGS M3 (sp - 112) ltac:(lia) ltac:(lia) DEFc) as (cb & Hcb & CB).
    destruct (Z.eq_dec cb 0) as [-> | NZ].
    + (* [comment removed for export] *)
      assert (PE : exists (fx4 : FPState) R4 M4, msteps RSEGS (@mkst fx3 R3 (Z_to_bv 64 (if Z.eqb m 2 then 0x36cd0 else 0x36d4c)) M3 (seg_rom RSEGS))
                                                    (@mkst fx4 R4 (Z_to_bv 64 (if Z.eqb m 2 then 0x3745c else 0x37db4)) M4 (seg_rom RSEGS))
                /\ mem_grows M3 M4 /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (b + 40 * n + 40 - 24 <= i < b + 40 * n + 40 - 24 + 8) -> M4 (Z_to_bv 64 i) = M3 (Z_to_bv 64 i))
                /\ lp_regs R R4 sp fb /\ getr R4 (PMK.reg 1) = Z_to_bv 64 (if Z.eqb m 2 then 0x36df4 else 0x36e08)
                /\ getr R4 (PMK.reg 10) = Z_to_bv 64 (fb + 40) /\ getr R4 (PMK.reg 11) = Z_to_bv 64 (fb + 464) /\ getr R4 (PMK.reg 12) = Z_to_bv 64 (fb + 16)).
      { destruct Hm23 as [-> | ->]; cbn [Z.eqb Pos.eqb].
        - LeanFeed.pfeed P (PNSPAP.bpaR20_conc fx3 R3 M3 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 43%nat => PNM.bs_pos c | 45%nat => b + 40 * n + 40 | 46%nat => 0 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSPAP.aligned; PMK.sc]).
          pvz_hg ltac:(idtac; destruct P as (fx4 & R4 & M4 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG4 & _ & FRZ4 & MS4 & KS4 & Y1' & Y10' & Y11' & Y12')); PMK.pvz_clrT.
          exists fx4, R4, M4. split; [exact MS4|]. split; [exact MG4|]. split; [exact FRZ4|]. split; [lpregs KS4 WK|]. split; [exact Y1'|]. split; [exact Y10'|]. split; [exact Y11'| exact Y12'].
        - LeanFeed.pfeed P (PNSPAP.bpaR30_conc fx3 R3 M3 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 43%nat => PNM.bs_pos c | 45%nat => b + 40 * n + 40 | 46%nat => 0 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSPAP.aligned; PMK.sc]).
          pvz_hg ltac:(idtac; destruct P as (fx4 & R4 & M4 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG4 & _ & FRZ4 & MS4 & KS4 & Y1' & Y10' & Y11' & Y12')); PMK.pvz_clrT.
          exists fx4, R4, M4. split; [exact MS4|]. split; [exact MG4|]. split; [exact FRZ4|]. split; [lpregs KS4 WK|]. split; [exact Y1'|]. split; [exact Y10'|]. split; [exact Y11'| exact Y12']. }
      destruct PE as (fx4 & R4 & M4 & MS4 & MG4 & FRZ4 & RG4 & V1 & V10 & V11 & V12).
      pose proof RG4 as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & QK).
      apply (POSUPD fx4 R4 M4 _ (exists c', brel LBX sp fb str (BENT M model cr s sm ax) (BENT M4 model1 cr1 (PNBO.set_stk s3 (l ++ [c'])) sm3 ax1) /\ PNM.bstate_ok c' /\ PNM.bs_mode c' = m) MS4 MG4 FRZ4).
      { intros c' OK' Hm' _ _ _ BR4. exists c'. split; [exact BR4|]. split; [exact OK'| exact Hm']. }
      intros (c' & BR4 & OK' & Hm').
      assert (AG34 : forall a m', sp - 112 <= a -> a + m' <= 2 ^ 64 -> L5C.agree_on M3 M4 a m') by (intros a m' G1 G2 j Gj; apply FRZ4; lia).
      assert (INV4 : PNR.binv (PNBO.set_stk s3 (l ++ [c']))).
      { split; [destruct INV1 as (ID & _); exact ID|]. cbn [PNBO.set_stk PNM.b_stk]. apply (shape_top_mode l c c' SH OK'); [intros E; destruct (NNIL E)| intros _; rewrite Hm'; unfold PNR.bmode_cont; lia]. }
      assert (CALL : PNR.brun_spec RSEGS AD AN L HI false (if Z.eqb m 2 then 0x3745c else 0x37db4) 3 (PNR.bargs_end AD) PNR.bprog_pop).
      { destruct Hm23 as [-> | ->]; cbn [Z.eqb Pos.eqb]; [exact ED| exact EA]. }
      apply (PNBK2.brel_call RSEGS AD AN L HI KH false _ 3 (PNR.bargs_end AD) PNR.bprog_pop 10 LBX sp fb str _ M4 model1 cr1 _ sm3 ax1 fx4 R4 (sp - 112) _ c1 e1 K
               CALL ltac:(lia) ltac:(lia) K0 BR4 FOK INCS CRED V1 ltac:(destruct Hm23 as [-> | ->]; cbn; (split; [lia| reflexivity])) Q2 Q3 Q4 ltac:(lia) ltac:(unfold PMSP.pm_scr; lia) (mod16_sub112 sp A16)).
      { unfold PNR.bargs_end, PNR.bargs3, PNR.o_p, PNR.o_ec, PNR.o_v, PMSP.o_p, PMSP.o_ec, PMSP.o_v. cbn [pa_off_p pa_off_ec pa_off_v AD PnLayoutS_u.ADDR_S PNBO.set_stk PNM.b_stk].
        rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [split; [exact V10|]; split; [exact V11| exact V12]|]. rewrite length_app in *. cbn [length] in *. lia. }
      { exact INV4. }
      { apply (ec_agree M3 M4); [apply AG34; lia|lia|lia| exact EC3]. }
      { exact He1. }
      { cbn [PNBO.set_stk s3 PNM.with_srcB PNM.b_src]. lia. }
      intros fx5 R5 M5 model5 s5 sm5 ax5 cr5 RP45 POST BR5 AG45.
      (* [comment removed for export] *)
      assert (TOX : forall Q : Prop, (forall (fx6 : FPState) R6, lp_regs R R6 sp fb -> brel LBX sp fb str (BENT M model cr s sm ax) (BENT M5 model5 cr5 s5 sm5 ax5) ->
                                        srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0x36e08 M5 model5) K) ->
                     srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 (if Z.eqb m 2 then 0x36df4 else 0x36e08) M5 model5) K).
      { intros _ HX. assert (RG5 : lp_regs R R5 sp fb) by exact (lp_regs_pres R R4 R5 sp fb RG4 RP45).
        destruct Hm23 as [-> | ->]; cbn [Z.eqb Pos.eqb]; [| exact (HX fx5 R5 RG5 BR5)].
        pose proof RG5 as (T2 & T3 & T4 & T8 & T9 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & TK).
        destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 10 LBX sp fb str _ M5 model5 cr5 s5 sm5 ax5 BR5) as (_ & _ & _ & _ & STK5 & MOK5).
        change (PMSP.pm_scr 10) with 32768 in STK5. pose proof (L5C.stk_writable RSEGS _ M5 sp 32768 STK5) as WR5. pose proof MOK5 as (Mh5 & Ml5 & _).
        LeanFeed.pfeed P (PNSPAP.bpaJ68_conc fx5 R5 M5 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSPAP.aligned; PMK.sc]).
        destruct P as (fx6 & R6 & M6 & MG6 & EQ6w & EQ6 & MS6 & KS6). assert (EM6 : M6 = M5) by (apply functional_extensionality; exact EQ6w). subst M6.
        apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 10 LBX sp fb str _ M5 model5 cr5 s5 sm5 ax5 fx5 fx6 R5 R6 0x36df4 0x36e08 M5 (fun _ => False) K
                 ltac:(lia) BR5 FOK INCS MS6 MG6 ltac:(intros a Ha _; reflexivity) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
        intros BR6. apply (HX fx6 R6); [lpregs KS6 TK| exact BR6]. }
      apply (TOX True). intros fx6 R6 RG6 BR6.
      apply (lp_X K LBX sp r fb str R M model cr s sm ax (PNR.bmu s1 sm1) fx6 R6 M5 model5 cr5 s5 sm5 ax5 CTX KONT IH).
      * split; [exact BR6|]. split; [exact RG6|].
        split; [apply (lp_saved_agree R M3 M5 sp r); [intros a m' G1 G2 j Gj; rewrite (AG45 a m' ltac:(lia) ltac:(lia) j Gj); apply FRZ4; lia|lia|lia| exact SV3]|].
        destruct POST as (_ & STEPc & _ & [(v & Hv & Ev & MOv & _ & _ & INV5)|(Ee & INV5 & _)] & BBP); unfold PNR.o_ec, PMSP.o_ec in *; cbn [pa_off_ec AD PnLayoutS_u.ADDR_S] in *;
          destruct STEPc as (_ & _ & _ & _ & LEc).
        -- split; [exists v, (pa_errcat_obj AD); split; [lia| exact Ev]|]. split; [exact INV5| intros _; exact (bb_room_keep _ _ _ _ BBP LEc BBR3)].
        -- split; [exists e1, c1; split; [exact He1| exact Ee]|]. split; [exact INV5| intros _; exact (bb_room_keep _ _ _ _ BBP LEc BBR3)].
      * intros MO5. destruct POST as (_ & STEP45 & _ & [(v & Hv & Ev & MOv & _)|(Ee & INV5 & PROG)] & _); [rewrite MOv in MO5; discriminate|].
        cbn [PNBO.set_stk s3 PNM.with_srcB PNM.b_src PNM.b_stk] in STEP45, PROG. destruct STEP45 as (_ & _ & _ & _ & LE45).
        destruct PROG as ((l5 & c5 & top5 & c5' & G1 & G2 & _) & UEQ). cbn [PNBO.set_stk s3 PNM.with_srcB PNM.b_src PNM.b_stk] in UEQ.
        unfold PNR.bmu. rewrite ES, bflag_app, Hm. pose proof (bflag_range (PNM.b_stk s5)) as FR.
        destruct Hm23 as [-> | ->]; cbn [Z.eqb Pos.eqb orb]; clear -UEQ FR UNR3 UN3; lia.
    + (* [comment removed for export] *)
      assert (PE : exists (fx4 : FPState) R4 M4, msteps RSEGS (@mkst fx3 R3 (Z_to_bv 64 (if Z.eqb m 2 then 0x36cd0 else 0x36d4c)) M3 (seg_rom RSEGS)) (@mkst fx4 R4 (Z_to_bv 64 0x37338) M4 (seg_rom RSEGS))
                /\ mem_grows M3 M4 /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (b + 40 * n + 40 - 24 <= i < b + 40 * n + 40 - 24 + 8) -> M4 (Z_to_bv 64 i) = M3 (Z_to_bv 64 i))
                /\ lp_regs R R4 sp fb /\ getr R4 (PMK.reg 1) = Z_to_bv 64 (if Z.eqb m 2 then 0x36d14 else 0x36d90)
                /\ getr R4 (PMK.reg 10) = Z_to_bv 64 (fb + 40) /\ getr R4 (PMK.reg 11) = Z_to_bv 64 (fb + 464)
                /\ getr R4 (PMK.reg 12) = Z_to_bv 64 (if Z.eqb m 2 then 0 else 1) /\ getr R4 (PMK.reg 13) = Z_to_bv 64 (fb + 16)).
      { destruct Hm23 as [-> | ->]; cbn [Z.eqb Pos.eqb].
        - LeanFeed.pfeed P (PNSPAP.bpaR21_conc fx3 R3 M3 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 43%nat => PNM.bs_pos c | 45%nat => b + 40 * n + 40 | 46%nat => cb | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSPAP.aligned; PMK.sc]).
          pvz_hg ltac:(idtac; destruct P as (fx4 & R4 & M4 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG4 & _ & FRZ4 & MS4 & KS4 & Y1' & Y10' & Y11' & Y12' & Y13')); PMK.pvz_clrT.
          exists fx4, R4, M4. split; [exact MS4|]. split; [exact MG4|]. split; [exact FRZ4|]. split; [lpregs KS4 WK|]. split; [exact Y1'|]. split; [exact Y10'|]. split; [exact Y11'|]. split; [exact Y12'| exact Y13'].
        - LeanFeed.pfeed P (PNSPAP.bpaR31_conc fx3 R3 M3 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 43%nat => PNM.bs_pos c | 45%nat => b + 40 * n + 40 | 46%nat => cb | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSPAP.aligned; PMK.sc]).
          pvz_hg ltac:(idtac; destruct P as (fx4 & R4 & M4 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG4 & _ & FRZ4 & MS4 & KS4 & Y1' & Y10' & Y11' & Y12' & Y13')); PMK.pvz_clrT.
          exists fx4, R4, M4. split; [exact MS4|]. split; [exact MG4|]. split; [exact FRZ4|]. split; [lpregs KS4 WK|]. split; [exact Y1'|]. split; [exact Y10'|]. split; [exact Y11'|]. split; [exact Y12'| exact Y13']. }
      destruct PE as (fx4 & R4 & M4 & MS4 & MG4 & FRZ4 & RG4 & V1 & V10 & V11 & V12 & V13).
      pose proof RG4 as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & QK).
      apply (POSUPD fx4 R4 M4 _ (exists c', brel LBX sp fb str (BENT M model cr s sm ax) (BENT M4 model1 cr1 (PNBO.set_stk s3 (l ++ [c'])) sm3 ax1) /\ PNM.bstate_ok c' /\ PNM.bs_mode c' = m) MS4 MG4 FRZ4).
      { intros c' OK' Hm' _ _ _ BR4. exists c'. split; [exact BR4|]. split; [exact OK'| exact Hm']. }
      intros (c' & BR4 & OK' & Hm').
      assert (AG34 : forall a m', sp - 112 <= a -> a + m' <= 2 ^ 64 -> L5C.agree_on M3 M4 a m') by (intros a m' G1 G2 j Gj; apply FRZ4; lia).
      assert (INV4 : PNR.binv (PNBO.set_stk s3 (l ++ [c']))).
      { split; [destruct INV1 as (ID & _); exact ID|]. cbn [PNBO.set_stk PNM.b_stk]. apply (shape_top_mode l c c' SH OK'); [intros E; destruct (NNIL E)| intros _; rewrite Hm'; unfold PNR.bmode_cont; lia]. }
      apply (PNBK2.brel_call RSEGS AD AN L HI KH false _ 6 (PNR.bargs_en AD) PNR.bprog_name 10 LBX sp fb str _ M4 model1 cr1 _ sm3 ax1 fx4 R4 (sp - 112) _ c1 e1 K
               REN ltac:(lia) ltac:(lia) K0 BR4 FOK INCS CRED V1 ltac:(destruct Hm23 as [-> | ->]; cbn; (split; [lia| reflexivity])) Q2 Q3 Q4 ltac:(lia) ltac:(unfold PMSP.pm_scr; lia) (mod16_sub112 sp A16)).
      { unfold PNR.bargs_en, PNR.o_p, PNR.o_ec, PNR.o_v, PMSP.o_p, PMSP.o_ec, PMSP.o_v. cbn [pa_off_p pa_off_ec pa_off_v AD PnLayoutS_u.ADDR_S].
        rewrite L5K.rl10, L5K.rl11, L5K.rl12, L5K.rl13. split; [exact V10|]. split; [exact V11|]. split; [exact V13|]. destruct Hm23 as [-> | ->]; cbn [Z.eqb Pos.eqb] in V12; [left| right]; exact V12. }
      { exact INV4. }
      { apply (ec_agree M3 M4); [apply AG34; lia|lia|lia| exact EC3]. }
      { exact He1. }
      { cbn [PNBO.set_stk s3 PNM.with_srcB PNM.b_src]. lia. }
      intros fx5 R5 M5 model5 s5 sm5 ax5 cr5 RP45 POST BR5 AG45.
      assert (RG5 : lp_regs R R5 sp fb) by exact (lp_regs_pres R R4 R5 sp fb RG4 RP45).
      pose proof RG5 as (T2 & T3 & T4 & T8 & T9 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & TK).
      assert (SV5 : lp_saved R M5 sp r).
      { apply (lp_saved_agree R M3 M5 sp r); [intros a m' G1 G2 j Gj; rewrite (AG45 a m' ltac:(lia) ltac:(lia) j Gj); apply FRZ4; lia|lia|lia| exact SV3]. }
      assert (CB5 : L5.u8_at RSEGS M5 (sp - 112) cb).
      { apply (L5C.u8_at_agree RSEGS M3 M5); [intros j Gj; rewrite (AG45 (sp - 112) 1 ltac:(lia) ltac:(lia) j Gj); apply FRZ4; lia|lia|lia| exact CB]. }
      destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 10 LBX sp fb str _ M5 model5 cr5 s5 sm5 ax5 BR5) as (PA5 & _ & _ & UN5 & STK5 & MOK5).
      change (PMSP.pm_scr 10) with 32768 in STK5. pose proof (L5C.stk_writable RSEGS _ M5 sp 32768 STK5) as WR5. pose proof MOK5 as (Mh5 & Ml5 & _).
      assert (WP5 : L5.writable RSEGS M5 (fb + 40) 416) by (destruct PA5 as (_ & D & _); apply (L5C.writable_of_defined RSEGS); [exact D|lia|lia]).
      pose proof BR5 as ((_ & _ & VIS5 & _ & BASE5 & _) & STEP5 & _). cbn [PNBK.be_M PNBK.be_s PNBK.be_sm] in VIS5, BASE5, STEP5.
      unfold PNR.o_v, PMSP.o_v, PMSP.visitor_at in VIS5. cbn [pa_off_v pa_vp_visitor AD PnLayoutS_u.ADDR_S] in VIS5.
      pose proof BASE5 as (IMG5 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG5.
      (* [comment removed for export] *)
      assert (POST5 : PNR.binv s5 /\ ec_some M5 fb /\ (length (l ++ [c']) <= length (PNM.b_stk s5))%nat /\ PM.unread (PNM.b_src s5) sm5 <= PM.unread src3 sm3
              /\ (PNM.b_more s5 = 1 -> PNR.btop_pos (PNBO.set_stk s3 (l ++ [c'])) s5 /\ PM.unread (PNM.b_src s5) sm5 < PM.unread src3 sm3)
              /\ PNR.bb_room s5 sm5).
      { destruct POST as (_ & (_ & _ & _ & _ & LE35) & _ & [(v & Hv & Ev & MOv & _ & LEN & INV5)|(Ee & INV5 & (TP & LT))] & BBP5); unfold PNR.o_ec, PMSP.o_ec in *; cbn [pa_off_ec AD PnLayoutS_u.ADDR_S] in *;
          cbn [PNBO.set_stk s3 PNM.with_srcB PNM.b_src] in LE35.
        - split; [exact INV5|]. split; [exists v, (pa_errcat_obj AD); split; [lia| exact Ev]|]. split; [cbn [PNBO.set_stk PNM.b_stk] in LEN; exact LEN|]. split; [exact LE35|].
          split; [intros X; rewrite MOv in X; discriminate| exact (bb_room_keep _ _ _ _ BBP5 LE35 BBR3)].
        - split; [exact INV5|]. split; [exists e1, c1; split; [exact He1| exact Ee]|].
          split; [destruct TP as (lt & ct & ct' & TE1 & TE2 & _); cbn [PNBO.set_stk PNM.b_stk] in TE1; rewrite TE1, TE2, !length_app; cbn; lia|]. split; [exact LE35|].
          split; [| exact (bb_room_keep _ _ _ _ BBP5 LE35 BBR3)].
          intros _. split; [exact TP|]. cbn [PNBO.set_stk s3 PNM.with_srcB PNM.b_src] in LT. exact LT. }
      destruct POST5 as (INV5 & ECS5 & LEN5 & LE35 & PROG5 & BBR5). clear POST.
      destruct Hm23 as [-> | ->]; cbn [Z.eqb Pos.eqb] in *.
      * (* [comment removed for export] *)
        destruct (lp_top LBX sp fb str _ M5 model5 cr5 s5 sm5 ax5 BR5 INV5) as (l5 & c5 & ES5 & OK5 & SH5 & VE5 & TOPC5 & WT5 & DB5 & Hb5 & TOPIN5 & S45 & EAL5 & Hn5).
        set (b5 := PNM.b_sb s5) in *. set (n5 := Z.of_nat (length l5)) in *.
        pose proof OK5 as (O5m & O5l & O5p & O5t & O5i). destruct TOPC5 as (T5m & T5l & T5p & T5t & T5i).
        LeanFeed.pfeed P (PNSPAP.bpaN2_conc fx5 R5 M5 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 45%nat => b5 + 40 * n5 + 40 | 46%nat => cb | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSPAP.aligned; PMK.sc]).
        pvz_hg ltac:(idtac; destruct P as (fx6 & R6 & M6 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG6 & _ & FRZ6 & MS6 & KS6 & Y10' & Y11' & TY6 & MD6)); PMK.pvz_clrT.
        set (c6 := PNM.BS 4 (PNM.bs_len c5) (PNM.bs_pos c5) cb (PNM.bs_idx c5)).
        apply (PNBK2.brel_piece_stk RSEGS AD AN L HI KH 10 LBX sp fb str _ M5 model5 cr5 s5 sm5 ax5 fx5 fx6 R5 R6 0x36d14 0x36e08 M6
                 (fun a => (b5 + 40 * n5 + 40 - 40 <= a < b5 + 40 * n5 + 40 - 40 + 4) \/ (b5 + 40 * n5 + 40 - 16 <= a < b5 + 40 * n5 + 40 - 16 + 1)) l5 [c5] [c6] K ltac:(lia) BR5 FOK INCS MS6 MG6
                 ltac:(intros a Ha N; apply FRZ6; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X])
                 ltac:(intros a; apply PMK.or_dec; apply PMK.rng_dec) ES5); fold b5 n5.
        { intros a Pa. cbn beta in Pa. right. right. clear -Pa TOPIN5. lia. }
        { rewrite length_app. cbn [length]. apply (L5C.u64_at_agree RSEGS M5 M6); [intros i Hi; apply FRZ6; lia|lia|lia|].
          replace (b5 + 40 * Z.of_nat (length l5 + 1)) with (b5 + 40 * n5 + 40) by (unfold n5; lia). replace (fb + 440) with (fb + 40 + 400) by lia. exact VE5. }
        { intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia]. cbn [nth]. rewrite Nat.add_0_r. fold n5.
          unfold PNM.bstate_at. cbn [c6 PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx].
          assert (AG : forall a m', b5 + 40 * n5 + 4 <= a -> a + m' <= b5 + 40 * n5 + 40 -> (a + m' <= b5 + 40 * n5 + 24 \/ b5 + 40 * n5 + 25 <= a) -> L5C.agree_on M5 M6 a m').
          { intros a m' G1 G2 G3 j Gj. apply FRZ6; [lia| lia| clear -G1 G2 G3 Gj; lia]. }
          split; [replace (b5 + 40 * n5) with (b5 + 40 * n5 + 40 - 40) by lia; exact MD6|].
          split; [apply (L5C.u64_at_agree RSEGS M5 M6); [apply AG; lia|lia|lia| exact T5l]|].
          split; [apply (L5C.u64_at_agree RSEGS M5 M6); [apply AG; lia|lia|lia| exact T5p]|].
          split; [replace (b5 + 40 * n5 + 24) with (b5 + 40 * n5 + 40 - 16) by lia; exact TY6|].
          apply (L5C.u64_at_agree RSEGS M5 M6); [apply AG; lia|lia|lia| exact T5i]. }
        { rewrite length_app. cbn [length]. unfold n5 in TOPIN5 |- *. clear -TOPIN5. nia. }
        intros BR6.
        apply (lp_X K LBX sp r fb str R M model cr s sm ax (PNR.bmu s1 sm1) fx6 R6 M6 model5 cr5 (PNBO.set_stk s5 (l5 ++ [c6])) sm5 ax5 CTX KONT IH).
        -- split; [exact BR6|]. split; [lpregs KS6 TK|].
           split; [apply (lp_saved_agree R M5 M6 sp r); [intros a m' G1 G2 j Gj; apply FRZ6; lia|lia|lia| exact SV5]|].
           split; [destruct ECS5 as (e5 & k5 & He5 & E5); exists e5, k5; split; [exact He5| apply (ec_agree M5 M6); [intros i Hi; apply FRZ6; lia|lia|lia| exact E5]]|].
           split; [| intros _; exact BBR5].
           split; [destruct INV5 as (ID & _); exact ID|]. cbn [PNBO.set_stk PNM.b_stk].
           pose proof (shape_cont_cons l5 c5 SH5) as NN5.
           apply (shape_top_mode l5 c5 c6 SH5); [unfold PNM.bstate_ok; cbn; lia| | intros _; cbn; unfold PNR.bmode_cont; lia].
           intros E5. exfalso. rewrite ES5, E5 in LEN5. revert LEN5 NNIL. clear. intros LEN5 NNIL. rewrite !length_app in LEN5. cbn in LEN5. destruct l; [exact (NNIL eq_refl)| cbn in LEN5; lia].
        -- intros MO6. cbn [PNBO.set_stk PNM.b_more PNM.b_src PNM.b_stk] in MO6. destruct (PROG5 MO6) as (TP & LT).
           unfold PNR.bmu. cbn [PNBO.set_stk PNM.b_src PNM.b_stk]. rewrite ES, !bflag_app, Hm. cbn [c6 PNM.bs_mode Z.eqb Pos.eqb orb]. clear -LT UNR3 UN5. lia.
      * (* [comment removed for export] *)
        LeanFeed.pfeed P (PNSPAP.bpaN3_conc fx5 R5 M5 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 46%nat => cb | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSPAP.aligned; PMK.sc]).
        destruct P as (fx6 & R6 & M6 & MG6 & EQ6w & EQ6 & MS6 & KS6 & Y1' & Y10' & Y11' & Y12' & Y13'). assert (EM6 : M6 = M5) by (apply functional_extensionality; exact EQ6w). subst M6.
        apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 10 LBX sp fb str _ M5 model5 cr5 s5 sm5 ax5 fx5 fx6 R5 R6 0x36d90 0x375ec M5 (fun _ => False) K
                 ltac:(lia) BR5 FOK INCS MS6 MG6 ltac:(intros a Ha _; reflexivity) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
        intros BR6. destruct ECS5 as (e5 & k5 & He5 & E5).
        apply (PNBK2.brel_call RSEGS AD AN L HI KH true _ 8 (PNR.bargs_rv AD) PNR.bprog_value 10 LBX sp fb str _ M5 model5 cr5 _ sm5 ax5 fx6 R6 (sp - 112) 0x36da4 k5 e5 K
                 RV ltac:(lia) ltac:(lia) K0 BR6 FOK INCS CRED Y1' ltac:(split; [lia| reflexivity]) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(lia) ltac:(unfold PMSP.pm_scr; lia) (mod16_sub112 sp A16)).
        { unfold PNR.bargs_rv, PNR.o_p, PNR.o_ec, PNR.o_v, PMSP.o_p, PMSP.o_ec, PMSP.o_v. cbn [pa_off_p pa_off_ec pa_off_v AD PnLayoutS_u.ADDR_S].
          rewrite L5K.rl10, L5K.rl11, L5K.rl12, L5K.rl13. split; [exact Y10'|]. split; [exact Y11'|]. split; [exact Y13'|]. split; [exists cb; split; [lia| exact Y12']| exact BBR5]. }
        { exact INV5. }
        { exact E5. }
        { exact He5. }
        { destruct STEP5 as (_ & _ & _ & _ & LE5). cbn [PNBO.set_stk s3 PNM.with_srcB PNM.b_src] in LE5. lia. }
        intros fx7 R7 M7 model7 s7 sm7 ax7 cr7 RP67 POST7 BR7 AG67.
        destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 10 LBX sp fb str _ M7 model7 cr7 s7 sm7 ax7 BR7) as (_ & _ & _ & UN7 & STK7 & MOK7).
        change (PMSP.pm_scr 10) with 32768 in STK7. pose proof (L5C.stk_writable RSEGS _ M7 sp 32768 STK7) as WR7. pose proof MOK7 as (Mh7 & Ml7 & _).
        assert (RG7 : lp_regs R R7 sp fb) by (apply (lp_regs_pres R R6 R7 sp fb); [lpregs KS6 TK| exact RP67]).
        pose proof RG7 as (U2 & U3 & U4 & U8 & U9 & U18 & U19 & U20 & U21 & U22 & U23 & U24 & U25 & UK).
        LeanFeed.pfeed P (PNSPAP.bpaJ2c_conc fx7 R7 M7 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSPAP.aligned; PMK.sc]).
        destruct P as (fx8 & R8 & M8 & MG8 & EQ8w & EQ8 & MS8 & KS8). assert (EM8 : M8 = M7) by (apply functional_extensionality; exact EQ8w). subst M8.
        apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 10 LBX sp fb str _ M7 model7 cr7 s7 sm7 ax7 fx7 fx8 R7 R8 0x36da4 0x36e08 M7 (fun _ => False) K
                 ltac:(lia) BR7 FOK INCS MS8 MG8 ltac:(intros a Ha _; reflexivity) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
        intros BR8.
        apply (lp_X K LBX sp r fb str R M model cr s sm ax (PNR.bmu s1 sm1) fx8 R8 M7 model7 cr7 s7 sm7 ax7 CTX KONT IH).
        -- split; [exact BR8|]. split; [lpregs KS8 UK|].
           split; [apply (lp_saved_agree R M5 M7 sp r); [intros a m' G1 G2; apply AG67; lia|lia|lia| exact SV5]|].
           destruct POST7 as (_ & _ & _ & [(v & Hv & Ev & MOv & _ & _ & INV7)|(Ee & INV7 & _)] & BBP7); unfold PNR.o_ec, PMSP.o_ec in *; cbn [pa_off_ec AD PnLayoutS_u.ADDR_S] in *.
           ** split; [exists v, (pa_errcat_obj AD); split; [lia| exact Ev]|]. split; [exact INV7| intros MO7; exact (BBP7 BBR5 MO7)].
           ** split; [exists e5, k5; split; [exact He5| exact Ee]|]. split; [exact INV7| intros MO7; exact (BBP7 BBR5 MO7)].
        -- intros MO7. destruct POST7 as (_ & STEP67 & _ & [(v & Hv & Ev & MOv & _)|(Ee & INV7 & PROG)] & _); [rewrite MOv in MO7; discriminate|].
           destruct STEP67 as (_ & _ & _ & _ & LE67).
           unfold PNR.bmu. rewrite ES, bflag_app, Hm. cbn [Z.eqb Pos.eqb orb]. pose proof (bflag_range (PNM.b_stk s7)) as FR.
           clear -LE67 LE35 UNR3 FR UN7. lia.
Qed.


(* [comment removed for export] *)
Lemma lp_loop K LBX sp r fb str (R : bvmap 5 word) (M : mem) model cr s sm ax :
  lp_ctx K LBX sp r fb str R cr s sm -> lp_kont K LBX sp r fb str R M model cr s sm ax ->
  forall n, forall (fx1 : FPState) R1 (M1 : mem) model1 cr1 s1 sm1 ax1,
    lp_linv LBX sp r fb str (BENT M model cr s sm ax) R R1 M1 model1 cr1 s1 sm1 ax1 -> (PNM.b_more s1 = 1 -> 0 <= PNR.bmu s1 sm1 <= n) ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x36c58 M1 model1) K.
Proof.
  intros CTX KONT n. pattern n. apply (well_founded_ind (Zwf_well_founded 0)). clear n.
  intros n IHn fx1 R1 M1 model1 cr1 s1 sm1 ax1 LI MU. head_intro CTX LI.
  destruct (lp_headfacts K LBX sp r fb str R M model cr s sm ax fx1 R1 M1 model1 cr1 s1 sm1 ax1 CTX LI) as (PA1 & STK1 & MOK1 & LE1 & UN1 & VIS1 & IMG1 & WP1 & AL40 & AL464).
  pose proof STK1 as (A16 & SLO & SHI & STOP & SDEF1). pose proof MOK1 as (Mh1 & Ml1 & Mm1).
  pose proof (L5C.stk_floor _ M1 sp 32768 STK1) as SFL. pose proof (L5C.stk_writable RSEGS _ M1 sp 32768 STK1) as WR1.
  pose proof LI as (BR1 & RG1 & SV1 & ECS1 & INV1 & _).
  pose proof RG1 as (X2 & X3 & X4 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & XK).
  pose proof PA1 as (_ & _ & _ & MO & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M01 & _).
  destruct M01 as [MO0|MO1]; rewrite ?MO0, ?MO1 in MO.
  - (* [comment removed for export] *)
    pose proof SV1 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88).
    pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 8))) as BU8. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 9))) as BU9.
    pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 18))) as BU18. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 19))) as BU19.
    pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 20))) as BU20. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 21))) as BU21.
    pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 22))) as BU22. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 23))) as BU23.
    pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 24))) as BU24. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 25))) as BU25.
    LeanFeed.pfeed P (PNSPAP.bpaHX_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 50%nat => r
                 | 51%nat => bv_unsigned (getr R (PMK.reg 8)) | 52%nat => bv_unsigned (getr R (PMK.reg 9)) | 53%nat => bv_unsigned (getr R (PMK.reg 18))
                 | 54%nat => bv_unsigned (getr R (PMK.reg 19)) | 55%nat => bv_unsigned (getr R (PMK.reg 20)) | 56%nat => bv_unsigned (getr R (PMK.reg 21))
                 | 57%nat => bv_unsigned (getr R (PMK.reg 22)) | 58%nat => bv_unsigned (getr R (PMK.reg 23)) | 59%nat => bv_unsigned (getr R (PMK.reg 24))
                 | 60%nat => bv_unsigned (getr R (PMK.reg 25)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSPAP.aligned; PMK.sc]).
    pvz_hg ltac:(idtac; destruct P as (fx2 & R2 & M2 & pvzP); PMK.pvz_lin pvzP;
                  destruct pvzP as (MG2 & EQ2w & EQ2 & MS2 & KS2 & Y1 & Y2 & Y8 & Y9 & Y10 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25)); PMK.pvz_clrT.
    assert (EM2 : M2 = M1) by (apply functional_extensionality; exact EQ2w). subst M2.
    apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 10 LBX sp fb str _ M1 model1 cr1 s1 sm1 ax1 fx1 fx2 R1 R2 0x36c58 0x36e54 M1 (fun _ => False) K
             ltac:(lia) BR1 FOK INCS MS2 MG2 ltac:(intros a Ha _; reflexivity) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
    intros BR2.
    apply (lp_fin K LBX sp r fb str R M model cr s sm ax fx2 R2 M1 model1 cr1 s1 sm1 ax1 CTX KONT BR2 ECS1 Y1 Y2);
      [PMK.rk| PMK.rk| exact Y8| exact Y9| exact Y18| exact Y19| exact Y20| exact Y21| exact Y22| exact Y23| exact Y24| exact Y25|].
    intros k Hk. rewrite (KS2 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). apply XK. exact Hk.
  - (* [comment removed for export] *)
    pose proof (MU MO1) as MU1.
    assert (IH : lp_IH K LBX sp r fb str R M model cr s sm ax (PNR.bmu s1 sm1)).
    { intros fx2 R2 M2 model2 cr2 s2 sm2 ax2 LI2 MU2.
      apply (IHn (PNR.bmu s1 sm1 - 1) ltac:(unfold Zwf; clear -MU1; lia) fx2 R2 M2 model2 cr2 s2 sm2 ax2 LI2). intros X. pose proof (MU2 X). lia. }
    destruct (lp_top LBX sp fb str _ M1 model1 cr1 s1 sm1 ax1 BR1 INV1) as (l & c & ES & OKc & _).
    pose proof OKc as (OKm & _).
    assert (CASES : PNM.bs_mode c = 0 \/ PNM.bs_mode c = 1 \/ PNM.bs_mode c = 2 \/ PNM.bs_mode c = 3 \/ PNM.bs_mode c = 4) by lia.
    destruct CASES as [Hm|[Hm|[Hm|[Hm|Hm]]]].
    + exact (lp_mode0 K LBX sp r fb str R M model cr s sm ax fx1 R1 M1 model1 cr1 s1 sm1 ax1 l c CTX KONT IH LI MO1 ES Hm).
    + exact (lp_mode1 K LBX sp r fb str R M model cr s sm ax fx1 R1 M1 model1 cr1 s1 sm1 ax1 l c CTX KONT LI MO1 ES Hm).
    + exact (lp_mode23 K LBX sp r fb str R M model cr s sm ax fx1 R1 M1 model1 cr1 s1 sm1 ax1 l c 2 CTX KONT IH LI MO1 ES Hm ltac:(left; reflexivity)).
    + exact (lp_mode23 K LBX sp r fb str R M model cr s sm ax fx1 R1 M1 model1 cr1 s1 sm1 ax1 l c 3 CTX KONT IH LI MO1 ES Hm ltac:(right; reflexivity)).
    + exact (lp_mode4 K LBX sp r fb str R M model cr s sm ax fx1 R1 M1 model1 cr1 s1 sm1 ax1 l c CTX KONT IH LI MO1 ES Hm).
Qed.

(* [comment removed for export] *)
Theorem parse_ok : PNRS.parse_spec L HI.
Proof.
  unfold PNRS.parse_spec, PNR.parse_spec.
  intros fx R M model K LBX cr sp r fb cat e s str sm ax HH MOK K0 ENT FOK ARGS RPRE INCS INV EC0 He UNR BB0 CRED KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2.
  pose proof MOK as (Mh & Ml & Mm). change (PMSP.pm_scr 10) with 32768 in STK. pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  destruct ARGS as (A10 & A11 & A12). rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
  unfold PNR.o_p, PNR.o_ec, PNR.o_v, PMSP.o_p, PMSP.o_ec, PMSP.o_v in A10, A11, A12, EC0. cbn [pa_off_p pa_off_ec pa_off_v AD PnLayoutS_u.ADDR_S] in A10, A11, A12, EC0.
  pose proof (L5C.stk_floor _ M sp 32768 STK) as SFL. pose proof (L5C.stk_writable RSEGS _ M sp 32768 STK) as WR.
  assert (AL40 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
  assert (AL464 : (fb + 464) mod 8 = 0) by (replace (fb + 464) with (fb + 8 * 58) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
  assert (AL472 : (fb + 472) mod 8 = 0) by (replace (fb + 472) with (fb + 8 * 59) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
  pose proof (PNBK.brel_init RSEGS AD AN L HI 10 LBX sp fb str M model cr s sm ax ltac:(lia) RPRE HH STK MOK) as BR0.
  change (PMSP.pm_scr 10) with 32768 in BR0.
  assert (CTX : lp_ctx K LBX sp r fb str R cr s sm).
  { split; [exact K0|]. split; [exact FOK|]. split; [exact INCS|]. split; [exact RAok|]. split; [exact Rsp|]. split; [exact Rgp|]. split; [exact Rtp|]. split; [exact CRED| exact UNR]. }
  assert (KONT' : lp_kont K LBX sp r fb str R M model cr s sm ax) by exact KONT.
  pose proof RPRE as (PA0 & IA0 & VIS0 & _ & BASE0 & _). unfold PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at in PA0, IA0, VIS0.
  cbn [pa_off_p pa_off_is pa_off_v pa_vp_visitor AD PnLayoutS_u.ADDR_S] in PA0, IA0, VIS0.
  pose proof BASE0 as (IMG0 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG0.
  pose proof PA0 as (_ & PD0 & _ & _ & DN0 & _ & _ & _ & SRC0 & _). unfold PNM.OFF_SRC in SRC0. pose proof SRC0 as (SP0 & _).
  pose proof INV as (ID0 & _). rewrite ID0 in DN0.
  assert (WP : L5.writable RSEGS M (fb + 40) 416) by (apply (L5C.writable_of_defined RSEGS); [exact PD0|lia|lia]).
  pose proof IA0 as (IV0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IOS0 & _). cbn [pa_vp_iss AD PnLayoutS_u.ADDR_S] in IV0.
  pose proof IOS0 as (_ & IST0 & _ & _ & _ & _ & _ & _ & ST02).
  unfold PMSP.cfg. cbn [PNL.pn_parse AN PnLayoutS_u.NADDR_S].
  (* [comment removed for export] *)
  assert (ENTRY : exists (fx1 : FPState) R1 M1,
            msteps RSEGS (@mkst fx R (Z_to_bv 64 0x36bc0) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0x36c58) M1 (seg_rom RSEGS)) /\ mem_grows M M1
            /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 112 <= i < sp - 112 + 112) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
            /\ lp_regs R R1 sp fb /\ lp_saved R M1 sp r).
  { destruct ST02 as [ST|ST]; rewrite ST in IST0.
    - LeanFeed.pfeed P (PNSPAP.bpaE0_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 36%nat => fb + 472 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSPAP.aligned; PMK.sc | replace (fb + 40 + 256) with (fb + 40 + 16 + 240) by lia; exact SP0 | replace (fb + 472 + 152) with (fb + 472 + 120 + 32) by lia; exact IST0]).
      pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
                    destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & X2 & X8 & X9 & X10 & _ & X12 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)); PMK.pvz_clrT.
      exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [exact FRZ1|].
      split; [unfold lp_regs; split; [exact X2|]; split; [PMK.rk|]; split; [PMK.rk|]; split; [exact X8|]; split; [exact X9|]; split; [exact X18|]; split; [PMK.rk|];
              split; [exact X20|]; split; [exact X21|]; split; [exact X22|]; split; [exact X23|]; split; [exact X24|]; split; [exact X25|];
              intros k Hk; apply KS1; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto|].
      unfold lp_saved. rewrite Rra in C8. rewrite L5.unsigned_lit in C8 by lia.
      split; [exact C8|]. split; [exact C16|]. split; [exact C24|]. split; [exact C32|]. split; [exact C40|]. split; [exact C48|].
      split; [exact C56|]. split; [exact C64|]. split; [exact C72|]. split; [exact C80| exact C88].
    - LeanFeed.pfeed P (PNSPAP.bpaE2_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 36%nat => fb + 472 | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSPAP.aligned; PMK.sc | replace (fb + 40 + 256) with (fb + 40 + 16 + 240) by lia; exact SP0 | replace (fb + 472 + 152) with (fb + 472 + 120 + 32) by lia; exact IST0]).
      pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
                    destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & X2 & X8 & X9 & X10 & _ & X12 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)); PMK.pvz_clrT.
      exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [exact FRZ1|].
      split; [unfold lp_regs; split; [exact X2|]; split; [PMK.rk|]; split; [PMK.rk|]; split; [exact X8|]; split; [exact X9|]; split; [exact X18|]; split; [PMK.rk|];
              split; [exact X20|]; split; [exact X21|]; split; [exact X22|]; split; [exact X23|]; split; [exact X24|]; split; [exact X25|];
              intros k Hk; apply KS1; revert Hk; clear; intros Hk; cbn in Hk |- *; tauto|].
      unfold lp_saved. rewrite Rra in C8. rewrite L5.unsigned_lit in C8 by lia.
      split; [exact C8|]. split; [exact C16|]. split; [exact C24|]. split; [exact C32|]. split; [exact C40|]. split; [exact C48|].
      split; [exact C56|]. split; [exact C64|]. split; [exact C72|]. split; [exact C80| exact C88]. }
  destruct ENTRY as (fx1 & R1 & M1 & MS1 & MG1 & FRZ1 & RG1 & SV1).
  change (mkCfg (@mkst fx R (Z_to_bv 64 0x36bc0) M (seg_rom RSEGS)) model) with (@PMSP.cfg RSEGS fx R 0x36bc0 M model).
  apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 10 LBX sp fb str _ M model cr s sm ax fx fx1 R R1 0x36bc0 0x36c58 M1 (fun a => sp - 112 <= a < sp - 112 + 112) K
           ltac:(lia) BR0 FOK INCS MS1 MG1 FRZ1 ltac:(intros a; apply PMK.rng_dec) ltac:(intros a Pa; cbn beta in Pa; unfold PMSP.pm_scr; clear -Pa; lia)).
  intros BR1.
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 10 LBX sp fb str _ M model cr s sm ax BR0) as (_ & _ & _ & UN0 & _).
  pose proof (bflag_range (PNM.b_stk s)) as FR0.
  apply (lp_loop K LBX sp r fb str R M model cr s sm ax CTX KONT' (PNR.bmu s sm) fx1 R1 M1 model cr s sm ax); [| intros _; unfold PNR.bmu; lia].
  split; [exact BR1|]. split; [exact RG1|]. split; [exact SV1|].
  split; [exists e, cat; split; [exact He| apply (ec_agree M M1); [intros i Hi; apply FRZ1; lia|lia|lia| exact EC0]]|]. split; [exact INV| intros _; exact BB0].
Qed.

End WithHeap.
End PNSPA.
