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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnModelFacts PnStatics PnKeep PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj PnBrKit PnBrKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnBrKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnSzKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSEndP_u
     Bs0_code_36760_36764_u Bs0_code_37038_3703c_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSEND.
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
Lemma mod16_sub48 sp : sp mod 16 = 0 -> (sp - 48) mod 16 = 0.
Proof. intros H. replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact H. Qed.
Lemma bax_cat_add ax : PNST.bax_cat (PNST.bax_add_cat ax) = true.
Proof. destruct ax; reflexivity. Qed.

(* [comment removed for export] *)
Lemma bstack_shape_pop l c top c' :
  PNR.bstack_shape (l ++ [c; top]) -> PNM.bstate_ok c' -> PNM.bs_mode c' = PNM.bs_mode c -> PNR.bstack_shape (l ++ [c']).
Proof.
  intros (L1 & L2 & B0 & CT & OK) OK' Hm. unfold PNR.bstack_shape. rewrite length_app in *. cbn [length] in *.
  split; [lia|]. split; [lia|].
  split.
  { destruct l as [|x l']; cbn in B0 |- *; [rewrite Hm; exact B0| exact B0]. }
  split.
  { intros i Hi. destruct (Nat.eq_dec i (length l)) as [->|NE].
    - rewrite nth_middle. rewrite Hm. pose proof (CT (length l) ltac:(lia)) as X. rewrite app_nth2 in X by lia. rewrite Nat.sub_diag in X. exact X.
    - rewrite app_nth1 by lia. pose proof (CT i ltac:(lia)) as X. rewrite app_nth1 in X by lia. exact X. }
  intros i Hi. destruct (Nat.eq_dec i (length l)) as [->|NE].
  - rewrite nth_middle. exact OK'.
  - rewrite app_nth1 by lia. pose proof (OK i ltac:(lia)) as X. rewrite app_nth1 in X by lia. exact X.
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KH := PNBKS.kh_S L HI LY HIok.
Let KL := PMKS.klayout_S L LY.
Abbreviation brel := (PNBK.brel RSEGS AD AN L HI 3).
Abbreviation pot := (PNR.pot_bparser L).

Hypothesis MKE : PNRS.make_ec_spec L HI.

(* [comment removed for export] *)
Definition ed_kont (K : list event -> Prop) (LBX : list (Z * Z)) (sp r fb cat e : Z) (str : PM.vstr) (R : bvmap 5 word)
           (M : mem) (model : Model) (cr : credit) (s : PNM.bpst) (sm : PM.strm) (ax : PNST.bax) : Prop :=
  forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (s' : PNM.bpst) (sm' : PM.strm) (ax' : PNST.bax) (cr' : credit),
      regs_preserved R R' ->
      PNR.brun_post RSEGS AD AN false PNR.bprog_pop R' M' fb s s' str sm sm' ax ax' cat e ->
      L5C.hpres L LBX sp (PMSP.pm_scr 3) (PNR.W_brun AD AN fb) M M' ->
      PMSP.credit_keep cr cr' (pot s) (pot s') ->
      model_but_vm model model' -> hi_heap HI (PNM.bparser_own s' ++ LBX) cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.
Definition ed_ctx (K : list event -> Prop) (LBX : list (Z * Z)) (sp r fb : Z) (str : PM.vstr) (R : bvmap 5 word) (cr : credit) (s : PNM.bpst) : Prop :=
  K [] /\ PMSP.frame_ok AD L sp fb /\ incl (PM.vs_own str) LBX /\ L5.ra_ok r
  /\ getr R (PMK.reg 2) = Z_to_bv 64 sp /\ getr R (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) /\ getr R (PMK.reg 4) = Z_to_bv 64 (pa_tp AD)
  /\ PMSP.credit_le (pot s) cr.

(* [comment removed for export] *)
Lemma ed_fin (pcret : Z) K LBX sp r fb cat e str (R : bvmap 5 word) (M : mem) model cr s sm ax
      (fx5 : FPState) R5 (M5 : mem) model5 cr5 s5 sm5 ax5 :
  (forall fx Rx Mx, getr Rx (PMK.reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 ->
      msteps RSEGS (@mkst fx Rx (Z_to_bv 64 pcret) Mx (seg_rom RSEGS)) (@mkst fx Rx (Z_to_bv 64 r) Mx (seg_rom RSEGS))) ->
  ed_ctx K LBX sp r fb str R cr s -> ed_kont K LBX sp r fb cat e str R M model cr s sm ax ->
  brel LBX sp fb str (BENT M model cr s sm ax) (BENT M5 model5 cr5 s5 sm5 ax5) ->
  getr R5 (PMK.reg 1) = Z_to_bv 64 r -> getr R5 (PMK.reg 2) = Z_to_bv 64 sp ->
  getr R5 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R5 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R5 (PMK.reg 8) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 8))) -> getr R5 (PMK.reg 9) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 9))) ->
  (forall k, In k [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (PMK.reg k) = getr R (PMK.reg k)) ->
  (   ((exists v, 1 <= v <= 64 /\ PMSP.ec_at RSEGS M5 (fb + 16) v (pa_errcat_obj AD)) /\ PNM.b_more s5 = 0 /\ PNST.bax_cat ax5 = true
       /\ (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat /\ PNR.binv s5)
   \/ (PMSP.ec_at RSEGS M5 (fb + 16) e cat /\ PNR.binv s5 /\ PNR.bprog_pop R5 M5 s s5 sm sm5)) ->
  PNM.b_bb s5 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 pcret M5 model5) K.
Proof.
  intros RET (K0 & FOK & INCS & (Hr1 & Hr2) & Rsp & Rgp & Rtp & CRED) KONT BR Y1 Y2 Y3 Y4 Y8 Y9 YK POST BB.
  pose proof BR as (RP & STEP & AXL & HP & CK & MB & HH & STK & MOK). cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax] in *.
  pose proof MOK as (Mh & Ml & Mm).
  eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| exact (RET fx5 R5 M5 Y1 Hr1 Hr2)|].
  apply (KONT fx5 R5 M5 model5 s5 sm5 ax5 cr5).
  - apply PMK.preserved_by_index. intros k Hk. cbn in Hk.
    destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
      first [ rewrite Y2, Rsp; reflexivity | rewrite Y3, Rgp; reflexivity | rewrite Y4, Rtp; reflexivity
            | rewrite Y8; apply Z_to_bv_bv_unsigned | rewrite Y9; apply Z_to_bv_bv_unsigned | apply YK; cbn; tauto ].
  - unfold PNR.brun_post. split; [exact RP|]. split; [exact STEP|]. split; [exact AXL|].
    unfold PNR.o_ec, PMSP.o_ec. cbn [pa_off_ec AD PnLayoutS_u.ADDR_S].
    split; [| exact BB].
    destruct POST as [((v & Hv & E1) & MO & CAT & LEN & INV')|(E0 & INV & PROG)].
    + left. exists v. split; [exact Hv|]. split; [exact E1|]. split; [exact MO|]. split; [exact CAT|]. split; [exact LEN| exact INV'].
    + right. split; [exact E0|]. split; [exact INV| exact PROG].
  - exact HP.
  - exact CK.
  - exact MB.
  - exact HH.
Qed.

(* [comment removed for export] *)
Lemma ed_stk LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 l c top :
  brel LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) -> PNR.binv s1 -> PNM.b_stk s1 = l ++ [c; top] ->
  PNM.bstate_ok c /\ PNM.bstate_ok top
  /\ L5.u64_at RSEGS M1 (fb + 40 + 392) (PNM.b_sb s1)
  /\ L5.u64_at RSEGS M1 (fb + 40 + 400) (PNM.b_sb s1 + 40 * (Z.of_nat (length l) + 2))
  /\ L5.u64_at RSEGS M1 (PNM.b_sb s1 + 40 * (Z.of_nat (length l) + 2) - 32) (PNM.bs_len top)
  /\ L5.u64_at RSEGS M1 (PNM.b_sb s1 + 40 * (Z.of_nat (length l) + 2) - 24) (PNM.bs_pos top)
  /\ L5.u64_at RSEGS M1 (PNM.b_sb s1 + 40 * (Z.of_nat (length l) + 2) - 64) (PNM.bs_pos c)
  /\ L5.writable RSEGS M1 (PNM.b_sb s1 + 40 * (Z.of_nat (length l) + 2) - 64) 8
  /\ PNM.bstate_at RSEGS M1 (PNM.b_sb s1 + 40 * Z.of_nat (length l)) c
  /\ 4096 <= PNM.b_sb s1 /\ PNM.b_sb s1 + 40 * (Z.of_nat (length l) + 2) <= PNM.b_sb s1 + 40 * 2 ^ PNM.b_sk s1
  /\ PNM.b_sb s1 + 40 * 2 ^ PNM.b_sk s1 <= hl_sptop L - 2 ^ 23 /\ PNM.b_sb s1 mod 8 = 0 /\ Z.of_nat (length l) + 2 <= 1025
  /\ L5.defined M1 (PNM.b_sb s1) (40 * 2 ^ PNM.b_sk s1).
Proof.
  intros BR INV ES.
  destruct (PNBK2.brel_blocks RSEGS AD AN L HI KH 3 LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR) as (BRG & OWNB & APQ).
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 3 LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR) as (PA1 & IA1 & GR1 & UN1 & STK & MOK).
  change (PMSP.pm_scr 3) with 18432 in STK. pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof INV as (_ & (L1 & L2 & _ & _ & OKs)). unfold PNM.MAX_DEPTH in L2.
  rewrite ES, length_app in L2. cbn [length] in L2.
  pose proof (OKs (length l) ltac:(rewrite ES, length_app; cbn; lia)) as OKc. rewrite ES, nth_middle in OKc.
  pose proof (OKs (length l + 1)%nat ltac:(rewrite ES, length_app; cbn; lia)) as OKt. rewrite ES, app_nth2 in OKt by lia. rewrite Nat.add_comm, Nat.add_sub in OKt. cbn [nth] in OKt.
  split; [exact OKc|]. split; [exact OKt|].
  pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SV1 & _). unfold PNM.OFF_STK in SV1.
  pose proof SV1 as (V0 & V8 & _ & Hk & Hlen & Hal & DB & _ & _ & EL). unfold PNM.BSZ in *.
  rewrite ES, length_app in Hlen, EL, V8. cbn [length] in Hlen, EL, V8.
  set (b := PNM.b_sb s1) in *. set (k := PNM.b_sk s1) in *. set (n := Z.of_nat (length l)) in *.
  assert (Hn : 0 <= n /\ n + 2 <= 2 ^ k) by (unfold n; lia).
  assert (TOPIN : b + 40 * (n + 2) <= b + 40 * 2 ^ k) by nia.
  assert (Bs : In (b, 40 * 2 ^ k) (PNM.bparser_own s1)).
  { unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own, b, k. apply in_or_app. right. cbn. auto. }
  destruct (OWNB _ _ Bs) as (S0 & S4). unfold hl_ceil in S4.
  split; [exact V0|].
  split; [replace (b + 40 * (n + 2)) with (b + 40 * Z.of_nat (length l + 2)) by (unfold n; lia); replace (fb + 40 + 400) with (fb + 40 + 392 + 8) by lia; exact V8|].
  pose proof (EL (length l) ltac:(lia)) as Ec. rewrite nth_middle in Ec. fold n in Ec.
  pose proof (EL (length l + 1)%nat ltac:(lia)) as Et. rewrite app_nth2 in Et by lia. rewrite Nat.add_comm, Nat.add_sub in Et. cbn [nth] in Et.
  replace (Z.of_nat (1 + length l)) with (n + 1) in Et by (unfold n; lia).
  destruct Et as (_ & Tl & Tp & _ & _). pose proof Ec as (_ & _ & Cp & _ & _).
  split; [replace (b + 40 * (n + 2) - 32) with (b + 40 * (n + 1) + 8) by lia; exact Tl|].
  split; [replace (b + 40 * (n + 2) - 24) with (b + 40 * (n + 1) + 16) by lia; exact Tp|].
  split; [replace (b + 40 * (n + 2) - 64) with (b + 40 * n + 16) by lia; exact Cp|].
  split; [apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M1 b (40 * 2 ^ k)); [exact DB|lia|lia]|lia|lia]|].
  split; [exact Ec|].
  split; [lia|]. split; [exact TOPIN|]. split; [lia|]. split; [apply PMPK.m16_8; exact Hal|]. split; [lia| exact DB].
Qed.

Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem end_document_ok : PNRS.end_document_spec L HI.
Proof.
  unfold PNRS.end_document_spec, PNR.end_document_spec, PNR.brun_spec.
  intros fx R M model K LBX cr sp r fb cat e s str sm ax HH MOK K0 ENT FOK ARGS RPRE INCS INV EC0 He UNR CRED KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2.
  pose proof MOK as (Mh & Ml & Mm). change (PMSP.pm_scr 3) with 18432 in STK. pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  destruct ARGS as ((A10 & A11 & A12) & HLEN). rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
  unfold PNR.o_p, PNR.o_ec, PNR.o_v, PMSP.o_p, PMSP.o_ec, PMSP.o_v in A10, A11, A12, EC0. cbn [pa_off_p pa_off_ec pa_off_v AD PnLayoutS_u.ADDR_S] in A10, A11, A12, EC0.
  pose proof (L5C.stk_floor _ M sp 18432 STK) as SFL. pose proof (L5C.stk_writable RSEGS _ M sp 18432 STK) as WR.
  assert (AL40 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
  assert (AL464 : (fb + 464) mod 8 = 0) by (replace (fb + 464) with (fb + 8 * 58) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
  pose proof (PNBK.brel_init RSEGS AD AN L HI 3 LBX sp fb str M model cr s sm ax ltac:(lia) RPRE HH STK MOK) as BR0.
  change (PMSP.pm_scr 3) with 18432 in BR0.
  assert (CTX : ed_ctx K LBX sp r fb str R cr s).
  { split; [exact K0|]. split; [exact FOK|]. split; [exact INCS|]. split; [exact RAok|]. split; [exact Rsp|]. split; [exact Rgp|]. split; [exact Rtp| exact CRED]. }
  assert (KONT' : ed_kont K LBX sp r fb cat e str R M model cr s sm ax) by exact KONT.
  assert (RET : forall fx Rx Mx, getr Rx (PMK.reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 ->
            msteps RSEGS (@mkst fx Rx (Z_to_bv 64 0x3754c) Mx (seg_rom RSEGS)) (@mkst fx Rx (Z_to_bv 64 r) Mx (seg_rom RSEGS))).
  { intros fx0 Rx Mx X1 H1 H2. apply (PMK.ret_to RSEGS fx0 Rx Mx 0x3754c W_36804 r F_36804 eq_refl D_36804 X1 H1 H2). }
  unfold PNRS.make_ec_spec in MKE.
  pose proof RPRE as (PA0 & _ & VIS0 & _ & BASE0 & _). unfold PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at in PA0, VIS0.
  cbn [pa_off_p pa_off_is pa_off_v pa_vp_visitor AD PnLayoutS_u.ADDR_S] in PA0, VIS0.
  pose proof BASE0 as (IMG0 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG0.
  pose proof PA0 as (_ & PD0 & _ & _ & _ & CM0 & ML0 & _).
  assert (WP : L5.writable RSEGS M (fb + 40) 416) by (apply (L5C.writable_of_defined RSEGS); [exact PD0|lia|lia]).
  (* [comment removed for export] *)
  pose proof INV as (ID & SH). pose proof SH as (L1 & _).
  destruct (exists_last (l := PNM.b_stk s) ltac:(intros X; rewrite X in HLEN; cbn in HLEN; lia)) as (l1 & top & ES1).
  destruct (exists_last (l := l1) ltac:(intros X; rewrite ES1, X in HLEN; cbn in HLEN; lia)) as (l & c & ES2). rewrite ES2, <- app_assoc in ES1. cbn [app] in ES1. clear ES2 l1.
  destruct (ed_stk LBX sp fb str _ M model cr s sm ax l c top BR0 INV ES1) as (OKc & OKt & V0 & V8 & TL & TP & CP & WCP & EC & Hb & TOPIN & S4 & ALb & Hn & DB0).
  set (b := PNM.b_sb s) in *. set (n := Z.of_nat (length l)) in *.
  pose proof OKt as (_ & TLr & TPr & _). pose proof OKc as (OKm & OKl & CPr & OKty & OKi).
  assert (ALn : (40 * (n + 2)) mod 8 = 0) by (replace (40 * (n + 2)) with (0 + 8 * (5 * (n + 2))) by lia; apply PMPK.m8_add; reflexivity).
  unfold PMSP.cfg. cbn [PNL.pn_end_document AN PnLayoutS_u.NADDR_S].
  LeanFeed.pfeed P (PNSENDP.bedA_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 40%nat => b | 41%nat => 40 * (n + 2)
               | 42%nat => PNM.bs_len top | 43%nat => PNM.bs_pos top | 44%nat => PNM.bs_pos c | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSENDP.aligned; PMK.sc
                         | rewrite (PNSZ.size64 _ (n + 2) eq_refl ltac:(lia)); lia | rewrite (PNSZ.size32 _ (n + 2) eq_refl ltac:(lia)); lia]).
  pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
                destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & X1 & X2 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & MO1 & C24 & C16 & C8)); PMK.pvz_clrT.
  change (mkCfg (@mkst fx R (Z_to_bv 64 0x3745c) M (seg_rom RSEGS)) model) with (@PMSP.cfg RSEGS fx R 0x3745c M model).
  apply (PNBK2.brel_piece_more RSEGS AD AN L HI KH 3 LBX sp fb str _ M model cr s sm ax fx fx1 R R1 0x3745c 0x37510 M1
           (fun a => (sp - 48 <= a < sp - 48 + 48) \/ (fb + 40 + 8 <= a < fb + 40 + 8 + 1)) 1 K ltac:(lia) BR0 FOK INCS MS1 MG1
           ltac:(intros a Ha N; apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X])
           ltac:(intros a; apply PMK.or_dec; apply PMK.rng_dec)
           ltac:(intros a Pa; cbn beta in Pa; unfold PMSP.pm_scr; clear -Pa; lia) ltac:(replace (fb + 48) with (fb + 40 + 8) by lia; exact MO1) ltac:(right; reflexivity)).
  intros BR1.
  assert (AG01 : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (a + m <= sp - 48 \/ sp <= a) -> (a + m <= fb + 48 \/ fb + 49 <= a) -> L5C.agree_on M M1 a m).
  { intros a m H1 H2 H3 H4 i Hi. apply FRZ1; lia. }
  assert (EC1 : PMSP.ec_at RSEGS M1 (fb + 16) e cat) by (apply (ec_agree M M1); [apply AG01; lia|lia|lia| exact EC0]).
  rewrite Rra in C8. rewrite L5.unsigned_lit in C8 by lia.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 8))) as BU8. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 9))) as BU9.
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 3 LBX sp fb str _ M1 model cr _ sm ax BR1) as (PA1 & _ & _ & _ & STK1 & _).
  change (PMSP.pm_scr 3) with 18432 in STK1. pose proof (L5C.stk_writable RSEGS _ M1 sp 18432 STK1) as WR1.
  assert (WP1 : L5.writable RSEGS M1 (fb + 40) 416) by (destruct PA1 as (_ & D & _); apply (L5C.writable_of_defined RSEGS); [exact D|lia|lia]).
  destruct (Z.eq_dec (PNM.bs_pos top) (PNM.bs_len top)) as [EQ|NE].
  - (* [comment removed for export] *)
    destruct (ed_stk LBX sp fb str _ M1 model cr _ sm ax l c top BR1 ltac:(cbn [PNBO.set_more PNR.binv PNM.b_more PNM.b_done PNM.b_stk]; split; [exact ID| exact SH]) ES1)
      as (_ & _ & U0 & U8 & UL & UP & UC & WUC & EC1' & _ & _ & _ & _ & _ & DB1). cbn [PNBO.set_more PNM.b_sb PNM.b_sk] in U0, U8, UL, UP, UC, WUC, EC1', DB1. fold b in U0, U8, UL, UP, UC, WUC, EC1', DB1.
    rewrite EQ in UP.
    rewrite EQ in X11.
    LeanFeed.pfeed P (PNSENDP.bedT_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 36%nat => r
                 | 37%nat => bv_unsigned (getr R (PMK.reg 8)) | 38%nat => bv_unsigned (getr R (PMK.reg 9)) | 40%nat => b | 41%nat => 40 * (n + 2)
                 | 42%nat => PNM.bs_len top | 43%nat => PNM.bs_len top | 44%nat => PNM.bs_pos c | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSENDP.aligned; PMK.sc]).
    pvz_hg ltac:(idtac; destruct P as (fx2 & R2 & M2 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG2 & _ & FRZ2 & MS2 & KS2 & Y1 & Y2 & Y8 & Y9 & Y11 & Y12 & Y13 & VE2)); PMK.pvz_clrT.
    destruct (PMCG.u64_of_defined RSEGS M2 (b + 40 * n + 16) ltac:(lia) ltac:(lia)) as (v' & Hv' & CP2).
    { apply (L5.defined_grows M1 M2 _ _ MG2). apply (L5.defined_sub M1 b (40 * 2 ^ PNM.b_sk s)); [exact DB1| lia| clear -Hn TOPIN; lia]. }
    set (c' := PNM.BS (PNM.bs_mode c) (PNM.bs_len c) v' (PNM.bs_type c) (PNM.bs_idx c)).
    apply (PNBK2.brel_piece_stk RSEGS AD AN L HI KH 3 LBX sp fb str _ M1 model cr _ sm ax fx1 fx2 R1 R2 0x37510 0x3754c M2
             (fun a => (fb + 40 + 400 <= a < fb + 40 + 400 + 8) \/ (b + 40 * (n + 2) - 64 <= a < b + 40 * (n + 2) - 64 + 8)) l [c; top] [c'] K ltac:(lia) BR1 FOK INCS MS2 MG2
             ltac:(intros a Ha N; apply FRZ2; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X])
             ltac:(intros a; apply PMK.or_dec; apply PMK.rng_dec)); cbn [PNBO.set_more PNM.b_stk PNM.b_sb PNM.b_sk]; fold b.
    { exact ES1. }
    { intros a Pa. cbn beta in Pa. right. clear -Pa Hn TOPIN. unfold n in *. lia. }
    { rewrite length_app. cbn [length]. replace (b + 40 * Z.of_nat (length l + 1)) with (b + 40 * (n + 2) - 40) by (unfold n; lia). replace (fb + 440) with (fb + 40 + 400) by lia. exact VE2. }
    { intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia]. cbn [nth]. rewrite Nat.add_0_r. fold n.
      destruct EC1' as (Em & El & _ & Et & Ei). unfold PNM.bstate_at. cbn [c' PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx].
      assert (AG : forall a m, b + 40 * n <= a -> a + m <= b + 40 * n + 40 -> (a + m <= b + 40 * n + 16 \/ b + 40 * n + 24 <= a) -> L5C.agree_on M1 M2 a m).
      { intros a m G1 G2 G3 j Gj. apply FRZ2; [lia| lia| clear -G1 G2 G3 Gj Hn; lia]. }
      split; [apply (PMF.u32_at_agree RSEGS M1 M2); [apply AG; lia|lia|lia| exact Em]|].
      split; [apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG; lia|lia|lia| exact El]|].
      split; [exact CP2|].
      split; [apply (L5C.u8_at_agree RSEGS M1 M2); [apply AG; lia|lia|lia| exact Et]|].
      apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG; lia|lia|lia| exact Ei]. }
    { rewrite length_app. cbn [length]. pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & Hlen & _) & _).
      cbn [PNBO.set_more PNM.b_stk PNM.b_sk] in Hlen. rewrite ES1, length_app in Hlen. cbn [length] in Hlen. lia. }
    intros BR2.
    apply (ed_fin 0x3754c K LBX sp r fb cat e str R M model cr s sm ax fx2 R2 M2 model cr _ sm ax RET CTX KONT' BR2 Y1 Y2); [PMK.rk| PMK.rk| exact Y8| exact Y9| | | cbn [PNBO.set_more PNBO.set_stk PNM.with_srcB PNM.b_bb]; reflexivity].
    { intros k Hk. rewrite (KS2 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). rewrite (KS1 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). reflexivity. }
    right. split; [apply (ec_agree M1 M2); [intros i Hi; apply FRZ2; lia|lia|lia| exact EC1]|].
    split.
    { unfold PNR.binv. cbn [PNBO.set_stk PNBO.set_more PNM.b_more PNM.b_done PNM.b_stk]. split; [exact ID|].
      rewrite ES1 in SH. apply (bstack_shape_pop l c top c' SH); [unfold PNM.bstate_ok; cbn; lia| reflexivity]. }
    unfold PNR.bprog_pop. cbn [PNBO.set_stk PNBO.set_more PNM.b_stk PNM.b_src]. split; [| reflexivity].
    exists l, c, top, c'. split; [exact ES1|]. split; [reflexivity|]. split; [unfold PNM.bstate_ok; cbn; lia|]. repeat split; reflexivity.
  - (* [comment removed for export] *)
    LeanFeed.pfeed P (PNSENDP.bedN_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 35%nat => fb + 16 | 40%nat => b | 41%nat => 40 * (n + 2)
                 | 42%nat => PNM.bs_len top | 43%nat => PNM.bs_pos top | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSENDP.aligned; PMK.sc
                           | (assert (EM : (PNM.bs_pos top - PNM.bs_len top) mod 2 ^ 64 <> 0) by (rewrite Z.mod_divide by lia; intros (q & Hq); clear -Hq NE TLr TPr; nia);
                              clear -EM; pose proof (Z.mod_pos_bound (PNM.bs_pos top - PNM.bs_len top) (2 ^ 64) ltac:(lia)); lia) ]).
    pvz_hg ltac:(idtac; destruct P as (fx2 & R2 & M2 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG2 & _ & FRZ2 & MS2 & KS2 & Y1 & Y10 & Y11)); PMK.pvz_clrT.
    apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 3 LBX sp fb str _ M1 model cr _ sm ax fx1 fx2 R1 R2 0x37510 0x36ee4 M2 (fun _ => False) K
             ltac:(lia) BR1 FOK INCS MS2 MG2 ltac:(intros a Ha _; apply FRZ2; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
    intros BR2.
    assert (EQ2 : forall i, 0 <= i < 2 ^ 64 -> M2 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)) by (intros i Hi; apply FRZ2; exact Hi).
    assert (ED2 : L5.defined M2 (fb + 16) 16) by (destruct EC1 as (_ & _ & ED); apply (L5.defined_grows M1 M2 _ _ MG2 ED)).
    apply (PNBK.brel_make_ec RSEGS AD AN L HI KH 3 LBX sp fb str _ M2 model cr _ sm ax fx2 R2 (sp - 48) 0x3755c 13 K MKE ltac:(lia) K0 BR2 FOK INCS
             Y1 ltac:(split; [lia| reflexivity]) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) Y10 Y11 ltac:(lia) ltac:(lia) ltac:(unfold PMSP.pm_scr; lia) (mod16_sub48 sp A16) ED2).
    intros fx3 R3 M3 RP23 EC3 BR3 AG23.
    destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 3 LBX sp fb str _ M3 model cr _ sm _ BR3) as (PA3 & _ & _ & _ & STK3 & _).
    change (PMSP.pm_scr 3) with 18432 in STK3. pose proof (L5C.stk_writable RSEGS _ M3 sp 18432 STK3) as WR3.
    assert (WP3 : L5.writable RSEGS M3 (fb + 40) 416) by (destruct PA3 as (_ & D & _); apply (L5C.writable_of_defined RSEGS); [exact D|lia|lia]).
    assert (AG13 : forall a m, sp - 48 <= a -> a + m <= fb + 16 -> L5C.agree_on M1 M3 a m) by (intros a m H1 H2 i Hi; rewrite (AG23 a m H1 H2 i Hi); apply EQ2; lia).
    assert (D8 : L5.u64_at RSEGS M3 (sp - 8) r) by (apply (L5C.u64_at_agree RSEGS M1 M3); [apply AG13; lia|lia|lia| exact C8]).
    assert (D16 : L5.u64_at RSEGS M3 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))) by (apply (L5C.u64_at_agree RSEGS M1 M3); [apply AG13; lia|lia|lia| exact C16]).
    assert (D24 : L5.u64_at RSEGS M3 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))) by (apply (L5C.u64_at_agree RSEGS M1 M3); [apply AG13; lia|lia|lia| exact C24]).
    LeanFeed.pfeed P (PNSENDP.bedE_conc fx3 R3 M3 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 35%nat => fb + 16 | 36%nat => r
                 | 37%nat => bv_unsigned (getr R (PMK.reg 8)) | 38%nat => bv_unsigned (getr R (PMK.reg 9)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSENDP.aligned; PMK.sc]).
    pvz_hg ltac:(idtac; destruct P as (fx4 & R4 & M4 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG4 & _ & FRZ4 & MS4 & KS4 & Y1' & Y2 & Y8 & Y9 & MO4)); PMK.pvz_clrT.
    apply (PNBK2.brel_piece_more RSEGS AD AN L HI KH 3 LBX sp fb str _ M3 model cr _ sm _ fx3 fx4 R3 R4 0x3755c 0x3754c M4
             (fun a => fb + 40 + 8 <= a < fb + 40 + 8 + 1) 0 K ltac:(lia) BR3 FOK INCS MS4 MG4 FRZ4 ltac:(intros a; apply PMK.rng_dec)
             ltac:(intros a Pa; cbn beta in Pa; right; clear -Pa; lia) ltac:(replace (fb + 48) with (fb + 40 + 8) by lia; exact MO4) ltac:(left; reflexivity)).
    intros BR4.
    apply (ed_fin 0x3754c K LBX sp r fb cat e str R M model cr s sm ax fx4 R4 M4 model cr _ sm _ RET CTX KONT' BR4 Y1' Y2); [PMK.rk| PMK.rk| exact Y8| exact Y9| | | cbn [PNBO.set_more PNBO.set_stk PNM.with_srcB PNM.b_bb]; reflexivity].
    { intros k Hk. rewrite (KS4 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). rewrite (PMK.cs_of_preserved R2 R3 k RP23) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto).
      rewrite (KS2 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). rewrite (KS1 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). reflexivity. }
    left. split; [| split; [reflexivity|]; split; [apply bax_cat_add|]; split; [cbn [PNBO.set_more PNM.b_stk]; lia| destruct INV as (ID' & SH'); split; [exact ID'| exact SH']]].
    exists 13. split; [lia|]. unfold PNR.o_ec, PMSP.o_ec in EC3. cbn [pa_off_ec AD PnLayoutS_u.ADDR_S] in EC3.
    apply (ec_agree M3 M4); [intros i Hi; apply FRZ4; lia|lia|lia| exact EC3].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem end_array_ok : PNRS.end_array_spec L HI.
Proof.
  unfold PNRS.end_array_spec, PNR.end_array_spec, PNR.brun_spec.
  intros fx R M model K LBX cr sp r fb cat e s str sm ax HH MOK K0 ENT FOK ARGS RPRE INCS INV EC0 He UNR CRED KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2.
  pose proof MOK as (Mh & Ml & Mm). change (PMSP.pm_scr 3) with 18432 in STK. pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  destruct ARGS as ((A10 & A11 & A12) & HLEN). rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
  unfold PNR.o_p, PNR.o_ec, PNR.o_v, PMSP.o_p, PMSP.o_ec, PMSP.o_v in A10, A11, A12, EC0. cbn [pa_off_p pa_off_ec pa_off_v AD PnLayoutS_u.ADDR_S] in A10, A11, A12, EC0.
  pose proof (L5C.stk_floor _ M sp 18432 STK) as SFL. pose proof (L5C.stk_writable RSEGS _ M sp 18432 STK) as WR.
  assert (AL40 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
  assert (AL464 : (fb + 464) mod 8 = 0) by (replace (fb + 464) with (fb + 8 * 58) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
  pose proof (PNBK.brel_init RSEGS AD AN L HI 3 LBX sp fb str M model cr s sm ax ltac:(lia) RPRE HH STK MOK) as BR0.
  change (PMSP.pm_scr 3) with 18432 in BR0.
  assert (CTX : ed_ctx K LBX sp r fb str R cr s).
  { split; [exact K0|]. split; [exact FOK|]. split; [exact INCS|]. split; [exact RAok|]. split; [exact Rsp|]. split; [exact Rgp|]. split; [exact Rtp| exact CRED]. }
  assert (KONT' : ed_kont K LBX sp r fb cat e str R M model cr s sm ax) by exact KONT.
  assert (RET : forall fx Rx Mx, getr Rx (PMK.reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 ->
            msteps RSEGS (@mkst fx Rx (Z_to_bv 64 0x37ea4) Mx (seg_rom RSEGS)) (@mkst fx Rx (Z_to_bv 64 r) Mx (seg_rom RSEGS))).
  { intros fx0 Rx Mx X1 H1 H2. apply (PMK.ret_to RSEGS fx0 Rx Mx 0x37ea4 W_370dc r F_370dc eq_refl D_370dc X1 H1 H2). }
  unfold PNRS.make_ec_spec in MKE.
  pose proof RPRE as (PA0 & _ & VIS0 & _ & BASE0 & _). unfold PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at in PA0, VIS0.
  cbn [pa_off_p pa_off_is pa_off_v pa_vp_visitor AD PnLayoutS_u.ADDR_S] in PA0, VIS0.
  pose proof BASE0 as (IMG0 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG0.
  pose proof PA0 as (_ & PD0 & _ & _ & _ & CM0 & ML0 & _).
  assert (WP : L5.writable RSEGS M (fb + 40) 416) by (apply (L5C.writable_of_defined RSEGS); [exact PD0|lia|lia]).
  (* [comment removed for export] *)
  pose proof INV as (ID & SH). pose proof SH as (L1 & _).
  destruct (exists_last (l := PNM.b_stk s) ltac:(intros X; rewrite X in HLEN; cbn in HLEN; lia)) as (l1 & top & ES1).
  destruct (exists_last (l := l1) ltac:(intros X; rewrite ES1, X in HLEN; cbn in HLEN; lia)) as (l & c & ES2). rewrite ES2, <- app_assoc in ES1. cbn [app] in ES1. clear ES2 l1.
  destruct (ed_stk LBX sp fb str _ M model cr s sm ax l c top BR0 INV ES1) as (OKc & OKt & V0 & V8 & TL & TP & CP & WCP & EC & Hb & TOPIN & S4 & ALb & Hn & DB0).
  set (b := PNM.b_sb s) in *. set (n := Z.of_nat (length l)) in *.
  pose proof OKt as (_ & TLr & TPr & _). pose proof OKc as (OKm & OKl & CPr & OKty & OKi).
  assert (ALn : (40 * (n + 2)) mod 8 = 0) by (replace (40 * (n + 2)) with (0 + 8 * (5 * (n + 2))) by lia; apply PMPK.m8_add; reflexivity).
  unfold PMSP.cfg. cbn [PNL.pn_end_array AN PnLayoutS_u.NADDR_S].
  LeanFeed.pfeed P (PNSENDP.beaA_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 40%nat => b | 41%nat => 40 * (n + 2)
               | 42%nat => PNM.bs_len top | 43%nat => PNM.bs_pos top | 44%nat => PNM.bs_pos c | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSENDP.aligned; PMK.sc
                         | rewrite (PNSZ.size64 _ (n + 2) eq_refl ltac:(lia)); lia | rewrite (PNSZ.size32 _ (n + 2) eq_refl ltac:(lia)); lia]).
  pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
                destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & X1 & X2 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & MO1 & C24 & C16 & C8)); PMK.pvz_clrT.
  change (mkCfg (@mkst fx R (Z_to_bv 64 0x37db4) M (seg_rom RSEGS)) model) with (@PMSP.cfg RSEGS fx R 0x37db4 M model).
  apply (PNBK2.brel_piece_more RSEGS AD AN L HI KH 3 LBX sp fb str _ M model cr s sm ax fx fx1 R R1 0x37db4 0x37e68 M1
           (fun a => (sp - 48 <= a < sp - 48 + 48) \/ (fb + 40 + 8 <= a < fb + 40 + 8 + 1)) 1 K ltac:(lia) BR0 FOK INCS MS1 MG1
           ltac:(intros a Ha N; apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X])
           ltac:(intros a; apply PMK.or_dec; apply PMK.rng_dec)
           ltac:(intros a Pa; cbn beta in Pa; unfold PMSP.pm_scr; clear -Pa; lia) ltac:(replace (fb + 48) with (fb + 40 + 8) by lia; exact MO1) ltac:(right; reflexivity)).
  intros BR1.
  assert (AG01 : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (a + m <= sp - 48 \/ sp <= a) -> (a + m <= fb + 48 \/ fb + 49 <= a) -> L5C.agree_on M M1 a m).
  { intros a m H1 H2 H3 H4 i Hi. apply FRZ1; lia. }
  assert (EC1 : PMSP.ec_at RSEGS M1 (fb + 16) e cat) by (apply (ec_agree M M1); [apply AG01; lia|lia|lia| exact EC0]).
  rewrite Rra in C8. rewrite L5.unsigned_lit in C8 by lia.
  pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 8))) as BU8. pose proof (bv_unsigned_in_range _ (getr R (PMK.reg 9))) as BU9.
  destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 3 LBX sp fb str _ M1 model cr _ sm ax BR1) as (PA1 & _ & _ & _ & STK1 & _).
  change (PMSP.pm_scr 3) with 18432 in STK1. pose proof (L5C.stk_writable RSEGS _ M1 sp 18432 STK1) as WR1.
  assert (WP1 : L5.writable RSEGS M1 (fb + 40) 416) by (destruct PA1 as (_ & D & _); apply (L5C.writable_of_defined RSEGS); [exact D|lia|lia]).
  destruct (Z.eq_dec (PNM.bs_pos top) (PNM.bs_len top)) as [EQ|NE].
  - (* [comment removed for export] *)
    destruct (ed_stk LBX sp fb str _ M1 model cr _ sm ax l c top BR1 ltac:(cbn [PNBO.set_more PNR.binv PNM.b_more PNM.b_done PNM.b_stk]; split; [exact ID| exact SH]) ES1)
      as (_ & _ & U0 & U8 & UL & UP & UC & WUC & EC1' & _ & _ & _ & _ & _ & DB1). cbn [PNBO.set_more PNM.b_sb PNM.b_sk] in U0, U8, UL, UP, UC, WUC, EC1', DB1. fold b in U0, U8, UL, UP, UC, WUC, EC1', DB1.
    rewrite EQ in UP.
    rewrite EQ in X11.
    LeanFeed.pfeed P (PNSENDP.beaT_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 34%nat => fb + 464 | 35%nat => fb + 16 | 36%nat => r
                 | 37%nat => bv_unsigned (getr R (PMK.reg 8)) | 38%nat => bv_unsigned (getr R (PMK.reg 9)) | 40%nat => b | 41%nat => 40 * (n + 2)
                 | 42%nat => PNM.bs_len top | 43%nat => PNM.bs_len top | 44%nat => PNM.bs_pos c | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSENDP.aligned; PMK.sc]).
    pvz_hg ltac:(idtac; destruct P as (fx2 & R2 & M2 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG2 & _ & FRZ2 & MS2 & KS2 & Y1 & Y2 & Y8 & Y9 & Y11 & Y12 & Y13 & VE2)); PMK.pvz_clrT.
    destruct (PMCG.u64_of_defined RSEGS M2 (b + 40 * n + 16) ltac:(lia) ltac:(lia)) as (v' & Hv' & CP2).
    { apply (L5.defined_grows M1 M2 _ _ MG2). apply (L5.defined_sub M1 b (40 * 2 ^ PNM.b_sk s)); [exact DB1| lia| clear -Hn TOPIN; lia]. }
    set (c' := PNM.BS (PNM.bs_mode c) (PNM.bs_len c) v' (PNM.bs_type c) (PNM.bs_idx c)).
    apply (PNBK2.brel_piece_stk RSEGS AD AN L HI KH 3 LBX sp fb str _ M1 model cr _ sm ax fx1 fx2 R1 R2 0x37e68 0x37ea4 M2
             (fun a => (fb + 40 + 400 <= a < fb + 40 + 400 + 8) \/ (b + 40 * (n + 2) - 64 <= a < b + 40 * (n + 2) - 64 + 8)) l [c; top] [c'] K ltac:(lia) BR1 FOK INCS MS2 MG2
             ltac:(intros a Ha N; apply FRZ2; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X])
             ltac:(intros a; apply PMK.or_dec; apply PMK.rng_dec)); cbn [PNBO.set_more PNM.b_stk PNM.b_sb PNM.b_sk]; fold b.
    { exact ES1. }
    { intros a Pa. cbn beta in Pa. right. clear -Pa Hn TOPIN. unfold n in *. lia. }
    { rewrite length_app. cbn [length]. replace (b + 40 * Z.of_nat (length l + 1)) with (b + 40 * (n + 2) - 40) by (unfold n; lia). replace (fb + 440) with (fb + 40 + 400) by lia. exact VE2. }
    { intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia]. cbn [nth]. rewrite Nat.add_0_r. fold n.
      destruct EC1' as (Em & El & _ & Et & Ei). unfold PNM.bstate_at. cbn [c' PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx].
      assert (AG : forall a m, b + 40 * n <= a -> a + m <= b + 40 * n + 40 -> (a + m <= b + 40 * n + 16 \/ b + 40 * n + 24 <= a) -> L5C.agree_on M1 M2 a m).
      { intros a m G1 G2 G3 j Gj. apply FRZ2; [lia| lia| clear -G1 G2 G3 Gj Hn; lia]. }
      split; [apply (PMF.u32_at_agree RSEGS M1 M2); [apply AG; lia|lia|lia| exact Em]|].
      split; [apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG; lia|lia|lia| exact El]|].
      split; [exact CP2|].
      split; [apply (L5C.u8_at_agree RSEGS M1 M2); [apply AG; lia|lia|lia| exact Et]|].
      apply (L5C.u64_at_agree RSEGS M1 M2); [apply AG; lia|lia|lia| exact Ei]. }
    { rewrite length_app. cbn [length]. pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & Hlen & _) & _).
      cbn [PNBO.set_more PNM.b_stk PNM.b_sk] in Hlen. rewrite ES1, length_app in Hlen. cbn [length] in Hlen. lia. }
    intros BR2.
    apply (ed_fin 0x37ea4 K LBX sp r fb cat e str R M model cr s sm ax fx2 R2 M2 model cr _ sm ax RET CTX KONT' BR2 Y1 Y2); [PMK.rk| PMK.rk| exact Y8| exact Y9| | | cbn [PNBO.set_more PNBO.set_stk PNM.with_srcB PNM.b_bb]; reflexivity].
    { intros k Hk. rewrite (KS2 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). rewrite (KS1 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). reflexivity. }
    right. split; [apply (ec_agree M1 M2); [intros i Hi; apply FRZ2; lia|lia|lia| exact EC1]|].
    split.
    { unfold PNR.binv. cbn [PNBO.set_stk PNBO.set_more PNM.b_more PNM.b_done PNM.b_stk]. split; [exact ID|].
      rewrite ES1 in SH. apply (bstack_shape_pop l c top c' SH); [unfold PNM.bstate_ok; cbn; lia| reflexivity]. }
    unfold PNR.bprog_pop. cbn [PNBO.set_stk PNBO.set_more PNM.b_stk PNM.b_src]. split; [| reflexivity].
    exists l, c, top, c'. split; [exact ES1|]. split; [reflexivity|]. split; [unfold PNM.bstate_ok; cbn; lia|]. repeat split; reflexivity.
  - (* [comment removed for export] *)
    LeanFeed.pfeed P (PNSENDP.beaN_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 35%nat => fb + 16 | 40%nat => b | 41%nat => 40 * (n + 2)
                 | 42%nat => PNM.bs_len top | 43%nat => PNM.bs_pos top | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSENDP.aligned; PMK.sc
                           | (assert (EM : (PNM.bs_pos top - PNM.bs_len top) mod 2 ^ 64 <> 0) by (rewrite Z.mod_divide by lia; intros (q & Hq); clear -Hq NE TLr TPr; nia);
                              clear -EM; pose proof (Z.mod_pos_bound (PNM.bs_pos top - PNM.bs_len top) (2 ^ 64) ltac:(lia)); lia) ]).
    pvz_hg ltac:(idtac; destruct P as (fx2 & R2 & M2 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG2 & _ & FRZ2 & MS2 & KS2 & Y1 & Y10 & Y11)); PMK.pvz_clrT.
    apply (PNBK2.brel_piece_fr RSEGS AD AN L HI KH 3 LBX sp fb str _ M1 model cr _ sm ax fx1 fx2 R1 R2 0x37e68 0x36ee4 M2 (fun _ => False) K
             ltac:(lia) BR1 FOK INCS MS2 MG2 ltac:(intros a Ha _; apply FRZ2; exact Ha) ltac:(intros a; right; intros X; exact X) ltac:(intros a X; destruct X)).
    intros BR2.
    assert (EQ2 : forall i, 0 <= i < 2 ^ 64 -> M2 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)) by (intros i Hi; apply FRZ2; exact Hi).
    assert (ED2 : L5.defined M2 (fb + 16) 16) by (destruct EC1 as (_ & _ & ED); apply (L5.defined_grows M1 M2 _ _ MG2 ED)).
    apply (PNBK.brel_make_ec RSEGS AD AN L HI KH 3 LBX sp fb str _ M2 model cr _ sm ax fx2 R2 (sp - 48) 0x37eb4 13 K MKE ltac:(lia) K0 BR2 FOK INCS
             Y1 ltac:(split; [lia| reflexivity]) ltac:(PMK.rk) ltac:(PMK.rk) ltac:(PMK.rk) Y10 Y11 ltac:(lia) ltac:(lia) ltac:(unfold PMSP.pm_scr; lia) (mod16_sub48 sp A16) ED2).
    intros fx3 R3 M3 RP23 EC3 BR3 AG23.
    destruct (PNBK2.brel_pre RSEGS AD AN L HI KH 3 LBX sp fb str _ M3 model cr _ sm _ BR3) as (PA3 & _ & _ & _ & STK3 & _).
    change (PMSP.pm_scr 3) with 18432 in STK3. pose proof (L5C.stk_writable RSEGS _ M3 sp 18432 STK3) as WR3.
    assert (WP3 : L5.writable RSEGS M3 (fb + 40) 416) by (destruct PA3 as (_ & D & _); apply (L5C.writable_of_defined RSEGS); [exact D|lia|lia]).
    assert (AG13 : forall a m, sp - 48 <= a -> a + m <= fb + 16 -> L5C.agree_on M1 M3 a m) by (intros a m H1 H2 i Hi; rewrite (AG23 a m H1 H2 i Hi); apply EQ2; lia).
    assert (D8 : L5.u64_at RSEGS M3 (sp - 8) r) by (apply (L5C.u64_at_agree RSEGS M1 M3); [apply AG13; lia|lia|lia| exact C8]).
    assert (D16 : L5.u64_at RSEGS M3 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))) by (apply (L5C.u64_at_agree RSEGS M1 M3); [apply AG13; lia|lia|lia| exact C16]).
    assert (D24 : L5.u64_at RSEGS M3 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))) by (apply (L5C.u64_at_agree RSEGS M1 M3); [apply AG13; lia|lia|lia| exact C24]).
    LeanFeed.pfeed P (PNSENDP.beaE_conc fx3 R3 M3 (fun j => match j with 2%nat => sp | 33%nat => fb + 40 | 35%nat => fb + 16 | 36%nat => r
                 | 37%nat => bv_unsigned (getr R (PMK.reg 8)) | 38%nat => bv_unsigned (getr R (PMK.reg 9)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PNSENDP.aligned; PMK.sc]).
    pvz_hg ltac:(idtac; destruct P as (fx4 & R4 & M4 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG4 & _ & FRZ4 & MS4 & KS4 & Y1' & Y2 & Y8 & Y9 & MO4)); PMK.pvz_clrT.
    apply (PNBK2.brel_piece_more RSEGS AD AN L HI KH 3 LBX sp fb str _ M3 model cr _ sm _ fx3 fx4 R3 R4 0x37eb4 0x37ea4 M4
             (fun a => fb + 40 + 8 <= a < fb + 40 + 8 + 1) 0 K ltac:(lia) BR3 FOK INCS MS4 MG4 FRZ4 ltac:(intros a; apply PMK.rng_dec)
             ltac:(intros a Pa; cbn beta in Pa; right; clear -Pa; lia) ltac:(replace (fb + 48) with (fb + 40 + 8) by lia; exact MO4) ltac:(left; reflexivity)).
    intros BR4.
    apply (ed_fin 0x37ea4 K LBX sp r fb cat e str R M model cr s sm ax fx4 R4 M4 model cr _ sm _ RET CTX KONT' BR4 Y1' Y2); [PMK.rk| PMK.rk| exact Y8| exact Y9| | | cbn [PNBO.set_more PNBO.set_stk PNM.with_srcB PNM.b_bb]; reflexivity].
    { intros k Hk. rewrite (KS4 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). rewrite (PMK.cs_of_preserved R2 R3 k RP23) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto).
      rewrite (KS2 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). rewrite (KS1 k) by (revert Hk; clear; intros Hk; cbn in Hk |- *; tauto). reflexivity. }
    left. split; [| split; [reflexivity|]; split; [apply bax_cat_add|]; split; [cbn [PNBO.set_more PNM.b_stk]; lia| destruct INV as (ID' & SH'); split; [exact ID'| exact SH']]].
    exists 13. split; [lia|]. unfold PNR.o_ec, PMSP.o_ec in EC3. cbn [pa_off_ec AD PnLayoutS_u.ADDR_S] in EC3.
    apply (ec_agree M3 M4); [intros i Hi; apply FRZ4; lia|lia|lia| exact EC3].
Qed.

End WithHeap.
End PNSEND.
