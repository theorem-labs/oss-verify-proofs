(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout PmModel PmModelFacts PmStatics PmSpecs PmStep PmKeep PmFrame PmParSpecs PmParKit PgSrc PgV8
     PnLayout PnModel PnModelFacts PnStatics PnKeep PnRun PnBrObj PnBrKit.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNBK2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma btop_pos_refl s : PNR.binv s -> PNR.btop_pos s s.
Proof.
  intros (_ & (L1 & _ & _ & _ & OK)).
  destruct (exists_last (l := PNM.b_stk s) ltac:(intros X; rewrite X in L1; cbn in L1; lia)) as (l & c & E).
  exists l, c, c. split; [exact E|]. split; [exact E|].
  split; [|repeat split; reflexivity].
  pose proof (OK (length l) ltac:(rewrite E, length_app; cbn; lia)) as H. rewrite E, nth_middle in H. exact H.
Qed.

Lemma btop_pos_trans s1 s2 s3 : PNR.btop_pos s1 s2 -> PNR.btop_pos s2 s3 -> PNR.btop_pos s1 s3.
Proof.
  intros (l & c & c' & E1 & E2 & OK & Hm & Hl & Ht & Hi) (l2 & d & d' & F1 & F2 & OK2 & Hm2 & Hl2 & Ht2 & Hi2).
  rewrite E2 in F1. destruct (app_inj_tail l l2 c' d F1) as (<- & <-).
  exists l, c, d'. split; [exact E1|]. split; [exact F2|]. split; [exact OK2|]. rewrite Hm2, Hl2, Ht2, Hi2. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma bstack_shape_top l c c' :
  PNR.bstack_shape (l ++ [c]) -> PNM.bstate_ok c' -> PNM.bs_mode c' = PNM.bs_mode c -> PNR.bstack_shape (l ++ [c']).
Proof.
  intros (L1 & L2 & B0 & CT & OK) OK' Hm. unfold PNR.bstack_shape. rewrite length_app in *. cbn [length] in *.
  split; [lia|]. split; [lia|].
  split.
  { destruct l as [|x l']; cbn in B0 |- *; [rewrite Hm; exact B0| exact B0]. }
  split.
  { intros i Hi. destruct (Nat.eq_dec i (length l)) as [->|NE].
    - rewrite nth_middle. rewrite Hm. pose proof (CT (length l) Hi) as X. rewrite nth_middle in X. exact X.
    - rewrite app_nth1 by lia. pose proof (CT i Hi) as X. rewrite app_nth1 in X by lia. exact X. }
  intros i Hi. destruct (Nat.eq_dec i (length l)) as [->|NE].
  - rewrite nth_middle. exact OK'.
  - rewrite app_nth1 by lia. pose proof (OK i Hi) as X. rewrite app_nth1 in X by lia. exact X.
Qed.

Lemma binv_set_stk_top s l c c' :
  PNR.binv s -> PNM.b_stk s = l ++ [c] -> PNM.bstate_ok c' -> PNM.bs_mode c' = PNM.bs_mode c -> PNR.binv (PNBO.set_stk s (l ++ [c'])).
Proof.
  intros (ID & SH) E OK Hm. unfold PNR.binv. cbn [PNBO.set_stk PNM.b_more PNM.b_done PNM.b_stk].
  split; [exact ID|]. rewrite E in SH. exact (bstack_shape_top l c c' SH OK Hm).
Qed.

Lemma btop_pos_set_stk s l c c' :
  PNM.b_stk s = l ++ [c] -> PNM.bstate_ok c' -> PNM.bs_mode c' = PNM.bs_mode c -> PNM.bs_len c' = PNM.bs_len c ->
  PNM.bs_type c' = PNM.bs_type c -> PNM.bs_idx c' = PNM.bs_idx c -> PNR.btop_pos s (PNBO.set_stk s (l ++ [c'])).
Proof.
  intros E OK Hm Hl Ht Hi. exists l, c, c'. cbn [PNBO.set_stk PNM.b_stk].
  split; [exact E|]. split; [reflexivity|]. split; [exact OK|]. split; [exact Hm|]. split; [exact Hl|]. split; [exact Ht| exact Hi].
Qed.

Lemma bflag_set_stk_top s l c c' :
  PNM.b_stk s = l ++ [c] -> PNM.bs_mode c' = PNM.bs_mode c -> PNR.bflag (PNM.b_stk (PNBO.set_stk s (l ++ [c']))) = PNR.bflag (PNM.b_stk s).
Proof. intros E Hm. cbn [PNBO.set_stk PNM.b_stk]. rewrite E. unfold PNR.bflag. rewrite !last_last. rewrite Hm. reflexivity. Qed.

(* [comment removed for export] *)
Section Kit.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AN : PNL.pn_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis KH : PNBK.khyps segs A AN L HI.
Let KL := PNBK.kh_KL _ _ _ _ _ KH.
Let HIok := PNBK.kh_HIok _ _ _ _ _ KH.
Let HFR := PNBK.kh_HFR _ _ _ _ _ KH.
Let HOP := PNBK.kh_HOP _ _ _ _ _ KH.
Let HOV := PNBK.kh_HOV _ _ _ _ _ KH.
Let HOIS := PNBK.kh_HOIS _ _ _ _ _ KH.
Let HOEC := PNBK.kh_HOEC _ _ _ _ _ KH.

Abbreviation mem := (word -> option byte).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Abbreviation bparser_at := (PNM.bparser_at segs A T3 T4 (pa_vp_parser A)).
Abbreviation iss_at := (PM.iss_at segs A T3).
Abbreviation brel := (PNBK.brel segs A AN L HI).
Abbreviation BENT := PNBK.BENT.
Abbreviation scr := PMSP.pm_scr.
Abbreviation pot := (PNR.pot_bparser L).

(* [comment removed for export] *)
Lemma brel_blocks h LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 :
  brel h LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) ->
  PMFR.brange L (PNM.bparser_own s1 ++ LBX)
  /\ (forall B m, In (B, m) (PNM.bparser_own s1) -> 4096 <= B /\ B + m <= hl_ceil L)
  /\ (PM.sr_qc (PNM.b_src s1) + PM.CHUNK <= PNM.b_sb s1 \/ PNM.b_sb s1 + PNM.BSZ * 2 ^ PNM.b_sk s1 <= PM.sr_qc (PNM.b_src s1)).
Proof.
  intros (RP & STEP & AXL & HP & CK & MB & HH & STK & MOK). cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax] in *.
  set (LB := PNM.bparser_own s1 ++ LBX) in *.
  assert (BRG : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr1 M1 _ HH); apply incl_refl).
  assert (NDL : NoDup (map fst LB)) by exact (PMPK.heap_nodup L HI HIok LB cr1 M1 _ HH).
  split; [exact BRG|].
  split.
  { intros B m Hin. destruct (BRG B m ltac:(unfold LB; apply in_or_app; left; exact Hin)) as (Q0 & _ & Q4). lia. }
  assert (Bq : In (PM.sr_qc (PNM.b_src s1), PM.CHUNK) LB) by (unfold LB, PNM.bparser_own, PM.src_own; cbn; auto).
  assert (Bs : In (PNM.b_sb s1, PNM.BSZ * 2 ^ PNM.b_sk s1) (PNM.brest_own s1 ++ LBX)).
  { unfold PNM.brest_own, PNM.bvec_own. cbn. auto. }
  assert (NE : PM.sr_qc (PNM.b_src s1) <> PNM.b_sb s1).
  { apply (PMPK.fst_neq_app (PM.src_own (PNM.b_src s1)) (PNM.brest_own s1 ++ LBX) _ PM.CHUNK _ (PNM.BSZ * 2 ^ PNM.b_sk s1));
      [unfold LB, PNM.bparser_own in NDL; rewrite <- app_assoc in NDL; exact NDL| unfold PM.src_own; cbn; auto| exact Bs]. }
  apply (PMPK.blocks_apart_heap L HI HIok LB cr1 M1 _ _ _ _ _ HH Bq); [| exact NE].
  unfold LB, PNM.bparser_own. rewrite <- app_assoc. apply in_or_app. right. exact Bs.
Qed.

Lemma brel_pre h LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 :
  brel h LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) ->
  bparser_at M1 (fb + 40) (fb + 472) s1 /\ iss_at M1 (fb + 472) str sm1 /\ PNM.bgrow_ok s1 /\ 0 <= PM.unread (PNM.b_src s1) sm1
  /\ L5C.stk (hl_sptop L) M1 sp (scr h) /\ PMSP.model_ok model1.
Proof.
  intros (RP & STEP & AXL & HP & CK & MB & HH & STK & MOK). cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax] in *.
  destruct RP as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & GR1).
  unfold PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at, PNM.PSIZE in PA1, IA1, VIS1, VREF1.
  rewrite HOP, HOIS in PA1. rewrite HOIS in IA1.
  split; [exact PA1|]. split; [exact IA1|]. split; [exact GR1|].
  split.
  { pose proof (PMPK.iss_size_lt segs A M1 _ _ _ IA1) as Z1.
    pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & G2 & _) & _). unfold PM.unread. lia. }
  split; [exact STK| exact MOK].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma brel_piece_fr h LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2 : mem) (P : Z -> Prop) K :
  0 <= h ->
  brel h LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) ->
  PMSP.frame_ok A L sp fb -> incl (PM.vs_own str) LBX ->
  msteps segs (@mkst fx1 R1 (Z_to_bv 64 pc1) M1 (seg_rom segs)) (@mkst fx2 R2 (Z_to_bv 64 pc2) M2 (seg_rom segs)) -> mem_grows M1 M2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, {P a} + {~ P a}) ->
  (forall a, P a -> sp - scr h <= a < sp) ->
  (brel h LBX sp fb str E0 (BENT M2 model1 cr1 s1 sm1 ax1) -> srealizes segs SCFG (@PMSP.cfg segs fx2 R2 pc2 M2 model1) K) ->
  srealizes segs SCFG (@PMSP.cfg segs fx1 R1 pc1 M1 model1) K.
Proof.
  intros Hh BR FOK INCS MS MG FRZ DEC PF KONT.
  destruct (brel_blocks h LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR) as (BRG & OWNB & APQ).
  destruct (brel_pre h LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR) as (PA1 & IA1 & GR1 & UN1 & STK & MOK).
  pose proof FOK as (F1 & F2 & F3). rewrite HFR in F2. pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (PNBK.scr_nonneg h Hh) as SC0.
  apply (PNBK.brel_piece segs A AN L HI KH h LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 fx1 fx2 R1 R2 pc1 pc2 M2 P s1 K Hh BR FOK INCS MS MG FRZ DEC);
    [intros a Pa; left; exact (PF a Pa)| | reflexivity| reflexivity| reflexivity| exact GR1| exact KONT].
  apply (PNMF.bparser_at_agree segs A (pa_vp_parser A) M1 M2 (fb + 40) (fb + 472) s1); unfold PNM.PSIZE; [lia|lia| | | exact PA1].
  - intros i Hi. apply FRZ; [lia|]. intros Pi. pose proof (PF i Pi). lia.
  - intros B m Hin. destruct (OWNB B m Hin) as (Q0 & Q4). unfold hl_ceil in Q4. split; [lia|]. split; [lia|].
    intros i Hi. apply FRZ; [lia|]. intros Pi. pose proof (PF i Pi). lia.
Qed.

(* [comment removed for export] *)
Lemma brel_piece_more h LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2 : mem) (P : Z -> Prop) v K :
  0 <= h ->
  brel h LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) ->
  PMSP.frame_ok A L sp fb -> incl (PM.vs_own str) LBX ->
  msteps segs (@mkst fx1 R1 (Z_to_bv 64 pc1) M1 (seg_rom segs)) (@mkst fx2 R2 (Z_to_bv 64 pc2) M2 (seg_rom segs)) -> mem_grows M1 M2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, {P a} + {~ P a}) ->
  (forall a, P a -> (sp - scr h <= a < sp) \/ (fb + 48 <= a < fb + 49)) ->
  L5.u8_at segs M2 (fb + 48) v -> (v = 0 \/ v = 1) ->
  (brel h LBX sp fb str E0 (BENT M2 model1 cr1 (PNBO.set_more s1 v) sm1 ax1) -> srealizes segs SCFG (@PMSP.cfg segs fx2 R2 pc2 M2 model1) K) ->
  srealizes segs SCFG (@PMSP.cfg segs fx1 R1 pc1 M1 model1) K.
Proof.
  intros Hh BR FOK INCS MS MG FRZ DEC PF U8 V01 KONT.
  destruct (brel_blocks h LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR) as (BRG & OWNB & APQ).
  destruct (brel_pre h LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR) as (PA1 & IA1 & GR1 & UN1 & STK & MOK).
  pose proof FOK as (F1 & F2 & F3). rewrite HFR in F2. pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (PNBK.scr_nonneg h Hh) as SC0.
  apply (PNBK.brel_piece segs A AN L HI KH h LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 fx1 fx2 R1 R2 pc1 pc2 M2 P (PNBO.set_more s1 v) K Hh BR FOK INCS MS MG FRZ DEC);
    [intros a Pa; destruct (PF a Pa) as [X|X]; [left; exact X| right; left; unfold PNBK.pwr; lia]| | reflexivity| reflexivity| reflexivity| exact GR1| exact KONT].
  apply (PNBO.bparser_set_more segs A (pa_vp_parser A) M1 M2 P FRZ MG (fb + 40) (fb + 472) s1 v); unfold PNM.PSIZE;
    [lia|lia|exact PA1| | | | replace (fb + 40 + 8) with (fb + 48) by lia; exact U8| exact V01].
  - intros B m Hin. destruct (OWNB B m Hin) as (Q0 & Q4). unfold hl_ceil in Q4. lia.
  - intros a Ha Pa. destruct (PF a Pa); lia.
  - intros B m Hin i Hi Pi. destruct (OWNB B m Hin) as (Q0 & Q4). unfold hl_ceil in Q4. destruct (PF i Pi); lia.
Qed.


(* [comment removed for export] *)
Lemma brel_piece_pos h LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2 : mem) (P : Z -> Prop) l c v K :
  0 <= h ->
  brel h LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) ->
  PMSP.frame_ok A L sp fb -> incl (PM.vs_own str) LBX ->
  msteps segs (@mkst fx1 R1 (Z_to_bv 64 pc1) M1 (seg_rom segs)) (@mkst fx2 R2 (Z_to_bv 64 pc2) M2 (seg_rom segs)) -> mem_grows M1 M2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, {P a} + {~ P a}) ->
  PNM.b_stk s1 = l ++ [c] ->
  (forall a, P a -> (sp - scr h <= a < sp)
                    \/ (PNM.b_sb s1 + 40 * Z.of_nat (length l) + 16 <= a < PNM.b_sb s1 + 40 * Z.of_nat (length l) + 24)) ->
  L5.u64_at segs M2 (PNM.b_sb s1 + 40 * Z.of_nat (length l) + 16) v -> 0 <= v < 2 ^ 64 ->
  (brel h LBX sp fb str E0 (BENT M2 model1 cr1 (PNBO.set_stk s1 (l ++ [PNM.BS (PNM.bs_mode c) (PNM.bs_len c) v (PNM.bs_type c) (PNM.bs_idx c)])) sm1 ax1) ->
   srealizes segs SCFG (@PMSP.cfg segs fx2 R2 pc2 M2 model1) K) ->
  srealizes segs SCFG (@PMSP.cfg segs fx1 R1 pc1 M1 model1) K.
Proof.
  intros Hh BR FOK INCS MS MG FRZ DEC ES PF U64 Hv KONT.
  destruct (brel_blocks h LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR) as (BRG & OWNB & APQ).
  destruct (brel_pre h LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR) as (PA1 & IA1 & GR1 & UN1 & STK & MOK).
  pose proof FOK as (F1 & F2 & F3). rewrite HFR in F2. pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (PNBK.scr_nonneg h Hh) as SC0.
  set (b := PNM.b_sb s1) in *. set (k := PNM.b_sk s1) in *. set (n := Z.of_nat (length l)) in *.
  set (c' := PNM.BS (PNM.bs_mode c) (PNM.bs_len c) v (PNM.bs_type c) (PNM.bs_idx c)) in *.
  pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SV1 & _).
  unfold PNM.OFF_STK in SV1. fold b k in SV1. pose proof SV1 as (_ & _ & _ & Hk & Hlen & Hal & DB & _ & _ & EL).
  rewrite ES, length_app in Hlen, EL. cbn [length] in Hlen, EL. unfold PNM.BSZ in *.
  assert (Hn : 0 <= n /\ n + 1 <= 2 ^ k) by (unfold n; lia).
  assert (Bq : In (PM.sr_qc (PNM.b_src s1), PM.CHUNK) (PNM.bparser_own s1)) by (unfold PNM.bparser_own, PM.src_own; cbn; auto).
  assert (Bs : In (b, 40 * 2 ^ k) (PNM.bparser_own s1)).
  { unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own, b, k. apply in_or_app. right. cbn. auto. }
  destruct (OWNB _ _ Bq) as (Q0 & Q4). destruct (OWNB _ _ Bs) as (S0 & S4). unfold hl_ceil in Q4, S4.
  assert (TOPIN : b + 40 * n + 40 <= b + 40 * 2 ^ k) by nia.
  apply (PNBK.brel_piece segs A AN L HI KH h LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 fx1 fx2 R1 R2 pc1 pc2 M2 P (PNBO.set_stk s1 (l ++ [c'])) K Hh BR FOK INCS MS MG FRZ DEC);
    [| | reflexivity| reflexivity| reflexivity| exact GR1| exact KONT].
  { intros a Pa. destruct (PF a Pa) as [X|X]; [left; exact X|]. right. right. exists (b, 40 * 2 ^ k). split; [exact Bs|]. cbn [fst snd]. lia. }
  apply (PNBO.bparser_top_upd segs A (pa_vp_parser A) M1 M2 P FRZ MG (fb + 40) (fb + 472) s1 l c c'); unfold PNM.PSIZE, PNM.BSZ; fold b k; try lia.
  - exact PA1.
  - exact ES.
  - intros a Ha Pa. destruct (PF a Pa); lia.
  - intros i Hi Pi. destruct (PF i Pi); [lia|]. destruct APQ; lia.
  - intros i Hi Pi. destruct (PF i Pi); lia.
  - (* [comment removed for export] *)
    pose proof (EL (length l) ltac:(lia)) as ET. rewrite nth_middle in ET. fold n in ET.
    destruct ET as (Tm & Tl & _ & Tt & Ti).
    assert (AG : forall a m, b + 40 * n <= a -> a + m <= b + 40 * n + 40 -> (a + m <= b + 40 * n + 16 \/ b + 40 * n + 24 <= a) -> L5C.agree_on M1 M2 a m).
    { intros a m H1 H2 H3 i Hi. apply FRZ; [lia|]. intros Pi. destruct (PF i Pi); lia. }
    unfold PNM.bstate_at. cbn [c' PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx].
    split; [apply (PMF.u32_at_agree segs M1 M2); [apply AG; lia|lia|lia| exact Tm]|].
    split; [apply (L5C.u64_at_agree segs M1 M2); [apply AG; lia|lia|lia| exact Tl]|].
    split; [exact U64|].
    split; [apply (L5C.u8_at_agree segs M1 M2); [apply AG; lia|lia|lia| exact Tt]|].
    apply (L5C.u64_at_agree segs M1 M2); [apply AG; lia|lia|lia| exact Ti].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma berrW_edep a : PMK.inW (PNST.berr_W A AN) a -> PNKP.edep A AN a.
Proof.
  intros (r0 & Hin & Hr). unfold PNST.berr_W, PNST.cat_W, PNST.dec_W in Hin. unfold L5.in_rng in Hr. unfold PNKP.edep. cbn [app] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [fst snd] in Hr;
    [left; lia| right; left; lia| | | | | right; left; lia]; right; right.
  - exists (PNL.pn_inf_guard AN, PNL.pn_inf_guard AN + 8). split; [unfold PNL.pn_d128_foot; cbn; tauto| cbn [fst snd]; lia].
  - exists (PNL.pn_nan_guard AN, PNL.pn_nan_guard AN + 8). split; [unfold PNL.pn_d128_foot; cbn; tauto| cbn [fst snd]; lia].
  - exists (PNL.pn_inf_obj AN, PNL.pn_inf_obj AN + 24). split; [unfold PNL.pn_d128_foot; cbn; tauto| cbn [fst snd]; lia].
  - exists (PNL.pn_nan_obj AN, PNL.pn_nan_obj AN + 24). split; [unfold PNL.pn_d128_foot; cbn; tauto| cbn [fst snd]; lia].
Qed.
Lemma wrun_floor fb a : PMK.inW (PNR.W_brun A AN fb) a -> fb + 16 <= a \/ hl_img_lo L <= a < hl_img_hi L.
Proof.
  intros I. destruct (PNBK.wrun_where segs A AN L HI KH fb a I) as [X|[X|[X|[X|[X|[X|X]]]]]]; [left; lia| left; lia| left; lia| left; lia| left; lia| left; lia|].
  right. apply (PNBK.kh_EDI _ _ _ _ _ KH). apply berrW_edep. exact X.
Qed.

(* [comment removed for export] *)
Lemma brel_call bb pc hg args prog h LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 (fx1 : FPState) R1 (sp' r' cat e : Z) K :
  PNR.brun_spec segs A AN L HI bb pc hg args prog ->
  0 <= hg -> 0 <= h -> K [] ->
  brel h LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) ->
  PMSP.frame_ok A L sp fb -> incl (PM.vs_own str) LBX -> PMSP.credit_le (pot (PNBK.be_s E0)) (PNBK.be_cr E0) ->
  getr R1 (PMK.reg 1) = Z_to_bv 64 r' -> L5.ra_ok r' -> getr R1 (PMK.reg 2) = Z_to_bv 64 sp' ->
  getr R1 (PMK.reg 3) = Z_to_bv 64 (pa_gp A) -> getr R1 (PMK.reg 4) = Z_to_bv 64 (pa_tp A) ->
  sp' <= sp -> sp - scr h <= sp' - scr hg -> sp' mod 16 = 0 ->
  args R1 fb s1 sm1 -> PNR.binv s1 -> PMSP.ec_at segs M1 (fb + 16) e cat -> 0 <= e <= 64 -> PM.unread (PNM.b_src s1) sm1 < 2 ^ 26 ->
  (forall (fx2 : FPState) R2 (M2 : mem) model2 s2 sm2 ax2 cr2,
      regs_preserved R1 R2 ->
      PNR.brun_post segs A AN bb prog R2 M2 fb s1 s2 str sm1 sm2 ax1 ax2 cat e ->
      brel h LBX sp fb str E0 (BENT M2 model2 cr2 s2 sm2 ax2) ->
      (forall a n, sp' <= a -> a + n <= fb + 16 -> L5C.agree_on M1 M2 a n) ->
      srealizes segs SCFG (@PMSP.cfg segs fx2 R2 r' M2 model2) K) ->
  srealizes segs SCFG (@PMSP.cfg segs fx1 R1 pc M1 model1) K.
Proof.
  intros SPEC Hg Hh K0 BR FOK INCS CRED0 X1 RA X2 X3 X4 S1 S2 S3 ARGS INV EC He UNR KONT.
  pose proof BR as (RP & STEP & AXL & HP & CK & MB & HH & STK & MOK). cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax] in RP, STEP, AXL, HP, CK, MB, HH, STK, MOK.
  pose proof FOK as (F1 & F2 & F3). rewrite HFR in F2. pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (PNBK.scr_nonneg h Hh) as SC0. pose proof (PNBK.scr_nonneg hg Hg) as SCg. pose proof (PMK.kl_img segs L KL) as (IMG0 & IMG1).
  assert (STKc : L5C.stk (hl_sptop L) M1 sp' (scr hg)) by (apply (PMK.stk_call L M1 sp (scr h) sp' (scr hg) STK); [exact S1| exact S2| exact SCg| exact S3]).
  assert (CRED1 : PMSP.credit_le (pot s1) cr1) by (unfold PMSP.credit_le, PMSP.credit_keep in *; lia).
  unfold PNR.brun_spec in SPEC.
  apply (SPEC fx1 R1 M1 model1 K LBX cr1 sp' r' fb cat e s1 str sm1 ax1 HH MOK K0).
  - unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RA|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4| exact STKc].
  - unfold PMSP.frame_ok. rewrite HFR. split; [lia|]. split; [exact F2| exact F3].
  - exact ARGS.
  - exact RP.
  - exact INCS.
  - exact INV.
  - unfold PNR.o_ec, PMSP.o_ec. rewrite HOEC. exact EC.
  - exact He.
  - exact UNR.
  - exact CRED1.
  - intros fx2 R2 M2 model2 s2 sm2 ax2 cr2 RP12 POST HP2 CK2 MB2 HH2.
    pose proof POST as (RP2 & STEP2 & AXL2 & _).
    pose proof (PMK.stk_after segs L KL LBX M1 M2 sp (scr h) sp' (scr hg) _ STK HP2 S1 S2 SCg) as STK2.
    apply (KONT fx2 R2 M2 model2 s2 sm2 ax2 cr2 RP12 POST).
    + unfold PNBK.brel. cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax].
      split; [exact RP2|]. split; [exact (PMPK.src_step_trans _ _ _ _ _ _ STEP STEP2)|]. split; [exact (PNST.bax_le_trans _ _ _ AXL AXL2)|].
      split.
      { apply (PMK.hpres_of L LBX sp (scr h) _ (PNBK.be_M E0) M2).
        - apply (PMK.ek_trans L LBX sp (scr h) _ (PNBK.be_M E0) M1 M2 (PMK.ek_of_hpres L LBX sp (scr h) _ _ M1 HP)).
          apply (PMK.ek_callee L LBX LBX sp (scr h) sp' (scr hg) _ _ M1 M2 HP2); [apply incl_refl| exact S2| exact S1| intros a _ O; exact O].
        - destruct STK2 as (_ & _ & _ & _ & D). exact D.
        - apply (PMK.dk_trans L LBX sp (scr h) (PNBK.be_M E0) M1 M2 (PMK.dk_of_hpres L LBX sp (scr h) _ _ M1 HP)).
          apply (PMK.dk_callee L LBX LBX sp (scr h) sp' (scr hg) _ M1 M2 HP2); [apply incl_refl| exact S2| exact S1]. }
      split; [exact (PNBK.credit_keep_trans _ _ _ _ _ _ CK CK2)|]. split; [exact (L5C.model_but_vm_trans _ _ _ MB MB2)|].
      split; [exact HH2|]. split; [exact STK2| exact (PMFR.model_ok_but_vm model1 model2 MOK MB2)].
    + intros a n H1 H2. apply (PMKP.ek_agree_stack segs L KL LBX sp' (scr hg) _ M1 M2 a n (PMK.ek_of_hpres L LBX sp' (scr hg) _ _ _ HP2) STKc SCg H1 ltac:(lia)).
      intros i Hi. apply PMFR.outside_of_not_inW. intros I. destruct (wrun_floor fb i I); lia.
Qed.


(* [comment removed for export] *)
Lemma brel_piece_nb h LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2 : mem) (P : Z -> Prop) x' K :
  0 <= h ->
  brel h LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) ->
  PMSP.frame_ok A L sp fb -> incl (PM.vs_own str) LBX ->
  msteps segs (@mkst fx1 R1 (Z_to_bv 64 pc1) M1 (seg_rom segs)) (@mkst fx2 R2 (Z_to_bv 64 pc2) M2 (seg_rom segs)) -> mem_grows M1 M2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, {P a} + {~ P a}) ->
  (forall a, P a -> (sp - scr h <= a < sp) \/ (fb + 384 <= a < fb + 408) \/ in_block (PM.vs_own (PNM.b_nb s1)) a) ->
  PM.vstr_at segs T3 M2 (fb + 384) x' -> PM.vs_own x' = PM.vs_own (PNM.b_nb s1) -> PM.vs_cap x' = PM.vs_cap (PNM.b_nb s1) ->
  (brel h LBX sp fb str E0 (BENT M2 model1 cr1 (PNBO.set_nb s1 x' (PNM.b_ng s1)) sm1 ax1) -> srealizes segs SCFG (@PMSP.cfg segs fx2 R2 pc2 M2 model1) K) ->
  srealizes segs SCFG (@PMSP.cfg segs fx1 R1 pc1 M1 model1) K.
Proof.
  intros Hh BR FOK INCS MS MG FRZ DEC PF VS OWNx CAPx KONT.
  destruct (brel_blocks h LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR) as (BRG & OWNB & APQ).
  destruct (brel_pre h LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR) as (PA1 & IA1 & GR1 & UN1 & STK & MOK).
  pose proof FOK as (F1 & F2 & F3). rewrite HFR in F2. pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (PNBK.scr_nonneg h Hh) as SC0.
  pose proof BR as (_ & _ & _ & _ & _ & _ & HH & _). cbn [PNBK.be_M PNBK.be_cr PNBK.be_s PNBK.be_model] in HH.
  set (LB := PNM.bparser_own s1 ++ LBX) in *.
  assert (NDL : NoDup (map fst LB)) by exact (PMPK.heap_nodup L HI HIok LB cr1 M1 _ HH).
  assert (Bq : In (PM.sr_qc (PNM.b_src s1), PM.CHUNK) (PNM.bparser_own s1)) by (unfold PNM.bparser_own, PM.src_own; cbn; auto).
  assert (Bs : In (PNM.b_sb s1, PNM.BSZ * 2 ^ PNM.b_sk s1) (PNM.bparser_own s1)).
  { unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own. apply in_or_app. right. cbn. auto. }
  destruct (OWNB _ _ Bq) as (Q0 & Q4). destruct (OWNB _ _ Bs) as (S0 & S4). unfold hl_ceil in Q4, S4. unfold PNM.BSZ in S4.
  assert (NBIN : forall B m, In (B, m) (PM.vs_own (PNM.b_nb s1)) -> In (B, m) (PNM.bparser_own s1)).
  { intros B m Hin. unfold PNM.bparser_own, PNM.brest_own. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin. }
  (* [comment removed for export] *)
  assert (APn : forall B m, In (B, m) (PM.vs_own (PNM.b_nb s1)) ->
            (PM.sr_qc (PNM.b_src s1) + PM.CHUNK <= B \/ B + m <= PM.sr_qc (PNM.b_src s1))
            /\ (PNM.b_sb s1 + PNM.BSZ * 2 ^ PNM.b_sk s1 <= B \/ B + m <= PNM.b_sb s1)).
  { intros B m Hin.
    assert (HB : In (B, m) LB) by (unfold LB; apply in_or_app; left; apply NBIN; exact Hin).
    assert (Hq : In (PM.sr_qc (PNM.b_src s1), PM.CHUNK) LB) by (unfold LB; apply in_or_app; left; exact Bq).
    assert (Hs : In (PNM.b_sb s1, PNM.BSZ * 2 ^ PNM.b_sk s1) LB) by (unfold LB; apply in_or_app; left; exact Bs).
    assert (NE1 : PM.sr_qc (PNM.b_src s1) <> B).
    { apply (PMPK.fst_neq_app (PM.src_own (PNM.b_src s1)) (PNM.brest_own s1 ++ LBX) _ PM.CHUNK B m);
        [unfold LB, PNM.bparser_own in NDL; rewrite <- app_assoc in NDL; exact NDL| unfold PM.src_own; cbn; auto|].
      apply in_or_app. left. unfold PNM.brest_own. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (NE2 : PNM.b_sb s1 <> B).
    { apply (PMPK.fst_neq_app (PM.src_own (PNM.b_src s1) ++ PNM.bvec_own (PNM.b_sb s1) (PNM.b_sk s1)) (PGV8.v8_own (PNM.b_bb s1) ++ PM.vs_own (PNM.b_nb s1) ++ PM.vs_own (PNM.b_tb s1) ++ LBX) _ (PNM.BSZ * 2 ^ PNM.b_sk s1) B m);
        [unfold LB, PNM.bparser_own, PNM.brest_own in NDL; rewrite <- !app_assoc in NDL; rewrite <- !app_assoc; exact NDL
        | apply in_or_app; right; unfold PNM.bvec_own; cbn; auto
        | apply in_or_app; right; apply in_or_app; left; exact Hin]. }
    split; [exact (PMPK.blocks_apart_heap L HI HIok LB cr1 M1 _ _ _ _ _ HH Hq HB NE1)| exact (PMPK.blocks_apart_heap L HI HIok LB cr1 M1 _ _ _ _ _ HH Hs HB NE2)]. }
  apply (PNBK.brel_piece segs A AN L HI KH h LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 fx1 fx2 R1 R2 pc1 pc2 M2 P (PNBO.set_nb s1 x' (PNM.b_ng s1)) K Hh BR FOK INCS MS MG FRZ DEC);
    [| | | reflexivity| | | exact KONT].
  - intros a Pa. destruct (PF a Pa) as [X|[X|((B, m) & Hb & Hr)]]; [left; exact X| right; left; unfold PNBK.pwr; lia|].
    right. right. exists (B, m). split; [apply NBIN; exact Hb| exact Hr].
  - apply (PNBO.bparser_set_nb segs A (pa_vp_parser A) M1 M2 P FRZ MG (fb + 40) (fb + 472) s1 x'); unfold PNM.PSIZE, PNM.OFF_NB, PNM.BSZ; try lia.
    + exact PA1.
    + intros a Ha Pa. destruct (PF a Pa) as [X|[X|((B, m) & Hb & Hr)]]; [lia| lia|]. cbn [fst snd] in Hr. destruct (OWNB B m (NBIN B m Hb)). lia.
    + intros i Hi Pi. destruct (PF i Pi) as [X|[X|((B, m) & Hb & Hr)]]; [lia| lia|]. cbn [fst snd] in Hr. destruct (APn B m Hb) as (AP & _). lia.
    + intros i Hi Pi. destruct (PF i Pi) as [X|[X|((B, m) & Hb & Hr)]]; [lia| lia|]. cbn [fst snd] in Hr. destruct (APn B m Hb) as (_ & AP). unfold PNM.BSZ in AP. lia.
    + replace (fb + 40 + 344) with (fb + 384) by lia. exact VS.
  - unfold PNM.bparser_own, PNM.brest_own. cbn [PNBO.set_nb PNM.b_src PNM.b_sb PNM.b_sk PNM.b_bb PNM.b_nb PNM.b_tb]. rewrite OWNx. reflexivity.
  - unfold PNR.pot_bparser. cbn [PNBO.set_nb PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg]. unfold PM.pot_text. rewrite CAPx. reflexivity.
  - unfold PNM.bgrow_ok in *. cbn [PNBO.set_nb PNM.b_nb PNM.b_ng PNM.b_tb PNM.b_tg PNM.b_bb PNM.b_bg]. destruct GR1 as (G1 & G2 & G3).
    split; [| split; [exact G2| exact G3]].
    unfold PM.tb_ok in *. rewrite CAPx. destruct G1 as (T1 & T2 & T3). split; [exact T1|]. split; [exact T2|].
    destruct x' as [n'|c' n' p']; destruct (PNM.b_nb s1) as [n0|c0 n0 p0]; cbn [PM.vs_own PM.vs_cap] in OWNx, CAPx, T3 |- *; try exact T3.
    + discriminate OWNx.
    + discriminate OWNx.
    + injection OWNx as E1 E2. subst. exact T3.
Qed.


(* [comment removed for export] *)
Lemma brel_piece_stk h LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2 : mem) (P : Z -> Prop) l0 tl tl' K :
  0 <= h ->
  brel h LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) ->
  PMSP.frame_ok A L sp fb -> incl (PM.vs_own str) LBX ->
  msteps segs (@mkst fx1 R1 (Z_to_bv 64 pc1) M1 (seg_rom segs)) (@mkst fx2 R2 (Z_to_bv 64 pc2) M2 (seg_rom segs)) -> mem_grows M1 M2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, {P a} + {~ P a}) ->
  PNM.b_stk s1 = l0 ++ tl ->
  (forall a, P a -> (sp - scr h <= a < sp) \/ (fb + 440 <= a < fb + 448)
                    \/ (PNM.b_sb s1 + 40 * Z.of_nat (length l0) <= a < PNM.b_sb s1 + 40 * 2 ^ PNM.b_sk s1)) ->
  L5.u64_at segs M2 (fb + 440) (PNM.b_sb s1 + 40 * Z.of_nat (length (l0 ++ tl'))) ->
  (forall i, (i < length tl')%nat -> PNM.bstate_at segs M2 (PNM.b_sb s1 + 40 * Z.of_nat (length l0 + i)) (nth i tl' PNM.bs_root)) ->
  Z.of_nat (length (l0 ++ tl')) <= 2 ^ PNM.b_sk s1 ->
  (brel h LBX sp fb str E0 (BENT M2 model1 cr1 (PNBO.set_stk s1 (l0 ++ tl')) sm1 ax1) -> srealizes segs SCFG (@PMSP.cfg segs fx2 R2 pc2 M2 model1) K) ->
  srealizes segs SCFG (@PMSP.cfg segs fx1 R1 pc1 M1 model1) K.
Proof.
  intros Hh BR FOK INCS MS MG FRZ DEC ES PF VE EL' LEN' KONT.
  destruct (brel_blocks h LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR) as (BRG & OWNB & APQ).
  destruct (brel_pre h LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR) as (PA1 & IA1 & GR1 & UN1 & STK & MOK).
  pose proof FOK as (F1 & F2 & F3). rewrite HFR in F2. pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (PNBK.scr_nonneg h Hh) as SC0. pose proof LEN' as LEN2. rewrite length_app, Nat2Z.inj_add in LEN2.
  set (b := PNM.b_sb s1) in *. set (k := PNM.b_sk s1) in *.
  assert (Bq : In (PM.sr_qc (PNM.b_src s1), PM.CHUNK) (PNM.bparser_own s1)) by (unfold PNM.bparser_own, PM.src_own; cbn; auto).
  assert (Bs : In (b, 40 * 2 ^ k) (PNM.bparser_own s1)).
  { unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own, b, k. apply in_or_app. right. cbn. auto. }
  destruct (OWNB _ _ Bq) as (Q0 & Q4). destruct (OWNB _ _ Bs) as (S0 & S4). unfold hl_ceil in Q4, S4. unfold PNM.BSZ in APQ.
  apply (PNBK.brel_piece segs A AN L HI KH h LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 fx1 fx2 R1 R2 pc1 pc2 M2 P (PNBO.set_stk s1 (l0 ++ tl')) K Hh BR FOK INCS MS MG FRZ DEC);
    [| | reflexivity| reflexivity| reflexivity| exact GR1| exact KONT].
  { intros a Pa. destruct (PF a Pa) as [X|[X|X]]; [left; exact X| right; left; unfold PNBK.pwr; lia|].
    right. right. exists (b, 40 * 2 ^ k). split; [exact Bs|]. cbn [fst snd]. lia. }
  apply (PNBO.bparser_stk_upd segs A (pa_vp_parser A) M1 M2 P FRZ MG (fb + 40) (fb + 472) s1 l0 tl tl'); unfold PNM.PSIZE, PNM.OFF_STK, PNM.BSZ; fold b k; try lia.
  - exact PA1.
  - exact ES.
  - intros a Ha Pa. destruct (PF a Pa) as [X|[X|X]]; lia.
  - intros i Hi Pi. destruct (PF i Pi) as [X|[X|X]]; [lia| lia|]. destruct APQ; lia.
  - intros i Hi Pi. destruct (PF i Pi) as [X|[X|X]]; lia.
  - replace (fb + 40 + 392 + 8) with (fb + 440) by lia. exact VE.
  - exact EL'.
Qed.


(* [comment removed for export] *)
Lemma brel_piece_hdstk h LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2 : mem) (P : Z -> Prop) mo dn l0 tl tl' K :
  0 <= h ->
  brel h LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) ->
  PMSP.frame_ok A L sp fb -> incl (PM.vs_own str) LBX ->
  msteps segs (@mkst fx1 R1 (Z_to_bv 64 pc1) M1 (seg_rom segs)) (@mkst fx2 R2 (Z_to_bv 64 pc2) M2 (seg_rom segs)) -> mem_grows M1 M2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, {P a} + {~ P a}) ->
  PNM.b_stk s1 = l0 ++ tl ->
  (forall a, P a -> (sp - scr h <= a < sp) \/ (fb + 48 <= a < fb + 50) \/ (fb + 440 <= a < fb + 448)
                    \/ (PNM.b_sb s1 + 40 * Z.of_nat (length l0) <= a < PNM.b_sb s1 + 40 * 2 ^ PNM.b_sk s1)) ->
  L5.u8_at segs M2 (fb + 48) mo -> L5.u8_at segs M2 (fb + 49) dn -> (mo = 0 \/ mo = 1) -> (dn = 0 \/ dn = 1) ->
  L5.u64_at segs M2 (fb + 440) (PNM.b_sb s1 + 40 * Z.of_nat (length (l0 ++ tl'))) ->
  (forall i, (i < length tl')%nat -> PNM.bstate_at segs M2 (PNM.b_sb s1 + 40 * Z.of_nat (length l0 + i)) (nth i tl' PNM.bs_root)) ->
  Z.of_nat (length (l0 ++ tl')) <= 2 ^ PNM.b_sk s1 ->
  (brel h LBX sp fb str E0 (BENT M2 model1 cr1 (PNM.BPST mo dn (PNM.b_src s1) (PNM.b_bb s1) (PNM.b_nb s1) (PNM.b_tb s1) (PNM.b_ng s1) (PNM.b_tg s1) (PNM.b_bg s1) (PNM.b_sb s1) (PNM.b_sk s1) (l0 ++ tl')) sm1 ax1) ->
   srealizes segs SCFG (@PMSP.cfg segs fx2 R2 pc2 M2 model1) K) ->
  srealizes segs SCFG (@PMSP.cfg segs fx1 R1 pc1 M1 model1) K.
Proof.
  intros Hh BR FOK INCS MS MG FRZ DEC ES PF U8 U9 M01 D01 VE EL' LEN' KONT.
  destruct (brel_blocks h LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR) as (BRG & OWNB & APQ).
  destruct (brel_pre h LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 BR) as (PA1 & IA1 & GR1 & UN1 & STK & MOK).
  pose proof FOK as (F1 & F2 & F3). rewrite HFR in F2. pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (PNBK.scr_nonneg h Hh) as SC0. pose proof LEN' as LEN2. rewrite length_app, Nat2Z.inj_add in LEN2.
  set (b := PNM.b_sb s1) in *. set (k := PNM.b_sk s1) in *.
  assert (Bq : In (PM.sr_qc (PNM.b_src s1), PM.CHUNK) (PNM.bparser_own s1)) by (unfold PNM.bparser_own, PM.src_own; cbn; auto).
  assert (Bs : In (b, 40 * 2 ^ k) (PNM.bparser_own s1)).
  { unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own, b, k. apply in_or_app. right. cbn. auto. }
  destruct (OWNB _ _ Bq) as (Q0 & Q4). destruct (OWNB _ _ Bs) as (S0 & S4). unfold hl_ceil in Q4, S4. unfold PNM.BSZ in APQ.
  apply (PNBK.brel_piece segs A AN L HI KH h LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 fx1 fx2 R1 R2 pc1 pc2 M2 P
           (PNM.BPST mo dn (PNM.b_src s1) (PNM.b_bb s1) (PNM.b_nb s1) (PNM.b_tb s1) (PNM.b_ng s1) (PNM.b_tg s1) (PNM.b_bg s1) (PNM.b_sb s1) (PNM.b_sk s1) (l0 ++ tl')) K Hh BR FOK INCS MS MG FRZ DEC);
    [| | reflexivity| reflexivity| reflexivity| exact GR1| exact KONT].
  { intros a Pa. destruct (PF a Pa) as [X|[X|[X|X]]]; [left; exact X| right; left; unfold PNBK.pwr; lia| right; left; unfold PNBK.pwr; lia|].
    right. right. exists (b, 40 * 2 ^ k). split; [exact Bs|]. cbn [fst snd]. lia. }
  apply (PNBO.bparser_hd_stk_upd segs A (pa_vp_parser A) M1 M2 P FRZ MG (fb + 40) (fb + 472) s1 mo dn l0 tl tl'); unfold PNM.PSIZE, PNM.OFF_STK, PNM.BSZ; fold b k; try lia.
  - exact PA1.
  - exact ES.
  - intros a Ha Pa. destruct (PF a Pa) as [X|[X|[X|X]]]; lia.
  - intros i Hi Pi. destruct (PF i Pi) as [X|[X|[X|X]]]; [lia| lia| lia|]. destruct APQ; lia.
  - intros i Hi Pi. destruct (PF i Pi) as [X|[X|[X|X]]]; lia.
  - replace (fb + 40 + 8) with (fb + 48) by lia. exact U8.
  - replace (fb + 40 + 9) with (fb + 49) by lia. exact U9.
  - replace (fb + 40 + 392 + 8) with (fb + 440) by lia. exact VE.
  - exact EL'.
Qed.

End Kit.
End PNBK2.
