(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrObjA_b PnAParKit_b PnAReset1_b PnOwnerOkA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNBKA.
Import L5A. Import L5CA. Import L5SAR.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation pot := (fun L ar s => PMSPA.scA L (PNRA.pot_bparser L ar s)).

(* [comment removed for export] *)
Definition own (E : Z) (R : bvmap 5 word) (M : mem) : Prop :=
  L5.u64_at RSEGS M (E - 8) (bv_unsigned (getr R (reg 1))) /\ L5.u64_at RSEGS M (E - 16) (bv_unsigned (getr R (reg 8)))
  /\ L5.u64_at RSEGS M (E - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M (E - 32) (bv_unsigned (getr R (reg 18)))
  /\ L5.u64_at RSEGS M (E - 40) (bv_unsigned (getr R (reg 19))) /\ L5.u64_at RSEGS M (E - 48) (bv_unsigned (getr R (reg 20)))
  /\ L5.u64_at RSEGS M (E - 56) (bv_unsigned (getr R (reg 21))) /\ L5.u64_at RSEGS M (E - 64) (bv_unsigned (getr R (reg 22)))
  /\ L5.u64_at RSEGS M (E - 72) (bv_unsigned (getr R (reg 23))) /\ L5.u64_at RSEGS M (E - 80) (bv_unsigned (getr R (reg 24)))
  /\ L5.u64_at RSEGS M (E - 88) (bv_unsigned (getr R (reg 25))) /\ L5.u64_at RSEGS M (E - 96) (bv_unsigned (getr R (reg 26)))
  /\ L5.u64_at RSEGS M (E - 104) (bv_unsigned (getr R (reg 27))).
Definition ocell (E : Z) (a : Z) : Prop := E - 104 <= a < E.
Lemma own_agree E R M1 M1' : 0 <= E - 104 -> E <= 2 ^ 64 ->
  own E R M1 -> (forall a, ocell E a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> own E R M1'.
Proof.
  intros H0 H1 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13) AG. unfold own, ocell in *.
  repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.

(* [comment removed for export] *)
Lemma aacc_local (M : mem) F off k v :
  F / 8 * 8 = F -> off mod 8 = 0 -> 0 <= off -> 0 <= F -> ((k = 8 /\ v = 0) \/ (1 <= k <= 7 /\ v = k)) ->
  byte_at M (F / 8 + off / 8 + 2147450880) v -> aacc M (F + off) k.
Proof.
  intros F8 O8 O0 F0 Hk B a Ha. unfold S, SB.
  assert (E : a / 8 = F / 8 + off / 8) by (destruct Hk as [(-> & _)|(Hk & _)]; lia).
  rewrite E. destruct Hk as [(-> & ->)|(Hk & ->)]; [left; exact B| right; exists k; split; [exact B| split; [exact Hk| lia]]].
Qed.

(* [comment removed for export] *)
Lemma depA_img a : PNST.dep PMA.AD PMA.AN a -> 65536 <= a < 6905856.
Proof.
  intros [(iv & Hin & Hr)|[Hc|(iv & Hin & Hr)]].
  - unfold PNST.pn_foot in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + pose proof (PMASK.dep_img a (or_introl (ex_intro _ iv (conj Hin Hr)))). lia.
    + unfold PNL.pn_d128_foot in Hin. cbn [PNL.pn_inf_guard PNL.pn_inf_obj PNL.pn_nan_guard PNL.pn_nan_obj PMA.AN NADDR_A] in Hin.
      repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
  - pose proof (PMASK.dep_img a (or_intror (or_introl Hc))). lia.
  - pose proof (PMASK.dep_img a (or_intror (or_intror (ex_intro _ iv (conj Hin Hr))))). lia.
Qed.

Lemma iv_apart x n y m : 0 < n -> 0 < m -> (forall a, x <= a < x + n -> ~ (y <= a < y + m)) -> x + n <= y \/ y + m <= x.
Proof.
  intros Hn Hm H. destruct (Z_le_gt_dec (x + n) y) as [X|X]; [left; exact X|]. destruct (Z_le_gt_dec (y + m) x) as [Y|Y]; [right; exact Y|].
  exfalso. apply (H (Z.max x y)); lia.
Qed.

Lemma credit_keep_refl cr p : PMSP.credit_keep cr cr p p.
Proof. unfold PMSP.credit_keep. lia. Qed.
Lemma credit_keep_trans c1 c2 c3 p1 p2 p3 : PMSP.credit_keep c1 c2 p1 p2 -> PMSP.credit_keep c2 c3 p2 p3 -> PMSP.credit_keep c1 c3 p1 p3.
Proof. unfold PMSP.credit_keep. lia. Qed.
Lemma src_step_refl src sm : PMSP.src_step src src sm sm.
Proof. unfold PMSP.src_step. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros X; exact X| lia]. Qed.
Lemma src_step_trans s1 s2 s3 m1 m2 m3 : PMSP.src_step s1 s2 m1 m2 -> PMSP.src_step s2 s3 m2 m3 -> PMSP.src_step s1 s3 m1 m3.
Proof.
  unfold PMSP.src_step. intros (A1 & A2 & A3 & A4 & A5) (B1 & B2 & B3 & B4 & B5).
  split; [rewrite B1; exact A1|]. split; [rewrite B2; exact A2|]. split; [lia|]. split; [intros X; apply B4, A4, X| lia].
Qed.

Lemma own_with_srcB s src' : PM.sr_qc src' = PM.sr_qc (PNM.b_src s) -> PNM.bparser_own (PNM.with_srcB s src') = PNM.bparser_own s.
Proof. intros E. unfold PNM.bparser_own, PNM.brest_own, PM.src_own. cbn [PNM.with_srcB PNM.b_src PNM.b_sb PNM.b_sk PNM.b_bb PNM.b_nb PNM.b_tb]. rewrite E. reflexivity. Qed.
Lemma pre_with_srcB s src' : PNM.bgrow_ok s -> PNM.bgrow_ok (PNM.with_srcB s src').
Proof. intros X. exact X. Qed.

(* [comment removed for export] *)
Definition set_cs (w : Z) (s : PNM.bpst) (x : PM.vstr) (g : Z) : PNM.bpst := if Z.eqb w 0 then PNBO.set_nb s x g else PNBO.set_tb s x g.
(* [comment removed for export] *)
Definition own_rest (w : Z) (s : PNM.bpst) : list (Z * Z) :=
  PM.src_own (PNM.b_src s) ++ PNM.bvec_own (PNM.b_sb s) (PNM.b_sk s) ++ PGV8.v8_own (PNM.b_bb s) ++ PM.vs_own (PNRA.bcs_str (1 - w) s).
Lemma bcs_off_rng w : w = 0 \/ w = 1 -> 344 <= PNRA.bcs_off w <= 368.
Proof. intros [->| ->]; unfold PNRA.bcs_off, PNM.OFF_NB, PNM.OFF_TB; cbn; lia. Qed.

Lemma ln_nodup_perm (l l' : list (Z * Z)) : Permutation l l' -> base.NoDup (map fst l) -> base.NoDup (map fst l').
Proof.
  intros P ND. apply base.NoDup_ListNoDup. apply base.NoDup_ListNoDup in ND.
  eapply Permutation_NoDup; [|exact ND]. apply Permutation_map. exact P.
Qed.
Lemma perm4 {T} (a b c n t x : list T) : Permutation ((a ++ b ++ c ++ n ++ t) ++ x) (n ++ (a ++ b ++ c ++ t) ++ x).
Proof.
  apply (Permutation_trans (l' := (a ++ b ++ c) ++ n ++ t ++ x)); [rewrite <- !app_assoc; apply Permutation_refl|].
  apply (Permutation_trans (Permutation_app_swap_app (a ++ b ++ c) n (t ++ x))). rewrite <- !app_assoc. apply Permutation_refl.
Qed.
Lemma perm5 {T} (a b c n t x : list T) : Permutation ((a ++ b ++ c ++ n ++ t) ++ x) (t ++ (a ++ b ++ c ++ n) ++ x).
Proof.
  apply (Permutation_trans (l' := (a ++ b ++ c ++ n) ++ t ++ x)); [rewrite <- !app_assoc; apply Permutation_refl|].
  apply (Permutation_app_swap_app (a ++ b ++ c ++ n) t x).
Qed.
Lemma perm_cs w s LBX : w = 0 \/ w = 1 -> Permutation (PNM.bparser_own s ++ LBX) (PM.vs_own (PNRA.bcs_str w s) ++ own_rest w s ++ LBX).
Proof.
  intros Hw. unfold own_rest, PNM.bparser_own, PNM.brest_own, PNRA.bcs_str. destruct Hw as [->| ->]; cbn [Z.eqb Z.sub Z.pos_sub]; [apply perm4| apply perm5].
Qed.
Lemma perm_cs' w s x' g' LBX : w = 0 \/ w = 1 -> Permutation (PM.vs_own x' ++ own_rest w s ++ LBX) (PNM.bparser_own (set_cs w s x' g') ++ LBX).
Proof.
  intros Hw. apply Permutation_sym.
  assert (E : own_rest w s = own_rest w (set_cs w s x' g')).
  { unfold own_rest, set_cs, PNRA.bcs_str. destruct Hw as [->| ->]; cbn [Z.eqb Z.sub Z.pos_sub PNBO.set_nb PNBO.set_tb PNM.b_src PNM.b_sb PNM.b_sk PNM.b_bb PNM.b_nb PNM.b_tb]; reflexivity. }
  assert (E' : x' = PNRA.bcs_str w (set_cs w s x' g')).
  { unfold set_cs, PNRA.bcs_str. destruct Hw as [->| ->]; cbn [Z.eqb PNBO.set_nb PNBO.set_tb PNM.b_nb PNM.b_tb]; reflexivity. }
  rewrite E. rewrite E' at 2. apply perm_cs. exact Hw.
Qed.
Lemma incl_rest w s : incl (own_rest w s) (PNM.bparser_own s).
Proof.
  unfold own_rest, PNM.bparser_own, PNM.brest_own, PNRA.bcs_str. intros b. destruct (Z.eqb (1 - w) 0); rewrite !in_app_iff; tauto.
Qed.

(* [comment removed for export] *)
Lemma bparser_set_csS (M M' : mem) vp op ois s w x' g' :
  (w = 0 \/ w = 1) -> 0 <= op -> op + 416 <= 2 ^ 64 ->
  (forall i, op <= i < op + 416 -> ~ (op + PNRA.bcs_off w <= i < op + PNRA.bcs_off w + 24) -> PNBOA.snt M M' i) ->
  (forall i, op <= i < op + 416 -> PNBOA.sns M M' i) ->
  (forall B m, In (B, m) (own_rest w s) -> 0 <= B /\ B + m <= 2 ^ 64 /\ PMFA.agA M M' B m) ->
  PM.vstr_at RSEGS PMSPA.accA M' (op + PNRA.bcs_off w) x' ->
  PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA vp M op ois s -> PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA vp M' op ois (set_cs w s x' g').
Proof.
  intros Hw Ho Ho' No So AGb VS' PA. pose proof PA as (_ & _ & _ & H8 & H9 & _ & _ & _ & SRC & _ & _ & BB & NB & TB & STK & M01 & D01).
  pose proof (bcs_off_rng w Hw) as HOFF.
  unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *.
  assert (BLK : forall B m, In (B, m) (own_rest w s) -> 0 <= m -> (forall i, B <= i < B + m -> PNBOA.snt M M' i) /\ (forall i, B <= i < B + m -> PNBOA.sns M M' i) /\ 0 <= B /\ B + m <= 2 ^ 64).
  { intros B m Hi Hm. destruct (AGb B m Hi) as (B0 & B1 & AG). split; [exact (PNBOA.agA_snt M M' _ _ AG)|]. split; [exact (PNBOA.agA_sns M M' _ _ AG)|]. lia. }
  assert (BLKG : forall B m, In (B, m) (own_rest w s) -> 0 <= m -> B mod 8 = 0 -> forall i, B <= i < B + PNBOA.gspan m -> PNBOA.sns M M' i).
  { intros B m Hi Hm HB. destruct (AGb B m Hi) as (B0 & B1 & [_ AG]). exact (PNBOA.agsh_gspan M M' B m HB Hm AG). }
  pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & _ & Qr & _). pose proof STK as (_ & _ & _ & Hk & _).
  assert (Iq : In (PM.sr_qc (PNM.b_src s), PM.CHUNK) (own_rest w s)) by (unfold own_rest, PM.src_own; left; reflexivity).
  assert (Is : In (PNM.b_sb s, PNM.BSZ * 2 ^ PNM.b_sk s) (own_rest w s)) by (unfold own_rest, PNM.bvec_own; apply in_or_app; right; left; reflexivity).
  assert (Ib : forall B m, In (B, m) (PGV8.v8_own (PNM.b_bb s)) -> In (B, m) (own_rest w s)) by (intros B m X; unfold own_rest; rewrite !in_app_iff; tauto).
  assert (Io : forall B m, In (B, m) (PM.vs_own (PNRA.bcs_str (1 - w) s)) -> In (B, m) (own_rest w s)) by (intros B m X; unfold own_rest; rewrite !in_app_iff; tauto).
  destruct (BLK _ _ Iq ltac:(unfold PM.CHUNK; lia)) as (NTq & NSq & Q0 & Q1).
  destruct (BLK _ _ Is ltac:(unfold PNM.BSZ; nia)) as (NTs & NSs & S0 & S1).
  set (Yd := fun i => M (Z_to_bv 64 i) <> None -> M' (Z_to_bv 64 i) <> None).
  assert (YS : forall i, PNBOA.snt M M' i -> Yd i) by (intros i E D; unfold PNBOA.snt in E; unfold Yd; rewrite E; exact D).
  assert (YV : forall i, op + PNRA.bcs_off w <= i < op + PNRA.bcs_off w + 24 -> Yd i).
  { intros i Hi _. destruct VS' as (D' & _). replace i with (op + PNRA.bcs_off w + (i - (op + PNRA.bcs_off w))) by lia. apply D'. lia. }
  pose proof (PNBOA.bparser_at_xfer RSEGS PMA.AD vp M M' (PNBOA.snt M M') Yd (PNBOA.sns M M') (PNBOA.sAGX M M') (fun i H => H) (PNBOA.sSHX M M')) as XFER.
  pose proof (PNBOA.src_keep_x RSEGS M M' (PNBOA.snt M M') (PNBOA.sns M M') (PNBOA.sAGX M M') (PNBOA.sSHX M M')) as SRCK.
  pose proof (PNBOA.v8_keep_x RSEGS M M' (PNBOA.snt M M') Yd (PNBOA.sns M M') (PNBOA.sAGX M M') (fun i H => H) (PNBOA.sSHX M M')) as V8K.
  pose proof (PNBOA.vstr_keep_x RSEGS M M' (PNBOA.snt M M') Yd (PNBOA.sns M M') (PNBOA.sAGX M M') (fun i H => H) (PNBOA.sSHX M M')) as VSK.
  pose proof (PNBOA.bvec_keep_x RSEGS M M' (PNBOA.snt M M') (PNBOA.sns M M') (PNBOA.sAGX M M') (PNBOA.sSHX M M')) as BVK.
  assert (OTHER : forall o y, (o = op + 344 /\ y = PNM.b_nb s /\ w = 1) \/ (o = op + 368 /\ y = PNM.b_tb s /\ w = 0) ->
            PM.vstr_at RSEGS PMSPA.accA M o y -> PM.vstr_at RSEGS PMSPA.accA M' o y).
  { intros o y Hoy VY. assert (Hoi : op <= o /\ o + 24 <= op + 416 /\ (o + 24 <= op + PNRA.bcs_off w \/ op + PNRA.bcs_off w + 24 <= o) /\ y = PNRA.bcs_str (1 - w) s).
    { unfold PNRA.bcs_off, PNRA.bcs_str, PNM.OFF_NB, PNM.OFF_TB. destruct Hoy as [(-> & -> & ->)|(-> & -> & ->)]; cbn; (split; [lia| split; [lia| split; [lia| reflexivity]]]). }
    destruct Hoi as (O1 & O2 & O3 & ->).
    apply (VSK o (PNRA.bcs_str (1 - w) s)); [lia| lia| intros i Hi; apply No; lia| intros i Hi; apply YS; apply No; lia| intros i Hi; apply So; lia| | | exact VY].
    - intros B m Hi. pose proof (Io B m Hi) as OI. destruct (PNRA.bcs_str (1 - w) s) eqn:EVS; cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst].
      unfold PM.vstr_at in VY. destruct VY as (_ & _ & _ & _ & _ & Hn & Hc & _). destruct (BLK _ _ OI ltac:(lia)) as (X & _). intros i Hr. apply YS. apply X. exact Hr.
    - intros B m Hi. pose proof (Io B m Hi) as OI. destruct (PNRA.bcs_str (1 - w) s) eqn:EVS; cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst].
      unfold PM.vstr_at in VY. destruct VY as (_ & _ & _ & _ & _ & Hn & Hc & _). destruct (BLK _ _ OI ltac:(lia)) as (_ & X & _). exact X. }
  assert (Es : set_cs w s x' g' = PNM.BPST (PNM.b_more s) (PNM.b_done s) (PNM.b_src s) (PNM.b_bb s) (PNM.b_nb (set_cs w s x' g')) (PNM.b_tb (set_cs w s x' g')) (PNM.b_ng (set_cs w s x' g')) (PNM.b_tg (set_cs w s x' g')) (PNM.b_bg s) (PNM.b_sb s) (PNM.b_sk s) (PNM.b_stk s)).
  { unfold set_cs. destruct Hw as [->| ->]; cbn [Z.eqb]; destruct s; reflexivity. }
  rewrite Es.
  apply (XFER op ois s _ ltac:(lia) ltac:(unfold PNM.PSIZE; lia) PA); unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK;
    cbn [PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk].
  - intros i Hi. destruct (Z_lt_le_dec i (op + PNRA.bcs_off w)) as [X|X]; [apply YS; apply No; lia|]. destruct (Z_lt_le_dec i (op + PNRA.bcs_off w + 24)) as [X'|X']; [apply YV; lia| apply YS; apply No; lia].
  - exact So.
  - intros i Hi. apply No; lia.
  - intros i Hi. apply No; lia.
  - intros i Hi. apply No; lia.
  - intros i Hi. apply No; lia.
  - apply (L5C.u8_at_agree RSEGS M M'); [apply PNBOA.sAGX; [lia|lia|intros i Hi; apply No; lia]|lia|lia|exact H8].
  - apply (L5C.u8_at_agree RSEGS M M'); [apply PNBOA.sAGX; [lia|lia|intros i Hi; apply No; lia]|lia|lia|exact H9].
  - exact M01.
  - exact D01.
  - apply SRCK; [lia|lia|lia|lia| intros i Hi; apply No; lia| exact NTq| intros i Hi; apply So; lia| exact NSq| exact SRC].
  - apply V8K; [lia|lia| intros i Hi; apply No; lia| intros i Hi; apply So; lia| | | exact BB].
    + intros B m Hi i Hr. pose proof (Ib B m Hi) as OI. destruct (PNM.b_bb s) eqn:EBB; cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst].
      unfold PGV8.v8_at in BB. destruct BB as (_ & _ & _ & _ & _ & Hn & Hc & _). destruct (BLK _ _ OI ltac:(lia)) as (X & _). apply YS. apply X. exact Hr.
    + intros B m Hi. pose proof (Ib B m Hi) as OI. destruct (PNM.b_bb s) eqn:EBB; cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst].
      unfold PGV8.v8_at in BB. destruct BB as (_ & _ & _ & _ & _ & Hn & Hc & _ & Hal & _). exact (BLKG _ _ OI ltac:(lia) (PMFA.mod16_8 _ Hal)).
  - unfold set_cs. destruct Hw as [->| ->]; cbn [Z.eqb PNBO.set_nb PNBO.set_tb PNM.b_nb].
    + unfold PNRA.bcs_off, PNM.OFF_NB in VS'. cbn [Z.eqb] in VS'. exact VS'.
    + apply OTHER; [left; auto| exact NB].
  - unfold set_cs. destruct Hw as [->| ->]; cbn [Z.eqb PNBO.set_nb PNBO.set_tb PNM.b_tb].
    + apply OTHER; [right; auto| exact TB].
    + unfold PNRA.bcs_off, PNM.OFF_TB in VS'. cbn [Z.eqb] in VS'. exact VS'.
  - apply BVK; [lia|lia|lia|lia| intros i Hi; apply No; lia| exact NTs| exact NSs| exact STK].
Qed.

(* [comment removed for export] *)
Lemma bparser_set_moreS (M M' : mem) vp op ois s v :
  6905856 <= op -> op + 416 <= 2 ^ 64 ->
  (forall i, op <= i < op + 416 -> ~ (op + 8 <= i < op + 9) -> PNBOA.snt M M' i) ->
  (forall i, op <= i < op + 416 -> PNBOA.sns M M' i) ->
  (forall B m, In (B, m) (PNM.bparser_own s) -> 0 <= B /\ B + m <= 2 ^ 64 /\ PMFA.agA M M' B m) ->
  L5.u8_at RSEGS M' (op + 8) v -> (v = 0 \/ v = 1) ->
  PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA vp M op ois s -> PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA vp M' op ois (PNBO.set_more s v).
Proof.
  intros Ho Ho' No So AGb U8 V01 PA. pose proof PA as (_ & Dop & _ & H8 & H9 & _ & _ & _ & SRC & _ & _ & BB & NB & TB & STK & M01 & D01).
  unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *.
  assert (BLK : forall B m, In (B, m) (PNM.bparser_own s) -> 0 <= m -> (forall i, B <= i < B + m -> PNBOA.snt M M' i) /\ (forall i, B <= i < B + m -> PNBOA.sns M M' i) /\ 0 <= B /\ B + m <= 2 ^ 64).
  { intros B m Hi Hm. destruct (AGb B m Hi) as (B0 & B1 & AG). split; [exact (PNBOA.agA_snt M M' _ _ AG)|]. split; [exact (PNBOA.agA_sns M M' _ _ AG)|]. lia. }
  assert (BLKG : forall B m, In (B, m) (PNM.bparser_own s) -> 0 <= m -> B mod 8 = 0 -> forall i, B <= i < B + PNBOA.gspan m -> PNBOA.sns M M' i).
  { intros B m Hi Hm HB. destruct (AGb B m Hi) as (B0 & B1 & [_ AG]). exact (PNBOA.agsh_gspan M M' B m HB Hm AG). }
  pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & _ & Qr & _). pose proof STK as (_ & _ & _ & Hk & _).
  destruct (BLK _ _ (PNBOA.PNM_own_src s) ltac:(unfold PM.CHUNK; lia)) as (NTq & NSq & Q0 & Q1).
  destruct (BLK _ _ (PNBOA.PNM_own_stk s) ltac:(unfold PNM.BSZ; nia)) as (NTs & NSs & S0 & S1).
  set (Yd := fun i => M (Z_to_bv 64 i) <> None -> M' (Z_to_bv 64 i) <> None).
  assert (YS : forall i, PNBOA.snt M M' i -> Yd i) by (intros i E D; unfold PNBOA.snt in E; unfold Yd; rewrite E; exact D).
  assert (Y8 : Yd (op + 8)).
  { intros _. rewrite (L5ADHR.byte_of_u8 M' (op + 8) v U8 ltac:(right; lia) ltac:(lia)). discriminate. }
  pose proof (PNBOA.bparser_at_xfer RSEGS PMA.AD vp M M' (PNBOA.snt M M') Yd (PNBOA.sns M M') (PNBOA.sAGX M M') (fun i H => H) (PNBOA.sSHX M M')) as XFER.
  pose proof (PNBOA.src_keep_x RSEGS M M' (PNBOA.snt M M') (PNBOA.sns M M') (PNBOA.sAGX M M') (PNBOA.sSHX M M')) as SRCK.
  pose proof (PNBOA.v8_keep_x RSEGS M M' (PNBOA.snt M M') Yd (PNBOA.sns M M') (PNBOA.sAGX M M') (fun i H => H) (PNBOA.sSHX M M')) as V8K.
  pose proof (PNBOA.vstr_keep_x RSEGS M M' (PNBOA.snt M M') Yd (PNBOA.sns M M') (PNBOA.sAGX M M') (fun i H => H) (PNBOA.sSHX M M')) as VSK.
  pose proof (PNBOA.bvec_keep_x RSEGS M M' (PNBOA.snt M M') (PNBOA.sns M M') (PNBOA.sAGX M M') (PNBOA.sSHX M M')) as BVK.
  assert (VKEEP : forall o y, (o = op + 344 /\ y = PNM.b_nb s) \/ (o = op + 368 /\ y = PNM.b_tb s) -> PM.vstr_at RSEGS PMSPA.accA M o y -> PM.vstr_at RSEGS PMSPA.accA M' o y).
  { intros o y Hoy VY. assert (Hoi : op + 16 <= o /\ o + 24 <= op + 416 /\ forall B m, In (B, m) (PM.vs_own y) -> In (B, m) (PNM.bparser_own s)).
    { destruct Hoy as [(-> & ->)|(-> & ->)]; (split; [lia| split; [lia|]]); [intros B m X; exact (PNBOA.PNM_own_nb s B m X)| intros B m X; exact (PNBOA.PNM_own_tb s B m X)]. }
    destruct Hoi as (O1 & O2 & OWNy).
    apply (VSK o y); [lia| lia| intros i Hi; apply No; lia| intros i Hi; apply YS; apply No; lia| intros i Hi; apply So; lia| | | exact VY].
    - intros B m Hi. pose proof (OWNy B m Hi) as OI. destruct y eqn:EVS; cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst].
      unfold PM.vstr_at in VY. destruct VY as (_ & _ & _ & _ & _ & Hn & Hc & _). destruct (BLK _ _ OI ltac:(lia)) as (X & _). intros i Hr. apply YS. apply X. exact Hr.
    - intros B m Hi. pose proof (OWNy B m Hi) as OI. destruct y eqn:EVS; cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst].
      unfold PM.vstr_at in VY. destruct VY as (_ & _ & _ & _ & _ & Hn & Hc & _). destruct (BLK _ _ OI ltac:(lia)) as (_ & X & _). exact X. }
  replace (PNBO.set_more s v) with (PNM.BPST v (PNM.b_done s) (PNM.b_src s) (PNM.b_bb s) (PNM.b_nb s) (PNM.b_tb s) (PNM.b_ng s) (PNM.b_tg s) (PNM.b_bg s) (PNM.b_sb s) (PNM.b_sk s) (PNM.b_stk s)) by (destruct s; reflexivity).
  apply (XFER op ois s _ ltac:(lia) ltac:(unfold PNM.PSIZE; lia) PA); unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK;
    cbn [PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk].
  - intros i Hi. destruct (Z.eq_dec i (op + 8)) as [->|X]; [exact Y8| apply YS; apply No; lia].
  - exact So.
  - intros i Hi. apply No; lia.
  - intros i Hi. apply No; lia.
  - intros i Hi. apply No; lia.
  - intros i Hi. apply No; lia.
  - exact U8.
  - apply (L5C.u8_at_agree RSEGS M M'); [apply PNBOA.sAGX; [lia|lia|intros i Hi; apply No; lia]|lia|lia|exact H9].
  - exact V01.
  - exact D01.
  - apply SRCK; [lia|lia|lia|lia| intros i Hi; apply No; lia| exact NTq| intros i Hi; apply So; lia| exact NSq| exact SRC].
  - apply V8K; [lia|lia| intros i Hi; apply No; lia| intros i Hi; apply So; lia| | | exact BB].
    + intros B m Hi i Hr. pose proof (PNBOA.PNM_own_bb s B m Hi) as OI. destruct (PNM.b_bb s) eqn:EBB; cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst].
      unfold PGV8.v8_at in BB. destruct BB as (_ & _ & _ & _ & _ & Hn & Hc & _). destruct (BLK _ _ OI ltac:(lia)) as (X & _). apply YS. apply X. exact Hr.
    + intros B m Hi. pose proof (PNBOA.PNM_own_bb s B m Hi) as OI. destruct (PNM.b_bb s) eqn:EBB; cbn in Hi; [destruct Hi| destruct Hi as [Hi|[]]; inversion Hi; subst].
      unfold PGV8.v8_at in BB. destruct BB as (_ & _ & _ & _ & _ & Hn & Hc & _ & Hal & _). exact (BLKG _ _ OI ltac:(lia) (PMFA.mod16_8 _ Hal)).
  - apply VKEEP; [left; auto| exact NB].
  - apply VKEEP; [right; auto| exact TB].
  - apply BVK; [lia|lia|lia|lia| intros i Hi; apply No; lia| exact NTs| exact NSs| exact STK].
Qed.

(* [comment removed for export] *)
Lemma btop_pos_refl s : PNRA.binv s -> PNRA.btop_pos s s.
Proof.
  intros (_ & (L1 & _ & _ & _ & OK)).
  destruct (exists_last (l := PNM.b_stk s) ltac:(intros X; rewrite X in L1; cbn in L1; lia)) as (l & c & E).
  exists l, c, c. split; [exact E|]. split; [exact E|].
  split; [|repeat split; reflexivity].
  pose proof (OK (length l) ltac:(rewrite E, length_app; cbn; lia)) as H. rewrite E, nth_middle in H. exact H.
Qed.
Lemma btop_pos_trans s1 s2 s3 : PNRA.btop_pos s1 s2 -> PNRA.btop_pos s2 s3 -> PNRA.btop_pos s1 s3.
Proof.
  intros (l & c & c' & E1 & E2 & OK & Hm & Hl & Ht & Hi) (l2 & d & d' & F1 & F2 & OK2 & Hm2 & Hl2 & Ht2 & Hi2).
  rewrite E2 in F1. destruct (app_inj_tail l l2 c' d F1) as (<- & <-).
  exists l, c, d'. split; [exact E1|]. split; [exact F2|]. split; [exact OK2|]. rewrite Hm2, Hl2, Ht2, Hi2. repeat split; assumption.
Qed.
Lemma bstack_shape_top l c c' :
  PNRA.bstack_shape (l ++ [c]) -> PNM.bstate_ok c' -> PNM.bs_mode c' = PNM.bs_mode c -> PNRA.bstack_shape (l ++ [c']).
Proof.
  intros (L1 & L2 & B0 & CT & OK) OK' Hm. unfold PNRA.bstack_shape. rewrite length_app in *. cbn [length] in *.
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
  PNRA.binv s -> PNM.b_stk s = l ++ [c] -> PNM.bstate_ok c' -> PNM.bs_mode c' = PNM.bs_mode c -> PNRA.binv (PNBO.set_stk s (l ++ [c'])).
Proof.
  intros (ID & SH) E OK Hm. unfold PNRA.binv. cbn [PNBO.set_stk PNM.b_more PNM.b_done PNM.b_stk].
  split; [exact ID|]. rewrite E in SH. exact (bstack_shape_top l c c' SH OK Hm).
Qed.
Lemma btop_pos_set_stk s l c c' :
  PNM.b_stk s = l ++ [c] -> PNM.bstate_ok c' -> PNM.bs_mode c' = PNM.bs_mode c -> PNM.bs_len c' = PNM.bs_len c ->
  PNM.bs_type c' = PNM.bs_type c -> PNM.bs_idx c' = PNM.bs_idx c -> PNRA.btop_pos s (PNBO.set_stk s (l ++ [c'])).
Proof.
  intros E OK Hm Hl Ht Hi. exists l, c, c'. cbn [PNBO.set_stk PNM.b_stk].
  split; [exact E|]. split; [reflexivity|]. split; [exact OK|]. split; [exact Hm|]. split; [exact Hl|]. split; [exact Ht| exact Hi].
Qed.

Lemma mem_eq_of_agree (M3 M1 : mem) : (forall a, 0 <= a < 2 ^ 64 -> ~ False -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> M3 = M1.
Proof.
  intros H. apply functional_extensionality. intros x. rewrite <- (Z_to_bv_bv_unsigned 64 x).
  pose proof (bv_unsigned_in_range 64 x) as B. change (bv_modulus 64) with (2 ^ 64) in B. apply H; [exact B| intros F0; exact F0].
Qed.
Lemma unread_nonneg vp (M : mem) op ois s str sm :
  PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA vp M op ois s -> PM.iss_at RSEGS PMA.AD PMSPA.accA M ois str sm -> 0 <= PM.unread (PNM.b_src s) sm.
Proof.
  intros PA IA. pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & G2 & _) & _).
  pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G3). unfold PM.unread. lia.
Qed.

Lemma zb_mod64 a : Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a.
Proof. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. clear; lia. Qed.
Lemma bax_cat_add ax : PNST.bax_cat (PNST.bax_add_cat ax) = true.
Proof. destruct ax; reflexivity. Qed.
Lemma bvu_rng (x : word) : 0 <= bv_unsigned x < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range 64 x) as B. change (bv_modulus 64) with (2 ^ 64) in B. exact B. Qed.

Lemma set_cs_src w s x g : PNM.b_src (set_cs w s x g) = PNM.b_src s.
Proof. unfold set_cs. destruct (Z.eqb w 0); reflexivity. Qed.
Lemma set_cs_stk w s x g : PNM.b_stk (set_cs w s x g) = PNM.b_stk s.
Proof. unfold set_cs. destruct (Z.eqb w 0); reflexivity. Qed.
Lemma set_cs_done w s x g : PNM.b_done (set_cs w s x g) = PNM.b_done s.
Proof. unfold set_cs. destruct (Z.eqb w 0); reflexivity. Qed.
Lemma set_cs_bb w s x g : PNM.b_bb (set_cs w s x g) = PNM.b_bb s.
Proof. unfold set_cs. destruct (Z.eqb w 0); reflexivity. Qed.
Lemma set_cs_str w s x g : PNRA.bcs_str w (set_cs w s x g) = x.
Proof. unfold set_cs, PNRA.bcs_str. destruct (Z.eqb w 0); reflexivity. Qed.
Lemma set_stk_str w s l : PNRA.bcs_str w (PNBO.set_stk s l) = PNRA.bcs_str w s.
Proof. unfold PNRA.bcs_str. destruct (Z.eqb w 0); reflexivity. Qed.
Lemma with_src_str w s x : PNRA.bcs_str w (PNM.with_srcB s x) = PNRA.bcs_str w s.
Proof. unfold PNRA.bcs_str. destruct (Z.eqb w 0); reflexivity. Qed.
Lemma btop_len s s3 : PNRA.btop_pos s s3 -> (length (PNM.b_stk s) <= length (PNM.b_stk s3))%nat.
Proof. intros (l & c & c' & E1 & E2 & _). rewrite E1, E2, !List.length_app. cbn [length]. apply Nat.le_refl. Qed.
Lemma fdiv_rng F : 6905856 <= F <= 140737488355264 -> 863232 <= F / 8 <= 17592186044408.
Proof.
  intros HF. split; [apply Z.div_le_lower_bound; clear - HF; lia| apply Z.div_le_upper_bound; clear - HF; lia].
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Lemma blk_ceil LB FF LK cr Aw M V q m : ri_inv HI LB FF LK cr Aw M V -> In (q, m) LB -> q + m <= ahl_ceil ar /\ app_mem q m.
Proof.
  intros HH Hq. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  destruct (WB _ Hq) as ((_ & _ & _ & _ & BC & BA) & _). cbn [fst snd] in BC, BA. exact (conj BC BA).
Qed.

(* [comment removed for export] *)
Lemma base_keepW LB FF sp scr W M M' :
  L5SAR.ek L ar LB FF sp scr W M M' ->
  (forall a, 65536 <= a < 0x139000 -> L5.outside W a) -> (forall a, 0x693d40 <= a < 0x693d48 -> L5.outside W a) ->
  L5.outside W 0x693f93 -> (forall a, 0x694070 <= a < 0x694074 -> L5.outside W a) ->
  PMSTA.base_okA RSEGS PMA.AD M -> PMSTA.base_okA RSEGS PMA.AD M'.
Proof.
  intros E O1 O2 O3 O4 (RO0 & (can & Hcan & CAN) & NL & LL).
  assert (AGD : forall a, 0 <= a < 2 ^ 64 -> PMST.dep PMA.AD a -> L5.outside W a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha D Ho. apply E. split; [exact Ha|]. split; [|exact Ho]. unfold aclient, aclient_g. right; right; left.
    pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia| exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))]. }
  cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock PMA.AD ADDR_A] in *.
  split; [|split; [|split]].
  - intros i Hi. cbn [pa_rw_lo PMA.AD ADDR_A] in Hi. rewrite E; [apply RO0; cbn [pa_rw_lo PMA.AD ADDR_A]; exact Hi|]. split; [lia|]. split; [| apply O1; lia]. unfold aclient, aclient_g. right; right; left.
    rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia| intros X; pose proof (L5A.aly_static_lo L C LYa _ X); lia].
  - exists can. split; [exact Hcan|]. apply (L5C.u64_at_agree RSEGS M M'); [|cbn [pa_canary PMA.AD ADDR_A]; lia|cbn [pa_canary PMA.AD ADDR_A]; lia| exact CAN]. intros i Hi. cbn [pa_canary PMA.AD ADDR_A] in Hi. apply AGD; [lia| right; left; cbn [pa_canary PMA.AD ADDR_A]; lia| apply O2; lia].
  - cbn [pa_need_locks PMA.AD ADDR_A] in NL |- *. apply (L5C.u8_at_agree RSEGS M M'); [|lia|lia| exact NL]. intros i Hi.
    apply AGD; [lia| apply PMST.in_foot_nl; cbn [pa_need_locks PMA.AD ADDR_A]; lia| replace i with 0x693f93 by lia; exact O3].
  - cbn [pa_locale_lock PMA.AD ADDR_A] in LL |- *. unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M M' 4%nat 0x694070); [exact LL| lia| cbn; lia|].
    intros i Hi. cbn in Hi. apply AGD; [lia| apply PMST.in_foot_ll; cbn [pa_locale_lock PMA.AD ADDR_A]; lia| apply O4; lia].
Qed.

(* [comment removed for export] *)
Lemma berr_keep LB FF sp scr W M M' ax :
  L5SAR.ek L ar LB FF sp scr W M M' -> (forall a, 65536 <= a < 6905856 -> L5.outside W a) ->
  PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN M ax -> PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN M' ax.
Proof.
  intros EK OUT ERR. apply (PNSTA.berr_okA_frame RSEGS PMA.AD PMA.AAD PMA.AN PMA.addrs_wf_B M M'); [| exact ERR].
  intros a Ha D. apply EK. split; [exact Ha|]. pose proof (depA_img a D) as DI. split; [| apply OUT; exact DI].
  unfold aclient, aclient_g. right; right; left.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [exact DI| exact (PMA.ly_static L C LY a D)].
Qed.

(* [comment removed for export] *)
Lemma pre_after_call LB1 FFx spx scr Wc (M1 M4 : mem) fb s1 s4 str sm1 sm4 ax1 ax4 :
  (forall f, In f FFx -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) ->
  ek L ar LB1 FFx spx scr Wc M1 M4 -> PMKA.wapp Wc -> PNRA.frame_okB FFx fb ->
  (forall i, (fb + 432 <= i < fb + 440 \/ fb + 880 <= i < fb + 888) -> L5.outside Wc i) ->
  PNRA.brun_pre RSEGS PMA.AD PMA.AN PMA.AAD M1 fb s1 str sm1 ax1 ->
  PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA (pa_vp_parser PMA.AD) M4 (fb + 464) (fb + 96) s4 ->
  PM.iss_at RSEGS PMA.AD PMSPA.accA M4 (fb + 96) str sm4 -> PNM.bgrow_ok s4 ->
  PMSTA.base_okA RSEGS PMA.AD M4 -> PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN M4 ax4 ->
  PNRA.brun_pre RSEGS PMA.AD PMA.AN PMA.AAD M4 fb s4 str sm4 ax4.
Proof.
  intros FRB EK WA FOK OUT (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1) PA4 IA4 GR4 BASE4 ERR4.
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in *. change (PNRA.o_is PMA.AD fb) with (fb + 96) in *. change (PNRA.o_v PMA.AD fb) with (fb + 432) in *.
  change (PNM.PSIZE + 8) with 424 in *. change PNM.PSIZE with 416 in *.
  unfold PNRA.brun_pre. change (PNRA.o_p PMA.AD fb) with (fb + 464). change (PNRA.o_is PMA.AD fb) with (fb + 96). change (PNRA.o_v PMA.AD fb) with (fb + 432).
  change (PNM.PSIZE + 8) with 424. change PNM.PSIZE with 416.
  split; [exact PA4|]. split; [exact IA4|].
  split. { apply (PMKA.visitor_keepA RSEGS PMA.AD L ar LB1 FFx spx scr Wc M1 M4 EK WA FRB (fb + 432)); [| | exact VIS1].
           - apply (PNAPAR.aobj_fbB FFx fb (fb + 432) 8 FOK); clear; lia.
           - intros i Hi. apply OUT. left. clear - Hi; lia. }
  split. { apply (PMKA.u64_keepA RSEGS L ar LB1 FFx spx scr Wc M1 M4 EK WA FRB (fb + 464 + 416)); [| | exact VREF1].
           - apply (PNAPAR.aobj_fbB FFx fb (fb + 464 + 416) 8 FOK); clear; lia.
           - intros i Hi. apply OUT. right. clear - Hi; lia. }
  split. { apply (PMFA.accA_agree M1 M4 (fb + 464) 424); [| exact OACC1].
           apply (PMKA.agsh_obj L ar LB1 FFx spx scr Wc M1 M4 EK WA FRB (fb + 464) 424). apply (PNAPAR.aobj_fbB FFx fb (fb + 464) 424 FOK); clear; lia. }
  split; [exact BASE4|]. split; [exact ERR4| exact GR4].
Qed.

End WithHeap.
End PNBKA.
