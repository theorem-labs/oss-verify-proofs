(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmLibSpecsX_u5 PmLibSpecsW_u5 PmRef_u5 PmRefFacts_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RelLeaf.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5 ParseBridges3_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmall Require Import SmallWin_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmallW Require Import SmallPtW_u5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module SPXWU.
Import PML PMES.
Abbreviation mem := (word -> option byte).

Section Credit.
Variable L : heap_layout.
Hypothesis KPM : 0 <= hl_k_per_malloc L.
Hypothesis BOV : 0 <= hl_b_overhead L.
Local Set Default Proof Using "All".

Lemma kleft_nonneg : forall ps, 0 <= PML.kleft ps * hl_k_per_malloc L.
Proof.
  intros ps. unfold PML.kleft. pose proof (Z.log2_nonneg (2 ^ 27 / PML.ps_bcap ps)). pose proof (Z.log2_nonneg (1056 / PML.ps_scap ps)). nia.
Qed.
Lemma pbytes_nonneg : forall ps, PML.ps_bcap ps <= 2 ^ 27 -> PML.ps_scap ps <= 1056 -> 0 <= PMX.pbytes L ps.
Proof.
  intros ps Hb Hs. unfold PMX.pbytes, PML.bleft, PML.kleft.
  pose proof (Z.log2_nonneg (2 ^ 27 / PML.ps_bcap ps)). pose proof (Z.log2_nonneg (1056 / PML.ps_scap ps)). nia.
Qed.
Lemma ecredit_of_pxU : forall cr ps g kx bx, PML.pcredit_x L cr ps (kx + PMES.kenc L g) (bx + PMES.benc L g) -> 0 <= kx -> 0 <= bx ->
  PML.ps_scap ps <= 1056 ->
  PMES.ecreditU L cr g (kx + PML.kleft ps * hl_k_per_malloc L) (bx + PMX.pbytes L ps).
Proof.
  intros cr ps g kx bx H Hk Hb Hs. pose proof H as (_ & _ & HB & _).
  apply (PMX.ecredit_of_pxU L cr ps g kx bx H Hk Hb (EK.kenc_nonneg L KPM BOV g) (EK.benc_nonneg L KPM BOV g) (kleft_nonneg ps)).
  exact (pbytes_nonneg ps HB Hs).
Qed.
Lemma px_of_ecreditU : forall cr cr' ps g g' kx bx, PML.pcredit_x L cr ps (kx + PMES.kenc L g) (bx + PMES.benc L g) -> 0 <= kx -> 0 <= bx ->
  PMES.ecreditU L cr' g' (kx + PML.kleft ps * hl_k_per_malloc L) (bx + PMX.pbytes L ps) ->
  PML.pcredit_x L cr' ps (kx + PMES.kenc L g') (bx + PMES.benc L g').
Proof.
  intros cr cr' ps g g' kx bx H Hk Hb E.
  exact (PMX.px_of_ecreditU L cr cr' ps g g' kx bx H Hk Hb (EK.kenc_nonneg L KPM BOV g') (EK.benc_nonneg L KPM BOV g') E).
Qed.
Lemma ecredit_of_bufcredU : forall cr cap K B g, PPS.bufcred L cr cap (K + PMES.kenc L g) (B + PMES.benc L g) -> 0 <= K -> 0 <= B ->
  PMES.ecreditU L cr g (K + Z.log2 (2 ^ 27 / cap) * hl_k_per_malloc L) (B + ((2 ^ 28 - 2 * cap) + Z.log2 (2 ^ 27 / cap) * hl_b_overhead L)).
Proof.
  intros cr cap K B g (H1 & H2 & H3 & H4 & H5) HK HB. unfold PMES.ecreditU.
  pose proof (Z.log2_nonneg (2 ^ 27 / cap)). pose proof (EK.kenc_nonneg L KPM BOV g). pose proof (EK.benc_nonneg L KPM BOV g).
  split; [nia|]. split; [lia|]. split; [nia | lia].
Qed.
Lemma bufcred_of_ecreditU : forall cr cr' cap K B g g', PPS.bufcred L cr cap (K + PMES.kenc L g) (B + PMES.benc L g) -> 0 <= K -> 0 <= B ->
  PMES.ecreditU L cr' g' (K + Z.log2 (2 ^ 27 / cap) * hl_k_per_malloc L) (B + ((2 ^ 28 - 2 * cap) + Z.log2 (2 ^ 27 / cap) * hl_b_overhead L)) ->
  PPS.bufcred L cr' cap (K + PMES.kenc L g') (B + PMES.benc L g').
Proof.
  intros cr cr' cap K B g g' (H1 & H2 & H3 & H4 & H5) HK HB (E1 & E2 & E3 & E4). unfold PPS.bufcred.
  pose proof (EK.kenc_nonneg L KPM BOV g'). pose proof (EK.benc_nonneg L KPM BOV g'). repeat split; lia.
Qed.
End Credit.

Lemma ev_ind_nonneg : forall es ev, 0 <= PMES.ev_ind es ev.
Proof.
  assert (C : forall c, 0 <= PMES.comma c) by (intros c; unfold PMES.comma; destruct (0 <? PMES.ec_count c); lia).
  assert (N : forall es, 1 <= PMES.nl es) by (intros es; unfold PMES.nl, PMES.depth; lia).
  assert (P : forall es, 0 <= fst (PMES.pre_scalar es)).
  { intros [|c r]; cbn -[PMES.comma PMES.nl]; [lia|]. destruct (PMES.ec_arr c); cbn -[PMES.comma PMES.nl]; [|lia]. pose proof (C c). pose proof (N (c :: r)). lia. }
  assert (Q : forall ev, 0 <= PMES.quotes ev) by (intros ev; unfold PMES.quotes; destruct ev; try lia; destruct (_ || _); lia).
  intros es ev. destruct ev; unfold PMES.ev_ind.
  - destruct es as [|c r]; [lia|]. destruct (PMES.ec_arr c); [|lia]. pose proof (C c). pose proof (N (c :: r)). lia.
  - destruct es as [|c r]; [lia|]. destruct (PMES.ec_nla c); unfold PMES.depth; lia.
  - destruct es as [|c r]; [lia|]. pose proof (C c). pose proof (N (c :: r)). lia.
  - pose proof (P es). pose proof (Q (PMES.EvStr tag bs)). lia.
  - pose proof (P es). pose proof (Q PMES.EvNull). lia.
  - pose proof (P es). pose proof (Q (PMES.EvBool b)). lia.
  - pose proof (P es). pose proof (Q PMES.EvU64). lia.
  - pose proof (P es). pose proof (Q PMES.EvI64). lia.
  - pose proof (P es). pose proof (Q PMES.EvDbl). lia.
Qed.
Lemma ind_run_nonneg : forall ks es, 0 <= PMW.ind_run es ks.
Proof. induction ks as [|k r IH]; intros es; cbn -[PMW.ind_k PMW.step_k]; [lia|]. pose proof (ev_ind_nonneg es (PMW.eev_of k)). unfold PMW.ind_k. pose proof (IH (PMW.step_k es k)). lia. Qed.
Lemma ind_raw_num : forall es tag bs, tag = 2 \/ tag = 3 -> PMES.ev_ind es (PMES.EvStr tag bs) = PMW.ind_k es PMW.EkNum /\ PMES.estep es (PMES.EvStr tag bs) = PMW.step_k es PMW.EkNum.
Proof. intros es tag bs [-> | ->]; split; reflexivity. Qed.

Lemma room_first : forall eg k rest al ev,
  PMW.wroomU eg (k :: rest) al -> PMW.kind_of ev = k -> PMES.pay_hi ev <= al -> PMES.eroomU eg ev.
Proof.
  intros eg k rest al ev HW Hk Hp. unfold PMES.eroomU, PMES.kmax. rewrite <- PMW.ind_k_of, Hk.
  unfold PMW.wroomU in HW. change (PMW.ind_run (PMES.g_es eg) (k :: rest)) with (PMW.ind_k (PMES.g_es eg) k + PMW.ind_run (PMW.step_k (PMES.g_es eg) k) rest) in HW.
  pose proof (ind_run_nonneg rest (PMW.step_k (PMES.g_es eg) k)) as NN. lia.
Qed.
Lemma room_begin_container : forall (arr : bool) c (M : mem) P ps w eg,
  PMR.rm_match c M P ps -> ps_level ps < 1024 ->
  PMW.wroomrU PMR.the_rm eg (PMW.rm_step PMR.the_rm (if arr then PMW.FBeginArray else PMW.FBeginObject) c w) -> PMES.eroomU eg (PMES.EvBegin arr).
Proof.
  intros arr c M P ps w eg ((R1 & R2 & R3 & R4 & R5) & _) HL HW.
  assert (E : PMW.rm_step PMR.the_rm (if arr then PMW.FBeginArray else PMW.FBeginObject) c w = PMR.r_of w (PMR.begin_container arr c w)) by (destruct arr; reflexivity).
  rewrite E in HW. unfold PMW.wroomrU, PMR.begin_container in HW.
  destruct (Z.ltb_spec 1024 (PMR.c_level (PMR.set_level c (PMR.c_level c + 1)))) as [X|X]; [exfalso; cbn [PMR.c_level PMR.set_level] in X; lia|].
  cbn [PMR.r_of PMW.r_evs PMW.r_allow PMR.q_evs PMR.q_al PMR.q_c PMR.q_w PMR.q_code] in HW.
  apply (room_first eg (PMW.EkBegin arr) [] 0 (PMES.EvBegin arr) HW eq_refl). cbn. lia.
Qed.
Lemma room_end_container : forall (arr : bool) c (M : mem) P ps w eg rest,
  PMR.rm_match c M P ps -> 1 <= ps_level ps -> ps_stack ps = rest ++ [SPTW.EC_KIND arr] ->
  PMW.wroomrU PMR.the_rm eg (PMW.rm_step PMR.the_rm (if arr then PMW.FEndArray else PMW.FEndObject) c w) -> PMES.eroomU eg PMES.EvEnd.
Proof.
  intros arr c M P ps w eg rest ((R1 & R2 & R3 & R4 & R5) & _) HL HS HW.
  rewrite SPTW.end_container_step in HW. unfold PMW.wroomrU, PMR.end_container in HW. rewrite R4 in HW.
  replace (ps_level ps <? 1) with false in HW by (symmetry; apply Z.ltb_ge; exact HL).
  unfold PMR.top in HW. rewrite R5, HS, last_last in HW. unfold SPTW.EC_KIND in HW.
  assert (E : (if arr then ST_ARRAY else ST_OBJECT) =? (if arr then ST_ARRAY else ST_OBJECT) = true) by (apply Z.eqb_refl). rewrite E in HW.
  cbn [PMR.r_of PMW.r_evs PMW.r_allow PMR.q_evs PMR.q_al PMR.q_c PMR.q_w PMR.q_code] in HW.
  apply (room_first eg PMW.EkEnd [] 0 PMES.EvEnd HW eq_refl). cbn. lia.
Qed.
Lemma wroom_end_number : forall (frac : bool) c buf eg,
  PMW.wroomrU PMR.the_rm eg (PMW.rm_step PMR.the_rm (if frac then PMW.FEndFrac else PMW.FEndInt) c buf) ->
  PMW.wroomU eg [PMW.EkNum] (28 + Z.of_nat (length buf)).
Proof.
  intros frac c buf eg HW.
  assert (E : PMW.rm_step PMR.the_rm (if frac then PMW.FEndFrac else PMW.FEndInt) c buf = PMR.r_of0 (PMR.end_number (PMR.of_text c buf) [])) by (destruct frac; reflexivity).
  rewrite E in HW. unfold PMW.wroomrU, PMR.end_number in HW. rewrite PMRF.bind_ok in HW by reflexivity.
  assert (AV : forall c0 w0, PMR.q_evs (PMR.after_value c0 w0) = [] /\ PMR.q_al (PMR.after_value c0 w0) = 0).
  { intros c0 w0. unfold PMR.after_value. destruct (_ || _); [split; reflexivity|]. destruct (_ =? _); split; reflexivity. }
  cbn [PMR.r_of0 PMW.r_evs PMW.r_allow PMRF.pre PMR.q_c PMR.q_w PMR.q_evs PMR.q_al PMR.q_code] in HW.
  destruct (AV (PMR.set_more (PMR.of_text c buf) true) (@nil Z)) as [AE AA]. rewrite AE, AA, Z.add_0_r in HW. cbn [app] in HW.
  unfold PMR.al_num in HW. cbn [PMR.c_dlen PMR.of_text PMR.set_tok PMR.set_more] in HW. exact HW.
Qed.
Lemma room_end_number : forall (frac : bool) c buf eg ev,
  PMW.wroomrU PMR.the_rm eg (PMW.rm_step PMR.the_rm (if frac then PMW.FEndFrac else PMW.FEndInt) c buf) ->
  PMW.kind_of ev = PMW.EkNum -> PMES.pay_hi ev <= 28 + Z.of_nat (length buf) -> PMES.eroomU eg ev.
Proof.
  intros frac c buf eg ev HW Hk Hp. exact (room_first eg PMW.EkNum [] (28 + Z.of_nat (length buf)) ev (wroom_end_number frac c buf eg HW) Hk Hp).
Qed.
Lemma room_end_number_raw : forall (frac : bool) c buf eg tag,
  PMW.wroomrU PMR.the_rm eg (PMW.rm_step PMR.the_rm (if frac then PMW.FEndFrac else PMW.FEndInt) c buf) ->
  tag = 2 \/ tag = 3 -> PMES.eroomU eg (PMES.EvStr tag buf).
Proof.
  intros frac c buf eg tag HW Ht. pose proof (wroom_end_number frac c buf eg HW) as W.
  unfold PMES.eroomU, PMES.kmax. rewrite (proj1 (ind_raw_num (PMES.g_es eg) tag buf Ht)). unfold PMW.wroomU in W. cbn [PMW.ind_run] in W.
  assert (PH : PMES.pay_hi (PMES.EvStr tag buf) = PMES.len buf) by (destruct Ht as [-> | ->]; reflexivity). rewrite PH. unfold PMES.len. clear - W. lia.
Qed.
Lemma wroom_lit : forall f tail sst c w eg,
  SPTW.lit_f f = Some (tail, sst) -> (S (length tail) <= length w)%nat -> forallb (fun q => fst q =? snd q) (combine (tl (firstn (S (length tail)) w)) tail) = true ->
  PMW.wroomrU PMR.the_rm eg (PMW.rm_step PMR.the_rm f c w) -> PMW.wroomU eg [PMW.EkLit] PMR.AL_LIT.
Proof.
  intros f tail sst c w eg Hf Hlen Hcmp HW. rewrite (SPTW.lit_step f tail sst c w Hf) in HW. unfold PMW.wroomrU, PMR.parse_lit in HW.
  replace (S (length tail) <=? length w)%nat with true in HW by (symmetry; apply Nat.leb_le; exact Hlen). rewrite Hcmp in HW. unfold PMR.lit_done in HW.
  cbn [PMR.r_of PMW.r_evs PMW.r_allow PMR.q_evs PMR.q_al PMR.q_c PMR.q_w PMR.q_code] in HW. exact HW.
Qed.
Lemma room_lit : forall f tail sst c w eg ev,
  SPTW.lit_f f = Some (tail, sst) -> (S (length tail) <= length w)%nat ->
  forallb (fun q => fst q =? snd q) (combine (tl (firstn (S (length tail)) w)) tail) = true ->
  PMW.wroomrU PMR.the_rm eg (PMW.rm_step PMR.the_rm f c w) -> (ev = PMES.EvNull \/ exists b, ev = PMES.EvBool b) -> PMES.eroomU eg ev.
Proof.
  intros f tail sst c w eg ev Hf Hlen Hcmp HW Hev.
  apply (room_first eg PMW.EkLit [] PMR.AL_LIT ev (wroom_lit f tail sst c w eg Hf Hlen Hcmp HW)).
  - destruct Hev as [-> | (b & ->)]; reflexivity.
  - unfold PMR.AL_LIT. destruct Hev as [-> | (b & ->)]; cbn; [lia|]. destruct b; lia.
Qed.
Lemma wroom_esv : forall c x (ps : pstate) rest top eg,
  PMR.rm_core c ps -> PMR.validate x = 0 -> ps_stack ps = rest ++ [top] ->
  PMW.wroomrU PMR.the_rm eg (PMW.rm_step PMR.the_rm PMW.FEndStringValue c x) ->
  (top = ST_MEMBER_NAME -> PMW.wroomU eg [PMW.EkKey] (PMR.al_str (Z.of_nat (length x)))) /\
  (top = ST_OBJECT \/ top = ST_ARRAY \/ top = ST_ROOT -> PMW.wroomU eg [PMW.EkStr true] (PMR.al_str (Z.of_nat (length x)))).
Proof.
  intros c x ps rest top eg (R1 & R2 & R3 & R4 & R5) Hv Hs HW.
  unfold PMW.wroomrU in HW. rewrite SPTW.end_string_step in HW. unfold PMR.end_string in HW.
  destruct (SPTW.of_text_fields c x) as (F1 & F2 & F3 & F4 & F5 & F6 & F7). rewrite F7, Hv in HW. cbn [negb Z.eqb] in HW.
  unfold PMR.top in HW. rewrite F5, R5, Hs, last_last, F6 in HW.
  split; intros Ht.
  - subst top. change (ST_MEMBER_NAME =? ST_MEMBER_NAME) with true in HW. cbv iota in HW.
    cbn [PMR.r_of0 PMW.r_evs PMW.r_allow PMR.q_evs PMR.q_al] in HW. exact HW.
  - destruct Ht as [-> |[-> | ->]].
    + change (ST_OBJECT =? ST_MEMBER_NAME) with false in HW. change ((ST_OBJECT =? ST_OBJECT) || (ST_OBJECT =? ST_ARRAY)) with true in HW.
      cbv iota in HW. cbn [PMR.r_of0 PMW.r_evs PMW.r_allow PMR.q_evs PMR.q_al] in HW. exact HW.
    + change (ST_ARRAY =? ST_MEMBER_NAME) with false in HW. change ((ST_ARRAY =? ST_OBJECT) || (ST_ARRAY =? ST_ARRAY)) with true in HW.
      cbv iota in HW. cbn [PMR.r_of0 PMW.r_evs PMW.r_allow PMR.q_evs PMR.q_al] in HW. exact HW.
    + change (ST_ROOT =? ST_MEMBER_NAME) with false in HW. change ((ST_ROOT =? ST_OBJECT) || (ST_ROOT =? ST_ARRAY)) with false in HW. change (ST_ROOT =? ST_ROOT) with true in HW.
      cbv iota in HW. cbn [PMR.r_of0 PMW.r_evs PMW.r_allow PMR.q_evs PMR.q_al] in HW. exact HW.
Qed.
Lemma room_esv_key : forall c x (ps : pstate) rest eg,
  PMR.rm_core c ps -> PMR.validate x = 0 -> ps_stack ps = rest ++ [ST_MEMBER_NAME] ->
  PMW.wroomrU PMR.the_rm eg (PMW.rm_step PMR.the_rm PMW.FEndStringValue c x) -> PMES.eroomU eg (PMES.EvKey x).
Proof.
  intros c x ps rest eg HC Hv Hs HW.
  apply (room_first eg PMW.EkKey [] (PMR.al_str (Z.of_nat (length x))) (PMES.EvKey x) (proj1 (wroom_esv c x ps rest _ eg HC Hv Hs HW) eq_refl) eq_refl).
  unfold PMES.pay_hi, PMR.al_str. pose proof (SPTW.esc_len_bound x). lia.
Qed.
Lemma room_esv_value : forall c x (ps : pstate) rest top eg tag,
  PMR.rm_core c ps -> PMR.validate x = 0 -> ps_stack ps = rest ++ [top] -> (top = ST_OBJECT \/ top = ST_ARRAY \/ top = ST_ROOT) -> 0 <= tag <= 1 ->
  PMW.wroomrU PMR.the_rm eg (PMW.rm_step PMR.the_rm PMW.FEndStringValue c x) -> PMES.eroomU eg (PMES.EvStr tag x).
Proof.
  intros c x ps rest top eg tag HC Hv Hs Htop Htag HW.
  apply (room_first eg (PMW.EkStr true) [] (PMR.al_str (Z.of_nat (length x))) (PMES.EvStr tag x) (proj2 (wroom_esv c x ps rest top eg HC Hv Hs HW) Htop)).
  - cbn. replace ((tag =? 2) || (tag =? 3)) with false; [reflexivity|]. symmetry. apply orb_false_intro; apply Z.eqb_neq; lia.
  - unfold PMES.pay_hi, PMR.al_str. pose proof (SPTW.esc_len_bound x). unfold PMES.len. destruct ((tag =? 1) || (tag =? 2) || (tag =? 3)); lia.
Qed.
End SPXWU.
