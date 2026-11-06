(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm5PlanKit Pm5L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB CutHeapV.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmLibSpecs PmEncSpecs PmLibSpecsXA PmLibSpecsX PmLibSpecsW PmRef PmRefFacts PmRefXA PmLibSpecsXAW RelLeaf.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module SPTAW.
Import PML PMES.
Abbreviation mem := (word -> option byte).
Abbreviation uv := CL5A.uv.
#[local] Notation S := Datatypes.S (only parsing).      (* [comment removed for export] *)

Section W.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
(* [comment removed for export] *)
#[local] Notation RSEGS := (hl_segs L).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition has (cells : list kentry) (X : kentry) : bool := CC.has_cell cells X.
Lemma has_ok : forall E (M : mem) cells X, know_ok RSEGS E M cells -> has cells X = true -> kentry_ok RSEGS E M X.
Proof. intros E M cells X HK H. apply CC.has_cell_In in H. exact (proj1 (Forall_forall _ _) HK X H). Qed.
Lemma u8_inj : forall (M : mem) a b1 b2, L5.u8_at RSEGS M a b1 -> L5.u8_at RSEGS M a b2 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> b1 = b2.
Proof.
  intros M a b1 b2 H1 H2 R1 R2. unfold L5.u8_at in H1, H2. rewrite H1 in H2. assert (H3 : Z_to_bv 8 b1 = Z_to_bv 8 b2) by congruence. clear H2. apply (f_equal bv_unsigned) in H3.
  rewrite !Z_to_bv_unsigned in H3. unfold bv_wrap in H3. change (bv_modulus 8) with 256 in H3. rewrite !Z.mod_small in H3 by lia. exact H3.
Qed.
Lemma u8_frame : forall (M1 M' : mem) a b, M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a) -> L5.u8_at RSEGS M1 a b -> L5.u8_at RSEGS M' a b.
Proof. intros M1 M' a b H H1. unfold L5.u8_at in *. cbn [rdn] in *. rewrite H. exact H1. Qed.
Lemma bytes_of_defined_r : forall (M : mem) (n : nat) (p : Z), 0 <= p -> p + Z.of_nat n <= 2 ^ 64 -> L5.defined M p (Z.of_nat n) ->
  exists s : list Z, length s = n /\ L5.bytes_at RSEGS M p s /\ Forall (fun c => 0 <= c < 256) s.
Proof.
  intros M n. induction n as [|n IH]; intros p Hp Hb Hd.
  - exists []. split; [reflexivity|]. split; [|constructor]. intros i Hi. cbn [length] in Hi. lia.
  - destruct (IH (p + 1) ltac:(lia) ltac:(lia)) as (s & Hl & Hs & Hr).
    { intros i Hi. replace (p + 1 + i) with (p + (i + 1)) by lia. apply Hd. lia. }
    pose proof (Hd 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. destruct (M (Z_to_bv 64 p)) as [b|] eqn:Hb0; [|contradiction].
    exists (bv_unsigned b :: s). split; [cbn [length]; rewrite Hl; reflexivity|]. split.
    + intros i Hi. destruct i as [|i].
      * cbn [nth]. rewrite Z.add_0_r. unfold L5.u8_at. cbn [rdn]. unfold rd1. rewrite Hb0. rewrite Z_to_bv_bv_unsigned. reflexivity.
      * cbn [nth]. replace (p + Z.of_nat (Datatypes.S i)) with (p + 1 + Z.of_nat i) by lia. apply Hs. cbn [length] in Hi. lia.
    + constructor; [|exact Hr]. pose proof (bv_unsigned_in_range _ b) as Bb. change (bv_modulus 8) with 256 in Bb. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma win_bytesA_ag : forall (M M' : mem) (S : Z -> Prop), (forall a, S a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  forall LBo ps ps' w, (forall ch a, In (ch, 16384) LBo -> ch <= a < ch + 16384 -> S a) ->
  PMSA.win_okA M LBo ps -> PMXAW.win_bytesA L M ps w -> ps_win ps' = ps_win ps -> PMXAW.win_bytesA L M' ps' w.
Proof.
  intros M M' S AG LBo ps ps' w HS HWIN HWB Hw'. unfold PMXAW.win_bytesA, PMSA.win_okA, PMLA.win_okA in *. rewrite Hw'.
  destruct (ps_win ps) as [[p e]|]; [|exact HWB]. destruct HWB as (HB & HL & HF). destruct HWIN as (ch & Hch & C1 & C2 & _).
  split; [|exact (conj HL HF)]. intros i Hi. apply (u8_frame M M'); [|exact (HB i Hi)]. apply AG. apply (HS ch _ Hch). apply Nat2Z.inj_lt in Hi. lia.
Qed.
(* [comment removed for export] *)
Lemma win_bytesA_exists : forall (M : mem) LBo ps, PMSA.win_okA M LBo ps -> 0 <= winlen ps ->
  (forall ch, In (ch, 16384) LBo -> 0 <= ch /\ ch + 16384 <= 2 ^ 64) -> exists w, PMXAW.win_bytesA L M ps w.
Proof.
  intros M LBo ps HWIN Hwl HR. unfold PMXAW.win_bytesA, PMSA.win_okA, PMLA.win_okA, winlen in *.
  destruct (ps_win ps) as [[p e]|]; [|exists []; reflexivity]. destruct HWIN as (ch & Hch & C1 & C2 & Hd & _). destruct (HR ch Hch) as (R0 & R1).
  destruct (bytes_of_defined_r M (Z.to_nat (e - p)) p ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; exact Hd)) as (w & Hl & Hb & Hf).
  exists w. split; [exact Hb|]. split; [rewrite Hl; lia|]. apply Forall_forall. intros x Hx. pose proof (proj1 (Forall_forall _ _) Hf x Hx) as R. cbn beta in R. clear -R. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rm_match_plain : forall c (M : mem) P ps,
  PMR.c_st c = ps_st ps -> PMR.c_more c = ps_more ps -> PMR.c_done c = ps_done ps -> PMR.c_level c = ps_level ps -> PMR.c_stack c = ps_stack ps ->
  ps_st ps <> ST_STRING -> ps_st ps <> ST_NUMBER -> (PMRXA.rm_matchA L) c M P ps.
Proof.
  intros c M P ps H1 H2 H3 H4 H5 NS NN. split; [exact (conj H1 (conj H2 (conj H3 (conj H4 H5))))|]. split; intros X; contradiction.
Qed.

(* [comment removed for export] *)
Lemma wf_stack_plain : forall ps, wf_ps ps -> ps_more ps = true -> ~ comment_or_cr (ps_st ps) -> ps_st ps <> ST_STRING -> ps_st ps <> ST_CR ->
  exists C, ps_stack ps = ST_ROOT :: C /\ Forall is_container C /\ Z.of_nat (length C) = ps_level ps /\ 0 <= ps_level ps <= 1024.
Proof.
  intros ps (_ & _ & _ & _ & C & T & HS & HC & HM) Hm Hncc Hns Hncr. destruct (HM Hm) as (HL & HLV & _ & HT & _).
  exists C. destruct HT as [(-> & _)|[(_ & X)|[(S & _ & _ & X)|(S & _ & _ & X)]]]; try contradiction.
  rewrite app_nil_r in HS. repeat split; try assumption; lia.
Qed.

(* [comment removed for export] *)
Lemma top_plain : forall c ps C, PMR.c_stack c = ps_stack ps -> ps_stack ps = ST_ROOT :: C -> Forall is_container C -> Z.of_nat (length C) = ps_level ps ->
  (ps_level ps = 0 -> PMR.top c = ST_ROOT) /\ (ps_level ps <> 0 -> PMR.top c = ST_OBJECT \/ PMR.top c = ST_ARRAY).
Proof.
  intros c ps C H5 HS HC HL. unfold PMR.top. rewrite H5, HS.
  destruct C as [|s r] using rev_ind.
  - cbn in HL. split; [intros _; reflexivity | intros X; exfalso; lia].
  - rewrite length_app in HL. cbn [length] in HL. split; [intros X; exfalso; lia | intros _].
    rewrite app_comm_cons, last_last. apply Forall_app in HC as [_ HC]. inversion HC as [|y l Hy _]. exact Hy.
Qed.

(* [comment removed for export] *)
Definition adm_all (v : nat) (cells : list kentry) (lo : Z) (n : nat) (f : Z -> bool) : bool := RLF.forall_b lo n (fun z => negb (RLF.byte_adm v cells z) || f z).
Lemma adm_all_sound : forall v cells lo n f E' (M' : mem) z, adm_all v cells lo n f = true -> know_ok RSEGS E' M' cells -> uv E' (EVar v) = z -> lo <= z < lo + Z.of_nat n -> f z = true.
Proof.
  intros v cells lo n f E' M' z H HK Hz Hr. pose proof (RLF.forall_b_sound n lo _ z H Hr) as X. cbn beta in X.
  rewrite (RLF.byte_adm_sound RSEGS v E' M' z cells HK) in X; [exact X|]. rewrite <- Hz. unfold uv. cbn [edenot]. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition w3x (f : PMW.fname) (c : PMR.ctrl) (inp : list Z) (M' : mem) (P : Z) (ps ps' : pstate) (w : list Z) (eg eg' : eghost) (code : Z) : Prop :=
  let rr := PMW.rm_step (PMRXA.the_rmA L) f c inp in
  code = PMW.r_code rr /\
  g_es eg' = PMW.es_run (g_es eg) (PMW.r_evs rr) /\
  (exists pay, 0 <= pay <= PMW.r_allow rr /\ g_len eg' = g_len eg + PMW.ind_run (g_es eg) (PMW.r_evs rr) + pay) /\
  (code = 0 -> PMW.rm_match (PMRXA.the_rmA L) (PMW.r_ctrl rr) M' P ps' /\ PMW.r_used rr = winlen ps - winlen ps' /\ (PMXAW.win_bytesA L) M' ps' (PMW.w_after (PMRXA.the_rmA L) rr w)).
Definition w3p (f : PMW.fname) (c : PMR.ctrl) (inp : list Z) (M' : mem) (P : Z) (ps ps' : pstate) (w : list Z) (code : Z) : Prop :=
  let rr := PMW.rm_step (PMRXA.the_rmA L) f c inp in
  code = PMW.r_code rr /\ PMW.r_evs rr = [] /\
  (code = 0 -> PMW.rm_match (PMRXA.the_rmA L) (PMW.r_ctrl rr) M' P ps' /\ PMW.r_used rr = winlen ps - winlen ps' /\ (PMXAW.win_bytesA L) M' ps' (PMW.w_after (PMRXA.the_rmA L) rr w)).

Lemma skipn_used0 : forall (w v : list Z), Z.to_nat (Z.of_nat (length w) - Z.of_nat (length w)) = 0%nat.
Proof. intros. lia. Qed.

(* [comment removed for export] *)
Lemma w3_begin_container : forall (arr : bool) c (M M' : mem) P ps ps' w eg eg' code,
  (PMRXA.rm_matchA L) c M P ps -> wf_ps ps' -> ps_done ps' = ps_done ps ->
  ((code = 0 /\ ps_level ps' = ps_level ps + 1 /\ ps_st ps' = (if arr then ST_EXPECT_VALUE_OR_END else ST_EXPECT_MEMBER_NAME_OR_END) /\ ps_more ps' = true /\
    ps_stack ps' = ps_stack ps ++ [if arr then ST_ARRAY else ST_OBJECT] /\ ps_win ps' = ps_win ps) \/ (code = 5 /\ ps_level ps = 1024)) ->
  (code = 0 -> g_es eg' = estep (g_es eg) (EvBegin arr) /\ exists pay, pay_ok (EvBegin arr) pay /\ g_len eg' = g_len eg + ev_ind (g_es eg) (EvBegin arr) + pay) ->
  (code <> 0 -> eg' = eg) ->
  (PMXAW.win_bytesA L) M' ps' w ->
  w3x (if arr then PMW.FBeginArray else PMW.FBeginObject) c w M' P ps ps' w eg eg' code.
Proof.
  intros arr c M M' P ps ps' w eg eg' code HRM Hwf Hdone HREL HEV HEQ HWB.
  destruct HRM as ((R1 & R2 & R3 & R4 & R5) & _ & _). unfold w3x.
  assert (E : PMW.rm_step (PMRXA.the_rmA L) (if arr then PMW.FBeginArray else PMW.FBeginObject) c w = PMR.r_of w (PMR.begin_container arr c w)) by (destruct arr; reflexivity).
  rewrite E. clear E. unfold PMR.begin_container. cbn [PMR.c_level PMR.set_level]. rewrite R4.
  destruct HREL as [(Hc0 & HL & HST & HMO & HSTK & HWIN)|(Hc5 & HL1024)].
  - assert (Hlt : (1024 <? ps_level ps + 1) = false).
    { apply Z.ltb_ge. destruct Hwf as (_ & _ & _ & _ & C & T & _ & _ & HM). destruct (HM HMO) as (_ & HLV & _). clear -HL HLV. lia. }
    rewrite Hlt. destruct (HEV Hc0) as (Hes & pay & Hpay & Hlen). cbn in Hpay. unfold PMW.w_after.
    cbn [PMR.r_of PMW.r_code PMW.r_evs PMW.r_allow PMW.r_ctrl PMW.r_used PMR.q_c PMR.q_w PMR.q_evs PMR.q_al PMR.q_code PMW.es_run PMW.ind_run]. unfold PMW.ind_k, PMW.step_k. cbn [PMW.eev_of].
    split; [exact Hc0|]. split; [exact Hes|]. split; [exists 0; split; [clear; lia | rewrite Hlen, Hpay; clear; lia]|]. intros _.
    split; [|split; [unfold winlen; rewrite HWIN; clear; lia | rewrite Z.sub_diag; cbn [Z.to_nat skipn]; exact HWB]].
    apply rm_match_plain; cbn [PMR.c_st PMR.c_more PMR.c_done PMR.c_level PMR.c_stack PMR.set_more PMR.set_st PMR.push PMR.set_stack PMR.set_level];
      [symmetry; exact HST | symmetry; exact HMO | rewrite Hdone; exact R3 | clear -HL; lia | rewrite R5; symmetry; exact HSTK | rewrite HST | rewrite HST];
      clear; destruct arr; unfold ST_EXPECT_VALUE_OR_END, ST_EXPECT_MEMBER_NAME_OR_END, ST_STRING, ST_NUMBER; lia.
  - rewrite HL1024. change (1024 <? 1024 + 1) with true. unfold PMW.w_after. cbn [PMR.r_of PMR.err PMW.r_code PMW.r_evs PMW.r_allow PMW.r_ctrl PMW.r_used PMR.q_c PMR.q_w PMR.q_evs PMR.q_al PMR.q_code PMW.es_run PMW.ind_run].
    rewrite (HEQ ltac:(clear -Hc5; lia)). split; [rewrite Hc5; reflexivity|]. split; [reflexivity|]. split; [exists 0; clear; lia|]. intros X. exfalso. clear -X Hc5. lia.
Qed.


(* [comment removed for export] *)
Lemma w3_after_value : forall c (M' : mem) P ps ps' w x rest stz,
  PMR.rm_core c ps -> ps_more ps = true -> ps_stack ps = rest ++ [x] ->
  ((stz = 2 /\ x = 0) \/ (stz = 7 /\ (x = 8 \/ x = 14))) ->
  ps_st ps' = stz -> ps_more ps' = true -> ps_done ps' = ps_done ps -> ps_level ps' = ps_level ps -> ps_stack ps' = ps_stack ps -> ps_win ps' = ps_win ps ->
  (PMXAW.win_bytesA L) M' ps' w ->
  w3p PMW.FAfterValue c w M' P ps ps' w 0.
Proof.
  intros c M' P ps ps' w x rest stz (R1 & R2 & R3 & R4 & R5) Hm Hs Hsx Q1 Q2 Q3 Q4 Q5 Q6 HWB. unfold w3p.
  change (PMW.rm_step (PMRXA.the_rmA L) PMW.FAfterValue c w) with (PMR.r_of w (PMR.after_value c w)). unfold PMR.after_value, PMR.top. rewrite R5, Hs, last_last.
  assert (E : (if (x =? ST_ARRAY) || (x =? ST_OBJECT) then PMR.ret (PMR.set_st c ST_EXPECT_COMMA_OR_END) w
               else if x =? ST_ROOT then PMR.ret (PMR.set_st c ST_ACCEPT) w else PMR.err c w PMR.E_SYNTAX) = PMR.ret (PMR.set_st c stz) w).
  { unfold ST_ARRAY, ST_OBJECT, ST_ROOT, ST_EXPECT_COMMA_OR_END, ST_ACCEPT. destruct Hsx as [(-> & ->)|(-> & [->| ->])]; reflexivity. }
  rewrite E. unfold PMW.w_after. cbn [PMR.r_of PMR.ret PMW.r_code PMW.r_evs PMW.r_ctrl PMW.r_used PMR.q_c PMR.q_w PMR.q_evs PMR.q_code].
  split; [reflexivity|]. split; [reflexivity|]. intros _.
  split; [|split; [unfold winlen; rewrite Q6; clear; lia | rewrite Z.sub_diag; cbn [Z.to_nat skipn]; exact HWB]].
  apply rm_match_plain; cbn [PMR.c_st PMR.c_more PMR.c_done PMR.c_level PMR.c_stack PMR.set_st];
    [rewrite Q1; reflexivity | rewrite Q2, R2; exact Hm | rewrite Q3; exact R3 | rewrite Q4; exact R4 | rewrite Q5; exact R5 | rewrite Q1 | rewrite Q1];
    clear -Hsx; destruct Hsx as [(-> & _)|(-> & _)]; unfold ST_STRING, ST_NUMBER; lia.
Qed.


(* [comment removed for export] *)
Lemma depth_bump_pre : forall es, depth (bump (snd (pre_scalar es))) = depth es.
Proof. intros es. unfold depth. destruct es as [|e0 r0]; cbn [pre_scalar snd bump length]; [reflexivity|]. destruct (ec_arr e0); cbn [bump set_nla length]; reflexivity. Qed.

(* [comment removed for export] *)
Lemma w3_end_number : forall (frac : bool) c (M' : mem) P ps ps2 w eg eg' code,
  PMR.rm_core c ps -> wf_ps_stale ps -> ps_more ps = true -> ps_st ps = ST_NUMBER ->
  (code = 0 /\ ps_more ps2 = true /\ ps_st ps2 = (if Z.eqb (ps_level ps) 0 then ST_ACCEPT else ST_EXPECT_COMMA_OR_END) /\
   ps_stack ps2 = ps_stack ps /\ ps_level ps2 = ps_level ps /\ ps_win ps2 = ps_win ps) -> ps_done ps2 = ps_done ps ->
  g_es eg' = bump (snd (pre_scalar (g_es eg))) -> (exists pay, 0 <= pay <= 28 + Z.of_nat (length (ps_buf ps)) /\ g_len eg' = g_len eg + fst (pre_scalar (g_es eg)) + pay) ->
  (PMXAW.win_bytesA L) M' ps2 w ->
  w3x (if frac then PMW.FEndFrac else PMW.FEndInt) c (ps_buf ps) M' P ps ps2 w eg eg' code.
Proof.
  intros frac c M' P ps ps2 w eg eg' code (R1 & R2 & R3 & R4 & R5) HWF Hm Hst (Hc0 & Q2 & Q3 & Q4 & Q5 & Q6) Hd Hes (pay & Hpay & Hlen) HWB. unfold w3x.
  assert (E : PMW.rm_step (PMRXA.the_rmA L) (if frac then PMW.FEndFrac else PMW.FEndInt) c (ps_buf ps) = PMR.r_of0 (PMR.end_number (PMR.of_text c (ps_buf ps)) [])) by (destruct frac; reflexivity).
  rewrite E. clear E.
  (* [comment removed for export] *)
  destruct HWF as (_ & n' & HW'). destruct (wf_stack_plain (ps_set_nst ps n') HW' Hm) as (C & HS & HC & HL & HLV); cbn [ps_st ps_stack ps_level ps_set_nst] in *; [rewrite Hst; unfold comment_or_cr, ST_NUMBER, ST_CR; lia | rewrite Hst; discriminate | rewrite Hst; discriminate|].
  pose proof (top_plain (PMR.set_more (PMR.of_text c (ps_buf ps)) true) ps C R5 HS HC HL) as (T0 & T1).
  unfold PMR.end_number. rewrite PMRF.bind_ok by reflexivity. cbn [PMR.q_c PMR.q_w PMR.q_evs PMR.q_al PMR.q_code]. unfold PMR.after_value.
  assert (E2 : (if (PMR.top (PMR.set_more (PMR.of_text c (ps_buf ps)) true) =? ST_ARRAY) || (PMR.top (PMR.set_more (PMR.of_text c (ps_buf ps)) true) =? ST_OBJECT)
                then PMR.ret (PMR.set_st (PMR.set_more (PMR.of_text c (ps_buf ps)) true) ST_EXPECT_COMMA_OR_END) []
                else if PMR.top (PMR.set_more (PMR.of_text c (ps_buf ps)) true) =? ST_ROOT then PMR.ret (PMR.set_st (PMR.set_more (PMR.of_text c (ps_buf ps)) true) ST_ACCEPT) []
                else PMR.err (PMR.set_more (PMR.of_text c (ps_buf ps)) true) [] PMR.E_SYNTAX)
               = PMR.ret (PMR.set_st (PMR.set_more (PMR.of_text c (ps_buf ps)) true) (if Z.eqb (ps_level ps) 0 then ST_ACCEPT else ST_EXPECT_COMMA_OR_END)) []).
  { destruct (Z.eqb_spec (ps_level ps) 0) as [H0|H0]; [rewrite (T0 H0); reflexivity|]. destruct (T1 H0) as [-> | ->]; reflexivity. }
  rewrite E2. unfold PMW.w_after.
  cbn [PMRF.pre PMR.r_of0 PMR.ret PMW.r_code PMW.r_evs PMW.r_allow PMW.r_ctrl PMW.r_used PMR.q_c PMR.q_w PMR.q_evs PMR.q_al PMR.q_code PMW.es_run PMW.ind_run app Z.add].
  unfold PMW.ind_k, PMW.step_k. cbn [PMW.eev_of PMES.estep PMES.ev_ind PMES.quotes].
  split; [exact Hc0|]. split; [exact Hes|].
  split; [exists pay; split; [unfold PMR.al_num; cbn [PMR.c_dlen PMR.of_text PMR.set_tok]; clear -Hpay; lia | rewrite Hlen; clear; lia]|]. intros _.
  split; [|split; [unfold winlen; rewrite Q6; clear; lia | cbn [Z.to_nat skipn]; exact HWB]].
  apply rm_match_plain; cbn [PMR.c_st PMR.c_more PMR.c_done PMR.c_level PMR.c_stack PMR.set_st PMR.set_more PMR.of_text PMR.set_tok];
    [rewrite Q3; reflexivity | rewrite Q2; reflexivity | rewrite Hd; exact R3 | rewrite Q5; exact R4 | rewrite Q4; exact R5 | rewrite Q3 | rewrite Q3];
    clear; destruct (ps_level ps =? 0); unfold ST_ACCEPT, ST_EXPECT_COMMA_OR_END, ST_STRING, ST_NUMBER; lia.
Qed.

(* [comment removed for export] *)
Lemma w3_begin_member : forall c (M M' : mem) P ps ps' w x rest stz,
  (PMRXA.rm_matchA L) c M P ps -> ps_more ps = true -> ps_stack ps = rest ++ [x] ->
  ((stz = 10 /\ x = 8) \/ (stz = 13 /\ x = 14)) ->
  ps_st ps' = stz -> ps_more ps' = true -> ps_done ps' = ps_done ps -> ps_level ps' = ps_level ps -> ps_stack ps' = ps_stack ps -> ps_win ps' = ps_win ps ->
  (PMXAW.win_bytesA L) M' ps' w ->
  w3p PMW.FBeginMember c w M' P ps ps' w 0.
Proof.
  intros c M M' P ps ps' w x rest stz ((R1 & R2 & R3 & R4 & R5) & _ & _) Hm Hs Hsx Q1 Q2 Q3 Q4 Q5 Q6 HWB. unfold w3p.
  change (PMW.rm_step (PMRXA.the_rmA L) PMW.FBeginMember c w) with (PMR.r_of w (PMR.begin_member c w)). unfold PMR.begin_member, PMR.top. rewrite R5, Hs, last_last.
  assert (E : (if x =? ST_OBJECT then PMR.ret (PMR.set_st c ST_EXPECT_MEMBER_NAME) w
               else if x =? ST_ARRAY then PMR.ret (PMR.set_st c ST_EXPECT_VALUE) w
               else if x =? ST_ROOT then PMR.ret c w else PMR.err c w PMR.E_SYNTAX) = PMR.ret (PMR.set_st c stz) w).
  { unfold ST_ARRAY, ST_OBJECT, ST_ROOT, ST_EXPECT_MEMBER_NAME, ST_EXPECT_VALUE. destruct Hsx as [(-> & ->)|(-> & ->)]; reflexivity. }
  rewrite E. unfold PMW.w_after. cbn [PMR.r_of PMR.ret PMW.r_code PMW.r_evs PMW.r_ctrl PMW.r_used PMR.q_c PMR.q_w PMR.q_evs PMR.q_code].
  split; [reflexivity|]. split; [reflexivity|]. intros _.
  split; [|split; [unfold winlen; rewrite Q6; clear; lia | rewrite Z.sub_diag; cbn [Z.to_nat skipn]; exact HWB]].
  apply rm_match_plain; cbn [PMR.c_st PMR.c_more PMR.c_done PMR.c_level PMR.c_stack PMR.set_st];
    [rewrite Q1; reflexivity | rewrite Q2, R2; exact Hm | rewrite Q3; exact R3 | rewrite Q4; exact R4 | rewrite Q5; exact R5 | rewrite Q1 | rewrite Q1];
    clear -Hsx; destruct Hsx as [(-> & _)|(-> & _)]; unfold ST_STRING, ST_NUMBER; lia.
Qed.

(* [comment removed for export] *)
Lemma win_bytes_skip : forall (M' : mem) ps' p e (n : nat) w st sst nst m dn lv stk sb sc bc bp buf,
  (PMXAW.win_bytesA L) M' ps' w -> ps_win ps' = Some (p, e) -> Z.of_nat n <= Z.of_nat (length w) ->
  (PMXAW.win_bytesA L) M' (PS st sst nst m dn lv stk sb sc bc bp buf (Some (p + Z.of_nat n, e))) (skipn n w).
Proof.
  intros M' ps' p e n w st sst nst m dn lv stk sb sc bc bp buf HWB Hw Hn. unfold PMXAW.win_bytesA in *. rewrite Hw in HWB. cbn [ps_win].
  destruct HWB as (HB & HL & HF). split; [|split; [rewrite length_skipn; lia | rewrite <- (firstn_skipn n w) in HF; apply Forall_app in HF as [_ HF]; exact HF]].
  intros i Hi. rewrite length_skipn in Hi. rewrite nth_skipn. replace (p + Z.of_nat n + Z.of_nat i) with (p + Z.of_nat (n + i)) by lia. apply HB. lia.
Qed.

(* [comment removed for export] *)
Definition byte_var (seg : expr) (cells : list kentry) (k : Z) : option nat :=
  match find (fun K => match K with KWord (SA b o) 1%nat (EVar _) => (expr_eqb b seg && Z.eqb o k)%bool | _ => false end) cells with
  | Some (KWord _ _ (EVar v)) => Some v | _ => None end.
Lemma byte_var_sound : forall seg cells k v E' (M' : mem) p w,
  byte_var seg cells k = Some v -> has cells (KRange (EVar v) 0 255) = true -> know_ok RSEGS E' M' cells -> uv E' seg = p -> L5.bytes_at RSEGS M' p w -> Forall (fun b => 0 <= b <= 255) w ->
  0 <= k < Z.of_nat (length w) -> uv E' (EVar v) = nth (Z.to_nat k) w 0.
Proof.
  intros seg cells k v E' M' p w Hbv Hrg HK Hp HB HF Hk. unfold byte_var in Hbv.
  pose proof (has_ok E' M' _ _ HK Hrg) as R1. cbn [kentry_ok] in R1. fold (uv E' (EVar v)) in R1.
  destruct (find _ cells) as [K|] eqn:Hf; [|discriminate Hbv]. apply find_some in Hf as [Hin HKc].
  destruct K as [[b o] w1 e| | | | | | | | | ]; try discriminate Hbv. destruct w1 as [|[|w1]]; try discriminate HKc. destruct e; try discriminate HKc.
  injection Hbv as <-. apply andb_prop in HKc as [Hb Ho]. apply expr_eqb_eq in Hb. apply Z.eqb_eq in Ho. subst b o.
  pose proof ((CL5A.kword8_elim RSEGS) E' M' _ _ (p + k) (proj1 (Forall_forall _ _) HK _ Hin) ltac:(unfold estart; cbn [a_base a_off]; fold (uv E' seg); rewrite Hp; reflexivity)) as U1.
  pose proof (HB (Z.to_nat k) ltac:(lia)) as U2. rewrite Z2Nat.id in U2 by lia.
  pose proof (proj1 (Forall_forall _ _) HF (nth (Z.to_nat k) w 0) ltac:(apply nth_In; lia)) as R2. cbn beta in R2.
  exact (u8_inj M' (p + k) _ _ U1 U2 ltac:(clear -R1; lia) ltac:(clear -R2; lia)).
Qed.
Definition wmatch_chk (seg : expr) (cells : list kentry) (litb : list (Z * Z)) : bool :=
  forallb (fun kl => match byte_var seg cells (fst kl) with Some v => (has cells (KRange (EVar v) 0 255) && adm_all v cells 0 256 (fun b => b =? snd kl))%bool | None => false end) litb.
Definition wmiss_chk (seg : expr) (cells : list kentry) (litb : list (Z * Z)) : bool :=
  existsb (fun kl => match byte_var seg cells (fst kl) with Some v => (has cells (KRange (EVar v) 0 255) && adm_all v cells 0 256 (fun b => negb (b =? snd kl)))%bool | None => false end) litb.
Lemma wmatch_sound : forall seg cells litb E' (M' : mem) p w, wmatch_chk seg cells litb = true -> know_ok RSEGS E' M' cells -> uv E' seg = p ->
  L5.bytes_at RSEGS M' p w -> Forall (fun b => 0 <= b <= 255) w -> (forall kl, In kl litb -> 0 <= fst kl < Z.of_nat (length w)) ->
  forall kl, In kl litb -> nth (Z.to_nat (fst kl)) w 0 = snd kl.
Proof.
  intros seg cells litb E' M' p w H HK Hp HB HF Hr kl Hin. unfold wmatch_chk in H. apply forallb_forall with (x := kl) in H; [|exact Hin].
  destruct (byte_var seg cells (fst kl)) as [v|] eqn:Hbv; [|discriminate H]. apply andb_prop in H as [Hrg H].
  pose proof (byte_var_sound seg cells (fst kl) v E' M' p w Hbv Hrg HK Hp HB HF (Hr kl Hin)) as Hv.
  pose proof (proj1 (Forall_forall _ _) HF (nth (Z.to_nat (fst kl)) w 0) ltac:(apply nth_In; pose proof (Hr kl Hin); lia)) as R2. cbn beta in R2.
  pose proof (adm_all_sound v cells 0 256 _ E' M' _ H HK Hv ltac:(clear -R2; lia)) as X. cbn beta in X. apply Z.eqb_eq in X. exact X.
Qed.
Lemma wmiss_sound : forall seg cells litb E' (M' : mem) p w, wmiss_chk seg cells litb = true -> know_ok RSEGS E' M' cells -> uv E' seg = p ->
  L5.bytes_at RSEGS M' p w -> Forall (fun b => 0 <= b <= 255) w -> (forall kl, In kl litb -> 0 <= fst kl < Z.of_nat (length w)) ->
  exists kl, In kl litb /\ nth (Z.to_nat (fst kl)) w 0 <> snd kl.
Proof.
  intros seg cells litb E' M' p w H HK Hp HB HF Hr. unfold wmiss_chk in H. apply existsb_exists in H as (kl & Hin & H). exists kl. split; [exact Hin|].
  destruct (byte_var seg cells (fst kl)) as [v|] eqn:Hbv; [|discriminate H]. apply andb_prop in H as [Hrg H].
  pose proof (byte_var_sound seg cells (fst kl) v E' M' p w Hbv Hrg HK Hp HB HF (Hr kl Hin)) as Hv.
  pose proof (proj1 (Forall_forall _ _) HF (nth (Z.to_nat (fst kl)) w 0) ltac:(apply nth_In; pose proof (Hr kl Hin); lia)) as R2. cbn beta in R2.
  pose proof (adm_all_sound v cells 0 256 _ E' M' _ H HK Hv ltac:(clear -R2; lia)) as X. cbn beta in X. apply negb_true_iff in X. apply Z.eqb_neq in X. exact X.
Qed.
(* [comment removed for export] *)
Definition litb_of (tail : list Z) : list (Z * Z) := combine (map Z.of_nat (seq 1 (length tail))) tail.
Lemma nth_tl : forall {A} i (l : list A) d, nth i (tl l) d = nth (S i) l d.
Proof. intros A i [|x l] d; destruct i; reflexivity. Qed.
Lemma nth_firstn_lt : forall {A} n i (l : list A) d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof. intros A n. induction n as [|n IH]; intros i [|x l] d Hi; [lia | lia | destruct i; reflexivity |]. destruct i; [reflexivity|]. cbn [firstn nth]. apply IH. lia. Qed.
Lemma litb_of_length : forall tail, length (litb_of tail) = length tail.
Proof. intros tail. unfold litb_of. rewrite length_combine, length_map, length_seq. lia. Qed.
Lemma litb_of_nth : forall tail i, (i < length tail)%nat -> nth i (litb_of tail) (0, 0) = (Z.of_nat (S i), nth i tail 0).
Proof.
  intros tail i Hi. unfold litb_of. rewrite combine_nth by (rewrite length_map, length_seq; reflexivity). f_equal.
  rewrite (nth_indep _ 0 (Z.of_nat 0%nat)) by (rewrite length_map, length_seq; exact Hi). rewrite map_nth, seq_nth by exact Hi. lia.
Qed.
Lemma cmp_nth : forall tail w i, (S (length tail) <= length w)%nat -> (i < length tail)%nat ->
  nth i (combine (tl (firstn (S (length tail)) w)) tail) (0, 0) = (nth (S i) w 0, nth i tail 0).
Proof.
  intros tail w i Hlen Hi. rewrite combine_nth by (rewrite length_tl, length_firstn; lia). rewrite nth_tl, nth_firstn_lt by lia. reflexivity.
Qed.
Lemma lit_cmp_true : forall tail w, (S (length tail) <= length w)%nat -> (forall kl, In kl (litb_of tail) -> nth (Z.to_nat (fst kl)) w 0 = snd kl) ->
  forallb (fun q => fst q =? snd q) (combine (tl (firstn (S (length tail)) w)) tail) = true.
Proof.
  intros tail w Hlen H. apply forallb_forall. intros ab Hin. apply In_nth with (d := (0, 0)) in Hin as (i & Hi & <-).
  rewrite length_combine, length_tl, length_firstn in Hi. rewrite cmp_nth by lia. cbn [fst snd]. apply Z.eqb_eq.
  specialize (H _ (@nth_In _ i (litb_of tail) (0, 0) ltac:(rewrite litb_of_length; lia))). rewrite litb_of_nth in H by lia. cbn [fst snd] in H. rewrite Nat2Z.id in H. exact H.
Qed.
Lemma lit_cmp_false : forall tail w, (S (length tail) <= length w)%nat -> (exists kl, In kl (litb_of tail) /\ nth (Z.to_nat (fst kl)) w 0 <> snd kl) ->
  forallb (fun q => fst q =? snd q) (combine (tl (firstn (S (length tail)) w)) tail) = false.
Proof.
  intros tail w Hlen (kl & Hin & Hne). apply In_nth with (d := (0, 0)) in Hin as (i & Hi & <-). rewrite litb_of_length in Hi.
  rewrite litb_of_nth in Hne by exact Hi. cbn [fst snd] in Hne. rewrite Nat2Z.id in Hne.
  destruct (forallb _ _) eqn:Hf; [|reflexivity]. exfalso. apply Hne.
  apply forallb_forall with (x := (nth (S i) w 0, nth i tail 0)) in Hf; [cbn [fst snd] in Hf; apply Z.eqb_eq in Hf; exact Hf|].
  rewrite <- (cmp_nth tail w i Hlen Hi). apply nth_In. rewrite length_combine, length_tl, length_firstn. lia.
Qed.

(* [comment removed for export] *)
Definition lit_f (f : PMW.fname) : option (list Z * Z) :=
  match f with PMW.FParseNull => Some ([117; 108; 108], PMR.ST_N) | PMW.FParseTrue => Some ([114; 117; 101], PMR.ST_T) | PMW.FParseFalse => Some ([97; 108; 115; 101], PMR.ST_F) | _ => None end.
Lemma lit_step : forall f tail sst c w, lit_f f = Some (tail, sst) -> PMW.rm_step (PMRXA.the_rmA L) f c w = PMR.r_of w (PMR.parse_lit tail sst c w).
Proof. intros f tail sst c w H. destruct f; cbn in H; try discriminate H; injection H as <- <-; reflexivity. Qed.
(* [comment removed for export] *)
Lemma w3_lit_short : forall f tail sst c (M M' : mem) P ps ps' w p e,
  lit_f f = Some (tail, sst) -> (PMRXA.rm_matchA L) c M P ps -> ps_win ps = Some (p, e) -> Z.of_nat (length w) = e - p ->
  ps_more ps = true -> (length w < S (length tail))%nat -> (1 <= length w)%nat ->
  ps_st ps' = sst -> ps_more ps' = true -> ps_done ps' = ps_done ps -> ps_level ps' = ps_level ps -> ps_stack ps' = ps_stack ps -> ps_win ps' = Some (p + 1, e) ->
  (PMXAW.win_bytesA L) M' ps' (skipn 1 w) ->
  forall eg, w3x f c w M' P ps ps' w eg eg 0.
Proof.
  intros f tail sst c M M' P ps ps' w p e Hf ((R1 & R2 & R3 & R4 & R5) & _ & _) Hw Hl Hm Hsh H1 Q1 Q2 Q3 Q4 Q5 Q6 HWB eg. unfold w3x. rewrite (lit_step f tail sst c w Hf).
  unfold PMR.parse_lit. replace (S (length tail) <=? length w)%nat with false by (symmetry; apply Nat.leb_gt; lia). unfold PMW.w_after.
  cbn [PMR.r_of PMR.ret PMW.r_code PMW.r_evs PMW.r_allow PMW.r_ctrl PMW.r_used PMR.q_c PMR.q_w PMR.q_evs PMR.q_al PMR.q_code PMW.es_run PMW.ind_run].
  assert (HT : Z.of_nat (length (tl w)) = Z.of_nat (length w) - 1) by (destruct w; cbn [tl length] in *; lia).
  split; [reflexivity|]. split; [reflexivity|]. split; [exists 0; clear; lia|]. intros _.
  split; [|split; [unfold winlen; rewrite Hw, Q6, HT; clear -Hl; lia | rewrite HT; replace (Z.to_nat (Z.of_nat (length w) - (Z.of_nat (length w) - 1))) with 1%nat by lia; exact HWB]].
  apply rm_match_plain; cbn [PMR.c_st PMR.c_more PMR.c_done PMR.c_level PMR.c_stack PMR.set_st];
    [rewrite Q1; reflexivity | rewrite Q2, R2; exact Hm | rewrite Q3; exact R3 | rewrite Q4; exact R4 | rewrite Q5; exact R5 | rewrite Q1 | rewrite Q1];
    destruct f; cbn in Hf; try discriminate Hf; injection Hf as _ <-; unfold PMR.ST_N, PMR.ST_T, PMR.ST_F, ST_STRING, ST_NUMBER; clear; lia.
Qed.
(* [comment removed for export] *)
Lemma w3_lit_match : forall f tail sst c (M M' : mem) P ps ps' w p e eg eg' (ev : eev),
  lit_f f = Some (tail, sst) -> (PMRXA.rm_matchA L) c M P ps -> ps_win ps = Some (p, e) -> Z.of_nat (length w) = e - p ->
  ps_more ps = true -> (S (length tail) <= length w)%nat -> forallb (fun q => fst q =? snd q) (combine (tl (firstn (S (length tail)) w)) tail) = true ->
  ps_st ps' = (if ps_level ps =? 0 then ST_ACCEPT else ST_EXPECT_COMMA_OR_END) -> ps_more ps' = true -> ps_done ps' = ps_done ps -> ps_level ps' = ps_level ps ->
  ps_stack ps' = ps_stack ps -> ps_win ps' = Some (p + Z.of_nat (S (length tail)), e) ->
  (ev = EvNull \/ exists b, ev = EvBool b) -> g_es eg' = estep (g_es eg) ev -> (exists pay, pay_ok ev pay /\ g_len eg' = g_len eg + ev_ind (g_es eg) ev + pay) ->
  (PMXAW.win_bytesA L) M' ps' (skipn (S (length tail)) w) ->
  w3x f c w M' P ps ps' w eg eg' 0.
Proof.
  intros f tail sst c M M' P ps ps' w p e eg eg' ev Hf ((R1 & R2 & R3 & R4 & R5) & _ & _) Hw Hl Hm Hlen Hcmp Q1 Q2 Q3 Q4 Q5 Q6 Hev Hes (pay & Hpay & Hglen) HWB.
  unfold w3x. rewrite (lit_step f tail sst c w Hf). unfold PMR.parse_lit. replace (S (length tail) <=? length w)%nat with true by (symmetry; apply Nat.leb_le; exact Hlen).
  rewrite Hcmp. unfold PMR.lit_done, PMR.st_after, PMW.w_after.
  cbn [PMR.r_of PMW.r_code PMW.r_evs PMW.r_allow PMW.r_ctrl PMW.r_used PMR.q_c PMR.q_w PMR.q_evs PMR.q_al PMR.q_code PMW.es_run PMW.ind_run PMR.c_level PMR.set_more].
  unfold PMW.ind_k, PMW.step_k. cbn [PMW.eev_of]. rewrite R4, length_skipn.
  assert (HEV : estep (g_es eg) ev = estep (g_es eg) EvNull /\ ev_ind (g_es eg) ev = ev_ind (g_es eg) EvNull /\ 0 <= pay <= PMR.AL_LIT).
  { unfold PMR.AL_LIT. destruct Hev as [-> | (b & ->)]; cbn in Hpay; [repeat split; lia|]. split; [reflexivity|]. split; [reflexivity|]. destruct b; lia. }
  destruct HEV as (E1 & E2 & E3).
  split; [reflexivity|]. split; [rewrite Hes; exact E1|]. split; [exists pay; split; [exact E3 | rewrite Hglen, E2; clear; lia]|]. intros _.
  split; [|split; [unfold winlen; rewrite Hw, Q6; clear -Hl Hlen; lia
                 | replace (Z.to_nat (Z.of_nat (length w) - Z.of_nat (length w - S (length tail)))) with (S (length tail)) by (clear -Hlen; lia); exact HWB]].
  apply rm_match_plain; cbn [PMR.c_st PMR.c_more PMR.c_done PMR.c_level PMR.c_stack PMR.set_st PMR.set_more];
    [rewrite Q1; reflexivity | rewrite Q2; reflexivity | rewrite Q3; exact R3 | rewrite Q4; exact R4 | rewrite Q5; exact R5 | rewrite Q1 | rewrite Q1];
    clear; destruct (ps_level ps =? 0); unfold ST_ACCEPT, ST_EXPECT_COMMA_OR_END, ST_STRING, ST_NUMBER; lia.
Qed.
(* [comment removed for export] *)
Lemma w3_lit_miss : forall f tail sst c (M M' : mem) P ps ps' w,
  lit_f f = Some (tail, sst) -> (S (length tail) <= length w)%nat -> forallb (fun q => fst q =? snd q) (combine (tl (firstn (S (length tail)) w)) tail) = false ->
  forall eg, w3x f c w M' P ps ps' w eg eg 11.
Proof.
  intros f tail sst c M M' P ps ps' w Hf Hlen Hcmp eg. unfold w3x. rewrite (lit_step f tail sst c w Hf). unfold PMR.parse_lit.
  replace (S (length tail) <=? length w)%nat with true by (symmetry; apply Nat.leb_le; exact Hlen). rewrite Hcmp.
  cbn [PMR.r_of PMR.err PMW.r_code PMW.r_evs PMW.r_allow PMR.q_c PMR.q_w PMR.q_evs PMR.q_al PMR.q_code PMW.es_run PMW.ind_run].
  split; [reflexivity|]. split; [reflexivity|]. split; [exists 0; clear; lia|]. intros X. exfalso. clear -X. lia.
Qed.

(* [comment removed for export] *)
Definition EC_KIND (arr : bool) : Z := if arr then ST_ARRAY else ST_OBJECT.
Definition EC_OTHER (arr : bool) : Z := if arr then ST_OBJECT else ST_ARRAY.
Definition EC_CLEVEL (arr : bool) : Z := if arr then PMR.E_UNEXP_RBRACKET else PMR.E_UNEXP_RBRACE.
Definition EC_COTHER (arr : bool) : Z := if arr then PMR.E_COMMA_OR_RBRACE else PMR.E_COMMA_OR_RBRACKET.
Lemma end_container_step : forall (arr : bool) c w, PMW.rm_step (PMRXA.the_rmA L) (if arr then PMW.FEndArray else PMW.FEndObject) c w = PMR.r_of w (PMR.end_container arr c w).
Proof. intros arr c w. destruct arr; reflexivity. Qed.
Lemma end_container_err_code : forall (arr : bool) c (M : mem) P ps w, (PMRXA.rm_matchA L) c M P ps ->
  (ps_level ps = 0 -> PMW.r_code (PMW.rm_step (PMRXA.the_rmA L) (if arr then PMW.FEndArray else PMW.FEndObject) c w) = EC_CLEVEL arr) /\
  (forall rest x, 1 <= ps_level ps -> ps_stack ps = rest ++ [x] -> x <> EC_KIND arr ->
     PMW.r_code (PMW.rm_step (PMRXA.the_rmA L) (if arr then PMW.FEndArray else PMW.FEndObject) c w) = (if x =? EC_OTHER arr then EC_COTHER arr else EC_CLEVEL arr)).
Proof.
  intros arr c M P ps w ((R1 & R2 & R3 & R4 & R5) & _ & _). rewrite end_container_step. unfold PMR.end_container. rewrite R4. split.
  - intros H0. rewrite H0. change (0 <? 1) with true. destruct arr; reflexivity.
  - intros rest x HL HS HX. replace (ps_level ps <? 1) with false by (symmetry; apply Z.ltb_ge; exact HL).
    unfold PMR.top. rewrite R5, HS, last_last.
    destruct arr; unfold EC_KIND, EC_OTHER, EC_COTHER, EC_CLEVEL in *;
      [ replace (x =? ST_ARRAY) with false by (symmetry; apply Z.eqb_neq; exact HX); destruct (x =? ST_OBJECT); reflexivity
      | replace (x =? ST_OBJECT) with false by (symmetry; apply Z.eqb_neq; exact HX); destruct (x =? ST_ARRAY); reflexivity ].
Qed.

Lemma w3_end_container : forall (arr : bool) c (M M' : mem) P ps ps' w eg eg' code,
  (PMRXA.rm_matchA L) c M P ps -> wf_ps ps' -> ps_done ps' = ps_done ps ->
  ((code = 0 /\ ps_level ps' = ps_level ps - 1 /\ ps_more ps' = true /\ (exists rest, ps_stack ps = rest ++ [EC_KIND arr] /\ ps_stack ps' = rest) /\ ps_st ps' = (if ps_level ps' =? 0 then ST_ACCEPT else ST_EXPECT_COMMA_OR_END) /\ ps_win ps' = ps_win ps) \/ In code [20; 21; 22; 23]) ->
  (code <> 0 -> code = PMW.r_code (PMW.rm_step (PMRXA.the_rmA L) (if arr then PMW.FEndArray else PMW.FEndObject) c w)) ->
  (code = 0 -> g_es eg' = estep (g_es eg) EvEnd /\ exists pay, pay_ok EvEnd pay /\ g_len eg' = g_len eg + ev_ind (g_es eg) EvEnd + pay) ->
  (code <> 0 -> eg' = eg) ->
  (PMXAW.win_bytesA L) M' ps' w ->
  w3x (if arr then PMW.FEndArray else PMW.FEndObject) c w M' P ps ps' w eg eg' code.
Proof.
  intros arr c M M' P ps ps' w eg eg' code HRM Hwf Hdone HREL HWD HEV HEQ HWB.
  pose proof HRM as ((R1 & R2 & R3 & R4 & R5) & _ & _). unfold w3x. rewrite end_container_step in HWD |- *. unfold PMR.end_container in HWD |- *. rewrite R4 in HWD |- *.
  destruct (Z.eq_dec code 0) as [Hc0|Hnz].
  - destruct HREL as [(_ & HL & HMO & (rest & HS & HS') & HST & HWIN)|Q]; [|exfalso; rewrite Hc0 in Q; cbn [In] in Q; lia].
    assert (HL1 : 1 <= ps_level ps).
    { destruct Hwf as (_ & _ & _ & _ & C & T & _ & _ & HM). destruct (HM HMO) as (_ & HLV & _). clear -HL HLV. lia. }
    replace (ps_level ps <? 1) with false by (symmetry; apply Z.ltb_ge; exact HL1).
    unfold PMR.top. rewrite R5, HS. unfold EC_KIND. rewrite last_last, Z.eqb_refl.
    destruct (HEV Hc0) as (Hes & pay & Hpay & Hlen). cbn in Hpay. unfold PMW.w_after.
    cbn [PMR.r_of PMW.r_code PMW.r_evs PMW.r_allow PMW.r_ctrl PMW.r_used PMR.q_c PMR.q_w PMR.q_evs PMR.q_al PMR.q_code PMW.es_run PMW.ind_run]. unfold PMW.ind_k, PMW.step_k. cbn [PMW.eev_of].
    split; [exact Hc0|]. split; [exact Hes|]. split; [exists 0; split; [clear; lia | rewrite Hlen, Hpay; clear; lia]|]. intros _.
    split; [|split; [unfold winlen; rewrite HWIN; clear; lia | rewrite Z.sub_diag; cbn [Z.to_nat skipn]; exact HWB]].
    apply rm_match_plain; cbn [PMR.c_st PMR.c_more PMR.c_done PMR.c_level PMR.c_stack PMR.set_more PMR.set_st PMR.pop PMR.set_stack PMR.set_level PMR.st_after]; rewrite ?R4, <- ?HL;
      [symmetry; exact HST | symmetry; exact HMO | rewrite Hdone; exact R3 | reflexivity | rewrite R5, HS; unfold EC_KIND; rewrite removelast_last; symmetry; exact HS' | rewrite HST | rewrite HST];
      clear; destruct (ps_level ps' =? 0); unfold ST_ACCEPT, ST_EXPECT_COMMA_OR_END, ST_STRING, ST_NUMBER; lia.
  - pose proof (HWD Hnz) as HC. rewrite (HEQ Hnz). unfold PMW.w_after. revert HC.
    assert (GEN : forall q : PMR.res, code = PMR.q_code q -> (PMR.q_code q = 0 \/ (PMR.q_evs q = [] /\ PMR.q_al q = 0)) ->
              code = PMW.r_code (PMR.r_of w q) /\ g_es eg = PMW.es_run (g_es eg) (PMW.r_evs (PMR.r_of w q)) /\ (exists pay0, 0 <= pay0 <= PMW.r_allow (PMR.r_of w q) /\ g_len eg = g_len eg + PMW.ind_run (g_es eg) (PMW.r_evs (PMR.r_of w q)) + pay0) /\ (code = 0 -> PMW.rm_match (PMRXA.the_rmA L) (PMW.r_ctrl (PMR.r_of w q)) M' P ps' /\ PMW.r_used (PMR.r_of w q) = winlen ps - winlen ps' /\ (PMXAW.win_bytesA L) M' ps' (skipn (Z.to_nat (PMW.r_used (PMR.r_of w q))) w))).
    { intros q Hq [Hz|[He Ha]]; [exfalso; clear -Hq Hz Hnz; lia|]. cbn [PMR.r_of PMW.r_code PMW.r_evs PMW.r_allow]. rewrite He, Ha. cbn [PMW.es_run PMW.ind_run].
      split; [exact Hq|]. split; [reflexivity|]. split; [exists 0; clear; lia|]. intros X. exfalso. exact (Hnz X). }
    destruct (ps_level ps <? 1); [intros HC; apply GEN; [exact HC | right; split; reflexivity]|].
    destruct (PMR.top c =? (if arr then ST_ARRAY else ST_OBJECT)); [intros HC; apply GEN; [exact HC | left; reflexivity]|].   (* [comment removed for export] *)
    destruct (PMR.top c =? (if arr then ST_OBJECT else ST_ARRAY)); intros HC; (apply GEN; [exact HC | right; split; reflexivity]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma skipn_nth_cons : forall (n : nat) (w : list Z), (n < length w)%nat -> skipn n w = nth n w 0 :: skipn (S n) w.
Proof. induction n as [|n IH]; intros [|b r] H; cbn in H |- *; try lia; [reflexivity|]. apply IH. lia. Qed.
Lemma ss_ws : forall c w n, (n < length w)%nat -> (nth n w 0 = 32 \/ nth n w 0 = 9 \/ nth n w 0 = 10) ->
  PMR.skip_space c (skipn n w) = PMR.skip_space c (skipn (S n) w).
Proof. intros c w n Hn Hb. rewrite (skipn_nth_cons n w Hn). set (r := skipn (S n) w). cbn [PMR.skip_space]. destruct Hb as [-> |[-> | ->]]; reflexivity. Qed.
Lemma ss_stop : forall c w n, (n < length w)%nat -> PMR.is_ws (nth n w 0) = false -> PMR.skip_space c (skipn n w) = (c, skipn n w).
Proof.
  intros c w n Hn Hb. rewrite (skipn_nth_cons n w Hn). set (r := skipn (S n) w). set (b := nth n w 0) in *. cbn [PMR.skip_space]. unfold PMR.is_ws in Hb.
  apply orb_false_elim in Hb as [Hb H13]. rewrite Hb, H13. reflexivity.
Qed.
Lemma ss_cr_last : forall c w n, (S n = length w)%nat -> nth n w 0 = 13 -> PMR.skip_space c (skipn n w) = (PMR.set_st (PMR.push c (PMR.c_st c)) ST_CR, []).
Proof. intros c w n Hn Hb. rewrite (skipn_nth_cons n w) by lia. rewrite Hb, (skipn_all2 w) by lia. reflexivity. Qed.
Lemma ss_crlf : forall c w n, (S n < length w)%nat -> nth n w 0 = 13 -> nth (S n) w 0 = 10 -> PMR.skip_space c (skipn n w) = PMR.skip_space c (skipn (S (S n)) w).
Proof. intros c w n Hn Hb Hb2. rewrite (skipn_nth_cons n w) by lia. rewrite (skipn_nth_cons (S n) w) by lia. rewrite Hb, Hb2. set (r := skipn (S (S n)) w). reflexivity. Qed.
Lemma ss_cr : forall c w n, (S n < length w)%nat -> nth n w 0 = 13 -> nth (S n) w 0 <> 10 -> PMR.skip_space c (skipn n w) = PMR.skip_space c (skipn (S n) w).
Proof.
  intros c w n Hn Hb Hb2. rewrite (skipn_nth_cons n w) by lia. rewrite (skipn_nth_cons (S n) w) by lia. rewrite Hb. set (r := skipn (S (S n)) w). set (b2 := nth (S n) w 0) in *.
  cbn [PMR.skip_space]. rewrite (proj2 (Z.eqb_neq b2 10) Hb2). reflexivity.
Qed.
Lemma ss_all : forall c w, PMR.skip_space c (skipn (length w) w) = (c, []).
Proof. intros c w. rewrite skipn_all. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma esc_cls_bound : forall c, 1 <= esc_cls c <= 6.
Proof. intros c. unfold esc_cls. destruct (existsb _ _); [lia|]. destruct ((c mod 256 <? 32) || (c mod 256 =? 127)); lia. Qed.
Lemma esc_len_bound : forall bs, 0 <= esc_len bs <= 6 * Z.of_nat (length bs).
Proof. induction bs as [|b bs IH]; cbn [esc_len fold_right length]; [lia|]. fold (esc_len bs). pose proof (esc_cls_bound b). lia. Qed.
Lemma str_pay_bound : forall tag bs pay, pay_ok (EvStr tag bs) pay -> 0 <= pay <= PMR.al_str (Z.of_nat (length bs)).
Proof.
  intros tag bs pay H. cbn in H. unfold PMR.al_str. pose proof (esc_len_bound bs). destruct ((tag =? 1) || (tag =? 2) || (tag =? 3)); subst pay; unfold len; lia.
Qed.
Lemma key_pay_bound : forall bs pay, pay_ok (EvKey bs) pay -> 0 <= pay <= PMR.al_str (Z.of_nat (length bs)).
Proof. intros bs pay H. cbn in H. subst pay. unfold PMR.al_str. pose proof (esc_len_bound bs). lia. Qed.
Lemma end_string_step : forall c x, PMW.rm_step (PMRXA.the_rmA L) PMW.FEndStringValue c x = PMR.r_of0 (PMR.end_string (PMR.of_text c x) []).
Proof. intros. reflexivity. Qed.
Lemma of_text_fields : forall c x,
  PMR.c_st (PMR.of_text c x) = PMR.c_st c /\ PMR.c_more (PMR.of_text c x) = PMR.c_more c /\ PMR.c_done (PMR.of_text c x) = PMR.c_done c /\
  PMR.c_level (PMR.of_text c x) = PMR.c_level c /\ PMR.c_stack (PMR.of_text c x) = PMR.c_stack c /\
  PMR.c_dlen (PMR.of_text c x) = Z.of_nat (length x) /\ PMR.u8_finish (PMR.c_u8 (PMR.of_text c x)) = PMR.validate x.
Proof. intros c x. unfold PMR.of_text, PMR.set_tok, PMR.validate. cbn. repeat split; reflexivity. Qed.
(* [comment removed for export] *)
Lemma w3_esv_err : forall c x (M' : mem) P ps ps' w eg u,
  PMR.validate x = u -> u <> 0 ->
  w3x PMW.FEndStringValue c x M' P ps ps' w eg eg (PMR.conv_errc u).
Proof.
  intros c x M' P ps ps' w eg u Hu Hnz. unfold w3x. rewrite end_string_step. unfold PMR.end_string.
  destruct (of_text_fields c x) as (_ & _ & _ & _ & _ & _ & F7). rewrite F7, Hu. replace (negb (u =? 0)) with true by (symmetry; apply negb_true_iff; apply Z.eqb_neq; exact Hnz).
  cbn [PMR.r_of0 PMR.err PMW.r_code PMW.r_evs PMW.r_allow PMW.r_ctrl PMW.r_used PMR.q_c PMR.q_evs PMR.q_code PMR.q_al PMW.es_run PMW.ind_run].
  split; [reflexivity|]. split; [reflexivity|]. split; [exists 0; lia|].
  intros H0. exfalso. unfold PMR.conv_errc, PMR.E_OVERLONG, PMR.E_BAD_CONT, PMR.E_UNPAIRED_SURR, PMR.E_ILLEGAL_SURR, PMR.E_ILLEGAL_CODEPOINT in H0.
  destruct (u =? 1); [lia|]. destruct (u =? 2); [lia|]. destruct (u =? 3); [lia|]. destruct (u =? 4); lia.
Qed.
(* [comment removed for export] *)
Lemma w3_esv_value : forall c x (M' : mem) P ps ps' w rest top eg eg' (tag pay : Z),
  PMR.rm_core c ps -> PMR.validate x = 0 -> ps_stack ps = rest ++ [top] -> (top = ST_OBJECT \/ top = ST_ARRAY \/ top = ST_ROOT) ->
  ps_st ps' = (if top =? ST_ROOT then ST_ACCEPT else ST_EXPECT_COMMA_OR_END) -> ps_more ps' = true -> ps_done ps' = ps_done ps -> ps_level ps' = ps_level ps ->
  ps_stack ps' = ps_stack ps -> ps_win ps' = ps_win ps ->
  0 <= tag <= 1 -> g_es eg' = estep (g_es eg) (EvStr tag x) -> pay_ok (EvStr tag x) pay -> g_len eg' = g_len eg + ev_ind (g_es eg) (EvStr tag x) + pay ->
  (PMXAW.win_bytesA L) M' ps' w ->
  w3x PMW.FEndStringValue c x M' P ps ps' w eg eg' 0.
Proof.
  intros c x M' P ps ps' w rest top eg eg' tag pay (R1 & R2 & R3 & R4 & R5) Hv Hs Htop Q1 Q2 Q3 Q4 Q5 Q6 Htag Hes Hpay Hglen HWB.
  unfold w3x. rewrite end_string_step. unfold PMR.end_string. destruct (of_text_fields c x) as (F1 & F2 & F3 & F4 & F5 & F6 & F7). rewrite F7, Hv. cbn [negb Z.eqb].
  unfold PMR.top. rewrite F5, R5, Hs, last_last.
  assert (KS : PMW.kind_of (EvStr tag x) = PMW.EkStr true).
  { cbn. replace ((tag =? 2) || (tag =? 3)) with false; [reflexivity|]. symmetry. apply orb_false_intro; apply Z.eqb_neq; lia. }
  assert (HR : forall stz, stz <> ST_STRING -> stz <> ST_NUMBER -> ps_st ps' = stz ->
    let rr := PMR.r_of0 (PMR.RES (PMR.set_st (PMR.set_more (PMR.of_text c x) true) stz) (tl []) [PMW.EkStr true] (PMR.al_str (PMR.c_dlen (PMR.of_text c x))) 0) in
    0 = PMW.r_code rr /\ g_es eg' = PMW.es_run (g_es eg) (PMW.r_evs rr) /\
    (exists pay0, 0 <= pay0 <= PMW.r_allow rr /\ g_len eg' = g_len eg + PMW.ind_run (g_es eg) (PMW.r_evs rr) + pay0) /\
    (0 = 0 -> PMW.rm_match (PMRXA.the_rmA L) (PMW.r_ctrl rr) M' P ps' /\ PMW.r_used rr = winlen ps - winlen ps' /\ (PMXAW.win_bytesA L) M' ps' (PMW.w_after (PMRXA.the_rmA L) rr w))).
  { intros stz NS NN Hst. cbn [PMR.r_of0 PMW.r_code PMW.r_evs PMW.r_allow PMW.r_ctrl PMW.r_used PMR.q_c PMR.q_evs PMR.q_code PMR.q_al PMW.es_run PMW.ind_run].
    rewrite <- KS, PMW.step_k_of, PMW.ind_k_of, F6. unfold PMW.w_after. cbn [PMW.r_used Z.to_nat skipn].
    split; [reflexivity|]. split; [exact Hes|]. split; [exists pay; split; [exact (str_pay_bound tag x pay Hpay) | rewrite Hglen; lia]|]. intros _.
    split; [|split; [unfold winlen; rewrite Q6; lia | exact HWB]].
    apply rm_match_plain; cbn [PMR.c_st PMR.c_more PMR.c_done PMR.c_level PMR.c_stack PMR.set_st PMR.set_more]; rewrite ?F1, ?F2, ?F3, ?F4, ?F5;
      [rewrite Hst; reflexivity | rewrite Q2; reflexivity | rewrite Q3; exact R3 | rewrite Q4; exact R4 | rewrite Q5; exact R5 | rewrite Hst; exact NS | rewrite Hst; exact NN]. }
  destruct Htop as [-> |[-> | ->]].
  - change (ST_OBJECT =? ST_MEMBER_NAME) with false. change ((ST_OBJECT =? ST_OBJECT) || (ST_OBJECT =? ST_ARRAY)) with true. cbv iota.
    apply (HR ST_EXPECT_COMMA_OR_END); [discriminate | discriminate | rewrite Q1; reflexivity].
  - change (ST_ARRAY =? ST_MEMBER_NAME) with false. change ((ST_ARRAY =? ST_OBJECT) || (ST_ARRAY =? ST_ARRAY)) with true. cbv iota.
    apply (HR ST_EXPECT_COMMA_OR_END); [discriminate | discriminate | rewrite Q1; reflexivity].
  - change (ST_ROOT =? ST_MEMBER_NAME) with false. change ((ST_ROOT =? ST_OBJECT) || (ST_ROOT =? ST_ARRAY)) with false. change (ST_ROOT =? ST_ROOT) with true. cbv iota.
    apply (HR ST_ACCEPT); [discriminate | discriminate | rewrite Q1; reflexivity].
Qed.
(* [comment removed for export] *)
Lemma w3_esv_key : forall c x (M' : mem) P ps ps' w rest eg eg' (pay : Z),
  PMR.rm_core c ps -> PMR.validate x = 0 -> ps_stack ps = rest ++ [ST_MEMBER_NAME] ->
  ps_st ps' = ST_EXPECT_COLON -> ps_more ps' = true -> ps_done ps' = ps_done ps -> ps_level ps' = ps_level ps -> ps_stack ps' = rest -> ps_win ps' = ps_win ps ->
  g_es eg' = estep (g_es eg) (EvKey x) -> pay_ok (EvKey x) pay -> g_len eg' = g_len eg + ev_ind (g_es eg) (EvKey x) + pay ->
  (PMXAW.win_bytesA L) M' ps' w ->
  w3x PMW.FEndStringValue c x M' P ps ps' w eg eg' 0.
Proof.
  intros c x M' P ps ps' w rest eg eg' pay (R1 & R2 & R3 & R4 & R5) Hv Hs Q1 Q2 Q3 Q4 Q5 Q6 Hes Hpay Hglen HWB.
  unfold w3x. rewrite end_string_step. unfold PMR.end_string. destruct (of_text_fields c x) as (F1 & F2 & F3 & F4 & F5 & F6 & F7). rewrite F7, Hv. cbn [negb Z.eqb].
  unfold PMR.top. rewrite F5, R5, Hs, last_last. change (ST_MEMBER_NAME =? ST_MEMBER_NAME) with true. cbv iota.
  cbn [PMR.r_of0 PMW.r_code PMW.r_evs PMW.r_allow PMW.r_ctrl PMW.r_used PMR.q_c PMR.q_evs PMR.q_code PMR.q_al PMW.es_run PMW.ind_run].
  change (PMW.EkKey) with (PMW.kind_of (EvKey x)). rewrite PMW.step_k_of, PMW.ind_k_of, F6. unfold PMW.w_after. cbn [PMW.r_used Z.to_nat skipn].
  split; [reflexivity|]. split; [exact Hes|]. split; [exists pay; split; [exact (key_pay_bound x pay Hpay) | rewrite Hglen; lia]|]. intros _.
  split; [|split; [unfold winlen; rewrite Q6; lia | exact HWB]].
  apply rm_match_plain; cbn [PMR.c_st PMR.c_more PMR.c_done PMR.c_level PMR.c_stack PMR.set_st PMR.set_more PMR.pop PMR.set_stack]; rewrite ?F1, ?F2, ?F3, ?F4, ?F5;
    [rewrite Q1; reflexivity | rewrite Q2; reflexivity | rewrite Q3; exact R3 | rewrite Q4; exact R4 | rewrite Q5, R5, Hs, removelast_last; reflexivity
    | rewrite Q1; discriminate | rewrite Q1; discriminate].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma room_first : forall (eroomA : eghost -> eev -> Prop) CL eg k rest al ev,
  PMXAW.roomwP eroomA CL -> PMXAW.wroom CL eg (k :: rest) al -> PMW.kind_of ev = k -> PMXAW.pay_hi ev <= al -> eroomA eg ev.
Proof.
  intros eroomA CL eg k rest al ev RW HW Hk Hp. apply RW.
  unfold PMXAW.wroom in HW. change (PMW.ind_run (g_es eg) (k :: rest)) with (PMW.ind_k (g_es eg) k + PMW.ind_run (PMW.step_k (g_es eg) k) rest) in HW.
  pose proof (PMXAW.ind_run_nonneg rest (PMW.step_k (g_es eg) k)) as NN. rewrite PMXAW.kmax_kind, Hk. lia.
Qed.
(* [comment removed for export] *)
Lemma room_begin_container : forall (eroomA : eghost -> eev -> Prop) CL (arr : bool) c (M : mem) P ps w eg,
  PMXAW.roomwP eroomA CL -> (PMRXA.rm_matchA L) c M P ps -> ps_level ps < 1024 ->
  PMXAW.wroomr (PMRXA.the_rmA L) CL eg (PMW.rm_step (PMRXA.the_rmA L) (if arr then PMW.FBeginArray else PMW.FBeginObject) c w) -> eroomA eg (EvBegin arr).
Proof.
  intros eroomA CL arr c M P ps w eg RW ((R1 & R2 & R3 & R4 & R5) & _) HL HW.
  assert (E : PMW.rm_step (PMRXA.the_rmA L) (if arr then PMW.FBeginArray else PMW.FBeginObject) c w = PMR.r_of w (PMR.begin_container arr c w)) by (destruct arr; reflexivity).
  rewrite E in HW. unfold PMXAW.wroomr, PMR.begin_container in HW.
  destruct (Z.ltb_spec 1024 (PMR.c_level (PMR.set_level c (PMR.c_level c + 1)))) as [X|X]; [exfalso; cbn [PMR.c_level PMR.set_level] in X; lia|].
  cbn [PMR.r_of PMW.r_evs PMW.r_allow PMR.q_evs PMR.q_al PMR.q_c PMR.q_w PMR.q_code] in HW.
  apply (room_first eroomA CL eg (PMW.EkBegin arr) [] 0 (EvBegin arr) RW HW eq_refl). cbn. lia.
Qed.
End W.
End SPTAW.
