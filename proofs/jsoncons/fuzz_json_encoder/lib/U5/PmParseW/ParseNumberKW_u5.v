(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmLibSpecsX_u5 PmLibSpecsW_u5 PmRef_u5 PmRefFacts_u5 PmRefFacts2_u5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNKW.
Import PML PMES PMR.
Abbreviation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint tokn (c : ctrl) (bs : list Z) : ctrl := match bs with [] => c | b :: r => tokn (tok1 c b) r end.
Definition CI (c : ctrl) (bs : list Z) (k : Z) : ctrl := set_nst (tokn c bs) k.
Lemma tokn_app : forall c u v, tokn c (u ++ v) = tokn (tokn c u) v.
Proof. intros c u; revert c; induction u as [|b u IH]; intros c v; [reflexivity|]. cbn [tokn app]. apply IH. Qed.
Lemma tokn_fields : forall c bs,
  c_st (tokn c bs) = c_st c /\ c_sst (tokn c bs) = c_sst c /\ c_nst (tokn c bs) = c_nst c /\ c_more (tokn c bs) = c_more c /\ c_done (tokn c bs) = c_done c /\
  c_level (tokn c bs) = c_level c /\ c_stack (tokn c bs) = c_stack c /\ c_cp (tokn c bs) = c_cp c /\ c_cp2 (tokn c bs) = c_cp2 c /\
  c_dlen (tokn c bs) = c_dlen c + Z.of_nat (length bs).
Proof.
  intros c bs; revert c; induction bs as [|b bs IH]; intros c; [cbn; repeat split; try reflexivity; lia|].
  cbn [tokn length]. destruct (IH (tok1 c b)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10). rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10.
  unfold tok1, set_tok. cbn. repeat split; try reflexivity. lia.
Qed.
Lemma CI_fields : forall c bs k,
  c_st (CI c bs k) = c_st c /\ c_more (CI c bs k) = c_more c /\ c_done (CI c bs k) = c_done c /\ c_level (CI c bs k) = c_level c /\ c_stack (CI c bs k) = c_stack c /\
  c_nst (CI c bs k) = k /\ c_dlen (CI c bs k) = c_dlen c + Z.of_nat (length bs) /\ c_sst (CI c bs k) = c_sst c /\ c_cp (CI c bs k) = c_cp c /\ c_cp2 (CI c bs k) = c_cp2 c.
Proof.
  intros c bs k. destruct (tokn_fields c bs) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10). unfold CI, set_nst. cbn. repeat split; assumption.
Qed.
Lemma CI_self : forall c, CI c [] (c_nst c) = c.
Proof. intros c. destruct c. reflexivity. Qed.
Lemma CI_step : forall c bs k b k', set_nst (tok1 (CI c bs k) b) k' = CI c (bs ++ [b]) k'.
Proof. intros c bs k b k'. unfold CI. rewrite tokn_app. cbn [tokn]. destruct (tokn c bs). reflexivity. Qed.
Lemma firstn_succ : forall (l : list Z) n, (n < length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l 0].
Proof. induction l as [|x l IH]; intros n Hn; [cbn in Hn; lia|]. destruct n as [|n]; [reflexivity|]. cbn [firstn nth app]. rewrite IH by (cbn in Hn; lia). reflexivity. Qed.
Lemma skipn_nth_cons : forall (n : nat) (w : list Z), (n < length w)%nat -> skipn n w = nth n w 0 :: skipn (S n) w.
Proof. induction n as [|n IH]; intros [|b r] H; cbn in H |- *; try lia; [reflexivity|]. apply IH. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive pact : Set := PGo (k : Z) | PErr (e : Z) | PEnd.
Definition pact_eqb (a b : pact) : bool :=
  match a, b with PGo x, PGo y => Z.eqb x y | PErr x, PErr y => Z.eqb x y | PEnd, PEnd => true | _, _ => false end.
Lemma pact_eqb_eq : forall a b, pact_eqb a b = true -> a = b.
Proof. intros [x|x|] [y|y|] H; cbn in H; try discriminate H; try reflexivity; apply Z.eqb_eq in H; subst; reflexivity. Qed.
Definition pn_act (k b : Z) : pact :=
  if k =? NS_MINUS then (if is_nzdigit b then PGo NS_INTEGER else if b =? 48 then PGo NS_ZERO else PErr E_INVALID_NUMBER)
  else if k =? NS_ZERO then (if b =? 46 then PGo NS_FRAC1 else if is_exp b then PGo NS_EXP1 else if is_digit b then PErr E_LEADING_ZERO else PEnd)
  else if k =? NS_INTEGER then (if is_digit b then PGo NS_INTEGER else if b =? 46 then PGo NS_FRAC1 else if is_exp b then PGo NS_EXP1 else PEnd)
  else if k =? NS_FRAC1 then (if is_digit b then PGo NS_FRAC2 else PErr E_INVALID_NUMBER)
  else if k =? NS_FRAC2 then (if is_digit b then PGo NS_FRAC2 else if is_exp b then PGo NS_EXP1 else PEnd)
  else if k =? NS_EXP1 then (if (b =? 45) || (b =? 43) then PGo NS_EXP2 else if is_digit b then PGo NS_EXP3 else PErr E_INVALID_NUMBER)
  else if k =? NS_EXP2 then (if is_digit b then PGo NS_EXP3 else PErr E_INVALID_NUMBER)
  else if k =? NS_EXP3 then (if is_digit b then PGo NS_EXP3 else PEnd)
  else PErr E_STUCK.
Lemma pn_act_sound : forall c b r, parse_number c (b :: r) =
  match pn_act (c_nst c) b with PGo k' => parse_number (set_nst (tok1 c b) k') r | PErr e => err c (b :: r) e | PEnd => end_number c (b :: r) end.
Proof.
  intros c b r. cbn [parse_number]. unfold pn_act.
  destruct (c_nst c =? NS_MINUS); [destruct (is_nzdigit b); [reflexivity|]; destruct (b =? 48); reflexivity|].
  destruct (c_nst c =? NS_ZERO); [destruct (b =? 46); [reflexivity|]; destruct (is_exp b); [reflexivity|]; destruct (is_digit b); reflexivity|].
  destruct (c_nst c =? NS_INTEGER); [destruct (is_digit b); [reflexivity|]; destruct (b =? 46); [reflexivity|]; destruct (is_exp b); reflexivity|].
  destruct (c_nst c =? NS_FRAC1); [destruct (is_digit b); reflexivity|].
  destruct (c_nst c =? NS_FRAC2); [destruct (is_digit b); [reflexivity|]; destruct (is_exp b); reflexivity|].
  destruct (c_nst c =? NS_EXP1); [destruct ((b =? 45) || (b =? 43)); [reflexivity|]; destruct (is_digit b); reflexivity|].
  destruct (c_nst c =? NS_EXP2); [destruct (is_digit b); reflexivity|].
  destruct (c_nst c =? NS_EXP3); [destruct (is_digit b); reflexivity|]. reflexivity.
Qed.
(* [comment removed for export] *)
Definition fixnst (k : Z) : Z := if k =? NS_ZERO then NS_INTEGER else k.
Definition fixz (c : ctrl) : ctrl := if c_nst c =? NS_ZERO then set_nst c NS_INTEGER else c.
Lemma pn_nil : forall c, parse_number c [] = ret (fixz c) [].
Proof. intros c. reflexivity. Qed.
Lemma fixz_fields : forall c,
  c_st (fixz c) = c_st c /\ c_more (fixz c) = c_more c /\ c_done (fixz c) = c_done c /\ c_level (fixz c) = c_level c /\ c_stack (fixz c) = c_stack c /\
  c_nst (fixz c) = fixnst (c_nst c) /\ c_dlen (fixz c) = c_dlen c.
Proof. intros c. unfold fixz, fixnst. destruct (c_nst c =? NS_ZERO); unfold set_nst; cbn; repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma pn_go : forall cw w n k k', (n < length w)%nat -> pn_act k (nth n w 0) = PGo k' ->
  parse_number (CI cw (firstn n w) k) (skipn n w) = parse_number (CI cw (firstn (S n) w) k') (skipn (S n) w).
Proof.
  intros cw w n k k' Hn Ha. rewrite (skipn_nth_cons n w Hn), pn_act_sound. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (CI_fields cw (firstn n w) k))))))), Ha.
  rewrite CI_step, <- (firstn_succ w n Hn). reflexivity.
Qed.
Lemma pn_err : forall cw w n k e, (n < length w)%nat -> pn_act k (nth n w 0) = PErr e ->
  parse_number (CI cw (firstn n w) k) (skipn n w) = err (CI cw (firstn n w) k) (skipn n w) e.
Proof.
  intros cw w n k e Hn Ha. rewrite (skipn_nth_cons n w Hn), pn_act_sound. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (CI_fields cw (firstn n w) k))))))), Ha. reflexivity.
Qed.
Lemma pn_end : forall cw w n k, (n < length w)%nat -> pn_act k (nth n w 0) = PEnd ->
  parse_number (CI cw (firstn n w) k) (skipn n w) = end_number (CI cw (firstn n w) k) (skipn n w).
Proof.
  intros cw w n k Hn Ha. rewrite (skipn_nth_cons n w Hn), pn_act_sound. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (CI_fields cw (firstn n w) k))))))), Ha. reflexivity.
Qed.
Lemma pn_all : forall cw w k, parse_number (CI cw (firstn (length w) w) k) (skipn (length w) w) = ret (fixz (CI cw w k)) [].
Proof. intros cw w k. rewrite skipn_all, firstn_all. apply pn_nil. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_value_any : forall c w, q_code (after_value c w) = q_code (after_value c []) /\ q_c (after_value c w) = q_c (after_value c []) /\
  q_evs (after_value c w) = [] /\ q_al (after_value c w) = 0 /\ q_w (after_value c w) = w.
Proof.
  intros c w. unfold after_value. destruct ((top c =? ST_ARRAY) || (top c =? ST_OBJECT)); [cbn; repeat split; reflexivity|].
  destruct (top c =? ST_ROOT); cbn; repeat split; reflexivity.
Qed.
Lemma end_number_any : forall c w, q_code (end_number c w) = q_code (end_number c []) /\ q_c (end_number c w) = q_c (end_number c []) /\
  q_evs (end_number c w) = q_evs (end_number c []) /\ q_al (end_number c w) = q_al (end_number c []) /\ q_w (end_number c w) = w.
Proof.
  intros c w. unfold end_number, PMR.bind. cbn [q_code q_c q_w q_evs q_al negb Z.eqb].
  destruct (after_value_any (set_more c true) w) as (E1 & E2 & E3 & E4 & E5). destruct (after_value_any (set_more c true) []) as (F1 & F2 & F3 & F4 & F5).
  rewrite E1, E2, E3, E4, E5, F3, F4. repeat split; reflexivity.
Qed.
(* [comment removed for export] *)
Lemma end_number_textw : forall c txt w, c_dlen c = Z.of_nat (length txt) ->
  let q := end_number c w in let q2 := end_number (of_text c txt) [] in
  q_code q = q_code q2 /\ q_evs q = q_evs q2 /\ q_al q = q_al q2 /\ q_w q = w /\ PMRF2.ctrl_but_tok (q_c q) (q_c q2) /\
  (q_code q = 0 -> c_st (q_c q) <> ST_STRING /\ c_st (q_c q) <> ST_NUMBER /\ c_more (q_c q) = true).
Proof.
  intros c txt w Hd. destruct (PMRF2.end_number_text c txt Hd) as (A1 & A2 & A3 & _ & _ & A6 & A7). destruct (end_number_any c w) as (E1 & E2 & E3 & E4 & E5).
  cbv zeta. rewrite E1, E2, E3, E4, E5. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [reflexivity|]. split; [exact A6|]. intros H0. exact (A7 ltac:(rewrite <- E1; rewrite E1; exact H0)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition w3n (cw : ctrl) (ww : list Z) (M' : mem) (P : Z) (ps ps' : pstate) (eg eg' : eghost) (code : Z) : Prop :=
  let rr := r_of ww (parse_number cw ww) in
  code = PMW.r_code rr /\
  g_es eg' = PMW.es_run (g_es eg) (PMW.r_evs rr) /\
  (exists pay, 0 <= pay <= PMW.r_allow rr /\ g_len eg' = g_len eg + PMW.ind_run (g_es eg) (PMW.r_evs rr) + pay) /\
  (code = 0 -> rm_match (PMW.r_ctrl rr) M' P ps' /\ PMW.r_used rr = winlen ps - winlen ps' /\ PMW.win_bytes M' ps' (PMW.w_after the_rm rr ww)).
Lemma w3n_fold : forall cw ww x M' P ps ps' eg eg' code,
  w3n cw ww M' P ps ps' eg eg' code ->
  let rr := PMW.rm_step the_rm PMW.FParseNumber cw (PMW.inp_win ps ww x) in
  code = PMW.r_code rr /\ g_es eg' = PMW.es_run (g_es eg) (PMW.r_evs rr) /\
  (exists pay, 0 <= pay <= PMW.r_allow rr /\ g_len eg' = g_len eg + PMW.ind_run (g_es eg) (PMW.r_evs rr) + pay) /\
  (code = 0 -> PMW.rm_match the_rm (PMW.r_ctrl rr) M' P ps' /\ PMW.r_used rr = winlen ps - winlen ps' /\ PMW.win_bytes M' ps' (PMW.w_after the_rm rr ww)).
Proof. intros. exact H. Qed.
(* [comment removed for export] *)
Lemma w3_ret : forall cw c1 ww (M M' : mem) P ps ps' eg e,
  rm_match cw M P ps -> parse_number cw ww = ret c1 [] ->
  c_st c1 = c_st cw -> c_more c1 = c_more cw -> c_done c1 = c_done cw -> c_level c1 = c_level cw -> c_stack c1 = c_stack cw ->
  ps_st ps' = ps_st ps -> ps_more ps' = ps_more ps -> ps_done ps' = ps_done ps -> ps_level ps' = ps_level ps -> ps_stack ps' = ps_stack ps ->
  ps_st ps = ST_NUMBER -> c_nst c1 = ps_nst ps' -> c_dlen c1 = Z.of_nat (length (ps_buf ps')) ->
  winlen ps = Z.of_nat (length ww) -> ps_win ps' = Some (e, e) ->
  w3n cw ww M' P ps ps' eg eg 0.
Proof.
  intros cw c1 ww M M' P ps ps' eg e ((R1 & R2 & R3 & R4 & R5) & _ & _) Hpn C1 C2 C3 C4 C5 Q1 Q2 Q3 Q4 Q5 HstN Hn Hd HW Hw'. unfold w3n. rewrite Hpn.
  unfold PMW.w_after. cbn [r_of ret PMW.r_code PMW.r_evs PMW.r_ctrl PMW.r_used PMW.r_allow q_c q_w q_evs q_code q_al length Z.of_nat PMW.es_run PMW.ind_run].
  rewrite Z.sub_0_r, Nat2Z.id, skipn_all.
  split; [reflexivity|]. split; [reflexivity|]. split; [exists 0; split; [lia | lia]|]. intros _.
  split; [|split; [unfold winlen at 2; rewrite Hw'; lia | unfold PMW.win_bytes; rewrite Hw'; split; [intros i Hi; cbn in Hi; lia|]; split; [cbn; lia | constructor]]].
  split; [split; [congruence|]; split; [congruence|]; split; [congruence|]; split; congruence|].
  split; [intros X; exfalso; rewrite Q1, HstN in X; discriminate X|]. intros _. split; [exact Hn | exact Hd].
Qed.
(* [comment removed for export] *)
Lemma w3_err : forall cw c1 w1 ww (M' : mem) P ps ps' eg code,
  parse_number cw ww = err c1 w1 code -> code <> 0 -> w3n cw ww M' P ps ps' eg eg code.
Proof.
  intros cw c1 w1 ww M' P ps ps' eg code Hpn Hc. unfold w3n. rewrite Hpn.
  cbn [r_of err PMW.r_code PMW.r_evs PMW.r_ctrl PMW.r_used PMW.r_allow q_c q_w q_evs q_code q_al PMW.es_run PMW.ind_run].
  split; [reflexivity|]. split; [reflexivity|]. split; [exists 0; lia|]. intros H0. exfalso. exact (Hc H0).
Qed.
(* [comment removed for export] *)
Lemma w3_end : forall cw ww (n : nat) k (M' : mem) P ps ps' eg eg' code p e,
  (n < length ww)%nat -> parse_number cw ww = end_number (CI cw (firstn n ww) k) (skipn n ww) ->
  let q := end_number (CI cw (firstn n ww) k) (skipn n ww) in
  code = q_code q -> g_es eg' = PMW.es_run (g_es eg) (q_evs q) ->
  (exists pay, 0 <= pay <= q_al q /\ g_len eg' = g_len eg + PMW.ind_run (g_es eg) (q_evs q) + pay) ->
  (code = 0 -> rm_core (q_c q) ps' /\ ps_st ps' <> ST_STRING /\ ps_st ps' <> ST_NUMBER) ->
  ps_win ps = Some (p, e) -> Z.of_nat (length ww) = e - p -> ps_win ps' = Some (p + Z.of_nat n, e) ->
  (code = 0 -> PMW.win_bytes M' ps' (skipn n ww)) ->
  w3n cw ww M' P ps ps' eg eg' code.
Proof.
  intros cw ww n k M' P ps ps' eg eg' code p e Hn Hpn q Hc Hes Hpay Hcore Hw HL Hw' HWB. unfold w3n. rewrite Hpn. fold q.
  destruct (end_number_any (CI cw (firstn n ww) k) (skipn n ww)) as (_ & _ & _ & _ & Qw). fold q in Qw.
  unfold PMW.w_after. cbn [r_of PMW.r_code PMW.r_evs PMW.r_ctrl PMW.r_used PMW.r_allow]. rewrite Qw, length_skipn.
  replace (Z.of_nat (length ww) - Z.of_nat (length ww - n)) with (Z.of_nat n) by lia. rewrite Nat2Z.id.
  split; [exact Hc|]. split; [exact Hes|]. split; [exact Hpay|]. intros H0. destruct (Hcore H0) as (HC & NS & NN).
  split; [split; [exact HC|]; split; intros X; exfalso; [exact (NS X) | exact (NN X)]|].
  split; [unfold winlen; rewrite Hw, Hw'; lia | exact (HWB H0)].
Qed.
End PNKW.
