(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec AxSymExec3 AxSymExec3B. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AxSymExec3C. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanPlanCore. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanPlanWhile. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Module APL.
Import AX2. Import AX2B. Import APC. Import AP.

Notation reL := with_ledger (only parsing).
Section WithNx0.
Variable segs : list Segment.
Variable IT : itab.
Variable nx0 : nat.
Variable A : atable.
Definition lmap (L : ledger) (r : option acs) : option acs := match r with Some cs => Some (with_ledger L cs) | None => None end.

(* [comment removed for export] *)
Lemma a_ss_reL : forall L cs, a_ss (with_ledger L cs) = a_ss cs.            Proof. reflexivity. Qed.
Lemma kn_reL : forall L cs, kn (with_ledger L cs) = kn cs.                  Proof. reflexivity. Qed.
Lemma pc_reL : forall L cs, pc (with_ledger L cs) = pc cs.                  Proof. reflexivity. Qed.
Lemma nxt_reL : forall L cs, nxt (with_ledger L cs) = nxt cs.               Proof. reflexivity. Qed.
Lemma reg_reL : forall L cs n, reg (with_ledger L cs) n = reg cs n.         Proof. reflexivity. Qed.
Lemma props_reL : forall L cs, a_props (with_ledger L cs) = a_props cs.     Proof. reflexivity. Qed.
Lemma brk_reL : forall L cs, a_brk (with_ledger L cs) = a_brk cs.           Proof. reflexivity. Qed.
Lemma fd_reL : forall L cs, a_fd (with_ledger L cs) = a_fd cs.              Proof. reflexivity. Qed.
Lemma tidset_reL : forall L cs, a_tidset (with_ledger L cs) = a_tidset cs.  Proof. reflexivity. Qed.
Lemma ledger_of_reL : forall L cs, ledger_of (with_ledger L cs) = L.        Proof. intros L cs. destruct L; reflexivity. Qed.

(* [comment removed for export] *)
Lemma with_ss_reL : forall L cs ss, with_ss (with_ledger L cs) ss = with_ledger L (with_ss cs ss).   Proof. reflexivity. Qed.
Lemma set_kn_reL : forall L cs k, set_kn (with_ledger L cs) k = with_ledger L (set_kn cs k).       Proof. reflexivity. Qed.
Lemma add_kn_reL : forall L cs k, add_kn (with_ledger L cs) k = with_ledger L (add_kn cs k).       Proof. reflexivity. Qed.
Lemma set_props_reL : forall L cs l, set_props (with_ledger L cs) l = with_ledger L (set_props cs l). Proof. reflexivity. Qed.
Lemma set_reg_reL : forall L cs n e, set_reg (with_ledger L cs) n e = with_ledger L (set_reg cs n e). Proof. reflexivity. Qed.
Lemma set_pc_reL : forall L cs p, set_pc (with_ledger L cs) p = with_ledger L (set_pc cs p).     Proof. reflexivity. Qed.
Lemma bump_reL : forall L cs d, bump (with_ledger L cs) d = with_ledger L (bump cs d).           Proof. reflexivity. Qed.
Lemma gpures_reL : forall G L cs cs', gpures G (with_ledger L cs) (with_ledger L cs') = with_ledger L (gpures G cs cs').
Proof. reflexivity. Qed.
Lemma gkeep_reL : forall G W L cs cs', gkeep G W (with_ledger L cs) (with_ledger L cs') = with_ledger L (gkeep G W cs cs').
Proof. reflexivity. Qed.
Lemma gkeepM_reL : forall G W L cs cs', gkeepM G W (with_ledger L cs) (with_ledger L cs') = with_ledger L (gkeepM G W cs cs').
Proof. intros. rewrite !gkeepM_eq. apply gkeep_reL. Qed.
Lemma gkeepE_reL : forall G W L cs cs', gkeepE G W (with_ledger L cs) (with_ledger L cs') = with_ledger L (gkeepE G W cs cs').
Proof. reflexivity. Qed.
Lemma gkeepEM_reL : forall G W L cs cs', gkeepEM G W (with_ledger L cs) (with_ledger L cs') = with_ledger L (gkeepEM G W cs cs').
Proof. intros. rewrite !gkeepEM_eq. apply gkeepE_reL. Qed.


Lemma expr_vars_lt_mono' : forall b b' e, expr_vars_lt b e = true -> (b <= b')%nat -> expr_vars_lt b' e = true.
Proof.
  intros b b' e. induction e; intros H Hle; cbn [expr_vars_lt] in *; try reflexivity;
    try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1 Hle), (IHe2 H2 Hle); reflexivity); try exact (IHe H Hle).
  apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
Qed.
Lemma APS_ledger_mono : forall b b' L, ledger_vars_lt b L = true -> (b <= b')%nat -> ledger_vars_lt b' L = true.
Proof.
  intros b b' L H Hle. unfold ledger_vars_lt, maps_vars_lt, pairs_vars_lt in *.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  assert (M : forall (X : Type) (f g : X -> expr) (l : list X),
            forallb (fun x => expr_vars_lt b (f x) && expr_vars_lt b (g x)) l = true ->
            forallb (fun x => expr_vars_lt b' (f x) && expr_vars_lt b' (g x)) l = true).
  { intros X f g l Hl. apply forallb_forall. intros x Hx. pose proof (proj1 (forallb_forall _ _) Hl x Hx) as Q.
    apply andb_prop in Q as [Q1 Q2]. rewrite (expr_vars_lt_mono' _ _ _ Q1 Hle), (expr_vars_lt_mono' _ _ _ Q2 Hle). reflexivity. }
  rewrite (M _ am_base am_len _ H1), (M _ fst snd _ H2), (M _ fst snd _ H3). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma fresh_ok_reL : forall L cs, fresh_ok nx0 cs = true -> ledger_vars_lt (nxt cs) L = true -> fresh_ok nx0 (with_ledger L cs) = true.
Proof.
  intros L cs H HL. unfold fresh_ok in *. unfold ledger_vars_lt in HL.
  apply andb_prop in H as [H F8]. apply andb_prop in H as [H F7]. apply andb_prop in H as [H F6]. apply andb_prop in H as [H F5].
  apply andb_prop in H as [H F4]. apply andb_prop in H as [H F3]. apply andb_prop in H as [F1 F2].
  apply andb_prop in HL as [HL HL3]. apply andb_prop in HL as [HL1 HL2].
  cbn [a_ss a_maps a_vis a_ghost a_brk a_fd with_ledger]. change (nxt (with_ledger L cs)) with (nxt cs). change (kn (with_ledger L cs)) with (kn cs).
  rewrite F1, F2, HL1, HL2, HL3, F6, F7, F8. reflexivity.
Qed.
Lemma node_bump_reL : forall L cs m, node_bump (with_ledger L cs) m = lmap L (node_bump cs m).
Proof. intros. unfold node_bump. rewrite nxt_reL. destruct (Nat.leb _ _); reflexivity. Qed.
Lemma node_droprange_reL : forall L cs b n, node_droprange (with_ledger L cs) b n = with_ledger L (node_droprange cs b n).
Proof. intros. unfold node_droprange. rewrite kn_reL. destruct (split_lit b); reflexivity. Qed.
Lemma node_havoc_reL : forall L cs rs cs', ledger_vars_lt (nxt cs) L = true ->
  node_havoc nx0 cs rs = Some cs' -> node_havoc nx0 (with_ledger L cs) rs = Some (with_ledger L cs').
Proof.
  intros L cs rs cs' HL H. unfold node_havoc in *. destruct (fresh_ok nx0 cs) eqn:F; [|discriminate H].
  rewrite (fresh_ok_reL L cs F HL). cbn [andb] in *. destruct (forallb _ rs); [|discriminate H]. injection H as <-. reflexivity.
Qed.
Lemma node_intro_reL : forall L cs lo hi cs', ledger_vars_lt (nxt cs) L = true ->
  node_intro nx0 cs lo hi = Some cs' -> node_intro nx0 (with_ledger L cs) lo hi = Some (with_ledger L cs').
Proof.
  intros L cs lo hi cs' HL H. unfold node_intro in *. destruct (fresh_ok nx0 cs) eqn:F; [|discriminate H].
  rewrite (fresh_ok_reL L cs F HL). cbn [andb] in *. destruct (_ && _ && _)%bool; [|discriminate H]. injection H as <-. reflexivity.
Qed.
Lemma node_havocwords_reL : forall L cs bs cs', ledger_vars_lt (nxt cs) L = true ->
  node_havocwords nx0 cs bs = Some cs' -> node_havocwords nx0 (with_ledger L cs) bs = Some (with_ledger L cs').
Proof.
  intros L cs bs cs' HL H. unfold node_havocwords in *. destruct (fresh_ok nx0 cs) eqn:F; [|discriminate H].
  rewrite (fresh_ok_reL L cs F HL). injection H as <-. reflexivity.
Qed.
Lemma node_respell_reL : forall L cs r e, node_respell (with_ledger L cs) r e = lmap L (node_respell cs r e).
Proof. intros. unfold node_respell. rewrite nxt_reL, kn_reL, reg_reL. destruct (_ && _ && _ && _)%bool; reflexivity. Qed.
Lemma node_abstractcell_reL : forall L cs b n, node_abstractcell A (with_ledger L cs) b n = lmap L (node_abstractcell A cs b n).
Proof. intros. unfold node_abstractcell. rewrite kn_reL. destruct (split_lit b). destruct (kunk_covered _ _); reflexivity. Qed.
Lemma node_settid_reL : forall L cs cs', ledger_vars_lt (nxt cs) L = true ->
  node_settid nx0 cs = Some cs' -> node_settid nx0 (with_ledger L cs) = Some (with_ledger L cs').
Proof.
  intros L cs cs' HL H. unfold node_settid in *.
  change (reg_lit (with_ledger L cs) 17) with (reg_lit cs 17). destruct (reg_lit cs 17) as [z|]; [|discriminate H].
  change (a_tidset (with_ledger L cs)) with (a_tidset cs).
  destruct (a_tidset cs); [destruct z as [|p|p]; try discriminate H; do 8 (try destruct p; try discriminate H)|]. cbn [negb andb] in *.
  destruct (fresh_ok nx0 cs) eqn:F.
  - rewrite (fresh_ok_reL L cs F HL).
    destruct z as [|p|p]; try discriminate H; do 8 (try destruct p; try discriminate H). injection H as <-. destruct L; reflexivity.
  - exfalso. destruct z as [|p|p]; try discriminate H; do 8 (try destruct p; try discriminate H).
Qed.

(* [comment removed for export] *)
Definition memv (v : nat) (l : list nat) : bool := existsb (Nat.eqb v) l.
Lemma memv_expr_vars : forall v e acc, memv v (expr_vars e acc) = (memv v (expr_vars e []) || memv v acc)%bool.
Proof.
  intros v e. unfold memv. induction e; intros acc; cbn [expr_vars]; try reflexivity.
  - destruct (existsb (Nat.eqb n) acc) eqn:E; cbn [existsb].
    + rewrite Bool.orb_false_r. destruct (Nat.eqb_spec v n) as [->|NE]; [|reflexivity]. cbn [orb]. rewrite E. reflexivity.
    + rewrite Bool.orb_false_r. reflexivity.
  - rewrite IHe1, IHe2, (IHe1 (expr_vars e2 [])). rewrite Bool.orb_assoc. reflexivity.
  - rewrite IHe1, IHe2, (IHe1 (expr_vars e2 [])). rewrite Bool.orb_assoc. reflexivity.
  - rewrite IHe1, IHe2, (IHe1 (expr_vars e2 [])). rewrite Bool.orb_assoc. reflexivity.
  - rewrite IHe1, IHe2, (IHe1 (expr_vars e2 [])). rewrite Bool.orb_assoc. reflexivity.
  - apply IHe.
Qed.
Lemma memv_vars_lt : forall b v e, expr_vars_lt b e = true -> (b <= v)%nat -> memv v (expr_vars e []) = false.
Proof.
  intros b v e. induction e; intros H Hv; cbn [expr_vars expr_vars_lt existsb memv] in *; try reflexivity.
  - cbn. apply Nat.ltb_lt in H. destruct (Nat.eqb_spec v n); [lia | reflexivity].
  - apply andb_prop in H as [H1 H2]. fold (memv v (expr_vars e1 (expr_vars e2 []))). rewrite memv_expr_vars, (IHe1 H1 Hv), (IHe2 H2 Hv). reflexivity.
  - apply andb_prop in H as [H1 H2]. fold (memv v (expr_vars e1 (expr_vars e2 []))). rewrite memv_expr_vars, (IHe1 H1 Hv), (IHe2 H2 Hv). reflexivity.
  - apply andb_prop in H as [H1 H2]. fold (memv v (expr_vars e1 (expr_vars e2 []))). rewrite memv_expr_vars, (IHe1 H1 Hv), (IHe2 H2 Hv). reflexivity.
  - apply andb_prop in H as [H1 H2]. fold (memv v (expr_vars e1 (expr_vars e2 []))). rewrite memv_expr_vars, (IHe1 H1 Hv), (IHe2 H2 Hv). reflexivity.
  - exact (IHe H Hv).
Qed.
Lemma memv_fold_maps : forall b v ms acc, maps_vars_lt b ms = true -> (b <= v)%nat ->
  memv v (fold_right (fun m acc => expr_vars (am_base m) (expr_vars (am_len m) acc)) acc ms) = memv v acc.
Proof.
  intros b v ms acc H Hv. induction ms as [|m ms IH]; [reflexivity|]. cbn [fold_right].
  unfold maps_vars_lt in H. cbn [forallb] in H. apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [Hb Hl].
  rewrite memv_expr_vars, (memv_vars_lt _ _ _ Hb Hv), memv_expr_vars, (memv_vars_lt _ _ _ Hl Hv). cbn [orb]. apply IH. exact H2.
Qed.
Lemma memv_fold_pairs : forall b v ps acc, pairs_vars_lt b ps = true -> (b <= v)%nat ->
  memv v (fold_right (fun p acc => expr_vars (fst p) (expr_vars (snd p) acc)) acc ps) = memv v acc.
Proof.
  intros b v ps acc H Hv. induction ps as [|p ps IH]; [reflexivity|]. cbn [fold_right].
  unfold pairs_vars_lt in H. cbn [forallb] in H. apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [Hb Hl].
  rewrite memv_expr_vars, (memv_vars_lt _ _ _ Hb Hv), memv_expr_vars, (memv_vars_lt _ _ _ Hl Hv). cbn [orb]. apply IH. exact H2.
Qed.
(* [comment removed for export] *)
Lemma memv_expr_congr : forall v e a1 a2, memv v a1 = memv v a2 -> memv v (expr_vars e a1) = memv v (expr_vars e a2).
Proof. intros v e a1 a2 H. rewrite (memv_expr_vars v e a1), (memv_expr_vars v e a2), H. reflexivity. Qed.
Lemma memv_fold_congr : forall v (l : list expr) a1 a2, memv v a1 = memv v a2 ->
  memv v (fold_right expr_vars a1 l) = memv v (fold_right expr_vars a2 l).
Proof. intros v l a1 a2 H. induction l as [|e l IH]; [exact H|]. cbn [fold_right]. apply memv_expr_congr. exact IH. Qed.
Lemma live_vars_reL : forall L cs v, ledger_vars_lt nx0 L = true -> ledger_vars_lt nx0 (ledger_of cs) = true -> (nx0 <= v)%nat ->
  memv v (live_vars (with_ledger L cs)) = memv v (live_vars cs).
Proof.
  intros L cs v HL HC Hv. unfold ledger_vars_lt in HL, HC.
  apply andb_prop in HL as [HL HL3]. apply andb_prop in HL as [HL1 HL2].
  apply andb_prop in HC as [HC HC3]. apply andb_prop in HC as [HC1 HC2]. cbn [lg_maps lg_vis lg_ghost ledger_of] in HC1, HC2, HC3.
  unfold live_vars. cbn [a_ss a_maps a_vis a_ghost a_brk a_fd a_props with_ledger].
  apply memv_expr_congr.
  set (P := fun (g : gatom) (acc : list nat) => fold_right expr_vars acc (g_args g)).
  assert (HP : forall l a1 a2, memv v a1 = memv v a2 -> memv v (fold_right P a1 l) = memv v (fold_right P a2 l)).
  { intros l a1 a2 Ha. induction l as [|g l IH]; [exact Ha|]. cbn [fold_right]. unfold P at 1. unfold P at 3.
    apply memv_fold_congr. exact IH. }
  apply HP.
  assert (HF : forall a1 a2, memv v a1 = memv v a2 ->
            memv v (match a_fd cs with FdFile _ l o => expr_vars l (expr_vars o a1) | _ => a1 end)
            = memv v (match a_fd cs with FdFile _ l o => expr_vars l (expr_vars o a2) | _ => a2 end)).
  { intros a1 a2 Ha. destruct (a_fd cs); [exact Ha| |exact Ha]. apply memv_expr_congr. apply memv_expr_congr. exact Ha. }
  apply HF.
  rewrite (memv_fold_pairs _ _ _ _ HL3 Hv), (memv_fold_pairs _ _ _ _ HL2 Hv), (memv_fold_maps _ _ _ _ HL1 Hv).
  rewrite (memv_fold_pairs _ _ _ _ HC3 Hv), (memv_fold_pairs _ _ _ _ HC2 Hv), (memv_fold_maps _ _ _ _ HC1 Hv). reflexivity.
Qed.
Lemma all_live_reL : forall L cs e, ledger_vars_lt nx0 L = true -> ledger_vars_lt nx0 (ledger_of cs) = true ->
  all_live nx0 (live_vars (with_ledger L cs)) e = all_live nx0 (live_vars cs) e.
Proof.
  intros L cs e HL HC. unfold all_live. induction (expr_vars e []) as [|v vs IH]; [reflexivity|]. cbn [forallb].
  rewrite IH. f_equal. destruct (Nat.ltb_spec v nx0) as [Hlt|Hge]; [reflexivity|]. cbn [orb].
  exact (live_vars_reL L cs v HL HC Hge).
Qed.
Lemma cs_gc_reL : forall L cs, ledger_vars_lt nx0 L = true -> ledger_vars_lt nx0 (ledger_of cs) = true ->
  cs_gc nx0 (with_ledger L cs) = with_ledger L (cs_gc nx0 cs).
Proof.
  intros L cs HL HC. rewrite !cs_gc_eq. unfold cs_gc_ref. change (reg (with_ledger L cs) 2) with (reg cs 2).
  destruct (split_lit (reg cs 2)) as [spb spk]. rewrite kn_reL, set_kn_reL. f_equal. f_equal.
  apply filter_ext. intros K.
  destruct K as [[b kk] w v|[b kk] l|[b kk] l bk|lo hi|e m|e lo hi|[b kk] n|a1 n1 a2 n2|[b kk] l c|[b kk] l]; cbn [kn_gc_entry];
    rewrite ?(all_live_reL L cs _ HL HC); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_havocbig_reL : forall L cs K cs', ledger_vars_lt (nxt cs) L = true ->
  node_havocbig nx0 cs K = Some cs' -> node_havocbig nx0 (with_ledger L cs) K = Some (with_ledger L cs').
Proof.
  intros L cs K cs' HL H. unfold node_havocbig in *.
  set (rs := List.filter (fun r : nat => bigb K (reg cs r)) (seq 1 31)) in *.
  set (rs' := List.filter (fun r : nat => bigb K (reg (with_ledger L cs) r)) (seq 1 31)) in *.
  assert (Ers : rs' = rs) by reflexivity. rewrite Ers. clear rs' Ers.
  destruct (node_havoc nx0 cs rs) as [cs1|] eqn:Hh; [|discriminate H].
  rewrite (node_havoc_reL L cs rs cs1 HL Hh).
  destruct (fresh_ok nx0 cs1) eqn:F; [|discriminate H].
  assert (Hn : (nxt cs <= nxt cs1)%nat).
  { unfold node_havoc in Hh. destruct (fresh_ok nx0 cs && _)%bool; [|discriminate Hh]. injection Hh as <-.
    unfold nxt. cbn [a_ss with_ss mk_ss s_next]. lia. }
  rewrite (fresh_ok_reL L cs1 F (APS_ledger_mono _ _ _ HL Hn)). rewrite kn_reL, nxt_reL, pc_reL, a_ss_reL.
  destruct (kn_bigsubst K (kn cs1) (nxt cs1)) as [k' c]. injection H as <-. reflexivity.
Qed.

Lemma run_block_wb_ws_reL : forall wb K fuel stops L cs cs' W, ledger_vars_lt (nxt cs) L = true ->
  run_block_wb_ws segs IT nx0 wb K fuel stops cs = Some (cs', W) ->
  run_block_wb_ws segs IT nx0 wb K fuel stops (with_ledger L cs) = Some (with_ledger L cs', W).
Proof.
  intros wb K fuel stops L cs cs' W HL H. unfold run_block_wb_ws in *.
  destruct (fresh_ok nx0 cs) eqn:F; [|discriminate H]. rewrite (fresh_ok_reL L cs F HL). rewrite a_ss_reL.
  cbv zeta in *. destruct (match wb with Some W0 => _ | None => true end); [|discriminate H].
  destruct (AX2C.carryK3 _ _ _ _) as [[kn' scs] hs]. destruct scs; [|discriminate H]. injection H as <- <-. reflexivity.
Qed.
Lemma fresh_ok_nx0 : forall cs, fresh_ok nx0 cs = true -> (nx0 <= nxt cs)%nat.
Proof.
  intros cs H. unfold fresh_ok in H. repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Nat.leb_le in X. exact X.
Qed.
Lemma run_block_gc_wb_ws_reL : forall wb K fuel stops L cs cs' W,
  ledger_vars_lt nx0 L = true -> ledger_vars_lt nx0 (ledger_of cs) = true ->
  run_block_gc_wb_ws segs IT nx0 wb K fuel stops cs = Some (cs', W) ->
  run_block_gc_wb_ws segs IT nx0 wb K fuel stops (with_ledger L cs) = Some (with_ledger L cs', W).
Proof.
  intros wb K fuel stops L cs cs' W HL HC H.
  assert (Hn : (nx0 <= nxt cs)%nat).
  { unfold run_block_gc_wb_ws, run_block_wb_ws in H. destruct (fresh_ok nx0 cs) eqn:F; [|discriminate H]. exact (fresh_ok_nx0 cs F). }
  unfold run_block_gc_wb_ws in *.
  destruct (run_block_wb_ws segs IT nx0 wb K fuel stops cs) as [[cs1 W1]|] eqn:Hr; [|discriminate H]. injection H as <- <-.
  rewrite (run_block_wb_ws_reL wb K fuel stops L cs cs1 W1 (APS_ledger_mono _ _ _ HL Hn) Hr).
  assert (E1 : ledger_of cs1 = ledger_of cs).
  { unfold run_block_wb_ws in Hr. destruct (fresh_ok nx0 cs); [|discriminate Hr]. cbv zeta in Hr.
    destruct (match wb with Some W0 => _ | None => true end); [|discriminate Hr].
    destruct (AX2C.carryK3 _ _ _ _) as [[kn' scs] hs]. destruct scs; [|discriminate Hr]. injection Hr as <- <-. reflexivity. }
  rewrite (cs_gc_reL L cs1 HL ltac:(rewrite E1; exact HC)). reflexivity.
Qed.
Lemma node_shdisj_reL : forall L cs b1 n1 b2 n2, node_shdisj A (with_ledger L cs) b1 n1 b2 n2 = lmap L (node_shdisj A cs b1 n1 b2 n2).
Proof.
  intros. rewrite !node_shdisj_eq. unfold node_shdisj_ref. rewrite kn_reL.
  destruct (split_lit b1), (split_lit b2). destruct (shadow_of A (kn cs) b1 n1) as [[sb1 sk1] sn1]. destruct (shadow_of A (kn cs) b2 n2) as [[sb2 sk2] sn2].
  match goal with |- (if ?c then _ else _) = _ => destruct c; reflexivity end.
Qed.

(* [comment removed for export] *)
Definition lsubst (sg : sbind) (L : ledger) : ledger :=
  LG (map (msubsts sg) (lg_maps L)) (lg_totsz L) (lg_ylo L) (lg_eager L)
     (map (psubsts sg) (lg_vis L)) (map (psubsts sg) (lg_ghost L)) (lg_abytes L).
Lemma insts_reL : forall sg L x, insts sg (with_ledger L x) = with_ledger (lsubst sg L) (insts sg x).
Proof. intros sg L x. destruct L; reflexivity. Qed.
Definition is_evar (e : expr) : bool := match e with EVar _ => true | _ => false end.
(* [comment removed for export] *)
Definition ledger_evars (L : ledger) : bool :=
  (forallb (fun m => is_evar (am_base m) && is_evar (am_len m)) (lg_maps L)
   && forallb (fun p => is_evar (fst p) && is_evar (snd p)) (lg_vis L)
   && forallb (fun p => is_evar (fst p) && is_evar (snd p)) (lg_ghost L))%bool.
Lemma sg_get_none_lt : forall sg lo v, sg_dom_ge lo sg = true -> (v < lo)%nat -> sg_get sg v = None.
Proof.
  intros sg lo v H Hv. induction sg as [|[w e] sg IH]; [reflexivity|]. cbn [sg_get].
  unfold sg_dom_ge in H. cbn [forallb fst] in H. apply andb_prop in H as [H1 H2]. apply Nat.leb_le in H1.
  destruct (Nat.eqb_spec w v); [lia|]. apply IH. exact H2.
Qed.
Lemma esubsts_evar_lt : forall sg lo e, sg_dom_ge lo sg = true -> is_evar e = true -> expr_vars_lt lo e = true -> esubsts sg e = e.
Proof.
  intros sg lo e H He Hl. destruct e; try discriminate He. cbn [esubsts]. cbn in Hl. apply Nat.ltb_lt in Hl.
  rewrite (sg_get_none_lt sg lo n H Hl). reflexivity.
Qed.
Lemma lsubst_id : forall sg lo L, sg_dom_ge lo sg = true -> ledger_evars L = true -> ledger_vars_lt lo L = true -> lsubst sg L = L.
Proof.
  intros sg lo L H He Hl. destruct L as [ms t y ea vs gs ab]. unfold lsubst. cbn [lg_maps lg_vis lg_ghost lg_totsz lg_ylo lg_eager lg_abytes].
  unfold ledger_evars, ledger_vars_lt, maps_vars_lt, pairs_vars_lt in He, Hl. cbn [lg_maps lg_vis lg_ghost] in He, Hl.
  apply andb_prop in He as [He He3]. apply andb_prop in He as [He1 He2].
  apply andb_prop in Hl as [Hl Hl3]. apply andb_prop in Hl as [Hl1 Hl2].
  assert (MP : forall ps, forallb (fun p : expr * expr => is_evar (fst p) && is_evar (snd p)) ps = true ->
               forallb (fun p : expr * expr => expr_vars_lt lo (fst p) && expr_vars_lt lo (snd p)) ps = true ->
               map (psubsts sg) ps = ps).
  { intros ps E1 E2. induction ps as [|[a b] ps IH]; [reflexivity|]. cbn [forallb fst snd map] in *.
    apply andb_prop in E1 as [E1 E1r]. apply andb_prop in E1 as [Ea Eb]. apply andb_prop in E2 as [E2 E2r]. apply andb_prop in E2 as [La Lb].
    unfold psubsts at 1. cbn [fst snd]. rewrite (esubsts_evar_lt sg lo a H Ea La), (esubsts_evar_lt sg lo b H Eb Lb). f_equal. exact (IH E1r E2r). }
  f_equal; [|exact (MP vs He2 Hl2)|exact (MP gs He3 Hl3)].
  clear MP. induction ms as [|[b l k] ms IH]; [reflexivity|]. cbn [forallb am_base am_len map] in *.
  apply andb_prop in He1 as [E1 E1r]. apply andb_prop in E1 as [Ea Eb]. apply andb_prop in Hl1 as [L1 L1r]. apply andb_prop in L1 as [La Lb].
  unfold msubsts at 1. cbn [am_base am_len am_kind]. rewrite (esubsts_evar_lt sg lo b H Ea La), (esubsts_evar_lt sg lo l H Eb Lb). f_equal. exact (IH E1r L1r).
Qed.
Lemma sg_dom_in_ge : forall lo hi sg, sg_dom_in lo hi sg = true -> sg_dom_ge lo sg = true.
Proof.
  intros lo hi sg H. unfold sg_dom_in, sg_dom_ge in *. apply forallb_forall. intros p Hp.
  pose proof (proj1 (forallb_forall _ _) H p Hp) as Q. apply andb_prop in Q as [Q _]. exact Q.
Qed.
Lemma list_eqb_refl_amap : forall l, list_eqb amap_eqb l l = true.
Proof. induction l as [|m l IH]; [reflexivity|]. cbn. unfold amap_eqb at 1. rewrite !expr_eqb_refl. destruct (am_kind m); cbn; exact IH. Qed.
Lemma list_eqb_refl_pair : forall l, list_eqb pair_eqb l l = true.
Proof. induction l as [|p l IH]; [reflexivity|]. cbn. unfold pair_eqb at 1. rewrite !expr_eqb_refl. cbn. exact IH. Qed.
Lemma entails_t_reL : forall L cs T, entails_t A cs T = true -> entails_t A (with_ledger L cs) (with_ledger L T) = true.
Proof.
  intros L cs T H. unfold entails_t in *.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  cbn [a_ss a_maps a_vis a_ghost a_brk a_fd a_tidset a_totsz a_ylo a_eager a_abytes with_ledger].
  change (kn (with_ledger L cs)) with (kn cs). change (kn (with_ledger L T)) with (kn T).
  change (pc (with_ledger L cs)) with (pc cs). change (pc (with_ledger L T)) with (pc T).
  rewrite H, X13, X12, X11, X10, X9, list_eqb_refl_amap, !list_eqb_refl_pair, X5, X4, X3, !Z.leb_refl. reflexivity.
Qed.
Lemma entails_s_reL : forall lo hi hints L cs T sg,
  ledger_evars L = true -> ledger_vars_lt lo L = true ->
  entails_s A lo hi hints cs T = Some sg -> entails_s A lo hi hints (with_ledger L cs) (with_ledger L T) = Some sg.
Proof.
  intros lo hi hints L cs T sg He Hl H. unfold entails_s in *.
  change (infer_sg lo hi hints (with_ledger L cs) (with_ledger L T)) with (infer_sg lo hi hints cs T).
  destruct (sg_dom_in lo hi (infer_sg lo hi hints cs T)) eqn:Hd; [|discriminate H]. cbn [andb] in *.
  destruct (entails_t A cs (insts _ T)) eqn:Ht; [|discriminate H]. injection H as <-.
  rewrite insts_reL, (lsubst_id _ lo L (sg_dom_in_ge _ _ _ Hd) He Hl), (entails_t_reL L _ _ Ht). reflexivity.
Qed.
Lemma entails_sM_reL : forall lo hi hints L cs T sg,
  ledger_evars L = true -> ledger_vars_lt lo L = true ->
  entails_sM A lo hi hints cs T = Some sg -> entails_sM A lo hi hints (with_ledger L cs) (with_ledger L T) = Some sg.
Proof. intros. rewrite entails_sM_eq in *. eapply entails_s_reL; eassumption. Qed.
Lemma entails_reL : forall L cs ch, entails cs ch = true -> entails (with_ledger L cs) (with_ledger L ch) = true.
Proof.
  intros L cs ch H. unfold entails in *.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  cbn [a_ss a_maps a_vis a_ghost a_brk a_fd a_tidset a_totsz a_ylo a_eager a_abytes with_ledger].
  change (kn (with_ledger L cs)) with (kn cs). change (kn (with_ledger L ch)) with (kn ch).
  change (pc (with_ledger L cs)) with (pc cs). change (pc (with_ledger L ch)) with (pc ch).
  rewrite H, X11, X10, X9, list_eqb_refl_amap, !list_eqb_refl_pair, X5, X4, X3, !Z.leb_refl. reflexivity.
Qed.
Lemma entails_h_reL : forall lo hi L cs ch, ledger_vars_lt lo L = true ->
  entails_h A lo hi cs ch = true -> entails_h A lo hi (with_ledger L cs) (with_ledger L ch) = true.
Proof.
  intros lo hi L cs ch HL H. unfold entails_h in *. unfold ledger_vars_lt in HL.
  apply andb_prop in HL as [HL HL3]. apply andb_prop in HL as [HL1 HL2].
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  cbn [a_ss a_maps a_vis a_ghost a_brk a_fd a_tidset a_totsz a_ylo a_eager a_abytes with_ledger].
  change (kn (with_ledger L cs)) with (kn cs). change (kn (with_ledger L ch)) with (kn ch).
  change (pc (with_ledger L cs)) with (pc cs). change (pc (with_ledger L ch)) with (pc ch).
  rewrite H, X18, X17, X16, X15, X14, HL1, HL2, HL3, X10, X9, list_eqb_refl_amap, !list_eqb_refl_pair, X5, X4, X3, !Z.leb_refl. reflexivity.
Qed.
Lemma entails_hM_reL : forall lo hi L cs ch, ledger_vars_lt lo L = true ->
  entails_hM A lo hi cs ch = true -> entails_hM A lo hi (with_ledger L cs) (with_ledger L ch) = true.
Proof. intros. rewrite entails_hM_eq in *. eapply entails_h_reL; eassumption. Qed.

(* [comment removed for export] *)
Lemma ret_lit_reL : forall L cs, ret_lit (with_ledger L cs) = ret_lit cs.          Proof. reflexivity. Qed.
Lemma reg_lit_reL : forall L cs n, reg_lit (with_ledger L cs) n = reg_lit cs n.    Proof. reflexivity. Qed.
Lemma after_call_reL : forall L cs ret rv k' cs', ledger_vars_lt (nxt cs) L = true ->
  after_call nx0 cs ret rv k' = Some cs' -> after_call nx0 (with_ledger L cs) ret rv k' = Some (with_ledger L cs').
Proof.
  intros L cs ret rv k' cs' HL H. unfold after_call in *. rewrite a_ss_reL.
  destruct (fresh_ok nx0 cs) eqn:F; [|discriminate H]. rewrite (fresh_ok_reL L cs F HL). cbn [andb] in *.
  destruct (_ && _)%bool; [|discriminate H]. injection H as <-. reflexivity.
Qed.
Lemma after_call2_reL : forall L cs ret rv k' extra cs', ledger_vars_lt (nxt cs) L = true ->
  after_call2 nx0 cs ret rv k' extra = Some cs' -> after_call2 nx0 (with_ledger L cs) ret rv k' extra = Some (with_ledger L cs').
Proof.
  intros L cs ret rv k' extra cs' HL H. unfold after_call2 in *. rewrite a_ss_reL.
  destruct (fresh_ok nx0 cs) eqn:F; [|discriminate H]. rewrite (fresh_ok_reL L cs F HL). cbn [andb] in *.
  destruct (_ && _)%bool; [|discriminate H]. injection H as <-. reflexivity.
Qed.
Lemma some_inj : forall (T : Type) (a b : T), Some a = Some b -> a = b.
Proof. intros T a b H. injection H as E. exact E. Qed.
(* [comment removed for export] *)
Ltac reL_norm := rewrite ?ret_lit_reL, ?reg_lit_reL, ?reg_reL, ?pc_reL, ?kn_reL, ?nxt_reL, ?a_ss_reL, ?brk_reL, ?fd_reL, ?tidset_reL, ?props_reL.
Ltac reL_walk H :=
  reL_norm;
  lazymatch type of H with
  | Some _ = Some _ => apply some_inj in H; subst; try reflexivity
  | None = Some _ => discriminate H
  | after_call _ _ _ _ _ = Some _ => eapply after_call_reL; [|exact H]
  | after_call2 _ _ _ _ _ _ = Some _ => eapply after_call2_reL; [|exact H]
  | (if ?b then _ else _) = Some _ => destruct b; try discriminate H; reL_walk H
  | (match ?x with _ => _ end) = Some _ => destruct x; try discriminate H; reL_walk H
  end.
(* [comment removed for export] *)
Ltac reL_walkx fx H :=
  reL_norm; try fx;
  lazymatch type of H with
  | Some _ = Some _ => apply some_inj in H; subst; try reflexivity
  | None = Some _ => discriminate H
  | after_call _ _ _ _ _ = Some _ => eapply after_call_reL; [|exact H]
  | after_call2 _ _ _ _ _ _ = Some _ => eapply after_call2_reL; [|exact H]
  | (if ?b then _ else _) = Some _ =>
      let Hb := fresh "Hb" in
      destruct b eqn:Hb; [rewrite ?Bool.andb_false_r, ?Bool.andb_false_l in Hb; try discriminate Hb|];
      try discriminate H; try clear Hb; reL_walkx fx H
  | (match ?x with _ => _ end) = Some _ => destruct x; try discriminate H; reL_walkx fx H
  end.
(* [comment removed for export] *)
Ltac reL_fresh_walk L cs HL H :=
  let F := fresh "F" in
  cbv zeta in H; cbv zeta;
  destruct (fresh_ok nx0 cs) eqn:F;
  [reL_walkx ltac:(rewrite (fresh_ok_reL L cs F HL)) H
  |reL_walkx ltac:(idtac) H].
Lemma summary_fill_reL : forall L cs entry cmax cs', ledger_vars_lt (nxt cs) L = true ->
  summary_fill A nx0 cs entry cmax = Some cs' -> summary_fill A nx0 (with_ledger L cs) entry cmax = Some (with_ledger L cs').
Proof.
  intros L cs entry cmax cs' HL H. rewrite summary_fill_eq in *. unfold summary_fill_ref in *. cbv zeta in H. cbv zeta.
  reL_walk H; try exact HL.
Qed.

Lemma summary_copy_reL : forall L cs entry cs', ledger_vars_lt (nxt cs) L = true ->
  summary_copy segs A nx0 cs entry = Some cs' -> summary_copy segs A nx0 (with_ledger L cs) entry = Some (with_ledger L cs').
Proof.
  intros L cs entry cs' HL H. rewrite summary_copy_eq in *. unfold summary_copy_ref in *. cbv zeta in H. cbv zeta.
  reL_walk H; try exact HL.
Qed.
Lemma summary_miz_reL : forall L cs cs', ledger_vars_lt (nxt cs) L = true ->
  summary_miz A nx0 cs = Some cs' -> summary_miz A nx0 (with_ledger L cs) = Some (with_ledger L cs').
Proof.
  intros L cs cs' HL H. unfold summary_miz in *. cbv zeta in H. cbv zeta. reL_walk H; try exact HL.
Qed.
Lemma summary_istrncpy_reL : forall L cs cs', ledger_vars_lt (nxt cs) L = true ->
  summary_istrncpy A nx0 cs = Some cs' -> summary_istrncpy A nx0 (with_ledger L cs) = Some (with_ledger L cs').
Proof.
  intros L cs cs' HL H. unfold summary_istrncpy in *. cbv zeta in H. cbv zeta. reL_walk H; try exact HL.
Qed.
Lemma summary_popfree_reL : forall L cs args cs', ledger_vars_lt (nxt cs) L = true ->
  summary_popfree A nx0 cs args = Some cs' -> summary_popfree A nx0 (with_ledger L cs) args = Some (with_ledger L cs').
Proof.
  intros L cs args cs' HL H. unfold summary_popfree in *. reL_fresh_walk L cs HL H; try exact HL.
Qed.
Lemma summary_sniff_reL : forall L cs cs', ledger_vars_lt (nxt cs) L = true ->
  summary_sniff segs A nx0 cs = Some cs' -> summary_sniff segs A nx0 (with_ledger L cs) = Some (with_ledger L cs').
Proof.
  intros L cs cs' HL H. unfold summary_sniff in *. cbv zeta in H. cbv zeta. reL_walk H; try exact HL.
Qed.
Lemma node_envscan_reL : forall L cs cs', ledger_vars_lt (nxt cs) L = true ->
  node_envscan A cs = Some cs' -> node_envscan A (with_ledger L cs) = Some (with_ledger L cs').
Proof.
  intros L cs cs' HL H. unfold node_envscan in *. cbv zeta in H. cbv zeta. reL_walk H; try exact HL.
Qed.
Lemma node_pnscan_reL : forall L cs cs', ledger_vars_lt (nxt cs) L = true ->
  node_pnscan A nx0 cs = Some cs' -> node_pnscan A nx0 (with_ledger L cs) = Some (with_ledger L cs').
Proof.
  intros L cs cs' HL H. unfold node_pnscan in *. reL_fresh_walk L cs HL H; try exact HL.
Qed.
Lemma node_layout_reL : forall L cs args cs', ledger_vars_lt (nxt cs) L = true ->
  node_layout cs args = Some cs' -> node_layout (with_ledger L cs) args = Some (with_ledger L cs').
Proof.
  intros L cs args cs' HL H. unfold node_layout in *. reL_fresh_walk L cs HL H; try exact HL.
Qed.

Lemma node_x_reL : forall x args L cs cs', ledger_vars_lt (nxt cs) L = true ->
  node_x segs A nx0 x args cs = Some cs' -> node_x segs A nx0 x args (with_ledger L cs) = Some (with_ledger L cs').
Proof.
  intros x args L cs cs' HL H. unfold node_x, gate0 in *.
  destruct x;
    try (match type of H with (if ?b then None else _) = _ => destruct b; [discriminate H|] end);
    first [ exact (summary_fill_reL _ _ _ _ _ HL H) | exact (summary_copy_reL _ _ _ _ HL H) | exact (summary_miz_reL _ _ _ HL H)
          | exact (node_envscan_reL _ _ _ HL H) | exact (node_pnscan_reL _ _ _ HL H) | exact (node_layout_reL _ _ _ _ HL H)
          | exact (summary_istrncpy_reL _ _ _ HL H) | exact (summary_popfree_reL _ _ _ _ HL H) | exact (summary_sniff_reL _ _ _ HL H) ].
Qed.

Lemma node_casedisj_reL : forall L cs b1 b2,
  node_casedisj A (with_ledger L cs) b1 b2 = match node_casedisj A cs b1 b2 with Some (x, y) => Some (with_ledger L x, with_ledger L y) | None => None end.
Proof.
  intros. unfold node_casedisj. rewrite kn_reL. destruct (find_disj2 (kn cs) b1 b2) as [[[[[[c1 o1] n1] c2] o2] n2]|]; [|reflexivity].  (* [comment removed for export] *)
  destruct (flat_x (kn cs) c1 o1 n1), (flat_x (kn cs) c2 o2 n2), (disj_side_fact A (kn cs) c1 o1 n1 c2 o2), (disj_side_fact A (kn cs) c2 o2 n2 c1 o1); reflexivity.
Qed.

Lemma node_havocbrk_reL : forall L cs lo hi cs', ledger_vars_lt (nxt cs) L = true ->
  node_havocbrk nx0 cs lo hi = Some cs' -> node_havocbrk nx0 (with_ledger L cs) lo hi = Some (with_ledger L cs').
Proof.
  intros L cs lo hi cs' HL H. unfold node_havocbrk in *. rewrite kn_reL, brk_reL.
  destruct (xlo (kn cs) (a_brk cs)); [|discriminate H]. destruct (xhi (kn cs) (a_brk cs)); [|discriminate H].
  destruct (fresh_ok nx0 cs) eqn:F; [|discriminate H]. rewrite (fresh_ok_reL L cs F HL). cbn [andb] in *.
  destruct (_ && _)%bool; [|discriminate H]. injection H as <-. destruct L; reflexivity.
Qed.

(* [comment removed for export] *)
Definition sg_agree (m : nat) (g h : sbind) : Prop := forall v, (v < m)%nat -> sg_get g v = sg_get h v.
Lemma sg_get_app : forall g h v, sg_get (g ++ h) v = match sg_get g v with Some e => Some e | None => sg_get h v end.
Proof. intros g h v. induction g as [|[w e] g IH]; [reflexivity|]. cbn [sg_get app]. destruct (Nat.eqb w v); [reflexivity | exact IH]. Qed.
Lemma sg_agree_app : forall m g h x, sg_agree m g h -> sg_agree m (g ++ x) (h ++ x).
Proof. intros m g h x H v Hv. rewrite !sg_get_app, (H v Hv). reflexivity. Qed.
Lemma sg_agree_refl : forall m g, sg_agree m g g.   Proof. intros m g v _; reflexivity. Qed.
Lemma esubsts_agree : forall m g h e, expr_vars_lt m e = true -> sg_agree m g h -> esubsts g e = esubsts h e.
Proof.
  intros m g h e. induction e; intros Hv Ha; cbn [esubsts expr_vars_lt] in *; try reflexivity;
    try (apply andb_prop in Hv as [H1 H2]; rewrite (IHe1 H1 Ha), (IHe2 H2 Ha); reflexivity); try (rewrite (IHe Hv Ha); reflexivity).
  apply Nat.ltb_lt in Hv. rewrite (Ha n Hv). reflexivity.
Qed.
Lemma asubsts_agree : forall m g h a, expr_vars_lt m (a_base a) = true -> sg_agree m g h -> asubsts g a = asubsts h a.
Proof. intros m g h [b o] Hv Ha. unfold asubsts. cbn [a_base a_off] in *. rewrite (esubsts_agree m g h b Hv Ha). reflexivity. Qed.
Lemma ksubsts_agree : forall m g h K, kentry_vars_lt m K = true -> sg_agree m g h -> ksubsts g K = ksubsts h K.
Proof.
  intros m g h K Hv Ha. destruct K as [[b kk] w v|[b kk] l|[b kk] l bk|lo hi|e mm|e lo hi|[b kk] n|[b1 k1] n1 [b2 k2] n2|[b kk] l c|[b kk] l];
    cbn [ksubsts kentry_vars_lt saddr_vars_lt a_base] in *;
    repeat match type of Hv with (_ && _)%bool = true => apply andb_prop in Hv as [Hv ?X] end;
    unfold asubsts; unfold saddr_vars_lt in *; cbn [a_base a_off] in *;
    repeat match goal with H : expr_vars_lt m ?e = true |- _ => rewrite (esubsts_agree m g h e H Ha); clear H end; reflexivity.
Qed.
Lemma free_slots_agree : forall m g h lo hi e acc, expr_vars_lt m e = true -> sg_agree m g h ->
  free_slots lo hi g e acc = free_slots lo hi h e acc.
Proof.
  intros m g h lo hi e. induction e; intros acc Hv Ha; cbn [free_slots expr_vars_lt] in *; try reflexivity;
    try (apply andb_prop in Hv as [H1 H2]; rewrite (IHe2 _ H2 Ha), (IHe1 _ H1 Ha); reflexivity); try (apply IHe; assumption).
  apply Nat.ltb_lt in Hv. rewrite (Ha n Hv). reflexivity.
Qed.
(* [comment removed for export] *)
Definition keys_lt (m : nat) (x : sbind) : Prop := forall v e, In (v, e) x -> (v < m)%nat.

(* [comment removed for export] *)
Definition ext_same (m : nat) (g h g' h' : sbind) : Prop := exists x, g' = g ++ x /\ h' = h ++ x.
Lemma ext_same_agree : forall m g h g' h', sg_agree m g h -> ext_same m g h g' h' -> sg_agree m g' h'.
Proof. intros m g h g' h' Ha (x & -> & ->). apply sg_agree_app. exact Ha. Qed.
Lemma ext_same_refl : forall m g h, ext_same m g h g h.
Proof. intros. exists []. rewrite !app_nil_r. split; reflexivity. Qed.
Lemma ext_same_trans : forall m g h g1 h1 g2 h2, ext_same m g h g1 h1 -> ext_same m g1 h1 g2 h2 -> ext_same m g h g2 h2.
Proof. intros m g h g1 h1 g2 h2 (x & -> & ->) (y & -> & ->). exists (x ++ y). rewrite !app_assoc. split; reflexivity. Qed.
Lemma ext_same_snoc : forall m g h p, ext_same m g h (g ++ [p]) (h ++ [p]).
Proof. intros. exists [p]. split; reflexivity. Qed.

Definition sr_lt (m : nat) (l : list expr) : Prop := forall e, In e l -> expr_vars_lt m e = true.

Lemma match_bare_ext : forall m lo hi rs ts g h, sr_lt m ts -> sg_agree m g h ->
  ext_same m g h (match_bare lo hi rs ts g) (match_bare lo hi rs ts h).
Proof.
  intros m lo hi rs. induction rs as [|r rs IH]; intros ts g h Hts Ha.
  - cbn. destruct ts; apply ext_same_refl.
  - destruct ts as [|t ts]; [apply ext_same_refl|]. cbn [match_bare].
    assert (Hts' : sr_lt m ts) by (intros e He; apply Hts; right; exact He).
    destruct t; try (apply IH; assumption).
    destruct (slotb lo hi n); [|apply IH; assumption].
    assert (Hn : (n < m)%nat) by (pose proof (Hts (EVar n) (or_introl eq_refl)) as Q; cbn in Q; apply Nat.ltb_lt in Q; exact Q).
    rewrite <- (Ha n Hn). destruct (sg_get g n).
    + apply IH; assumption.
    + eapply ext_same_trans; [apply ext_same_snoc|]. apply IH; [exact Hts' | apply sg_agree_app; exact Ha].
Qed.
(* [comment removed for export] *)
Definition sg_sim (P : nat -> bool) (g h : sbind) : Prop :=
  forall v, if P v then sg_get g v <> None /\ sg_get h v <> None else sg_get g v = sg_get h v.
Lemma sg_sim_agree : forall P m g h, (forall v, (v < m)%nat -> P v = false) -> sg_sim P g h -> sg_agree m g h.
Proof. intros P m g h Pm H v Hv. pose proof (H v) as Q. rewrite (Pm v Hv) in Q. exact Q. Qed.
Lemma sg_sim_app : forall P g h x, sg_sim P g h -> sg_sim P (g ++ x) (h ++ x).
Proof.
  intros P g h x H v. pose proof (H v) as Q. rewrite !sg_get_app. destruct (P v).
  - destruct Q as [Q1 Q2]. destruct (sg_get g v); [|exfalso; exact (Q1 eq_refl)]. destruct (sg_get h v); [|exfalso; exact (Q2 eq_refl)]. split; discriminate.
  - rewrite Q. reflexivity.
Qed.
Lemma ext_same_sim : forall P m g h g' h', sg_sim P g h -> ext_same m g h g' h' -> sg_sim P g' h'.
Proof. intros P m g h g' h' Hs (x & -> & ->). apply sg_sim_app. exact Hs. Qed.
Lemma free_slots_sim : forall P g h lo hi e acc, sg_sim P g h -> free_slots lo hi g e acc = free_slots lo hi h e acc.
Proof.
  intros P g h lo hi e. induction e; intros acc Hs; cbn [free_slots]; try reflexivity;
    try (rewrite (IHe2 _ Hs), (IHe1 _ Hs); reflexivity); try (apply IHe; exact Hs).
  destruct (slotb lo hi n); [|reflexivity]. pose proof (Hs n) as Q. destruct (P n).
  - destruct Q as [Q1 Q2]. destruct (sg_get g n); [|exfalso; exact (Q1 eq_refl)]. destruct (sg_get h n); [|exfalso; exact (Q2 eq_refl)]. reflexivity.
  - rewrite Q. reflexivity.
Qed.
Lemma solve1_ext : forall P m lo hi g h r t, (forall v, (v < m)%nat -> P v = false) -> sg_sim P g h ->
  expr_vars_lt m t = true -> ext_same m g h (solve1 lo hi g r t) (solve1 lo hi h r t).
Proof.
  intros P m lo hi g h r t Pm Hs Ht. unfold solve1.
  rewrite <- (esubsts_agree m g h t Ht (sg_sim_agree P m g h Pm Hs)).
  rewrite <- (free_slots_sim P g h lo hi (esubsts g t) [] Hs).
  destruct (free_slots lo hi g (esubsts g t) []) as [|v rest]; [apply ext_same_refl|].
  destruct (forallb (Nat.eqb v) rest); [|apply ext_same_refl].
  destruct (evar_in v (esubst v (ELit 0) (esubsts g t))); [apply ext_same_refl|].
  destruct (ldivk _ _); [apply ext_same_snoc | apply ext_same_refl].
Qed.
Lemma match_lin_ext : forall P m lo hi rs ts g h, (forall v, (v < m)%nat -> P v = false) -> sr_lt m ts -> sg_sim P g h ->
  ext_same m g h (match_lin lo hi rs ts g) (match_lin lo hi rs ts h).
Proof.
  intros P m lo hi rs. induction rs as [|r rs IH]; intros ts g h Pm Hts Hs.
  - cbn. destruct ts; apply ext_same_refl.
  - destruct ts as [|t ts]; [apply ext_same_refl|]. cbn [match_lin].
    assert (Hts' : sr_lt m ts) by (intros e He; apply Hts; right; exact He).
    assert (Ht : expr_vars_lt m t = true) by (apply Hts; left; reflexivity).
    assert (STEP : forall g1 h1, ext_same m g h g1 h1 -> sg_sim P g1 h1 -> ext_same m g h (match_lin lo hi rs ts g1) (match_lin lo hi rs ts h1)).
    { intros g1 h1 E1 S1. eapply ext_same_trans; [exact E1|]. apply IH; assumption. }
    destruct t; try (apply STEP; [apply ext_same_refl | exact Hs]);
      (pose proof (solve1_ext P m lo hi g h r _ Pm Hs Ht) as E; apply STEP; [exact E | exact (ext_same_sim P m _ _ _ _ Hs E)]).
Qed.
Definition kn_lt (m : nat) (k : list kentry) : Prop := forall K, In K k -> kentry_vars_lt m K = true.
Lemma match_kwords_ext : forall P m lo hi k tk g h, (forall v, (v < m)%nat -> P v = false) -> kn_lt m tk -> sg_sim P g h ->
  ext_same m g h (match_kwords lo hi k tk g) (match_kwords lo hi k tk h).
Proof.
  intros P m lo hi k tk. induction tk as [|K tk IH]; intros g h Pm Htk Hs; [apply ext_same_refl|].
  assert (Htk' : kn_lt m tk) by (intros K' HK'; apply Htk; right; exact HK').
  assert (HK : kentry_vars_lt m K = true) by (apply Htk; left; reflexivity).
  assert (STEP : forall g1 h1, ext_same m g h g1 h1 -> sg_sim P g1 h1 -> ext_same m g h (match_kwords lo hi k tk g1) (match_kwords lo hi k tk h1)).
  { intros g1 h1 E1 S1. eapply ext_same_trans; [exact E1|]. apply IH; assumption. }
  cbn [match_kwords].
  destruct K as [a w t|a l|a l bk|lo' hi'|e mm|e lo' hi'|a n|a1 n1 a2 n2|a l c|a l]; try (apply STEP; [apply ext_same_refl | exact Hs]).
  cbn [kentry_vars_lt saddr_vars_lt] in HK. apply andb_prop in HK as [Ha Ht].
  assert (Hag : sg_agree m g h) by exact (sg_sim_agree P m g h Pm Hs).
  rewrite <- (free_slots_sim P g h lo hi (a_base a) [] Hs). rewrite <- (asubsts_agree m g h a Ha Hag).
  destruct t; cbv zeta;
    try (destruct (free_slots lo hi g (a_base a) []); [|apply STEP; [apply ext_same_refl | exact Hs]];
         destruct (find_kword k (asubsts g a) w) as [e0|]; [|apply STEP; [apply ext_same_refl | exact Hs]];
         pose proof (solve1_ext P m lo hi g h e0 _ Pm Hs Ht) as E; apply STEP; [exact E | exact (ext_same_sim P m _ _ _ _ Hs E)]).
  (* [comment removed for export] *)
  cbn in Ht. apply Nat.ltb_lt in Ht.
  destruct (slotb lo hi n); [|apply STEP; [apply ext_same_refl | exact Hs]].
  pose proof (Hs n) as Q. rewrite (Pm n Ht) in Q. rewrite <- Q.
  destruct (sg_get g n); [apply STEP; [apply ext_same_refl | exact Hs]|].
  destruct (free_slots lo hi g (a_base a) []); [|apply STEP; [apply ext_same_refl | exact Hs]].
  destruct (find_kword k (asubsts g a) w) as [e0|]; [|apply STEP; [apply ext_same_refl | exact Hs]].
  apply STEP; [apply ext_same_snoc | apply sg_sim_app; exact Hs].
Qed.
Lemma infer_sg_ext : forall P m lo hi hA hB cs TA TB,
  (forall v, (v < m)%nat -> P v = false) -> sg_sim P hA hB -> a_ss TA = a_ss TB ->
  sr_lt m (s_regs (a_ss TA)) -> kn_lt m (kn TA) ->
  ext_same m hA hB (infer_sg lo hi hA cs TA) (infer_sg lo hi hB cs TB).
Proof.
  intros P m lo hi hA hB cs TA TB Pm Hs Ess Hr Hk. unfold infer_sg. unfold kn in *. rewrite <- Ess.
  pose proof (match_bare_ext m lo hi (s_regs (a_ss cs)) (s_regs (a_ss TA)) hA hB Hr (sg_sim_agree P m _ _ Pm Hs)) as E1.
  pose proof (ext_same_sim P m _ _ _ _ Hs E1) as S1.
  pose proof (match_lin_ext P m lo hi (s_regs (a_ss cs)) (s_regs (a_ss TA)) _ _ Pm Hr S1) as E2.
  pose proof (ext_same_sim P m _ _ _ _ S1 E2) as S2.
  pose proof (match_kwords_ext P m lo hi (s_know (a_ss cs)) (s_know (a_ss TA)) _ _ Pm Hk S2) as E3.
  eapply ext_same_trans; [exact E1|]. eapply ext_same_trans; [exact E2 | exact E3].
Qed.

(* [comment removed for export] *)
Definition tl_lt (b : nat) (ts : list (Z * expr)) : Prop := forall k a, In (k, a) ts -> expr_vars_lt b a = true.
Lemma tl_lt_nil : forall b, tl_lt b [].   Proof. intros b k a H. destruct H. Qed.
Lemma tl_lt_cons : forall b k a ts, expr_vars_lt b a = true -> tl_lt b ts -> tl_lt b ((k, a) :: ts).
Proof. intros b k a ts Ha Hts k' a' [E|H]; [injection E as <- <-; exact Ha | exact (Hts k' a' H)]. Qed.
Lemma tl_lt_tail : forall b t ts, tl_lt b (t :: ts) -> tl_lt b ts.   Proof. intros b t ts H k a Hin. apply (H k a). right. exact Hin. Qed.
Lemma tl_lt_head : forall b k a ts, tl_lt b ((k, a) :: ts) -> expr_vars_lt b a = true.   Proof. intros b k a ts H. apply (H k a). left. reflexivity. Qed.
Lemma lins_lt : forall b k a ts, expr_vars_lt b a = true -> tl_lt b ts -> tl_lt b (lins k a ts).
Proof.
  intros b k a ts Ha. induction ts as [|[k' a'] ts IH]; intros Hts; cbn [lins].
  - destruct (Z.eqb (snorm k) 0); [apply tl_lt_nil | apply tl_lt_cons; [exact Ha | apply tl_lt_nil]].
  - pose proof (tl_lt_head _ _ _ _ Hts) as Ha'. pose proof (tl_lt_tail _ _ _ Hts) as Hts'.
    destruct (expr_eqb a a').
    + cbv zeta. destruct (Z.eqb _ 0); [exact Hts' | apply tl_lt_cons; assumption].
    + destruct (expr_cmp a a'); try (apply tl_lt_cons; [exact Ha' | apply IH; exact Hts']).
      destruct (Z.eqb (snorm k) 0); [exact Hts | apply tl_lt_cons; [exact Ha | exact Hts]].
Qed.
Lemma ladd_lt : forall b x y, tl_lt b (snd x) -> tl_lt b (snd y) -> tl_lt b (snd (ladd x y)).
Proof.
  intros b x y Hx Hy. unfold ladd. cbn [snd].
  assert (G : forall l acc, tl_lt b acc -> tl_lt b l -> tl_lt b (fold_right (fun t acc => lins (fst t) (snd t) acc) acc l)).
  { intros l. induction l as [|[k a] ts IH]; intros acc Hacc Hl; cbn [fold_right fst snd]; [exact Hacc|].
    apply lins_lt; [exact (tl_lt_head _ _ _ _ Hl) | apply IH; [exact Hacc | exact (tl_lt_tail _ _ _ Hl)]]. }
  apply G; assumption.
Qed.
Lemma lscale_terms_lt : forall b m ts, tl_lt b ts -> tl_lt b (lscale_terms m ts).
Proof.
  intros b m ts. induction ts as [|[k a] ts IH]; intros H; cbn [lscale_terms]; [apply tl_lt_nil|]. cbv zeta.
  destruct (Z.eqb _ 0); [apply IH; exact (tl_lt_tail _ _ _ H) | apply tl_lt_cons; [exact (tl_lt_head _ _ _ _ H) | apply IH; exact (tl_lt_tail _ _ _ H)]].
Qed.
Lemma lscale_lt : forall b m x, tl_lt b (snd x) -> tl_lt b (snd (lscale m x)).
Proof. intros b m x H. unfold lscale. cbn [snd]. apply lscale_terms_lt. exact H. Qed.
Lemma lin_of_lt : forall b e, expr_vars_lt b e = true -> tl_lt b (snd (lin_of e)).
Proof.
  intros b e. induction e; intros H; cbn [lin_of snd]; try (apply tl_lt_cons; [exact H | apply tl_lt_nil]); try apply tl_lt_nil.
  - pose proof H as H0. cbn [expr_vars_lt] in H. apply andb_prop in H as [H1 H2].
    destruct op; cbn [snd]; try (apply tl_lt_cons; [exact H0 | apply tl_lt_nil]).
    + apply ladd_lt; [apply IHe1; exact H1 | apply IHe2; exact H2].
    + apply ladd_lt; [apply IHe1; exact H1 | apply lscale_lt; apply IHe2; exact H2].
    + destruct e2; cbn [snd]; try (apply tl_lt_cons; [exact H0 | apply tl_lt_nil]). apply lscale_lt. apply IHe1. exact H1.
  - pose proof H as H0. cbn [expr_vars_lt] in H. apply andb_prop in H as [H1 H2].
    destruct op; cbn [snd]; try (apply tl_lt_cons; [exact H0 | apply tl_lt_nil]).
    destruct e1; cbn [snd]; try (destruct e2; cbn [snd]; try (apply tl_lt_cons; [exact H0 | apply tl_lt_nil]); apply lscale_lt; apply IHe1; exact H1).
    apply lscale_lt. apply IHe2. exact H2.
Qed.
Lemma lterm_lt : forall b t, expr_vars_lt b (snd t) = true -> expr_vars_lt b (lterm t) = true.
Proof. intros b [k a] H. unfold lterm. cbn [fst snd] in *. destruct (Z.eqb k 1); [exact H | cbn; exact H]. Qed.
Lemma lterms_lt : forall b ts, tl_lt b ts -> expr_vars_lt b (lterms ts) = true.
Proof.
  intros b ts. induction ts as [|[k a] ts IH]; intros H; cbn [lterms]; [reflexivity|].
  destruct ts as [|t' ts'].
  - apply lterm_lt. cbn [snd]. exact (tl_lt_head _ _ _ _ H).
  - cbn [expr_vars_lt]. rewrite (lterm_lt b (k, a) (tl_lt_head _ _ _ _ H)). cbn [andb]. apply IH. exact (tl_lt_tail _ _ _ H).
Qed.
Lemma unlin_lt : forall b x, tl_lt b (snd x) -> expr_vars_lt b (unlin x) = true.
Proof.
  intros b [c ts] H. unfold unlin. cbn [fst snd] in *. destruct ts as [|t ts']; [reflexivity|].
  destruct (Z.eqb c 0); [apply lterms_lt; exact H|]. cbn [expr_vars_lt]. rewrite (lterms_lt b _ H). reflexivity.
Qed.
Lemma mkAlu_lt : forall b op x y, expr_vars_lt b x = true -> expr_vars_lt b y = true -> expr_vars_lt b (mkAlu op x y) = true.
Proof.
  intros b op x y Hx Hy. unfold mkAlu.
  destruct (is_lit x), (is_lit y); try reflexivity;
  (destruct op; try (cbn [expr_vars_lt]; rewrite Hx, Hy; reflexivity);
   try (apply unlin_lt; apply ladd_lt; [apply lin_of_lt; exact Hx | first [apply lin_of_lt; exact Hy | apply lscale_lt; apply lin_of_lt; exact Hy]]);
   try (destruct (shamt_of y 6); [first [apply unlin_lt; apply lscale_lt; apply lin_of_lt; exact Hx | cbn [expr_vars_lt]; rewrite Hx; reflexivity] | cbn [expr_vars_lt]; rewrite Hx, Hy; reflexivity]);
   try (destruct (is_lit y); [cbn [expr_vars_lt]; rewrite Hx, Hy; reflexivity | destruct (shamt_of y 6); cbn [expr_vars_lt]; rewrite Hx, ?Hy; reflexivity])).
Qed.
Lemma mkAluw_lt : forall b op x y, expr_vars_lt b x = true -> expr_vars_lt b y = true -> expr_vars_lt b (mkAluw op x y) = true.
Proof.
  intros b op x y Hx Hy. unfold mkAluw.
  destruct (is_lit x) eqn:Lx, (is_lit y) eqn:Ly; try reflexivity;
  (destruct op; try (cbn [expr_vars_lt]; rewrite Hx, Hy; reflexivity);
   rewrite ?Ly; try (destruct (shamt_of y 5); [rewrite ?Lx; cbn [expr_vars_lt]; rewrite ?Hx; reflexivity | cbn [expr_vars_lt]; rewrite Hx, Hy; reflexivity])).
Qed.
Lemma mkMd_lt : forall b op x y, expr_vars_lt b x = true -> expr_vars_lt b y = true -> expr_vars_lt b (mkMd op x y) = true.
Proof.
  intros b op x y Hx Hy. unfold mkMd.
  destruct (is_lit x), (is_lit y); try reflexivity; destruct op; try (cbn [expr_vars_lt]; rewrite Hx, Hy; reflexivity);
    apply unlin_lt; apply lscale_lt; apply lin_of_lt; assumption.
Qed.
Lemma mkMdw_lt : forall b op x y, expr_vars_lt b x = true -> expr_vars_lt b y = true -> expr_vars_lt b (mkMdw op x y) = true.
Proof. intros b op x y Hx Hy. unfold mkMdw. destruct (is_lit x), (is_lit y); try reflexivity; cbn [expr_vars_lt]; rewrite Hx, Hy; reflexivity. Qed.
(* [comment removed for export] *)
Definition sg_into (m : nat) (sg : sbind) (e : expr) : Prop :=
  forall n, evar_in n e = true -> match sg_get sg n with Some t => expr_vars_lt m t = true | None => (n < m)%nat end.
Lemma esubsts_lt : forall m sg e, sg_into m sg e -> expr_vars_lt m (esubsts sg e) = true.
Proof.
  intros m sg e. induction e; intros H; cbn [esubsts expr_vars_lt]; try reflexivity.
  - pose proof (H n) as Q. cbn [evar_in] in Q. rewrite Nat.eqb_refl in Q. specialize (Q eq_refl).
    destruct (sg_get sg n) as [t|]; [exact Q | cbn; apply Nat.ltb_lt; exact Q].
  - apply mkAlu_lt; [apply IHe1 | apply IHe2]; intros n Hn; apply H; cbn [evar_in]; rewrite Hn; [reflexivity | apply Bool.orb_true_r].
  - apply mkAluw_lt; [apply IHe1 | apply IHe2]; intros n Hn; apply H; cbn [evar_in]; rewrite Hn; [reflexivity | apply Bool.orb_true_r].
  - apply mkMd_lt; [apply IHe1 | apply IHe2]; intros n Hn; apply H; cbn [evar_in]; rewrite Hn; [reflexivity | apply Bool.orb_true_r].
  - apply mkMdw_lt; [apply IHe1 | apply IHe2]; intros n Hn; apply H; cbn [evar_in]; rewrite Hn; [reflexivity | apply Bool.orb_true_r].
  - apply IHe. intros k Hk. apply H. cbn [evar_in]. exact Hk.
Qed.

Lemma slot_var_inv : forall lo hi e v, slot_var lo hi e = Some v -> e = EVar v /\ (lo <= v < hi)%nat.
Proof.
  intros lo hi e v H. unfold slot_var in H. destruct e; try discriminate H.
  destruct ((lo <=? n)%nat && (n <? hi)%nat)%bool eqn:Hb; [|discriminate H]. injection H as <-.
  apply andb_prop in Hb as [H1 H2]. apply Nat.leb_le in H1. apply Nat.ltb_lt in H2. split; [reflexivity | lia].
Qed.

(* [comment removed for export] *)
Lemma use_all_transfer : forall (chk chk' : acs -> plan -> cres) (mk mk' : acs -> acs) p0 p0' cs0 cs0' (f : acs -> acs) outs ks ss,
  (forall x k s, In x outs -> chk (mk x) k = COk s -> chk' (mk' (f x)) k = COk s) ->
  use_all chk mk p0 cs0 outs ks = LOk ss -> use_all chk' mk' p0' cs0' (map f outs) ks = LOk ss.
Proof.
  intros chk chk' mk mk' p0 p0' cs0 cs0' f outs. induction outs as [|x outs IH]; intros ks ss Hk H; cbn [use_all map] in *.
  - destruct ks; [exact H | discriminate H].
  - destruct ks as [|k ks]; [discriminate H|].
    destruct (chk (mk x) k) as [s0| |] eqn:Hc; [|discriminate H|discriminate H].
    rewrite (Hk x k s0 (or_introl eq_refl) Hc).
    destruct (use_all chk mk p0 cs0 outs ks) as [ss'|r] eqn:Hu; [|discriminate H]. injection H as <-.
    rewrite (IH ks ss' (fun x0 k0 s1 Hin => Hk x0 k0 s1 (or_intror Hin)) Hu). reflexivity.
Qed.
Lemma sg_top_reledger : forall L SD, sg_top (reledger_sd L SD) = sg_top SD.
Proof. intros L SD. unfold sg_top. cbn [reledger_sd sg_outs sg_hi]. rewrite map_map. reflexivity. Qed.
Lemma wsubsts_agree : forall m g h W, wvars_lt m W = true -> sg_agree m g h -> wsubsts g W = wsubsts h W.
Proof.
  intros m g h W HW Ha. unfold wsubsts. apply map_ext_in. intros [a e] Hin.
  pose proof (proj1 (forallb_forall _ _) HW (a, e) Hin) as Q. cbn [fst snd] in Q. apply andb_prop in Q as [Q1 Q2].
  cbn [fst snd]. rewrite (asubsts_agree m g h a Q1 Ha), (esubsts_agree m g h e Q2 Ha). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma sr_map_agree : forall m g h rs, sr_vars_lt m rs = true -> sg_agree m g h -> map (esubsts g) rs = map (esubsts h) rs.
Proof.
  intros m g h rs. induction rs as [|r rs IH]; intros H Ha; [reflexivity|]. cbn [sr_vars_lt map] in *.
  apply andb_prop in H as [H1 H2]. rewrite (esubsts_agree m g h r H1 Ha), (IH H2 Ha). reflexivity.
Qed.
Lemma kn_map_agree : forall m g h k, kn_vars_lt m k = true -> sg_agree m g h -> map (ksubsts g) k = map (ksubsts h) k.
Proof.
  intros m g h k. induction k as [|K k IH]; intros H Ha; [reflexivity|]. cbn [kn_vars_lt map] in *.
  apply andb_prop in H as [H1 H2]. rewrite (ksubsts_agree m g h K H1 Ha), (IH H2 Ha). reflexivity.
Qed.
Lemma insts_core_agree : forall m g h X L0, core_vars_lt m X = true -> sg_agree m g h ->
  with_ledger L0 (insts g X) = with_ledger L0 (insts h X).
Proof.
  intros m g h X L0 HX Ha. unfold core_vars_lt in HX.
  apply andb_prop in HX as [HX Hp]. apply andb_prop in HX as [HX Hfd]. apply andb_prop in HX as [HX Hbrk]. apply andb_prop in HX as [Hsr Hkn].
  unfold insts, with_ledger. cbn [a_ss a_brk a_fd a_tidset a_props].
  rewrite (sr_map_agree m g h _ Hsr Ha), (kn_map_agree m g h _ Hkn Ha), (esubsts_agree m g h _ Hbrk Ha).
  replace (fsubsts h (a_fd X)) with (fsubsts g (a_fd X)); [reflexivity|].
  unfold fsubsts. destruct (a_fd X); try reflexivity. cbn [fd_vars_lt] in Hfd. apply andb_prop in Hfd as [F1 F2].
  rewrite (esubsts_agree m g h _ F1 Ha), (esubsts_agree m g h _ F2 Ha). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma reskel_maps_keys : forall lo hi sk ms r sg, reskel_maps lo hi sk ms = Some (r, sg) ->
  map fst sg = evar_ids (flat_map (fun m => [am_base m; am_len m]) sk) /\ (forall v, In v (map fst sg) -> (lo <= v < hi)%nat).
Proof.
  intros lo hi sk. induction sk as [|s0 sk IH]; intros ms r sg H; cbn [reskel_maps] in H.
  - destruct ms; [|discriminate H]. injection H as <- <-. split; [reflexivity | intros v []].
  - destruct (slot_var lo hi (am_base s0)) as [b|] eqn:Hb; [|discriminate H]. destruct (slot_var lo hi (am_len s0)) as [l|] eqn:Hl; [|discriminate H].
    pose proof (slot_var_inv _ _ _ _ Hb) as [Eb Rb]. pose proof (slot_var_inv _ _ _ _ Hl) as [El Rl].
    cbn [flat_map evar_ids app]. rewrite Eb, El. cbn [app].
    assert (K : forall (sg' : sbind) (e1 e2 : expr), (map fst sg' = evar_ids (flat_map (fun m => [am_base m; am_len m]) sk) /\ (forall v, In v (map fst sg') -> (lo <= v < hi)%nat)) ->
              map fst ((b, e1) :: (l, e2) :: sg') = b :: l :: evar_ids (flat_map (fun m => [am_base m; am_len m]) sk)
              /\ (forall v, In v (map fst ((b, e1) :: (l, e2) :: sg')) -> (lo <= v < hi)%nat)).
    { intros sg' e1 e2 [E1 E2]. cbn [map fst]. split; [rewrite E1; reflexivity|]. intros v [<-|[<-|Hv]]; [lia | lia | exact (E2 v Hv)]. }
    destruct ms as [|m ms'].
    + destruct (reskel_maps lo hi sk []) as [[r' sg']|] eqn:H'; [|discriminate H]. injection H as <- <-. exact (K sg' _ _ (IH _ _ _ H')).
    + destruct (reskel_maps lo hi sk ms') as [[r' sg']|] eqn:H'; [|discriminate H]. injection H as <- <-. exact (K sg' _ _ (IH _ _ _ H')).
Qed.
Lemma reskel_pairs_keys : forall lo hi sk ps r sg, reskel_pairs lo hi sk ps = Some (r, sg) ->
  map fst sg = evar_ids (flat_map (fun p => [fst p; snd p]) sk) /\ (forall v, In v (map fst sg) -> (lo <= v < hi)%nat).
Proof.
  intros lo hi sk. induction sk as [|s0 sk IH]; intros ps r sg H; cbn [reskel_pairs] in H.
  - destruct ps; [|discriminate H]. injection H as <- <-. split; [reflexivity | intros v []].
  - destruct (slot_var lo hi (fst s0)) as [b|] eqn:Hb; [|discriminate H]. destruct (slot_var lo hi (snd s0)) as [l|] eqn:Hl; [|discriminate H].
    pose proof (slot_var_inv _ _ _ _ Hb) as [Eb Rb]. pose proof (slot_var_inv _ _ _ _ Hl) as [El Rl].
    cbn [flat_map evar_ids app]. rewrite Eb, El. cbn [app].
    assert (K : forall (sg' : sbind) (e1 e2 : expr), (map fst sg' = evar_ids (flat_map (fun p : expr * expr => [fst p; snd p]) sk) /\ (forall v, In v (map fst sg') -> (lo <= v < hi)%nat)) ->
              map fst ((b, e1) :: (l, e2) :: sg') = b :: l :: evar_ids (flat_map (fun p : expr * expr => [fst p; snd p]) sk)
              /\ (forall v, In v (map fst ((b, e1) :: (l, e2) :: sg')) -> (lo <= v < hi)%nat)).
    { intros sg' e1 e2 [E1 E2]. cbn [map fst]. split; [rewrite E1; reflexivity|]. intros v [<-|[<-|Hv]]; [lia | lia | exact (E2 v Hv)]. }
    destruct ps as [|q ps'].
    + destruct (reskel_pairs lo hi sk []) as [[r' sg']|] eqn:H'; [|discriminate H]. injection H as <- <-. exact (K sg' _ _ (IH _ _ _ H')).
    + destruct (reskel_pairs lo hi sk ps') as [[r' sg']|] eqn:H'; [|discriminate H]. injection H as <- <-. exact (K sg' _ _ (IH _ _ _ H')).
Qed.
Lemma reskel_keys : forall lo hi SK L L' sk, reskel lo hi SK L = Some (L', sk) ->
  map fst sk = skel_ids SK /\ (forall v, In v (map fst sk) -> (lo <= v < hi)%nat).
Proof.
  intros lo hi SK L L' sk H. unfold reskel in H.
  destruct (reskel_maps lo hi (lg_maps SK) (lg_maps L)) as [[ms s1]|] eqn:H1; [|discriminate H].
  destruct (reskel_pairs lo hi (lg_vis SK) (lg_vis L)) as [[vs s2]|] eqn:H2; [|discriminate H].
  destruct (reskel_pairs lo hi (lg_ghost SK) (lg_ghost L)) as [[gs s3]|] eqn:H3; [|discriminate H].
  injection H as <- <-. destruct (reskel_maps_keys _ _ _ _ _ _ H1) as [K1 R1]. destruct (reskel_pairs_keys _ _ _ _ _ _ H2) as [K2 R2]. destruct (reskel_pairs_keys _ _ _ _ _ _ H3) as [K3 R3].
  unfold skel_ids. rewrite !map_app. split; [rewrite K1, K2, K3; reflexivity|].
  intros v Hv. rewrite !in_app_iff in Hv. destruct Hv as [Hv|[Hv|Hv]]; [exact (R1 v Hv) | exact (R2 v Hv) | exact (R3 v Hv)].
Qed.

(* [comment removed for export] *)
Definition inb (v : nat) (l : list nat) : bool := existsb (Nat.eqb v) l.
Lemma sg_get_in_keys : forall g v, inb v (map fst g) = true -> sg_get g v <> None.
Proof.
  intros g v. induction g as [|[w e] g IH]; intros H; cbn [map fst inb existsb sg_get] in *; [discriminate H|].
  destruct (Nat.eqb_spec v w) as [->|NE]; [rewrite Nat.eqb_refl; discriminate|].
  destruct (Nat.eqb_spec w v); [congruence|]. apply IH. exact H.
Qed.
Lemma sg_get_notin_keys : forall g v, inb v (map fst g) = false -> sg_get g v = None.
Proof.
  intros g v. induction g as [|[w e] g IH]; intros H; cbn [map fst inb existsb sg_get] in *; [reflexivity|].
  destruct (Nat.eqb_spec v w) as [->|NE]; [discriminate H|]. destruct (Nat.eqb_spec w v); [congruence|]. apply IH. exact H.
Qed.
Lemma sg_sim_hints : forall ka kb u, map fst ka = map fst kb ->
  sg_sim (fun v => inb v (map fst ka)) (ka ++ u) (kb ++ u).
Proof.
  intros ka kb u E v. rewrite !sg_get_app. destruct (inb v (map fst ka)) eqn:Hin.
  - pose proof (sg_get_in_keys ka v Hin) as Q1. pose proof (sg_get_in_keys kb v ltac:(rewrite <- E; exact Hin)) as Q2.
    destruct (sg_get ka v); [|exfalso; exact (Q1 eq_refl)]. destruct (sg_get kb v); [|exfalso; exact (Q2 eq_refl)]. split; discriminate.
  - rewrite (sg_get_notin_keys ka v Hin), (sg_get_notin_keys kb v ltac:(rewrite <- E; exact Hin)). reflexivity.
Qed.
Definition shiftk (d : nat) (sg : sbind) : sbind := map (fun ve => ((fst ve + d)%nat, snd ve)) sg.
Lemma shiftk_keys : forall d sg, map fst (shiftk d sg) = map (fun v => (v + d)%nat) (map fst sg).
Proof. intros d sg. unfold shiftk. rewrite !map_map. reflexivity. Qed.
Lemma inb_notin : forall v l, (forall w, In w l -> w <> v) -> inb v l = false.
Proof.
  intros v l H. unfold inb. induction l as [|w l IH]; [reflexivity|]. cbn [existsb].
  destruct (Nat.eqb_spec v w) as [E|NE]; [exfalso; exact (H w (or_introl eq_refl) (eq_sym E))|]. cbn [orb]. apply IH. intros w' Hw'. apply H. right. exact Hw'.
Qed.
Lemma inb_map_ge : forall d m keys v, (forall k, In k keys -> (m <= k + d)%nat) -> (v < m)%nat ->
  inb v (map (fun k => (k + d)%nat) keys) = false.
Proof.
  intros d m keys v H Hv. unfold inb. destruct (existsb (Nat.eqb v) (map (fun k => (k + d)%nat) keys)) eqn:E; [|reflexivity].
  apply existsb_exists in E as [x [Hx Ex]]. apply Nat.eqb_eq in Ex. subst x. apply in_map_iff in Hx as (k & <- & Hk). pose proof (H k Hk). lia.
Qed.
(* [comment removed for export] *)
Lemma sg_dom_in_keys : forall lo hi g h, map fst g = map fst h -> sg_dom_in lo hi g = sg_dom_in lo hi h.
Proof.
  intros lo hi g. induction g as [|[v e] g IH]; intros h E; destruct h as [|[w e'] h]; try discriminate E; [reflexivity|].
  cbn [map fst] in E. injection E as <- E. unfold sg_dom_in in *. cbn [forallb fst]. rewrite (IH h E). reflexivity.
Qed.
Lemma forallb_snd_app : forall (P : expr -> bool) (g h : sbind), forallb (fun b => P (snd b)) (g ++ h) = (forallb (fun b => P (snd b)) g && forallb (fun b => P (snd b)) h)%bool.
Proof. intros P g h. apply forallb_app. Qed.
(* [comment removed for export] *)
Lemma reskel_maps_targets : forall b lo hi sk ms r sg, reskel_maps lo hi sk ms = Some (r, sg) -> maps_vars_lt b ms = true ->
  forallb (fun ve => expr_vars_lt b (snd ve)) sg = true.
Proof.
  intros b lo hi sk. induction sk as [|s0 sk IH]; intros ms r sg H Hms; cbn [reskel_maps] in H.
  - destruct ms; [|discriminate H]. injection H as <- <-. reflexivity.
  - destruct (slot_var lo hi (am_base s0)) as [bb|]; [|discriminate H]. destruct (slot_var lo hi (am_len s0)) as [l|]; [|discriminate H].
    destruct ms as [|m ms'].
    + destruct (reskel_maps lo hi sk []) as [[r' sg']|] eqn:H'; [|discriminate H]. injection H as <- <-. cbn [forallb snd]. exact (IH [] r' sg' H' eq_refl).
    + destruct (reskel_maps lo hi sk ms') as [[r' sg']|] eqn:H'; [|discriminate H]. injection H as <- <-.
      unfold maps_vars_lt in Hms. cbn [forallb] in Hms. apply andb_prop in Hms as [Hm Hms']. apply andb_prop in Hm as [Hm1 Hm2].
      cbn [forallb snd]. rewrite Hm1, Hm2. cbn [andb]. exact (IH ms' r' sg' H' Hms').
Qed.
Lemma reskel_pairs_targets : forall b lo hi sk ps r sg, reskel_pairs lo hi sk ps = Some (r, sg) -> pairs_vars_lt b ps = true ->
  forallb (fun ve => expr_vars_lt b (snd ve)) sg = true.
Proof.
  intros b lo hi sk. induction sk as [|s0 sk IH]; intros ps r sg H Hps; cbn [reskel_pairs] in H.
  - destruct ps; [|discriminate H]. injection H as <- <-. reflexivity.
  - destruct (slot_var lo hi (fst s0)) as [bb|]; [|discriminate H]. destruct (slot_var lo hi (snd s0)) as [l|]; [|discriminate H].
    destruct ps as [|q ps'].
    + destruct (reskel_pairs lo hi sk []) as [[r' sg']|] eqn:H'; [|discriminate H]. injection H as <- <-. cbn [forallb snd]. exact (IH [] r' sg' H' eq_refl).
    + destruct (reskel_pairs lo hi sk ps') as [[r' sg']|] eqn:H'; [|discriminate H]. injection H as <- <-.
      unfold pairs_vars_lt in Hps. cbn [forallb] in Hps. apply andb_prop in Hps as [Hq Hps']. apply andb_prop in Hq as [Hq1 Hq2].
      cbn [forallb snd fst]. rewrite Hq1, Hq2. cbn [andb]. exact (IH ps' r' sg' H' Hps').
Qed.
Lemma reskel_targets : forall b lo hi SK L L' sk, reskel lo hi SK L = Some (L', sk) -> ledger_vars_lt b L = true ->
  forallb (fun ve => expr_vars_lt b (snd ve)) sk = true.
Proof.
  intros b lo hi SK L L' sk H HL. unfold reskel in H. unfold ledger_vars_lt in HL.
  apply andb_prop in HL as [HL HL3]. apply andb_prop in HL as [HL1 HL2].
  destruct (reskel_maps lo hi (lg_maps SK) (lg_maps L)) as [[ms s1]|] eqn:H1; [|discriminate H].
  destruct (reskel_pairs lo hi (lg_vis SK) (lg_vis L)) as [[vs s2]|] eqn:H2; [|discriminate H].
  destruct (reskel_pairs lo hi (lg_ghost SK) (lg_ghost L)) as [[gs s3]|] eqn:H3; [|discriminate H].
  injection H as <- <-. rewrite !forallb_app, (reskel_maps_targets b _ _ _ _ _ _ H1 HL1), (reskel_pairs_targets b _ _ _ _ _ _ H2 HL2), (reskel_pairs_targets b _ _ _ _ _ _ H3 HL3). reflexivity.
Qed.
Lemma shiftk_targets : forall P d sg, forallb (fun ve => P (snd ve)) (shiftk d sg) = forallb (fun ve : nat * expr => P (snd ve)) sg.
Proof. intros P d sg. unfold shiftk. induction sg as [|[v e] sg IH]; [reflexivity|]. cbn [map forallb snd]. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
Lemma shiftb_get' : forall lo top d v,
  sg_get (shiftb lo top d) v = if ((lo <=? v) && (v <? top))%nat then Some (EVar (v + d)%nat) else None.
Proof.
  intros lo top d v. unfold shiftb.
  assert (G : forall n k, sg_get (map (fun v0 : nat => (v0, EVar (v0 + d)%nat)) (seq k n)) v = if ((k <=? v) && (v <? k + n))%nat then Some (EVar (v + d)%nat) else None).
  { intros n. induction n as [|n IH]; intros k; cbn [seq map sg_get].
    - destruct (Nat.leb_spec k v), (Nat.ltb_spec v (k + 0)); cbn [andb]; try reflexivity. lia.
    - destruct (Nat.eqb_spec k v) as [->|NE].
      + replace ((v <=? v)%nat && (v <? v + Datatypes.S n)%nat)%bool with true; [reflexivity|]. symmetry. apply andb_true_intro. split; [apply Nat.leb_refl | apply Nat.ltb_lt; lia].
      + rewrite IH. destruct (Nat.leb_spec (Datatypes.S k) v), (Nat.leb_spec k v), (Nat.ltb_spec v (Datatypes.S k + n)), (Nat.ltb_spec v (k + Datatypes.S n)); cbn [andb]; try reflexivity; lia. }
  rewrite G. destruct (Nat.leb_spec lo v), (Nat.ltb_spec v (lo + (top - lo))), (Nat.ltb_spec v top); cbn [andb]; try reflexivity; lia.
Qed.
Lemma nodup_nat_app : forall a b, nodup_nat (a ++ b) = true ->
  nodup_nat a = true /\ nodup_nat b = true /\ (forall v, In v a -> In v b -> False).
Proof.
  intros a b. induction a as [|x a IH]; intros H; cbn [app nodup_nat] in *.
  - split; [reflexivity|]. split; [exact H | intros v []].
  - apply andb_prop in H as [H1 H2]. destruct (IH H2) as (N1 & N2 & D).
    apply Bool.negb_true_iff in H1.
    assert (Hx : forall v, In v (a ++ b) -> v <> x).
    { intros v Hv ->. assert (E : existsb (Nat.eqb x) (a ++ b) = true) by (apply existsb_exists; exists x; split; [exact Hv | apply Nat.eqb_refl]). rewrite E in H1. discriminate H1. }
    split; [|split; [exact N2|]].
    + apply andb_true_intro. split; [|exact N1]. apply Bool.negb_true_iff.
      destruct (existsb (Nat.eqb x) a) eqn:E; [|reflexivity]. exfalso. apply existsb_exists in E as [y [Hy Ey]]. apply Nat.eqb_eq in Ey. subst y.
      exact (Hx x (in_or_app _ _ _ (or_introl Hy)) eq_refl).
    + intros v [<-|Hv] Hb; [exact (Hx x (in_or_app _ _ _ (or_intror Hb)) eq_refl) | exact (D v Hv Hb)].
Qed.
Lemma nodup_nat_cons : forall x l, nodup_nat (x :: l) = true -> nodup_nat l = true /\ ~ In x l.
Proof.
  intros x l H. cbn [nodup_nat] in H. apply andb_prop in H as [H1 H2]. split; [exact H2|]. intros Hin.
  apply Bool.negb_true_iff in H1. assert (E : existsb (Nat.eqb x) l = true) by (apply existsb_exists; exists x; split; [exact Hin | apply Nat.eqb_refl]).
  rewrite E in H1. discriminate H1.
Qed.
Lemma sg_get_shiftk_cons : forall d v e sg w, sg_get (shiftk d ((v, e) :: sg)) w = if Nat.eqb (v + d) w then Some e else sg_get (shiftk d sg) w.
Proof. intros. reflexivity. Qed.
(* [comment removed for export] *)
Lemma esubsts_skel : forall lo top d pre sk rest v e,
  (lo <= v < top)%nat -> sg_get pre (v + d)%nat = None -> sg_get (shiftk d sk) (v + d)%nat = Some e ->
  esubsts (pre ++ shiftk d sk ++ rest) (esubsts (shiftb lo top d) (EVar v)) = e.
Proof.
  intros lo top d pre sk rest v e Hv Hpre Hsk. cbn [esubsts]. rewrite shiftb_get'.
  replace ((lo <=? v)%nat && (v <? top)%nat)%bool with true by (symmetry; apply andb_true_intro; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
  cbn [esubsts]. rewrite sg_get_app, Hpre, sg_get_app, Hsk. reflexivity.
Qed.
Lemma reskel_maps_lsubst : forall lo hi top d sk ms r sg pre rest,
  reskel_maps lo hi sk ms = Some (r, sg) -> nodup_nat (map fst sg) = true -> (hi <= top)%nat ->
  (forall v, In v (map fst sg) -> sg_get pre (v + d)%nat = None) ->
  map (msubsts (pre ++ shiftk d sg ++ rest)) (map (msubsts (shiftb lo top d)) r) = ms.
Proof.
  intros lo hi top d sk. induction sk as [|s0 sk IH]; intros ms r sg pre rest H Hnd Htop Hpre; cbn [reskel_maps] in H.
  - destruct ms; [|discriminate H]. injection H as <- <-. reflexivity.
  - destruct (slot_var lo hi (am_base s0)) as [b|] eqn:Hb; [|discriminate H]. destruct (slot_var lo hi (am_len s0)) as [l|] eqn:Hl; [|discriminate H].
    pose proof (slot_var_inv _ _ _ _ Hb) as [_ Rb]. pose proof (slot_var_inv _ _ _ _ Hl) as [_ Rl].
    assert (STEP : forall e1 e2 sg' r' ms', reskel_maps lo hi sk ms' = Some (r', sg') -> sg = (b, e1) :: (l, e2) :: sg' ->
              map (msubsts (pre ++ shiftk d sg ++ rest)) (map (msubsts (shiftb lo top d)) r') = ms'
              /\ esubsts (pre ++ shiftk d sg ++ rest) (esubsts (shiftb lo top d) (EVar b)) = e1
              /\ esubsts (pre ++ shiftk d sg ++ rest) (esubsts (shiftb lo top d) (EVar l)) = e2).
    { intros e1 e2 sg' r' ms' H' Esg. subst sg. cbn [map fst] in Hnd, Hpre.
      destruct (nodup_nat_cons _ _ Hnd) as [Hnd1 Hnb]. destruct (nodup_nat_cons _ _ Hnd1) as [Hnd2 Hnl].
      assert (Hbl : b <> l) by (intros ->; apply Hnb; left; reflexivity).
      split; [|split].
      - replace (pre ++ shiftk d ((b, e1) :: (l, e2) :: sg') ++ rest) with ((pre ++ shiftk d [(b, e1); (l, e2)]) ++ shiftk d sg' ++ rest)
          by (unfold shiftk; cbn [map app]; rewrite <- !app_assoc; reflexivity).
        apply (IH ms' r' sg' _ rest H' Hnd2 Htop). intros v Hv. rewrite sg_get_app, (Hpre v (or_intror (or_intror Hv))).
        unfold shiftk. cbn [map fst snd sg_get].
        destruct (Nat.eqb_spec (b + d) (v + d)); [exfalso; apply Hnb; right; replace b with v by lia; exact Hv|].
        destruct (Nat.eqb_spec (l + d) (v + d)); [exfalso; apply Hnl; replace l with v by lia; exact Hv|]. reflexivity.
      - apply (esubsts_skel lo top d pre _ rest b e1); [lia | exact (Hpre b (or_introl eq_refl)) |].
        rewrite sg_get_shiftk_cons, Nat.eqb_refl. reflexivity.
      - apply (esubsts_skel lo top d pre _ rest l e2); [lia | exact (Hpre l (or_intror (or_introl eq_refl))) |].
        rewrite sg_get_shiftk_cons. destruct (Nat.eqb_spec (b + d) (l + d)); [exfalso; apply Hbl; lia|].
        rewrite sg_get_shiftk_cons, Nat.eqb_refl. reflexivity. }
    destruct ms as [|m ms'].
    + destruct (reskel_maps lo hi sk []) as [[r' sg']|] eqn:H'; [|discriminate H]. injection H as <- <-.
      destruct (STEP (ELit 0) (ELit 0) sg' r' [] H' eq_refl) as (E & _ & _). exact E.
    + destruct (reskel_maps lo hi sk ms') as [[r' sg']|] eqn:H'; [|discriminate H]. injection H as <- <-.
      destruct (STEP (am_base m) (am_len m) sg' r' ms' H' eq_refl) as (E & E1 & E2).
      cbn [map]. unfold msubsts at 1 2. cbn [am_base am_len am_kind]. rewrite E, E1, E2. destruct m; reflexivity.
Qed.
Lemma reskel_pairs_lsubst : forall lo hi top d sk ps r sg pre rest,
  reskel_pairs lo hi sk ps = Some (r, sg) -> nodup_nat (map fst sg) = true -> (hi <= top)%nat ->
  (forall v, In v (map fst sg) -> sg_get pre (v + d)%nat = None) ->
  map (psubsts (pre ++ shiftk d sg ++ rest)) (map (psubsts (shiftb lo top d)) r) = ps.
Proof.
  intros lo hi top d sk. induction sk as [|s0 sk IH]; intros ps r sg pre rest H Hnd Htop Hpre; cbn [reskel_pairs] in H.
  - destruct ps; [|discriminate H]. injection H as <- <-. reflexivity.
  - destruct (slot_var lo hi (fst s0)) as [b|] eqn:Hb; [|discriminate H]. destruct (slot_var lo hi (snd s0)) as [l|] eqn:Hl; [|discriminate H].
    pose proof (slot_var_inv _ _ _ _ Hb) as [_ Rb]. pose proof (slot_var_inv _ _ _ _ Hl) as [_ Rl].
    assert (STEP : forall e1 e2 sg' r' ps', reskel_pairs lo hi sk ps' = Some (r', sg') -> sg = (b, e1) :: (l, e2) :: sg' ->
              map (psubsts (pre ++ shiftk d sg ++ rest)) (map (psubsts (shiftb lo top d)) r') = ps'
              /\ esubsts (pre ++ shiftk d sg ++ rest) (esubsts (shiftb lo top d) (EVar b)) = e1
              /\ esubsts (pre ++ shiftk d sg ++ rest) (esubsts (shiftb lo top d) (EVar l)) = e2).
    { intros e1 e2 sg' r' ps' H' Esg. subst sg. cbn [map fst] in Hnd, Hpre.
      destruct (nodup_nat_cons _ _ Hnd) as [Hnd1 Hnb]. destruct (nodup_nat_cons _ _ Hnd1) as [Hnd2 Hnl].
      assert (Hbl : b <> l) by (intros ->; apply Hnb; left; reflexivity).
      split; [|split].
      - replace (pre ++ shiftk d ((b, e1) :: (l, e2) :: sg') ++ rest) with ((pre ++ shiftk d [(b, e1); (l, e2)]) ++ shiftk d sg' ++ rest)
          by (unfold shiftk; cbn [map app]; rewrite <- !app_assoc; reflexivity).
        apply (IH ps' r' sg' _ rest H' Hnd2 Htop). intros v Hv. rewrite sg_get_app, (Hpre v (or_intror (or_intror Hv))).
        unfold shiftk. cbn [map fst snd sg_get].
        destruct (Nat.eqb_spec (b + d) (v + d)); [exfalso; apply Hnb; right; replace b with v by lia; exact Hv|].
        destruct (Nat.eqb_spec (l + d) (v + d)); [exfalso; apply Hnl; replace l with v by lia; exact Hv|]. reflexivity.
      - apply (esubsts_skel lo top d pre _ rest b e1); [lia | exact (Hpre b (or_introl eq_refl)) |].
        rewrite sg_get_shiftk_cons, Nat.eqb_refl. reflexivity.
      - apply (esubsts_skel lo top d pre _ rest l e2); [lia | exact (Hpre l (or_intror (or_introl eq_refl))) |].
        rewrite sg_get_shiftk_cons. destruct (Nat.eqb_spec (b + d) (l + d)); [exfalso; apply Hbl; lia|].
        rewrite sg_get_shiftk_cons, Nat.eqb_refl. reflexivity. }
    destruct ps as [|q ps'].
    + destruct (reskel_pairs lo hi sk []) as [[r' sg']|] eqn:H'; [|discriminate H]. injection H as <- <-.
      destruct (STEP (ELit 0) (ELit 0) sg' r' [] H' eq_refl) as (E & _ & _). exact E.
    + destruct (reskel_pairs lo hi sk ps') as [[r' sg']|] eqn:H'; [|discriminate H]. injection H as <- <-.
      destruct (STEP (fst q) (snd q) sg' r' ps' H' eq_refl) as (E & E1 & E2).
      cbn [map]. unfold psubsts at 1 2. cbn [fst snd]. rewrite E, E1, E2. destruct q; reflexivity.
Qed.

Lemma reskel_lsubst : forall lo hi top d SK L L' sk rest,
  reskel lo hi SK L = Some (L', sk) -> nodup_nat (skel_ids SK) = true -> (hi <= top)%nat ->
  lsubst (shiftk d sk ++ rest) (lsubst (shiftb lo top d) L') =
  LG (lg_maps L) (lg_totsz L) (lg_ylo L) (lg_eager L) (lg_vis L) (lg_ghost L) (lg_abytes L).
Proof.
  intros lo hi top d SK L L' sk rest H Hnd Htop.
  destruct (reskel_keys _ _ _ _ _ _ H) as [Hkeys _]. rewrite <- Hkeys in Hnd.
  unfold reskel in H.
  destruct (reskel_maps lo hi (lg_maps SK) (lg_maps L)) as [[ms s1]|] eqn:H1; [|discriminate H].
  destruct (reskel_pairs lo hi (lg_vis SK) (lg_vis L)) as [[vs s2]|] eqn:H2; [|discriminate H].
  destruct (reskel_pairs lo hi (lg_ghost SK) (lg_ghost L)) as [[gs s3]|] eqn:H3; [|discriminate H].
  injection H as <- <-. rewrite !map_app in Hnd.
  destruct (nodup_nat_app _ _ Hnd) as (N1 & N23 & D1). destruct (nodup_nat_app _ _ N23) as (N2 & N3 & D23).
  unfold lsubst. cbn [lg_maps lg_vis lg_ghost lg_totsz lg_ylo lg_eager lg_abytes]. unfold shiftk. rewrite !map_app. fold (shiftk d s1) (shiftk d s2) (shiftk d s3).
  f_equal.
  - rewrite <- app_assoc. change (shiftk d s1 ++ (shiftk d s2 ++ shiftk d s3) ++ rest) with ([] ++ shiftk d s1 ++ ((shiftk d s2 ++ shiftk d s3) ++ rest)).
    apply (reskel_maps_lsubst lo hi top d _ _ _ _ [] _ H1 N1 Htop). intros v _. reflexivity.
  - replace ((shiftk d s1 ++ shiftk d s2 ++ shiftk d s3) ++ rest) with (shiftk d s1 ++ shiftk d s2 ++ (shiftk d s3 ++ rest)) by (rewrite <- !app_assoc; reflexivity).
    apply (reskel_pairs_lsubst lo hi top d _ _ _ _ (shiftk d s1) _ H2 N2 Htop).
    intros v Hv. apply sg_get_notin_keys. rewrite shiftk_keys. unfold inb.
    destruct (existsb (Nat.eqb (v + d)) (map (fun v0 : nat => (v0 + d)%nat) (map fst s1))) eqn:E; [|reflexivity]. exfalso.
    apply existsb_exists in E as [x [Hx Ex]]. apply Nat.eqb_eq in Ex. apply in_map_iff in Hx as (w & <- & Hw).
    apply (D1 w Hw). apply in_or_app. left. replace w with v by lia. exact Hv.
  - replace ((shiftk d s1 ++ shiftk d s2 ++ shiftk d s3) ++ rest) with ((shiftk d s1 ++ shiftk d s2) ++ shiftk d s3 ++ rest) by (rewrite <- !app_assoc; reflexivity).
    apply (reskel_pairs_lsubst lo hi top d _ _ _ _ (shiftk d s1 ++ shiftk d s2) _ H3 N3 Htop).
    intros v Hv. apply sg_get_notin_keys. rewrite map_app, !shiftk_keys. unfold inb. rewrite existsb_app.
    destruct (existsb (Nat.eqb (v + d)) (map (fun v0 : nat => (v0 + d)%nat) (map fst s1))) eqn:E1.
    { exfalso. apply existsb_exists in E1 as [x [Hx Ex]]. apply Nat.eqb_eq in Ex. apply in_map_iff in Hx as (w & <- & Hw).
      apply (D1 w Hw). apply in_or_app. right. replace w with v by lia. exact Hv. }
    destruct (existsb (Nat.eqb (v + d)) (map (fun v0 : nat => (v0 + d)%nat) (map fst s2))) eqn:E2; [|reflexivity].
    exfalso. apply existsb_exists in E2 as [x [Hx Ex]]. apply Nat.eqb_eq in Ex. apply in_map_iff in Hx as (w & <- & Hw).
    apply (D23 w Hw). replace w with v by lia. exact Hv.
Qed.

(* [comment removed for export] *)
Lemma reskel_maps_mono : forall lo hi sk ms ms' r sg, reskel_maps lo hi sk ms = Some (r, sg) -> (length ms' <= length ms)%nat ->
  exists r' sg', reskel_maps lo hi sk ms' = Some (r', sg').
Proof.
  intros lo hi sk. induction sk as [|s0 sk IH]; intros ms ms' r sg H Hlen; cbn [reskel_maps] in *.
  - destruct ms; [|discriminate H]. destruct ms'; [exists [], []; reflexivity | cbn in Hlen; lia].
  - destruct (slot_var lo hi (am_base s0)) as [b|]; [|discriminate H]. destruct (slot_var lo hi (am_len s0)) as [l|]; [|discriminate H].
    destruct ms as [|m ms0].
    + destruct (reskel_maps lo hi sk []) as [[r0 sg0]|] eqn:H0; [|discriminate H]. destruct ms'; [|cbn in Hlen; lia].
      eexists _, _. reflexivity.
    + destruct (reskel_maps lo hi sk ms0) as [[r0 sg0]|] eqn:H0; [|discriminate H].
      destruct ms' as [|m' ms1].
      * destruct (IH ms0 [] r0 sg0 H0 ltac:(cbn; lia)) as (r' & sg' & ->). eexists _, _. reflexivity.
      * destruct (IH ms0 ms1 r0 sg0 H0 ltac:(cbn in Hlen; lia)) as (r' & sg' & ->). eexists _, _. reflexivity.
Qed.
Lemma reskel_pairs_mono : forall lo hi sk ps ps' r sg, reskel_pairs lo hi sk ps = Some (r, sg) -> (length ps' <= length ps)%nat ->
  exists r' sg', reskel_pairs lo hi sk ps' = Some (r', sg').
Proof.
  intros lo hi sk. induction sk as [|s0 sk IH]; intros ps ps' r sg H Hlen; cbn [reskel_pairs] in *.
  - destruct ps; [|discriminate H]. destruct ps'; [exists [], []; reflexivity | cbn in Hlen; lia].
  - destruct (slot_var lo hi (fst s0)) as [b|]; [|discriminate H]. destruct (slot_var lo hi (snd s0)) as [l|]; [|discriminate H].
    destruct ps as [|q ps0].
    + destruct (reskel_pairs lo hi sk []) as [[r0 sg0]|] eqn:H0; [|discriminate H]. destruct ps'; [|cbn in Hlen; lia].
      eexists _, _. reflexivity.
    + destruct (reskel_pairs lo hi sk ps0) as [[r0 sg0]|] eqn:H0; [|discriminate H].
      destruct ps' as [|q' ps1].
      * destruct (IH ps0 [] r0 sg0 H0 ltac:(cbn; lia)) as (r' & sg' & ->). eexists _, _. reflexivity.
      * destruct (IH ps0 ps1 r0 sg0 H0 ltac:(cbn in Hlen; lia)) as (r' & sg' & ->). eexists _, _. reflexivity.
Qed.
Lemma reskel_mono : forall lo hi SK Lc La ska L,
  reskel lo hi SK Lc = Some (La, ska) ->
  (length (lg_maps L) <= length (lg_maps Lc))%nat -> (length (lg_vis L) <= length (lg_vis Lc))%nat -> (length (lg_ghost L) <= length (lg_ghost Lc))%nat ->
  exists Lb skb, reskel lo hi SK L = Some (Lb, skb).
Proof.
  intros lo hi SK Lc La ska L H M1 M2 M3. unfold reskel in *.
  destruct (reskel_maps lo hi (lg_maps SK) (lg_maps Lc)) as [[ms s1]|] eqn:H1; [|discriminate H].
  destruct (reskel_pairs lo hi (lg_vis SK) (lg_vis Lc)) as [[vs s2]|] eqn:H2; [|discriminate H].
  destruct (reskel_pairs lo hi (lg_ghost SK) (lg_ghost Lc)) as [[gs s3]|] eqn:H3; [|discriminate H].
  destruct (reskel_maps_mono _ _ _ _ _ _ _ H1 M1) as (r1 & g1 & ->). destruct (reskel_pairs_mono _ _ _ _ _ _ _ H2 M2) as (r2 & g2 & ->).
  destruct (reskel_pairs_mono _ _ _ _ _ _ _ H3 M3) as (r3 & g3 & ->). eexists _, _. reflexivity.
Qed.
Lemma sg_hi_le_top : forall SD, (sg_hi SD <= sg_top SD)%nat.
Proof.
  intros SD. unfold sg_top.
  assert (G : forall l a, (a <= fold_left Nat.max l a)%nat) by (intros l; induction l as [|x l IH]; intros a; cbn; [lia | pose proof (IH (Nat.max a x)); lia]).
  apply G.
Qed.
Lemma expr_vars_lt_evar_in : forall b e n, expr_vars_lt b e = true -> evar_in n e = true -> (n < b)%nat.
Proof.
  intros b e n. induction e; intros H Hin; cbn [expr_vars_lt evar_in] in *; try discriminate Hin;
    try (apply andb_prop in H as [H1 H2]; apply Bool.orb_prop in Hin as [Hin|Hin]; [exact (IHe1 H1 Hin) | exact (IHe2 H2 Hin)]); try exact (IHe H Hin).
  apply Nat.eqb_eq in Hin. subst n0. apply Nat.ltb_lt in H. exact H.
Qed.
Lemma ksubsts_lt_gen : forall b m sg K, (forall e, expr_vars_lt b e = true -> expr_vars_lt m (esubsts sg e) = true) ->
  kentry_vars_lt b K = true -> kentry_vars_lt m (ksubsts sg K) = true.
Proof.
  intros b m sg K HS HK.
  destruct K as [[bb kk] w v|[bb kk] l|[bb kk] l bk|lo hi|e mm|e lo hi|[bb kk] n|[b1 k1] n1 [b2 k2] n2|[bb kk] l c|[bb kk] l];
    unfold ksubsts, kentry_vars_lt, saddr_vars_lt, asubsts in *; cbn [a_base a_off] in *;
    repeat match type of HK with (_ && _)%bool = true => apply andb_prop in HK as [HK ?X] end;
    repeat match goal with H : expr_vars_lt b ?e = true |- _ => rewrite (HS e H); clear H end; reflexivity.
Qed.
Lemma kn_lt_gen : forall b m sg k, (forall e, expr_vars_lt b e = true -> expr_vars_lt m (esubsts sg e) = true) ->
  kn_vars_lt b k = true -> kn_vars_lt m (map (ksubsts sg) k) = true.
Proof.
  intros b m sg k HS. induction k as [|K k IH]; intros H; [reflexivity|]. cbn [kn_vars_lt map] in *.
  apply andb_prop in H as [H1 H2]. rewrite (ksubsts_lt_gen b m sg K HS H1), (IH H2). reflexivity.
Qed.
Lemma sr_lt_gen : forall b m sg rs, (forall e, expr_vars_lt b e = true -> expr_vars_lt m (esubsts sg e) = true) ->
  sr_vars_lt b rs = true -> sr_vars_lt m (map (esubsts sg) rs) = true.
Proof.
  intros b m sg rs HS. induction rs as [|r rs IH]; intros H; [reflexivity|]. cbn [sr_vars_lt map] in *.
  apply andb_prop in H as [H1 H2]. rewrite (HS r H1), (IH H2). reflexivity.
Qed.
Lemma core_vars_lt_insts : forall b m sg X, (forall e, expr_vars_lt b e = true -> expr_vars_lt m (esubsts sg e) = true) ->
  core_vars_lt b X = true -> core_vars_lt m (insts sg X) = true.
Proof.
  intros b m sg X HS H. unfold core_vars_lt in *.
  apply andb_prop in H as [H Hp]. apply andb_prop in H as [H Hfd]. apply andb_prop in H as [H Hbrk]. apply andb_prop in H as [Hsr Hkn].
  unfold insts, kn, mk_ss in *. cbn [a_ss s_regs s_know a_brk a_fd a_props forallb].
  rewrite (sr_lt_gen b m sg _ HS Hsr), (kn_lt_gen b m sg _ HS Hkn), (HS _ Hbrk).
  replace (fd_vars_lt m (fsubsts sg (a_fd X))) with true; [reflexivity|].
  unfold fsubsts. destruct (a_fd X); try reflexivity. cbn [fd_vars_lt] in Hfd |- *. apply andb_prop in Hfd as [F1 F2]. rewrite (HS _ F1), (HS _ F2). reflexivity.
Qed.
Lemma wvars_lt_wsubsts : forall b m sg W, (forall e, expr_vars_lt b e = true -> expr_vars_lt m (esubsts sg e) = true) ->
  wvars_lt b W = true -> wvars_lt m (wsubsts sg W) = true.
Proof.
  intros b m sg W HS H. unfold wvars_lt, wsubsts in *. apply forallb_forall. intros w' Hw'. apply in_map_iff in Hw' as ([a e] & <- & Hin).
  pose proof (proj1 (forallb_forall _ _) H (a, e) Hin) as Q. cbn [fst snd] in Q |- *. apply andb_prop in Q as [Q1 Q2].
  unfold asubsts. cbn [a_base]. rewrite (HS _ Q1), (HS _ Q2). reflexivity.
Qed.
Lemma sr_lt_of : forall m rs, sr_vars_lt m rs = true -> sr_lt m rs.
Proof. intros m rs. induction rs as [|r rs IH]; intros H e He; [destruct He|]. cbn [sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct He as [<-|He]; [exact H1 | exact (IH H2 e He)]. Qed.
Lemma kn_lt_of : forall m k, kn_vars_lt m k = true -> kn_lt m k.
Proof. intros m k. induction k as [|K k IH]; intros H K' HK'; [destruct HK'|]. cbn [kn_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct HK' as [<-|HK']; [exact H1 | exact (IH H2 K' HK')]. Qed.
(* [comment removed for export] *)
Lemma shift_into : forall lo top d b e, (b <= top)%nat -> expr_vars_lt b e = true -> sg_into (b + d) (shiftb lo top d) e.
Proof.
  intros lo top d b e Hbt He n Hn. pose proof (expr_vars_lt_evar_in b e n He Hn) as Hnb. rewrite shiftb_get'.
  destruct (Nat.leb_spec lo n), (Nat.ltb_spec n top); cbn [andb]; try lia. cbn. apply Nat.ltb_lt. lia.
Qed.
Lemma esubsts_shift_lt : forall lo top d b e, (b <= top)%nat -> expr_vars_lt b e = true -> expr_vars_lt (b + d) (esubsts (shiftb lo top d) e) = true.
Proof. intros lo top d b e Hbt He. apply esubsts_lt. apply shift_into; assumption. Qed.
(* [comment removed for export] *)
Definition tl_allb (P : nat -> bool) (ts : list (Z * expr)) : Prop := forall k a, In (k, a) ts -> expr_vars_allb P a = true.
Lemma tl_allb_nil : forall P, tl_allb P [].   Proof. intros P k a H. destruct H. Qed.
Lemma tl_allb_cons : forall P k a ts, expr_vars_allb P a = true -> tl_allb P ts -> tl_allb P ((k, a) :: ts).
Proof. intros P k a ts Ha Hts k' a' [E|H]; [injection E as <- <-; exact Ha | exact (Hts k' a' H)]. Qed.
Lemma tl_allb_tail : forall P t ts, tl_allb P (t :: ts) -> tl_allb P ts.   Proof. intros P t ts H k a Hin. apply (H k a). right. exact Hin. Qed.
Lemma tl_allb_head : forall P k a ts, tl_allb P ((k, a) :: ts) -> expr_vars_allb P a = true.   Proof. intros P k a ts H. apply (H k a). left. reflexivity. Qed.
Lemma lins_allb : forall P k a ts, expr_vars_allb P a = true -> tl_allb P ts -> tl_allb P (lins k a ts).
Proof.
  intros P k a ts Ha. induction ts as [|[k' a'] ts IH]; intros Hts; cbn [lins].
  - destruct (Z.eqb (snorm k) 0); [apply tl_allb_nil | apply tl_allb_cons; [exact Ha | apply tl_allb_nil]].
  - pose proof (tl_allb_head _ _ _ _ Hts) as Ha'. pose proof (tl_allb_tail _ _ _ Hts) as Hts'.
    destruct (expr_eqb a a').
    + cbv zeta. destruct (Z.eqb _ 0); [exact Hts' | apply tl_allb_cons; assumption].
    + destruct (expr_cmp a a'); try (apply tl_allb_cons; [exact Ha' | apply IH; exact Hts']).
      destruct (Z.eqb (snorm k) 0); [exact Hts | apply tl_allb_cons; [exact Ha | exact Hts]].
Qed.
Lemma ladd_allb : forall P x y, tl_allb P (snd x) -> tl_allb P (snd y) -> tl_allb P (snd (ladd x y)).
Proof.
  intros P x y Hx Hy. unfold ladd. cbn [snd].
  assert (G : forall l acc, tl_allb P acc -> tl_allb P l -> tl_allb P (fold_right (fun t acc => lins (fst t) (snd t) acc) acc l)).
  { intros l. induction l as [|[k a] ts IH]; intros acc Hacc Hl; cbn [fold_right fst snd]; [exact Hacc|].
    apply lins_allb; [exact (tl_allb_head _ _ _ _ Hl) | apply IH; [exact Hacc | exact (tl_allb_tail _ _ _ Hl)]]. }
  apply G; assumption.
Qed.
Lemma lscale_terms_allb : forall P m ts, tl_allb P ts -> tl_allb P (lscale_terms m ts).
Proof.
  intros P m ts. induction ts as [|[k a] ts IH]; intros H; cbn [lscale_terms]; [apply tl_allb_nil|]. cbv zeta.
  destruct (Z.eqb _ 0); [apply IH; exact (tl_allb_tail _ _ _ H) | apply tl_allb_cons; [exact (tl_allb_head _ _ _ _ H) | apply IH; exact (tl_allb_tail _ _ _ H)]].
Qed.
Lemma lscale_allb : forall P m x, tl_allb P (snd x) -> tl_allb P (snd (lscale m x)).
Proof. intros P m x H. unfold lscale. cbn [snd]. apply lscale_terms_allb. exact H. Qed.
Lemma lin_of_allb : forall P e, expr_vars_allb P e = true -> tl_allb P (snd (lin_of e)).
Proof.
  intros P e. induction e; intros H; cbn [lin_of snd]; try (apply tl_allb_cons; [exact H | apply tl_allb_nil]); try apply tl_allb_nil.
  - pose proof H as H0. cbn [expr_vars_allb] in H. apply andb_prop in H as [H1 H2].
    destruct op; cbn [snd]; try (apply tl_allb_cons; [exact H0 | apply tl_allb_nil]).
    + apply ladd_allb; [apply IHe1; exact H1 | apply IHe2; exact H2].
    + apply ladd_allb; [apply IHe1; exact H1 | apply lscale_allb; apply IHe2; exact H2].
    + destruct e2; cbn [snd]; try (apply tl_allb_cons; [exact H0 | apply tl_allb_nil]). apply lscale_allb. apply IHe1. exact H1.
  - pose proof H as H0. cbn [expr_vars_allb] in H. apply andb_prop in H as [H1 H2].
    destruct op; cbn [snd]; try (apply tl_allb_cons; [exact H0 | apply tl_allb_nil]).
    destruct e1; cbn [snd]; try (destruct e2; cbn [snd]; try (apply tl_allb_cons; [exact H0 | apply tl_allb_nil]); apply lscale_allb; apply IHe1; exact H1).
    apply lscale_allb. apply IHe2. exact H2.
Qed.
Lemma lterm_allb : forall P t, expr_vars_allb P (snd t) = true -> expr_vars_allb P (lterm t) = true.
Proof. intros P [k a] H. unfold lterm. cbn [fst snd] in *. destruct (Z.eqb k 1); [exact H | cbn; exact H]. Qed.
Lemma lterms_allb : forall P ts, tl_allb P ts -> expr_vars_allb P (lterms ts) = true.
Proof.
  intros P ts. induction ts as [|[k a] ts IH]; intros H; cbn [lterms]; [reflexivity|].
  destruct ts as [|t' ts'].
  - apply lterm_allb. cbn [snd]. exact (tl_allb_head _ _ _ _ H).
  - cbn [expr_vars_allb]. rewrite (lterm_allb P (k, a) (tl_allb_head _ _ _ _ H)). cbn [andb]. apply IH. exact (tl_allb_tail _ _ _ H).
Qed.
Lemma unlin_allb : forall P x, tl_allb P (snd x) -> expr_vars_allb P (unlin x) = true.
Proof.
  intros P [c ts] H. unfold unlin. cbn [fst snd] in *. destruct ts as [|t ts']; [reflexivity|].
  destruct (Z.eqb c 0); [apply lterms_allb; exact H|]. cbn [expr_vars_allb]. rewrite (lterms_allb P _ H). reflexivity.
Qed.
Lemma mkAlu_allb : forall P op x y, expr_vars_allb P x = true -> expr_vars_allb P y = true -> expr_vars_allb P (mkAlu op x y) = true.
Proof.
  intros P op x y Hx Hy. unfold mkAlu.
  destruct (is_lit x), (is_lit y); try reflexivity;
  (destruct op; try (cbn [expr_vars_allb]; rewrite Hx, Hy; reflexivity);
   try (apply unlin_allb; apply ladd_allb; [apply lin_of_allb; exact Hx | first [apply lin_of_allb; exact Hy | apply lscale_allb; apply lin_of_allb; exact Hy]]);
   try (destruct (shamt_of y 6); [first [apply unlin_allb; apply lscale_allb; apply lin_of_allb; exact Hx | cbn [expr_vars_allb]; rewrite Hx; reflexivity] | cbn [expr_vars_allb]; rewrite Hx, Hy; reflexivity]);
   try (destruct (is_lit y); [cbn [expr_vars_allb]; rewrite Hx, Hy; reflexivity | destruct (shamt_of y 6); cbn [expr_vars_allb]; rewrite Hx, ?Hy; reflexivity])).
Qed.
Lemma mkAluw_allb : forall P op x y, expr_vars_allb P x = true -> expr_vars_allb P y = true -> expr_vars_allb P (mkAluw op x y) = true.
Proof.
  intros P op x y Hx Hy. unfold mkAluw.
  destruct (is_lit x) eqn:Lx, (is_lit y) eqn:Ly; try reflexivity;
  (destruct op; try (cbn [expr_vars_allb]; rewrite Hx, Hy; reflexivity);
   rewrite ?Ly; try (destruct (shamt_of y 5); [rewrite ?Lx; cbn [expr_vars_allb]; rewrite ?Hx; reflexivity | cbn [expr_vars_allb]; rewrite Hx, Hy; reflexivity])).
Qed.
Lemma mkMd_allb : forall P op x y, expr_vars_allb P x = true -> expr_vars_allb P y = true -> expr_vars_allb P (mkMd op x y) = true.
Proof.
  intros P op x y Hx Hy. unfold mkMd.
  destruct (is_lit x), (is_lit y); try reflexivity; destruct op; try (cbn [expr_vars_allb]; rewrite Hx, Hy; reflexivity);
    apply unlin_allb; apply lscale_allb; apply lin_of_allb; assumption.
Qed.
Lemma mkMdw_allb : forall P op x y, expr_vars_allb P x = true -> expr_vars_allb P y = true -> expr_vars_allb P (mkMdw op x y) = true.
Proof. intros P op x y Hx Hy. unfold mkMdw. destruct (is_lit x), (is_lit y); try reflexivity; cbn [expr_vars_allb]; rewrite Hx, Hy; reflexivity. Qed.

(* [comment removed for export] *)
Definition sg_intoP (P : nat -> bool) (sg : sbind) (e : expr) : Prop :=
  forall n, evar_in n e = true -> match sg_get sg n with Some t => expr_vars_allb P t = true | None => P n = true end.
Lemma esubsts_allb : forall P sg e, sg_intoP P sg e -> expr_vars_allb P (esubsts sg e) = true.
Proof.
  intros P sg e. induction e; intros H; cbn [esubsts expr_vars_allb]; try reflexivity.
  - pose proof (H n) as Q. cbn [evar_in] in Q. rewrite Nat.eqb_refl in Q. specialize (Q eq_refl).
    destruct (sg_get sg n) as [t|]; [exact Q | cbn; exact Q].
  - apply mkAlu_allb; [apply IHe1 | apply IHe2]; intros n Hn; apply H; cbn [evar_in]; rewrite Hn; [reflexivity | apply Bool.orb_true_r].
  - apply mkAluw_allb; [apply IHe1 | apply IHe2]; intros n Hn; apply H; cbn [evar_in]; rewrite Hn; [reflexivity | apply Bool.orb_true_r].
  - apply mkMd_allb; [apply IHe1 | apply IHe2]; intros n Hn; apply H; cbn [evar_in]; rewrite Hn; [reflexivity | apply Bool.orb_true_r].
  - apply mkMdw_allb; [apply IHe1 | apply IHe2]; intros n Hn; apply H; cbn [evar_in]; rewrite Hn; [reflexivity | apply Bool.orb_true_r].
  - apply IHe. intros k Hk. apply H. cbn [evar_in]. exact Hk.
Qed.

(* [comment removed for export] *)
Definition sg_agreeP (Q : nat -> bool) (g h : sbind) : Prop := forall v, Q v = true -> sg_get g v = sg_get h v.
Lemma sg_sim_agreeP : forall P g h, sg_sim P g h -> sg_agreeP (fun v => negb (P v)) g h.
Proof. intros P g h H v Hv. pose proof (H v) as X. destruct (P v); [discriminate Hv | exact X]. Qed.
Lemma esubsts_agreeP : forall Q g h e, expr_vars_allb Q e = true -> sg_agreeP Q g h -> esubsts g e = esubsts h e.
Proof.
  intros Q g h e. induction e; intros Hv Ha; cbn [esubsts expr_vars_allb] in *; try reflexivity;
    try (apply andb_prop in Hv as [H1 H2]; rewrite (IHe1 H1 Ha), (IHe2 H2 Ha); reflexivity); try (rewrite (IHe Hv Ha); reflexivity).
  rewrite (Ha n Hv). reflexivity.
Qed.
Lemma ksubsts_agreeP : forall Q g h K, kentry_vars_allb Q K = true -> sg_agreeP Q g h -> ksubsts g K = ksubsts h K.
Proof.
  intros Q g h K Hv Ha. destruct K as [[b kk] w v|[b kk] l|[b kk] l bk|lo hi|e mm|e lo hi|[b kk] n|[b1 k1] n1 [b2 k2] n2|[b kk] l c|[b kk] l];
    cbn [ksubsts kentry_vars_allb saddr_vars_allb a_base] in *;
    repeat match type of Hv with (_ && _)%bool = true => apply andb_prop in Hv as [Hv ?X] end;
    unfold asubsts; unfold saddr_vars_allb in *; cbn [a_base a_off] in *;
    repeat match goal with H : expr_vars_allb Q ?e = true |- _ => rewrite (esubsts_agreeP Q g h e H Ha); clear H end; reflexivity.
Qed.
Lemma sr_map_agreeP : forall Q g h rs, forallb (expr_vars_allb Q) rs = true -> sg_agreeP Q g h -> map (esubsts g) rs = map (esubsts h) rs.
Proof.
  intros Q g h rs. induction rs as [|r rs IH]; intros H Ha; [reflexivity|]. cbn [forallb map] in *.
  apply andb_prop in H as [H1 H2]. rewrite (esubsts_agreeP Q g h r H1 Ha), (IH H2 Ha). reflexivity.
Qed.
Lemma kn_map_agreeP : forall Q g h k, forallb (kentry_vars_allb Q) k = true -> sg_agreeP Q g h -> map (ksubsts g) k = map (ksubsts h) k.
Proof.
  intros Q g h k. induction k as [|K k IH]; intros H Ha; [reflexivity|]. cbn [forallb map] in *.
  apply andb_prop in H as [H1 H2]. rewrite (ksubsts_agreeP Q g h K H1 Ha), (IH H2 Ha). reflexivity.
Qed.
Lemma insts_core_agreeP : forall Q g h X L0, core_vars_allb Q X = true -> sg_agreeP Q g h ->
  with_ledger L0 (insts g X) = with_ledger L0 (insts h X).
Proof.
  intros Q g h X L0 HX Ha. unfold core_vars_allb in HX.
  apply andb_prop in HX as [HX Hp]. apply andb_prop in HX as [HX Hfd]. apply andb_prop in HX as [HX Hbrk]. apply andb_prop in HX as [Hsr Hkn].
  unfold insts, with_ledger. cbn [a_ss a_brk a_fd a_tidset a_props].
  rewrite (sr_map_agreeP Q g h _ Hsr Ha), (kn_map_agreeP Q g h _ Hkn Ha), (esubsts_agreeP Q g h _ Hbrk Ha).
  replace (fsubsts h (a_fd X)) with (fsubsts g (a_fd X)); [reflexivity|].
  unfold fsubsts. destruct (a_fd X); try reflexivity. cbn [fd_vars_allb] in Hfd. apply andb_prop in Hfd as [F1 F2].
  rewrite (esubsts_agreeP Q g h _ F1 Ha), (esubsts_agreeP Q g h _ F2 Ha). reflexivity.
Qed.
Lemma use_exit_agreeP : forall Q g h rho d FR KP x L0, core_vars_allb Q (insts rho x) = true -> sg_agreeP Q g h ->
  with_ledger L0 (use_exit g rho d FR KP x) = with_ledger L0 (use_exit h rho d FR KP x).
Proof.
  intros Q g h rho d FR KP x L0 Hc Ha. unfold use_exit.
  rewrite <- !set_props_reL, <- !with_ss_reL.
  change (a_ss (insts g (insts rho x))) with (a_ss (with_ledger L0 (insts g (insts rho x)))).
  change (kn (insts g (insts rho x))) with (kn (with_ledger L0 (insts g (insts rho x)))).
  change (pc (insts g (insts rho x))) with (pc (with_ledger L0 (insts g (insts rho x)))).
  change (a_ss (insts h (insts rho x))) with (a_ss (with_ledger L0 (insts h (insts rho x)))).
  change (kn (insts h (insts rho x))) with (kn (with_ledger L0 (insts h (insts rho x)))).
  change (pc (insts h (insts rho x))) with (pc (with_ledger L0 (insts h (insts rho x)))).
  rewrite (insts_core_agreeP Q g h (insts rho x) L0 Hc Ha). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma expr_vars_allb_evar_in : forall P e n, expr_vars_allb P e = true -> evar_in n e = true -> P n = true.
Proof.
  intros P e n. induction e; intros H Hin; cbn [expr_vars_allb evar_in] in *; try discriminate Hin;
    try (apply andb_prop in H as [H1 H2]; apply Bool.orb_prop in Hin as [Hin|Hin]; [exact (IHe1 H1 Hin) | exact (IHe2 H2 Hin)]); try exact (IHe H Hin).
  apply Nat.eqb_eq in Hin. subst n0. exact H.
Qed.
Lemma shift_intoP : forall (P Q : nat -> bool) lo top d e,
  (forall n, P n = true -> Q (if ((lo <=? n) && (n <? top))%nat then (n + d)%nat else n) = true) ->
  expr_vars_allb P e = true -> sg_intoP Q (shiftb lo top d) e.
Proof.
  intros P Q lo top d e HPQ He n Hn. pose proof (expr_vars_allb_evar_in P e n He Hn) as Hp. rewrite shiftb_get'.
  specialize (HPQ n Hp). destruct ((lo <=? n)%nat && (n <? top)%nat)%bool; [cbn [expr_vars_allb]; exact HPQ | exact HPQ].
Qed.
Lemma esubsts_shift_allb : forall (P Q : nat -> bool) lo top d e,
  (forall n, P n = true -> Q (if ((lo <=? n) && (n <? top))%nat then (n + d)%nat else n) = true) ->
  expr_vars_allb P e = true -> expr_vars_allb Q (esubsts (shiftb lo top d) e) = true.
Proof. intros P Q lo top d e HPQ He. apply esubsts_allb. apply (shift_intoP P); assumption. Qed.
Lemma ksubsts_allb_gen : forall P Q sg K, (forall e, expr_vars_allb P e = true -> expr_vars_allb Q (esubsts sg e) = true) ->
  kentry_vars_allb P K = true -> kentry_vars_allb Q (ksubsts sg K) = true.
Proof.
  intros P Q sg K HS HK.
  destruct K as [[bb kk] w v|[bb kk] l|[bb kk] l bk|lo hi|e mm|e lo hi|[bb kk] n|[b1 k1] n1 [b2 k2] n2|[bb kk] l c|[bb kk] l];
    unfold ksubsts, kentry_vars_allb, saddr_vars_allb, asubsts in *; cbn [a_base a_off] in *;
    repeat match type of HK with (_ && _)%bool = true => apply andb_prop in HK as [HK ?X] end;
    repeat match goal with H : expr_vars_allb P ?e = true |- _ => rewrite (HS e H); clear H end; reflexivity.
Qed.
Lemma core_vars_allb_insts : forall P Q sg X, (forall e, expr_vars_allb P e = true -> expr_vars_allb Q (esubsts sg e) = true) ->
  core_vars_allb P X = true -> core_vars_allb Q (insts sg X) = true.
Proof.
  intros P Q sg X HS H. unfold core_vars_allb in *.
  apply andb_prop in H as [H Hp]. apply andb_prop in H as [H Hfd]. apply andb_prop in H as [H Hbrk]. apply andb_prop in H as [Hsr Hkn].
  unfold insts, kn, mk_ss in *. cbn [a_ss s_regs s_know a_brk a_fd a_props forallb].
  assert (Rs : forall rs, forallb (expr_vars_allb P) rs = true -> forallb (expr_vars_allb Q) (map (esubsts sg) rs) = true).
  { intros rs. induction rs as [|r rs IH]; intros Hr; [reflexivity|]. cbn [forallb map] in *. apply andb_prop in Hr as [R1 R2]. rewrite (HS _ R1), (IH R2). reflexivity. }
  assert (Ks : forall k, forallb (kentry_vars_allb P) k = true -> forallb (kentry_vars_allb Q) (map (ksubsts sg) k) = true).
  { intros k. induction k as [|K k IH]; intros Hk; [reflexivity|]. cbn [forallb map] in *. apply andb_prop in Hk as [K1 K2]. rewrite (ksubsts_allb_gen P Q sg K HS K1), (IH K2). reflexivity. }
  rewrite (Rs _ Hsr), (Ks _ Hkn), (HS _ Hbrk).
  replace (fd_vars_allb Q (fsubsts sg (a_fd X))) with true; [reflexivity|].
  unfold fsubsts. destruct (a_fd X); try reflexivity. cbn [fd_vars_allb] in Hfd |- *. apply andb_prop in Hfd as [F1 F2]. rewrite (HS _ F1), (HS _ F2). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma entails_t_reL2 : forall L1 L2 cs T,
  entails_t A (with_ledger L1 cs) (with_ledger L1 T) = true -> entails_t A (with_ledger L2 cs) (with_ledger L2 T) = true.
Proof.
  intros L1 L2 cs T H. unfold entails_t in *.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  cbn [a_ss a_maps a_vis a_ghost a_brk a_fd a_tidset a_totsz a_ylo a_eager a_abytes with_ledger] in *.
  change (kn (with_ledger L2 cs)) with (kn cs). change (kn (with_ledger L2 T)) with (kn T).
  change (pc (with_ledger L2 cs)) with (pc cs). change (pc (with_ledger L2 T)) with (pc T).
  change (kn (with_ledger L1 cs)) with (kn cs) in *. change (kn (with_ledger L1 T)) with (kn T) in *.
  change (pc (with_ledger L1 cs)) with (pc cs) in *. change (pc (with_ledger L1 T)) with (pc T) in *.
  rewrite H, X13, X12, X11, X10, X9, list_eqb_refl_amap, !list_eqb_refl_pair, X5, X4, X3, !Z.leb_refl. reflexivity.
Qed.
Lemma use_exit_reL : forall sg rho d FR KP Lx x,
  use_exit sg rho d FR KP (with_ledger Lx x) = with_ledger (lsubst sg (lsubst rho Lx)) (use_exit sg rho d FR KP x).
Proof.
  intros sg rho d FR KP Lx x. unfold use_exit. rewrite !insts_reL.
  rewrite <- set_props_reL, <- with_ss_reL. reflexivity.
Qed.
Lemma use_exit_agree : forall m g h rho d FR KP x L0, core_vars_lt m (insts rho x) = true -> sg_agree m g h ->
  with_ledger L0 (use_exit g rho d FR KP x) = with_ledger L0 (use_exit h rho d FR KP x).
Proof.
  intros m g h rho d FR KP x L0 Hc Ha. unfold use_exit.
  rewrite <- !set_props_reL, <- !with_ss_reL.
  change (a_ss (insts g (insts rho x))) with (a_ss (with_ledger L0 (insts g (insts rho x)))).
  change (kn (insts g (insts rho x))) with (kn (with_ledger L0 (insts g (insts rho x)))).
  change (pc (insts g (insts rho x))) with (pc (with_ledger L0 (insts g (insts rho x)))).
  change (a_ss (insts h (insts rho x))) with (a_ss (with_ledger L0 (insts h (insts rho x)))).
  change (kn (insts h (insts rho x))) with (kn (with_ledger L0 (insts h (insts rho x)))).
  change (pc (insts h (insts rho x))) with (pc (with_ledger L0 (insts h (insts rho x)))).
  rewrite (insts_core_agree m g h (insts rho x) L0 Hc Ha). reflexivity.
Qed.
Lemma skel_lo_in : forall SK b, skel_lo SK = Some b -> In b (skel_ids SK).
Proof. intros SK b H. unfold skel_lo in H. destruct (skel_ids SK) as [|v r]; [discriminate|]. injection H as ->. left. reflexivity. Qed.
Lemma forallb_leb_in : forall b l k, forallb (Nat.leb b) l = true -> In k l -> (b <= k)%nat.
Proof. intros b l k H Hin. apply Nat.leb_le. exact (proj1 (forallb_forall _ _) H k Hin). Qed.

Lemma use_site_reL : forall SD0 d n nhi b cs L Lc La skh ska hints0 sg,
  let lo := sg_lo SD0 in let hi := sg_hi SD0 in
  let rho := shiftb lo (sg_top SD0) d in
  skel_lo (ledger_of (sg_in SD0)) = Some b ->
  core_vars_lt b (sg_in SD0) = true -> forallb (core_vars_allb (vout b hi (sg_top SD0))) (sg_outs SD0) = true -> wvars_lt b (sg_w SD0) = true ->
  forallb (Nat.leb b) (skel_ids (ledger_of (sg_in SD0))) = true -> nodup_nat (skel_ids (ledger_of (sg_in SD0))) = true ->
  reskel lo hi (ledger_of (sg_in SD0)) (ledger_of cs) = Some (Lc, skh) ->
  reskel lo hi (ledger_of (sg_in SD0)) L = Some (La, ska) ->
  ledger_vars_lt n L = true ->
  entails_s A n nhi (shiftk d skh ++ hints0) cs (insts rho (with_ledger Lc (sg_in SD0))) = Some sg ->
  exists X,
    sg = shiftk d skh ++ hints0 ++ X /\
    entails_s A n nhi (shiftk d ska ++ hints0) (with_ledger L cs) (insts rho (with_ledger La (sg_in SD0))) = Some (shiftk d ska ++ hints0 ++ X) /\
    (forallb (fun ve => expr_vars_lt n (snd ve)) sg = true -> forallb (fun ve => expr_vars_lt n (snd ve)) (shiftk d ska ++ hints0 ++ X) = true) /\
    wsubsts (shiftk d ska ++ hints0 ++ X) (wsubsts rho (sg_w SD0)) = wsubsts sg (wsubsts rho (sg_w SD0)) /\
    (forall FR KP x0, In x0 (sg_outs SD0) ->
        use_exit (shiftk d ska ++ hints0 ++ X) rho d FR KP (with_ledger La x0) = with_ledger L (use_exit sg rho d FR KP (with_ledger Lc x0))
        /\ ledger_of (use_exit sg rho d FR KP (with_ledger Lc x0)) = ledger_of cs).
Proof.
  intros SD0 d n nhi b cs L Lc La skh ska hints0 sg lo hi rho Hb HcI HcO HcW Hle Hnd Hrc Hra HLn He. subst rho.
  destruct (reskel_keys _ _ _ _ _ _ Hrc) as [Kc Kc']. destruct (reskel_keys _ _ _ _ _ _ Hra) as [Ka Ka'].
  assert (Hbhi : (b < hi)%nat).
  { pose proof (skel_lo_in _ _ Hb) as Hin. rewrite <- Kc in Hin. exact (proj2 (Kc' b Hin)). }
  pose proof (sg_hi_le_top SD0) as Htop. change (sg_hi SD0) with hi in Htop.
  set (m := (b + d)%nat).
  assert (HS : forall e, expr_vars_lt b e = true -> expr_vars_lt m (esubsts (shiftb lo (sg_top SD0) d) e) = true).
  { intros e H0. unfold m. apply esubsts_shift_lt; [lia | exact H0]. }
  set (P := fun v => inb v (map fst (shiftk d skh))).
  assert (HP : forall v, (v < m)%nat -> P v = false).
  { intros v Hv. unfold P. rewrite shiftk_keys. apply (inb_map_ge d m); [|exact Hv].
    intros k Hk. rewrite Kc in Hk. unfold m. pose proof (forallb_leb_in _ _ _ Hle Hk). lia. }
  assert (Hsim : sg_sim P (shiftk d skh ++ hints0) (shiftk d ska ++ hints0)).
  { unfold P. apply sg_sim_hints. rewrite !shiftk_keys, Kc, Ka. reflexivity. }
  assert (Hcore : core_vars_lt m (insts (shiftb lo (sg_top SD0) d) (sg_in SD0)) = true) by exact (core_vars_lt_insts b m (shiftb lo (sg_top SD0) d) _ HS HcI).
  unfold entails_s in He |- *.
  change (infer_sg n nhi (shiftk d ska ++ hints0) (with_ledger L cs) (insts (shiftb lo (sg_top SD0) d) (with_ledger La (sg_in SD0))))
    with (infer_sg n nhi (shiftk d ska ++ hints0) cs (insts (shiftb lo (sg_top SD0) d) (with_ledger La (sg_in SD0)))).
  assert (Q : ext_same m (shiftk d skh ++ hints0) (shiftk d ska ++ hints0)
                (infer_sg n nhi (shiftk d skh ++ hints0) cs (insts (shiftb lo (sg_top SD0) d) (with_ledger Lc (sg_in SD0))))
                (infer_sg n nhi (shiftk d ska ++ hints0) cs (insts (shiftb lo (sg_top SD0) d) (with_ledger La (sg_in SD0))))).
  { apply (infer_sg_ext P m); [exact HP | exact Hsim | rewrite !insts_reL; reflexivity | |].
    - rewrite insts_reL. cbn [a_ss with_ledger]. unfold insts. cbn [a_ss s_regs mk_ss]. apply sr_lt_of. apply (sr_lt_gen b m (shiftb lo (sg_top SD0) d) _ HS).
      unfold core_vars_lt in HcI. repeat match type of HcI with (_ && _)%bool = true => apply andb_prop in HcI as [HcI ?X] end. exact HcI.
    - rewrite insts_reL. change (kn (with_ledger ?LL ?x)) with (kn x). unfold insts, kn. cbn [a_ss s_know mk_ss]. apply kn_lt_of. apply (kn_lt_gen b m (shiftb lo (sg_top SD0) d) _ HS).
      unfold core_vars_lt in HcI. repeat match type of HcI with (_ && _)%bool = true => apply andb_prop in HcI as [HcI ?X] end. exact X2. }
  destruct Q as [X [E1 E2]]. rewrite E1 in He. rewrite E2.
  rewrite (sg_dom_in_keys n nhi ((shiftk d ska ++ hints0) ++ X) ((shiftk d skh ++ hints0) ++ X));
    [| rewrite !map_app, !shiftk_keys, Kc, Ka; reflexivity].
  destruct (sg_dom_in n nhi ((shiftk d skh ++ hints0) ++ X)); [|discriminate He]. cbn [andb] in He |- *.
  match type of He with (if ?c then _ else _) = _ => destruct c eqn:Ht; [|discriminate He] end.
  apply some_inj in He. subst sg.
  assert (Hag : sg_agree m ((shiftk d skh ++ hints0) ++ X) ((shiftk d ska ++ hints0) ++ X)).
  { apply sg_agree_app. exact (sg_sim_agree P m _ _ HP Hsim). }
  exists X. rewrite <- !app_assoc in Hag. rewrite <- !app_assoc in Ht. rewrite <- ?app_assoc. split; [reflexivity|]. split; [|split; [|split]].
  - (* [comment removed for export] *)
    rewrite !insts_reL in Ht |- *.
    rewrite (reskel_lsubst lo hi (sg_top SD0) d _ _ _ _ (hints0 ++ X) Hra Hnd Htop).
    rewrite (reskel_lsubst lo hi (sg_top SD0) d _ _ _ _ (hints0 ++ X) Hrc Hnd Htop) in Ht.
    change (LG (lg_maps (ledger_of cs)) (lg_totsz (ledger_of cs)) (lg_ylo (ledger_of cs)) (lg_eager (ledger_of cs))
               (lg_vis (ledger_of cs)) (lg_ghost (ledger_of cs)) (lg_abytes (ledger_of cs))) with (ledger_of cs) in Ht.
    rewrite <- (insts_core_agree m _ _ _ _ Hcore Hag).
    destruct L as [lm lt ly le lv lg la]. cbn [lg_maps lg_totsz lg_ylo lg_eager lg_vis lg_ghost lg_abytes].
    rewrite (entails_t_reL2 (ledger_of cs) (LG lm lt ly le lv lg la) cs _); [reflexivity|].
    rewrite with_ledger_of. exact Ht.
  - (* [comment removed for export] *)
    intros Hf. rewrite !forallb_snd_app in Hf |- *. apply andb_prop in Hf as [_ Hf]. rewrite Hf, shiftk_targets.
    rewrite (reskel_targets n _ _ _ _ _ _ Hra HLn). reflexivity.
  - (* [comment removed for export] *)
    symmetry. apply (wsubsts_agree m); [| exact Hag].
    apply (wvars_lt_wsubsts b m (shiftb lo (sg_top SD0) d) _ HS HcW).
  - (* [comment removed for export] *)
    intros FR KP x0 Hin. rewrite !use_exit_reL.
    rewrite (reskel_lsubst lo hi (sg_top SD0) d _ _ _ _ (hints0 ++ X) Hra Hnd Htop).
    rewrite (reskel_lsubst lo hi (sg_top SD0) d _ _ _ _ (hints0 ++ X) Hrc Hnd Htop).
    change (LG (lg_maps (ledger_of cs)) (lg_totsz (ledger_of cs)) (lg_ylo (ledger_of cs)) (lg_eager (ledger_of cs))
               (lg_vis (ledger_of cs)) (lg_ghost (ledger_of cs)) (lg_abytes (ledger_of cs))) with (ledger_of cs).
    split; [| apply ledger_of_with].
    rewrite with_ledger_twice.
    (* [comment removed for export] *)
    assert (Hlob : (lo <= b)%nat).
    { pose proof (skel_lo_in _ _ Hb) as Hin'. rewrite <- Kc in Hin'. exact (proj1 (Kc' b Hin')). }
    assert (HP2 : forall v, (hi + d <= v)%nat -> P v = false).
    { intros v Hv. unfold P. rewrite shiftk_keys. apply inb_notin. intros w Hw. apply in_map_iff in Hw as (k & <- & Hk).
      pose proof (proj2 (Kc' k Hk)). lia. }
    assert (Hx0 : core_vars_allb (fun v => negb (P v)) (insts (shiftb lo (sg_top SD0) d) x0) = true).
    { apply (core_vars_allb_insts (vout b hi (sg_top SD0)) (fun v => negb (P v)) (shiftb lo (sg_top SD0) d)).
      - intros e He. apply (esubsts_shift_allb (vout b hi (sg_top SD0)) (fun v => negb (P v)) lo (sg_top SD0) d e); [|exact He].
        intros w Hw. unfold vout in Hw. apply Bool.orb_prop in Hw.
        destruct ((lo <=? w)%nat && (w <? sg_top SD0)%nat)%bool eqn:Hr.
        + apply andb_prop in Hr as [R1 R2]. apply Nat.leb_le in R1. apply Nat.ltb_lt in R2.
          destruct Hw as [Hw|Hw].
          * apply Nat.ltb_lt in Hw. rewrite (HP (w + d)%nat); [reflexivity | unfold m; lia].
          * apply andb_prop in Hw as [N1 N2]. apply Nat.leb_le in N1. rewrite (HP2 (w + d)%nat); [reflexivity | lia].
        + destruct Hw as [Hw|Hw].
          * apply Nat.ltb_lt in Hw. rewrite (HP w); [reflexivity | unfold m; lia].
          * apply andb_prop in Hw as [N1 N2]. apply Nat.leb_le in N1. apply Nat.ltb_lt in N2.
            exfalso. apply Bool.andb_false_iff in Hr as [Hr|Hr]; [apply Nat.leb_gt in Hr; lia | apply Nat.ltb_ge in Hr; lia].
      - exact (proj1 (forallb_forall _ _) HcO x0 Hin). }
    assert (HagP : sg_agreeP (fun v => negb (P v)) ((shiftk d skh ++ hints0) ++ X) ((shiftk d ska ++ hints0) ++ X)).
    { apply sg_sim_agreeP. apply sg_sim_app. exact Hsim. }
    rewrite <- !app_assoc in HagP.
    rewrite <- (use_exit_agreeP (fun v => negb (P v)) _ _ (shiftb lo (sg_top SD0) d) d FR KP x0 _ Hx0 HagP).
    destruct L as [lm lt ly le lv lg la]. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma reskel_maps_shape : forall lo hi sk ms r sg, reskel_maps lo hi sk ms = Some (r, sg) ->
  forallb (fun m => is_evar (am_base m) && is_evar (am_len m))%bool r = true /\ maps_vars_lt hi r = true
  /\ length r = length ms /\ (length ms <= length sk)%nat.
Proof.
  intros lo hi sk. induction sk as [|s0 sk IH]; intros ms r sg H; cbn [reskel_maps] in H.
  - destruct ms; [|discriminate H]. injection H as <- <-. cbn. lia.
  - destruct (slot_var lo hi (am_base s0)) as [b|] eqn:Hb; [|discriminate H]. destruct (slot_var lo hi (am_len s0)) as [l|] eqn:Hl; [|discriminate H].
    pose proof (slot_var_inv _ _ _ _ Hb) as [_ Rb]. pose proof (slot_var_inv _ _ _ _ Hl) as [_ Rl].
    destruct ms as [|m ms'].
    + destruct (reskel_maps lo hi sk []) as [[r' sg']|] eqn:H'; [|discriminate H]. injection H as <- <-.
      destruct (IH _ _ _ H') as (E1 & E2 & E3 & E4). rewrite E1, E2, E3. cbn. lia.
    + destruct (reskel_maps lo hi sk ms') as [[r' sg']|] eqn:H'; [|discriminate H]. injection H as <- <-.
      destruct (IH _ _ _ H') as (E1 & E2 & E3 & E4). cbn [forallb maps_vars_lt am_base am_len is_evar length andb expr_vars_lt].
      unfold maps_vars_lt in E2. rewrite E1, E2, E3. rewrite (proj2 (Nat.ltb_lt b hi) ltac:(lia)), (proj2 (Nat.ltb_lt l hi) ltac:(lia)). cbn. lia.
Qed.
Lemma reskel_pairs_shape : forall lo hi sk ps r sg, reskel_pairs lo hi sk ps = Some (r, sg) ->
  forallb (fun p => is_evar (fst p) && is_evar (snd p))%bool r = true /\ pairs_vars_lt hi r = true
  /\ length r = length ps /\ (length ps <= length sk)%nat.
Proof.
  intros lo hi sk. induction sk as [|s0 sk IH]; intros ps r sg H; cbn [reskel_pairs] in H.
  - destruct ps; [|discriminate H]. injection H as <- <-. cbn. lia.
  - destruct (slot_var lo hi (fst s0)) as [b|] eqn:Hb; [|discriminate H]. destruct (slot_var lo hi (snd s0)) as [l|] eqn:Hl; [|discriminate H].
    pose proof (slot_var_inv _ _ _ _ Hb) as [_ Rb]. pose proof (slot_var_inv _ _ _ _ Hl) as [_ Rl].
    destruct ps as [|q ps'].
    + destruct (reskel_pairs lo hi sk []) as [[r' sg']|] eqn:H'; [|discriminate H]. injection H as <- <-.
      destruct (IH _ _ _ H') as (E1 & E2 & E3 & E4). rewrite E1, E2, E3. cbn. lia.
    + destruct (reskel_pairs lo hi sk ps') as [[r' sg']|] eqn:H'; [|discriminate H]. injection H as <- <-.
      destruct (IH _ _ _ H') as (E1 & E2 & E3 & E4). cbn [forallb pairs_vars_lt fst snd is_evar length andb expr_vars_lt].
      unfold pairs_vars_lt in E2. rewrite E1, E2, E3. rewrite (proj2 (Nat.ltb_lt b hi) ltac:(lia)), (proj2 (Nat.ltb_lt l hi) ltac:(lia)). cbn. lia.
Qed.
Lemma reskel_shape : forall lo hi SK L L' sk, reskel lo hi SK L = Some (L', sk) ->
  ledger_evars L' = true /\ ledger_vars_lt hi L' = true
  /\ length (lg_maps L') = length (lg_maps L) /\ length (lg_vis L') = length (lg_vis L) /\ length (lg_ghost L') = length (lg_ghost L)
  /\ (length (lg_maps L) <= length (lg_maps SK))%nat /\ (length (lg_vis L) <= length (lg_vis SK))%nat /\ (length (lg_ghost L) <= length (lg_ghost SK))%nat.
Proof.
  intros lo hi SK L L' sk H. unfold reskel in H.
  destruct (reskel_maps lo hi (lg_maps SK) (lg_maps L)) as [[ms s1]|] eqn:H1; [|discriminate H].
  destruct (reskel_pairs lo hi (lg_vis SK) (lg_vis L)) as [[vs s2]|] eqn:H2; [|discriminate H].
  destruct (reskel_pairs lo hi (lg_ghost SK) (lg_ghost L)) as [[gs s3]|] eqn:H3; [|discriminate H].
  injection H as <- <-.
  destruct (reskel_maps_shape _ _ _ _ _ _ H1) as (A1 & B1 & C1 & D1).
  destruct (reskel_pairs_shape _ _ _ _ _ _ H2) as (A2 & B2 & C2 & D2).
  destruct (reskel_pairs_shape _ _ _ _ _ _ H3) as (A3 & B3 & C3 & D3).
  unfold ledger_evars, ledger_vars_lt. cbn [lg_maps lg_vis lg_ghost]. rewrite A1, A2, A3, B1, B2, B3. repeat split; try reflexivity; try assumption.
Qed.
End WithNx0.
End APL.
