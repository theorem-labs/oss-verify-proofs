(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Atp_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Tactic Notation "if_dead1" "by" ne_hyp_list(hs) :=
  let K := fresh "Kc" in if_cases K; zify_cond K; rewrite ?land64_mod, ?a_signed_small in K by lia; [exfalso; clear - K hs; lia| clear K].
Tactic Notation "if_dead2" "by" ne_hyp_list(hs) :=
  let K := fresh "Kc" in if_cases K; zify_cond K; rewrite ?land64_mod, ?a_signed_small in K by lia; [clear K| exfalso; clear - K hs; lia].

Lemma rt_pres_fp_trans : forall live frames sp W m1 m2 m3,
  rt_pres_fp live frames sp W m1 m2 -> rt_pres_fp live frames sp W m2 m3 -> rt_pres_fp live frames sp W m1 m3.
Proof. intros live frames sp W m1 m2 m3 H1 H2 a Ha Ho. rewrite (H2 a Ha Ho). exact (H1 a Ha Ho). Qed.

Lemma rt_pres_fp_refl : forall live frames sp W m, rt_pres_fp live frames sp W m m.
Proof. intros live frames sp W m a _ _. reflexivity. Qed.

Lemma rt_pres_fp_of_ex : forall live frames sp' q d n W m m',
  rt_pres_ex live frames sp' d n m m' -> sp' <= q -> (forall a, outside W a -> ~ (d <= a < d + n)) ->
  rt_pres_fp live frames q W m m'.
Proof.
  intros live frames sp' q d n W m m' H LE HW a Ha Ho. apply H; [| exact (HW _ Ho)].
  apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| exact LE].
Qed.

Lemma rt_pres_of_ex0 : forall live frames sp d m m', rt_pres_ex live frames sp d 0 m m' -> rt_pres live frames sp m m'.
Proof. intros live frames sp d m m' H a Ha. apply H; [exact Ha| lia]. Qed.

Lemma cells_size_1 : forall c, cells_size [c] = csize c.
Proof. intros c. cbn. lia. Qed.

Lemma rw_cells_recastA : forall (m : mem) A cs cs', rw_cells bsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells bsegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' EQ. split; [split; [exact W'| rewrite EQ; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), EQ, (cells_bytes_length cs W). exact R.
Qed.

Lemma rec_node16 : forall (m : mem) A (w0 w1 : word) rest,
  rw_cells bsegs m A (CB 16 (le8 w0 ++ le8 w1) :: rest) -> rw_cells bsegs m A (C8 w0 :: C8 w1 :: rest).
Proof.
  intros m A w0 w1 rest H. eapply rw_cells_recastA; [exact H| | cbn [cells_bytes cbytes]; rewrite <- app_assoc; reflexivity].
  destruct H as [[W _] _]. cbn [cells_wf cell_wf] in W |- *. tauto.
Qed.

Section LvlKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable E : aenvA.
Hypothesis OK : aenvA_ok E.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma fp_client_stack1 : forall Σ l h, ae_lo E <= l -> h <= USTACK_TOP -> fp_client RT Σ (ae_lo E) [(l, h)].
Proof. intros Σ l h H1 H2. constructor; [left; cbn [fst snd]; lia| constructor]. Qed.
Lemma fp_client_stack2 : forall Σ l1 h1 l2 h2, ae_lo E <= l1 -> h1 <= USTACK_TOP -> ae_lo E <= l2 -> h2 <= USTACK_TOP ->
  fp_client RT Σ (ae_lo E) [(l1, h1); (l2, h2)].
Proof. intros Σ l1 h1 l2 h2 H1 H2 H3 H4. constructor; [left; cbn [fst snd]; lia|]. constructor; [left; cbn [fst snd]; lia| constructor]. Qed.

Lemma lvl_art_munch : forall Σ W m m', ART RT Σ m -> a_live RT Σ E -> fp_client RT Σ (ae_lo E) W ->
  munch W m m' -> wmono bsegs m m' -> ART RT Σ m'.
Proof using AF.
  intros Σ W m m' HA (_ & _ & _ & _ & LW) FP MU WM. exact (art_fp_client RT AF Σ m m' (ae_lo E) W HA LW FP MU WM).
Qed.

Lemma lvl_shz_rec : forall Σ m a n, ART RT Σ m -> a_live RT Σ E -> ae_lo E <= a -> a + n <= ae_hi E + 16 ->
  a mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> shz m a n.
Proof using AF OK.
  intros Σ m a n HA (_ & _ & _ & _ & LW) H1 H2 A8 N8 N0. destruct (ok_hi E OK) as [HL HT].
  apply (shz_stack RT AF Σ m a n HA); lia.
Qed.

Lemma lvl_shz_tape : forall Σ m, ART RT Σ m -> a_live RT Σ E -> shz m (ae_TAPE E) (8 * ae_n E).
Proof using AF OK.
  intros Σ m HA (LT & _ & _ & _ & _). destruct (ok_tape E OK) as (T16 & NT8 & TN & TS & TL).
  assert (T8 : ae_TAPE E mod 8 = 0) by (Z.div_mod_to_equations; lia).
  pose proof (shz_live RT AF Σ m (ae_TAPE E) (ae_NT E) HA LT T8) as S.
  replace (8 * (ae_NT E / 8)) with (ae_NT E) in S by (Z.div_mod_to_equations; lia).
  apply (shz_sub m _ _ _ _ S); lia.
Qed.

Lemma lvl_shz_doc : forall m, AINV_A E m -> shz m (ae_DOC E) 16.
Proof using OK. intros m AI. exact (shz_doc E m OK AI). Qed.

Lemma lvl_acc_ptr : forall Σ m P ptr, ART RT Σ m -> a_live RT Σ E -> ptr_atA E P ptr -> ptr <> [] -> acc bsegs m (ae_PB E) (ae_NPB E).
Proof using AF.
  intros Σ m P ptr HA (_ & _ & LP & _ & _) (pre & Ep & _) NE.
  destruct LP as [E0|LP]; [exfalso; rewrite E0 in Ep; destruct pre; [cbn in Ep; exact (NE (eq_sym Ep))| discriminate Ep]|].
  exact (proj2 (af_acc_live RT AF Σ m _ _ HA LP)).
Qed.

Lemma lvl_ptr_range : forall P ptr, ptr_atA E P ptr -> ptr <> [] ->
  0 < ae_PB E /\ ae_PB E <= P /\ P + zlength ptr <= ae_PB E + ae_NPB E /\ ae_PB E + ae_NPB E <= ae_lo E.
Proof using OK.
  intros P ptr (pre & Ep & EP) NE.
  assert (NE1 : ae_p1 E <> []).
  { intros E0. rewrite E0 in Ep. destruct pre; [cbn in Ep; exact (NE (eq_sym Ep))| discriminate Ep]. }
  pose proof (ok_ptr E OK NE1) as (A & B & C & D). rewrite EP. pose proof (zlength_nonneg pre).
  assert (L : zlength (ae_p1 E) = zlength pre + zlength ptr) by (rewrite Ep; unfold zlength; rewrite length_app; lia).
  lia.
Qed.

Lemma checked_dst_stack : forall Σ m sp d n, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN + 64 <= d -> d + n <= USTACK_TOP - 16 ->
  bv_unsigned sp <= d -> wr_at bsegs m d n -> checked_dst RT Σ m sp d n.
Proof using AF.
  intros Σ m sp d n HA H1 H2 H3 WR. split; [| split].
  - intros Hp. split; [apply (af_acc_stack RT AF Σ m d n HA); unfold USTACK_TOP in *; lia|]. right; right; left. lia.
  - intros i Hi. left. unfold USTACK_TOP in *. lia.
  - exact WR.
Qed.

Lemma call_ok_lvl : forall Σ m q', a_live RT Σ E -> stk bsegs m (ae_lo E) q' -> ae_lo E + RT_STACK <= q' -> q' + 16 <= USTACK_TOP ->
  q' mod 16 = 0 -> call_ok RT Σ m (Z_to_bv 64 q') (ae_lo E).
Proof using OK.
  intros Σ m q' (_ & _ & _ & _ & LW) ST H1 H2 H3. pose proof (ok_lo E OK).
  unfold call_ok. rewrite unsigned_lit by ul. split; [exact ST|]. split; [exact LW|]. split; [exact H1|]. split; [exact H2| exact H3].
Qed.

Lemma rt_pres_fp_of_munch : forall Σ mA l q W m m', ART RT Σ mA -> a_live RT Σ E -> ae_lo E <= l ->
  munch ((l, q) :: W) m m' -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q W m m'.
Proof using AF.
  intros Σ mA l q W m m' HA (_ & _ & _ & _ & LW) LL MU a Ha Ho. apply MU. cbn [outside]. split; [| exact Ho].
  destruct (aclient_split_c RT AF Σ mA q (bv_unsigned a) HA Ha); lia.
Qed.

Lemma rt_pres_fp_lower : forall Σ mA sp' q l' h' W m m', ART RT Σ mA -> a_live RT Σ E -> ae_lo E <= l' -> h' <= q -> sp' <= q ->
  rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) sp' [(l', h')] m m' -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q W m m'.
Proof using AF.
  intros Σ mA sp' q l' h' W m m' HA (_ & _ & _ & _ & LW) LL HQ SQ PR a Ha Ho. apply PR.
  - apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| exact SQ].
  - cbn [outside]. split; [| exact I]. destruct (aclient_split_c RT AF Σ mA q (bv_unsigned a) HA Ha); lia.
Qed.

Lemma lvl_live_ptr : forall Σ P ptr, a_live RT Σ E -> ptr_atA E P ptr -> ptr <> [] -> In (ae_PB E, ae_NPB E) (rt_live RT Σ).
Proof.
  intros Σ P ptr (_ & _ & LP & _ & _) (pre & Ep & _) NE.
  destruct LP as [E0|LP]; [exfalso; rewrite E0 in Ep; destruct pre; [cbn in Ep; exact (NE (eq_sym Ep))| discriminate Ep]| exact LP].
Qed.

Lemma rt_pres_fp_of_ex_lower : forall Σ mA sp' q d n W m m', ART RT Σ mA -> a_live RT Σ E -> ae_lo E <= d -> d + n <= q -> sp' <= q ->
  rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) sp' d n m m' -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q W m m'.
Proof using AF.
  intros Σ mA sp' q d n W m m' HA (_ & _ & _ & _ & LW) LD DQ SQ PR a Ha Ho. apply PR.
  - apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| exact SQ].
  - destruct (aclient_split_c RT AF Σ mA q (bv_unsigned a) HA Ha); lia.
Qed.

Lemma rt_pres_fp_mono_sp : forall live frames sp' q W m m', rt_pres_fp live frames sp' W m m' -> sp' <= q -> rt_pres_fp live frames q W m m'.
Proof.
  intros live frames sp' q W m m' PR SQ a Ha Ho. apply PR; [| exact Ho].
  apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| exact SQ].
Qed.

Lemma rec_copy16 : forall (m1 m2 : mem) out (c16 : list cell) (c1 : cell) (j2 bs : list byte) live frames sp',
  rw_cells bsegs m1 out (c16 ++ [c1; CB 4 j2]) -> cells_size c16 = 16%nat -> csize c1 = 4%nat ->
  bytes_at bsegs m2 out bs -> length bs = 16%nat -> wmono bsegs m1 m2 ->
  rt_pres_ex live frames sp' out 16 m1 m2 -> sp' <= out + 16 -> out + 24 <= USTACK_TOP ->
  rw_cells bsegs m2 out [CB 16 bs; c1; CB 4 j2].
Proof.
  intros m1 m2 out c16 c1 j2 bs live frames sp' OUT1 SZ C4SZ BY LEN WM PRES LE HI.
  destruct (proj1 (rw_cells_app bsegs m1 out c16 [c1; CB 4 j2]) OUT1) as [A B]. rewrite SZ in B.
  pose proof (proj2 A) as WA. rewrite SZ in WA.
  apply (proj2 (rw_cells_app bsegs m2 out [CB 16 bs] [c1; CB 4 j2])). split.
  - rewrite <- LEN. apply rw_cells_CB_intro; [exact BY|]. rewrite LEN. exact (wr_at_transport bsegs m1 m2 out _ WA WM).
  - cbn [cells_size csize Nat.add]. apply (rw_cells_agree_nw bsegs m1 m2 _ _ B). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES).
    intros x Hx. cbn [cells_size csize Nat.add] in Hx. rewrite C4SZ in Hx. split; [left; unfold USTACK_TOP in *; lia| lia].
Qed.

End LvlKit.
