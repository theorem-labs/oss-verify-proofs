(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v; 176 of its 211 lines of code are new or changed and 361 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/Tac_b5.v, with its module paths and module names changed; 1788 of its 1832 lines of code are new or changed and 167 lines of the source are left out. *)
(* Segment F17 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): the opens_record range 0x8229c-0x823e4 plus
   the instrumented-load report blocks. The record field walk (G06 opens_record) makes nine instrumented checks,
   each a load of the metadata byte (X >> 3) + 0x7fff8000 of a record byte X and a compare; the report call is
   shown not reached from the addressability facts in the cut. v1.9 adds ONE external callee: the body copies
   the first fragment's body into the frame object at fr + 2880 with `jal __asan_memcpy` (0x823d4).
   Entry cut Inv_A8229c, exit cut Inv_A823e8 (the F18 entry): the official cuts of SlotInv.v. The segment is split
   at 0x822a0 (Inv_A822a0), which F15's rf = 1 edge at 0x82178 also enters without running the bltz at 0x8229c:
   seg_F17 is that single branch, seg_F17b the opens_record body. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot F18.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Tac_f17b Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require PropExec.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module RF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFrag.
Module RM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcModel.
Module ULP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.PropExec.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module AW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW.SmLib.
Module ACPY := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpy_c.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.

(* ---- The model side of the opens_record body: the first-fragment state of turn S j. SlotModel's `turn`
   replaces it by (have = 1, n = gg[26], body = gg[27 .. 27 + gg[26])) exactly when `f_opens len gg` is true and
   keeps turn j's values otherwise, and the body's nine byte tests together with the 0x822a4 guard
   ([A + 232] = 0 is 50 <= len_j, s4 = 0 is blocksum = 0) are exactly the conjuncts of
   `f_opens len gg = fg_fr len gg && (gg[19] =? 1)`. In v1.9 the two address bytes are gone: the body itself is
   copied into the frame object first.sroa.7 at fr + 2880 (the `jal __asan_memcpy` at 0x823d4) and its length is
   kept in [A + 112]. *)
Lemma f17_tFG_S : forall inp j, t_FG inp (S j) = fg_st (t_len inp j) (t_FG inp j) (t_g inp j).
Proof.
  intros inp j. unfold t_FG at 1. rewrite fst_at_S. unfold turn.
  destruct (f_opens (t_len inp j) (t_g inp j)); reflexivity.
Qed.

Lemma f17_turn_false : forall s len g, f_opens len g = false ->
  fs_have (turn s len g) = fs_have s /\ fs_n (turn s len g) = fs_n s /\
  fs_body (turn s len g) = fs_body s.
Proof.
  intros s len g H. unfold turn. rewrite H.
  split; [reflexivity|]. split; reflexivity.
Qed.

Lemma f17_turn_true : forall s len g, f_opens len g = true ->
  fs_have (turn s len g) = 1 /\ fs_n (turn s len g) = RF.bat g 26 /\
  fs_body (turn s len g) = firstn (Z.to_nat (RF.bat g 26)) (skipn 27 g).
Proof.
  intros s len g H. unfold turn. rewrite H.
  split; [reflexivity|]. split; reflexivity.
Qed.

(* f_opens from the nine byte tests, the length flag and the block sum, and its negation from any one of them.
   Each test is stated as the model's own boolean (`bat g k =? c`), which is what the body's branches are
   decided on: a branch is taken when that boolean is false. *)
Lemma f17_fopens_true : forall len g,
  (50 <=? len) = true ->
  (RF.bat g 16 =? 205) = true -> (RF.bat g 17 =? 234) = true ->
  (RF.bat g 18 =? 4) = true -> (RF.bat g 19 =? 1) = true ->
  (RF.bat g 22 =? 0) = true -> (RF.bat g 23 =? 2) = true ->
  (RF.bat g 24 =? 0) = true -> (RF.bat g 25 =? 254) = true ->
  ((1 <=? RF.fg_n g) && (RF.fg_n g <=? 22)) = true ->
  (RM.blocksum (skipn 18 g) =? 0) = true ->
  f_opens len g = true.
Proof.
  intros len g H50 H16 H17 H18 H19 H22 H23 H24 H25 Hn Hbs.
  apply andb_true_iff in Hn as (Hn1 & Hn2).
  unfold f_opens, RF.fg_fr.
  rewrite H50, H16, H17, H18, H19, H22, H23, H24, H25, Hn1, Hn2, Hbs.
  reflexivity.
Qed.

Lemma f17_fopens_false : forall len g,
  ((50 <=? len) = false \/ (RF.bat g 16 =? 205) = false \/ (RF.bat g 17 =? 234) = false \/
   (RF.bat g 18 =? 4) = false \/ (RF.bat g 19 =? 1) = false \/ (RF.bat g 22 =? 0) = false \/
   (RF.bat g 23 =? 2) = false \/ (RF.bat g 24 =? 0) = false \/ (RF.bat g 25 =? 254) = false \/
   ((1 <=? RF.fg_n g) && (RF.fg_n g <=? 22)) = false \/ (RM.blocksum (skipn 18 g) =? 0) = false) ->
  f_opens len g = false.
Proof.
  intros len g H. unfold f_opens, RF.fg_fr.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]].
  - rewrite H. reflexivity.
  - rewrite H, ?Bool.andb_false_r. reflexivity.
  - rewrite H, ?Bool.andb_false_r. reflexivity.
  - rewrite H, ?Bool.andb_false_r. reflexivity.
  - (* the byte-19 test is f_opens's second factor (fg_fr allows 1 or 2) *)
    rewrite H, ?Bool.andb_false_r. reflexivity.
  - rewrite H, ?Bool.andb_false_r. reflexivity.
  - rewrite H, ?Bool.andb_false_r. reflexivity.
  - rewrite H, ?Bool.andb_false_r. reflexivity.
  - rewrite H, ?Bool.andb_false_r. reflexivity.
  - apply andb_false_iff in H.
    destruct H as [H|H]; rewrite H, ?Bool.andb_false_r; reflexivity.
  - rewrite H, ?Bool.andb_false_r. reflexivity.
Qed.

(* One corollary per test, so an exit names the test that failed instead of searching for it: a search (tauto /
   auto / eassumption) tries its goal against every hypothesis and every disjunct, and those unifications unfold
   the model's byte functions, so each disjunct is injected by hand here. *)
Lemma f17_fop_len : forall len g, (50 <=? len) = false -> f_opens len g = false.
Proof. intros len g H. apply f17_fopens_false. left. exact H. Qed.
Lemma f17_fop_16 : forall len g, (RF.bat g 16 =? 205) = false -> f_opens len g = false.
Proof. intros len g H. apply f17_fopens_false. right; left. exact H. Qed.
Lemma f17_fop_17 : forall len g, (RF.bat g 17 =? 234) = false -> f_opens len g = false.
Proof. intros len g H. apply f17_fopens_false. right; right; left. exact H. Qed.
Lemma f17_fop_18 : forall len g, (RF.bat g 18 =? 4) = false -> f_opens len g = false.
Proof. intros len g H. apply f17_fopens_false. right; right; right; left. exact H. Qed.
Lemma f17_fop_19 : forall len g, (RF.bat g 19 =? 1) = false -> f_opens len g = false.
Proof. intros len g H. apply f17_fopens_false. right; right; right; right; left. exact H. Qed.
Lemma f17_fop_22 : forall len g, (RF.bat g 22 =? 0) = false -> f_opens len g = false.
Proof. intros len g H. apply f17_fopens_false. right; right; right; right; right; left. exact H. Qed.
Lemma f17_fop_23 : forall len g, (RF.bat g 23 =? 2) = false -> f_opens len g = false.
Proof. intros len g H. apply f17_fopens_false. right; right; right; right; right; right; left. exact H. Qed.
Lemma f17_fop_24 : forall len g, (RF.bat g 24 =? 0) = false -> f_opens len g = false.
Proof.
  intros len g H. apply f17_fopens_false. right; right; right; right; right; right; right; left. exact H.
Qed.
Lemma f17_fop_25 : forall len g, (RF.bat g 25 =? 254) = false -> f_opens len g = false.
Proof.
  intros len g H. apply f17_fopens_false.
  right; right; right; right; right; right; right; right; left. exact H.
Qed.
Lemma f17_fop_26 : forall len g, ((1 <=? RF.fg_n g) && (RF.fg_n g <=? 22)) = false ->
  f_opens len g = false.
Proof.
  intros len g H. apply f17_fopens_false.
  right; right; right; right; right; right; right; right; right; left. exact H.
Qed.
Lemma f17_fop_bs : forall len g, (RM.blocksum (skipn 18 g) =? 0) = false -> f_opens len g = false.
Proof.
  intros len g H. apply f17_fopens_false.
  right; right; right; right; right; right; right; right; right; right. exact H.
Qed.

(* On a long frame the turn's sum flag IS the block-sum test, which is fg_fr's last conjunct. The `true && _` is
   removed by rewriting: closing `X = true && X` by conversion makes the checker evaluate X, the block sum of the
   symbolic record, and that does not finish in useful time. *)
Lemma f17_sumok_bs : forall inp j, t_big inp j = true ->
  (RM.blocksum (skipn 18 (t_g inp j)) =? 0) = t_sum_ok inp j.
Proof. intros inp j H. unfold t_sum_ok. rewrite H, Bool.andb_true_l. reflexivity. Qed.

(* The record's byte 6 after a turn that does not open it: either the record is untouched (FgRefuse / FgNone)
   or it was cleared (FgDrop / FgJoin / FgClose), where byte 6 is 0 and FI is vacuous. FgFirst is excluded,
   since it needs fg_fr and gg[19] = 1, i.e. f_opens. *)
Lemma f17_clear_bat6 : forall st, (7 <= length st)%nat -> RF.bat (RF.fg_clear st) 6 = 0.
Proof.
  intros st HL. unfold RF.bat, RF.fg_clear.
  change (Z.to_nat 6) with 6%nat.
  rewrite app_nth2 by (rewrite length_firstn; lia).
  rewrite length_firstn. replace (6 - Nat.min 6 (length st))%nat with 0%nat by lia.
  reflexivity.
Qed.

Lemma f17_next_clear_or_same : forall len st g, f_opens len g = false ->
  length st = 72%nat -> length g = 50%nat ->
  fg_next st g (fcls len st g) = st \/ RF.bat (fg_next st g (fcls len st g)) 6 = 0.
Proof.
  intros len st g Hop HL HG. unfold fcls. rewrite rf_class_nn by lia.
  destruct (RF.fg_fr len g) eqn:F1; cbn [negb].
  2:{ left. reflexivity. }
  destruct (RF.bat g 19 =? 1) eqn:F2.
  { exfalso. unfold f_opens in Hop. rewrite F1, F2 in Hop. discriminate Hop. }
  pose proof (f18_fr_fg_n len g F1) as Hn.
  destruct (RF.fg_keep st g) eqn:K1; cbn [negb].
  2:{ right. apply f17_clear_bat6. lia. }
  pose proof (f18_keep_T st g K1) as HT.
  assert (HJ : length (RF.fg_join st g) = 72%nat)
    by (apply rf_fg_join_length; [exact HL | exact HG | lia | lia]).
  destruct (RF.fg_close st g); cbn [negb]; right; apply f17_clear_bat6; lia.
Qed.

(* The opening turn writes fg_first, whose byte 6 is 1 and whose byte 7 is gg[26] = fg_n gg, and whose body from
   offset 8 is gg[27 .. 27 + fg_n gg) - which is exactly the body the memcpy copies into fr + 2880. *)
Lemma f17_first_bat6 : forall st g, (12 <= length g)%nat -> RF.bat (RF.fg_first st g) 6 = 1.
Proof.
  intros st g HG.
  assert (Hb6 : length (RF.bsl g 6 6) = 6%nat)
    by (rewrite rf_bsl_length; [reflexivity | lia | lia | lia]).
  unfold RF.bat, RF.fg_first. change (Z.to_nat 6) with 6%nat.
  rewrite app_nth2 by (rewrite Hb6; lia). rewrite Hb6.
  replace (6 - 6)%nat with 0%nat by lia. reflexivity.
Qed.

Lemma f17_first_bat7 : forall st g, (27 <= length g)%nat -> RF.bat (RF.fg_first st g) 7 = RF.fg_n g.
Proof.
  intros st g HG.
  assert (Hb6 : length (RF.bsl g 6 6) = 6%nat)
    by (rewrite rf_bsl_length; [reflexivity | lia | lia | lia]).
  unfold RF.bat, RF.fg_first, RF.fg_n. change (Z.to_nat 7) with 7%nat.
  rewrite app_nth2 by (rewrite Hb6; lia). rewrite Hb6.
  replace (7 - 6)%nat with 1%nat by lia. cbn [app nth]. reflexivity.
Qed.

(* The body of fg_first, read as FI reads it: the first fg_n gg bytes from offset 8. *)
Lemma f17_first_body : forall st g, length g = 50%nat -> 1 <= RF.fg_n g <= 22 ->
  firstn (Z.to_nat (RF.fg_n g)) (skipn 8 (RF.fg_first st g))
    = firstn (Z.to_nat (RF.fg_n g)) (skipn 27 g).
Proof.
  intros st g HG Hn.
  assert (Hb6 : length (RF.bsl g 6 6) = 6%nat)
    by (rewrite rf_bsl_length; [reflexivity | lia | lia | lia]).
  assert (Hbody : length (RF.fg_body g) = Z.to_nat (RF.fg_n g))
    by (unfold RF.fg_body; rewrite rf_bsl_length; [reflexivity | lia | lia | lia]).
  unfold RF.fg_first.
  (* the 8-byte prefix is the six header bytes and [1; gg[26]]; the body follows it *)
  rewrite app_assoc.
  assert (H8 : length (RF.bsl g 6 6 ++ [Z_to_bv 8 1; nth 26 g (Z_to_bv 8 0)]) = 8%nat)
    by (rewrite length_app, Hb6; reflexivity).
  rewrite skipn_app, (skipn_all2 (RF.bsl g 6 6 ++ [Z_to_bv 8 1; nth 26 g (Z_to_bv 8 0)])) by lia.
  rewrite H8, Nat.sub_diag, skipn_O, app_nil_l.
  rewrite firstn_app, Hbody, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite firstn_all2 by lia.
  unfold RF.fg_body, RF.bsl. reflexivity.
Qed.

(* FI of turn S j, on both arms. *)
Lemma f17_fi_false : forall g j, f_opens (flen g j) (t_g (g_in g) j) = false ->
  FI (t_FG (g_in g) j) (fst_at (g_in g) j) -> FI (t_FG (g_in g) (S j)) (fst_at (g_in g) (S j)).
Proof.
  intros g j Hop HFI.
  rewrite f17_tFG_S. unfold fg_st. rewrite fst_at_S.
  destruct (f17_turn_false (fst_at (g_in g) j) (t_len (g_in g) j) (t_g (g_in g) j) Hop)
    as (E1 & E2 & E3).
  unfold FI in *. rewrite E1, E2, E3.
  destruct (f17_next_clear_or_same (t_len (g_in g) j) (t_FG (g_in g) j) (t_g (g_in g) j) Hop
              (f18_t_FG_length (g_in g) j) (f18_t_g_length (g_in g) j)) as [Hsame | Hz].
  - rewrite Hsame. exact HFI.
  - intros H6. rewrite Hz in H6. discriminate H6.
Qed.

Lemma f17_fi_true : forall g j, f_opens (flen g j) (t_g (g_in g) j) = true ->
  FI (t_FG (g_in g) (S j)) (fst_at (g_in g) (S j)).
Proof.
  intros g j Hop.
  pose proof (f18_t_g_length (g_in g) j) as HG.
  assert (HFR : RF.fg_fr (t_len (g_in g) j) (t_g (g_in g) j) = true /\
                (RF.bat (t_g (g_in g) j) 19 =? 1) = true).
  { unfold f_opens, flen in Hop. apply andb_prop in Hop. exact Hop. }
  destruct HFR as (HFR1 & H19).
  pose proof (f18_fr_fg_n _ _ HFR1) as Hn.
  assert (ECL : fcls (t_len (g_in g) j) (t_FG (g_in g) j) (t_g (g_in g) j) = RF.FgFirst).
  { unfold fcls. rewrite rf_class_nn by lia. rewrite HFR1. cbn [negb]. rewrite H19. reflexivity. }
  rewrite f17_tFG_S. unfold fg_st. rewrite ECL. cbn [fg_next]. rewrite fst_at_S.
  destruct (f17_turn_true (fst_at (g_in g) j) (t_len (g_in g) j) (t_g (g_in g) j) Hop)
    as (E1 & E2 & E3).
  unfold FI. rewrite E1, E2, E3.
  rewrite (f17_first_bat7 (t_FG (g_in g) j) (t_g (g_in g) j) ltac:(lia)).
  intros _. split; [reflexivity|]. split; [reflexivity|].
  symmetry. apply (f17_first_body (t_FG (g_in g) j) (t_g (g_in g) j) HG Hn).
Qed.


(* The two frame records (38 bytes at fr + 2688, 72 at fr + 2768) across the opens_record stores: they lie in
   the frame, which is apart from the spill cells and from the body object the memcpy writes. *)
Lemma f17_idfg_keep : forall g fr j m m' W,
  IDj g fr (S j) m -> FGj g fr (S j) m -> LF.munch W m m' ->
  (forall x, fr + 2688 <= x < fr + 2840 -> LF.outside W x) ->
  IDj g fr (S j) m' /\ FGj g fr (S j) m'.
Proof.
  intros g fr j m m' W (Hid & Hidok) (Hfg & Hfgok) MU HW.
  split.
  - split; [|exact Hidok]. eapply fl_bytes; [exact Hid | exact MU |].
    rewrite f18_t_ID_length. intros x Hx. apply HW. lia.
  - split; [|exact Hfgok]. eapply fl_bytes; [exact Hfg | exact MU |].
    rewrite f18_t_FG_length. intros x Hx. apply HW. lia.
Qed.

(* q64 (SlotInv) is stated with lib/Lib's le8; this file's `le8` (the one the step engine writes with) is the
   tree's other copy of the same definition, so the two cells are convertible. *)
Lemma f17_q64_ba : forall m a v, bytes_at rsegs m a (le8 (Z_to_bv 64 v)) -> q64 m a v.
Proof. intros m a v H. exact H. Qed.

(* One 8-byte word written at a, read back; and a word at c kept across a write at a disjoint 8-byte cell. *)
Lemma f17_w8_same : forall m a (v : Z), 0 <= a -> a + 8 <= 2 ^ 64 ->
  bytes_at rsegs (write_to_mem m (wa a) (le8 (Z_to_bv 64 v))) a (le8 (Z_to_bv 64 v)).
Proof. intros m a v H0 H1. apply (bytes_at_write_same rsegs); [lia | rewrite length_le8; lia]. Qed.

Lemma f17_w8_other : forall m a c (w v : Z), bytes_at rsegs m c (le8 (Z_to_bv 64 v)) ->
  0 <= a -> a + 8 <= 2 ^ 64 -> (c + 8 <= a \/ a + 8 <= c) ->
  bytes_at rsegs (write_to_mem m (wa a) (le8 (Z_to_bv 64 w))) c (le8 (Z_to_bv 64 v)).
Proof.
  intros m a c w v H H0 H1 H2.
  apply (bytes_at_write_other rsegs); [exact H | lia | rewrite length_le8; lia | rewrite !length_le8; lia].
Qed.
(* The first-fragment state of turn S j: turn j's when the record does not open, and (1, gg[26], the copied
   body) when it does. v1.9's FSb names two spills ([A + 104] = have, [A + 112] = n) and the body object in
   the frame (bytes at fr + 2880, addressable 35). *)
Lemma f17_fsj_regs : forall g fr k (regs regs' : bvmap 5 word) m,
  FSj g fr k regs m -> getr regs' 9 = getr regs 9 -> FSj g fr k regs' m.
Proof.
  intros g fr k regs regs' m (H104 & H112 & Hbody & Hbad & HFI) E9.
  assert (Hsr : forall off v, spill regs m off v -> spill regs' m off v)
    by (intros off v (A & HA & Hq); exists A; split; [unfold rg in *; rewrite E9; exact HA | exact Hq]).
  split; [exact (Hsr _ _ H104)|]. split; [exact (Hsr _ _ H112)|].
  split; [exact Hbody|]. split; [exact Hbad | exact HFI].
Qed.

Lemma f17_fsj_false : forall g fr j regs m, f_opens (flen g j) (t_g (g_in g) j) = false ->
  FSj g fr j regs m -> FSj g fr (S j) regs m.
Proof.
  intros g fr j regs m Hop (H104 & H112 & Hbody & Hbad & HFI).
  unfold FSj, FSb. rewrite fst_at_S.
  destruct (f17_turn_false (fst_at (g_in g) j) (t_len (g_in g) j) (t_g (g_in g) j) Hop)
    as (E1 & E2 & E3).
  rewrite E1, E2, E3.
  split; [exact H104|]. split; [exact H112|]. split; [exact Hbody|]. split; [exact Hbad|].
  exact (f17_fi_false g j Hop HFI).
Qed.

Lemma f17_fsj_true : forall g fr j regs m, f_opens (flen g j) (t_g (g_in g) j) = true ->
  spill regs m 104 1 -> spill regs m 112 (RF.bat (t_g (g_in g) j) 26) ->
  bytes_at rsegs m (fr + 2880)
    (firstn (Z.to_nat (RF.bat (t_g (g_in g) j) 26)) (skipn 27 (t_g (g_in g) j))) ->
  addressable m (fr + 2880) 35 ->
  FSj g fr (S j) regs m.
Proof.
  intros g fr j regs m Hop H104 H112 Hbody Hbad.
  unfold FSj, FSb. rewrite fst_at_S.
  destruct (f17_turn_true (fst_at (g_in g) j) (t_len (g_in g) j) (t_g (g_in g) j) Hop)
    as (E1 & E2 & E3).
  rewrite E1, E2, E3.
  split; [exact H104|]. split; [exact H112|]. split; [exact Hbody|]. split; [exact Hbad|].
  exact (f17_fi_true g j Hop).
Qed.

(* ---- The code side: one loaded byte of the record, as the model's `bat`. The body reads each byte with
   `lbu` after its shadow check, so the compared word is the zero-extended byte. *)
Lemma f17_fs1 : forall (l : list byte) (k : nat) d, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l d].
Proof.
  intros l k d Hk. destruct (skipn k l) as [|b l0] eqn:E.
  - exfalso. apply (f_equal (@length _)) in E. rewrite length_skipn in E. cbn [length] in E. lia.
  - cbn [firstn]. f_equal.
    pose proof (rf_nth_skipn l k 0 d) as HH. rewrite E in HH. cbn [nth] in HH.
    rewrite Nat.add_0_r in HH. exact HH.
Qed.

Lemma f17_byte_word : forall (l : list byte) (k : Z), 0 <= k -> (Z.to_nat k < length l)%nat ->
  zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn (Z.to_nat k) l)))) = Z_to_bv 64 (RF.bat l k).
Proof.
  intros l k Hk Hl.
  rewrite (f17_fs1 l (Z.to_nat k) (Z_to_bv 8 0) Hl).
  rewrite ULP.le_word_1, ULP.b_extract8_id, zext_small. reflexivity.
Qed.

Lemma f17_bne_val : forall (l : list byte) (k c : Z), 0 <= k -> (Z.to_nat k < length l)%nat ->
  0 <= c < 2 ^ 64 ->
  negb (bv_eqb (zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn (Z.to_nat k) l)))))
               (Z_to_bv 64 c))
    = negb (RF.bat l k =? c).
Proof.
  intros l k c Hk Hl Hc. rewrite (f17_byte_word l k Hk Hl). unfold RF.bat.
  f_equal. exact (rf_beq (nth (Z.to_nat k) l (Z_to_bv 8 0)) c Hc).
Qed.

Lemma f17_bltu_val : forall (l : list byte) (k : Z), 0 <= k -> (Z.to_nat k < length l)%nat ->
  bv_ltu (Z_to_bv 64 (bv_unsigned (zext 64 (bv_extract 0 8
            (le_bytes_to_word (firstn 1 (skipn (Z.to_nat k) l))))) + -23)) (Z_to_bv 64 (-22))
    = negb ((1 <=? RF.bat l k) && (RF.bat l k <=? 22)).
Proof.
  intros l k Hk Hl. rewrite (f17_byte_word l k Hk Hl). unfold RF.bat.
  exact (rf_n (nth (Z.to_nat k) l (Z_to_bv 8 0))).
Qed.


(* ---- The memcpy's write set [D, D + n) u [sp - K, sp) (Seg/P4.v p4_out / p4_cases, with the copy's length a
   parameter). ---- *)
Lemma f17_out2 : forall lo1 hi1 lo2 hi2 x, (x < lo1 \/ hi1 <= x) -> (x < lo2 \/ hi2 <= x) ->
  LF.outside [(lo1, hi1); (lo2, hi2)] x.
Proof. intros lo1 hi1 lo2 hi2 x H1 H2. cbn [LF.outside]. split; [lia|]. split; [lia | exact I]. Qed.

(* Every byte is outside the write set, in the destination, or in the stack scratch. *)
Lemma f17_cases : forall D n sp K x,
  LF.outside [(D, D + n); (sp - K, sp)] x \/ (D <= x < D + n) \/ (sp - K <= x < sp).
Proof.
  intros D n sp K x.
  destruct (Z.lt_ge_cases x D) as [H1|H1]; [|destruct (Z.lt_ge_cases x (D + n)) as [H2|H2]].
  all: destruct (Z.lt_ge_cases x (sp - K)) as [H3|H3]; [|destruct (Z.lt_ge_cases x sp) as [H4|H4]].
  all: first [ right; left; lia | right; right; lia | left; apply f17_out2; lia ].
Qed.

(* A byte of a carried byte range is readable (image B's F17b.v f17_ba_rd). *)
Lemma f17_ba_rd : forall m a bs q, bytes_at rsegs m a bs -> a <= q < a + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa q) = Some b.
Proof.
  intros m a bs q (H0 & H1 & H) Hq.
  pose proof (H (Z.to_nat (q - a)) ltac:(lia)) as Hb. rewrite Z2Nat.id in Hb by lia.
  replace (a + (q - a)) with q in Hb by lia.
  destruct (nth_error bs (Z.to_nat (q - a))) as [b|] eqn:En; [exists b; exact Hb|].
  exfalso. apply nth_error_None in En. lia.
Qed.

(* rec_parse across a write window that misses the record bytes phi + 14 .. phi + 17, every shadow byte and the
   u16 at fr + 196 (F18.rec_parse_kept asks for all of [0, HIGHMEM_BEG) instead of the shadow, which the memcpy's
   destination need not miss: on FRA's side arm the frame lies in the FakeStack, which may be low app memory). *)
Lemma f17_rec_parse_kept : forall g j fr phi m m' W,
  rec_parse g j fr phi m -> (forall a, phi <= a < phi + 50 -> app_mem a) -> LF.munch W m m' ->
  (forall x, phi <= x < phi + 50 -> LF.outside W x) ->
  (forall x, in_shadow x -> LF.outside W x) ->
  (forall x, fr + 196 <= x < fr + 198 -> LF.outside W x) ->
  rec_parse g j fr phi m'.
Proof.
  intros g j fr phi m m' W (field16 & v14 & v15 & v16 & v17 & Hf16 & Hb14 & Hb15 & Hb16 & Hb17 &
     Rv14 & Rv15 & Rv16 & Rv17 & Hs14 & Hs15 & Hs16 & Hs17 & Heq1 & Heq2) Hpap MU OWphi OWsh OWkp.
  assert (SHin : forall t x, 14 <= t <= 17 -> Z.shiftr (phi + t) 3 + ASAN_K <= x < Z.shiftr (phi + t) 3 + ASAN_K + 1 ->
            LF.outside W x).
  { intros t x Ht Hx. apply OWsh.
    replace x with (shadow_addr (phi + t)).
    2:{ rewrite Z.shiftr_div_pow2 in Hx by lia. change (2 ^ 3) with 8 in Hx. unfold shadow_addr. lia. }
    apply shadow_of_app. apply Hpap. lia. }
  exists field16, v14, v15, v16, v17.
  split; [unfold u16 in *; eapply fl_bytes; [exact Hf16 | exact MU | rewrite length_le2; intros x Hx; apply OWkp; lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb14 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb15 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb16 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb17 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [exact Rv14|]. split; [exact Rv15|]. split; [exact Rv16|]. split; [exact Rv17|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs14 | exact MU | cbn [length]; intros x Hx; apply (SHin 14 x); lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs15 | exact MU | cbn [length]; intros x Hx; apply (SHin 15 x); lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs16 | exact MU | cbn [length]; intros x Hx; apply (SHin 16 x); lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs17 | exact MU | cbn [length]; intros x Hx; apply (SHin 17 x); lia]|].
  split; [exact Heq1|]. exact Heq2.
Qed.

(* word_mem pins the value only modulo 2^64 (Seg/F6.v f6_word_mem_eq): the FakeStack base read off the tp word
   is one value. *)
Lemma f17_wm_congr : forall m a v1 v2, word_mem rsegs m a v1 -> word_mem rsegs m a v2 ->
  v1 mod 2 ^ 64 = v2 mod 2 ^ 64.
Proof.
  intros m a v1 v2 H1 H2.
  assert (E : forall k, (k < 8)%nat -> le_byte v1 8 k = le_byte v2 8 k).
  { intros k Hk. pose proof (H1 k Hk) as E1. pose proof (H2 k Hk) as E2.
    rewrite E1 in E2.
    assert (EB : Z_to_bv 8 (le_byte v1 8 k) = Z_to_bv 8 (le_byte v2 8 k)) by congruence.
    rewrite <- (kb_byte_unsigned v1 8 k), <- (kb_byte_unsigned v2 8 k), EB. reflexivity. }
  assert (M : forall v k, le_byte (v mod 2 ^ 64) 8 k = le_byte v 8 k).
  { intros v k. unfold le_byte. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity. }
  pose proof (kb_le8_digits (v1 mod 2 ^ 64) ltac:(apply Z.mod_pos_bound; lia)) as D1.
  pose proof (kb_le8_digits (v2 mod 2 ^ 64) ltac:(apply Z.mod_pos_bound; lia)) as D2.
  rewrite !M in D1. rewrite !M in D2.
  rewrite D1 at 1. rewrite D2 at 1.
  rewrite (E 0%nat ltac:(lia)), (E 1%nat ltac:(lia)), (E 2%nat ltac:(lia)), (E 3%nat ltac:(lia)),
    (E 4%nat ltac:(lia)), (E 5%nat ltac:(lia)), (E 6%nat ltac:(lia)), (E 7%nat ltac:(lia)).
  reflexivity.
Qed.

(* A byte that is not outside a three-interval write set is in one of the three intervals. *)
Lemma f17_in3 : forall l1 h1 l2 h2 l3 h3 x, ~ LF.outside [(l1, h1); (l2, h2); (l3, h3)] x ->
  (l1 <= x < h1) \/ (l2 <= x < h2) \/ (l3 <= x < h3).
Proof.
  intros l1 h1 l2 h2 l3 h3 x H.
  destruct (Z_lt_le_dec x l1) as [L1|L1]; [|destruct (Z_lt_le_dec x h1) as [L2|L2]; [left; lia|]];
  (destruct (Z_lt_le_dec x l2) as [L3|L3]; [|destruct (Z_lt_le_dec x h2) as [L4|L4]; [right; left; lia|]]);
  (destruct (Z_lt_le_dec x l3) as [L5|L5]; [|destruct (Z_lt_le_dec x h3) as [L6|L6]; [right; right; lia|]]);
  exfalso; apply H; cbn [LF.outside]; repeat split; lia.
Qed.

Section F17.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* v1.9's opens_record body copies the first fragment's body into the frame object first.sroa.7 with
   `jal __asan_memcpy` at 0x823d4 (v1.8 saved two body bytes to spills instead), so this segment now has a
   callee. *)
Hypothesis HMC : ACPY.asan_memcpy_contract.
(* Every exit of seg_F17b reaches pc 0x823e8; discharge it through the official F18 entry cut of turn j. *)
Lemma to_exit_823e8 : forall j : nat,
  Hat B APIf ra (Inv_A823e8_at B APIf ra) j ->
  forall g regs mem md,
    Inv_A823e8_at B APIf ra g j (mkCfg (mkst regs (Z_to_bv 64 0x823e8) mem (seg_rom rsegs)) md) ->
    SR rsegs (mkCfg (mkst regs (Z_to_bv 64 0x823e8) mem (seg_rom rsegs)) md) (Post B APIf ra g).
Proof.
  intros j Hexit g regs mem md HI.
  pose proof (proj1 FF) as SEGS.
  pose proof (Hexit g _ HI) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

(* This file's run is the UL engine's evt, but a callee contract is a Lib.Exec.evt. SmLib.ul_entry moves a UL
   run into Lib; this is the other direction, which the memcpy call needs (the two msteps are the same relation
   over the same step, so each direction is the mirror induction of the other). *)
Lemma f17_lib_msteps : forall s s', LE.msteps rsegs s s' -> msteps rsegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH]; [apply msteps_refl|].
  eapply msteps_cons; [exact Hs | exact IH].
Qed.

Lemma f17_lib_evt : forall Q ms, LE.evt rsegs Q ms -> evt rsegs Q ms.
Proof. intros Q ms (ms' & H & HQ). exists ms'. split; [exact (f17_lib_msteps _ _ H) | exact HQ]. Qed.

(* The opens_record body's tail, 0x823c8 .. 0x823e8, over explicit register words (as F18 states its bcmp run):
   the memcpy of the first fragment's body into the frame object first.sroa.7 (dst [A+32] = fr + 2880, src
   s7 + 27 = phi + 27, len s9 = gg[26]), then `sd a0,104(s1)` = 1, `sd s9,112(s1)` = gg[26], then the join's
   `ld s9,176(s1)`. This is the file's ONLY use of a callee contract. The contract wants mem_inv, which the cut
   does not carry (it carries ro_agree), so the call runs through Tac_f17b.f17_mc, which takes the contract on
   MemNorm's normalized memory and carries the post back (image B's F17b does the same,
   proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F17b.v @ 3803efccea0). Every register is a parameter, so the caller
   passes `Sem.reg_get R0 k` for its register file R0 (as image B's call does); the four the run reads are pinned by
   equations. The destination's old bytes come from its stk fact (the frame is byte-backed, fra_stk), the copy and
   the callee's scratch are apart from the stack pointer by disjunctions (on FRA's real arm sp = fr). *)
Lemma f17_tail : forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 : word) (Fr : bvmap 5 word) fc (m : word -> option byte) A phi fr n spz lo (src : list byte),
  s1 = Z_to_bv 64 A -> s7 = Z_to_bv 64 phi -> s9 = Z_to_bv 64 n -> sp = Z_to_bv 64 spz ->
  bytes_at rsegs m (A + 32) (le8 (Z_to_bv 64 (fr + 2880))) ->
  bytes_at rsegs m (A + 176) (le8 (Z_to_bv 64 (fr + 64))) ->
  bytes_at rsegs m (phi + 27) src -> length src = Z.to_nat n -> 1 <= n <= 22 ->
  addressable m (phi + 27) n -> addressable m (fr + 2880) n ->
  stk rsegs m (fr + 2880) (fr + 2880 + n) ->
  (phi + 27 + n <= fr + 2880 \/ fr + 2880 + n <= phi + 27) ->
  app_mem (phi + 27 + n) -> app_mem (fr + 2880 + n) -> app_mem (phi + 34) -> app_mem (fr + 2887) ->
  (fr + 2880 + n <= spz - ACPY.ASAN_MEMCPY_K \/ spz <= fr + 2880) ->
  (phi + 27 + n <= spz - ACPY.ASAN_MEMCPY_K \/ spz <= phi + 27) ->
  stk rsegs m lo spz -> lo + ACPY.ASAN_MEMCPY_K <= spz -> HIGHMEM_BEG <= lo -> spz <= APPMEM_END ->
  AC.GT <= fr -> 0 <= phi ->
  ro_agree rsegs m -> asan_cells m -> shadow_rw m ->
  0 <= A -> A + 184 <= 2 ^ 64 ->
  wr_at rsegs m (A + 88) 32 -> fr + FRAME_BYTES <= A -> spz <= A ->
  evt rsegs
    (fun ms' => exists (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                       (mc : word -> option byte),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A) a0' a1' a2' a3' a4' a5' a6' a7'
                           s2 s3 s4 s5 s6 (Z_to_bv 64 phi) s8 (Z_to_bv 64 (fr + 64)) s10 s11 t3' t4' t5' t6')
                   Fr (Z_to_bv 64 0x823e8) fc None
                   (write_to_mem (write_to_mem mc (wa (A + 104)) (le8 (Z_to_bv 64 1)))
                      (wa (A + 112)) (le8 (Z_to_bv 64 n))) (seg_rom rsegs) /\
       LF.munch [(fr + 2880, fr + 2880 + n); (spz - ACPY.ASAN_MEMCPY_K, spz)] m mc /\
       LF.wmono rsegs m mc /\ ro_agree rsegs mc /\ stk rsegs mc lo spz /\ bytes_at rsegs mc (fr + 2880) src)
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           Fr (Z_to_bv 64 0x823c8) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A phi fr n spz lo src E1 E7 E9 Esp Hq32 Hq176 Hsrc Hlen Hn HadS HadD HstD Hdj HeaS HeaD HapS HapD
    HspD HspS HSTK HK HLO HSP HGT Hphi0 HRO HAC HSH HA0 HAtop HwA HfrA HspA.
  subst s1 s7 s9.
  pose proof (eq_refl : FRAME_BYTES = 3136) as HFB.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HR32 : ov_read_bytes rsegs m (wa (A + 32)) 8 = Some (le8 (Z_to_bv 64 (fr + 2880)))).
  { pose proof (bytes_at_ov_read rsegs m (A + 32) (le8 (Z_to_bv 64 (fr + 2880))) 0 8 Hq32
        ltac:(rewrite length_le8; cbn; lia)) as H.
    rewrite Z.add_0_r, skipn_O in H.
    rewrite firstn_all2 in H by (rewrite length_le8; cbn; lia). exact H. }
  step. (* 0x823c8: addi a1,s7,27 : a1 = phi + 27 *)
  step. (* 0x823cc: ld a0,32(s1) : a0 = fr + 2880 *)
  step. (* 0x823d0: mv a2,s9 : a2 = n *)
  step. (* 0x823d4: jal __asan_memcpy : ra = 0x823d8, pc = ASAN_MEMCPY *)
  clear HR32.
  (* the call: this run is the UL engine's, the contract a Lib.Exec run *)
  apply f17_lib_evt.
  eapply LE.evt_cut.
  { eapply (Tac_f17b.f17_mc HMC) with (D := fr + 2880) (S := phi + 27) (N := n) (spz := spz) (lo := lo)
      (src := src);
      [ reflexivity | reflexivity | reflexivity | exact Esp | lia | lia
      | unfold HIGHMEM_BEG in HLO; unfold AC.GT; lia | exact HSP | exact Hn | exact HRO | exact Hsrc | exact Hlen
      | exact HstD | exact Hdj | exact HadS | exact HadD | exact HeaS | exact HeaD
      | replace (phi + 27 + 7) with (phi + 34) by lia; exact HapS
      | replace (fr + 2880 + 7) with (fr + 2887) by lia; exact HapD
      | unfold ART.RT_HI; lia | exact HspD | exact HspS | exact HSTK | exact HK | exact HLO | exact HAC
      | exact HSH ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mc
              & E & MU & WM & RO' & ST' & Bsrc).
  subst ms'.
  (* back in this file's engine for the return block *)
  apply AW.ul_entry.
  (* the contract's post states the map with Lib's mkR; this file's engine normalizes only its own *)
  rewrite AW.mkR_ul.
  replace (LM.ret_pc (Z_to_bv 64 533464)) with (Z_to_bv 64 0x823d8)
    by (symmetry; apply LM.ret_pc_even; [clear; lia | reflexivity]).
  (* the spill cells stay writable across the call (wmono) and the stores *)
  pose proof (LF.wr_at_transport rsegs m mc (A + 88) 32 HwA WM) as HwC.
  (* [A + 176] (= fr + 64) is above sp and above the frame, so neither the copy nor the call's scratch touches
     it, and the two stores at [A + 104, A + 120) miss it *)
  assert (Hq176c : bytes_at rsegs mc (A + 176) (le8 (Z_to_bv 64 (fr + 64)))).
  { eapply fl_bytes; [exact Hq176 | exact MU |].
    rewrite length_le8. intros x Hx. cbn [LF.outside]. split; [lia|]. split; [lia | exact I]. }
  step. (* 0x823d8: addi a0,zero,1 *)
  assert (HS104 : store_ok rsegs mc (wa (A + 104)) 8 = true).
  { replace (A + 104) with (A + 88 + 16) by lia. apply (wr_at_store_ok rsegs mc (A + 88) 32 16 8 HwC); lia. }
  step. (* 0x823dc: sd a0,104(s1) *)
  match goal with |- evt _ _ (MS _ _ _ _ _ ?m2 _) =>
    assert (HS112 : store_ok rsegs m2 (wa (A + 112)) 8 = true) by
      (replace (A + 112) with (A + 88 + 24) by lia;
       apply (wr_at_store_ok rsegs m2 (A + 88) 32 24 8);
       [ repeat apply wr_at_write; exact HwC | lia | lia ]) end.
  step. (* 0x823e0: sd s9,112(s1) *)
  match goal with |- evt _ _ (MS _ _ _ _ _ ?m3 _) =>
    assert (HR176 : ov_read_bytes rsegs m3 (wa (A + 176)) 8 = Some (le8 (Z_to_bv 64 (fr + 64)))) by
      (assert (Hb2 : bytes_at rsegs m3 (A + 176) (le8 (Z_to_bv 64 (fr + 64))));
       [ repeat (apply (bytes_at_write_other rsegs);
                 [| lia | rewrite length_le8; lia | rewrite !length_le8; lia]); exact Hq176c
       | pose proof (bytes_at_ov_read rsegs m3 (A + 176) (le8 (Z_to_bv 64 (fr + 64))) 0 8 Hb2
             ltac:(rewrite length_le8; cbn; lia)) as H;
         rewrite Z.add_0_r, skipn_O in H;
         rewrite firstn_all2 in H by (rewrite length_le8; cbn; lia); exact H ]) end.
  step. (* 0x823e4: ld s9,176(s1) : s9 = fr + 64 *)
  apply evt_done.
  exists (Z_to_bv 64 0x823d8), (Z_to_bv 64 1), a1', a2', a3', a4', a5', a6', a7',
         t0', t1', t2', t3', t4', t5', t6', mc.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact RO'|]. split; [exact ST' | exact Bsrc].
Qed.
(* The bltz segment's only exit is pc 0x822a0; discharge it through the official split cut of turn j. *)
Lemma to_exit_822a0 : forall j : nat,
  Hat B APIf ra (Inv_A822a0_at B APIf ra) j ->
  forall g regs mem md,
    Inv_A822a0_at B APIf ra g j (mkCfg (mkst regs (Z_to_bv 64 0x822a0) mem (seg_rom rsegs)) md) ->
    SR rsegs (mkCfg (mkst regs (Z_to_bv 64 0x822a0) mem (seg_rom rsegs)) md) (Post B APIf ra g).
Proof.
  intros j Hexit g regs mem md HI.
  pose proof (proj1 FF) as SEGS.
  pose proof (Hexit g _ HI) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

(* The cut's spill base A (s1, pinned to FRA's spill base through the high-memory spill window): sp <= A, the frame
   is below it (fr + FRAME_BYTES <= A), and the spill window [A+88, A+120) is writable (inside FRA's
   window [S - SLOT_STACK, S), as S - 4096 < sp <= A and A + 416 <= S). *)
Lemma fra_spill : forall g fr hb regs mem md A,
  FRA B APIf ra g fr hb regs mem md ->
  getr regs (9%bv) = Z_to_bv 64 A ->
  (forall a, A + 88 <= a < A + 120 -> HIGHMEM_BEG <= a < APPMEM_END) ->
  AC.aspZ regs <= A /\ fr + FRAME_BYTES <= A /\ wr_at rsegs mem (A + 88) 32 /\
  g_S g - AF.SLOT_STACK <= A + 88 /\ A + 120 <= g_S g.
Proof.
  intros g fr hb regs mem md A HFRA Hs9 Happ.
  pose proof (eq_refl : FRAME_BYTES = 3136) as HFB. pose proof (eq_refl : FRAME_SHADOW = 392) as HFS.
  pose proof (Happ (A + 88) ltac:(lia)) as HAlo.
  pose proof (Happ (A + 119) ltac:(lia)) as HAhi.
  destruct HFRA as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  destruct Hwin as (Hw0 & Hw1 & Hwv).
  assert (EA : A0 = A).
  { assert (E9 : Z_to_bv 64 A = Z_to_bv 64 A0) by (rewrite <- Hs9; exact Hr9).
    apply (f_equal (bv_unsigned (n:=64))) in E9.
    clear - E9 HAlo HAhi Hw0 Hw1 HA416 Hspa HS4.
    unfold AF.SLOT_STACK, HIGHMEM_BEG, APPMEM_END in *.
    rewrite !MState.unsigned_lit in E9 by lia. lia. }
  subst A0.
  split; [rewrite Haspz; exact Hspa|].
  split; [exact Hfa|].
  split.
  { split; [unfold AF.SLOT_STACK in *; lia|]. split; [lia|].
    intros i Hi. exact (proj1 (Hwv (A + 88 + i) ltac:(unfold AF.SLOT_STACK in *; lia))). }
  split; [unfold AF.SLOT_STACK in *; lia | unfold AF.SLOT_STACK in *; lia].
Qed.

(* One instrumented 1-byte shadow read of an addressable byte X: the shadow byte b is readable at
   (X >> 3) + ASAN_K and passes the check (b = 0, or X mod 8 < b). *)
Lemma f17_shadow : forall m X, addressable m X 1 ->
  exists b : byte, ov_read_bytes rsegs m (wa (Z.shiftr X 3 + ASAN_K)) 1 = Some [b]
    /\ (bv_signed b = 0 \/ X mod 8 < bv_signed b) /\ -128 <= bv_signed b < 128.
Proof.
  intros m X HA. destruct (meta_byte m X 1 HA ltac:(lia)) as (b & RO & OK & IS).
  exists b. split; [| split].
  - pose proof (cells_at_read rsegs m (Z.shiftr X 3 + ASAN_K) [C1 b] 0%nat (C1 b) RO eq_refl) as H.
    cbn [csize cbytes] in H. rewrite Z.add_0_r in H. exact H.
  - destruct OK as [H|H]; [left; exact H | right; lia].
  - pose proof (sbyte_range b); lia.
Qed.

(* The image segments all end below the high application memory, so no high app address is in a segment. *)
Lemma f17_seg_high : forall z, HIGHMEM_BEG <= z -> find_segment rsegs z 1 = None.
Proof.
  intros z Hz. destruct (find_segment rsegs z 1) as [s|] eqn:E; [|reflexivity].
  exfalso. destruct (kb_find_segment rsegs z 1 s E) as (Hin & _ & Hhi).
  assert (Hall : forallb (fun s0 => Z.leb (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) HIGHMEM_BEG) rsegs = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall s Hin). apply Z.leb_le in Hall. lia.
Qed.

(* FRA survives one 8-byte store at A + off inside the first-fragment spill window [A+88, A+120) of the spill
   base A = s1 (high app memory, above the frame [fr, fr + FRAME_BYTES)), by the canonical rebuild sl_fr_cl: AH
   and stklo via the bundle's lw_store (the window is above stklo, so a_store_ok); ro_agree because no high app
   address is in an image segment; the low image, frame header, A+304 / A+16..32 spills, saved registers and the frame's
   shadow bytes are outside the store; the slot window stays readable and writable (stk_write); FSREC by
   fsrec_munch_lo (the store misses the low image and is at or above stklo). *)
Lemma fra_store1 : forall g fr hb regs mem md A off (w : word),
  FRA B APIf ra g fr hb regs mem md ->
  getr regs (9%bv) = Z_to_bv 64 A ->
  (A + 416 <= fr \/ fr + FRAME_BYTES <= A) ->
  (forall a, A + 88 <= a < A + 120 -> HIGHMEM_BEG <= a < APPMEM_END) ->
  88 <= off -> off + 8 <= 120 ->
  FRA B APIf ra g fr hb regs (write_to_mem mem (wa (A + off)) (le8 w)) md.
Proof.
  intros g fr hb regs mem md A off w HFRA Hs9 Hdisj Happ Ho1 Ho2.
  pose proof (eq_refl : FRAME_BYTES = 3136) as HFB. pose proof (eq_refl : FRAME_SHADOW = 392) as HFS.
  pose proof (fra_spill g fr hb regs mem md A HFRA Hs9 Happ) as (_ & _ & _ & HWlo & _).
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (_ & Hfrapp).
  pose proof (Happ (A + 88) ltac:(lia)) as HAlo.
  pose proof (Happ (A + 119) ltac:(lia)) as HAhi.
  assert (HAr : 0 <= A < 2 ^ 64) by (clear - HAlo HAhi; unfold HIGHMEM_BEG, APPMEM_END in *; lia).
  pose proof HFRA as HF0.
  destruct HF0 as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (Hsp0 : 0 <= g_S g - AF.SLOT_STACK) by (destruct Hwin as (H0 & _); exact H0).
  assert (EA : A0 = A).
  { assert (E9 : Z_to_bv 64 A = Z_to_bv 64 A0) by (rewrite <- Hs9; exact Hr9).
    apply (f_equal (bv_unsigned (n:=64))) in E9.
    unfold AF.SLOT_STACK, HIGHMEM_BEG, APPMEM_END in *.
    rewrite !MState.unsigned_lit in E9 by lia. lia. }
  subst A0.
  (* the cut's base A is the only value register 9 names in range *)
  assert (HA9 : forall A', getr regs 9 = Z_to_bv 64 A' -> 0 <= A' < 2 ^ 64 -> A' = A).
  { intros A' HA' HA'r.
    assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (rewrite <- HA'; exact Hs9).
    apply (f_equal (bv_unsigned (n:=64))) in E. rewrite !MState.unsigned_lit in E by lia. exact E. }
  remember (write_to_mem mem (wa (A + off)) (le8 w)) as mem' eqn:Emem.
  assert (MU : LF.munch [(A + off, A + off + 8)] mem mem').
  { subst mem'. apply LF.munch_write; [apply LF.munch_refl | | | ];
      try (rewrite length_le8); try (cbn [LF.inside]; left);
      unfold APPMEM_END, HIGHMEM_BEG in *; lia. }
  assert (WM : LF.wmono rsegs mem mem') by (subst mem'; apply LF.wmono_write, LF.wmono_refl).
  assert (HRO' : ro_agree rsegs mem').
  { intros a Ha.
    assert (Hout : LF.outside [(A + off, A + off + 8)] (bv_unsigned a)).
    { cbn [LF.outside]. split; [|exact I]. intros Hin.
      assert (Hn : find_segment rsegs (bv_unsigned a) 1 = None) by (apply f17_seg_high; lia).
      change ((match find_segment rsegs (bv_unsigned a) 1 with
               | Some seg => negb (seg_writable seg) | None => false end) = true) in Ha.
      rewrite Hn in Ha. discriminate Ha. }
    pose proof (Hro a Ha) as H.
    change ((match mem' a with Some b => Some b | None => seg_rom rsegs a end) = seg_rom rsegs a).
    rewrite (MU a Hout). exact H. }
  assert (HAW : all_app [(A + off, A + off + 8)]).
  { cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right. apply Happ. lia. }
  assert (HD : rt_disjoint [(A + off, A + off + 8)]).
  { unfold rt_disjoint.
    unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ,
      RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN, HIGHMEM_BEG in *.
    repeat split; left; lia. }
  assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
    ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
    mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia.
    cbn [LF.outside]. split; [|exact I]. intros [HH1 HH2]. apply Hns.
    unfold AC.a_store_ok. right; left. unfold AF.SLOT_STACK in *. lia. }
  assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  pose proof (lw_store (APIf rc) (hb ++ g_H g) mem mem' md HAH HstoreC HwmL) as LWS.
  pose proof (lws_ah _ _ _ _ _ LWS) as HAH'. pose proof (lws_lo _ _ _ _ _ LWS) as HSTK.
  apply (sl_fr_cl B APIf ra empty FF g fr hb regs regs mem mem' md [(A + off, A + off + 8)]
           HFRA MU WM HRO' HAW HD HAH' HSTK).
  - (* the low image [0, 6283264) *)
    intros x Hx. split; [unfold HIGHMEM_BEG in *; lia | exact I].
  - (* the frame header [fr, fr + 24) *)
    intros x Hx. split; [destruct Hdisj; lia | exact I].
  - (* the frame-base spill [A + 304, A + 312) *)
    intros A' HA' HA'r x Hx. rewrite (HA9 A' HA' HA'r) in Hx. split; [lia | exact I].
  - (* the saved registers [S - 104, S) *)
    intros x Hx. split; [lia | exact I].
  - (* the frame's shadow bytes: metadata addresses are below HIGHMEM_BEG <= A + 88 *)
    intros x Hx. split; [|exact I]. intros [HH1 HH2].
    assert (Hin : in_shadow x).
    { assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
      { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
      assert (Hinfr : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by (unfold FRAME_SHADOW, FRAME_BYTES in *; lia).
      pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Hfrapp _ Hinfr)) as His.
      replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
      unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia.
  - (* the fr reload and selector spills [A + 16, A + 32) *)
    intros A' HA' HA'r x Hx. rewrite (HA9 A' HA' HA'r) in Hx. split; [lia | exact I].
  - (* the slot window stays readable and writable *)
    subst mem'.
    refine (LF.stk_write rsegs mem (g_S g - AF.SLOT_STACK) (g_S g) (A + off) (le8 w) Hwin _ _);
      [unfold HIGHMEM_BEG in *; lia | rewrite length_le8; unfold APPMEM_END in *; lia].
  - (* the side-arm FakeStack record: the store misses the low image and is at or above stklo *)
    intro HF. eapply fsrec_munch_lo with (W := [(A + off, A + off + 8)]);
      [exact HF | exact HAH | exact MU | |].
    + intros x Hx. split; [unfold HIGHMEM_BEG in *; lia | exact I].
    + intros x _ _ Hxlo. split; [lia | exact I].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* ENT survives one 8-byte store inside the spill window [A+88, A+120): the window lies inside the entry-anchored
   slot window [S - SLOT_STACK, S) (fra_spill), so no byte ENT speaks of is written, and the stack bounds and the
   runtime's ownership of the image are kept by a_laws_store (the store is inside the stack, so a_store_ok). *)
Lemma ent_store1 : forall g fr hb regs mem md A off (w : word),
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  getr regs (9%bv) = Z_to_bv 64 A ->
  (forall a, A + 88 <= a < A + 120 -> HIGHMEM_BEG <= a < APPMEM_END) ->
  88 <= off -> off + 8 <= 120 ->
  ENT APIf g hb (write_to_mem mem (wa (A + off)) (le8 w)) md.
Proof.
  intros g fr hb regs mem md A off w HFRA HENT Hs9 Happ Ho1 Ho2.
  pose proof (eq_refl : FRAME_BYTES = 3136) as HFB. pose proof (eq_refl : FRAME_SHADOW = 392) as HFS.
  pose proof (fra_spill g fr hb regs mem md A HFRA Hs9 Happ) as (_ & _ & _ & HWlo & HWhi).
  pose proof (Happ (A + 88) ltac:(lia)) as HAlo.
  pose proof (Happ (A + 119) ltac:(lia)) as HAhi.
  pose proof HFRA as HFc.
  destruct HFc as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  remember (write_to_mem mem (wa (A + off)) (le8 w)) as mem' eqn:Emem.
  assert (MU : LF.munch [(A + off, A + off + 8)] mem mem').
  { subst mem'. apply LF.munch_write; [apply LF.munch_refl | | | ];
      try (rewrite length_le8); try (cbn [LF.inside]; left);
      unfold APPMEM_END, HIGHMEM_BEG in *; lia. }
  assert (WM : LF.wmono rsegs mem mem') by (subst mem'; apply LF.wmono_write, LF.wmono_refl).
  assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
    ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
    mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia.
    cbn [LF.outside]. split; [|exact I]. intros [HH1 HH2]. apply Hns.
    unfold AC.a_store_ok. right; left. unfold AF.SLOT_STACK in *. lia. }
  assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  pose proof (lw_store (APIf rc) (hb ++ g_H g) mem mem' md HAH HstoreC HwmL) as LWS.
  pose proof (lws_ah _ _ _ _ _ LWS) as HAH'. pose proof (lws_own _ _ _ _ _ LWS) as Hown'.
  pose proof (lws_lo _ _ _ _ _ LWS) as HSTK. pose proof (lws_hi _ _ _ _ _ LWS) as HSTKHI.
  (* ent_store is stated over UL.Frame.munch (Tac_slot imports UL.Tac); MU is Lib.Frame.munch, the same body, so
     it converts once W is given. *)
  eapply ent_store with (W := [(A + off, A + off + 8)]);
    [exact HENT | exact HFRA | exact MU | | exact HSTK | exact HSTKHI |].
  - intros x Hx. destruct (Z_le_gt_dec (A + off) x) as [D1|D1];
      [destruct (Z_lt_ge_dec x (A + off + 8)) as [D2|D2]|].
    + right; left. unfold AF.SLOT_STACK in *. lia.
    + left. hnf. split; [lia | exact I].
    + left. hnf. split; [lia | exact I].
  - intros a Hia Ho. exact (proj2 (Hown' a) Ho).
Qed.

(* A spill word [A' + off, A' + off + 8) (A' any base that s1 names) survives a run that keeps s1 and writes only
   W, when W misses that word. *)
Lemma spill_keep : forall (regs regs' : bvmap 5 word) (m m' : word -> option byte) (W : list (Z * Z)) off v,
  spill regs m off v -> getr regs' 9 = getr regs 9 -> LF.munch W m m' ->
  (forall A, rg regs 9 A -> forall x, A + off <= x < A + off + 8 -> LF.outside W x) ->
  spill regs' m' off v.
Proof.
  intros regs regs' m m' W off v (A & HA & Hq) E9 MU HW.
  exists A. split; [unfold rg in *; rewrite E9; exact HA|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
  rewrite length_le8. intros x Hx. exact (HW A HA x ltac:(lia)).
Qed.

(* A spill word survives a register change that keeps s1 (memory unchanged). *)
Lemma spill_regs : forall (regs regs' : bvmap 5 word) (m : word -> option byte) off v,
  spill regs m off v -> getr regs' 9 = getr regs 9 -> spill regs' m off v.
Proof.
  intros regs regs' m off v (A & HA & Hq) E9.
  exists A. split; [unfold rg in *; rewrite E9; exact HA | exact Hq].
Qed.

(* A spill cell of the base s1 = A, as a plain q64 at A + off: the spill's own base is the same A, since both
   are the value of register 9 and both are in range. *)
Lemma f17_spill_q : forall (regs : bvmap 5 word) m off v A,
  spill regs m off v -> rg regs 9 A -> 0 <= A -> 0 <= off -> A + off + 8 <= 2 ^ 64 ->
  q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & HA' & Hq) HA HA0 Hoff0 Hoff.
  (* the cell itself bounds the spill base: [A' + off, A' + off + 8) is addressable memory, and s1 fixes the
     base modulo 2^64, so the two agree: a wrapped base would put the cell outside memory *)
  assert (Hb : 0 <= A' + off /\ A' + off + 8 <= 2 ^ 64).
  { unfold q64 in Hq. apply bytes_at_bound in Hq. rewrite length_le8 in Hq. cbn [Z.of_nat] in Hq. lia. }
  assert (Hmod : A mod 2 ^ 64 = A' mod 2 ^ 64).
  { unfold rg in HA, HA'. rewrite HA in HA'.
    apply (f_equal (bv_unsigned (n:=64))) in HA'. rewrite !MState.unsigned_lit_wrap in HA'. exact HA'. }
  rewrite (Z.mod_small A (2 ^ 64)) in Hmod by lia.
  assert (A' = A) as ->; [|exact Hq].
  clear -Hmod Hb Hoff Hoff0 HA0. Z.div_mod_to_equations. lia.
Qed.

(* FLSI across a register change that keeps s1 (memory unchanged). *)
Lemma flsi_regs : forall g j fr (regs regs' : bvmap 5 word) m,
  FLSI g j fr regs m -> getr regs' 9 = getr regs 9 -> FLSI g j fr regs' m.
Proof.
  intros g j fr regs regs' m HFL E9.
  destruct HFL as (((H40 & H120 & H136 & H160 & H168 & H176 & H208 & H248p & Had & Hpb & Hph &
    P184 & P256 & P264 & P272 & P32) &
    H128 & Hstk & H144 & Had2691) &
    H216 & H224 & H248 & Hf1 &
    (Cs256 & Cs184 & Cs192 & Cs80 & Cs88 & Cs96 & Cs272 & Cs264 & Cad1 & Cad2 & Cs72 & Cs64 & Cs56 & Cs48)).
  unfold FLSI, FLSH, PRO, FLC.
  split.
  { split.
    { split; [exact (spill_regs regs regs' m _ _ H40 E9)|].
      split; [exact (spill_regs regs regs' m _ _ H120 E9)|].
      split; [exact (spill_regs regs regs' m _ _ H136 E9)|].
      split; [exact (spill_regs regs regs' m _ _ H160 E9)|].
      split; [exact (spill_regs regs regs' m _ _ H168 E9)|].
      split; [exact (spill_regs regs regs' m _ _ H176 E9)|].
      split; [exact (spill_regs regs regs' m _ _ H208 E9)|].
      split; [exact (spill_regs regs regs' m _ _ H248p E9)|].
      split; [exact Had|]. split; [exact Hpb|]. split; [exact Hph|].
      split; [exact (spill_regs regs regs' m _ _ P184 E9)|].
      split; [exact (spill_regs regs regs' m _ _ P256 E9)|].
      split; [exact (spill_regs regs regs' m _ _ P264 E9)|].
      split; [exact (spill_regs regs regs' m _ _ P272 E9) | exact (spill_regs regs regs' m _ _ P32 E9)]. }
    split; [exact (spill_regs regs regs' m _ _ H128 E9)|].
    split; [exact Hstk|].
    split; [exact (spill_regs regs regs' m _ _ H144 E9) | exact Had2691]. }
  split; [exact (spill_regs regs regs' m _ _ H216 E9)|].
  split; [exact (spill_regs regs regs' m _ _ H224 E9)|].
  split; [exact (spill_regs regs regs' m _ _ H248 E9)|]. split; [exact Hf1|].
  split; [exact (spill_regs regs regs' m _ _ Cs256 E9)|].
  split; [exact (spill_regs regs regs' m _ _ Cs184 E9)|].
  split; [exact (spill_regs regs regs' m _ _ Cs192 E9)|].
  split; [exact (spill_regs regs regs' m _ _ Cs80 E9)|].
  split; [exact (spill_regs regs regs' m _ _ Cs88 E9)|].
  split; [exact (spill_regs regs regs' m _ _ Cs96 E9)|].
  split; [exact (spill_regs regs regs' m _ _ Cs272 E9)|].
  split; [exact (spill_regs regs regs' m _ _ Cs264 E9)|].
  split; [exact Cad1|]. split; [exact Cad2|].
  split; [exact (spill_regs regs regs' m _ _ Cs72 E9)|].
  split; [exact (spill_regs regs regs' m _ _ Cs64 E9)|].
  split; [exact (spill_regs regs regs' m _ _ Cs56 E9) | exact (spill_regs regs regs' m _ _ Cs48 E9)].
Qed.

(* FLSI across a run that keeps s1 and writes W, where W misses every FLSI spill word (offsets 32 .. 272 other
   than the first-fragment spills 104 / 112, which FLSI does not name) and the input block, is app memory, and
   leaves the frame byte-backed (F18.flsi_keep asks for the whole frame outside W instead; the memcpy writes the
   frame object first.sroa.7 at fr + 2880, whose bytes the copy leaves readable). *)
Lemma flsi_cp : forall g j fr (regs regs' : bvmap 5 word) m m' (W : list (Z * Z)),
  FLSI g j fr regs m -> getr regs' 9 = getr regs 9 ->
  LF.munch W m m' -> all_app W -> LF.wmono rsegs m m' ->
  (forall A, rg regs 9 A -> forall off x, 32 <= off <= 272 -> (off + 8 <= 104 \/ 120 <= off) ->
     A + off <= x < A + off + 8 -> LF.outside W x) ->
  stk rsegs m' fr (fr + FRAME_BYTES) ->
  (forall x, g_p g <= x < g_p g + Z.of_nat (length (g_in g)) -> LF.outside W x) ->
  FLSI g j fr regs' m'.
Proof.
  intros g j fr regs regs' m m' W HFLSI E9 MU HAW WM HWsp Hstk' HWin.
  assert (HSK : forall off v, 32 <= off <= 272 -> (off + 8 <= 104 \/ 120 <= off) ->
                  spill regs m off v -> spill regs' m' off v).
  { intros off v Hoff Hd Hsp. apply (spill_keep regs regs' m m' W off v Hsp E9 MU).
    intros A HA x Hx. exact (HWsp A HA off x Hoff Hd Hx). }
  unfold FLSI, FLSH, PRO, f1_IN, FLC in HFLSI |- *.
  destruct HFLSI as (((Fs40 & Fs120 & Fs136 & Fs160 & Fs168 & Fs176 & Fs208 & Fs248p & Fad & Fpb & Fph &
                       P184 & P256 & P264 & P272 & P32) &
                      Fs128 & Fstk & Fs144 & Fad2691) &
                     Fs216 & Fs224 & Fs248 & (Finp & Finad & Finb) &
                     (Cs256 & Cs184 & Cs192 & Cs80 & Cs88 & Cs96 & Cs272 & Cs264 & Cad1 & Cad2 &
                      Cs72 & Cs64 & Cs56 & Cs48)).
  split.
  { split.
    { split; [exact (HSK 40 _ ltac:(lia) ltac:(lia) Fs40)|].
      split; [exact (HSK 120 _ ltac:(lia) ltac:(lia) Fs120)|].
      split; [exact (HSK 136 _ ltac:(lia) ltac:(lia) Fs136)|].
      split; [exact (HSK 160 _ ltac:(lia) ltac:(lia) Fs160)|].
      split; [exact (HSK 168 _ ltac:(lia) ltac:(lia) Fs168)|].
      split; [exact (HSK 176 _ ltac:(lia) ltac:(lia) Fs176)|].
      split; [exact (HSK 208 _ ltac:(lia) ltac:(lia) Fs208)|].
      split; [exact (HSK 248 _ ltac:(lia) ltac:(lia) Fs248p)|].
      split; [eapply sl_addr_keep; [exact Fad | exact MU | exact HAW]|].
      split; [apply (fl_bytes W m m' (g_p g) (g_in g) Fpb MU); exact HWin|].
      split.
      { intros Hn. destruct (Fph Hn) as (Fin & Fad2). split; [exact Fin|].
        eapply sl_addr_keep; [exact Fad2 | exact MU | exact HAW]. }
      split; [exact (HSK 184 _ ltac:(lia) ltac:(lia) P184)|].
      split; [exact (HSK 256 _ ltac:(lia) ltac:(lia) P256)|].
      split; [exact (HSK 264 _ ltac:(lia) ltac:(lia) P264)|].
      split; [exact (HSK 272 _ ltac:(lia) ltac:(lia) P272) | exact (HSK 32 _ ltac:(lia) ltac:(lia) P32)]. }
    split; [exact (HSK 128 _ ltac:(lia) ltac:(lia) Fs128)|].
    split; [exact Hstk'|].
    split; [exact (HSK 144 _ ltac:(lia) ltac:(lia) Fs144)|].
    eapply sl_addr_keep; [exact Fad2691 | exact MU | exact HAW]. }
  split; [exact (HSK 216 _ ltac:(lia) ltac:(lia) Fs216)|].
  split; [exact (HSK 224 _ ltac:(lia) ltac:(lia) Fs224)|].
  split; [exact (HSK 248 _ ltac:(lia) ltac:(lia) Fs248)|].
  split.
  { split; [exact Finp|].
    split; [eapply sl_addr_keep; [exact Finad | exact MU | exact HAW]|].
    apply (fl_bytes W m m' (g_p g) (g_in g) Finb MU). exact HWin. }
  split; [exact (HSK 256 _ ltac:(lia) ltac:(lia) Cs256)|].
  split; [exact (HSK 184 _ ltac:(lia) ltac:(lia) Cs184)|].
  split; [exact (HSK 192 _ ltac:(lia) ltac:(lia) Cs192)|].
  split; [exact (HSK 80 _ ltac:(lia) ltac:(lia) Cs80)|].
  split; [exact (HSK 88 _ ltac:(lia) ltac:(lia) Cs88)|].
  split; [exact (HSK 96 _ ltac:(lia) ltac:(lia) Cs96)|].
  split; [exact (HSK 272 _ ltac:(lia) ltac:(lia) Cs272)|].
  split; [exact (HSK 264 _ ltac:(lia) ltac:(lia) Cs264)|].
  split; [eapply sl_addr_keep; [exact Cad1 | exact MU | exact HAW]|].
  split; [eapply sl_addr_keep; [exact Cad2 | exact MU | exact HAW]|].
  split; [exact (HSK 72 _ ltac:(lia) ltac:(lia) Cs72)|].
  split; [exact (HSK 64 _ ltac:(lia) ltac:(lia) Cs64)|].
  split; [exact (HSK 56 _ ltac:(lia) ltac:(lia) Cs56) | exact (HSK 48 _ ltac:(lia) ltac:(lia) Cs48)].
Qed.

(* Two values of s1, one in range: the other is the same or a whole 2^64 away. *)
Lemma f17_rg9_wrap : forall (regs : bvmap 5 word) A A',
  rg regs 9 A -> 0 <= A < 2 ^ 64 -> rg regs 9 A' -> A' = A \/ A' <= A - 2 ^ 64 \/ A + 2 ^ 64 <= A'.
Proof.
  intros regs A A' HA HAr HA'.
  assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (unfold rg in *; rewrite <- HA'; exact HA).
  apply (f_equal (bv_unsigned (n:=64))) in E.
  rewrite (MState.unsigned_lit A) in E by exact HAr. rewrite MState.unsigned_lit_wrap in E.
  pose proof (Z.div_mod A' (2 ^ 64) ltac:(lia)) as DM. rewrite E in DM.
  remember (A' / 2 ^ 64) as k eqn:Ek. clear Ek.
  destruct (Z.lt_trichotomy k 0) as [Hk|[Hk|Hk]]; [right; left | left | right; right]; lia.
Qed.

(* A byte of a live heap block is below stklo and is not a frame byte (Seg/F29.v fra_blk, with the stklo bound):
   blocks end at or below stklo (a_laws_blocks); on the real arm the frame is at or above stklo, on the side arm it
   is FakeStack memory, which no block byte is. *)
Lemma f17_blk_out : forall g fr hb regs mem md p n x, FRA B APIf ra g fr hb regs mem md ->
  In (p, n) (hb ++ g_H g) -> p <= x < p + n ->
  x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ ~ (fr <= x < fr + FRAME_BYTES).
Proof.
  intros g fr hb regs mem md p n x HFRA Hin Hx.
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (lw_blocks (APIf rc) (hb ++ g_H g) mem md p n HAH Hin) as LB.
  pose proof (lwb_end _ _ _ _ _ _ LB) as Hend.
  split; [lia|].
  intro Hfx. destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
  - pose proof (Hreal x Hfx). lia.
  - exact (lwb_byte_not_fs _ _ _ _ _ _ LB x Hx (Hfs x Hfx)).
Qed.

(* FRA and ENT across the memcpy (Seg/P4.v seg_P4's transport of its memset, with the destination the frame
   object first.sroa.7 at fr + 2880 and n <= 35 bytes): the write set W = [fr + 2880, fr + 2880 + n) u
   [sp - K, sp) is app memory above the image; AH and the stack bounds by lw_store on the real arm (both pieces are
   at or above stklo) and by lw_fs_store on the side arm (the destination is FakeStack memory, whose metadata W
   misses: Tac_fs.a_fs_ok_pres); the entry-anchored window and the frame stay byte-backed (outside W from mem, the
   destination from the copy's readable bytes, the scratch from the call's stack window); FSREC by
   fra_fsrec_stklo; then the canonical rebuild sl_fr_cl, and ENT by ent_store. *)
Lemma f17_cp_fra : forall g fr hb regs mem mc md n,
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md -> 0 <= n <= 35 ->
  LF.munch [(fr + 2880, fr + 2880 + n); (AC.aspZ regs - ACPY.ASAN_MEMCPY_K, AC.aspZ regs)] mem mc ->
  LF.wmono rsegs mem mc -> ro_agree rsegs mc ->
  stk rsegs mc (AC.aspZ regs - FN_STACK) (AC.aspZ regs) ->
  (forall x, fr + 2880 <= x < fr + 2880 + n -> exists b, mrd rsegs mc (wa x) = Some b) ->
  FRA B APIf ra g fr hb regs mc md /\ ENT APIf g hb mc md /\ stk rsegs mc fr (fr + FRAME_BYTES).
Proof.
  intros g fr hb regs mem mc md n HFRA HENT Hn MU WM HRO' STk HDst.
  pose proof (eq_refl : FRAME_BYTES = 3136) as HFB. pose proof (eq_refl : FRAME_SHADOW = 392) as HFS.
  pose proof HFRA as HF0.
  destruct HF0 as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2f & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9f & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  rewrite Haspz in MU, STk.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH) as Hstkhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HKv : ACPY.ASAN_MEMCPY_K = 2224) by reflexivity.
  assert (HHB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAE : APPMEM_END = 0x800000000000) by reflexivity.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HFN : FN_STACK = AF.SLOT_STACK - 4096) by reflexivity.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGT & Happfr).
  pose proof (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hfrsp & _ & _ & _).
  assert (Hapart : fr + FRAME_BYTES <= sp - ACPY.ASAN_MEMCPY_K \/ sp <= fr).
  { destruct (Hfrsp ACPY.ASAN_MEMCPY_K ltac:(unfold FN_STACK; lia)) as [H|H]; rewrite Haspz in H;
      [left | right]; exact H. }
  assert (HA0r : 0 <= A0 < 2 ^ 64) by lia.
  (* the cut's base A0 is the only value register 9 names in range *)
  assert (HA9 : forall A', getr regs 9 = Z_to_bv 64 A' -> 0 <= A' < 2 ^ 64 -> A' = A0).
  { intros A' HA' HA'r.
    assert (E : Z_to_bv 64 A' = Z_to_bv 64 A0) by (rewrite <- HA'; exact Hr9f).
    apply (f_equal (bv_unsigned (n:=64))) in E. rewrite !MState.unsigned_lit in E by lia. exact E. }
  assert (HAW : all_app [(fr + 2880, fr + 2880 + n); (sp - ACPY.ASAN_MEMCPY_K, sp)]).
  { cbn [all_app]. split; [intros a Ha; apply Happfr; lia|]. split; [|exact I].
    intros a Ha. unfold app_mem. right. lia. }
  assert (HD : rt_disjoint [(fr + 2880, fr + 2880 + n); (sp - ACPY.ASAN_MEMCPY_K, sp)]).
  { unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK,
      RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN.
    cbn [disjoint_from]. repeat split; first [left; lia | right; lia | exact I]. }
  (* the frame stays byte-backed: the destination's bytes are readable after the copy *)
  assert (HDstk : stk rsegs mc fr (fr + FRAME_BYTES)).
  { apply (fl_stk _ mem mc fr (fr + FRAME_BYTES) (fra_stk B APIf ra g fr hb regs mem md HFRA) MU WM).
    intros x Hx. destruct (f17_cases (fr + 2880) n sp ACPY.ASAN_MEMCPY_K x) as [Ho|[Hd|Hsc]].
    - left. exact Ho.
    - right. exact (HDst x Hd).
    - exfalso. destruct Hapart; lia. }
  (* AH, the runtime's ownership and the stack bounds across the copy, by frame arm *)
  assert (Hwrit : forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs mc x)
    by (intros x Hx Hwx; exact (WM (Z_to_bv 64 x) Hwx)).
  assert (LWS : lw_sto (APIf rc) (hb ++ g_H g) mem mc md).
  { destruct Hloc as [[Hs50 [Hspfr Hreal]]|[Hs5fr [Hfsb [Hfs Hrec]]]].
    - (* real arm: the destination is a frame byte and the scratch a stack byte, both in [stklo, APPMEM_END) *)
      apply (lw_store (APIf rc) (hb ++ g_H g) mem mc md HAH); [|exact Hwrit].
      intros x Hx Hnok. apply MU. rewrite MState.unsigned_lit by exact Hx.
      destruct (f17_cases (fr + 2880) n sp ACPY.ASAN_MEMCPY_K x) as [Ho|[Hd|Hsc]]; [exact Ho| |].
      + exfalso. apply Hnok. right. left. specialize (Hreal x ltac:(lia)). lia.
      + exfalso. apply Hnok. right. left. lia.
    - (* side arm: the destination lies in the side stack FS, the scratch in [stklo, APPMEM_END) *)
      destruct (Hfs fr ltac:(lia)) as (FS & HFSr & HFSw & HFSlo & HFShi).
      destruct (lw_fs_place (APIf rc) (hb ++ g_H g) mem md FS HAH HFSw HFSr) as [HGTFS HFSend HFSmod HFSapp].
      pose proof (lw_fs_ok (APIf rc) (hb ++ g_H g) mem md FS HAH HFSw HFSr) as Hfsok0.
      pose proof (Hfsb FS HFSw HFSr) as HFSfr.
      assert (HinFS : forall a, fr <= a < fr + FRAME_BYTES -> FS <= a < FS + AC.FS_SIZE).
      { intros a Ha. destruct (Hfs a Ha) as (b & Hbr & Hbw & Hb1 & Hb2).
        pose proof (f17_wm_congr mem _ b FS Hbw HFSw) as X. rewrite !Z.mod_small in X by lia.
        subst b. lia. }
      (* every present byte stays present: outside W by munch, in W by the copy's bytes and the call's window *)
      assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                exists b, mbyte rsegs mc q = Some b).
      { intros q Hq (b & Hb).
        destruct (f17_cases (fr + 2880) n sp ACPY.ASAN_MEMCPY_K q) as [Ho|[Hd|Hsc]].
        - exists b. unfold mbyte in Hb |- *. rewrite MU; [exact Hb|].
          rewrite MState.unsigned_lit by exact Hq. exact Ho.
        - destruct (HDst q Hd) as (b' & Hb'). exists b'. unfold mbyte. unfold mrd, wa in Hb'. exact Hb'.
        - destruct STk as (_ & _ & HSs). destruct (HSs q ltac:(lia)) as (_ & b' & Hb').
          exists b'. unfold mbyte. unfold mrd, wa in Hb'. exact Hb'. }
      (* the side stack's metadata is below the frames and below stklo, so W misses it *)
      assert (Hmeta : forall q, Tac_fs.fs_meta FS q ->
                LF.outside [(fr + 2880, fr + 2880 + n); (sp - ACPY.ASAN_MEMCPY_K, sp)] q).
      { intros q Hq. pose proof (Tac_fs.fs_meta_below _ _ Hq) as Hqr. apply f17_out2; lia. }
      assert (Hfsok' : AC.a_fs_ok mc FS).
      { apply (Tac_fs.a_fs_ok_pres _ mem mc FS Hfsok0 MU Hwrit Hpres Hmeta); lia. }
      apply (lw_fs_store (APIf rc) (hb ++ g_H g) mem mc md FS HAH HFSw HFSr); [| exact Hwrit | exact Hfsok'].
      intros x Hx Hnok Hnfs Hnsh. apply MU. rewrite MState.unsigned_lit by exact Hx.
      destruct (f17_cases (fr + 2880) n sp ACPY.ASAN_MEMCPY_K x) as [Ho|[Hd|Hsc]]; [exact Ho| |].
      + exfalso. apply Hnfs. apply HinFS. lia.
      + exfalso. apply Hnok. right. left. lia. }
  pose proof (lws_ah _ _ _ _ _ LWS) as HAH'. pose proof (lws_own _ _ _ _ _ LWS) as Hown'.
  pose proof (lws_lo _ _ _ _ _ LWS) as HSTK'. pose proof (lws_hi _ _ _ _ _ LWS) as HSTKhi'.
  (* the entry-anchored slot window after the copy *)
  assert (HSTKwin : stk rsegs mc (g_S g - AF.SLOT_STACK) (g_S g)).
  { apply (fl_stk _ mem mc (g_S g - AF.SLOT_STACK) (g_S g) Hwin MU WM).
    intros x Hx. destruct (f17_cases (fr + 2880) n sp ACPY.ASAN_MEMCPY_K x) as [Ho|[Hd|Hsc]].
    - left. exact Ho.
    - right. exact (HDst x Hd).
    - right. destruct STk as (_ & _ & HSs). exact (proj2 (HSs x ltac:(lia))). }
  (* FSREC: W writes nothing below stklo outside the frame body *)
  assert (HRECK : FSREC fr mem -> FSREC fr mc).
  { intros Hrec0.
    eapply fra_fsrec_stklo;
      [exact HFRA
      | first [exact MU | exact (proj1 (fr_munch_ul _ _ _) MU) | exact (proj2 (fr_munch_ul _ _ _) MU)]
      | | exact Hrec0].
    intros x Hx Hnb.
    first [ apply f17_out2 | apply (proj2 (fr_outside_lib _ _)); apply f17_out2
          | apply (proj1 (fr_outside_lib _ _)); apply f17_out2 ]; lia. }
  assert (HFRAm : FRA B APIf ra g fr hb regs mc md).
  { apply (sl_fr_cl B APIf ra empty FF g fr hb regs regs mem mc md
             [(fr + 2880, fr + 2880 + n); (sp - ACPY.ASAN_MEMCPY_K, sp)] HFRA MU WM HRO' HAW HD HAH' HSTK').
    - (* the low image [0, 6283264) *)
      intros x Hx. split; [lia|]. split; [lia | exact I].
    - (* the frame header [fr, fr + 24) *)
      intros x Hx. split; [lia|]. split; [destruct Hapart; lia | exact I].
    - (* the frame-base spill [A + 304, A + 312) *)
      intros A' HA' HA'r x Hx. rewrite (HA9 A' HA' HA'r) in Hx. split; [lia|]. split; [lia | exact I].
    - (* the saved registers [S - 104, S) *)
      intros x Hx. split; [lia|]. split; [lia | exact I].
    - (* the frame's shadow bytes: shadow bytes are never app memory, W is *)
      intros x Hx.
      assert (Hin : in_shadow x).
      { assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
        { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
        assert (Hinfr : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES)
          by (unfold FRAME_SHADOW, FRAME_BYTES in *; lia).
        pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happfr _ Hinfr)) as His.
        replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
        unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
      split; [|split; [|exact I]]; intros [HH1 HH2].
      + pose proof (Happfr x ltac:(lia)) as Hap. unfold app_mem in Hap. unfold in_shadow in Hin.
        unfold LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG in Hap, Hin. lia.
      + unfold in_shadow in Hin. unfold LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG in Hin. lia.
    - (* the fr reload and selector spills [A + 16, A + 32) *)
      intros A' HA' HA'r x Hx. rewrite (HA9 A' HA' HA'r) in Hx. split; [lia|]. split; [lia | exact I].
    - exact HSTKwin.
    - exact HRECK.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity. }
  (* ENT: the copy writes only the frame body and the slot window below S (ent_store) *)
  assert (HENTm : ENT APIf g hb mc md).
  { eapply ent_store;
      [exact HENT | exact HFRA
      | first [exact MU | exact (proj1 (fr_munch_ul _ _ _) MU) | exact (proj2 (fr_munch_ul _ _ _) MU)]
      | | exact HSTK' | exact HSTKhi' | exact (fun a _ Ho => proj2 (Hown' a) Ho)].
    intros x Hx. destruct (f17_cases (fr + 2880) n sp ACPY.ASAN_MEMCPY_K x) as [Ho|[Hd|Hsc]].
    - left. first [exact Ho | exact (proj2 (fr_outside_lib _ _) Ho) | exact (proj1 (fr_outside_lib _ _) Ho)].
    - right. right. left. lia.
    - right. left. lia. }
  split; [exact HFRAm|]. split; [exact HENTm | exact HDstk].
Qed.

(* A value with bit 0 set is nonzero, also after wrapping to 64 bits. *)
Lemma f17_lor_odd : forall a b, (Z.testbit a 0 = true \/ Z.testbit b 0 = true) ->
  Z.lor a b <> 0 /\ Z.lor a b mod 2 ^ 64 <> 0.
Proof.
  intros a b Hab.
  assert (T : Z.testbit (Z.lor a b) 0 = true).
  { rewrite Z.lor_spec. destruct Hab as [H|H]; rewrite H; [reflexivity | apply Bool.orb_true_r]. }
  split; intro H.
  - rewrite H in T. change (Z.testbit 0 0) with false in T. discriminate T.
  - rewrite <- (Z.mod_pow2_bits_low (Z.lor a b) 64 0) in T by lia. rewrite H in T.
    change (Z.testbit 0 0) with false in T. discriminate T.
Qed.

(* v1.9's guard is `bnez a0, 0x823e4` at 0x822a8: with a0 = 1 | s4 (the short arm's [s1+232] = 1 or'ed with s4,
   or a nonzero s4) the branch is TAKEN, out of the body and into the join. *)
Ltac or1_bnez_tk :=
  match goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with true by
        ((match goal with |- true = _ => symmetry | _ => idtac end);
         rewrite ?Bool.negb_true_iff;
         try unfold bv_eqb; apply Z.eqb_neq;
         rewrite ?bv_or_unsigned, ?MState.unsigned_lit_wrap; rewrite ?Z.mod_0_l by lia;
         first [ refine (proj2 (f17_lor_odd _ _ _)); left; reflexivity
               | refine (proj2 (f17_lor_odd _ _ _)); right; reflexivity
               | refine (proj1 (f17_lor_odd _ _ _)); left; reflexivity
               | refine (proj1 (f17_lor_odd _ _ _)); right; reflexivity ])
  end; cbv_concl_iota.

(* Discharge a `getr R k = getr regs k` goal where R is a bvmap_set chain over mkR_of regs. *)
Ltac regeq :=
  simp_regs;
  first [ reflexivity
        | symmetry; eassumption
        | symmetry; apply Regs6ss.mkR_of_eqv; reflexivity
        | eassumption
        | apply Regs6ss.mkR_of_eqv; reflexivity ].
(* Finish an exit arc of the opens_record body into the segment postcondition K. v1.9 moved `ld s9,176(s1)` out
   of the arms into the join 0x823e4, which every arc reaches, so each arc takes that load itself and lands at
   0x823e8; the arc names the f_opens test that failed, so nothing is searched for in the context. *)
Ltac exit_K_step fop Hb :=
  step;
  apply evt_done; hnf; do 3 eexists; split; [reflexivity|];
  split; [reflexivity|];
  do 13 (split; [regeq|]);
  left; split; [reflexivity | exact (fop _ _ Hb)].
(* The instrumented shadow check bnez convergence: both the fast (shadow byte = 0) and the slow
   (partial granule; the slow block's `andi; bge errpath` is shown not taken from X mod 8 < b) paths
   rejoin at `cont`; generalise the scratch register. Leaves the continuation goal `forall rr, evt .. cont`. *)
Ltac converge scratch Xe b OK BD :=
  match goal with
  | |- evt ?segs ?Q (MS ?R ?F (if _ then _ else ?cont) ?fc ?rv ?m ?ro) =>
      let Gc := fresh "Gc" in
      enough (Gc : forall rr, evt segs Q (MS (bvmap_set scratch rr R) F cont fc rv m ro)) by
        (let K0 := fresh "K0" in
         destruct (Z.eqb_spec (bv_signed b) 0) as [K0|K0];
         [ match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with false by (unfold sxb; rewrite K0; vm_compute; reflexivity) end;
           cbv_concl_iota;
           match goal with |- evt _ _ (MS ?R2 _ _ _ _ _ _) => exact (Gc (Sem.reg_get R2 scratch)) end
         | let Hmb := fresh "Hmb" in let Hlt := fresh "Hlt" in
           pose proof (Z.mod_pos_bound Xe 8 ltac:(lia)) as Hmb;
           assert (Hlt : Xe mod 8 < bv_signed b) by (destruct OK as [HH|HH]; [exfalso; apply K0; exact HH | lia]);
           match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with true by (unfold sxb; rewrite bv_eqb_lit by lia;
               replace (bv_signed b =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity) end;
           cbv_concl_iota; step; step;
           match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with false by (rewrite (unsigned_lit Xe) by (unfold APPMEM_END in *; lia);
               rewrite land7 by lia; rewrite lts_sxb by lia;
               replace (Xe mod 8 <? bv_signed b) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity) end;
           cbv_concl_iota; step;
           match goal with |- evt _ _ (MS ?R2 _ _ _ _ _ _) => exact (Gc (Sem.reg_get R2 scratch)) end ])
  end; intro.

(* Shadow check of the byte phi+kk into a1 (scratch a2), after the caller set a0 = phi+kk. *)
Ltac shadowcheck phi mem Haddr kk :=
  step; step;
  rewrite (unsigned_lit (phi + kk)) by (unfold APPMEM_END in *; lia);
  let Had := fresh "Had" in let b := fresh "b" in let HRsh := fresh "HRsh" in
  let OK := fresh "OK" in let BD := fresh "BD" in
  assert (Had : addressable mem (phi + kk) 1) by (apply (addressable_sub mem phi 50 kk 1 Haddr); lia);
  destruct (f17_shadow mem (phi + kk) Had) as (b & HRsh & OK & BD);
  step; step; converge (Z_to_bv 5 12) (phi + kk) b OK BD.

(* The same convergence for a slow block of the other shape, `andi; blt back` (check 9 at 0x823b4 -> 0x82af8):
   the blt is TAKEN from X mod 8 < b, straight back to `cont`, with no `j`. *)
Ltac converge_blt scratch Xe b OK BD :=
  match goal with
  | |- evt ?segs ?Q (MS ?R ?F (if _ then _ else ?cont) ?fc ?rv ?m ?ro) =>
      let Gc := fresh "Gc" in
      enough (Gc : forall rr, evt segs Q (MS (bvmap_set scratch rr R) F cont fc rv m ro)) by
        (let K0 := fresh "K0" in
         destruct (Z.eqb_spec (bv_signed b) 0) as [K0|K0];
         [ match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with false by (unfold sxb; rewrite K0; vm_compute; reflexivity) end;
           cbv_concl_iota;
           match goal with |- evt _ _ (MS ?R2 _ _ _ _ _ _) => exact (Gc (Sem.reg_get R2 scratch)) end
         | let Hmb := fresh "Hmb" in let Hlt := fresh "Hlt" in
           pose proof (Z.mod_pos_bound Xe 8 ltac:(lia)) as Hmb;
           assert (Hlt : Xe mod 8 < bv_signed b) by (destruct OK as [HH|HH]; [exfalso; apply K0; exact HH | lia]);
           match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with true by (unfold sxb; rewrite bv_eqb_lit by lia;
               replace (bv_signed b =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity) end;
           cbv_concl_iota; step; step;
           match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with true by (rewrite (unsigned_lit Xe) by (unfold APPMEM_END in *; lia);
               rewrite land7 by lia; rewrite lts_sxb by lia;
               replace (Xe mod 8 <? bv_signed b) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity) end;
           cbv_concl_iota;
           match goal with |- evt _ _ (MS ?R2 _ _ _ _ _ _) => exact (Gc (Sem.reg_get R2 scratch)) end ])
  end; intro.

Ltac shadowcheck_blt phi mem Haddr kk :=
  step; step;
  rewrite (unsigned_lit (phi + kk)) by (unfold APPMEM_END in *; lia);
  let Had := fresh "Had" in let b := fresh "b" in let HRsh := fresh "HRsh" in
  let OK := fresh "OK" in let BD := fresh "BD" in
  assert (Had : addressable mem (phi + kk) 1) by (apply (addressable_sub mem phi 50 kk 1 Haddr); lia);
  destruct (f17_shadow mem (phi + kk) Had) as (b & HRsh & OK & BD);
  step; step; converge_blt (Z_to_bv 5 12) (phi + kk) b OK BD.

(* Drop the 1-byte read facts and shadow-check outcomes of a finished check (image B's F17b.v clr1): a load step
   tries every read fact of its width in the context, so keeping them made each later check take twice as long
   as the one before it (measured: 2, 4, 8, 19, 44 s for checks 2 .. 6 of the draft, which did not finish). *)
Ltac clr1 := repeat match goal with
  | H : ov_read_bytes _ _ _ 1 = _ |- _ => clear H
  | H : bv_signed _ = 0 \/ _ |- _ => clear H
  end.

(* Frame byte phi+kk read into a0, li a1, bne a0,a1,exit. The split is made on the MODEL test `bat L kk =? cc`,
   which is a boolean over the record bytes, and the branch condition is then replaced by it (f17_bne_val).
   Splitting on the condition itself would abstract the whole evt goal twice per check, so the nine checks
   would carry 2^9 copies of it; this keeps one. *)
Ltac frbc phi mem L Hrbb kk cc Hb fop :=
  let Hrr := fresh "Hrr" in let HH := fresh "HH" in
  assert (Hrr : ov_read_bytes rsegs mem (wa (phi + kk)) 1 = Some (firstn 1 (skipn (Z.to_nat kk) L))) by
    (pose proof (bytes_at_ov_read rsegs mem phi L (Z.to_nat kk) 1 Hrbb ltac:(lia)) as HH;
     replace (phi + Z.of_nat (Z.to_nat kk)) with (phi + kk) in HH by lia; exact HH);
  step; step; step;
  destruct (RF.bat L kk =? cc) eqn:Hb;
  [ match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false by
        (symmetry; rewrite (f17_bne_val L kk cc ltac:(lia) ltac:(lia) ltac:(lia)), Hb; reflexivity) end;
    cbv_concl_iota
  | match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with true by
        (symmetry; rewrite (f17_bne_val L kk cc ltac:(lia) ltac:(lia) ltac:(lia)), Hb; reflexivity) end;
    cbv_concl_iota; exit_K_step fop Hb ].

(* Frame byte phi+kk read into a0, bnez a0,exit (the constant is 0). *)
Ltac frbnzc phi mem L Hrbb kk Hb fop :=
  let Hrr := fresh "Hrr" in let HH := fresh "HH" in
  assert (Hrr : ov_read_bytes rsegs mem (wa (phi + kk)) 1 = Some (firstn 1 (skipn (Z.to_nat kk) L))) by
    (pose proof (bytes_at_ov_read rsegs mem phi L (Z.to_nat kk) 1 Hrbb ltac:(lia)) as HH;
     replace (phi + Z.of_nat (Z.to_nat kk)) with (phi + kk) in HH by lia; exact HH);
  step; step;
  destruct (RF.bat L kk =? 0) eqn:Hb;
  [ match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false by
        (symmetry; rewrite (f17_bne_val L kk 0 ltac:(lia) ltac:(lia) ltac:(lia)), Hb; reflexivity) end;
    cbv_concl_iota
  | match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with true by
        (symmetry; rewrite (f17_bne_val L kk 0 ltac:(lia) ltac:(lia) ltac:(lia)), Hb; reflexivity) end;
    cbv_concl_iota; exit_K_step fop Hb ].

(* The opens_record body proper, from the split cut 0x822a0 to the F18 entry cut 0x823e8. v1.9's guard
   `bnez a0, 0x823e4` at 0x822a8 LEAVES the body when a0 = [s1+232] | s4 is nonzero; the body at 0x822ac runs
   only when it is 0. On the short arm (t_big false) [s1+232] = 1, so the branch is taken. On the long arm
   (t_big true, so 50 <= len_j and the guarded record facts hold) both arms are possible: the body makes the nine
   instrumented checks (each a load of the metadata byte (X >> 3) + 0x7fff8000 of a record byte X and a compare;
   the report call is not reached), the record-field compares, and on its fall-through the memcpy of the body
   into fr + 2880 (0x823d4) and the two spill stores [s1+104] = 1 and [s1+112] = gg[26]. Every arm meets the
   join 0x823e4 `ld s9,176(s1)`, so every exit has s9 = fr + 64 and keeps s2. *)
Lemma seg_F17b : forall j : nat,
  Hat B APIf ra (Inv_A823e8_at B APIf ra) j -> Hat B APIf ra (Inv_A822a0_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof (eq_refl : FRAME_BYTES = 3136) as HFB. pose proof (eq_refl : FRAME_SHADOW = 392) as HFS.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hn & Hj & HHB & HFLSI & HLK &
    Hs7 & Hs22 & Hrec40 & (A & Hs1 & Hv232 & Hb192 & Hq136 & Hq120 & Hq176 & Happ & Hw240 & Hs24 & Hrecg &
    HL12) & Hs18 & Hrecb & H152 & H280 & HIFS3 & Hs20).
  subst c.
  rewrite SEGS.
  (* FRA's spill-base / frame placement and the writable spill window (fra_spill). *)
  assert (Hs9g : getr regs (9%bv) = Z_to_bv 64 A) by (unfold rg in Hs1; exact Hs1).
  destruct (fra_spill g fr _ regs mem md A HFRA Hs9g Happ) as (HspA & HfrA & Hwr & HWlo & HWhi).
  assert (Hdisj : A + 416 <= fr \/ fr + FRAME_BYTES <= A) by (right; exact HfrA).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A2 & sp & s5v & HRT & HAH & Hro & Hsn & Hhalt & Hrest).
  eapply (sl_run regs (Z_to_bv 64 0x822a0) mem md
    (fun R pc' mem' =>
       pc' = Z_to_bv 64 0x823e8 /\
       Sem.reg_get R 2 = Sem.reg_get regs 2 /\ Sem.reg_get R 3 = Sem.reg_get regs 3 /\ Sem.reg_get R 4 = Sem.reg_get regs 4 /\
       Sem.reg_get R 8 = Sem.reg_get regs 8 /\ Sem.reg_get R 9 = Sem.reg_get regs 9 /\ Sem.reg_get R 19 = Sem.reg_get regs 19 /\
       Sem.reg_get R 26 = Sem.reg_get regs 26 /\ Sem.reg_get R 21 = Sem.reg_get regs 21 /\ Sem.reg_get R 23 = Sem.reg_get regs 23 /\
       Sem.reg_get R 24 = Sem.reg_get regs 24 /\ Sem.reg_get R 22 = Sem.reg_get regs 22 /\
       Sem.reg_get R 18 = Sem.reg_get regs 18 /\ Sem.reg_get R 25 = Z_to_bv 64 (fr + 64) /\
       (* The memory changes exactly on the arm where the record opens (f_opens true): the memcpy at 0x823d4
          writes the first fragment's body into first.sroa.7 = fr + 2880 (and its own stack scratch), then
          0x823dc / 0x823e0 store have = 1 and n = gg[26] into [A + 104] / [A + 112]. On every other arm the
          memory is untouched. The intermediate memory mc is the call's; what the continuation needs of it is
          named here (the copy's write set, ro_agree, the sp-anchored stack window, the copied bytes), since the
          call's own post is not available past the run. *)
       ((mem' = mem /\ f_opens (flen g j) (t_g (g_in g) j) = false) \/
        (f_opens (flen g j) (t_g (g_in g) j) = true /\
         exists mc : word -> option byte,
           LF.munch [(fr + 2880, fr + 2880 + RF.bat (t_g (g_in g) j) 26);
                     (AC.aspZ regs - ACPY.ASAN_MEMCPY_K, AC.aspZ regs)] mem mc /\
           LF.wmono rsegs mem mc /\ ro_agree rsegs mc /\
           stk rsegs mc (AC.aspZ regs - FN_STACK) (AC.aspZ regs) /\
           bytes_at rsegs mc (fr + 2880)
             (firstn (Z.to_nat (RF.bat (t_g (g_in g) j) 26)) (skipn 27 (t_g (g_in g) j))) /\
           mem' = write_to_mem (write_to_mem mc (wa (A + 104)) (le8 (Z_to_bv 64 1)))
                    (wa (A + 112)) (le8 (Z_to_bv 64 (RF.bat (t_g (g_in g) j) 26))))))
    (Post B APIf ra g)).
  - exact Hhalt.
  - (* stepping the opens_record body from 0x822a0 *)
    pose proof Hq176 as Hv176b. unfold q64 in Hv176b.
    (* v1.9's memcpy destination pointer is PRO's new spill [A + 32] = fr + 2880 (the frame object
       first.sroa.7); take it out of FLSI before the stepping context drops it. *)
    assert (HAr0 : HIGHMEM_BEG <= A + 88 /\ A + 120 <= APPMEM_END)
      by (split; [exact (proj1 (Happ (A + 88) ltac:(lia)))
                 | pose proof (Happ (A + 119) ltac:(lia)) as Hap; lia]).
    assert (Hq32 : q64 mem (A + 32) (fr + 2880)).
    { pose proof HFLSI as HP. unfold FLSI, FLSH, PRO in HP.
      destruct HP as (((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P32) & _) & _).
      exact (f17_spill_q regs mem 32 (fr + 2880) A P32 Hs1
               ltac:(clear - HAr0; unfold HIGHMEM_BEG in *; lia) ltac:(lia)
               ltac:(clear - HAr0; unfold APPMEM_END in *; lia)). }
    (* what the memcpy at 0x823d4 reads off FRA and the cut (the copy's destination first.sroa.7 is addressable
       for 35 bytes and byte-backed; the frame and the copy's source are apart from the callee window; the
       runtime cells and shadow for the contract), before the stepping context drops them *)
    pose proof HIFS3 as (_ & _ & (_ & _ & _ & Hbad35 & _)).
    pose proof (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGTfr & Happfr).
    pose proof (fra_frame B APIf ra g fr _ regs mem md HFRA) as (Hplace & _).
    pose proof (fra_stk B APIf ra g fr _ regs mem md HFRA) as Hstkfr.
    pose proof (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hwlo & Hwstk).
    pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HAC0.
    pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSW0.
    pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ mem md HAH)
      as Hstkhigh.
    clear Hs24 HL12 Hs9g Hs22 Hq136 Hq120 Hq176 HENT HFLSI Hs18 H152 H280 HIFS3.
    destruct Hrest as (Hgimg & Hr2 & Hspm & Haspz & Hstklo & Hr4 & Hr8 & Hr9f & Hr3 & Hr19 & Hr26 & Hrest2).
    assert (Hsp2 : Sem.reg_get regs (2%bv) = Z_to_bv 64 (AC.aspZ regs)) by
      (rewrite Haspz; rewrite <- Hr2; unfold getr; reflexivity).
    assert (Hs9r : Sem.reg_get regs (9%bv) = Z_to_bv 64 A) by
      (unfold rg in Hs1; rewrite <- Hs1; unfold getr; reflexivity).
    assert (Hs23r : Sem.reg_get regs (23%bv) = Z_to_bv 64 phi) by
      (unfold rg in Hs7; rewrite <- Hs7; unfold getr; reflexivity).
    assert (Hs26r : Sem.reg_get regs (26%bv) = Z_to_bv 64 ASAN_K) by
      (unfold rg in Hr26; rewrite <- Hr26; unfold getr; reflexivity).
    assert (IDW : bvmap_set (9%bv) (Z_to_bv 64 A)
                   (bvmap_set (23%bv) (Z_to_bv 64 phi)
                     (bvmap_set (26%bv) (Z_to_bv 64 ASAN_K) (Regs6ss.mkR_of regs)))
                  = Regs6ss.mkR_of regs)
      by (rewrite <- Hs9r, <- Hs23r, <- Hs26r; cbn; reflexivity).
    rewrite <- IDW.
    (* the record's model bytes stay an opaque list rb during the stepping (as the push-9 proof kept its record
       bytes generalized): the tested bytes and the postcondition name rb, so the kernel never unfolds t_g
       inside the step conversions *)
    remember (t_g (g_in g) j) as rb eqn:Erb.
    destruct (t_big (g_in g) j) eqn:Ebig.
    2:{ (* short arm (t_big false): [s1+232] = 1, so a0 = 1 | s4 has bit 0 set and `bnez a0, 0x823e4` is TAKEN,
           into the join `ld s9,176(s1)` and on to 0x823e8 (memory unchanged) *)
      clear Hrec40 Hrecg Hrecb.
      assert (H50 : (50 <=? flen g j) = false) by (unfold flen; unfold t_big in Ebig; exact Ebig).
      assert (Hv232b : q64 mem (A + 232) 1) by (rewrite ?Ebig in Hv232; exact Hv232).
      clear Hv232. unfold q64 in Hv232b.
      assert (HR232 : ov_read_bytes rsegs mem (wa (A + 232)) 8 = Some (le8 (Z_to_bv 64 1))).
      { pose proof (bytes_at_ov_read rsegs mem (A + 232) (le8 (Z_to_bv 64 1)) 0 8 Hv232b
            ltac:(rewrite length_le8; cbn; lia)) as H.
        rewrite Z.add_0_r, skipn_O in H.
        rewrite firstn_all2 in H by (rewrite length_le8; cbn; lia). exact H. }
      step. (* 0x822a0: ld a0,232(s1) : a0 = 1 *)
      step. (* 0x822a4: or a0,a0,s4 *)
      step. (* 0x822a8: bnez a0,823e4 -- taken *)
      or1_bnez_tk.
      assert (HR176 : ov_read_bytes rsegs mem (wa (A + 176)) 8 = Some (le8 (Z_to_bv 64 (fr + 64)))).
      { pose proof (bytes_at_ov_read rsegs mem (A + 176) (le8 (Z_to_bv 64 (fr + 64))) 0 8 Hv176b
            ltac:(rewrite length_le8; cbn; lia)) as H.
        rewrite Z.add_0_r, skipn_O in H.
        rewrite firstn_all2 in H by (rewrite length_le8; cbn; lia). exact H. }
      exit_K_step f17_fop_len H50. }
    (* long arm (t_big true): 50 <= len_j, so the guarded record facts hold. The record's 50 model bytes are at
       phi, so every byte the body tests is `bat (t_g (g_in g) j) k`. *)
    assert (HfL : 50 <= flen g j) by (unfold t_big in Ebig; apply Z.leb_le in Ebig; unfold flen; exact Ebig).
    assert (H50t : (50 <=? flen g j) = true) by (unfold flen; unfold t_big in Ebig; exact Ebig).
    destruct (Hrec40 HfL) as (Haddr & _). destruct (Hrecg HfL) as (_ & _ & Hrecw).
    destruct (Hrecb HfL) as (Hrbb & _ & _).
    assert (Hrblen : length rb = 50%nat) by (rewrite Erb; apply f18_t_g_length).
    clear Hrec40 Hrecg Hrecb.
    assert (Hv232b : q64 mem (A + 232) 0) by (rewrite ?Ebig in Hv232; exact Hv232).
    clear Hv232. unfold q64 in Hv232b.
    assert (HR232 : ov_read_bytes rsegs mem (wa (A + 232)) 8 = Some (le8 (Z_to_bv 64 0))).
    { pose proof (bytes_at_ov_read rsegs mem (A + 232) (le8 (Z_to_bv 64 0)) 0 8 Hv232b
          ltac:(rewrite length_le8; cbn; lia)) as H.
      rewrite Z.add_0_r, skipn_O in H.
      rewrite firstn_all2 in H by (rewrite length_le8; cbn; lia). exact H. }
    step. (* 0x822a0: ld a0,232(s1) : 0 on the long arm *)
    step. (* 0x822a4: or a0,a0,s4 *)
    step. (* 0x822a8: bnez a0,823e4 : NOT taken exactly when s4 = 0, i.e. the block sum is 0 *)
    (* s4 = 1 - sum_ok (0x81e9c / 0x81f50), which the cut pins: the body runs exactly when the block sum is 0.
       The register term is taken from the goal, so the rewrite below matches it. *)
    match goal with
    | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        match c with
        | context [Z.lor 0 (bv_unsigned (Sem.reg_get ?R ?r))] =>
            assert (Hs20r : Sem.reg_get R r = Z_to_bv 64 (1 - b2z (t_sum_ok (g_in g) j))) by
              (transitivity (Sem.reg_get regs r);
               [ symmetry; apply Regs6ss.mkR_of_eqv; reflexivity
               | unfold rg in Hs20; rewrite <- Hs20; unfold getr; reflexivity ])
        end
    end.
    assert (HR176 : ov_read_bytes rsegs mem (wa (A + 176)) 8 = Some (le8 (Z_to_bv 64 (fr + 64)))).
    { pose proof (bytes_at_ov_read rsegs mem (A + 176) (le8 (Z_to_bv 64 (fr + 64))) 0 8 Hv176b
          ltac:(rewrite length_le8; cbn; lia)) as H.
      rewrite Z.add_0_r, skipn_O in H.
      rewrite firstn_all2 in H by (rewrite length_le8; cbn; lia). exact H. }
    (* the branch condition is a closed computation once s4 is known; whichever boolean it computes to is the
       arm the code takes, so both encodings of `bnez` are covered *)
    destruct (t_sum_ok (g_in g) j) eqn:ESUM;
      (match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
         first [ replace c with true by (symmetry; rewrite Hs20r; vm_compute; reflexivity)
               | replace c with false by (symmetry; rewrite Hs20r; vm_compute; reflexivity) ]
       end; cbv_concl_iota).
    + (* s4 = 0: the guard's branch is not taken and the opens_record body at 0x822ac runs; its nine byte tests
         decide f_opens *)
      assert (Hbs : (RM.blocksum (skipn 18 rb) =? 0) = true)
        by (rewrite Erb, (f17_sumok_bs (g_in g) j Ebig); exact ESUM).
      pose proof Haddr as Haddr'. destruct Haddr' as (Hphi0 & _ & HphiE & _).
      unfold q64 in Hb192.
      (* check 1 (0x822ac .. 0x822c8): phi+16, const 205. v1.9 has no `ld s9` inside the body: the join loads it. *)
      step. (* 0x822ac: addi a0,s7,16 *)
      Time shadowcheck phi mem Haddr 16.
      Time frbc phi mem rb Hrbb 16 205 Hb16 f17_fop_16. clr1.
      (* check 2 (0x822cc .. 0x822ec): phi+17, const 234. v1.9 interleaves `ld a3,200(s1)` (the phi + 18
         pointer, [A + 200] since the renumber) between the shadow load and its bnez. *)
      assert (HR200 : ov_read_bytes rsegs mem (wa (A + 200)) 8 = Some (le8 (Z_to_bv 64 (phi + 18)))).
      { pose proof (bytes_at_ov_read rsegs mem (A + 200) (le8 (Z_to_bv 64 (phi + 18))) 0 8 Hb192
            ltac:(rewrite length_le8; cbn; lia)) as H.
        rewrite Z.add_0_r, skipn_O in H.
        rewrite firstn_all2 in H by (rewrite length_le8; cbn; lia). exact H. }
      step. (* 0x822cc: addi a0,s7,17 *)
      step. step. (* srli a1,a0,3 ; add a1,a1,s10 *)
      rewrite (unsigned_lit (phi + 17)) by (unfold APPMEM_END in HphiE; lia).
      assert (Had17 : addressable mem (phi + 17) 1) by (apply (addressable_sub mem phi 50 17 1 Haddr); lia).
      destruct (f17_shadow mem (phi + 17) Had17) as (b17 & HRsh17 & OK17 & BD17).
      step. (* 0x822d8: lb a1,0(a1) *)
      step. (* 0x822dc: ld a3,200(s1) : a3 = phi + 18 *)
      step. (* 0x822e0: bnez a1,.. *)
      Time converge (Z_to_bv 5 12) (phi + 17) b17 OK17 BD17.
      Time frbc phi mem rb Hrbb 17 234 Hb17 f17_fop_17. clr1.
      (* check 3 (0x822f0 .. 0x82308): the byte at a3 = phi+18, const 4; the shadow byte goes to a0 *)
      step. step. (* srli a0,a3,3 ; add a0,a0,s10 *)
      rewrite (unsigned_lit (phi + 18)) by (unfold APPMEM_END in *; lia).
      assert (Had18 : addressable mem (phi + 18) 1) by (apply (addressable_sub mem phi 50 18 1 Haddr); lia).
      destruct (f17_shadow mem (phi + 18) Had18) as (b18 & HRsh18 & OK18 & BD18).
      step. (* 0x822f8: lb a0,0(a0) *)
      step. (* 0x822fc: bnez a0,.. *)
      Time converge (Z_to_bv 5 11) (phi + 18) b18 OK18 BD18.
      Time frbc phi mem rb Hrbb 18 4 Hb18 f17_fop_18. clr1.
      (* check 4: phi+19, const 1 *)
      Time step. Time shadowcheck phi mem Haddr 19. Time frbc phi mem rb Hrbb 19 1 Hb19 f17_fop_19. clr1.
      (* check 5: phi+22, bnez a0 (exit if != 0) *)
      Time step. Time shadowcheck phi mem Haddr 22. Time frbnzc phi mem rb Hrbb 22 Hb22 f17_fop_22. clr1.
      (* check 6: phi+23, const 2 *)
      Time step. Time shadowcheck phi mem Haddr 23. Time frbc phi mem rb Hrbb 23 2 Hb23 f17_fop_23. clr1.
      (* check 7: phi+24, bnez a0 *)
      Time step. Time shadowcheck phi mem Haddr 24. Time frbnzc phi mem rb Hrbb 24 Hb24 f17_fop_24. clr1.
      (* check 8: phi+25, const 254 *)
      Time step. Time shadowcheck phi mem Haddr 25. Time frbc phi mem rb Hrbb 25 254 Hb25 f17_fop_25. clr1.
      (* check 9: phi+26, range check (b[8] - 23 >=u -22) *)
      Time step. Time shadowcheck_blt phi mem Haddr 26.
      assert (Hrr26 : ov_read_bytes rsegs mem (wa (phi + 26)) 1
                        = Some (firstn 1 (skipn (Z.to_nat 26) rb))).
      { pose proof (bytes_at_ov_read rsegs mem phi rb (Z.to_nat 26) 1 Hrbb ltac:(lia)) as H.
        replace (phi + Z.of_nat (Z.to_nat 26)) with (phi + 26) in H by lia. exact H. }
      step. (* lbu s9,0(a0) *)
      step. (* addi a0,s9,-23 *)
      step. (* li a1,-22 *)
      step. (* bltu a0,a1,823e4 : the range test 1 <= gg[26] <= 22 *)
      destruct ((1 <=? RF.bat rb 26) && (RF.bat rb 26 <=? 22)) eqn:Hb26;
      [ match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
          replace c with false by
            (symmetry; rewrite (f17_bltu_val rb 26 ltac:(lia) ltac:(lia)), Hb26; reflexivity) end;
        cbv_concl_iota
      | match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
          replace c with true by
            (symmetry; rewrite (f17_bltu_val rb 26 ltac:(lia) ltac:(lia)), Hb26; reflexivity) end;
        cbv_concl_iota; exit_K_step f17_fop_26 Hb26 ].
      (* ---- the record opens: 0x823c8 .. 0x823e4 (the memcpy of its body into the frame object first.sroa.7,
         `sd a0,104(s1)` = 1, `sd s9,112(s1)` = gg[26], the join's `ld s9,176(s1)`) is f17_tail. Its premises are
         read off the cut (record bytes and addressability), FRA (the frame object's placement and bytes, the
         sp-anchored stack window, the runtime cells) and the live heap block (the record is apart from the frame
         and below the callee window). *)
      assert (Hop : f_opens (flen g j) rb = true)
        by exact (f17_fopens_true (flen g j) rb H50t Hb16 Hb17 Hb18 Hb19 Hb22 Hb23 Hb24 Hb25 Hb26 Hbs).
      assert (Hn26 : 1 <= RF.bat rb 26 <= 22)
        by (apply andb_prop in Hb26 as (Hl1 & Hl2); apply Z.leb_le in Hl1; apply Z.leb_le in Hl2; lia).
      pose proof (ba_sub mem phi rb 27 (Z.to_nat (RF.bat rb 26)) Hrbb ltac:(rewrite Hrblen; lia)) as Hsrc.
      replace (phi + Z.of_nat 27) with (phi + 27) in Hsrc by lia.
      assert (Hsrcl : length (firstn (Z.to_nat (RF.bat rb 26)) (skipn 27 rb)) = Z.to_nat (RF.bat rb 26))
        by (rewrite length_firstn, length_skipn, Hrblen; lia).
      assert (HadS : addressable mem (phi + 27) (RF.bat rb 26))
        by (apply (addressable_sub mem phi 50 27 (RF.bat rb 26) Haddr); lia).
      assert (HadD : addressable mem (fr + 2880) (RF.bat rb 26)).
      { pose proof (addressable_sub mem (fr + 2880) 35 0 (RF.bat rb 26) Hbad35 ltac:(lia) ltac:(lia) ltac:(lia))
          as HadD0.
        rewrite Z.add_0_r in HadD0. exact HadD0. }
      assert (HstD : stk rsegs mem (fr + 2880) (fr + 2880 + RF.bat rb 26)).
      { destruct (LF.stk_split rsegs mem fr (fr + 2880) (fr + FRAME_BYTES) Hstkfr ltac:(lia)) as (_ & Hs1').
        destruct (LF.stk_split rsegs mem (fr + 2880) (fr + 2880 + RF.bat rb 26) (fr + FRAME_BYTES) Hs1'
                    ltac:(lia)) as (Hs2' & _).
        exact Hs2'. }
      assert (Hblkm : forall x, phi <= x < phi + 50 ->
                x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ ~ (fr <= x < fr + FRAME_BYTES)).
      { intros x Hx. apply (f17_blk_out g fr _ regs mem md phi (AC.a_size (flen g j)) x HFRA).
        - unfold hb1. apply in_or_app. left. left. reflexivity.
        - unfold AC.a_size. lia. }
      assert (Hdj : phi + 27 + RF.bat rb 26 <= fr + 2880 \/ fr + 2880 + RF.bat rb 26 <= phi + 27).
      { destruct (Z_le_gt_dec (phi + 27 + RF.bat rb 26) (fr + 2880)) as [D1|D1]; [left; exact D1|].
        destruct (Z_le_gt_dec (fr + 2880 + RF.bat rb 26) (phi + 27)) as [D2|D2]; [right; exact D2|].
        exfalso. destruct (Hblkm (Z.max (phi + 27) (fr + 2880)) ltac:(lia)) as (_ & Hnf). apply Hnf. lia. }
      assert (HappP : forall a, phi <= a < phi + 50 -> app_mem a).
      { intros a Ha. pose proof Haddr as (_ & _ & _ & Hab). destruct (Hab (a - phi) ltac:(lia)) as (Hap & _).
        replace (phi + (a - phi)) with a in Hap by lia. exact Hap. }
      pose proof (Hplace ACPY.ASAN_MEMCPY_K ltac:(unfold FN_STACK, AF.SLOT_STACK, ACPY.ASAN_MEMCPY_K; lia)) as HplK.
      pose proof (Hblkm (phi + 49) ltac:(lia)) as (Hphilo & _).
      (* s9 holds the loaded byte raw; f17_tail names it as the model's gg[26] *)
      rewrite (f17_byte_word rb 26 ltac:(lia) ltac:(lia)).
      match goal with |- evt _ _ (MS ?R0 ?F0 _ ?fc0 _ _ _) =>
        eapply evt_mono;
        [ apply (f17_tail (Sem.reg_get R0 1) (Sem.reg_get R0 2) (Sem.reg_get R0 3) (Sem.reg_get R0 4)
                  (Sem.reg_get R0 5) (Sem.reg_get R0 6) (Sem.reg_get R0 7) (Sem.reg_get R0 8)
                  (Sem.reg_get R0 9) (Sem.reg_get R0 10) (Sem.reg_get R0 11) (Sem.reg_get R0 12)
                  (Sem.reg_get R0 13) (Sem.reg_get R0 14) (Sem.reg_get R0 15) (Sem.reg_get R0 16)
                  (Sem.reg_get R0 17) (Sem.reg_get R0 18) (Sem.reg_get R0 19) (Sem.reg_get R0 20)
                  (Sem.reg_get R0 21) (Sem.reg_get R0 22) (Sem.reg_get R0 23) (Sem.reg_get R0 24)
                  (Sem.reg_get R0 25) (Sem.reg_get R0 26) (Sem.reg_get R0 27) (Sem.reg_get R0 28)
                  (Sem.reg_get R0 29) (Sem.reg_get R0 30) (Sem.reg_get R0 31) F0 fc0 mem A phi fr
                  (RF.bat rb 26) (AC.aspZ regs) (AC.aspZ regs - FN_STACK)
                  (firstn (Z.to_nat (RF.bat rb 26)) (skipn 27 rb)))
        | ] end.
      { reflexivity. }
      { reflexivity. }
      { reflexivity. }
      { exact Hsp2. }
      { exact Hq32. }
      { exact Hv176b. }
      { exact Hsrc. }
      { exact Hsrcl. }
      { exact Hn26. }
      { exact HadS. }
      { exact HadD. }
      { exact HstD. }
      { exact Hdj. }
      { apply HappP. lia. }
      { apply Happfr. lia. }
      { apply HappP. lia. }
      { apply Happfr. lia. }
      { destruct HplK as [P|P]; [left|right]; lia. }
      { left. unfold FN_STACK, AF.SLOT_STACK, ACPY.ASAN_MEMCPY_K in Hwlo |- *. lia. }
      { exact Hwstk. }
      { unfold FN_STACK, AF.SLOT_STACK, ACPY.ASAN_MEMCPY_K. lia. }
      { lia. }
      { lia. }
      { exact HGTfr. }
      { exact Hphi0. }
      { exact Hro. }
      { exact HAC0. }
      { exact HSW0. }
      { unfold HIGHMEM_BEG in HAr0. lia. }
      { unfold APPMEM_END in HAr0. lia. }
      { exact Hwr. }
      { exact HfrA. }
      { exact HspA. }
      intros ms' (ra' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & mc
                  & -> & MUc & WMc & ROc & STc & BSc).
      hnf. do 3 eexists. split; [reflexivity|].
      split; [reflexivity|].
      do 13 (split; [regeq|]).
      right. split; [exact Hop|]. exists mc.
      split; [exact MUc|]. split; [exact WMc|]. split; [exact ROc|]. split; [exact STc|]. split; [exact BSc|].
      reflexivity.
    + (* s4 <> 0: the block sum is nonzero, so the record does not open; the guard's bnez was taken into the
         join 0x823e4 (memory unchanged) *)
      assert (Hbs : (RM.blocksum (skipn 18 rb) =? 0) = false)
        by (rewrite Erb, (f17_sumok_bs (g_in g) j Ebig); exact ESUM).
      exit_K_step f17_fop_bs Hbs.
  - (* continuation: assemble the official F18 entry cut Inv_A823e8_at (turn j) at 0x823e8 from K *)
    intros R pc' mem' regs' md' (Hpc & E2 & E3 & E4 & E8 & E9 & E19 & E26 & E21 & E23 & E24 & E22 & E18 & E25 &
      Hmem) Hreg Hmat.
    subst pc'.
    assert (G2 : getr regs' 2 = getr regs 2)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G3 : getr regs' 3 = getr regs 3)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G4 : getr regs' 4 = getr regs 4)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G8 : getr regs' 8 = getr regs 8)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G9 : getr regs' 9 = getr regs 9)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G19 : getr regs' 19 = getr regs 19)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G21 : getr regs' 21 = getr regs 21)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G23 : getr regs' 23 = getr regs 23)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G24 : getr regs' 24 = getr regs 24)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G22 : getr regs' 22 = getr regs 22)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G26 : getr regs' 26 = getr regs 26)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G18 : getr regs' 18 = getr regs 18)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G25 : getr regs' 25 = Z_to_bv 64 (fr + 64))
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (ASP : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite G2; reflexivity).
    assert (HAlo : HIGHMEM_BEG <= A + 88) by exact (proj1 (Happ (A + 88) ltac:(lia))).
    assert (HAhi : A + 120 <= APPMEM_END) by (pose proof (Happ (A + 119) ltac:(lia)) as Hap; lia).
    assert (HAr : 0 <= A < 2 ^ 64) by (clear - HAlo HAhi; unfold HIGHMEM_BEG, APPMEM_END in *; lia).
    assert (HAtop : A + 120 <= 2 ^ 64) by (clear - HAhi; unfold APPMEM_END in *; lia).
    pose proof (eq_refl : ACPY.ASAN_MEMCPY_K = 2224) as HKv.
    pose proof (eq_refl : AF.SLOT_STACK = 1048576) as HSS.
    pose proof (eq_refl : FN_STACK = AF.SLOT_STACK - 4096) as HFN.
    pose proof (eq_refl : HIGHMEM_BEG = 0x10007fff8000) as HHBv.
    pose proof (eq_refl : APPMEM_END = 0x800000000000) as HAEv.
    pose proof (eq_refl : AC.GT = 0x5fe000) as HGTv.
    pose proof (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGTfr & Happfr).
    pose proof (fra_frame B APIf ra g fr _ regs mem md HFRA) as (Hplace & _).
    pose proof (Hplace ACPY.ASAN_MEMCPY_K ltac:(lia)) as HplK.
    pose proof (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hwlo & _).
    pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ mem md HAH)
      as Hstkhigh.
    (* Both exits: a write set W whose bytes lie in the frame object first.sroa.7 [fr + 2880, fr + 2902), in the
       callee's stack scratch [sp - K, sp) or in the first-fragment spills [A + 104, A + 120). W is app memory, the
       frame stays byte-backed, FRA and ENT move (f17_cp_fra across the copy, fra_store1 / ent_store1 across the
       two spill stores, then sl_fra_move / ent_mat), and LT = IFS g fr (S j) holds of turn S j. *)
    assert (COM : exists W, LF.munch W mem mem' /\ LF.wmono rsegs mem mem' /\ all_app W /\
                  (forall x, ~ LF.outside W x ->
                     (fr + 2880 <= x < fr + 2902) \/
                     (AC.aspZ regs - ACPY.ASAN_MEMCPY_K <= x < AC.aspZ regs) \/ (A + 104 <= x < A + 120)) /\
                  stk rsegs mem' fr (fr + FRAME_BYTES) /\
                  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md' /\
                  ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md' /\
                  LT g fr j regs' mem').
    { destruct HIFS3 as (HID & HFG & HFSj).
      destruct Hmem as [(-> & Hopf) | (Hopt & mc & MUc & WMc & ROc & STc & BSc & ->)].
      - exists []. split; [apply LF.munch_refl|]. split; [apply LF.wmono_refl|].
        split; [cbn [all_app]; exact I|].
        split; [intros x Hx; exfalso; apply Hx; exact I|].
        split; [exact (fra_stk B APIf ra g fr _ regs mem md HFRA)|].
        split; [exact (sl_fra_move B APIf ra g fr _ regs regs' mem md md' HFRA G2 G3 G4 G8 G9 G19 G26 Hmat)|].
        split; [eapply ent_mat; [exact HENT | exact Hmat]|].
        (* the record did not open: the first-fragment state of turn S j is turn j's (f17_fsj_false) *)
        split; [exact HID|]. split; [exact HFG|].
        exact (f17_fsj_regs g fr (S j) regs regs' mem (f17_fsj_false g fr j regs mem Hopf HFSj) G9).
      - assert (Hn26 : 1 <= RF.bat (t_g (g_in g) j) 26 <= 22).
        { pose proof Hopt as Ho. unfold f_opens in Ho. apply andb_prop in Ho as (Ho1 & _).
          exact (f18_fr_fg_n _ _ Ho1). }
        assert (Hrbl : length (t_g (g_in g) j) = 50%nat) by apply f18_t_g_length.
        assert (BSl : length (firstn (Z.to_nat (RF.bat (t_g (g_in g) j) 26)) (skipn 27 (t_g (g_in g) j)))
                        = Z.to_nat (RF.bat (t_g (g_in g) j) 26))
          by (rewrite length_firstn, length_skipn, Hrbl; lia).
        (* the copy (mem -> mc): FRA, ENT and the frame's bytes by f17_cp_fra *)
        assert (HDst : forall x, fr + 2880 <= x < fr + 2880 + RF.bat (t_g (g_in g) j) 26 ->
                         exists b, mrd rsegs mc (wa x) = Some b).
        { intros x Hx. apply (f17_ba_rd mc (fr + 2880) _ x BSc). rewrite BSl. lia. }
        destruct (f17_cp_fra g fr _ regs mem mc md (RF.bat (t_g (g_in g) j) 26) HFRA HENT ltac:(lia)
                    MUc WMc ROc STc HDst) as (HFRAc & HENTc & HSTKc).
        (* the two spill stores (mc -> mem') *)
        pose proof (fra_store1 g fr _ regs mc md A 104 (Z_to_bv 64 1) HFRAc Hs9g Hdisj Happ
                      ltac:(lia) ltac:(lia)) as HF1.
        pose proof (ent_store1 g fr _ regs mc md A 104 (Z_to_bv 64 1) HFRAc HENTc Hs9g Happ
                      ltac:(lia) ltac:(lia)) as HE1.
        pose proof (fra_store1 g fr _ regs _ md A 112 (Z_to_bv 64 (RF.bat (t_g (g_in g) j) 26)) HF1 Hs9g Hdisj
                      Happ ltac:(lia) ltac:(lia)) as HF2.
        pose proof (ent_store1 g fr _ regs _ md A 112 (Z_to_bv 64 (RF.bat (t_g (g_in g) j) 26)) HF1 HE1 Hs9g
                      Happ ltac:(lia) ltac:(lia)) as HE2.
        assert (MU2 : LF.munch [(A + 104, A + 120)] mc
                        (write_to_mem (write_to_mem mc (wa (A + 104)) (le8 (Z_to_bv 64 1)))
                           (wa (A + 112)) (le8 (Z_to_bv 64 (RF.bat (t_g (g_in g) j) 26))))).
        { apply LF.munch_write; [ apply LF.munch_write; [ apply LF.munch_refl | | | ] | | | ];
            try (rewrite length_le8); try (cbn [LF.inside]; left);
            clear - HAlo HAhi; unfold APPMEM_END, LOWMEM_END, HIGHMEM_BEG in *; lia. }
        assert (WM2 : LF.wmono rsegs mc
                        (write_to_mem (write_to_mem mc (wa (A + 104)) (le8 (Z_to_bv 64 1)))
                           (wa (A + 112)) (le8 (Z_to_bv 64 (RF.bat (t_g (g_in g) j) 26)))))
          by (repeat apply LF.wmono_write; apply LF.wmono_refl).
        assert (MU : LF.munch [(fr + 2880, fr + 2880 + RF.bat (t_g (g_in g) j) 26);
                               (AC.aspZ regs - ACPY.ASAN_MEMCPY_K, AC.aspZ regs); (A + 104, A + 120)] mem
                       (write_to_mem (write_to_mem mc (wa (A + 104)) (le8 (Z_to_bv 64 1)))
                          (wa (A + 112)) (le8 (Z_to_bv 64 (RF.bat (t_g (g_in g) j) 26))))).
        { apply (LF.munch_trans _ mem mc).
          - apply (LF.munch_weaken [(fr + 2880, fr + 2880 + RF.bat (t_g (g_in g) j) 26);
                                    (AC.aspZ regs - ACPY.ASAN_MEMCPY_K, AC.aspZ regs)]); [|exact MUc].
            intros x Hx. cbn [LF.outside] in Hx |- *. destruct Hx as (H1 & H2 & _).
            split; [exact H1|]. split; [exact H2 | exact I].
          - apply (LF.munch_weaken [(A + 104, A + 120)]); [|exact MU2].
            intros x Hx. cbn [LF.outside] in Hx |- *. destruct Hx as (_ & _ & H3 & _).
            split; [exact H3 | exact I]. }
        assert (HAW' : all_app [(fr + 2880, fr + 2880 + RF.bat (t_g (g_in g) j) 26);
                                (AC.aspZ regs - ACPY.ASAN_MEMCPY_K, AC.aspZ regs); (A + 104, A + 120)]).
        { cbn [all_app]. split; [intros a Ha; apply Happfr; lia|].
          split; [intros a Ha; unfold app_mem; right; lia|].
          split; [intros a Ha; unfold app_mem; right; apply Happ; lia | exact I]. }
        exists [(fr + 2880, fr + 2880 + RF.bat (t_g (g_in g) j) 26);
                (AC.aspZ regs - ACPY.ASAN_MEMCPY_K, AC.aspZ regs); (A + 104, A + 120)].
        split; [exact MU|].
        split; [exact (LF.wmono_trans rsegs _ _ _ WMc WM2)|].
        split; [exact HAW'|].
        split.
        { intros x Hx. destruct (f17_in3 _ _ _ _ _ _ x Hx) as [Hw|[Hw|Hw]]; [left | right; left | right; right];
            lia. }
        split.
        { (* the frame stays byte-backed across the two stores (they are above it) *)
          apply (LF.stk_transport rsegs [(A + 104, A + 120)] mc _ fr (fr + FRAME_BYTES) HSTKc MU2 WM2).
          intros x Hx. left. cbn [LF.outside]. split; [lia | exact I]. }
        split; [exact (sl_fra_move B APIf ra g fr _ regs regs' _ md md' HF2 G2 G3 G4 G8 G9 G19 G26 Hmat)|].
        split; [eapply ent_mat; [exact HE2 | exact Hmat]|].
        (* the record opened: the two frame records are untouched (they lie in the frame below first.sroa.7,
           apart from the callee window and below the spill window), and the first-fragment state is turn S j's:
           [A + 104] = 1 and [A + 112] = gg[26] off the two stores, the copied body at fr + 2880 *)
        assert (HRW : forall x, fr + 2688 <= x < fr + 2840 ->
                  LF.outside [(fr + 2880, fr + 2880 + RF.bat (t_g (g_in g) j) 26);
                              (AC.aspZ regs - ACPY.ASAN_MEMCPY_K, AC.aspZ regs); (A + 104, A + 120)] x).
        { intros x Hx. cbn [LF.outside]. split; [lia|]. split; [destruct HplK as [P|P]; lia|].
          split; [lia | exact I]. }
        destruct (f17_idfg_keep g fr j mem _ _ HID HFG MU HRW) as (HID' & HFG').
        split; [exact HID'|]. split; [exact HFG'|].
        apply (f17_fsj_true g fr j regs' _ Hopt).
        + (* [A + 104] = 1 *)
          exists A. split; [unfold rg; rewrite G9; exact Hs1|]. apply f17_q64_ba.
          apply f17_w8_other; [apply f17_w8_same | | | ]; clear - HAr HAtop; lia.
        + (* [A + 112] = gg[26] *)
          exists A. split; [unfold rg; rewrite G9; exact Hs1|]. apply f17_q64_ba.
          apply f17_w8_same; clear - HAr HAtop; lia.
        + (* the copied body at fr + 2880, which the two stores (above the frame) miss *)
          eapply fl_bytes; [exact BSc | exact MU2 |]. rewrite BSl. intros x Hx.
          cbn [LF.outside]. split; [lia | exact I].
        + (* first.sroa.7 stays addressable: W is app memory *)
          destruct HFSj as (_ & _ & _ & Hbad & _).
          exact (sl_addr_keep mem _ [(fr + 2880, fr + 2880 + RF.bat (t_g (g_in g) j) 26);
                   (AC.aspZ regs - ACPY.ASAN_MEMCPY_K, AC.aspZ regs); (A + 104, A + 120)] (fr + 2880) 35 Hbad MU HAW'). }
    destruct COM as (W & MU & WM & HAW & HWin & HSTKfr' & HFRA' & HENT' & HLT).
    assert (HWout : forall x, (x < fr + 2880 \/ fr + 2902 <= x) ->
                      (x < AC.aspZ regs - ACPY.ASAN_MEMCPY_K \/ AC.aspZ regs <= x) ->
                      (x < A + 104 \/ A + 120 <= x) -> LF.outside W x).
    { intros x H1 H2 H3. destruct (Tac_f17b.f17m_outside_dec W x) as [Ho|Ho]; [exact Ho|].
      exfalso. destruct (HWin x Ho) as [Hw|[Hw|Hw]]; lia. }
    (* no shadow byte is written: W is app memory *)
    assert (HWsh : forall x, in_shadow x -> LF.outside W x).
    { intros x Hx. apply HWout.
      - destruct (Z_lt_le_dec x (fr + 2880)) as [L|L]; [left; exact L|].
        destruct (Z_lt_le_dec x (fr + 2902)) as [L2|L2]; [|right; exact L2].
        exfalso. pose proof (Happfr x ltac:(lia)) as Hap. unfold app_mem in Hap. unfold in_shadow in Hx.
        unfold LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG in Hap, Hx. lia.
      - left. unfold in_shadow in Hx. unfold LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG in Hx. lia.
      - left. unfold in_shadow in Hx. unfold LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG in Hx. lia. }
    assert (MK : meta_kept mem mem') by exact (munch_meta _ mem mem' MU HAW).
    (* The heap block [phi, phi + a_size len_j) is live (in hb), so it ends at or below stklo, below the callee
       window and the spill window, and none of its bytes is a frame byte (f17_blk_out): W misses every record
       byte. *)
    assert (Hblk : forall x, phi <= x < phi + AC.a_size (flen g j) -> LF.outside W x).
    { intros x Hx.
      destruct (f17_blk_out g fr _ regs mem md phi (AC.a_size (flen g j)) x HFRA
                  ltac:(unfold hb1; apply in_or_app; left; left; reflexivity) Hx) as (Hlo & Hnf).
      apply HWout; lia. }
    assert (HFLSI' : FLSI g j fr regs' mem').
    { apply (flsi_cp g j fr regs regs' mem mem' W HFLSI G9 MU HAW WM).
      - intros A' HA' off x Ho Hd Hx.
        destruct (f17_rg9_wrap regs A A' Hs1 HAr HA') as [E|[E|E]]; [subst A' | |]; apply HWout; lia.
      - exact HSTKfr'.
      - (* the input block is a live heap block of the entry (when it is not empty) *)
        intros x Hx. pose proof HFLSI as HP. unfold FLSI in HP. destruct HP as (_ & _ & _ & _ & (Hin & _ & _) & _).
        assert (Hn0 : 0 < g_n g) by (rewrite g_n_len; lia).
        destruct (f17_blk_out g fr _ regs mem md (g_p g) (g_n g) x HFRA
                    (in_or_app _ _ _ (or_intror (Hin Hn0))) ltac:(rewrite g_n_len; lia)) as (Hlo & Hnf).
        apply HWout; lia. }
    destruct Hw240 as (w240 & Hw240q & Hw240r & Hw240t & Hw240f).
    apply (to_exit_823e8 j Hexit).
    exists phi, regs', mem', md', fr. rewrite SEGS.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hn|]. split; [exact Hj|].
    split.
    { destruct HHB as (Hphinz & Haddrp). split; [exact Hphinz|]. exact (addressable_kept mem mem' _ _ Haddrp MK). }
    split; [exact HFLSI'|].
    split.
    { destruct HLK as (HLj & HL21 & HLour). split; [exact HLj|]. split.
      - unfold rg in *. rewrite G21. exact HL21.
      - unfold OURb in *. eapply fl_bytes; [exact HLour | exact MU |]. rewrite OUR_length.
        intros x Hx. apply HWout; destruct HplK as [P|P]; lia. }
    split.
    { exists A, w240.
      split; [unfold rg; rewrite G9; exact Hs1|].
      split; [exact HAr|].
      split; [rewrite ASP; exact HspA|].
      split; [unfold rg; rewrite G23; exact Hs7|].
      split; [unfold rg; rewrite G24; exact Hs24|].
      split; [unfold rg; rewrite G22; exact Hs22|].
      split.
      { intro HfL. destruct (Hrecg HfL) as (HRI & _ & Hrecw).
        apply (rec_inv0_kept g j fr phi A mem mem' W HRI MU).
        - intros x Hx. apply Hblk. unfold AC.a_size. lia.
        - intros x Hx. apply HWout; lia. }
      split; [unfold q64 in Hq136 |- *; eapply fl_bytes; [exact Hq136 | exact MU |];
              rewrite length_le8; intros x Hx; apply HWout; lia|].
      split; [unfold q64 in Hq120 |- *; eapply fl_bytes; [exact Hq120 | exact MU |];
              rewrite length_le8; intros x Hx; apply HWout; lia|].
      split; [unfold q64 in Hq176 |- *; eapply fl_bytes; [exact Hq176 | exact MU |];
              rewrite length_le8; intros x Hx; apply HWout; lia|].
      split.
      { unfold q64 in Hw240q |- *. eapply fl_bytes; [exact Hw240q | exact MU |].
        rewrite length_le8. intros x Hx. apply HWout; lia. }
      split; [exact Hw240r|].
      split; [exact Hw240f|].
      (* t_8819 holds only on the long arm (t_8819 = t_big && ..), so the guarded record facts hold *)
      intro E8819.
      assert (HfL : 50 <= flen g j).
      { pose proof E8819 as E0. unfold t_8819, t_big in E0. apply andb_prop in E0 as [E1 _].
        apply andb_prop in E1 as [E1' _]. apply Z.leb_le in E1'. unfold flen. exact E1'. }
      destruct (Hrec40 HfL) as (Haddr & _).
      destruct (Hrecg HfL) as (HRI0 & Hphiw & Hrecw).
      destruct (HL12 E8819) as (HRP & (ls & rs & HLq & HLb & HLl & HRb & HRl & HLm & HLad) &
        (ls2 & rs2 & HL2q & HL2b & HL2l & HR2b & HR2l & HL2m & HL2ad)).
      destruct (ba_first6 mem (fr + 186) ls HLb HLl) as (HLb6 & HLl6).
      destruct (ba_first6 mem phi rs HRb HRl) as (HRb6 & HRl6).
      destruct (ba_first6 mem (fr + 180) ls2 HL2b HL2l) as (HL2b6 & HL2l6).
      destruct (ba_first6 mem (phi + 6) rs2 HR2b HR2l) as (HR2b6 & HR2l6).
      split; [exact (Hw240t E8819)|].
      (* push 15: the parse-made record facts; W misses the record bytes, every shadow byte and fr + 196 *)
      split.
      { destruct HRI0 as (_ & _ & _ & _ & Hpap & _).
        apply (f17_rec_parse_kept g j fr phi mem mem' W HRP Hpap MU).
        - intros x Hx. apply Hblk. unfold AC.a_size. lia.
        - exact HWsh.
        - intros x Hx. apply HWout; destruct HplK as [P|P]; lia. }
      exists (firstn 6 ls), (firstn 6 rs), (firstn 6 ls2), (firstn 6 rs2).
      split.
      { unfold q64 in HLq |- *. eapply fl_bytes; [exact HLq | exact MU |].
        rewrite length_le8. intros x Hx. apply HWout; lia. }
      split.
      { eapply fl_bytes; [exact HLb6 | exact MU |]. rewrite HLl6. intros x Hx.
        apply HWout; destruct HplK as [P|P]; lia. }
      split; [rewrite HLl6; lia|].
      split.
      { eapply fl_bytes; [exact HRb6 | exact MU |]. rewrite HRl6. intros x Hx. apply Hblk. unfold AC.a_size. lia. }
      split; [rewrite HRl6; lia|].
      split; [rewrite memcmp_firstn; exact HLm|].
      split; [exact (addressable_kept mem mem' (fr + 186) 6 HLad MK)|].
      split.
      { pose proof (addressable_sub mem phi 50 0 6 Haddr ltac:(lia) ltac:(lia) ltac:(lia)) as Had6.
        rewrite Z.add_0_r in Had6. exact (addressable_kept mem mem' phi 6 Had6 MK). }
      split; [rewrite ASP; exact Hphiw|].
      split.
      { unfold q64 in HL2q |- *. eapply fl_bytes; [exact HL2q | exact MU |].
        rewrite length_le8. intros x Hx. apply HWout; lia. }
      split.
      { eapply fl_bytes; [exact HL2b6 | exact MU |]. rewrite HL2l6. intros x Hx.
        apply HWout; destruct HplK as [P|P]; lia. }
      split; [rewrite HL2l6; lia|].
      split.
      { eapply fl_bytes; [exact HR2b6 | exact MU |]. rewrite HR2l6. intros x Hx. apply Hblk. unfold AC.a_size. lia. }
      split; [rewrite HR2l6; lia|].
      split; [rewrite memcmp_firstn; exact HL2m|].
      split; [exact (addressable_kept mem mem' (fr + 180) 6 HL2ad MK)|].
      exact (addressable_kept mem mem' (phi + 6) 6
               (addressable_sub mem phi 50 6 6 Haddr ltac:(lia) ltac:(lia) ltac:(lia)) MK). }
    (* push 6c8 tail: s2 kept, s9 = fr + 64, the record bytes (inside the live heap block, so off W) and the two
       per-turn spills (offsets 152 / 280, off W) *)
    split; [unfold rg; rewrite G18; exact Hs18|].
    split; [unfold rg; exact G25|].
    split.
    { intro HfL. destruct (Hrecb HfL) as (Hbg & Hbp & Hlp).
      assert (Lg : (length (t_g (g_in g) j) <= 50)%nat) by (unfold t_g, fr50; rewrite firstn_length; lia).
      split; [eapply fl_bytes; [exact Hbg | exact MU |]; intros x Hx; apply Hblk; unfold AC.a_size; lia|].
      split; [eapply fl_bytes; [exact Hbp | exact MU |]; intros x Hx; apply Hblk; unfold AC.a_size; lia
             | exact Hlp]. }
    split.
    { apply (spill_keep regs regs' mem mem' W 152 _ H152 G9 MU).
      intros A' HA' x Hx.
      destruct (f17_rg9_wrap regs A A' Hs1 HAr HA') as [E|[E|E]]; [subst A' | |]; apply HWout; lia. }
    split.
    { apply (spill_keep regs regs' mem mem' W 280 _ H280 G9 MU).
      intros A' HA' x Hx.
      destruct (f17_rg9_wrap regs A A' Hs1 HAr HA') as [E|[E|E]]; [subst A' | |]; apply HWout; lia. }
    (* push 12B: LT = IFS g fr (S j), from IFS3 and the arm's own f_opens value (COM) *)
    exact HLT.
Qed.

(* 0x8229c: `bltz a0,82bf4`, not taken, since the cut's a0 (the ingest result) is nonnegative. The branch writes
   no register and no memory, so the whole state crosses to the split cut 0x822a0 (same turn j) unchanged: FRA
   moves with sl_fra_move (the register file is kept), ENT with ent_mat (only the model's lazy pages may grow),
   FLSI and the spills with s1 kept, and every guarded conjunct as it is. *)
Lemma seg_F17 : forall j : nat,
  Hat B APIf ra (Inv_A822a0_at B APIf ra) j -> Hat B APIf ra (Inv_A8229c_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof (eq_refl : FRAME_BYTES = 3136) as HFB. pose proof (eq_refl : FRAME_SHADOW = 392) as HFS.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hn & Hj & HHB & HFLSI & HLK &
    Hs7 & Hs22 & Hrec40 & Ha0 & (A & Hs1 & Hv232 & Hb192 & Hq136 & Hq120 & Hq176 & Happ & Hw240 & Hs24 & Hrecg &
    HL12) & Hs18 & Hrecb & H152 & H280 & HIFS3 & Hs20).
  subst c.
  rewrite SEGS.
  destruct Ha0 as (v0 & Ha0r & Ha0b).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A2 & sp & s5v & HRT & HAH & Hro & Hsn & Hhalt & Hrest).
  eapply (sl_run regs (Z_to_bv 64 0x8229c) mem md
    (fun R pc' mem' =>
       pc' = Z_to_bv 64 0x822a0 /\
       Sem.reg_get R 2 = Sem.reg_get regs 2 /\ Sem.reg_get R 3 = Sem.reg_get regs 3 /\ Sem.reg_get R 4 = Sem.reg_get regs 4 /\
       Sem.reg_get R 8 = Sem.reg_get regs 8 /\ Sem.reg_get R 9 = Sem.reg_get regs 9 /\ Sem.reg_get R 19 = Sem.reg_get regs 19 /\
       Sem.reg_get R 26 = Sem.reg_get regs 26 /\ Sem.reg_get R 21 = Sem.reg_get regs 21 /\ Sem.reg_get R 23 = Sem.reg_get regs 23 /\
       Sem.reg_get R 24 = Sem.reg_get regs 24 /\ Sem.reg_get R 22 = Sem.reg_get regs 22 /\
       Sem.reg_get R 18 = Sem.reg_get regs 18 /\ Sem.reg_get R 20 = Sem.reg_get regs 20 /\
       mem' = mem)
    (Post B APIf ra g)).
  - exact Hhalt.
  - (* 0x8229c: bltz a0,82bf4 -- not taken (a0 = ingest result >= 0) *)
    assert (Hr10 : Sem.reg_get regs (10%bv) = Z_to_bv 64 v0) by
      (unfold rg in Ha0r; rewrite <- Ha0r; unfold getr; reflexivity).
    step.
    match goal with
    | |- evt _ _ (MS _ _ (if bv_lts (Sem.reg_get ?M ?r) ?z then _ else _) _ _ _ _) =>
        assert (Hval : Sem.reg_get M r = Z_to_bv 64 v0) by
          (transitivity (Sem.reg_get regs r);
           [symmetry; exact (Regs6ss.mkR_of_eqv regs r eq_refl) | exact Hr10]);
        assert (Hcf : bv_lts (Sem.reg_get M r) z = false) by
          (rewrite Hval; unfold bv_lts; rewrite !signed_lit by lia; apply Z.ltb_ge; lia);
        rewrite Hcf; cbv_concl_iota; clear Hcf
    end.
    apply evt_done; hnf; do 3 eexists; split; [reflexivity|];
      split; [reflexivity|]; do 13 (split; [regeq|]); reflexivity.
  - (* the split cut at 0x822a0: same registers, same memory, model only materialized *)
    intros R pc' mem' regs' md' (Hpc & E2 & E3 & E4 & E8 & E9 & E19 & E26 & E21 & E23 & E24 & E22 & E18 & E20 &
      Hmem)
      Hreg Hmat.
    subst pc' mem'.
    assert (G2 : getr regs' 2 = getr regs 2)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G3 : getr regs' 3 = getr regs 3)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G4 : getr regs' 4 = getr regs 4)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G8 : getr regs' 8 = getr regs 8)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G9 : getr regs' 9 = getr regs 9)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G19 : getr regs' 19 = getr regs 19)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G21 : getr regs' 21 = getr regs 21)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G22 : getr regs' 22 = getr regs 22)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G23 : getr regs' 23 = getr regs 23)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G24 : getr regs' 24 = getr regs 24)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G26 : getr regs' 26 = getr regs 26)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G18 : getr regs' 18 = getr regs 18)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G20 : getr regs' 20 = getr regs 20)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (ASP : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite G2; reflexivity).
    apply (to_exit_822a0 j Hexit).
    exists phi, regs', mem, md', fr. rewrite SEGS.
    split; [reflexivity|].
    split; [exact (sl_fra_move B APIf ra g fr _ regs regs' mem md md' HFRA G2 G3 G4 G8 G9 G19 G26 Hmat)|].
    split; [eapply ent_mat; [exact HENT | exact Hmat]|].
    split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|].
    split; [exact (flsi_regs g j fr regs regs' mem HFLSI G9)|].
    split.
    { destruct HLK as (HLj & HL21 & HLour). split; [exact HLj|].
      split; [unfold rg in *; rewrite G21; exact HL21 | exact HLour]. }
    split; [unfold rg in *; rewrite G23; exact Hs7|].
    split; [unfold rg in *; rewrite G22; exact Hs22|].
    split; [exact Hrec40|].
    split.
    { exists A.
      split; [unfold rg in *; rewrite G9; exact Hs1|].
      split; [exact Hv232|]. split; [exact Hb192|].
      split; [exact Hq136|]. split; [exact Hq120|]. split; [exact Hq176|].
      split; [exact Happ|]. split; [exact Hw240|].
      split; [unfold rg in *; rewrite G24; exact Hs24|].
      split; [|exact HL12].
      intro HfL. destruct (Hrecg HfL) as (HRI & Hphiw & Hrecw).
      split; [exact HRI|]. split; [rewrite ASP; exact Hphiw | exact Hrecw]. }
    split; [unfold rg in *; rewrite G18; exact Hs18|].
    split; [exact Hrecb|].
    split; [exact (spill_regs regs regs' mem _ _ H152 G9)|].
    split; [exact (spill_regs regs regs' mem _ _ H280 G9)|].
    (* the bltz writes no register and no memory: IFS3 and s4 cross unchanged *)
    split.
    { destruct HIFS3 as (HID & HFG & HFSj). split; [exact HID|]. split; [exact HFG|].
      exact (f17_fsj_regs g fr j regs regs' mem HFSj G9). }
    unfold rg in *. rewrite G20. exact Hs20.
Qed.

End F17.
