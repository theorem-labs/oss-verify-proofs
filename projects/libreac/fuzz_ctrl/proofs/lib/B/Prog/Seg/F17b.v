(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names and numbers changed; 1592 of its 1709 lines of code are new or changed and 894 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F12.v, with its module paths, module names and addresses changed; 1175 of its 1288 lines of code are new or changed and 1596 lines of the source are left out. *)
(* Segment F17b of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, libreac v1.9.0 image B): the opens_record body,
   from the split cut 0x82468 (the official Inv_B82468_at of lib/B/Prog/SlotInv.v) to the F18 entry cut 0x82634
   (Inv_B82634_at), S_F17b of forms-asan-ubsan-v190.md. The v1.9.0 move of the patched-image seg_F17b
   (a working branch 0e6fdff1ed1, lib/B/Prog/Seg/F17.v (not in this delivery); patched 0x823e4-0x825b4), the B twin of image A's v1.9
   seg_F17b (a working branch): v1.9.0 copies the first fragment's body into the frame object `first`
   with `jal __asan_memcpy` where the patched image saved two body bytes and the count to spills.
     0x82468 sltiu a0,s4,50 ; 0x8246c ld a1,248(s1) ; 0x82470 or a0,a0,a1 ; 0x82474 bnez a0,82634
       -- the length-and-sum guard: [A+248] = 1 - sum_ok (FS9), so the body runs exactly when 50 <= len_j and
          the block sum is 0.
     0x82478-0x825d8: the UBSan pointer-overflow checks T29-T39 (never taken: Phi <> 0 and Phi + 50 <= 2^64),
       the nine instrumented shadow checks of the record bytes Phi + 16 .. 19, 22 .. 26 (each slow block
       `andi; bge` leaves the error path aside), and the nine byte tests (16 = 0xcd, 17 = 0xea, 18 = 4,
       19 = s6 = 1, 22 = 0, 23 = 2, 24 = 0, 25 = 0xfe, 1 <= 26 <= 22); a failed test branches to 0x82634.
     0x825dc-0x82630 (all tests passed, f_opens true): s1 = A, [A+312] = Phi + 18 (FM), [A+168] = fr + 2880 and
       [A+88] = fr + 2885 (FLI): `sw s6,0(a1)` stores have = 1 to fr + 2880, the shadow check of Phi + 26
       (slow block 0x82ea0 `andi; blt` back to 0x82604), `sb a2,4(a0)` stores n = gg[26] to fr + 2884, T40-T41,
       and `jal __asan_memcpy` (a0 = fr + 2885, a1 = Phi + 27, a2 = n) copies gg[27 .. 27 + n) into the body of
       `first`. The contract (lib/B/Prog/asan_memcpy_c.v) is a Section Hypothesis; Seg/Tac_f17b.v runs it on
       the normalized memory (no cut carries mem_inv, push 5c).
   Every exit reaches 0x82634 with s1, s2, s4, s6, s8, s9, s11 and the FRA registers kept. The model step: turn
   S j's first-fragment state (SlotModel.turn) is (1, gg[26], gg[27 .. 27 + gg[26])) when f_opens holds and turn
   j's otherwise, which is the exit's FSj (S j) (memory facts at fr + 2880 .. fr + 2920, SlotInv.FSb); IDj / FGj
   (S j) are the entry's RECS. FRA and ENT cross the write set [fr + 2880, fr + 2885 + n) u [sp - 2224, sp) by
   Tac_p12.tp_fra_ent; the single lazy-model run is Tac_slot.sl_run. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require bcmp_wrap_c asan_memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro Tac_p12 Tac_f17b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require PropExec.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Import ListNotations.
(* lib.Prog's RcFrag chain loads lib/Reusable/YK11.v, so the short name YK11 would resolve to that copy; this
   file's registers, mkst and FPState must be image B's, as SlotInv's and Tac_slot's are. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module SF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec.StrFun.
(* The wrapper_bcmp stack-scratch size, in the spelling of SlotInv's official cuts. *)
Module BW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.bcmp_wrap_c.
Module KNC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_kind_name_c.
Module ACPY := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memcpy_c.
(* The fragment / identity record model (bat, fg_fr, fg_first, ...) and the block sum. *)
Module RF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFrag.
Module RM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcModel.
(* The step engine's value functions (v_sltiu / v_or), for the length-and-sum guard at 0x82468. *)
Module ULPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.PropExec.
Module UEx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Exec.
Module LEx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

Local Notation memcmp_model := SF.memcmp_model.

(* A Lib.Exec run is a UL run: the two step relations have the same body (lib/B/Prog/Seg/F26.v f26_lu_evt). *)
Lemma f17_lu_msteps : forall s s', LEx.msteps rsegs s s' -> UEx.msteps rsegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH]; [apply UEx.msteps_refl|].
  eapply UEx.msteps_cons; [exact Hs | exact IH].
Qed.
Lemma f17_lu_evt : forall Q ms, LEx.evt rsegs Q ms -> UEx.evt rsegs Q ms.
Proof. intros Q ms (ms' & H & HQ). exists ms'. split; [exact (f17_lu_msteps _ _ H) | exact HQ]. Qed.

(* ---- The model side of the opens_record body (ifs-design.md section 6, item 3). ---- *)

Lemma f17_g_length : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. unfold t_g. apply fr50_length. Qed.

Lemma f17_bat_range : forall l k, 0 <= RF.bat l k < 256.
Proof.
  intros l k. unfold RF.bat.
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat k) l (Z_to_bv 8 0))) as H.
  unfold bv_modulus in H. cbn in H. lia.
Qed.

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



(* f_opens from the body's nine byte tests, the length flag and the block sum (image B tests gg[26] with a `beqz`
   and a `bltu 22` instead of image A's single range compare), and its negation from any one of them. *)
Lemma f17_fopens_true : forall len g,
  (50 <=? len) = true ->
  negb (RF.bat g 16 =? 205) = false -> negb (RF.bat g 17 =? 234) = false ->
  negb (RF.bat g 18 =? 4) = false -> negb (RF.bat g 19 =? 1) = false ->
  negb (RF.bat g 22 =? 0) = false -> negb (RF.bat g 23 =? 2) = false ->
  negb (RF.bat g 24 =? 0) = false -> negb (RF.bat g 25 =? 254) = false ->
  (RF.bat g 26 =? 0) = false -> negb (RF.bat g 26 <=? 22) = false ->
  (RM.blocksum (skipn 18 g) =? 0) = true ->
  f_opens len g = true.
Proof.
  intros len g H50 H16 H17 H18 H19 H22 H23 H24 H25 H26a H26b Hbs.
  apply Bool.negb_false_iff in H16. apply Bool.negb_false_iff in H17.
  apply Bool.negb_false_iff in H18. apply Bool.negb_false_iff in H19.
  apply Bool.negb_false_iff in H22. apply Bool.negb_false_iff in H23.
  apply Bool.negb_false_iff in H24. apply Bool.negb_false_iff in H25.
  apply Bool.negb_false_iff in H26b.
  assert (Hn1 : (1 <=? RF.fg_n g) = true).
  { unfold RF.fg_n. apply Z.leb_le. apply Z.eqb_neq in H26a.
    pose proof (f17_bat_range g 26). lia. }
  unfold f_opens, RF.fg_fr.
  rewrite H50, H16, H17, H18, H19, H22, H23, H24, H25, Hn1, Hbs.
  unfold RF.fg_n in H26b |- *. rewrite H26b. reflexivity.
Qed.

Lemma f17_fopens_false : forall len g,
  ((50 <=? len) = false \/ negb (RF.bat g 16 =? 205) = true \/ negb (RF.bat g 17 =? 234) = true \/
   negb (RF.bat g 18 =? 4) = true \/ negb (RF.bat g 19 =? 1) = true \/ negb (RF.bat g 22 =? 0) = true \/
   negb (RF.bat g 23 =? 2) = true \/ negb (RF.bat g 24 =? 0) = true \/ negb (RF.bat g 25 =? 254) = true \/
   (RF.bat g 26 =? 0) = true \/ negb (RF.bat g 26 <=? 22) = true \/
   (RM.blocksum (skipn 18 g) =? 0) = false) ->
  f_opens len g = false.
Proof.
  intros len g H. unfold f_opens, RF.fg_fr, RF.fg_n.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]].
  - rewrite H. reflexivity.
  - rewrite Bool.negb_true_iff in H. rewrite H, ?Bool.andb_false_r. reflexivity.
  - rewrite Bool.negb_true_iff in H. rewrite H, ?Bool.andb_false_r. reflexivity.
  - rewrite Bool.negb_true_iff in H. rewrite H, ?Bool.andb_false_r. reflexivity.
  - rewrite Bool.negb_true_iff in H. rewrite H, ?Bool.andb_false_r. reflexivity.
  - rewrite Bool.negb_true_iff in H. rewrite H, ?Bool.andb_false_r. reflexivity.
  - rewrite Bool.negb_true_iff in H. rewrite H, ?Bool.andb_false_r. reflexivity.
  - rewrite Bool.negb_true_iff in H. rewrite H, ?Bool.andb_false_r. reflexivity.
  - rewrite Bool.negb_true_iff in H. rewrite H, ?Bool.andb_false_r. reflexivity.
  - apply Z.eqb_eq in H. rewrite H. cbn. rewrite ?Bool.andb_false_r. reflexivity.
  - rewrite Bool.negb_true_iff in H. rewrite H, ?Bool.andb_false_r. reflexivity.
  - rewrite H, ?Bool.andb_false_r. reflexivity.
Qed.


(* ---- The turn's two frame records keep fixed lengths (model): the fragment record t_FG j 72 bytes (fg_next keeps
   72 in every class) and the identity record t_ID j 38 bytes (every ingest keeps 38, RcIdentModel.ING_length).
   Copied from prover a Theorem Labs lane's lib/B/Prog/Seg/F20.v (a working branch 81dc3c31079, its rl_ lemmas), which this file does not
   import. IFS's transport across the call needs both records inside the frame body. ---- *)
Lemma f18_fg_n : forall len g, fg_fr len g = true -> 1 <= fg_n g <= 22.
Proof.
  intros len g H. unfold fg_fr in H. rewrite !andb_true_iff in H.
  destruct H as (H & _). destruct H as (H & Hn2). destruct H as (_ & Hn1).
  apply Z.leb_le in Hn1. apply Z.leb_le in Hn2. lia.
Qed.
Lemma f18_keep_T : forall st g, fg_keep st g = true -> fg_T st g <= 64.
Proof.
  intros st g H. unfold fg_keep in H. rewrite !andb_true_iff in H.
  destruct H as (_ & H). apply Z.leb_le in H. lia.
Qed.
Lemma f18_next_length : forall f fr pa pp pn len st g, length st = 72%nat -> length g = 50%nat ->
  length (fg_next st g (fg_class f fr pa pp pn len st g)) = 72%nat.
Proof.
  intros f fr pa pp pn len st g HL HG. unfold fg_class.
  destruct ((f =? 0) || (fr =? 0) || (pa =? 0) || (pp =? 0) || (pn =? 0)); [cbn [fg_next]; exact HL|].
  destruct (fg_fr len g) eqn:FR; cbn [negb]; [|cbn [fg_next]; exact HL].
  destruct (bat g 19 =? 1).
  - cbn [fg_next]. pose proof (f18_fg_n len g FR) as Hn. unfold fg_first, fg_body.
    rewrite !length_app, length_skipn, (RcFragLib.rf_bsl_length g 6 6),
      (RcFragLib.rf_bsl_length g 27 (fg_n g)) by lia.
    cbn [length]. lia.
  - destruct (fg_keep st g) eqn:KEEP; cbn [negb]; [|cbn [fg_next]; apply RcFragLib.rf_clear_length; exact HL].
    destruct (fg_close st g); cbn [negb fg_next]; apply RcFragLib.rf_clear_length, RcFragLib.rf_fg_join_length;
      solve [exact HL | exact HG | apply (f18_fg_n len); exact FR | apply f18_keep_T; exact KEEP].
Qed.
Lemma f18_FG_length : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - reflexivity.
  - unfold t_FG in *. rewrite fst_at_S. unfold turn.
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_fg]; unfold fg_st, fcls;
      apply (f18_next_length 1 1 1 1 1); solve [exact IH | unfold t_g; apply fr50_length].
Qed.
Lemma f18_ID_length : forall inp j, length (t_ID inp j) = 38%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - reflexivity.
  - unfold t_ID in *. rewrite fst_at_S. unfold turn. cbv zeta.
    assert (Hr : length (rp_id (fs_id (fst_at inp j)) (t_len inp j) (t_g inp j)) = 38%nat).
    { unfold rp_id. match goal with |- context [if ?c then _ else _] => destruct c end;
        [apply RcIdentModel.ING_length; exact IH | exact IH]. }
    assert (Hf : length (fg_id (rp_id (fs_id (fst_at inp j)) (t_len inp j) (t_g inp j)) (t_len inp j)
                           (fs_fg (fst_at inp j)) (t_g inp j)) = 38%nat).
    { unfold fg_id. match goal with |- context [if ?c then _ else _] => destruct c end;
        [apply RcIdentModel.ING_length; exact Hr | exact Hr]. }
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_id]; exact Hf.
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
  pose proof (f18_fg_n len g F1) as Hn.
  destruct (RF.fg_keep st g) eqn:K1; cbn [negb].
  2:{ right. apply f17_clear_bat6. lia. }
  pose proof (f18_keep_T st g K1) as HT.
  assert (HJ : length (RF.fg_join st g) = 72%nat)
    by (apply rf_fg_join_length; [exact HL | exact HG | lia | lia]).
  destruct (RF.fg_close st g); cbn [negb]; right; apply f17_clear_bat6; lia.
Qed.

(* The opening turn writes fg_first, whose byte 6 is 1 and whose byte 7 is gg[26] = fg_n gg, and whose body from
   offset 8 is gg[27 .. 27 + fg_n gg) - which is exactly the body the memcpy copies into fr + 2885. *)
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
  rewrite app_assoc, skipn_app.
  assert (L8 : length (RF.bsl g 6 6 ++ [Z_to_bv 8 1; nth 26 g (Z_to_bv 8 0)]) = 8%nat)
    by (rewrite length_app, Hb6; reflexivity).
  rewrite L8.
  rewrite (skipn_all2 (RF.bsl g 6 6 ++ [Z_to_bv 8 1; nth 26 g (Z_to_bv 8 0)])) by lia.
  rewrite Nat.sub_diag, skipn_O, app_nil_l.
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
              (f18_FG_length (g_in g) j) (f17_g_length (g_in g) j)) as [Hsame | Hz].
  - rewrite Hsame. exact HFI.
  - intros H6. rewrite Hz in H6. discriminate H6.
Qed.

Lemma f17_fi_true : forall g j, f_opens (flen g j) (t_g (g_in g) j) = true ->
  FI (t_FG (g_in g) (S j)) (fst_at (g_in g) (S j)).
Proof.
  intros g j Hop.
  pose proof (f17_g_length (g_in g) j) as HG.
  assert (HFR : RF.fg_fr (t_len (g_in g) j) (t_g (g_in g) j) = true /\
                (RF.bat (t_g (g_in g) j) 19 =? 1) = true).
  { unfold f_opens, flen in Hop. apply andb_prop in Hop. exact Hop. }
  destruct HFR as (HFR1 & H19).
  pose proof (f18_fg_n _ _ HFR1) as Hn.
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


(* The two frame records (38 bytes at fr + 2688, 72 at fr + 2768) across the opens arm's write set: they lie in
   the frame below `first` [fr + 2880, fr + 2920) and apart from the callee window. *)
Lemma f17_idfg_keep : forall g fr j m m' W,
  IDj g fr (S j) m -> FGj g fr (S j) m -> LF.munch W m m' ->
  (forall x, fr + 2688 <= x < fr + 2840 -> LF.outside W x) ->
  IDj g fr (S j) m' /\ FGj g fr (S j) m'.
Proof.
  intros g fr j m m' W (Hid & Hidok) (Hfg & Hfgok) MU HW.
  split.
  - split; [|exact Hidok]. eapply fl_bytes; [exact Hid | exact MU |].
    rewrite f18_ID_length. intros x Hx. apply HW. lia.
  - split; [|exact Hfgok]. eapply fl_bytes; [exact Hfg | exact MU |].
    rewrite f18_FG_length. intros x Hx. apply HW. lia.
Qed.

(* ---- The code side: one loaded byte of the record, as the model's `bat`. The body reads each byte with
   `lbu` after its shadow check, so the compared word is the zero-extended byte. ---- *)
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
  rewrite le_word_1, b_extract8_id, zext_small. reflexivity.
Qed.

Lemma f17_beq_val : forall (l : list byte) (k c : Z), 0 <= k -> (Z.to_nat k < length l)%nat ->
  0 <= c < 2 ^ 64 ->
  bv_eqb (zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn (Z.to_nat k) l)))))
         (Z_to_bv 64 c)
    = (RF.bat l k =? c).
Proof.
  intros l k c Hk Hl Hc. rewrite (f17_byte_word l k Hk Hl). unfold RF.bat.
  exact (rf_beq (nth (Z.to_nat k) l (Z_to_bv 8 0)) c Hc).
Qed.

Lemma f17_bne_val : forall (l : list byte) (k c : Z), 0 <= k -> (Z.to_nat k < length l)%nat ->
  0 <= c < 2 ^ 64 ->
  negb (bv_eqb (zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn (Z.to_nat k) l)))))
               (Z_to_bv 64 c))
    = negb (RF.bat l k =? c).
Proof.
  intros l k c Hk Hl Hc. f_equal. exact (f17_beq_val l k c Hk Hl Hc).
Qed.

(* `li a0,22; bltu a0,a2` with a2 the loaded byte: taken exactly when the byte is above 22. *)
Lemma f17_bltu22 : forall (l : list byte) (k : Z), 0 <= k -> (Z.to_nat k < length l)%nat ->
  bv_ltu (Z_to_bv 64 22)
         (zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn (Z.to_nat k) l)))))
    = negb (RF.bat l k <=? 22).
Proof.
  intros l k Hk Hl. rewrite (f17_byte_word l k Hk Hl).
  pose proof (f17_bat_range l k) as HR.
  unfold bv_ltu. rewrite !MState.unsigned_lit by lia.
  destruct (Z.leb_spec (RF.bat l k) 22) as [H|H]; cbn [negb];
    [apply Z.ltb_ge | apply Z.ltb_lt]; lia.
Qed.

(* The length-and-sum guard 0x823e4 `sltiu a0,s4,50` / 0x823e8 `or a0,a0,s9`: a0 is 0 exactly when the record is
   long (50 <= len_j) and the block sum is 0 (s9 = 1 - sum_ok, FS9). *)
Lemma f17_guard : forall len s, 0 <= len < 2 ^ 64 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (ULPE.v_sltiu (Z_to_bv 64 len) 50))
                    (bv_unsigned (Z_to_bv 64 (1 - b2z s))))
  = Z_to_bv 64 (if (50 <=? len) && s then 0 else 1).
Proof.
  intros len s Hlen. unfold ULPE.v_sltiu.
  rewrite (MState.unsigned_lit len) by lia. change (bv_wrap 64 50) with 50.
  destruct (Z.ltb_spec len 50) as [H|H].
  - replace (50 <=? len) with false by (symmetry; apply Z.leb_gt; lia).
    destruct s; cbn [andb b2z]; vm_compute; reflexivity.
  - replace (50 <=? len) with true by (symmetry; apply Z.leb_le; lia).
    destruct s; cbn [andb b2z]; vm_compute; reflexivity.
Qed.


(* The first-fragment state of turn S j in the frame object `first` (SlotInv.FSb: have at fr + 2880, n at
   fr + 2884, the body at fr + 2885, 40 addressable bytes): turn j's when the record does not open, and
   (1, gg[26], gg[27 .. 27 + gg[26])) when it does. *)
Lemma f17_fsj_false : forall g fr j regs m, f_opens (flen g j) (t_g (g_in g) j) = false ->
  FSj g fr j regs m -> FSj g fr (S j) regs m.
Proof.
  intros g fr j regs m Hop (H0 & H4 & Hbody & Had & HFI).
  unfold FSj, FSb. rewrite fst_at_S.
  destruct (f17_turn_false (fst_at (g_in g) j) (t_len (g_in g) j) (t_g (g_in g) j) Hop) as (E1 & E2 & E3).
  rewrite E1, E2, E3.
  split; [exact H0|]. split; [exact H4|]. split; [exact Hbody|]. split; [exact Had|].
  exact (f17_fi_false g j Hop HFI).
Qed.

Lemma f17_fsj_true : forall g fr j regs m, f_opens (flen g j) (t_g (g_in g) j) = true ->
  u32 m (fr + 2880) 1 -> b8 m (fr + 2884) (RF.bat (t_g (g_in g) j) 26) ->
  bytes_at rsegs m (fr + 2885)
    (firstn (Z.to_nat (RF.bat (t_g (g_in g) j) 26)) (skipn 27 (t_g (g_in g) j))) ->
  addressable m (fr + 2880) 40 -> FSj g fr (S j) regs m.
Proof.
  intros g fr j regs m Hop H0 H4 Hbody Had.
  unfold FSj, FSb. rewrite fst_at_S.
  destruct (f17_turn_true (fst_at (g_in g) j) (t_len (g_in g) j) (t_g (g_in g) j) Hop) as (E1 & E2 & E3).
  rewrite E1, E2, E3.
  split; [exact H0|]. split; [exact H4|]. split; [exact Hbody|]. split; [exact Had|].
  exact (f17_fi_true g j Hop).
Qed.

(* A sub-range of a carried byte range (lib/B/Prog/Seg/F29.v ba_sub). *)
Lemma f17_ba_sub : forall m A bs k jj, bytes_at rsegs m A bs -> (k + jj <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn jj (skipn k bs)).
Proof.
  intros m A bs k jj (HA & HL & H) Hkj.
  assert (Lf : length (firstn jj (skipn k bs)) = jj) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i jj) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

(* A carried byte range, in the form the load steps consume. *)
Lemma f17_rd : forall m a bs n, bytes_at rsegs m a bs -> length bs = n ->
  ov_read_bytes rsegs m (wa a) n = Some bs.
Proof.
  intros m a bs n H Hl. subst n.
  pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as HH.
  rewrite Z.add_0_r, skipn_O, firstn_all in HH. exact HH.
Qed.

(* The spill base of a `spill` fact is the s1 of the cut (lib/B/Prog/Seg/F12.v f12_spill_base). *)
Lemma f17_base : forall regs A A' m off v,
  rg regs 9 A -> rg regs 9 A' -> 0 <= A < APPMEM_END -> 0 <= off <= 440 -> q64 m (A' + off) v -> A' = A.
Proof.
  intros regs A A' m off v HA HA' HAb Hoff Hq.
  pose proof (rg_eq64 _ _ _ _ HA' HA) as Hm.
  unfold q64, bytes_at in Hq. destruct Hq as (Hq0 & Hq1 & _).
  rewrite length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
  unfold APPMEM_END in HAb. change (2 ^ 64) with 18446744073709551616 in *.
  Z.div_mod_to_equations. lia.
Qed.

(* A spilled word read at the cut's spill base A. *)
Lemma f17_spq : forall regs m off v A, spill regs m off v -> rg regs 9 A ->
  0 <= A < APPMEM_END -> 0 <= off <= 440 -> q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & HA' & Hq) HA HAb Hoff.
  pose proof (f17_base regs A A' m off v HA HA' HAb Hoff Hq) as E. subst A'. exact Hq.
Qed.

(* An address below or above one interval is outside it. *)
Lemma f17_out1 : forall lo hi x, (x < lo \/ hi <= x) -> LF.outside [(lo, hi)] x.
Proof. intros lo hi x H. cbn [LF.outside]. split; [lia | exact I]. Qed.

Lemma f17_out2 : forall lo1 hi1 lo2 hi2 x, (x < lo1 \/ hi1 <= x) -> (x < lo2 \/ hi2 <= x) ->
  LF.outside [(lo1, hi1); (lo2, hi2)] x.
Proof. intros lo1 hi1 lo2 hi2 x H1 H2. cbn [LF.outside]. split; [lia|]. split; [lia | exact I]. Qed.

(* A byte of a carried byte range is readable. *)
Lemma f17_ba_rd : forall m a bs q, bytes_at rsegs m a bs -> a <= q < a + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa q) = Some b.
Proof.
  intros m a bs q (H0 & H1 & H) Hq.
  pose proof (H (Z.to_nat (q - a)) ltac:(lia)) as Hb. rewrite Z2Nat.id in Hb by lia.
  replace (a + (q - a)) with q in Hb by lia.
  destruct (nth_error bs (Z.to_nat (q - a))) as [b|] eqn:En; [exists b; exact Hb|].
  exfalso. apply nth_error_None in En. lia.
Qed.

(* Membership in a write set is decidable. *)
Lemma f17_outside_dec : forall W x, {LF.outside W x} + {~ LF.outside W x}.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [LF.outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; intros (_ & C); exact (H C)].
  destruct (Z_lt_le_dec x lo) as [L|L]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [L2|L2]; [right; intros (C & _); lia | left; split; [lia | exact H]].
Defined.

(* The first 6 bytes of a carried byte list (the bcmp operands of F18 / F19) and memcmp over them
   (lib/B/Prog/Seg/F18.v ba_first6 / memcmp_firstn of a working branch 0e6fdff1ed1). *)
Lemma f17_ba_first6 : forall m a bs, bytes_at rsegs m a bs -> (6 <= length bs)%nat ->
  bytes_at rsegs m a (firstn 6 bs) /\ length (firstn 6 bs) = 6%nat.
Proof.
  intros m a bs H Hl. split.
  - pose proof (f17_ba_sub m a bs 0 6 H ltac:(lia)) as Hs. cbn [Z.of_nat skipn] in Hs.
    rewrite Z.add_0_r in Hs. exact Hs.
  - rewrite length_firstn. lia.
Qed.

Lemma f17_memcmp_firstn : forall n l r, memcmp_model (firstn n l) (firstn n r) n = memcmp_model l r n.
Proof.
  induction n as [|n IH]; intros [|a l] [|b r]; cbn; try reflexivity.
  destruct (bv_unsigned a =? bv_unsigned b); [apply IH | reflexivity].
Qed.

Lemma f17_bsl_len_le : forall bs k n, (length (RF.bsl bs k n) <= Z.to_nat n)%nat.
Proof. intros bs k n. unfold RF.bsl. rewrite length_firstn. apply Nat.le_min_l. Qed.

(* SlotInv's record invariant rec_inv (v1.9: the sum-flag spill [A+248] and the block spill [A+312]) across a
   write that misses Phi's 50 bytes, the spills [A+248, A+320), every shadow byte (the shadow bytes of
   Phi+14 .. Phi+17) and kp's halfword [kp+20, kp+22) (F18.v rec_inv_kept with the v1.9 spill range). *)
Lemma f17_rec_inv_kept : forall g j phi A kp m m' W,
  rec_inv g j phi A kp m -> LF.munch W m m' ->
  (forall x, phi <= x < phi + 50 -> LF.outside W x) ->
  (forall x, A + 248 <= x < A + 320 -> LF.outside W x) ->
  (forall x, in_shadow x -> LF.outside W x) ->
  (0 <= kp -> kp + 22 <= 2 ^ 64 -> forall x, kp + 20 <= x < kp + 22 -> LF.outside W x) ->
  rec_inv g j phi A kp m'.
Proof.
  intros g j phi A kp m m' W (Hp0 & Hp50 & Hfl & Htk & Hpap & H312 & H18 & H34 &
     field16 & v14 & v15 & v16 & v17 & H248 & Hf16 & Hkpub & Hkp0 & Hb14 & Hb15 & Hb16 & Hb17 &
     Rv14 & Rv15 & Rv16 & Rv17 & Hs14 & Hs15 & Hs16 & Hs17 & Heq1 & Heq2)
    MU OWphi OWspill OWsh OWkp.
  assert (SHin : forall t x, 14 <= t <= 17 -> x = Z.shiftr (phi + t) 3 + ASAN_K -> LF.outside W x).
  { intros t x Ht ->. apply OWsh. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    exact (shadow_of_app (phi + t) (Hpap (phi + t) ltac:(lia))). }
  unfold rec_inv.
  split; [exact Hp0|]. split; [exact Hp50|]. split; [exact Hfl|]. split; [exact Htk|]. split; [exact Hpap|].
  split; [unfold q64 in *; eapply fl_bytes; [exact H312 | exact MU | rewrite length_le8; intros x Hx; apply OWspill; lia]|].
  split; [eapply fl_bytes; [exact H18 | exact MU | intros x Hx; apply OWphi; unfold t_blk in Hx;
            pose proof (f17_bsl_len_le (t_g (g_in g) j) 18 32) as BL; change (Z.to_nat 32) with 32%nat in BL; lia]|].
  split; [eapply fl_bytes; [exact H34 | exact MU | intros x Hx; apply OWphi;
            pose proof (f17_bsl_len_le (t_g (g_in g) j) 34 6) as BL; change (Z.to_nat 6) with 6%nat in BL; lia]|].
  exists field16, v14, v15, v16, v17.
  split; [unfold q64 in *; eapply fl_bytes; [exact H248 | exact MU | rewrite length_le8; intros x Hx; apply OWspill; lia]|].
  split; [unfold u16 in *; eapply fl_bytes; [exact Hf16 | exact MU | rewrite length_le2; intros x Hx; apply (OWkp Hkp0 Hkpub); lia]|].
  split; [exact Hkpub|]. split; [exact Hkp0|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb14 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb15 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb16 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb17 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [exact Rv14|]. split; [exact Rv15|]. split; [exact Rv16|]. split; [exact Rv17|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs14 | exact MU | cbn [length]; intros x Hx; apply (SHin 14); lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs15 | exact MU | cbn [length]; intros x Hx; apply (SHin 15); lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs16 | exact MU | cbn [length]; intros x Hx; apply (SHin 16); lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs17 | exact MU | cbn [length]; intros x Hx; apply (SHin 17); lia]|].
  split; [exact Heq1|]. exact Heq2.
Qed.


(* The memory facts of the opens arm, in two steps: the two stores of `first`'s have / n (mem -> m0), then the
   memcpy of the body (m0 -> m'). *)
Definition f17_mid (fr : Z) (gg : list byte) (mem m0 : word -> option byte) : Prop :=
  LF.munch [(fr + 2880, fr + 2885)] mem m0 /\ LF.wmono rsegs mem m0 /\
  u32 m0 (fr + 2880) 1 /\ b8 m0 (fr + 2884) (RF.bat gg 26).
Definition f17_cp (fr sp : Z) (gg : list byte) (m0 m' : word -> option byte) : Prop :=
  LF.munch [(fr + 2885, fr + 2885 + RF.bat gg 26); (sp - ACPY.ASAN_MEMCPY_K, sp)] m0 m' /\
  LF.wmono rsegs m0 m' /\ ro_agree rsegs m' /\ stk rsegs m' (sp - FN_STACK) sp /\
  bytes_at rsegs m' (fr + 2885) (firstn (Z.to_nat (RF.bat gg 26)) (skipn 27 gg)).

(* FLI's two spills of `first` (positions 2 and 28): [A+168] = fr + 2880 and [A+88] = fr + 2885. *)
Lemma f17_fli : forall g fr regs m, FLI g fr regs m ->
  spill regs m 168 (fr + 2880) /\ spill regs m 88 (fr + 2885).
Proof. intros g fr regs m H. unfold FLI in H. decompose [and] H. split; assumption. Qed.


Section F17b.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* v1.9.0's opens_record body copies the first fragment's body into the frame object `first` with
   `jal __asan_memcpy` at 0x82630 (the patched image saved two body bytes to spills instead), so this segment has
   a callee. *)
Hypothesis HMC : ACPY.asan_memcpy_contract.

(* Every exit of seg_F17b reaches pc 0x82634; discharge it through the official F18 entry cut of turn j. *)
Lemma to_exit_34 : forall j : nat,
  Hat B APIf ra (Inv_B82634_at B APIf ra) j ->
  forall g regs mem md,
    Inv_B82634_at B APIf ra g j (mkCfg (mkst regs (Z_to_bv 64 0x82634) mem (seg_rom rsegs)) md) ->
    SR rsegs (mkCfg (mkst regs (Z_to_bv 64 0x82634) mem (seg_rom rsegs)) md) (Post B APIf ra g).
Proof.
  intros j Hexit g regs mem md HI.
  pose proof (proj1 FF) as SEGS.
  pose proof (Hexit g _ HI) as HSR. rewrite SEGS in HSR. exact HSR.
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


(* Discharge a `getr R k = getr regs k` goal where R is a bvmap_set chain over mkR_of regs. *)
Ltac regeq :=
  simp_regs;
  first [ reflexivity
        | symmetry; eassumption
        | symmetry; apply Regs6ss.mkR_of_eqv; reflexivity
        | eassumption
        | apply Regs6ss.mkR_of_eqv; reflexivity ].

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

(* Shadow check of the byte phi+kk (srli; add s10; lb; bnez slow), after the caller set the address register to
   phi+kk; the slow block's scratch register is `scratch` (a2 for the checks on a0 at 16-18, a3 from 19 on). *)
Ltac shadowcheck phi mem Haddr kk scratch :=
  step; step;
  rewrite (unsigned_lit (phi + kk)) by (unfold APPMEM_END in *; lia);
  let Had := fresh "Had" in let b := fresh "b" in let HRsh := fresh "HRsh" in
  let OK := fresh "OK" in let BD := fresh "BD" in
  assert (Had : addressable mem (phi + kk) 1) by (apply (addressable_sub mem phi 50 kk 1 Haddr); lia);
  destruct (f17_shadow mem (phi + kk) Had) as (b & HRsh & OK & BD);
  step; step; converge scratch (phi + kk) b OK BD.


(* f_opens = false from the one failed test in the context: walk f17_fopens_false's disjunction and stop at the
   first disjunct that is a hypothesis (linear in the disjuncts; tauto would case-split on every disjunctive
   hypothesis, the shadow checks' `b = 0 \/ X mod 8 < b` included). *)
Ltac fop_false :=
  apply f17_fopens_false; repeat (first [ left; assumption | right ]); assumption.

(* Drop the 1-byte read facts of a finished check: a load step tries every read fact of its width. *)
(* Drop the shadow-check disjunctions `b = 0 \/ X mod 8 < b` too: lia case-splits on every disjunction in the
   context, and nine of them make each later trap check exponential. *)
Ltac clr1 := repeat match goal with
  | H : ov_read_bytes _ _ _ 1 = _ |- _ => clear H
  | H : bv_signed _ = 0 \/ _ |- _ => clear H
  end.

(* A failed byte test: the branch to 0x82634 is taken with memory unchanged and f_opens false. *)
Ltac f17_exit := apply evt_done; hnf; do 3 eexists; split; [reflexivity|];
  split; [reflexivity|]; do 13 (split; [regeq|]); left; split; [reflexivity | fop_false].

(* S_F17b: the opens_record body, from the split cut 0x82468 to the F18 entry cut 0x82634. *)
Lemma seg_F17b : forall j : nat,
  Hat B APIf ra (Inv_B82634_at B APIf ra) j -> Hat B APIf ra (Inv_B82468_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hn & Hj & HHB & Hs2 & H20 & HTURN &
    HLK & HFM & HFSj & Hrec40 & Hs11 &
    (A & kp & Hs1 & Hq280 & Hfst & Hw272 & Hs8 & Hkpwin & Hkpsp & Hphig & H8819) & HRECS & Hs9).
  subst c.
  rewrite SEGS.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A2 & sp & s5v & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof Hwin as (Hw0 & Hw1 & _).
  assert (HAr : 0 <= A2 < APPMEM_END) by (unfold AF.SLOT_STACK in *; lia).
  assert (EA : A = A2) by exact (f17_base regs A2 A mem 280 kp Hr9 Hs1 HAr ltac:(lia) Hq280).
  subst A2.
  assert (Hs9g : getr regs (9%bv) = Z_to_bv 64 A) by (unfold rg in Hs1; exact Hs1).
  pose proof HFM as (M184 & M24 & M22 & M25 & M312).
  pose proof HLK as (Hj255 & H240 & HOURb & HFLI).
  destruct (f17_fli g fr regs mem HFLI) as (F168 & F88).
  unfold FS9 in Hs9.
  pose proof (f17_spq regs mem 248 _ A Hs9 Hs1 HAr ltac:(lia)) as Q248.
  (* the turn's record length is a nonnegative 64-bit number (FTURN's byte count, HB's block) *)
  assert (Hlen0 : 0 <= flen g j).
  { destruct HTURN as (_ & _ & _ & Hle).
    pose proof (Nat2Z.is_nonneg (length (t_phi (g_in g) j))). unfold flen. lia. }
  assert (Hlenhi : flen g j <= APPMEM_END).
  { destruct HHB as (_ & (Hp0 & _ & Hpe & _)). unfold AC.a_size in Hpe.
    pose proof (Z.le_max_l (flen g j) 1). lia. }
  (* The one lazy-model run of this segment: Tac_slot.sl_run (AsanLift.evt_SR_canon_lazy), 0x82468 -> 0x82634.
     Pages it reads: [A+248], the record bytes [Phi + 16, Phi + 27) and their shadow bytes, [A+312], [A+168],
     [A+88]; in the callee the copy's source [Phi + 27, Phi + 49). Pages it writes (the opens arm only):
     [fr + 2880, fr + 2885 + gg[26]) and the callee's stack window [sp - 2224, sp). *)
  eapply (sl_run regs (Z_to_bv 64 0x82468) mem md
    (fun R pc' mem' =>
       pc' = Z_to_bv 64 0x82634 /\
       Sem.reg_get R 2 = Sem.reg_get regs 2 /\ Sem.reg_get R 3 = Sem.reg_get regs 3 /\
       Sem.reg_get R 4 = Sem.reg_get regs 4 /\ Sem.reg_get R 8 = Sem.reg_get regs 8 /\
       Sem.reg_get R 9 = Sem.reg_get regs 9 /\ Sem.reg_get R 19 = Sem.reg_get regs 19 /\
       Sem.reg_get R 26 = Sem.reg_get regs 26 /\ Sem.reg_get R 18 = Sem.reg_get regs 18 /\
       Sem.reg_get R 22 = Sem.reg_get regs 22 /\ Sem.reg_get R 24 = Sem.reg_get regs 24 /\
       Sem.reg_get R 27 = Sem.reg_get regs 27 /\ Sem.reg_get R 20 = Sem.reg_get regs 20 /\
       Sem.reg_get R 25 = Sem.reg_get regs 25 /\
       ((mem' = mem /\ f_opens (flen g j) (t_g (g_in g) j) = false) \/
        (f_opens (flen g j) (t_g (g_in g) j) = true /\
         exists m0, f17_mid fr (t_g (g_in g) j) mem m0 /\ f17_cp fr (AC.aspZ regs) (t_g (g_in g) j) m0 mem')))
    (Post B APIf ra g)).
  - exact Hhalt.
  - (* stepping the opens_record body from 0x82468 *)
    assert (Hs9r : Sem.reg_get regs (9%bv) = Z_to_bv 64 A) by
      (unfold rg in Hs1; rewrite <- Hs1; unfold getr; reflexivity).
    assert (Hs18r : Sem.reg_get regs (18%bv) = Z_to_bv 64 phi) by
      (unfold rg in Hs2; rewrite <- Hs2; unfold getr; reflexivity).
    assert (Hs20r : Sem.reg_get regs (20%bv) = Z_to_bv 64 (flen g j)) by
      (unfold rg in H20; rewrite <- H20; unfold getr; reflexivity).
    assert (Hs22r : Sem.reg_get regs (22%bv) = Z_to_bv 64 1) by
      (unfold rg in M22; rewrite <- M22; unfold getr; reflexivity).
    assert (Hs26r : Sem.reg_get regs (26%bv) = Z_to_bv 64 ASAN_K) by
      (unfold rg in Hr26; rewrite <- Hr26; unfold getr; reflexivity).
    assert (Hs27r : Sem.reg_get regs (27%bv) = Z_to_bv 64 (-8)) by
      (unfold rg in Hs11; rewrite <- Hs11; unfold getr; reflexivity).
    assert (IDW : bvmap_set (9%bv) (Z_to_bv 64 A)
                   (bvmap_set (18%bv) (Z_to_bv 64 phi)
                     (bvmap_set (20%bv) (Z_to_bv 64 (flen g j))
                       (bvmap_set (22%bv) (Z_to_bv 64 1)
                         (bvmap_set (26%bv) (Z_to_bv 64 ASAN_K)
                           (bvmap_set (27%bv) (Z_to_bv 64 (-8)) (Regs6ss.mkR_of regs))))))
                  = Regs6ss.mkR_of regs)
      by (rewrite <- Hs9r, <- Hs18r, <- Hs20r, <- Hs22r, <- Hs26r, <- Hs27r; cbn; reflexivity).
    rewrite <- IDW.
    (* 0x82468 sltiu a0,s4,50 ; 0x8246c ld a1,248(s1) ; 0x82470 or a0,a0,a1 ; 0x82474 bnez a0,82634 *)
    pose proof (f17_rd mem (A + 248) _ 8 Q248 (length_le8 _)) as HR248.
    step. step. step. step.
    rewrite (f17_guard (flen g j) (t_sum_ok (g_in g) j) ltac:(unfold APPMEM_END in *; lia)).
    destruct (Z.leb_spec 50 (flen g j)) as [Hl50|Hl50].
    + destruct (t_sum_ok (g_in g) j) eqn:ESUM.
      * (* the record is long and the block sum is 0: the opens_record body runs *)
        assert (Hbs : (RM.blocksum (skipn 18 (t_g (g_in g) j)) =? 0) = true).
        { unfold t_sum_ok, t_big in ESUM.
          replace (50 <=? t_len (g_in g) j) with true in ESUM
            by (symmetry; apply Z.leb_le; unfold flen in Hl50; lia).
          rewrite Bool.andb_true_l in ESUM. exact ESUM. }
        assert (H50t : (50 <=? flen g j) = true) by (apply Z.leb_le; lia).
        rewrite Bool.andb_true_l.
        match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
          replace c with false by (symmetry; vm_compute; reflexivity) end; cbv_concl_iota.
        destruct (Hrec40 ltac:(lia)) as (Haddr & _).
        destruct (Hphig ltac:(lia)) as (Hphiwin & Hphisp).
        assert (Hrbb : bytes_at rsegs mem phi (t_g (g_in g) j))
          by (apply (fturn_g g j phi regs mem HTURN); unfold flen in Hl50; lia).
        assert (Hrblen : length (t_g (g_in g) j) = 50%nat) by (apply f17_g_length).
        pose proof Haddr as Haddr'. destruct Haddr' as (Hphi0 & _ & HphiE & _).
        (* Phi <> 0 (HB's live block), for the T29 check and the wrap checks *)
        assert (Hphipos : 0 < phi) by (destruct HHB as (Hphinz & _); lia).
        assert (Hphi64 : phi + 50 <= 2 ^ 64) by (unfold APPMEM_END in HphiE; lia).
        assert (Ephi : bv_unsigned (Z_to_bv 64 phi) = phi) by (apply unsigned_lit; unfold APPMEM_END in *; lia).
        assert (Ephi18 : bv_unsigned (Z_to_bv 64 (phi + 18)) = phi + 18)
          by (apply unsigned_lit; unfold APPMEM_END in *; lia).
        (* 0x82478 beqz s2,82fa0 (T29): Phi <> 0 *)
        step. if_false.
        (* 0x8247c li a0,-19 ; 0x82480 bltu a0,s2 (T30): Phi + 18 does not wrap *)
        step. step. if_false.
        (* 0x82484 li a0,-16 ; 0x82488 bgeu s2,a0 (T31): Phi + 16 does not wrap *)
        step. step. if_false.
        (* check 1: Phi+16 = 0xcd *)
        step. (* addi a0,s2,16 *)
        shadowcheck phi mem Haddr 16 (Z_to_bv 5 12).
        assert (Hrr16 : ov_read_bytes rsegs mem (wa (phi + 16)) 1
                          = Some (firstn 1 (skipn (Z.to_nat 16) (t_g (g_in g) j)))).
        { pose proof (bytes_at_ov_read rsegs mem phi (t_g (g_in g) j) (Z.to_nat 16) 1 Hrbb ltac:(lia)) as H.
          replace (phi + Z.of_nat (Z.to_nat 16)) with (phi + 16) in H by lia. exact H. }
        step. step. step.
        rewrite (f17_bne_val (t_g (g_in g) j) 16 205 ltac:(lia) ltac:(lia) ltac:(lia)).
        match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:Hb16 end;
          cbv_concl_iota; [ f17_exit | ]. clr1.
        (* 0x824ac li a0,-18 ; 0x824b0 bltu a0,s2 (T32): Phi + 17 does not wrap *)
        step. step. if_false.
        (* check 2: Phi+17 = 0xea *)
        step. shadowcheck phi mem Haddr 17 (Z_to_bv 5 12).
        assert (Hrr17 : ov_read_bytes rsegs mem (wa (phi + 17)) 1
                          = Some (firstn 1 (skipn (Z.to_nat 17) (t_g (g_in g) j)))).
        { pose proof (bytes_at_ov_read rsegs mem phi (t_g (g_in g) j) (Z.to_nat 17) 1 Hrbb ltac:(lia)) as H.
          replace (phi + Z.of_nat (Z.to_nat 17)) with (phi + 17) in H by lia. exact H. }
        step. step. step.
        rewrite (f17_bne_val (t_g (g_in g) j) 17 234 ltac:(lia) ltac:(lia) ltac:(lia)).
        match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:Hb17 end;
          cbv_concl_iota; [ f17_exit | ]. clr1.
        (* check 3: b = Phi+18, b[0] = 4 (a0 = b stays live) *)
        step. shadowcheck phi mem Haddr 18 (Z_to_bv 5 12).
        assert (Hrr18 : ov_read_bytes rsegs mem (wa (phi + 18)) 1
                          = Some (firstn 1 (skipn (Z.to_nat 18) (t_g (g_in g) j)))).
        { pose proof (bytes_at_ov_read rsegs mem phi (t_g (g_in g) j) (Z.to_nat 18) 1 Hrbb ltac:(lia)) as H.
          replace (phi + Z.of_nat (Z.to_nat 18)) with (phi + 18) in H by lia. exact H. }
        step. step. step.
        rewrite (f17_bne_val (t_g (g_in g) j) 18 4 ltac:(lia) ltac:(lia) ltac:(lia)).
        match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:Hb18 end;
          cbv_concl_iota; [ f17_exit | ]. clr1.
        (* 0x824f4 li a1,-1 ; 0x824f8 beq a0,a1 (T33): b + 1 does not wrap *)
        step. step. if_false.
        (* check 4: b[1] = Phi[19] = s6 = 1 *)
        step. shadowcheck phi mem Haddr 19 (Z_to_bv 5 13).
        assert (Hrr19 : ov_read_bytes rsegs mem (wa (phi + 19)) 1
                          = Some (firstn 1 (skipn (Z.to_nat 19) (t_g (g_in g) j)))).
        { pose proof (bytes_at_ov_read rsegs mem phi (t_g (g_in g) j) (Z.to_nat 19) 1 Hrbb ltac:(lia)) as H.
          replace (phi + Z.of_nat (Z.to_nat 19)) with (phi + 19) in H by lia. exact H. }
        step. step.
        rewrite (f17_bne_val (t_g (g_in g) j) 19 1 ltac:(lia) ltac:(lia) ltac:(lia)).
        match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:Hb19 end;
          cbv_concl_iota; [ f17_exit | ]. clr1.
        (* 0x82518 li a1,-5 ; 0x8251c bltu a1,a0 (T34) *)
        step. step. if_false.
        (* check 5: b[4] = Phi[22] = 0 *)
        step. shadowcheck phi mem Haddr 22 (Z_to_bv 5 13).
        assert (Hrr22 : ov_read_bytes rsegs mem (wa (phi + 22)) 1
                          = Some (firstn 1 (skipn (Z.to_nat 22) (t_g (g_in g) j)))).
        { pose proof (bytes_at_ov_read rsegs mem phi (t_g (g_in g) j) (Z.to_nat 22) 1 Hrbb ltac:(lia)) as H.
          replace (phi + Z.of_nat (Z.to_nat 22)) with (phi + 22) in H by lia. exact H. }
        step. step.
        rewrite (f17_bne_val (t_g (g_in g) j) 22 0 ltac:(lia) ltac:(lia) ltac:(lia)).
        match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:Hb22 end;
          cbv_concl_iota; [ f17_exit | ]. clr1.
        (* 0x8253c li a1,-6 ; 0x82540 bltu a1,a0 (T35) *)
        step. step. if_false.
        (* check 6: b[5] = Phi[23] = 2 *)
        step. shadowcheck phi mem Haddr 23 (Z_to_bv 5 13).
        assert (Hrr23 : ov_read_bytes rsegs mem (wa (phi + 23)) 1
                          = Some (firstn 1 (skipn (Z.to_nat 23) (t_g (g_in g) j)))).
        { pose proof (bytes_at_ov_read rsegs mem phi (t_g (g_in g) j) (Z.to_nat 23) 1 Hrbb ltac:(lia)) as H.
          replace (phi + Z.of_nat (Z.to_nat 23)) with (phi + 23) in H by lia. exact H. }
        step. step. step.
        rewrite (f17_bne_val (t_g (g_in g) j) 23 2 ltac:(lia) ltac:(lia) ltac:(lia)).
        match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:Hb23 end;
          cbv_concl_iota; [ f17_exit | ]. clr1.
        (* 0x82564 li a1,-7 ; 0x82568 bltu a1,a0 (T36) *)
        step. step. if_false.
        (* check 7: b[6] = Phi[24] = 0 *)
        step. shadowcheck phi mem Haddr 24 (Z_to_bv 5 13).
        assert (Hrr24 : ov_read_bytes rsegs mem (wa (phi + 24)) 1
                          = Some (firstn 1 (skipn (Z.to_nat 24) (t_g (g_in g) j)))).
        { pose proof (bytes_at_ov_read rsegs mem phi (t_g (g_in g) j) (Z.to_nat 24) 1 Hrbb ltac:(lia)) as H.
          replace (phi + Z.of_nat (Z.to_nat 24)) with (phi + 24) in H by lia. exact H. }
        step. step.
        rewrite (f17_bne_val (t_g (g_in g) j) 24 0 ltac:(lia) ltac:(lia) ltac:(lia)).
        match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:Hb24 end;
          cbv_concl_iota; [ f17_exit | ]. clr1.
        (* 0x82588 bltu s11,a0 (T37, s11 = -8) *)
        step. if_false.
        (* check 8: b[7] = Phi[25] = 0xfe *)
        step. shadowcheck phi mem Haddr 25 (Z_to_bv 5 13).
        assert (Hrr25 : ov_read_bytes rsegs mem (wa (phi + 25)) 1
                          = Some (firstn 1 (skipn (Z.to_nat 25) (t_g (g_in g) j)))).
        { pose proof (bytes_at_ov_read rsegs mem phi (t_g (g_in g) j) (Z.to_nat 25) 1 Hrbb ltac:(lia)) as H.
          replace (phi + Z.of_nat (Z.to_nat 25)) with (phi + 25) in H by lia. exact H. }
        step. step. step.
        rewrite (f17_bne_val (t_g (g_in g) j) 25 254 ltac:(lia) ltac:(lia) ltac:(lia)).
        match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:Hb25 end;
          cbv_concl_iota; [ f17_exit | ]. clr1.
        (* 0x825ac li a1,-9 ; 0x825b0 bltu a1,a0 (T38) *)
        step. step. if_false.
        (* check 9a: b[8] = Phi[26] into a1, beqz a1 -> 0x82634 *)
        step. shadowcheck phi mem Haddr 26 (Z_to_bv 5 13).
        assert (Hrr26 : ov_read_bytes rsegs mem (wa (phi + 26)) 1
                          = Some (firstn 1 (skipn (Z.to_nat 26) (t_g (g_in g) j)))).
        { pose proof (bytes_at_ov_read rsegs mem phi (t_g (g_in g) j) (Z.to_nat 26) 1 Hrbb ltac:(lia)) as H.
          replace (phi + Z.of_nat (Z.to_nat 26)) with (phi + 26) in H by lia. exact H. }
        step. step.
        rewrite (f17_beq_val (t_g (g_in g) j) 26 0 ltac:(lia) ltac:(lia) ltac:(lia)).
        match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:Hb26a end;
          cbv_concl_iota; [ f17_exit | ]. clr1.
        (* 0x825d0 beq a0,s11 (T39): b + 8 <> 0 *)
        step. if_false.
        (* check 9b: 0x825d4 li a0,22 ; 0x825d8 bltu a0,a1,82634 (b[8] > 22) *)
        step. step.
        rewrite (f17_bltu22 (t_g (g_in g) j) 26 ltac:(lia) ltac:(lia)).
        match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:Hb26b end;
          cbv_concl_iota; [ f17_exit | ]. clr1.
        (* every test passed: the record opens *)
        assert (Hop : f_opens (flen g j) (t_g (g_in g) j) = true)
          by exact (f17_fopens_true _ _ H50t Hb16 Hb17 Hb18 Hb19 Hb22 Hb23 Hb24 Hb25 Hb26a Hb26b Hbs).
        assert (Hn26 : 1 <= RF.bat (t_g (g_in g) j) 26 <= 22).
        { pose proof (f17_bat_range (t_g (g_in g) j) 26) as Hr.
          apply Z.eqb_neq in Hb26a. apply Bool.negb_false_iff, Z.leb_le in Hb26b. lia. }
        assert (Ebig : t_big (g_in g) j = true) by (unfold t_big; apply Z.leb_le; unfold flen in Hl50; lia).
        rewrite Ebig in M312.
        (* the record's model bytes stay an opaque list rb during the tail's stepping (image A's v1.9 F17b
           does the same): no step conversion may unfold t_g on the symbolic input *)
        clear HR248 Hkpwin Hkpsp Hloc H8819 Hw272.
        remember (t_g (g_in g) j) as rb eqn:Erb.
        pose proof (f17_spq regs mem 312 _ A M312 Hs1 HAr ltac:(lia)) as Q312.
        pose proof (f17_spq regs mem 168 _ A F168 Hs1 HAr ltac:(lia)) as Q168.
        pose proof (f17_spq regs mem 88 _ A F88 Hs1 HAr ltac:(lia)) as Q88.
        pose proof (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGTfr & Happfr).
        pose proof (fra_stk B APIf ra g fr _ regs mem md HFRA) as Hstkfr.
        assert (Hfr0 : 0 <= fr) by (unfold AC.GT in HGTfr; lia).
        pose proof (Hfst (fr + 2880) ltac:(lia)) as Hfl. pose proof (Hfst (fr + 2919) ltac:(lia)) as Hfh.
        assert (Hwrf : wr_at rsegs mem (fr + 2880) 40).
        { destruct Hstkfr as (Hk0 & Hk1 & Hkv). split; [lia|]. split; [unfold APPMEM_END in *; lia|].
          intros i Hi. exact (proj1 (Hkv (fr + 2880 + i) ltac:(lia))). }
        destruct (Tac_f17b.f17m_meta_bytes mem (phi + 26)
                    (addressable_sub mem phi 50 26 1 Haddr ltac:(lia) ltac:(lia) ltac:(lia)))
          as (b26 & Hsb26 & OK26 & BD26).
        (* 0x825dc ld a0,312(s1) ; 0x825e0 addi a0,a0,8 ; 0x825e4 ld a1,168(s1). Each load gets exactly the one
           read fact it needs (a load step tries every read fact of its width in the context). *)
        pose proof (f17_rd mem (A + 312) _ 8 Q312 (length_le8 _)) as HR312.
        step. clear HR312.
        step.
        pose proof (f17_rd mem (A + 168) _ 8 Q168 (length_le8 _)) as HR168.
        step. clear HR168.
        (* 0x825e8 sw s6,0(a1): have = 1 at fr + 2880 *)
        assert (HS0 : store_ok rsegs mem (wa (fr + 2880)) 4 = true).
        { replace (fr + 2880) with (fr + 2880 + 0) by lia.
          apply (wr_at_store_ok rsegs mem (fr + 2880) 40 0 4 Hwrf); lia. }
        assert (HS0' : store_ok rsegs mem (wa (fr + 2880 + 0)) 4 = true)
          by (apply (wr_at_store_ok rsegs mem (fr + 2880) 40 0 4 Hwrf); lia).
        step.
        remember (write_to_mem mem (wa (fr + 2880)) (le4 (Z_to_bv 64 1))) as M1 eqn:EM1.
        assert (MU1 : LF.munch [(fr + 2880, fr + 2885)] mem M1).
        { rewrite EM1. apply LF.munch_write; [apply LF.munch_refl | lia | rewrite length_le4; lia
          | cbn [LF.inside]; left; rewrite length_le4; lia]. }
        assert (HfrO : forall x, x < fr + 2880 \/ fr + 2885 <= x -> LF.outside [(fr + 2880, fr + 2885)] x)
          by (intros x Hx; apply f17_out1; exact Hx).
        assert (HshO : forall x, in_shadow x -> LF.outside [(fr + 2880, fr + 2885)] x).
        { intros x Hx. apply HfrO.
          destruct (Z_lt_le_dec x (fr + 2880)) as [L|L]; [left; exact L|].
          destruct (Z_lt_le_dec x (fr + 2885)) as [L2|L2]; [|right; exact L2].
          exfalso. exact (app_not_shadow x (Happfr x ltac:(lia)) Hx). }
        assert (Hap26 : app_mem (phi + 26)).
        { pose proof Haddr as (_ & _ & _ & Hab). destruct (Hab 26 ltac:(lia)) as (Hap & _). exact Hap. }
        assert (HshE : Z.shiftr (phi + 26) 3 + ASAN_K = shadow_addr (phi + 26))
          by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
        assert (HRs26 : ov_read_bytes rsegs M1 (wa (Z.shiftr (phi + 26) 3 + ASAN_K)) 1 = Some [b26]).
        { apply (f17_rd M1 _ [b26] 1); [|reflexivity].
          eapply fl_bytes; [exact Hsb26 | exact MU1 |]. cbn [length]. intros x Hx.
          apply HshO. replace x with (shadow_addr (phi + 26)) by (rewrite <- HshE; lia).
          apply shadow_of_app. exact Hap26. }
        assert (Q312a : q64 M1 (A + 312) (phi + 18)).
        { unfold q64 in *. eapply fl_bytes; [exact Q312 | exact MU1 |].
          rewrite length_le8. intros x Hx. apply HfrO. right. lia. }
        assert (Q168a : q64 M1 (A + 168) (fr + 2880)).
        { unfold q64 in *. eapply fl_bytes; [exact Q168 | exact MU1 |].
          rewrite length_le8. intros x Hx. apply HfrO. right. lia. }
        assert (Q88a : q64 M1 (A + 88) (fr + 2885)).
        { unfold q64 in *. eapply fl_bytes; [exact Q88 | exact MU1 |].
          rewrite length_le8. intros x Hx. apply HfrO. right. lia. }
        assert (Hrbb1 : bytes_at rsegs M1 phi (rb)).
        { eapply fl_bytes; [exact Hrbb | exact MU1 |]. rewrite Hrblen. intros x Hx. apply HfrO.
          destruct Hphiwin as [Hd|Hd]; [left|right]; lia. }
        (* 0x825ec li a1,9 ; 0x825f0 bltu a0,a1 (T40): Phi + 26 >= 9 *)
        assert (Ephi26 : bv_unsigned (Z_to_bv 64 (phi + 26)) = phi + 26)
          by (apply unsigned_lit; unfold APPMEM_END in *; lia).
        step. step. if_false.
        (* the shadow check of Phi + 26: srli a1,a0,3 ; add a1,a1,s10 ; lb a1,0(a1) ; bnez a1,82ea0 *)
        step. step.
        rewrite Ephi26.
        step. step.
        match goal with
        | |- evt ?segs ?Q (MS ?R ?F (if _ then _ else ?cont) ?fc ?rv ?m ?ro) =>
            enough (Gc : forall rr, evt segs Q (MS (bvmap_set (Z_to_bv 5 12) rr R) F cont fc rv m ro))
        end.
        2:{ intro rr26. clear OK26.
            assert (HRb26 : ov_read_bytes rsegs M1 (wa (phi + 26)) 1
                              = Some (firstn 1 (skipn (Z.to_nat 26) (rb)))).
            { pose proof (bytes_at_ov_read rsegs M1 phi (rb) (Z.to_nat 26) 1 Hrbb1 ltac:(lia)) as H.
              replace (phi + Z.of_nat (Z.to_nat 26)) with (phi + 26) in H by lia. exact H. }
            (* 0x82604 ld a1,312(s1) ; 0x82608 lbu a2,8(a1) ; 0x8260c ld a0,168(s1) *)
            pose proof (f17_rd M1 (A + 312) _ 8 Q312a (length_le8 _)) as HR312a.
            step. clear HR312a.
            step. clear HRb26.
            pose proof (f17_rd M1 (A + 168) _ 8 Q168a (length_le8 _)) as HR168a.
            step. clear HR168a.
            rewrite (f17_byte_word (rb) 26 ltac:(lia) ltac:(lia)).
            (* 0x82610 sb a2,4(a0): n at fr + 2884 *)
            assert (HSt4 : store_ok rsegs M1 (wa (fr + 2880 + 4)) 1 = true).
            { rewrite EM1. apply (wr_at_store_ok rsegs _ (fr + 2880) 40 4 1); [apply wr_at_write; exact Hwrf | lia | lia]. }
            assert (HSt4' : store_ok rsegs M1 (wa (fr + 2884)) 1 = true)
              by (replace (fr + 2884) with (fr + 2880 + 4) by lia; exact HSt4).
            step.
            match goal with |- evt _ _ (MS _ _ _ _ _ ?m2 _) => remember m2 as M2 eqn:EM2 end.
            assert (MU2 : LF.munch [(fr + 2880, fr + 2885)] M1 M2).
            { rewrite EM2. apply LF.munch_write; [apply LF.munch_refl | lia | rewrite ?length_le1; cbn [length]; lia
              | cbn [LF.inside]; left; rewrite ?length_le1; cbn [length]; lia]. }
            assert (MU12 : LF.munch [(fr + 2880, fr + 2885)] mem M2) by exact (LF.munch_trans _ _ _ _ MU1 MU2).
            assert (Q312b : q64 M2 (A + 312) (phi + 18)).
            { unfold q64 in *. eapply fl_bytes; [exact Q312 | exact MU12 |].
              rewrite length_le8. intros x Hx. apply HfrO. right. lia. }
            assert (Q88b : q64 M2 (A + 88) (fr + 2885)).
            { unfold q64 in *. eapply fl_bytes; [exact Q88 | exact MU12 |].
              rewrite length_le8. intros x Hx. apply HfrO. right. lia. }
            (* 0x82614 beqz a1 (T41): Phi + 18 <> 0 *)
            step. if_false.
            (* 0x82618 li a0,-10 ; 0x8261c ld a1,312(s1) ; 0x82620 bltu a0,a1 (T42): Phi + 18 <= 2^64 - 10 *)
            step.
            pose proof (f17_rd M2 (A + 312) _ 8 Q312b (length_le8 _)) as HR312b.
            step. step. if_false.
            (* 0x82624 ld a1,312(s1) ; 0x82628 addi a1,a1,9 ; 0x8262c ld a0,88(s1) ; 0x82630 jal __asan_memcpy *)
            step. clear HR312b. step.
            pose proof (f17_rd M2 (A + 88) _ 8 Q88b (length_le8 _)) as HR88b.
            step. clear HR88b. step.
            (* the call: Tac_f17b.f17_mc (the asan_memcpy contract on the normalized memory), back at 0x82634.
               The facts the copy needs, on the call's memory M2. *)
            pose proof (fra_frame B APIf ra g fr _ regs mem md HFRA) as (Hplace & _).
            pose proof (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hwlo & Hwstk).
            pose proof HRT as (HAC0 & HSW0 & _).
            pose proof HFSj as (HF0 & HF4 & HFbody & HFad & HFFI).
            assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
            assert (HKv : ACPY.ASAN_MEMCPY_K = 2224) by reflexivity.
            assert (HBWv : BW.BCMP_WRAP_K = 4560) by reflexivity.
            assert (HstkH : HIGHMEM_BEG <= AC.aspZ regs - FN_STACK).
            { pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
              pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hhi. lia. }
            assert (HAW1 : all_app [(fr + 2880, fr + 2885)]).
            { cbn [all_app]. split; [|exact I]. intros a Ha. apply Happfr. lia. }
            assert (WM1 : LF.wmono rsegs mem M1) by (rewrite EM1; apply LF.wmono_write; apply LF.wmono_refl).
            assert (WM2 : LF.wmono rsegs M1 M2) by (rewrite EM2; apply LF.wmono_write; apply LF.wmono_refl).
            assert (WM12 : LF.wmono rsegs mem M2) by exact (LF.wmono_trans rsegs _ _ _ WM1 WM2).
            assert (ROm2 : ro_agree rsegs M2).
            { apply (sl_ro_keep [(fr + 2880, fr + 2885)] mem M2 Hro MU12). intros x Hx. apply HfrO. left. lia. }
            assert (BSm2 : bytes_at rsegs M2 (phi + 27) (firstn (Z.to_nat (RF.bat rb 26)) (skipn 27 rb))).
            { pose proof (f17_ba_sub mem phi rb 27 (Z.to_nat (RF.bat rb 26)) Hrbb ltac:(rewrite Hrblen; lia)) as Hs.
              replace (phi + Z.of_nat 27) with (phi + 27) in Hs by lia.
              eapply fl_bytes; [exact Hs | exact MU12 |]. rewrite length_firstn, length_skipn, Hrblen.
              intros x Hx. apply HfrO. destruct Hphiwin as [Hd|Hd]; [left|right]; lia. }
            assert (STDm2 : stk rsegs M2 (fr + 2885) (fr + 2885 + RF.bat rb 26)).
            { destruct (LF.stk_split rsegs mem fr (fr + 2885) (fr + FRAME_BYTES) Hstkfr ltac:(lia)) as (_ & Hs1').
              destruct (LF.stk_split rsegs mem (fr + 2885) (fr + 2885 + RF.bat rb 26) (fr + FRAME_BYTES) Hs1'
                          ltac:(lia)) as (Hs2' & _).
              apply (LF.stk_transport rsegs [(fr + 2880, fr + 2885)] mem M2 _ _ Hs2' MU12 WM12).
              intros x Hx. left. apply HfrO. right. lia. }
            assert (ASm2 : addressable M2 (phi + 27) (RF.bat rb 26)).
            { exact (sl_addr_keep mem M2 [(fr + 2880, fr + 2885)] _ _
                       (addressable_sub mem phi 50 27 (RF.bat rb 26) Haddr ltac:(lia) ltac:(lia) ltac:(lia))
                       MU12 HAW1). }
            assert (ADm2 : addressable M2 (fr + 2885) (RF.bat rb 26)).
            { pose proof (addressable_sub mem (fr + 2880) 40 5 (RF.bat rb 26) HFad ltac:(lia) ltac:(lia) ltac:(lia))
                as Ha5.
              replace (fr + 2880 + 5) with (fr + 2885) in Ha5 by lia.
              exact (sl_addr_keep mem M2 [(fr + 2880, fr + 2885)] _ _ Ha5 MU12 HAW1). }
            assert (HappP : forall a, phi <= a < phi + 50 -> app_mem a).
            { intros a Ha. pose proof Haddr as (_ & _ & _ & Hab). destruct (Hab (a - phi) ltac:(lia)) as (Hap & _).
              replace (phi + (a - phi)) with a in Hap by lia. exact Hap. }
            assert (STKm2 : stk rsegs M2 (AC.aspZ regs - FN_STACK) (AC.aspZ regs)).
            { apply (LF.stk_transport rsegs [(fr + 2880, fr + 2885)] mem M2 _ _ Hwstk MU12 WM12).
              intros x Hx. left. apply HfrO. destruct (Hplace FN_STACK ltac:(lia)) as [P|P]; [right|left]; lia. }
            assert (ACm2 : asan_cells M2).
            { apply (asan_cells_kept [(fr + 2880, fr + 2885)] mem M2 HAC0 MU12).
              unfold RT_LO, RT_HI. cbn [disjoint_from]. split; [|exact I]. lia. }
            assert (SWm2 : shadow_rw M2).
            { exact (shadow_rw_kept mem M2 HSW0 (munch_meta _ mem M2 MU12 HAW1) WM12). }
            assert (Hsp2 : Sem.reg_get regs 2 = Z_to_bv 64 (AC.aspZ regs)).
            { rewrite Haspz. transitivity (getr regs 2); [unfold getr; reflexivity | exact Hr2]. }
            pose proof (Hplace ACPY.ASAN_MEMCPY_K ltac:(lia)) as HplK.
            match goal with |- evt _ _ (MS ?R0 ?F0 _ ?fc0 _ ?m0 _) =>
              eapply UEx.evt_cut;
              [ apply f17_lu_evt;
                apply (Tac_f17b.f17_mc HMC (Sem.reg_get R0 1) (Sem.reg_get R0 2) (Sem.reg_get R0 3)
                  (Sem.reg_get R0 4) (Sem.reg_get R0 5) (Sem.reg_get R0 6) (Sem.reg_get R0 7) (Sem.reg_get R0 8)
                  (Sem.reg_get R0 9) (Sem.reg_get R0 10) (Sem.reg_get R0 11) (Sem.reg_get R0 12) (Sem.reg_get R0 13)
                  (Sem.reg_get R0 14) (Sem.reg_get R0 15) (Sem.reg_get R0 16) (Sem.reg_get R0 17) (Sem.reg_get R0 18)
                  (Sem.reg_get R0 19) (Sem.reg_get R0 20) (Sem.reg_get R0 21) (Sem.reg_get R0 22) (Sem.reg_get R0 23)
                  (Sem.reg_get R0 24) (Sem.reg_get R0 25) (Sem.reg_get R0 26) (Sem.reg_get R0 27) (Sem.reg_get R0 28)
                  (Sem.reg_get R0 29) (Sem.reg_get R0 30) (Sem.reg_get R0 31) F0 fc0 m0
                  (fr + 2885) (phi + 27) (RF.bat rb 26) (AC.aspZ regs) (AC.aspZ regs - FN_STACK)
                  (firstn (Z.to_nat (RF.bat rb 26)) (skipn 27 rb)))
              | ] end.
            { reflexivity. }
            { reflexivity. }
            { reflexivity. }
            { reflexivity. }
            { exact Hsp2. }
            { lia. }
            { lia. }
            { assert (HHB0 : AC.GT <= HIGHMEM_BEG) by (unfold AC.GT, HIGHMEM_BEG; lia). lia. }
            { lia. }
            { lia. }
            { exact ROm2. }
            { exact BSm2. }
            { rewrite length_firstn, length_skipn, Hrblen. lia. }
            { exact STDm2. }
            { destruct Hphiwin as [Hd|Hd]; [left|right]; lia. }
            { exact ASm2. }
            { exact ADm2. }
            { apply HappP. lia. }
            { apply Happfr. lia. }
            { apply HappP. lia. }
            { apply Happfr. lia. }
            { unfold RT_HI. lia. }
            { destruct HplK as [P|P]; [left|right]; lia. }
            { destruct Hphisp as [P|P]; [left|right]; lia. }
            { exact STKm2. }
            { lia. }
            { exact HstkH. }
            { exact ACm2. }
            { exact SWm2. }
            intros ms' (R' & m' & -> & Hr2' & Hr3' & Hr4' & Hr8' & Hr9' & Hr18' & Hr19' & Hr20' & Hr21' & Hr22' &
              Hr23' & Hr24' & Hr25' & Hr26' & Hr27' & MUc & WMc & ROc & STc & BSc & _ & _).
            apply UEx.evt_done. hnf. do 3 eexists. split; [reflexivity|].
            split; [reflexivity|].
            split; [transitivity (getr R' 2); [unfold getr; reflexivity | rewrite Hr2'; regeq]|].
            split; [transitivity (getr R' 3); [unfold getr; reflexivity | rewrite Hr3'; regeq]|].
            split; [transitivity (getr R' 4); [unfold getr; reflexivity | rewrite Hr4'; regeq]|].
            split; [transitivity (getr R' 8); [unfold getr; reflexivity | rewrite Hr8'; regeq]|].
            split; [transitivity (getr R' 9); [unfold getr; reflexivity | rewrite Hr9'; regeq]|].
            split; [transitivity (getr R' 19); [unfold getr; reflexivity | rewrite Hr19'; regeq]|].
            split; [transitivity (getr R' 26); [unfold getr; reflexivity | rewrite Hr26'; regeq]|].
            split; [transitivity (getr R' 18); [unfold getr; reflexivity | rewrite Hr18'; regeq]|].
            split; [transitivity (getr R' 22); [unfold getr; reflexivity | rewrite Hr22'; regeq]|].
            split; [transitivity (getr R' 24); [unfold getr; reflexivity | rewrite Hr24'; regeq]|].
            split; [transitivity (getr R' 27); [unfold getr; reflexivity | rewrite Hr27'; regeq]|].
            split; [transitivity (getr R' 20); [unfold getr; reflexivity | rewrite Hr20'; regeq]|].
            split; [transitivity (getr R' 25); [unfold getr; reflexivity | rewrite Hr25'; regeq]|].
            right. split; [exact Hop|]. exists M2. split.
            - unfold f17_mid. split; [exact MU12|]. split; [exact WM12|].
              split.
              + unfold u32. rewrite EM2.
                apply (bytes_at_write_other rsegs M1 (fr + 2884) _ (fr + 2880) _);
                  [rewrite EM1; apply bytes_at_write_same; [lia | rewrite length_le4; lia]
                  | lia | rewrite length_le1; lia | rewrite length_le4, length_le1; lia].
              + unfold b8. rewrite EM2.
                replace (le1 (Z_to_bv 64 (RF.bat rb 26))) with [Z_to_bv 8 (RF.bat rb 26)]
                  by (unfold le1; cbn [Z_to_le_bytes];
                      rewrite unsigned_lit by (pose proof (f17_bat_range rb 26); lia); reflexivity).
                apply (bytes_at_write_same rsegs M1 (fr + 2884)); [lia | cbn [length]; lia].
            - exact (conj MUc (conj WMc (conj ROc (conj STc BSc)))). }
        destruct (Z.eqb_spec (bv_signed b26) 0) as [K0|K0].
        -- match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with false by (unfold sxb; rewrite K0; vm_compute; reflexivity) end;
           cbv_concl_iota;
           match goal with |- evt _ _ (MS ?R2 _ _ _ _ _ _) => exact (Gc (Sem.reg_get R2 (Z_to_bv 5 12))) end.
        -- assert (Hlt26 : (phi + 26) mod 8 < bv_signed b26) by
             (pose proof (Z.mod_pos_bound (phi + 26) 8 ltac:(lia)); destruct OK26 as [HH|HH];
              [exfalso; apply K0; exact HH | lia]).
           match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with true by (unfold sxb; rewrite bv_eqb_lit by (pose proof BD26; lia);
               replace (bv_signed b26 =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity) end;
           cbv_concl_iota.
           step. (* andi a2,a0,7 *)
           step. (* blt a2,a1,82604 *)
           match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with true by (unfold APPMEM_END in HphiE;
               rewrite (unsigned_lit (phi + 26)) by lia; rewrite land7 by lia; rewrite lts_sxb by lia;
               symmetry; apply Z.ltb_lt; lia) end;
           cbv_concl_iota;
           match goal with |- evt _ _ (MS ?R2 _ _ _ _ _ _) => exact (Gc (Sem.reg_get R2 (Z_to_bv 5 12))) end.
      * (* the block sum is nonzero: [A+248] = 1, the guard exits at 0x82634 with memory unchanged *)
        assert (Hbs : (RM.blocksum (skipn 18 (t_g (g_in g) j)) =? 0) = false).
        { unfold t_sum_ok, t_big in ESUM.
          replace (50 <=? t_len (g_in g) j) with true in ESUM
            by (symmetry; apply Z.leb_le; unfold flen in Hl50; lia).
          rewrite Bool.andb_true_l in ESUM. exact ESUM. }
        rewrite Bool.andb_true_l.
        match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
          replace c with true by (symmetry; vm_compute; reflexivity) end; cbv_concl_iota.
        f17_exit.
    + (* the record is short (len_j < 50): the guard exits at 0x82634 with memory unchanged *)
      assert (H50f : (50 <=? flen g j) = false) by (apply Z.leb_gt; lia).
      rewrite Bool.andb_false_l.
      match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        replace c with true by (symmetry; vm_compute; reflexivity) end; cbv_concl_iota.
      f17_exit.
  - (* continuation: assemble the official F18 entry cut Inv_B82634_at (turn j) at 0x82634 from K *)
    intros R pc' mem' regs' md'
      (Hpc & E2 & E3 & E4 & E8 & E9 & E19 & E26 & E18 & E22 & E24 & E27 & E20 & E25 & Hmem) Hreg Hmat.
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
    assert (G26 : getr regs' 26 = getr regs 26)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G18 : getr regs' 18 = getr regs 18)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G22 : getr regs' 22 = getr regs 22)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G24 : getr regs' 24 = getr regs 24)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G27 : getr regs' 27 = getr regs 27)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G20 : getr regs' 20 = getr regs 20)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (G25 : getr regs' 25 = getr regs 25)
      by ((etransitivity; [apply Hreg|]); unfold getr; cbn [bv_eqb negb]; eassumption).
    assert (ASP : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite G2; reflexivity).
    pose proof (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGTfr & Happfr).
    pose proof (fra_frame B APIf ra g fr _ regs mem md HFRA) as (Hplace & _).
    pose proof (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hwlo & Hwstk).
    pose proof (fra_stk B APIf ra g fr _ regs mem md HFRA) as Hstkfr.
    pose proof HFSj as (HF0 & HF4 & HFbody & HFad & HFFI).
    assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
    assert (Hfr0 : 0 <= fr) by lia.
    assert (HKv : ACPY.ASAN_MEMCPY_K = 2224) by reflexivity.
    assert (HBWv : BW.BCMP_WRAP_K = 4560) by reflexivity.
    pose proof (Hplace ACPY.ASAN_MEMCPY_K ltac:(lia)) as HplK.
    assert (HstkH : HIGHMEM_BEG <= sp - FN_STACK).
    { pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
      pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hhi. lia. }
    pose proof Hstkfr as (Hk0 & Hk1 & _).
    rewrite Haspz in Hmem, HplK.
    (* both arms: a write set W whose bytes lie in `first` [fr + 2880, fr + 2920) or in the callee window
       [sp - 2224, sp), the post memory readable on W, FRA / ENT moved, and IFS of turn S j *)
    assert (COM : exists W, LF.munch W mem mem' /\ LF.wmono rsegs mem mem' /\ all_app W /\
                  (forall x, ~ LF.outside W x ->
                     (fr + 2880 <= x < fr + 2920) \/ (sp - ACPY.ASAN_MEMCPY_K <= x < sp)) /\
                  (forall q, ~ LF.outside W q -> exists b, mrd rsegs mem' (wa q) = Some b) /\
                  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md' /\
                  ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md' /\
                  IFS g fr (S j) regs' mem').
    { destruct HRECS as (HID & HFG).
      destruct Hmem as [(-> & Hopf) | (Hopt & m0 & (MU0 & WM0 & U0 & B0) & (MUc & WMc & ROc & STc & BSc))].
      - exists []. split; [apply LF.munch_refl|]. split; [apply LF.wmono_refl|].
        split; [cbn [all_app]; exact I|].
        split; [intros x Hx; exfalso; apply Hx; exact I|].
        split; [intros q Hq; exfalso; apply Hq; exact I|].
        split; [exact (sl_fra_move B APIf ra g fr _ regs regs' mem md md' HFRA G2 G3 G4 G8 G9 G19 G26 Hmat)|].
        split; [eapply ent_mat; [exact HENT | exact Hmat]|].
        split; [exact HID|]. split; [exact HFG|].
        exact (f17_fsj_false g fr j regs' mem Hopf HFSj).
      - pose proof (f18_fg_n _ _ (proj1 (andb_prop _ _ Hopt))) as Hn26. unfold fg_n in Hn26.
        exists [(fr + 2880, fr + 2885 + RF.bat (t_g (g_in g) j) 26); (sp - ACPY.ASAN_MEMCPY_K, sp)].
        assert (MU : LF.munch [(fr + 2880, fr + 2885 + RF.bat (t_g (g_in g) j) 26);
                               (sp - ACPY.ASAN_MEMCPY_K, sp)] mem mem').
        { apply (LF.munch_trans _ mem m0 mem').
          - apply (LF.munch_weaken [(fr + 2880, fr + 2885)]); [|exact MU0].
            intros x Hx. cbn [LF.outside] in Hx |- *. destruct Hx as (H1 & _). split; [lia | exact I].
          - apply (LF.munch_weaken [(fr + 2885, fr + 2885 + RF.bat (t_g (g_in g) j) 26);
                                    (sp - ACPY.ASAN_MEMCPY_K, sp)]); [|exact MUc].
            intros x Hx. cbn [LF.outside] in Hx |- *. destruct Hx as (H1 & H2 & _).
            split; [lia|]. split; [exact H2 | exact I]. }
        assert (WM : LF.wmono rsegs mem mem') by exact (LF.wmono_trans rsegs _ _ _ WM0 WMc).
        assert (HWin : forall x, ~ LF.outside [(fr + 2880, fr + 2885 + RF.bat (t_g (g_in g) j) 26);
                                              (sp - ACPY.ASAN_MEMCPY_K, sp)] x ->
                         (fr + 2880 <= x < fr + 2920) \/ (sp - ACPY.ASAN_MEMCPY_K <= x < sp)).
        { intros x Hx. cbn [LF.outside] in Hx.
          destruct (Z_lt_le_dec x (fr + 2880)) as [L1|L1];
            [destruct (Z_lt_le_dec x (sp - ACPY.ASAN_MEMCPY_K)) as [L3|L3];
             [exfalso; apply Hx; split; [lia|]; split; [lia | exact I]|];
             destruct (Z_lt_le_dec x sp) as [L4|L4]; [right; lia|];
             exfalso; apply Hx; split; [lia|]; split; [lia | exact I]|].
          destruct (Z_lt_le_dec x (fr + 2885 + RF.bat (t_g (g_in g) j) 26)) as [L2|L2]; [left; lia|].
          destruct (Z_lt_le_dec x (sp - ACPY.ASAN_MEMCPY_K)) as [L3|L3];
            [exfalso; apply Hx; split; [lia|]; split; [lia | exact I]|].
          destruct (Z_lt_le_dec x sp) as [L4|L4]; [right; lia|].
          exfalso; apply Hx; split; [lia|]; split; [lia | exact I]. }
        assert (HAW : all_app [(fr + 2880, fr + 2885 + RF.bat (t_g (g_in g) j) 26); (sp - ACPY.ASAN_MEMCPY_K, sp)]).
        { cbn [all_app]. split; [intros a Ha; apply Happfr; lia|]. split; [|exact I].
          intros a Ha. unfold app_mem. right. unfold APPMEM_END in *. lia. }
        (* the have / n bytes survive the copy (it writes from fr + 2885 and in its own window) *)
        assert (U0' : u32 mem' (fr + 2880) 1).
        { unfold u32 in *. eapply fl_bytes; [exact U0 | exact MUc |]. rewrite length_le4. intros x Hx.
          cbn [LF.outside]. split; [lia|]. split; [destruct HplK as [P|P]; lia | exact I]. }
        assert (B0' : b8 mem' (fr + 2884) (RF.bat (t_g (g_in g) j) 26)).
        { unfold b8 in *. eapply fl_bytes; [exact B0 | exact MUc |]. cbn [length]. intros x Hx.
          cbn [LF.outside]. split; [lia|]. split; [destruct HplK as [P|P]; lia | exact I]. }
        assert (HRD : forall q, ~ LF.outside [(fr + 2880, fr + 2885 + RF.bat (t_g (g_in g) j) 26);
                                              (sp - ACPY.ASAN_MEMCPY_K, sp)] q ->
                        exists b, mrd rsegs mem' (wa q) = Some b).
        { intros q Hq. destruct (HWin q Hq) as [Hf|Hw].
          - destruct (Z_lt_le_dec q (fr + 2884)) as [L|L].
            + apply (f17_ba_rd mem' (fr + 2880) _ q U0'). rewrite length_le4. lia.
            + destruct (Z_lt_le_dec q (fr + 2885)) as [L2|L2].
              * apply (f17_ba_rd mem' (fr + 2884) _ q B0'). cbn [length]. lia.
              * destruct (Z_lt_le_dec q (fr + 2885 + RF.bat (t_g (g_in g) j) 26)) as [L3|L3].
                -- apply (f17_ba_rd mem' (fr + 2885) _ q BSc).
                   rewrite length_firstn, length_skipn, f17_g_length. lia.
                -- exfalso. apply Hq. cbn [LF.outside]. split; [lia|]. split; [destruct HplK as [P|P]; lia | exact I].
          - destruct STc as (_ & _ & Hs). destruct (Hs q ltac:(unfold FN_STACK in *; lia)) as (_ & b & Hb).
            exists b. exact Hb. }
        assert (HDW : rt_disjoint [(fr + 2880, fr + 2885 + RF.bat (t_g (g_in g) j) 26);
                                   (sp - ACPY.ASAN_MEMCPY_K, sp)]).
        { unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
            RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
            RT_AGLOB, RT_AGLOB_LEN.
          cbn [disjoint_from]. unfold HIGHMEM_BEG in *. repeat split; first [right; lia | left; lia | exact I]. }
        assert (HCL : forall q, ~ LF.outside [(fr + 2880, fr + 2885 + RF.bat (t_g (g_in g) j) 26);
                                              (sp - ACPY.ASAN_MEMCPY_K, sp)] q ->
                  (fr + 24 <= q < fr + FRAME_BYTES) \/ (Sfr fr <= q < Sfr fr + FRAME_SHADOW) \/
                  (AC.aspZ regs - FN_STACK <= q < AC.aspZ regs) \/
                  (bv_unsigned (getr regs 9) + 72 <= q < bv_unsigned (getr regs 9) + 336)).
        { intros q Hq. rewrite Haspz. destruct (HWin q Hq) as [Hf|Hw]; [left; lia | right; right; left; lia]. }
        destruct (Tac_p12.tp_fra_ent B APIf ra empty FF g fr _ regs mem mem' md
                    [(fr + 2880, fr + 2885 + RF.bat (t_g (g_in g) j) 26); (sp - ACPY.ASAN_MEMCPY_K, sp)]
                    HFRA HENT MU WM HDW ROc HCL HRD)
          as (HFRAm & HENTm).
        split; [exact MU|]. split; [exact WM|]. split; [exact HAW|]. split; [exact HWin|]. split; [exact HRD|].
        split; [exact (sl_fra_move B APIf ra g fr _ regs regs' mem' md md' HFRAm G2 G3 G4 G8 G9 G19 G26 Hmat)|].
        split; [eapply ent_mat; [exact HENTm | exact Hmat]|].
        assert (HRW : forall x, fr + 2688 <= x < fr + 2840 ->
                  LF.outside [(fr + 2880, fr + 2885 + RF.bat (t_g (g_in g) j) 26); (sp - ACPY.ASAN_MEMCPY_K, sp)] x).
        { intros x Hx. cbn [LF.outside]. split; [lia|]. split; [destruct HplK as [P|P]; lia | exact I]. }
        destruct (f17_idfg_keep g fr j mem mem' _ HID HFG MU HRW) as (HID' & HFG').
        split; [exact HID'|]. split; [exact HFG'|].
        apply (f17_fsj_true g fr j regs' mem' Hopt U0' B0' BSc).
        apply (sl_addr_keep mem mem' [(fr + 2880, fr + 2885 + RF.bat (t_g (g_in g) j) 26);
                                      (sp - ACPY.ASAN_MEMCPY_K, sp)] _ _ HFad MU HAW). }
    destruct COM as (W & MU & WM & HAW & HWin & HRD & HFRA' & HENT' & HIFS').
    assert (HWout : forall x, (x < fr + 2880 \/ fr + 2920 <= x) -> (x < sp - ACPY.ASAN_MEMCPY_K \/ sp <= x) ->
                      LF.outside W x).
    { intros x H1 H2. destruct (f17_outside_dec W x) as [Ho|Ho]; [exact Ho|]. exfalso. destruct (HWin x Ho); lia. }
    assert (HWsh : forall x, in_shadow x -> LF.outside W x).
    { intros x Hx. destruct (f17_outside_dec W x) as [Ho|Ho]; [exact Ho|]. exfalso.
      apply (app_not_shadow x); [|exact Hx].
      destruct (HWin x Ho) as [Hf|Hw]; [apply Happfr; lia | unfold app_mem; right; unfold APPMEM_END in *; lia]. }
    assert (MK : meta_kept mem mem') by exact (munch_meta _ mem mem' MU HAW).
    (* the spills: [A, A + 448) is above the frame and at or above sp *)
    assert (Ksp : forall off v, 0 <= off <= 440 -> spill regs mem off v -> spill regs' mem' off v).
    { intros off v Ho Hs. pose proof (f17_spq regs mem off v A Hs Hs1 HAr Ho) as Hq.
      exists A. split; [unfold rg in *; rewrite G9; exact Hs1|].
      unfold q64 in Hq |- *. eapply fl_bytes; [exact Hq | exact MU |].
      rewrite length_le8. intros x Hx. apply HWout; lia. }
    (* Phi's live block lies below stklo, apart from the frame and below the callee window *)
    assert (Hblk : forall x, phi <= x < phi + flen g j -> LF.outside W x).
    { intros x Hx.
      destruct (lw_blocks (APIf rc) _ mem md phi (AC.a_size (flen g j)) HAH
                  ltac:(apply in_or_app; left; unfold hb1; cbn [In]; left; reflexivity)) as [_ _ Hend _ Hall].
      assert (Hasz : flen g j <= AC.a_size (flen g j)) by (unfold AC.a_size; lia).
      apply HWout; [|left; lia].
      destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
      - left. pose proof (Hreal (fr + 2880) ltac:(lia)). lia.
      - destruct (Z_lt_le_dec x (fr + 2880)) as [L|L]; [left; exact L|].
        destruct (Z_lt_le_dec x (fr + 2920)) as [L2|L2]; [|right; exact L2].
        exfalso. destruct (Hall x ltac:(lia)) as (_ & _ & _ & _ & Hnfs). exact (Hnfs (Hfs x ltac:(lia))). }
    pose proof HLK as (Hj255' & H240' & HOURb' & HFLI').
    apply (to_exit_34 j Hexit).
    exists phi, regs', mem', md', fr. rewrite SEGS.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hn|]. split; [exact Hj|].
    split.
    { destruct HHB as (Hphinz & Haddrp). split; [exact Hphinz|]. exact (addressable_kept mem mem' _ _ Haddrp MK). }
    split.
    { destruct (Tac_ro.fli_mem _ _ _ _ HFLI') as (Had6 & Hstkf & Hid & Hfg & HKNT & Hfst40).
      apply (Tac_ro.lk_keep g fr j regs regs' mem mem' HLK).
      - unfold rg in *. rewrite G27. exact Hs11.
      - exact (addressable_kept mem mem' _ _ Had6 MK).
      - apply (Tac_f17b.f17m_stk_keep W mem mem' fr (fr + FRAME_BYTES) Hstkf MU WM).
        intros q _ Ho. exact (HRD q Ho).
      - exact (addressable_kept mem mem' _ _ Hid MK).
      - exact (addressable_kept mem mem' _ _ Hfg MK).
      - apply (Tac_ro.knt_munch W mem mem' HKNT MU MK). intros x Hx.
        apply HWout; left; unfold KNC.KIND_NAME, HIGHMEM_BEG in *; lia.
      - exact (addressable_kept mem mem' _ _ Hfst40 MK).
      - unfold OURb in *. eapply fl_bytes; [exact HOURb' | exact MU |]. rewrite OUR_length.
        intros x Hx. change (Z.of_nat 6) with 6 in Hx. apply HWout; [left; lia|].
        destruct HplK as [P|P]; [left|right]; lia.
      - intros off v Ho Hs. apply Ksp; [lia | exact Hs]. }
    (* s4 = len and FM (s6, s8, s9 kept; the spills [A+184] / [A+312]) *)
    split; [unfold rg in *; rewrite G20; exact H20|].
    split.
    { unfold FM. split; [apply Ksp; [lia | exact M184]|].
      split; [unfold rg in *; rewrite G24; exact M24|].
      split; [unfold rg in *; rewrite G22; exact M22|].
      split; [unfold rg in *; rewrite G25; exact M25|].
      apply Ksp; [lia | exact M312]. }
    (* the F18 entry's A / kp / [A+272] block, with its t_8819-guarded record facts *)
    split.
    { destruct Hw272 as (w272 & Hw272q & Hw272r & Hw272t & Hw272f).
      exists A, kp, w272.
      split; [unfold rg; rewrite G9; exact Hs1|].
      split; [lia|].
      split; [rewrite ASP, Haspz; exact Hspa|].
      split; [unfold rg; rewrite G18; exact Hs2|].
      split; [unfold rg; rewrite G24; exact Hs8|].
      split; [unfold q64 in *; eapply fl_bytes; [exact Hq280 | exact MU | rewrite length_le8; intros x Hx; apply HWout; lia]|].
      split; [unfold q64 in *; eapply fl_bytes; [exact Hw272q | exact MU | rewrite length_le8; intros x Hx; apply HWout; lia]|].
      split; [exact Hw272r|].
      split; [exact Hw272f|].
      intro E8819.
      assert (HfL : 50 <= flen g j).
      { pose proof E8819 as E0. unfold t_8819, t_big in E0. apply andb_prop in E0 as [E1 _].
        apply andb_prop in E1 as [E1' _]. apply Z.leb_le in E1'. unfold flen. exact E1'. }
      destruct (Hrec40 HfL) as (Haddr & _).
      destruct (Hphig HfL) as (Hphiwin & Hphisp).
      destruct (H8819 E8819) as (HRI & HL1 & HL2).
      pose proof HRI as (Hp0 & Hp50 & Hfl & Htk & Hpap & _).
      destruct HL1 as (L & ls & rs & HLq & HLb & HLl & HRb & HRl & HLm & HLad & HL6 & HL7 & HLsp & HLwin).
      destruct HL2 as (L2 & ls2 & rs2 & HL2q & HL2b & HL2l & HR2b & HR2l & HL2m & HL2ad & HL26 & HL27 & HL2sp & HL2win).
      destruct (f17_ba_first6 mem L ls HLb HLl) as (HLb6 & HLl6).
      destruct (f17_ba_first6 mem phi rs HRb HRl) as (HRb6 & HRl6).
      destruct (f17_ba_first6 mem L2 ls2 HL2b HL2l) as (HL2b6 & HL2l6).
      destruct (f17_ba_first6 mem (phi + 6) rs2 HR2b HR2l) as (HR2b6 & HR2l6).
      assert (HLr : 0 <= L < 2 ^ 64) by (destruct HLb as (H0 & H1 & _); lia).
      assert (HL2r : 0 <= L2 < 2 ^ 64) by (destruct HL2b as (H0 & H1 & _); lia).
      split; [exact (Hw272t E8819)|].
      split.
      { apply (f17_rec_inv_kept g j phi A kp mem mem' W HRI MU).
        - intros x Hx. apply HWout; [destruct Hphiwin as [Hd|Hd]; lia | destruct Hphisp as [Hd|Hd]; lia].
        - intros x Hx. apply HWout; lia.
        - exact HWsh.
        - intros Hkp0 Hkpb x Hx. apply HWout; [destruct Hkpwin as [Hd|Hd]; lia | destruct Hkpsp as [Hd|Hd]; lia]. }
      exists L, L2, (firstn 6 ls), (firstn 6 rs), (firstn 6 ls2), (firstn 6 rs2).
      split; [unfold q64 in HLq |- *; eapply fl_bytes; [exact HLq | exact MU | rewrite length_le8; intros x Hx; apply HWout; lia]|].
      split; [exact HLr|].
      split; [eapply fl_bytes; [exact HLb6 | exact MU |]; rewrite HLl6; intros x Hx;
              apply HWout; [destruct HLwin as [Hd|Hd]; lia | destruct HLsp as [Hd|Hd]; lia]|].
      split; [rewrite HLl6; lia|].
      split; [eapply fl_bytes; [exact HRb6 | exact MU |]; rewrite HRl6; intros x Hx;
              apply HWout; [destruct Hphiwin as [Hd|Hd]; lia | destruct Hphisp as [Hd|Hd]; lia]|].
      split; [rewrite HRl6; lia|].
      split; [rewrite f17_memcmp_firstn; exact HLm|].
      split; [exact (addressable_kept mem mem' L 6 HLad MK)|].
      split.
      { pose proof (addressable_sub mem phi 50 0 6 Haddr ltac:(lia) ltac:(lia) ltac:(lia)) as Had6.
        rewrite Z.add_0_r in Had6. exact (addressable_kept mem mem' phi 6 Had6 MK). }
      split; [exact HL6|]. split; [exact HL7|].
      split; [apply Hpap; lia|]. split; [apply Hpap; lia|].
      split; [rewrite ASP; exact HLsp|].
      split; [rewrite ASP; destruct Hphisp as [Hd|Hd]; [left; lia | right; lia]|].
      split; [rewrite ASP; exact Hphisp|].
      split; [rewrite ASP; exact Hkpsp|].
      split; [unfold q64 in HL2q |- *; eapply fl_bytes; [exact HL2q | exact MU | rewrite length_le8; intros x Hx; apply HWout; lia]|].
      split; [exact HL2r|].
      split; [eapply fl_bytes; [exact HL2b6 | exact MU |]; rewrite HL2l6; intros x Hx;
              apply HWout; [destruct HL2win as [Hd|Hd]; lia | destruct HL2sp as [Hd|Hd]; lia]|].
      split; [rewrite HL2l6; lia|].
      split; [eapply fl_bytes; [exact HR2b6 | exact MU |]; rewrite HR2l6; intros x Hx;
              apply HWout; [destruct Hphiwin as [Hd|Hd]; lia | destruct Hphisp as [Hd|Hd]; lia]|].
      split; [rewrite HR2l6; lia|].
      split; [rewrite f17_memcmp_firstn; exact HL2m|].
      split; [exact (addressable_kept mem mem' L2 6 HL2ad MK)|].
      split; [exact (addressable_kept mem mem' (phi + 6) 6
                       (addressable_sub mem phi 50 6 6 Haddr ltac:(lia) ltac:(lia) ltac:(lia)) MK)|].
      split; [exact HL26|]. split; [exact HL27|].
      split; [apply Hpap; lia|]. split; [apply Hpap; lia|].
      split; [rewrite ASP; exact HL2sp|].
      rewrite ASP. destruct Hphisp as [Hd|Hd]; [left; lia | right; lia]. }
    (* FTURN (the two cursor spills and Phi's bytes inside the live block) *)
    split.
    { destruct HTURN as (T224 & T232 & Tb & Tl).
      split; [apply Ksp; [lia | exact T224]|].
      split; [apply Ksp; [lia | exact T232]|].
      split; [|exact Tl].
      eapply fl_bytes; [exact Tb | exact MU |].
      rewrite t_phi_length. intros x Hx. apply Hblk.
      rewrite Z2Nat.id in Hx by (unfold flen in Hlen0; exact Hlen0).
      unfold flen. exact Hx. }
    exact HIFS'.
Qed.

End F17b.
