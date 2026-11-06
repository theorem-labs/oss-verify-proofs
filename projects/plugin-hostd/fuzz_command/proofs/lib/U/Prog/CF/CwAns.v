(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_canonical on the ASan build of
   plugin-hostd/fuzz_command, in the shape of cgif_file_fuzzer's walks (lib/A/AC8b.v: a loop walked by the
   symbolic executor over the position-abstract listing, its inline shadow checks removed by tok_load/tok_branch)
   and of this unit's xstrdup walk (the malloc call through amalloc04_sub of PaCall.v).
   The walk is cut at six points: the malloc return (0x89338: the null check, decided by the executor, and the
   empty-line check), the outer head (0x89354), the word-scan head (0x89364), the word start (0x893a0), the copy
   head (0x893e8) and the tail (0x89474); the model of the output is lib/Prog/RecFacts.v's
   canon T = join_sp (words T), and the word lemmas below are the Words section of fuzz_command's own released
   plain proof lib/Prog/rec_canonical.v, copied so that the walk stands on RecFacts alone. The walk's hypotheses are
   the statement's AMALLOC4 and TL (CmdPaLib.v: the malloc trampoline is the rule's entry, the GOT shadow cell). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_canonical.v, with its module paths and module names changed; 696 of its 835 lines of code are new or changed and 2224 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v, with its module paths, module names, addresses and numbers changed; 1174 of its 1277 lines of code are new or changed and 732 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/send_message.v, with its module paths and module names changed; 297 of its 406 lines of code are new or changed and 1168 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes FP ZBridge Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import CType StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import CommandModel CommandFP CommandTac printf_facts_c atoi_c snprintf_c strcmp_c strspn_c strcspn_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import check_words_chain syntax_reply_matches check_words_add_c check_words_chain_c check_words_pin_set_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import CwItems CwBody.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require MemNorm KindBGlue.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecFacts.
Import ListNotations.
Open Scope Z_scope.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK14 YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01 YL00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require YI06.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecKindB joined_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.

(* Memory, image and record facts for the check_words proof (ubsan build). *)

Lemma cw_mbyte_mrd : forall segs m a, mbyte segs m a = mrd segs m (wa a).
Proof. reflexivity. Qed.

Lemma cw_hi_present : forall m a, 2 ^ 20 <= a < 2 ^ 64 -> mbyte rsegs m a <> None -> present m a.
Proof.
  intros m a Ha H. unfold mbyte, mrd, wa, present in *. destruct (m (Z_to_bv 64 a)) as [b|] eqn:E; [exists b; reflexivity|].
  exfalso. apply H. apply MemNorm.seg_rom_unmapped. rewrite unsigned_lit by lia.
  apply (find_segment_none_above rsegs (2 ^ 20) a 1 rsegs_top); lia.
Qed.

Lemma cw_ro_low : forall x, ro_addr rsegs x = true -> bv_unsigned x < 2 ^ 20.
Proof.
  intros x Hx. destruct (Z_lt_ge_dec (bv_unsigned x) (2 ^ 20)) as [H|H]; [exact H|].
  pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. cbn in R.
  rewrite <- (Z_to_bv_bv_unsigned x) in Hx. rewrite ro_addr_hi in Hx by lia. discriminate.
Qed.

Lemma cw_ro_munch : forall W m m', MemNorm.ro_agree rsegs m -> munch W m m' ->
  (forall x, 0 <= x < 2 ^ 20 -> outside W x) -> MemNorm.ro_agree rsegs m'.
Proof.
  intros W m m' H HM HW x Hx. unfold mrd. rewrite (HM x); [exact (H x Hx)|].
  pose proof (cw_ro_low x Hx). pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. cbn in R.
  apply HW. lia.
Qed.

Lemma cw_bytes_of_le : forall (B : malloc_syms) m a bs, ms_segs B = rsegs -> 0 <= a ->
  a + Z.of_nat (length bs) <= 2 ^ 64 -> VerbsB.le_at B m a bs -> bytes_at rsegs m a bs.
Proof.
  intros B0 m a bs HS H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  unfold VerbsB.le_at, blk_data in H. cbv zeta in H. rewrite HS in H.
  pose proof (H (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id in E. exact E.
Qed.

Lemma cw_le_of_bytes : forall (B : malloc_syms) m a bs, ms_segs B = rsegs -> bytes_at rsegs m a bs ->
  VerbsB.le_at B m a bs.
Proof.
  intros B0 m a bs HS (H0 & H1 & H2). unfold VerbsB.le_at, blk_data. cbv zeta. rewrite HS. intros i Hi.
  replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia.
  rewrite cw_mbyte_mrd. apply H2. lia.
Qed.

Lemma cw_le_keep : forall (B : malloc_syms) m m' a bs, VerbsB.le_at B m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte (ms_segs B) m' (a + i) = mbyte (ms_segs B) m (a + i)) ->
  VerbsB.le_at B m' a bs.
Proof.
  intros B0 m m' a bs H K. unfold VerbsB.le_at, blk_data in *. cbv zeta in *. intros i Hi.
  rewrite K by exact Hi. exact (H i Hi).
Qed.

Lemma cw_wv_keep : forall (B : malloc_syms) (L : layout) (A : astate) m m' W arr wp ws,
  words_view B m W arr wp ws -> words_place L A m arr wp ws ->
  (forall i, 0 <= i < 12 -> mbyte (ms_segs B) m' (W + 16 + i) = mbyte (ms_segs B) m (W + 16 + i)) ->
  (forall q k i, In (q, k) (blocks L A) -> 0 <= i < k -> mbyte (ms_segs B) m' (q + i) = mbyte (ms_segs B) m (q + i)) ->
  words_view B m' W arr wp ws.
Proof.
  intros B0 L A m m' W arr wp ws (WL & WN & W24 & W16 & WK) (PA & PK) K1 K2.
  split; [exact WL|]. split; [exact WN|].
  split.
  { apply (cw_le_keep B0 m); [exact W24|]. intros i Hi. rewrite Mem.length_le4 in Hi.
    replace (W + 24 + i) with (W + 16 + (8 + i)) by ring. apply K1. lia. }
  split.
  { apply (cw_le_keep B0 m); [exact W16|]. intros i Hi. rewrite Mem.length_le8 in Hi. apply K1. lia. }
  intros k Hk. destruct (WK k Hk) as [Hp [Hn Hs]]. split; [|split; [exact Hn|]].
  - apply (cw_le_keep B0 m); [exact Hp|]. intros i Hi. rewrite Mem.length_le8 in Hi.
    destruct PA as (q & n & Hq & H1 & H2).
    replace (arr + 8 * Z.of_nat k + i) with (q + (arr + 8 * Z.of_nat k + i - q)) by ring.
    apply (K2 q n); [exact Hq | lia].
  - apply (cw_le_keep B0 m); [exact Hs|]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    destruct (PK k Hk) as (q & n & Hq & H1 & H2).
    replace (nth k wp 0 + i) with (q + (nth k wp 0 + i - q)) by ring.
    apply (K2 q n); [exact Hq | lia].
Qed.

Lemma cw_join_no0 : forall ws, (forall w, In w ws -> ~ In NUL w) -> ~ In NUL (RecFacts.join_sp ws).
Proof.
  induction ws as [|w ws IH]; intros H.
  - cbn. intros [].
  - destruct ws as [|w2 ws'].
    + cbn [RecFacts.join_sp]. apply H. left. reflexivity.
    + change (RecFacts.join_sp (w :: w2 :: ws')) with (w ++ RecFacts.SPACE :: RecFacts.join_sp (w2 :: ws')).
      intros Hin. apply in_app_or in Hin as [Hin|[Hin|Hin]].
      * exact (H w (or_introl eq_refl) Hin).
      * unfold RecFacts.SPACE, NUL in Hin. apply (f_equal bv_unsigned) in Hin. vm_compute in Hin. discriminate.
      * exact (IH (fun w' Hw' => H w' (or_intror Hw')) Hin).
Qed.

Lemma cw_join_len : forall ws, Z.of_nat (length (RecFacts.join_sp ws)) <= join_need ws.
Proof.
  induction ws as [|w ws IH]; [cbn; lia|].
  destruct ws as [|w2 ws'].
  - cbn [RecFacts.join_sp]. unfold join_need. cbn [fold_right]. lia.
  - change (RecFacts.join_sp (w :: w2 :: ws')) with (w ++ RecFacts.SPACE :: RecFacts.join_sp (w2 :: ws')).
    rewrite length_app. cbn [length].
    change (join_need (w :: w2 :: ws')) with (Z.of_nat (length w) + 1 + join_need (w2 :: ws')). lia.
Qed.

Lemma cw_cells_bytes_app : forall l1 l2, cells_bytes (l1 ++ l2) = cells_bytes l1 ++ cells_bytes l2.
Proof.
  induction l1 as [|c l1 IH]; intros l2; cbn [app cells_bytes]; [reflexivity|].
  rewrite IH, app_assoc. reflexivity.
Qed.

Lemma cw_cells_wf_app : forall l1 l2, cells_wf (l1 ++ l2) -> cells_wf l1 /\ cells_wf l2.
Proof.
  induction l1 as [|c l1 IH]; intros l2 H; [split; [exact I | exact H]|].
  destruct H as [H1 H2]. destruct (IH l2 H2) as [H3 H4]. split; [split; [exact H1 | exact H3] | exact H4].
Qed.

Lemma cw_rw_sub : forall m X Y pre mid post, rw_cells rsegs m X (pre ++ mid ++ post) ->
  Y = X + Z.of_nat (cells_size pre) -> rw_cells rsegs m Y mid.
Proof.
  intros m X Y pre mid post [[Hwf Hb] (Hw0 & Hw1 & Hw)] ->.
  destruct (cw_cells_wf_app _ _ Hwf) as [Wp Wmp]. destruct (cw_cells_wf_app _ _ Wmp) as [Wm _].
  rewrite !cw_cells_bytes_app in Hb.
  apply bytes_at_app in Hb as [_ Hb]. apply bytes_at_app in Hb as [Hb _].
  rewrite (cells_bytes_length pre Wp) in Hb.
  rewrite !cells_size_app in Hw1, Hw.
  split; [split; [exact Wm | exact Hb]|].
  split; [lia|]. split; [lia|]. intros i Hi.
  replace (X + Z.of_nat (cells_size pre) + i) with (X + (Z.of_nat (cells_size pre) + i)) by ring.
  apply Hw. lia.
Qed.

Lemma cw_rw_move : forall m m' X cs, rw_cells rsegs m X cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> mbyte rsegs m' (X + i) = mbyte rsegs m (X + i) /\
     writable_at rsegs m' (X + i)) -> rw_cells rsegs m' X cs.
Proof.
  intros m m' X cs H K. apply (rw_cells_transfer rsegs m m' X cs H).
  intros i Hi. destruct (K i Hi) as [E Wr]. split; [exact E | intros _; exact Wr].
Qed.

Lemma cw_rw_bytes : forall m X cs, cells_wf cs -> bytes_at rsegs m X (cells_bytes cs) ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> writable_at rsegs m (X + i)) -> rw_cells rsegs m X cs.
Proof.
  intros m X cs Hwf Hb Hw. pose proof Hb as (H0 & H1 & _). rewrite (cells_bytes_length cs Hwf) in H1.
  split; [split; [exact Hwf | exact Hb]|]. split; [exact H0|]. split; [exact H1|].
  intros i Hi. exact (Hw i Hi).
Qed.

Lemma cw_mbyte_norm : forall m a, MemNorm.ro_agree rsegs m -> 0 <= a < TASK_SIZE ->
  mbyte rsegs (MemNorm.normalize_cj rsegs m) a = mbyte rsegs m a.
Proof.
  intros m a RO Ha. unfold TASK_SIZE in Ha. rewrite !cw_mbyte_mrd.
  apply (MemNorm.mrd_normalize_cj rsegs m (wa a) RO).
  right. right. unfold wa. rewrite unsigned_lit by lia. unfold TASK_SIZE. lia.
Qed.

Lemma cw_wr_norm : forall m a, MemNorm.ro_agree rsegs m -> 2 ^ 20 <= a < TASK_SIZE -> writable_at rsegs m a ->
  writable_at rsegs (MemNorm.normalize_cj rsegs m) a.
Proof.
  intros m a RO Ha H. unfold TASK_SIZE in Ha. unfold writable_at in *.
  rewrite (MemNorm.wview_rel_cj rsegs m (MemNorm.normalize_cj rsegs m) (Z_to_bv 64 a)
    (MemNorm.mem_rel_cj_normalize rsegs m RO)); [exact H|].
  apply MemNorm.cj_drop_false_intro; [apply ro_addr_hi; lia|].
  right. rewrite unsigned_lit by lia. unfold TASK_SIZE. lia.
Qed.

Lemma cw_mid_eq : forall {X : Type} (l1 l2 l3 l4 : list X) x, l1 ++ x :: l2 = l3 ++ x :: l4 ->
  ~ In x l1 -> ~ In x l3 -> l1 ++ l2 = l3 ++ l4.
Proof.
  intros X l1. induction l1 as [|y l1 IH]; intros l2 l3 l4 x E N1 N3.
  - destruct l3 as [|z l3]; cbn in E |- *.
    + injection E as E. exact E.
    + injection E as E1 E2. exfalso. apply N3. left. symmetry. exact E1.
  - destruct l3 as [|z l3]; cbn in E |- *.
    + injection E as E1 E2. exfalso. apply N1. left. exact E1.
    + injection E as E1 E2. subst z. f_equal.
      apply (IH l2 l3 l4 x E2); [intro H; apply N1; right; exact H | intro H; apply N3; right; exact H].
Qed.

Lemma cw_lle_trans : forall A A' L1 L2 L3, layout_le A L1 L2 -> layout_le A' L2 L3 ->
  (length (st_regions A) <= length (st_regions A'))%nat -> layout_le A L1 L3.
Proof.
  intros A A' L1 L2 L3 (H1 & H2 & H3 & H4) (G1 & G2 & G3 & G4) HL.
  split; [congruence|]. split; [congruence|]. split; [congruence|].
  intros r Hr. rewrite (G4 r ltac:(lia)). exact (H4 r Hr).
Qed.

Lemma cw_bytes_of_image : forall segs m n A bs, image_bytes segs A n = Some bs ->
  (forall i, 0 <= i < Z.of_nat n -> mbyte segs m (A + i) = seg_rom segs (Z_to_bv 64 (A + i))) ->
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 -> bytes_at segs m A bs.
Proof.
  intros segs m n. induction n as [|n IH]; intros A bs HI HM H0 H1; cbn [image_bytes] in HI.
  - injection HI as <-. split; [exact H0|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (PropExec.seg_rom segs (wa A)) as [b0|] eqn:E0; [|discriminate].
    destruct (image_bytes segs (A + 1) n) as [bs'|] eqn:E1; [|discriminate].
    injection HI as <-.
    change (b0 :: bs') with ([b0] ++ bs'). apply bytes_at_app. split.
    + split; [exact H0|]. split; [cbn; lia|]. intros i Hi. cbn [length] in Hi.
      destruct i as [|i]; [|lia]. cbn [nth_error].
      replace (A + Z.of_nat 0) with A by lia. rewrite <- cw_mbyte_mrd.
      pose proof (HM 0 ltac:(lia)) as H. rewrite Z.add_0_r in H. rewrite H. exact E0.
    + replace (A + Z.of_nat (length [b0])) with (A + 1) by (cbn; lia).
      apply IH; [exact E1 | | lia | lia]. intros i Hi.
      replace (A + 1 + i) with (A + (1 + i)) by lia. apply HM. lia.
Qed.

Lemma cw_image_nth : forall segs n A bs i, image_bytes segs A n = Some bs -> (i < n)%nat ->
  PropExec.seg_rom segs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  intros segs n. induction n as [|n IH]; intros A bs i HI Hi; [lia|].
  cbn [image_bytes] in HI.
  destruct (PropExec.seg_rom segs (wa A)) as [b0|] eqn:E0; [|discriminate].
  destruct (image_bytes segs (A + 1) n) as [bs'|] eqn:E1; [|discriminate].
  injection HI as <-.
  destruct i as [|i]; cbn [nth_error].
  - rewrite Z.add_0_r. exact E0.
  - replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply IH; [exact E1 | lia].
Qed.

Lemma cw_img_res : forall (B : malloc_syms) k lo sz a, ms_segs B = rsegs ->
  nth_error (map (fun s => (bv_unsigned (fst s), bv_unsigned (snd s))) (segments_reserved rsegs)) k = Some (lo, sz) ->
  lo <= a < lo + sz -> in_img B a.
Proof.
  intros B0 k lo sz a HS E Ha. unfold in_img. rewrite HS. split.
  - assert (L : length rsegs = 4%nat) by (vm_compute; reflexivity).
    intros H. rewrite H in L. discriminate.
  - rewrite nth_error_map in E. destruct (nth_error (segments_reserved rsegs) k) as [s|] eqn:E2; [|discriminate].
    cbv beta iota delta [option_map] in E. injection E as E3 E4.
    exists s. split; [exact (nth_error_In _ _ E2) | lia].
Qed.

Lemma cw_img_iv : forall (B : malloc_syms) a, ms_segs B = rsegs -> 0x10000 <= a < 0x55000 -> in_img B a.
Proof.
  intros B0 a HS Ha.
  destruct (Z_lt_ge_dec a 0x13000).
  { apply (cw_img_res B0 0 0x10000 0x3000); [exact HS | vm_compute; reflexivity | lia]. }
  destruct (Z_lt_ge_dec a 0x22000).
  { apply (cw_img_res B0 1 0x13000 0xF000); [exact HS | vm_compute; reflexivity | lia]. }
  destruct (Z_lt_ge_dec a 0x23000).
  { apply (cw_img_res B0 2 0x22000 0x1000); [exact HS | vm_compute; reflexivity | lia]. }
  apply (cw_img_res B0 3 0x23000 0x32000); [exact HS | vm_compute; reflexivity | lia].
Qed.

Lemma cw_relro_iv : forall a, in_globals frame_RELRO a -> 0x226b0 <= a < 0x23000.
Proof. intros a (lo & len & Hin & Hb). unfold frame_RELRO in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; lia. Qed.

Lemma cw_relro_of : forall a, 0x226b0 <= a < 0x22d40 -> in_globals frame_RELRO a.
Proof. intros a Ha. exists 140976, 1680. split; [left; reflexivity | lia]. Qed.

Lemma cw_g_iv : forall a, in_globals frame_G a -> 0x33ff0 <= a < 0x343ec.
Proof. intros a (lo & len & Hin & Hb). unfold frame_G in Hin. destruct Hin as [E|[]]. injection E as <- <-. lia. Qed.

Lemma cw_g_of : forall a, 0x33ff0 <= a < 0x343ec -> in_globals frame_G a.
Proof. intros a Ha. exists 212976, 1020. split; [left; reflexivity | lia]. Qed.

Lemma cw_got_rom_img : image_bytes rsegs 0x22d40 8 = Some (Mem.le8 (Z_to_bv 64 0x54730)).
Proof. vm_compute. repeat first [ reflexivity | apply bv_eq; reflexivity | f_equal ]. Qed.

Lemma cw_grec_img : image_bytes rsegs 0x22cf8 8 = Some (Mem.le8 (Z_to_bv 64 CW_GREC)).
Proof. unfold CW_GREC. vm_compute. repeat first [ reflexivity | apply bv_eq; reflexivity | f_equal ]. Qed.

Lemma cw_got_rom : forall m a, word_mem rsegs m 0x22d40 0x54730 -> 0x22d40 <= a < 0x22d48 ->
  mbyte rsegs m a = seg_rom rsegs (Z_to_bv 64 a).
Proof.
  intros m a W Ha.
  pose proof (KindBGlue.word_mem_le8 rsegs m 0x22d40 0x54730 W ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & H).
  rewrite Mem.length_le8 in H.
  assert (Ei : a = 0x22d40 + Z.of_nat (Z.to_nat (a - 0x22d40))) by lia.
  rewrite Ei, cw_mbyte_mrd. rewrite (H (Z.to_nat (a - 0x22d40)) ltac:(lia)).
  symmetry. exact (cw_image_nth rsegs 8 _ _ (Z.to_nat (a - 0x22d40)) cw_got_rom_img ltac:(lia)).
Qed.

Lemma cw_guard_wr : forall m i, 0 <= i < 8 -> writable_at rsegs m (0x54730 + i).
Proof.
  intros m i Hi.
  assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  repeat (destruct C as [C|C];
    [subst i; unfold writable_at, wview; destruct (m _); [discriminate | vm_compute; discriminate]|]).
  subst i; unfold writable_at, wview; destruct (m _); [discriminate | vm_compute; discriminate].
Qed.

Lemma cw_call_a : forall bl m mJ lo a c P,
  call_at rsegs bl m a c P ->
  (forall pn, In pn bl -> 4096 <= fst pn /\ fst pn + snd pn <= lo) ->
  0 <= a -> a + 56 <= lo -> lo <= 2 ^ 64 ->
  (forall x, a <= x < a + 56 -> mbyte rsegs mJ x = mbyte rsegs m x) ->
  (forall pn x, In pn bl -> fst pn <= x < fst pn + snd pn -> mbyte rsegs mJ x = mbyte rsegs m x) ->
  call_at_a mJ lo a c.
Proof.
  intros bl m mJ lo a c P (C0 & C1 & C2 & C3 & C4 & _ & C6) HB A0 A1 ALo KA KB.
  unfold CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *. rewrite Z.add_0_r in C3.
  split; [exact A0|]. split; [exact A1|].
  split; [apply (bytes_at_transfer rsegs m); [exact C3 | intros i Hi; rewrite Mem.length_le4 in Hi; apply KA; lia]|].
  split; [apply (bytes_at_transfer rsegs m); [exact C4 | intros i Hi; rewrite Mem.length_le4 in Hi; apply KA; lia]|].
  split; [unfold RecFacts.REC_FN_COUNT in C0; lia|]. split; [exact C1|].
  intros k s Hs.
  assert (Hk : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Hs; discriminate).
  destruct (nth_error P k) as [pn|] eqn:Hp; [|apply nth_error_None in Hp; lia].
  destruct (C6 k s pn Hs Hp) as (D0 & D1 & D2 & D3 & D4 & D5).
  destruct (HB pn D2) as [B0 B1].
  exists (Z_to_bv 64 (fst pn)).
  assert (U : bv_unsigned (Z_to_bv 64 (fst pn)) = fst pn) by (apply unsigned_lit; lia).
  unfold lowp. rewrite U.
  split; [apply (bytes_at_transfer rsegs m); [exact D0 | intros i Hi; rewrite Mem.length_le8 in Hi; apply KA; lia]|].
  split; [lia|]. split; [lia|]. split; [lia|].
  split.
  { apply (bytes_at_transfer rsegs m); [exact D4|]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    apply (KB pn); [exact D2 | lia]. }
  split; [exact D5 | lia].
Qed.

Lemma cw_word_low : forall (B : malloc_syms) m lo (W arr : Z) wp ws k, ms_segs B = rsegs ->
  words_view B m W arr wp ws -> 0 <= arr -> arr + 8 * Z.of_nat (length ws) <= lo -> lo <= 2 ^ 64 ->
  (forall j, (j < length ws)%nat -> 1 <= nth j wp 0 /\ nth j wp 0 + Z.of_nat (length (nth j ws [])) + 1 <= lo) ->
  0 <= k < Z.of_nat (length ws) ->
  lowp lo m (bv_unsigned (Z_to_bv 64 arr) + 8 * k) (nth (Z.to_nat k) (map (Z_to_bv 64) wp) (Z_to_bv 64 0))
    (nth (Z.to_nat k) ws []).
Proof.
  intros B0 m lo W arr wp ws k HS (WL & WN & _ & _ & WK) A0 A1 HL HP Hk.
  assert (Hk' : (Z.to_nat k < length ws)%nat) by lia.
  destruct (WK (Z.to_nat k) Hk') as (E1 & E2 & E3).
  destruct (HP (Z.to_nat k) Hk') as [P0 P1].
  rewrite (map_nth (Z_to_bv 64) wp 0 (Z.to_nat k)).
  assert (UA : bv_unsigned (Z_to_bv 64 arr) = arr) by (apply unsigned_lit; lia).
  assert (UP : bv_unsigned (Z_to_bv 64 (nth (Z.to_nat k) wp 0)) = nth (Z.to_nat k) wp 0) by (apply unsigned_lit; lia).
  rewrite Z2Nat.id in E1 by lia.
  unfold lowp. rewrite UA, UP.
  split; [apply (cw_bytes_of_le B0 m _ _ HS); [lia | rewrite Mem.length_le8; lia | exact E1]|].
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [apply (cw_bytes_of_le B0 m _ _ HS); [lia | rewrite length_app; cbn [length]; lia | exact E3]|].
  split; [exact E2 | lia].
Qed.
Lemma stk_normalize_cj : forall mem lo hi, 2 ^ 20 <= lo -> hi <= TASK_SIZE ->
  (forall a, lo <= a < hi -> YP09.writable_at rsegs mem a) -> stk rsegs (MemNorm.normalize_cj rsegs mem) lo hi.
Proof.
  intros mem lo hi Hlo Hhi HW. unfold TASK_SIZE in Hhi. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (writable_hi_present mem a ltac:(lia) (HW a Ha)) as [bb E].
  assert (NE : MemNorm.normalize_cj rsegs mem (wa a) = mem (wa a)).
  { unfold MemNorm.normalize_cj. rewrite (MemNorm.cj_drop_false_intro rsegs (wa a)); [reflexivity | |].
    - unfold wa. apply ro_addr_hi. lia.
    - right. unfold wa. rewrite unsigned_lit by lia. unfold TASK_SIZE. lia. }
  unfold wview, mrd. rewrite NE. unfold wa. rewrite E. split; [discriminate | exists bb; reflexivity].
Qed.

Lemma ms_rel_cj_MS : forall s R F pc fc rv m0 ro, MemNorm.ms_rel_cj rsegs s (MS R F pc fc rv m0 ro) ->
  s = MS R F pc fc rv (ms_mem s) ro /\ MemNorm.mem_rel_cj rsegs (ms_mem s) m0.
Proof.
  intros [r f p sv rv' c mm o] R F pc fc rv m0 ro (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  cbn in *. subst. split; [reflexivity | exact H8].
Qed.

Lemma eqv_mkst_fx : forall R F pc fc m ro ms, Regs6ss.ms_eqv (MS R F pc fc None m ro) ms ->
  exists R', ms = @mkst (mkFP F fc) R' pc m ro /\ Regs6ss.xregs_eqv R R'.
Proof.
  intros R F pc fc m ro [r f p sv rv c mm o] (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  cbn in *. subst. exists r. split; [reflexivity | exact H1].
Qed.

Lemma guard_wview : forall (m : word -> option byte) i, 0 <= i < 8 ->
  wview rsegs m (Mem.wa (snprintf_c.GOT_GUARD + i)) <> None /\ wview rsegs m (Mem.wa (snprintf_c.GUARD + i)) <> None.
Proof.
  intros m i Hi. unfold snprintf_c.GOT_GUARD, snprintf_c.GUARD.
  assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  repeat (destruct C as [C|C]; [subst i; unfold wview;
    split; (match goal with |- context [m ?x] => destruct (m x) end; [discriminate | vm_compute; discriminate])|]).
  subst i. unfold wview.
  split; (match goal with |- context [m ?x] => destruct (m x) end; [discriminate | vm_compute; discriminate]).
Qed.

Lemma call_at_blocks : forall segs bl mem a c P pn, call_at segs bl mem a c P -> In pn P -> In pn bl.
Proof.
  intros segs bl mem a c P pn (_ & _ & HL & _ & _ & _ & HK) Hin.
  apply In_nth_error in Hin as (k & Ek).
  assert (Hk : (k < length (snd c))%nat) by (rewrite <- HL; apply nth_error_Some; rewrite Ek; discriminate).
  destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
  exact (proj1 (proj2 (proj2 (HK k s pn Es Ek)))).
Qed.

Lemma rec_rep_O_blocks : forall segs gr sc L A mem R O pn,
  rec_rep segs gr sc L A mem R O -> In pn O -> In pn (blocks L A).
Proof.
  intros segs gr sc L A mem R O pn (Q & HR & HO) Hin. apply HO in Hin.
  destruct HR as (HS & HC & HA & HP & HX & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin|Hin].
  - apply in_concat in Hin as (P & HP' & Hpn). apply In_nth_error in HP' as (i & EP).
    destruct (nth_error (r_calls R) i) as [c|] eqn:Ec.
    + exact (call_at_blocks _ _ _ _ _ _ _ (proj1 (C4 i c P Ec EP)) Hpn).
    + exfalso. apply nth_error_None in Ec.
      assert (i < length (l_calls Q))%nat by (apply nth_error_Some; rewrite EP; discriminate). lia.
  - apply in_app_or in Hin as [Hin|Hin]; [exact (call_at_blocks _ _ _ _ _ _ _ C5 Hin)|].
    apply in_app_or in Hin as [Hin|Hin].
    + unfold answer_at in HA. destruct (l_answer Q) as [pn'|]; cbn in Hin; [|contradiction].
      destruct Hin as [<-|[]]. destruct (r_answer R); [exact (proj1 (proj2 (proj2 HA)))|contradiction].
    + unfold reply_at in HP. destruct (l_reply Q) as [pn'|]; cbn in Hin; [|contradiction].
      destruct Hin as [<-|[]]. destruct (r_reply R); [exact (proj1 (proj2 (proj2 (proj2 (proj2 HP)))))|contradiction].
Qed.

Lemma in_mid_inv : forall {X : Type} (b1 b2 : list X) x y, In y (b1 ++ b2) -> In y (b1 ++ x :: b2).
Proof.
  intros X b1 b2 x y H. apply in_app_or in H. apply in_or_app.
  destruct H as [H|H]; [left; exact H | right; right; exact H].
Qed.

Lemma with_vmmaps_twice' : forall v1 v2 md, with_vmmaps v2 (with_vmmaps v1 md) = with_vmmaps v2 md.
Proof. intros v1 v2 md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Section Own.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis AXM : AllocExtra B MR.
Hypothesis CTXM : forall L A mem md a, MR L A mem md -> ms_ctx B <= a < ms_ctx B + CTX_SIZE -> owned B L A a.

Lemma not_owned_mid : forall L A mem md L2 A2 mem2 md2 a, MR L A mem md -> MR L2 A2 mem2 md2 ->
  (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ owned B L2 A2 a.
Proof using LAWS AXM CTXM.
  intros L A mem md L2 A2 mem2 md2 a H1 H2 Hd N1 [Ha|Hs]; [|apply N1; right; exact Hs].
  destruct Hd as [Hd|Hd].
  - pose proof (mr_owned_low B MR LAWS L2 A2 mem2 md2 a H2 (or_introl Ha)). lia.
  - apply N1. apply (CTXM L A mem md a H1). exact (ax_img AXM L2 A2 mem2 md2 a H2 Hd Ha).
Qed.

End Own.

Lemma rw_cells_rel_cj : forall segs m m0 a cs, MemNorm.mem_rel_cj segs m m0 -> rw_cells segs m0 a cs -> rw_cells segs m a cs.
Proof.
  intros segs m m0 a cs HR [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - exact (MemNorm.bytes_at_rel_cj segs m m0 a _ HR Hb).
  - exact (MemNorm.wr_at_rel_cj segs m m0 a _ HR Hw).
Qed.
