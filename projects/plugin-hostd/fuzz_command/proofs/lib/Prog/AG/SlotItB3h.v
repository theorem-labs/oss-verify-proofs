(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, addresses and numbers changed; 2641 of its 2742 lines of code are new or changed and 1015 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_host_setting.v, with its module paths changed; 599 of its 833 lines of code are new or changed and 2508 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/RecStubU.v, with its module paths and module names changed; 444 of its 497 lines of code are new or changed and 780 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/SlotItCK.v; 330 of its 390 lines of code are new or changed and 437 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/SlotItB3qh.v, with its module paths and numbers changed; 526 of its 771 lines of code are new or changed and 145 lines of the source are left out. *)
(* lib/Prog/SlotItB3h.v with the agreement room cap CAP_AG (lib/SlotAgree.v) for CAPMAX. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes MState.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL0g YL01 YL00 YI14 YI16 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require KindBGlue BlocksNodup.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import AllocSI AllocGS.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import KindB RecFacts RecModel RecInv RecInvP SlotSpec SlotGlue SlotRuns HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.AG Require Import SlotCallees SlotIter SlotEnd SlotItBase SlotItSt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_c send_message_c CommandB VerbsB CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.AG Require Import SlotItA SlotItE SlotItB SlotItBW.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import joined_c rec_shape_of_c check_reply_answer_c check_reply_c check_arity_c memcpy_c strspn_c strcspn_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.AG Require Slot SlotInv SlotRec.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecTail RecAnsB RecAns SlotWords.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.AG Require SlotItB2 SlotItCK.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require chain_words VerbsMem RecGlue hand_back send_message HarnessPropsProof.
Import ListNotations.
Local Open Scope Z_scope.

(* The splitter, check_reply and check_arity from the third malloc's return (stB, pc 0x141c8) to check_words' entry
   (stBW, pc 0x14980): SlotItB2.w_evt (with SlotItCK.ck_evt_holds) on the memory normalized to the task's addresses,
   lifted into SR by SlotItBase.sr_cj. *)

(* The normalized memory keeps every byte below TASK_SIZE outside the read-only range. *)
Lemma b3_cj_eq : forall (m : word -> option byte) a, 0 <= a < TASK_SIZE -> ~ (0x10000 <= a < 0x22000) ->
  normalize_cj rsegs m (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros m a Ha Hr. unfold normalize_cj.
  rewrite (MemNorm.cj_drop_false_intro rsegs (Z_to_bv 64 a)); [reflexivity | apply hand_back.hb_ro_false |].
  - unfold TASK_SIZE in *. lia.
  - lia.
  - right. rewrite unsigned_lit by (unfold TASK_SIZE in *; lia). exact (proj2 Ha).
Qed.

Lemma b3_cj_mbyte : forall (m : word -> option byte) a, 0 <= a < TASK_SIZE -> ~ (0x10000 <= a < 0x22000) ->
  mbyte rsegs (normalize_cj rsegs m) a = mbyte rsegs m a /\
  (writable_at rsegs m a <-> writable_at rsegs (normalize_cj rsegs m) a).
Proof.
  intros m a Ha Hr. pose proof (b3_cj_eq m a Ha Hr) as E.
  unfold mbyte, writable_at, wview. rewrite E. split; [reflexivity | tauto].
Qed.

Lemma b3_cj_cells : forall m a cs, rw_cells rsegs m a cs -> 0 <= a -> a + Z.of_nat (cells_size cs) <= TASK_SIZE ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ~ (0x10000 <= a + i < 0x22000)) ->
  rw_cells rsegs (normalize_cj rsegs m) a cs.
Proof.
  intros m a cs H H0 H1 H2. apply (KindB.rw_cells_transfer rsegs m); [exact H|].
  intros i Hi. destruct (b3_cj_mbyte m (a + i) ltac:(lia) (H2 i Hi)) as [E W]. split; [exact E | tauto].
Qed.

Lemma b3_cj_u8 : forall m a bs, u8arr rsegs m a bs -> a + Z.of_nat (length bs) <= TASK_SIZE ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> ~ (0x10000 <= a + i < 0x22000)) ->
  u8arr rsegs (normalize_cj rsegs m) a bs.
Proof.
  intros m a bs [Hb (W0 & W1 & W2)] H1 H2. split.
  - apply (KindB.bytes_at_transfer rsegs m); [exact Hb|]. intros i Hi.
    exact (proj1 (b3_cj_mbyte m (a + i) ltac:(lia) (H2 i Hi))).
  - split; [exact W0|]. split; [exact W1|]. intros i Hi.
    exact (proj1 (proj2 (b3_cj_mbyte m (a + i) ltac:(lia) (H2 i Hi))) (W2 i Hi)).
Qed.

Lemma b3_img : forall q k, 0 < k -> (forall i, 0 <= i < k -> ~ (0x10000 <= q + i < 0x55000)) ->
  q + k <= 0x10000 \/ 0x55000 <= q.
Proof.
  intros q k Hk H. destruct (Z_lt_ge_dec q 0x10000) as [H1|H1].
  - left. destruct (Z_le_gt_dec (q + k) 0x10000) as [H2|H2]; [exact H2|].
    exfalso. apply (H (0x10000 - q)); lia.
  - right. destruct (Z_lt_ge_dec q 0x55000) as [H2|H2]; [|lia].
    exfalso. apply (H 0); lia.
Qed.

Lemma b3_m8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.

Definition b3_al8 (x : Z) : Prop := x mod 8 = 0.
Definition b3_slk (r : Z) (x slack : list byte) : Prop :=
  (- (r + Z.of_nat (length x) + 1)) mod 8 <= Z.of_nat (length slack).

Ltac cz := apply Z.leb_le; vm_compute; reflexivity.

Lemma b3_r8_lt : forall c a, c <= a < 8 * ((c + 7) / 8) -> a < c + 8.
Proof. intros c a H. Z.div_mod_to_equations. lia. Qed.

Lemma b3_r8_low : forall c a, c <= 0x10000 -> a < 8 * ((c + 7) / 8) -> a < 0x10000.
Proof. intros c a H1 H2. pose proof (SlotItB2.b2_r8 c 0x10000 H1 eq_refl). lia. Qed.

Lemma b3_r8_mono : forall c d, c <= d -> 8 * ((c + 7) / 8) <= 8 * ((d + 7) / 8).
Proof. intros c d H. pose proof (Z.div_le_mono (c + 7) (d + 7) 8 ltac:(lia) ltac:(lia)). lia. Qed.

Lemma b3_slack_len : forall e s, s = 8 * ((e + 7) / 8) - e -> (- e) mod 8 <= s.
Proof. intros e s ->. Z.div_mod_to_equations. lia. Qed.

Lemma b3_out4 : forall t1 e1 t2 e2 t3 e3 t4 e4 a, (a < t1 \/ e1 <= a) -> (a < t2 \/ e2 <= a) ->
  (a < t3 \/ e3 <= a) -> (a < t4 \/ e4 <= a) -> Frame.outside [(t1, e1); (t2, e2); (t3, e3); (t4, e4)] a.
Proof. intros. cbn. refine (conj _ (conj _ (conj _ (conj _ Logic.I)))); lia. Qed.

Lemma b3_notout4 : forall t1 e1 t2 e2 t3 e3 t4 e4 a, ~ Frame.outside [(t1, e1); (t2, e2); (t3, e3); (t4, e4)] a ->
  (t1 <= a < e1) \/ (t2 <= a < e2) \/ (t3 <= a < e3) \/ (t4 <= a < e4).
Proof.
  intros t1 e1 t2 e2 t3 e3 t4 e4 a H.
  destruct (Z_lt_ge_dec a t1); [|destruct (Z_lt_ge_dec a e1); [left; lia|]];
  (destruct (Z_lt_ge_dec a t2); [|destruct (Z_lt_ge_dec a e2); [right; left; lia|]]);
  (destruct (Z_lt_ge_dec a t3); [|destruct (Z_lt_ge_dec a e3); [right; right; left; lia|]]);
  (destruct (Z_lt_ge_dec a t4); [|destruct (Z_lt_ge_dec a e4); [right; right; right; lia|]]);
  exfalso; apply H; apply b3_out4; lia.
Qed.

Lemma b3_ne_O : forall (O : list (Z * Z)) p1 k1 t k, In (p1, k1) O -> ~ In t (map fst O) -> (p1, k1) <> (t, k).
Proof.
  intros O p1 k1 t k H N E. injection E as -> _. apply N. apply in_map_iff. exists (t, k1). split; [reflexivity | exact H].
Qed.

Lemma b3_wr_cb : forall m q (k : nat) bs a, rw_cells rsegs m q [CB k bs] -> q <= a < q + Z.of_nat k ->
  writable_at rsegs m a.
Proof.
  intros m q k bs a [_ (W0 & W1 & W2)] Ha. replace a with (q + (a - q)) by ring. apply W2. cbn [cells_size csize]. lia.
Qed.

Lemma b3_cb32 : forall m a t c ar nw jp, rw_cells rsegs m a [C8 t; C8 c; C8 ar; C4 nw; CB 4 jp] ->
  exists jw, rw_cells rsegs m a [CB 32 jw].
Proof.
  intros m a t c ar nw jp H. exists (cells_bytes [C8 t; C8 c; C8 ar; C4 nw; CB 4 jp]).
  apply (SlotItB.ib_cells_eq m a _ _ H); [| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity].
  assert (LB : length (cells_bytes [C8 t; C8 c; C8 ar; C4 nw; CB 4 jp]) = 32%nat).
  { destruct H as [[Hwf _] _]. rewrite (Cells.cells_bytes_length _ Hwf). reflexivity. }
  revert LB. generalize (cells_bytes [C8 t; C8 c; C8 ar; C4 nw; CB 4 jp]). intros bs LB. cbn. tauto.
Qed.

(* The words of the line in copy and their addresses in arr. *)
Lemma b3_wb : forall m copy arr L0w (M : list byte) C Aa wp,
  rw_cells rsegs m copy [CB (Z.to_nat (L0w + 1)) C] -> rw_cells rsegs m arr [CB (Z.to_nat (arr_size L0w)) Aa] ->
  0 <= L0w -> L0w = Z.of_nat (length (Verbs.upto0 M)) ->
  length wp = length (Verbs.words (Verbs.line M)) ->
  firstn (8 * length (Verbs.words (Verbs.line M))) Aa = concat (map (fun p => le8 (Z_to_bv 64 p)) wp) ->
  (forall k p w, nth_error wp k = Some p -> nth_error (Verbs.words (Verbs.line M)) k = Some w ->
     copy <= p /\ p + Z.of_nat (length w) + 1 <= copy + L0w + 1 /\
     firstn (length w + 1) (skipn (Z.to_nat (p - copy)) C) = w ++ [Z_to_bv 8 0]) ->
  (forall k p w, nth_error wp k = Some p -> nth_error (Verbs.words (Verbs.line M)) k = Some w ->
     bytes_at rsegs m p (w ++ [Z_to_bv 8 0])) /\
  (forall k p, nth_error wp k = Some p -> bytes_at rsegs m (arr + 8 * Z.of_nat k) (le8 (Z_to_bv 64 p))).
Proof.
  intros m copy arr L0w M C Aa wp CC AA HL HU WPL WPF WPW.
  assert (CB1 : bytes_at rsegs m copy C).
  { pose proof (SlotItB2.b2_cells_bytes _ _ _ CC) as Hb. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (LCC : length C = Z.to_nat (L0w + 1)) by (destruct CC as [[[H _] _] _]; exact H).
  assert (AB1 : bytes_at rsegs m arr Aa).
  { pose proof (SlotItB2.b2_cells_bytes _ _ _ AA) as Hb. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (LAA : length Aa = Z.to_nat (arr_size L0w)) by (destruct AA as [[[H _] _] _]; exact H).
  split.
  - intros k p w Ep Ew. destruct (WPW k p w Ep Ew) as (P1 & P2 & P3).
    replace p with (copy + Z.of_nat (Z.to_nat (p - copy))) by (clear - P1; lia).
    apply (SlotItB2.b2_sub m copy C _ _ CB1); [rewrite length_app; cbn [length]; clear - P1 P2 LCC HL; lia|].
    rewrite length_app. cbn [length]. exact P3.
  - intros k p Ep. assert (Hk : (k < length wp)%nat) by (apply nth_error_Some; rewrite Ep; discriminate).
    replace (8 * Z.of_nat k) with (Z.of_nat (8 * k)) by lia.
    apply (SlotItB2.b2_sub m arr Aa _ _ AB1).
    + rewrite length_le8, LAA. rewrite WPL in Hk. pose proof (SlotRec.words_count (Verbs.line M)) as HWC.
      pose proof (SlotRec.line_len M) as HLL. unfold arr_size. rewrite HU.
      apply (SlotItB2.b2_arr_bound k (length (Verbs.words (Verbs.line M))) _ Hk). clear - HWC HLL. lia.
    + rewrite length_le8. exact (SlotItB2.b2_firstn_ptr Aa wp k p ltac:(rewrite WPL; exact WPF) Ep).
Qed.

Section B3.
Context {rc : RunCeil}.
Variables (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head)
  (SK : sink_syms) (ra empty : Z) (S : Z) (rg : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
  (L0 : layout) (A0 : astate) (p0 n0 : Z) (pl : list byte) (b : sbound).
Hypothesis FG : Slot.frame_given B API LS SH SK ra empty.
Hypothesis PRE : lib_pre_x (LS := LS) (SH := SH) (SK := SK) B (API rc) SLOT_STACK empty L0 A0 rg mem0 md0 ra p0 n0 pl b.
Hypothesis RG2 : spZ rg = S.

Notation CF := (SlotInv.CF B (API rc) S rg mem0 md0 L0 A0).
Notation FB := (SlotInv.FB S).

(* stB's facts for its witnesses. *)
Definition SB (fx : FPState) L A regs mem md O R1 x quit (text copy arr : Z) (jsv jw : list byte) (m p n : Z)
    (R0 : rstate) : Prop :=
  CF fx L A regs mem md /\ SlotInv.rcap A /\
  vr_run (rec_clear R0) (m_D p0 pl p n) = (R1, x, quit) /\
  RFX L0 A0 L A mem R1 O (qv quit)
    [(text, strnlen_res (m_len p0 pl p n) (m_D p0 pl p n) + 1); (copy, strnlen_res (m_len p0 pl p n) (m_D p0 pl p n) + 1);
     (arr, arr_size (strnlen_res (m_len p0 pl p n) (m_D p0 pl p n)))] /\
  text <> copy /\ text <> arr /\ copy <> arr /\ text mod 16 = 0 /\ copy mod 16 = 0 /\ arr mod 16 = 0 /\
  LR p0 n0 pl m p n regs mem /\
  getr regs 10 = Z_to_bv 64 arr /\ getr regs 18 = Z_to_bv 64 (r_state R0) /\
  getr regs 19 = Z_to_bv 64 (r_host R0) /\ getr regs 20 = Z_to_bv 64 text /\ getr regs 21 = Z_to_bv 64 copy /\
  getr regs 23 = Z_to_bv 64 (strnlen_res (m_len p0 pl p n) (m_D p0 pl p n)) /\
  rw_cells rsegs mem FB (LOC0 jsv) /\
  rw_cells rsegs mem (FB + 40) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); CB 16 jw] /\
  msg_props R0 (m_D p0 pl p n).

Lemma b3_disj : forall (fx : FPState) L A mem md q1 k1 q2 k2, aa_MR (API rc) L A mem md ->
  In (q1, k1) (blocks L A) -> In (q2, k2) (blocks L A) -> (q1, k1) <> (q2, k2) -> q1 + k1 <= q2 \/ q2 + k2 <= q1.
Proof.
  intros fx L A mem md q1 k1 q2 k2 HM H1 H2 Ne.
  destruct (YI04.pairwise_in2 _ _ _ _ (mr_blocks_disjoint B _ (aa_laws (API rc)) L A mem md HM) H1 H2 Ne) as [D|D];
    unfold ranges_disjoint in D; cbn in D; lia.
Qed.

Lemma b3_blk : forall (fx : FPState) L A mem md q k, aa_MR (API rc) L A mem md -> In (q, k) (blocks L A) -> 0 < k ->
  4096 <= q /\ q + k <= alloc_ceiling /\ (q + k <= 0x10000 \/ 0x55000 <= q).
Proof.
  intros fx L A mem md q k HM Hin Hk.
  destruct (it_blk_out B API LS SH SK ra empty FG fx L A mem md q k 0 HM Hin ltac:(lia)) as (_ & H1 & H2).
  split; [exact H1|]. split; [exact H2|].
  apply b3_img; [exact Hk|]. intros i Hi.
  exact (proj1 (it_blk_out B API LS SH SK ra empty FG fx L A mem md q k i HM Hin Hi)).
Qed.

Lemma b3_noimg : forall (fx : FPState) L A mem md q k a, aa_MR (API rc) L A mem md -> In (q, k) (blocks L A) ->
  q <= a < q + k -> ~ in_img B a.
Proof.
  intros fx L A mem md q k a HM Hin Ha.
  unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp). cbn [fst snd] in E. injection E as Eq Ek.
  subst q k'.
  pose proof (ax_blocks_img (it_AX B API LS SH SK ra empty FG fx) L A mem md p k (a - ptr_addr L p) HM Hp ltac:(lia))
    as NI.
  replace (ptr_addr L p + (a - ptr_addr L p)) with a in NI by ring. exact NI.
Qed.

(* A byte of a block of the message: heap, not the allocator's, in no entry block. *)
Lemma b3_xblk : forall (fx : FPState) L A mem md q k a, aa_MR (API rc) L A mem md -> In (q, k) (blocks L A) ->
  ~ In (q, k) (blocks L0 A0) -> (forall a0 k0, In (a0, k0) (blocks L0 A0) -> In (a0, k0) (blocks L A)) ->
  q <= a < q + k ->
  a < alloc_ceiling /\ ~ in_img B a /\ ~ owned B L A a /\
  (forall a0 k0, In (a0, k0) (blocks L0 A0) -> ~ (a0 <= a < a0 + k0)).
Proof.
  intros fx L A mem md q k a HM Hin N0 E0 Ha.
  destruct (KindB.block_facts B _ (aa_laws (API rc)) L A mem md q k (a - q) HM Hin ltac:(lia)) as (_ & Q1 & Q2 & Q3).
  replace (q + (a - q)) with a in Q3 by ring.
  split; [lia|]. split; [exact (b3_noimg fx L A mem md q k a HM Hin Ha)|]. split; [exact Q3|].
  intros a0 k0 H0 Hx.
  assert (Ne : (a0, k0) <> (q, k)) by (intros E; rewrite E in H0; exact (N0 H0)).
  destruct (b3_disj fx L A mem md a0 k0 q k HM (E0 a0 k0 H0) Hin Ne); lia.
Qed.

(* The bytes of a live block, writable, on the normalized memory. *)
Lemma b3_u8 : forall (fx : FPState) L A mem md q k, aa_MR (API rc) L A mem md -> In (q, k) (blocks L A) -> 0 < k ->
  exists bs, u8arr rsegs (normalize_cj rsegs mem) q bs /\ length bs = Z.to_nat k.
Proof.
  intros fx L A mem md q k HM Hin Hk.
  destruct (b3_blk fx L A mem md q k HM Hin Hk) as (Q1 & Q2 & Q3).
  pose proof alloc_ceiling_val as AC.
  assert (PR : forall i, 0 <= i < Z.of_nat (Z.to_nat k) -> present mem (q + i)).
  { intros i Hi. exact (proj1 (KindB.block_facts B _ (aa_laws (API rc)) L A mem md q k i HM Hin ltac:(lia))). }
  destruct (KindB.present_rw_cells rsegs mem q (Z.to_nat k) ltac:(lia) ltac:(lia) PR) as [junk [[Hwf Hb] Hw]].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  assert (Lj : length junk = Z.to_nat k) by (cbn in Hwf; tauto).
  exists junk. split; [|exact Lj].
  apply b3_cj_u8.
  - split; [exact Hb|].
    replace (Z.of_nat (length junk)) with (Z.of_nat (cells_size [CB (Z.to_nat k) junk])) by (cbn [cells_size csize]; lia).
    exact Hw.
  - rewrite Lj. unfold TASK_SIZE. lia.
  - intros i Hi. rewrite Lj in Hi. lia.
Qed.

(* The reply: its block, its bytes x with the slack up to the 8-byte end, apart from the message's blocks. *)
Lemma b3_rep : forall (fx : FPState) L A mem md R O text copy arr kt kc ka x lo,
  aa_MR (API rc) L A mem md -> g_rec_rep rsegs L A mem R O ->
  In (text, kt) (blocks L A) -> ~ In text (map fst O) -> In (copy, kc) (blocks L A) -> ~ In copy (map fst O) ->
  In (arr, ka) (blocks L A) -> ~ In arr (map fst O) ->
  text mod 8 = 0 -> copy mod 8 = 0 -> arr mod 8 = 0 -> lo mod 8 = 0 -> alloc_ceiling <= lo ->
  r_reply R = Some (x ++ [Z_to_bv 8 0]) ->
  exists rep slack,
    bytes_at rsegs mem (CommandModel.G_REC + REC_REPLY) (le8 rep) /\
    bytes_at rsegs mem (CommandModel.G_REC + REC_REPLY_SIZE) (le8 (Z_to_bv 64 (Z.of_nat (length x) + 1))) /\
    bv_unsigned rep <> 0 /\ bytes_at rsegs mem (bv_unsigned rep) (x ++ NUL :: slack) /\
    b3_slk (bv_unsigned rep) x slack /\
    forall i, 0 <= i < Z.of_nat (length x) + 1 + Z.of_nat (length slack) ->
      (bv_unsigned rep + i < text \/ text + kt <= bv_unsigned rep + i) /\
      (bv_unsigned rep + i < copy \/ copy + kc <= bv_unsigned rep + i) /\
      (bv_unsigned rep + i < arr \/ arr + ka <= bv_unsigned rep + i) /\ bv_unsigned rep + i < lo.
Proof.
  intros fx L A mem md R O text copy arr kt kc ka x lo HM REP XT NTO XC NCO XA NAO T8 C8' A8 L8 LO RR.
  pose proof alloc_ceiling_val as AC.
  destruct (it_FA B API LS SH SK ra empty FG fx) as (_ & _ & _ & _ & _ & SLACK & _).
  pose proof REP as (Q & (_ & _ & _ & RP & _) & HO).
  unfold reply_at in RP. rewrite RR in RP.
  destruct (l_reply Q) as [[pr pk]|] eqn:EQ; [|contradiction].
  destruct RP as (RW & RS & Hpr0 & _ & Hpb & Hpk & RXB & _). cbn [fst snd] in RW, RS, Hpr0, Hpb, Hpk, RXB.
  rewrite length_app in RS, Hpk. cbn [length] in RS, Hpk. rewrite Nat2Z.inj_add in RS, Hpk.
  assert (PO : In (pr, pk) O).
  { apply HO. unfold lay_blocks. rewrite EQ. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
    left. reflexivity. }
  destruct (b3_blk fx L A mem md pr pk HM Hpb ltac:(lia)) as (P1 & P2 & _).
  assert (DT := b3_disj fx L A mem md pr pk text kt HM Hpb XT (b3_ne_O O pr pk text kt PO NTO)).
  assert (DC := b3_disj fx L A mem md pr pk copy kc HM Hpb XC (b3_ne_O O pr pk copy kc PO NCO)).
  assert (DA := b3_disj fx L A mem md pr pk arr ka HM Hpb XA (b3_ne_O O pr pk arr ka PO NAO)).
  pose proof (b3_r8_mono (pr + (Z.of_nat (length x) + 1)) (pr + pk) ltac:(lia)) as RM.
  pose proof (SlotItB2.b2_r8_ge (pr + pk)) as RG.
  assert (RT : pr + pk <= text -> 8 * ((pr + pk + 7) / 8) <= text) by (intros H; apply SlotItB2.b2_r8; assumption).
  assert (RC : pr + pk <= copy -> 8 * ((pr + pk + 7) / 8) <= copy) by (intros H; apply SlotItB2.b2_r8; assumption).
  assert (RA' : pr + pk <= arr -> 8 * ((pr + pk + 7) / 8) <= arr) by (intros H; apply SlotItB2.b2_r8; assumption).
  assert (RL : 8 * ((pr + pk + 7) / 8) <= lo) by (apply SlotItB2.b2_r8; [lia | exact L8]).
  destruct (RecGlue.slack_bytes rsegs mem pr (Z.of_nat (length x) + 1) (x ++ [Z_to_bv 8 0]) RXB
              ltac:(rewrite length_app; cbn [length]; lia) ltac:(lia) ltac:(lia)) as (slack & SBy & SL).
  { intros a Ha. destruct (Z_lt_ge_dec a (pr + pk)) as [Hl|Hg].
    - replace a with (pr + (a - pr)) by ring.
      exact (proj1 (KindB.block_facts B _ (aa_laws (API rc)) L A mem md pr pk (a - pr) HM Hpb ltac:(lia))).
    - apply (SLACK L A mem md pr pk a HM Hpb). lia. }
  exists (Z_to_bv 64 pr), slack. rewrite unsigned_lit by lia.
  split; [exact RW|]. split; [exact RS|]. split; [exact Hpr0|].
  split; [rewrite <- app_assoc in SBy; exact SBy|].
  split; [unfold b3_slk; apply b3_slack_len; lia|].
  intros i Hi. lia.
Qed.

(* The answer word and, when it is not 0, the answer's bytes apart from the message's blocks. *)
Lemma b3_ans : forall (fx : FPState) L A mem md R O text copy arr kt kc ka lo,
  aa_MR (API rc) L A mem md -> g_rec_rep rsegs L A mem R O ->
  In (text, kt) (blocks L A) -> ~ In text (map fst O) -> In (copy, kc) (blocks L A) -> ~ In copy (map fst O) ->
  In (arr, ka) (blocks L A) -> ~ In arr (map fst O) -> alloc_ceiling <= lo ->
  exists ans xa,
    bytes_at rsegs mem (CommandModel.G_REC + REC_ANSWER) (le8 ans) /\
    (bv_unsigned ans <> 0 -> r_answer R = Some xa /\ cstr_at mem (bv_unsigned ans) xa /\
       forall i, 0 <= i < Z.of_nat (length xa) + 1 ->
         (bv_unsigned ans + i < text \/ text + kt <= bv_unsigned ans + i) /\
         (bv_unsigned ans + i < copy \/ copy + kc <= bv_unsigned ans + i) /\
         (bv_unsigned ans + i < arr \/ arr + ka <= bv_unsigned ans + i) /\ bv_unsigned ans + i < lo) /\
    (bv_unsigned ans = 0 -> r_answer R = None).
Proof.
  intros fx L A mem md R O text copy arr kt kc ka lo HM REP XT NTO XC NCO XA NAO LO.
  pose proof REP as (Q & (_ & _ & HA & _) & HO).
  unfold answer_at in HA.
  destruct (r_answer R) as [t|] eqn:ER; destruct (l_answer Q) as [[pa ka']|] eqn:EA; try contradiction.
  - destruct HA as (AW & Hpa0 & Hpb & Hpk & AXB & AN & _). cbn [fst snd] in AW, Hpa0, Hpb, Hpk, AXB.
    assert (PO : In (pa, ka') O).
    { apply HO. unfold lay_blocks. rewrite EA. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
      left. reflexivity. }
    destruct (b3_blk fx L A mem md pa ka' HM Hpb ltac:(lia)) as (P1 & P2 & _).
    assert (DT := b3_disj fx L A mem md pa ka' text kt HM Hpb XT (b3_ne_O O pa ka' text kt PO NTO)).
    assert (DC := b3_disj fx L A mem md pa ka' copy kc HM Hpb XC (b3_ne_O O pa ka' copy kc PO NCO)).
    assert (DA := b3_disj fx L A mem md pa ka' arr ka HM Hpb XA (b3_ne_O O pa ka' arr ka PO NAO)).
    exists (Z_to_bv 64 pa), t. rewrite unsigned_lit by (pose proof alloc_ceiling_val; lia).
    split; [exact AW|]. split; [|intros H; contradiction].
    intros _. split; [reflexivity|]. split; [split; [exact AXB | exact AN]|].
    intros i Hi. lia.
  - exists (Z_to_bv 64 0), []. split; [exact HA|]. rewrite unsigned_lit by lia.
    split; [intros H; contradiction | intros _; reflexivity].
Qed.

(* g_rec.ncalls and the first call's fn. *)
Lemma b3_calls : forall L A mem R O, g_rec_rep rsegs L A mem R O ->
  0 <= Z.of_nat (length (r_calls R)) <= 16 /\
  bytes_at rsegs mem (CommandModel.G_REC + CommandModel.REC_NCALLS) (le4 (Z_to_bv 64 (Z.of_nat (length (r_calls R))))) /\
  (0 < Z.of_nat (length (r_calls R)) -> 0 <= fst (nth 0 (r_calls R) (0, [])) < 26 /\
     bytes_at rsegs mem (CommandModel.G_REC + CommandModel.REC_CALLS + CALL_FN)
       (le4 (Z_to_bv 64 (fst (nth 0 (r_calls R) (0, [])))))).
Proof.
  intros L A mem R O (Q & (_ & GC & _) & _).
  destruct GC as (CL & CQ & CN & CI & _).
  split; [lia|]. split; [exact CN|].
  intros Hp. destruct (r_calls R) as [|c cs] eqn:Ec; [cbn in Hp; lia|].
  destruct (l_calls Q) as [|P Ps] eqn:EP; [cbn in CQ; discriminate|].
  destruct (CI 0%nat c P eq_refl eq_refl) as [(H1 & _ & _ & H4 & _) _].
  cbn [nth]. unfold REC_FN_COUNT in H1. split; [lia|].
  unfold CALL_OFF_FN, OFF_CALLS, CALL_SIZE in H4. unfold CommandModel.REC_CALLS, CALL_FN.
  replace (G_REC + 16 + 56 * Z.of_nat 0 + 0) with (CommandModel.G_REC + 16 + 0) in H4 by (unfold G_REC, CommandModel.G_REC; lia).
  exact H4.
Qed.

Lemma b3_ha1 : forall c l a, 0 <= l -> 4096 <= c -> c + (l + 1) <= alloc_ceiling -> c + l + 1 <= a -> a < c + l + 1 + 8 ->
  0 <= a < TASK_SIZE.
Proof. intros c l a H0 H1 H2 H3 H4. pose proof alloc_ceiling_val. unfold TASK_SIZE. lia. Qed.

Lemma b3_ha2 : forall c l a, 0 <= l -> (c + (l + 1) <= 0x10000 \/ 0x55000 <= c) ->
  c + l + 1 <= a < 8 * ((c + l + 1 + 7) / 8) -> ~ (0x10000 <= a < 0x22000).
Proof.
  intros c l a H0 [H|H] [H1 H2]; [pose proof (b3_r8_low (c + l + 1) a ltac:(lia) H2); lia | lia].
Qed.

(* From stB's facts: the run on the normalized memory to check_words' entry. *)
Lemma b3_evt : check_reply_contract -> check_arity_contract -> memcpy_contract -> strspn_contract -> strcspn_contract ->
  forall fx L A regs mem md O R1 x quit text copy arr jsv jw m p n R0,
  SB fx L A regs mem md O R1 x quit text copy arr jsv jw m p n R0 ->
  Exec.evt rsegs (SlotItB2.w_post (Z_to_bv 64 FB) (reg_get regs 3) (reg_get regs 4) (reg_get regs 18)
      (reg_get regs 19) (reg_get regs 22) (reg_get regs 24) (normalize_cj rsegs mem) (S - SLOT_STACK) (m_src p n)
      (m_len p0 pl p n) text copy arr (m_D p0 pl p n))
    (MS (Regs6ss.mkR_of regs) (@fp_regs fx) (Z_to_bv 64 0x141c8) (@fp_csr fx) None (normalize_cj rsegs mem)
       (seg_rom rsegs)).
Proof.
  intros CRC CAC MEMC SSPN SCSPN fx L A regs mem md O R1 x quit text copy arr jsv jw m p n R0
    (HCF & HRC & EVR & HRX & D1 & D2 & D3 & T16 & C16 & A16 & HLR & G10 & G18 & G19 & G20 & G21 & G23 & LC0 & LC1 & MP).
  pose proof HCF as (M & Wf & Bd & I & (vm & Hmd) & R2 & R3 & R4 & SV & SW & SF & RO & GIm & EB & FZ).
  pose proof HRX as (REP & SPILL & QB & Hq & ENO & BLK & XC & HOL).
  pose proof HLR as (L8 & L9 & L22 & L24 & L25 & L27 & Hm & Hn & Hp & Hpn).
  assert (SEGS : ms_segs B = rsegs) by exact (it_SEGS B API LS SH SK ra empty FG).
  pose proof (it_HS B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b PRE RG2) as HS.
  assert (TS : S <= TASK_SIZE) by (eapply it_TS; eassumption).
  assert (S16 : S mod 16 = 0) by (eapply it_S16; eassumption).
  assert (T8 : b3_al8 text) by exact (b3_m8 _ T16).
  assert (C8' : b3_al8 copy) by exact (b3_m8 _ C16).
  assert (A8 : b3_al8 arr) by exact (b3_m8 _ A16).
  assert (LO8 : b3_al8 (S - SLOT_STACK)) by (unfold b3_al8, SLOT_STACK; clear - S16; Z.div_mod_to_equations; lia).
  clear T16 C16 A16 S16.
  pose proof alloc_ceiling_val as AC.
  assert (Hn0 : 0 < n0) by (clear - Hn Hp Hpn; lia).
  destruct (it_inblk B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE fx L A regs mem md HCF Hn0)
    as (IB & IB0 & Hp04 & Hpac & HL & _).
  pose proof (m_len_range p0 pl p n Hn) as [HL1 HL2].
  pose proof (m_D_len p0 n0 pl p n Hn Hp Hpn HL) as HDL.
  pose proof (SlotRec.strnlen_upto0 _ _ HDL) as HU.
  set (LWv := strnlen_res (m_len p0 pl p n) (m_D p0 pl p n)) in *.
  assert (LWR : 0 <= LWv <= m_len p0 pl p n).
  { assert (E : Verbs.upto0 (m_D p0 pl p n) = firstn (length (Verbs.upto0 (m_D p0 pl p n))) (m_D p0 pl p n))
      by (unfold Verbs.upto0; apply SlotWords.sw_upto_prefix).
    apply (f_equal (@length byte)) in E. rewrite length_firstn in E. clear - E HU HDL. lia. }
  destruct (XC _ (or_introl eq_refl)) as (XT & NT0 & NTO).
  destruct (XC _ (or_intror (or_introl eq_refl))) as (XCo & NC0 & NCO).
  destruct (XC _ (or_intror (or_intror (or_introl eq_refl)))) as (XA & NA0 & NAO).
  cbn [fst] in NTO, NCO, NAO.
  assert (ASZ : 16 <= arr_size LWv <= 2 ^ 16) by (unfold arr_size; clear - LWR HL1; Z.div_mod_to_equations; lia).
  destruct (b3_blk fx L A mem md text (LWv + 1) M XT ltac:(clear - LWR; lia)) as (TB1 & TB2 & TB3).
  destruct (b3_blk fx L A mem md copy (LWv + 1) M XCo ltac:(clear - LWR; lia)) as (CB1 & CB2 & CB3).
  destruct (b3_blk fx L A mem md arr (arr_size LWv) M XA ltac:(clear - ASZ; lia)) as (AB1 & AB2 & AB3).
  assert (DTC := b3_disj fx L A mem md _ _ _ _ M XT XCo ltac:(intros E; exact (D1 (f_equal fst E)))).
  assert (DTA := b3_disj fx L A mem md _ _ _ _ M XT XA ltac:(intros E; exact (D2 (f_equal fst E)))).
  assert (DCA := b3_disj fx L A mem md _ _ _ _ M XCo XA ltac:(intros E; exact (D3 (f_equal fst E)))).
  assert (DIT := b3_disj fx L A mem md p0 n0 text _ M IB XT ltac:(intros E; rewrite E in IB0; exact (NT0 IB0))).
  assert (USP : bv_unsigned (Z_to_bv 64 FB) = FB).
  { apply unsigned_lit. unfold SlotInv.FB. unfold SLOT_STACK in HS. clear - HS AC. lia. }
  (* Section W of SlotItB2 *)
  assert (H_lo : 0x54cb8 <= S - SLOT_STACK) by (unfold SLOT_STACK in *; clear - HS AC; lia).
  assert (H_LOS : S - SLOT_STACK + 6000 <= bv_unsigned (Z_to_bv 64 FB))
    by (rewrite USP; unfold SlotInv.FB, SLOT_STACK; clear - HS; lia).
  assert (H_SPH : bv_unsigned (Z_to_bv 64 FB) + 176 <= 2 ^ 63) by (rewrite USP; unfold SlotInv.FB; clear - HS; lia).
  assert (H_TS : bv_unsigned (Z_to_bv 64 FB) + 176 <= TASK_SIZE) by (rewrite USP; unfold SlotInv.FB; clear - TS; lia).
  assert (H_src : 0 <= m_src p n /\ m_src p n + m_len p0 pl p n <= S - SLOT_STACK).
  { unfold m_src, hdr_n in *. unfold SLOT_STACK in *. clear - HL1 HL2 Hp Hpn Hp04 Hpac HS Hn. lia. }
  assert (H_tx : 0 < text /\ text + LWv + 1 <= S - SLOT_STACK) by (unfold SLOT_STACK in *; clear - TB1 TB2 HS; lia).
  assert (H_cp : 0 < copy /\ copy + LWv + 1 <= S - SLOT_STACK) by (unfold SLOT_STACK in *; clear - CB1 CB2 HS; lia).
  assert (H_ar : 0 < arr /\ arr + arr_size LWv <= S - SLOT_STACK) by (unfold SLOT_STACK in *; clear - AB1 AB2 HS; lia).
  assert (H_txi : text + LWv + 1 <= 0x10000 \/ 0x54cb8 <= text) by (clear - TB3; lia).
  assert (H_cpi : copy + LWv + 1 <= 0x10000 \/ 0x54cb8 <= copy) by (clear - CB3; lia).
  assert (H_ari : arr + arr_size LWv <= 0x10000 \/ 0x54cb8 <= arr) by (clear - AB3; lia).
  assert (H_d1 : text + LWv + 1 <= copy \/ copy + LWv + 1 <= text) by (clear - DTC; lia).
  assert (H_d2 : arr + arr_size LWv <= text \/ text + LWv + 1 <= arr) by (clear - DTA; lia).
  assert (H_d3 : arr + arr_size LWv <= copy \/ copy + LWv + 1 <= arr) by (clear - DCA; lia).
  assert (H_d4 : m_src p n + m_len p0 pl p n <= text \/ text + LWv + 1 <= m_src p n).
  { unfold m_src, hdr_n in *. clear - DIT HL1 HL2 Hp Hpn Hn. lia. }
  pose proof (MemNorm.mem_inv_cj_task rsegs _ (MemNorm.mem_inv_cj_normalize rsegs mem)) as H_tk.
  destruct (it_vrt B API LS SH SK ra empty FG fx L A mem md M GIm) as (can0 & _ & _ & V3 & V4).
  assert (SSPn : VerbsMem.ssp_at (normalize_cj rsegs mem) can0).
  { split.
    - apply (bytes_at_normalize_cj_low rsegs mem _ _ RO); [rewrite Mem.length_le8; cz |].
      apply (send_message.sm_bytes_of_le B mem VerbsB.SSP_GOT_B (Mem.le8 (Z_to_bv 64 VerbsB.SSP_GUARD_B)) SEGS);
        [cbv; discriminate | rewrite Mem.length_le8; cz | exact V3].
    - apply (bytes_at_normalize_cj_low rsegs mem _ _ RO); [rewrite Mem.length_le8; cz |].
      apply (send_message.sm_bytes_of_le B mem VerbsB.SSP_GUARD_B (Mem.le8 can0) SEGS);
        [cbv; discriminate | rewrite Mem.length_le8; cz | exact V4]. }
  destruct (chain_words.cw_f18 _ _ SSPn) as [H_gg (can & H_gu)].
  destruct (it_FA B API LS SH SK ra empty FG fx) as (_ & _ & _ & _ & _ & SLACK & _).
  assert (H_cs : forall a, copy + LWv + 1 <= a < 8 * ((copy + LWv + 1 + 7) / 8) ->
            mbyte rsegs (normalize_cj rsegs mem) a <> None).
  { intros a Ha.
    assert (Pa : present mem a).
    { apply (SLACK L A mem md copy (LWv + 1) a M XCo). rewrite Z.add_assoc. exact Ha. }
    pose proof (b3_r8_lt _ _ Ha) as H8.
    pose proof (b3_ha1 copy LWv a (proj1 LWR) CB1 CB2 (proj1 Ha) H8) as Ha1.
    pose proof (b3_ha2 copy LWv a (proj1 LWR) CB3 Ha) as Ha2.
    rewrite (proj1 (b3_cj_mbyte mem a Ha1 Ha2)).
    destruct Pa as [bb Eb]. unfold mbyte. rewrite Eb. discriminate. }
  assert (GI' : forall a, in_globals frame_RELRO a -> mbyte rsegs mem a = seg_rom rsegs (Z_to_bv 64 a)).
  { intros a Ha. rewrite <- SEGS. exact (GIm a Ha). }
  destruct (SlotRec.relro_img mem GI') as (IG1 & _ & _ & IG4 & IG5 & IG6 & _ & _).
  assert (H_grec : bytes_at rsegs (normalize_cj rsegs mem) CommandModel.GOT_GREC (le8 (Z_to_bv 64 CommandModel.G_REC))).
  { apply (bytes_at_normalize_cj_low rsegs mem _ _ RO); [rewrite length_le8; cz|].
    exact IG1. }
  assert (H_gq : bytes_at rsegs (normalize_cj rsegs mem) CommandModel.GOT_GQUIT (le8 (Z_to_bv 64 CommandModel.G_QUIT))).
  { apply (bytes_at_normalize_cj_low rsegs mem _ _ RO);
      [rewrite length_le8; cz|].
    exact IG4. }
  assert (H_sh : bytes_at rsegs (normalize_cj rsegs mem) G_SHAPES g_shapes_bytes).
  { assert (GL : length g_shapes_bytes = 448%nat) by (vm_compute; reflexivity).
    apply (bytes_at_normalize_cj_low rsegs mem _ _ RO); [rewrite GL; cz|]. exact IG5. }
  assert (H_par : bytes_at rsegs (normalize_cj rsegs mem) G_PARSED g_parsed_bytes).
  { assert (GL : length g_parsed_bytes = 528%nat) by (vm_compute; reflexivity).
    apply (bytes_at_normalize_cj_low rsegs mem _ _ RO); [rewrite GL; cz|]. exact IG6. }
  assert (H_q : 0 <= qv quit < 2 ^ 32 /\ bytes_at rsegs (normalize_cj rsegs mem) CommandModel.G_QUIT (le4 (Z_to_bv 64 (qv quit)))).
  { split; [exact Hq|]. apply (bytes_at_normalize_cj_low rsegs mem _ _ RO);
      [rewrite length_le4; cz | exact QB]. }
  (* the recorder *)
  pose proof MP as MP'. unfold msg_props in MP'. rewrite EVR in MP'. cbv beta iota zeta in MP'.
  destruct MP' as (NR1 & RR & N0 & _ & AOK & ROK & ARO & _).
  destruct (it_rep_parts L A mem R1 O REP) as [_ (_ & _ & X3 & _ & _ & _)].
  rewrite NR1 in X3.
  assert (H_nr : bytes_at rsegs (normalize_cj rsegs mem) (CommandModel.G_REC + REC_NREPLIES) (le4 (Z_to_bv 64 1))).
  { apply (bytes_at_normalize_cj_low rsegs mem _ _ RO);
      [rewrite length_le4; cz | exact X3]. }
  assert (LOA : alloc_ceiling <= S - SLOT_STACK) by (clear - HS; lia).
  destruct (b3_rep fx L A mem md R1 O text copy arr _ _ _ x (S - SLOT_STACK) M REP XT NTO XCo NCO XA NAO
              T8 C8' A8 LO8 LOA RR)
    as (rep & slack & RP0 & RS0 & H_rnz & RB0 & H_sl & ROUT).
  destruct (b3_ans fx L A mem md R1 O text copy arr _ _ _ (S - SLOT_STACK) M REP XT NTO XCo NCO XA NAO LOA)
    as (ans & xa & AN0 & HAN & HAZ).
  destruct (b3_calls L A mem R1 O REP) as (NC1 & NC2 & FN0).
  assert (H_rp : bytes_at rsegs (normalize_cj rsegs mem) (CommandModel.G_REC + REC_REPLY) (le8 rep)).
  { apply (bytes_at_normalize_cj_low rsegs mem _ _ RO);
      [rewrite length_le8; cz | exact RP0]. }
  assert (H_rs : bytes_at rsegs (normalize_cj rsegs mem) (CommandModel.G_REC + REC_REPLY_SIZE)
                   (le8 (Z_to_bv 64 (Z.of_nat (length x) + 1)))).
  { apply (bytes_at_normalize_cj_low rsegs mem _ _ RO);
      [rewrite length_le8; cz | exact RS0]. }
  assert (H_ans : bytes_at rsegs (normalize_cj rsegs mem) (CommandModel.G_REC + REC_ANSWER) (le8 ans)).
  { apply (bytes_at_normalize_cj_low rsegs mem _ _ RO);
      [rewrite length_le8; cz | exact AN0]. }
  assert (H_rb : bytes_at rsegs (normalize_cj rsegs mem) (bv_unsigned rep) (x ++ NUL :: slack)).
  { apply (bytes_at_normalize_cj_low rsegs mem _ _ RO); [|exact RB0].
    rewrite length_app. cbn [length].
    pose proof (ROUT (Z.of_nat (length x) + Z.of_nat (length slack)) ltac:(clear - x slack; lia)) as (_ & _ & _ & H).
    unfold TASK_SIZE. clear - H HS TS. unfold SLOT_STACK in *. unfold TASK_SIZE in TS. lia. }
  assert (H_ro : forall i, 0 <= i < Z.of_nat (length x) + 1 + Z.of_nat (length slack) ->
            Frame.outside [(text, text + LWv + 1); (copy, copy + LWv + 1); (arr, arr + arr_size LWv);
                           (bv_unsigned (Z_to_bv 64 FB) - 96, bv_unsigned (Z_to_bv 64 FB) + 72)] (bv_unsigned rep + i) /\
            bv_unsigned rep + i < S - SLOT_STACK).
  { intros i Hi. destruct (ROUT i Hi) as (O1 & O2 & O3 & O4). split; [|exact O4].
    rewrite USP. apply b3_out4; unfold SlotInv.FB, SLOT_STACK in *; clear - O1 O2 O3 O4; lia. }
  assert (H_ab : bv_unsigned ans <> 0 -> cstr_at (normalize_cj rsegs mem) (bv_unsigned ans) xa /\
            forall i, 0 <= i < Z.of_nat (length xa) + 1 ->
              Frame.outside [(text, text + LWv + 1); (copy, copy + LWv + 1); (arr, arr + arr_size LWv);
                             (bv_unsigned (Z_to_bv 64 FB) - 96, bv_unsigned (Z_to_bv 64 FB) + 72)] (bv_unsigned ans + i) /\
              bv_unsigned ans + i < S - SLOT_STACK).
  { intros Hne. destruct (HAN Hne) as (_ & [Hb Hn'] & AOUT). split; [split; [|exact Hn']|].
    - apply (bytes_at_normalize_cj_low rsegs mem _ _ RO); [|exact Hb].
      rewrite length_app. cbn [length].
      pose proof (AOUT (Z.of_nat (length xa)) ltac:(clear - xa; lia)) as (_ & _ & _ & H).
      clear - H HS TS. unfold SLOT_STACK in *. unfold TASK_SIZE in *. lia.
    - intros i Hi. destruct (AOUT i Hi) as (O1 & O2 & O3 & O4). split; [|exact O4].
      rewrite USP. apply b3_out4; unfold SlotInv.FB, SLOT_STACK in *; clear - O1 O2 O3 O4; lia. }
  assert (H_aok : answer_ok ans x xa (Z.of_nat (length (Verbs.words (Verbs.line (m_D p0 pl p n)))))
                    (nth 0 (Verbs.words (Verbs.line (m_D p0 pl p n))) [])).
  { split.
    - intros Hne. destruct (HAN Hne) as (EA & _). rewrite EA in AOK. exact AOK.
    - intros Hz. rewrite (HAZ Hz) in AOK. exact AOK. }
  assert (H_nc : 0 <= Z.of_nat (length (r_calls R1)) <= 16 /\
            bytes_at rsegs (normalize_cj rsegs mem) (CommandModel.G_REC + CommandModel.REC_NCALLS)
              (le4 (Z_to_bv 64 (Z.of_nat (length (r_calls R1)))))).
  { split; [exact NC1|]. apply (bytes_at_normalize_cj_low rsegs mem _ _ RO);
      [rewrite length_le4; cz | exact NC2]. }
  assert (H_fn : 0 < Z.of_nat (length (r_calls R1)) -> 0 <= fst (nth 0 (r_calls R1) (0, [])) < 26 /\
            bytes_at rsegs (normalize_cj rsegs mem) (CommandModel.G_REC + CommandModel.REC_CALLS + CALL_FN)
              (le4 (Z_to_bv 64 (fst (nth 0 (r_calls R1) (0, [])))))).
  { intros Hp'. destruct (FN0 Hp') as [F1 F2]. split; [exact F1|].
    apply (bytes_at_normalize_cj_low rsegs mem _ _ RO);
      [rewrite length_le4; cz | exact F2]. }
  (* w_evt's own premises *)
  pose proof (MemNorm.mem_inv_cj_inv rsegs _ (MemNorm.mem_inv_cj_normalize rsegs mem)) as MI.
  assert (ST : stk rsegs (normalize_cj rsegs mem) (S - SLOT_STACK) (bv_unsigned (Z_to_bv 64 FB))).
  { rewrite USP. apply RecAns.stk_normalize_cj; [unfold SLOT_STACK in *; clear - HS AC; lia | unfold SlotInv.FB; clear - TS; lia|].
    intros a Ha. apply SW. left. rewrite RG2. unfold SlotInv.FB in Ha. clear - Ha. lia. }
  assert (HSRC : 0 <= m_src p n - p0) by (unfold m_src, hdr_n; clear - Hp Hn; lia).
  pose proof (it_in_bytes B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE fx L A regs mem md HCF Hn0
     (m_src p n - p0) (m_len p0 pl p n) HSRC ltac:(clear - HL1; lia)
     ltac:(unfold m_src, hdr_n in *; clear - HL1 HL2 Hp Hpn Hn; lia)) as HD.
  replace (p0 + (m_src p n - p0)) with (m_src p n) in HD by ring.
  change (firstn (Z.to_nat (m_len p0 pl p n)) (skipn (Z.to_nat (m_src p n - p0)) pl)) with (m_D p0 pl p n) in HD.
  assert (SRC : bytes_at rsegs (normalize_cj rsegs mem) (m_src p n) (m_D p0 pl p n)).
  { apply (bytes_at_normalize_cj_low rsegs mem _ _ RO); [|exact HD].
    rewrite HDL. destruct H_src as [_ Hs2]. unfold SLOT_STACK in *. clear - Hs2 HS TS. lia. }
  destruct (b3_u8 fx L A mem md text (LWv + 1) M XT ltac:(clear - LWR; lia)) as (jt & TX & LT).
  destruct (b3_u8 fx L A mem md copy (LWv + 1) M XCo ltac:(clear - LWR; lia)) as (jc & CP & LC).
  destruct (b3_u8 fx L A mem md arr (arr_size LWv) M XA ltac:(clear - ASZ; lia)) as (ja & AR & LA).
  assert (FR0 : rw_cells rsegs (normalize_cj rsegs mem) (bv_unsigned (Z_to_bv 64 FB)) (LOC0 jsv)).
  { rewrite USP. apply b3_cj_cells; [exact LC0 | unfold SlotInv.FB, SLOT_STACK in *; clear - HS AC; lia | | ].
    - unfold LOC0. cbn. unfold SlotInv.FB, TASK_SIZE in *. clear - TS. lia.
    - intros i Hi. unfold LOC0 in Hi. cbn in Hi. unfold SlotInv.FB, SLOT_STACK in *. clear - Hi HS AC. lia. }
  assert (FR1 : rw_cells rsegs (normalize_cj rsegs mem) (bv_unsigned (Z_to_bv 64 FB) + 40)
                  [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); CB 16 jw]).
  { rewrite USP. apply b3_cj_cells; [exact LC1 | unfold SlotInv.FB, SLOT_STACK in *; clear - HS AC; lia | | ].
    - cbn. unfold SlotInv.FB, TASK_SIZE in *. clear - TS. lia.
    - intros i Hi. cbn in Hi. unfold SlotInv.FB, SLOT_STACK in *. clear - Hi HS AC. lia. }
  unfold Regs6ss.mkR_of.
  assert (E2 : reg_get regs 2 = Z_to_bv 64 FB) by exact R2.
  assert (E8 : reg_get regs 8 = Z_to_bv 64 (m_src p n)) by exact L8.
  assert (E9 : reg_get regs 9 = Z_to_bv 64 (m_len p0 pl p n)) by exact L9.
  assert (E10 : reg_get regs 10 = Z_to_bv 64 arr) by exact G10.
  assert (E20 : reg_get regs 20 = Z_to_bv 64 text) by exact G20.
  assert (E21 : reg_get regs 21 = Z_to_bv 64 copy) by exact G21.
  assert (E23 : reg_get regs 23 = Z_to_bv 64 LWv) by exact G23.
  assert (E25 : reg_get regs 25 = Z_to_bv 64 MASK) by exact L25.
  assert (E27 : reg_get regs 27 = Z_to_bv 64 32) by exact L27.
  rewrite E2, E8, E9, E10, E20, E21, E23, E25, E27.
  exact (SlotItB2.w_evt (Z_to_bv 64 FB) (reg_get regs 3) (reg_get regs 4) (reg_get regs 18) (reg_get regs 19)
    (reg_get regs 22) (reg_get regs 24) (@fp_regs fx) (@fp_csr fx) (normalize_cj rsegs mem) (S - SLOT_STACK) (m_src p n)
    (m_len p0 pl p n) text copy arr (m_D p0 pl p n) can H_lo H_LOS H_SPH H_TS HL1 H_src LWR H_tx H_cp H_ar eq_refl
    SSPN SCSPN MEMC CRC CAC HDL H_txi H_cpi H_ari H_d1 H_d2 H_d3 H_d4 (conj T8 (conj A8 LO8)) FZ H_tk H_gg H_gu H_cs
    ans rep x slack xa (Z.of_nat (length (r_calls R1))) (fst (nth 0 (r_calls R1) (0, []))) (qv quit)
    H_grec H_ans H_nr H_rp H_rs H_sh H_rnz H_rb N0 H_sl H_ro H_ab H_aok ROK H_par H_nc H_fn H_gq H_q ARO
    SlotItCK.ck_evt_holds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ jt jc ja jsv jw MI ST SRC TX LT CP LC AR LA FR0 FR1).
Qed.

(* From the run's end (w_post on the normalized memory) back to the real memory: stBW. *)
Lemma b3_post : forall fx L A regs mem md O R1 x quit text copy arr jsv jw m p n R0,
  SB fx L A regs mem md O R1 x quit text copy arr jsv jw m p n R0 ->
  (r_refuse R0 <> 0 -> declared (r_code R0) = true) -> 0 <= r_state R0 < 2 ^ 64 -> 0 <= r_host R0 < 2 ^ 64 ->
  forall R' F' pc' fc' m0' regs' mem',
  SlotItB2.w_post (Z_to_bv 64 FB) (reg_get regs 3) (reg_get regs 4) (reg_get regs 18) (reg_get regs 19)
      (reg_get regs 22) (reg_get regs 24) (normalize_cj rsegs mem) (S - SLOT_STACK) (m_src p n) (m_len p0 pl p n)
      text copy arr (m_D p0 pl p n) (MS R' F' pc' fc' None m0' (seg_rom rsegs)) ->
  mem_rel_cj rsegs mem' m0' -> cj_same rsegs mem mem' -> (forall r, getr regs' r = getr R' r) ->
  stBW B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0 (mkCfg (@mkst (mkFP F' fc') regs' pc' mem' (seg_rom rsegs)) md).
Proof.
  intros fx L A regs mem md O R1 x quit text copy arr jsv jw m p n R0
    (HCF & HRC & EVR & HRX & D1 & D2 & D3 & T16 & C16 & A16 & HLR & G10 & G18 & G19 & G20 & G21 & G23 & LC0 & LC1 & MP)
    DCL RS RH R' F' pc' fc' m0' regs' mem'
    (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc2 & m' & T & C & Aa & wp &
     jsv' & jp & E & MU & WM & MI & FZ2 & LC0' & LC1' & TT & CC & AA & WPL & WPF & WPW) REL ROS GR.
  injection E as ER EF Epc Efc Em. subst R' F' pc' fc' m0'.
  pose proof HCF as (M & Wf & Bd & I & (vm & Hmd) & R2 & R3 & R4 & SV & SW & SF & RO & GIm & EB & FZ).
  pose proof HRX as (REP & SPILL & QB & Hq & ENO & BLK & XC & HOL).
  pose proof HLR as (L8 & L9 & L22 & L24 & L25 & L27 & Hm & Hn & Hp & Hpn).
  clear T16 C16 A16.
  assert (SEGS : ms_segs B = rsegs) by exact (it_SEGS B API LS SH SK ra empty FG).
  pose proof (it_HS B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b PRE RG2) as HS.
  assert (TS : S <= TASK_SIZE) by (eapply it_TS; eassumption).
  pose proof alloc_ceiling_val as AC.
  assert (Hn0 : 0 < n0) by (clear - Hn Hp Hpn; lia).
  destruct (it_inblk B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE fx L A regs mem md HCF Hn0)
    as (IB & IB0 & Hp04 & Hpac & HL & _).
  pose proof (m_len_range p0 pl p n Hn) as [HL1 HL2].
  pose proof (m_D_len p0 n0 pl p n Hn Hp Hpn HL) as HDL.
  pose proof (SlotRec.strnlen_upto0 _ _ HDL) as HU.
  assert (USP : bv_unsigned (Z_to_bv 64 FB) = FB).
  { apply unsigned_lit. unfold SlotInv.FB. unfold SLOT_STACK in HS. clear - HS AC. lia. }
  pose proof (MemNorm.mem_rel_cj_normalize rsegs mem RO) as REL0.
  pose proof (MemNorm.munch_rel_cj rsegs _ _ _ _ _ REL0 REL ROS MU) as MU2.
  pose proof (MemNorm.wmono_rel_cj rsegs _ _ _ _ REL0 REL ROS WM) as WM2.
  pose proof (MemNorm.ro_agree_same_cj rsegs _ _ RO ROS) as RO2.
  pose proof (RecAns.rw_cells_rel_cj rsegs _ _ _ _ REL LC0') as LC0m.
  pose proof (RecAns.rw_cells_rel_cj rsegs _ _ _ _ REL LC1') as LC1m.
  pose proof (RecAns.rw_cells_rel_cj rsegs _ _ _ _ REL TT) as TTm.
  pose proof (RecAns.rw_cells_rel_cj rsegs _ _ _ _ REL CC) as CCm.
  pose proof (RecAns.rw_cells_rel_cj rsegs _ _ _ _ REL AA) as AAm.
  rewrite USP in MU2, LC0m, LC1m.
  clear MU WM LC0' LC1' TT CC AA REL ROS REL0.
  set (LWv := strnlen_res (m_len p0 pl p n) (m_D p0 pl p n)) in *.
  assert (LWR : 0 <= LWv <= m_len p0 pl p n).
  { assert (E : Verbs.upto0 (m_D p0 pl p n) = firstn (length (Verbs.upto0 (m_D p0 pl p n))) (m_D p0 pl p n))
      by (unfold Verbs.upto0; apply SlotWords.sw_upto_prefix).
    apply (f_equal (@length byte)) in E. rewrite length_firstn in E. clear - E HU HDL. lia. }
  destruct (XC _ (or_introl eq_refl)) as (XT & NT0 & NTO).
  destruct (XC _ (or_intror (or_introl eq_refl))) as (XCo & NC0 & NCO).
  destruct (XC _ (or_intror (or_intror (or_introl eq_refl)))) as (XA & NA0 & NAO).
  cbn [fst] in NTO, NCO, NAO.
  assert (ASZ : 16 <= arr_size LWv <= 2 ^ 16) by (unfold arr_size; clear - LWR HL1; Z.div_mod_to_equations; lia).
  destruct (b3_blk fx L A mem md text (LWv + 1) M XT ltac:(clear - LWR; lia)) as (TB1 & TB2 & TB3).
  destruct (b3_blk fx L A mem md copy (LWv + 1) M XCo ltac:(clear - LWR; lia)) as (CB1 & CB2 & CB3).
  destruct (b3_blk fx L A mem md arr (arr_size LWv) M XA ltac:(clear - ASZ; lia)) as (AB1 & AB2 & AB3).
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> (a < text \/ text + LWv + 1 <= a) -> (a < copy \/ copy + LWv + 1 <= a) ->
             (a < arr \/ arr + arr_size LWv <= a) -> a < S - SLOT_STACK ->
             mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a)).
  { intros a Ha H1 H2 H3 H4.
    assert (Ho : Frame.outside [(text, text + LWv + 1); (copy, copy + LWv + 1); (arr, arr + arr_size LWv);
                                (S - SLOT_STACK, FB + 72)] a) by (apply b3_out4; clear - H1 H2 H3 H4; lia).
    split; [exact (KindB.munch_mbyte rsegs _ _ _ a MU2 Ha Ho) | exact (KindB.munch_writable rsegs _ _ _ a MU2 Ha Ho)]. }
  assert (RX2 : RFX L0 A0 L A mem' R1 O (qv quit) [(text, LWv + 1); (copy, LWv + 1); (arr, arr_size LWv)]).
  { apply (it_rfx_move L0 A0 L A mem R1 O (qv quit) _ L A mem' _ HRX).
    - intros a Ha. destruct (KM a) as [E1 W1];
        [lia | clear - Ha TB3; lia | clear - Ha CB3; lia | clear - Ha AB3; lia | unfold SLOT_STACK in *; clear - Ha HS AC; lia |].
      split; [exact E1 | tauto].
    - intros p1 k1 i Hin Hi. destruct (it_rec_blk rsegs L A mem R1 O (p1, k1) REP Hin) as [Hb Hk1]. cbn [snd] in Hk1.
      destruct (b3_blk fx L A mem md p1 k1 M Hb ltac:(clear - Hk1; lia)) as (P1 & P2 & _).
      pose proof (b3_disj fx L A mem md p1 k1 text _ M Hb XT (b3_ne_O O p1 k1 text _ Hin NTO)) as Q1.
      pose proof (b3_disj fx L A mem md p1 k1 copy _ M Hb XCo (b3_ne_O O p1 k1 copy _ Hin NCO)) as Q2.
      pose proof (b3_disj fx L A mem md p1 k1 arr _ M Hb XA (b3_ne_O O p1 k1 arr _ Hin NAO)) as Q3.
      exact (proj1 (KM (p1 + i) ltac:(clear - Hi P1 P2 AC; lia) ltac:(clear - Hi Q1; lia) ltac:(clear - Hi Q2; lia)
        ltac:(clear - Hi Q3; lia) ltac:(unfold SLOT_STACK in *; clear - Hi P2 HS; lia))).
    - intros pn Hin. exact (proj1 (it_rec_blk rsegs L A mem R1 O pn REP Hin)).
    - exact BLK.
    - exact XC. }
  assert (EB0 : forall a0 k0, In (a0, k0) (blocks L0 A0) -> In (a0, k0) (blocks L A))
    by (intros a0 k0 H; exact (proj1 (EB a0 k0 H))).
  assert (CF2 : CF (mkFP Ft fc2) L A regs' mem' md).
  { apply (it_cf_run B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2 fx (mkFP Ft fc2) L A regs mem md
             _ mem' regs' HCF MU2 WM2 RO2).
    - intros a Ha Hx. apply b3_notout4 in Hx. destruct Hx as [Hx|[Hx|[Hx|Hx]]].
      + right. right. exact (b3_xblk fx L A mem md text (LWv + 1) a M XT NT0 EB0 ltac:(clear - Hx; lia)).
      + right. right. exact (b3_xblk fx L A mem md copy (LWv + 1) a M XCo NC0 EB0 ltac:(clear - Hx; lia)).
      + right. right. exact (b3_xblk fx L A mem md arr (arr_size LWv) a M XA NA0 EB0 ltac:(clear - Hx; lia)).
      + left. exact Hx.
    - intros p1 n1 i Hin Hi Hx. pose proof (RecTail.user_in_blocks L A p1 n1 Hin) as Hb.
      destruct (b3_blk fx L A mem md _ _ M Hb ltac:(clear - Hi; lia)) as (P1 & P2 & _).
      assert (NI : ~ in_img B (ptr_addr L p1 + i))
        by exact (b3_noimg fx L A mem md _ _ (ptr_addr L p1 + i) M Hb ltac:(clear - Hi; lia)).
      apply (KindB.present_of_writable_out B SEGS mem' (ptr_addr L p1 + i) ltac:(clear - Hi P1 P2 AC; lia) NI).
      apply b3_notout4 in Hx. destruct Hx as [Hx|[Hx|[Hx|Hx]]].
      + exact (b3_wr_cb mem' text _ T (ptr_addr L p1 + i) TTm ltac:(clear - Hx LWR; lia)).
      + exact (b3_wr_cb mem' copy _ C (ptr_addr L p1 + i) CCm ltac:(clear - Hx LWR; lia)).
      + exact (b3_wr_cb mem' arr _ Aa (ptr_addr L p1 + i) AAm ltac:(clear - Hx ASZ; lia)).
      + exfalso. unfold SLOT_STACK in *. clear - Hx P2 Hi HS. lia.
    - exact FZ2.
    - rewrite GR. exact (eq_sym R2).
    - rewrite GR. reflexivity.
    - rewrite GR. reflexivity. }
  pose proof (SlotRec.words_count (Verbs.line (m_D p0 pl p n))) as HWC.
  pose proof (SlotRec.line_len (m_D p0 pl p n)) as HLL.
  pose proof (SlotItB2.b2_upto_len (m_D p0 pl p n)) as HUL.
  assert (AW8 : 8 * Z.of_nat (length (Verbs.words (Verbs.line (m_D p0 pl p n)))) <= arr_size LWv).
  { unfold arr_size. rewrite HU. clear - HWC HLL. Z.div_mod_to_equations. lia. }
  assert (NW31 : Z.of_nat (length (Verbs.words (Verbs.line (m_D p0 pl p n)))) < 2 ^ 31)
    by (clear - HWC HUL HDL HL1; lia).
  destruct (b3_wb mem' copy arr LWv (m_D p0 pl p n) C Aa wp CCm AAm ltac:(clear - LWR; lia) HU WPL WPF WPW) as [WB PB].
  destruct (b3_cb32 _ _ _ _ _ _ _ LC1m) as [jw' LCW].
  assert (U24 : bv_unsigned (reg_get regs 24) = n - hdr_n n).
  { change (reg_get regs 24) with (getr regs 24). rewrite L24. apply unsigned_lit. unfold hdr_n.
    clear - Hn Hp Hpn Hp04 Hpac AC. lia. }
  unfold stBW, hwords.
  exists (mkFP Ft fc2), L, A, regs', mem', md, O, R1, x, quit, text, copy, arr, (LWv + 1), (LWv + 1), (arr_size LWv), wp.
  split; [reflexivity|].
  split; [exact CF2|]. split; [exact HRC|]. split; [exact EVR|]. split; [exact DCL|]. split; [exact RS|].
  split; [exact RH|]. split; [exact RX2|].
  split; [exact D1|]. split; [exact D2|]. split; [exact D3|].
  split; [clear - LWR HL1; lia|]. split; [clear - LWR HL1; lia|]. split; [clear - ASZ; lia|].
  split.
  { unfold LR. split; [rewrite GR; reflexivity|]. split; [rewrite GR; reflexivity|].
    split; [rewrite GR; exact L22|]. split; [rewrite GR; exact L24|].
    split; [rewrite GR; reflexivity|]. split; [rewrite GR; reflexivity|]. exact (conj Hm (conj Hn (conj Hp Hpn))). }
  split; [rewrite GR; reflexivity|].
  split; [transitivity (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 FB) + 40)); [rewrite GR; reflexivity | rewrite USP; reflexivity]|].
  split; [rewrite GR; exact G18|]. split; [rewrite GR; exact G19|].
  split; [rewrite GR; reflexivity|]. split; [rewrite GR; reflexivity|]. split; [rewrite GR; reflexivity|].
  split; [transitivity (Z_to_bv 64 (bv_unsigned (reg_get regs 24) - m_len p0 pl p n)); [rewrite GR; reflexivity|];
          rewrite U24; reflexivity|].
  split; [exists jsv', jw'; split; [exact LC0m | exact LCW]|].
  split.
  { unfold words_view.
    split; [exact WPL|]. split; [exact NW31|].
    split.
    { apply (send_message.sm_le_of_bytes B mem' _ _ SEGS).
      exact (send_message.sm_cell_get2 rsegs mem' (FB + 40)
               [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr)]
               (C4 (Z_to_bv 64 (Z.of_nat (length (Verbs.words (Verbs.line (m_D p0 pl p n))))))) [CB 4 jp] 24%nat LC1m
               eq_refl). }
    split.
    { apply (send_message.sm_le_of_bytes B mem' _ _ SEGS).
      exact (send_message.sm_cell_get2 rsegs mem' (FB + 40) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy)]
               (C8 (Z_to_bv 64 arr)) [C4 (Z_to_bv 64 (Z.of_nat (length (Verbs.words (Verbs.line (m_D p0 pl p n))))));
               CB 4 jp] 16%nat LC1m eq_refl). }
    intros k Hk.
    destruct (nth_error wp k) as [pk|] eqn:Ep; [|apply nth_error_None in Ep; clear - Ep Hk WPL; lia].
    destruct (nth_error (Verbs.words (Verbs.line (m_D p0 pl p n))) k) as [wk|] eqn:Ew;
      [|apply nth_error_None in Ew; clear - Ew Hk; lia].
    rewrite (SlotItB2.b2_nth wp k pk 0 Ep), (SlotItB2.b2_nth _ k wk [] Ew).
    split; [apply (send_message.sm_le_of_bytes B mem' _ _ SEGS); exact (PB k pk Ep)|].
    split.
    - intros Hin. pose proof (nth_error_In _ _ Ew) as Hw.
      destruct (HarnessPropsProof.hwords_word _ wk Hw) as [_ Hb]. destruct (Hb _ Hin) as (_ & _ & H0).
      apply H0. reflexivity.
    - apply (send_message.sm_le_of_bytes B mem' _ _ SEGS). exact (WB k pk wk Ep Ew). }
  split.
  { unfold words_place, in_block. split.
    - exists arr, (arr_size LWv). split; [exact XA|]. split; clear - AW8; lia.
    - intros k Hk.
      destruct (nth_error wp k) as [pk|] eqn:Ep; [|apply nth_error_None in Ep; clear - Ep Hk WPL; lia].
      destruct (nth_error (Verbs.words (Verbs.line (m_D p0 pl p n))) k) as [wk|] eqn:Ew;
        [|apply nth_error_None in Ew; clear - Ew Hk; lia].
      rewrite (SlotItB2.b2_nth wp k pk 0 Ep), (SlotItB2.b2_nth _ k wk [] Ew).
      destruct (WPW k pk wk Ep Ew) as (P1 & P2 & _).
      exists copy, (LWv + 1). split; [exact XCo|]. split; clear - P1 P2; lia. }
  split.
  { exists arr, (arr_size LWv). split; [exact XA|]. split; [exact NAO|]. split; clear - AW8; lia. }
  split.
  { intros k Hk.
    destruct (nth_error wp k) as [pk|] eqn:Ep; [|apply nth_error_None in Ep; clear - Ep Hk WPL; lia].
    destruct (nth_error (Verbs.words (Verbs.line (m_D p0 pl p n))) k) as [wk|] eqn:Ew;
      [|apply nth_error_None in Ew; clear - Ew Hk; lia].
    rewrite (SlotItB2.b2_nth wp k pk 0 Ep), (SlotItB2.b2_nth _ k wk [] Ew).
    destruct (WPW k pk wk Ep Ew) as (P1 & P2 & _).
    exists copy, (LWv + 1). split; [exact XCo|]. split; [exact NCO|]. split; clear - P1 P2; lia. }
  split.
  { pose proof (SlotRec.words_acc_need (Verbs.line (m_D p0 pl p n)) []) as JN. unfold Verbs.words.
    cbn [length] in JN. clear - JN HUL HDL HL1. lia. }
  exact MP.
Qed.

Lemma ib2_seg_h : check_reply_contract -> check_arity_contract -> memcpy_contract -> strspn_contract -> strcspn_contract ->
  forall (m p n : Z) (R0 : rstate) (c : config),
  (r_refuse R0 <> 0 -> declared (r_code R0) = true) -> 0 <= r_state R0 < 2 ^ 64 -> 0 <= r_host R0 < 2 ^ 64 ->
  stB B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0 c ->
  SR rsegs c (stBW B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0).
Proof.
  intros CRC CAC MEMC SSPN SCSPN m p n R0 c DCL RS RH
    (fx & L & A & regs & mem & md & O & R1 & x & quit & text & copy & arr & jsv & jw & -> & HSB).
  pose proof HSB as (HCF & _).
  pose proof HCF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RO & _).
  destruct (it_model B API S rg mem0 md0 L0 A0 fx L A regs mem md HCF) as [Hh Hl].
  eapply (@sr_cj fx regs (Z_to_bv 64 0x141c8) mem md _ _ Hh Hl RO).
  { exact (b3_evt CRC CAC MEMC SSPN SCSPN fx L A regs mem md O R1 x quit text copy arr jsv jw m p n R0 HSB). }
  { intros s0 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m' & T & C &
      Aa & wp & jsv' & jp & -> & _).
    do 5 eexists. reflexivity. }
  intros R' F' pc' fc' m0' regs' mem' HQ REL ROS GR.
  apply SR_ret.
  exact (b3_post fx L A regs mem md O R1 x quit text copy arr jsv jw m p n R0 HSB DCL RS RH R' F' pc' fc' m0' regs' mem'
           HQ REL ROS GR).
Qed.

End B3.

(* HB2 of SlotItProof.v. *)
Lemma ib2_seg_h_closed : forall (rc : RunCeil) (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z) (S : Z) (rg : bvmap 5 word)
    (mem0 : word -> option byte) (md0 : Model) (L0 : layout) (A0 : astate) (p0 n0 : Z) (pl : list byte) (b : sbound),
  Slot.frame_given B API LS SH SK ra empty ->
  lib_pre_x (LS := LS) (SH := SH) (SK := SK) B (API rc) SLOT_STACK empty L0 A0 rg mem0 md0 ra p0 n0 pl b ->
  spZ rg = S ->
  check_reply_contract -> check_arity_contract -> memcpy_contract -> strspn_contract -> strcspn_contract ->
  forall (m p n : Z) (R0 : rstate) (c : config),
  (r_refuse R0 <> 0 -> declared (r_code R0) = true) -> 0 <= r_state R0 < 2 ^ 64 -> 0 <= r_host R0 < 2 ^ 64 ->
  stB B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0 c ->
  SR rsegs c (stBW B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0).
Proof.
  intros rc B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2.
  exact (@ib2_seg_h rc B API LS SH SK ra empty S rg mem0 md0 L0 A0 p0 n0 pl b FG PRE RG2).
Qed.
