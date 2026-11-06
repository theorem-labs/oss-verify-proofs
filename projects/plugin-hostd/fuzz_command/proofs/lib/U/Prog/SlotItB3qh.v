(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, addresses and numbers changed; 2641 of its 2742 lines of code are new or changed and 1015 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_host_setting.v, with its module paths changed; 599 of its 833 lines of code are new or changed and 2508 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/RecStubU.v, with its module paths and module names changed; 444 of its 497 lines of code are new or changed and 780 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/SlotItCK.v; 330 of its 390 lines of code are new or changed and 437 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes MState.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL0g YL01 YL00 YI14 YI16 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require KindBGlue BlocksNodup.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import AllocSI AllocGS.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU SlotSpec SlotGlue
  SlotRuns SlotCallees SlotIter SlotEnd SlotItBase SlotItSt verbs_receive_c send_message_c CommandB VerbsB CommandModel
  SlotItA SlotItE strnlen_c SlotItB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Slot SlotInv SlotRec RecTail RecAnsB SlotWords
  RecAns RecGlue.
Import ListNotations.
Local Open Scope Z_scope.

(* Helpers for the ubsan segment from the third malloc's return (stB, pc 0x14200) to check_words' entry (stBW, pc
   0x14bac): facts on the memory normalized to the task's addresses, the blocks of the message, and the reply, answer
   and call words of g_rec. *)

(* The read-only bytes of the ubsan image: 0x10000 .. 0x22000 (the segments of rsegs, by computation). *)
Fixpoint q3h_rof (l : list (Z * Z * bool)) (a : Z) : bool :=
  match l with
  | [] => false
  | (b, z, w) :: l' => if (b <=? a) && (a + 1 <=? b + z) then negb w else q3h_rof l' a
  end.

Lemma q3h_ro_addr_rof : forall segs a,
  ro_addr segs a = q3h_rof (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) segs) (bv_unsigned a).
Proof.
  intros segs a. unfold ro_addr. generalize (bv_unsigned a) as z.
  induction segs as [|sg segs IH]; intros z; [reflexivity|].
  cbn [find_segment map q3h_rof]. destruct (_ && _); [reflexivity | apply IH].
Qed.

Lemma q3h_ro_true : forall a, 0 <= a < 2 ^ 64 -> ro_addr rsegs (Z_to_bv 64 a) = true -> 0x10000 <= a < 0x22000.
Proof.
  intros a Ha. rewrite q3h_ro_addr_rof, unsigned_lit by lia.
  let l := eval vm_compute in (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) rsegs) in
  replace (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) rsegs) with l
    by (vm_compute; reflexivity).
  cbn [q3h_rof].
  repeat match goal with |- context [?u <=? ?v] => destruct (Z.leb_spec u v) end; cbn [andb negb];
    intros E; first [discriminate | lia].
Qed.

Lemma q3h_ro_false : forall a, 0 <= a < 2 ^ 64 -> ~ (0x10000 <= a < 0x22000) -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha N. destruct (ro_addr rsegs (Z_to_bv 64 a)) eqn:E; [|reflexivity].
  exfalso. apply N. exact (q3h_ro_true a Ha E).
Qed.

(* The normalized memory keeps every byte below TASK_SIZE outside the read-only range. *)
Lemma q3h_cj_eq : forall (m : word -> option byte) a, 0 <= a < TASK_SIZE -> ~ (0x10000 <= a < 0x22000) ->
  normalize_cj rsegs m (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros m a Ha Hr. unfold normalize_cj.
  rewrite (cj_drop_false_intro rsegs (Z_to_bv 64 a)); [reflexivity | apply q3h_ro_false |].
  - unfold TASK_SIZE in *. lia.
  - lia.
  - right. rewrite unsigned_lit by (unfold TASK_SIZE in *; lia). exact (proj2 Ha).
Qed.

Lemma q3h_cj_mbyte : forall (m : word -> option byte) a, 0 <= a < TASK_SIZE -> ~ (0x10000 <= a < 0x22000) ->
  mbyte rsegs (normalize_cj rsegs m) a = mbyte rsegs m a /\
  (writable_at rsegs m a <-> writable_at rsegs (normalize_cj rsegs m) a).
Proof.
  intros m a Ha Hr. pose proof (q3h_cj_eq m a Ha Hr) as E.
  unfold mbyte, writable_at, wview. rewrite E. split; [reflexivity | tauto].
Qed.

Lemma q3h_cj_cells : forall m a cs, rw_cells rsegs m a cs -> 0 <= a -> a + Z.of_nat (cells_size cs) <= TASK_SIZE ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ~ (0x10000 <= a + i < 0x22000)) ->
  rw_cells rsegs (normalize_cj rsegs m) a cs.
Proof.
  intros m a cs H H0 H1 H2. apply (KindB.rw_cells_transfer rsegs m); [exact H|].
  intros i Hi. destruct (q3h_cj_mbyte m (a + i) ltac:(lia) (H2 i Hi)) as [E W]. split; [exact E | tauto].
Qed.

Lemma q3h_cj_u8 : forall m a bs, u8arr rsegs m a bs -> a + Z.of_nat (length bs) <= TASK_SIZE ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> ~ (0x10000 <= a + i < 0x22000)) ->
  u8arr rsegs (normalize_cj rsegs m) a bs.
Proof.
  intros m a bs [Hb (W0 & W1 & W2)] H1 H2. split.
  - apply (KindB.bytes_at_transfer rsegs m); [exact Hb|]. intros i Hi.
    exact (proj1 (q3h_cj_mbyte m (a + i) ltac:(lia) (H2 i Hi))).
  - split; [exact W0|]. split; [exact W1|]. intros i Hi.
    exact (proj1 (proj2 (q3h_cj_mbyte m (a + i) ltac:(lia) (H2 i Hi))) (W2 i Hi)).
Qed.

(* k bytes from q, none in the image 0x10000 .. 0x55000 (SlotItA.it_blk_out): all below it or all above it. *)
Lemma q3h_img : forall q k, 0 < k -> (forall i, 0 <= i < k -> ~ (0x10000 <= q + i < 0x55000)) ->
  q + k <= 0x10000 \/ 0x55000 <= q.
Proof.
  intros q k Hk H. destruct (Z_lt_ge_dec q 0x10000) as [H1|H1].
  - left. destruct (Z_le_gt_dec (q + k) 0x10000) as [H2|H2]; [exact H2|].
    exfalso. apply (H (0x10000 - q)); lia.
  - right. destruct (Z_lt_ge_dec q 0x55000) as [H2|H2]; [|lia].
    exfalso. apply (H 0); lia.
Qed.

Lemma q3h_m8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.

Lemma q3h_r8_mono : forall c d, c <= d -> 8 * ((c + 7) / 8) <= 8 * ((d + 7) / 8).
Proof. intros c d H. pose proof (Z.div_le_mono (c + 7) (d + 7) 8 ltac:(lia) ltac:(lia)). lia. Qed.

Lemma q3h_slack_len : forall e s, s = 8 * ((e + 7) / 8) - e -> (- e) mod 8 <= s.
Proof. intros e s ->. Z.div_mod_to_equations. lia. Qed.

Lemma q3h_r8 : forall c t, c <= t -> t mod 8 = 0 -> 8 * ((c + 7) / 8) <= t.
Proof. intros c t H1 H2. Z.div_mod_to_equations. lia. Qed.

Lemma q3h_r8_ge : forall c, c <= 8 * ((c + 7) / 8).
Proof. intros c. Z.div_mod_to_equations. lia. Qed.

Lemma q3h_arr_bound : forall k nw L, (k < nw)%nat -> (2 * nw <= L + 1)%nat ->
  (8 * k + 8 <= Z.to_nat (8 * (Z.of_nat L / 2) + 16))%nat.
Proof. intros k nw L H1 H2. Z.div_mod_to_equations. lia. Qed.

Lemma q3h_out4 : forall t1 e1 t2 e2 t3 e3 t4 e4 a, (a < t1 \/ e1 <= a) -> (a < t2 \/ e2 <= a) ->
  (a < t3 \/ e3 <= a) -> (a < t4 \/ e4 <= a) -> Frame.outside [(t1, e1); (t2, e2); (t3, e3); (t4, e4)] a.
Proof. intros. cbn. refine (conj _ (conj _ (conj _ (conj _ Logic.I)))); lia. Qed.

Lemma q3h_notout4 : forall t1 e1 t2 e2 t3 e3 t4 e4 a, ~ Frame.outside [(t1, e1); (t2, e2); (t3, e3); (t4, e4)] a ->
  (t1 <= a < e1) \/ (t2 <= a < e2) \/ (t3 <= a < e3) \/ (t4 <= a < e4).
Proof.
  intros t1 e1 t2 e2 t3 e3 t4 e4 a H.
  destruct (Z_lt_ge_dec a t1); [|destruct (Z_lt_ge_dec a e1); [left; lia|]];
  (destruct (Z_lt_ge_dec a t2); [|destruct (Z_lt_ge_dec a e2); [right; left; lia|]]);
  (destruct (Z_lt_ge_dec a t3); [|destruct (Z_lt_ge_dec a e3); [right; right; left; lia|]]);
  (destruct (Z_lt_ge_dec a t4); [|destruct (Z_lt_ge_dec a e4); [right; right; right; lia|]]);
  exfalso; apply H; apply q3h_out4; lia.
Qed.

Lemma q3h_ne_O : forall (O : list (Z * Z)) p1 k1 t k, In (p1, k1) O -> ~ In t (map fst O) -> (p1, k1) <> (t, k).
Proof.
  intros O p1 k1 t k H N E. injection E as -> _. apply N. apply in_map_iff. exists (t, k1). split; [reflexivity | exact H].
Qed.

Lemma q3h_wr_cb : forall m q (k : nat) bs a, rw_cells rsegs m q [CB k bs] -> q <= a < q + Z.of_nat k ->
  writable_at rsegs m a.
Proof.
  intros m q k bs a [_ (W0 & W1 & W2)] Ha. replace a with (q + (a - q)) by ring. apply W2. cbn [cells_size csize]. lia.
Qed.

Lemma q3h_cb32 : forall m a t c ar nw jp, rw_cells rsegs m a [C8 t; C8 c; C8 ar; C4 nw; CB 4 jp] ->
  exists jw, rw_cells rsegs m a [CB 32 jw].
Proof.
  intros m a t c ar nw jp H. exists (cells_bytes [C8 t; C8 c; C8 ar; C4 nw; CB 4 jp]).
  apply (SlotItB.ib_cells_eq m a _ _ H); [| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity].
  assert (LB : length (cells_bytes [C8 t; C8 c; C8 ar; C4 nw; CB 4 jp]) = 32%nat).
  { destruct H as [[Hwf _] _]. rewrite (Cells.cells_bytes_length _ Hwf). reflexivity. }
  revert LB. generalize (cells_bytes [C8 t; C8 c; C8 ar; C4 nw; CB 4 jp]). intros bs LB. cbn. tauto.
Qed.

Lemma q3h_cells_bytes : forall m a cs, rw_cells rsegs m a cs -> bytes_at rsegs m a (cells_bytes cs).
Proof. intros m a cs [[_ H] _]. exact H. Qed.

Lemma q3h_le8_nth : forall (wp : list Z) k p, nth_error wp k = Some p ->
  firstn 8 (skipn (8 * k) (concat (map (fun q => le8 (Z_to_bv 64 q)) wp))) = le8 (Z_to_bv 64 p).
Proof.
  induction wp as [|q wp IH]; intros [|k] p H; cbn in H; try discriminate.
  - injection H as <-. cbn [map concat]. rewrite Nat.mul_0_r, skipn_O, firstn_app, length_le8, Nat.sub_diag, firstn_O,
      app_nil_r. apply firstn_all2. rewrite length_le8. lia.
  - cbn [map concat]. replace (8 * S k)%nat with (8 + 8 * k)%nat by lia.
    rewrite skipn_app, length_le8, skipn_all2 by (rewrite length_le8; lia).
    replace (8 + 8 * k - 8)%nat with (8 * k)%nat by lia. cbn [app]. exact (IH k p H).
Qed.

Lemma q3h_firstn_ptr : forall (Aa : list byte) (wp : list Z) k p,
  firstn (8 * length wp) Aa = concat (map (fun q => le8 (Z_to_bv 64 q)) wp) -> nth_error wp k = Some p ->
  firstn 8 (skipn (8 * k) Aa) = le8 (Z_to_bv 64 p).
Proof.
  intros Aa wp k p H E. assert (Hk : (k < length wp)%nat) by (apply nth_error_Some; rewrite E; discriminate).
  rewrite <- (q3h_le8_nth wp k p E), <- H. rewrite !firstn_skipn_comm, firstn_firstn.
  replace (Init.Nat.min (8 * k + 8) (8 * length wp)) with (8 * k + 8)%nat by lia. reflexivity.
Qed.

Lemma q3h_sub : forall m a (C X : list byte) k, bytes_at rsegs m a C -> (k + length X <= length C)%nat ->
  firstn (length X) (skipn k C) = X -> bytes_at rsegs m (a + Z.of_nat k) X.
Proof.
  intros m a C X k H Hl E.
  pose proof (RecAns.bytes_at_firstn_skipn rsegs m a C k H) as [_ H2]. rewrite length_firstn in H2.
  replace (Init.Nat.min k (length C)) with k in H2 by lia.
  pose proof (RecAns.bytes_at_firstn_skipn rsegs m (a + Z.of_nat k) (skipn k C) (length X) H2) as [H3 _].
  rewrite E in H3. exact H3.
Qed.

(* The words of the line in copy and their addresses in arr. *)
Lemma q3h_wb : forall m copy arr L0w (M : list byte) C Aa wp,
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
  { pose proof (q3h_cells_bytes _ _ _ CC) as Hb. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (LCC : length C = Z.to_nat (L0w + 1)) by (destruct CC as [[[H _] _] _]; exact H).
  assert (AB1 : bytes_at rsegs m arr Aa).
  { pose proof (q3h_cells_bytes _ _ _ AA) as Hb. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (LAA : length Aa = Z.to_nat (arr_size L0w)) by (destruct AA as [[[H _] _] _]; exact H).
  split.
  - intros k p w Ep Ew. destruct (WPW k p w Ep Ew) as (P1 & P2 & P3).
    replace p with (copy + Z.of_nat (Z.to_nat (p - copy))) by (clear - P1; lia).
    apply (q3h_sub m copy C _ _ CB1); [rewrite length_app; cbn [length]; clear - P1 P2 LCC HL; lia|].
    rewrite length_app. cbn [length]. exact P3.
  - intros k p Ep. assert (Hk : (k < length wp)%nat) by (apply nth_error_Some; rewrite Ep; discriminate).
    replace (8 * Z.of_nat k) with (Z.of_nat (8 * k)) by lia.
    apply (q3h_sub m arr Aa _ _ AB1).
    + rewrite length_le8, LAA. rewrite WPL in Hk. pose proof (SlotRec.words_count (Verbs.line M)) as HWC.
      pose proof (SlotRec.line_len M) as HLL. unfold arr_size. rewrite HU.
      apply (q3h_arr_bound k (length (Verbs.words (Verbs.line M))) _ Hk). clear - HWC HLL. lia.
    + rewrite length_le8. exact (q3h_firstn_ptr Aa wp k p ltac:(rewrite WPL; exact WPF) Ep).
Qed.

Section Q3H.
Context {rc : RunCeil}.
Variables (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head)
  (SK : sink_syms) (ra empty : Z) (S : Z) (rg : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
  (L0 : layout) (A0 : astate) (p0 n0 : Z) (pl : list byte) (b : sbound).
Hypothesis FG : Slot.frame_given_u B API LS SH SK ra empty.
Hypothesis PRE : lib_pre_x (LS := LS) (SH := SH) (SK := SK) B (API rc) SLOT_STACK empty L0 A0 rg mem0 md0 ra p0 n0 pl b.
Hypothesis RG2 : spZ rg = S.

Notation CF := (SlotInv.CF B (API rc) S rg mem0 md0 L0 A0).
Notation FB := (SlotInv.FB S).

(* stB's facts for its witnesses (SlotItB.stB without the configuration). *)
Definition q3h_SB (fx : FPState) L A regs mem md O R1 x quit (text copy arr : Z) (jw : list byte) (m p n : Z)
    (R0 : rstate) : Prop :=
  CF fx L A regs mem md /\ SlotInv.rcap A /\
  vr_run (rec_clear R0) (m_D p0 pl p n) = (R1, x, quit) /\
  RFX L0 A0 L A mem R1 O (qv quit)
    [(text, LW p0 pl p n + 1); (copy, LW p0 pl p n + 1); (arr, arr_size (LW p0 pl p n))] /\
  text <> copy /\ text <> arr /\ copy <> arr /\ text mod 16 = 0 /\ copy mod 16 = 0 /\ arr mod 16 = 0 /\
  LR p0 n0 pl m p n regs mem /\
  getr regs 10 = Z_to_bv 64 arr /\ getr regs 18 = Z_to_bv 64 (r_state R0) /\
  getr regs 19 = Z_to_bv 64 (r_host R0) /\ getr regs 20 = Z_to_bv 64 (LW p0 pl p n) /\
  getr regs 21 = Z_to_bv 64 (LW p0 pl p n + 1) /\
  rw_cells rsegs mem FB (LOC1 (n - hdr_n n)) /\
  rw_cells rsegs mem (FB + 24) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); CB 16 jw] /\
  msg_props R0 (m_D p0 pl p n) /\
  (r_refuse R0 <> 0 -> declared (r_code R0) = true) /\ 0 <= r_state R0 < 2 ^ 64 /\ 0 <= r_host R0 < 2 ^ 64.

Lemma q3h_stB : forall m p n R0 c, stB B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0 c ->
  exists (fx : FPState) L A regs mem md O R1 x quit text copy arr jw,
    c = mkCfg (@mkst fx regs (Z_to_bv 64 0x14200) mem (seg_rom rsegs)) md /\
    q3h_SB fx L A regs mem md O R1 x quit text copy arr jw m p n R0.
Proof.
  intros m p n R0 c (fx & L & A & regs & mem & md & O & R1 & x & quit & text & copy & arr & jw & E & H).
  exists fx, L, A, regs, mem, md, O, R1, x, quit, text, copy, arr, jw. split; [exact E | exact H].
Qed.

Lemma q3h_disj : forall (fx : FPState) L A mem md q1 k1 q2 k2, aa_MR (API rc) L A mem md ->
  In (q1, k1) (blocks L A) -> In (q2, k2) (blocks L A) -> (q1, k1) <> (q2, k2) -> q1 + k1 <= q2 \/ q2 + k2 <= q1.
Proof.
  intros fx L A mem md q1 k1 q2 k2 HM H1 H2 Ne.
  destruct (YI04.pairwise_in2 _ _ _ _ (mr_blocks_disjoint B _ (aa_laws (API rc)) L A mem md HM) H1 H2 Ne) as [D|D];
    unfold ranges_disjoint in D; cbn in D; lia.
Qed.

Lemma q3h_blk : forall (fx : FPState) L A mem md q k, aa_MR (API rc) L A mem md -> In (q, k) (blocks L A) -> 0 < k ->
  4096 <= q /\ q + k <= alloc_ceiling /\ (q + k <= 0x10000 \/ 0x55000 <= q).
Proof.
  intros fx L A mem md q k HM Hin Hk.
  destruct (it_blk_out B API LS SH SK ra empty FG fx L A mem md q k 0 HM Hin ltac:(lia)) as (_ & H1 & H2).
  split; [exact H1|]. split; [exact H2|].
  apply q3h_img; [exact Hk|]. intros i Hi.
  exact (proj1 (it_blk_out B API LS SH SK ra empty FG fx L A mem md q k i HM Hin Hi)).
Qed.

Lemma q3h_noimg : forall (fx : FPState) L A mem md q k a, aa_MR (API rc) L A mem md -> In (q, k) (blocks L A) ->
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
Lemma q3h_xblk : forall (fx : FPState) L A mem md q k a, aa_MR (API rc) L A mem md -> In (q, k) (blocks L A) ->
  ~ In (q, k) (blocks L0 A0) -> (forall a0 k0, In (a0, k0) (blocks L0 A0) -> In (a0, k0) (blocks L A)) ->
  q <= a < q + k ->
  a < alloc_ceiling /\ ~ in_img B a /\ ~ owned B L A a /\
  (forall a0 k0, In (a0, k0) (blocks L0 A0) -> ~ (a0 <= a < a0 + k0)).
Proof.
  intros fx L A mem md q k a HM Hin N0 E0 Ha.
  destruct (KindB.block_facts B _ (aa_laws (API rc)) L A mem md q k (a - q) HM Hin ltac:(lia)) as (_ & Q1 & Q2 & Q3).
  replace (q + (a - q)) with a in Q3 by ring.
  split; [lia|]. split; [exact (q3h_noimg fx L A mem md q k a HM Hin Ha)|]. split; [exact Q3|].
  intros a0 k0 H0 Hx.
  assert (Ne : (a0, k0) <> (q, k)) by (intros E; rewrite E in H0; exact (N0 H0)).
  destruct (q3h_disj fx L A mem md a0 k0 q k HM (E0 a0 k0 H0) Hin Ne); lia.
Qed.

(* The bytes of a live block, writable, on the normalized memory. *)
Lemma q3h_u8 : forall (fx : FPState) L A mem md q k, aa_MR (API rc) L A mem md -> In (q, k) (blocks L A) -> 0 < k ->
  exists bs, u8arr rsegs (normalize_cj rsegs mem) q bs /\ length bs = Z.to_nat k.
Proof.
  intros fx L A mem md q k HM Hin Hk.
  destruct (q3h_blk fx L A mem md q k HM Hin Hk) as (Q1 & Q2 & Q3).
  pose proof alloc_ceiling_val as AC.
  assert (PR : forall i, 0 <= i < Z.of_nat (Z.to_nat k) -> present mem (q + i)).
  { intros i Hi. exact (proj1 (KindB.block_facts B _ (aa_laws (API rc)) L A mem md q k i HM Hin ltac:(lia))). }
  destruct (KindB.present_rw_cells rsegs mem q (Z.to_nat k) ltac:(lia) ltac:(lia) PR) as [junk [[Hwf Hb] Hw]].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  assert (Lj : length junk = Z.to_nat k) by (cbn in Hwf; tauto).
  exists junk. split; [|exact Lj].
  apply q3h_cj_u8.
  - split; [exact Hb|].
    replace (Z.of_nat (length junk)) with (Z.of_nat (cells_size [CB (Z.to_nat k) junk])) by (cbn [cells_size csize]; lia).
    exact Hw.
  - rewrite Lj. unfold TASK_SIZE. lia.
  - intros i Hi. rewrite Lj in Hi. lia.
Qed.

(* The reply: its block, its bytes x with the slack up to the 8-byte end, apart from the message's blocks. *)
Lemma q3h_rep : forall (fx : FPState) L A mem md R O text copy arr kt kc ka x lo,
  aa_MR (API rc) L A mem md -> g_rec_rep rsegs L A mem R O ->
  In (text, kt) (blocks L A) -> ~ In text (map fst O) -> In (copy, kc) (blocks L A) -> ~ In copy (map fst O) ->
  In (arr, ka) (blocks L A) -> ~ In arr (map fst O) ->
  text mod 8 = 0 -> copy mod 8 = 0 -> arr mod 8 = 0 -> lo mod 8 = 0 -> alloc_ceiling <= lo ->
  r_reply R = Some (x ++ [Z_to_bv 8 0]) ->
  exists rep slack,
    bytes_at rsegs mem (CommandModel.G_REC + REC_REPLY) (le8 rep) /\
    bytes_at rsegs mem (CommandModel.G_REC + REC_REPLY_SIZE) (le8 (Z_to_bv 64 (Z.of_nat (length x) + 1))) /\
    bv_unsigned rep <> 0 /\ bytes_at rsegs mem (bv_unsigned rep) (x ++ NUL :: slack) /\
    (- (bv_unsigned rep + Z.of_nat (length x) + 1)) mod 8 <= Z.of_nat (length slack) /\
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
  destruct (q3h_blk fx L A mem md pr pk HM Hpb ltac:(lia)) as (P1 & P2 & _).
  assert (DT := q3h_disj fx L A mem md pr pk text kt HM Hpb XT (q3h_ne_O O pr pk text kt PO NTO)).
  assert (DC := q3h_disj fx L A mem md pr pk copy kc HM Hpb XC (q3h_ne_O O pr pk copy kc PO NCO)).
  assert (DA := q3h_disj fx L A mem md pr pk arr ka HM Hpb XA (q3h_ne_O O pr pk arr ka PO NAO)).
  pose proof (q3h_r8_mono (pr + (Z.of_nat (length x) + 1)) (pr + pk) ltac:(lia)) as RM.
  pose proof (q3h_r8_ge (pr + pk)) as RG.
  assert (RT : pr + pk <= text -> 8 * ((pr + pk + 7) / 8) <= text) by (intros H; apply q3h_r8; assumption).
  assert (RC : pr + pk <= copy -> 8 * ((pr + pk + 7) / 8) <= copy) by (intros H; apply q3h_r8; assumption).
  assert (RA' : pr + pk <= arr -> 8 * ((pr + pk + 7) / 8) <= arr) by (intros H; apply q3h_r8; assumption).
  assert (RL : 8 * ((pr + pk + 7) / 8) <= lo) by (apply q3h_r8; [lia | exact L8]).
  destruct (RecGlue.slack_bytes rsegs mem pr (Z.of_nat (length x) + 1) (x ++ [Z_to_bv 8 0]) RXB
              ltac:(rewrite length_app; cbn [length]; lia) ltac:(lia) ltac:(lia)) as (slack & SBy & SL).
  { intros a Ha. destruct (Z_lt_ge_dec a (pr + pk)) as [Hl|Hg].
    - replace a with (pr + (a - pr)) by ring.
      exact (proj1 (KindB.block_facts B _ (aa_laws (API rc)) L A mem md pr pk (a - pr) HM Hpb ltac:(lia))).
    - apply (SLACK L A mem md pr pk a HM Hpb). lia. }
  exists (Z_to_bv 64 pr), slack. rewrite unsigned_lit by lia.
  split; [exact RW|]. split; [exact RS|]. split; [exact Hpr0|].
  split; [rewrite <- app_assoc in SBy; exact SBy|].
  split; [apply q3h_slack_len; lia|].
  intros i Hi. lia.
Qed.

(* The answer word and, when it is not 0, the answer's bytes apart from the message's blocks. *)
Lemma q3h_ans : forall (fx : FPState) L A mem md R O text copy arr kt kc ka lo,
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
    destruct (q3h_blk fx L A mem md pa ka' HM Hpb ltac:(lia)) as (P1 & P2 & _).
    assert (DT := q3h_disj fx L A mem md pa ka' text kt HM Hpb XT (q3h_ne_O O pa ka' text kt PO NTO)).
    assert (DC := q3h_disj fx L A mem md pa ka' copy kc HM Hpb XC (q3h_ne_O O pa ka' copy kc PO NCO)).
    assert (DA := q3h_disj fx L A mem md pa ka' arr ka HM Hpb XA (q3h_ne_O O pa ka' arr ka PO NAO)).
    exists (Z_to_bv 64 pa), t. rewrite unsigned_lit by (pose proof alloc_ceiling_val; lia).
    split; [exact AW|]. split; [|intros H; contradiction].
    intros _. split; [reflexivity|]. split; [split; [exact AXB | exact AN]|].
    intros i Hi. lia.
  - exists (Z_to_bv 64 0), []. split; [exact HA|]. rewrite unsigned_lit by lia.
    split; [intros H; contradiction | intros _; reflexivity].
Qed.

(* g_rec.ncalls and the first call's fn. *)
Lemma q3h_calls : forall L A mem R O, g_rec_rep rsegs L A mem R O ->
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
  replace (RecInvU.G_REC + 16 + 56 * Z.of_nat 0 + 0) with (CommandModel.G_REC + 16 + 0) in H4
    by (unfold RecInvU.G_REC, CommandModel.G_REC; lia).
  exact H4.
Qed.

End Q3H.
