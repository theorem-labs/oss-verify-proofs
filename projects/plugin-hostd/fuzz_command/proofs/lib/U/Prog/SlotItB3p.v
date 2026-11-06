(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, addresses and numbers changed; 2641 of its 2742 lines of code are new or changed and 1015 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_host_setting.v, with its module paths changed; 599 of its 833 lines of code are new or changed and 2508 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/RecStubU.v, with its module paths and module names changed; 444 of its 497 lines of code are new or changed and 780 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/SlotItCK.v; 330 of its 390 lines of code are new or changed and 437 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/SlotItB3qh.v; 223 of its 354 lines of code are new or changed and 259 lines of the source are left out. *)
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
  SlotRuns SlotCallees SlotIter SlotEnd SlotItBase SlotItSt verbs_receive_c send_message_c CommandB VerbsB
  CommandModel SlotItA SlotItE SlotItB SlotItBW joined_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Slot SlotInv SlotRec RecTail RecAnsB SlotWords
  RecAns SlotItCK0 SlotItCK send_message.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require HarnessPropsProof.
Import ListNotations.
Local Open Scope Z_scope.

(* The end of the ubsan splitter, check_reply and check_arity run (SlotItCK0.w_post on the memory normalized to the
   task's addresses, after SlotItBase.sr_cj) back to the real memory: stBW (pc 0x14bac). *)

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

(* The struct words: the count and its 4 slack bytes as one 8-byte cell. *)
Lemma b3_cb8 : forall m a t c ar nw jp, rw_cells rsegs m a [C8 t; C8 c; C8 ar; C4 nw; CB 4 jp] ->
  rw_cells rsegs m a [C8 t; C8 c; C8 ar; CB 8 (Mem.le4 nw ++ jp)].
Proof.
  intros m a t c ar nw jp H.
  assert (LB : length (Mem.le4 nw ++ jp) = 8%nat).
  { destruct H as [[Hwf _] _]. cbn in Hwf. rewrite length_app, Mem.length_le4. intuition lia. }
  apply (SlotItB.ib_cells_eq m a _ _ H).
  - revert LB. generalize (Mem.le4 nw ++ jp). intros bs LB. cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

(* The locals at sp: LOC0 of the stored count's bytes is LOC1 of the count. *)
Lemma b3_loc1 : forall m a k, rw_cells rsegs m a (LOC0 (Mem.le8 (Z_to_bv 64 k))) -> rw_cells rsegs m a (LOC1 k).
Proof.
  intros m a k H. apply (SlotItB.ib_cells_eq m a _ _ H).
  - unfold LOC1. cbn. tauto.
  - unfold LOC0, LOC1. cbn [cells_bytes cbytes]. reflexivity.
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
  { pose proof (SlotItCK.ck_cells_bytes _ _ _ CC) as Hb. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (LCC : length C = Z.to_nat (L0w + 1)) by (destruct CC as [[[H _] _] _]; exact H).
  assert (AB1 : bytes_at rsegs m arr Aa).
  { pose proof (SlotItCK.ck_cells_bytes _ _ _ AA) as Hb. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (LAA : length Aa = Z.to_nat (arr_size L0w)) by (destruct AA as [[[H _] _] _]; exact H).
  split.
  - intros k p w Ep Ew. destruct (WPW k p w Ep Ew) as (P1 & P2 & P3).
    replace p with (copy + Z.of_nat (Z.to_nat (p - copy))) by (clear - P1; lia).
    apply (SlotItCK.ck_sub m copy C _ _ CB1); [rewrite length_app; cbn [length]; clear - P1 P2 LCC HL; lia|].
    rewrite length_app. cbn [length]. exact P3.
  - intros k p Ep. assert (Hk : (k < length wp)%nat) by (apply nth_error_Some; rewrite Ep; discriminate).
    replace (8 * Z.of_nat k) with (Z.of_nat (8 * k)) by lia.
    apply (SlotItCK.ck_sub m arr Aa _ _ AB1).
    + rewrite length_le8, LAA. rewrite WPL in Hk. pose proof (SlotRec.words_count (Verbs.line M)) as HWC.
      pose proof (SlotRec.line_len M) as HLL. unfold arr_size. rewrite HU.
      apply (SlotItCK.ck_arr_bound k (length (Verbs.words (Verbs.line M))) _ Hk). clear - HWC HLL. lia.
    + rewrite length_le8. exact (SlotItCK.ck_firstn_ptr Aa wp k p ltac:(rewrite WPL; exact WPF) Ep).
Qed.

Section B3.
Context {rc : RunCeil}.
Variables (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head)
  (SK : sink_syms) (ra empty : Z) (S : Z) (rg : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
  (L0 : layout) (A0 : astate) (p0 n0 : Z) (pl : list byte) (b : sbound).
Hypothesis FG : Slot.frame_given_u B API LS SH SK ra empty.
Hypothesis PRE : lib_pre_x (LS := LS) (SH := SH) (SK := SK) B (API rc) SLOT_STACK empty L0 A0 rg mem0 md0 ra p0 n0 pl b.
Hypothesis RG2 : spZ rg = S.

Notation CF := (SlotInv.CF B (API rc) S rg mem0 md0 L0 A0).
Notation FB := (SlotInv.FB S).

(* stB's facts for its witnesses (the conjunction after the configuration in SlotItB.stB). *)
Definition SB (fx : FPState) L A regs mem md O R1 x quit (text copy arr : Z) (jw : list byte) (m p n : Z)
    (R0 : rstate) : Prop :=
  CF fx L A regs mem md /\ SlotInv.rcap A /\
  vr_run (rec_clear R0) (m_D p0 pl p n) = (R1, x, quit) /\
  RFX L0 A0 L A mem R1 O (qv quit)
    [(text, strnlen_res (m_len p0 pl p n) (m_D p0 pl p n) + 1); (copy, strnlen_res (m_len p0 pl p n) (m_D p0 pl p n) + 1);
     (arr, arr_size (strnlen_res (m_len p0 pl p n) (m_D p0 pl p n)))] /\
  text <> copy /\ text <> arr /\ copy <> arr /\ text mod 16 = 0 /\ copy mod 16 = 0 /\ arr mod 16 = 0 /\
  LR p0 n0 pl m p n regs mem /\
  getr regs 10 = Z_to_bv 64 arr /\ getr regs 18 = Z_to_bv 64 (r_state R0) /\
  getr regs 19 = Z_to_bv 64 (r_host R0) /\ getr regs 20 = Z_to_bv 64 (strnlen_res (m_len p0 pl p n) (m_D p0 pl p n)) /\
  getr regs 21 = Z_to_bv 64 (strnlen_res (m_len p0 pl p n) (m_D p0 pl p n) + 1) /\
  rw_cells rsegs mem FB (LOC1 (n - hdr_n n)) /\
  rw_cells rsegs mem (FB + 24) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); CB 16 jw] /\
  msg_props R0 (m_D p0 pl p n) /\
  (r_refuse R0 <> 0 -> declared (r_code R0) = true) /\ 0 <= r_state R0 < 2 ^ 64 /\ 0 <= r_host R0 < 2 ^ 64.

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

(* From the run's end (w_post on the normalized memory) back to the real memory: stBW. *)
Lemma b3_post_u : forall fx L A regs mem md O R1 x quit text copy arr jw m p n R0,
  SB fx L A regs mem md O R1 x quit text copy arr jw m p n R0 ->
  (r_refuse R0 <> 0 -> declared (r_code R0) = true) -> 0 <= r_state R0 < 2 ^ 64 -> 0 <= r_host R0 < 2 ^ 64 ->
  forall R' F' pc' fc' m0' regs' mem',
  SlotItCK0.w_post (Z_to_bv 64 FB) (reg_get regs 3) (reg_get regs 4) (reg_get regs 18) (reg_get regs 19)
      (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 26) (normalize_cj rsegs mem) (S - SLOT_STACK)
      (m_src p n) (m_len p0 pl p n) text copy arr (m_D p0 pl p n) (Mem.le8 (Z_to_bv 64 (n - hdr_n n)))
      (MS R' F' pc' fc' None m0' (seg_rom rsegs)) ->
  mem_rel_cj rsegs mem' m0' -> cj_same rsegs mem mem' -> (forall r, getr regs' r = getr R' r) ->
  stBW B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0 (mkCfg (@mkst (mkFP F' fc') regs' pc' mem' (seg_rom rsegs)) md).
Proof.
  intros fx L A regs mem md O R1 x quit text copy arr jw m p n R0
    (HCF & HRC & EVR & HRX & D1 & D2 & D3 & T16 & C16 & A16 & HLR & G10 & G18 & G19 & G20 & G21 & LC0 & LC1 & MP & _)
    DCL RS RH R' F' pc' fc' m0' regs' mem'
    (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s4' & t3' & t4' & t5' & t6' & Ft & fc2 & m' & T & C & Aa &
     wp & jp & E & MU & WM & MI & FZ2 & LC0' & LC1' & TT & CC & AA & WPL & WPF & WPW) REL ROS GR.
  injection E as ER EF Epc Efc Em. subst R' F' pc' fc' m0'.
  pose proof HCF as (M & Wf & Bd & I & (vm & Hmd) & R2 & R3 & R4 & SV & SW & SF & RO & GIm & EB & FZ).
  pose proof HRX as (REP & SPILL & QB & Hq & ENO & BLK & XC & HOL).
  pose proof HLR as (L8 & L9 & L23 & L22 & L26 & L24 & L25 & L27 & Hm & Hn & Hp & Hpn).
  pose proof (b3_m8 _ A16) as A8.
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
                                (S - SLOT_STACK, FB + 56)] a) by (apply b3_out4; clear - H1 H2 H3 H4; lia).
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
  pose proof (SlotItCK.ck_upto_len (m_D p0 pl p n)) as HUL.
  assert (AW8 : 8 * Z.of_nat (length (Verbs.words (Verbs.line (m_D p0 pl p n)))) <= arr_size LWv).
  { unfold arr_size. rewrite HU. clear - HWC HLL. Z.div_mod_to_equations. lia. }
  assert (NW31 : Z.of_nat (length (Verbs.words (Verbs.line (m_D p0 pl p n)))) < 2 ^ 31)
    by (clear - HWC HUL HDL HL1; lia).
  destruct (b3_wb mem' copy arr LWv (m_D p0 pl p n) C Aa wp CCm AAm ltac:(clear - LWR; lia) HU WPL WPF WPW) as [WB PB].
  pose proof (b3_cb8 _ _ _ _ _ _ _ LC1m) as LCW.
  pose proof (b3_loc1 _ _ _ LC0m) as LCL.
  unfold stBW, hwords.
  exists (mkFP Ft fc2), L, A, regs', mem', md, O, R1, x, quit, text, copy, arr, (LWv + 1), (LWv + 1), (arr_size LWv), wp,
    (Mem.le4 (Z_to_bv 64 (Z.of_nat (length (Verbs.words (Verbs.line (m_D p0 pl p n)))))) ++ jp).
  split; [reflexivity|].
  split; [exact CF2|]. split; [exact HRC|]. split; [exact EVR|]. split; [exact DCL|]. split; [exact RS|].
  split; [exact RH|]. split; [exact RX2|].
  split; [exact D1|]. split; [exact D2|]. split; [exact D3|].
  split; [clear - LWR HL1; lia|]. split; [clear - LWR HL1; lia|]. split; [clear - ASZ; lia|].
  split; [exact A8|].
  split.
  { unfold LR. split; [rewrite GR; reflexivity|]. split; [rewrite GR; reflexivity|].
    split; [rewrite GR; exact L23|]. split; [rewrite GR; exact L22|]. split; [rewrite GR; exact L26|].
    split; [rewrite GR; reflexivity|]. split; [rewrite GR; reflexivity|]. split; [rewrite GR; reflexivity|].
    exact (conj Hm (conj Hn (conj Hp Hpn))). }
  split; [rewrite GR; reflexivity|].
  split; [transitivity (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 FB) + 24)); [rewrite GR; reflexivity | rewrite USP; reflexivity]|].
  split; [rewrite GR; exact G18|]. split; [rewrite GR; exact G19|].
  split; [exact LCL|]. split; [exact LCW|].
  split.
  { unfold words_view.
    split; [exact WPL|]. split; [exact NW31|].
    split.
    { apply (send_message.sm_le_of_bytes B mem' _ _ SEGS).
      exact (send_message.sm_cell_get2 rsegs mem' (FB + 24)
               [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr)]
               (C4 (Z_to_bv 64 (Z.of_nat (length (Verbs.words (Verbs.line (m_D p0 pl p n))))))) [CB 4 jp] 24%nat LC1m
               eq_refl). }
    split.
    { apply (send_message.sm_le_of_bytes B mem' _ _ SEGS).
      exact (send_message.sm_cell_get2 rsegs mem' (FB + 24) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy)]
               (C8 (Z_to_bv 64 arr)) [C4 (Z_to_bv 64 (Z.of_nat (length (Verbs.words (Verbs.line (m_D p0 pl p n))))));
               CB 4 jp] 16%nat LC1m eq_refl). }
    intros k Hk.
    destruct (nth_error wp k) as [pk|] eqn:Ep; [|apply nth_error_None in Ep; clear - Ep Hk WPL; lia].
    destruct (nth_error (Verbs.words (Verbs.line (m_D p0 pl p n))) k) as [wk|] eqn:Ew;
      [|apply nth_error_None in Ew; clear - Ew Hk; lia].
    rewrite (SlotItCK.ck_nth wp k pk 0 Ep), (SlotItCK.ck_nth _ k wk [] Ew).
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
      rewrite (SlotItCK.ck_nth wp k pk 0 Ep), (SlotItCK.ck_nth _ k wk [] Ew).
      destruct (WPW k pk wk Ep Ew) as (P1 & P2 & _).
      exists copy, (LWv + 1). split; [exact XCo|]. split; clear - P1 P2; lia. }
  split.
  { exists arr, (arr_size LWv). split; [exact XA|]. split; [exact NAO|]. split; clear - AW8; lia. }
  split.
  { intros k Hk.
    destruct (nth_error wp k) as [pk|] eqn:Ep; [|apply nth_error_None in Ep; clear - Ep Hk WPL; lia].
    destruct (nth_error (Verbs.words (Verbs.line (m_D p0 pl p n))) k) as [wk|] eqn:Ew;
      [|apply nth_error_None in Ew; clear - Ew Hk; lia].
    rewrite (SlotItCK.ck_nth wp k pk 0 Ep), (SlotItCK.ck_nth _ k wk [] Ew).
    destruct (WPW k pk wk Ep Ew) as (P1 & P2 & _).
    exists copy, (LWv + 1). split; [exact XCo|]. split; [exact NCO|]. split; clear - P1 P2; lia. }
  split.
  { pose proof (SlotRec.words_acc_need (Verbs.line (m_D p0 pl p n)) []) as JN. unfold Verbs.words.
    cbn [length] in JN. clear - JN HUL HDL HL1. lia. }
  exact MP.
Qed.

End B3.
