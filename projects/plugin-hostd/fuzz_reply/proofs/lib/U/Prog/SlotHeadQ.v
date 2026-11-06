(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 613 of its 658 lines of code are new or changed and 1184 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/SlotPass9G.v, with its module paths changed; 303 of its 406 lines of code are new or changed and 555 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep HarnessRep ListRep CheckRep drain_b_c source_reset_c op_add_c check_bounded_c SlotInv SlotSteps SlotHead SlotHeadP SlotRes KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotHeadRun SlotHeadPick.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import Image.
Import ListNotations.
Local Open Scope Z_scope.

Definition short_key (q : Z * list byte * list byte) : Z * list byte * list byte :=
  (fst q, firstn 7 (snd q)).
Definition short_entry (e : rentry) : rentry :=
  RE (re_fd e) (re_eof e) (re_skip e) (re_pad1 e) (re_buf e) (re_used e) (re_cap e)
     (re_hp e) (re_kh e) (re_pad2 e) (map short_key (re_keys e)) (re_U e) (re_junk e).

Lemma short_keys_addr : forall ks, map key_addr (map short_key ks) = map key_addr ks.
Proof. intros ks. rewrite map_map. reflexivity. Qed.
Lemma short_keys_text : forall ks, map key_text (map short_key ks) = map key_text ks.
Proof. intros ks. rewrite map_map. reflexivity. Qed.
Lemma short_keys_texts : forall ks, keys_texts (map short_key ks) = keys_texts ks.
Proof. intros ks. unfold keys_texts. rewrite map_map. reflexivity. Qed.
Lemma short_keys_ptrs : forall ks, key_ptrs (map short_key ks) = key_ptrs ks.
Proof. intros ks. unfold key_ptrs. rewrite map_map. reflexivity. Qed.
Lemma slot_key_ptrs_length : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|q ks IH]; [reflexivity|].
  change (length (le8 (Z_to_bv 64 (key_addr q)) ++ key_ptrs ks) = (8 * S (length ks))%nat).
  rewrite length_app, length_le8, IH. lia.
Qed.
Lemma short_keys_total : forall ks, keys_total (map short_key ks) = keys_total ks.
Proof.
  induction ks as [|q ks IH]; [reflexivity|].
  change (Z.of_nat (length (key_text q)) + 5 + keys_total (map short_key ks) =
          Z.of_nat (length (key_text q)) + 5 + keys_total ks). rewrite IH. reflexivity.
Qed.
Lemma short_entry_bytes : forall e, entry_bytes (short_entry e) = entry_bytes e.
Proof. intros e. unfold entry_bytes, re_nheld. cbn. rewrite length_map. reflexivity. Qed.
Lemma short_entry_blocks : forall e, entry_blocks (short_entry e) = entry_blocks e.
Proof. intros e. unfold entry_blocks. cbn. rewrite short_keys_addr. reflexivity. Qed.
Lemma short_target : forall G OUT es hj,
  target_addrs G OUT (map short_entry es) hj = target_addrs G OUT es hj.
Proof.
  intros G OUT es hj. unfold target_addrs. rewrite map_map.
  assert (H : map (fun e => entry_blocks (short_entry e)) es = map entry_blocks es).
  { apply map_ext. apply short_entry_blocks. } rewrite H. reflexivity.
Qed.
Lemma short_cost : forall es hj, slot_cost (map short_entry es) hj = slot_cost es hj.
Proof.
  intros es. induction es as [|e es IH]; intros [|h hj]; try reflexivity.
  change (pair_cost (short_entry e) h + slot_cost (map short_entry es) hj = pair_cost e h + slot_cost es hj).
  rewrite IH. unfold pair_cost. cbn [short_entry re_keys re_skip re_used]. rewrite short_keys_total. reflexivity.
Qed.
Lemma short_view : forall G OUT es hj, view_of G OUT (map short_entry es) hj = view_of G OUT es hj.
Proof.
  intros G OUT es hj.
  assert (W : AllocBound.zsum nw_ent (map short_entry es) = AllocBound.zsum nw_ent es).
  { induction es as [|e es IH]; [reflexivity|]. cbn [map]. rewrite !AllocBound.zsum_cons, IH. f_equal.
    unfold nw_ent, re_nheld. cbn [short_entry re_cap re_used re_hp re_kh re_keys]. rewrite length_map. reflexivity. }
  unfold view_of, nc_wt. rewrite W, map_map, length_map. reflexivity.
Qed.

Lemma bytes_at_prefix : forall segs m a bs n, bytes_at segs m a bs -> bytes_at segs m a (firstn n bs).
Proof.
  intros segs m a bs n (Ha & Hb & H). split; [exact Ha|]. split; [rewrite length_firstn; lia|].
  intros i Hi. rewrite length_firstn in Hi. rewrite nth_error_firstn, (proj2 (Nat.ltb_lt i n) ltac:(lia)). apply H. lia.
Qed.

Section StackFrame.
Context {rc : RunCeil}.
Variable B : malloc_syms.
Variables (m m' : word -> option byte) (S : Z).
Hypothesis HS : YM05.alloc_ceiling + 8 <= S.
Hypothesis MU : munch [(S, S + 16)] m m'.
Hypothesis WM : wmono (ms_segs B) m m'.

Lemma tail_bytes : forall a bs, bytes_at (ms_segs B) m a bs ->
  a + Z.of_nat (length bs) <= S \/ S + 16 <= a -> bytes_at (ms_segs B) m' a bs.
Proof.
  intros a bs H D. eapply bytes_at_transport; [exact H|exact MU|].
  cbn [disjoint_from]. split; [exact D|exact I].
Qed.
Lemma tail_cells : forall a cs, rw_cells (ms_segs B) m a cs ->
  a + Z.of_nat (cells_size cs) <= S \/ S + 16 <= a -> rw_cells (ms_segs B) m' a cs.
Proof.
  intros a cs H D. eapply rw_cells_transport; [exact H|exact MU|exact WM|].
  cbn [disjoint_from]. split; [exact D|exact I].
Qed.

Lemma tail_entry : forall L A e, RelayRep.entry_ok B L A m e -> RelayRep.entry_ok B L A m' (short_entry e).
Proof.
  intros L A e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & BU & H10 & HP & ND1 & ND2 & KS).
  unfold RelayRep.entry_ok, re_nheld in *.
  cbn [short_entry re_fd re_eof re_skip re_pad1 re_pad2 re_buf re_used re_cap re_hp re_kh re_keys re_U re_junk].
  rewrite length_map, short_keys_ptrs, short_keys_addr, short_keys_text.
  do 9 (split; [assumption|]). split.
  { destruct BU as [BU|(C & IN & FR & J & BC)]; [left; exact BU|right].
    split; [exact C|]. split; [exact IN|]. split; [exact FR|]. split; [exact J|].
    apply tail_cells; [exact BC|]. destruct FR as (_ & FR & _). cbn [cells_size csize].
    rewrite Nat.add_0_r, Z2Nat.id by lia. left. lia. }
  split; [exact H10|]. split.
  { destruct HP as [(HP & HK)|(IN & FR & HC & HH & HB)].
    - left. split; [exact HP|]. rewrite HK. reflexivity.
    - right. split; [exact IN|]. split; [exact FR|]. split; [exact HC|]. split; [exact HH|].
      apply tail_bytes; [exact HB|]. destruct FR as (_ & FR & _).
      rewrite slot_key_ptrs_length. left. lia. }
  split; [exact ND1|]. split; [exact ND2|].
  apply Forall_map. eapply Forall_impl; [|exact KS].
  intros [[addr txt] slack] (IN & FR & HB & NZ & LEN & PAD).
  cbn [short_key key_addr key_text key_slack fst snd] in *.
  split; [exact IN|]. split; [exact FR|]. split.
  { apply tail_bytes.
    - rewrite bytes_at_app in HB |- *. destruct HB as [HB HT]. split; [exact HB|].
      change (bytes_at (ms_segs B) m (addr + Z.of_nat (length txt))
        (firstn 8 (Z_to_bv 8 0 :: slack))). apply bytes_at_prefix. exact HT.
    - cbn [short_key key_addr key_text key_slack fst snd]. rewrite length_app. cbn [length].
      rewrite length_firstn. destruct FR as (_ & FR & _). left. lia. }
  split; [exact NZ|]. split; [exact LEN|]. rewrite length_firstn.
  pose proof (Z.mod_pos_bound (- (addr + Z.of_nat (length txt) + 1)) 8 ltac:(lia)). lia.
Qed.

Lemma tail_list : forall L A LA l lines,
  LA + 16 <= S -> list_at B L A m LA l lines -> list_at B L A m' LA l lines.
Proof.
  intros L A LA l lines HLA (C & HN & AR & ND1 & ND2 & RS).
  split; [apply tail_cells; [exact C|left; cbn; lia]|]. split; [exact HN|]. split.
  { destruct AR as [AR|(HC & IN & FR & HJ & HA)]; [left; exact AR|right].
    split; [exact HC|]. split; [exact IN|]. split; [exact FR|]. split; [exact HJ|].
    apply tail_cells; [exact HA|]. destruct FR as (_ & FR & _). left. cbn [cells_size csize].
    rewrite Nat.add_0_r, Z2Nat.id by lia. lia. }
  split; [exact ND1|]. split; [exact ND2|]. eapply Forall_impl; [|exact RS].
  intros r (IN & FR & CR & H1 & H2). split; [exact IN|]. split; [exact FR|].
  split; [|split; assumption]. apply tail_cells; [exact CR|]. destruct FR as (_ & FR & _). left. cbn. lia.
Qed.

Lemma tail_src : forall L A HA h,
  HA + 96 <= S -> src_at B L A m HA h -> src_at B L A m' HA h.
Proof.
  intros L A HA h HHA (C1 & H1 & H2 & H3 & H4 & LP & C2 & H5 & H6 & H7 & IN & FR & HJ & C3 & NZ & LE & LH & ND).
  split; [apply tail_cells; [exact C1|left; cbn; lia]|].
  do 4 (split; [assumption|]). split; [apply tail_list; [lia|exact LP]|].
  split; [apply tail_cells; [exact C2|left; cbn; lia]|].
  do 6 (split; [assumption|]). split.
  { apply tail_cells; [exact C3|]. destruct FR as (_ & FR & _). left. cbn. lia. }
  split; [exact NZ|]. split; [apply tail_list; [lia|exact LE]|]. split; [apply tail_list; [lia|exact LH]|exact ND].
Qed.
End StackFrame.

Lemma entry_size : forall rc B L A m e,
  RelayRep.entry_ok (rc := rc) B L A m e -> length (entry_bytes e) = 56%nat.
Proof.
  intros rc B L A m e (_ & _ & P1 & P2 & _). unfold entry_bytes.
  rewrite !length_app, !length_le4, !length_le8, P1, P2. reflexivity.
Qed.

Lemma table_slice : forall rc B L A m es tail G j e,
  Forall (RelayRep.entry_ok (rc := rc) B L A m) es ->
  bytes_at (ms_segs B) m G (concat (map entry_bytes es) ++ tail) ->
  nth_error es j = Some e ->
  RelayRep.entry_ok B L A m e /\ bytes_at (ms_segs B) m (G + 56 * Z.of_nat j) (entry_bytes e).
Proof.
  intros rc B L A m es. induction es as [|e0 es IH]; intros tail G [|j] e HF HB Hnth; try discriminate.
  - injection Hnth as <-. inversion HF as [|? ? HE HT]; subst.
    cbn [map concat] in HB. rewrite <- app_assoc, bytes_at_app in HB.
    split; [exact HE|]. replace (G + 56 * Z.of_nat 0) with G by lia. exact (proj1 HB).
  - inversion HF as [|? ? HE HT]; subst. cbn [map concat] in HB.
    rewrite <- app_assoc, bytes_at_app in HB. destruct HB as [_ HB].
    rewrite (entry_size rc B L A m e0 HE) in HB.
    destruct (IH tail (G + 56) j e HT HB Hnth) as [HE' HB'].
    split; [exact HE'|]. replace (G + 56 * Z.of_nat (S j)) with (G + 56 + 56 * Z.of_nat j) by lia. exact HB'.
Qed.

Lemma table_bounded : forall rc B L A m G es tail,
  ms_segs B = rsegs -> table_at B m G es tail ->
  Forall (RelayRep.entry_ok (rc := rc) B L A m) es ->
  forall j, 0 <= j < Z.of_nat (length es) -> source_bounded m G j.
Proof.
  intros rc B L A m G es tail SEG (_ & ((CW & HB) & _)) HF j Hj.
  cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  assert (HN : (Z.to_nat j < length es)%nat) by lia.
  destruct (nth_error es (Z.to_nat j)) as [e|] eqn:EN.
  2:{ apply nth_error_None in EN. lia. }
  destruct (table_slice rc B L A m es tail G _ e HF HB EN) as [HE BE].
  rewrite Z2Nat.id in BE by lia.
  destruct HE as (_ & _ & P1 & P2 & _ & HC & HU & U6 & _ & BUF & _).
  assert (UR : 0 <= re_used e <= re_cap e).
  { destruct BUF as [(C & _ & U)|(C & _ & _ & J & _)]; lia. }
  exists (Z_to_bv 64 (re_used e)), (Z_to_bv 64 (re_cap e)).
  unfold entry_bytes in BE. rewrite !bytes_at_app, !length_le4, !length_le8, P1 in BE.
  destruct BE as (_ & _ & _ & _ & _ & BU & BC & _).
  split.
  { rewrite <- SEG. replace (G + 56 * j + 24) with (G + 56 * j + 4 + 4 + 4 + 4 + 8) by lia. exact BU. }
  split.
  { rewrite <- SEG. replace (G + 56 * j + 32) with (G + 56 * j + 4 + 4 + 4 + 4 + 8 + 8) by lia. exact BC. }
  rewrite !unsigned_lit by (destruct HC as [HC|[HC|HC]]; lia). destruct HC as [HC|[HC|HC]]; lia.
Qed.

Lemma tail_relay : forall rc B L A m m' t nfd G OUT es hj S,
  @YM05.alloc_ceiling rc + 8 <= S -> G_S + 384 <= S ->
  munch [(S, S + 16)] m m' -> wmono (ms_segs B) m m' ->
  relay_at (rc := rc) B L A m t nfd G OUT es hj ->
  relay_at (rc := rc) B L A m' t nfd G OUT (map short_entry es) hj.
Proof.
  intros rc B L A m m' t nfd G OUT es hj S HS HG MU WM
    ((tail & HT & TC) & IN & FR & ES & ND & FD & PA & NDH & ZH & NDA).
  split.
  { exists tail. split; [rewrite length_map; exact HT|].
    assert (EB : map entry_bytes (map short_entry es) = map entry_bytes es).
    { rewrite map_map. apply map_ext. apply short_entry_bytes. }
    rewrite EB. apply (tail_cells B m m' S MU WM); [exact TC|]. destruct FR as (_ & FR & _).
    unfold SRC_TABLE, SRC_ENTRY in FR. left. cbn. lia. }
  split; [exact IN|]. split; [exact FR|]. split.
  { apply Forall_map. eapply Forall_impl; [|exact ES]. intros e HE. exact (tail_entry B m m' S HS MU WM L A e HE). }
  split; [rewrite map_map; exact ND|]. split; [apply Forall_map; exact FD|]. split.
  { clear HT TC IN FR ES ND FD NDH ZH NDA.
    induction PA as [|e p es hj HE HP IH]; cbn [map]; [constructor|]. constructor; [|exact IH].
    unfold pair_ok in *. cbv zeta in *. cbn [short_entry re_keys re_fd re_skip re_used re_eof re_U].
    rewrite short_keys_texts. destruct HE as (SRC & HI & REST).
    split; [apply (tail_src B m m' S HS MU WM); [unfold SRC_SIZE; lia|exact SRC]|]. split; assumption. }
  split; [exact NDH|]. split.
  { intros i HI HZ. apply (tail_cells B m m' S MU WM); [exact (ZH i HI HZ)|].
    left. cbn. unfold SRC_SIZE. lia. }
  rewrite short_target. exact NDA.
Qed.

Lemma tail_globals : forall rc B m m' S cl br gn dd ei N G nfd mx no cap out,
  @YM05.alloc_ceiling rc + 8 <= S -> 0x31aa0 <= S -> errno_addr B + 4 <= @YM05.alloc_ceiling rc ->
  munch [(S, S + 16)] m m' -> wmono (ms_segs B) m m' ->
  globals_at B m cl br gn dd ei N G nfd mx no cap out ->
  globals_at B m' cl br gn dd ei N G nfd mx no cap out.
Proof.
  intros rc B m m' S cl br gn dd ei N G nfd mx no cap out HS HG HE MU WM
    (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & ER & REST).
  unfold globals_at.
  do 13 (split; [eapply tail_cells; [exact MU|exact WM|eassumption|
    left; match goal with |- ?a <= S => let z := eval vm_compute in a in change (z <= S); lia end]|]).
  split; [|exact REST]. destruct ER as [ev ER]. exists ev.
  eapply tail_cells; [exact MU|exact WM|exact ER|left; cbn; lia].
Qed.

Lemma tail_output : forall rc B L A m m' S no cap out,
  @YM05.alloc_ceiling rc + 8 <= S -> munch [(S, S + 16)] m m' ->
  output_at (rc := rc) B L A m no cap out -> output_at (rc := rc) B L A m' no cap out.
Proof.
  intros rc B L A m m' S no cap out HS MU ((O & junk & H) & CAP).
  split; [|exact CAP]. exists O, junk. destruct H as [H|H]; [left; exact H|right].
  destruct H as (HC & HN & IN & FR & BY & LO & LJ).
  split; [exact HC|]. split; [exact HN|]. split; [exact IN|]. split; [exact FR|].
  split; [|split; assumption]. eapply tail_bytes; [exact MU|exact BY|].
  destruct FR as (_ & FR & _). rewrite length_app. left. lia.
Qed.

Lemma tail_run : check_bounded_contract -> forall (SP N G : Z)
    (x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) m,
  x2 = Z_to_bv 64 SP -> 0 <= SP - 16 -> SP < 2 ^ 64 ->
  stk rsegs m (SP - 16) SP -> -2 ^ 31 <= N < 2 ^ 31 -> 0 <= G < 2 ^ 64 ->
  bytes_at rsegs m check_bounded_c.G_NSRC (le4 (Z_to_bv 64 N)) ->
  bytes_at rsegs m check_bounded_c.G_SRC (le8 (Z_to_bv 64 G)) ->
  (0 < N -> G <> 0 /\ G mod 8 = 0) ->
  (forall j, 0 <= j < N -> source_bounded m G j) ->
  0x318e0 <= SP - 16 -> G + 56 * N <= SP - 16 ->
  forall x1,
  evt rsegs (fun ms => exists a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 m',
      ms = MS (mkR (Z_to_bv 64 0x142b4) x2 x3 x4 a0 a1 x7 x8 x26 a2 a3 a4 a5 a6 a7 a8 a9 x8
                   x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 TAIL_STEP) fc None m' (seg_rom rsegs) /\
      munch [(SP - 16, SP)] m m' /\ wmono rsegs m m')
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
             x28 x29 x30 x31) F (Z_to_bv 64 TAIL_CHECK) fc None m (seg_rom rsegs)).
Proof.
  intros CB SP N G x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m -> SP0 SP1 ST HN HG RN RG AL RS DG DS x1.
  step. eapply evt_cut.
  { eapply CB with (lo := SP - 16) (n := N) (src := Z_to_bv 64 G);
      rewrite ?unsigned_lit by lia; try eassumption;
      unfold CHECK_BOUNDED_FRAME, check_bounded_c.G_NSRC, check_bounded_c.G_SRC; lia. }
  intros ms (a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & a8 & a9 & m' & -> & MU & WM & ST').
  rewrite unsigned_lit in MU by lia.
  rewrite ret_pc_even by (unfold TAIL_CHECK; lia).
  change (Z_to_bv 64 (TAIL_CHECK + 4)) with (Z_to_bv 64 0x142b4).
  step. step. apply evt_done. do 11 eexists. split; [reflexivity|]. split; assumption.
Qed.

Lemma MI_tail : forall B API LS SH SK ra empty rc fx j E CS RI t k RG c,
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  check_bounded_contract ->
  (forall es hj no regs, RG es hj no regs -> tail_regs E t k regs) -> walk_at (ss_pl E) (t + 1) k ->
  MI (rc := rc) B (API rc) E RI t k TAIL_CHECK RG c ->
  SR (ms_segs B) c (LI (rc := rc) B (API rc) E RI (t + 1) k).
Proof.
  intros B API LS SH SK ra empty rc fx j E CS RI t k RG c HF CB HRG HW HM.
  pose proof HF as (FF & _ & PRE & _). pose proof (proj1 FF) as SEGS.
  assert (ERANGE : errno_addr B + 4 <= @YM05.alloc_ceiling rc).
  { destruct FF as (_ & _ & _ & _ & _ & _ & H & _). exact (H rc). }
  pose proof (proj1 (proj1 PRE)) as LP.
  destruct LP as (MR0 & _ & _ & _ & _ & _ & SPLO & SPHI & _).
  pose proof (@YM05.alloc_ceiling_value rc) as AC.
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  set (S := slot_sp E - 16).
  assert (SHI : @YM05.alloc_ceiling rc + 8 <= S) by (unfold S, slot_sp, SLOT_FRAME, SLOT_STACK in *; lia).
  assert (SG : G_S + 384 <= S) by (unfold G_S; lia).
  assert (SPB : 0 <= slot_sp E - 16 /\ slot_sp E < 2 ^ 64) by (unfold S, slot_sp, SLOT_FRAME in *; lia).
  destruct HM as (fx' & L & A & regs & mem & md & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out & es & hj &
    -> & FZ & Ht & Hk & Hn & HR & HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST & HDK & HGL & Hnfd & HOUT & HREL &
    Hes & Hcost & HRI).
  destruct (HRG _ _ _ _ HR) as ((B2 & B3 & B4 & B20) & (F23 & F25 & F21 & F19 & F27 & F24) & R8 & R26 & R22).
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HMR) as (Hh & Hl & Hmat).
  assert (ST : stk rsegs mem (slot_sp E - 16) (slot_sp E)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (WA : writable_at rsegs mem a).
    { rewrite <- SEGS. apply (proj2 (proj2 (proj2 HIK))). left. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
    split; [exact WA|]. destruct (writable_hi_present mem a ltac:(lia) WA) as [b HB].
    exists b. unfold mrd, wa. rewrite HB. reflexivity. }
  assert (RN : bytes_at rsegs mem check_bounded_c.G_NSRC (le4 (Z_to_bv 64 (Z.of_nat (length es))))).
  { destruct HGL as (_ & _ & _ & _ & _ & _ & _ & ((CW & BY) & _) & _).
    cbn [cells_bytes cbytes] in BY. rewrite app_nil_r, bytes_at_app in BY.
    rewrite <- SEGS. exact (proj1 BY). }
  assert (RG0 : bytes_at rsegs mem check_bounded_c.G_SRC (le8 (Z_to_bv 64 G))).
  { destruct HGL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ((CW & BY) & _) & _).
    cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. rewrite <- SEGS. exact BY. }
  pose proof HREL as ((tail & TAB) & GIN & GFR & HES & _).
  assert (GB : 4096 <= G /\ G + 896 <= @YM05.alloc_ceiling rc).
  { destruct GFR as (G0 & G1 & _). split; assumption. }
  assert (RS : forall q, 0 <= q < Z.of_nat (length es) -> source_bounded mem G q).
  { exact (table_bounded rc B L A mem G es tail SEGS TAB HES). }
  assert (GAL : G mod 8 = 0).
  { unfold blocks in GIN. apply in_map_iff in GIN as ([p k'] & EG & Hp). cbn [fst snd] in EG.
    injection EG as EG _. rewrite <- EG.
    pose proof (mr_blocks_aligned _ _ (aa_laws (API rc)) L A mem md p k' HMR Hp) as H16.
    Z.div_mod_to_equations. lia. }
  assert (E2 : reg_get regs 2 = Z_to_bv 64 (slot_sp E)) by exact B2.
  assert (E3 : reg_get regs 3 = getr (ss_regs E) 3) by exact B3.
  assert (E4 : reg_get regs 4 = getr (ss_regs E) 4) by exact B4.
  assert (E8 : reg_get regs 8 = Z_to_bv 64 (ss_p E + k)) by exact R8.
  assert (E19 : reg_get regs 19 = Z_to_bv 64 4) by exact F19.
  assert (E20 : reg_get regs 20 = Z_to_bv 64 G_RELAY_LO) by exact B20.
  assert (E21 : reg_get regs 21 = Z_to_bv 64 10) by exact F21.
  assert (E22 : reg_get regs 22 = Z_to_bv 64 t) by exact R22.
  assert (E23 : reg_get regs 23 = Z_to_bv 64 (slot_sp E + 32)) by exact F23.
  assert (E24 : reg_get regs 24 = Z_to_bv 64 1) by exact F24.
  assert (E25 : reg_get regs 25 = Z_to_bv 64 DIV10) by exact F25.
  assert (E26 : reg_get regs 26 = Z_to_bv 64 (ss_n E - k)) by exact R26.
  assert (E27 : reg_get regs 27 = Z_to_bv 64 (G_S + 4)) by exact F27.
  rewrite SEGS. eapply (evt_SR_canon rsegs); [|exact Hh|exact Hl|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite E2, E3, E4, E8, E19, E20, E21, E22, E23, E24, E25, E26, E27.
    eapply (tail_run CB (slot_sp E) (Z.of_nat (length es)) G); try eassumption; try reflexivity; unfold S in *; lia. }
  intros ms1 (can1 & (a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & a8 & a9 & mem' & -> & MU & WM) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (MU' : munch [(S, S + 16)] mem mem') by (unfold S; replace (slot_sp E - 16 + 16) with (slot_sp E) by lia; exact MU).
  assert (WM' : wmono (ms_segs B) mem mem') by (rewrite SEGS; exact WM).
  assert (LOW : forall a, 0 <= a < S ->
    mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
    (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha. split; [eapply munch_mbyte|eapply munch_writable];
      [exact MU'|lia|cbn [outside]; split; [lia|exact I]|exact MU'|lia|cbn [outside]; split; [lia|exact I]]. }
  assert (MR' : aa_MR (API rc) L A mem' md).
  { apply (mr_frame _ _ (aa_laws (API rc)) L A mem mem' md md HMR).
    - intros a HO. pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a HMR HO). apply LOW. lia.
    - intros a HO HP. pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a HMR HO).
      eapply munch_present; [exact MU'|lia|cbn [outside]; split; [lia|exact I]|exact HP].
    - intros p n i HP HI. destruct (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ p n i HMR HP HI) as (PR & B0 & B1 & _).
      eapply munch_present; [exact MU'|lia|cbn [outside]; split; [lia|exact I]|exact PR].
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  assert (RO' : ro_agree (ms_segs B) mem').
  { intros a HA. pose proof (bv_unsigned_in_range 64 a) as AB. change (bv_modulus 64) with (2 ^ 64) in AB.
    pose proof (ro_in_img B SEGS (bv_unsigned a) AB) as RI0.
    rewrite Z_to_bv_bv_unsigned, <- SEGS in RI0. specialize (RI0 HA).
    pose proof (in_img_low B SEGS _ RI0) as AL.
    unfold mrd. rewrite (MU' a) by (cbn; split; [lia|exact I]). apply HRO. exact HA. }
  assert (IK' : image_kept (rc := rc) B E mem').
  { destruct HIK as (IK1 & IK2 & IK3 & IK4). split.
    - intros a HA H1 H2 H3 H4. destruct (IK1 a HA H1 H2 H3 H4) as [EQA WQA].
      pose proof (in_img_low B SEGS _ HA) as AL. destruct (LOW a ltac:(lia)) as [EQB WQB]. split; [congruence|tauto].
    - split.
      + intros a HA. pose proof (IK2 a HA) as WQA.
        unfold in_globals, G_reply, frame_G in HA. destruct HA as (b & n & [EQ|[EQ|[]]] & HA); inversion EQ; subst;
          destruct (LOW a ltac:(lia)) as [EQB WQB]; tauto.
      + split.
        * intros a HA HNS. destruct (IK3 a HA HNS) as [EQA WQA].
          assert (OUT : outside [(S, S + 16)] a).
          { cbn. split; [unfold S, slot_sp, SLOT_FRAME, lib_scratch, SLOT_STACK in *; lia|exact I]. }
          pose proof (munch_mbyte (ms_segs B) _ _ _ a MU' ltac:(lia) OUT) as EQB.
          pose proof (munch_writable (ms_segs B) _ _ _ a MU' ltac:(lia) OUT) as WQB. split; [congruence|tauto].
        * intros a HA. apply WM'. exact (IK4 a HA). }
  assert (DK' : driver_kept B E (target_addrs G (bv_unsigned out) (map short_entry es) hj) L A mem').
  { rewrite short_target. destruct HDK as (DK1 & DK2 & DK3 & DK4). split; [exact DK1|]. split.
    - intros p n i HP HNT HNP HI. pose proof (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ p n i MR0 HP HI) as (_ & B0 & B1 & _).
      rewrite (proj1 (LOW (ptr_addr (ss_L E) p + i) ltac:(lia))). exact (DK2 p n i HP HNT HNP HI).
    - split; [|exact DK4]. intros i HI.
      destruct (proj1 (proj1 PRE)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PIN & _).
      destruct PIN as [(HN & _)|(HN & p & HP & EP)]; [lia|].
      pose proof (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ p (ss_n E) i MR0 HP HI) as (_ & B0 & B1 & _).
      rewrite EP in B0, B1. rewrite (proj1 (LOW (ss_p E + i) ltac:(lia))). exact (DK3 i HI). }
  rewrite <- SEGS. eapply (MI_tail48 B API LS SH SK ra empty rc fx j E CS RI t k
    (fun _ _ _ r => tail48_regs E t k r)); [exact HF|intros; assumption|exact HW|].
  exists fx', L, A, R1, mem', md, cl, br, gn, dd, ei, G, nfd, mx, nout, cap, out, (map short_entry es), hj.
  split; [rewrite SEGS; reflexivity|]. split; [exact FZ|]. split; [exact Ht|]. split; [exact Hk|]. split; [exact Hn|].
  split.
  { unfold tail48_regs, base_regs, fix_regs. repeat split; geq X1. }
  split; [exact MR'|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HINIT|]. split; [exact HVM|].
  split; [exact RO'|]. split; [exact IK'|]. split.
  { destruct HST as (C1 & C2 & C3). unfold stack_mid.
    split; [apply (tail_cells B mem mem' S MU' WM'); [exact C1|right; unfold S; cbn; lia]|].
    split; apply (tail_cells B mem mem' S MU' WM'); [exact C2|right; unfold S; cbn; lia|exact C3|right; unfold S; cbn; lia]. }
  split; [exact DK'|]. split.
  { rewrite length_map. eapply tail_globals; [exact SHI|unfold G_S in SG; lia|exact ERANGE|exact MU'|exact WM'|exact HGL]. }
  split; [exact Hnfd|]. split; [eapply tail_output; eassumption|].
  split; [eapply tail_relay; eassumption|]. split; [rewrite length_map; exact Hes|].
  split; [rewrite short_cost; exact Hcost|]. rewrite short_view. exact HRI.
Qed.
