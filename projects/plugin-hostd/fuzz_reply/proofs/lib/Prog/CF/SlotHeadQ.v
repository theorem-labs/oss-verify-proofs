(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 618 of its 664 lines of code are new or changed and 1183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass9G.v; 625 of its 781 lines of code are new or changed and 508 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import drain_b_c source_reset_c op_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import check_bounded_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotInv SlotSteps SlotHead SlotHeadP SlotRes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotHeadRun SlotHeadPick SlotWalk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

(* Only the first seven padding bytes are needed by the aligned string reader. *)
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
Lemma short_view : forall G OUT es hj,
  view_of G OUT (map short_entry es) hj = view_of G OUT es hj.
Proof.
  intros G OUT es hj.
  assert (W : AllocBound.zsum nw_ent (map short_entry es) = AllocBound.zsum nw_ent es).
  { induction es as [|e es IH]; [reflexivity|]. cbn [map]. rewrite !AllocBound.zsum_cons, IH. f_equal.
    unfold nw_ent, re_nheld. cbn [short_entry re_cap re_used re_hp re_kh re_keys]. rewrite length_map. reflexivity. }
  unfold view_of, nc_wt. rewrite W, map_map, length_map. reflexivity.
Qed.
Lemma short_cost : forall es hj, slot_cost (map short_entry es) hj = slot_cost es hj.
Proof.
  intros es. induction es as [|e es IH]; intros [|h hj]; try reflexivity.
  change (pair_cost (short_entry e) h + slot_cost (map short_entry es) hj = pair_cost e h + slot_cost es hj).
  rewrite IH. unfold pair_cost. cbn [short_entry re_keys re_skip re_used]. rewrite short_keys_total. reflexivity.
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

Lemma tail_entry : forall L A e, CF.RelayRep.entry_ok B L A m e -> CF.RelayRep.entry_ok B L A m' (short_entry e).
Proof.
  intros L A e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & BU & H10 & HP & ND1 & ND2 & KS).
  unfold CF.RelayRep.entry_ok, re_nheld in *.
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
  CF.RelayRep.entry_ok (rc := rc) B L A m e -> length (entry_bytes e) = 56%nat.
Proof.
  intros rc B L A m e (_ & _ & P1 & P2 & _). unfold entry_bytes.
  rewrite !length_app, !length_le4, !length_le8, P1, P2. reflexivity.
Qed.

Lemma table_slice : forall rc B L A m es tail G j e,
  Forall (CF.RelayRep.entry_ok (rc := rc) B L A m) es ->
  bytes_at (ms_segs B) m G (concat (map entry_bytes es) ++ tail) ->
  nth_error es j = Some e ->
  CF.RelayRep.entry_ok B L A m e /\ bytes_at (ms_segs B) m (G + 56 * Z.of_nat j) (entry_bytes e).
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
  Forall (CF.RelayRep.entry_ok (rc := rc) B L A m) es ->
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
  @YM05.alloc_ceiling rc + 8 <= S -> 0x311c0 <= S -> errno_addr B + 4 <= @YM05.alloc_ceiling rc ->
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
  (forall j, 0 <= j < N -> source_bounded m G j) ->
  0x31000 <= SP - 16 -> G + 56 * N <= SP - 16 ->
  forall x1,
  evt rsegs (fun ms => exists a0 a1 a2 a3 a4 m',
      ms = MS (mkR (Z_to_bv 64 0x13d3c) x2 x3 x4 x5 x6 x7 x8 x23 a0 a1 a2 a3 a4 (Z_to_bv 64 1) x16 x17 x8
                   x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 TAIL_STEP) fc None m' (seg_rom rsegs) /\
      munch [(SP - 16, SP)] m m' /\ wmono rsegs m m')
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
             x28 x29 x30 x31) F (Z_to_bv 64 TAIL_CHECK) fc None m (seg_rom rsegs)).
Proof.
  intros CB SP N G x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m -> SP0 SP1 ST HN HG RN RG RS DG DS x1.
  step. eapply evt_cut.
  { eapply CB with (lo := SP - 16) (n := N) (src := Z_to_bv 64 G);
      rewrite ?unsigned_lit by lia; try eassumption;
      unfold CHECK_BOUNDED_FRAME, check_bounded_c.G_NSRC, check_bounded_c.G_SRC; lia. }
  intros ms (a0 & a1 & a2 & a3 & a4 & a5 & m' & -> & MU & WM & ST').
  rewrite unsigned_lit in MU by lia.
  rewrite ret_pc_even by (unfold TAIL_CHECK; lia).
  change (Z_to_bv 64 (TAIL_CHECK + 4)) with (Z_to_bv 64 0x13d3c).
  step. step. step. apply evt_done. do 6 eexists. split; [reflexivity|]. split; assumption.
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
  destruct (HRG _ _ _ _ HR) as ((B2 & B3 & B4 & B20) & (F19 & F21 & F24 & F25 & F26 & F27) & R8 & R23 & R22).
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
  assert (E2 : reg_get regs 2 = Z_to_bv 64 (slot_sp E)) by exact B2.
  assert (E3 : reg_get regs 3 = getr (ss_regs E) 3) by exact B3.
  assert (E4 : reg_get regs 4 = getr (ss_regs E) 4) by exact B4.
  assert (E8 : reg_get regs 8 = Z_to_bv 64 (ss_p E + k)) by exact R8.
  assert (E19 : reg_get regs 19 = Z_to_bv 64 (slot_sp E + 32)) by exact F19.
  assert (E20 : reg_get regs 20 = Z_to_bv 64 G_RELAY_LO) by exact B20.
  assert (E21 : reg_get regs 21 = Z_to_bv 64 DIV10) by exact F21.
  assert (E22 : reg_get regs 22 = Z_to_bv 64 t) by exact R22.
  assert (E23 : reg_get regs 23 = Z_to_bv 64 (ss_n E - k)) by exact R23.
  assert (E24 : reg_get regs 24 = Z_to_bv 64 (slot_sp E + 16)) by exact F24.
  assert (E25 : reg_get regs 25 = Z_to_bv 64 4) by exact F25.
  assert (E26 : reg_get regs 26 = Z_to_bv 64 (G_S + 4)) by exact F26.
  assert (E27 : reg_get regs 27 = Z_to_bv 64 (G_S + SRC_SIZE * SOURCES_MAX + 4)) by exact F27.
  rewrite SEGS. eapply (evt_SR_canon rsegs); [|exact Hh|exact Hl|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite E2, E3, E4, E8, E19, E20, E21, E22, E23, E24, E25, E26, E27.
    eapply (tail_run CB (slot_sp E) (Z.of_nat (length es)) G); try eassumption; try reflexivity; unfold S in *; lia. }
  intros ms1 (can1 & (a0 & a1 & a2 & a3 & a4 & mem' & -> & MU & WM) & EQ1).
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

Section ClearOutputFrame.
Context {rc : RunCeil}.
Variable B : malloc_syms.
Variables m m' : word -> option byte.
Hypothesis MU : munch [(0x31000, 0x31008)] m m'.
Hypothesis WM : wmono (ms_segs B) m m'.
Hypothesis IMG : forall a, 0x30fc0 <= a < 0x311c0 -> in_img B a.

Lemma fresh_clear_apart : forall a n, fresh_block B a n -> 0 < n ->
  a + n + 7 <= 0x31000 \/ 0x31008 <= a.
Proof.
  intros a n (_ & _ & NI) HN.
  destruct (Z_le_gt_dec (a + n + 7) 0x31000) as [H|H]; [left; exact H|right].
  destruct (Z_le_gt_dec 0x31008 a) as [HA|HA]; [exact HA|exfalso].
  destruct (Z_le_gt_dec a 0x31000) as [A0|A0].
  - destruct (Z_le_gt_dec (a + n) 0x31000) as [A1|A1].
    + apply (NI (n - 1) ltac:(lia)), IMG. lia.
    + apply (NI (0x31000 - a) ltac:(lia)), IMG. lia.
  - apply (NI 0 ltac:(lia)), IMG. lia.
Qed.

Lemma clear_bytes : forall a bs,
  bytes_at (ms_segs B) m a bs -> a + Z.of_nat (length bs) <= 0x31000 \/ 0x31008 <= a ->
  bytes_at (ms_segs B) m' a bs.
Proof. intros a bs H D. eapply bytes_at_transport; [exact H|exact MU|]. cbn [disjoint_from]. tauto. Qed.
Lemma clear_cells : forall a cs,
  rw_cells (ms_segs B) m a cs -> a + Z.of_nat (cells_size cs) <= 0x31000 \/ 0x31008 <= a ->
  rw_cells (ms_segs B) m' a cs.
Proof. intros a cs H D. eapply rw_cells_transport; [exact H|exact MU|exact WM|]. cbn [disjoint_from]. tauto. Qed.
Lemma clear_fresh_bytes : forall a n bs, fresh_block B a n -> 0 < n ->
  Z.of_nat (length bs) <= n + 7 -> bytes_at (ms_segs B) m a bs -> bytes_at (ms_segs B) m' a bs.
Proof. intros a n bs FR HN HL HB. apply clear_bytes; [exact HB|]. pose proof (fresh_clear_apart a n FR HN). lia. Qed.
Lemma clear_fresh_cells : forall a n cs, fresh_block B a n -> 0 < n ->
  Z.of_nat (cells_size cs) <= n -> rw_cells (ms_segs B) m a cs -> rw_cells (ms_segs B) m' a cs.
Proof. intros a n cs FR HN HL HB. apply clear_cells; [exact HB|]. pose proof (fresh_clear_apart a n FR HN). lia. Qed.

Lemma clear_entry : forall L A e, CF.RelayRep.entry_ok B L A m e -> CF.RelayRep.entry_ok B L A m' (short_entry e).
Proof.
  intros L A e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & BU & H10 & HP & ND1 & ND2 & KS).
  unfold CF.RelayRep.entry_ok, re_nheld in *.
  cbn [short_entry re_fd re_eof re_skip re_pad1 re_pad2 re_buf re_used re_cap re_hp re_kh re_keys re_U re_junk].
  rewrite length_map, short_keys_ptrs, short_keys_addr, short_keys_text.
  do 9 (split; [assumption|]). split.
  { destruct BU as [BU|(C & IN & FR & J & BC)]; [left; exact BU|right].
    split; [exact C|]. split; [exact IN|]. split; [exact FR|]. split; [exact J|].
    eapply clear_fresh_cells; [exact FR|exact C|cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia|exact BC]. }
  split; [exact H10|]. split.
  { destruct HP as [(HP & HK)|(IN & FR & HC & HH & HB)].
    - left. split; [exact HP|]. rewrite HK. reflexivity.
    - right. split; [exact IN|]. split; [exact FR|]. split; [exact HC|]. split; [exact HH|].
      eapply clear_fresh_bytes; [exact FR|lia| |exact HB].
      rewrite slot_key_ptrs_length. lia. }
  split; [exact ND1|]. split; [exact ND2|].
  apply Forall_map. eapply Forall_impl; [|exact KS].
  intros [[addr txt] slack] (IN & FR & HB & NZ & LEN & PAD).
  cbn [short_key key_addr key_text key_slack fst snd] in *.
  split; [exact IN|]. split; [exact FR|]. split.
  { eapply clear_fresh_bytes; [exact FR|lia| |].
    - cbn [short_key key_addr key_text key_slack fst snd]. rewrite length_app. cbn [length]. rewrite length_firstn. lia.
    - rewrite bytes_at_app in HB |- *. destruct HB as [HB HT]. split; [exact HB|].
      change (bytes_at (ms_segs B) m (addr + Z.of_nat (length txt))
        (firstn 8 (Z_to_bv 8 0 :: slack))). apply bytes_at_prefix. exact HT. }
  split; [exact NZ|]. split; [exact LEN|]. rewrite length_firstn.
  pose proof (Z.mod_pos_bound (- (addr + Z.of_nat (length txt) + 1)) 8 ltac:(lia)). lia.
Qed.

Lemma clear_list : forall L A LA l lines,
  0x31008 <= LA -> list_at B L A m LA l lines -> list_at B L A m' LA l lines.
Proof.
  intros L A LA l lines HLA (C & HN & AR & ND1 & ND2 & RS).
  split; [apply clear_cells; [exact C|right; lia]|]. split; [exact HN|]. split.
  { destruct AR as [AR|(HC & IN & FR & HJ & HA)]; [left; exact AR|right].
    split; [exact HC|]. split; [exact IN|]. split; [exact FR|]. split; [exact HJ|].
    eapply clear_fresh_cells; [exact FR|lia| |exact HA]. cbn [cells_size csize].
    rewrite Nat.add_0_r, Z2Nat.id by lia. lia. }
  split; [exact ND1|]. split; [exact ND2|]. eapply Forall_impl; [|exact RS].
  intros r (IN & FR & CR & H1 & H2). split; [exact IN|]. split; [exact FR|].
  split; [|split; assumption]. eapply clear_fresh_cells; [exact FR|lia|cbn; lia|exact CR].
Qed.

Lemma clear_src : forall L A HA h,
  0x31008 <= HA -> src_at B L A m HA h -> src_at B L A m' HA h.
Proof.
  intros L A HA h HHA (C1 & H1 & H2 & H3 & H4 & LP & C2 & H5 & H6 & H7 & IN & FR & HJ & C3 & NZ & LE & LH & ND).
  split; [apply clear_cells; [exact C1|right; lia]|].
  do 4 (split; [assumption|]). split; [apply clear_list; [lia|exact LP]|].
  split; [apply clear_cells; [exact C2|right; lia]|]. do 6 (split; [assumption|]). split.
  { eapply clear_fresh_cells; [exact FR|lia|cbn; lia|exact C3]. }
  split; [exact NZ|]. split; [apply clear_list; [lia|exact LE]|]. split; [apply clear_list; [lia|exact LH]|exact ND].
Qed.

Lemma clear_relay : forall L A t nfd G OUT es hj,
  relay_at (rc := rc) B L A m t nfd G OUT es hj ->
  relay_at (rc := rc) B L A m' t nfd G OUT (map short_entry es) hj.
Proof.
  intros L A t nfd G OUT es hj
    ((tail & HT & TC) & IN & FR & ES & ND & FD & PA & NDH & ZH & NDA).
  split.
  { exists tail. split; [rewrite length_map; exact HT|].
    assert (EB : map entry_bytes (map short_entry es) = map entry_bytes es).
    { rewrite map_map. apply map_ext. apply short_entry_bytes. }
    rewrite EB. eapply clear_fresh_cells; [exact FR|unfold SRC_TABLE, SRC_ENTRY; lia|cbn; unfold SRC_TABLE, SRC_ENTRY; lia|exact TC]. }
  split; [exact IN|]. split; [exact FR|]. split.
  { apply Forall_map. eapply Forall_impl; [|exact ES]. intros e HE. exact (clear_entry L A e HE). }
  split; [rewrite map_map; exact ND|]. split; [apply Forall_map; exact FD|]. split.
  { clear HT TC IN FR ES ND FD NDH ZH NDA.
    induction PA as [|e p es hj HE HP IH]; cbn [map]; [constructor|]. constructor; [|exact IH].
    unfold pair_ok in *. cbv zeta in *. cbn [short_entry re_keys re_fd re_skip re_used re_eof re_U].
    rewrite short_keys_texts. destruct HE as (SRC & HI & REST).
    split; [apply clear_src; [unfold G_S, SRC_SIZE; lia|exact SRC]|]. split; assumption. }
  split; [exact NDH|]. split.
  { intros i HI HZ. apply clear_cells; [exact (ZH i HI HZ)|]. right. unfold G_S, SRC_SIZE. lia. }
  rewrite short_target. exact NDA.
Qed.

Lemma clear_output : forall L A no cap out, output_at (rc := rc) B L A m no cap out ->
  output_at (rc := rc) B L A m' (Z_to_bv 64 0) cap out.
Proof.
  intros L A no cap out ((O & junk & H) & CAP). split; [|exact CAP].
  destruct H as [(HC & HO & HN & ->)|(HC & HN & IN & FR & BY & LO & LJ)].
  - exists [], junk. left. repeat split; assumption || reflexivity.
  - exists [], (O ++ junk). right. rewrite (unsigned_lit 0) by lia.
    split; [exact HC|]. split; [lia|]. split; [exact IN|]. split; [exact FR|].
    split; [|split; [reflexivity|rewrite length_app; lia]]. cbn [app].
    eapply clear_fresh_bytes; [exact FR|exact HC|rewrite length_app; lia|exact BY].
Qed.
End ClearOutputFrame.

Lemma pair_find : forall X Y (P : X -> Y -> Prop) xs ys y,
  Forall2 P xs ys -> In y ys -> exists x, P x y.
Proof.
  intros X Y P xs ys y H. induction H as [|x y0 xs ys HP HR IH]; intros HY; [destruct HY|].
  destruct HY as [<-|HY]; [exists x; exact HP|exact (IH HY)].
Qed.

Definition open_flag (hj : list (hsrc * nat)) (i : nat) : Z := if slot_open hj i then 1 else 0.

Lemma flag_read : forall rc B L A mem t nfd G OUT es hj i,
  ms_segs B = rsegs -> relay_at (rc := rc) B L A mem t nfd G OUT es hj -> (i < 4)%nat ->
  ov_read_bytes rsegs mem (Z_to_bv 64 (G_S + SRC_SIZE * Z.of_nat i + 4)) 4 =
    Some (le4 (Z_to_bv 64 (open_flag hj i))).
Proof.
  intros rc B L A mem t nfd G OUT es hj i SEG (_ & _ & _ & _ & _ & _ & PA & _ & ZH & _) HI.
  unfold open_flag. destruct (slot_open hj i) eqn:HO.
  - unfold slot_open in HO. apply existsb_exists in HO. destruct HO as (q & HQ & HE).
    apply Nat.eqb_eq in HE. subst q. apply in_map_iff in HQ. destruct HQ as ([h q] & EQ & HQ). cbn in EQ. subst q.
    destruct (pair_find _ _ _ _ _ (h, i) PA HQ) as [e HP].
    destruct HP as (SRC & _). cbv zeta in SRC. cbn [fst snd] in SRC.
    destruct SRC as (C & _ & _ & OPEN & _). rewrite OPEN in C. rewrite SEG in C.
    change (Z_to_bv 64 (G_S + SRC_SIZE * Z.of_nat i + 4)) with (wa (G_S + SRC_SIZE * Z.of_nat i + Z.of_nat 4)).
    eapply (rw_cells_read _ _ _ _ 4%nat (C4 (Z_to_bv 64 1))); [exact C|reflexivity].
  - specialize (ZH i HI HO). rewrite SEG in ZH.
    change (Z_to_bv 64 (G_S + SRC_SIZE * Z.of_nat i + 4)) with (wa (G_S + SRC_SIZE * Z.of_nat i + Z.of_nat 4)).
    pose proof (rw_cells_cb_split rsegs mem _ _ _ 4%nat 4%nat ZH eq_refl eq_refl) as C.
    change (le4 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 4).
    eapply (rw_cells_read _ _ _ _ 4%nat (CB 4 (repeat (Z_to_bv 8 0) 4))); [exact C|reflexivity].
Qed.

Lemma jump_table_bytes : forall mem, ro_agree rsegs mem -> bytes_at rsegs mem JT_BASE JTB.
Proof.
  intros mem RO.
  pose proof (ro_cells_image rsegs (normalize rsegs mem) JT_BASE JTB (mem_inv_normalize rsegs mem)
    ltac:(vm_compute; reflexivity) ltac:(unfold JT_BASE; lia) ltac:(change (length JTB) with 36%nat; unfold JT_BASE; lia)) as (_ & BY).
  cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
  apply (proj2 (bytes_at_rel rsegs mem (normalize rsegs mem) JT_BASE JTB (mem_rel_normalize rsegs mem RO))). exact BY.
Qed.

Lemma input_read : forall rc B API LS SH SK ra empty fx j E CS L A mem TA k,
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  driver_kept B E TA L A mem -> 0 <= k < ss_n E ->
  ov_read_bytes (ms_segs B) mem (Z_to_bv 64 (ss_p E + k)) 1 =
    Some [nth (Z.to_nat k) (ss_pl E) (Z_to_bv 8 0)].
Proof.
  intros rc B API LS SH SK ra empty fx j E CS L A mem TA k (_ & _ & PRE & _) (_ & _ & DK & _) HK.
  destruct PRE as ((LP & LEN & BD & _) & _).
  assert (NB : nth_error (ss_pl E) (Z.to_nat k) = Some (nth (Z.to_nat k) (ss_pl E) (Z_to_bv 8 0))).
  { apply nth_error_nth'. lia. }
  assert (MB : mbyte (ms_segs B) mem (ss_p E + k) = Some (nth (Z.to_nat k) (ss_pl E) (Z_to_bv 8 0))).
  { rewrite (DK k HK), (BD k ltac:(lia)), NB. reflexivity. }
  change (match mbyte (ms_segs B) mem (ss_p E + k) with Some b => Some [b] | None => None end =
    Some [nth (Z.to_nat k) (ss_pl E) (Z_to_bv 8 0)]).
  rewrite MB. reflexivity.
Qed.

Lemma LI_dispatch : forall B API LS SH SK ra empty rc fx j E CS RI t k c,
  slot_frame B API LS SH SK ra empty rc fx j E CS -> RI_mono RI ->
  LI (rc := rc) B (API rc) E RI t k c -> t < OPS_MAX -> k < ss_n E ->
  SR (ms_segs B) c (fun c' =>
    (exists s, MI (rc := rc) B (API rc) E RI t (disp_k E (op_at E k) k) (jt_target (op_at E k))
      (fun _ hj no regs => no = 0 /\ disp_src (op_at E k) s hj /\ disp_regs E t (disp_k E (op_at E k) k) s regs) c') \/
    (exists k'', LI (rc := rc) B (API rc) E RI (t + 1) k'' c')).
Proof.
  intros B API LS SH SK ra empty rc fx j E CS RI t k c HF RIM HL HT HK.
  pose proof HF as (FF & _ & PRE & _). pose proof (proj1 FF) as SEG.
  pose proof FF as FFG. do 26 (destruct FFG as [_ FFG]). destruct FFG as [FG _].
  pose proof FF as FFA. do 30 (destruct FFA as [_ FFA]). specialize (FFA rc fx).
  do 12 (destruct FFA as [_ FFA]). destruct FFA as (AX & UNG & _).
  assert (ERR : errno_addr B = 0x311ec).
  { pose proof FF as FTP. do 16 (destruct FTP as [_ FTP]). destruct FTP as (TP & EO & _).
    unfold errno_addr. rewrite TP, EO. reflexivity. }
  assert (GA : forall a, 0x30fc0 <= a < 0x311c0 -> in_globals frame_G a).
  { intros a Ha. apply in_G_bss. lia. }
  assert (IMG : forall a, 0x30fc0 <= a < 0x311c0 -> in_img B a).
  { intros a Ha. exact (proj1 (FG a (GA a Ha))). }
  pose proof (proj1 (proj1 PRE)) as LP.
  destruct LP as (MR0 & _ & _ & _ & _ & _ & SPLO & SPHI & _).
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (SPB : 0x311c0 < slot_sp E /\ slot_sp E < 2 ^ 64).
  { unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  assert (HB : head_body E t k = true).
  { apply andb_true_iff. split; apply Z.ltb_lt; assumption. }
  destruct HL as (fx' & L & A & regs & mem & md & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out & es & hj &
    -> & FZ & Ht & Hk & HW & Hn & HR & HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST & HDK & HGL & Hnfd & HOUT & HREL &
    Hes & Hcost & HRI).
  destruct HR as (B2 & B3 & B4 & B20 & HR). specialize (HR HB).
  destruct HR as (R9 & R18 & R22 & R15 & F19 & F21 & F24 & F25 & F26 & F27).
  destruct HST as (ST1 & ST2 & ST3). specialize (ST3 HB).
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HMR) as (Hh & Hl & Hmat).
  set (mem1 := write_to_mem mem (Z_to_bv 64 0x31000) (le8 (Z_to_bv 64 0))).
  assert (MU : munch [(0x31000, 0x31008)] mem mem1).
  { unfold mem1. change (Z_to_bv 64 0x31000) with (wa 0x31000).
    eapply munch_write; [apply munch_refl|lia|rewrite length_le8; lia|cbn [inside]; left; rewrite length_le8; lia]. }
  assert (WM : wmono (ms_segs B) mem mem1) by (apply wmono_write, wmono_refl).
  assert (EQ : forall a, 0 <= a < 2 ^ 64 -> outside [(0x31000, 0x31008)] a ->
    mbyte (ms_segs B) mem1 a = mbyte (ms_segs B) mem a /\
    (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem1 a)).
  { intros a Ha HO. split; [exact (munch_mbyte _ _ _ _ a MU Ha HO)|exact (munch_writable _ _ _ _ a MU Ha HO)]. }
  assert (BX : forall L0 A0 m0 md0 p n i,
    aa_MR (API rc) L0 A0 m0 md0 -> In (p, n) (user_blocks A0) -> 0 <= i < n ->
    0 <= ptr_addr L0 p + i < 2 ^ 64 /\ outside [(0x31000, 0x31008)] (ptr_addr L0 p + i)).
  { intros L0 A0 m0 md0 p n i HM HP HI.
    destruct (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ p n i HM HP HI) as (_ & B0 & B1 & _).
    split; [lia|]. cbn [outside]. split; [|exact I]. intro HX.
    apply (ax_blocks_img AX L0 A0 m0 md0 p n i HM HP HI), IMG. lia. }
  assert (MR1 : aa_MR (API rc) L A mem1 md).
  { apply (mr_frame _ _ (aa_laws (API rc)) L A mem mem1 md md HMR).
    - intros a HO. pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a HMR HO) as HA.
      apply EQ; [lia|]. cbn [outside]. split; [|exact I]. intro HX. exact (UNG L A mem md a HMR (GA a ltac:(lia)) HO).
    - intros a HO HP. pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a HMR HO) as HA.
      eapply munch_present; [exact MU|lia| |exact HP]. cbn [outside]. split; [|exact I]. intro HX.
      exact (UNG L A mem md a HMR (GA a ltac:(lia)) HO).
    - intros p n i HP HI. destruct (BX L A mem md p n i HMR HP HI) as [HR HO].
      eapply munch_present; [exact MU|exact HR|exact HO|]. exact (proj1 (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ p n i HMR HP HI)).
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  assert (RO1 : ro_agree (ms_segs B) mem1).
  { intros a HA. unfold mrd. rewrite (MU a); [apply HRO; exact HA|]. cbn [outside]. split; [|exact I]. intro HX.
    assert (HNRO : ro_addr rsegs (Z_to_bv 64 (bv_unsigned a)) = false).
    { assert (bv_unsigned a = 0x31000 \/ bv_unsigned a = 0x31001 \/ bv_unsigned a = 0x31002 \/ bv_unsigned a = 0x31003 \/
              bv_unsigned a = 0x31004 \/ bv_unsigned a = 0x31005 \/ bv_unsigned a = 0x31006 \/ bv_unsigned a = 0x31007)
        as [EE|[EE|[EE|[EE|[EE|[EE|[EE|EE]]]]]]] by lia; rewrite EE; vm_compute; reflexivity. }
    rewrite Z_to_bv_bv_unsigned, <- SEG in HNRO. congruence. }
  pose proof HGL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OUTC & _).
  assert (SOK : store_ok rsegs mem (Z_to_bv 64 0x31000) 8 = true).
  { rewrite <- SEG. change (Z_to_bv 64 0x31000) with (wa (G_OUTV + Z.of_nat 8)).
    eapply (rw_cells_store_ok _ _ _ _ 8%nat (C8 nout)); [exact OUTC|reflexivity|reflexivity]. }
  assert (MWR : forall a, 0x31000 <= a < 0x31008 -> writable_at (ms_segs B) mem a).
  { intros a Ha. destruct OUTC as (_ & _ & _ & WR).
    replace a with (G_OUTV + (a - G_OUTV)) by lia. apply WR. change (0 <= a - 0x30ff8 < 32). lia. }
  assert (IK1 : image_kept (rc := rc) B E mem1).
  { destruct HIK as (I1 & I2 & I3 & I4). split.
    - intros a HA H1 H2 H3 H4. destruct (I1 a HA H1 H2 H3 H4) as [EA WA].
      pose proof (in_img_low B SEG a HA) as AR.
      assert (HO : outside [(0x31000, 0x31008)] a) by (cbn [outside]; split; [intro HX; apply H4, GA; lia|exact I]).
      destruct (EQ a ltac:(lia) HO) as [EB WB]. split; [congruence|tauto].
    - split.
      + intros a HA. pose proof (I2 a HA) as WA.
        destruct (Z_le_gt_dec 0x31000 a), (Z_lt_ge_dec a 0x31008).
        * pose proof (MWR a ltac:(lia)) as W0. pose proof (WM (Z_to_bv 64 a) W0) as W1. tauto.
        * assert (AR : 0 <= a < 2 ^ 64).
          { unfold in_globals, G_reply, frame_G in HA. destruct HA as (b & n & [EE|[EE|[]]] & HR); inversion EE; subst; lia. }
          destruct (EQ a AR ltac:(cbn [outside]; split; [lia|exact I])) as [EB WB]. tauto.
        * assert (AR : 0 <= a < 2 ^ 64).
          { unfold in_globals, G_reply, frame_G in HA. destruct HA as (b & n & [EE|[EE|[]]] & HR); inversion EE; subst; lia. }
          destruct (EQ a AR ltac:(cbn [outside]; split; [lia|exact I])) as [EB WB]. tauto.
        * assert (AR : 0 <= a < 2 ^ 64).
          { unfold in_globals, G_reply, frame_G in HA. destruct HA as (b & n & [EE|[EE|[]]] & HR); inversion EE; subst; lia. }
          destruct (EQ a AR ltac:(cbn [outside]; split; [lia|exact I])) as [EB WB]. tauto.
      + split.
        * intros a HA HNS. destruct (I3 a HA HNS) as [EA WA].
          destruct (EQ a ltac:(lia) ltac:(cbn [outside]; split; [lia|exact I])) as [EB WB]. split; [congruence|tauto].
        * intros a HA. apply WM. exact (I4 a HA). }
  assert (DK1 : driver_kept B E (target_addrs G (bv_unsigned out) (map short_entry es) hj) L A mem1).
  { rewrite short_target. destruct HDK as (D1 & D2 & D3 & D4). split; [exact D1|]. split.
    - intros p n i HP HNT HNP HI. destruct (BX _ _ _ _ p n i MR0 HP HI) as [AR AO].
      rewrite (proj1 (EQ _ AR AO)). exact (D2 p n i HP HNT HNP HI).
    - split; [|exact D4]. intros i HI.
      destruct (proj1 (proj1 PRE)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PIN & _).
      destruct PIN as [(HN & _)|(HN & p & HP & EP)]; [lia|].
      destruct (BX _ _ _ _ p (ss_n E) i MR0 HP HI) as [AR AO]. rewrite EP in AR, AO.
      rewrite (proj1 (EQ _ AR AO)). exact (D3 i HI). }
  assert (ST1' : stack_mid B E mem1).
  { unfold stack_mid. split; [eapply clear_cells; [exact MU|exact WM|exact ST1|right; lia]|].
    split; eapply clear_cells; [exact MU|exact WM|exact ST2|right; lia|exact MU|exact WM|exact ST3|right; lia]. }
  assert (GL1 : globals_at B mem1 cl br gn dd ei (Z.of_nat (length (map short_entry es))) G nfd mx (Z_to_bv 64 0) cap out).
  { rewrite length_map. destruct HGL as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & ER & REST).
    unfold globals_at.
    do 10 (split; [eapply clear_cells; [exact MU|exact WM|eassumption|left;
      match goal with |- ?a <= _ => let z := eval vm_compute in a in change (z <= 0x31000); lia end]|]).
    split.
    { unfold mem1. change (Z_to_bv 64 0x31000) with (wa (G_OUTV + Z.of_nat 8)).
      exact (rw_cells_write _ _ _ _ 8%nat (Cells.C8 nout) (Cells.C8 (Z_to_bv 64 0)) C11 eq_refl eq_refl I). }
    do 2 (split; [eapply clear_cells; [exact MU|exact WM|eassumption|right;
      match goal with |- _ <= ?a => let z := eval vm_compute in a in change (0x31008 <= z); lia end]|]).
    split; [|exact REST]. destruct ER as [ev ER]. exists ev. eapply clear_cells; [exact MU|exact WM|exact ER|right; rewrite ERR; lia]. }
  pose proof (clear_relay B mem mem1 MU WM IMG L A t nfd G (bv_unsigned out) es hj HREL) as REL1.
  pose proof (clear_output B mem mem1 MU IMG L A nout cap out HOUT) as OUT1.
  set (K := disp_k E (op_at E k) k).
  assert (KB : k + 1 <= K <= ss_n E).
  { unfold K, disp_k. destruct (pick_op (op_at E k)); cbn [andb]; destruct (Z.ltb_spec (k + 1) (ss_n E)); lia. }
  assert (MID : forall regs' pc RG', RG' (map short_entry es) hj 0 regs' ->
    MI (rc := rc) B (API rc) E RI t K pc RG'
      (mkCfg (@YK11.mkst fx' regs' (Z_to_bv 64 pc) mem1 (seg_rom (ms_segs B))) md)).
  { intros regs' pc RG' HRG. exists fx', L, A, regs', mem1, md, cl, br, gn, dd, ei, G, nfd, mx, (Z_to_bv 64 0), cap, out,
      (map short_entry es), hj.
    split; [reflexivity|]. split; [exact FZ|]. split; [lia|]. split; [lia|]. split; [exact Hn|].
    split; [rewrite (unsigned_lit 0) by lia; exact HRG|].
    split; [exact MR1|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HINIT|]. split; [exact HVM|].
    split; [exact RO1|]. split; [exact IK1|]. split; [exact ST1'|]. split; [exact DK1|]. split; [exact GL1|].
    split; [destruct ((pc =? TAIL_CHECK) || (pc =? TAIL_STEP)); lia|]. split; [exact OUT1|]. split; [eapply relay_at_t; [exact REL1|cbn; repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia]|]. split; [rewrite length_map; exact Hes|].
    split; [rewrite short_cost; lia|]. rewrite short_view. eapply RIM; [exact HRI|lia]. }
  assert (R0 : ov_read_bytes rsegs mem (Z_to_bv 64 (ss_p E + k)) 1 = Some [nth (Z.to_nat k) (ss_pl E) (Z_to_bv 8 0)]).
  { rewrite <- SEG. eapply input_read with (fx := fx); [exact HF|exact HDK|lia]. }
  assert (RBYTE1 : k + 1 < ss_n E -> ov_read_bytes rsegs mem1 (Z_to_bv 64 (ss_p E + k + 1)) 1 =
    Some [nth (Z.to_nat (k + 1)) (ss_pl E) (Z_to_bv 8 0)]).
  { intros HK1. replace (ss_p E + k + 1) with (ss_p E + (k + 1)) by lia. rewrite <- SEG.
    eapply input_read with (fx := fx); [exact HF|exact DK1|lia]. }
  assert (RF : forall i, (i < 4)%nat -> ov_read_bytes rsegs mem1 (Z_to_bv 64 (G_S + SRC_SIZE * Z.of_nat i + 4)) 4 =
    Some (le4 (Z_to_bv 64 (open_flag hj i)))).
  { intros i HI. eapply flag_read; [exact SEG|exact REL1|exact HI]. }
  assert (RSP : ov_read_bytes rsegs mem1 (Z_to_bv 64 (slot_sp E + 8)) 8 = Some (le8 (Z_to_bv 64 G_S))).
  { destruct ST1' as (_ & _ & C). rewrite SEG in C.
    replace (Z_to_bv 64 (slot_sp E + 8)) with (wa (slot_sp E + 8 + Z.of_nat 0)) by (f_equal; lia).
    eapply (rw_cells_read _ _ _ _ 0%nat (C8 (Z_to_bv 64 G_S))); [exact C|reflexivity]. }
  assert (JT : bytes_at rsegs mem1 JT_BASE JTB) by (apply jump_table_bytes; rewrite <- SEG; exact RO1).
  assert (FB : forall i, open_flag hj i = 0 \/ open_flag hj i = 1).
  { intros i. unfold open_flag. destruct (slot_open hj i); auto. }
  assert (E2 : reg_get regs 2 = Z_to_bv 64 (slot_sp E)) by exact B2.
  assert (E3 : reg_get regs 3 = getr (ss_regs E) 3) by exact B3.
  assert (E4 : reg_get regs 4 = getr (ss_regs E) 4) by exact B4.
  assert (E9 : reg_get regs 9 = Z_to_bv 64 (ss_n E - k)) by exact R9.
  assert (E15 : reg_get regs 15 = Z_to_bv 64 1) by exact R15.
  assert (E18 : reg_get regs 18 = Z_to_bv 64 (ss_p E + k)) by exact R18.
  assert (E19 : reg_get regs 19 = Z_to_bv 64 (slot_sp E + 32)) by exact F19.
  assert (E20 : reg_get regs 20 = Z_to_bv 64 G_RELAY_LO) by exact B20.
  assert (E21 : reg_get regs 21 = Z_to_bv 64 DIV10) by exact F21.
  assert (E22 : reg_get regs 22 = Z_to_bv 64 t) by exact R22.
  assert (E24 : reg_get regs 24 = Z_to_bv 64 (slot_sp E + 16)) by exact F24.
  assert (E25 : reg_get regs 25 = Z_to_bv 64 4) by exact F25.
  assert (E26 : reg_get regs 26 = Z_to_bv 64 (G_S + 4)) by exact F26.
  assert (E27 : reg_get regs 27 = Z_to_bv 64 (G_S + SRC_SIZE * SOURCES_MAX + 4)) by exact F27.
  unfold head_pc. rewrite HB, SEG. eapply (evt_SR_canon rsegs); [|exact Hh|exact Hl|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite E2, E3, E4, E9, E15, E18, E19, E20, E21, E22, E24, E25, E26, E27.
    eapply (dsp_run t (ss_n E) k (ss_p E) (slot_sp E) (open_flag hj 0) (open_flag hj 1) (open_flag hj 2) (open_flag hj 3));
      try exact R0; try exact SOK; try reflexivity; try exact RBYTE1; try exact RSP; try exact JT; try apply FB;
      try (apply (RF 0%nat); lia); try (apply (RF 1%nat); lia); try (apply (RF 2%nat); lia); try (apply (RF 3%nat); lia);
      unfold INPUT_MAX in Hn; lia. }
  intros ms1 (can1 & (s0 & s1 & s2 & s7 & a0 & a1 & a2 & a3 & a4 & pc & -> & E0 & E7 & HO) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  fold (op_at E k) in E0, E7, HO.
  change (dk (op_at E k) k (ss_n E)) with K in E0, E7, HO. subst s0 s7.
  rewrite <- SEG. destruct HO as [(-> & E18' & DS)|(-> & HP & HN1 & E9' & E18' & Z0 & Z1 & Z2 & Z3)].
  - destruct DS as [(HP & i & HI & FI & ES1)|(HP & ES1)].
    + assert (FI' : open_flag hj i = 1).
      { replace (open_flag hj i) with (nth i [open_flag hj 0; open_flag hj 1; open_flag hj 2; open_flag hj 3] 0).
        - exact FI.
        - destruct i as [|[|[|[|i]]]]; try lia; reflexivity. }
      assert (OI : slot_open hj i = true) by (unfold open_flag in FI'; destruct (slot_open hj i); congruence).
      subst s1. apply SR_ret. left. exists (G_S + SRC_SIZE * Z.of_nat i). apply MID.
      split; [reflexivity|]. split; [left; split; [exact HP|exists i; repeat split; assumption || reflexivity]|].
      unfold disp_regs, base_regs, fix_regs. repeat split; geq X1.
    + subst s1. apply SR_ret. left. exists 0. apply MID.
      split; [reflexivity|]. split; [right; split; [exact HP|reflexivity]|]. unfold disp_regs, base_regs, fix_regs. repeat split; geq X1.
  - subst s1 s2.
    eapply SR_mono.
    + eapply (MI_tail48 B API LS SH SK ra empty rc fx j E CS RI t K (fun _ _ _ r => tail48_regs E t K r));
        [exact HF|intros; assumption|exact (walk_pick E t k (op_at E k) HW (frame_len B API LS SH SK ra empty rc fx j E CS HF)
          HK eq_refl (pick_not1 (op_at E k) HP HN1))|].
      apply MID. unfold tail48_regs, base_regs, fix_regs. repeat split; geq X1.
    + intros c' HC. right. exists K. exact HC.
Qed.
