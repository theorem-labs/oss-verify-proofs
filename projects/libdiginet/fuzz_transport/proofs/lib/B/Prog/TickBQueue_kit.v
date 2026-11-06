(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 329 of its 374 lines of code are new or changed and 1879 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickEpi.v, with its module names changed; 715 of its 765 lines of code are new or changed and 324 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickQueue_kit.v, with its module paths, module names, addresses and numbers changed; 48 of its 717 lines of code are new or changed and 96 lines of the source are left out. *)
(* TickBQueue_kit: what the queue piece of diginet_session_tick's image-B walk (lib/B/Prog/TickCutB.v tick_queue_stmt,
   code +0x698 .. +0x710 and +0x7a8 .. +0x840 of fuzz_transport.asan-ubsan 0x8909c) uses beyond the kit, and the four
   points inside the piece at which its segments meet, as statements in TickCutB.v's continuation form:
     tq_body_at  +0x7ac (0x89848)  s9 = body, `jal __asan_set_shadow_00`, the shadow byte 205, `jal take`;
     tq_tk_at    +0x7dc (0x89878)  take returned: the taken test, has_display and the display stores;
     tq_sd_at    +0x814 (0x898b0)  a2 = body_len, a4 = now, `jal send_data`, s10 = its result;
     tq_f8_at    +0x834 (0x898d0)  `jal __asan_set_shadow_f8`, then `j` to the epilogue cut.
   rule 24: proves no function (lemmas and cut statements for one piece of the walk of diginet_session_tick; the walk
   is composed at TickCutB.v tick_holds_of).
   It is image B's twin of lib/A/Prog/TickQueue_kit.v (image A's queue piece, which this tree does not hold): the model
   lemmas are that file's, restated (they name no image); the machine lemmas are its proofs at image B's segments, G
   (lib/B/TransportGB.v G_HARNESS_B), world table (lib/B/Prog/TWorldB.v TMAP_B) and frame layout (the body at frame +
   160, its shadow bytes 20 .. 205; image A: frame + 384, bytes 48 .. 233).
   Model (TModel/TSess0.v take_m, TSess.v send_data_m): tick_queue_m split at take (tq_queue_eq); take_m and the two
   display stores keep every world byte outside g_s's queue and queued, and outside display_sent / last_display_us
   (tq_take_keep, tq_dw_keep), so the run invariants (1) and (4) and g_fail_next reach the world send_data is given.
   Machine: the caller's kept fact at the memory take returned (the out cells put back, TransportGCg.v gover) is its
   kept fact at that memory (tq_kept_ungover: the last step of TransportGCg.v dk_kept_trans_out_g, for a callee called
   at a state that holds the walk's own frame); tick_cur carried over a step that writes the walk's window below the
   saved words, its own frame but the frame's last word, or G (tq_cur_step), and over a G-form callee (tq_cur_call).
   The engine's register and chunk readings and the bytes of G are lib/B/Prog/TickBKit.v's (sn_regB, sn_chunk_valB,
   slh_inGB, tick_wr_G). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg set_state_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg TickCutB TickBKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas TOpsKeep TSessFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOpsKeep.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The four points inside the piece, as offsets from the listing's base, and the return addresses of its four calls
   (`jal __asan_set_shadow_00` +0x7b8, `jal take` +0x7d8, `jal send_data` +0x824, `jal __asan_set_shadow_f8`
   +0x83c). *)
Definition TQ_BODY : Z := AF_diginet_session_tick + 0x7ac.
Definition TQ_TK : Z := AF_diginet_session_tick + 0x7dc.
Definition TQ_SD : Z := AF_diginet_session_tick + 0x814.
Definition TQ_F8 : Z := AF_diginet_session_tick + 0x834.
Definition TQ_R00 : Z := AF_diginet_session_tick + 0x7bc.
Definition TQ_RSD : Z := AF_diginet_session_tick + 0x828.
Definition TQ_RF8 : Z := AF_diginet_session_tick + 0x840.

(* ------------------------------------------------------------------ *)
(* 1. The model on the queue path                                      *)
(* ------------------------------------------------------------------ *)

(* The display test of :460. *)
Definition tq_allow (B : list byte) (now : Z) : Z :=
  DLib.int_of_bool ((TW.S_display_sent B =? 0) ||
                    (TW.S_cfg_display_gap_us B <=? TS0.u64 (now - TW.S_last_display_us B))).
(* The world send_data is given (:467-470). *)
Definition tq_dw (B : list byte) (hd now : Z) : list byte :=
  if hd =? 0 then B else TW.set_S_last_display_us (TW.set_S_display_sent B 1) now.
(* What remains once take returned (:465-471). *)
Definition tq_after_take (I : TI.timg) (F : option TI.tframe) (B1 body : list byte) (len hd n now : Z)
    : option (list byte * Z) :=
  if n =? 0 then Some (B1, DLib.DIGINET_OK)
  else TSS.send_data_m I F (tq_dw B1 hd now) (firstn (Z.to_nat len) body) n now.
(* What remains at the call of take (:461-471). *)
Definition tq_take_cont (I : TI.timg) (F : option TI.tframe) (B : list byte) (allow now : Z)
    : option (list byte * Z) :=
  match TS0.take_m B allow with
  | None => None
  | Some (B1, (body, len, hd, n)) => tq_after_take I F B1 body len hd n now
  end.

Lemma tq_queue_eq : forall (I : TI.timg) (F : option TI.tframe) (B : list byte) (now : Z),
  tick_queue_m I F B now =
  if TW.S_queued B =? 0 then Some (B, DLib.DIGINET_OK) else tq_take_cont I F B (tq_allow B now) now.
Proof. intros I F B now. reflexivity. Qed.

Lemma tq_allow_range : forall B now, 0 <= tq_allow B now <= 1.
Proof. intros B now. unfold tq_allow, DLib.int_of_bool. destruct (_ || _)%bool; lia. Qed.

(* X is B but at the world offsets [lo, hi). *)
Definition tq_keep (lo hi : Z) (B X : list byte) : Prop :=
  length X = length B /\ forall i, ~ (lo <= Z.of_nat i < hi) -> nth_error X i = nth_error B i.

Lemma tq_keep_refl : forall lo hi B, tq_keep lo hi B B.
Proof. intros lo hi B. split; [reflexivity | intros i _; reflexivity]. Qed.

Lemma tq_keep_trans : forall lo hi B X Y, tq_keep lo hi B X -> tq_keep lo hi X Y -> tq_keep lo hi B Y.
Proof.
  intros lo hi B X Y [L1 H1] [L2 H2]. split; [congruence|].
  intros i Hi. rewrite (H2 i Hi). exact (H1 i Hi).
Qed.

Lemma tq_keep_upd : forall lo hi B X k v, tq_keep lo hi B X -> 0 <= k ->
  k + Z.of_nat (length v) <= Z.of_nat (length X) -> lo <= k -> k + Z.of_nat (length v) <= hi ->
  tq_keep lo hi B (TW.upd X k v).
Proof.
  intros lo hi B X k v [HL HK] Hk Hl Hlo Hhi. split.
  - rewrite TWL.length_upd by lia. exact HL.
  - intros i Hi. rewrite TWL.ne_upd by lia.
    destruct ((Z.to_nat k <=? i) && (i <? Z.to_nat k + length v))%nat eqn:E.
    + exfalso. apply andb_prop in E as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2. apply Hi. lia.
    + exact (HK i Hi).
Qed.

Lemma tq_keep_u_at : forall lo hi B X k n, tq_keep lo hi B X -> 0 <= k ->
  (k + Z.of_nat n <= lo \/ hi <= k) -> TW.u_at X k n = TW.u_at B k n.
Proof.
  intros lo hi B X k n [_ HK] Hk Hd. unfold TW.u_at. f_equal.
  apply TOK.tok_list_ext. intros i. rewrite !TWL.ne_sub by exact Hk.
  destruct (i <? n)%nat eqn:E; [|reflexivity]. apply Nat.ltb_lt in E.
  apply HK. lia.
Qed.

Lemma tq_keep_s32 : forall lo hi B X k, tq_keep lo hi B X -> 0 <= k ->
  (k + 4 <= lo \/ hi <= k) -> TW.s32_at X k = TW.s32_at B k.
Proof. intros lo hi B X k K Hk Hd. unfold TW.s32_at. rewrite (tq_keep_u_at lo hi B X k 4 K Hk); [reflexivity | cbn; lia]. Qed.

(* The bytes of g_s's queue and of queued. *)
Definition TQ_QLO : Z := TW.A_S_queue_bytes 0.
Definition TQ_QHI : Z := TW.A_S_queued + 4.

(* The world of an equation of two world-carrying results, by the first projection (no injection). *)
Lemma tq_some_fst : forall (A Bt : Type) (a a' : A) (b b' : Bt), Some (a, b) = Some (a', b') -> a = a'.
Proof. intros A Bt a a' b b' H. exact (f_equal (fun o => match o with Some (x, _) => x | None => a end) H). Qed.

(* take's tail move (:378-379) writes queue entries only. *)
Lemma tq_tail_keep : forall fuel B kept j B2 kept2,
  length B = Z.to_nat TW.W_LEN -> 0 <= kept -> 0 <= j ->
  TS0.take_tail_m B kept j fuel = Some (B2, kept2) ->
  tq_keep TQ_QLO TQ_QHI B B2.
Proof.
  induction fuel as [|f IH]; intros B kept j B2 kept2 HL Hk Hj H; cbn [TS0.take_tail_m] in H.
  - rewrite <- (tq_some_fst _ _ _ _ _ _ H). apply tq_keep_refl.
  - destruct ((TW.S_queue_N <=? j) || (TW.S_queue_N <=? kept))%bool eqn:E; [discriminate H|].
    apply orb_false_iff in E as [E1 E2]. apply Z.leb_gt in E1. apply Z.leb_gt in E2.
    assert (LS : length (TW.sub B (TW.A_S_queue_bytes j) 32) = 32%nat).
    { apply TWL.length_sub; unfold TW.A_S_queue_bytes, TW.OFF_g_s, TW.S_queue_N in *; [lia|].
      rewrite HL. unfold TW.W_LEN. lia. }
    assert (K1 : tq_keep TQ_QLO TQ_QHI B (TW.upd B (TW.A_S_queue_bytes kept) (TW.sub B (TW.A_S_queue_bytes j) 32))).
    { apply tq_keep_upd; [apply tq_keep_refl | | | |];
        rewrite ?LS, ?HL; unfold TQ_QLO, TQ_QHI, TW.A_S_queue_bytes, TW.A_S_queued, TW.OFF_g_s, TW.W_LEN,
          TW.S_queue_N in *; lia. }
    assert (L1 : length (TW.upd B (TW.A_S_queue_bytes kept) (TW.sub B (TW.A_S_queue_bytes j) 32)) =
      Z.to_nat TW.W_LEN) by (destruct K1 as [L _]; rewrite L; exact HL).
    exact (tq_keep_trans _ _ _ _ _ K1 (IH _ (kept + 1) (j + 1) B2 kept2 L1 ltac:(lia) ltac:(lia) H)).
Qed.

(* take's loop (:358-382) writes queue entries only, kept <= i throughout. *)
Lemma tq_loop_keep : forall fuel B allow i taken kept len hd body B2 r,
  length B = Z.to_nat TW.W_LEN -> 0 <= kept <= i ->
  TS0.take_loop_m B allow i taken kept len hd body fuel = Some (B2, r) ->
  tq_keep TQ_QLO TQ_QHI B B2.
Proof.
  induction fuel as [|f IH]; intros B allow i taken kept len hd body B2 r HL Hk H; cbn [TS0.take_loop_m] in H.
  - rewrite <- (tq_some_fst _ _ _ _ _ _ H). apply tq_keep_refl.
  - destruct (TW.S_queue_N <=? i) eqn:Ei; [discriminate H|]. apply Z.leb_gt in Ei.
    cbv zeta in H.
    match type of H with context [if ?c then None else _] => destruct c; [discriminate H|] end.
    (* the world and kept after this turn, by the two arms of fits *)
    assert (ARM : forall (fits : bool),
      (if fits then True else True) ->
      tq_keep TQ_QLO TQ_QHI B
        (if fits then B
         else if kept =? i then B
              else TW.upd B (TW.A_S_queue_bytes kept) (TW.sub B (TW.A_S_queue_bytes i) 32))).
    { intros fits _. destruct fits; [apply tq_keep_refl|].
      destruct (kept =? i); [apply tq_keep_refl|].
      assert (LS : length (TW.sub B (TW.A_S_queue_bytes i) 32) = 32%nat).
      { apply TWL.length_sub; unfold TW.A_S_queue_bytes, TW.OFF_g_s, TW.S_queue_N in *; [lia|].
        rewrite HL. unfold TW.W_LEN. lia. }
      apply tq_keep_upd; [apply tq_keep_refl | | | |];
        rewrite ?LS, ?HL; unfold TQ_QLO, TQ_QHI, TW.A_S_queue_bytes, TW.A_S_queued, TW.OFF_g_s, TW.W_LEN,
          TW.S_queue_N in *; lia. }
    match type of H with
    | context [if ?fits then (?B1a, ?b1a, ?l1a, ?t1a, ?h1a, ?k1a) else (?B1b, ?b1b, ?l1b, ?t1b, ?h1b, ?k1b)] =>
        destruct fits eqn:Ef
    end;
    cbn beta iota in H.
    + pose proof (ARM true I) as K1. cbn beta iota in K1.
      match type of H with context [if ?c then match _ with _ => _ end else _] => destruct c end.
      * match type of H with context [TS0.take_tail_m ?Bx ?kx ?jx ?fx] =>
          destruct (TS0.take_tail_m Bx kx jx fx) as [[B3 kept3]|] eqn:ET; [|discriminate H] end.
        rewrite <- (tq_some_fst _ _ _ _ _ _ H). refine (tq_tail_keep _ _ _ _ _ _ HL _ _ ET); lia.
      * refine (IH _ _ _ _ _ _ _ _ _ _ HL _ H). lia.
    + pose proof (ARM false I) as K1. cbn beta iota in K1.
      assert (L1 : length (if kept =? i then B
                           else TW.upd B (TW.A_S_queue_bytes kept) (TW.sub B (TW.A_S_queue_bytes i) 32)) =
                   Z.to_nat TW.W_LEN) by (destruct K1 as [L _]; rewrite L; exact HL).
      match type of H with context [if ?c then match _ with _ => _ end else _] => destruct c end.
      * match type of H with context [TS0.take_tail_m ?Bx ?kx ?jx ?fx] =>
          destruct (TS0.take_tail_m Bx kx jx fx) as [[B3 kept3]|] eqn:ET; [|discriminate H] end.
        rewrite <- (tq_some_fst _ _ _ _ _ _ H).
        refine (tq_keep_trans _ _ _ _ _ K1 (tq_tail_keep _ _ _ _ _ _ L1 _ _ ET)); lia.
      * refine (tq_keep_trans _ _ _ _ _ K1 (IH _ _ _ _ _ _ _ _ _ _ L1 _ H)). lia.
Qed.

(* take_m writes g_s's queue entries and queued only. *)
Lemma tq_take_keep : forall B allow B1 body len hd n,
  length B = Z.to_nat TW.W_LEN ->
  TS0.take_m B allow = Some (B1, (body, len, hd, n)) ->
  tq_keep TQ_QLO TQ_QHI B B1.
Proof.
  intros B allow B1 body len hd n HL H. unfold TS0.take_m in H.
  destruct (TS0.take_loop_m B allow 0 0 0 0 0 [] (Z.to_nat (TW.S_queued B)))
    as [[B2 [[[[body2 len2] hd2] taken2] kept2]]|] eqn:EL; [|discriminate H].
  rewrite <- (tq_some_fst _ _ _ _ _ _ H).
  assert (K2 : tq_keep TQ_QLO TQ_QHI B B2) by (refine (tq_loop_keep _ _ _ _ _ _ _ _ _ _ _ HL _ EL); lia).
  assert (L2 : length B2 = Z.to_nat TW.W_LEN) by (destruct K2 as [L _]; rewrite L; exact HL).
  unfold TW.set_S_queued. apply tq_keep_upd; [exact K2 | | | |];
    rewrite ?TWL.length_put, ?L2; unfold TQ_QLO, TQ_QHI, TW.A_S_queue_bytes, TW.A_S_queued, TW.OFF_g_s, TW.W_LEN; lia.
Qed.

(* The bytes of display_sent and last_display_us. *)
Definition TQ_DLO : Z := TW.A_S_last_display_us.
Definition TQ_DHI : Z := TW.A_S_display_sent + 4.

Lemma tq_dw_keep : forall B hd now, length B = Z.to_nat TW.W_LEN -> tq_keep TQ_DLO TQ_DHI B (tq_dw B hd now).
Proof.
  intros B hd now HL. unfold tq_dw. destruct (hd =? 0); [apply tq_keep_refl|].
  assert (K1 : tq_keep TQ_DLO TQ_DHI B (TW.set_S_display_sent B 1)).
  { unfold TW.set_S_display_sent. apply tq_keep_upd; [apply tq_keep_refl | | | |];
      rewrite ?TWL.length_put, ?HL; unfold TQ_DLO, TQ_DHI, TW.A_S_display_sent, TW.A_S_last_display_us, TW.OFF_g_s,
        TW.W_LEN; lia. }
  assert (L1 : length (TW.set_S_display_sent B 1) = Z.to_nat TW.W_LEN) by (destruct K1 as [L _]; rewrite L; exact HL).
  unfold TW.set_S_last_display_us. apply tq_keep_upd; [exact K1 | | | |];
    rewrite ?TWL.length_put, ?L1; unfold TQ_DLO, TQ_DHI, TW.A_S_display_sent, TW.A_S_last_display_us, TW.OFF_g_s,
      TW.W_LEN; lia.
Qed.

Lemma tq_keep_len : forall lo hi B X, tq_keep lo hi B X -> length B = Z.to_nat TW.W_LEN -> length X = Z.to_nat TW.W_LEN.
Proof. intros lo hi B X [L _] HL. rewrite L. exact HL. Qed.

(* A world change inside g_s's queue or its display fields keeps the run invariants (1) and (4) (M.fly and g_cmd,
   g_ncmd lie outside g_s) and g_fail_next. *)
Lemma tq_keep_inv14 : forall lo hi B X, tq_keep lo hi B X -> TW.A_M_fly_len + 8 <= lo -> hi <= TW.OFF_g_cmd ->
  (TW.M_fly_on B <> 0 -> TW.M_fly_len B <= TC.SPEC_MAX_FRAME) ->
  (forall s, 0 <= s < TW.g_ncmd B -> TW.Cmd_st B s = TC.PENDING -> TW.Cmd_len B s <= DSpec.SPEC_CMD_MAX) ->
  (TW.M_fly_on X <> 0 -> TW.M_fly_len X <= TC.SPEC_MAX_FRAME) /\
  (forall s, 0 <= s < TW.g_ncmd X -> TW.Cmd_st X s = TC.PENDING -> TW.Cmd_len X s <= DSpec.SPEC_CMD_MAX).
Proof.
  intros lo hi B X K Hlo Hhi H1 H4.
  assert (E1 : TW.M_fly_on X = TW.M_fly_on B)
    by (unfold TW.M_fly_on; apply (tq_keep_s32 lo hi B X); [exact K | unfold TW.A_M_fly_on, TW.OFF_M; lia |
        unfold TW.A_M_fly_on, TW.A_M_fly_len, TW.OFF_M in *; lia]).
  assert (E2 : TW.M_fly_len X = TW.M_fly_len B)
    by (unfold TW.M_fly_len; apply (tq_keep_u_at lo hi B X); [exact K | unfold TW.A_M_fly_len, TW.OFF_M; lia |
        cbn [Z.of_nat Pos.of_succ_nat]; lia]).
  assert (E3 : TW.g_ncmd X = TW.g_ncmd B)
    by (unfold TW.g_ncmd; apply (tq_keep_u_at lo hi B X); [exact K | unfold TW.OFF_g_ncmd; lia |
        unfold TW.OFF_g_ncmd, TW.OFF_g_cmd in *; lia]).
  split.
  - rewrite E1, E2. exact H1.
  - intros s Hs Hst. rewrite E3 in Hs.
    assert (E4 : TW.Cmd_st X s = TW.Cmd_st B s)
      by (unfold TW.Cmd_st; apply (tq_keep_s32 lo hi B X); [exact K | unfold TW.A_Cmd_st, TW.OFF_g_cmd; lia |
          unfold TW.A_Cmd_st, TW.OFF_g_cmd in *; lia]).
    assert (E5 : TW.Cmd_len X s = TW.Cmd_len B s)
      by (unfold TW.Cmd_len; apply (tq_keep_u_at lo hi B X); [exact K | unfold TW.A_Cmd_len, TW.OFF_g_cmd; lia |
          unfold TW.A_Cmd_len, TW.OFF_g_cmd in *; lia]).
    rewrite E5. apply H4; [exact Hs | rewrite <- E4; exact Hst].
Qed.

Lemma tq_keep_gfn : forall lo hi B X, tq_keep lo hi B X -> hi <= TW.OFF_g_fail_next ->
  TW.g_fail_next X = TW.g_fail_next B.
Proof.
  intros lo hi B X K Hhi. unfold TW.g_fail_next.
  apply (tq_keep_u_at lo hi B X); [exact K | unfold TW.OFF_g_fail_next; lia | right; exact Hhi].
Qed.

(* take_m's results: the 32-bit taken, body_len and has_display in range (TModel/TSessFacts.v take_m_out). *)
Lemma tq_take_out : forall B allow B1 body len hd n,
  TS0.take_m B allow = Some (B1, (body, len, hd, n)) -> 0 <= n < 2 ^ 32 /\ 0 <= len <= 1484 /\ 0 <= hd < 256.
Proof.
  intros B allow B1 body len hd n H.
  exact (OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSessFacts.take_m_out B allow B1 body len hd n H).
Qed.

(* The world after the two display stores, as the code stores them (display_sent, then last_display_us). *)
Lemma tq_tw_dw : forall (rd rd' : Z -> option Z) B1 now,
  tw_at TMAP_B rd B1 ->
  (forall j, (j < 4)%nat -> rd' (TICK_S + 208 + Z.of_nat j) = Some (YO0f.le_byte 1 4 j)) ->
  (forall j, (j < 8)%nat -> rd' (TICK_S + 200 + Z.of_nat j) = Some (YO0f.le_byte now 8 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TICK_S + 200 <= x < TICK_S + 212) -> rd' x = rd x) ->
  tw_at TMAP_B rd' (TW.set_S_last_display_us (TW.set_S_display_sent B1 1) now).
Proof.
  intros rd rd' B1 now Hat HD HL HO.
  assert (CS : TICK_S = TB_g_s) by reflexivity.
  set (rdm := fun x => if ((TICK_S + 200 <=? x) && (x <? TICK_S + 208))%bool then rd x else rd' x).
  assert (H1 : tw_at TMAP_B rdm (TW.set_S_display_sent B1 1)).
  { unfold TW.set_S_display_sent, TW.A_S_display_sent.
    apply (tw_write TMAP_B rd rdm B1 TW.OFF_g_s TB_g_s TW.SZ_g_s 208 4 1 TMAP_B_ok Hat TMAP_B_g_s);
      [lia | unfold TW.SZ_g_s; lia | |].
    - intros j Hj. unfold rdm. rewrite <- CS.
      assert (Hb : ((TICK_S + 200 <=? TICK_S + 208 + Z.of_nat j) && (TICK_S + 208 + Z.of_nat j <? TICK_S + 208))%bool
        = false) by (apply andb_false_iff; right; apply Z.ltb_ge; lia).
      rewrite Hb. exact (HD j Hj).
    - intros x Hx Hn. unfold rdm. rewrite <- CS in Hn.
      destruct ((TICK_S + 200 <=? x) && (x <? TICK_S + 208))%bool eqn:Eb; [reflexivity|].
      apply andb_false_iff in Eb.
      apply HO; [exact Hx |].
      destruct Eb as [Eb | Eb]; [apply Z.leb_gt in Eb | apply Z.ltb_ge in Eb]; cbn [Z.of_nat Pos.of_succ_nat] in Hn; lia. }
  unfold TW.set_S_last_display_us, TW.A_S_last_display_us.
  apply (tw_write TMAP_B rdm rd' _ TW.OFF_g_s TB_g_s TW.SZ_g_s 200 8 now TMAP_B_ok H1 TMAP_B_g_s);
    [lia | unfold TW.SZ_g_s; lia | |].
  - intros j Hj. rewrite <- CS. exact (HL j Hj).
  - intros x Hx Hn. unfold rdm. rewrite <- CS in Hn.
    destruct ((TICK_S + 200 <=? x) && (x <? TICK_S + 208))%bool eqn:Eb; [|reflexivity].
    apply andb_true_iff in Eb. destruct Eb as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    exfalso. apply Hn. cbn [Z.of_nat Pos.of_succ_nat]. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. Machine facts                                                    *)
(* ------------------------------------------------------------------ *)

(* Two side-stack frame counts at a state with the class-5 frame on top are the call's. *)
Lemma tq_count_top : forall c pos l, c <> TICK_CID -> count_cid c ((TICK_CID, pos) :: l) = count_cid c l.
Proof.
  intros c pos l Hc. cbn [count_cid]. destruct (Z.eqb_spec TICK_CID c) as [E|E]; [exfalso; exact (Hc (eq_sym E))|].
  reflexivity.
Qed.

(* The body's shadow after the fill and the store at byte 205: [frame + 160, frame + 1644) is addressable. *)
Lemma tq_ra_body : forall (rd : Z -> option Z) F,
  0 <= F -> F mod 8 = 0 ->
  (forall i, 20 <= i < 205 -> rd (SHADOW_OFF + F / 8 + i) = Some 0) ->
  rd (SHADOW_OFF + F / 8 + 205) = Some 4 ->
  range_addressable rd SHADOW_OFF (F + 160) TAKE_BODY.
Proof.
  intros rd F HF0 HF8 HZ H4.
  apply (block_shadow_range rd SHADOW_OFF (F + 160) 1484 (F + 160) TAKE_BODY); [| lia | unfold TAKE_BODY; lia].
  split; [rewrite Z.add_mod, HF8 by lia; reflexivity|]. split; [lia|].
  intros i Hi. change ((1484 + 7) / 8) with 186 in Hi.
  assert (ES : shadow_of_addr SHADOW_OFF (F + 160) + i = SHADOW_OFF + F / 8 + (20 + i)).
  { unfold shadow_of_addr. pose proof (Z.div_mod F 8 ltac:(lia)) as D. rewrite HF8, Z.add_0_r in D.
    replace (F + 160) with ((F / 8 + 20) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  rewrite ES. change (1484 / 8) with 185. change (1484 mod 8) with 4.
  destruct (Z.ltb_spec i 185) as [Hlt | Hge].
  - apply HZ. lia.
  - replace (20 + i) with 205 by lia. exact H4.
Qed.

(* The awr obligation's regions, computed. *)
Ltac tq_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* A register kept by a run (its symbolic value is its own atom), from the equation Q of its value at the run's
   start, through the equation EE of the valuation's low atoms (TickBKit.v sn_regB). *)
Ltac tq_kreg HS EE r n Q H :=
  lazymatch type of Q with _ = ?v =>
    sn_regB HS r v H ltac:(cbn [sv_denot]; rewrite (EE n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.

(* No shadow entry, and the empty span. *)
Definition TQ_B0 : Z * Z := (0, 0).

(* A run from a state with no region writes nothing. *)
Lemma tq_nr_kept : forall E (H : word -> bool) (m m' : word -> option byte),
  frame_of E [] (mrestrict H m) (mrestrict H m') -> forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
  intros E H m m' HF a Ha. apply (kept_of_frame E [] H m m' (fun _ => False) HF); [|exact Ha | tauto].
  intros b wlo whi x Hin _. cbn in Hin. destruct Hin.
Qed.

(* Every byte send_data may store is a byte of G (send_data_cg.v senddata_wr is a row of tick_wr: TickBKit.v
   tick_wr_G). *)
Lemma tq_sdwr_G : forall a, senddata_wr a -> inG TG.G_HARNESS_B a.
Proof. intros a H. apply (tick_wr_G []). unfold tick_wr. do 19 right. exact H. Qed.

Lemma tq_nth_firstn : forall (l : list Z) k j, (j < k)%nat -> nth j (firstn k l) 0 = nth j l 0.
Proof.
  induction l as [|x l IH]; intros k j Hj.
  - destruct k; cbn; destruct j; reflexivity.
  - destruct k as [|k]; [lia|]. cbn [firstn]. destruct j as [|j]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.

(* The first k bytes of a byte list read at b. *)
Lemma tq_garr8_firstn : forall (m : word -> option byte) b (X : list byte) k,
  garr8 tfibsegs m b (TW.zs X) -> garr8 tfibsegs m b (TW.zs (firstn k X)).
Proof.
  intros m b X k H j Hj. unfold TW.zs in *. rewrite length_map, length_firstn in Hj.
  rewrite <- firstn_map, (tq_nth_firstn _ k j) by lia. apply H. rewrite length_map. lia.
Qed.

(* An n-byte cell of v read as garr8 of put n v is v (TWorldG.v tw_le_byte_put). *)
Lemma tq_val_of_garr8_put : forall (m : word -> option byte) a (n : nat) v,
  garr8 tfibsegs m a (TW.zs (TW.put n v)) -> val_mem tfibsegs m a n v.
Proof.
  intros m a n v H k Hk.
  assert (Hj : (k < length (TW.zs (TW.put n v)))%nat) by (unfold TW.zs; rewrite length_map, TWL.length_put; exact Hk).
  rewrite (garr8_mbyte tfibsegs m a _ k H Hj). f_equal. f_equal. unfold TW.zs.
  rewrite (nth_indep _ 0 ((fun x : byte => bv_unsigned x) (Z_to_bv 8 0))) by (rewrite length_map, TWL.length_put; exact Hk).
  rewrite map_nth. apply tw_le_byte_put. exact Hk.
Qed.

(* The plain walk's branch lemmas (Prog/T/diginet_session_tick.v br_eqb_s, swrap32_eq0). *)
Lemma tq_br_eqb_s : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  destruct (Z.eqb_spec a b) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N. Z.div_mod_to_equations. lia.
Qed.
Lemma tq_swrap32_eq0 : forall n, 0 <= n < 2^32 -> (bv_swrap 32 n =? 0) = (n =? 0).
Proof.
  intros n Hn. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  destruct (Z.eqb_spec n 0) as [->|N]; [reflexivity|]. apply Z.eqb_neq. intros E. apply N.
  Z.div_mod_to_equations. lia.
Qed.
Lemma tq_swrap32_range : forall x, -2^31 <= bv_swrap 32 x < 2^31.
Proof.
  intros x. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  pose proof (Z.mod_pos_bound (x + 2^31) (2^32) ltac:(lia)). lia.
Qed.

(* take's two out cells, body_len at p + 80 and has_display at p + 76. *)
Definition tq_outs (p : Z) : list (Z * Z) := [(p + 80, 8); (p + 76, 4)].
Lemma tq_outs_bounds : forall p a, inG (tq_outs p) a -> p + 76 <= a < p + 88.
Proof.
  intros p a H. unfold inG, tq_outs in H. apply Exists_exists in H as ((b0 & n0) & Hin & Hz).
  unfold in_zr in Hz. cbn [fst snd] in Hz. cbn [In] in Hin.
  destruct Hin as [Hin | [Hin | []]]; injection Hin as <- <-; lia.
Qed.
Lemma tq_outs_in : forall p a, p + 76 <= a < p + 88 -> inG (tq_outs p) a.
Proof.
  intros p a H. unfold inG, tq_outs. apply Exists_exists.
  destruct (Z_lt_le_dec a (p + 80)) as [L | L].
  - exists (p + 76, 4). split; [right; left; reflexivity | unfold in_zr; cbn [fst snd]; lia].
  - exists (p + 80, 8). split; [left; reflexivity | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* The bytes take may store: g_s's, the body's, the two cells'. *)
Lemma tq_take_wr_cases : forall Bw bp blp hdp a, take_wr Bw bp blp hdp a ->
  (TICK_S <= a < TICK_S + TW.SZ_g_s) \/ (bp <= a < bp + TAKE_BODY) \/ (blp <= a < blp + 8) \/ (hdp <= a < hdp + 4).
Proof.
  intros Bw bp blp hdp a H. unfold take_wr in H.
  destruct H as [(q & Hq & _ & Hy) | [Hy | [Hy | [Hy | Hy]]]].
  - left. unfold TICK_S, twb_fld, TW.A_S_queue_bytes, TW.OFF_g_s, TW.SZ_g_s, TW.S_queue_N, TW.S_queue_ESZ in *. lia.
  - left. unfold TICK_S, twb_fld, TW.A_S_queued, TW.OFF_g_s, TW.SZ_g_s in *. lia.
  - right. left. exact Hy.
  - right. right. left. exact Hy.
  - right. right. right. exact Hy.
Qed.

(* take's G stores are stores of tick_wr (its queue rows, widened, and queued). *)
Lemma tq_take_wr_tick : forall Bw Bw' bp blp hdp a, take_wr Bw bp blp hdp a ->
  ~ (bp <= a < bp + TAKE_BODY) -> ~ (blp <= a < blp + 8) -> ~ (hdp <= a < hdp + 4) -> tick_wr Bw' a.
Proof.
  intros Bw Bw' bp blp hdp a H N1 N2 N3. unfold take_wr in H. unfold tick_wr.
  destruct H as [(q & Hq & _ & Hy) | [Hy | [Hy | [Hy | Hy]]]].
  - do 17 right. left. exists q. split; [exact Hq | exact Hy].
  - do 18 right. left. exact Hy.
  - exfalso. exact (N1 Hy).
  - exfalso. exact (N2 Hy).
  - exfalso. exact (N3 Hy).
Qed.

(* The bytes of a stored value, through the view. *)
Lemma tq_aview_of_val : forall (H : word -> bool) (m : word -> option byte) a (n : nat) v j,
  val_mem tfibsegs (mrestrict H m) a n v -> (j < n)%nat ->
  aview tfibsegs H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
  intros H m a n v j Hv Hj. unfold aview. rewrite (Hv j Hj). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small.
  unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

Section qk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).

(* The state at pc with no region: the registers as atoms (SlostHead.v slh_entry5). *)
Lemma tq_entry_nr : forall pc (W : world segs) regs mem,
  st_ok_pi segs VAL (Eimg (PI := PI_transportb) (Ereg regs [])) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros pc W regs mem. rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* The stack facts every segment uses: the journal's window lies at or above alloc_ceiling and below 2 ^ 47, the
   statement's window premise, and sp1 (32-aligned, 192 .. 208 below the entry sp). TICK_STK = 208 + SENDDATA_STK
   and SENDDATA_STK is at least ESTACK and TAKE_STK. *)
Lemma tq_fix_stack : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F,
  tick_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
  alloc_ceiling <= sp0 - STK /\ sp0 - STK <= spZ regs - TICK_STK /\ spZ regs <= sp0 /\ sp0 <= 2 ^ 47 /\
  sp0 mod 16 = 0 /\ spZ regs - 208 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0 /\
  TICK_STK = 208 + SENDDATA_STK /\ ESTACK <= SENDDATA_STK /\ TAKE_STK <= SENDDATA_STK /\ ESTACK = 4096.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F HFIX.
  pose proof HFIX as (HJ0 & _ & _ & _ & _ & _ & _ & Hsp16 & Hlo & Hhi & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    Esp1 & _).
  pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  assert (Hsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0).
  { rewrite Esp1. unfold TICK_FRAME.
    pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)) as D.
    pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)) as M.
    pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
    set (q := (spZ regs - 192) / 32) in *. set (r0 := (spZ regs - 192) mod 32) in *. set (t := spZ regs / 16) in *.
    split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
  split; [lia|]. split; [exact Hlo|]. split; [exact Hhi|]. split; [lia|]. split; [exact Hsp0a|].
  split; [exact (proj1 Hsp1)|]. split; [exact (proj2 Hsp1)|].
  split; [exact tick_stk_eq|]. split; [vm_compute; discriminate|]. split; [vm_compute; discriminate|]. reflexivity.
Qed.

(* TransportGCg.v dk_kept_trans_out_g's last step, for a callee called at a state that holds the walk's own frame
   (dk_kept_trans_nf_g gives the kept fact at the memory with the out cells put back): the walk's kept fact at that
   memory is its kept fact at the memory the callee returned, when the out cells lie in the walk's own window and
   are present there. Kit gap: TransportGCg.v states the fold only for a callee called at the walk's call state. *)
Lemma tq_kept_ungover : forall outs lyc Sc (W : world segs) memc mdc (W2 : world segs) mem2 memX slo shi
    (Eo : Z -> Prop),
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
  (forall a, inG outs a -> slo <= a < shi) ->
  (forall a, inG outs a -> apresent (w_H W2) mem2 a) ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 (gover outs mem2 memX) slo shi Eo ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 slo shi Eo.
Proof.
  intros outs lyc Sc W memc mdc W2 mem2 memX slo shi Eo LAWS HAR Hce Hshi Hout Hpres (K1 & K2 & K3 & K4 & K5 & K6).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HnG : forall a, a < alloc_ceiling -> ~ inG outs a) by (intros a Ha Hin; pose proof (Hout a Hin); lia).
  assert (Hgv : forall a, 0 <= a < 2 ^ 64 -> ~ inG outs a ->
    aview segs (w_H W2) (gover outs mem2 memX) a = aview segs (w_H W2) mem2 a)
    by (intros a Ha Hn; exact (gover_out_aview segs outs (w_H W2) mem2 memX a Ha Hn)).
  assert (Hgp : forall a, 0 <= a < 2 ^ 64 -> ~ inG outs a ->
    apresent (w_H W2) (gover outs mem2 memX) a -> apresent (w_H W2) mem2 a)
    by (intros a Ha Hn Hp; exact (gover_out_apresent outs (w_H W2) mem2 memX a Ha Hn Hp)).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw. assert (Hn : ~ inG outs a) by (intros Hin; pose proof (Hout a Hin); lia).
    rewrite <- (Hgv a ltac:(lia) Hn). exact (K1 a Ha Hw).
  - intros b n i Hb Hi Hn.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b n HAR Hb) as (_ & H4096 & Hbce & _).
    assert (Hno : ~ inG outs (b + i)) by (apply HnG; lia).
    rewrite <- (Hgv (b + i) ltac:(lia) Hno). exact (K2 b n i Hb Hi Hn).
  - intros a Hi HnGg Hno He. pose proof (transportb_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
    assert (Hn : ~ inG outs a) by (apply HnG; lia).
    rewrite <- (Hgv a ltac:(lia) Hn). exact (K3 a Hi HnGg Hno He).
  - intros cid pos a Hin Hr Hn.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    assert (Ha : 0 <= a < alloc_ceiling).
    { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
    assert (Hn2 : ~ inG outs a) by (apply HnG; lia).
    rewrite <- (Hgv a ltac:(lia) Hn2). exact (K4 cid pos a Hin Hr Hn).
  - intros a Ha Hw Hp. assert (Hn : ~ inG outs a) by (intros Hin; pose proof (Hout a Hin); lia).
    apply (Hgp a ltac:(lia) Hn). exact (K5 a Ha Hw Hp).
  - intros a Ha. destruct (inGb outs a) eqn:Eb.
    + exact (Hpres a (proj1 (inGb_spec outs a) Eb)).
    + assert (Hn : ~ inG outs a) by (apply inGb_false; exact Eb).
      apply (Hgp a ltac:(lia) Hn). exact (K6 a Ha).
Qed.


(* tick_cur carried over a step of the walk that changes only bytes of its window below the saved words, of its own
   frame but the frame's last word (and its shadow bytes and flag byte), or of G (TransportGFrame.v dk_kept_nfz_gw
   for what the call keeps; the saved words and the frame's last word are not changed). *)
Lemma tq_cur_step : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw pos F ly2 S2 W2 mem2 md2
    mem3 md3 e (Zs : Z -> Prop),
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS_B -> frame_flag_lawP segs B ->
  @AR rc segs B lyc Sc W memc mdc ->
  alloc_ceiling <= spZ regs - TICK_STK -> spZ regs <= 2 ^ 64 ->
  tick_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly2 S2 W2 mem2 md2 e ->
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 ((TICK_CID, pos) :: own) ly2 S2 W2 mem3 md3 (k + e) ->
  F = frame_addr lyc TICK_CID pos ->
  (forall a, Zs a ->
     (spZ regs - TICK_STK <= a < spZ regs - 104) \/
     (dkg_nf TICK_CID F (flag_addr lyc TICK_CID pos) a /\ ~ (F + TICK_FBYTES - 8 <= a < F + TICK_FBYTES)) \/
     inG TG.G_HARNESS_B a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  tick_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly2 S2 W2 mem3 md3 e.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw pos F ly2 S2 W2 mem2 md2 mem3 md3 e Zs
    LAWS HGX FFL HARc Hce Hshi (HJ & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL) HJ3 EF HZ KP GP.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HTS : 104 <= TICK_STK) by (vm_compute; discriminate).
  assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
    by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm) Hbm)).
  destruct (dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 mem2 md2 TICK_CID pos F
    (flag_addr lyc TICK_CID pos) HAR2 Hfr Hbl HlyF EF eq_refl FFL) as (_ & _ & _ & N4).
  assert (Hin2 : In (TICK_CID, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
  assert (EF2 : frame_addr ly2 TICK_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite HlyF; reflexivity).
  destruct (frames_bounds segs B LAWS ly2 S2 W2 mem2 md2 TICK_CID pos HAR2 Hin2) as (F4096 & Fce & _).
  rewrite EF2 in F4096, Fce. change (fs_frame_bytes TICK_CID) with 2048 in Fce.
  refine (conj HJ3 (conj He (conj Hfr (conj Hperm (conj HlyF (conj HMO (conj _ (conj _ _)))))))).
  - apply (dk_kept_nfz_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc ly2 S2 W memc mdc W2 mem2 md2 mem2 mem3
      (spZ regs - TICK_STK) (spZ regs) TICK_CID pos F (flag_addr lyc TICK_CID pos) (tick_wr Bw) Zs HGX HARc HAR2 Hfr
      Hbl HlyF EF eq_refl FFL).
    + exact Hce.
    + exact Hshi.
    + intros a Ha. destruct (HZ a Ha) as [X | [(X & _) | X]]; [left; lia | right; left; exact X | right; right; exact X].
    + exact HK.
    + exact KP.
    + exact GP.
  - rewrite Forall_forall in HSV |- *. intros o Hin.
    assert (Hob : 8 <= fst o <= 104).
    { unfold TICK_SAVED in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [<- | Hin]; [cbn [fst]; lia|]). destruct Hin. }
    rewrite <- (HSV o Hin). apply rdword_ext.
    intros i Hi. apply KP; [lia|]. intros Hz.
    destruct (HZ _ Hz) as [X | [(X & _) | X]]; [lia | pose proof (N4 _ X); lia |].
    pose proof (inG_low segs B transportb_segs_low _ _ HGX X). unfold kLowMemEnd in *. lia.
  - rewrite <- HFL. apply rdword_ext.
    intros i Hi. unfold TICK_FBYTES in *. apply KP; [lia|]. intros Hz.
    destruct (HZ _ Hz) as [X | [(_ & X) | X]]; [lia | lia |].
    destruct (HGX _ X) as [Hi' _].
    apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 TICK_CID pos (F + 2048 - 8 + i) HAR2 Hin2); [|exact Hi'].
    rewrite EF2. change (fs_frame_bytes TICK_CID) with 2048. lia.
Qed.

(* tick_cur after a G-form callee called at a state (ly2, S2) that holds the walk's own frame, with the callee's window
   [sp1 - XSTK, sp1) below the walk's sp1 and its out cells outs in the walk's own window above sp1 (take's
   [(blp, 8); (hdp, 4)]; [] for send_data): TransportGCg.v dk_kept_trans_nf_g with the own frame and the out cells as
   NF, then tq_kept_ungover; the saved words and the frame's last word are kept by the callee's post. Also: every
   byte of the walk's window above sp1 but the out cells is the one at the call. *)
Lemma tq_cur_call : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw pos F
    ly2 S2 (W2 : world segs) mem2 md2 e ly3 S3 (W3 : world segs) mem3 md3 e3 sp1 XSTK (outs : list (Z * Z))
    (E' : Z -> Prop),
  AR_laws segs B -> ameter_laws MT -> frame_flag_lawP segs B ->
  @AR rc segs B lyc Sc W memc mdc ->
  alloc_ceiling <= spZ regs - TICK_STK -> spZ regs <= 2 ^ 64 ->
  spZ regs - TICK_STK <= sp1 - XSTK -> sp1 <= spZ regs - 104 -> 0 <= XSTK ->
  F = frame_addr lyc TICK_CID pos ->
  tick_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly2 S2 W2 mem2 md2 e ->
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 ((TICK_CID, pos) :: own) ly3 S3 W3 mem3 md3 (k + e + e3) ->
  0 <= e3 <= 0 ->
  frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) ->
  acall_kept_g segs B TG.G_HARNESS_B ly2 S2 W2 mem2 W3 (gover outs mem3 mem2) (sp1 - XSTK) sp1 E' ->
  mo_le MT S2 S3 0 ->
  (forall a, inG outs a -> sp1 <= a < spZ regs - 104) ->
  (forall a, inG outs a -> apresent (w_H W3) mem3 a) ->
  (forall a, E' a -> tick_wr Bw a \/ dkg_nf TICK_CID F (flag_addr lyc TICK_CID pos) a \/ inG outs a) ->
  (forall a, E' a -> ~ (F + TICK_FBYTES - 8 <= a < F + TICK_FBYTES)) ->
  tick_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly3 S3 W3 mem3 md3 (e + e3) /\
  (forall a, sp1 <= a < spZ regs -> ~ inG outs a -> aview segs (w_H W3) mem3 a = aview segs (w_H W2) mem2 a).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw pos F ly2 S2 W2 mem2 md2 e ly3 S3 W3 mem3 md3 e3
    sp1 XSTK outs E' LAWS MTL FFL HARc Hce Hshi Hwlo Hwhi HX0 EF (HJ & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL)
    HJ3 He3 Hfr3 Hperm3 HKC HMO3 Hout Hpres HE HEf.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
  pose proof HJ as (_ & _ & (memS2 & HJi2 & _) & _). rewrite !Z.add_0_r in HJi2.
  pose proof HJi2 as (_ & Hlyle2 & _). pose proof Hlyle2 as (_ & _ & _ & _ & _ & ELF2 & _).
  pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
  pose proof HJi3 as (_ & Hlyle3 & _). pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _).
  clear HJi2 memS2 HJi3 memS3.
  assert (ELF3c : ly_F ly3 = ly_F lyc) by (rewrite ELF3, <- ELF2; exact HlyF).
  assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
    by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm) Hbm)).
  assert (Hfa : forall cid p, frame_addr ly2 cid p = frame_addr lyc cid p)
    by (intros cid p; unfold frame_addr; rewrite HlyF; reflexivity).
  destruct (dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 mem2 md2 TICK_CID pos F
    (flag_addr lyc TICK_CID pos) HAR2 Hfr Hbl HlyF EF eq_refl FFL) as (N1 & _ & N3 & N4).
  assert (Hin2 : In (TICK_CID, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
  assert (EF2 : frame_addr ly2 TICK_CID pos = F) by (rewrite Hfa; exact (eq_sym EF)).
  destruct (frames_bounds segs B LAWS ly2 S2 W2 mem2 md2 TICK_CID pos HAR2 Hin2) as (F4096 & Fce & _).
  rewrite EF2 in F4096, Fce. change (fs_frame_bytes TICK_CID) with 2048 in Fce.
  assert (Hgv : forall a, 0 <= a < 2 ^ 64 -> ~ inG outs a ->
    aview segs (w_H W3) (gover outs mem3 mem2) a = aview segs (w_H W3) mem3 a)
    by (intros a Ha Hn; exact (gover_out_aview segs outs (w_H W3) mem3 mem2 a Ha Hn)).
  pose proof HKC as (L1 & _ & _ & L4 & _).
  (* the caller's kept fact at the memory with the out cells put back, then at mem3 *)
  assert (KG : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 (gover outs mem3 mem2) (spZ regs - TICK_STK) (spZ regs)
    (tick_wr Bw)).
  { apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc ly2 S2 W memc W2 mem2 W3 (gover outs mem3 mem2)
      (spZ regs - TICK_STK) (spZ regs) (sp1 - XSTK) sp1 (tick_wr Bw) E'
      (fun a => dkg_nf TICK_CID F (flag_addr lyc TICK_CID pos) a \/ inG outs a)).
    - exact Hce.
    - exact Hshi.
    - exact Hfa.
    - intros f Hf. rewrite Hfr. right. exact Hf.
    - exact Hbl.
    - intros b m i Hb Hi [Hn | Hn]; [exact (N1 b m i Hb Hi Hn)|].
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HARc Hb) as (_ & H4096 & Hbce & _).
      pose proof (Hout _ Hn). lia.
    - intros c p a Hin Hr [Hn | Hn]; [exact (N3 c p a Hin Hr Hn)|].
      pose proof (Hout _ Hn) as Ho.
      destruct (frames_bounds segs B LAWS lyc Sc W memc mdc c p HARc Hin) as (G4096 & Gce & _).
      pose proof (fs_frame_bytes_nonneg c) as Hfs.
      destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc c p) (fs_frame_bytes c) Hfs) as Hse.
      assert (Hd : (frame_addr lyc c p + fs_frame_bytes c) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
    - exact HK.
    - exact HKC.
    - lia.
    - lia.
    - intros a Ha. destruct (HE a Ha) as [X | X]; [left; exact X | right; exact X]. }
  assert (KG3 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 mem3 (spZ regs - TICK_STK) (spZ regs) (tick_wr Bw)).
  { apply (tq_kept_ungover outs lyc Sc W memc mdc W3 mem3 mem2 (spZ regs - TICK_STK) (spZ regs) (tick_wr Bw) LAWS HARc
      Hce Hshi); [| exact Hpres | exact KG].
    intros a Ha. pose proof (Hout a Ha). lia. }
  assert (KW : forall a, sp1 <= a < spZ regs -> ~ inG outs a -> aview segs (w_H W3) mem3 a = aview segs (w_H W2) mem2 a).
  { intros a Ha Hn. rewrite <- (Hgv a ltac:(lia) Hn). apply L1; lia. }
  split; [|exact KW].
  refine (conj _ (conj _ (conj _ (conj _ (conj ELF3c (conj _ (conj KG3 (conj _ _)))))))).
  - replace (k + (e + e3)) with (k + e + e3) by lia. exact HJ3.
  - unfold TICK_EV in *. lia.
  - rewrite Hfr3. exact Hfr.
  - exact (Permutation_trans Hperm3 Hperm).
  - exact (mo_le_trans MT MTL _ _ _ _ _ HMO HMO3).
  - rewrite Forall_forall in HSV |- *. intros o Hin.
    assert (Hob : 8 <= fst o <= 104).
    { unfold TICK_SAVED in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [<- | Hin]; [cbn [fst]; lia|]). destruct Hin. }
    rewrite <- (HSV o Hin). apply rdword_ext.
    intros i Hi. apply KW; [lia|]. intros Ho. pose proof (Hout _ Ho). lia.
  - rewrite <- HFL. apply rdword_ext.
    intros i Hi. unfold TICK_FBYTES in *.
    assert (Hn : ~ inG outs (F + 2048 - 8 + i)) by (intros Ho; pose proof (Hout _ Ho); lia).
    rewrite <- (Hgv (F + 2048 - 8 + i) ltac:(lia) Hn).
    apply (L4 TICK_CID pos _ Hin2); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EF2;
      change (fs_frame_bytes TICK_CID) with 2048; lia |].
    intros HE'. exact (HEf _ HE' ltac:(unfold TICK_FBYTES; lia)).
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The points inside the piece                                      *)
(* ------------------------------------------------------------------ *)

(* The registers from +0x6c8 on: the base ones, s3 = the frame's shadow address, s4 = s, s5 = the shadow address of
   s + 208 (display_sent, +0x6b4 .. +0x6b8), s6 = the body's shadow address (the frame's shadow byte 20), s7 = s + 200
   (last_display_us, +0x6c8), s8 = the shadow base. *)
Definition tq_regs (regs regs2 : bvmap 5 word) (sp1 F : Z) : Prop :=
  tick_regs_base regs regs2 sp1 F /\
  YK11.getr regs2 19 = w64 (SHADOW_OFF + F / 8) /\ YK11.getr regs2 20 = w64 TICK_S /\
  YK11.getr regs2 21 = w64 (SHADOW_OFF + (TICK_S + 208) / 8) /\
  YK11.getr regs2 22 = w64 (SHADOW_OFF + F / 8 + 20) /\ YK11.getr regs2 23 = w64 (TICK_S + 200) /\
  YK11.getr regs2 24 = w64 SHADOW_OFF.

(* +0x834: s10 = the result; a1 = 186, a0 = s6, `jal __asan_set_shadow_f8`, `j` to the epilogue cut. *)
Definition tq_f8_at : Prop :=
  tick_laws B MT -> tick_callees B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate)
         (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    tick_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    tick_epi_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' pos F ly2 S2 W2 mem2 md2 e ->
    tick_regs_epi regs regs2 sp1 F r -> YK11.getr regs2 22 = w64 (SHADOW_OFF + F / 8 + 20) ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + TQ_F8)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_tick_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

(* +0x814: the display stores done (world Bs); a2 = body_len (sp1 + 80), a0 = s, a1 = body, a4 = now, `jal
   send_data` with a3 = n, s10 = its result, to +0x834. *)
Definition tq_sd_at : Prop :=
  tick_laws B MT -> tick_callees B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (Bs body X : list byte) (len n : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    tick_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    tick_run_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F ly2 S2 W2 mem2 md2 e ->
    tw_at TMAP_B (aview segs (w_H W2) mem2) Bs -> TW.g_fail_next Bs <= 1 ->
    (TW.M_fly_on Bs <> 0 -> TW.M_fly_len Bs <= TC.SPEC_MAX_FRAME) ->
    (forall s, 0 <= s < TW.g_ncmd Bs -> TW.Cmd_st Bs s = TC.PENDING -> TW.Cmd_len Bs s <= DSpec.SPEC_CMD_MAX) ->
    TSS.send_data_m timg_B TF Bs (firstn (Z.to_nat len) body) n now = Some (Bw', r) ->
    0 <= len <= TAKE_BODY -> 0 <= n < 2 ^ 32 ->
    length X = Z.to_nat TAKE_BODY -> firstn (Z.to_nat len) X = firstn (Z.to_nat len) body ->
    garr8 segs (mrestrict (w_H W2) mem2) (F + 160) (TW.zs X) ->
    rdword (aview segs (w_H W2) mem2) (sp1 + 80) = Some len ->
    (forall i, 20 <= i < 205 -> aview segs (w_H W2) mem2 (SHADOW_OFF + F / 8 + i) = Some 0) ->
    aview segs (w_H W2) mem2 (SHADOW_OFF + F / 8 + 205) = Some 4 ->
    tq_regs regs regs2 sp1 F -> YK11.getr regs2 25 = w64 (F + 160) -> YK11.getr regs2 13 = w64 (bv_swrap 32 n) ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + TQ_SD)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_tick_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

(* +0x7dc: take returned (a0 = the 32-bit taken; body_len at sp1 + 80, has_display at sp1 + 76): the taken test,
   has_display, the display stores, to +0x814 or (nothing taken) to +0x834 with s10 = 0. *)
Definition tq_tk_at : Prop :=
  tick_laws B MT -> tick_callees B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (B0 B1 body X : list byte) (allow len hd n : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    tick_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    tick_run_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F ly2 S2 W2 mem2 md2 e ->
    tw_at TMAP_B (aview segs (w_H W2) mem2) B1 -> TW.g_fail_next B1 <= 1 ->
    tick_runinv B0 -> length B0 = Z.to_nat TW.W_LEN ->
    TS0.take_m B0 allow = Some (B1, (body, len, hd, n)) ->
    tq_after_take timg_B TF B1 body len hd n now = Some (Bw', r) ->
    length X = Z.to_nat TAKE_BODY -> firstn (Z.to_nat len) X = firstn (Z.to_nat len) body ->
    garr8 segs (mrestrict (w_H W2) mem2) (F + 160) (TW.zs X) ->
    garr8 segs (mrestrict (w_H W2) mem2) (sp1 + 80) (TW.zs (TW.put 8 len)) ->
    garr8 segs (mrestrict (w_H W2) mem2) (sp1 + 76) (TW.zs (TW.put 4 hd)) ->
    (forall i, 20 <= i < 205 -> aview segs (w_H W2) mem2 (SHADOW_OFF + F / 8 + i) = Some 0) ->
    aview segs (w_H W2) mem2 (SHADOW_OFF + F / 8 + 205) = Some 4 ->
    tq_regs regs regs2 sp1 F -> YK11.getr regs2 25 = w64 (F + 160) -> YK11.getr regs2 10 = w64 (bv_swrap 32 n) ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + TQ_TK)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_tick_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

(* +0x7ac: the display test done (s10 = allow, s5 and s7 set): s9 = body, the fill of the body's shadow (`jal
   __asan_set_shadow_00`), the shadow byte 205 = 4, `jal take`, to +0x7dc. *)
Definition tq_body_at : Prop :=
  tick_laws B MT -> tick_callees B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (now r : Z)
         (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (B0 : list byte) (allow : Z)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z)
         (regs2 : bvmap 5 word),
    tick_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ->
    tick_run_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F ly2 S2 W2 mem2 md2 e ->
    tw_at TMAP_B (aview segs (w_H W2) mem2) B0 -> TW.g_fail_next B0 <= 1 -> tick_runinv B0 ->
    0 <= allow <= 1 ->
    tq_take_cont timg_B TF B0 allow now = Some (Bw', r) ->
    tq_regs regs regs2 sp1 F -> YK11.getr regs2 26 = w64 allow ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + TQ_BODY)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_tick_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

End qk.
