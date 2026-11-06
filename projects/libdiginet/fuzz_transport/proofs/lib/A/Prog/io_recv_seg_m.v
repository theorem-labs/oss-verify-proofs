(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 579 of its 683 lines of code are new or changed and 822 lines of the source are left out. *)
(* io_recv_seg_m: the model facts and the symbolic entry state of the machine walk of io_recv (io_recv_cgW.v).
   - ir_keep / ir_mrx_keep / ir_mtick_keep: m_rx_m and m_tick_m change no world byte outside ir_wo, the offsets of
     m_rx_cg.v mrx_wr (m_tick_m's writes are m_lost_m's, all among them); ir_wo_mrx turns an offset of ir_wo into an
     address of mrx_wr; ir_G_kept reads a byte of G the callees did not write through the world relation at their
     world; ir_grx_keep: g_rx is not among them.
   - ir_m_fail / ir_m_zero / ir_m_main: TCb.v io_recv_m's three branches.
   - ss_ir: the symbolic state at the entry (the frame and the four globals the code reads; the three aliases of the
     addresses the code forms from an auipc high part and an immediate).
   - the branch conditions at the valuation. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
m_lost_cg m_rx_cg m_tick_cg check_state_data_cg io_recv_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TSess0 TCb TImg TWorldLemmas TIoRecv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TIR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TIoRecv.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.

(* ------------------------------------------------------------------ *)
(* The world bytes m_rx_m and m_tick_m may change                      *)
(* ------------------------------------------------------------------ *)

Definition ir_rng (A n x : Z) : Prop := A <= x < A + n.

(* The offsets in the world of m_rx_cg.v mrx_wr, field by field, the two indexed arrays first (m_tick_m's writes are
   m_lost_m's: M.desk_counter_valid, M.fly_on and m_set's M.state, OW.n, OW.t[OW.n], all among these). *)
Definition ir_wo (x : Z) : Prop :=
  (exists i, 0 <= i < TC.TRANS_MAX /\ ir_rng (TW.A_OW_t_state i) TW.OW_t_ESZ x) \/
  (exists j, 0 <= j < TW.OW_dn_N /\ ir_rng (TC.A_OW_dn_body j) 22 x) \/
  ir_rng TW.A_M_desk_known 4 x \/ ir_rng TW.A_M_desk 6 x \/ ir_rng TW.A_M_state 4 x \/
  ir_rng TW.A_M_e2_acked 8 x \/ ir_rng TW.A_M_foreign 4 x \/ ir_rng TW.A_M_last_rx 8 x \/
  ir_rng TW.A_M_wake_sent 8 x \/ ir_rng TW.A_M_next_ka 8 x \/ ir_rng TW.A_M_backoff_until 8 x \/
  ir_rng TW.A_M_desk_counter_valid 4 x \/ ir_rng TW.A_M_desk_counter 4 x \/ ir_rng TW.A_M_fail 4 x \/
  ir_rng TW.A_M_fly_on 4 x \/ ir_rng TW.A_OW_n 4 x \/ ir_rng TW.A_OW_e2 4 x \/ ir_rng TW.A_OW_acks 4 x \/
  ir_rng TW.A_OW_desk 4 x \/ ir_rng TW.A_OW_foreign 4 x \/ ir_rng TW.A_OW_acked 4 x \/
  ir_rng TW.A_OW_ndata 4 x \/ ir_rng TW.A_OW_acked_counter 4 x \/ ir_rng TW.A_OW_acked_retry 4 x \/
  ir_rng TW.A_OW_desk_off 4 x \/ ir_rng TW.A_OW_desk_p 8 x \/ ir_rng TW.A_OW_desk_body 8 x.

(* B' has the length of B and every byte of B outside ir_wo. *)
Definition ir_keep (B B' : list byte) : Prop :=
  length B' = length B /\
  forall x, 0 <= x -> ~ ir_wo x -> nth (Z.to_nat x) B' (Z_to_bv 8 0) = nth (Z.to_nat x) B (Z_to_bv 8 0).

Lemma ir_keep_refl : forall B, ir_keep B B.
Proof. intros B. split; [reflexivity | intros; reflexivity]. Qed.

Lemma ir_keep_trans : forall B1 B2 B3, ir_keep B1 B2 -> ir_keep B2 B3 -> ir_keep B1 B3.
Proof.
intros B1 B2 B3 [L1 K1] [L2 K2]. split; [rewrite L2; exact L1|].
intros x Hx Hn. rewrite (K2 x Hx Hn). exact (K1 x Hx Hn).
Qed.

Lemma ir_keep_upd : forall B0 X k v, ir_keep B0 X -> 0 <= k ->
  k + Z.of_nat (length v) <= Z.of_nat (length B0) ->
  (forall j, k <= j < k + Z.of_nat (length v) -> ir_wo j) ->
  ir_keep B0 (TW.upd X k v).
Proof.
intros B0 X k v [L K] Hk Hl Hin. split.
- rewrite TWL.length_upd; [exact L | exact Hk | rewrite L; exact Hl].
- intros x Hx Hn. rewrite tw_nth_upd_out; [exact (K x Hx Hn) | exact Hk | rewrite L; exact Hl | exact Hx |].
  intros Hr. exact (Hn (Hin x Hr)).
Qed.

(* the same with the field's nominal width L, which ir_go reads off the setter *)
Lemma ir_keep_updL : forall B0 X k v (L : nat), ir_keep B0 X -> 0 <= k -> (length v <= L)%nat ->
  k + Z.of_nat L <= Z.of_nat (length B0) ->
  (forall j, k <= j < k + Z.of_nat L -> ir_wo j) ->
  ir_keep B0 (TW.upd X k v).
Proof.
intros B0 X k v L HK Hk HvL HL Hin. apply (ir_keep_upd B0 X k v HK Hk); [lia|].
intros j Hj. apply Hin. lia.
Qed.

(* The bytes of a span outside ir_wo are the same in the two worlds. *)
Lemma ir_keep_sub : forall B B' k (m : nat), ir_keep B B' -> 0 <= k ->
  k + Z.of_nat m <= Z.of_nat (length B) ->
  (forall j, k <= j < k + Z.of_nat m -> ~ ir_wo j) ->
  TW.sub B' k m = TW.sub B k m.
Proof.
intros B B' k m [L K] Hk Hl Hn.
assert (Ls : forall l : list byte, Z.of_nat (length l) = Z.of_nat (length B) -> length (TW.sub l k m) = m)
  by (intros l Hll; apply TWL.length_sub; lia).
apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)); [rewrite !Ls by lia; reflexivity|].
intros j Hj. rewrite Ls in Hj by lia.
rewrite !tw_nth_sub by (rewrite ?L; lia).
replace (Z.to_nat k + j)%nat with (Z.to_nat (k + Z.of_nat j)) by lia.
apply K; [lia|]. apply Hn. lia.
Qed.

(* ---- the setters: each write lies in ir_wo ---- *)

(* the fields of ir_wo that are not an array entry, with their width *)
Definition ir_flds : list (Z * Z) :=
  [(TW.A_M_desk_known, 4);
   (TW.A_M_desk, 6);
   (TW.A_M_state, 4);
   (TW.A_M_e2_acked, 8);
   (TW.A_M_e2_acked, 4);
   (TW.A_M_e1_us, 4);
   (TW.A_M_foreign, 4);
   (TW.A_M_last_rx, 8);
   (TW.A_M_wake_sent, 8);
   (TW.A_M_next_ka, 8);
   (TW.A_M_backoff_until, 8);
   (TW.A_M_desk_counter_valid, 4);
   (TW.A_M_desk_counter, 4);
   (TW.A_M_fail, 4);
   (TW.A_M_fly_on, 4);
   (TW.A_OW_n, 4);
   (TW.A_OW_e2, 4);
   (TW.A_OW_acks, 4);
   (TW.A_OW_desk, 4);
   (TW.A_OW_foreign, 4);
   (TW.A_OW_acked, 4);
   (TW.A_OW_ndata, 4);
   (TW.A_OW_acked_counter, 4);
   (TW.A_OW_acked_retry, 4);
   (TW.A_OW_desk_off, 4);
   (TW.A_OW_desk_p, 8);
   (TW.A_OW_desk_body, 8)].

Ltac ir_offg :=
  unfold ir_wo, ir_rng, TW.A_M_desk_known, TW.A_M_desk, TW.A_M_state, TW.A_M_e2_acked, TW.A_M_e1_us,
    TW.A_M_foreign, TW.A_M_last_rx, TW.A_M_wake_sent, TW.A_M_next_ka, TW.A_M_backoff_until,
    TW.A_M_desk_counter_valid, TW.A_M_desk_counter, TW.A_M_fail, TW.A_M_fly_on, TW.A_OW_n, TW.A_OW_t_state,
    TW.A_OW_t_old, TW.A_OW_t_reason, TW.A_OW_e2, TW.A_OW_acks, TW.A_OW_desk, TW.A_OW_foreign, TW.A_OW_acked,
    TW.A_OW_ndata, TW.A_OW_acked_counter, TW.A_OW_acked_retry, TW.A_OW_desk_off, TW.A_OW_desk_p,
    TW.A_OW_desk_body, TW.OW_t_ESZ, TW.OW_dn_N, TC.A_OW_dn_body, TC.A_OW_dn_len, TC.A_OW_dn_counter,
    TC.A_OW_dn_retry, TC.TRANS_MAX, TW.OFF_M, TW.OFF_OW, TW.W_LEN.

Ltac ir_offs := ir_offg; unfold ir_wo, ir_rng, TW.A_M_desk_known, TW.A_M_desk, TW.A_M_state, TW.A_M_e2_acked,
    TW.A_M_e1_us, TW.A_M_foreign, TW.A_M_last_rx, TW.A_M_wake_sent, TW.A_M_next_ka, TW.A_M_backoff_until,
    TW.A_M_desk_counter_valid, TW.A_M_desk_counter, TW.A_M_fail, TW.A_M_fly_on, TW.A_OW_n, TW.A_OW_t_state,
    TW.A_OW_t_old, TW.A_OW_t_reason, TW.A_OW_e2, TW.A_OW_acks, TW.A_OW_desk, TW.A_OW_foreign, TW.A_OW_acked,
    TW.A_OW_ndata, TW.A_OW_acked_counter, TW.A_OW_acked_retry, TW.A_OW_desk_off, TW.A_OW_desk_p,
    TW.A_OW_desk_body, TW.OW_t_ESZ, TW.OW_dn_N, TC.A_OW_dn_body, TC.A_OW_dn_len, TC.A_OW_dn_counter,
    TC.A_OW_dn_retry, TC.TRANS_MAX, TW.OFF_M, TW.OFF_OW, TW.W_LEN in *.

Lemma ir_wo_fld : forall A L x, A <= x < A + L -> In (A, L) ir_flds -> ir_wo x.
Proof.
intros A L x Hx Hin. unfold ir_flds in Hin. cbn [In] in Hin.
destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|Hin]]]]]]]]]]]]]]]]]]]]]]]]]]];
  [ injection Hin as <- <-; do 2 right; left; ir_offs; lia
  | injection Hin as <- <-; do 3 right; left; ir_offs; lia
  | injection Hin as <- <-; do 4 right; left; ir_offs; lia
  | injection Hin as <- <-; do 5 right; left; ir_offs; lia
  | injection Hin as <- <-; do 5 right; left; ir_offs; lia
  | injection Hin as <- <-; do 5 right; left; ir_offs; lia
  | injection Hin as <- <-; do 6 right; left; ir_offs; lia
  | injection Hin as <- <-; do 7 right; left; ir_offs; lia
  | injection Hin as <- <-; do 8 right; left; ir_offs; lia
  | injection Hin as <- <-; do 9 right; left; ir_offs; lia
  | injection Hin as <- <-; do 10 right; left; ir_offs; lia
  | injection Hin as <- <-; do 11 right; left; ir_offs; lia
  | injection Hin as <- <-; do 12 right; left; ir_offs; lia
  | injection Hin as <- <-; do 13 right; left; ir_offs; lia
  | injection Hin as <- <-; do 14 right; left; ir_offs; lia
  | injection Hin as <- <-; do 15 right; left; ir_offs; lia
  | injection Hin as <- <-; do 16 right; left; ir_offs; lia
  | injection Hin as <- <-; do 17 right; left; ir_offs; lia
  | injection Hin as <- <-; do 18 right; left; ir_offs; lia
  | injection Hin as <- <-; do 19 right; left; ir_offs; lia
  | injection Hin as <- <-; do 20 right; left; ir_offs; lia
  | injection Hin as <- <-; do 21 right; left; ir_offs; lia
  | injection Hin as <- <-; do 22 right; left; ir_offs; lia
  | injection Hin as <- <-; do 23 right; left; ir_offs; lia
  | injection Hin as <- <-; do 24 right; left; ir_offs; lia
  | injection Hin as <- <-; do 25 right; left; ir_offs; lia
  | injection Hin as <- <-; do 26 right; ir_offs; lia
  | destruct Hin ].
Qed.

Lemma ir_wo_fld_bnd : forall A L, In (A, L) ir_flds -> 0 <= A /\ A + L <= TW.W_LEN.
Proof.
intros A L Hin. unfold ir_flds in Hin. cbn [In] in Hin.
repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; ir_offg; lia |]). destruct Hin.
Qed.

Lemma ir_wo_ts : forall i x, TW.A_OW_t_state i <= x < TW.A_OW_t_state i + 4 -> 0 <= i < TC.TRANS_MAX -> ir_wo x.
Proof. intros i x Hx Hi. left. exists i. split; [exact Hi | ir_offs; lia]. Qed.
Lemma ir_bnd_ts : forall i, 0 <= i < TC.TRANS_MAX -> 0 <= TW.A_OW_t_state i /\ TW.A_OW_t_state i + 4 <= TW.W_LEN.
Proof. intros i Hi. ir_offs; lia. Qed.
Lemma ir_wo_to : forall i x, TW.A_OW_t_old i <= x < TW.A_OW_t_old i + 4 -> 0 <= i < TC.TRANS_MAX -> ir_wo x.
Proof. intros i x Hx Hi. left. exists i. split; [exact Hi | ir_offs; lia]. Qed.
Lemma ir_bnd_to : forall i, 0 <= i < TC.TRANS_MAX -> 0 <= TW.A_OW_t_old i /\ TW.A_OW_t_old i + 4 <= TW.W_LEN.
Proof. intros i Hi. ir_offs; lia. Qed.
Lemma ir_wo_tr : forall i x, TW.A_OW_t_reason i <= x < TW.A_OW_t_reason i + 4 -> 0 <= i < TC.TRANS_MAX -> ir_wo x.
Proof. intros i x Hx Hi. left. exists i. split; [exact Hi | ir_offs; lia]. Qed.
Lemma ir_bnd_tr : forall i, 0 <= i < TC.TRANS_MAX -> 0 <= TW.A_OW_t_reason i /\ TW.A_OW_t_reason i + 4 <= TW.W_LEN.
Proof. intros i Hi. ir_offs; lia. Qed.
Lemma ir_wo_db : forall i x, TC.A_OW_dn_body i <= x < TC.A_OW_dn_body i + 8 -> 0 <= i < 2 -> ir_wo x.
Proof. intros i x Hx Hi. right; left. exists i. split; [ir_offs; lia | ir_offs; lia]. Qed.
Lemma ir_bnd_db : forall i, 0 <= i < 2 -> 0 <= TC.A_OW_dn_body i /\ TC.A_OW_dn_body i + 8 <= TW.W_LEN.
Proof. intros i Hi. ir_offs; lia. Qed.
Lemma ir_wo_dl : forall i x, TC.A_OW_dn_len i <= x < TC.A_OW_dn_len i + 8 -> 0 <= i < 2 -> ir_wo x.
Proof. intros i x Hx Hi. right; left. exists i. split; [ir_offs; lia | ir_offs; lia]. Qed.
Lemma ir_bnd_dl : forall i, 0 <= i < 2 -> 0 <= TC.A_OW_dn_len i /\ TC.A_OW_dn_len i + 8 <= TW.W_LEN.
Proof. intros i Hi. ir_offs; lia. Qed.
Lemma ir_wo_dc : forall i x, TC.A_OW_dn_counter i <= x < TC.A_OW_dn_counter i + 4 -> 0 <= i < 2 -> ir_wo x.
Proof. intros i x Hx Hi. right; left. exists i. split; [ir_offs; lia | ir_offs; lia]. Qed.
Lemma ir_bnd_dc : forall i, 0 <= i < 2 -> 0 <= TC.A_OW_dn_counter i /\ TC.A_OW_dn_counter i + 4 <= TW.W_LEN.
Proof. intros i Hi. ir_offs; lia. Qed.
Lemma ir_wo_dr : forall i x, TC.A_OW_dn_retry i <= x < TC.A_OW_dn_retry i + 2 -> 0 <= i < 2 -> ir_wo x.
Proof. intros i x Hx Hi. right; left. exists i. split; [ir_offs; lia | ir_offs; lia]. Qed.
Lemma ir_bnd_dr : forall i, 0 <= i < 2 -> 0 <= TC.A_OW_dn_retry i /\ TC.A_OW_dn_retry i + 2 <= TW.W_LEN.
Proof. intros i Hi. ir_offs; lia. Qed.

Ltac ir_setters :=
  unfold TW.set_OW_t_reason, TW.set_OW_t_old, TW.set_OW_t_state, TW.set_M_state, TW.set_OW_n,
    TW.set_M_desk_counter_valid, TW.set_M_fly_on, TW.set_M_e1_us, TW.set_M_e2_acked, TW.set_M_wake_sent,
    TW.set_OW_e2, TW.set_M_fail, TW.set_M_next_ka, TW.set_OW_desk_off, TW.set_OW_desk, TW.set_OW_desk_body,
    TW.set_OW_desk_p, TW.set_M_foreign, TW.set_OW_foreign, TW.set_OW_acked, TW.set_OW_acked_counter,
    TW.set_OW_acked_retry, TW.set_M_backoff_until, TW.set_OW_acks, TW.set_M_desk_counter, TC.set_OW_dn_body,
    TC.set_OW_dn_len, TC.set_OW_dn_counter, TC.set_OW_dn_retry, TW.set_OW_ndata, TW.set_M_last_rx,
    TW.set_M_desk_known, TW.set_M_desk in *.

(* the branch facts as propositions, for lia *)
Ltac ir_bools :=
  repeat match goal with
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  end.

Ltac ir_inlist := solve [ cbn [ir_flds In]; repeat (first [ left; reflexivity | right ]) ].

Ltac ir_in :=
  let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj;
  first
  [ eapply ir_wo_fld; [exact Hj | ir_inlist]
  | eapply ir_wo_ts; [exact Hj | ir_bools; lia]
  | eapply ir_wo_to; [exact Hj | ir_bools; lia]
  | eapply ir_wo_tr; [exact Hj | ir_bools; lia]
  | eapply ir_wo_db; [exact Hj | ir_bools; lia]
  | eapply ir_wo_dl; [exact Hj | ir_bools; lia]
  | eapply ir_wo_dc; [exact Hj | ir_bools; lia]
  | eapply ir_wo_dr; [exact Hj | ir_bools; lia] ].

Ltac ir_bnd :=
  first
  [ eapply ir_wo_fld_bnd; ir_inlist
  | eapply ir_bnd_ts; ir_bools; lia
  | eapply ir_bnd_to; ir_bools; lia
  | eapply ir_bnd_tr; ir_bools; lia
  | eapply ir_bnd_db; ir_bools; lia
  | eapply ir_bnd_dl; ir_bools; lia
  | eapply ir_bnd_dc; ir_bools; lia
  | eapply ir_bnd_dr; ir_bools; lia ].

Ltac ir_width v :=
  lazymatch v with
  | TW.put ?m _ => constr:(m)
  | TW.sub _ _ ?m => constr:(m)
  end.

Ltac ir_len := first [ rewrite TWL.length_put; lia | apply TWL.length_sub_le ].

Ltac ir_go :=
  lazymatch goal with
  | |- ir_keep ?B0 (TW.upd ?X ?kk ?v) =>
      let L := ir_width v in
      apply (ir_keep_updL B0 X kk v L);
      [ ir_go
      | let H := fresh "Hb" in assert (H : 0 <= kk /\ kk + Z.of_nat L <= TW.W_LEN) by ir_bnd; lia
      | ir_len
      | let H := fresh "Hb" in assert (H : 0 <= kk /\ kk + Z.of_nat L <= TW.W_LEN) by ir_bnd; lia
      | ir_in ]
  | |- ir_keep ?B0 ?X =>
      first [ match goal with H : ir_keep B0 X |- _ => exact H end
            | lazymatch X with B0 => apply ir_keep_refl end ]
  end.

Ltac ir_k := ir_setters; ir_go.

(* split a model equation at each branch, innermost first *)
Ltac ir_split H :=
  repeat (cbv beta iota zeta in H;
    lazymatch type of H with
    | None = Some _ => discriminate H
    | Some _ = Some _ => fail
    | _ =>
        match type of H with
        | context [match ?c with _ => _ end] =>
            lazymatch c with
            | context [match _ with _ => _ end] => fail
            | _ => tryif is_var c then destruct c else (let E := fresh "E" in destruct c eqn:E)
            end
        end
    end).

Lemma ir_mset_keep : forall B0, Z.of_nat (length B0) = TW.W_LEN ->
  forall B B' st why u, ir_keep B0 B -> TC.m_set_m B st why = Some (B', u) -> ir_keep B0 B'.
Proof.
intros B0 HL B B' st why u HK H. unfold TC.m_set_m in H.
ir_split H; apply TIR.some_pair_inv in H as [<- _]; ir_k.
Qed.

Lemma ir_mlost_keep : forall B0, Z.of_nat (length B0) = TW.W_LEN ->
  forall B B' why u, ir_keep B0 B -> TC.m_lost_m B why = Some (B', u) -> ir_keep B0 B'.
Proof.
intros B0 HL B B' why u HK H. unfold TC.m_lost_m in H.
refine (ir_mset_keep B0 HL _ B' TC.S_IDLE why u _ H). ir_k.
Qed.

Lemma ir_monline_keep : forall B0, Z.of_nat (length B0) = TW.W_LEN ->
  forall B B' u, ir_keep B0 B -> TC.m_maybe_online_m B = Some (B', u) -> ir_keep B0 B'.
Proof.
intros B0 HL B B' u HK H. unfold TC.m_maybe_online_m in H. ir_split H.
- refine (ir_mset_keep B0 HL _ B' TC.S_ONLINE TC.R_ONLINE u _ H). ir_k.
- apply TIR.some_pair_inv in H as [<- _]. exact HK.
Qed.

Lemma ir_mtick_keep : forall B0, Z.of_nat (length B0) = TW.W_LEN ->
  forall B B' u, ir_keep B0 B -> TC.m_tick_m B = Some (B', u) -> ir_keep B0 B'.
Proof.
intros B0 HL B B' u HK H. unfold TC.m_tick_m in H. ir_split H.
all: first [ exact (ir_mlost_keep B0 HL B B' _ u HK H)
           | (apply TIR.some_pair_inv in H as [<- _]; exact HK) ].
Qed.

Ltac ir_calls B0 HL :=
  repeat match goal with
  | E : TC.m_set_m ?Y _ _ = Some (?Z, _) |- _ =>
      let K := fresh "K" in assert (K : ir_keep B0 Z) by (refine (ir_mset_keep B0 HL Y Z _ _ _ _ E); ir_k); clear E
  | E : TC.m_lost_m ?Y _ = Some (?Z, _) |- _ =>
      let K := fresh "K" in assert (K : ir_keep B0 Z) by (refine (ir_mlost_keep B0 HL Y Z _ _ _ E); ir_k); clear E
  | E : TC.m_maybe_online_m ?Y = Some (?Z, _) |- _ =>
      let K := fresh "K" in assert (K : ir_keep B0 Z) by (refine (ir_monline_keep B0 HL Y Z _ _ E); ir_k); clear E
  | E : TC.m_tick_m ?Y = Some (?Z, _) |- _ =>
      let K := fresh "K" in assert (K : ir_keep B0 Z) by (refine (ir_mtick_keep B0 HL Y Z _ _ E); ir_k); clear E
  end.

Lemma ir_mwake_keep : forall B0, Z.of_nat (length B0) = TW.W_LEN ->
  forall B B' rr, ir_keep B0 B -> TC.m_wake_m B = Some (B', rr) -> ir_keep B0 B'.
Proof.
intros B0 HL B B' rr HK H. unfold TC.m_wake_m in H. ir_split H.
all: apply TIR.some_pair_inv in H as [<- _]; ir_calls B0 HL; ir_k.
Qed.

Ltac ir_calls_w B0 HL :=
  repeat match goal with
  | E : TC.m_wake_m ?Y = Some (?Z, _) |- _ =>
      let K := fresh "K" in assert (K : ir_keep B0 Z) by (refine (ir_mwake_keep B0 HL Y Z _ _ E); ir_k); clear E
  | _ => progress ir_calls B0 HL
  end.

Lemma ir_mrx_keep : forall B0, Z.of_nat (length B0) = TW.W_LEN ->
  forall I F B B' n rr, ir_keep B0 B -> TC.m_rx_m I F B n = Some (B', rr) -> ir_keep B0 B'.
Proof.
intros B0 HL I F B B' n rr HK H. unfold TC.m_rx_m in H.
destruct F as [fr|]; [|discriminate H].
ir_split H.
all: apply TIR.some_pair_inv in H as [<- _]; ir_calls_w B0 HL; ir_k.
Qed.


Lemma ir_rowM : forall o b n x, In (o, b, n) TMAP_A -> o <= x < o + n ->
  TW.OFF_M <= x < TW.OFF_M + TW.SZ_M -> b + (x - o) = TA_M + (x - TW.OFF_M).
Proof.
intros o b n x Hin Hx HM.
destruct (tw_same TMAP_A o b n TW.OFF_M TA_M TW.SZ_M TMAP_A_ok Hin TMAP_A_M) as [(-> & -> & ->) | (Ho & _)];
  [reflexivity | exfalso; lia].
Qed.

Lemma ir_rowOW : forall o b n x, In (o, b, n) TMAP_A -> o <= x < o + n ->
  TW.OFF_OW <= x < TW.OFF_OW + TW.SZ_OW -> b + (x - o) = TA_OW + (x - TW.OFF_OW).
Proof.
intros o b n x Hin Hx HM.
destruct (tw_same TMAP_A o b n TW.OFF_OW TA_OW TW.SZ_OW TMAP_A_ok Hin TMAP_A_OW) as [(-> & -> & ->) | (Ho & _)];
  [reflexivity | exfalso; lia].
Qed.

Lemma ir_wo_mrx : forall o b n x, In (o, b, n) TMAP_A -> o <= x < o + n -> ir_wo x -> mrx_wr (b + (x - o)).
Proof.
intros o b n x Hin Hx HW.
assert (HM : TW.OFF_M <= x < TW.OFF_M + TW.SZ_M -> b + (x - o) = TA_M + (x - TW.OFF_M))
  by (intros H; exact (ir_rowM o b n x Hin Hx H)).
assert (HO : TW.OFF_OW <= x < TW.OFF_OW + TW.SZ_OW -> b + (x - o) = TA_OW + (x - TW.OFF_OW))
  by (intros H; exact (ir_rowOW o b n x Hin Hx H)).
unfold TW.SZ_M, TW.SZ_OW in HM, HO.
unfold mrx_wr, twa_fld. ir_offs.
destruct HW as [(i & Hi & Hr) | [(jj & Hjj & Hr) | HW]].
- rewrite (HO ltac:(lia)). do 14 right. left. exists i. split; [lia | lia].
- rewrite (HO ltac:(lia)). do 26 right. exists jj. split; [lia | lia].
- destruct HW as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H]]]]]]]]]]]]]]]]]]]]]]]]];
  [ rewrite (HM ltac:(lia)); left; lia
  | rewrite (HM ltac:(lia)); do 1 right; left; lia
  | rewrite (HM ltac:(lia)); do 2 right; left; lia
  | rewrite (HM ltac:(lia)); do 3 right; left; lia
  | rewrite (HM ltac:(lia)); do 4 right; left; lia
  | rewrite (HM ltac:(lia)); do 5 right; left; lia
  | rewrite (HM ltac:(lia)); do 6 right; left; lia
  | rewrite (HM ltac:(lia)); do 7 right; left; lia
  | rewrite (HM ltac:(lia)); do 8 right; left; lia
  | rewrite (HM ltac:(lia)); do 9 right; left; lia
  | rewrite (HM ltac:(lia)); do 10 right; left; lia
  | rewrite (HM ltac:(lia)); do 11 right; left; lia
  | rewrite (HM ltac:(lia)); do 12 right; left; lia
  | rewrite (HO ltac:(lia)); do 13 right; left; lia
  | rewrite (HO ltac:(lia)); do 15 right; left; lia
  | rewrite (HO ltac:(lia)); do 16 right; left; lia
  | rewrite (HO ltac:(lia)); do 17 right; left; lia
  | rewrite (HO ltac:(lia)); do 18 right; left; lia
  | rewrite (HO ltac:(lia)); do 19 right; left; lia
  | rewrite (HO ltac:(lia)); do 20 right; left; lia
  | rewrite (HO ltac:(lia)); do 21 right; left; lia
  | rewrite (HO ltac:(lia)); do 22 right; left; lia
  | rewrite (HO ltac:(lia)); do 23 right; left; lia
  | rewrite (HO ltac:(lia)); do 24 right; left; lia
  | rewrite (HO ltac:(lia)); do 25 right; left; lia
  ].
Qed.

(* Every byte of G the two callees do not write is read back as it was: the walk's view at the callee's world and
   the world relation at its world. *)
Lemma ir_G_kept : forall (rd rd' : Z -> option Z) (B1 B2 : list byte) a,
  tw_at TMAP_A rd B1 -> tw_at TMAP_A rd' B2 -> ir_keep B1 B2 ->
  inG TG.G_HARNESS a -> ~ mrx_wr a -> rd' a = rd a.
Proof.
intros rd rd' B1 B2 a HT1 HT2 HK Ha Hw.
unfold inG in Ha. apply Exists_exists in Ha as ((b, n) & Hin & Har).
unfold in_zr in Har. cbn [fst snd] in Har.
destruct (TMAP_A_G_rows b n Hin) as (o & Hrow).
destruct (tw_row TMAP_A o b n TMAP_A_ok Hrow) as (Ho & Hn & Honl & Hb & Hbn).
pose proof HT1 as [HL1 HR1]. pose proof HT2 as [HL2 HR2].
replace a with (b + (a - b)) by lia.
rewrite (HR1 o b n (a - b) Hrow ltac:(lia)), (HR2 o b n (a - b) Hrow ltac:(lia)).
f_equal. f_equal.
apply (proj2 HK); [lia|].
intros HW. apply Hw. replace a with (b + ((o + (a - b)) - o)) by lia.
exact (ir_wo_mrx o b n (o + (a - b)) Hrow ltac:(lia) HW).
Qed.

(* g_rx is not a byte the callees write, so the pointer the copy reads is the one the model reads. *)
Lemma ir_grx_keep : forall B1 B2, Z.of_nat (length B1) = TW.W_LEN -> ir_keep B1 B2 ->
  TW.g_rx B2 = TW.g_rx B1.
Proof.
intros B1 B2 HL HK. unfold TW.g_rx, TW.u_at.
rewrite (ir_keep_sub B1 B2 TW.OFF_g_rx 8 HK ltac:(unfold TW.OFF_g_rx; lia) ltac:(ir_offs; unfold TW.OFF_g_rx; lia)).
- reflexivity.
- intros j Hj. ir_offs. unfold TW.OFF_g_rx in Hj. intros HW.
  destruct HW as [(i & Hi & Hr) | [(jj & Hjj & Hr) | HW]]; [lia | lia |].
  repeat (destruct HW as [HW|HW]); lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The model's branches                                                *)
(* ------------------------------------------------------------------ *)

Lemma ir_w1_len : forall Bw, Z.of_nat (length Bw) = TW.W_LEN -> TW.g_rx_len (iorecv_w1 Bw) = TW.g_rx_len Bw.
Proof.
intros Bw HL. unfold TW.g_rx_len, iorecv_w1, TW.set_g_rx_times.
apply TWL.u_at_upd_out; rewrite ?TWL.length_put; unfold TW.OFF_g_rx_len, TW.OFF_g_rx_times, TW.W_LEN in *; lia.
Qed.

Lemma ir_w1_rx : forall Bw, Z.of_nat (length Bw) = TW.W_LEN -> TW.g_rx (iorecv_w1 Bw) = TW.g_rx Bw.
Proof.
intros Bw HL. unfold TW.g_rx, iorecv_w1, TW.set_g_rx_times.
apply TWL.u_at_upd_out; rewrite ?TWL.length_put; unfold TW.OFF_g_rx, TW.OFF_g_rx_times, TW.W_LEN in *; lia.
Qed.

Lemma ir_w1_length : forall Bw, Z.of_nat (length Bw) = TW.W_LEN -> Z.of_nat (length (iorecv_w1 Bw)) = TW.W_LEN.
Proof.
intros Bw HL. unfold iorecv_w1, TW.set_g_rx_times.
rewrite TWL.length_upd_put; [exact HL | unfold TW.OFF_g_rx_times; lia | rewrite HL; unfold TW.OFF_g_rx_times, TW.W_LEN; lia].
Qed.

Lemma ir_m_fail : forall F Bw cap Bw' r got,
  TC.truth (TW.g_rx_fail Bw) = true -> TC.io_recv_m timg_A F Bw cap = Some (Bw', r, got) ->
  Bw' = TW.set_g_rx_fail Bw 0 /\ r = - TC.EIO /\ got = [].
Proof.
intros F Bw cap Bw' r got Hf H. unfold TC.io_recv_m in H. rewrite Hf in H. cbv beta iota zeta in H.
apply TIR.some_triple_inv in H as (H1 & H2 & H3). subst. split; [reflexivity | split; reflexivity].
Qed.

Lemma ir_m_zero : forall F Bw cap Bw' r got,
  TC.truth (TW.g_rx_fail Bw) = false -> ((TW.g_rx Bw =? 0) || (TW.g_rx_times Bw =? 0))%bool = true ->
  TC.io_recv_m timg_A F Bw cap = Some (Bw', r, got) -> Bw' = Bw /\ r = 0 /\ got = [].
Proof.
intros F Bw cap Bw' r got Hf Hz H. unfold TC.io_recv_m in H. rewrite Hf, Hz in H. cbv beta iota zeta in H.
apply TIR.some_triple_inv in H as (H1 & H2 & H3). subst. split; [reflexivity | split; reflexivity].
Qed.

Lemma ir_m_main : forall F Bw cap Bw' r got n,
  Z.of_nat (length Bw) = TW.W_LEN ->
  TC.truth (TW.g_rx_fail Bw) = false -> (TW.g_rx Bw =? 0) = false -> (TW.g_rx_times Bw =? 0) = false ->
  n = (if TW.g_rx_len Bw <? cap then TW.g_rx_len Bw else cap) ->
  TC.io_recv_m timg_A F Bw cap = Some (Bw', r, got) ->
  ((n = 0 /\ exists u, TC.m_tick_m (iorecv_w1 Bw) = Some (Bw', u)) \/
   (n <> 0 /\ exists rr, TC.m_rx_m timg_A (TC.frame_from F (TW.g_rx Bw)) (iorecv_w1 Bw) n = Some (Bw', rr))) /\
  (exists bytes, TC.frame_read F (TW.g_rx Bw') n = Some bytes /\ r = bv_swrap 32 n /\
     got = (if 0 <? r then bytes else [])).
Proof.
intros F Bw cap Bw' r got n HL Hf Hrx Ht Hn H.
unfold TC.io_recv_m in H. rewrite Hf, Hrx, Ht in H. cbn [orb] in H. cbv beta iota zeta in H.
destruct (TC.int_dec (TW.g_rx_times Bw)) as [t|] eqn:Ed; [|cbv beta iota zeta in H; discriminate H].
assert (Ht' : t = TW.g_rx_times Bw - 1).
{ revert Ed. unfold TC.int_dec. destruct (TW.g_rx_times Bw =? TC.INT_MIN) eqn:EQ; intros Ed; [discriminate Ed | injection Ed as Ed; lia]. }
subst t. cbv beta iota zeta in H.
change (TW.set_g_rx_times Bw (TW.g_rx_times Bw - 1)) with (iorecv_w1 Bw) in H.
rewrite (ir_w1_len Bw HL) in H. rewrite <- Hn in H. rewrite (ir_w1_rx Bw HL) in H.
destruct (n =? 0) eqn:En.
- apply Z.eqb_eq in En.
  destruct (TC.m_tick_m (iorecv_w1 Bw)) as [[Bt u]|] eqn:Etk; [|cbv beta iota zeta in H; discriminate H]. cbv beta iota zeta in H.
  destruct (TC.frame_read F (TW.g_rx Bt) n) as [bytes|] eqn:Efr; [|cbv beta iota zeta in H; discriminate H]. cbv beta iota zeta in H.
  apply TIR.some_triple_inv in H as (H1 & H2 & H3). subst Bt r got.
  split; [left; split; [exact En | exists u; first [exact Etk | reflexivity]]|].
  exists bytes. split; [first [exact Efr | reflexivity] | split; reflexivity].
- apply Z.eqb_neq in En.
  destruct (TC.m_rx_m timg_A (TC.frame_from F (TW.g_rx Bw)) (iorecv_w1 Bw) n) as [[Br rr]|] eqn:Erx;
    [|cbv beta iota zeta in H; discriminate H].
  cbv beta iota zeta in H.
  destruct (TC.frame_read F (TW.g_rx Br) n) as [bytes|] eqn:Efr; [|cbv beta iota zeta in H; discriminate H]. cbv beta iota zeta in H.
  apply TIR.some_triple_inv in H as (H1 & H2 & H3). subst Br r got.
  split; [right; split; [exact En | exists rr; first [exact Erx | reflexivity]]|].
  exists bytes. split; [first [exact Efr | reflexivity] | split; reflexivity].
Qed.

(* g_fail_next is not among the bytes the callees write, nor g_rx_times' or g_rx_fail's. *)
Lemma ir_gfn_keep : forall B1 B2, Z.of_nat (length B1) = TW.W_LEN -> ir_keep B1 B2 ->
  TW.g_fail_next B2 = TW.g_fail_next B1.
Proof.
intros B1 B2 HL HK. unfold TW.g_fail_next, TW.u_at.
rewrite (ir_keep_sub B1 B2 TW.OFF_g_fail_next 1 HK ltac:(unfold TW.OFF_g_fail_next; lia)
  ltac:(ir_offs; unfold TW.OFF_g_fail_next; lia)).
- reflexivity.
- intros j Hj. ir_offs. unfold TW.OFF_g_fail_next in Hj. intros HW.
  destruct HW as [(i & Hi & Hr) | [(jj & Hjj & Hr) | HW]]; [lia | lia |].
  repeat (destruct HW as [HW|HW]); lia.
Qed.

Lemma ir_w1_gfn : forall Bw, Z.of_nat (length Bw) = TW.W_LEN -> TW.g_fail_next (iorecv_w1 Bw) = TW.g_fail_next Bw.
Proof.
intros Bw HL. unfold TW.g_fail_next, iorecv_w1, TW.set_g_rx_times.
apply TWL.u_at_upd_out; rewrite ?TWL.length_put; unfold TW.OFF_g_fail_next, TW.OFF_g_rx_times, TW.W_LEN in *; lia.
Qed.

Lemma ir_fail_gfn : forall Bw, Z.of_nat (length Bw) = TW.W_LEN ->
  TW.g_fail_next (TW.set_g_rx_fail Bw 0) = TW.g_fail_next Bw.
Proof.
intros Bw HL. unfold TW.g_fail_next, TW.set_g_rx_fail.
apply TWL.u_at_upd_out; rewrite ?TWL.length_put; unfold TW.OFF_g_fail_next, TW.OFF_g_rx_fail, TW.W_LEN in *; lia.
Qed.

(* frame_from's Some: TF is some f and p lies in [tf_addr f, tf_addr f + length]. *)
Lemma ir_frame_from_some : forall F p fr, TC.frame_from F p = Some fr ->
  exists f, F = Some f /\ 0 <= p - TI.tf_addr f <= Z.of_nat (length (TI.tf_bytes f)) /\
    fr = TI.TFrame p (skipn (Z.to_nat (p - TI.tf_addr f)) (TI.tf_bytes f)).
Proof.
intros F p fr H. unfold TC.frame_from in H. destruct F as [f|]; [|discriminate H].
exists f. split; [reflexivity|]. cbv zeta in H.
match type of H with context [if ?c then _ else _] => destruct c eqn:E end; [discriminate H|].
apply orb_false_iff in E as [E1 E2]. apply Z.ltb_ge in E1. apply Z.ltb_ge in E2.
split; [lia | congruence].
Qed.

(* frame_read's Some for n <> 0: TF is some f and [p, p + n) lies in its range. *)
Lemma ir_frame_read_some : forall F p n bytes, TC.frame_read F p n = Some bytes -> n <> 0 ->
  exists f, F = Some f /\ 0 <= p - TI.tf_addr f /\ 0 <= n /\
    p - TI.tf_addr f + n <= Z.of_nat (length (TI.tf_bytes f)) /\
    bytes = TW.sub (TI.tf_bytes f) (p - TI.tf_addr f) (Z.to_nat n).
Proof.
intros F p n bytes H Hn. unfold TC.frame_read in H. rewrite (proj2 (Z.eqb_neq n 0) Hn) in H.
destruct F as [f|]; [|discriminate H]. exists f. split; [reflexivity|]. cbv zeta in H.
match type of H with context [if ?c then _ else _] => destruct c eqn:E end; [discriminate H|].
apply orb_false_iff in E as [E E3]. apply orb_false_iff in E as [E1 E2].
apply Z.ltb_ge in E1. apply Z.ltb_ge in E2. apply Z.ltb_ge in E3.
split; [lia|]. split; [lia|]. split; [lia | congruence].
Qed.


(* ------------------------------------------------------------------ *)
(* The symbolic state at the entry                                     *)
(* ------------------------------------------------------------------ *)

(* Atoms: 0 .. 31 the registers at the entry, 32 the shadow base (no shadow entry: io_recv makes no instrumented
   check), 33 g_rx_fail, 34 g_rx, 35 g_rx_times, 36 g_rx_len. Regions: the 32-byte frame below sp and the four
   globals the code reads; g_rx_fail and g_rx_times are written (bytes of G). *)
Definition ir_fail_region : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 31)) 0 4 0 4 [YP09.mkChunk 0 (YP09.CVal 4 (SOff 33 0))].
Definition ir_rx_region : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 32)) 0 8 0 0 [YP09.mkChunk 0 (YP09.CVal 8 (SOff 34 0))].
Definition ir_times_region : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 33)) 0 4 0 4 [YP09.mkChunk 0 (YP09.CVal 4 (SOff 35 0))].
Definition ir_len_region : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 34)) 0 8 0 0 [YP09.mkChunk 0 (YP09.CVal 8 (SOff 36 0))].
Definition ir_regions : smem :=
  [stack_region IORECV_FRAME; ir_fail_region; ir_rx_region; ir_times_region; ir_len_region].

(* The three addresses the code forms from an auipc high part and an immediate (raw words of the listing): the store
   at g_rx_fail (0x834e4), the store at g_rx_times (0x83518) and the second load of g_rx (0x83540). Each is the address
   of the global the listing's load slot names (ir_vals_img). *)
Definition ir_alias : list (sv * sv) :=
  [(SOff (A_HI 65) (-1240), SOff (A_OBJ 31) 0);
   (SOff (A_HI 67) (-1248), SOff (A_OBJ 33) 0);
   (SOff (A_HI 66) 1200, SOff (A_OBJ 32) 0)].
(* The facts: sp, the shadow base, the two 4-byte loads, and the bases of the two writable regions (outside the
   shadow band, as the run's static check asks). *)
Definition ir_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 (2 ^ 32 - 1) 0); (35%nat, mkAF 0 (2 ^ 32 - 1) 0);
           (A_OBJ 31, mkAF TA_g_rx_fail TA_g_rx_fail 0); (A_OBJ 33, mkAF TA_g_rx_times TA_g_rx_times 0)] [] ir_alias.
Definition ss_ir : sstate := mkSS AF_io_recv sr_atoms ir_regions None ir_facts.
Definition IR_SH : list shent := [].
Definition IR_Bx : sv := SOff 32 0.

(* ------------------------------------------------------------------ *)
(* The branch conditions at the valuation                              *)
(* ------------------------------------------------------------------ *)

Lemma ir_sext32 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 v).
Proof.
intros E n v H R. cbn [sv_denot]. rewrite H. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia. rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma ir_br_eq32 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit 0)) = (bv_swrap 32 v =? 0).
Proof.
intros E n v H R. cbn [branch_taken]. rewrite (ir_sext32 E n v H R). cbn [sv_denot]. unfold bv_eqb.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
pose proof (bv_swrap_in_range 32 v ltac:(discriminate)) as RR. change (bv_half_modulus 32) with (2 ^ 31) in RR.
rewrite (Z.mod_small 0 (2 ^ 64)) by lia.
destruct (Z.eqb_spec (bv_swrap 32 v) 0) as [Heq | Hne].
- rewrite Heq. reflexivity.
- apply Z.eqb_neq. intros HH. apply Hne.
  destruct (Z_lt_le_dec (bv_swrap 32 v) 0) as [Hneg | Hpos].
  + rewrite <- (Z.mod_unique (bv_swrap 32 v) (2 ^ 64) (-1) (bv_swrap 32 v + 2 ^ 64)) in HH by lia. lia.
  + rewrite (Z.mod_small (bv_swrap 32 v) (2 ^ 64)) in HH by lia. exact HH.
Qed.

Lemma ir_br_eq64 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v =? 0).
Proof.
intros E n v H R. cbn [branch_taken sv_denot]. rewrite H, unsigned_lit_small, Z.add_0_r by lia.
unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small v), (Z.mod_small 0) by lia. reflexivity.
Qed.

Lemma ir_br_ltu : forall E n1 n2 v1 v2, ew E n1 = Z_to_bv 64 v1 -> ew E n2 = Z_to_bv 64 v2 ->
  0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SOff n1 0)) (sv_denot E (SOff n2 0)) = (v1 <? v2).
Proof.
intros E n1 n2 v1 v2 H1 H2 R1 R2. cbn [branch_taken sv_denot]. rewrite H1, H2, !unsigned_lit_small, !Z.add_0_r by lia.
unfold bv_ltu. rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

(* sext.w of a 64-bit value: the model's bv_swrap 32 *)
Lemma ir_sextw : forall E x n, sv_denot E x = Z_to_bv 64 n ->
  sv_denot E (SAluw ALU_ADD x (SLit 0)) = Z_to_bv 64 (bv_swrap 32 n).
Proof.
intros E x n H. cbn [sv_denot]. rewrite H. rewrite (zalu32_sound ALU_ADD n 0).
unfold zalu32, zalu_raw, zu32, M32. rewrite Z_to_bv64_canon. f_equal.
rewrite Zmod_0_l, Z.add_0_r. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2 ^ 32).
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* The run's static check at the entry state. *)
Lemma ir_static :
  sh_static_ok (run_K A_LIM IR_Bx IR_SH ss_ir) IR_Bx YC4b.Bspan IR_SH (ss_facts ss_ir) (ss_mem ss_ir) = true.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Three kit-style lemmas the walk uses by name                        *)
(* ------------------------------------------------------------------ *)

Section irk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.

(* DgnTransportCg.v trans_src_ok_acall_g with its gx_kept over all of G replaced by agreement on the range's G bytes:
   a G-form callee that writes G (m_rx, m_tick) keeps the image bytes outside G only; the walk discharges the G
   premise with the statement's trans_tf_off_g (no byte of TF is a byte of G). *)
Lemma ir_src_acall : AR_laws segs B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 slo shi (E : Z -> Prop) q n,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> frames S2 = frames Sc ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  TransportGCg.acall_kept_g segs B TransportG.G_HARNESS lyc Sc W memc W2 mem2 slo shi E ->
  (forall a, q <= a < q + n -> W_journalG.inG TransportG.G_HARNESS a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  (forall a, q <= a < q + n -> ~ E a) -> (forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ E a) ->
  (q + n <= slo \/ shi <= q) ->
  trans_src_ok B lyc Sc W memc q n -> 0 < n ->
  trans_src_ok B ly2 S2 W2 mem2 q n /\
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
Proof.
  intros LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E q n HAR HAR2 Hperm Hfr Hfa Elo Ehi
    (K1 & K2 & K3 & K4 & _) HGK HnE HnEs Hoff Hs Hn.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (KS : forall cid pos s, In (cid, pos) (frames Sc) ->
     in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
     aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s).
  { intros cid pos s Hin Hs'. apply (K4 cid pos s Hin (or_intror Hs')). apply HnEs.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F1 & F2 & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold in_zr in Hs'. cbn [fst snd] in Hs'.
    unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  assert (KV : forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
  { intros a Ha. destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & _)].
    - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
      pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq].
      replace a with (bA + (a - bA)) by lia.
      apply (K2 bA nA (a - bA) Hin ltac:(lia)). replace (bA + (a - bA)) with a by lia. exact (HnE a Ha).
    - destruct HL as [(cid & pos & Hin & F1 & F2) | [(HG & _) | [(S1 & S3) | (HR & _)]]].
      + apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact (HnE a Ha)].
      + exact (HGK a Ha (HG a Ha)).
      + destruct (trans_stk_bounds B lyc Sc W memc mdc HAR) as [T1 T2]. apply K1; lia.
      + pose proof (HR a Ha) as Ra. destruct (trans_ro_rd_scoped B HRU HRE a Ra) as [Ho He].
        apply (K3 a (trans_ro_img a Ra)); [|exact Ho | exact He].
        intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ra) as Rb.
        unfold TransportG.G_HARNESS_LO in Gh. lia. }
  split; [|exact KV].
  exact (trans_src_ok_kept B LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 q n HAR HAR2 Hperm Hfr Hfa Elo Ehi KV KS Hs Hn).
Qed.

(* trans_src_ok of a range of any length, the empty one included, bounds it and places it in application memory:
   the copy's source for n = 0 (io_recv_cg.v:147-149; DgnTransportCg.v trans_src_ok_rd and trans_src_ok_place ask
   0 < n). A heap block: al_blocks and YCbq.v amem_range_of_block; the other cases: decode_rd_ok. *)
Lemma ir_src_ok_amem : AR_laws segs B -> forall lyc Sc (W : world segs) memc mdc q n,
  @AR rc segs B lyc Sc W memc mdc -> trans_src_ok B lyc Sc W memc q n ->
  0 <= q /\ q + n <= 2 ^ 63 /\ amem_range q n.
Proof.
  intros LAWS lyc Sc W memc mdc q n HAR Hs.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct Hs as [(bA & nA & Hin & H1 & H2) | (_ & (_ & _ & _ & Ham & H0 & H63))].
  - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & H4096 & Hce & _ & _ & _ & Hn0).
    pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq].
    split; [lia | split; [lia |]].
    exact (amem_range_of_block segs B LAWS lyc Sc W memc mdc bA nA q n HAR Hin H1 ltac:(lia)).
  - split; [exact H0 | split; [exact H63 | exact Ham]].
Qed.

(* TransportGCg.v dk_kept_step_g with the step taken at a later world W2 (after a G-form callee). *)
Lemma ir_kept_step_w : AR_laws segs B ->
  forall G lyc Sc (W : world segs) memc mdc (W2 : world segs) memX memY slo shi (Eo Zs : Z -> Prop),
  @AR rc segs B lyc Sc W memc mdc ->
  acall_kept_g segs B G lyc Sc W memc W2 memX slo shi Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) memY a = aview segs (w_H W2) memX a) ->
  (forall a, apresent (w_H W2) memX a -> apresent (w_H W2) memY a) ->
  (forall a, Zs a -> alloc_ceiling <= a < 2 ^ 64 -> slo <= a < shi) ->
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> Zs (b + i) -> Eo (b + i)) ->
  (forall a, Zs a -> in_img segs a -> ~ inG G a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) -> False) ->
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     Zs a -> Eo a) ->
  acall_kept_g segs B G lyc Sc W memc W2 memY slo shi Eo.
Proof.
intros LAWS G lyc Sc W memc mdc W2 memX memY slo shi Eo Zs HAR (K1 & K2 & K3 & K4 & K5 & K6) Hkp Hgr HZw HZb HZi HZf.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw. rewrite Hkp; [apply K1; assumption | lia | intros HZ; exact (Hw (HZw a HZ Ha))].
- intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hce & _).
  rewrite Hkp; [apply (K2 b m i Hb Hi Hn) | lia | intros HZ; exact (Hn (HZb b m i Hb Hi HZ))].
- intros a Hi HnG Hno He. pose proof (transport_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  rewrite Hkp; [apply K3; assumption | lia | intros HZ; exact (HZi a HZ Hi HnG Hno He)].
- intros cid pos a Hin Hr Hn. destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  assert (Ha : 0 <= a < 2 ^ 64).
  { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  rewrite Hkp; [apply (K4 cid pos a Hin Hr Hn) | exact Ha | intros HZ; exact (Hn (HZf cid pos a Hin Hr HZ))].
- intros a Ha Hw Hp. apply Hgr. apply K5; assumption.
- intros a Ha. apply Hgr. apply K6. exact Ha.
Qed.
End irk.
