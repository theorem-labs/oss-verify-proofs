(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxDeskKit.v, with its module paths and module names changed; 712 of its 791 lines of code are new or changed and 480 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op3b: Lemma lc_op3b_ok : lc_op3b_stmt (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v), the
   segment OP3B of the image-A walk of LLVMFuzzerTestOneInput: offsets +0x970 .. +0x98c and +0x12e8 of the listing
   lib/A/Prog/DgnTransportList.v (fuzz_transport.asan 0x81bd4 .. 0x81bf0 and 0x8254c), from the cut lc_st_tick (TICK)
   to the cut lc_st_tail (TAIL).

   What the code does. +0x970 `jal m_tick` (return +0x974); +0x974 / +0x978 a0 = &g_s (auipc / addi); +0x97c
   `mv a1, s6` (the new g_now, kept in s6 across m_tick); +0x980 `jal diginet_session_tick` (return +0x984); +0x984
   `li a0, 1`; +0x988 `jal settle` (return +0x98c); +0x98c `j +0x12e8`; +0x12e8 `li s6, 7`; then the tail cut
   +0x12ec. The segment reaches no __asan_report_* call.

   The callees. m_tick and diginet_session_tick are G-form callees composed in the walk's own G journal (their
   statements lp_mtick, lp_tick); settle is a donor-form callee, lifted by TransportGCg.v gx_call_cg (lp_settle). Each
   is entered with sp = sp1 (the realigned sp, callee-saved), gp / tp of the entry and ra = its return address; its
   post gives the next cut by LLVMFuzzerTestOneInput_st.v lc_core_kept: what it keeps above alloc_ceiling (the spill
   slots and the saved words lie above sp1, its window below), and the bytes of the blocks, of the class-2 frame and of
   that frame's shadow, none of which is a byte the callee writes (each written range lies in G: op3b_mtick_wr_G,
   op3b_tick_wr_G; a byte of G is an image byte, a block or frame byte is not: AR_laws' al_client_img; the shadow lies
   above G's hull).

   The model. Op3Ok.v op3_ok gives the operation's Some at the stream fun _ => 1 (op 3 reads no stream) and
   agree timg_A (ops + 1) at its world; LLVMFuzzerTestOneInput_st.v lc_tick_eq splits it into m_tick_m, the tick and
   settle 1, whose world is the tick's (lc_settle_world). The tick's premises at m_tick's world: the run invariants
   by K6 (lc_runinv_stmt) at op_begin's world (SimLib.v agree_op_begin) carried over the g_now store (TRunInv.v
   rk_upd) and m_tick (m_tick_rk, rk_out); g_now and g_fail_next are not bytes m_tick_m writes (io_recv_seg_m.v
   ir_mtick_keep), so a1 = s6 is the model's now and g_fail_next stays below 2; the read-only bytes by K1
   (lc_rom_view_stmt); TF = None. settle's queue-length invariant at the tick's world: K6 at agree timg_A (ops + 1).
   The kit statements the proof takes as arguments: K1 lc_rom_view_stmt and K6 lc_runinv_stmt. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0 AE2k ACfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
m_lost_cg notice_cg io_send_cg diginet_body_check_cg send_data_cg m_tick_cg diginet_session_tick_cg settle_cg
receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
TransportGNotice io_send_seg_world io_recv_seg_m.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TOps
  TWorldLemmas TRunInv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts SimLib Op3Ok LinksProof.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module TRI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TRunInv.
Module AG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.Agree.
Module QF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.
Module SL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.SimLib.
Module O3 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.Op3Ok.
Module LP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LinksProof.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The powers of two the bounds name, as numerals (for lia). *)
Local Ltac op3b_num :=
  repeat match goal with
  | |- context [2 ^ 64] => change (2 ^ 64) with 18446744073709551616
  | H : context [2 ^ 64] |- _ => change (2 ^ 64) with 18446744073709551616 in H
  | |- context [2 ^ 63] => change (2 ^ 63) with 9223372036854775808
  | H : context [2 ^ 63] |- _ => change (2 ^ 63) with 9223372036854775808 in H
  | |- context [2 ^ 47] => change (2 ^ 47) with 140737488355328
  | H : context [2 ^ 47] |- _ => change (2 ^ 47) with 140737488355328 in H
  | |- context [2 ^ 40] => change (2 ^ 40) with 1099511627776
  | H : context [2 ^ 40] |- _ => change (2 ^ 40) with 1099511627776 in H
  | |- context [2 ^ 31] => change (2 ^ 31) with 2147483648
  | H : context [2 ^ 31] |- _ => change (2 ^ 31) with 2147483648 in H
  end.
Local Ltac op3b_lia := op3b_num; lia.

(* ------------------------------------------------------------------ *)
(* 1. The model                                                        *)
(* ------------------------------------------------------------------ *)

(* g_now is not among the bytes m_tick_m writes (io_recv_seg_m.v ir_wo: M and OW only). *)
Lemma op3b_gnow_keep : forall B1 B2, Z.of_nat (length B1) = TW.W_LEN -> ir_keep B1 B2 ->
  TW.g_now B2 = TW.g_now B1.
Proof.
intros B1 B2 HL HK. unfold TW.g_now, TW.u_at.
rewrite (ir_keep_sub B1 B2 TW.OFF_g_now 8 HK ltac:(unfold TW.OFF_g_now; lia)
  ltac:(ir_offs; unfold TW.OFF_g_now; lia)).
- reflexivity.
- intros j Hj. ir_offs. unfold TW.OFF_g_now in Hj. intros HW.
  destruct HW as [(i & Hi & Hr) | [(jj & Hjj & Hr) | HW]]; [lia | lia |].
  repeat (destruct HW as [HW|HW]); lia.
Qed.

(* m_tick_m keeps g_now and g_fail_next. *)
Lemma op3b_mtick_keep : forall X Y u, Z.of_nat (length X) = TW.W_LEN -> TC.m_tick_m X = Some (Y, u) ->
  TW.g_now Y = TW.g_now X /\ TW.g_fail_next Y = TW.g_fail_next X.
Proof.
intros X Y u HL H. pose proof (ir_mtick_keep X HL X Y u (ir_keep_refl X) H) as HK.
exact (conj (op3b_gnow_keep X Y HL HK) (ir_gfn_keep X Y HL HK)).
Qed.

(* The g_now store keeps the world's length and g_fail_next. *)
Lemma op3b_now_len : forall Bx v, Z.of_nat (length Bx) = TW.W_LEN ->
  Z.of_nat (length (TW.set_g_now Bx v)) = TW.W_LEN.
Proof.
intros Bx v HL. unfold TW.set_g_now.
rewrite TWL.length_upd_put; [exact HL | unfold TW.OFF_g_now; lia | rewrite HL; unfold TW.OFF_g_now, TW.W_LEN; lia].
Qed.
Lemma op3b_now_gfn : forall Bx v, Z.of_nat (length Bx) = TW.W_LEN ->
  TW.g_fail_next (TW.set_g_now Bx v) = TW.g_fail_next Bx.
Proof.
intros Bx v HL. unfold TW.g_fail_next, TW.set_g_now.
apply TWL.u_at_upd_out; rewrite ?TWL.length_put; unfold TW.OFF_g_fail_next, TW.OFF_g_now, TW.W_LEN in *; lia.
Qed.

(* lc_tick_w is a g_now store. *)
Lemma op3b_now_eq : forall D c1 B1, exists v, lc_tick_w D c1 B1 = TW.set_g_now B1 v.
Proof.
intros D c1 B1. unfold lc_tick_w.
destruct (TOP.fuzz_u8_m D c1) as [c2 sb]. cbv beta iota zeta.
destruct (TOP.fuzz_u16_m D c2) as [c3 t]. cbv beta iota zeta.
eexists. reflexivity.
Qed.

(* The operation's model at op 3, from the head's simulation facts and op_begin's world B1: m_tick, the tick at the
   new g_now, settle 1 keeping the tick's world, the operation's equation at the stream fun _ => 1 and agree at
   ops + 1. *)
Lemma op3b_model : forall (D : list byte) (ops : Z) (B0 B1 : list byte) (c : TOP.fuzz_in) (k : nat),
  AG.agree timg_A ops B0 -> 0 <= ops < TC.OPS_MAX -> QF.fuzz_in_ok D c -> lc_opc D c = 3 ->
  TC.op_begin_m B0 = Some (B1, tt) ->
  exists B3 B4 r,
    TC.m_tick_m (lc_tick_w D (lc_oc D c) B1) = Some (B3, tt) /\
    TSS.diginet_session_tick_m timg_A None B3 (TW.g_now B3) = Some (B4, r) /\
    TC.settle_m B4 1 = Some (B4, tt) /\
    TOP.LLVMFuzzerTestOneInput_op_m timg_A B0 (fun _ => 1) D c k = Some (B4, (lc_tick_c D (lc_oc D c), k)) /\
    AG.agree timg_A (ops + 1) B4.
Proof.
intros D ops B0 B1 c k HA Hops Hc Ho Hob.
destruct (O3.op3_ok LP.links_holds timg_A ops B0 (fun _ => 1) D c k HA (proj2 Hops) Hc Ho)
  as (B' & c' & E & HA' & _).
pose proof E as E0.
rewrite (lc_tick_eq timg_A B0 (fun _ => 1) D c k Ho), Hob in E. cbv beta iota in E.
destruct (TC.m_tick_m (lc_tick_w D (lc_oc D c) B1)) as [[B3 []]|] eqn:E3; [|discriminate E].
cbv beta iota in E.
destruct (TSS.diginet_session_tick_m timg_A None B3 (TW.g_now B3)) as [[B4 r]|] eqn:E4; [|discriminate E].
cbv beta iota in E.
destruct (TC.settle_m B4 1) as [[B5 []]|] eqn:E5; [|discriminate E].
cbv beta iota in E.
destruct (lc_some3 _ _ _ _ _ _ _ eq_refl E) as (EB & EC & _).
pose proof (lc_settle_world B4 B5 1 tt E5) as E54.
rewrite E54 in EB, E5. subst B'. subst c'.
exists B3, B4, r. refine (conj _ (conj E4 (conj E5 (conj E0 HA')))). first [exact E3 | reflexivity].
Qed.

(* The tick's premises at m_tick's world B3, from K6 at op_begin's world B1: the run invariants (TRunInv.v run_inv),
   g_fail_next <= 1 and g_now (the value s6 keeps across m_tick). *)
Lemma op3b_inv3 : forall (D : list byte) (ops : Z) (B1 B3 : list byte) (c1 : TOP.fuzz_in),
  lc_runinv_stmt -> AG.agree timg_A ops B1 ->
  TC.m_tick_m (lc_tick_w D c1 B1) = Some (B3, tt) ->
  TRI.run_inv B3 /\ TW.g_fail_next B3 <= 1 /\ TW.g_now B3 = TW.g_now (lc_tick_w D c1 B1).
Proof.
intros D ops B1 B3 c1 HK6 HA E3.
pose proof (AG.ac_len _ _ _ (AG.ag_core _ _ _ HA)) as HL1.
destruct (HK6 ops B1 HA) as (I1 & I2 & Iq & I4 & Inc & I5a & I5b & Igf).
assert (HR1 : TRI.run_inv B1) by exact (conj I1 (conj I2 (conj I4 (conj I5a (conj I5b (conj Inc Iq)))))).
destruct (op3b_now_eq D c1 B1) as (v & Ev).
assert (HL1z : Z.of_nat (length B1) = TW.W_LEN) by (rewrite HL1; apply Z2Nat.id; unfold TW.W_LEN; lia).
assert (HLt : Z.of_nat (length (lc_tick_w D c1 B1)) = TW.W_LEN) by (rewrite Ev; exact (op3b_now_len B1 v HL1z)).
assert (Hrk : TRI.rk B1 (lc_tick_w D c1 B1)).
{ rewrite Ev. unfold TW.set_g_now.
  apply (TRI.rk_upd B1 B1 TW.OFF_g_now (TW.put 8 v) HL1 (TRI.rk_refl B1)).
  - unfold TW.OFF_g_now. lia.
  - rewrite TWL.length_put. unfold TW.OFF_g_now, TW.W_LEN. lia.
  - rewrite TWL.length_put. unfold TRI.outR. do 6 right. left.
    unfold TW.OFF_g_ncmd, TW.OFF_g_now, TW.OFF_g_rx. lia. }
pose proof (TRI.m_tick_rk B1 HL1 _ B3 tt Hrk E3) as Hrk3.
destruct (TRI.rk_out B1 B3 HL1 HR1 Hrk3) as (_ & HR3).
destruct (op3b_mtick_keep (lc_tick_w D c1 B1) B3 tt HLt E3) as (Hn & Hf).
split; [exact HR3|]. split; [|exact Hn].
rewrite Hf, Ev, (op3b_now_gfn B1 v HL1z). exact Igf.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The written ranges of the callees lie in G                       *)
(* ------------------------------------------------------------------ *)

Local Ltac op3b_gsf :=
  unfold twa_fld, TW.A_S_inflight, TW.A_S_desk_counter_valid, TW.A_S_state, TW.A_S_inflight_retries,
    TW.A_S_inflight_frame, TW.A_S_inflight_sent_us, TW.A_S_next_keepalive_us, TW.A_S_display_sent,
    TW.A_S_last_display_us, TW.A_S_stats_tx_frames, TW.A_S_stats_tx_keepalives, TW.A_S_stats_tx_retransmits,
    TW.A_S_stats_ack_lost, TW.A_S_queue_bytes, TW.A_S_queued, TW.A_S_host_counter, TW.A_S_inflight_len,
    TW.A_S_inflight_counter, TW.A_S_stats_tx_data, TW.S_queue_ESZ, TW.S_queue_N, TS0.DIGINET_ETH_HDR_LEN,
    SENDDATA_CAP, TW.OFF_g_s, TW.SZ_g_s in *.

(* A byte of g_s's payload is a byte of G. *)
Lemma op3b_gs_G : forall a, TA_g_s <= a < TA_g_s + TW.SZ_g_s -> inG TG.G_HARNESS a.
Proof. intros a Ha. exact (ios_inG_row _ _ _ a TMAP_A_g_s Ha). Qed.

(* send_data's stores (send_data_cg.v senddata_wr). *)
Lemma op3b_sd_G : forall a, senddata_wr a -> inG TG.G_HARNESS a.
Proof.
intros a H. unfold senddata_wr in H.
repeat match type of H with _ \/ _ => destruct H as [H|H] end;
  first [ exact (ios_wr_inG _ a H) | (apply op3b_gs_G; op3b_gsf; lia) ].
Qed.

(* diginet_session_tick's stores (diginet_session_tick_cg.v tick_wr). *)
Lemma op3b_tick_wr_G : forall Bw a, tick_wr Bw a -> inG TG.G_HARNESS a.
Proof.
intros Bw a H. unfold tick_wr in H.
repeat match type of H with _ \/ _ => destruct H as [H|H] end;
  first [ exact (notice_wr_G _ _ a H) | exact (ios_wr_inG _ a H) | exact (op3b_sd_G a H)
        | (destruct H as (q & Hq & H); apply op3b_gs_G; op3b_gsf; lia)
        | (apply op3b_gs_G; op3b_gsf; lia) ].
Qed.

(* m_tick's stores (m_tick_cg.v mtick_wr: m_lost's, in M and OW). *)
Lemma op3b_mtick_wr_G : forall Bw a, mtick_wr Bw a -> inG TG.G_HARNESS a.
Proof.
intros Bw a (_ & H).
assert (HM : (TA_M <= a < TA_M + TW.SZ_M) \/ (TA_OW <= a < TA_OW + TW.SZ_OW)).
{ unfold mlost_wr, mset_wr, twa_fld, TW.A_M_desk_counter_valid, TW.A_M_fly_on, TW.A_M_state, TW.A_OW_n,
    TW.A_OW_t_state, TW.OW_t_ESZ, TC.TRANS_MAX, TW.SZ_M, TW.SZ_OW in *. lia. }
destruct HM as [HM | HM]; [exact (ios_inG_row _ _ _ a TMAP_A_M HM) | exact (ios_inG_row _ _ _ a TMAP_A_OW HM)].
Qed.

(* TF = None: the tick's apartness premise is vacuous. *)
Lemma op3b_apart : forall Bw, tick_apart None Bw.
Proof. intros Bw x _ fr Hfr. discriminate Hfr. Qed.

Lemma op3b_aregs_trans : forall r1 r2 r3 : bvmap 5 word,
  aregs_preserved r1 r2 -> aregs_preserved r2 r3 -> aregs_preserved r1 r3.
Proof. intros r1 r2 r3 H12 H23 r Hr. rewrite (H23 r Hr). exact (H12 r Hr). Qed.

(* ------------------------------------------------------------------ *)
(* 3. The symbolic states and their tactics                            *)
(* ------------------------------------------------------------------ *)

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac op3b_reg HS r v H tac :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* The write right of a run from a state with no region. *)
Ltac op3b_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_nil.
(* A run from a state with no region writes no byte. *)
Ltac op3b_keep_tac HFr KR W mold msn :=
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) (ms_mem msn) a = aview tfibsegs (w_H W) mold a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    apply (YC4b.kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []];
    let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
    let Hin := fresh "Hin" in let Hx := fresh "Hx" in
    intros b wlo whi x Hin Hx;
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
    cbn [In] in Hin; destruct Hin
  | ].

Section env. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Definition op3b_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs []).
Definition op3b_B0 : Z * Z := (0, 0).
Definition op3b_Bx : sv := SLit 0.

Lemma op3b_base : BASE = transport_text.
Proof. vm_compute. reflexivity. Qed.

Lemma op3b_ew : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (op3b_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold op3b_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma op3b_img : forall regs, img_env VAL A_LIM (op3b_E regs).
Proof. intros regs. unfold op3b_E. apply Eimg_env. Qed.
Lemma op3b_agree : forall regs, env_agree 32 (Ereg regs []) (op3b_E regs).
Proof. intros regs. split; [intros m Hm; unfold op3b_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* An image object's address, as the run leaves it in a register (`auipc` / `addi`). *)
Lemma op3b_sv_obj : forall regs k v, (A_TEXT <= k < A_LIM)%nat -> VAL k = v -> 0 <= v < 2 ^ 64 ->
  sv_denot (op3b_E regs) (SOff k 0) = w64 v.
Proof.
intros regs k v Hk Hv Hr. cbn [sv_denot]. unfold op3b_E. rewrite Eimg_img by exact Hk. rewrite Hv.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.

(* A symbolic state with no region holds of any machine state at its pc. *)
Lemma op3b_entry : forall (W : world segs) regs mem (pc : Z),
  st_ok_pi segs VAL (op3b_E regs) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem pc. rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.
End env.

(* ------------------------------------------------------------------ *)
(* 4. The walk's facts across a run and a call                         *)
(* ------------------------------------------------------------------ *)

Section op3b. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The states between the calls: the loop's common facts at operation op with lo_k op receptions, the world relation
   at Bw, the cursor after the u16 in s8 / s7, s4 = g_fail_next's page, and R of the registers. *)
Definition op3b_at (cx : lcx) (op : lop) (off : Z) (Bw : list byte) (R : bvmap 5 word -> Prop)
    : world segs -> config -> Prop :=
  fun W c => exists ly S regs mem md e,
    c = lc_cfg cx off regs mem md /\
    lc_lcore B MT cx op false false (lo_k op) ly S W regs mem md e /\
    lc_tw W mem Bw /\
    lc_cur cx regs 24 23 (lc_tick_c (l_pl cx) (lc_oc (l_pl cx) (lo_c op))) /\
    YK11.getr regs 20 = w64 LF_S4 /\ R regs.

Lemma op3b_at_mono : forall cx op off Bw (R R' : bvmap 5 word -> Prop) W c,
  (forall regs, R regs -> R' regs) -> op3b_at cx op off Bw R W c -> op3b_at cx op off Bw R' W c.
Proof.
intros cx op off Bw R R' W c HR (ly & S & regs & mem & md & e & H1 & H2 & H3 & H4 & H5 & H6).
exists ly, S, regs, mem, md, e. exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (HR regs H6)))))).
Qed.

(* The event count: e <= RECV_EV * k with k <= ops < OPS_MAX receptions, inside the slot's EV_LIB. *)
Lemma op3b_ev : forall cx op ly' S' (W' : world segs) regs' mem' md' e,
  lc_base B MT XL RLO RHI cx -> lc_lcore B MT cx op false false (lo_k op) ly' S' W' regs' mem' md' e ->
  st_nev (l_S cx) + e <= EV_MAX.
Proof.
intros cx op ly' S' W' regs' mem' md' e HB HL.
destruct HL as (_ & _ & _ & _ & (_ & Hops & _ & _ & Hk) & He & _).
unfold lc_base, tfib_lib_pre_x in HB.
destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & Hev & _).
pose proof transport_llvmf_events_ok as Hlib. unfold transport_llvmf_events, RECV_EV in *.
lia.
Qed.

(* What a callee's contract asks of the call state, from the cut's core and the run to the `jal`. *)
Lemma op3b_callpre : forall cx ly' S' (W' : world segs) regs' mem' md' e (regsX : bvmap 5 word) (k FSTK : Z),
  lc_base B MT XL RLO RHI cx -> lc_core B cx ly' S' W' regs' mem' md' e ->
  aregs_preserved regs' regsX ->
  YK11.getr regsX 1 = Z_to_bv 64 (BASE + k) -> 0 <= k < 2 ^ 40 -> k mod 2 = 0 ->
  0 <= FSTK <= LLVMF_STK - 336 ->
  YK0s.ret_ok (YK11.getr regsX 1) /\ 4096 <= raZ regsX /\
  YK11.getr regsX 3 = w64 (as_gp B) /\ YK11.getr regsX 4 = w64 (as_tp B) /\
  spZ regsX = lc_sp1 cx /\ spZ regsX mod 16 = 0 /\
  lc_sp0 cx - LLVMF_STK <= spZ regsX - FSTK /\ spZ regsX <= lc_sp0 cx.
Proof.
intros cx ly' S' W' regs' mem' md' e regsX k FSTK HB HC HPX R1 Hk Hk2 HF.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [_ _ Hstk Hsp1c _ _ _ _ _].
destruct Hstk as (Hce & Hslo & Hshi & H47).
pose proof HC as (_ & _ & _ & _ & R2 & _ & _ & R3 & R4 & Hsp1 & Hsp1al & _).
pose proof asan_consts as ((CVlo & CVhi) & _).
unfold LF_FRAME in Hsp1.
assert (R2X : YK11.getr regsX 2 = w64 (lc_sp1 cx))
  by exact (eq_trans (HPX 2 ltac:(unfold acallee_saved; lia)) R2).
assert (QSP : spZ regsX = lc_sp1 cx).
{ change (spZ regsX) with (bv_unsigned (YK11.getr regsX 2)). rewrite R2X. unfold w64.
  apply unsigned_lit_small. op3b_lia. }
split; [rewrite R1; apply (ret_ok_codeptr_v (PI := PI_transport)); [exact Hk | exact Hk2]|].
split.
{ change (raZ regsX) with (bv_unsigned (YK11.getr regsX 1)). rewrite R1, op3b_base.
  rewrite unsigned_lit_small by (unfold transport_text; op3b_lia). unfold transport_text. lia. }
split; [exact (eq_trans (HPX 3 ltac:(unfold acallee_saved; lia)) R3)|].
split; [exact (eq_trans (HPX 4 ltac:(unfold acallee_saved; lia)) R4)|].
split; [exact QSP|].
split.
{ rewrite QSP. pose proof (Z.div_mod (lc_sp1 cx) 32 ltac:(lia)) as D1.
  rewrite Hsp1al, Z.add_0_r in D1. rewrite D1.
  replace (32 * (lc_sp1 cx / 32)) with ((2 * (lc_sp1 cx / 32)) * 16) by ring.
  apply Z.mod_mul. lia. }
split; rewrite QSP; lia.
Qed.

(* What lc_core_kept asks of the bytes, from a run that wrote nothing and a G-form call whose written range lies in
   G: the bytes above alloc_ceiling outside the call's window, the blocks' bytes, and the frame's and its shadow's. *)
Lemma op3b_kept : forall cx ly' S' (W' : world segs) regs' mem' md' e (memX : word -> option byte)
    (W2 : world segs) mem2 (X : Z) (E : Z -> Prop),
  AR_laws segs B -> lc_base B MT XL RLO RHI cx -> lc_core B cx ly' S' W' regs' mem' md' e ->
  (forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W') memX a = aview segs (w_H W') mem' a) ->
  (forall a, E a -> inG TG.G_HARNESS a) ->
  acall_kept_g segs B TG.G_HARNESS ly' S' W' memX W2 mem2 (lc_sp1 cx - X) (lc_sp1 cx) E ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - X <= a < lc_sp1 cx) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a) /\
  (forall b m i, In (b, m) (ablocks B ly' S') -> 0 <= i < req_size m ->
     aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W') mem' (b + i)) /\
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES \/ lc_SH cx <= a < lc_SH cx + 32 ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a).
Proof.
intros cx ly' S' W' regs' mem' md' e memX W2 mem2 X E LAWS HB HC KR HEG HK.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HAR _ _ _ HFaddr HFin _ _ _].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF4096 & _ & HFce & _).
destruct HK as (K1 & K2 & _ & K4 & _).
pose proof asan_consts as ((CVlo & CVhi) & _).
assert (HF8 : 0 <= lc_F cx / 8 <= lc_F cx) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
unfold LF_FBYTES in *.
split; [|split].
- intros a Ha Hn. rewrite (K1 a Ha Hn). apply KR. lia.
- intros b m i Hin Hi.
  destruct (al_blocks _ _ LAWS ly' S' W' mem' md' b m HAR Hin) as (_ & H4096 & Hbc & _).
  rewrite (K2 b m i Hin Hi).
  + apply KR. op3b_lia.
  + intros Hw. assert (Hr : b <= b + i < b + req_size m) by lia.
    apply (proj2 (al_client_img _ _ LAWS ly' S' W' mem' md' (b + i) HAR
      (or_introl (ex_intro _ b (ex_intro _ m (conj Hin Hr)))))).
    exact (trans_g_img _ (HEG _ Hw)).
- intros a Ha.
  rewrite (K4 LF_CID (l_fpos cx) a HFin).
  + apply KR. unfold lc_SH, SHADOW_OFF in Ha. op3b_lia.
  + destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd]; rewrite HFaddr.
    * change (fs_frame_bytes LF_CID) with 256. lia.
    * change (fs_frame_bytes LF_CID / 8) with 32. unfold shadow_addr. unfold lc_SH in Ha. lia.
  + intros Hw. destruct Ha as [Ha | Ha].
    * assert (HaF : frame_addr ly' LF_CID (l_fpos cx) <= a <
                    frame_addr ly' LF_CID (l_fpos cx) + fs_frame_bytes LF_CID)
        by (rewrite HFaddr; change (fs_frame_bytes LF_CID) with 256; lia).
      apply (proj2 (al_client_img _ _ LAWS ly' S' W' mem' md' a HAR
        (or_intror (or_introl (ex_intro _ LF_CID (ex_intro _ (l_fpos cx) (conj HFin HaF))))))).
      exact (trans_g_img _ (HEG _ Hw)).
    * pose proof (inG_G_HARNESS_hull a (HEG a Hw)) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
      unfold lc_SH, SHADOW_OFF in Ha. lia.
Qed.

(* The same for a run alone (no call): every byte is kept. *)
Lemma op3b_kept0 : forall cx ly' S' (W' : world segs) regs' mem' md' e (memX : word -> option byte) (X : Z),
  AR_laws segs B -> lc_base B MT XL RLO RHI cx -> lc_core B cx ly' S' W' regs' mem' md' e ->
  (forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W') memX a = aview segs (w_H W') mem' a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - X <= a < lc_sp1 cx) ->
     aview segs (w_H W') memX a = aview segs (w_H W') mem' a) /\
  (forall b m i, In (b, m) (ablocks B ly' S') -> 0 <= i < req_size m ->
     aview segs (w_H W') memX (b + i) = aview segs (w_H W') mem' (b + i)) /\
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES \/ lc_SH cx <= a < lc_SH cx + 32 ->
     aview segs (w_H W') memX a = aview segs (w_H W') mem' a).
Proof.
intros cx ly' S' W' regs' mem' md' e memX X LAWS HB HC KR.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HAR _ _ _ _ _ _ _ _].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF4096 & _ & HFce & _).
pose proof asan_consts as ((CVlo & CVhi) & _).
assert (HF8 : 0 <= lc_F cx / 8 <= lc_F cx) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
unfold LF_FBYTES in *.
split; [|split].
- intros a Ha _. apply KR. lia.
- intros b m i Hin Hi.
  destruct (al_blocks _ _ LAWS ly' S' W' mem' md' b m HAR Hin) as (_ & H4096 & Hbc & _).
  apply KR. op3b_lia.
- intros a Ha. apply KR. unfold lc_SH, SHADOW_OFF in Ha. op3b_lia.
Qed.

(* lc_core with the registers of another state that agrees on sp, s0, s1, gp and tp. *)
Lemma op3b_core_regs : forall cx ly S (W : world segs) regs mem md e (regs2 : bvmap 5 word),
  lc_core B cx ly S W regs mem md e ->
  YK11.getr regs2 2 = YK11.getr regs 2 -> YK11.getr regs2 3 = YK11.getr regs 3 ->
  YK11.getr regs2 4 = YK11.getr regs 4 -> YK11.getr regs2 8 = YK11.getr regs 8 ->
  YK11.getr regs2 9 = YK11.getr regs 9 ->
  lc_core B cx ly S W regs2 mem md e.
Proof.
intros cx ly S W regs mem md e regs2 HC E2 E3 E4 E8 E9.
destruct HC as (HJ & Hfrs & HlyF & Hperm & R2 & R8 & R9 & R3 & R4 & Hrest).
exact (conj HJ (conj Hfrs (conj HlyF (conj Hperm (conj (eq_trans E2 R2) (conj (eq_trans E8 R8)
  (conj (eq_trans E9 R9) (conj (eq_trans E3 R3) (conj (eq_trans E4 R4) Hrest))))))))).
Qed.

(* The loop's common facts at the next state, from the core there: s2 / s10 and s5 kept, the spill slots and the
   frame's shadow kept, the operation's start facts, the events and the meter (no charge). *)
Lemma op3b_lcore_next : forall cx op k ly' S' (W' : world segs) regs' mem' md' e
    ly2 S2 (W2 : world segs) regs2 mem2 md2 (X : Z),
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx ->
  lc_lcore B MT cx op false false k ly' S' W' regs' mem' md' e ->
  lc_core B cx ly2 S2 W2 regs2 mem2 md2 e ->
  YK11.getr regs2 18 = YK11.getr regs' 18 -> YK11.getr regs2 21 = YK11.getr regs' 21 ->
  YK11.getr regs2 26 = YK11.getr regs' 26 ->
  0 <= X ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - X <= a < lc_sp1 cx) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a) ->
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES \/ lc_SH cx <= a < lc_SH cx + 32 ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a) ->
  mo_le MT S' S2 0 ->
  lc_lcore B MT cx op false false k ly2 S2 W2 regs2 mem2 md2 e.
Proof.
intros cx op k ly' S' W' regs' mem' md' e ly2 S2 W2 regs2 mem2 md2 X HP HB HL HC2 E18 E21 E26 HX KA KF HMO.
pose proof (lp_meter_laws _ _ _ _ _ HP) as MTL.
destruct HL as (HC & (R18 & R26) & HSP & HFSH & HOK & He & (Hmle & Hmok) & R21).
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [_ _ Hstk Hsp1c _ _ _ _ _].
destruct Hstk as (Hce & Hslo & Hshi & H47).
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _ & _ & HF4096 & _ & HFce & _).
pose proof asan_consts as ((CVlo & CVhi) & _).
unfold LF_FRAME in Hsp1.
split; [exact HC2|].
split; [split; [exact (eq_trans E18 R18) | exact (eq_trans E26 R26)]|].
split.
{ apply (lc_spills_kept cx _ (aview segs (w_H W') mem') (aview segs (w_H W2) mem2)); [| |exact HSP].
  - intros o Ho.
    pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES in *; op3b_lia)) as SV.
    rewrite Forall_forall in SV. destruct (SV o Ho) as (_ & _ & H8 & H192). lia.
  - intros a Ha. apply KA; op3b_lia. }
split.
{ apply (lc_fsh_kept cx (aview segs (w_H W') mem')); [|exact HFSH]. intros a Ha. apply KF. right. exact Ha. }
split; [exact HOK|].
split; [exact He|].
split; [split|].
- pose proof (mle_station MT _ _ _ _ _ MTL Hmle HMO) as H. rewrite Z.add_0_r in H. exact H.
- apply (mo_ok_step MT MTL S' S2 0); [rewrite Z.add_0_l; exact Hmok | exact HMO].
- exact (eq_trans E21 R21).
Qed.

Lemma op3b_cur_kept : forall cx (r1 r2 : bvmap 5 word) c,
  aregs_preserved r1 r2 -> lc_cur cx r1 24 23 c -> lc_cur cx r2 24 23 c.
Proof.
intros cx r1 r2 c HP (H24 & H23). split.
- exact (eq_trans (HP 24 ltac:(unfold acallee_saved; lia)) H24).
- exact (eq_trans (HP 23 ltac:(unfold acallee_saved; lia)) H23).
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The four pieces                                                  *)
(* ------------------------------------------------------------------ *)

(* +0x970: `jal m_tick`; the return at +0x974. *)
Lemma op3b_s1 : forall (cx : lcx) (op : lop) ly' S' (W' : world segs) regs' mem' md' e (Bt B3 : list byte),
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx ->
  lc_lcore B MT cx op false false (lo_k op) ly' S' W' regs' mem' md' e ->
  lc_tw W' mem' Bt ->
  lc_cur cx regs' 24 23 (lc_tick_c (l_pl cx) (lc_oc (l_pl cx) (lo_c op))) ->
  YK11.getr regs' 20 = w64 LF_S4 ->
  TC.m_tick_m Bt = Some (B3, tt) ->
  SRr segs W' (lc_cfg cx LO_TICK regs' mem' md')
    (op3b_at cx op 0x974 B3 (fun regs => YK11.getr regs 22 = YK11.getr regs' 22)).
Proof.
intros cx op ly' S' W' regs' mem' md' e Bt B3 HP HB HL Htw HCUR R20 Hm.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HL as (HC & _).
pose proof HC as (HJ & Hfrs & _).
pose proof (op3b_ev cx op ly' S' W' regs' mem' md' e HB HL) as Hev.
assert (XS : 0 <= MTICK_STK <= LLVMF_STK - 336) by (split; vm_compute; intros Hc; discriminate Hc).
unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (transport_text + 2416)) mem'
    (YK11.seg_rom segs)) md') Q) end.
rewrite <- op3b_base.
pose proof (op3b_entry (fx := l_fx cx) W' regs' mem' 2416) as HS.
pose proof (op3b_img regs') as HEI.
assert (SHOK : sh_ok segs op3b_Bx (@nil shent) (op3b_E regs') (mrestrict (w_H W') mem')) by constructor.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUN.
paj_run_tok RUN HS HJ SHOK op3b_B0.
{ op3b_awr. }
op3b_keep_tac HFr KR W' mem' ms.
clear HF HFr HG.
pmkst HS.
op3b_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 2420)) Q1 ltac:(apply codeptr_val; exact HEI).
assert (HPX : aregs_preserved regs' (ms_regs ms))
  by (apply (aregs_preserved_of_st_ok segs (w_H W') (op3b_E regs') _ ms regs' [] HS);
      [apply op3b_agree | vm_compute; reflexivity]).
destruct (op3b_callpre cx ly' S' W' regs' mem' md' e (ms_regs ms) 2420 MTICK_STK HB HC HPX Q1
  ltac:(op3b_lia) eq_refl XS) as (Hret & Hra & Rgp & Rtp & QSP & Hsp16 & Hlo & Hhi).
assert (TW1 : tw_at TMAP_A (aview segs (w_H W') (ms_mem ms)) Bt).
{ apply (tw_kept TMAP_A (aview segs (w_H W') mem')); [exact Htw|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  apply KR. op3b_lia. }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at (l_fx cx) sg (transport_sigma TS_m_tick) rg mm mdx) Q) end.
eapply SRr_bind.
{ exact (lp_mtick _ _ _ _ _ HP (l_fx cx) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_regs ms) Bt B3
    HJ Hret Hra Rgp Rtp Hsp16 Hlo Hhi TW1 Hm ltac:(unfold MTICK_EV, MLOST_EV; lia)). }
cbv beta. intros W2 c2 _ HQ.
unfold transport_mtick_post, transport_cg_post in HQ.
destruct HQ as (ly2 & S2 & regs2 & mem2 & md2 & e2 & Hc2 & He2 & HJ2 & HP2 & Hfr2 & Hperm2 & HK2 & Hmo2 & HTW2).
assert (Ee2 : e2 = 0) by (unfold MTICK_EV, MLOST_EV in He2; lia). subst e2. rewrite Z.add_0_r in HJ2.
rewrite Q1 in Hc2. subst c2. rewrite QSP in HK2.
pose proof (op3b_aregs_trans _ _ _ HPX HP2) as HPA.
destruct (op3b_kept cx ly' S' W' regs' mem' md' e (ms_mem ms) W2 mem2 MTICK_STK (mtick_wr Bt) LAWS HB HC KR
  (op3b_mtick_wr_G Bt) HK2) as (KA & KB & KF).
pose proof (lc_core_kept B MT XL RLO RHI cx ly' S' W' regs' mem' md' e MTICK_STK ly2 S2 W2 regs2 mem2 md2 e
  LAWS HB HC HJ2 Hfr2 Hperm2 HPA XS KA KB KF) as HC2.
pose proof (op3b_lcore_next cx op (lo_k op) ly' S' W' regs' mem' md' e ly2 S2 W2 regs2 mem2 md2 MTICK_STK HP HB HL HC2
  (HPA 18 ltac:(unfold acallee_saved; lia)) (HPA 21 ltac:(unfold acallee_saved; lia))
  (HPA 26 ltac:(unfold acallee_saved; lia)) (proj1 XS) KA KF Hmo2) as HL2.
apply SRr_ret.
exists ly2, S2, regs2, mem2, md2, e.
split; [unfold lc_cfg; rewrite op3b_base; reflexivity|].
split; [exact HL2|].
split; [exact HTW2|].
split; [exact (op3b_cur_kept cx regs' regs2 _ HPA HCUR)|].
split; [exact (eq_trans (HPA 20 ltac:(unfold acallee_saved; lia)) R20)|].
exact (HPA 22 ltac:(unfold acallee_saved; lia)).
Qed.

(* +0x974 .. +0x980: a0 = &g_s, a1 = s6, `jal diginet_session_tick`; the return at +0x984. *)
Lemma op3b_s2 : forall (cx : lcx) (op : lop) (B3 B4 : list byte) (r : Z) (W : world segs) (c : config),
  lc_rom_view_stmt B MT XL RLO RHI ->
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx ->
  TRI.run_inv B3 -> TW.g_fail_next B3 <= 1 ->
  TSS.diginet_session_tick_m timg_A None B3 (TW.g_now B3) = Some (B4, r) ->
  op3b_at cx op 0x974 B3 (fun regs => YK11.getr regs 22 = w64 (TW.g_now B3)) W c ->
  SRr segs W c (op3b_at cx op 0x984 B4 (fun _ => True)).
Proof.
intros cx op B3 B4 r W c HK1 HP HB HRI Hgf Htk HAT.
destruct HAT as (ly' & S' & regs' & mem' & md' & e & Hc & HL & Htw & HCUR & R20 & R22). subst c.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HL as (HC & _).
pose proof HC as (HJ & Hfrs & _).
pose proof (op3b_ev cx op ly' S' W regs' mem' md' e HB HL) as Hev.
pose proof (HK1 HP cx ly' S' W regs' mem' md' e HB HC) as HROM.
destruct HRI as (I1 & I2 & I4 & I5a & I5b & Inc & Iq).
assert (XS : 0 <= TICK_STK <= LLVMF_STK - 336) by (split; vm_compute; intros Hc; discriminate Hc).
assert (Hnow : 0 <= TW.g_now B3 < 2 ^ 64).
{ pose proof (TWL.u_at_range B3 TW.OFF_g_now 8) as Rw. change (8 * Z.of_nat 8) with 64 in Rw. exact Rw. }
unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (transport_text + 2420)) mem'
    (YK11.seg_rom segs)) md') Q) end.
rewrite <- op3b_base.
pose proof (op3b_entry (fx := l_fx cx) W regs' mem' 2420) as HS.
pose proof (op3b_img regs') as HEI.
assert (SHOK : sh_ok segs op3b_Bx (@nil shent) (op3b_E regs') (mrestrict (w_H W) mem')) by constructor.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUN.
paj_run_tok RUN HS HJ SHOK op3b_B0.
{ op3b_awr. }
op3b_keep_tac HFr KR W mem' ms.
clear HF HFr HG.
pmkst HS.
op3b_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 2436)) Q1 ltac:(apply codeptr_val; exact HEI).
op3b_reg HS (10%bv : bv 5) (w64 TICK_S) Q10
  ltac:(apply op3b_sv_obj;
        [unfold A_TEXT, A_LIM; lia | vm_compute; reflexivity | unfold TICK_S, TA_g_s; op3b_lia]).
op3b_reg HS (11%bv : bv 5) (YK11.getr regs' (Z_to_bv 5 22)) Q11
  ltac:(cbn [sv_denot]; rewrite (op3b_ew regs' 22 (Z_to_bv 5 22) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
assert (Q11' : YK11.getr (ms_regs ms) 11 = w64 (TW.g_now B3)) by exact (eq_trans Q11 R22).
assert (HPX : aregs_preserved regs' (ms_regs ms))
  by (apply (aregs_preserved_of_st_ok segs (w_H W) (op3b_E regs') _ ms regs' [] HS);
      [apply op3b_agree | vm_compute; reflexivity]).
destruct (op3b_callpre cx ly' S' W regs' mem' md' e (ms_regs ms) 2436 TICK_STK HB HC HPX Q1
  ltac:(op3b_lia) eq_refl XS) as (Hret & Hra & Rgp & Rtp & QSP & Hsp16 & Hlo & Hhi).
assert (TW1 : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms)) B3).
{ apply (tw_kept TMAP_A (aview segs (w_H W) mem')); [exact Htw|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  apply KR. op3b_lia. }
assert (ROM1 : trans_rom_view_rd W (ms_mem ms)).
{ intros a Ha. rewrite KR by (pose proof (trans_ro_rd_bounds a Ha); op3b_lia). exact (HROM a Ha). }
assert (C5 : count_cid TICK_CID (frames S') < fs_frames TICK_CID) by (rewrite Hfrs; vm_compute; reflexivity).
assert (C0 : count_cid SENDDATA_CID (frames S') < fs_frames SENDDATA_CID)
  by (rewrite Hfrs; vm_compute; reflexivity).
assert (C2 : count_cid TRANS_BC_CID (frames S') < fs_frames TRANS_BC_CID)
  by (rewrite Hfrs; vm_compute; reflexivity).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at (l_fx cx) sg (transport_sigma TS_diginet_session_tick) rg mm mdx) Q) end.
eapply SRr_bind.
{ exact (lp_tick _ _ _ _ _ HP (l_fx cx) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_regs ms) (TW.g_now B3) r None B3 B4
    HJ Hret Hra Rgp Rtp Q10 Q11' Hsp16 Hlo Hhi Hnow TW1 Hgf Htk I ROM1 (op3b_apart B3)
    I1 I2 Iq I4 Inc I5a I5b C5 C0 C2 ltac:(unfold TICK_EV; lia)). }
cbv beta. intros W2 c2 _ HQ.
unfold transport_tick_post, transport_cg_post in HQ.
destruct HQ as (ly2 & S2 & regs2 & mem2 & md2 & e2 & Hc2 & He2 & HJ2 & HP2 & Hfr2 & Hperm2 & HK2 & Hmo2 &
  (_ & HTW2 & _)).
assert (Ee2 : e2 = 0) by (unfold TICK_EV in He2; lia). subst e2. rewrite Z.add_0_r in HJ2.
rewrite Q1 in Hc2. subst c2. rewrite QSP in HK2.
pose proof (op3b_aregs_trans _ _ _ HPX HP2) as HPA.
destruct (op3b_kept cx ly' S' W regs' mem' md' e (ms_mem ms) W2 mem2 TICK_STK (tick_wr B3) LAWS HB HC KR
  (op3b_tick_wr_G B3) HK2) as (KA & KB & KF).
pose proof (lc_core_kept B MT XL RLO RHI cx ly' S' W regs' mem' md' e TICK_STK ly2 S2 W2 regs2 mem2 md2 e
  LAWS HB HC HJ2 Hfr2 Hperm2 HPA XS KA KB KF) as HC2.
pose proof (op3b_lcore_next cx op (lo_k op) ly' S' W regs' mem' md' e ly2 S2 W2 regs2 mem2 md2 TICK_STK HP HB HL HC2
  (HPA 18 ltac:(unfold acallee_saved; lia)) (HPA 21 ltac:(unfold acallee_saved; lia))
  (HPA 26 ltac:(unfold acallee_saved; lia)) (proj1 XS) KA KF Hmo2) as HL2.
apply SRr_ret.
exists ly2, S2, regs2, mem2, md2, e.
split; [unfold lc_cfg; rewrite op3b_base; reflexivity|].
split; [exact HL2|].
split; [exact HTW2|].
split; [exact (op3b_cur_kept cx regs' regs2 _ HPA HCUR)|].
split; [exact (eq_trans (HPA 20 ltac:(unfold acallee_saved; lia)) R20)|].
exact I.
Qed.

(* +0x984 .. +0x988: a0 = 1, `jal settle` (lifted by gx_call_cg); the return at +0x98c. *)
Lemma op3b_s3 : forall (cx : lcx) (op : lop) (B4 : list byte) (W : world segs) (c : config),
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx ->
  TC.settle_m B4 1 = Some (B4, tt) ->
  (forall i, 0 <= i < TW.S_queued B4 -> TW.S_queue_len B4 i <= TS0.DIGINET_CMD_MAX_LEN) ->
  op3b_at cx op 0x984 B4 (fun _ => True) W c ->
  SRr segs W c (op3b_at cx op 0x98c B4 (fun _ => True)).
Proof.
intros cx op B4 W c HP HB Hst Hq HAT.
destruct HAT as (ly' & S' & regs' & mem' & md' & e & Hc & HL & Htw & HCUR & R20 & _). subst c.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (G_HARNESS_gx_noerrno B (lp_g_no_errno _ _ _ _ _ HP)) as HGNE.
pose proof HL as (HC & _).
pose proof HC as (HJ & _).
pose proof (op3b_ev cx op ly' S' W regs' mem' md' e HB HL) as Hev.
assert (XS : 0 <= SETTLE_STK <= LLVMF_STK - 336) by (split; vm_compute; intros Hc; discriminate Hc).
unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (transport_text + 2436)) mem'
    (YK11.seg_rom segs)) md') Q) end.
rewrite <- op3b_base.
pose proof (op3b_entry (fx := l_fx cx) W regs' mem' 2436) as HS.
pose proof (op3b_img regs') as HEI.
assert (SHOK : sh_ok segs op3b_Bx (@nil shent) (op3b_E regs') (mrestrict (w_H W) mem')) by constructor.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUN.
paj_run_tok RUN HS HJ SHOK op3b_B0.
{ op3b_awr. }
op3b_keep_tac HFr KR W mem' ms.
clear HF HFr HG.
pmkst HS.
op3b_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 2444)) Q1 ltac:(apply codeptr_val; exact HEI).
op3b_reg HS (10%bv : bv 5) (w64 1) Q10 ltac:(reflexivity).
assert (HPX : aregs_preserved regs' (ms_regs ms))
  by (apply (aregs_preserved_of_st_ok segs (w_H W) (op3b_E regs') _ ms regs' [] HS);
      [apply op3b_agree | vm_compute; reflexivity]).
destruct (op3b_callpre cx ly' S' W regs' mem' md' e (ms_regs ms) 2444 SETTLE_STK HB HC HPX Q1
  ltac:(op3b_lia) eq_refl XS) as (Hret & Hra & Rgp & Rtp & QSP & Hsp16 & Hlo & Hhi).
assert (TW1 : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms)) B4).
{ apply (tw_kept TMAP_A (aview segs (w_H W) mem')); [exact Htw|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  apply KR. op3b_lia. }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at (l_fx cx) sg (transport_sigma TS_settle) rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_call_cg (l_fx cx) rc tfib_sink_head segs B MT TG.G_HARNESS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (ms_regs ms) SETTLE_STK SETTLE_EV 0 (fun _ => False) (fun _ _ _ => B4 = B4) HGX HGNE HJ).
  intros memS HJS.
  exact (lp_settle _ _ _ _ _ HP (l_fx cx) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_regs ms) 1 B4 B4
    HJS Hret Hra Rgp Rtp Q10 ltac:(op3b_lia) Hsp16 Hlo Hhi TW1 Hst Hq ltac:(unfold SETTLE_EV; lia)). }
cbv beta. intros W2 c2 _ HQ.
unfold transport_cg_post in HQ.
destruct HQ as (ly2 & S2 & regs2 & mem2 & md2 & e2 & Hc2 & He2 & HJ2 & HP2 & Hfr2 & Hperm2 & HK2 & Hmo2 &
  (_ & HGK)).
assert (Ee2 : e2 = 0) by (unfold SETTLE_EV in He2; lia). subst e2. rewrite Z.add_0_r in HJ2.
rewrite Q1 in Hc2. subst c2. rewrite QSP in HK2.
pose proof (op3b_aregs_trans _ _ _ HPX HP2) as HPA.
destruct (op3b_kept cx ly' S' W regs' mem' md' e (ms_mem ms) W2 mem2 SETTLE_STK (fun _ => False) LAWS HB HC KR
  (fun a (Hf : False) => False_ind _ Hf) HK2) as (KA & KB & KF).
pose proof (lc_core_kept B MT XL RLO RHI cx ly' S' W regs' mem' md' e SETTLE_STK ly2 S2 W2 regs2 mem2 md2 e
  LAWS HB HC HJ2 Hfr2 Hperm2 HPA XS KA KB KF) as HC2.
pose proof (op3b_lcore_next cx op (lo_k op) ly' S' W regs' mem' md' e ly2 S2 W2 regs2 mem2 md2 SETTLE_STK HP HB HL
  HC2 (HPA 18 ltac:(unfold acallee_saved; lia)) (HPA 21 ltac:(unfold acallee_saved; lia))
  (HPA 26 ltac:(unfold acallee_saved; lia)) (proj1 XS) KA KF Hmo2) as HL2.
apply SRr_ret.
exists ly2, S2, regs2, mem2, md2, e.
split; [unfold lc_cfg; rewrite op3b_base; reflexivity|].
split; [exact HL2|].
split.
{ apply (tw_kept TMAP_A (aview segs (w_H W) (ms_mem ms))); [exact TW1|].
  intros x Hx. exact (HGK x (ios_tw_in_G x Hx)). }
split; [exact (op3b_cur_kept cx regs' regs2 _ HPA HCUR)|].
split; [exact (eq_trans (HPA 20 ltac:(unfold acallee_saved; lia)) R20)|].
exact I.
Qed.

(* +0x98c `j +0x12e8`, +0x12e8 `li s6, 7`: the tail cut +0x12ec. *)
Lemma op3b_s4 : forall (cx : lcx) (op : lop) (B4 : list byte) (W : world segs) (c : config),
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx ->
  TOP.LLVMFuzzerTestOneInput_op_m timg_A (lo_B op) (fun _ => 1) (l_pl cx) (lo_c op) (lo_k op) =
    Some (B4, (lc_tick_c (l_pl cx) (lc_oc (l_pl cx) (lo_c op)), lo_k op)) ->
  op3b_at cx op 0x98c B4 (fun _ => True) W c ->
  SRr segs W c (lc_st_tail B MT cx op).
Proof.
intros cx op B4 W c HP HB Hop HAT.
destruct HAT as (ly' & S' & regs' & mem' & md' & e & Hc & HL & Htw & HCUR & R20 & _). subst c.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (lp_meter_laws _ _ _ _ _ HP) as MTL.
pose proof HL as (HC & _).
pose proof HC as (HJ & _).
unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (transport_text + 2444)) mem'
    (YK11.seg_rom segs)) md') Q) end.
rewrite <- op3b_base.
pose proof (op3b_entry (fx := l_fx cx) W regs' mem' 2444) as HS.
pose proof (op3b_img regs') as HEI.
assert (SHOK : sh_ok segs op3b_Bx (@nil shent) (op3b_E regs') (mrestrict (w_H W) mem')) by constructor.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUNTO.
paj_run_to_tok RUNTO HS HJ SHOK op3b_B0 4844.
{ op3b_awr. }
op3b_keep_tac HFr KR W mem' ms.
clear HF HFr HG.
op3b_reg HS (2%bv : bv 5) (YK11.getr regs' (Z_to_bv 5 2)) Q2
  ltac:(cbn [sv_denot]; rewrite (op3b_ew regs' 2 (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
op3b_reg HS (3%bv : bv 5) (YK11.getr regs' (Z_to_bv 5 3)) Q3
  ltac:(cbn [sv_denot]; rewrite (op3b_ew regs' 3 (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
op3b_reg HS (4%bv : bv 5) (YK11.getr regs' (Z_to_bv 5 4)) Q4
  ltac:(cbn [sv_denot]; rewrite (op3b_ew regs' 4 (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
op3b_reg HS (8%bv : bv 5) (YK11.getr regs' (Z_to_bv 5 8)) Q8
  ltac:(cbn [sv_denot]; rewrite (op3b_ew regs' 8 (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
op3b_reg HS (9%bv : bv 5) (YK11.getr regs' (Z_to_bv 5 9)) Q9
  ltac:(cbn [sv_denot]; rewrite (op3b_ew regs' 9 (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
op3b_reg HS (18%bv : bv 5) (YK11.getr regs' (Z_to_bv 5 18)) Q18
  ltac:(cbn [sv_denot]; rewrite (op3b_ew regs' 18 (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
op3b_reg HS (20%bv : bv 5) (YK11.getr regs' (Z_to_bv 5 20)) Q20
  ltac:(cbn [sv_denot]; rewrite (op3b_ew regs' 20 (Z_to_bv 5 20) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
op3b_reg HS (21%bv : bv 5) (YK11.getr regs' (Z_to_bv 5 21)) Q21
  ltac:(cbn [sv_denot]; rewrite (op3b_ew regs' 21 (Z_to_bv 5 21) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
op3b_reg HS (23%bv : bv 5) (YK11.getr regs' (Z_to_bv 5 23)) Q23
  ltac:(cbn [sv_denot]; rewrite (op3b_ew regs' 23 (Z_to_bv 5 23) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
op3b_reg HS (24%bv : bv 5) (YK11.getr regs' (Z_to_bv 5 24)) Q24
  ltac:(cbn [sv_denot]; rewrite (op3b_ew regs' 24 (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
op3b_reg HS (26%bv : bv 5) (YK11.getr regs' (Z_to_bv 5 26)) Q26
  ltac:(cbn [sv_denot]; rewrite (op3b_ew regs' 26 (Z_to_bv 5 26) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
op3b_reg HS (22%bv : bv 5) (w64 7) Q22 ltac:(reflexivity).
destruct (op3b_kept0 cx ly' S' W regs' mem' md' e (ms_mem ms) 0 LAWS HB HC KR) as (KA & KB & KF).
pose proof (lc_core_kept B MT XL RLO RHI cx ly' S' W regs' mem' md' e 0 ly' S' W regs' (ms_mem ms) _ e
  LAWS HB HC HJ eq_refl (Permutation_refl _) (fun r _ => eq_refl) ltac:(unfold LLVMF_STK; lia) KA KB KF) as HC5.
pose proof (op3b_core_regs cx ly' S' W regs' (ms_mem ms) _ e (ms_regs ms) HC5 Q2 Q3 Q4 Q8 Q9) as HC6.
pose proof (op3b_lcore_next cx op (lo_k op) ly' S' W regs' mem' md' e ly' S' W (ms_regs ms) (ms_mem ms) _ 0 HP HB HL
  HC6 Q18 Q21 Q26 ltac:(lia) KA KF (mle_start MT S' MTL)) as HL5.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
  apply SRr_ret;
  exists ly', S', (ms_regs ms), (ms_mem ms), mdx, e, 1, B4, (lc_tick_c (l_pl cx) (lc_oc (l_pl cx) (lo_c op))),
    (lo_k op)
end.
split; [unfold lc_cfg; rewrite op3b_base; reflexivity|].
split; [exact HL5|].
split; [unfold recv_addr_ok; op3b_lia|].
split; [exact Hop|].
split.
{ apply (tw_kept TMAP_A (aview segs (w_H W) mem')); [exact Htw|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  apply KR. op3b_lia. }
split; [destruct HCUR as (H24 & H23); split; [exact (eq_trans Q24 H24) | exact (eq_trans Q23 H23)]|].
split; [exact (eq_trans Q20 R20) | exact Q22].
Qed.

(* ------------------------------------------------------------------ *)
(* 6. The segment                                                      *)
(* ------------------------------------------------------------------ *)

Lemma lc_op3b_ok (HK1 : lc_rom_view_stmt B MT XL RLO RHI) (HK6 : lc_runinv_stmt) :
  lc_op3b_stmt B MT XL RLO RHI.
Proof.
unfold lc_op3b_stmt. intros HP cx op W' c' HB HT.
destruct HT as (ly' & S' & regs' & mem' & md' & e & B1 & HT). cbv zeta in HT.
destruct HT as (Hc & Ho & HL & Hob & Htw & R22 & HCUR & R20).
pose proof HL as (_ & _ & _ & _ & (HA & Hops & Hcin & _ & _) & _).
destruct (op3b_model (l_pl cx) (lo_ops op) (lo_B op) B1 (lo_c op) (lo_k op) HA Hops Hcin Ho Hob)
  as (B3 & B4 & r & E3 & E4 & E5 & Eop & HA4).
pose proof (SL.agree_op_begin timg_A (lo_ops op) (lo_B op) B1 HA Hob) as HA1.
destruct (op3b_inv3 (l_pl cx) (lo_ops op) B1 B3 (lc_oc (l_pl cx) (lo_c op)) HK6 HA1 E3) as (HRI & Hgf3 & Hgn3).
destruct (HK6 (lo_ops op + 1) B4 HA4) as (_ & Hq4 & _).
subst c'.
eapply SRr_bind; [exact (op3b_s1 cx op ly' S' W' regs' mem' md' e _ B3 HP HB HL Htw HCUR R20 E3)|].
intros W2 c2 _ H2.
eapply SRr_bind.
{ refine (op3b_s2 cx op B3 B4 r W2 c2 HK1 HP HB HRI Hgf3 E4 _).
  refine (op3b_at_mono cx op 0x974 B3 _ _ W2 c2 _ H2).
  intros regs Hr. exact (eq_trans Hr (eq_trans R22 (f_equal w64 (eq_sym Hgn3)))). }
intros W3 c3 _ H3.
eapply SRr_bind; [exact (op3b_s3 cx op B4 W3 c3 HP HB E5 Hq4 H3)|].
intros W4 c4 _ H4.
exact (op3b_s4 cx op B4 W4 c4 HP HB Eop H4).
Qed.

End op3b.
