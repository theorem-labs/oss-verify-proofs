(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AFip.v (segA: the run of a
   wrapper over its own instruction table, the application of a runtime-entry contract at a call site and the
   rebuilding of the symbolic state after the call), A/AFis.v (at_ST's frame and window conjuncts,
   kept_of_frame, chunk_val_at) and A/AF0x.v (st_ok_pin_reg, the val_mem / apresent / fpchain helpers) to
   libreac/fuzz_decode's calloc wrapper in image A (fuzz_decode.asan); module paths changed, and every address,
   cell and offset below is decode's own. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/DecodeCallocWrap.v, with its module paths and module names changed; 3365 of its 3449 lines of code are new or changed and 788 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/LLVMFuzzerTestOneInput_seg_cfg.v, with its module paths and module names changed; 789 of its 923 lines of code are new or changed and 3315 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op3b: Lemma lc_op3b_ok : lc_op3b_stmt (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v), the
   segment OP3B of the image-B walk of LLVMFuzzerTestOneInput: offsets +0xcf4 .. +0xd10 and +0xe88 .. +0xe8c of the
   listing lib/B/Prog/DgnTransportBList.v (fuzz_transport.asan-ubsan 0x81f94 .. 0x81fb0 and 0x82128 .. 0x8212c), from
   the cut lc_st_tick (TICK) to the cut lc_st_tail (TAIL).

   What the code does. +0xcf4 `jal m_tick` (return +0xcf8); +0xcf8 `ld a1, 0x68c(s6)` (g_now read again through
   s6 = transportb_hi 9, g_now's page); +0xcfc / +0xd00 a0 = &g_s (auipc / addi); +0xd04 `jal diginet_session_tick`
   (return +0xd08); +0xd08 `li a0, 1`; +0xd0c `jal settle` (return +0xd10); +0xd10 `j +0xe88`; +0xe88 `li s6, 1`;
   +0xe8c `j +0x1670`, the tail cut. The segment reaches no __asan_report_* call and no UBSan trap branch.

   The load of g_now. The run from +0xcf8 starts from a symbolic state with one read-only region, based at the atom of
   s6 (register 22): the eight bytes at s6 + 0x68c = TB_g_now hold the world's g_now (TWorldG.v tw_read_val), the
   value of atom 32 of the run's valuation. So a1 = g_now of m_tick's world, the tick's now.

   The callees. m_tick and diginet_session_tick are G-form callees composed in the walk's own G journal (their
   statements lp_mtick, lp_tick); settle is a donor-form callee, lifted by TransportGCg.v gx_call_cg (lp_settle). Each
   is entered with sp = sp1 (the realigned sp, callee-saved), gp / tp of the entry and ra = its return address; its
   post gives the next cut by LLVMFuzzerTestOneInput_st.v lc_core_kept: what it keeps above alloc_ceiling (the spill
   slots and the saved words lie above sp1, its window below), the input's bytes, the class-2 frame's bytes (its last
   word among them), their presence, and the frame's shadow, none of which is a byte the callee writes (each written
   range lies in G: op3b_mtick_wr_G, op3b_tick_wr_G; a byte of G is an image byte, a block or frame byte is not:
   AR_laws' al_client_img; the shadow lies above G's hull).

   The model. Op3Ok.v op3_ok gives the operation's Some at the stream fun _ => 1 (op 3 reads no stream) and
   agree timg_B (ops + 1) at its world; LLVMFuzzerTestOneInput_st.v lc_tick_eq splits it into m_tick_m, the tick and
   settle 1, whose world is the tick's (lc_settle_world). The tick's premises at m_tick's world: the run invariants
   by K6 (lc_runinv_stmt) at op_begin's world (SimLib.v agree_op_begin) carried over the g_now store (TRunInv.v
   rk_upd) and m_tick (m_tick_rk, rk_out); g_fail_next is not a byte m_tick_m writes (TIoRecv.v m_tick_gk), so it
   stays below 2; the read-only bytes by K1 (lc_rom_view_stmt); TF = None. settle's queue-length invariant at the
   tick's world: K6 at agree timg_B (ops + 1). The kit statements the proof takes as arguments: K1 lc_rom_view_stmt
   and K6 lc_runinv_stmt. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0 YE2k YCfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
m_set_cg notice_cg io_send_cg diginet_body_check_cg send_data_cg m_tick_cg diginet_session_tick_cg settle_cg receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TOps
  TWorldLemmas TRunInv TIoRecv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts SimLib Op3Ok LinksProof.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module TRI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TRunInv.
Module TIR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TIoRecv.
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
   g_now of m_tick's world, settle 1 keeping the tick's world, the operation's equation at the stream fun _ => 1 and
   agree at ops + 1. *)
Lemma op3b_model : forall (D : list byte) (ops : Z) (B0 B1 : list byte) (c : TOP.fuzz_in) (k : nat),
  AG.agree timg_B ops B0 -> 0 <= ops < TC.OPS_MAX -> QF.fuzz_in_ok D c -> lc_opc D c = 3 ->
  TC.op_begin_m B0 = Some (B1, tt) ->
  exists B3 B4 r,
    TC.m_tick_m (lc_tick_w D (lc_oc D c) B1) = Some (B3, tt) /\
    TSS.diginet_session_tick_m timg_B None B3 (TW.g_now B3) = Some (B4, r) /\
    TC.settle_m B4 1 = Some (B4, tt) /\
    TOP.LLVMFuzzerTestOneInput_op_m timg_B B0 (fun _ => 1) D c k = Some (B4, (lc_tick_c D (lc_oc D c), k)) /\
    AG.agree timg_B (ops + 1) B4.
Proof.
intros D ops B0 B1 c k HA Hops Hc Ho Hob.
destruct (O3.op3_ok LP.links_holds timg_B ops B0 (fun _ => 1) D c k HA (proj2 Hops) Hc Ho)
  as (B' & c' & E & HA' & _).
pose proof E as E0.
rewrite (lc_tick_eq timg_B B0 (fun _ => 1) D c k Ho), Hob in E. cbv beta iota in E.
destruct (TC.m_tick_m (lc_tick_w D (lc_oc D c) B1)) as [[B3 []]|] eqn:E3; [|discriminate E].
cbv beta iota in E.
destruct (TSS.diginet_session_tick_m timg_B None B3 (TW.g_now B3)) as [[B4 r]|] eqn:E4; [|discriminate E].
cbv beta iota in E.
destruct (TC.settle_m B4 1) as [[B5 []]|] eqn:E5; [|discriminate E].
cbv beta iota in E.
destruct (lc_some3 _ _ _ _ _ _ _ eq_refl E) as (EB & EC & _).
pose proof (lc_settle_world B4 B5 1 tt E5) as E54.
rewrite E54 in EB, E5. subst B'. subst c'.
exists B3, B4, r. refine (conj _ (conj E4 (conj E5 (conj E0 HA')))). first [exact E3 | reflexivity].
Qed.

(* The tick's premises at m_tick's world B3, from K6 at op_begin's world B1: the run invariants (TRunInv.v run_inv)
   and g_fail_next <= 1. *)
Lemma op3b_inv3 : forall (D : list byte) (ops : Z) (B1 B3 : list byte) (c1 : TOP.fuzz_in),
  lc_runinv_stmt -> AG.agree timg_B ops B1 ->
  TC.m_tick_m (lc_tick_w D c1 B1) = Some (B3, tt) ->
  TRI.run_inv B3 /\ TW.g_fail_next B3 <= 1.
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
assert (HLt' : length (lc_tick_w D c1 B1) = Z.to_nat TW.W_LEN) by (rewrite <- HLt, Nat2Z.id; reflexivity).
destruct (TIR.m_tick_gk (lc_tick_w D c1 B1) HLt' (lc_tick_w D c1 B1) B3 tt (TIR.gkeep_refl _) E3) as (_ & Hf).
split; [exact HR3|].
rewrite Hf, Ev, (op3b_now_gfn B1 v HL1z). exact Igf.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The written ranges of the callees lie in G                       *)
(* ------------------------------------------------------------------ *)

(* A payload byte of a row of TMAP_B is a byte of G. *)
Lemma op3b_row_G : forall o b n a, In (o, b, n) TMAP_B -> b <= a < b + n -> inG TG.G_HARNESS_B a.
Proof.
intros o b n a Hin Ha. unfold inG. apply Exists_exists. exists (b, n).
split; [exact (TMAP_B_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* A field of a row's payload is a byte of G. *)
Lemma op3b_fld_G : forall o b n A k a, twb_fld o b A k a -> In (o, b, n) TMAP_B -> o <= A -> A + k <= o + n ->
  inG TG.G_HARNESS_B a.
Proof. intros o b n A k a Ha Hin H1 H2. unfold twb_fld in Ha. apply (op3b_row_G o b n a Hin). lia. Qed.

(* The same with the place inside the row as one closed boolean (a field at a constant offset). *)
Lemma op3b_fld_Gb : forall o b n A k a, twb_fld o b A k a -> In (o, b, n) TMAP_B ->
  ((o <=? A) && (A + k <=? o + n))%bool = true -> inG TG.G_HARNESS_B a.
Proof.
intros o b n A k a Ha Hin Hb. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exact (op3b_fld_G o b n A k a Ha Hin H1 H2).
Qed.

(* A twb_fld fact at a constant offset of one of the rows the callees write (no world term in it). *)
Local Ltac op3b_fld H :=
  first [ exact (op3b_fld_Gb _ _ _ _ _ _ H TMAP_B_M eq_refl)
        | exact (op3b_fld_Gb _ _ _ _ _ _ H TMAP_B_g_s eq_refl)
        | exact (op3b_fld_Gb _ _ _ _ _ _ H TMAP_B_g_q eq_refl)
        | exact (op3b_fld_Gb _ _ _ _ _ _ H TMAP_B_g_fail_next eq_refl)
        | exact (op3b_fld_Gb _ _ _ _ _ _ H TMAP_B_g_last_counter eq_refl)
        | exact (op3b_fld_Gb _ _ _ _ _ _ H TMAP_B_g_nq eq_refl)
        | exact (op3b_fld_Gb _ _ _ _ _ _ H TMAP_B_GOT eq_refl)
        | exact (op3b_fld_Gb _ _ _ _ _ _ H TMAP_B_OW eq_refl) ].

(* The indexed fields, each at an index bounded by a premise (an abstract index: lia on the offsets). *)
Lemma op3b_ow_t_G : forall i a, 0 <= i < TC.TRANS_MAX ->
  twb_fld TW.OFF_OW TB_OW (TW.A_OW_t_state i) TW.OW_t_ESZ a -> inG TG.G_HARNESS_B a.
Proof.
intros i a Hi H. apply (op3b_fld_G _ _ _ _ _ a H TMAP_B_OW);
  unfold TW.A_OW_t_state, TW.OFF_OW, TW.SZ_OW, TW.OW_t_ESZ, TC.TRANS_MAX in *; lia.
Qed.
Lemma op3b_got_t_G : forall i a, 0 <= i < TC.TRANS_MAX ->
  twb_fld TW.OFF_GOT TB_GOT (TW.A_GOT_t_state i) TW.GOT_t_ESZ a -> inG TG.G_HARNESS_B a.
Proof.
intros i a Hi H. apply (op3b_fld_G _ _ _ _ _ a H TMAP_B_GOT);
  unfold TW.A_GOT_t_state, TW.OFF_GOT, TW.SZ_GOT, TW.GOT_t_ESZ, TC.TRANS_MAX in *; lia.
Qed.
Lemma op3b_cmd_G : forall s a, 0 <= s < TC.CMDS_MAX ->
  twb_fld TW.OFF_g_cmd TB_g_cmd (TW.A_Cmd_st s) 4 a -> inG TG.G_HARNESS_B a.
Proof.
intros s a Hs H. apply (op3b_fld_G _ _ _ _ _ a H TMAP_B_g_cmd);
  unfold TW.A_Cmd_st, TW.OFF_g_cmd, TW.SZ_g_cmd, TC.CMDS_MAX in *; lia.
Qed.
Lemma op3b_q_G : forall q a, 0 <= q < TW.S_queue_N ->
  twb_fld TW.OFF_g_s TB_g_s (TW.A_S_queue_bytes q) TW.S_queue_ESZ a -> inG TG.G_HARNESS_B a.
Proof.
intros q a Hq H. apply (op3b_fld_G _ _ _ _ _ a H TMAP_B_g_s);
  unfold TW.A_S_queue_bytes, TW.OFF_g_s, TW.SZ_g_s, TW.S_queue_ESZ, TW.S_queue_N in *; lia.
Qed.
Lemma op3b_fly_G : forall n a,
  twb_fld TW.OFF_M TB_M TW.A_M_fly_frame (Z.min n TC.SPEC_MAX_FRAME) a -> inG TG.G_HARNESS_B a.
Proof.
intros n a H. pose proof (Z.le_min_r n TC.SPEC_MAX_FRAME) as Hm.
apply (op3b_fld_G _ _ _ _ _ a H TMAP_B_M); unfold TW.A_M_fly_frame, TW.OFF_M, TW.SZ_M, TC.SPEC_MAX_FRAME in *; lia.
Qed.

(* m_set's stores (m_set_cg.v mset_st_wr: OW.t[OW.n].state, OW.n, M.state). *)
Lemma op3b_mset_G : forall Bw st a, mset_st_wr Bw st a -> inG TG.G_HARNESS_B a.
Proof.
intros Bw st a (_ & H). unfold mset_wr in H.
destruct H as [(Hn & H) | [H | H]]; [exact (op3b_ow_t_G _ a Hn H) | op3b_fld H | op3b_fld H].
Qed.

(* m_tick's stores (m_tick_cg.v mtick_wr: m_lost's two stores in M and m_set's). *)
Lemma op3b_mtick_wr_G : forall Bw a, mtick_wr Bw a -> inG TG.G_HARNESS_B a.
Proof.
intros Bw a (_ & H). unfold mlost_wr in H.
destruct H as [H | [H | H]]; [op3b_fld H | op3b_fld H | exact (op3b_mset_G Bw TC.S_IDLE a H)].
Qed.

(* notice's stores (notice_cg.v notice_wr: GOT and M.fly.on). *)
Lemma op3b_notice_G : forall Bw n a, notice_wr Bw n a -> inG TG.G_HARNESS_B a.
Proof.
intros Bw n a H. unfold notice_wr in H.
destruct H as [(_ & [(Hn & H) | H]) | [(_ & H) | [(_ & H) | [(_ & H) | [(_ & H) | (_ & H)]]]]];
  [exact (op3b_got_t_G _ a Hn H) | op3b_fld H | op3b_fld H | op3b_fld H | op3b_fld H | op3b_fld H | op3b_fld H].
Qed.

(* io_send's stores (io_send_cg.v iosend_wr). *)
Lemma op3b_iosend_G : forall n a, iosend_wr n a -> inG TG.G_HARNESS_B a.
Proof.
intros n a H. unfold iosend_wr in H.
destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[(s & Hs & H)|[H|H]]]]]]]]]]]]]]]]]];
  [op3b_fld H | op3b_fld H | op3b_fld H | op3b_fld H | op3b_fld H | op3b_fld H | op3b_fld H | op3b_fld H
  | op3b_fld H | op3b_fld H | op3b_fld H | op3b_fld H | op3b_fld H | op3b_fld H | op3b_fld H
  | exact (op3b_fly_G n a H) | exact (op3b_cmd_G s a Hs H) | op3b_fld H | op3b_fld H].
Qed.

(* send_data's stores (send_data_cg.v senddata_wr). *)
Lemma op3b_sd_G : forall a, senddata_wr a -> inG TG.G_HARNESS_B a.
Proof.
intros a H. unfold senddata_wr in H.
destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]];
  [op3b_fld H | op3b_fld H | op3b_fld H | op3b_fld H | op3b_fld H | op3b_fld H | op3b_fld H | op3b_fld H
  | op3b_fld H | exact (op3b_iosend_G _ a H)].
Qed.

(* diginet_session_tick's stores (diginet_session_tick_cg.v tick_wr). *)
Lemma op3b_tick_wr_G : forall Bw a, tick_wr Bw a -> inG TG.G_HARNESS_B a.
Proof.
intros Bw a H. unfold tick_wr in H.
destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[(q & Hq & H)|[H|H]]]]]]]]]]]]]]]]]]];
  [op3b_fld H | op3b_fld H | op3b_fld H | op3b_fld H | op3b_fld H | op3b_fld H | op3b_fld H | op3b_fld H
  | op3b_fld H | op3b_fld H | op3b_fld H | op3b_fld H | op3b_fld H
  | exact (op3b_notice_G _ _ a H) | exact (op3b_notice_G _ _ a H) | exact (op3b_notice_G _ _ a H)
  | exact (op3b_iosend_G _ a H) | exact (op3b_q_G q a Hq H) | op3b_fld H | exact (op3b_sd_G a H)].
Qed.

(* A payload byte of the world table is a byte of G. *)
Lemma op3b_tw_in_G : forall x, tw_in TMAP_B x -> inG TG.G_HARNESS_B x.
Proof. intros x (o & b & n & Hin & Hx). exact (op3b_row_G o b n x Hin Hx). Qed.

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
(* The write right of a run whose regions have no writable byte. *)
Ltac op3b_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia |]);
  apply awr_ok_x_nil.
(* A run whose regions have no writable byte writes no byte. *)
Ltac op3b_keep_tac HFr KR W mold msn :=
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) (ms_mem msn) a = aview tfibsegs (w_H W) mold a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    apply (YC4b.kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []];
    let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
    let Hin := fresh "Hin" in let Hx := fresh "Hx" in
    intros b wlo whi x Hin Hx;
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
    cbn [In] in Hin;
    repeat (let He := fresh "He" in destruct Hin as [He | Hin];
      [ let E1 := fresh "E" in let E2 := fresh "E" in let E3 := fresh "E" in
        injection He as E1 E2 E3; subst wlo whi; lia |]);
    destruct Hin
  | ].

Section env. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Definition op3b_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).
Definition op3b_B0 : Z * Z := (0, 0).
Definition op3b_Bx : sv := SLit 0.

Lemma op3b_base : BASE = transportb_text.
Proof. vm_compute. reflexivity. Qed.

Lemma op3b_ew : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (op3b_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold op3b_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma op3b_img : forall regs, img_env VAL A_LIM (op3b_E regs).
Proof. intros regs. unfold op3b_E. apply Eimg_env. Qed.
Lemma op3b_agree : forall regs, env_agree 32 (Ereg regs []) (op3b_E regs).
Proof. intros regs. split; [intros m Hm; unfold op3b_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* A symbolic state with no region holds of any machine state at its pc. *)
Lemma op3b_entry : forall (W : world segs) regs mem (pc : Z),
  st_ok_pi segs VAL (op3b_E regs) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem pc. rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* The run from +0xcf8: the valuation with atom 32 = g_now, and the read-only region of g_now's eight bytes at
   s6 + 0x68c (s6 = transportb_hi 9, atom 22). *)
Definition op3b_E2 (regs : bvmap 5 word) (v : Z) : env := Eimg (PI := PI_transportb) (Ereg regs [Z_to_bv 64 v]).
Definition op3b_rg : YP09.region :=
  YP09.mkRegion (Some 22%nat) 0x68c 0x694 0 0 [YP09.mkChunk 0x68c (YP09.CVal 8 (SOff 32 0))].

Lemma op3b_img2 : forall regs v, img_env VAL A_LIM (op3b_E2 regs v).
Proof. intros regs v. unfold op3b_E2. apply Eimg_env. Qed.
Lemma op3b_agree2 : forall regs v, env_agree 32 (Ereg regs [Z_to_bv 64 v]) (op3b_E2 regs v).
Proof. intros regs v. split; [intros m Hm; unfold op3b_E2; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma op3b_ew2 : forall regs v n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (op3b_E2 regs v) n = YK11.getr regs r.
Proof. intros regs v n r Hn. unfold op3b_E2. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma op3b_e32 : forall regs v, ew (op3b_E2 regs v) 32 = Z_to_bv 64 v.
Proof.
intros regs v. unfold op3b_E2. rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_extra regs [Z_to_bv 64 v] 0).
Qed.
Lemma op3b_den32 : forall regs v, 0 <= v < 2 ^ 64 -> sv_denot (op3b_E2 regs v) (SOff 32 0) = Z_to_bv 64 v.
Proof. intros regs v Hv. cbn [sv_denot]. rewrite op3b_e32, unsigned_lit_small, Z.add_0_r by exact Hv. reflexivity. Qed.

(* An image object's address under either valuation. *)
Lemma op3b_sv_obj : forall E k v, img_env VAL A_LIM E -> (A_TEXT <= k < A_LIM)%nat -> VAL k = v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff k 0) = w64 v.
Proof.
intros E k v HE Hk Hv Hr. cbn [sv_denot]. rewrite (HE k Hk), Hv, Z.add_0_r. reflexivity.
Qed.

Lemma op3b_entry2 : forall (W : world segs) regs mem (Bw : list byte),
  tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 22 = w64 (transportb_hi 9) ->
  st_ok_pi segs VAL (op3b_E2 regs (TW.g_now Bw)) (mkSS 3320 sr_atoms [op3b_rg] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 3320)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem Bw Htw R22.
  pose proof (TWL.u_at_range Bw TW.OFF_g_now 8) as Rn. change (8 * Z.of_nat 8) with 64 in Rn.
  assert (Rn' : 0 <= TW.g_now Bw < 2 ^ 64) by exact Rn.
  assert (B22 : base_val (op3b_E2 regs (TW.g_now Bw)) (Some 22%nat) = 0x5de6f4).
  { cbn [base_val]. rewrite (op3b_ew2 regs (TW.g_now Bw) 22 (Z_to_bv 5 22) eq_refl).
    assert (R22' : YK11.getr regs (Z_to_bv 5 22) = w64 0x5de6f4) by exact R22.
    rewrite R22'. unfold w64. apply unsigned_lit_small. lia. }
  rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold op3b_rg, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B22.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs (op3b_E2 regs (TW.g_now Bw)) _ 0x5de6f4 0x68c 8 (SOff 32 0) (TW.g_now Bw));
      [exact (op3b_den32 regs (TW.g_now Bw) Rn') | exact Rn' | lia |].
    replace (0x5de6f4 + 0x68c) with (TB_g_now + 0) by (unfold TB_g_now; lia).
    exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_now TB_g_now TW.SZ_g_now 0 8 TMAP_B_ok Htw TMAP_B_g_now
      ltac:(lia) ltac:(unfold TW.SZ_g_now; lia)).
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.
End env.

(* ------------------------------------------------------------------ *)
(* 4. The walk's facts across a run and a call                         *)
(* ------------------------------------------------------------------ *)

Section op3b. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The states between the calls: the loop's common facts at operation op with lo_k op receptions, the world relation
   at Bw, the cursor after the u16 in s8 / s11, s4 = c, and R of the registers. *)
Definition op3b_at (cx : lcx) (op : lop) (off : Z) (Bw : list byte) (R : bvmap 5 word -> Prop)
    : world segs -> config -> Prop :=
  fun W c => exists ly S regs mem md e,
    c = lc_cfg cx off regs mem md /\
    lc_lcore B MT cx op false false (lo_k op) ly S W regs mem md e /\
    lc_tw W mem Bw /\
    lc_cur cx regs 24 27 (lc_tick_c (l_pl cx) (lc_oc (l_pl cx) (lo_c op))) /\
    YK11.getr regs 20 = w64 (lc_F cx + 32) /\ R regs.

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
split; [rewrite R1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [exact Hk | exact Hk2]|].
split.
{ change (raZ regsX) with (bv_unsigned (YK11.getr regsX 1)). rewrite R1, op3b_base.
  rewrite unsigned_lit_small by (unfold transportb_text; op3b_lia). unfold transportb_text. lia. }
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
   G: the bytes above alloc_ceiling outside the call's window, the input's bytes, the frame's and its shadow's bytes,
   and the presence of the frame's bytes. *)
Lemma op3b_kept : forall cx ly' S' (W' : world segs) regs' mem' md' e (memX : word -> option byte)
    (W2 : world segs) mem2 (X : Z) (E : Z -> Prop),
  AR_laws segs B -> lc_base B MT XL RLO RHI cx -> lc_core B cx ly' S' W' regs' mem' md' e ->
  (forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W') memX a = aview segs (w_H W') mem' a) ->
  (forall a, E a -> inG TG.G_HARNESS_B a) ->
  acall_kept_g segs B TG.G_HARNESS_B ly' S' W' memX W2 mem2 (lc_sp1 cx - X) (lc_sp1 cx) E ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - X <= a < lc_sp1 cx) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a) /\
  (forall i, 0 <= i < l_n cx -> aview segs (w_H W2) mem2 (l_p cx + i) = aview segs (w_H W') mem' (l_p cx + i)) /\
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES \/ lc_SH cx <= a < lc_SH cx + 32 ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a) /\
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES -> apresent (w_H W') mem' a -> apresent (w_H W2) mem2 a).
Proof.
intros cx ly' S' W' regs' mem' md' e memX W2 mem2 X E LAWS HB HC KR HEG HK.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HAR _ _ _ HFaddr HFin Hn HINg _].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF4096 & _ & HFce & _).
destruct HK as (K1 & K2 & _ & K4 & _).
pose proof asan_consts as ((CVlo & CVhi) & _).
assert (HF8 : 0 <= lc_F cx / 8 <= lc_F cx) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
unfold LF_FBYTES in *.
assert (KF : forall a, lc_F cx <= a < lc_F cx + 256 \/ lc_SH cx <= a < lc_SH cx + 32 ->
  aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a).
{ intros a Ha.
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
    * pose proof (inG_G_HARNESS_hull a (HEG a Hw)) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
      unfold lc_SH, SHADOW_OFF in Ha. lia. }
split; [|split; [|split]].
- intros a Ha Hn'. rewrite (K1 a Ha Hn'). apply KR. lia.
- intros i Hi.
  destruct Hn as (Hn1 & _).
  pose proof (HINg ltac:(lia)) as InP.
  destruct (req_size_pos (l_n cx) ltac:(lia)) as (_ & Hq).
  destruct (al_blocks _ _ LAWS ly' S' W' mem' md' (l_p cx) (l_n cx) HAR InP) as (_ & H4096 & Hbc & _).
  rewrite (K2 (l_p cx) (l_n cx) i InP ltac:(lia)).
  + apply KR. op3b_lia.
  + intros Hw. assert (Hr : l_p cx <= l_p cx + i < l_p cx + req_size (l_n cx)) by lia.
    apply (proj2 (al_client_img _ _ LAWS ly' S' W' mem' md' (l_p cx + i) HAR
      (or_introl (ex_intro _ (l_p cx) (ex_intro _ (l_n cx) (conj InP Hr)))))).
    exact (trans_g_img _ (HEG _ Hw)).
- exact KF.
- intros a Ha Hp. apply (apresent_transfer segs (w_H W') (w_H W2) mem' mem2 a).
  + op3b_lia.
  + apply (frm_img segs B LAWS ly' S' W' mem' md' LF_CID (l_fpos cx) a HAR HFin).
    rewrite HFaddr. change (fs_frame_bytes LF_CID) with 256. exact Ha.
  + exact (KF a (or_introl Ha)).
  + exact Hp.
Qed.

(* The same for a run alone (no call): every byte is kept. *)
Lemma op3b_kept0 : forall cx ly' S' (W' : world segs) regs' mem' md' e (memX : word -> option byte),
  AR_laws segs B -> lc_base B MT XL RLO RHI cx -> lc_core B cx ly' S' W' regs' mem' md' e ->
  (forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W') memX a = aview segs (w_H W') mem' a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - 0 <= a < lc_sp1 cx) ->
     aview segs (w_H W') memX a = aview segs (w_H W') mem' a) /\
  (forall i, 0 <= i < l_n cx -> aview segs (w_H W') memX (l_p cx + i) = aview segs (w_H W') mem' (l_p cx + i)) /\
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES \/ lc_SH cx <= a < lc_SH cx + 32 ->
     aview segs (w_H W') memX a = aview segs (w_H W') mem' a) /\
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES -> apresent (w_H W') mem' a -> apresent (w_H W') memX a).
Proof.
intros cx ly' S' W' regs' mem' md' e memX LAWS HB HC KR.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HAR _ _ _ HFaddr HFin Hn HINg _].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF4096 & _ & HFce & _).
pose proof asan_consts as ((CVlo & CVhi) & _).
assert (HF8 : 0 <= lc_F cx / 8 <= lc_F cx) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
unfold LF_FBYTES in *.
split; [|split; [|split]].
- intros a Ha _. apply KR. lia.
- intros i Hi.
  destruct Hn as (Hn1 & _).
  pose proof (HINg ltac:(lia)) as InP.
  destruct (req_size_pos (l_n cx) ltac:(lia)) as (_ & Hq).
  destruct (al_blocks _ _ LAWS ly' S' W' mem' md' (l_p cx) (l_n cx) HAR InP) as (_ & H4096 & Hbc & _).
  apply KR. op3b_lia.
- intros a Ha. apply KR. unfold lc_SH, SHADOW_OFF in Ha. op3b_lia.
- intros a Ha Hp. apply (apresent_transfer segs (w_H W') (w_H W') mem' memX a).
  + op3b_lia.
  + apply (frm_img segs B LAWS ly' S' W' mem' md' LF_CID (l_fpos cx) a HAR HFin).
    rewrite HFaddr. change (fs_frame_bytes LF_CID) with 256. exact Ha.
  + apply KR. op3b_lia.
  + exact Hp.
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

(* The loop's common facts at the next state, from the core there: s2 / s10 and s3 kept, the spill slots and the
   frame's shadow kept, the operation's start facts, the events and the meter (no charge). *)
Lemma op3b_lcore_next : forall cx op k ly' S' (W' : world segs) regs' mem' md' e
    ly2 S2 (W2 : world segs) regs2 mem2 md2 (X : Z),
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx ->
  lc_lcore B MT cx op false false k ly' S' W' regs' mem' md' e ->
  lc_core B cx ly2 S2 W2 regs2 mem2 md2 e ->
  YK11.getr regs2 18 = YK11.getr regs' 18 -> YK11.getr regs2 19 = YK11.getr regs' 19 ->
  YK11.getr regs2 26 = YK11.getr regs' 26 ->
  0 <= X ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - X <= a < lc_sp1 cx) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a) ->
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES \/ lc_SH cx <= a < lc_SH cx + 32 ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a) ->
  mo_le MT S' S2 0 ->
  lc_lcore B MT cx op false false k ly2 S2 W2 regs2 mem2 md2 e.
Proof.
intros cx op k ly' S' W' regs' mem' md' e ly2 S2 W2 regs2 mem2 md2 X HP HB HL HC2 E18 E19 E26 HX KA KF HMO.
pose proof (lp_meter_laws _ _ _ _ _ HP) as MTL.
destruct HL as (HC & (R18 & R26) & HSP & HFSH & HOK & He & (Hmle & Hmok) & R19).
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
- exact (eq_trans E19 R19).
Qed.

Lemma op3b_cur_kept : forall cx (r1 r2 : bvmap 5 word) c,
  aregs_preserved r1 r2 -> lc_cur cx r1 24 27 c -> lc_cur cx r2 24 27 c.
Proof.
intros cx r1 r2 c HP (H24 & H27). split.
- exact (eq_trans (HP 24 ltac:(unfold acallee_saved; lia)) H24).
- exact (eq_trans (HP 27 ltac:(unfold acallee_saved; lia)) H27).
Qed.

(* lc_core at a callee's return, from lc_core_kept and op3b_kept's four facts. *)
Lemma op3b_core_call : forall cx ly' S' (W' : world segs) regs' mem' md' e (X : Z) ly2 S2 (W2 : world segs)
    regs2 mem2 md2,
  lc_base B MT XL RLO RHI cx -> lc_core B cx ly' S' W' regs' mem' md' e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly2 S2 W2 mem2 md2 e ->
  frames S2 = frames S' -> Permutation (ablocks B ly2 S2) (ablocks B ly' S') ->
  aregs_preserved regs' regs2 -> 0 <= X <= LLVMF_STK - 336 ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - X <= a < lc_sp1 cx) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a) ->
  (forall i, 0 <= i < l_n cx -> aview segs (w_H W2) mem2 (l_p cx + i) = aview segs (w_H W') mem' (l_p cx + i)) ->
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES \/ lc_SH cx <= a < lc_SH cx + 32 ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a) ->
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES -> apresent (w_H W') mem' a -> apresent (w_H W2) mem2 a) ->
  lc_core B cx ly2 S2 W2 regs2 mem2 md2 e.
Proof.
intros cx ly' S' W' regs' mem' md' e X ly2 S2 W2 regs2 mem2 md2 HB HC HJ2 HFR2 HP2 HPR HX KA KI KF GA.
apply (lc_core_kept B MT XL RLO RHI cx ly' S' W' regs' mem' md' e X ly2 S2 W2 regs2 mem2 md2 e HB HC HJ2 HFR2 HP2
  HPR HX KA KI); [|exact GA].
intros a Ha. apply KF. left. unfold LF_FBYTES in *. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The four pieces                                                  *)
(* ------------------------------------------------------------------ *)

(* +0xcf4: `jal m_tick`; the return at +0xcf8. *)
Lemma op3b_s1 : forall (cx : lcx) (op : lop) ly' S' (W' : world segs) regs' mem' md' e (Bt B3 : list byte),
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx ->
  lc_lcore B MT cx op false false (lo_k op) ly' S' W' regs' mem' md' e ->
  lc_tw W' mem' Bt ->
  lc_cur cx regs' 24 27 (lc_tick_c (l_pl cx) (lc_oc (l_pl cx) (lo_c op))) ->
  YK11.getr regs' 20 = w64 (lc_F cx + 32) ->
  YK11.getr regs' 22 = w64 (transportb_hi 9) ->
  TC.m_tick_m Bt = Some (B3, tt) ->
  SRr segs W' (lc_cfg cx LO_TICK regs' mem' md')
    (op3b_at cx op 0xcf8 B3 (fun regs => YK11.getr regs 22 = w64 (transportb_hi 9))).
Proof.
intros cx op ly' S' W' regs' mem' md' e Bt B3 HP HB HL Htw HCUR R20 R22 Hm.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HL as (HC & _).
pose proof HC as (HJ & Hfrs & _).
pose proof (op3b_ev cx op ly' S' W' regs' mem' md' e HB HL) as Hev.
assert (XS : 0 <= MTICK_STK <= LLVMF_STK - 336) by (split; vm_compute; intros Hc; discriminate Hc).
unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (transportb_text + 3316)) mem'
    (YK11.seg_rom segs)) md') Q) end.
rewrite <- op3b_base.
pose proof (op3b_entry (fx := l_fx cx) W' regs' mem' 3316) as HS.
pose proof (op3b_img regs') as HEI.
assert (SHOK : sh_ok segs op3b_Bx (@nil shent) (op3b_E regs') (mrestrict (w_H W') mem')) by constructor.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
paj_run_tok RUN HS HJ SHOK op3b_B0.
{ op3b_awr. }
op3b_keep_tac HFr KR W' mem' ms.
clear HF HFr HG.
pmkst HS.
op3b_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 3320)) Q1 ltac:(apply codeptr_val; exact HEI).
assert (HPX : aregs_preserved regs' (ms_regs ms))
  by (apply (aregs_preserved_of_st_ok segs (w_H W') (op3b_E regs') _ ms regs' [] HS);
      [apply op3b_agree | vm_compute; reflexivity]).
destruct (op3b_callpre cx ly' S' W' regs' mem' md' e (ms_regs ms) 3320 MTICK_STK HB HC HPX Q1
  ltac:(op3b_lia) eq_refl XS) as (Hret & Hra & Rgp & Rtp & QSP & Hsp16 & Hlo & Hhi).
assert (TW1 : tw_at TMAP_B (aview segs (w_H W') (ms_mem ms)) Bt).
{ apply (tw_kept TMAP_B (aview segs (w_H W') mem')); [exact Htw|].
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
  apply KR. op3b_lia. }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at (l_fx cx) sg (transportb_sigma TB_m_tick) rg mm mdx) Q) end.
eapply SRr_bind.
{ exact (lp_mtick _ _ _ _ _ HP (l_fx cx) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_regs ms) Bt B3
    HJ Hret Hra Rgp Rtp Hsp16 Hlo Hhi TW1 Hm ltac:(unfold MTICK_EV, MSET_EV; lia)). }
cbv beta. intros W2 c2 _ HQ.
unfold transport_mtick_post, transport_cg_post in HQ.
destruct HQ as (ly2 & S2 & regs2 & mem2 & md2 & e2 & Hc2 & He2 & HJ2 & HP2 & Hfr2 & Hperm2 & HK2 & Hmo2 & HTW2).
assert (Ee2 : e2 = 0) by (unfold MTICK_EV, MSET_EV in He2; lia). subst e2. rewrite Z.add_0_r in HJ2.
rewrite Q1 in Hc2. subst c2. rewrite QSP in HK2.
pose proof (op3b_aregs_trans _ _ _ HPX HP2) as HPA.
destruct (op3b_kept cx ly' S' W' regs' mem' md' e (ms_mem ms) W2 mem2 MTICK_STK (mtick_wr Bt) LAWS HB HC KR
  (op3b_mtick_wr_G Bt) HK2) as (KA & KI & KF & GA).
pose proof (op3b_core_call cx ly' S' W' regs' mem' md' e MTICK_STK ly2 S2 W2 regs2 mem2 md2
  HB HC HJ2 Hfr2 Hperm2 HPA XS KA KI KF GA) as HC2.
pose proof (op3b_lcore_next cx op (lo_k op) ly' S' W' regs' mem' md' e ly2 S2 W2 regs2 mem2 md2 MTICK_STK HP HB HL HC2
  (HPA 18 ltac:(unfold acallee_saved; lia)) (HPA 19 ltac:(unfold acallee_saved; lia))
  (HPA 26 ltac:(unfold acallee_saved; lia)) (proj1 XS) KA KF Hmo2) as HL2.
apply SRr_ret.
exists ly2, S2, regs2, mem2, md2, e.
split; [unfold lc_cfg; rewrite op3b_base; reflexivity|].
split; [exact HL2|].
split; [exact HTW2|].
split; [exact (op3b_cur_kept cx regs' regs2 _ HPA HCUR)|].
split; [exact (eq_trans (HPA 20 ltac:(unfold acallee_saved; lia)) R20)|].
exact (eq_trans (HPA 22 ltac:(unfold acallee_saved; lia)) R22).
Qed.

(* +0xcf8 .. +0xd04: a1 = g_now (through s6), a0 = &g_s, `jal diginet_session_tick`; the return at +0xd08. *)
Lemma op3b_s2 : forall (cx : lcx) (op : lop) (B3 B4 : list byte) (r : Z) (W : world segs) (c : config),
  lc_rom_view_stmt B MT XL RLO RHI ->
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx ->
  TRI.run_inv B3 -> TW.g_fail_next B3 <= 1 ->
  TSS.diginet_session_tick_m timg_B None B3 (TW.g_now B3) = Some (B4, r) ->
  op3b_at cx op 0xcf8 B3 (fun regs => YK11.getr regs 22 = w64 (transportb_hi 9)) W c ->
  SRr segs W c (op3b_at cx op 0xd08 B4 (fun _ => True)).
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
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (transportb_text + 3320)) mem'
    (YK11.seg_rom segs)) md') Q) end.
rewrite <- op3b_base.
pose proof (op3b_entry2 (fx := l_fx cx) W regs' mem' B3 Htw R22) as HS.
pose proof (op3b_img2 regs' (TW.g_now B3)) as HEI.
assert (SHOK : sh_ok segs op3b_Bx (@nil shent) (op3b_E2 regs' (TW.g_now B3)) (mrestrict (w_H W) mem'))
  by constructor.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
paj_run_tok RUN HS HJ SHOK op3b_B0.
{ op3b_awr. }
op3b_keep_tac HFr KR W mem' ms.
clear HF HFr HG.
pmkst HS.
op3b_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 3336)) Q1 ltac:(apply codeptr_val; exact HEI).
op3b_reg HS (10%bv : bv 5) (w64 TICK_S) Q10
  ltac:(apply (op3b_sv_obj _ _ _ HEI);
        [unfold A_TEXT, A_LIM; lia | vm_compute; reflexivity | unfold TICK_S, TB_g_s; op3b_lia]).
op3b_reg HS (11%bv : bv 5) (w64 (TW.g_now B3)) Q11
  ltac:(exact (op3b_den32 regs' (TW.g_now B3) Hnow)).
assert (HPX : aregs_preserved regs' (ms_regs ms))
  by (apply (aregs_preserved_of_st_ok segs (w_H W) (op3b_E2 regs' (TW.g_now B3)) _ ms regs'
        [Z_to_bv 64 (TW.g_now B3)] HS);
      [apply op3b_agree2 | vm_compute; reflexivity]).
destruct (op3b_callpre cx ly' S' W regs' mem' md' e (ms_regs ms) 3336 TICK_STK HB HC HPX Q1
  ltac:(op3b_lia) eq_refl XS) as (Hret & Hra & Rgp & Rtp & QSP & Hsp16 & Hlo & Hhi).
assert (TW1 : tw_at TMAP_B (aview segs (w_H W) (ms_mem ms)) B3).
{ apply (tw_kept TMAP_B (aview segs (w_H W) mem')); [exact Htw|].
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
  apply KR. op3b_lia. }
assert (ROM1 : trans_rom_view_rd W (ms_mem ms)).
{ intros a Ha. rewrite KR by (pose proof (trans_ro_rd_bounds a Ha); op3b_lia). exact (HROM a Ha). }
assert (C5 : count_cid TICK_CID (frames S') < fs_frames TICK_CID) by (rewrite Hfrs; vm_compute; reflexivity).
assert (C0 : count_cid SENDDATA_CID (frames S') < fs_frames SENDDATA_CID)
  by (rewrite Hfrs; vm_compute; reflexivity).
assert (C2 : count_cid TRANS_BC_CID (frames S') < fs_frames TRANS_BC_CID)
  by (rewrite Hfrs; vm_compute; reflexivity).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at (l_fx cx) sg (transportb_sigma TB_diginet_session_tick) rg mm mdx) Q) end.
eapply SRr_bind.
{ exact (lp_tick _ _ _ _ _ HP (l_fx cx) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_regs ms) (TW.g_now B3) r None B3 B4
    HJ Hret Hra Rgp Rtp Q10 Q11 Hsp16 Hlo Hhi Hnow TW1 Hgf Htk I ROM1 (op3b_apart B3)
    I1 I2 Iq I4 Inc I5a I5b C5 C0 C2 ltac:(unfold TICK_EV; lia)). }
cbv beta. intros W2 c2 _ HQ.
unfold transport_tick_post, transport_cg_post in HQ.
destruct HQ as (ly2 & S2 & regs2 & mem2 & md2 & e2 & Hc2 & He2 & HJ2 & HP2 & Hfr2 & Hperm2 & HK2 & Hmo2 &
  (_ & HTW2 & _)).
assert (Ee2 : e2 = 0) by (unfold TICK_EV in He2; lia). subst e2. rewrite Z.add_0_r in HJ2.
rewrite Q1 in Hc2. subst c2. rewrite QSP in HK2.
pose proof (op3b_aregs_trans _ _ _ HPX HP2) as HPA.
destruct (op3b_kept cx ly' S' W regs' mem' md' e (ms_mem ms) W2 mem2 TICK_STK (tick_wr B3) LAWS HB HC KR
  (op3b_tick_wr_G B3) HK2) as (KA & KI & KF & GA).
pose proof (op3b_core_call cx ly' S' W regs' mem' md' e TICK_STK ly2 S2 W2 regs2 mem2 md2
  HB HC HJ2 Hfr2 Hperm2 HPA XS KA KI KF GA) as HC2.
pose proof (op3b_lcore_next cx op (lo_k op) ly' S' W regs' mem' md' e ly2 S2 W2 regs2 mem2 md2 TICK_STK HP HB HL HC2
  (HPA 18 ltac:(unfold acallee_saved; lia)) (HPA 19 ltac:(unfold acallee_saved; lia))
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

(* +0xd08 .. +0xd0c: a0 = 1, `jal settle` (lifted by gx_call_cg); the return at +0xd10. *)
Lemma op3b_s3 : forall (cx : lcx) (op : lop) (B4 : list byte) (W : world segs) (c : config),
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx ->
  TC.settle_m B4 1 = Some (B4, tt) ->
  (forall i, 0 <= i < TW.S_queued B4 -> TW.S_queue_len B4 i <= TS0.DIGINET_CMD_MAX_LEN) ->
  op3b_at cx op 0xd08 B4 (fun _ => True) W c ->
  SRr segs W c (op3b_at cx op 0xd10 B4 (fun _ => True)).
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
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (transportb_text + 3336)) mem'
    (YK11.seg_rom segs)) md') Q) end.
rewrite <- op3b_base.
pose proof (op3b_entry (fx := l_fx cx) W regs' mem' 3336) as HS.
pose proof (op3b_img regs') as HEI.
assert (SHOK : sh_ok segs op3b_Bx (@nil shent) (op3b_E regs') (mrestrict (w_H W) mem')) by constructor.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
paj_run_tok RUN HS HJ SHOK op3b_B0.
{ op3b_awr. }
op3b_keep_tac HFr KR W mem' ms.
clear HF HFr HG.
pmkst HS.
op3b_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 3344)) Q1 ltac:(apply codeptr_val; exact HEI).
op3b_reg HS (10%bv : bv 5) (w64 1) Q10 ltac:(reflexivity).
assert (HPX : aregs_preserved regs' (ms_regs ms))
  by (apply (aregs_preserved_of_st_ok segs (w_H W) (op3b_E regs') _ ms regs' [] HS);
      [apply op3b_agree | vm_compute; reflexivity]).
destruct (op3b_callpre cx ly' S' W regs' mem' md' e (ms_regs ms) 3344 SETTLE_STK HB HC HPX Q1
  ltac:(op3b_lia) eq_refl XS) as (Hret & Hra & Rgp & Rtp & QSP & Hsp16 & Hlo & Hhi).
assert (TW1 : tw_at TMAP_B (aview segs (w_H W) (ms_mem ms)) B4).
{ apply (tw_kept TMAP_B (aview segs (w_H W) mem')); [exact Htw|].
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
  apply KR. op3b_lia. }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at (l_fx cx) sg (transportb_sigma TB_settle) rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_call_cg (l_fx cx) rc tfib_sink_head segs B MT TG.G_HARNESS_B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
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
  (fun a (Hf : False) => False_ind _ Hf) HK2) as (KA & KI & KF & GA).
pose proof (op3b_core_call cx ly' S' W regs' mem' md' e SETTLE_STK ly2 S2 W2 regs2 mem2 md2
  HB HC HJ2 Hfr2 Hperm2 HPA XS KA KI KF GA) as HC2.
pose proof (op3b_lcore_next cx op (lo_k op) ly' S' W regs' mem' md' e ly2 S2 W2 regs2 mem2 md2 SETTLE_STK HP HB HL
  HC2 (HPA 18 ltac:(unfold acallee_saved; lia)) (HPA 19 ltac:(unfold acallee_saved; lia))
  (HPA 26 ltac:(unfold acallee_saved; lia)) (proj1 XS) KA KF Hmo2) as HL2.
apply SRr_ret.
exists ly2, S2, regs2, mem2, md2, e.
split; [unfold lc_cfg; rewrite op3b_base; reflexivity|].
split; [exact HL2|].
split.
{ apply (tw_kept TMAP_B (aview segs (w_H W) (ms_mem ms))); [exact TW1|].
  intros x Hx. exact (HGK x (op3b_tw_in_G x Hx)). }
split; [exact (op3b_cur_kept cx regs' regs2 _ HPA HCUR)|].
split; [exact (eq_trans (HPA 20 ltac:(unfold acallee_saved; lia)) R20)|].
exact I.
Qed.

(* +0xd10 `j +0xe88`, +0xe88 `li s6, 1`, +0xe8c `j +0x1670`: the tail cut +0x1670. *)
Lemma op3b_s4 : forall (cx : lcx) (op : lop) (B4 : list byte) (W : world segs) (c : config),
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx ->
  TOP.LLVMFuzzerTestOneInput_op_m timg_B (lo_B op) (fun _ => 1) (l_pl cx) (lo_c op) (lo_k op) =
    Some (B4, (lc_tick_c (l_pl cx) (lc_oc (l_pl cx) (lo_c op)), lo_k op)) ->
  op3b_at cx op 0xd10 B4 (fun _ => True) W c ->
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
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (transportb_text + 3344)) mem'
    (YK11.seg_rom segs)) md') Q) end.
rewrite <- op3b_base.
pose proof (op3b_entry (fx := l_fx cx) W regs' mem' 3344) as HS.
pose proof (op3b_img regs') as HEI.
assert (SHOK : sh_ok segs op3b_Bx (@nil shent) (op3b_E regs') (mrestrict (w_H W) mem')) by constructor.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
paj_run_to_tok RUNTO HS HJ SHOK op3b_B0 5744.
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
op3b_reg HS (19%bv : bv 5) (YK11.getr regs' (Z_to_bv 5 19)) Q19
  ltac:(cbn [sv_denot]; rewrite (op3b_ew regs' 19 (Z_to_bv 5 19) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
op3b_reg HS (20%bv : bv 5) (YK11.getr regs' (Z_to_bv 5 20)) Q20
  ltac:(cbn [sv_denot]; rewrite (op3b_ew regs' 20 (Z_to_bv 5 20) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
op3b_reg HS (24%bv : bv 5) (YK11.getr regs' (Z_to_bv 5 24)) Q24
  ltac:(cbn [sv_denot]; rewrite (op3b_ew regs' 24 (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
op3b_reg HS (26%bv : bv 5) (YK11.getr regs' (Z_to_bv 5 26)) Q26
  ltac:(cbn [sv_denot]; rewrite (op3b_ew regs' 26 (Z_to_bv 5 26) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
op3b_reg HS (27%bv : bv 5) (YK11.getr regs' (Z_to_bv 5 27)) Q27
  ltac:(cbn [sv_denot]; rewrite (op3b_ew regs' 27 (Z_to_bv 5 27) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
op3b_reg HS (22%bv : bv 5) (w64 1) Q22 ltac:(reflexivity).
destruct (op3b_kept0 cx ly' S' W regs' mem' md' e (ms_mem ms) LAWS HB HC KR) as (KA & KI & KF & GA).
pose proof (op3b_core_call cx ly' S' W regs' mem' md' e 0 ly' S' W regs' (ms_mem ms) _
  HB HC HJ eq_refl (Permutation_refl _) (fun r _ => eq_refl) ltac:(unfold LLVMF_STK; lia) KA KI KF GA) as HC5.
pose proof (op3b_core_regs cx ly' S' W regs' (ms_mem ms) _ e (ms_regs ms) HC5 Q2 Q3 Q4 Q8 Q9) as HC6.
pose proof (op3b_lcore_next cx op (lo_k op) ly' S' W regs' mem' md' e ly' S' W (ms_regs ms) (ms_mem ms) _ 0 HP HB HL
  HC6 Q18 Q19 Q26 ltac:(lia) KA KF (mle_start MT S' MTL)) as HL5.
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
{ apply (tw_kept TMAP_B (aview segs (w_H W) mem')); [exact Htw|].
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
  apply KR. op3b_lia. }
split; [destruct HCUR as (H24 & H27); split; [exact (eq_trans Q24 H24) | exact (eq_trans Q27 H27)]|].
split; [exact (eq_trans Q20 R20) | exact Q22].
Qed.

(* ------------------------------------------------------------------ *)
(* 6. The segment                                                      *)
(* ------------------------------------------------------------------ *)

Lemma lc_op3b_ok (K1 : lc_rom_view_stmt B MT XL RLO RHI) (K6 : lc_runinv_stmt) :
  lc_op3b_stmt B MT XL RLO RHI.
Proof.
unfold lc_op3b_stmt. intros HP cx op W' c' HB HT.
destruct HT as (ly' & S' & regs' & mem' & md' & e & B1 & HT). cbv zeta in HT.
destruct HT as (Hc & Ho & HL & Hob & Htw & R22 & HCUR & R20).
pose proof HL as (_ & _ & _ & _ & (HA & Hops & Hcin & _ & _) & _).
destruct (op3b_model (l_pl cx) (lo_ops op) (lo_B op) B1 (lo_c op) (lo_k op) HA Hops Hcin Ho Hob)
  as (B3 & B4 & r & E3 & E4 & E5 & Eop & HA4).
pose proof (SL.agree_op_begin timg_B (lo_ops op) (lo_B op) B1 HA Hob) as HA1.
destruct (op3b_inv3 (l_pl cx) (lo_ops op) B1 B3 (lc_oc (l_pl cx) (lo_c op)) K6 HA1 E3) as (HRI & Hgf3).
destruct (K6 (lo_ops op + 1) B4 HA4) as (_ & Hq4 & _).
subst c'.
eapply SRr_bind; [exact (op3b_s1 cx op ly' S' W' regs' mem' md' e _ B3 HP HB HL Htw HCUR R20 R22 E3)|].
intros W2 c2 _ H2.
eapply SRr_bind; [exact (op3b_s2 cx op B3 B4 r W2 c2 K1 HP HB HRI Hgf3 E4 H2)|].
intros W3 c3 _ H3.
eapply SRr_bind; [exact (op3b_s3 cx op B4 W3 c3 HP HB E5 Hq4 H3)|].
intros W4 c4 _ H4.
exact (op3b_s4 cx op B4 W4 c4 HP HB Eop H4).
Qed.

End op3b.

Print Assumptions lc_op3b_ok.
