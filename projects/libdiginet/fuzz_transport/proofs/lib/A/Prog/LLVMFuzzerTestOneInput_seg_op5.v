(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 2564 of its 2742 lines of code are new or changed and 961 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/send_data_seg_head.v, with its module paths and module names changed; 1345 of its 1476 lines of code are new or changed and 2611 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op5: Lemma lc_op5_ok (K1 : lc_rom_view_stmt ..) (K6 : lc_runinv_stmt) : lc_op5_stmt
   (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v), the OP5 segment of the image-A walk of fuzz_transport.asan's
   LLVMFuzzerTestOneInput, offsets +0x618 .. +0x680 of the listing lib/A/Prog/DgnTransportList.v (0x8187c .. 0x818e4),
   from the arm cut ARM5 (lc_st_arm cx op 5) to the cut SET56 (lc_st_set56 cx op) at +0x1018. The two kit statements
   are arguments, as segs.v's KIT RULE asks: K1 gives trans_rom_view_rd at the cut, which diginet_session_wake asks;
   K6 gives the two run invariants and g_fail_next <= 1 at the operation's start world.

   The code (offsets from the entry 0x81264; the listing slot of +k is k / 4):
     +0x618 .. +0x62c  s6 = &OW (the auipc pair, image object 12), a0 = s6, a1 = 0, a2 = 304, `jal __asan_memset`
                       (return +0x630): op_begin's memset of OW.
     +0x630 .. +0x640  a0 = &GOT (image object 13), a1 = 0, a2 = 224, `jal __asan_memset` (return +0x644):
                       op_begin's memset of GOT.
     +0x644 .. +0x658  `lbu a0, -1076(s4)` (s4 = transport_hi 10, so the address is g_fail_next), a1 = -1,
                       `sw a1, 232(s6)` (OW.desk_off = -1), `ld a1, 184(s1)` (the spill slot holding &M),
                       `sw a0, 88(a1)` (M.fail = g_fail_next), `jal m_wake` (return +0x65c).
     +0x65c .. +0x670  `ld a1, 176(s1)` (the spill slot holding transport_hi 9), `ld a1, -1052(a1)` (g_now),
                       s6 = a0 (m_wake's result want), a0 = &g_s (image object 9),
                       `jal diginet_session_wake` (return +0x674).
     +0x674 .. +0x67c  a1 = s6 (want), s6 = 7, `jal check_state_wake_code` (return +0x680).
     +0x680            `j +0x1018`, the SET56 cut.
   No instrumented check and no __asan_report_* call lies on this stretch: every access is at a constant offset of
   a harness global or of the realigned frame.

   The model (section 1). LLVMFuzzerTestOneInput_st.v lc_op5_eq: op_begin, m_wake, diginet_session_wake at g_now,
   check_state_wake_code and settle. TSim/WakeOps.v op5_step gives the whole operation's Some from the simulation
   invariant at the loop head; o5_model reads the pieces back (check_state_wake_code forces rc = want and keeps the
   world, settle keeps it: lc_settle_world) and states the operation's equation at every stream. op_begin's world is
   written in the order the code writes it (o5_w1 .. o5_w4); g_fail_next is the same where the `lbu` reads it and
   where the model's set_M_fail reads it (o5_gf_w3). The run invariants and g_fail_next <= 1 at m_wake's world come
   from K6 through TRunInv.v m_wake_rk / rk_out and TIoRecv.v m_wake_gk (o5_inv_at_B2); m_wake's answer is one of
   four small constants (o5_want_rng), so both arguments of check_state_wake_code fit an int.

   The walk (section 3). The two intrinsics are TransportGCg.v gx_intrin_at (OW and GOT are bytes of G whose shadow
   is 0 by lp_recv_cells: o5_sh_ow / o5_sh_got); m_wake and diginet_session_wake are G-form callees composed in the
   walk's own G journal (lp_mwake, lp_wake; TF = None, so trans_tframe_at, trans_tf_off_g and wake_apart hold of
   None); check_state_wake_code is a leaf, read at this unit's model through DgnTransportCg.v transport_leaf_at and
   lifted into the G journal by TransportGCg.v gx_call_leaf over DgnTransportLeafb.v decode_leafb_journal. Every
   straight stretch is a run of the token engine over the G journal (TransportGRunA.v paj_run_x / paj_run_to_x)
   from a state rebuilt at its first pc with every register an atom: run C reads g_fail_next (o5_rg_gf) and the
   184(s1) spill (o5_rg_sp), writes OW.desk_off (o5_rg_ow) and M.fail (o5_rg_mf, based at the spill's value), and
   its two stores are read back from the regions the run leaves (o5_rg_ow2, o5_rg_mf2); run D reads the 176(s1)
   spill (o5_rg_hi) and g_now (o5_rg_nw); runs A, B, E and F read and write no memory. The world after run C is
   op_begin's, through one tw_write per store (a view that is the run's memory but at M.fail, rmid, between them).

   What the walk keeps. Every step is folded into one acall_kept_g from the cut's memory over the window
   [sp1 - O5_X, sp1), O5_X the widest callee window of LLVMFuzzerTestOneInput's closure (it covers both intrinsics'
   and the leaf's ESTACK, MWAKE_STK and WAKE_STK), with the written range o5_wr inside G (o5_step for the walk's
   own steps; dk_kept_trans_g for m_wake; dk_kept_trans_nf_g for diginet_session_wake, whose call state is m_wake's
   return state). At the cut that fact gives LLVMFuzzerTestOneInput_st.v lc_core_kept's three clauses (no byte of
   o5_wr is a block byte, a frame byte or a frame-shadow byte), lc_spills_kept and lc_fsh_kept; the callee-saved
   registers but s6 are the cut's (o5_keep), and s6 is 7 again after +0x678.

   The walk's journal is whatever the cut states give (lc_core): nothing here reads its footprint list. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0 AE2k ACfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AsanCells TransportG TransportShape AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  DgnTransportLeafb DgnTransportCgRun LeafCgKit AsanKA check_state_wake_c check_state_wake_code_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_wake_cg diginet_session_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import settle_cg receive_cg m_lost_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require m_wake_cgW.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg notice_cg send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCgX.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  check_state_wake_code_cg check_refusal_submit_cg check_latest_submit_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  diginet_session_config_default_cg diginet_session_init_cg m_tick_cg diginet_session_tick_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  diginet_session_close_cg diginet_session_submit_cg build_and_receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require ExecF Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require
  TWorld TWorldLemmas TImg TCb TSess0 TSess TOps TIoRecv TRunInv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require
  Agree QueueFacts InitOk LoopOk LinksProof WakeOps WakeBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI16.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module TIR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TRunInv.
Module TIRC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TIoRecv.
Module AG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.Agree.
Module QF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.
Module LOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LoopOk.
Module LP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LinksProof.
Module WO := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.WakeOps.
Module WB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.WakeBase.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module O5LB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.DgnTransportLeafb.
Module O5CR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.DgnTransportCgRun.
Module O5CK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LeafCgKit.
Module O5KA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.AsanKA.
Module O5CW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_wake_c.
Module O5WC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_wake_code_c.
Module O5EF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.ExecF.
Module O5MEM := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module LCSWC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_wake_code_cg.
Module MWW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_wake_cgW.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The model of the operation                                       *)
(* ------------------------------------------------------------------ *)

(* op_begin's four stages, in the order the code writes them: the two fills, OW.desk_off, M.fail. *)
Definition o5_w1 (B : list byte) : list byte :=
  TW.upd B TW.OFF_OW (repeat (DSpec.b8 0) (Z.to_nat TW.SZ_OW)).
Definition o5_w2 (B : list byte) : list byte :=
  TW.upd (o5_w1 B) TW.OFF_GOT (repeat (DSpec.b8 0) (Z.to_nat TW.SZ_GOT)).
Definition o5_w3 (B : list byte) : list byte := TW.set_OW_desk_off (o5_w2 B) (-1).
Definition o5_w4 (B : list byte) : list byte := TW.set_M_fail (o5_w3 B) (TW.g_fail_next (o5_w3 B)).

Lemma o5_begin_eq : forall B, TC.op_begin_m B = Some (o5_w4 B, tt).
Proof. intros B. reflexivity. Qed.

(* A write inside the world that misses the one byte of g_fail_next keeps it. *)
Lemma o5_gf_out : forall (Bx v : list byte) k, 0 <= k ->
  k + Z.of_nat (length v) <= Z.of_nat (length Bx) ->
  (k + Z.of_nat (length v) <= TW.OFF_g_fail_next \/ TW.OFF_g_fail_next + 1 <= k) ->
  TW.g_fail_next (TW.upd Bx k v) = TW.g_fail_next Bx.
Proof.
intros Bx v k Hk Hl Hd. unfold TW.g_fail_next.
apply TWL.u_at_upd_out; [exact Hk | unfold TW.OFF_g_fail_next; lia | change (Z.of_nat 1) with 1; lia | exact Hl].
Qed.

(* The lengths of the first two stages. *)
Lemma o5_len12 : forall B, Z.of_nat (length B) = TW.W_LEN ->
  Z.of_nat (length (o5_w1 B)) = TW.W_LEN /\ Z.of_nat (length (o5_w2 B)) = TW.W_LEN.
Proof.
intros B HL.
assert (L1 : Z.of_nat (length (o5_w1 B)) = TW.W_LEN).
{ unfold o5_w1. rewrite TWL.length_upd; [exact HL | unfold TW.OFF_OW; lia|].
  rewrite repeat_length. unfold TW.OFF_OW, TW.SZ_OW, TW.W_LEN in *. lia. }
split; [exact L1|].
unfold o5_w2. rewrite TWL.length_upd; [exact L1 | unfold TW.OFF_GOT; lia|].
rewrite repeat_length. unfold TW.OFF_GOT, TW.SZ_GOT, TW.W_LEN in *. lia.
Qed.

(* The value the code loads: g_fail_next is the same at the state the `lbu` reads (after the two fills) and at the
   state the model's set_M_fail reads (after the store of OW.desk_off). *)
Lemma o5_gf_w3 : forall B, Z.of_nat (length B) = TW.W_LEN ->
  TW.g_fail_next (o5_w3 B) = TW.g_fail_next (o5_w2 B).
Proof.
intros B HL. destruct (o5_len12 B HL) as (_ & L2).
unfold o5_w3, TW.set_OW_desk_off, TW.A_OW_desk_off.
apply o5_gf_out; rewrite ?TWL.length_put;
  unfold TW.OFF_OW, TW.OFF_g_fail_next, TW.W_LEN in *; cbn [Z.of_nat]; lia.
Qed.

(* Two Some answers of one option are equal, component by component (no inversion of a world). *)
Lemma o5_some2 : forall {T U : Type} (o : option (T * U)) (x x' : T) (y y' : U),
  o = Some (x, y) -> o = Some (x', y') -> x = x' /\ y = y'.
Proof.
intros T U o x x' y y' E1 E2. rewrite E1 in E2.
split; [exact (f_equal (fun z => match z with Some (a, _) => a | None => x end) E2)
       | exact (f_equal (fun z => match z with Some (_, b) => b | None => y end) E2)].
Qed.

(* check_state_wake_code answers Some exactly when its two arguments agree, and keeps the world. *)
Lemma o5_cswc : forall B rc want B' u, TC.check_state_wake_code_m B rc want = Some (B', u) ->
  rc = want /\ B' = B.
Proof.
intros B rc want B' u H. unfold TC.check_state_wake_code_m in H.
destruct (Z.eqb_spec rc want) as [E|E]; cbn [negb] in H; [|discriminate H].
split; [exact E|].
exact (eq_sym (f_equal (fun z => match z with Some (b, _) => b | None => B end) H)).
Qed.

(* The whole operation, from the simulation invariant at the loop head: the four model steps the code makes, the
   settle that keeps its world, and the operation's equation at EVERY stream (op 5 reads none). *)
Lemma o5_model : forall (ops : Z) (B0 D : list byte) (c : TOP.fuzz_in) (k : nat),
  AG.agree timg_A ops B0 -> 0 <= ops < TC.OPS_MAX -> lc_opc D c = 5 ->
  exists B1 B2 B3 want r,
    TC.op_begin_m B0 = Some (B1, tt) /\
    AG.agree timg_A ops B1 /\
    TC.m_wake_m B1 = Some (B2, want) /\
    TSS.diginet_session_wake_m timg_A None B2 (TW.g_now B2) = Some (B3, r) /\
    r = want /\
    TC.settle_m B3 0 = Some (B3, tt) /\
    AG.agree timg_A (ops + 1) B3 /\
    (forall A : nat -> Z,
       TOP.LLVMFuzzerTestOneInput_op_m timg_A B0 A D c k = Some (B3, (lc_oc D c, k))).
Proof.
intros ops B0 D c k HA Hops Ho.
unfold lc_opc in Ho.
destruct (WO.op5_step LP.links_holds timg_A ops B0 (fun _ => 0) D c k HA Hops Ho) as (Bz & Ez & HAz).
pose proof (lc_op5_eq timg_A B0 (fun _ => 0) D c k Ho) as Eq.
rewrite Eq in Ez. clear Eq.
destruct (TC.op_begin_m B0) as [[B1 []]|] eqn:E1; [|discriminate Ez].
destruct (TC.m_wake_m B1) as [[B2 want]|] eqn:E2; [|discriminate Ez].
destruct (TSS.diginet_session_wake_m timg_A None B2 (TW.g_now B2)) as [[B3 r]|] eqn:E3; [|discriminate Ez].
destruct (TC.check_state_wake_code_m B3 r want) as [[B4 []]|] eqn:E4; [|discriminate Ez].
destruct (TC.settle_m B4 0) as [[B5 []]|] eqn:E5; [|discriminate Ez].
destruct (o5_some2 _ _ _ _ _ Ez (@eq_refl _ (Some (B5, (lc_oc D c, k))))) as (EB & _).
destruct (o5_cswc B3 r want B4 tt E4) as (Erw & EB4). subst B4.
pose proof (lc_settle_world B3 B5 0 tt E5) as EB5. subst B5.
subst Bz.
destruct (WB.op_begin_facts timg_A ops B0 HA) as (W0 & EW0 & HA1 & _).
rewrite E1 in EW0.
assert (EB1 : W0 = B1)
  by exact (eq_sym (f_equal (fun z => match z with Some (b, _) => b | None => W0 end) EW0)).
subst W0.
exists B1, B2, B3, want, r.
(* `destruct ... eqn:E1` replaced op_begin_m B0 in the goal too. *)
split; [reflexivity|]. split; [exact HA1|]. split; [exact E2|]. split; [exact E3|].
split; [exact Erw|]. split; [exact E5|]. split; [exact HAz|].
intros A. rewrite (lc_op5_eq timg_A B0 A D c k Ho), E1, E2, E3, E4, E5. reflexivity.
Qed.

(* The run invariants and g_fail_next at the world diginet_session_wake is called at. *)
Lemma o5_inv_at_B2 : lc_runinv_stmt -> forall ops B1 B2 want,
  AG.agree timg_A ops B1 -> TC.m_wake_m B1 = Some (B2, want) ->
  (TW.M_fly_on B2 <> 0 -> TW.M_fly_len B2 <= TC.SPEC_MAX_FRAME) /\
  (forall s, 0 <= s < TW.g_ncmd B2 -> TW.Cmd_st B2 s = TC.PENDING -> TW.Cmd_len B2 s <= DSpec.SPEC_CMD_MAX) /\
  TW.g_fail_next B2 <= 1.
Proof.
intros K6 ops B1 B2 want HA Hm.
pose proof (AG.ac_len _ _ _ (AG.ag_core _ _ _ HA)) as HL.
destruct (K6 ops B1 HA) as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8).
assert (RI : TIR.run_inv B1) by (split; [exact I1|]; split; [exact I2|]; split; [exact I4|];
  split; [exact I6|]; split; [exact I7|]; split; [exact I5 | exact I3]).
destruct (TIR.rk_out B1 B2 HL RI (TIR.m_wake_rk B1 HL B1 B2 want (TIR.rk_refl B1) Hm))
  as (_ & R1 & _ & R4 & _ & _ & _ & _).
destruct (TIRC.m_wake_gk B1 HL B1 B2 want (TIRC.gkeep_refl B1) Hm) as (_ & GF).
split; [exact R1|]. split; [exact R4 | rewrite GF; exact I8].
Qed.

(* m_wake answers one of four small constants (TCb.v :218-233), so it fits an int. *)
Ltac o5_rc_small := cbn [fst snd]; split; [vm_compute; intros HX; discriminate HX | vm_compute; reflexivity].
Lemma o5_want_rng : forall Bw Bw' v, TC.m_wake_m Bw = Some (Bw', v) -> - 2 ^ 31 <= v < 2 ^ 31.
Proof.
intros Bw Bw' v H.
assert (Ev : v = match TC.m_wake_m Bw with Some (_, x) => x | None => 0 end) by (rewrite H; reflexivity).
assert (HS : TC.m_wake_m Bw <> None) by (rewrite H; discriminate).
rewrite Ev. clear Ev H. revert HS. unfold TC.m_wake_m. cbv zeta.
destruct (negb (TC.truth (TW.M_desk_known Bw))); [intros _; o5_rc_small|].
destruct (TC.truth (TW.M_foreign Bw)); [intros _; o5_rc_small|].
destruct (TC.int_inc (TW.OW_e2 _)) as [e2|]; [|cbn [fst snd]; intros HX; exfalso; exact (HX eq_refl)].
cbv beta iota.
destruct (TC.truth (TW.M_fail _)); [intros _; o5_rc_small|].
destruct (TC.m_set_m _ _ _) as [[B5 u5]|];
  [intros _; o5_rc_small | cbn [fst snd]; intros HX; exfalso; exact (HX eq_refl)].
Qed.

(* Every payload byte of the harness globals lies in a loaded segment of image A, so no world hides it; the leaf
   therefore reads the world relation at the raw memory (check_state_wake_c.v csw_view). *)
Lemma o5_hull_vis : forall (W : world tfibsegs) x,
  TG.G_HARNESS_LO <= x < TG.G_HARNESS_HI -> w_H W (Z_to_bv 64 x) = false.
Proof.
intros W x Hx. apply (O5CR.decode_vis_seg W).
apply (O5CR.decode_covers_img TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) x);
  [vm_compute; reflexivity | lia].
Qed.

Lemma o5_tw_csw : forall (W : world tfibsegs) mem Bw,
  tw_at TMAP_A (aview tfibsegs (w_H W) mem) Bw -> tw_at TMAP_A (O5CW.csw_view mem) Bw.
Proof.
intros W mem Bw H. apply (tw_kept TMAP_A _ _ Bw H). intros x Hx.
unfold O5CW.csw_view.
rewrite (O5CR.decode_aview_mrd W mem x (o5_hull_vis W x (TMAP_A_hull x Hx))). reflexivity.
Qed.

(* A shadow byte of the slot's frame is above G's hull. *)
Lemma o5_sh_hi : forall F a, 0 <= F -> SHADOW_OFF + F / 8 <= a -> a < TG.G_HARNESS_HI -> False.
Proof.
intros F a H0 H1 H2. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as D0.
remember (F / 8) as q eqn:Eq. clear Eq.
unfold SHADOW_OFF, TG.G_HARNESS_HI in *. lia.
Qed.


Lemma o5_rng_idx : forall b i n : Z, 0 <= i < n -> b <= b + i < b + n.
Proof. intros b i n H. lia. Qed.

(* ------------------------------------------------------------------ *)
(* 2. The bytes the segment writes, and the shadow of the two fills    *)
(* ------------------------------------------------------------------ *)

Section gw. Context {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Variable B : asyms.

(* The nine payload ranges of G the segment's own stores and its two callees may change. *)
Lemma o5_inG : forall a,
  (TA_M <= a < TA_M + TW.SZ_M) \/ (TA_OW <= a < TA_OW + TW.SZ_OW) \/ (TA_GOT <= a < TA_GOT + TW.SZ_GOT) \/
  (TA_g_s <= a < TA_g_s + TW.SZ_g_s) \/ (TA_g_cmd <= a < TA_g_cmd + TW.SZ_g_cmd) \/
  (TA_g_q <= a < TA_g_q + TW.SZ_g_q) \/ (TA_g_nq <= a < TA_g_nq + TW.SZ_g_nq) \/
  (TA_g_fail_next <= a < TA_g_fail_next + 1) \/
  (TA_g_last_counter <= a < TA_g_last_counter + TW.SZ_g_last_counter) ->
  W_journalG.inG TG.G_HARNESS a.
Proof.
intros a Ha. unfold W_journalG.inG. apply Exists_exists.
assert (RW : forall o b n, In (o, b, n) TMAP_A -> b <= a < b + n ->
  exists r, In r TG.G_HARNESS /\ in_zr a r).
{ intros o b n Hin Hr. exists (b, n).
  split; [exact (TMAP_A_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia]. }
destruct Ha as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]].
- exact (RW _ _ _ TMAP_A_M H).
- exact (RW _ _ _ TMAP_A_OW H).
- exact (RW _ _ _ TMAP_A_GOT H).
- exact (RW _ _ _ TMAP_A_g_s H).
- exact (RW _ _ _ TMAP_A_g_cmd H).
- exact (RW _ _ _ TMAP_A_g_q H).
- exact (RW _ _ _ TMAP_A_g_nq H).
- exact (RW _ _ _ TMAP_A_g_fail_next H).
- exact (RW _ _ _ TMAP_A_g_last_counter H).
Qed.

(* The bytes the segment may change: op_begin's two fills, OW.desk_off, M.fail, and the two callees' ranges. *)
Definition o5_wr (B1 B2 : list byte) (a : Z) : Prop :=
  (TA_OW <= a < TA_OW + TW.SZ_OW) \/ (TA_GOT <= a < TA_GOT + TW.SZ_GOT) \/
  (TA_M + 88 <= a < TA_M + 92) \/ mwake_wr B1 a \/ wake_wr B2 a.

Ltac o5_offs :=
  unfold twa_fld, mset_wr, iosend_wr, notice_wr, wake_ntc, SENDCTL_F,
    TW.A_M_e2_acked, TW.A_M_wake_sent, TW.A_M_fail, TW.A_M_state, TW.A_M_fly_on, TW.A_M_fly_cmd,
    TW.A_M_fly_counter, TW.A_M_fly_retries, TW.A_M_fly_sent, TW.A_M_fly_len, TW.A_M_fly_frame,
    TW.A_M_host_counter, TW.A_M_next_ka, TW.A_M_last_display, TW.A_M_display_sent,
    TW.A_OW_e2, TW.A_OW_n, TW.A_OW_t_state, TW.OW_t_ESZ,
    TW.A_GOT_e2, TW.A_GOT_e3, TW.A_GOT_acks, TW.A_GOT_acked, TW.A_GOT_desk, TW.A_GOT_ndata,
    TW.A_GOT_foreign, TW.A_GOT_n, TW.A_GOT_t_state, TW.GOT_t_ESZ,
    TW.A_S_stats_refused, TW.A_S_e1_named_us, TW.A_S_wake_acked, TW.A_S_wake_sent_us,
    TW.A_S_inflight_frame, TW.A_S_inflight_len, TW.A_S_stats_tx_wakes, TW.A_S_inflight,
    TW.A_S_inflight_counter, TW.A_S_inflight_retries, TW.A_S_inflight_sent_us, TW.A_S_stats_tx_frames,
    TW.A_S_state, TW.A_Cmd_st, TW.OFF_M, TW.OFF_OW, TW.OFF_GOT, TW.OFF_g_s, TW.OFF_g_cmd, TW.OFF_g_q,
    TW.OFF_g_nq, TW.SZ_g_nq, TW.OFF_g_fail_next, TW.OFF_g_last_counter,
    TW.SZ_M, TW.SZ_OW, TW.SZ_GOT, TW.SZ_g_s, TW.SZ_g_cmd, TW.SZ_g_q, TW.SZ_g_last_counter,
    TA_M, TA_OW, TA_GOT, TA_g_s, TA_g_cmd, TA_g_q, TA_g_nq, TA_g_fail_next, TA_g_last_counter,
    TC.TRANS_MAX, TC.CMDS_MAX, TC.SPEC_MAX_FRAME, TW.Cmd_ESZ, TW.A_Cmd_bytes in *.

Lemma o5_wr_inG : forall B1 B2 a, o5_wr B1 B2 a -> W_journalG.inG TG.G_HARNESS a.
Proof.
intros B1 B2 a H. apply o5_inG.
unfold o5_wr, mwake_wr, wake_wr in H. o5_offs.
repeat match goal with
| Hx : _ \/ _ |- _ => destruct Hx as [Hx|Hx]
| Hx : _ /\ _ |- _ => destruct Hx
| Hx : exists _, _ |- _ => destruct Hx
end.
all: o5_offs.
all: first [ left; lia | right; left; lia | do 2 right; left; lia | do 3 right; left; lia
           | do 4 right; left; lia | do 5 right; left; lia | do 6 right; left; lia
           | do 7 right; left; lia | do 8 right; lia ].
Qed.

(* The shadow cells the two fills read: the 48 granules of OW's 64-byte hull (g_rx_len's payload granule and its
   three guard granules, OW's 38 payload granules, OW's six guard granules) and the 32 of GOT's (the last four guard
   granules of g_s, GOT's 28 payload granules). Every one is a row of trans_recv_cells (receive_cg.v). *)
Definition o5_cs : list (Z * Z) :=
  trans_zgran TA_g_rx_len (TA_g_rx_len + TW.SZ_g_rx_len) ++
  [(TA_g_rx_len + 8, 0xf9); (TA_g_rx_len + 16, 0xf9); (TA_g_rx_len + 24, 0xf9)] ++
  trans_zgran TA_OW (TA_OW + TW.SZ_OW) ++
  [(TA_OW + TW.SZ_OW, 0xf9); (TA_OW + TW.SZ_OW + 8, 0xf9); (TA_OW + TW.SZ_OW + 16, 0xf9);
   (TA_OW + TW.SZ_OW + 24, 0xf9); (TA_OW + TW.SZ_OW + 32, 0xf9); (TA_OW + TW.SZ_OW + 40, 0xf9)] ++
  [(TA_GOT - 32, 0xf9); (TA_GOT - 24, 0xf9); (TA_GOT - 16, 0xf9); (TA_GOT - 8, 0xf9)] ++
  trans_zgran TA_GOT (TA_GOT + TW.SZ_GOT).

Lemma o5_cover_ow : trans_cs_cover o5_cs TA_OW TW.SZ_OW = true.
Proof. vm_compute. reflexivity. Qed.
Lemma o5_cover_got : trans_cs_cover o5_cs TA_GOT TW.SZ_GOT = true.
Proof. vm_compute. reflexivity. Qed.

Lemma o5_sh_cells : trans_recv_cells B -> trans_sh_cells B o5_cs.
Proof.
intros (Z1 & Z2 & Z3 & HC). unfold o5_cs.
apply trans_sh_cells_app; [apply trans_sh_cells_zshadow; [exact Z3 | reflexivity]|].
apply trans_sh_cells_app.
{ repeat apply trans_sh_cells_cons; try apply trans_sh_cells_nil.
  all: apply trans_sh_cell_const; [intro ly; pose proof (HC ly) as H; tauto | lia]. }
apply trans_sh_cells_app; [apply trans_sh_cells_zshadow; [exact Z1 | reflexivity]|].
apply trans_sh_cells_app.
{ repeat apply trans_sh_cells_cons; try apply trans_sh_cells_nil.
  all: apply trans_sh_cell_const; [intro ly; pose proof (HC ly) as H; tauto | lia]. }
apply trans_sh_cells_app.
{ repeat apply trans_sh_cells_cons; try apply trans_sh_cells_nil.
  all: apply trans_sh_cell_const; [intro ly; pose proof (HC ly) as H; tauto | lia]. }
apply trans_sh_cells_zshadow; [exact Z2 | reflexivity].
Qed.

Lemma o5_sh_ow : trans_recv_cells B -> trans_sh_any B TA_OW TW.SZ_OW.
Proof. intros H. exact (trans_sh_any_cells B o5_cs TA_OW TW.SZ_OW (o5_sh_cells H) o5_cover_ow). Qed.
Lemma o5_sh_got : trans_recv_cells B -> trans_sh_any B TA_GOT TW.SZ_GOT.
Proof. intros H. exact (trans_sh_any_cells B o5_cs TA_GOT TW.SZ_GOT (o5_sh_cells H) o5_cover_got). Qed.
End gw.

(* ------------------------------------------------------------------ *)
(* 3. The walk                                                         *)
(* ------------------------------------------------------------------ *)

Section seg5. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The walk's valuation: the 32 registers of the state the stretch starts at, and the extra atoms the stretch's
   read regions name. No shadow entry: the stretch runs no instrumented check. *)
Definition o5_E (regs : bvmap 5 word) (extra : list word) : env := Eimg (PI := PI_transport) (Ereg regs extra).
Definition o5_Bx : sv := SLit 0.
Definition o5_B0 : Z * Z := (0, 0).

Lemma o5_env : forall regs extra, img_env VAL A_LIM (o5_E regs extra).
Proof. intros regs extra. unfold o5_E. apply Eimg_env. Qed.

Lemma o5_ewr : forall regs extra n (r : bv 5),
  Z.of_nat n = bv_unsigned r -> ew (o5_E regs extra) n = YK11.getr regs r.
Proof. intros regs extra n r Hn. unfold o5_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma o5_ewx : forall regs extra j, (j < 200)%nat ->
  ew (o5_E regs extra) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof.
intros regs extra j Hj. unfold o5_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra.
Qed.

Lemma o5_ewo : forall regs extra (j : nat), (j < 159)%nat ->
  ew (o5_E regs extra) (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)).
Proof.
intros regs extra j Hj. unfold o5_E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia.
Qed.

Lemma o5_shok : forall regs extra (W : world segs) mem,
  sh_ok segs o5_Bx (@nil shent) (o5_E regs extra) (mrestrict (w_H W) mem).
Proof. intros regs extra W mem. apply Forall_nil. Qed.

Lemma o5_facts_nil : forall regs extra, facts_ok (o5_E regs extra) (mkFacts [] [] []).
Proof.
intros regs extra. unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
repeat split; exact I.
Qed.

(* A state at the first pc of a straight stretch: the registers as atoms, the regions the stretch reads or writes,
   and the atom facts the engine needs to place each written window (YP0j.v cells_safe_b). *)
Lemma o5_entry : forall (fx : YK11.FPState) (W : world segs) regs extra mem (pc : Z) (rs : smem) (G : facts),
  regions_wf rs = true ->
  Forall (region_ok segs (o5_E regs extra) (mrestrict (w_H W) mem)) rs ->
  pairwise_disjoint (o5_E regs extra) rs ->
  facts_ok (o5_E regs extra) G ->
  st_ok_pi segs VAL (o5_E regs extra) (mkSS pc sr_atoms rs None G)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros fx W regs extra mem pc rs G Hw Hr Hd Hf. rewrite restrict_mkst_fx.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- exact Hw.
- exact Hr.
- exact Hd.
- exact Hf.
Qed.

(* A state at the first pc of a stretch that reads and writes no memory. *)
Lemma o5_entry0 : forall (fx : YK11.FPState) (W : world segs) regs extra mem (pc : Z),
  st_ok_pi segs VAL (o5_E regs extra) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros fx W regs extra mem pc. apply o5_entry.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- apply o5_facts_nil.
Qed.

(* The value of the symbolic register atom n, and of an image object's atom. *)
Lemma o5_den_reg : forall regs extra (n : nat) (r : bv 5) (v : word),
  Z.of_nat n = bv_unsigned r -> YK11.getr regs r = v -> sv_denot (o5_E regs extra) (SOff n 0) = v.
Proof.
intros regs extra n r v Hn Hv. cbn [sv_denot].
rewrite (o5_ewr regs extra n r Hn), Hv, Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

Lemma o5_den_obj : forall regs extra (j : nat) (v : Z), (j < 159)%nat -> VAL (A_OBJ j) = v ->
  sv_denot (o5_E regs extra) (SOff (A_OBJ j) 0) = w64 v.
Proof.
intros regs extra j v Hj Hv. cbn [sv_denot].
rewrite (o5_ewo regs extra j Hj), Hv, Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

Lemma o5_lit64 : forall z, 0 <= z <= 18446744073709551615 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply unsigned_lit_small. change (2 ^ 64) with 18446744073709551616. lia. Qed.

(* The value of register q in the machine state of a symbolic state HS. *)
Ltac o5_reg HS q v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) q) in
      assert (H : YK11.getr (ms_regs msx) q = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx q HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) q) in
      assert (H : YK11.getr (ms_regs msx) q = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx q HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "o5_reg: no match for" T; fail
  end.

(* The write right of a run whose regions have no writable byte. *)
Ltac o5_awr0 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* The regions of run C (+0x644 .. +0x658): g_fail_next's byte at s4 - 1076 (read only, its value atom 32),
   OW.desk_off at s6 + 232 (written), the spill slot at s1 + 184 holding &M (read only, its value atom 33) and
   M.fail at (&M) + 88 (written, based at atom 33). *)
Definition o5_rg_gf : YP09.region :=
  YP09.mkRegion (Some 20%nat) (-1076) (-1075) 0 0 [YP09.mkChunk (-1076) (YP09.CVal 1 (SOff 32 0))].
Definition o5_rg_ow : YP09.region := YP09.mkRegion (Some 22%nat) 232 236 232 236 [].
Definition o5_rg_sp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 184 192 0 0 [YP09.mkChunk 184 (YP09.CVal 8 (SOff 33 0))].
Definition o5_rg_mf : YP09.region := YP09.mkRegion (Some 33%nat) 88 92 88 92 [].

(* The regions of run D (+0x65c .. +0x670): the spill slot at s1 + 176 holding transport_hi 9 (its value atom 32)
   and g_now's eight bytes at that page - 1052 (its value atom 33). *)
Definition o5_rg_hi : YP09.region :=
  YP09.mkRegion (Some 9%nat) 176 184 0 0 [YP09.mkChunk 176 (YP09.CVal 8 (SLit (transport_hi 9)))].
Definition o5_rg_nw : YP09.region :=
  YP09.mkRegion None TA_g_now (TA_g_now + 8) 0 0 [YP09.mkChunk TA_g_now (YP09.CVal 8 (SOff 32 0))].

(* The atom facts run C needs: the bases of its two written windows (OW and M), each at its exact address, so the
   engine can place them away from the shadow span (YP0j.v cells_safe_b). *)
Definition o5_facts_C : facts :=
  mkFacts [(22%nat, mkAF TA_OW TA_OW 5); (33%nat, mkAF TA_M TA_M 5)] [] [].

(* The same two written regions after run C, with the chunk each store left. *)
Definition o5_rg_ow2 : YP09.region :=
  YP09.mkRegion (Some 22%nat) 232 236 232 236
    [YP09.mkChunk 232 (YP09.CVal 4 (SLit 18446744073709551615))].
Definition o5_rg_mf2 : YP09.region :=
  YP09.mkRegion (Some 33%nat) 88 92 88 92
    [YP09.mkChunk 88 (YP09.CVal 4 (SExt false 8 (SOff 32 0)))].

(* The four bytes the `li a1, -1` store leaves are the model's put 4 (-1). *)
Lemma o5_le_m1 : forall j, (j < 4)%nat -> YO0f.le_byte 18446744073709551615 4 j = YO0f.le_byte (-1) 4 j.
Proof. intros j Hj. do 4 (destruct j as [|j]; [vm_compute; reflexivity|]). lia. Qed.

(* The value the `lbu` of g_fail_next leaves: its atom, zero-extended. *)
Lemma o5_zext8_den : forall E n u, ew E n = Z_to_bv 64 u -> 0 <= u < 256 ->
  sv_denot E (SExt false 8 (SOff n 0)) = Z_to_bv 64 u.
Proof.
intros E n u Hn Hu. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite O5MEM.zext_small. f_equal. rewrite O5MEM.extract_low_mod by lia.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with 18446744073709551616. change (2 ^ Z.of_N 8) with 256.
rewrite (Z.mod_small u) by lia. apply Z.mod_small. lia.
Qed.

(* The callee-saved registers but s6 (x22): OP5's own code writes s6 (s6 = &OW at +0x61c, s6 = want at +0x664,
   s6 = 7 at +0x678) and no other callee-saved register. *)
Definition O5_KEEP : list (bv 5) := map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27].
Definition o5_keep (r r' : bvmap 5 word) : Prop := forall x, In x O5_KEEP -> YK11.getr r' x = YK11.getr r x.
Ltac o5_inK := unfold O5_KEEP; cbn [map In]; repeat (first [left; reflexivity | right]).

Lemma o5_keep_trans : forall r1 r2 r3, o5_keep r1 r2 -> o5_keep r2 r3 -> o5_keep r1 r3.
Proof. intros r1 r2 r3 H12 H23 x Hx. rewrite (H23 x Hx). exact (H12 x Hx). Qed.
Lemma o5_keep_of_pres : forall r r', aregs_preserved r r' -> o5_keep r r'.
Proof.
intros r r' H x Hx. unfold O5_KEEP in Hx. apply in_map_iff in Hx as (k & <- & Hk).
apply H. unfold acallee_saved. cbn [In] in Hk.
repeat (destruct Hk as [Hk|Hk]; [subst k; lia|]). destruct Hk.
Qed.
Lemma o5_pres_of_keep : forall r r', o5_keep r r' -> YK11.getr r' (Z_to_bv 5 22) = YK11.getr r (Z_to_bv 5 22) ->
  aregs_preserved r r'.
Proof.
intros r r' H H22 k Hk. destruct (Z.eq_dec k 22) as [->|Hne]; [exact H22|].
apply H. unfold O5_KEEP. apply in_map_iff. exists k. split; [reflexivity|].
unfold acallee_saved in Hk.
assert (Ek : k = 2 \/ k = 3 \/ k = 4 \/ k = 8 \/ k = 9 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/
             k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27) by lia.
cbn [In]. clear Hk. repeat (destruct Ek as [Ek|Ek]; [subst k; tauto|]). subst k. tauto.
Qed.

Lemma o5_agree : forall regs extra, env_agree 32 (Ereg regs extra) (o5_E regs extra).
Proof.
intros regs extra. split; [intros n Hn; unfold o5_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.

(* The callee window of this stretch: the widest window LLVMFuzzerTestOneInput's closure uses below the realigned sp
   (LLVMFuzzerTestOneInput_cg.v TRANS_LLVMF_USE less the frame and the realignment). It covers the two intrinsics'
   ESTACK, m_wake's MWAKE_STK, diginet_session_wake's WAKE_STK and the leaf's ESTACK, and 336 + it fits LLVMF_STK
   (trans_llvmf_use_fits), which is what LLVMFuzzerTestOneInput_st.v lc_core_kept asks. *)
Definition O5_X : Z := TRANS_LLVMF_USE - TRANS_LLVMF_FRAME - TRANS_LLVMF_ALIGN.
Lemma o5_X_fits : 336 + O5_X <= LLVMF_STK /\ ESTACK <= O5_X /\ MWAKE_STK <= O5_X /\ WAKE_STK <= O5_X /\ 0 <= O5_X.
Proof. vm_compute. repeat split; intros H; discriminate H. Qed.

(* The callee-saved registers but s6, read off a state the run left. *)
Section kr. Context {fx : YK11.FPState}.
Lemma o5_keep_run : forall (Hh : word -> bool) E ss ms regs0 extra,
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok segs E ss (restrict Hh ms) ->
  env_agree 32 (Ereg regs0 extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) O5_KEEP = true ->
  o5_keep regs0 (ms_regs ms).
Proof.
intros Hh E ss ms regs0 extra HS HA Hl x Hx.
exact (regs_kept_of_st_ok segs E ss (restrict Hh ms) regs0 extra O5_KEEP HS HA Hl x Hx).
Qed.
End kr.

(* A step of the walk's own code, at the current world W1, that changes only bytes of the callees' stack window
   [slo, shi) or bytes of G in the written range Eo keeps what the walk carries. *)
Lemma o5_step : forall lyc Sc (W : world segs) memc mdc (W1 : world segs) memX memY slo shi (Eo Zs : Z -> Prop),
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS ->
  @AR rc segs B lyc Sc W memc mdc -> alloc_ceiling <= slo ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W1 memX slo shi Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W1) memY a = aview segs (w_H W1) memX a) ->
  (forall a, apresent (w_H W1) memX a -> apresent (w_H W1) memY a) ->
  (forall a, Zs a -> (slo <= a < shi) \/ (W_journalG.inG TG.G_HARNESS a /\ Eo a)) ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W1 memY slo shi Eo.
Proof.
intros lyc Sc W memc mdc W1 memX memY slo shi Eo Zs LAWS HGX HAR Hslo KP Hkp Hgr HZ.
pose proof (@YM05.alloc_ceiling_val rc) as (CR & _).
apply (dk_kept_step_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc W1 memX memY slo shi Eo Zs
  HAR KP Hkp Hgr).
- intros a Ha Hc. destruct (HZ a Ha) as [Hw | (Hg & _)]; [exact Hw|]. exfalso.
  pose proof (inG_low tfibsegs B transport_segs_low TG.G_HARNESS a HGX Hg) as Hl. unfold kLowMemEnd in Hl. lia.
- intros b m i Hb Hi Hz. destruct (HZ _ Hz) as [Hw | (_ & He)]; [|exact He]. exfalso.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hce & _). lia.
- intros a Hz Hi HnG _ _. destruct (HZ a Hz) as [Hw | (Hg & _)]; [|exact (HnG Hg)].
  pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl. lia.
- intros cid pos a Hin Hr Hz. destruct (HZ a Hz) as [Hw | (_ & He)]; [|exact He]. exfalso.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
  assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
  unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
Qed.

Lemma lc_op5_ok (K1 : @lc_rom_view_stmt rc B MT XL RLO RHI) (K6 : lc_runinv_stmt) :
  @lc_op5_stmt rc B MT XL RLO RHI.
Proof.
unfold lc_op5_stmt. intros HP cx op W c HB HARM.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (G_HARNESS_gx_noerrno B (lp_g_no_errno _ _ _ _ _ HP)) as HGNE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HARM as (ly0 & S0 & regs0 & mem0 & md0 & e0 & Ec & Hopc & HL & Htw0 & Hcur9 & Hcur8 & R20 & R22).
pose proof HL as (HCORE & HFR & HSPL & HFSH & HOPOK & HEV & HMET & R21).
pose proof (@lc_geom rc B MT XL RLO RHI cx ly0 S0 W regs0 mem0 md0 e0 HB HCORE) as GEO.
destruct GEO as [HAR0 Hsp0al Hstk Hsp1c HFaddr HFin Hnlen Hinb Hlive].
destruct Hstk as (Hceil & Hslo & Hshi & H47).
pose proof HCORE as (HJ0 & Hfrs0 & HlyF0 & HPERM0 & Rsp & R8 & R9 & Rgp & Rtp & Hsp1b & Hsp1m & HSAV &
  HF4096 & HFal & HFceil & HFpres & HFL & HIN).
pose proof HOPOK as (HAGREE & HOPS & HFIO & HFIN & HKOPS).
pose proof HFR as (R18 & R26).
pose proof HB as (HAFN & Hra0 & Ha0 & Ha1 & Hpn & Hnl & Hgarr & Hfrs00 & Hev & Hlive2 & Hrod & Hsink & Hfd &
  Hfss & Hmeta & Hmok0).
assert (LB : length (lo_B op) = Z.to_nat TW.W_LEN) by exact (AG.ac_len _ _ _ (AG.ag_core _ _ _ HAGREE)).
assert (LBZ : Z.of_nat (length (lo_B op)) = TW.W_LEN)
  by (rewrite LB; unfold TW.W_LEN; reflexivity).
pose proof (lp_meter_laws _ _ _ _ _ HP) as MTL.
destruct (o5_model (lo_ops op) (lo_B op) (l_pl cx) (lo_c op) (lo_k op) HAGREE HOPS (eq_sym Hopc))
  as (B1 & B2 & B3 & want & r & EB1 & HA1 & EB2 & EB3 & Erw & ES & HA3 & EOP).
subst c.
(* the straight stretches run from a state whose registers are atoms; no stretch of OP5 runs a checked access *)
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUNTO.
pose proof (@YM05.alloc_ceiling_val rc) as (CEILR & CEILM).
change (2 ^ 47) with 140737488355328 in H47.
assert (HSP1 : 0 <= lc_sp1 cx < 2 ^ 64).
{ change (2 ^ 64) with 18446744073709551616. unfold LF_FRAME in Hsp1b. lia. }
assert (HXB : 0 <= O5_X <= 32432 /\ ESTACK <= O5_X /\ MWAKE_STK <= O5_X /\ WAKE_STK <= O5_X).
{ pose proof o5_X_fits as HX. unfold LLVMF_STK in HX. lia. }
destruct HXB as (HXa & HXb & HXc & HXd).
assert (HCE : alloc_ceiling <= lc_sp1 cx - O5_X) by lia.
assert (HSTKHI : lc_sp1 cx + 192 < 18446744073709551616) by (unfold LF_FRAME in Hsp1b; lia).
assert (HSP1hi : lc_sp1 cx <= 2 ^ 64) by (change (2 ^ 64) with 18446744073709551616; lia).
(* the offset of the realigned sp inside the slot's frame: a multiple of 16, at most 0 *)
assert (HO16 : (lc_sp1 cx - lc_sp0 cx) mod 16 = 0).
{ pose proof (Z.div_mod (lc_sp1 cx) 32 ltac:(lia)) as D32. rewrite Hsp1m, Z.add_0_r in D32.
  pose proof (Z.div_mod (lc_sp0 cx) 16 ltac:(lia)) as D16. rewrite Hsp0al, Z.add_0_r in D16.
  replace (lc_sp1 cx - lc_sp0 cx) with (16 * (2 * (lc_sp1 cx / 32) - lc_sp0 cx / 16)) by lia.
  rewrite Z.mul_comm. apply Z_mod_mult. }
(* the stack bytes of the slot's frame are present at the cut *)
pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). rewrite !Z.add_0_r in HJi0.
pose proof HJi0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & _).
clear HJi0 memS0.
(* ---- run A, +0x618 .. +0x62c: s6 = &OW, the memset's arguments and the call ---- *)
unfold lc_cfg.
assert (EPCA : w64 (transport_text + lo_arm 5) = Z_to_bv 64 (BASE + 1560)) by (vm_compute; reflexivity).
rewrite EPCA.
assert (HEI : img_env VAL A_LIM (o5_E regs0 (@nil word))) by apply o5_env.
assert (SHOK : sh_ok segs o5_Bx (@nil shent) (o5_E regs0 (@nil word)) (mrestrict (w_H W) mem0)) by apply o5_shok.
pose proof (o5_entry0 (l_fx cx) W regs0 (@nil word) mem0 1560) as HS.
paj_run_tok RUN HS HJ0 SHOK o5_B0.
{ o5_awr0. }
set (md1 := with_vm_backing (m_vm_lazy md0) mat md0) in *. clearbody md1. clear mat.
rename ms into ms1. rename HJ0 into HJ1.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) mem0 a).
{ intros a Ha. apply (YC4b.kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin. destruct Hin. }
assert (GR1 : forall a, apresent (w_H W) mem0 a -> apresent (w_H W) (ms_mem ms1) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
o5_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 1584)) QA1 ltac:(apply codeptr_val; exact HEI).
o5_reg HS (2%bv : bv 5) (w64 (lc_sp1 cx)) QA2
  ltac:(exact (o5_den_reg regs0 (@nil word) 2%nat (2%bv : bv 5) _ eq_refl Rsp)).
o5_reg HS (3%bv : bv 5) (w64 (as_gp B)) QA3
  ltac:(exact (o5_den_reg regs0 (@nil word) 3%nat (3%bv : bv 5) _ eq_refl Rgp)).
o5_reg HS (4%bv : bv 5) (w64 (as_tp B)) QA4
  ltac:(exact (o5_den_reg regs0 (@nil word) 4%nat (4%bv : bv 5) _ eq_refl Rtp)).
o5_reg HS (10%bv : bv 5) (w64 TA_OW) QA10
  ltac:(exact (o5_den_obj regs0 (@nil word) 12%nat TA_OW ltac:(lia) ltac:(vm_compute; reflexivity))).
o5_reg HS (9%bv : bv 5) (w64 (lc_sp1 cx)) QA9
  ltac:(exact (o5_den_reg regs0 (@nil word) 9%nat (9%bv : bv 5) _ eq_refl R9)).
o5_reg HS (11%bv : bv 5) (w64 0) QA11 ltac:(reflexivity).
o5_reg HS (12%bv : bv 5) (w64 304) QA12 ltac:(reflexivity).
o5_reg HS (20%bv : bv 5) (w64 LF_S4) QA20
  ltac:(exact (o5_den_reg regs0 (@nil word) 20%nat (20%bv : bv 5) _ eq_refl R20)).
o5_reg HS (22%bv : bv 5) (w64 TA_OW) QA22
  ltac:(exact (o5_den_obj regs0 (@nil word) 12%nat TA_OW ltac:(lia) ltac:(vm_compute; reflexivity))).
assert (KPR1 : o5_keep regs0 (ms_regs ms1)).
{ apply (o5_keep_run (w_H W) (o5_E regs0 (@nil word)) _ _ regs0 (@nil word) HS
    (o5_agree regs0 (@nil word))). vm_compute. reflexivity. }
assert (TW1 : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms1)) (lo_B op)).
{ apply (tw_kept TMAP_A (aview segs (w_H W) mem0)); [exact Htw0|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  apply KR1. change (2 ^ 64) with 18446744073709551616. lia. }
assert (USPA : spZ (ms_regs ms1) = lc_sp1 cx)
  by (unfold spZ; rewrite QA2; unfold w64; apply unsigned_lit_small; lia).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
destruct (o5_sh_ow B (lp_recv_cells _ _ _ _ _ HP) ly0 S0 W (ms_mem ms1) md1 HAR1) as (HRAow & HHULLow).
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transport_sigma TS___asan_memset)) mm rom) mdx) Q)
end.
eapply SRr_bind.
{ apply (@gx_intrin_at (l_fx cx) rc tfib_sink_head segs B LAWS transport_segs_low OSet
    (transport_sigma TS___asan_memset) (lp_memset _ _ _ _ _ HP (l_fx cx)) TG.G_HARNESS W (ms_regs ms1)
    (ms_mem ms1) LLVMF_STK (lc_sp0 cx) _ (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) _ ly0 S0 md1 e0
    TA_OW 0 304 (lc_sp1 cx - lc_sp0 cx) (Z_to_bv 64 (BASE + 1584)) HGX G_HARNESS_rw HJ1 QA10 QA11 QA12).
  - lia.
  - unfold TA_OW; lia.
  - unfold TA_OW; lia.
  - rewrite USPA; lia.
  - exact HO16.
  - unfold LF_FRAME in Hsp1b; lia.
  - unfold LLVMF_STK, ESTACK; unfold LF_FRAME in Hsp1b; lia.
  - exact QA3.
  - exact QA4.
  - exact QA1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ1|].
    intros a Ha. right. apply o5_inG. right; left. unfold TW.SZ_OW in *; lia.
  - unfold amem_range, TA_OW, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia.
  - exact HRAow.
  - intros _; exact HHULLow.
  - exact I. }
cbv beta. intros WA cA _ (EWA & regsA & memA & mdA & EcA & HJA & HPA & Qa0 & HFILLA & HKEPTA & HGRA).
subst WA. subst cA.
(* the world after op_begin's fill of OW *)
assert (TWA : tw_at TMAP_A (aview segs (w_H W) memA) (o5_w1 (lo_B op))).
{ refine (tw_fill_set TMAP_A _ _ _ TW.OFF_OW TA_OW TW.SZ_OW 0 0 304 TMAP_A_ok TW1 TMAP_A_OW
    ltac:(lia) ltac:(lia) ltac:(unfold TW.SZ_OW; lia) _ _).
  - intros i Hi. replace (TA_OW + 0 + i) with (TA_OW + i) by lia. exact (HFILLA i Hi).
  - intros x Hx Hn. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    apply HKEPTA; [change (2 ^ 64) with 18446744073709551616; lia | lia | unfold ESTACK; lia]. }
(* what the two steps so far kept *)
assert (KA1 : acall_kept_g segs B TG.G_HARNESS ly0 S0 W mem0 W memA
  (lc_sp1 cx - O5_X) (lc_sp1 cx) (o5_wr B1 B2)).
{ apply (o5_step ly0 S0 W mem0 md0 W (ms_mem ms1) memA (lc_sp1 cx - O5_X) (lc_sp1 cx) (o5_wr B1 B2)
    (fun a => TA_OW <= a < TA_OW + 304 \/ (lc_sp1 cx - ESTACK <= a < lc_sp1 cx))
    LAWS HGX HAR0 HCE).
  - apply (o5_step ly0 S0 W mem0 md0 W mem0 (ms_mem ms1) (lc_sp1 cx - O5_X) (lc_sp1 cx) (o5_wr B1 B2)
      (fun _ : Z => False) LAWS HGX HAR0 HCE).
    + apply dk_kept_refl_g. intros a Ha. apply Hpres0.
      pose proof o5_X_fits as HX. unfold LF_FRAME, LLVMF_STK in *. lia.
    + intros a Ha _. exact (KR1 a Ha).
    + exact GR1.
    + intros a [].
  - intros a Ha Hn. apply HKEPTA; [exact Ha | tauto |].
    intros Hc. apply Hn. right. unfold ESTACK in *. lia.
  - exact HGRA.
  - intros a [Hz | Hz]; [right | left].
    + split; [apply o5_inG; right; left; unfold TW.SZ_OW; lia | left; unfold TW.SZ_OW; lia].
    + unfold ESTACK in *. lia. }
(* the callee-saved registers the rest of the stretch reads, at the return of the fill *)
assert (RB2 : YK11.getr regsA (Z_to_bv 5 2) = w64 (lc_sp1 cx))
  by (rewrite (HPA 2 ltac:(hnf; lia)); exact QA2).
assert (RB3 : YK11.getr regsA (Z_to_bv 5 3) = w64 (as_gp B))
  by (rewrite (HPA 3 ltac:(hnf; lia)); exact QA3).
assert (RB4 : YK11.getr regsA (Z_to_bv 5 4) = w64 (as_tp B))
  by (rewrite (HPA 4 ltac:(hnf; lia)); exact QA4).
assert (RB9 : YK11.getr regsA (Z_to_bv 5 9) = w64 (lc_sp1 cx))
  by (rewrite (HPA 9 ltac:(hnf; lia)); exact QA9).
assert (RB20 : YK11.getr regsA (Z_to_bv 5 20) = w64 LF_S4)
  by (rewrite (HPA 20 ltac:(hnf; lia)); exact QA20).
assert (RB22 : YK11.getr regsA (Z_to_bv 5 22) = w64 TA_OW)
  by (rewrite (HPA 22 ltac:(hnf; lia)); exact QA22).
assert (KPA : o5_keep regs0 regsA) by (apply (o5_keep_trans regs0 (ms_regs ms1)); [exact KPR1 | apply o5_keep_of_pres; exact HPA]).
clear dependent ms1.
(* ---- run B, +0x630 .. +0x640: a0 = &GOT, the fill's arguments and the call ---- *)
clear HEI.
assert (HEI : img_env VAL A_LIM (o5_E regsA (@nil word))) by apply o5_env.
assert (SHOK : sh_ok segs o5_Bx (@nil shent) (o5_E regsA (@nil word)) (mrestrict (w_H W) memA)) by apply o5_shok.
pose proof (o5_entry0 (l_fx cx) W regsA (@nil word) memA 1584) as HS.
paj_run_tok RUN HS HJA SHOK o5_B0.
{ o5_awr0. }
set (md2 := with_vm_backing (m_vm_lazy mdA) mat mdA) in *. clearbody md2. clear mat.
rename ms into ms2. rename HJA into HJ2.
assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) (ms_mem ms2) a = aview segs (w_H W) memA a).
{ intros a Ha. apply (YC4b.kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin. destruct Hin. }
assert (GR2 : forall a, apresent (w_H W) memA a -> apresent (w_H W) (ms_mem ms2) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
assert (KPR2 : o5_keep regsA (ms_regs ms2)).
{ apply (o5_keep_run (w_H W) (o5_E regsA (@nil word)) _ _ regsA (@nil word) HS
    (o5_agree regsA (@nil word))). vm_compute. reflexivity. }
clear HF HFr HG.
o5_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 1604)) QB1 ltac:(apply codeptr_val; exact HEI).
o5_reg HS (2%bv : bv 5) (w64 (lc_sp1 cx)) QB2
  ltac:(exact (o5_den_reg regsA (@nil word) 2%nat (2%bv : bv 5) _ eq_refl RB2)).
o5_reg HS (3%bv : bv 5) (w64 (as_gp B)) QB3
  ltac:(exact (o5_den_reg regsA (@nil word) 3%nat (3%bv : bv 5) _ eq_refl RB3)).
o5_reg HS (4%bv : bv 5) (w64 (as_tp B)) QB4
  ltac:(exact (o5_den_reg regsA (@nil word) 4%nat (4%bv : bv 5) _ eq_refl RB4)).
o5_reg HS (10%bv : bv 5) (w64 TA_GOT) QB10
  ltac:(exact (o5_den_obj regsA (@nil word) 13%nat TA_GOT ltac:(lia) ltac:(vm_compute; reflexivity))).
o5_reg HS (11%bv : bv 5) (w64 0) QB11 ltac:(reflexivity).
o5_reg HS (12%bv : bv 5) (w64 224) QB12 ltac:(reflexivity).
o5_reg HS (9%bv : bv 5) (w64 (lc_sp1 cx)) QB9
  ltac:(exact (o5_den_reg regsA (@nil word) 9%nat (9%bv : bv 5) _ eq_refl RB9)).
o5_reg HS (20%bv : bv 5) (w64 LF_S4) QB20
  ltac:(exact (o5_den_reg regsA (@nil word) 20%nat (20%bv : bv 5) _ eq_refl RB20)).
o5_reg HS (22%bv : bv 5) (w64 TA_OW) QB22
  ltac:(exact (o5_den_reg regsA (@nil word) 22%nat (22%bv : bv 5) _ eq_refl RB22)).
assert (TWB0 : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms2)) (o5_w1 (lo_B op))).
{ apply (tw_kept TMAP_A (aview segs (w_H W) memA)); [exact TWA|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  apply KR2. change (2 ^ 64) with 18446744073709551616. lia. }
assert (USPB : spZ (ms_regs ms2) = lc_sp1 cx)
  by (unfold spZ; rewrite QB2; unfold w64; apply unsigned_lit_small; lia).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
destruct (o5_sh_got B (lp_recv_cells _ _ _ _ _ HP) ly0 S0 W (ms_mem ms2) md2 HAR2) as (HRAgot & HHULLgot).
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transport_sigma TS___asan_memset)) mm rom) mdx) Q)
end.
eapply SRr_bind.
{ apply (@gx_intrin_at (l_fx cx) rc tfib_sink_head segs B LAWS transport_segs_low OSet
    (transport_sigma TS___asan_memset) (lp_memset _ _ _ _ _ HP (l_fx cx)) TG.G_HARNESS W (ms_regs ms2)
    (ms_mem ms2) LLVMF_STK (lc_sp0 cx) _ (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) _ ly0 S0 md2 e0
    TA_GOT 0 224 (lc_sp1 cx - lc_sp0 cx) (Z_to_bv 64 (BASE + 1604)) HGX G_HARNESS_rw HJ2 QB10 QB11 QB12).
  - lia.
  - unfold TA_GOT; lia.
  - unfold TA_GOT; lia.
  - rewrite USPB; lia.
  - exact HO16.
  - unfold LF_FRAME in Hsp1b; lia.
  - unfold LLVMF_STK, ESTACK; unfold LF_FRAME in Hsp1b; lia.
  - exact QB3.
  - exact QB4.
  - exact QB1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ2|].
    intros a Ha. right. apply o5_inG. right; right; left. unfold TW.SZ_GOT in *; lia.
  - unfold amem_range, TA_GOT, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia.
  - exact HRAgot.
  - intros _; exact HHULLgot.
  - exact I. }
cbv beta. intros WB cB _ (EWB & regsB & memB & mdB & EcB & HJB & HPB & Qb0 & HFILLB & HKEPTB & HGRB).
subst WB. subst cB.
(* the world after op_begin's fill of GOT *)
assert (TWB : tw_at TMAP_A (aview segs (w_H W) memB) (o5_w2 (lo_B op))).
{ unfold o5_w2.
  refine (tw_fill_set TMAP_A _ _ _ TW.OFF_GOT TA_GOT TW.SZ_GOT 0 0 224 TMAP_A_ok TWB0 TMAP_A_GOT
    ltac:(lia) ltac:(lia) ltac:(unfold TW.SZ_GOT; lia) _ _).
  - intros i Hi. replace (TA_GOT + 0 + i) with (TA_GOT + i) by lia. exact (HFILLB i Hi).
  - intros x Hx Hnw. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    apply HKEPTB; [change (2 ^ 64) with 18446744073709551616; lia | lia | unfold ESTACK; lia]. }
(* what the walk kept through the second fill *)
assert (KA2 : acall_kept_g segs B TG.G_HARNESS ly0 S0 W mem0 W memB
  (lc_sp1 cx - O5_X) (lc_sp1 cx) (o5_wr B1 B2)).
{ apply (o5_step ly0 S0 W mem0 md0 W (ms_mem ms2) memB (lc_sp1 cx - O5_X) (lc_sp1 cx) (o5_wr B1 B2)
    (fun a => TA_GOT <= a < TA_GOT + 224 \/ (lc_sp1 cx - ESTACK <= a < lc_sp1 cx))
    LAWS HGX HAR0 HCE).
  - apply (o5_step ly0 S0 W mem0 md0 W memA (ms_mem ms2) (lc_sp1 cx - O5_X) (lc_sp1 cx) (o5_wr B1 B2)
      (fun _ : Z => False) LAWS HGX HAR0 HCE).
    + exact KA1.
    + intros a Ha _. exact (KR2 a Ha).
    + exact GR2.
    + intros a [].
  - intros a Ha Hnw. apply HKEPTB; [exact Ha | tauto |].
    intros Hc. apply Hnw. right. unfold ESTACK in *. lia.
  - exact HGRB.
  - intros a [Hz | Hz]; [right | left].
    + split; [apply o5_inG; right; right; left; unfold TW.SZ_GOT; lia
             | right; left; unfold TW.SZ_GOT; lia].
    + unfold ESTACK in *. lia. }
(* the callee-saved registers at the return of the second fill *)
assert (RC2 : YK11.getr regsB (Z_to_bv 5 2) = w64 (lc_sp1 cx))
  by (rewrite (HPB 2 ltac:(hnf; lia)); exact QB2).
assert (RC3 : YK11.getr regsB (Z_to_bv 5 3) = w64 (as_gp B))
  by (rewrite (HPB 3 ltac:(hnf; lia)); exact QB3).
assert (RC4 : YK11.getr regsB (Z_to_bv 5 4) = w64 (as_tp B))
  by (rewrite (HPB 4 ltac:(hnf; lia)); exact QB4).
assert (RC9 : YK11.getr regsB (Z_to_bv 5 9) = w64 (lc_sp1 cx))
  by (rewrite (HPB 9 ltac:(hnf; lia)); exact QB9).
assert (RC20 : YK11.getr regsB (Z_to_bv 5 20) = w64 LF_S4)
  by (rewrite (HPB 20 ltac:(hnf; lia)); exact QB20).
assert (RC22 : YK11.getr regsB (Z_to_bv 5 22) = w64 TA_OW)
  by (rewrite (HPB 22 ltac:(hnf; lia)); exact QB22).
assert (KPB : o5_keep regs0 regsB)
  by (apply (o5_keep_trans regs0 regsA); [exact KPA |
      apply (o5_keep_trans regsA (ms_regs ms2)); [exact KPR2 | apply o5_keep_of_pres; exact HPB]]).
(* the spill slot at sp1 + 184 still holds &M *)
assert (KSTKB : forall a, lc_sp1 cx <= a < lc_sp1 cx + 192 ->
  aview segs (w_H W) memB a = aview segs (w_H W) mem0 a).
{ intros a Ha. pose proof KA2 as (KK1 & _).
  apply KK1; [change (2 ^ 64) with 18446744073709551616; lia | lia]. }
assert (HSP184 : rdword (aview segs (w_H W) memB) (lc_sp1 cx + 184) = Some TA_M).
{ rewrite (rdword_ext (aview segs (w_H W) mem0) (aview segs (w_H W) memB) (lc_sp1 cx + 184))
    by (intros j Hj; apply KSTKB; lia).
  unfold lc_spills in HSPL. rewrite Forall_forall in HSPL.
  exact (HSPL (184, TA_M)
    ltac:(unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm; cbn [app In]; tauto)). }
clear dependent ms2.
(* ---- run C, +0x644 .. +0x658: g_fail_next, OW.desk_off = -1, M.fail, the call of m_wake ---- *)
clear HEI.
assert (ELS4 : LF_S4 = 6157652) by reflexivity.
assert (ETAM : TA_M = 6156640) by reflexivity.
assert (ETAOW : TA_OW = 6238304) by reflexivity.
assert (ETAGF : TA_g_fail_next = 6156576) by reflexivity.
assert (ETAGN : TA_g_now = 6156544) by reflexivity.
assert (ETHI9 : transport_hi 9 = 6157596) by reflexivity.
pose (GFV := TW.g_fail_next (o5_w2 (lo_B op))).
pose (EXC := [w64 GFV; w64 TA_M] : list word).
assert (HGFV : 0 <= GFV < 256).
{ pose proof (TWL.u_at_range (o5_w2 (lo_B op)) TW.OFF_g_fail_next 1) as R.
  cbn [Z.of_nat] in R. unfold GFV, TW.g_fail_next. cbn [Z.mul] in R. lia. }
assert (HEI : img_env VAL A_LIM (o5_E regsB EXC)) by apply o5_env.
assert (SHOK : sh_ok segs o5_Bx (@nil shent) (o5_E regsB EXC) (mrestrict (w_H W) memB)) by apply o5_shok.
assert (EC32 : ew (o5_E regsB EXC) 32%nat = w64 GFV) by exact (o5_ewx regsB EXC 0%nat ltac:(lia)).
assert (EC33 : ew (o5_E regsB EXC) 33%nat = w64 TA_M) by exact (o5_ewx regsB EXC 1%nat ltac:(lia)).
assert (UC20 : bv_unsigned (ew (o5_E regsB EXC) 20%nat) = LF_S4).
{ rewrite (o5_ewr regsB EXC 20%nat (Z_to_bv 5 20) eq_refl), RC20, ELS4. apply o5_lit64. lia. }
assert (UC22 : bv_unsigned (ew (o5_E regsB EXC) 22%nat) = TA_OW).
{ rewrite (o5_ewr regsB EXC 22%nat (Z_to_bv 5 22) eq_refl), RC22, ETAOW. apply o5_lit64. lia. }
assert (UC9 : bv_unsigned (ew (o5_E regsB EXC) 9%nat) = lc_sp1 cx).
{ rewrite (o5_ewr regsB EXC 9%nat (Z_to_bv 5 9) eq_refl), RC9. apply o5_lit64. lia. }
assert (UC33 : bv_unsigned (ew (o5_E regsB EXC) 33%nat) = TA_M)
  by (rewrite EC33, ETAM; apply o5_lit64; lia).
assert (HRGC : Forall (region_ok segs (o5_E regsB EXC) (mrestrict (w_H W) memB))
  [o5_rg_gf; o5_rg_ow; o5_rg_sp; o5_rg_mf]).
{ repeat apply Forall_cons; try apply Forall_nil.
  - unfold o5_rg_gf, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite UC20, ELS4. split; [lia|].
    split; [change (2 ^ 64) with 18446744073709551616; lia|].
    split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs (o5_E regsB EXC) (mrestrict (w_H W) memB) 6157652 (-1076) 1 (SOff 32 0) GFV).
    + cbn [sv_denot]. rewrite EC32, Z.add_0_r, (o5_lit64 GFV ltac:(lia)). reflexivity.
    + cbn [Z.of_N N.to_nat]. change (8 * 1) with 8. change (2 ^ 8) with 256. lia.
    + cbn [Z.of_N]. lia.
    + replace (6157652 + -1076) with (TA_g_fail_next + 0) by (rewrite ETAGF; lia).
      exact (tw_read_val segs (mrestrict (w_H W) memB) TMAP_A (o5_w2 (lo_B op)) TW.OFF_g_fail_next
        TA_g_fail_next 1 0 1 TMAP_A_ok TWB TMAP_A_g_fail_next ltac:(lia) ltac:(cbn [Z.of_nat]; lia)).
  - unfold o5_rg_ow, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite UC22, ETAOW. split; [lia|].
    split; [change (2 ^ 64) with 18446744073709551616; lia|].
    split; [| apply Forall_nil].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (6238304 + o) G_HARNESS_rw).
    apply o5_inG. right; left. rewrite ETAOW. unfold TW.SZ_OW. lia.
  - unfold o5_rg_sp, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite UC9. split; [lia|].
    split; [change (2 ^ 64) with 18446744073709551616; lia|].
    split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs (o5_E regsB EXC) (mrestrict (w_H W) memB) (lc_sp1 cx) 184 8 (SOff 33 0) TA_M).
    + cbn [sv_denot]. rewrite EC33, Z.add_0_r, ETAM, (o5_lit64 6156640 ltac:(lia)). reflexivity.
    + cbn [Z.of_N N.to_nat]. change (8 * 8) with 64. change (2 ^ 64) with 18446744073709551616.
      rewrite ETAM. lia.
    + cbn [Z.of_N]. lia.
    + exact (val_mem_of_rdword segs (w_H W) memB (lc_sp1 cx + 184) TA_M HSP184).
  - unfold o5_rg_mf, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite UC33, ETAM. split; [lia|].
    split; [change (2 ^ 64) with 18446744073709551616; lia|].
    split; [| apply Forall_nil].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (6156640 + o) G_HARNESS_rw).
    apply o5_inG. left. rewrite ETAM. unfold TW.SZ_M. lia. }
assert (HPDC : pairwise_disjoint (o5_E regsB EXC) [o5_rg_gf; o5_rg_ow; o5_rg_sp; o5_rg_mf]).
{ apply pairwise_disjoint_of_extents.
  unfold o5_rg_gf, o5_rg_ow, o5_rg_sp, o5_rg_mf, extent_of_region.
  cbn [map zpairwise_disjoint zall_disjoint zdisj fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite UC20, UC22, UC9, UC33, ELS4, ETAOW, ETAM.
  repeat split; try exact I; unfold zdisj; cbn [fst snd]; lia. }
assert (HFC : facts_ok (o5_E regsB EXC) o5_facts_C).
{ unfold o5_facts_C, facts_ok.
  cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite UC22, UC33, ETAOW, ETAM.
  repeat split; try exact I; try lia; vm_compute; reflexivity. }
pose proof (o5_entry (l_fx cx) W regsB EXC memB 1604 [o5_rg_gf; o5_rg_ow; o5_rg_sp; o5_rg_mf] o5_facts_C
  ltac:(vm_compute; reflexivity) HRGC HPDC HFC) as HS.
paj_run_tok RUN HS HJB SHOK o5_B0.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat first
    [ apply awr_ok_x_nil
    | apply awr_ok_x_cons;
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia | ]
    | apply awr_ok_x_cons_g;
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
        rewrite ?UC22, ?UC33, ?ETAOW, ?ETAM in Ha;
        apply o5_inG; rewrite ?ETAOW, ?ETAM; unfold TW.SZ_M, TW.SZ_OW;
        first [ left; lia | right; left; lia ] | ] ]. }
set (md3 := with_vm_backing (m_vm_lazy mdB) mat mdB) in *. clearbody md3. clear mat.
rename ms into ms3. rename HJB into HJ3.
assert (KR3 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (TA_OW + 232 <= a < TA_OW + 236) -> ~ (TA_M + 88 <= a < TA_M + 92) ->
  aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) memB a).
{ intros a Ha Hn1 Hn2.
  apply (YC4b.kept_of_frame _ _ _ _ _
    (fun x => (TA_OW + 232 <= x < TA_OW + 236) \/ (TA_M + 88 <= x < TA_M + 92)) HFr);
    [| exact Ha | intros [Hc|Hc]; [exact (Hn1 Hc) | exact (Hn2 Hc)]].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  clear - Hin Hx UC22 UC33.
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H
  | H : False |- _ => destruct H
  | H : (_, _, _) = (_, _, _) |- _ => inversion H; subst; clear H
  end;
  cbn [base_val] in Hx; rewrite ?UC22, ?UC33 in Hx; cbv beta;
  first [left; lia | right; lia | lia]. }
assert (GR3 : forall a, apresent (w_H W) memB a -> apresent (w_H W) (ms_mem ms3) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
assert (KPR3 : o5_keep regsB (ms_regs ms3)).
{ apply (o5_keep_run (w_H W) (o5_E regsB EXC) _ _ regsB EXC HS (o5_agree regsB EXC)).
  vm_compute. reflexivity. }
clear HF HFr HG.
(* the two stores, read back from the regions the run left *)
pose proof (YC4b.st_ok_region_nth _ _ _ 1%nat o5_rg_ow2 HS
  ltac:(cbn [ss_mem setpc sh_ss]; reflexivity)) as ROW.
pose proof (YC4b.st_ok_region_nth _ _ _ 3%nat o5_rg_mf2 HS
  ltac:(cbn [ss_mem setpc sh_ss]; reflexivity)) as RMF.
assert (VOW : forall j, (j < 4)%nat ->
  aview segs (w_H W) (ms_mem ms3) (TA_OW + 232 + Z.of_nat j) = Some (YO0f.le_byte (-1) 4 j)).
{ intros j Hj. rewrite <- (o5_le_m1 j Hj).
  exact (MWW.mw_cval (o5_E regsB EXC) W (ms_mem ms3) o5_rg_ow2 22%nat TA_OW 232 4
    (SLit 18446744073709551615) 18446744073709551615 ROW eq_refl UC22
    ltac:(unfold o5_rg_ow2; cbn [YP09.r_chunks]; left; reflexivity)
    ltac:(cbn [sv_denot]; reflexivity) ltac:(lia) ltac:(cbn [Z.of_N]; lia) j Hj). }
assert (VMF : forall j, (j < 4)%nat ->
  aview segs (w_H W) (ms_mem ms3) (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte GFV 4 j)).
{ intros j Hj.
  exact (MWW.mw_cval (o5_E regsB EXC) W (ms_mem ms3) o5_rg_mf2 33%nat TA_M 88 4
    (SExt false 8 (SOff 32 0)) GFV RMF eq_refl UC33
    ltac:(unfold o5_rg_mf2; cbn [YP09.r_chunks]; left; reflexivity)
    ltac:(exact (o5_zext8_den (o5_E regsB EXC) 32%nat GFV EC32 ltac:(lia)))
    ltac:(lia) ltac:(cbn [Z.of_N]; lia) j Hj). }
(* op_begin's world is the one the two stores leave *)
assert (EB1W : B1 = o5_w4 (lo_B op)).
{ destruct (o5_some2 _ _ _ _ _ EB1 (o5_begin_eq (lo_B op))) as (H & _). exact H. }
pose (rmid := fun a => if (TA_M + 88 <=? a) && (a <? TA_M + 92)
                       then aview segs (w_H W) memB a else aview segs (w_H W) (ms_mem ms3) a).
assert (RMIDin : forall a, TA_M + 88 <= a < TA_M + 92 -> rmid a = aview segs (w_H W) memB a).
{ intros a Ha. unfold rmid.
  replace ((TA_M + 88 <=? a) && (a <? TA_M + 92)) with true;
    [reflexivity | symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia]. }
assert (RMIDout : forall a, ~ (TA_M + 88 <= a < TA_M + 92) -> rmid a = aview segs (w_H W) (ms_mem ms3) a).
{ intros a Ha. unfold rmid.
  replace ((TA_M + 88 <=? a) && (a <? TA_M + 92)) with false; [reflexivity|].
  symmetry. destruct (Z.leb_spec (TA_M + 88) a); destruct (Z.ltb_spec a (TA_M + 92)); cbn [andb];
    first [reflexivity | exfalso; lia]. }
assert (TW3a : tw_at TMAP_A rmid (o5_w3 (lo_B op))).
{ unfold o5_w3, TW.set_OW_desk_off, TW.A_OW_desk_off.
  refine (tw_write TMAP_A _ _ _ TW.OFF_OW TA_OW TW.SZ_OW 232 4 (-1) TMAP_A_ok TWB TMAP_A_OW
    ltac:(lia) ltac:(unfold TW.SZ_OW; cbn [Z.of_nat]; lia) _ _).
  - intros j Hj. rewrite RMIDout by (rewrite ETAOW, ETAM; lia). exact (VOW j Hj).
  - intros x Hx Hnw. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    destruct (Z_le_dec (TA_M + 88) x) as [Hl|Hl]; destruct (Z_lt_dec x (TA_M + 92)) as [Hr'|Hr'].
    + apply RMIDin. lia.
    + rewrite RMIDout by lia. apply KR3; [change (2 ^ 64) with 18446744073709551616; lia
                                         | cbn [Z.of_nat] in Hnw; lia | lia].
    + rewrite RMIDout by lia. apply KR3; [change (2 ^ 64) with 18446744073709551616; lia
                                         | cbn [Z.of_nat] in Hnw; lia | lia].
    + rewrite RMIDout by lia. apply KR3; [change (2 ^ 64) with 18446744073709551616; lia
                                         | cbn [Z.of_nat] in Hnw; lia | lia]. }
assert (TW3 : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms3)) (o5_w4 (lo_B op))).
{ unfold o5_w4, TW.set_M_fail, TW.A_M_fail. rewrite (o5_gf_w3 (lo_B op) LBZ).
  refine (tw_write TMAP_A rmid _ _ TW.OFF_M TA_M TW.SZ_M 88 4 GFV TMAP_A_ok TW3a TMAP_A_M
    ltac:(lia) ltac:(unfold TW.SZ_M; cbn [Z.of_nat]; lia) _ _).
  - intros j Hj. exact (VMF j Hj).
  - intros x Hx Hnw. rewrite RMIDout by (cbn [Z.of_nat] in Hnw; lia). reflexivity. }
assert (TW3B : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms3)) B1) by (rewrite EB1W; exact TW3).
(* what the walk kept through run C *)
assert (KA3 : acall_kept_g segs B TG.G_HARNESS ly0 S0 W mem0 W (ms_mem ms3)
  (lc_sp1 cx - O5_X) (lc_sp1 cx) (o5_wr B1 B2)).
{ apply (o5_step ly0 S0 W mem0 md0 W memB (ms_mem ms3) (lc_sp1 cx - O5_X) (lc_sp1 cx) (o5_wr B1 B2)
    (fun a => (TA_OW + 232 <= a < TA_OW + 236) \/ (TA_M + 88 <= a < TA_M + 92))
    LAWS HGX HAR0 HCE).
  - exact KA2.
  - intros a Ha Hnw. apply KR3; [exact Ha | tauto | tauto].
  - exact GR3.
  - intros a [Hz | Hz]; right.
    + split; [apply o5_inG; right; left; unfold TW.SZ_OW; lia | left; unfold TW.SZ_OW; lia].
    + split; [apply o5_inG; left; unfold TW.SZ_M; lia | right; right; left; lia]. }
(* the registers at the call of m_wake *)
assert (HPRE3 : aregs_preserved regsB (ms_regs ms3)).
{ apply o5_pres_of_keep; [exact KPR3|].
  o5_reg HS (Z_to_bv 5 22) (YK11.getr regsB (Z_to_bv 5 22)) Q22c
    ltac:(exact (o5_den_reg regsB EXC 22%nat (Z_to_bv 5 22) _ eq_refl eq_refl)).
  exact Q22c. }
o5_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 1628)) QC1 ltac:(apply codeptr_val; exact HEI).
assert (QC2 : YK11.getr (ms_regs ms3) 2 = w64 (lc_sp1 cx))
  by exact (eq_trans (HPRE3 2 ltac:(hnf; lia)) RC2).
assert (QC3 : YK11.getr (ms_regs ms3) 3 = w64 (as_gp B))
  by exact (eq_trans (HPRE3 3 ltac:(hnf; lia)) RC3).
assert (QC4 : YK11.getr (ms_regs ms3) 4 = w64 (as_tp B))
  by exact (eq_trans (HPRE3 4 ltac:(hnf; lia)) RC4).
assert (USPC : spZ (ms_regs ms3) = lc_sp1 cx)
  by (unfold spZ; rewrite QC2; unfold w64; apply unsigned_lit_small; lia).
assert (HSP16 : spZ (ms_regs ms3) mod 16 = 0).
{ rewrite USPC. pose proof (Z.div_mod (lc_sp1 cx) 32 ltac:(lia)) as D1.
  rewrite Hsp1m, Z.add_0_r in D1. rewrite D1.
  replace (32 * (lc_sp1 cx / 32)) with ((2 * (lc_sp1 cx / 32)) * 16) by ring. apply Z.mod_mul. lia. }
assert (HEVB : st_nev (l_S cx) + e0 + MWAKE_EV <= EV_MAX).
{ unfold MWAKE_EV. unfold RECV_EV in HEV. unfold EV_LIB in Hev.
  change TC.OPS_MAX with 1024 in HOPS. lia. }
assert (EBRC : BASE + 1628 = 0x818c0) by (vm_compute; reflexivity).
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transport_sigma TS_m_wake)) mm rom) mdx) Q)
end.
eapply SRr_bind.
{ eapply (lp_mwake _ _ _ _ _ HP (l_fx cx)).
  - first [exact HJ3 | apply (ajournal_gx_materialize segs B LAWS transport_segs_low); exact HJ3].
  - rewrite QC1. apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - unfold raZ. rewrite QC1, EBRC. rewrite unsigned_lit_small by lia. lia.
  - exact QC3.
  - exact QC4.
  - exact HSP16.
  - rewrite USPC. unfold MWAKE_STK, MWAKE_FRAME, LLVMF_STK. unfold LF_FRAME in Hsp1b. lia.
  - rewrite USPC. unfold LF_FRAME in Hsp1b. lia.
  - exact TW3B.
  - exact EB2.
  - exact HEVB. }
cbv beta. intros WC cC _ HPOSTC.
unfold transport_mwake_post, transport_cg_post in HPOSTC. cbv beta in HPOSTC.
destruct HPOSTC as (ly4 & S4 & regs4 & mem4 & md4 & e4 & Ec4 & He4 & HJ4 & HP4 & Hfr4 & Hperm4 & HK4 & Hmo4 &
  (HA0w & HTW4)).
assert (Ee4 : e4 = 0) by (unfold MWAKE_EV in He4; lia). subst e4. rewrite Z.add_0_r in HJ4.
rewrite QC1 in Ec4. subst cC.
(* what the m_wake call kept, folded into the walk's own *)
assert (KA4 : acall_kept_g segs B TG.G_HARNESS ly0 S0 W mem0 WC mem4
  (lc_sp1 cx - O5_X) (lc_sp1 cx) (o5_wr B1 B2)).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS ly0 S0 W mem0 W (ms_mem ms3) WC mem4
    (lc_sp1 cx - O5_X) (lc_sp1 cx) (spZ (ms_regs ms3) - MWAKE_STK) (spZ (ms_regs ms3))
    (o5_wr B1 B2) (mwake_wr B1) HCE HSP1hi KA3 HK4).
  - rewrite USPC. lia.
  - rewrite USPC. lia.
  - intros a Ha. right; right; right; left. exact Ha. }
(* ---- run D, +0x65c .. +0x670: g_now, s6 = want, a0 = &g_s, the call of diginet_session_wake ---- *)
clear HEI SHOK.
assert (QD9 : YK11.getr regs4 (Z_to_bv 5 9) = w64 (lc_sp1 cx))
  by exact (eq_trans (HP4 9 ltac:(hnf; lia)) (eq_trans (HPRE3 9 ltac:(hnf; lia)) RC9)).
assert (QD2 : YK11.getr regs4 (Z_to_bv 5 2) = w64 (lc_sp1 cx))
  by exact (eq_trans (HP4 2 ltac:(hnf; lia)) QC2).
assert (QD3 : YK11.getr regs4 (Z_to_bv 5 3) = w64 (as_gp B))
  by exact (eq_trans (HP4 3 ltac:(hnf; lia)) QC3).
assert (QD4 : YK11.getr regs4 (Z_to_bv 5 4) = w64 (as_tp B))
  by exact (eq_trans (HP4 4 ltac:(hnf; lia)) QC4).
pose (NW := TW.g_now B2).
assert (RNW : 0 <= NW < 2 ^ 64).
{ unfold NW, TW.g_now. pose proof (TWL.u_at_range B2 TW.OFF_g_now 8) as Hr.
  change (8 * Z.of_nat 8) with 64 in Hr. lia. }
pose (EXD := [w64 NW] : list word).
assert (HEI : img_env VAL A_LIM (o5_E regs4 EXD)) by apply o5_env.
assert (SHOK : sh_ok segs o5_Bx (@nil shent) (o5_E regs4 EXD) (mrestrict (w_H WC) mem4)) by apply o5_shok.
assert (ED32 : ew (o5_E regs4 EXD) 32%nat = w64 NW) by exact (o5_ewx regs4 EXD 0%nat ltac:(lia)).
assert (UD9 : bv_unsigned (ew (o5_E regs4 EXD) 9%nat) = lc_sp1 cx).
{ rewrite (o5_ewr regs4 EXD 9%nat (Z_to_bv 5 9) eq_refl), QD9. apply o5_lit64. lia. }
assert (HSP176 : rdword (aview segs (w_H WC) mem4) (lc_sp1 cx + 176) = Some (transport_hi 9)).
{ pose proof KA4 as (KK1 & _).
  rewrite (rdword_ext (aview segs (w_H W) mem0) (aview segs (w_H WC) mem4) (lc_sp1 cx + 176))
    by (intros j Hj; apply KK1; [change (2 ^ 64) with 18446744073709551616; lia | lia]).
  unfold lc_spills in HSPL. rewrite Forall_forall in HSPL.
  exact (HSPL (176, transport_hi 9)
    ltac:(unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm; cbn [app In]; tauto)). }
assert (HNOWB : val_mem segs (mrestrict (w_H WC) mem4) (0 + TA_g_now) 8 NW).
{ pose proof (tw_read_val segs _ TMAP_A B2 TW.OFF_g_now TA_g_now TW.SZ_g_now 0 8 TMAP_A_ok HTW4
    TMAP_A_g_now ltac:(lia) ltac:(unfold TW.SZ_g_now; lia)) as Hv.
  rewrite !Z.add_0_r in Hv. rewrite Z.add_0_l. exact Hv. }
assert (HRGD : Forall (region_ok segs (o5_E regs4 EXD) (mrestrict (w_H WC) mem4)) [o5_rg_hi; o5_rg_nw]).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - unfold o5_rg_hi, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite UD9. split; [lia|]. split; [change (2 ^ 64) with 18446744073709551616; lia|].
    split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs (o5_E regs4 EXD) _ (lc_sp1 cx) 176 8 (SLit (transport_hi 9)) (transport_hi 9));
      [reflexivity | change (8 * Z.of_N 8) with 64; rewrite ETHI9; lia | cbn [Z.of_N]; lia |].
    exact (val_mem_of_rdword segs (w_H WC) mem4 _ _ HSP176).
  - unfold o5_rg_nw, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [rewrite ETAGN; lia|]. split; [rewrite ETAGN; change (2 ^ 64) with 18446744073709551616; lia|].
    split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs (o5_E regs4 EXD) _ 0 TA_g_now 8 (SOff 32 0) NW);
      [ cbn [sv_denot]; rewrite ED32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | change (8 * Z.of_N 8) with 64; exact RNW | cbn [Z.of_N]; lia | exact HNOWB]. }
assert (HPDD : pairwise_disjoint (o5_E regs4 EXD) [o5_rg_hi; o5_rg_nw]).
{ unfold o5_rg_hi, o5_rg_nw. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UD9, ETAGN. lia. }
clear HS.
pose proof (o5_entry (l_fx cx) WC regs4 EXD mem4 1628 [o5_rg_hi; o5_rg_nw] (mkFacts [] [] [])
  ltac:(vm_compute; reflexivity) HRGD HPDD (o5_facts_nil regs4 EXD)) as HS.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs4 (Z_to_bv 64 (BASE + 1628)) mem4
    (YK11.seg_rom segs)) md4) Q) end.
paj_run_tok RUN HS HJ4 SHOK o5_B0.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat first
    [ apply awr_ok_x_nil
    | apply awr_ok_x_cons;
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia | ] ]. }
set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
rename ms into ms5. rename HJ4 into HJ5.
assert (KR5 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H WC) (ms_mem ms5) a = aview segs (w_H WC) mem4 a).
{ intros a Ha. apply (YC4b.kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin. clear - Hin Hx.
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H
  | H : False |- _ => destruct H
  | H : (_, _, _) = (_, _, _) |- _ => inversion H; subst; clear H
  end;
  cbn [base_val] in Hx; exfalso; lia. }
assert (GR5 : forall a, apresent (w_H WC) mem4 a -> apresent (w_H WC) (ms_mem ms5) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
assert (KPR5 : o5_keep regs4 (ms_regs ms5)).
{ apply (o5_keep_run (w_H WC) (o5_E regs4 EXD) _ _ regs4 EXD HS (o5_agree regs4 EXD)).
  vm_compute. reflexivity. }
clear HF HFr HG.
o5_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 1652)) QE1 ltac:(apply codeptr_val; exact HEI).
o5_reg HS (10%bv : bv 5) (w64 WAKE_S) QE10 ltac:(vm_compute; reflexivity).
o5_reg HS (11%bv : bv 5) (w64 NW) QE11
  ltac:(cbn [sv_denot]; rewrite ED32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (QE2 : YK11.getr (ms_regs ms5) 2 = w64 (lc_sp1 cx))
  by exact (eq_trans (KPR5 (Z_to_bv 5 2) ltac:(o5_inK)) QD2).
assert (QE3 : YK11.getr (ms_regs ms5) 3 = w64 (as_gp B))
  by exact (eq_trans (KPR5 (Z_to_bv 5 3) ltac:(o5_inK)) QD3).
assert (QE4 : YK11.getr (ms_regs ms5) 4 = w64 (as_tp B))
  by exact (eq_trans (KPR5 (Z_to_bv 5 4) ltac:(o5_inK)) QD4).
assert (USPD : spZ (ms_regs ms5) = lc_sp1 cx)
  by (unfold spZ; rewrite QE2; unfold w64; apply unsigned_lit_small; lia).
o5_reg HS (22%bv : bv 5) (w64 want) QE22
  ltac:(exact (o5_den_reg regs4 EXD 10%nat (Z_to_bv 5 10) _ eq_refl HA0w)).
(* the facts the call of diginet_session_wake asks *)
destruct (o5_inv_at_B2 K6 (lo_ops op) B1 B2 want HA1 EB2) as (HINV1 & HINV4 & HGFN2).
assert (TWD : tw_at TMAP_A (aview segs (w_H WC) (ms_mem ms5)) B2).
{ apply (tw_kept TMAP_A (aview segs (w_H WC) mem4)); [exact HTW4|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  apply KR5. change (2 ^ 64) with 18446744073709551616. lia. }
assert (ROMd : trans_rom_view_rd WC (ms_mem ms5)).
{ intros a Ha. rewrite KR5 by (pose proof (trans_ro_rd_bounds a Ha); lia).
  rewrite <- (K1 HP cx ly0 S0 W regs0 mem0 md0 e0 HB HCORE a Ha).
  pose proof KA4 as (_ & _ & KK3 & _).
  destruct (trans_ro_rd_scoped B (lp_ro_unowned _ _ _ _ _ HP) (lp_rom_no_errno _ _ _ _ _ HP) a Ha) as [Ho He].
  apply (KK3 a (trans_ro_img a Ha)); [| exact Ho | exact He].
  intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
  unfold TG.G_HARNESS_LO in Gh. lia. }
assert (HCNTW : count_cid WAKE_CID (frames S4) + 2 < fs_frames WAKE_CID).
{ rewrite Hfr4, Hfrs0. change WAKE_CID with LF_CID. cbn [count_cid]. change (LF_CID =? LF_CID) with true.
  cbn [Z.add]. vm_compute. reflexivity. }
assert (HEVW : st_nev (l_S cx) + e0 + WAKE_EV <= EV_MAX).
{ assert (EW0 : WAKE_EV = 0) by reflexivity. rewrite EW0.
  unfold RECV_EV in HEV. unfold EV_LIB in Hev. change TC.OPS_MAX with 1024 in HOPS. lia. }
assert (HSP16D : spZ (ms_regs ms5) mod 16 = 0).
{ rewrite USPD. pose proof (Z.div_mod (lc_sp1 cx) 32 ltac:(lia)) as D1.
  rewrite Hsp1m, Z.add_0_r in D1. rewrite D1.
  replace (32 * (lc_sp1 cx / 32)) with ((2 * (lc_sp1 cx / 32)) * 16) by ring. apply Z.mod_mul. lia. }
assert (EBRD : BASE + 1652 = 0x818d8) by (vm_compute; reflexivity).
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg
    (Z_to_bv 64 (transport_sigma TS_diginet_session_wake)) mm rom) mdx) Q)
end.
eapply SRr_bind.
{ eapply (lp_wake _ _ _ _ _ HP (l_fx cx)).
  - first [exact HJ5 | apply (ajournal_gx_materialize segs B LAWS transport_segs_low); exact HJ5].
  - rewrite QE1. apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - unfold raZ. rewrite QE1, EBRD. rewrite unsigned_lit_small by lia. lia.
  - exact QE3.
  - exact QE4.
  - exact QE10.
  - exact QE11.
  - exact HSP16D.
  - rewrite USPD. pose proof o5_X_fits as HX. unfold LLVMF_STK. unfold LF_FRAME in Hsp1b. lia.
  - rewrite USPD. unfold LF_FRAME in Hsp1b. lia.
  - exact RNW.
  - exact TWD.
  - exact HGFN2.
  - exact EB3.
  - exact I.
  - intros fr Hfr. discriminate Hfr.
  - exact ROMd.
  - intros x _ fr Hfr. discriminate Hfr.
  - exact HINV1.
  - exact HINV4.
  - exact HCNTW.
  - exact HEVW. }
cbv beta. intros WD cD _ HPOSTD.
unfold transport_wake_post, transport_cg_post in HPOSTD. cbv beta in HPOSTD.
destruct HPOSTD as (ly6 & S6 & regs6 & mem6 & md6 & e6 & Ec6 & He6 & HJ6 & HP6 & Hfr6 & Hperm6 & HK6 & Hmo6 &
  (HA0r & HTW6 & HGF6)).
assert (Ee6 : e6 = 0)
  by (assert (EW0 : WAKE_EV = 0) by reflexivity; rewrite EW0 in He6; lia).
subst e6. rewrite Z.add_0_r in HJ6.
rewrite QE1 in Ec6. subst cD.
(* ---- run E, +0x674 .. +0x67c: a1 = want, s6 = 7, the call of check_state_wake_code ---- *)
clear HEI SHOK HS.
assert (QF22 : YK11.getr regs6 (Z_to_bv 5 22) = w64 want)
  by exact (eq_trans (HP6 22 ltac:(hnf; lia)) QE22).
assert (QF2 : YK11.getr regs6 (Z_to_bv 5 2) = w64 (lc_sp1 cx))
  by exact (eq_trans (HP6 2 ltac:(hnf; lia)) QE2).
assert (QF3 : YK11.getr regs6 (Z_to_bv 5 3) = w64 (as_gp B))
  by exact (eq_trans (HP6 3 ltac:(hnf; lia)) QE3).
assert (QF4 : YK11.getr regs6 (Z_to_bv 5 4) = w64 (as_tp B))
  by exact (eq_trans (HP6 4 ltac:(hnf; lia)) QE4).
assert (HEI : img_env VAL A_LIM (o5_E regs6 (@nil word))) by apply o5_env.
assert (SHOK : sh_ok segs o5_Bx (@nil shent) (o5_E regs6 (@nil word)) (mrestrict (w_H WD) mem6)) by apply o5_shok.
pose proof (o5_entry0 (l_fx cx) WD regs6 (@nil word) mem6 1652) as HS.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs6 (Z_to_bv 64 (BASE + 1652)) mem6
    (YK11.seg_rom segs)) md6) Q) end.
paj_run_tok RUN HS HJ6 SHOK o5_B0.
{ o5_awr0. }
set (md7 := with_vm_backing (m_vm_lazy md6) mat md6) in *. clearbody md7. clear mat.
rename ms into ms7. rename HJ6 into HJ7.
assert (KR7 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H WD) (ms_mem ms7) a = aview segs (w_H WD) mem6 a).
{ intros a Ha. apply (YC4b.kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin. destruct Hin. }
assert (GR7 : forall a, apresent (w_H WD) mem6 a -> apresent (w_H WD) (ms_mem ms7) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
assert (KPR7 : o5_keep regs6 (ms_regs ms7)).
{ apply (o5_keep_run (w_H WD) (o5_E regs6 (@nil word)) _ _ regs6 (@nil word) HS
    (o5_agree regs6 (@nil word))). vm_compute. reflexivity. }
clear HF HFr HG.
o5_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 1664)) QG1 ltac:(apply codeptr_val; exact HEI).
o5_reg HS (10%bv : bv 5) (w64 r) QG10
  ltac:(exact (o5_den_reg regs6 (@nil word) 10%nat (Z_to_bv 5 10) _ eq_refl HA0r)).
o5_reg HS (11%bv : bv 5) (w64 want) QG11
  ltac:(exact (o5_den_reg regs6 (@nil word) 22%nat (Z_to_bv 5 22) _ eq_refl QF22)).
o5_reg HS (22%bv : bv 5) (w64 7) QG22 ltac:(reflexivity).
assert (QG2 : YK11.getr (ms_regs ms7) 2 = w64 (lc_sp1 cx))
  by exact (eq_trans (KPR7 (Z_to_bv 5 2) ltac:(o5_inK)) QF2).
assert (QG3 : YK11.getr (ms_regs ms7) 3 = w64 (as_gp B))
  by exact (eq_trans (KPR7 (Z_to_bv 5 3) ltac:(o5_inK)) QF3).
assert (QG4 : YK11.getr (ms_regs ms7) 4 = w64 (as_tp B))
  by exact (eq_trans (KPR7 (Z_to_bv 5 4) ltac:(o5_inK)) QF4).
assert (USPE : spZ (ms_regs ms7) = lc_sp1 cx)
  by (unfold spZ; rewrite QG2; unfold w64; apply unsigned_lit_small; lia).
assert (USPEb : bv_unsigned (YK11.getr (ms_regs ms7) (Z_to_bv 5 2)) = lc_sp1 cx) by exact USPE.
assert (HWRNG : - 2 ^ 31 <= want < 2 ^ 31) by exact (o5_want_rng B1 B2 want EB2).
assert (HRRNG : - 2 ^ 31 <= r < 2 ^ 31) by (rewrite Erw; exact HWRNG).
assert (TWE : tw_at TMAP_A (O5CW.csw_view (ms_mem ms7)) B3).
{ apply (o5_tw_csw WD). apply (tw_kept TMAP_A (aview segs (w_H WD) mem6)); [exact HTW6|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  apply KR7. change (2 ^ 64) with 18446744073709551616. lia. }
assert (ECSW : TC.check_state_wake_code_m B3 r want = Some (B3, tt)).
{ unfold TC.check_state_wake_code_m. rewrite Erw, Z.eqb_refl. reflexivity. }
assert (EBRE : BASE + 1664 = 0x818e4) by (vm_compute; reflexivity).
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg
    (Z_to_bv 64 O5WC.CHECK_STATE_WAKE_CODE) mm rom) mdx) Q)
end.
eapply SRr_bind.
{ eapply (gx_call_leaf segs B TG.G_HARNESS LLVMF_STK (lc_sp0 cx) _ (l_ly cx) (l_S cx) (l_W cx) (l_mem cx)
    (l_md cx) _ ly6 S6 WD (ms_mem ms7) md7 e0 _ (YK11.getr (ms_regs ms7) 1) _ HJ7).
  intros memS HJS.
  eapply (@O5LB.decode_leafb_journal (l_fx cx) rc tfib_sink_head B LAWS WD (ms_regs ms7) (ms_mem ms7)
    LLVMF_STK (lc_sp0 cx) _ (l_ly cx) (l_S cx) (l_W cx) memS (l_md cx) _ ly6 S6 md7 e0
    (lc_sp1 cx - lc_sp0 cx) O5WC.CHECK_STATE_WAKE_CODE None [] (fun _ => B3 = B3) HJS).
  - rewrite USPE. lia.
  - exact HO16.
  - unfold LF_FRAME in Hsp1b; lia.
  - unfold ESTACK, LLVMF_STK; unfold LF_FRAME in Hsp1b; lia.
  - rewrite QG1. apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - exact QG3.
  - exact QG4.
  - intros a Ha. unfold O5CK.in_wr in Ha. inversion Ha.
  - intros HPRE.
    pose proof (lp_cswc _ _ _ _ _ HP (l_fx cx)) as LF.
    unfold transport_leaf_at, LCSWC.transport_check_state_wake_code_cg in LF.
    specialize (LF ly6 S6 WD (ms_regs ms7) (ms_mem ms7) md7 (lc_sp1 cx - 4096) B3 B3 r want HPRE).
    cbv zeta in LF.
    apply LF; clear LF.
    + exact QG10.
    + exact QG11.
    + exact HRRNG.
    + exact HWRNG.
    + exact TWE.
    + exact ECSW.
    + rewrite USPEb.
      apply (O5LB.decode_leafb_stk_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJS);
        [unfold LLVMF_STK; unfold LF_FRAME in Hsp1b; lia | unfold LF_FRAME in Hsp1b; lia].
    + rewrite USPEb. unfold O5WC.CHECK_STATE_WAKE_CODE_FRAME. lia.
    + unfold O5KA.off_stk. rewrite USPEb.
      unfold O5WC.CHECK_STATE_WAKE_CODE_FRAME, TG.G_HARNESS_LO, TG.G_HARNESS_HI.
      first [lia | left; lia | right; lia].
    + rewrite USPEb.
      apply (O5LB.decode_leafb_rng_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJS);
        unfold O5WC.CHECK_STATE_WAKE_CODE_FRAME, LLVMF_STK; unfold LF_FRAME in Hsp1b; lia. }
cbv beta. intros WE cE _ (EWE & regs8 & mem8 & md8 & Ec8 & HJ8 & HP8 & _ & HEFF8 & HGR8 & _).
subst WE. rewrite QG1 in Ec8. subst cE.
(* ---- run F, +0x680: the `j` to the cut SET56 ---- *)
clear HEI SHOK HS.
assert (Q22r8 : YK11.getr regs8 (Z_to_bv 5 22) = w64 7)
  by exact (eq_trans (HP8 22 ltac:(hnf; lia)) QG22).
assert (HEI : img_env VAL A_LIM (o5_E regs8 (@nil word))) by apply o5_env.
assert (SHOK : sh_ok segs o5_Bx (@nil shent) (o5_E regs8 (@nil word)) (mrestrict (w_H WD) mem8)) by apply o5_shok.
pose proof (o5_entry0 (l_fx cx) WD regs8 (@nil word) mem8 1664) as HS.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs8 (Z_to_bv 64 (BASE + 1664)) mem8
    (YK11.seg_rom segs)) md8) Q) end.
paj_run_to_tok RUNTO HS HJ8 SHOK o5_B0 LO_SET56.
{ o5_awr0. }
set (md9 := with_vm_backing (m_vm_lazy md8) mat md8) in *. clearbody md9. clear mat.
rename ms into ms9. rename HJ8 into HJ9.
assert (KR9 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H WD) (ms_mem ms9) a = aview segs (w_H WD) mem8 a).
{ intros a Ha. apply (YC4b.kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin. destruct Hin. }
assert (GR9 : forall a, apresent (w_H WD) mem8 a -> apresent (w_H WD) (ms_mem ms9) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
assert (KPR9 : o5_keep regs8 (ms_regs ms9)).
{ apply (o5_keep_run (w_H WD) (o5_E regs8 (@nil word)) _ _ regs8 (@nil word) HS
    (o5_agree regs8 (@nil word))). vm_compute. reflexivity. }
o5_reg HS (22%bv : bv 5) (w64 7) QI22
  ltac:(exact (o5_den_reg regs8 (@nil word) 22%nat (Z_to_bv 5 22) _ eq_refl Q22r8)).
clear HF HFr HG.
(* the registers the cut names, from the start registers *)
assert (KPALL : o5_keep regs0 (ms_regs ms9)).
{ apply (o5_keep_trans regs0 regsB); [exact KPB|].
  apply (o5_keep_trans regsB (ms_regs ms3)); [exact KPR3|].
  apply (o5_keep_trans (ms_regs ms3) regs4); [apply o5_keep_of_pres; exact HP4|].
  apply (o5_keep_trans regs4 (ms_regs ms5)); [exact KPR5|].
  apply (o5_keep_trans (ms_regs ms5) regs6); [apply o5_keep_of_pres; exact HP6|].
  apply (o5_keep_trans regs6 (ms_regs ms7)); [exact KPR7|].
  apply (o5_keep_trans (ms_regs ms7) regs8); [apply o5_keep_of_pres; exact HP8|].
  exact KPR9. }
assert (HPRES : aregs_preserved regs0 (ms_regs ms9)).
{ apply o5_pres_of_keep; [exact KPALL | exact (eq_trans QI22 (eq_sym R22))]. }
(* what the whole stretch kept *)
pose proof HJ5 as (_ & _ & (memS4 & HJi4 & _) & _). rewrite !Z.add_0_r in HJi4.
pose proof HJi4 as (HAR4 & Hly4le & _). pose proof Hly4le as (_ & _ & _ & _ & _ & ELF4 & _).
clear HJi4 memS4.
assert (KAW : acall_kept_g segs B TG.G_HARNESS ly0 S0 W mem0 WD mem6
  (lc_sp1 cx - O5_X) (lc_sp1 cx) (o5_wr B1 B2)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS ly0 S0 ly4 S4 W mem0 WC (ms_mem ms5) WD mem6
    (lc_sp1 cx - O5_X) (lc_sp1 cx) (spZ (ms_regs ms5) - WAKE_STK) (spZ (ms_regs ms5))
    (o5_wr B1 B2) (wake_wr B2) (fun _ : Z => False) HCE HSP1hi).
  - intros cid pos. unfold frame_addr. rewrite ELF4, HlyF0. reflexivity.
  - intros f Hf. rewrite Hfr4. exact Hf.
  - intros bm Hbm. exact (Permutation_in _ (Permutation_sym Hperm4) Hbm).
  - intros b m i _ _ [].
  - intros cid pos a _ _ [].
  - apply (o5_step ly0 S0 W mem0 md0 WC mem4 (ms_mem ms5) (lc_sp1 cx - O5_X) (lc_sp1 cx) (o5_wr B1 B2)
      (fun _ : Z => False) LAWS HGX HAR0 HCE KA4).
    + intros a Ha _. exact (KR5 a Ha).
    + exact GR5.
    + intros a [].
  - exact HK6.
  - rewrite USPD. pose proof o5_X_fits as HX. lia.
  - rewrite USPD. lia.
  - intros a Ha. left. right; right; right; right. exact Ha. }
assert (KAF : acall_kept_g segs B TG.G_HARNESS ly0 S0 W mem0 WD (ms_mem ms9)
  (lc_sp1 cx - O5_X) (lc_sp1 cx) (o5_wr B1 B2)).
{ apply (o5_step ly0 S0 W mem0 md0 WD mem8 (ms_mem ms9) (lc_sp1 cx - O5_X) (lc_sp1 cx) (o5_wr B1 B2)
    (fun _ : Z => False) LAWS HGX HAR0 HCE).
  - apply (o5_step ly0 S0 W mem0 md0 WD (ms_mem ms7) mem8 (lc_sp1 cx - O5_X) (lc_sp1 cx) (o5_wr B1 B2)
      (fun a => lc_sp1 cx - 4096 <= a < lc_sp1 cx) LAWS HGX HAR0 HCE).
    + apply (o5_step ly0 S0 W mem0 md0 WD mem6 (ms_mem ms7) (lc_sp1 cx - O5_X) (lc_sp1 cx) (o5_wr B1 B2)
        (fun _ : Z => False) LAWS HGX HAR0 HCE KAW).
      * intros a Ha _. exact (KR7 a Ha).
      * exact GR7.
      * intros a [].
    + intros a Ha Hnw. apply HEFF8; [exact Ha | rewrite USPE; unfold ESTACK; lia |].
      intros Hx. unfold O5CK.in_wr in Hx. inversion Hx.
    + exact HGR8.
    + intros a Ha. left. unfold ESTACK in HXb. lia.
  - intros a Ha _. exact (KR9 a Ha).
  - exact GR9.
  - intros a []. }
pose proof KAF as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6).
assert (HWRG : forall a, o5_wr B1 B2 a -> in_img segs a /\ TG.G_HARNESS_LO <= a < TG.G_HARNESS_HI).
{ intros a Ha. pose proof (o5_wr_inG B1 B2 a Ha) as Hg.
  split; [exact (trans_g_img a Hg) | exact (inG_G_HARNESS_hull a Hg)]. }
pose proof asan_consts as ((CVlo & CVhi) & _).
assert (Hfrs6 : frames S6 = frames S0) by (rewrite Hfr6, Hfr4; reflexivity).
assert (Hperm6c : Permutation (ablocks B ly6 S6) (ablocks B ly0 S0))
  by exact (Permutation_trans Hperm6 Hperm4).
(* the core, the spill slots and the frame's shadow at the cut *)
assert (KCORE : @lc_core rc B cx ly6 S6 WD (ms_regs ms9) (ms_mem ms9) md9 e0).
{ apply (@lc_core_kept rc B MT XL RLO RHI cx ly0 S0 W regs0 mem0 md0 e0 O5_X
    ly6 S6 WD (ms_regs ms9) (ms_mem ms9) md9 e0 LAWS HB HCORE).
  - exact HJ9.
  - rewrite Hfrs6. reflexivity.
  - exact Hperm6c.
  - exact HPRES.
  - pose proof o5_X_fits as HX. unfold LLVMF_STK in *. lia.
  - intros a Ha Hw. exact (KF1 a Ha Hw).
  - intros b m i Hb Hi.
    assert (HBND : 0 <= b + i < 2 ^ 64).
    { destruct (al_blocks _ _ LAWS ly0 S0 W mem0 md0 b m HAR0 Hb) as (_ & _ & _ & Happ & _ & _).
      pose proof (app_addr_below_ceil (b + i) (in_app_addr _ _ _ Happ (o5_rng_idx b i (req_size m) Hi))) as HAC.
      pose proof (@ASAN_CEIL_range rc) as (CRa & _).
      change (2 ^ 64) with 18446744073709551616. lia. }
    assert (HNW : ~ o5_wr B1 B2 (b + i)).
    { intros Hx. exact (blk_img segs B LAWS ly0 S0 W mem0 md0 b m (b + i) HAR0 Hb
        (o5_rng_idx b i (req_size m) Hi) (proj1 (HWRG (b + i) Hx))). }
    exact (KF2 b m i Hb Hi HNW).
  - intros a Ha.
    assert (HNW : ~ o5_wr B1 B2 a).
    { intros Hx. destruct Ha as [Ha | Ha].
      - exact (frm_img segs B LAWS ly0 S0 W mem0 md0 LF_CID (l_fpos cx) a HAR0 HFin
          ltac:(rewrite HFaddr; change (fs_frame_bytes LF_CID) with LF_FBYTES; unfold LF_FBYTES in *; lia)
          (proj1 (HWRG a Hx))).
      - exact (o5_sh_hi (lc_F cx) a ltac:(lia) (proj1 Ha) (proj2 (proj2 (HWRG a Hx)))). }
    exact (KF4 LF_CID (l_fpos cx) a HFin
      ltac:(destruct Ha as [Ha|Ha];
            [ left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite HFaddr;
              change (fs_frame_bytes LF_CID) with LF_FBYTES; lia
            | right; unfold in_zr; cbn [fst snd]; rewrite HFaddr;
              change (fs_frame_bytes LF_CID / 8) with 32; unfold lc_SH, shadow_addr in *; lia ]) HNW). }
assert (KSPL : lc_spills cx (lf_spill_loop (lc_F cx)) (aview segs (w_H WD) (ms_mem ms9))).
{ apply (lc_spills_kept cx (lf_spill_loop (lc_F cx)) (aview segs (w_H W) mem0)).
  - intros o Ho. pose proof (lf_spill_vals (lc_F cx) ltac:(lia)
      ltac:(unfold LF_FBYTES in *; change (2 ^ 63) with 9223372036854775808; lia)) as HV.
    rewrite Forall_forall in HV. pose proof (HV o Ho) as (_ & _ & Hlo & Hhi). split; lia.
  - intros a Ha. apply KF1; [change (2 ^ 64) with 18446744073709551616; lia | lia].
  - exact HSPL. }
assert (KFSH : lc_fsh cx (aview segs (w_H WD) (ms_mem ms9)) false false).
{ apply (lc_fsh_kept cx (aview segs (w_H W) mem0)).
  - intros a Ha.
    assert (HNW : ~ o5_wr B1 B2 a).
    { intros Hx. exact (o5_sh_hi (lc_F cx) a ltac:(lia) (proj1 Ha) (proj2 (proj2 (HWRG a Hx)))). }
    exact (KF4 LF_CID (l_fpos cx) a HFin
      ltac:(right; unfold in_zr; cbn [fst snd]; rewrite HFaddr;
            change (fs_frame_bytes LF_CID / 8) with 32; unfold lc_SH, shadow_addr in *; lia) HNW).
  - exact HFSH. }
(* the meter across the two calls *)
assert (Hmo46 : mo_le MT S0 S6 0).
{ replace 0 with (0 + 0) by lia. exact (mo_le_trans MT MTL _ _ _ _ _ Hmo4 Hmo6). }
(* the world at the cut *)
assert (TWF : tw_at TMAP_A (aview segs (w_H WD) (ms_mem ms9)) B3).
{ apply (tw_kept TMAP_A (aview segs (w_H WD) mem6)); [exact HTW6|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  transitivity (aview segs (w_H WD) mem8 x).
  - apply KR9. change (2 ^ 64) with 18446744073709551616. lia.
  - transitivity (aview segs (w_H WD) (ms_mem ms7) x).
    + apply HEFF8; [change (2 ^ 64) with 18446744073709551616; lia
                   | rewrite USPE; unfold ESTACK; lia
                   | intros Hx2; unfold O5CK.in_wr in Hx2; inversion Hx2].
    + apply KR7. change (2 ^ 64) with 18446744073709551616. lia. }
(* the registers the cut names *)
assert (KR18 : YK11.getr (ms_regs ms9) 18 = w64 (lc_SH cx))
  by exact (eq_trans (KPALL (Z_to_bv 5 18) ltac:(o5_inK)) R18).
assert (KR26 : YK11.getr (ms_regs ms9) 26 = w64 SHADOW_OFF)
  by exact (eq_trans (KPALL (Z_to_bv 5 26) ltac:(o5_inK)) R26).
assert (KR20 : YK11.getr (ms_regs ms9) 20 = w64 LF_S4)
  by exact (eq_trans (KPALL (Z_to_bv 5 20) ltac:(o5_inK)) R20).
assert (KR21 : YK11.getr (ms_regs ms9) 21 = w64 (lo_ops op))
  by exact (eq_trans (KPALL (Z_to_bv 5 21) ltac:(o5_inK)) R21).
assert (KCUR : lc_cur cx (ms_regs ms9) 24 23 (lc_oc (l_pl cx) (lo_c op))).
{ destruct Hcur8 as (Hc1 & Hc2). split.
  - exact (eq_trans (KPALL (Z_to_bv 5 24) ltac:(o5_inK)) Hc1).
  - exact (eq_trans (KPALL (Z_to_bv 5 23) ltac:(o5_inK)) Hc2). }
(* the cut SET56 *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (BASE + LO_SET56)) mm rom) mdx) Q)
end.
apply SRr_ret.
exists ly6, S6, (ms_regs ms9), (ms_mem ms9), md9, e0, B3.
split.
{ assert (EPCZ : BASE + LO_SET56 = transport_text + LO_SET56) by (vm_compute; reflexivity).
  unfold lc_cfg, w64. rewrite EPCZ. reflexivity. }
split; [left; exact (eq_sym Hopc)|].
split.
{ split; [exact KCORE|]. split; [exact (conj KR18 KR26)|]. split; [exact KSPL|]. split; [exact KFSH|].
  split; [exact HOPOK|]. split; [exact HEV|]. split; [|exact KR21].
  destruct HMET as (HMle & HMok). split.
  - replace (Z.of_nat (lo_k op) * lf_rcost MT) with (Z.of_nat (lo_k op) * lf_rcost MT + 0) by lia.
    exact (mo_le_trans MT MTL _ _ _ _ _ HMle Hmo46).
  - apply (mo_ok_step MT MTL S0 S6 0 ((TC.OPS_MAX - Z.of_nat (lo_k op)) * lf_rcost MT));
      [rewrite Z.add_0_l; exact HMok | exact Hmo46]. }
split; [unfold lc_tw; exact TWF|].
split; [exact ES|].
split; [exact EOP|].
split; [exact KCUR|].
split; [exact KR20 | exact QI22].
Qed.
End seg5.
