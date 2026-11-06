(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AFip.v (segA: the run of a
   wrapper over its own instruction table, the application of a runtime-entry contract at a call site and the
   rebuilding of the symbolic state after the call), A/AFis.v (at_ST's frame and window conjuncts,
   kept_of_frame, chunk_val_at) and A/AF0x.v (st_ok_pin_reg, the val_mem / apresent / fpchain helpers) to
   libreac/fuzz_decode's calloc wrapper in image A (fuzz_decode.asan); module paths changed, and every address,
   cell and offset below is decode's own. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/DecodeCallocWrap.v, with its module paths and module names changed; 3365 of its 3449 lines of code are new or changed and 788 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/LLVMFuzzerTestOneInput_seg_cfg.v, with its module paths and module names changed; 1296 of its 1454 lines of code are new or changed and 3291 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op5: Lemma lc_op5_ok : lc_op5_stmt B MT XL RLO RHI, the segment OP5 of the image-B walk
   of fuzz_transport.asan-ubsan's LLVMFuzzerTestOneInput (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v): from the cut ARM5
   (lc_st_arm cx op 5, +0x7f4) to the cut SET56 (lc_st_set56, +0x900), the offsets +0x7f4 .. +0x860 of the listing
   lib/B/Prog/DgnTransportBList.v (slot k at 0x812a0 + 4 k).

   What the code does (TCb.v op_begin_m, m_wake_m, TSess.v diginet_session_wake_m, TCb.v check_state_wake_code_m).
     +0x7f4 .. +0x808  s6 = OW (auipc / addi, the listing's object 12), a0 = s6, a1 = 0, a2 = 304,
                       `jal __asan_memset` (return +0x80c);
     +0x80c .. +0x81c  a0 = GOT (object 13), a2 = 224, a1 = 0, `jal __asan_memset` (return +0x820);
     +0x820 .. +0x838  a0 = the spill slot 184(s1) (g_fail_next's page, transportb_hi 10), the byte g_fail_next at
                       a0 + 0x678 (`lbu`), OW.desk_off := -1 (`sw` at s6 + 0xe8), a1 = the spill slot 168(s1) (M,
                       object 8), M.fail := the byte (`sw` at a1 + 0x58): op_begin's world (lc5_B1); `jal m_wake`
                       (return +0x83c);
     +0x83c .. +0x850  a1 = the spill slot 152(s1) (g_now's page, transportb_hi 9), a1 = g_now at a1 + 0x68c (`ld`),
                       s6 = a0 (m_wake's code), a0 = g_s (object 9), `jal diginet_session_wake` (return +0x854);
     +0x854 .. +0x85c  a1 = s6, s6 = 1, `jal check_state_wake_code` (a leaf; return +0x860);
     +0x860            `j +0x900`, the cut SET56.
   Report and trap edges: none. The region has no shadow check and no branch: its loads (three spill slots, the byte
   g_fail_next, g_now) and its two stores (OW.desk_off, M.fail) are not instrumented, so no instruction of it reaches
   an __asan_report_* call or the UBSan trap word +0x1b44. The checks of the two memsets are their contract's pre
   (aintrin_realizes through TransportGCg.v gx_intrin_at): the destinations OW (304 bytes) and GOT (224 bytes) are
   bytes of G (writable by TransportGRwB.v G_HARNESS_B_rw, not owned: G_HARNESS_gx_ok), with their shadow and hulls
   from the record facts receive_cg.v trans_recv_cells (lc5_sh_OW, lc5_sh_GOT, through
   LLVMFuzzerTestOneInput_st.v trans_sh_any_cells).

   The walk. Each stretch between two calls is one symbolic run of the token engine taken over the caller's G
   journal (TransportGRunB.v paj_run_x / paj_run_to_x), from a symbolic state built at the stretch's first
   instruction (the registers as atoms; the spill slots and the fields the stretch reads or stores as regions; the
   stores' bytes are bytes of G: awr_ok_x). m_wake and diginet_session_wake are G-form callees composed in the walk's
   journal (lp_mwake, lp_wake); their written ranges lie in G (op5_mwake_wr_G, op5_wake_wr_G), so what they keep
   carries the cut's core (LLVMFuzzerTestOneInput_st.v lc_core_kept_run through op5_next). check_state_wake_code is a
   leaf, through DgnTransportBLeafb.v decode_leafb_journal and TransportGCg.v gx_call_leaf (lp_cswc). The cut between
   two stretches is op5_at: the loop's common facts, the world relation, s8 / s11 and s4 kept, and the registers the
   next stretch reads.

   The model. WakeOps.v op5_step (LoopOk.v's op 5 case) at the start facts of the cut (lc_opok) says op 5 answers
   Some; LLVMFuzzerTestOneInput_st.v lc_op5_eq splits it into op_begin (lc5_begin), m_wake_m, the wake at g_now of
   m_wake's world, check_state_wake_code_m (which makes rc = want and keeps the world: op5_csw) and settle 0, which
   keeps the world (lc_settle_world): that world is SET56's, and settle_m at it answers Some. The wake's premises at
   m_wake's world: two run invariants (the frame in flight is at most SPEC_MAX_FRAME; each pending command's length
   is at most SPEC_CMD_MAX) by K6 (lc_runinv_stmt) at the start world, carried over op_begin and m_wake (TRunInv.v
   rk_upd, m_wake_rk, rk_out), g_fail_next <= 1 likewise (TIoRecv.v gkeep_upd, m_wake_gk), TF = None, the read-only
   bytes by K1 (lc_rom_view_stmt), and the side-stack counts of image B's wake: count_cid 1 = 0 < fs_frames 1 and
   count_cid 2 + 1 = 2 < fs_frames 2 (the class-2 frame of this function is the only one). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0 YCfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  m_set_cg m_wake_cg check_state_data_cg notice_cg io_send_cg send_control_cg set_state_cg diginet_session_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  DgnTransportBLeafb DgnTransportBCgRun TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
  LeafCgKit AsanKA check_state_wake_c check_state_wake_code_c check_state_wake_code_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TRunInv TIoRecv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree WakeOps LinksProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module TRI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TRunInv.
Module TIR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TIoRecv.
Module AG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.Agree.
Module WO := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.WakeOps.
Module LP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LinksProof.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module O5LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module O5KA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.AsanKA.
Module O5CSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_wake_c.
Module O5CWC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_wake_code_c.
Module O5CWG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_wake_code_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The powers of two the bounds name, as numerals (for lia). *)
Local Ltac op5_num :=
  repeat match goal with
  | |- context [2 ^ 64] => change (2 ^ 64) with 18446744073709551616
  | H : context [2 ^ 64] |- _ => change (2 ^ 64) with 18446744073709551616 in H
  | |- context [2 ^ 63] => change (2 ^ 63) with 9223372036854775808
  | H : context [2 ^ 63] |- _ => change (2 ^ 63) with 9223372036854775808 in H
  | |- context [2 ^ 47] => change (2 ^ 47) with 140737488355328
  | H : context [2 ^ 47] |- _ => change (2 ^ 47) with 140737488355328 in H
  | |- context [2 ^ 46] => change (2 ^ 46) with 70368744177664
  | H : context [2 ^ 46] |- _ => change (2 ^ 46) with 70368744177664 in H
  | |- context [2 ^ 40] => change (2 ^ 40) with 1099511627776
  | H : context [2 ^ 40] |- _ => change (2 ^ 40) with 1099511627776 in H
  | |- context [2 ^ 32] => change (2 ^ 32) with 4294967296
  | H : context [2 ^ 32] |- _ => change (2 ^ 32) with 4294967296 in H
  | |- context [2 ^ 31] => change (2 ^ 31) with 2147483648
  | H : context [2 ^ 31] |- _ => change (2 ^ 31) with 2147483648 in H
  end.
Local Ltac op5_lia := op5_num; lia.
(* A member of a closed list of numerals. *)
Local Ltac op5_inl := cbn [In]; repeat (first [left; reflexivity | right]).

(* ------------------------------------------------------------------ *)
(* 1. The model                                                        *)
(* ------------------------------------------------------------------ *)

(* op_begin_m's worlds (TCb.v :340-344): the two memsets, OW.desk_off, M.fail. *)
Definition lc5_Bo (Bw : list byte) : list byte := TW.upd Bw TW.OFF_OW (repeat (DSpec.b8 0) (Z.to_nat TW.SZ_OW)).
Definition lc5_Bm (Bw : list byte) : list byte :=
  TW.upd (lc5_Bo Bw) TW.OFF_GOT (repeat (DSpec.b8 0) (Z.to_nat TW.SZ_GOT)).
Definition lc5_B3 (Bw : list byte) : list byte := TW.set_OW_desk_off (lc5_Bm Bw) (-1).
Definition lc5_B1 (Bw : list byte) : list byte := TW.set_M_fail (lc5_B3 Bw) (TW.g_fail_next (lc5_B3 Bw)).

Lemma lc5_begin : forall Bw, TC.op_begin_m Bw = Some (lc5_B1 Bw, tt).
Proof. intros Bw. reflexivity. Qed.

Ltac lc5_num :=
  unfold TW.OFF_OW, TW.OFF_GOT, TW.OFF_M, TW.OFF_g_fail_next, TW.W_LEN, TW.SZ_OW, TW.SZ_GOT, TW.SZ_M in *.

Lemma lc5_len_upd : forall (bs v : list byte) k, Z.of_nat (length bs) = TW.W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= TW.W_LEN -> Z.of_nat (length (TW.upd bs k v)) = TW.W_LEN.
Proof. intros bs v k HL Hk Hv. rewrite TWL.length_upd by lia. exact HL. Qed.

Lemma lc5_u_out : forall (bs v : list byte) k k' n, Z.of_nat (length bs) = TW.W_LEN -> 0 <= k -> 0 <= k' ->
  (k' + Z.of_nat n <= k \/ k + Z.of_nat (length v) <= k') -> k + Z.of_nat (length v) <= TW.W_LEN ->
  TW.u_at (TW.upd bs k v) k' n = TW.u_at bs k' n.
Proof. intros bs v k k' n HL Hk Hk' Hd Hv. apply TWL.u_at_upd_out; lia. Qed.

Lemma lc5_len_rep : forall n, Z.of_nat (length (repeat (DSpec.b8 0) (Z.to_nat n))) = Z.max 0 n.
Proof. intros n. rewrite repeat_length. lia. Qed.

Lemma lc5_len_put : forall n v, Z.of_nat (length (TW.put n v)) = Z.of_nat n.
Proof. intros n v. rewrite TWL.length_put. reflexivity. Qed.

Ltac lc5_lside := rewrite ?lc5_len_rep, ?lc5_len_put; lc5_num; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *; lia.

Lemma lc5_len_Bo : forall Bw, Z.of_nat (length Bw) = TW.W_LEN -> Z.of_nat (length (lc5_Bo Bw)) = TW.W_LEN.
Proof. intros Bw HL. unfold lc5_Bo. apply lc5_len_upd; [exact HL | lc5_lside | lc5_lside]. Qed.
Lemma lc5_len_Bm : forall Bw, Z.of_nat (length Bw) = TW.W_LEN -> Z.of_nat (length (lc5_Bm Bw)) = TW.W_LEN.
Proof. intros Bw HL. unfold lc5_Bm. apply lc5_len_upd; [exact (lc5_len_Bo Bw HL) | lc5_lside | lc5_lside]. Qed.

(* The byte g_fail_next of op_begin's world before M.fail: the byte after the memsets. *)
Lemma lc5_gfn : forall Bw, Z.of_nat (length Bw) = TW.W_LEN ->
  TW.g_fail_next (lc5_B3 Bw) = TW.u_at (lc5_Bm Bw) TW.OFF_g_fail_next 1.
Proof.
intros Bw HL. unfold TW.g_fail_next, lc5_B3, TW.set_OW_desk_off, TW.A_OW_desk_off.
rewrite lc5_u_out by first [exact (lc5_len_Bm Bw HL) | lc5_lside].
reflexivity.
Qed.

(* op_begin's two block writes, as lengths. *)
Lemma lc5_zow : Z.of_nat (Z.to_nat TW.SZ_OW) = 304 /\ Z.of_nat (Z.to_nat TW.SZ_GOT) = 224.
Proof. split; reflexivity. Qed.

Local Ltac lc5_rside :=
  rewrite ?repeat_length, ?TWL.length_put, ?(proj1 lc5_zow), ?(proj2 lc5_zow); ri_num; lia.

(* op_begin (TCb.v:388-394) keeps TRunInv.v rk: no byte it writes is read by run_inv. *)
Lemma lc5_rk1 : forall (B0 : list byte), length B0 = Z.to_nat TW.W_LEN -> TRI.rk B0 (lc5_B1 B0).
Proof.
intros B0 LB. unfold lc5_B1, lc5_B3, lc5_Bm, lc5_Bo. ri_set.
repeat (apply (TRI.rk_upd _ _ _ _ LB); [| lc5_rside | lc5_rside | lc5_rside ]).
apply TRI.rk_refl.
Qed.

Local Ltac lc5_gside :=
  rewrite ?repeat_length, ?TWL.length_put, ?(proj1 lc5_zow), ?(proj2 lc5_zow);
  unfold TW.A_M_fail, TW.A_OW_desk_off, TW.OFF_M, TW.OFF_OW, TW.OFF_GOT,
    TW.OFF_g_fail_next, TW.W_LEN, TW.SZ_OW, TW.SZ_GOT;
  lia.

(* op_begin does not write g_fail_next (TIoRecv.v gkeep). *)
Lemma lc5_gk1 : forall (B0 : list byte), length B0 = Z.to_nat TW.W_LEN -> TIR.gkeep B0 (lc5_B1 B0).
Proof.
intros B0 LB. pose proof (TIR.len_w B0 LB) as LB'.
unfold lc5_B1, lc5_B3, lc5_Bm, lc5_Bo. gk_setters.
repeat (apply TIR.gkeep_upd; [| lc5_gside | rewrite LB'; lc5_gside | lc5_gside ]).
apply TIR.gkeep_refl.
Qed.

(* The run invariants and g_fail_next <= 1 at m_wake's world, from K6 at the start world. *)
Lemma op5_inv2 : forall (ops : Z) (B0 B2 : list byte) (want : Z), lc_runinv_stmt -> AG.agree timg_B ops B0 ->
  TC.m_wake_m (lc5_B1 B0) = Some (B2, want) ->
  TRI.run_inv B2 /\ TW.g_fail_next B2 <= 1.
Proof.
intros ops B0 B2 want HK6 HA E2.
pose proof (AG.ac_len _ _ _ (AG.ag_core _ _ _ HA)) as LB.
destruct (HK6 ops B0 HA) as (I1 & I2 & Iq & I4 & Inc & I5a & I5b & Igf).
assert (RI0 : TRI.run_inv B0) by exact (conj I1 (conj I2 (conj I4 (conj I5a (conj I5b (conj Inc Iq)))))).
pose proof (TRI.m_wake_rk B0 LB (lc5_B1 B0) B2 want (lc5_rk1 B0 LB) E2) as RK2.
destruct (TRI.rk_out B0 B2 LB RI0 RK2) as (_ & RI2).
split; [exact RI2|].
destruct (TIR.m_wake_gk B0 LB (lc5_B1 B0) B2 want (lc5_gk1 B0 LB) E2) as (_ & GK).
rewrite GK. exact Igf.
Qed.

(* m_wake's code is one of SPEC_E_ARG, SPEC_E_REFUSED, -EIO, SPEC_OK: a signed 32-bit value. *)
Lemma op5_want_range : forall B B' w, TC.m_wake_m B = Some (B', w) -> - 2 ^ 31 <= w < 2 ^ 31.
Proof.
intros B B' w H.
assert (G : match TC.m_wake_m B with Some (_, w0) => - 2 ^ 31 <= w0 < 2 ^ 31 | None => True end).
{ unfold TC.m_wake_m. cbv beta iota zeta.
  repeat match goal with
  | |- context [match ?x with _ => _ end] =>
      lazymatch x with
      | context [match _ with _ => _ end] => fail
      | _ => destruct x; cbv beta iota zeta
      end
  end.
  all: first
    [ exact I
    | match goal with |- _ <= ?v < _ => let v' := eval vm_compute in v in change v with v' end; op5_lia ]. }
rewrite H in G. exact G.
Qed.

(* check_state_wake_code_m keeps the world and makes rc = want. *)
Lemma op5_csw : forall B3 B4 r w (u : unit), TC.check_state_wake_code_m B3 r w = Some (B4, u) -> B4 = B3 /\ r = w.
Proof.
intros B3 B4 r w u H. unfold TC.check_state_wake_code_m in H. revert H.
destruct (Z.eqb_spec r w) as [Erw | Nrw]; intros H; cbn [negb] in H.
- split; [|exact Erw].
  exact (eq_sym (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => B3 end) H)).
- discriminate H.
Qed.

(* The operation's model at op 5 (WakeOps.v op5_step, at any stream): m_wake at op_begin's world, the wake at its
   g_now, the check (rc = want), settle 0 keeping the wake's world, and the operation's equation at every stream. *)
Lemma op5_model : forall (D : list byte) (ops : Z) (B0 : list byte) (c : TOP.fuzz_in) (k : nat),
  AG.agree timg_B ops B0 -> 0 <= ops < TC.OPS_MAX -> lc_opc D c = 5 ->
  exists B2 want B3 r,
    TC.m_wake_m (lc5_B1 B0) = Some (B2, want) /\
    TSS.diginet_session_wake_m timg_B None B2 (TW.g_now B2) = Some (B3, r) /\
    TC.check_state_wake_code_m B3 r want = Some (B3, tt) /\
    TC.settle_m B3 0 = Some (B3, tt) /\
    (forall A, TOP.LLVMFuzzerTestOneInput_op_m timg_B B0 A D c k = Some (B3, (lc_oc D c, k))).
Proof.
intros D ops B0 c k HA Hops Ho.
destruct (WO.op5_step LP.links_holds timg_B ops B0 (fun _ => 0) D c k HA Hops Ho) as (Bz & E & _).
rewrite (lc_op5_eq timg_B B0 (fun _ => 0) D c k Ho), lc5_begin in E. cbv beta iota in E.
destruct (TC.m_wake_m (lc5_B1 B0)) as [[B2 want]|] eqn:E2; cbv beta iota in E; [|discriminate E].
destruct (TSS.diginet_session_wake_m timg_B None B2 (TW.g_now B2)) as [[B3 r]|] eqn:E3;
  cbv beta iota in E; [|discriminate E].
destruct (TC.check_state_wake_code_m B3 r want) as [[B4 u4]|] eqn:E4; cbv beta iota in E; [|discriminate E].
destruct (TC.settle_m B4 0) as [[B5 u5]|] eqn:E5; cbv beta iota in E; [|discriminate E].
pose proof (lc_settle_world B4 B5 0 u5 E5) as EB5. subst B5.
destruct (op5_csw B3 B4 r want u4 E4) as (EB4 & _). subst B4.
assert (E4' : TC.check_state_wake_code_m B3 r want = Some (B3, tt)) by (destruct u4; exact E4).
assert (E5' : TC.settle_m B3 0 = Some (B3, tt)) by (destruct u5; exact E5).
exists B2, want, B3, r.
split; [first [exact E2 | reflexivity]|]. split; [exact E3|]. split; [exact E4'|]. split; [exact E5'|].
intros A. rewrite (lc_op5_eq timg_B B0 A D c k Ho), lc5_begin. cbv beta iota.
rewrite E2. cbv beta iota. rewrite E3. cbv beta iota. rewrite E4'. cbv beta iota. rewrite E5'. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The world relation across the stretches                           *)
(* ------------------------------------------------------------------ *)

(* A view that is rdF on the bytes P marks and rd0 elsewhere. *)
Definition lc5_in (lo n x : Z) : bool := (lo <=? x) && (x <? lo + n).
Definition lc5_mix (P : Z -> bool) (rdF rd0 : Z -> option Z) : Z -> option Z :=
  fun x => if P x then rdF x else rd0 x.

Lemma lc5_in_true : forall lo n x, lo <= x < lo + n -> lc5_in lo n x = true.
Proof. intros lo n x H. unfold lc5_in. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.
Lemma lc5_in_false' : forall lo n x, ~ (lo <= x < lo + n) -> lc5_in lo n x = false.
Proof.
intros lo n x H. unfold lc5_in. destruct (Z.leb_spec lo x); destruct (Z.ltb_spec x (lo + n)); cbn [andb];
  first [reflexivity | exfalso; lia].
Qed.
Lemma lc5_in_false : forall lo n x, lc5_in lo n x = false -> ~ (lo <= x < lo + n).
Proof. intros lo n x H Hx. rewrite (lc5_in_true lo n x Hx) in H. discriminate H. Qed.

Lemma lc5_tw_start : forall rdF rd0 Bw, tw_at TMAP_B rd0 Bw -> tw_at TMAP_B (lc5_mix (fun _ => false) rdF rd0) Bw.
Proof. intros rdF rd0 Bw H. apply (tw_kept TMAP_B rd0 _ Bw H). intros x _. reflexivity. Qed.

(* One 4-byte store of v at the world offset ko = o + k of the row (o, b, n). *)
Lemma lc5_tw_step : forall rdF rd0 P Bw o b n k ko v,
  tw_at TMAP_B (lc5_mix P rdF rd0) Bw -> In (o, b, n) TMAP_B -> ko = o + k -> 0 <= k -> k + 4 <= n ->
  (forall j, (j < 4)%nat -> rdF (b + k + Z.of_nat j) = Some (YO0f.le_byte v 4 j)) ->
  tw_at TMAP_B (lc5_mix (fun x => P x || lc5_in (b + k) 4 x) rdF rd0) (TW.upd Bw ko (TW.put 4 v)).
Proof.
intros rdF rd0 P Bw o b n k ko v H Hin Hko Hk Hkn HV. subst ko.
apply (tw_write TMAP_B (lc5_mix P rdF rd0) (lc5_mix (fun x => P x || lc5_in (b + k) 4 x) rdF rd0) Bw o b n k 4 v
  TMAP_B_ok H Hin Hk ltac:(change (Z.of_nat 4) with 4; lia)).
- intros j Hj. unfold lc5_mix. cbv beta.
  rewrite (lc5_in_true (b + k) 4 (b + k + Z.of_nat j)) by lia. rewrite orb_true_r. exact (HV j Hj).
- intros x Hx Hn. unfold lc5_mix. cbv beta. change (Z.of_nat 4) with 4 in Hn.
  rewrite (lc5_in_false' (b + k) 4 x) by lia. rewrite orb_false_r. reflexivity.
Qed.

Lemma lc5_tw_end : forall rdF rd0 P Bw, tw_at TMAP_B (lc5_mix P rdF rd0) Bw ->
  (forall x, tw_in TMAP_B x -> P x = false -> rdF x = rd0 x) -> tw_at TMAP_B rdF Bw.
Proof.
intros rdF rd0 P Bw H Hk. apply (tw_kept TMAP_B (lc5_mix P rdF rd0) rdF Bw H).
intros x Hx. unfold lc5_mix. destruct (P x) eqn:E; [reflexivity | exact (Hk x Hx E)].
Qed.

Ltac lc5_unP HP :=
  cbv beta in HP;
  repeat match type of HP with
  | orb _ _ = false =>
      let Hq := fresh "Hq" in apply orb_false_iff in HP; destruct HP as [HP Hq]; apply lc5_in_false in Hq
  end.

(* The memsets: a payload of a row zeroed (op_begin_m :390-391). *)
Lemma lc5_w_set : forall rd0 rdF Bw o b n,
  tw_at TMAP_B rd0 Bw -> In (o, b, n) TMAP_B -> 0 <= n ->
  (forall i, 0 <= i < n -> rdF (b + i) = Some (0 mod 256)) ->
  (forall x, tw_in TMAP_B x -> ~ (b <= x < b + n) -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF (TW.upd Bw o (repeat (DSpec.b8 0) (Z.to_nat n))).
Proof.
intros rd0 rdF Bw o b n Htw Hin Hn HV HK.
pose proof (tw_fill_set TMAP_B rd0 rdF Bw o b n 0 0 n TMAP_B_ok Htw Hin ltac:(lia) Hn ltac:(lia)) as H.
rewrite !Z.add_0_r in H. apply H.
- intros i Hi. exact (HV i Hi).
- intros x Hx Hnx. exact (HK x Hx Hnx).
Qed.

(* +0x820 .. +0x834: OW.desk_off := -1 and M.fail := the byte g_fail_next: op_begin's world. *)
Lemma lc5_w_c1 : forall Bw rd0 rdF,
  tw_at TMAP_B rd0 (lc5_Bm Bw) ->
  (forall j, (j < 4)%nat -> rdF (TB_OW + 232 + Z.of_nat j) = Some (YO0f.le_byte (-1) 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 88 + Z.of_nat j) = Some (YO0f.le_byte (TW.g_fail_next (lc5_B3 Bw)) 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_OW + 232 <= x < TB_OW + 236) -> ~ (TB_M + 88 <= x < TB_M + 92) -> rdF x = rd0 x) ->
  tw_at TMAP_B rdF (lc5_B1 Bw).
Proof.
intros Bw rd0 rdF Htw VD VF Hk.
assert (SM : TW.SZ_M = 1648) by reflexivity. assert (SO : TW.SZ_OW = 304) by reflexivity.
unfold lc5_B1. set (g := TW.g_fail_next (lc5_B3 Bw)) in *.
unfold lc5_B3, TW.set_M_fail, TW.set_OW_desk_off, TW.A_M_fail, TW.A_OW_desk_off.
pose proof (lc5_tw_start rdF rd0 _ Htw) as H0.
pose proof (lc5_tw_step rdF rd0 _ _ TW.OFF_OW TB_OW TW.SZ_OW 232 (TW.OFF_OW + 232) (-1) H0 TMAP_B_OW
  ltac:(lia) ltac:(lia) ltac:(lia) VD) as H1.
pose proof (lc5_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 88 (TW.OFF_M + 88) g H1 TMAP_B_M
  ltac:(lia) ltac:(lia) ltac:(lia) VF) as H2.
apply (lc5_tw_end rdF rd0 _ _ H2).
intros x Hx HP. lc5_unP HP. apply Hk; [exact Hx | lia | lia].
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The bytes of G the stretches and the callees write               *)
(* ------------------------------------------------------------------ *)

(* A payload byte of a row of TMAP_B is a byte of G. *)
Lemma op5_inG_row : forall o b n a, In (o, b, n) TMAP_B -> b <= a < b + n -> inG TG.G_HARNESS_B a.
Proof.
intros o b n a Hin Ha. unfold inG. apply Exists_exists. exists (b, n).
split; [exact (TMAP_B_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.
Lemma op5_inG_OW : forall a, TB_OW <= a < TB_OW + 304 -> inG TG.G_HARNESS_B a.
Proof. intros a Ha. apply (op5_inG_row _ _ _ a TMAP_B_OW). unfold TW.SZ_OW. lia. Qed.
Lemma op5_inG_GOT : forall a, TB_GOT <= a < TB_GOT + 224 -> inG TG.G_HARNESS_B a.
Proof. intros a Ha. apply (op5_inG_row _ _ _ a TMAP_B_GOT). unfold TW.SZ_GOT. lia. Qed.
Lemma op5_inG_M : forall a, TB_M <= a < TB_M + 1648 -> inG TG.G_HARNESS_B a.
Proof. intros a Ha. apply (op5_inG_row _ _ _ a TMAP_B_M). unfold TW.SZ_M. lia. Qed.
Lemma op5_inG_gs : forall a, TB_g_s <= a < TB_g_s + 18264 -> inG TG.G_HARNESS_B a.
Proof. intros a Ha. apply (op5_inG_row _ _ _ a TMAP_B_g_s). unfold TW.SZ_g_s. lia. Qed.

(* m_wake's stores (m_wake_cg.v mwake_wr): fields of M and OW, and m_set's (m_set_cg.v mset_wr). *)
Lemma op5_mwake_wr_G : forall Bw a, mwake_wr Bw a -> inG TG.G_HARNESS_B a.
Proof.
intros Bw a (_ & _ & H).
destruct H as [H | [H | [H | [H | (_ & _ & H)]]]].
- apply op5_inG_M. unfold twb_fld in H. ri_num. lia.
- apply op5_inG_M. unfold twb_fld in H. ri_num. lia.
- apply op5_inG_OW. unfold twb_fld in H. ri_num. lia.
- apply op5_inG_M. unfold twb_fld in H. ri_num. lia.
- unfold mset_wr in H. destruct H as [(Hn & H) | [H | H]].
  + apply op5_inG_OW. unfold twb_fld in H. ri_num. unfold TW.OW_t_ESZ in *. lia.
  + apply op5_inG_OW. unfold twb_fld in H. ri_num. lia.
  + apply op5_inG_M. unfold twb_fld in H. ri_num. lia.
Qed.

(* io_send's stores (io_send_cg.v iosend_wr), each a field of G. *)
Lemma op5_iosend_wr_G : forall n a, iosend_wr n a -> inG TG.G_HARNESS_B a.
Proof.
intros n a H. unfold iosend_wr in H.
repeat match type of H with _ \/ _ => destruct H as [H|H] end.
all: first
  [ (destruct H as (s & Hs & H); apply (op5_inG_row _ _ _ a TMAP_B_g_cmd); unfold twb_fld in H; ri_num;
     unfold TW.SZ_g_cmd, TW.Cmd_ESZ in *; lia)
  | (apply (op5_inG_row _ _ _ a TMAP_B_g_fail_next); unfold twb_fld in H; ri_num; lia)
  | (apply op5_inG_GOT; unfold twb_fld in H; ri_num; lia)
  | (apply op5_inG_M; unfold twb_fld in H; ri_num; lia)
  | (apply (op5_inG_row _ _ _ a TMAP_B_g_last_counter); unfold twb_fld in H; ri_num;
     unfold TW.SZ_g_last_counter in *; lia)
  | (apply (op5_inG_row _ _ _ a TMAP_B_g_q); unfold twb_fld in H; ri_num; unfold TW.SZ_g_q in *; lia)
  | (apply (op5_inG_row _ _ _ a TMAP_B_g_nq); unfold twb_fld in H; ri_num; unfold TW.SZ_g_nq in *; lia) ].
Qed.

(* diginet_session_wake's stores (diginet_session_wake_cg.v wake_wr): fields of g_s, io_send's, notice's. *)
Lemma op5_wake_wr_G : forall Bw a, wake_wr Bw a -> inG TG.G_HARNESS_B a.
Proof.
intros Bw a H. unfold wake_wr in H.
repeat match type of H with _ \/ _ => destruct H as [H|H] end.
all: first
  [ exact (op5_iosend_wr_G _ a H)
  | (destruct H as (_ & [H | H]);
     [ apply op5_inG_gs; unfold twb_fld in H; ri_num; lia | exact (notice_wr_G _ _ a H) ])
  | (apply op5_inG_gs; unfold twb_fld, SENDCTL_F in H; ri_num; lia) ].
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The shadow of OW and GOT (the memsets' destinations)              *)
(* ------------------------------------------------------------------ *)

(* The record's cells of trans_recv_cells, as shadow cells: g_rx_len's granule and its three guards, OW's 38 granules
   and six guards, GOT's four leading guards (g_s's) and its 28 granules: the aligned groups of OW's and GOT's
   hulls. *)
Definition lc5_cs : list (Z * Z) :=
  trans_zgran TB_g_rx_len (TB_g_rx_len + TW.SZ_g_rx_len) ++
  [(TB_g_rx_len + 8, 0xf9); (TB_g_rx_len + 16, 0xf9); (TB_g_rx_len + 24, 0xf9)] ++
  trans_zgran TB_OW (TB_OW + TW.SZ_OW) ++
  [(TB_OW + TW.SZ_OW, 0xf9); (TB_OW + TW.SZ_OW + 8, 0xf9); (TB_OW + TW.SZ_OW + 16, 0xf9);
   (TB_OW + TW.SZ_OW + 24, 0xf9); (TB_OW + TW.SZ_OW + 32, 0xf9); (TB_OW + TW.SZ_OW + 40, 0xf9)] ++
  [(TB_GOT - 32, 0xf9); (TB_GOT - 24, 0xf9); (TB_GOT - 16, 0xf9); (TB_GOT - 8, 0xf9)] ++
  trans_zgran TB_GOT (TB_GOT + TW.SZ_GOT).

Lemma lc5_cover : trans_cs_cover lc5_cs TB_OW 304 = true /\ trans_cs_cover lc5_cs TB_GOT 224 = true.
Proof. split; vm_compute; reflexivity. Qed.

Section sh. Context {rc : YM05.RunCeil}.
Variable B : asyms.

Lemma lc5_sh_cells : trans_recv_cells B -> trans_sh_cells B lc5_cs.
Proof.
intros (HZow & HZgot & HZrx & HC).
unfold lc5_cs.
apply trans_sh_cells_app; [apply trans_sh_cells_zshadow; [exact HZrx | reflexivity]|].
apply trans_sh_cells_app.
{ repeat apply trans_sh_cells_cons; try apply trans_sh_cells_nil.
  all: apply trans_sh_cell_const; [intro ly; pose proof (HC ly) as Hc; tauto | lia]. }
apply trans_sh_cells_app; [apply trans_sh_cells_zshadow; [exact HZow | reflexivity]|].
apply trans_sh_cells_app.
{ repeat apply trans_sh_cells_cons; try apply trans_sh_cells_nil.
  all: apply trans_sh_cell_const; [intro ly; pose proof (HC ly) as Hc; tauto | lia]. }
apply trans_sh_cells_app.
{ repeat apply trans_sh_cells_cons; try apply trans_sh_cells_nil.
  all: apply trans_sh_cell_const; [intro ly; pose proof (HC ly) as Hc; tauto | lia]. }
apply trans_sh_cells_zshadow; [exact HZgot | reflexivity].
Qed.

Lemma lc5_sh_OW : trans_recv_cells B -> trans_sh_any B TB_OW 304.
Proof. intros HR. exact (trans_sh_any_cells B lc5_cs TB_OW 304 (lc5_sh_cells HR) (proj1 lc5_cover)). Qed.
Lemma lc5_sh_GOT : trans_recv_cells B -> trans_sh_any B TB_GOT 224.
Proof. intros HR. exact (trans_sh_any_cells B lc5_cs TB_GOT 224 (lc5_sh_cells HR) (proj2 lc5_cover)). Qed.
End sh.

(* ------------------------------------------------------------------ *)
(* 5. The machine: valuations, symbolic states and their tactics       *)
(* ------------------------------------------------------------------ *)

(* The callee-saved registers the cuts and the core read: sp, gp, tp, s0, s1, s2, s3, s4, s8, s10, s11. *)
Definition op5_kr (regsA regsB : bvmap 5 word) : Prop :=
  forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 24; 26; 27] ->
    YK11.getr regsB (Z_to_bv 5 r) = YK11.getr regsA (Z_to_bv 5 r).
Lemma op5_kr_trans : forall r1 r2 r3, op5_kr r1 r2 -> op5_kr r2 r3 -> op5_kr r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.
Lemma op5_kr_pres : forall r1 r2, aregs_preserved r1 r2 -> op5_kr r1 r2.
Proof.
intros r1 r2 HP r Hr. apply HP. cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr]; [unfold acallee_saved; lia |]). destruct Hr.
Qed.

(* Byte j < 4 of a 64-bit word holding v is byte j of the 4-byte little-endian v. *)
Lemma op5_bow : forall v j, (j < 4)%nat ->
  bv_unsigned (byte_of_word (Z_to_bv 64 v) (Z.of_nat j)) = YO0f.le_byte v 4 j.
Proof.
intros v j Hj. unfold byte_of_word, YO0f.le_byte. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with (2 ^ 8). change (2 ^ Z.of_N 64) with (2 ^ 64). change (8 * Z.of_nat 4) with 32.
change 256 with (2 ^ 8).
apply Z.bits_inj'. intros m Hm.
destruct (Z_lt_le_dec m 8) as [Hl|Hl].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
  rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* The 4 bytes of a chunk of a region of the state, of value v, read through the view. *)
Lemma op5_chunk : forall (E : env) (H : word -> bool) (mm : word -> option byte) nb lo hi wlo whi cs b off e v,
  YP09.region_ok tfibsegs E (mrestrict H mm) (YP09.mkRegion nb lo hi wlo whi cs) ->
  YP09.base_val E nb = b -> In (YP09.mkChunk off (CVal 4 e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  forall j, (j < 4)%nat -> aview tfibsegs H mm (b + off + Z.of_nat j) = Some (YO0f.le_byte v 4 j).
Proof.
intros E H mm nb lo hi wlo whi cs b off e v HR Hb Hin He j Hj.
destruct HR as (_ & _ & _ & HC). cbn [YP09.r_base YP09.r_chunks] in HC. rewrite Hb in HC.
pose proof (proj1 (Forall_forall _ _) HC _ Hin) as HC1. unfold YP09.chunk_ok in HC1.
cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in HC1.
destruct (HC1 (Z.of_nat j) ltac:(cbn; lia)) as (bt & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. rewrite He in Hb1.
injection Hb1 as <-.
change (aview tfibsegs H mm (b + off + Z.of_nat j))
  with (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte tfibsegs (mrestrict H mm) (b + off + Z.of_nat j))).
rewrite Hb2. cbn [option_map]. f_equal. apply op5_bow. exact Hj.
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac op5_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "op5_reg: no match for" T; fail
  end.
(* The write right of a run whose regions have no write window. *)
Ltac op5_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
          [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
            cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; exfalso; lia |]);
  apply awr_ok_x_nil.
(* A run from a state with no write window writes no byte. *)
Ltac op5_keep_tac HFr KR W mold msn :=
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) (ms_mem msn) a = aview tfibsegs (w_H W) mold a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    apply (YC4b.kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []];
    let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
    let Hin := fresh "Hin" in let Hx := fresh "Hx" in
    intros b wlo whi x Hin Hx;
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
    cbn [In] in Hin;
    repeat (destruct Hin as [Hin | Hin]; [ injection Hin as <- <- <-; cbn [base_val] in Hx; exfalso; lia |]);
    destruct Hin
  | ].
(* The windows a run wrote, each inside the bytes Zs. *)
Ltac op5_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The symbolic states with regions. +0x820: the spill slots 184(s1) (g_fail_next's page) and 168(s1) (M, the
   listing's object 8), the byte g_fail_next (atom 32), and the two fields the stretch stores, M.fail (at object 8)
   and OW.desk_off (at s6 = OW). *)
Definition op5_c_sp184 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 184 192 0 0 [YP09.mkChunk 184 (YP09.CVal 8 (SLit (transportb_hi 10)))].
Definition op5_c_gfn : YP09.region :=
  YP09.mkRegion None TB_g_fail_next (TB_g_fail_next + 1) 0 0 [YP09.mkChunk TB_g_fail_next (YP09.CVal 1 (SOff 32 0))].
Definition op5_c_sp168 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 168 176 0 0 [YP09.mkChunk 168 (YP09.CVal 8 (SOff (A_OBJ 8) 0))].
Definition op5_c_fail : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 88 92 88 92 [].
Definition op5_c_doff : YP09.region := YP09.mkRegion (Some 22%nat) 232 236 232 236 [].
Definition op5_c_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (22%nat, mkAF TB_OW TB_OW 5); (A_OBJ 8, mkAF TB_M TB_M 5);
           (32%nat, mkAF 0 255 0)] [] [].
Definition op5_c_ss : sstate :=
  mkSS 2080 sr_atoms [op5_c_sp184; op5_c_gfn; op5_c_sp168; op5_c_fail; op5_c_doff] None op5_c_facts.
(* +0x83c: the spill slot 152(s1) (g_now's page) and g_now's 8 bytes (atom 32). *)
Definition op5_d_sp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 152 160 0 0 [YP09.mkChunk 152 (YP09.CVal 8 (SLit (transportb_hi 9)))].
Definition op5_d_now : YP09.region :=
  YP09.mkRegion None TB_g_now (TB_g_now + 8) 0 0 [YP09.mkChunk TB_g_now (YP09.CVal 8 (SOff 32 0))].
Definition op5_d_ss : sstate := mkSS 2108 sr_atoms [op5_d_sp; op5_d_now] None (mkFacts [] [] []).

Section env. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Definition op5_Ex (regs : bvmap 5 word) (extra : list word) : env := Eimg (PI := PI_transportb) (Ereg regs extra).
Definition op5_B0 : Z * Z := (0, 0).
Definition op5_Bx : sv := SLit 0.

Lemma op5_base : BASE = transportb_text.
Proof. vm_compute. reflexivity. Qed.
Lemma op5_vals : VAL (A_OBJ 8) = TB_M /\ VAL (A_OBJ 9) = TB_g_s /\ VAL (A_OBJ 12) = TB_OW /\ VAL (A_OBJ 13) = TB_GOT.
Proof. vm_compute. repeat split. Qed.

Lemma op5_ew : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (op5_Ex regs extra) n = YK11.getr regs r.
Proof. intros regs extra n r Hn. unfold op5_Ex. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma op5_img : forall regs extra, img_env VAL A_LIM (op5_Ex regs extra).
Proof. intros regs extra. unfold op5_Ex. apply Eimg_env. Qed.
Lemma op5_agree : forall regs extra, env_agree 32 (Ereg regs extra) (op5_Ex regs extra).
Proof. intros regs extra. split; [intros m Hm; unfold op5_Ex; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma op5_ex32 : forall regs v, ew (op5_Ex regs [v]) 32 = v.
Proof. intros regs v. unfold op5_Ex. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs [v] 0%nat). Qed.
(* An image object's address, as the run leaves it in a register (auipc / addi). *)
Lemma op5_sv_obj : forall regs extra k v, (A_TEXT <= k < A_LIM)%nat -> VAL k = v -> 0 <= v < 2 ^ 64 ->
  sv_denot (op5_Ex regs extra) (SOff k 0) = w64 v.
Proof.
intros regs extra k v Hk Hv Hr. cbn [sv_denot]. unfold op5_Ex. rewrite Eimg_img by exact Hk. rewrite Hv.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.
(* A register atom's value in the valuation. *)
Lemma op5_U : forall regs extra n (r : bv 5) v, Z.of_nat n = bv_unsigned r ->
  YK11.getr regs r = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew (op5_Ex regs extra) n) = v.
Proof.
intros regs extra n r v Hn Hr Hv. rewrite (op5_ew regs extra n r Hn), Hr. unfold w64.
apply unsigned_lit_small. exact Hv.
Qed.
(* M's address, the image atom of object 8. *)
Lemma op5_U249 : forall regs extra, bv_unsigned (ew (op5_Ex regs extra) 249%nat) = TB_M.
Proof.
intros regs extra. unfold op5_Ex. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). change 249%nat with (A_OBJ 8).
rewrite (proj1 op5_vals). apply unsigned_lit_small. unfold TB_M. lia.
Qed.

(* A symbolic state with no region holds of any machine state at its pc. *)
Lemma op5_entry : forall (W : world segs) regs extra mem (pc : Z),
  st_ok_pi segs VAL (op5_Ex regs extra) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs extra mem pc. rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* The state at +0x820 holds of the machine state there (atom 32: the byte g_fail_next at the world X). *)
Lemma op5_c_entry : forall (W : world segs) regs mem X s1,
  YK11.getr regs (Z_to_bv 5 9) = w64 s1 -> YK11.getr regs (Z_to_bv 5 22) = w64 TB_OW ->
  70368744177664 <= s1 -> s1 + 192 <= 140737488355328 -> s1 mod 32 = 0 ->
  rdword (aview segs (w_H W) mem) (s1 + 184) = Some (transportb_hi 10) ->
  rdword (aview segs (w_H W) mem) (s1 + 168) = Some TB_M ->
  tw_at TMAP_B (aview segs (w_H W) mem) X ->
  st_ok_pi segs VAL (op5_Ex regs [Z_to_bv 64 (TW.u_at X TW.OFF_g_fail_next 1)]) op5_c_ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 2080)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem X s1 R9 R22 Hs1a Hs1b Hs1c H184 H168 Htw.
set (E := op5_Ex regs [Z_to_bv 64 (TW.u_at X TW.OFF_g_fail_next 1)]).
pose proof lf_spill_pages as (_ & _ & E10 & _).
assert (U9 : bv_unsigned (ew E 9%nat) = s1)
  by (unfold E; exact (op5_U regs _ 9 (Z_to_bv 5 9) s1 eq_refl R9 ltac:(op5_lia))).
assert (U22 : bv_unsigned (ew E 22%nat) = TB_OW)
  by (unfold E; exact (op5_U regs _ 22 (Z_to_bv 5 22) TB_OW eq_refl R22 ltac:(unfold TB_OW; op5_lia))).
assert (U249 : bv_unsigned (ew E 249%nat) = TB_M) by (unfold E; apply op5_U249).
assert (U8 : bv_unsigned (ew E (A_OBJ 8)) = TB_M) by exact U249.
pose proof (TWL.u_at_range X TW.OFF_g_fail_next 1) as Rg.
change (2 ^ (8 * Z.of_nat 1)) with 256 in Rg.
assert (E32 : ew E 32 = Z_to_bv 64 (TW.u_at X TW.OFF_g_fail_next 1)) by (unfold E; apply op5_ex32).
rewrite restrict_mkst_fx. unfold op5_c_ss.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
    cbn [op5_c_sp184 op5_c_gfn op5_c_sp168 op5_c_fail op5_c_doff
      YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [op5_lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ s1 184 8 (SLit (transportb_hi 10)) (transportb_hi 10));
      [reflexivity | rewrite E10; change (8 * Z.of_N 8) with 64; op5_lia | cbn; lia |].
    exact (val_mem_of_rdword segs (w_H W) mem _ _ H184).
  + split; [unfold TB_g_fail_next; lia|]. split; [unfold TB_g_fail_next; op5_lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ 0 TB_g_fail_next 1 (SOff 32 0) (TW.u_at X TW.OFF_g_fail_next 1));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (8 * Z.of_N 1) with 8; change (2 ^ 8) with 256; lia | cbn; lia |].
    pose proof (tw_read_val segs (mrestrict (w_H W) mem) TMAP_B X TW.OFF_g_fail_next TB_g_fail_next 1 0 1
      TMAP_B_ok Htw TMAP_B_g_fail_next ltac:(lia) ltac:(lia)) as HV.
    rewrite !Z.add_0_r in HV. rewrite Z.add_0_l. exact HV.
  + rewrite U9. split; [lia|]. split; [op5_lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ s1 168 8 (SOff (A_OBJ 8) 0) TB_M);
      [cbn [sv_denot]; rewrite ?U8, ?U249, Z.add_0_r; reflexivity
      | change (8 * Z.of_N 8) with 64; unfold TB_M; op5_lia | cbn; lia |].
    exact (val_mem_of_rdword segs (w_H W) mem _ _ H168).
  + rewrite ?U8, ?U249. split; [unfold TB_M; lia|]. split; [unfold TB_M; op5_lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_M + o) G_HARNESS_B_rw). apply op5_inG_M. lia.
  + rewrite U22. split; [unfold TB_OW; lia|]. split; [unfold TB_OW; op5_lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_OW + o) G_HARNESS_B_rw). apply op5_inG_OW. lia.
- apply pairwise_disjoint_of_extents.
  unfold op5_c_sp184, op5_c_gfn, op5_c_sp168, op5_c_fail, op5_c_doff, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U9, U22, ?U8, ?U249.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold TB_g_fail_next, TB_M, TB_OW.
  repeat split; first [exact I | lia].
- unfold op5_c_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U22, ?U8, ?U249, E32, !unsigned_lit_small by lia.
  change (2 ^ 5) with 32. change (2 ^ 46) with 70368744177664. change (2 ^ 47) with 140737488355328.
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold TB_OW, TB_M; first [lia | reflexivity].
Qed.

(* The state at +0x83c holds of the machine state there (atom 32: g_now's 8 bytes, nw). *)
Lemma op5_d_entry : forall (W : world segs) regs mem (s1 nw : Z),
  YK11.getr regs (Z_to_bv 5 9) = w64 s1 -> 70368744177664 <= s1 -> s1 + 160 <= 140737488355328 ->
  rdword (aview segs (w_H W) mem) (s1 + 152) = Some (transportb_hi 9) ->
  val_mem segs (mrestrict (w_H W) mem) TB_g_now 8 nw -> 0 <= nw < 2 ^ 64 ->
  st_ok_pi segs VAL (op5_Ex regs [w64 nw]) op5_d_ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 2108)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem s1 nw R9 Hs1a Hs1b H152 HNOW RNW.
set (E := op5_Ex regs [w64 nw]).
pose proof lf_spill_pages as (_ & E9 & _).
assert (U9 : bv_unsigned (ew E 9%nat) = s1)
  by (unfold E; exact (op5_U regs _ 9 (Z_to_bv 5 9) s1 eq_refl R9 ltac:(op5_lia))).
assert (E32 : ew E 32 = w64 nw) by (unfold E; apply op5_ex32).
rewrite restrict_mkst_fx. unfold op5_d_ss.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
    cbn [op5_d_sp op5_d_now YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [op5_lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ s1 152 8 (SLit (transportb_hi 9)) (transportb_hi 9));
      [reflexivity | rewrite E9; change (8 * Z.of_N 8) with 64; op5_lia | cbn; lia |].
    exact (val_mem_of_rdword segs (w_H W) mem _ _ H152).
  + split; [unfold TB_g_now; lia|]. split; [unfold TB_g_now; op5_lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ 0 TB_g_now 8 (SOff 32 0) nw);
      [ cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | change (8 * Z.of_N 8) with 64; exact RNW | cbn; lia |].
    rewrite Z.add_0_l. exact HNOW.
- apply pairwise_disjoint_of_extents.
  unfold op5_d_sp, op5_d_now, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold TB_g_now. repeat split; first [exact I | lia].
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* The harness globals' payloads lie in loaded segments: no world hides them, and the world relation at a world's
   view is the relation at the raw memory the leaf reads (csw_view). *)
Lemma op5_hull_vis : forall (W : world segs) x, TG.G_HARNESS_B_LO <= x < TG.G_HARNESS_B_HI ->
  w_H W (Z_to_bv 64 x) = false.
Proof.
  intros W x Hx. apply (decode_vis_seg W).
  apply (decode_covers_img TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) x);
    [vm_compute; reflexivity | lia].
Qed.
Lemma op5_tw_csw : forall (W : world segs) mem Bw,
  tw_at TMAP_B (aview segs (w_H W) mem) Bw -> tw_at TMAP_B (O5CSW.csw_view mem) Bw.
Proof.
  intros W mem Bw H. apply (tw_kept TMAP_B _ _ Bw H). intros x Hx.
  unfold O5CSW.csw_view. rewrite (decode_aview_mrd W mem x (op5_hull_vis W x (TMAP_B_hull x Hx))). reflexivity.
Qed.
End env.

(* The register r of 2 .. 27 that the state HS holds as its own atom is the register of regs0. *)
Ltac op5_kreg HS regs0 :=
  lazymatch goal with |- YK11.getr _ (Z_to_bv 5 ?q) = _ =>
    let n := eval vm_compute in (Z.to_nat q) in
    let H := fresh "Hq" in
    op5_reg HS (Z_to_bv 5 q) (YK11.getr regs0 (Z_to_bv 5 q)) H
      ltac:(cbn [sv_denot]; rewrite (op5_ew regs0 _ n (Z_to_bv 5 q) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
            reflexivity);
    exact H
  end.
Ltac op5_kr_tac HS regs0 :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr]; [op5_kreg HS regs0 |]); destruct Hr.

(* ------------------------------------------------------------------ *)
(* 6. The walk                                                         *)
(* ------------------------------------------------------------------ *)

Section seg. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The states between the stretches: the loop's common facts at operation op with lo_k op receptions, the world
   relation at Bw, the cursor after the op byte in s8 / s11, s4 = c, and R of the registers. *)
Definition op5_at (cx : lcx) (op : lop) (off : Z) (Bw : list byte) (R : bvmap 5 word -> Prop)
    : world segs -> config -> Prop :=
  fun W c => exists ly S regs mem md e,
    c = lc_cfg cx off regs mem md /\
    lc_lcore B MT cx op false false (lo_k op) ly S W regs mem md e /\
    lc_tw W mem Bw /\
    lc_cur cx regs 24 27 (lc_oc (l_pl cx) (lo_c op)) /\
    YK11.getr regs 20 = w64 (lc_F cx + 32) /\ R regs.

(* The event count: e <= RECV_EV * k with k <= ops < OPS_MAX receptions, inside the slot's EV_LIB. *)
Lemma op5_ev : forall cx op ly' S' (W' : world segs) regs' mem' md' e,
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

(* The stack: sp1 above alloc_ceiling, sp0 below 2 ^ 47, the alignments. *)
Lemma op5_sp : forall cx ly' S' (W' : world segs) regs' mem' md' e,
  lc_base B MT XL RLO RHI cx -> lc_core B cx ly' S' W' regs' mem' md' e ->
  alloc_ceiling + 32432 <= lc_sp1 cx /\ lc_sp0 cx - 336 <= lc_sp1 cx <= lc_sp0 cx - 320 /\
  lc_sp0 cx <= 140737488355328 /\ (lc_sp1 cx - lc_sp0 cx) mod 16 = 0 /\ lc_sp1 cx mod 16 = 0 /\
  0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof.
intros cx ly' S' W' regs' mem' md' e HB HC.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [_ Hsp0al Hstk Hsp1c _ _ _ _ _].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & Hsp1al & _).
destruct Hstk as (_ & _ & Hst3 & Hst4). unfold LF_FRAME in Hsp1.
pose proof asan_consts as ((CVlo & CVhi) & _).
change (2 ^ 47) with 140737488355328 in Hst4.
assert (H16 : lc_sp1 cx mod 16 = 0).
{ apply Z.mod_divide in Hsp1al as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((q * 2) * 16) by ring.
  apply Z_mod_mult. }
split; [exact Hsp1c|]. split; [exact Hsp1|]. split; [lia|].
split; [rewrite Zminus_mod, H16, Hsp0al; reflexivity|].
split; [exact H16 | split; lia].
Qed.

(* What a callee's contract asks of the call state, from the cut's core and the run to the `jal`. *)
Lemma op5_callpre : forall cx ly' S' (W' : world segs) regs' mem' md' e (regsX : bvmap 5 word) (k FSTK : Z),
  lc_base B MT XL RLO RHI cx -> lc_core B cx ly' S' W' regs' mem' md' e ->
  op5_kr regs' regsX ->
  YK11.getr regsX 1 = Z_to_bv 64 (BASE + k) -> 0 <= k < 2 ^ 40 -> k mod 2 = 0 ->
  0 <= FSTK <= LLVMF_STK - 336 ->
  YK0s.ret_ok (YK11.getr regsX 1) /\ 4096 <= raZ regsX /\
  YK11.getr regsX 3 = w64 (as_gp B) /\ YK11.getr regsX 4 = w64 (as_tp B) /\
  spZ regsX = lc_sp1 cx /\ spZ regsX mod 16 = 0 /\
  lc_sp0 cx - LLVMF_STK <= spZ regsX - FSTK /\ spZ regsX <= lc_sp0 cx.
Proof.
intros cx ly' S' W' regs' mem' md' e regsX k FSTK HB HC HKR R1 Hk Hk2 HF.
destruct (op5_sp cx ly' S' W' regs' mem' md' e HB HC) as (Hsp1c & Hsp1 & Hsp0 & _ & H16 & CVlo & CVhi).
pose proof HC as (_ & _ & _ & _ & R2 & _ & _ & R3 & R4 & _).
assert (ELS : LLVMF_STK = 32768) by reflexivity.
assert (R2X : YK11.getr regsX (Z_to_bv 5 2) = w64 (lc_sp1 cx)) by exact (eq_trans (HKR 2 ltac:(op5_inl)) R2).
assert (QSP : spZ regsX = lc_sp1 cx).
{ unfold spZ. transitivity (bv_unsigned (Z_to_bv 64 (lc_sp1 cx))); [f_equal; exact R2X|].
  apply unsigned_lit_small. op5_lia. }
split; [rewrite R1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [exact Hk | exact Hk2]|].
split.
{ unfold raZ. rewrite R1, op5_base. rewrite unsigned_lit_small by (unfold transportb_text; op5_lia).
  unfold transportb_text. lia. }
split; [exact (eq_trans (HKR 3 ltac:(op5_inl)) R3)|].
split; [exact (eq_trans (HKR 4 ltac:(op5_inl)) R4)|].
split; [exact QSP|].
split; [rewrite QSP; exact H16|].
split; rewrite QSP; lia.
Qed.

(* What lc_core_kept_run asks of the bytes, from a run, a memset or a leaf that changes only bytes of G and the
   window [sp1 - X, sp1): the bytes above alloc_ceiling outside the window, the blocks' bytes, the frame's bytes and
   its shadow. *)
Lemma op5_kept_g : forall cx ly' S' (W' : world segs) regs' mem' md' e (mem2 : word -> option byte) (X : Z),
  AR_laws segs B -> lc_base B MT XL RLO RHI cx -> lc_core B cx ly' S' W' regs' mem' md' e ->
  0 <= X <= LLVMF_STK - 336 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS_B a -> ~ (lc_sp1 cx - X <= a < lc_sp1 cx) ->
     aview segs (w_H W') mem2 a = aview segs (w_H W') mem' a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - X <= a < lc_sp1 cx) ->
     aview segs (w_H W') mem2 a = aview segs (w_H W') mem' a) /\
  (forall b m i, In (b, m) (ablocks B ly' S') -> 0 <= i < req_size m ->
     aview segs (w_H W') mem2 (b + i) = aview segs (w_H W') mem' (b + i)) /\
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES \/ lc_SH cx <= a < lc_SH cx + 32 ->
     aview segs (w_H W') mem2 a = aview segs (w_H W') mem' a).
Proof.
intros cx ly' S' W' regs' mem' md' e mem2 X LAWS HB HC HX KR.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HAR _ _ Hsp1c HFaddr HFin _ _ _].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF4096 & _ & HFce & _).
pose proof asan_consts as ((CVlo & CVhi) & _).
assert (ELS : LLVMF_STK = 32768) by reflexivity.
assert (HF8 : 0 <= lc_F cx / 8 <= lc_F cx) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (GHI : forall a, inG TG.G_HARNESS_B a -> a < TG.G_HARNESS_B_HI)
  by (intros a Ha; exact (proj2 (inG_G_HARNESS_hull a Ha))).
unfold TG.G_HARNESS_B_HI in GHI.
unfold LF_FBYTES in *.
split; [|split].
- intros a Ha Hn. apply KR; [lia | intros HG; pose proof (GHI a HG); lia | exact Hn].
- intros b m i Hin Hi.
  destruct (al_blocks _ _ LAWS ly' S' W' mem' md' b m HAR Hin) as (_ & H4096 & Hbc & _).
  apply KR; [op5_lia | | lia].
  intros HG. exact (blk_img segs B LAWS ly' S' W' mem' md' b m (b + i) HAR Hin ltac:(lia) (trans_g_img (b + i) HG)).
- intros a Ha.
  assert (HSH : lc_SH cx = SHADOW_OFF + lc_F cx / 8) by reflexivity. unfold SHADOW_OFF in HSH.
  apply KR.
  + destruct Ha; op5_lia.
  + intros HG. destruct Ha as [Ha | Ha].
    * apply (frm_img segs B LAWS ly' S' W' mem' md' LF_CID (l_fpos cx) a HAR HFin);
        [rewrite HFaddr; change (fs_frame_bytes LF_CID) with 256; exact Ha | exact (trans_g_img a HG)].
    * pose proof (GHI a HG). lia.
  + destruct Ha; lia.
Qed.

(* The same across a G-form call whose written range E lies in G, after a run that changed only bytes of G. *)
Lemma op5_kept : forall cx ly' S' (W' : world segs) regs' mem' md' e (memX : word -> option byte)
    (W2 : world segs) mem2 (X : Z) (E : Z -> Prop),
  AR_laws segs B -> lc_base B MT XL RLO RHI cx -> lc_core B cx ly' S' W' regs' mem' md' e ->
  0 <= X <= LLVMF_STK - 336 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS_B a -> aview segs (w_H W') memX a = aview segs (w_H W') mem' a) ->
  (forall a, E a -> inG TG.G_HARNESS_B a) ->
  acall_kept_g segs B TG.G_HARNESS_B ly' S' W' memX W2 mem2 (lc_sp1 cx - X) (lc_sp1 cx) E ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - X <= a < lc_sp1 cx) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a) /\
  (forall b m i, In (b, m) (ablocks B ly' S') -> 0 <= i < req_size m ->
     aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W') mem' (b + i)) /\
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES \/ lc_SH cx <= a < lc_SH cx + 32 ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a).
Proof.
intros cx ly' S' W' regs' mem' md' e memX W2 mem2 X E LAWS HB HC HX KR HEG HK.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HAR _ _ Hsp1c HFaddr HFin _ _ _].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF4096 & _ & HFce & _).
destruct HK as (K1 & K2 & _ & K4 & _).
pose proof asan_consts as ((CVlo & CVhi) & _).
assert (HF8 : 0 <= lc_F cx / 8 <= lc_F cx) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (GHI : forall a, inG TG.G_HARNESS_B a -> a < TG.G_HARNESS_B_HI)
  by (intros a Ha; exact (proj2 (inG_G_HARNESS_hull a Ha))).
unfold TG.G_HARNESS_B_HI in GHI.
unfold LF_FBYTES in *.
split; [|split].
- intros a Ha Hn. rewrite (K1 a Ha Hn). apply KR; [lia | intros HG; pose proof (GHI a HG); lia].
- intros b m i Hin Hi.
  destruct (al_blocks _ _ LAWS ly' S' W' mem' md' b m HAR Hin) as (_ & H4096 & Hbc & _).
  assert (Hni : ~ in_img segs (b + i)) by exact (blk_img segs B LAWS ly' S' W' mem' md' b m (b + i) HAR Hin ltac:(lia)).
  rewrite (K2 b m i Hin Hi).
  + apply KR; [op5_lia | intros HG; exact (Hni (trans_g_img _ HG))].
  + intros Hw. exact (Hni (trans_g_img _ (HEG _ Hw))).
- intros a Ha.
  assert (HSH : lc_SH cx = SHADOW_OFF + lc_F cx / 8) by reflexivity. unfold SHADOW_OFF in HSH.
  assert (HnG : ~ inG TG.G_HARNESS_B a).
  { intros HG. destruct Ha as [Ha | Ha].
    - apply (frm_img segs B LAWS ly' S' W' mem' md' LF_CID (l_fpos cx) a HAR HFin);
        [rewrite HFaddr; change (fs_frame_bytes LF_CID) with 256; exact Ha | exact (trans_g_img a HG)].
    - pose proof (GHI a HG). lia. }
  rewrite (K4 LF_CID (l_fpos cx) a HFin).
  + apply KR; [destruct Ha; op5_lia | exact HnG].
  + destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd]; rewrite HFaddr.
    * change (fs_frame_bytes LF_CID) with 256. lia.
    * change (fs_frame_bytes LF_CID / 8) with 32. unfold shadow_addr. unfold lc_SH in Ha. lia.
  + intros Hw. exact (HnG (HEG a Hw)).
Qed.

(* The loop's common facts at the next state, from the journal there, the kept registers and the kept bytes. *)
Lemma op5_next : forall cx op ly S (W : world segs) regs mem md e ly2 S2 (W2 : world segs) regs2 mem2 md2 (X : Z),
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx ->
  lc_lcore B MT cx op false false (lo_k op) ly S W regs mem md e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly2 S2 W2 mem2 md2 e ->
  frames S2 = frames S -> Permutation (ablocks B ly2 S2) (ablocks B ly S) ->
  op5_kr regs regs2 -> 0 <= X <= LLVMF_STK - 336 ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - X <= a < lc_sp1 cx) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall b m i, In (b, m) (ablocks B ly S) -> 0 <= i < req_size m ->
     aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W) mem (b + i)) ->
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES \/ lc_SH cx <= a < lc_SH cx + 32 ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  mo_le MT S S2 0 ->
  lc_lcore B MT cx op false false (lo_k op) ly2 S2 W2 regs2 mem2 md2 e.
Proof.
intros cx op ly S W regs mem md e ly2 S2 W2 regs2 mem2 md2 X HP HB HL HJ2 Hfr2 Hperm2 HKR HX KA KB KF HMO.
pose proof (lp_meter_laws _ _ _ _ _ HP) as MTL.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
destruct HL as (HC & (R18 & R26) & HSP & HFSH & HOK & He & (Hmle & Hmok) & R19).
pose proof (lc_geom B MT XL RLO RHI cx ly S W regs mem md e HB HC) as G.
destruct G as [HAR _ Hstk Hsp1c HFaddr HFin Hn HINg _].
destruct Hstk as (Hce & Hslo & Hshi & H47).
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _ & _ & HF4096 & _ & HFce & _).
pose proof asan_consts as ((CVlo & CVhi) & _).
unfold LF_FRAME in Hsp1. change (2 ^ 47) with 140737488355328 in H47.
assert (ELS : LLVMF_STK = 32768) by reflexivity.
split.
{ apply (lc_core_kept_run B MT XL RLO RHI cx ly S W regs mem md e ly2 S2 W2 regs2 mem2 md2 e HB HC HJ2 Hfr2 Hperm2).
  - intros r Hr. apply HKR. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [op5_inl |]). destruct Hr.
  - intros a Ha. apply KA; [op5_lia | lia].
  - intros i Hi. destruct Hn as (Hn1 & _).
    assert (Hn0 : 0 < l_n cx) by lia.
    pose proof (HINg Hn0) as InP. pose proof (req_size_pos (l_n cx) ltac:(lia)) as (Hq1 & Hq2).
    exact (KB _ _ i InP ltac:(lia)).
  - intros a Ha. apply KF. left. unfold LF_FBYTES in *. lia.
  - intros a Ha Hpr. apply (apresent_transfer segs (w_H W) (w_H W2) mem mem2 a).
    + unfold LF_FBYTES in *. op5_lia.
    + apply (frm_img segs B LAWS ly S W mem md LF_CID (l_fpos cx) a HAR HFin).
      rewrite HFaddr. change (fs_frame_bytes LF_CID) with LF_FBYTES. exact Ha.
    + apply KF. left. exact Ha.
    + exact Hpr. }
split; [split; [exact (eq_trans (HKR 18 ltac:(op5_inl)) R18) | exact (eq_trans (HKR 26 ltac:(op5_inl)) R26)]|].
split.
{ apply (lc_spills_kept cx _ (aview segs (w_H W) mem) (aview segs (w_H W2) mem2)); [| |exact HSP].
  - intros o Ho.
    pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES in *; op5_lia)) as SV.
    rewrite Forall_forall in SV. destruct (SV o Ho) as (_ & _ & H8 & H192). lia.
  - intros a Ha. apply KA; [op5_lia | lia]. }
split.
{ apply (lc_fsh_kept cx (aview segs (w_H W) mem)); [|exact HFSH]. intros a Ha. apply KF. right. exact Ha. }
split; [exact HOK|].
split; [exact He|].
split; [split|].
- pose proof (mle_station MT _ _ _ _ _ MTL Hmle HMO) as H. rewrite Z.add_0_r in H. exact H.
- apply (mo_ok_step MT MTL S S2 0); [rewrite Z.add_0_l; exact Hmok | exact HMO].
- exact (eq_trans (HKR 19 ltac:(op5_inl)) R19).
Qed.

(* A cut op5_at from the walk's facts at the next state. *)
Lemma op5_at_intro : forall cx op off Bw (R : bvmap 5 word -> Prop) ly S (W : world segs) regs mem md e
    ly2 S2 (W2 : world segs) regs2 mem2 md2 (X : Z),
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx ->
  lc_lcore B MT cx op false false (lo_k op) ly S W regs mem md e ->
  lc_cur cx regs 24 27 (lc_oc (l_pl cx) (lo_c op)) -> YK11.getr regs 20 = w64 (lc_F cx + 32) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly2 S2 W2 mem2 md2 e ->
  frames S2 = frames S -> Permutation (ablocks B ly2 S2) (ablocks B ly S) ->
  op5_kr regs regs2 -> 0 <= X <= LLVMF_STK - 336 ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - X <= a < lc_sp1 cx) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall b m i, In (b, m) (ablocks B ly S) -> 0 <= i < req_size m ->
     aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W) mem (b + i)) ->
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES \/ lc_SH cx <= a < lc_SH cx + 32 ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  mo_le MT S S2 0 -> lc_tw W2 mem2 Bw -> R regs2 ->
  op5_at cx op off Bw R W2
    (mkCfg (@YK11.mkst (l_fx cx) regs2 (Z_to_bv 64 (BASE + off)) mem2 (YK11.seg_rom segs)) md2).
Proof.
intros cx op off Bw R ly S W regs mem md e ly2 S2 W2 regs2 mem2 md2 X HP HB HL HCUR R20 HJ2 Hfr2 Hperm2 HKR HX
  KA KB KF HMO HTW HR.
exists ly2, S2, regs2, mem2, md2, e.
split; [unfold lc_cfg; rewrite op5_base; reflexivity|].
split; [exact (op5_next cx op ly S W regs mem md e ly2 S2 W2 regs2 mem2 md2 X HP HB HL HJ2 Hfr2 Hperm2 HKR HX
  KA KB KF HMO)|].
split; [exact HTW|].
split; [destruct HCUR as (C24 & C27); split;
  [exact (eq_trans (HKR 24 ltac:(op5_inl)) C24) | exact (eq_trans (HKR 27 ltac:(op5_inl)) C27)]|].
split; [exact (eq_trans (HKR 20 ltac:(op5_inl)) R20) | exact HR].
Qed.

(* +0x7f4 .. +0x808: s6 = OW, a0 = OW, a1 = 0, a2 = 304, `jal __asan_memset`; then the memset (gx_intrin_at). *)
Lemma op5_s1 : forall (cx : lcx) (op : lop) ly' S' (W' : world segs) regs' mem' md' e,
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx ->
  lc_lcore B MT cx op false false (lo_k op) ly' S' W' regs' mem' md' e ->
  lc_tw W' mem' (lo_B op) ->
  lc_cur cx regs' 24 27 (lc_oc (l_pl cx) (lo_c op)) -> YK11.getr regs' 20 = w64 (lc_F cx + 32) ->
  SRr segs W' (lc_cfg cx 2036 regs' mem' md')
    (op5_at cx op 2060 (lc5_Bo (lo_B op)) (fun regs => YK11.getr regs 22 = w64 TB_OW)).
Proof.
intros cx op ly' S' W' regs' mem' md' e HP HB HL Htw HCUR R20.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (lp_meter_laws _ _ _ _ _ HP) as MTL.
pose proof HL as (HC & _).
pose proof HC as (HJ & _ & _ & _ & Rsp & _ & _ & Rgp & Rtp & _).
destruct (op5_sp cx ly' S' W' regs' mem' md' e HB HC) as (Hsp1c & Hsp1 & Hsp0 & Ho16 & H16 & CVlo & CVhi).
unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (transportb_text + 2036)) mem'
    (YK11.seg_rom segs)) md') Q) end.
rewrite <- op5_base.
pose proof (op5_entry (fx := l_fx cx) W' regs' [] mem' 2036) as HS.
pose proof (op5_img regs' []) as HEI.
assert (SHOK : sh_ok segs op5_Bx (@nil shent) (op5_Ex regs' []) (mrestrict (w_H W') mem')) by constructor.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
paj_run_tok RUN HS HJ SHOK op5_B0.
{ op5_awr. }
op5_keep_tac HFr KR W' mem' ms.
clear HF HFr HG.
pmkst HS.
op5_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 2060)) Q1 ltac:(apply codeptr_val; exact HEI).
op5_reg HS (10%bv : bv 5) (w64 TB_OW) Q10
  ltac:(apply op5_sv_obj; [unfold A_TEXT, A_LIM; lia | exact (proj1 (proj2 (proj2 op5_vals))) | unfold TB_OW; op5_lia]).
op5_reg HS (11%bv : bv 5) (w64 0) Q11 ltac:(reflexivity).
op5_reg HS (12%bv : bv 5) (w64 304) Q12 ltac:(reflexivity).
op5_reg HS (22%bv : bv 5) (w64 TB_OW) Q22
  ltac:(apply op5_sv_obj; [unfold A_TEXT, A_LIM; lia | exact (proj1 (proj2 (proj2 op5_vals))) | unfold TB_OW; op5_lia]).
assert (HK1 : op5_kr regs' (ms_regs ms)) by op5_kr_tac HS regs'.
assert (Rsp1 : YK11.getr (ms_regs ms) (Z_to_bv 5 2) = w64 (lc_sp1 cx)) by exact (eq_trans (HK1 2 ltac:(op5_inl)) Rsp).
assert (QSP : spZ (ms_regs ms) = lc_sp1 cx).
{ unfold spZ. transitivity (bv_unsigned (Z_to_bv 64 (lc_sp1 cx))); [f_equal; exact Rsp1|].
  apply unsigned_lit_small. op5_lia. }
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
destruct (lc5_sh_OW B (lp_recv_cells _ _ _ _ _ HP) ly' S' W' (ms_mem ms) _ HAR1) as [HRA HHULL].
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transportb_sigma TB___asan_memset)) mm rom) mdx) Qx)
end.
eapply SRr_bind.
{ apply (@gx_intrin_at (l_fx cx) rc tfib_sink_head segs B LAWS transportb_segs_low OSet
    (transportb_sigma TB___asan_memset) (lp_memset _ _ _ _ _ HP (l_fx cx)) TG.G_HARNESS_B W' (ms_regs ms) (ms_mem ms)
    _ _ _ _ _ _ _ _ _ ly' S' _ e TB_OW 0 304 (lc_sp1 cx - lc_sp0 cx) (Z_to_bv 64 (BASE + 2060)) HGX G_HARNESS_B_rw
    HJ Q10 Q11 Q12).
  - op5_lia.
  - unfold TB_OW. lia.
  - unfold TB_OW. op5_lia.
  - rewrite QSP. lia.
  - exact Ho16.
  - lia.
  - unfold ESTACK, LLVMF_STK. lia.
  - exact (eq_trans (HK1 3 ltac:(op5_inl)) Rgp).
  - exact (eq_trans (HK1 4 ltac:(op5_inl)) Rtp).
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [op5_lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. intros a Ha. right. apply op5_inG_OW. lia.
  - left. unfold kLowMemEnd, TB_OW. lia.
  - exact HRA.
  - intros _. exact HHULL.
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hset2 & Heff2 & Hgr2).
assert (KRw : forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS_B a -> ~ (lc_sp1 cx - 4096 <= a < lc_sp1 cx) ->
  aview segs (w_H W') mem2 a = aview segs (w_H W') mem' a).
{ intros a Ha HnG Hw.
  rewrite (Heff2 a Ha ltac:(intros Hd; apply HnG; apply op5_inG_OW; lia) ltac:(unfold ESTACK; lia)).
  exact (KR a Ha). }
destruct (op5_kept_g cx ly' S' W' regs' mem' md' e mem2 4096 LAWS HB HC ltac:(unfold LLVMF_STK; lia) KRw)
  as (KA & KB & KF).
apply SRr_ret.
apply (op5_at_intro cx op 2060 (lc5_Bo (lo_B op)) _ ly' S' W' regs' mem' md' e ly' S' W' regs2 mem2 md2 4096
  HP HB HL HCUR R20 HJ2 eq_refl (Permutation_refl _) (op5_kr_trans _ _ _ HK1 (op5_kr_pres _ _ HP2))
  ltac:(unfold LLVMF_STK; lia) KA KB KF (mle_start MT S' MTL)).
- unfold lc_tw, lc5_Bo.
  apply (lc5_w_set (aview segs (w_H W') mem') _ (lo_B op) TW.OFF_OW TB_OW TW.SZ_OW Htw TMAP_B_OW).
  + unfold TW.SZ_OW. lia.
  + intros i Hi. exact (Hset2 i Hi).
  + intros x Hx Hn. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    rewrite (Heff2 x ltac:(op5_lia) Hn ltac:(unfold ESTACK; lia)). exact (KR x ltac:(op5_lia)).
- cbv beta. exact (eq_trans (HP2 22 ltac:(unfold acallee_saved; lia)) Q22).
Qed.

(* +0x80c .. +0x81c: a0 = GOT, a2 = 224, a1 = 0, `jal __asan_memset`; then the memset (gx_intrin_at). *)
Lemma op5_s2 : forall (cx : lcx) (op : lop) (W : world segs) (c : config),
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx ->
  op5_at cx op 2060 (lc5_Bo (lo_B op)) (fun regs => YK11.getr regs 22 = w64 TB_OW) W c ->
  SRr segs W c (op5_at cx op 2080 (lc5_Bm (lo_B op)) (fun regs => YK11.getr regs 22 = w64 TB_OW)).
Proof.
intros cx op W c HP HB HAT.
destruct HAT as (ly' & S' & regs' & mem' & md' & e & Hc & HL & Htw & HCUR & R20 & R22). subst c.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (lp_meter_laws _ _ _ _ _ HP) as MTL.
pose proof HL as (HC & _).
pose proof HC as (HJ & _ & _ & _ & Rsp & _ & _ & Rgp & Rtp & _).
destruct (op5_sp cx ly' S' W regs' mem' md' e HB HC) as (Hsp1c & Hsp1 & Hsp0 & Ho16 & H16 & CVlo & CVhi).
unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (transportb_text + 2060)) mem'
    (YK11.seg_rom segs)) md') Q) end.
rewrite <- op5_base.
pose proof (op5_entry (fx := l_fx cx) W regs' [] mem' 2060) as HS.
pose proof (op5_img regs' []) as HEI.
assert (SHOK : sh_ok segs op5_Bx (@nil shent) (op5_Ex regs' []) (mrestrict (w_H W) mem')) by constructor.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
paj_run_tok RUN HS HJ SHOK op5_B0.
{ op5_awr. }
op5_keep_tac HFr KR W mem' ms.
clear HF HFr HG.
pmkst HS.
op5_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 2080)) Q1 ltac:(apply codeptr_val; exact HEI).
op5_reg HS (10%bv : bv 5) (w64 TB_GOT) Q10
  ltac:(apply op5_sv_obj; [unfold A_TEXT, A_LIM; lia | exact (proj2 (proj2 (proj2 op5_vals))) | unfold TB_GOT; op5_lia]).
op5_reg HS (11%bv : bv 5) (w64 0) Q11 ltac:(reflexivity).
op5_reg HS (12%bv : bv 5) (w64 224) Q12 ltac:(reflexivity).
assert (HK1 : op5_kr regs' (ms_regs ms)) by op5_kr_tac HS regs'.
assert (Q22 : YK11.getr (ms_regs ms) (Z_to_bv 5 22) = YK11.getr regs' (Z_to_bv 5 22)) by op5_kreg HS regs'.
assert (Rsp1 : YK11.getr (ms_regs ms) (Z_to_bv 5 2) = w64 (lc_sp1 cx)) by exact (eq_trans (HK1 2 ltac:(op5_inl)) Rsp).
assert (QSP : spZ (ms_regs ms) = lc_sp1 cx).
{ unfold spZ. transitivity (bv_unsigned (Z_to_bv 64 (lc_sp1 cx))); [f_equal; exact Rsp1|].
  apply unsigned_lit_small. op5_lia. }
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
destruct (lc5_sh_GOT B (lp_recv_cells _ _ _ _ _ HP) ly' S' W (ms_mem ms) _ HAR1) as [HRA HHULL].
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transportb_sigma TB___asan_memset)) mm rom) mdx) Qx)
end.
eapply SRr_bind.
{ apply (@gx_intrin_at (l_fx cx) rc tfib_sink_head segs B LAWS transportb_segs_low OSet
    (transportb_sigma TB___asan_memset) (lp_memset _ _ _ _ _ HP (l_fx cx)) TG.G_HARNESS_B W (ms_regs ms) (ms_mem ms)
    _ _ _ _ _ _ _ _ _ ly' S' _ e TB_GOT 0 224 (lc_sp1 cx - lc_sp0 cx) (Z_to_bv 64 (BASE + 2080)) HGX G_HARNESS_B_rw
    HJ Q10 Q11 Q12).
  - op5_lia.
  - unfold TB_GOT. lia.
  - unfold TB_GOT. op5_lia.
  - rewrite QSP. lia.
  - exact Ho16.
  - lia.
  - unfold ESTACK, LLVMF_STK. lia.
  - exact (eq_trans (HK1 3 ltac:(op5_inl)) Rgp).
  - exact (eq_trans (HK1 4 ltac:(op5_inl)) Rtp).
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [op5_lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. intros a Ha. right. apply op5_inG_GOT. lia.
  - left. unfold kLowMemEnd, TB_GOT. lia.
  - exact HRA.
  - intros _. exact HHULL.
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hset2 & Heff2 & Hgr2).
assert (KRw : forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS_B a -> ~ (lc_sp1 cx - 4096 <= a < lc_sp1 cx) ->
  aview segs (w_H W) mem2 a = aview segs (w_H W) mem' a).
{ intros a Ha HnG Hw.
  rewrite (Heff2 a Ha ltac:(intros Hd; apply HnG; apply op5_inG_GOT; lia) ltac:(unfold ESTACK; lia)).
  exact (KR a Ha). }
destruct (op5_kept_g cx ly' S' W regs' mem' md' e mem2 4096 LAWS HB HC ltac:(unfold LLVMF_STK; lia) KRw)
  as (KA & KB & KF).
apply SRr_ret.
apply (op5_at_intro cx op 2080 (lc5_Bm (lo_B op)) _ ly' S' W regs' mem' md' e ly' S' W regs2 mem2 md2 4096
  HP HB HL HCUR R20 HJ2 eq_refl (Permutation_refl _) (op5_kr_trans _ _ _ HK1 (op5_kr_pres _ _ HP2))
  ltac:(unfold LLVMF_STK; lia) KA KB KF (mle_start MT S' MTL)).
- unfold lc_tw, lc5_Bm.
  apply (lc5_w_set (aview segs (w_H W) mem') _ (lc5_Bo (lo_B op)) TW.OFF_GOT TB_GOT TW.SZ_GOT Htw TMAP_B_GOT).
  + unfold TW.SZ_GOT. lia.
  + intros i Hi. exact (Hset2 i Hi).
  + intros x Hx Hn. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    rewrite (Heff2 x ltac:(op5_lia) Hn ltac:(unfold ESTACK; lia)). exact (KR x ltac:(op5_lia)).
- cbv beta. exact (eq_trans (HP2 22 ltac:(unfold acallee_saved; lia)) (eq_trans Q22 R22)).
Qed.

(* The awr obligation of the stretch +0x820: three regions with no window, then M.fail and OW.desk_off, bytes of G. *)
Ltac op5_c_awr U249 U22 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  do 3 (apply awr_ok_x_cons;
        [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; exfalso; lia |]);
  apply awr_ok_x_cons_g;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U249 in Ha; apply op5_inG_M; lia |];
  apply awr_ok_x_cons_g;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U22 in Ha; apply op5_inG_OW; lia |];
  apply awr_ok_x_nil.

(* +0x820 .. +0x838: the byte g_fail_next, OW.desk_off := -1, M.fail := the byte (op_begin's world), `jal m_wake`;
   then m_wake (lp_mwake, a G-form callee). *)
Lemma op5_s3 : forall (cx : lcx) (op : lop) (B2 : list byte) (want : Z) (W : world segs) (c : config),
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx ->
  TC.m_wake_m (lc5_B1 (lo_B op)) = Some (B2, want) ->
  op5_at cx op 2080 (lc5_Bm (lo_B op)) (fun regs => YK11.getr regs 22 = w64 TB_OW) W c ->
  SRr segs W c (op5_at cx op 2108 B2 (fun regs => YK11.getr regs 10 = w64 want)).
Proof.
intros cx op B2 want W c HP HB Hm HAT.
destruct HAT as (ly' & S' & regs' & mem' & md' & e & Hc & HL & HTW & HCUR & R20 & R22). subst c.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (lp_meter_laws _ _ _ _ _ HP) as MTL.
pose proof HL as (HC & _ & HSP & _ & (HAG & _) & _).
pose proof HC as (HJ & Hfrs & _ & _ & Rsp & _ & R9 & Rgp & Rtp & _ & Hsp1al & _).
destruct (op5_sp cx ly' S' W regs' mem' md' e HB HC) as (Hsp1c & Hsp1 & Hsp0 & Ho16 & H16 & CVlo & CVhi).
pose proof (op5_ev cx op ly' S' W regs' mem' md' e HB HL) as Hev.
pose proof (TIR.len_w _ (AG.ac_len _ _ _ (AG.ag_core _ _ _ HAG))) as HLB.
assert (XS : 0 <= MWAKE_STK <= LLVMF_STK - 336) by (split; vm_compute; intros Hx; discriminate Hx).
(* the spill slots of g_fail_next's page and of M *)
assert (HSP184 : rdword (aview segs (w_H W) mem') (lc_sp1 cx + 184) = Some (transportb_hi 10)).
{ unfold lc_spills in HSP. rewrite Forall_forall in HSP.
  exact (HSP (184, transportb_hi 10) ltac:(unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm;
    cbn [app In]; repeat first [left; reflexivity | right])). }
assert (HSP168 : rdword (aview segs (w_H W) mem') (lc_sp1 cx + 168) = Some TB_M).
{ unfold lc_spills in HSP. rewrite Forall_forall in HSP.
  exact (HSP (168, TB_M) ltac:(unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm;
    cbn [app In]; repeat first [left; reflexivity | right])). }
unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (transportb_text + 2080)) mem'
    (YK11.seg_rom segs)) md') Q) end.
rewrite <- op5_base.
pose proof (op5_c_entry (fx := l_fx cx) W regs' mem' (lc5_Bm (lo_B op)) (lc_sp1 cx) R9 R22 ltac:(lia) ltac:(lia)
  Hsp1al HSP184 HSP168 HTW) as HS.
set (E0 := op5_Ex regs' [Z_to_bv 64 (TW.u_at (lc5_Bm (lo_B op)) TW.OFF_g_fail_next 1)]) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply op5_img).
assert (SHOK : sh_ok segs op5_Bx (@nil shent) E0 (mrestrict (w_H W) mem')) by constructor.
assert (U22 : bv_unsigned (ew E0 22%nat) = TB_OW)
  by (unfold E0; exact (op5_U regs' _ 22 (Z_to_bv 5 22) TB_OW eq_refl R22 ltac:(unfold TB_OW; op5_lia))).
assert (U249 : bv_unsigned (ew E0 249%nat) = TB_M) by (unfold E0; apply op5_U249).
assert (E32 : ew E0 32 = Z_to_bv 64 (TW.u_at (lc5_Bm (lo_B op)) TW.OFF_g_fail_next 1)) by (unfold E0; apply op5_ex32).
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
paj_run_tok RUN HS HJ SHOK op5_B0.
{ op5_c_awr U249 U22. }
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ ((TB_OW + 232 <= a < TB_OW + 236) \/ (TB_M + 88 <= a < TB_M + 92)) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem' a).
{ intros a Ha Hn.
  apply (YC4b.kept_of_frame _ _ _ _ _ (fun x => (TB_OW + 232 <= x < TB_OW + 236) \/ (TB_M + 88 <= x < TB_M + 92)) HFr);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. op5_win Hin Hx ltac:(rewrite ?U22, ?U249 in Hx; lia). }
clear HF HFr HG.
(* the two stored fields *)
pose proof (YC4b.st_ok_region_nth E0 _ _ 3%nat _ HS eq_refl) as RG3. cbn [ms_mem restrict] in RG3.
pose proof (YC4b.st_ok_region_nth E0 _ _ 4%nat _ HS eq_refl) as RG4. cbn [ms_mem restrict] in RG4.
assert (DG : sv_denot E0 (SOff 32 0) = Z_to_bv 64 (TW.g_fail_next (lc5_B3 (lo_B op)))).
{ cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned, (lc5_gfn _ HLB). reflexivity. }
assert (DM1 : sv_denot E0 (SLit 18446744073709551615) = Z_to_bv 64 (-1)) by (apply bv_eq; reflexivity).
pose proof (op5_chunk _ _ _ _ _ _ _ _ _ TB_M 88 (SOff 32 0) _ RG3 U249 ltac:(cbn [In]; tauto) DG) as VF.
pose proof (op5_chunk _ _ _ _ _ _ _ _ _ TB_OW 232 (SLit 18446744073709551615) (-1) RG4 U22
  ltac:(cbn [In]; tauto) DM1) as VD.
clear RG3 RG4.
(* op_begin's world at the call memory *)
assert (HTWF : lc_tw W (ms_mem ms) (lc5_B1 (lo_B op))).
{ unfold lc_tw. apply (lc5_w_c1 (lo_B op) (aview segs (w_H W) mem') _ HTW VD VF).
  intros x Hx N1 N2. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
  apply KR1; [op5_lia | intros [H1 | H1]; [exact (N1 H1) | exact (N2 H1)]]. }
clear VD VF.
pmkst HS.
op5_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 2108)) Q1 ltac:(apply codeptr_val; exact HEI).
subst E0.
assert (HK1 : op5_kr regs' (ms_regs ms)) by op5_kr_tac HS regs'.
destruct (op5_callpre cx ly' S' W regs' mem' md' e (ms_regs ms) 2108 MWAKE_STK HB HC HK1 Q1 ltac:(op5_lia)
  eq_refl XS) as (Hret & Hra & Rgp' & Rtp' & QSP & Hsp16 & Hlo & Hhi).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at (l_fx cx) sg (transportb_sigma TB_m_wake) rg mm mdx) Q) end.
eapply SRr_bind.
{ exact (lp_mwake _ _ _ _ _ HP (l_fx cx) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_regs ms) (lc5_B1 (lo_B op)) B2 want
    HJ Hret Hra Rgp' Rtp' Hsp16 Hlo Hhi HTWF Hm ltac:(unfold MWAKE_EV, MSET_EV; lia)). }
cbv beta. intros W2 c2 _ HQ.
unfold transport_mwake_post, transport_cg_post in HQ.
destruct HQ as (ly2 & S2 & regs2 & mem2 & md2 & e2 & Hc2 & He2 & HJ2 & HP2 & Hfr2 & Hperm2 & HK2 & Hmo2 &
  (HA0 & HTW2)).
assert (Ee2 : e2 = 0) by (unfold MWAKE_EV, MSET_EV in He2; lia). subst e2. rewrite Z.add_0_r in HJ2.
rewrite Q1 in Hc2. subst c2. rewrite QSP in HK2.
destruct (op5_kept cx ly' S' W regs' mem' md' e (ms_mem ms) W2 mem2 MWAKE_STK (mwake_wr (lc5_B1 (lo_B op)))
  LAWS HB HC XS
  ltac:(intros a Ha HnG; apply KR1; [exact Ha | intros [H1 | H1]; apply HnG; [apply op5_inG_OW | apply op5_inG_M]; lia])
  (op5_mwake_wr_G _) HK2) as (KA & KB & KF).
apply SRr_ret.
exact (op5_at_intro cx op 2108 B2 _ ly' S' W regs' mem' md' e ly2 S2 W2 regs2 mem2 md2 MWAKE_STK HP HB HL HCUR R20
  HJ2 Hfr2 Hperm2 (op5_kr_trans _ _ _ HK1 (op5_kr_pres _ _ HP2)) XS KA KB KF Hmo2 HTW2 HA0).
Qed.

(* +0x83c .. +0x850: a1 = g_now (through the spill slot 152(s1)), s6 = a0 (m_wake's code), a0 = g_s,
   `jal diginet_session_wake`; then the wake (lp_wake, a G-form callee) at TF = None. *)
Lemma op5_s4 : forall (cx : lcx) (op : lop) (B2 B3 : list byte) (want rcv : Z) (W : world segs) (c : config),
  lc_rom_view_stmt B MT XL RLO RHI ->
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx ->
  TRI.run_inv B2 -> TW.g_fail_next B2 <= 1 ->
  TSS.diginet_session_wake_m timg_B None B2 (TW.g_now B2) = Some (B3, rcv) ->
  op5_at cx op 2108 B2 (fun regs => YK11.getr regs 10 = w64 want) W c ->
  SRr segs W c (op5_at cx op 2132 B3 (fun regs => YK11.getr regs 10 = w64 rcv /\ YK11.getr regs 22 = w64 want)).
Proof.
intros cx op B2 B3 want rcv W c HK1R HP HB HRI Hgf Mw HAT.
destruct HAT as (ly' & S' & regs' & mem' & md' & e & Hc & HL & HTW & HCUR & R20 & R10). subst c.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (lp_meter_laws _ _ _ _ _ HP) as MTL.
pose proof HL as (HC & _ & HSP & _).
pose proof HC as (HJ & Hfrs & _ & _ & Rsp & _ & R9 & Rgp & Rtp & _).
destruct (op5_sp cx ly' S' W regs' mem' md' e HB HC) as (Hsp1c & Hsp1 & Hsp0 & Ho16 & H16 & CVlo & CVhi).
pose proof (op5_ev cx op ly' S' W regs' mem' md' e HB HL) as Hev.
pose proof (HK1R HP cx ly' S' W regs' mem' md' e HB HC) as HROM.
destruct HRI as (I1 & _ & I4 & _).
assert (XS : 0 <= WAKE_STK <= LLVMF_STK - 336) by (split; vm_compute; intros Hx; discriminate Hx).
set (nw := TW.g_now B2) in *.
assert (RNW : 0 <= nw < 2 ^ 64).
{ unfold nw, TW.g_now. pose proof (TWL.u_at_range B2 TW.OFF_g_now 8) as Hr.
  change (8 * Z.of_nat 8) with 64 in Hr. exact Hr. }
assert (HSP152 : rdword (aview segs (w_H W) mem') (lc_sp1 cx + 152) = Some (transportb_hi 9)).
{ unfold lc_spills in HSP. rewrite Forall_forall in HSP.
  exact (HSP (152, transportb_hi 9) ltac:(unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm;
    cbn [app In]; repeat first [left; reflexivity | right])). }
assert (HNOW : val_mem segs (mrestrict (w_H W) mem') TB_g_now 8 nw).
{ pose proof (tw_read_val segs _ TMAP_B B2 TW.OFF_g_now TB_g_now TW.SZ_g_now 0 8 TMAP_B_ok HTW
    TMAP_B_g_now ltac:(lia) ltac:(unfold TW.SZ_g_now; lia)) as Hv.
  rewrite !Z.add_0_r in Hv. exact Hv. }
unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (transportb_text + 2108)) mem'
    (YK11.seg_rom segs)) md') Q) end.
rewrite <- op5_base.
pose proof (op5_d_entry (fx := l_fx cx) W regs' mem' (lc_sp1 cx) nw R9 ltac:(lia) ltac:(lia) HSP152 HNOW RNW) as HS.
pose proof (op5_img regs' [w64 nw]) as HEI.
assert (SHOK : sh_ok segs op5_Bx (@nil shent) (op5_Ex regs' [w64 nw]) (mrestrict (w_H W) mem')) by constructor.
assert (E32 : ew (op5_Ex regs' [w64 nw]) 32 = w64 nw) by apply op5_ex32.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
paj_run_tok RUN HS HJ SHOK op5_B0.
{ op5_awr. }
op5_keep_tac HFr KR W mem' ms.
clear HF HFr HG.
pmkst HS.
op5_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 2132)) Q1 ltac:(apply codeptr_val; exact HEI).
op5_reg HS (10%bv : bv 5) (w64 WAKE_S) Q10
  ltac:(apply op5_sv_obj; [unfold A_TEXT, A_LIM; lia | exact (proj1 (proj2 op5_vals)) | unfold WAKE_S, TB_g_s; op5_lia]).
op5_reg HS (11%bv : bv 5) (w64 nw) Q11
  ltac:(cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
op5_reg HS (22%bv : bv 5) (YK11.getr regs' (Z_to_bv 5 10)) Q22a
  ltac:(cbn [sv_denot]; rewrite (op5_ew regs' _ 10 (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
assert (HK1 : op5_kr regs' (ms_regs ms)) by op5_kr_tac HS regs'.
destruct (op5_callpre cx ly' S' W regs' mem' md' e (ms_regs ms) 2132 WAKE_STK HB HC HK1 Q1 ltac:(op5_lia)
  eq_refl XS) as (Hret & Hra & Rgp' & Rtp' & QSP & Hsp16 & Hlo & Hhi).
assert (TW1 : tw_at TMAP_B (aview segs (w_H W) (ms_mem ms)) B2).
{ apply (tw_kept TMAP_B (aview segs (w_H W) mem')); [exact HTW|].
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
  apply KR. op5_lia. }
assert (ROM1 : trans_rom_view_rd W (ms_mem ms)).
{ intros a Ha. rewrite KR by (pose proof (trans_ro_rd_bounds a Ha); op5_lia). exact (HROM a Ha). }
assert (C1 : count_cid WAKE_CID (frames S') < fs_frames WAKE_CID) by (rewrite Hfrs; vm_compute; reflexivity).
assert (C2 : count_cid SENDCTL_CID (frames S') + 1 < fs_frames SENDCTL_CID)
  by (rewrite Hfrs; vm_compute; reflexivity).
assert (EV0 : WAKE_EV = 0) by reflexivity.
assert (Hap : wake_apart None B2) by (intros x _ fr Hfr; discriminate Hfr).
assert (Htf : trans_tf_off_g None) by (intros fr Hfr; discriminate Hfr).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at (l_fx cx) sg (transportb_sigma TB_diginet_session_wake) rg mm mdx) Q) end.
eapply SRr_bind.
{ exact (lp_wake _ _ _ _ _ HP (l_fx cx) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_regs ms) nw rcv None B2 B3
    HJ Hret Hra Rgp' Rtp' Q10 Q11 Hsp16 Hlo Hhi RNW TW1 Hgf Mw I Htf ROM1 Hap I1 I4 C1 C2
    ltac:(rewrite EV0; lia)). }
cbv beta. intros W2 c2 _ HQ.
unfold transport_wake_post, transport_cg_post in HQ.
destruct HQ as (ly2 & S2 & regs2 & mem2 & md2 & e2 & Hc2 & He2 & HJ2 & HP2 & Hfr2 & Hperm2 & HK2 & Hmo2 &
  (HA0 & HTW2 & _)).
assert (Ee2 : e2 = 0) by (rewrite EV0 in He2; lia). subst e2. rewrite Z.add_0_r in HJ2.
rewrite Q1 in Hc2. subst c2. rewrite QSP in HK2.
destruct (op5_kept cx ly' S' W regs' mem' md' e (ms_mem ms) W2 mem2 WAKE_STK (wake_wr B2) LAWS HB HC XS
  ltac:(intros a Ha _; exact (KR a Ha)) (op5_wake_wr_G _) HK2) as (KA & KB & KF).
apply SRr_ret.
apply (op5_at_intro cx op 2132 B3 _ ly' S' W regs' mem' md' e ly2 S2 W2 regs2 mem2 md2 WAKE_STK HP HB HL HCUR R20
  HJ2 Hfr2 Hperm2 (op5_kr_trans _ _ _ HK1 (op5_kr_pres _ _ HP2)) XS KA KB KF Hmo2 HTW2).
cbv beta. split; [exact HA0|].
exact (eq_trans (HP2 22 ltac:(unfold acallee_saved; lia)) (eq_trans Q22a R10)).
Qed.

(* A leaf called from the walk's G journal, through the unit's leaf bridge (DgnTransportBLeafb.v
   decode_leafb_journal) and TransportGCg.v gx_call_leaf: the world and the journal kept, the callee-saved registers
   kept, every byte outside the leaf's stack window kept, presence kept, and the leaf's X. *)
Lemma op5_leaf : forall (fx : YK11.FPState) (W : world segs) (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md
    own lyc Sc mdc k (o PC : Z) (X : (word -> option byte) -> Prop),
  AR_laws segs B ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  YK0s.ret_ok (YK11.getr regsT 1) -> YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  (@decode_leafb_ecall_pre rc B lyc Sc W regsT memT mdc ->
     SRr segs W (@O5LCK.cfg_at fx PC regsT memT mdc) (@decode_leafb_post fx rc B lyc Sc W regsT memT mdc None [] X)) ->
  SRr segs W (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 PC) memT (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
      c2 = mkCfg (@YK11.mkst fx regs2 (YK11.getr regsT 1) mem2 (YK11.seg_rom segs)) md2 /\
      @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W mem2
        md2 k /\
      aregs_preserved regsT regs2 /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
         aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
      (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\ X mem2).
Proof.
  intros fx W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o PC X LAWS HJ Hsp Hal Hneg Hbud Hra Hgp Htp HLEAF.
  apply (@gx_call_leaf fx rc tfib_sink_head segs B TG.G_HARNESS_B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k _
    (YK11.getr regsT 1)
    (fun regs2 mem2 md2 => aregs_preserved regsT regs2 /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
         aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
      (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\ X mem2) HJ).
  intros memS HJi.
  eapply SRr_mono.
  { apply (@decode_leafb_journal fx rc tfib_sink_head B LAWS W regsT memT STK sp0 FP ly S W0 memS md own lyc Sc mdc k
      o PC None [] X HJi Hsp Hal Hneg Hbud Hra Hgp Htp).
    - intros a Ha. unfold O5LCK.in_wr in Ha. inversion Ha.
    - exact HLEAF. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & Ec & HJ2 & HP & _ & Heff & Hgr & HX).
  split; [reflexivity|]. exists regs2, mem2, md2. split; [exact Ec|]. split; [exact HJ2|].
  split; [exact HP|].
  split; [intros a Ha Hn; exact (Heff a Ha Hn ltac:(intros Hw; unfold O5LCK.in_wr in Hw; inversion Hw))|].
  split; [exact Hgr | exact HX].
Qed.

(* +0x854 .. +0x85c: a1 = s6 (want), s6 = 1, `jal check_state_wake_code` (a0 = rc); then the leaf (lp_cswc). *)
Lemma op5_s5 : forall (cx : lcx) (op : lop) (B3 : list byte) (rcv want : Z) (W : world segs) (c : config),
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx ->
  - 2 ^ 31 <= rcv < 2 ^ 31 -> - 2 ^ 31 <= want < 2 ^ 31 ->
  TC.check_state_wake_code_m B3 rcv want = Some (B3, tt) ->
  op5_at cx op 2132 B3 (fun regs => YK11.getr regs 10 = w64 rcv /\ YK11.getr regs 22 = w64 want) W c ->
  SRr segs W c (op5_at cx op 2144 B3 (fun regs => YK11.getr regs 22 = w64 1)).
Proof.
intros cx op B3 rcv want W c HP HB Hrc Hwt Mc HAT.
destruct HAT as (ly' & S' & regs' & mem' & md' & e & Hc & HL & HTW & HCUR & R20 & (R10 & R22)). subst c.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (lp_meter_laws _ _ _ _ _ HP) as MTL.
pose proof HL as (HC & _).
pose proof HC as (HJ & _ & _ & _ & Rsp & _ & _ & Rgp & Rtp & _).
destruct (op5_sp cx ly' S' W regs' mem' md' e HB HC) as (Hsp1c & Hsp1 & Hsp0 & Ho16 & H16 & CVlo & CVhi).
unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (transportb_text + 2132)) mem'
    (YK11.seg_rom segs)) md') Q) end.
rewrite <- op5_base.
pose proof (op5_entry (fx := l_fx cx) W regs' [] mem' 2132) as HS.
pose proof (op5_img regs' []) as HEI.
assert (SHOK : sh_ok segs op5_Bx (@nil shent) (op5_Ex regs' []) (mrestrict (w_H W) mem')) by constructor.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
paj_run_tok RUN HS HJ SHOK op5_B0.
{ op5_awr. }
op5_keep_tac HFr KR W mem' ms.
clear HF HFr HG.
pmkst HS.
op5_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 2144)) Q1 ltac:(apply codeptr_val; exact HEI).
op5_reg HS (10%bv : bv 5) (YK11.getr regs' (Z_to_bv 5 10)) Q10a
  ltac:(cbn [sv_denot]; rewrite (op5_ew regs' _ 10 (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
op5_reg HS (11%bv : bv 5) (YK11.getr regs' (Z_to_bv 5 22)) Q11a
  ltac:(cbn [sv_denot]; rewrite (op5_ew regs' _ 22 (Z_to_bv 5 22) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
op5_reg HS (22%bv : bv 5) (w64 1) Q22 ltac:(reflexivity).
assert (HK1 : op5_kr regs' (ms_regs ms)) by op5_kr_tac HS regs'.
assert (Q10 : YK11.getr (ms_regs ms) (Z_to_bv 5 10) = Z_to_bv 64 rcv) by exact (eq_trans Q10a R10).
assert (Q11 : YK11.getr (ms_regs ms) (Z_to_bv 5 11) = Z_to_bv 64 want) by exact (eq_trans Q11a R22).
destruct (op5_callpre cx ly' S' W regs' mem' md' e (ms_regs ms) 2144 4096 HB HC HK1 Q1 ltac:(op5_lia) eq_refl
  ltac:(unfold LLVMF_STK; lia)) as (Hret & Hra & Rgp' & Rtp' & QSP & Hsp16 & Hlo & Hhi).
assert (USP : bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = lc_sp1 cx).
{ transitivity (bv_unsigned (Z_to_bv 64 (lc_sp1 cx))); [f_equal; exact (eq_trans (HK1 2 ltac:(op5_inl)) Rsp)|].
  apply unsigned_lit_small. op5_lia. }
destruct (gx_open segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJd & _ & _).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 O5CWC.CHECK_STATE_WAKE_CODE) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (op5_leaf (l_fx cx) W (ms_regs ms) (ms_mem ms) LLVMF_STK (lc_sp0 cx) [] (l_ly cx) (l_S cx) (l_W cx)
    (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly' S' _ e (lc_sp1 cx - lc_sp0 cx) O5CWC.CHECK_STATE_WAKE_CODE
    (fun _ => B3 = B3) LAWS HJ).
  - rewrite QSP. ring.
  - exact Ho16.
  - lia.
  - unfold ESTACK, LLVMF_STK. lia.
  - exact Hret.
  - exact Rgp'.
  - exact Rtp'.
  - intros HPRE.
    pose proof (lp_cswc B MT XL RLO RHI HP (l_fx cx)) as LF.
    unfold transport_leaf_at, O5CWG.transport_check_state_wake_code_cg in LF.
    specialize (LF ly' S' W (ms_regs ms) (ms_mem ms) _ (lc_sp1 cx - ESTACK) B3 B3 rcv want HPRE).
    cbv zeta in LF.
    apply LF; clear LF.
    + exact Q10.
    + exact Q11.
    + exact Hrc.
    + exact Hwt.
    + apply (op5_tw_csw W). apply (tw_kept TMAP_B (aview segs (w_H W) mem')); [exact HTW|].
      intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
      apply KR. op5_lia.
    + exact Mc.
    + rewrite USP.
      exact (decode_leafb_stk_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (lc_sp1 cx - ESTACK) (lc_sp1 cx) HJd
        ltac:(unfold ESTACK, LLVMF_STK; lia) ltac:(lia)).
    + rewrite USP. unfold O5CWC.CHECK_STATE_WAKE_CODE_FRAME, ESTACK. lia.
    + unfold O5KA.off_stk. rewrite USP.
      unfold O5CWC.CHECK_STATE_WAKE_CODE_FRAME, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI. left. lia.
    + rewrite USP. unfold O5CWC.CHECK_STATE_WAKE_CODE_FRAME.
      exact (decode_leafb_rng_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (lc_sp1 cx - 16) 16 HJd
        ltac:(unfold LLVMF_STK; lia) ltac:(lia)). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & Ec3 & HJ3 & HP3 & KE3 & Hgr3 & _).
change (YK11.getr (ms_regs ms) 1) with (YK11.getr (ms_regs ms) 1%bv) in Ec3. rewrite Q1 in Ec3. subst c3.
assert (KRw : forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS_B a -> ~ (lc_sp1 cx - 4096 <= a < lc_sp1 cx) ->
  aview segs (w_H W) mem3 a = aview segs (w_H W) mem' a).
{ intros a Ha _ Hw. rewrite (KE3 a Ha ltac:(rewrite QSP; unfold ESTACK; lia)). exact (KR a Ha). }
destruct (op5_kept_g cx ly' S' W regs' mem' md' e mem3 4096 LAWS HB HC ltac:(unfold LLVMF_STK; lia) KRw)
  as (KA & KB & KF).
apply SRr_ret.
apply (op5_at_intro cx op 2144 B3 _ ly' S' W regs' mem' md' e ly' S' W regs3 mem3 md3 4096
  HP HB HL HCUR R20 HJ3 eq_refl (Permutation_refl _) (op5_kr_trans _ _ _ HK1 (op5_kr_pres _ _ HP3))
  ltac:(unfold LLVMF_STK; lia) KA KB KF (mle_start MT S' MTL)).
- apply (tw_kept TMAP_B (aview segs (w_H W) mem')); [exact HTW|].
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
  rewrite (KE3 x ltac:(op5_lia) ltac:(rewrite QSP; unfold ESTACK; op5_lia)). exact (KR x ltac:(op5_lia)).
- cbv beta. exact (eq_trans (HP3 22 ltac:(unfold acallee_saved; lia)) Q22).
Qed.

(* +0x860: `j +0x900`, the cut SET56: the world of the wake, at which settle 0 answers Some and op 5's equation. *)
Lemma op5_s6 : forall (cx : lcx) (op : lop) (B3 : list byte) (W : world segs) (c : config),
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx ->
  lc_opc (l_pl cx) (lo_c op) = 5 ->
  TC.settle_m B3 0 = Some (B3, tt) ->
  (forall A, TOP.LLVMFuzzerTestOneInput_op_m timg_B (lo_B op) A (l_pl cx) (lo_c op) (lo_k op) =
             Some (B3, (lc_oc (l_pl cx) (lo_c op), lo_k op))) ->
  op5_at cx op 2144 B3 (fun regs => YK11.getr regs 22 = w64 1) W c ->
  SRr segs W c (lc_st_set56 B MT cx op).
Proof.
intros cx op B3 W c HP HB Ho ESET EQOP HAT.
destruct HAT as (ly' & S' & regs' & mem' & md' & e & Hc & HL & HTW & HCUR & R20 & R22). subst c.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (lp_meter_laws _ _ _ _ _ HP) as MTL.
pose proof HL as (HC & _).
pose proof HC as (HJ & _).
unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (transportb_text + 2144)) mem'
    (YK11.seg_rom segs)) md') Q) end.
rewrite <- op5_base.
pose proof (op5_entry (fx := l_fx cx) W regs' [] mem' 2144) as HS.
pose proof (op5_img regs' []) as HEI.
assert (SHOK : sh_ok segs op5_Bx (@nil shent) (op5_Ex regs' []) (mrestrict (w_H W) mem')) by constructor.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
paj_run_to_tok RUNTO HS HJ SHOK op5_B0 2304.
{ op5_awr. }
op5_keep_tac HFr KR W mem' ms.
clear HF HFr HG.
assert (HK1 : op5_kr regs' (ms_regs ms)) by op5_kr_tac HS regs'.
assert (Q22 : YK11.getr (ms_regs ms) (Z_to_bv 5 22) = YK11.getr regs' (Z_to_bv 5 22)) by op5_kreg HS regs'.
destruct (op5_kept_g cx ly' S' W regs' mem' md' e (ms_mem ms) 0 LAWS HB HC ltac:(unfold LLVMF_STK; lia)
  ltac:(intros a Ha _ _; exact (KR a Ha))) as (KA & KB & KF).
pmkst HS.
apply SRr_ret.
lazymatch goal with |- context [mkCfg _ ?mdx] => exists ly', S', (ms_regs ms), (ms_mem ms), mdx, e, B3 end.
split; [unfold lc_cfg, LO_SET56; rewrite op5_base; reflexivity|].
split; [left; exact Ho|].
split; [exact (op5_next cx op ly' S' W regs' mem' md' e ly' S' W (ms_regs ms) (ms_mem ms) _ 0 HP HB HL HJ eq_refl
  (Permutation_refl _) HK1 ltac:(unfold LLVMF_STK; lia) KA KB KF (mle_start MT S' MTL))|].
split.
{ apply (tw_kept TMAP_B (aview segs (w_H W) mem')); [exact HTW|].
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
  apply KR. op5_lia. }
split; [exact ESET|].
split; [exact EQOP|].
split; [destruct HCUR as (C24 & C27); split;
  [exact (eq_trans (HK1 24 ltac:(op5_inl)) C24) | exact (eq_trans (HK1 27 ltac:(op5_inl)) C27)]|].
split; [exact (eq_trans (HK1 20 ltac:(op5_inl)) R20) | exact (eq_trans Q22 R22)].
Qed.

(* ------------------------------------------------------------------ *)
(* 7. The segment                                                      *)
(* ------------------------------------------------------------------ *)

Lemma lc_op5_ok (K1 : lc_rom_view_stmt B MT XL RLO RHI) (K6 : lc_runinv_stmt) : lc_op5_stmt B MT XL RLO RHI.
Proof.
unfold lc_op5_stmt. intros HP cx op W' c' HB HA.
destruct HA as (ly' & S' & regs' & mem' & md' & e & Hc & Ho5 & HL & Htw & _ & HCUR & (R20 & _)).
assert (Ho : lc_opc (l_pl cx) (lo_c op) = 5) by (symmetry; exact Ho5).
pose proof HL as (_ & _ & _ & _ & (HAG & Hops & _ & _ & _) & _).
destruct (op5_model (l_pl cx) (lo_ops op) (lo_B op) (lo_c op) (lo_k op) HAG Hops Ho)
  as (B2 & want & B3 & r & M2 & M3 & M4 & ESET & EQOP).
destruct (op5_inv2 (lo_ops op) (lo_B op) B2 want K6 HAG M2) as (HRI2 & Hgf2).
destruct (op5_csw B3 B3 r want tt M4) as (_ & Erw). subst r.
pose proof (op5_want_range _ _ _ M2) as Hwr.
subst c'. replace (lo_arm 5) with 2036 by reflexivity.
eapply SRr_bind; [exact (op5_s1 cx op ly' S' W' regs' mem' md' e HP HB HL Htw HCUR R20)|].
intros W1 c1 _ H1.
eapply SRr_bind; [exact (op5_s2 cx op W1 c1 HP HB H1)|].
intros W2 c2 _ H2.
eapply SRr_bind; [exact (op5_s3 cx op B2 want W2 c2 HP HB M2 H2)|].
intros W3 c3 _ H3.
eapply SRr_bind; [exact (op5_s4 cx op B2 B3 want want W3 c3 K1 HP HB HRI2 Hgf2 M3 H3)|].
intros W4 c4 _ H4.
eapply SRr_bind; [exact (op5_s5 cx op B3 want want W4 c4 HP HB Hwr Hwr M4 H4)|].
intros W5 c5 _ H5.
exact (op5_s6 cx op B3 W5 c5 HP HB Ho ESET EQOP H5).
Qed.

End seg.
