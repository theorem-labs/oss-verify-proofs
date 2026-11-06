(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths and module names changed; 1543 of its 1645 lines of code are new or changed and 663 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op6a: Lemma lc_op6a_ok : lc_op6a_stmt B MT XL RLO RHI, the segment OP6A of the image-A
   walk of fuzz_transport.asan's LLVMFuzzerTestOneInput (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v): from the cut ARM6
   (lc_st_arm cx op 6, +0x684) to the cut CLS (lc_st_cls, +0x1004), the offsets +0x684 .. +0x6e4 and +0xf68 .. +0x1000
   of the listing lib/A/Prog/DgnTransportList.v.

   What the code does (TCb.v op_begin_m, then m_close_m with m_set_m inlined).
     +0x684 .. +0x698  s9 = OW, `jal __asan_memset` (OW, 0, 304);
     +0x69c .. +0x6ac  `jal __asan_memset` (GOT, 0, 224);
     +0x6b0 .. +0x6c4  a0 = the byte g_fail_next (`lbu` at s4 - 1076), a6 = M (the spill slot 184(s1)), a1 = M.desk_known,
                       M.fail := a0, OW.desk_off := -1: the world is op_begin's (lc6_B1);
     +0x6c8 .. +0x6dc  `beqz a1`, then a0 = M.foreign and `bnez a0`, then a0 = M.state and `bne a0, 3`;
     +0x6e0 .. +0x6e4  (desk known, not foreign, M.state = S_CLOSED) M.fly.on := 0, `j` to CLS;
     +0xf68 .. +0xf74  (desk known, not foreign, M.state <> S_CLOSED) OW.e3 := OW.e3 + 1 (= 1: OW was zeroed),
                       M.fail := 0;
     +0xf78 .. +0xf84  a3 = M.state, M.fly.on := 0, `beq a3, 3` to CLS;
     +0xf88 .. +0x1000 a2 = OW.n (= 0), `blt 15, a2` (not taken), the three checked stores of OW.t[0] (state 3, old a3,
                       reason 8: their shadow is OW's, 0, so the reports 0x82c54, 0x82c5c, 0x82c60 are not reached),
                       OW.n := 1, M.state := 3.
   The walk. Each stretch between two calls or branches is one symbolic run of the token engine taken over the caller's
   G journal (lib/A/Prog/TransportGRunA.v paj_run_x / paj_run_to_x), from a symbolic state built at the stretch's first
   instruction from the machine facts there (its registers as atoms, the fields it reads or writes as regions); the
   two calls of __asan_memset are TransportGCg.v gx_intrin_at (destinations in G, their shadow and hulls from the
   record facts trans_recv_cells: lc6_sh_OW, lc6_sh_GOT). Every byte a stretch writes is a byte of G (awr_ok_x). The
   world is threaded by TWorldG.v tw_fill / tw_write (lc6_w_set .. lc6_w_d2), the model by lc6_close_eq / lc6_mset. The
   core lc_core is carried by LLVMFuzzerTestOneInput_st.v lc_core_kept (the journal itself is never named: it is the
   hypothesis the engine and the call kit return); the rest of the cut by lc6_cls. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Permutation Bool.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YP09 YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v AE2k ACfn Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg DgnTransportCgX TransportGCg TransportGRwA TransportGRunA CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TOps TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require QueueFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module QF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The model: op_begin's world and m_close_m                         *)
(* ------------------------------------------------------------------ *)

(* op_begin_m's worlds (TCb.v :340-344): the two memsets, OW.desk_off, M.fail. *)
Definition lc6_Bo (Bw : list byte) : list byte := TW.upd Bw TW.OFF_OW (repeat (DSpec.b8 0) (Z.to_nat TW.SZ_OW)).
Definition lc6_Bm (Bw : list byte) : list byte :=
  TW.upd (lc6_Bo Bw) TW.OFF_GOT (repeat (DSpec.b8 0) (Z.to_nat TW.SZ_GOT)).
Definition lc6_B3 (Bw : list byte) : list byte := TW.set_OW_desk_off (lc6_Bm Bw) (-1).
Definition lc6_B1 (Bw : list byte) : list byte := TW.set_M_fail (lc6_B3 Bw) (TW.g_fail_next (lc6_B3 Bw)).
(* m_close_m's world before m_set when the desk is known, not foreign and not closed (:381-382). *)
Definition lc6_B1e (X : list byte) : list byte := TW.set_M_fail (TW.set_OW_e3 X 1) 0.
(* m_set_m's world (:200-206) at OW.n = 0 with M.state = st <> S_CLOSED. *)
Definition lc6_set (Xf : list byte) (st : Z) : list byte :=
  TW.set_M_state (TW.set_OW_n (TW.set_OW_t_reason (TW.set_OW_t_old (TW.set_OW_t_state Xf 0 TC.S_CLOSED) 0 st) 0
    TC.R_CLOSED) 1) TC.S_CLOSED.

Lemma lc6_begin : forall Bw, TC.op_begin_m Bw = Some (lc6_B1 Bw, tt).
Proof. intros Bw. reflexivity. Qed.

Ltac lc6_num :=
  unfold TW.OFF_OW, TW.OFF_GOT, TW.OFF_M, TW.OFF_g_fail_next, TW.W_LEN, TW.SZ_OW, TW.SZ_GOT, TW.SZ_M in *.

Lemma lc6_len_upd : forall (bs v : list byte) k, Z.of_nat (length bs) = TW.W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= TW.W_LEN -> Z.of_nat (length (TW.upd bs k v)) = TW.W_LEN.
Proof. intros bs v k HL Hk Hv. rewrite TWL.length_upd by lia. exact HL. Qed.

Lemma lc6_u_out : forall (bs v : list byte) k k' n, Z.of_nat (length bs) = TW.W_LEN -> 0 <= k -> 0 <= k' ->
  (k' + Z.of_nat n <= k \/ k + Z.of_nat (length v) <= k') -> k + Z.of_nat (length v) <= TW.W_LEN ->
  TW.u_at (TW.upd bs k v) k' n = TW.u_at bs k' n.
Proof. intros bs v k k' n HL Hk Hk' Hd Hv. apply TWL.u_at_upd_out; lia. Qed.

Lemma lc6_len_rep : forall n, Z.of_nat (length (repeat (DSpec.b8 0) (Z.to_nat n))) = Z.max 0 n.
Proof. intros n. rewrite repeat_length. lia. Qed.

Lemma lc6_len_put : forall n v, Z.of_nat (length (TW.put n v)) = Z.of_nat n.
Proof. intros n v. rewrite TWL.length_put. reflexivity. Qed.

Ltac lc6_lside := rewrite ?lc6_len_rep, ?lc6_len_put; lc6_num; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *; lia.

Lemma lc6_len_Bo : forall Bw, Z.of_nat (length Bw) = TW.W_LEN -> Z.of_nat (length (lc6_Bo Bw)) = TW.W_LEN.
Proof. intros Bw HL. unfold lc6_Bo. apply lc6_len_upd; [exact HL | lc6_lside | lc6_lside]. Qed.
Lemma lc6_len_Bm : forall Bw, Z.of_nat (length Bw) = TW.W_LEN -> Z.of_nat (length (lc6_Bm Bw)) = TW.W_LEN.
Proof. intros Bw HL. unfold lc6_Bm. apply lc6_len_upd; [exact (lc6_len_Bo Bw HL) | lc6_lside | lc6_lside]. Qed.
Lemma lc6_len_B3 : forall Bw, Z.of_nat (length Bw) = TW.W_LEN -> Z.of_nat (length (lc6_B3 Bw)) = TW.W_LEN.
Proof.
intros Bw HL. unfold lc6_B3, TW.set_OW_desk_off, TW.A_OW_desk_off.
apply lc6_len_upd; [exact (lc6_len_Bm Bw HL) | lc6_lside | lc6_lside].
Qed.
Lemma lc6_len_B1 : forall Bw, Z.of_nat (length Bw) = TW.W_LEN -> Z.of_nat (length (lc6_B1 Bw)) = TW.W_LEN.
Proof.
intros Bw HL. unfold lc6_B1, TW.set_M_fail, TW.A_M_fail.
apply lc6_len_upd; [exact (lc6_len_B3 Bw HL) | lc6_lside | lc6_lside].
Qed.
Lemma lc6_len_B1e : forall X, Z.of_nat (length X) = TW.W_LEN -> Z.of_nat (length (lc6_B1e X)) = TW.W_LEN.
Proof.
intros X HL. unfold lc6_B1e, TW.set_M_fail, TW.set_OW_e3, TW.A_M_fail, TW.A_OW_e3.
apply lc6_len_upd; [apply lc6_len_upd; [exact HL | lc6_lside | lc6_lside] | lc6_lside | lc6_lside].
Qed.
Lemma lc6_len_fly : forall X, Z.of_nat (length X) = TW.W_LEN ->
  Z.of_nat (length (TW.set_M_fly_on X 0)) = TW.W_LEN.
Proof. intros X HL. unfold TW.set_M_fly_on, TW.A_M_fly_on. apply lc6_len_upd; [exact HL | lc6_lside | lc6_lside]. Qed.

(* The fields the code reads, through the writes before them. *)
Lemma lc6_rd_Bm : forall Bw k n, Z.of_nat (length Bw) = TW.W_LEN -> 0 <= k -> k + Z.of_nat n <= TW.OFF_GOT ->
  TW.u_at (lc6_Bm Bw) k n = TW.u_at Bw k n.
Proof.
intros Bw k n HL Hk Hn. unfold lc6_Bm, lc6_Bo.
rewrite lc6_u_out by first [exact (lc6_len_Bo Bw HL) | lc6_lside].
rewrite lc6_u_out by first [exact HL | lc6_lside].
reflexivity.
Qed.

Lemma lc6_rd_B1 : forall Bw k n, Z.of_nat (length Bw) = TW.W_LEN -> 0 <= k ->
  (k + Z.of_nat n <= TW.OFF_M + 88 \/ TW.OFF_M + 92 <= k) ->
  (k + Z.of_nat n <= TW.OFF_OW + 232 \/ TW.OFF_OW + 236 <= k) ->
  TW.u_at (lc6_B1 Bw) k n = TW.u_at (lc6_Bm Bw) k n.
Proof.
intros Bw k n HL Hk H1 H2. unfold lc6_B1, TW.set_M_fail, TW.A_M_fail.
rewrite lc6_u_out by first [exact (lc6_len_B3 Bw HL) | lc6_lside].
unfold lc6_B3, TW.set_OW_desk_off, TW.A_OW_desk_off.
rewrite lc6_u_out by first [exact (lc6_len_Bm Bw HL) | lc6_lside].
reflexivity.
Qed.

Lemma lc6_gfn : forall Bw, Z.of_nat (length Bw) = TW.W_LEN ->
  TW.g_fail_next (lc6_B3 Bw) = TW.u_at (lc6_Bm Bw) TW.OFF_g_fail_next 1.
Proof.
intros Bw HL. unfold TW.g_fail_next, lc6_B3, TW.set_OW_desk_off, TW.A_OW_desk_off.
rewrite lc6_u_out by first [exact (lc6_len_Bm Bw HL) | lc6_lside].
reflexivity.
Qed.

(* The three fields m_close_m tests, at op_begin's world: as after the memsets. *)
Lemma lc6_fields_B1 : forall Bw, Z.of_nat (length Bw) = TW.W_LEN ->
  TW.M_desk_known (lc6_B1 Bw) = bv_swrap 32 (TW.u_at (lc6_Bm Bw) TW.A_M_desk_known 4) /\
  TW.M_foreign (lc6_B1 Bw) = bv_swrap 32 (TW.u_at (lc6_Bm Bw) TW.A_M_foreign 4) /\
  TW.M_state (lc6_B1 Bw) = bv_swrap 32 (TW.u_at (lc6_Bm Bw) TW.A_M_state 4).
Proof.
intros Bw HL. unfold TW.M_desk_known, TW.M_foreign, TW.M_state, TW.s32_at.
unfold TW.A_M_desk_known, TW.A_M_foreign, TW.A_M_state.
rewrite !lc6_rd_B1 by first [exact HL | lc6_lside]. repeat split; reflexivity.
Qed.

(* OW's zeros after the memset: OW.n at OW + 0 and OW.e3 at OW + 200. *)
Lemma lc6_zero_Bm : forall Bw k, Z.of_nat (length Bw) = TW.W_LEN -> k = 0 \/ k = 200 ->
  TW.u_at (lc6_Bm Bw) (TW.OFF_OW + k) 4 = 0.
Proof.
intros Bw k HL Hk. unfold lc6_Bm.
rewrite lc6_u_out by first [exact (lc6_len_Bo Bw HL) | lc6_lside].
unfold lc6_Bo, TW.u_at.
rewrite TWL.sub_upd_d by first [lc6_lside | rewrite HL; lc6_lside].
destruct Hk as [-> | ->]; reflexivity.
Qed.

Lemma lc6_zero_B1 : forall Bw k, Z.of_nat (length Bw) = TW.W_LEN -> k = 0 \/ k = 200 ->
  TW.u_at (lc6_B1 Bw) (TW.OFF_OW + k) 4 = 0.
Proof.
intros Bw k HL Hk. rewrite lc6_rd_B1 by (exact HL || (destruct Hk as [-> | ->]; lc6_lside)).
exact (lc6_zero_Bm Bw k HL Hk).
Qed.

Lemma lc6_zero_B1e : forall X, Z.of_nat (length X) = TW.W_LEN -> TW.u_at X (TW.OFF_OW + 0) 4 = 0 ->
  TW.u_at (lc6_B1e X) (TW.OFF_OW + 0) 4 = 0.
Proof.
intros X HL HZ. unfold lc6_B1e, TW.set_M_fail, TW.set_OW_e3, TW.A_M_fail, TW.A_OW_e3.
rewrite lc6_u_out by first [apply lc6_len_upd; [exact HL | lc6_lside | lc6_lside] | lc6_lside].
rewrite lc6_u_out by first [exact HL | lc6_lside].
exact HZ.
Qed.

Lemma lc6_state_B1e : forall X, Z.of_nat (length X) = TW.W_LEN ->
  TW.u_at (lc6_B1e X) TW.A_M_state 4 = TW.u_at X TW.A_M_state 4.
Proof.
intros X HL. unfold lc6_B1e, TW.set_M_fail, TW.set_OW_e3, TW.A_M_fail, TW.A_OW_e3, TW.A_M_state.
rewrite lc6_u_out by first [apply lc6_len_upd; [exact HL | lc6_lside | lc6_lside] | lc6_lside].
rewrite lc6_u_out by first [exact HL | lc6_lside].
reflexivity.
Qed.

(* m_set_m at a world whose OW.n is 0 (OW was zeroed by op_begin), after M.fly.on := 0. *)
Lemma lc6_mset : forall X, Z.of_nat (length X) = TW.W_LEN -> TW.u_at X (TW.OFF_OW + 0) 4 = 0 ->
  TC.m_set_m (TW.set_M_fly_on X 0) TC.S_CLOSED TC.R_CLOSED =
  if TW.M_state X =? TC.S_CLOSED then Some (TW.set_M_fly_on X 0, tt)
  else Some (lc6_set (TW.set_M_fly_on X 0) (TW.M_state X), tt).
Proof.
intros X HL HZ.
assert (Est : TW.M_state (TW.set_M_fly_on X 0) = TW.M_state X).
{ unfold TW.M_state, TW.s32_at, TW.set_M_fly_on, TW.A_M_fly_on, TW.A_M_state.
  rewrite lc6_u_out by first [exact HL | lc6_lside]. reflexivity. }
assert (En : TW.OW_n (TW.set_M_fly_on X 0) = 0).
{ unfold TW.OW_n, TW.s32_at, TW.set_M_fly_on, TW.A_M_fly_on, TW.A_OW_n.
  rewrite lc6_u_out by first [exact HL | lc6_lside]. rewrite HZ. reflexivity. }
unfold TC.m_set_m. rewrite Est, En.
destruct (TW.M_state X =? TC.S_CLOSED); [reflexivity|].
replace (0 <? TC.TRANS_MAX) with true by reflexivity. replace (0 <? 0) with false by reflexivity.
replace (TC.int_inc 0) with (Some 1) by reflexivity.
reflexivity.
Qed.

(* m_close_m at op_begin's world: OW.e3 is 0 there, so its increment is 1. *)
Lemma lc6_close_eq : forall Bw, Z.of_nat (length Bw) = TW.W_LEN ->
  TC.m_close_m (lc6_B1 Bw) =
  if TC.truth (TW.M_desk_known (lc6_B1 Bw)) && negb (TC.truth (TW.M_foreign (lc6_B1 Bw))) &&
     negb (TW.M_state (lc6_B1 Bw) =? TC.S_CLOSED)
  then TC.m_set_m (TW.set_M_fly_on (lc6_B1e (lc6_B1 Bw)) 0) TC.S_CLOSED TC.R_CLOSED
  else TC.m_set_m (TW.set_M_fly_on (lc6_B1 Bw) 0) TC.S_CLOSED TC.R_CLOSED.
Proof.
intros Bw HL.
assert (E3 : TW.OW_e3 (lc6_B1 Bw) = 0).
{ unfold TW.OW_e3, TW.s32_at, TW.A_OW_e3. rewrite (lc6_zero_B1 Bw 200 HL (or_intror eq_refl)). reflexivity. }
unfold TC.m_close_m. rewrite E3. replace (TC.int_inc 0) with (Some 1) by reflexivity.
lazymatch goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The world relation across the stretches                           *)
(* ------------------------------------------------------------------ *)

(* A view that is rdF on the bytes P marks and rd0 elsewhere (m_lost_cgW.v's ml_mix). *)
Definition lc6_in (lo n x : Z) : bool := (lo <=? x) && (x <? lo + n).
Definition lc6_mix (P : Z -> bool) (rdF rd0 : Z -> option Z) : Z -> option Z :=
  fun x => if P x then rdF x else rd0 x.

Lemma lc6_in_true : forall lo n x, lo <= x < lo + n -> lc6_in lo n x = true.
Proof. intros lo n x H. unfold lc6_in. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.
Lemma lc6_in_false' : forall lo n x, ~ (lo <= x < lo + n) -> lc6_in lo n x = false.
Proof.
intros lo n x H. unfold lc6_in. destruct (Z.leb_spec lo x); destruct (Z.ltb_spec x (lo + n)); cbn [andb];
  first [reflexivity | exfalso; lia].
Qed.
Lemma lc6_in_false : forall lo n x, lc6_in lo n x = false -> ~ (lo <= x < lo + n).
Proof. intros lo n x H Hx. rewrite (lc6_in_true lo n x Hx) in H. discriminate H. Qed.

Lemma lc6_tw_start : forall rdF rd0 Bw, tw_at TMAP_A rd0 Bw -> tw_at TMAP_A (lc6_mix (fun _ => false) rdF rd0) Bw.
Proof. intros rdF rd0 Bw H. apply (tw_kept TMAP_A rd0 _ Bw H). intros x _. reflexivity. Qed.

(* One 4-byte store of v at the world offset ko = o + k of the row (o, b, n). *)
Lemma lc6_tw_step : forall rdF rd0 P Bw o b n k ko v,
  tw_at TMAP_A (lc6_mix P rdF rd0) Bw -> In (o, b, n) TMAP_A -> ko = o + k -> 0 <= k -> k + 4 <= n ->
  (forall j, (j < 4)%nat -> rdF (b + k + Z.of_nat j) = Some (YO0f.le_byte v 4 j)) ->
  tw_at TMAP_A (lc6_mix (fun x => P x || lc6_in (b + k) 4 x) rdF rd0) (TW.upd Bw ko (TW.put 4 v)).
Proof.
intros rdF rd0 P Bw o b n k ko v H Hin Hko Hk Hkn HV. subst ko.
apply (tw_write TMAP_A (lc6_mix P rdF rd0) (lc6_mix (fun x => P x || lc6_in (b + k) 4 x) rdF rd0) Bw o b n k 4 v
  TMAP_A_ok H Hin Hk ltac:(change (Z.of_nat 4) with 4; lia)).
- intros j Hj. unfold lc6_mix. cbv beta.
  rewrite (lc6_in_true (b + k) 4 (b + k + Z.of_nat j)) by lia. rewrite orb_true_r. exact (HV j Hj).
- intros x Hx Hn. unfold lc6_mix. cbv beta. change (Z.of_nat 4) with 4 in Hn.
  rewrite (lc6_in_false' (b + k) 4 x) by lia. rewrite orb_false_r. reflexivity.
Qed.

Lemma lc6_tw_end : forall rdF rd0 P Bw, tw_at TMAP_A (lc6_mix P rdF rd0) Bw ->
  (forall x, tw_in TMAP_A x -> P x = false -> rdF x = rd0 x) -> tw_at TMAP_A rdF Bw.
Proof.
intros rdF rd0 P Bw H Hk. apply (tw_kept TMAP_A (lc6_mix P rdF rd0) rdF Bw H).
intros x Hx. unfold lc6_mix. destruct (P x) eqn:E; [reflexivity | exact (Hk x Hx E)].
Qed.

Ltac lc6_unP HP :=
  cbv beta in HP;
  repeat match type of HP with
  | orb _ _ = false =>
      let Hq := fresh "Hq" in apply orb_false_iff in HP; destruct HP as [HP Hq]; apply lc6_in_false in Hq
  end.

(* The memsets: OW's and GOT's payloads zeroed (op_begin_m :390-391). *)
Lemma lc6_w_set : forall rd0 rdF Bw o b n,
  tw_at TMAP_A rd0 Bw -> In (o, b, n) TMAP_A -> 0 <= n ->
  (forall i, 0 <= i < n -> rdF (b + i) = Some (0 mod 256)) ->
  (forall x, tw_in TMAP_A x -> ~ (b <= x < b + n) -> rdF x = rd0 x) ->
  tw_at TMAP_A rdF (TW.upd Bw o (repeat (DSpec.b8 0) (Z.to_nat n))).
Proof.
intros rd0 rdF Bw o b n Htw Hin Hn HV HK.
pose proof (tw_fill_set TMAP_A rd0 rdF Bw o b n 0 0 n TMAP_A_ok Htw Hin ltac:(lia) Hn ltac:(lia)) as H.
rewrite !Z.add_0_r in H. apply H.
- intros i Hi. exact (HV i Hi).
- intros x Hx Hnx. exact (HK x Hx Hnx).
Qed.

(* +0x6b0 .. +0x6c4: OW.desk_off := -1 and M.fail := the byte g_fail_next: op_begin's world. *)
Lemma lc6_w_c1 : forall Bw rd0 rdF,
  tw_at TMAP_A rd0 (lc6_Bm Bw) ->
  (forall j, (j < 4)%nat -> rdF (TA_OW + 232 + Z.of_nat j) = Some (YO0f.le_byte (-1) 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte (TW.g_fail_next (lc6_B3 Bw)) 4 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_OW + 232 <= x < TA_OW + 236) -> ~ (TA_M + 88 <= x < TA_M + 92) -> rdF x = rd0 x) ->
  tw_at TMAP_A rdF (lc6_B1 Bw).
Proof.
intros Bw rd0 rdF Htw VD VF Hk.
assert (SM : TW.SZ_M = 1648) by reflexivity. assert (SO : TW.SZ_OW = 304) by reflexivity.
unfold lc6_B1. set (g := TW.g_fail_next (lc6_B3 Bw)) in *.
unfold lc6_B3, TW.set_M_fail, TW.set_OW_desk_off, TW.A_M_fail, TW.A_OW_desk_off.
pose proof (lc6_tw_start rdF rd0 _ Htw) as H0.
pose proof (lc6_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW 232 (TW.OFF_OW + 232) (-1) H0 TMAP_A_OW
  ltac:(lia) ltac:(lia) ltac:(lia) VD) as H1.
pose proof (lc6_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 88 (TW.OFF_M + 88) g H1 TMAP_A_M
  ltac:(lia) ltac:(lia) ltac:(lia) VF) as H2.
apply (lc6_tw_end rdF rd0 _ _ H2).
intros x Hx HP. lc6_unP HP. apply Hk; [exact Hx | lia | lia].
Qed.

(* +0xf68 .. +0xf74: OW.e3 := 1, M.fail := 0. *)
Lemma lc6_w_c2e : forall X rd0 rdF,
  tw_at TMAP_A rd0 X ->
  (forall j, (j < 4)%nat -> rdF (TA_OW + 200 + Z.of_nat j) = Some (YO0f.le_byte 1 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_OW + 200 <= x < TA_OW + 204) -> ~ (TA_M + 88 <= x < TA_M + 92) -> rdF x = rd0 x) ->
  tw_at TMAP_A rdF (lc6_B1e X).
Proof.
intros X rd0 rdF Htw VE VF Hk.
assert (SM : TW.SZ_M = 1648) by reflexivity. assert (SO : TW.SZ_OW = 304) by reflexivity.
unfold lc6_B1e, TW.set_M_fail, TW.set_OW_e3, TW.A_M_fail, TW.A_OW_e3.
pose proof (lc6_tw_start rdF rd0 _ Htw) as H0.
pose proof (lc6_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW 200 (TW.OFF_OW + 200) 1 H0 TMAP_A_OW
  ltac:(lia) ltac:(lia) ltac:(lia) VE) as H1.
pose proof (lc6_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 88 (TW.OFF_M + 88) 0 H1 TMAP_A_M
  ltac:(lia) ltac:(lia) ltac:(lia) VF) as H2.
apply (lc6_tw_end rdF rd0 _ _ H2).
intros x Hx HP. lc6_unP HP. apply Hk; [exact Hx | lia | lia].
Qed.

(* +0x6e0 and +0xf7c: M.fly.on := 0. *)
Lemma lc6_w_fly : forall X rd0 rdF,
  tw_at TMAP_A rd0 X ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 96 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_M + 96 <= x < TA_M + 100) -> rdF x = rd0 x) ->
  tw_at TMAP_A rdF (TW.set_M_fly_on X 0).
Proof.
intros X rd0 rdF Htw VF Hk.
assert (SM : TW.SZ_M = 1648) by reflexivity.
unfold TW.set_M_fly_on, TW.A_M_fly_on.
pose proof (lc6_tw_start rdF rd0 _ Htw) as H0.
pose proof (lc6_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 96 (TW.OFF_M + 96 + 0) 0 H0 TMAP_A_M
  ltac:(lia) ltac:(lia) ltac:(lia) VF) as H1.
apply (lc6_tw_end rdF rd0 _ _ H1).
intros x Hx HP. lc6_unP HP. apply Hk; [exact Hx | lia].
Qed.

(* +0xf94 .. +0x1000: OW.t[0] := {3, st, 8}, OW.n := 1, M.state := 3. *)
Lemma lc6_w_d2 : forall Xf rd0 rdF st,
  tw_at TMAP_A rd0 Xf ->
  (forall j, (j < 4)%nat -> rdF (TA_OW + 4 + Z.of_nat j) = Some (YO0f.le_byte TC.S_CLOSED 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_OW + 8 + Z.of_nat j) = Some (YO0f.le_byte st 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_OW + 12 + Z.of_nat j) = Some (YO0f.le_byte TC.R_CLOSED 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_OW + 0 + Z.of_nat j) = Some (YO0f.le_byte 1 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TA_M + 12 + Z.of_nat j) = Some (YO0f.le_byte TC.S_CLOSED 4 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_OW <= x < TA_OW + 16) -> ~ (TA_M + 12 <= x < TA_M + 16) -> rdF x = rd0 x) ->
  tw_at TMAP_A rdF (lc6_set Xf st).
Proof.
intros Xf rd0 rdF st Htw VS VO VR VN VM Hk.
assert (SM : TW.SZ_M = 1648) by reflexivity. assert (SO : TW.SZ_OW = 304) by reflexivity.
unfold lc6_set, TW.set_M_state, TW.set_OW_n, TW.set_OW_t_reason, TW.set_OW_t_old, TW.set_OW_t_state, TW.A_M_state,
  TW.A_OW_n, TW.A_OW_t_reason, TW.A_OW_t_old, TW.A_OW_t_state.
pose proof (lc6_tw_start rdF rd0 _ Htw) as H0.
pose proof (lc6_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW 4 (TW.OFF_OW + 4 + 12 * 0 + 0) TC.S_CLOSED H0 TMAP_A_OW
  ltac:(lia) ltac:(lia) ltac:(lia) VS) as H1.
pose proof (lc6_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW 8 (TW.OFF_OW + 4 + 12 * 0 + 4) st H1 TMAP_A_OW
  ltac:(lia) ltac:(lia) ltac:(lia) VO) as H2.
pose proof (lc6_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW 12 (TW.OFF_OW + 4 + 12 * 0 + 8) TC.R_CLOSED H2 TMAP_A_OW
  ltac:(lia) ltac:(lia) ltac:(lia) VR) as H3.
pose proof (lc6_tw_step rdF rd0 _ _ TW.OFF_OW TA_OW TW.SZ_OW 0 (TW.OFF_OW + 0) 1 H3 TMAP_A_OW
  ltac:(lia) ltac:(lia) ltac:(lia) VN) as H4.
pose proof (lc6_tw_step rdF rd0 _ _ TW.OFF_M TA_M TW.SZ_M 12 (TW.OFF_M + 12) TC.S_CLOSED H4 TMAP_A_M
  ltac:(lia) ltac:(lia) ltac:(lia) VM) as H5.
apply (lc6_tw_end rdF rd0 _ _ H5).
intros x Hx HP. lc6_unP HP. apply Hk; [exact Hx | lia | lia].
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The shadow of OW and GOT (the memsets' destinations)              *)
(* ------------------------------------------------------------------ *)

(* The record's cells of trans_recv_cells, as shadow cells: g_rx_len's granule and its three guards, OW's 38 granules
   and six guards, GOT's four leading guards (g_s's) and its 28 granules. *)
Definition lc6_cs : list (Z * Z) :=
  trans_zgran TA_g_rx_len (TA_g_rx_len + TW.SZ_g_rx_len) ++
  [(TA_g_rx_len + 8, 0xf9); (TA_g_rx_len + 16, 0xf9); (TA_g_rx_len + 24, 0xf9)] ++
  trans_zgran TA_OW (TA_OW + TW.SZ_OW) ++
  [(TA_OW + TW.SZ_OW, 0xf9); (TA_OW + TW.SZ_OW + 8, 0xf9); (TA_OW + TW.SZ_OW + 16, 0xf9);
   (TA_OW + TW.SZ_OW + 24, 0xf9); (TA_OW + TW.SZ_OW + 32, 0xf9); (TA_OW + TW.SZ_OW + 40, 0xf9)] ++
  [(TA_GOT - 32, 0xf9); (TA_GOT - 24, 0xf9); (TA_GOT - 16, 0xf9); (TA_GOT - 8, 0xf9)] ++
  trans_zgran TA_GOT (TA_GOT + TW.SZ_GOT).

Lemma lc6_cover : trans_cs_cover lc6_cs TA_OW 304 = true /\ trans_cs_cover lc6_cs TA_GOT 224 = true.
Proof. split; vm_compute; reflexivity. Qed.

Section sh. Context {rc : YM05.RunCeil}.
Variable B : asyms.

Lemma lc6_sh_cells : trans_recv_cells B -> trans_sh_cells B lc6_cs.
Proof.
intros (HZow & HZgot & HZrx & HC).
unfold lc6_cs.
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

Lemma lc6_sh_OW : trans_recv_cells B -> trans_sh_any B TA_OW 304.
Proof. intros HR. exact (trans_sh_any_cells B lc6_cs TA_OW 304 (lc6_sh_cells HR) (proj1 lc6_cover)). Qed.
Lemma lc6_sh_GOT : trans_recv_cells B -> trans_sh_any B TA_GOT 224.
Proof. intros HR. exact (trans_sh_any_cells B lc6_cs TA_GOT 224 (lc6_sh_cells HR) (proj2 lc6_cover)). Qed.
End sh.

(* ------------------------------------------------------------------ *)
(* 4. The machine                                                       *)
(* ------------------------------------------------------------------ *)

(* The first offset of each stretch in the listing (AF_LLVMFuzzerTestOneInput = 0). *)
Definition LC6_A : Z := 0x684.
Definition LC6_B : Z := 0x69c.
Definition LC6_C1 : Z := 0x6b0.
Definition LC6_C2C : Z := 0x6e0.
Definition LC6_C2E : Z := 0xf68.
Definition LC6_D1 : Z := 0xf78.
Definition LC6_D2 : Z := 0xf88.

Lemma lc6_arm6 : lo_arm 6 = LC6_A.
Proof. reflexivity. Qed.
Section pa. Context {rc : YM05.RunCeil}.
Lemma lc6_base : @pa_val _ transport_listing PI_transport A_TEXT = transport_text.
Proof. vm_compute. reflexivity. Qed.
Lemma lc6_vals : @pa_val _ transport_listing PI_transport (A_OBJ 8) = TA_M /\
  @pa_val _ transport_listing PI_transport (A_OBJ 12) = TA_OW /\
  @pa_val _ transport_listing PI_transport (A_OBJ 13) = TA_GOT.
Proof. vm_compute. repeat split. Qed.
Lemma lc6_s4 : LF_S4 + -1076 = TA_g_fail_next.
Proof. vm_compute. reflexivity. Qed.
End pa.

(* The registers the stretches keep: sp, gp, tp, s0, s1, s2, s4, s5, s6, s7, s8, s10. *)
Definition LC6_KEEPZ : list Z := [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 26].
Definition LC6_KEEP : list (bv 5) := map (Z_to_bv 5) LC6_KEEPZ.
Definition lc6_rk (regs regsX : bvmap 5 word) : Prop :=
  forall r, In r LC6_KEEP -> YK11.getr regsX r = YK11.getr regs r.

Ltac lc6_inK := unfold LC6_KEEP, LC6_KEEPZ; cbn [map In]; repeat (first [left; reflexivity | right]).

Lemma lc6_rk_refl : forall regs, lc6_rk regs regs.
Proof. intros regs r _. reflexivity. Qed.
Lemma lc6_rk_trans : forall r1 r2 r3, lc6_rk r1 r2 -> lc6_rk r2 r3 -> lc6_rk r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.
Lemma lc6_rk_pres : forall regsA regsB, aregs_preserved regsA regsB -> lc6_rk regsA regsB.
Proof.
intros regsA regsB HP r Hr. unfold LC6_KEEP in Hr. apply in_map_iff in Hr. destruct Hr as (z & <- & Hz).
apply HP. unfold LC6_KEEPZ in Hz. cbn [In] in Hz. unfold acallee_saved.
repeat (destruct Hz as [<- | Hz]; [lia |]). destruct Hz.
Qed.

(* The view the walk keeps from one memory to the next: every byte that is not a byte of G and not in the 4096 bytes
   below sp1 (the memsets' ESTACK window). *)
Definition lc6_km (cx : lcx) (W : world tfibsegs) (m m2 : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS a -> ~ (lc_sp1 cx - 4096 <= a < lc_sp1 cx) ->
    aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) m a.
Lemma lc6_km_refl : forall cx W m, lc6_km cx W m m.
Proof. intros cx W m a _ _ _. reflexivity. Qed.
Lemma lc6_km_trans : forall cx W m1 m2 m3, lc6_km cx W m1 m2 -> lc6_km cx W m2 m3 -> lc6_km cx W m1 m3.
Proof. intros cx W m1 m2 m3 H1 H2 a Ha HG Hw. rewrite (H2 a Ha HG Hw). exact (H1 a Ha HG Hw). Qed.

(* Byte j < 4 of a 64-bit word holding v is byte j of the 4-byte little-endian v (m_lost_cgW.v ml_bow). *)
Lemma lc6_bow : forall v j, (j < 4)%nat ->
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
Lemma lc6_chunk : forall (E : env) (H : word -> bool) (mm : word -> option byte) nb lo hi wlo whi cs b off e v,
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
rewrite Hb2. cbn [option_map]. f_equal. apply lc6_bow. exact Hj.
Qed.

(* beqz / beq / bne on sign-extended 32-bit values (m_lost_cgW.v ml_eqb0, close_seg_join.v cj_eqb). *)
Lemma lc6_eqb : forall v w, - 2 ^ 31 <= v < 2 ^ 31 -> - 2 ^ 31 <= w < 2 ^ 31 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 w) = (v =? w).
Proof.
intros v w Hv Hw. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64).
assert (Em : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> x mod 2 ^ 64 = if x <? 0 then x + 2 ^ 64 else x).
{ intros x Hx. destruct (Z.ltb_spec x 0) as [Hn | Hn].
  - symmetry. apply (Z.mod_unique x (2 ^ 64) (-1) (x + 2 ^ 64)); lia.
  - apply Z.mod_small. lia. }
rewrite (Em v Hv), (Em w Hw).
destruct (Z.ltb_spec v 0) as [V | V]; destruct (Z.ltb_spec w 0) as [Wq | Wq];
  apply Bool.eq_iff_eq_true; rewrite !Z.eqb_eq; split; intros HH; lia.
Qed.

(* The 4-byte signed load of an atom holding the unsigned int u (m_lost_cgW.v ml_sext_den). *)
Lemma lc6_sext_den : forall E n u, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros E n u Hn Hu. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
change (sext 64 (bv_extract 0 32 (Z_to_bv 64 u))) with (Z_to_bv 64 (bv_signed (bv_extract 0 32 (Z_to_bv 64 u)))).
f_equal. rewrite (LMem.signed_of_extract 32 (Z_to_bv 64 u)) by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Ltac lc6_reg HS r v H tac :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "lc6_reg: no match for" T; fail
  end.

(* The windows a run wrote, each inside the bytes Zs (m_lost_cgW.v ml_win). *)
Ltac lc6_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The symbolic states of the stretches. Bases: atom 16 is a6 = M, atom 25 is s9 = OW, atom 26 is s10 = the shadow
   base; the shadow entry of OW's 304 bytes (38 whole granules) decides the three checked stores of OW.t[0]. *)
Definition LC6_SH : list shent := [mkSHE 25 0 304].
Definition LC6_Bx : sv := SOff 26 0.
(* +0xf88: OW.n (0 since the memset) and OW.t[0], M.state. *)
Definition lc6_d2_ow : YP09.region := YP09.mkRegion (Some 25%nat) 0 16 0 16 [YP09.mkChunk 0 (YP09.CVal 4 (SLit 0))].
Definition lc6_d2_st : YP09.region := YP09.mkRegion (Some 16%nat) 12 16 12 16 [].
Definition lc6_d2_facts : facts :=
  mkFacts [(16%nat, mkAF TA_M TA_M 5); (25%nat, mkAF TA_OW TA_OW 5); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition lc6_d2_ss : sstate := mkSS LC6_D2 sr_atoms [lc6_d2_ow; lc6_d2_st] None lc6_d2_facts.
(* +0xf78: M.state (atom 32: its 4 bytes, unsigned), M.fly.on. *)
Definition lc6_d1_st : YP09.region := YP09.mkRegion (Some 16%nat) 12 16 0 0 [YP09.mkChunk 12 (YP09.CVal 4 (SOff 32 0))].
Definition lc6_fly : YP09.region := YP09.mkRegion (Some 16%nat) 96 100 96 100 [].
Definition lc6_d1_facts : facts := mkFacts [(16%nat, mkAF TA_M TA_M 5); (32%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition lc6_d1_ss : sstate := mkSS LC6_D1 sr_atoms [lc6_d1_st; lc6_fly] None lc6_d1_facts.
(* +0x6e0: M.fly.on. *)
Definition lc6_c2c_ss : sstate := mkSS LC6_C2C sr_atoms [lc6_fly] None (mkFacts [(16%nat, mkAF TA_M TA_M 5)] [] []).
(* +0xf68: OW.e3 (0 since the memset), M.fail. *)
Definition lc6_e3 : YP09.region := YP09.mkRegion (Some 25%nat) 200 204 200 204 [YP09.mkChunk 200 (YP09.CVal 4 (SLit 0))].
Definition lc6_fail : YP09.region := YP09.mkRegion (Some 16%nat) 88 92 88 92 [].
Definition lc6_c2e_ss : sstate :=
  mkSS LC6_C2E sr_atoms [lc6_e3; lc6_fail] None (mkFacts [(16%nat, mkAF TA_M TA_M 5); (25%nat, mkAF TA_OW TA_OW 5)] [] []).
(* +0x6b0: the byte g_fail_next at s4 - 1076 (atom 32), the spill slot 184(s1) holding M (image object 8), M's fields
   desk_known (atom 33), M.state (atom 35), M.foreign (atom 34) as the world holds them, and the two fields the stretch
   stores, M.fail and OW.desk_off. *)
Definition lc6_c1_gfn : YP09.region :=
  YP09.mkRegion (Some 20%nat) (-1076) (-1075) 0 0 [YP09.mkChunk (-1076) (YP09.CVal 1 (SOff 32 0))].
Definition lc6_c1_sp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 184 192 0 0 [YP09.mkChunk 184 (YP09.CVal 8 (SOff (A_OBJ 8) 0))].
Definition lc6_c1_dk : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SOff 33 0))].
Definition lc6_c1_st : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 12 16 0 0 [YP09.mkChunk 12 (YP09.CVal 4 (SOff 35 0))].
Definition lc6_c1_fr : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 24 28 0 0 [YP09.mkChunk 24 (YP09.CVal 4 (SOff 34 0))].
Definition lc6_c1_fail : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 88 92 88 92 [].
Definition lc6_c1_doff : YP09.region := YP09.mkRegion (Some 25%nat) 232 236 232 236 [].
Definition lc6_c1_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (20%nat, mkAF LF_S4 LF_S4 0); (25%nat, mkAF TA_OW TA_OW 5);
           (A_OBJ 8, mkAF TA_M TA_M 5); (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 (2 ^ 32 - 1) 0);
           (34%nat, mkAF 0 (2 ^ 32 - 1) 0); (35%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition lc6_c1_ss : sstate :=
  mkSS LC6_C1 sr_atoms [lc6_c1_gfn; lc6_c1_sp; lc6_c1_dk; lc6_c1_st; lc6_c1_fr; lc6_c1_fail; lc6_c1_doff] None
    lc6_c1_facts.
(* The values of atoms 32 .. 35 at the world X: the byte g_fail_next, M.desk_known, M.foreign, M.state (unsigned). *)
Definition lc6_c1_ex (X : list byte) : list word :=
  [Z_to_bv 64 (TW.u_at X TW.OFF_g_fail_next 1); Z_to_bv 64 (TW.u_at X TW.A_M_desk_known 4);
   Z_to_bv 64 (TW.u_at X TW.A_M_foreign 4); Z_to_bv 64 (TW.u_at X TW.A_M_state 4)].
Lemma lc6_lfs4 : LF_S4 = 6157652.
Proof. vm_compute. reflexivity. Qed.

Section seg. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The walk's valuation agrees with the registers below atom 32. *)
Lemma lc6_agree : forall regs extra E,
  (forall n, (n < 32)%nat -> ew E n = ew (Eimg (PI := PI_transport) (Ereg regs extra)) n) ->
  ed E = ed (Eimg (PI := PI_transport) (Ereg regs extra)) -> env_agree 32 (Ereg regs extra) E.
Proof.
intros regs extra E H1 H2. split.
- intros n Hn. rewrite (H1 n Hn). apply Eimg_low. unfold A_TEXT. lia.
- rewrite H2. reflexivity.
Qed.

(* A symbolic state with no region holds of any machine state at its pc (diginet_session_close_seg_join.v). *)
Lemma lc6_entry0 : forall {fx : YK11.FPState} (W : world tfibsegs) regs mem (pc : Z),
  st_ok_pi tfibsegs (@pa_val _ transport_listing PI_transport) (Eimg (PI := PI_transport) (Ereg regs []))
    (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (@pa_val _ transport_listing PI_transport A_TEXT + pc)) mem
      (YK11.seg_rom tfibsegs))).
Proof.
intros fx W regs mem pc. rewrite restrict_mkst_fx.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* A register atom's value in the walk's valuation. *)
Lemma lc6_U : forall (regs : bvmap 5 word) extra n (r : bv 5) v, Z.of_nat n = bv_unsigned r ->
  YK11.getr regs r = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew (Eimg (PI := PI_transport) (Ereg regs extra)) n) = v.
Proof.
intros regs extra n r v Hn Hr Hv. rewrite (can_ew_Eimg_Ereg_nat regs extra n r Hn), Hr. unfold w64.
apply unsigned_lit_small. exact Hv.
Qed.

(* The registers lc_core fixes, moved to another register file that keeps them. *)
Lemma lc6_core_regs : forall cx ly S W regsA regsB m md e,
  lc_core B cx ly S W regsA m md e -> lc6_rk regsA regsB -> lc_core B cx ly S W regsB m md e.
Proof.
intros cx ly S W regsA regsB m md e HC HRK.
destruct HC as (HJ & Hfr & HlyF & Hperm & Rsp & R8 & R9 & Rgp & Rtp & Hrest).
refine (conj HJ (conj Hfr (conj HlyF (conj Hperm (conj _ (conj _ (conj _ (conj _ (conj _ Hrest))))))))).
- exact (eq_trans (HRK (Z_to_bv 5 2) ltac:(lc6_inK)) Rsp).
- exact (eq_trans (HRK (Z_to_bv 5 8) ltac:(lc6_inK)) R8).
- exact (eq_trans (HRK (Z_to_bv 5 9) ltac:(lc6_inK)) R9).
- exact (eq_trans (HRK (Z_to_bv 5 3) ltac:(lc6_inK)) Rgp).
- exact (eq_trans (HRK (Z_to_bv 5 4) ltac:(lc6_inK)) Rtp).
Qed.

(* What lc6_km gives lc_core_kept (X = 4096): the bytes at or above alloc_ceiling outside the window, the blocks'
   bytes and the frame's bytes and shadow (none is a byte of G, none is in the window). *)
Lemma lc6_kabf : forall cx ly' S' (W' : world segs) regs' m1 md1 e m2,
  AR_laws segs B -> lc_base B MT XL RLO RHI cx -> lc_core B cx ly' S' W' regs' m1 md1 e -> lc6_km cx W' m1 m2 ->
  (forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - 4096 <= a < lc_sp1 cx) ->
     aview segs (w_H W') m2 a = aview segs (w_H W') m1 a) /\
  (forall b m i, In (b, m) (ablocks B ly' S') -> 0 <= i < req_size m ->
     aview segs (w_H W') m2 (b + i) = aview segs (w_H W') m1 (b + i)) /\
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES \/ lc_SH cx <= a < lc_SH cx + 32 ->
     aview segs (w_H W') m2 a = aview segs (w_H W') m1 a).
Proof.
intros cx ly' S' W' regs' m1 md1 e m2 LAWS HB HC HKM.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' m1 md1 e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & Hsp1al & _ & HF4096 & HFal & HFceil & _).
pose proof asan_consts as ((CVlo & CVhi) & _).
assert (GHI : forall a, inG TG.G_HARNESS a -> a < TG.G_HARNESS_HI) by (intros a Ha; exact (proj2 (inG_G_HARNESS_hull a Ha))).
unfold TG.G_HARNESS_HI in GHI.
assert (HF8 : 0 <= lc_F cx / 8 <= lc_F cx) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
unfold LF_FBYTES in *.
split; [|split].
- intros a Ha Hw. apply HKM; [lia | intros HG; pose proof (GHI a HG); lia | exact Hw].
- intros b m i Hb Hi. destruct (al_blocks _ _ LAWS ly' S' W' m1 md1 b m HARg Hb) as (_ & H4096 & Hbc & _).
  apply HKM; [lia | | lia].
  intros HG. exact (blk_img segs B LAWS ly' S' W' m1 md1 b m (b + i) HARg Hb ltac:(lia) (trans_g_img (b + i) HG)).
- intros a Ha.
  assert (HSH : lc_SH cx = SHADOW_OFF + lc_F cx / 8) by reflexivity. unfold SHADOW_OFF in HSH.
  apply HKM.
  + destruct Ha; lia.
  + intros HG. destruct Ha as [Ha | Ha].
    * apply (frm_img segs B LAWS ly' S' W' m1 md1 LF_CID (l_fpos cx) a HARg HFin);
        [rewrite HFaddr; change (fs_frame_bytes LF_CID) with 256; exact Ha | exact (trans_g_img a HG)].
    * pose proof (GHI a HG). lia.
  + destruct Ha; lia.
Qed.

(* The cut CLS from the walk's last facts: the core at the last memory, the kept registers, the kept view, and the
   model's op_begin / m_close worlds. *)
Lemma lc6_cls : forall cx op ly' S' (W' : world segs) regs' mem' md' e regsF memF mdF B1 B2,
  lc_base B MT XL RLO RHI cx ->
  lc_lcore B MT cx op false false (lo_k op) ly' S' W' regs' mem' md' e ->
  lc_opc (l_pl cx) (lo_c op) = 6 ->
  lc_cur cx regs' 24 23 (lc_oc (l_pl cx) (lo_c op)) -> YK11.getr regs' 20 = w64 LF_S4 -> YK11.getr regs' 22 = w64 7 ->
  lc_core B cx ly' S' W' regs' memF mdF e -> lc6_rk regs' regsF -> lc6_km cx W' mem' memF ->
  TC.op_begin_m (lo_B op) = Some (B1, tt) -> TC.m_close_m B1 = Some (B2, tt) -> lc_tw W' memF B2 ->
  lc_st_cls B MT cx op W'
    (mkCfg (@YK11.mkst (l_fx cx) regsF (Z_to_bv 64 (BASE + LO_CLS)) memF (YK11.seg_rom segs)) mdF).
Proof.
intros cx op ly' S' W' regs' mem' md' e regsF memF mdF B1 B2 HB HL Ho Hcur R20 R22 HCF HRK HKM HOB HMC HTW.
destruct HL as (HC & HFR & HSP & HFSH & HOK & HEV & HMT & R21).
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & Hsp1al & _ & HF4096 & HFal & HFceil & _).
pose proof asan_consts as ((CVlo & CVhi) & _).
assert (GHI : forall a, inG TG.G_HARNESS a -> a < TG.G_HARNESS_HI) by (intros a Ha; exact (proj2 (inG_G_HARNESS_hull a Ha))).
unfold TG.G_HARNESS_HI in GHI.
assert (HF8 : 0 <= lc_F cx / 8 <= lc_F cx) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (HSH : lc_SH cx = SHADOW_OFF + lc_F cx / 8) by reflexivity. unfold SHADOW_OFF in HSH.
destruct Hstk as (Hst1 & Hst2 & Hst3 & Hst4). destruct Hsp1 as [Hsp1a Hsp1b]. destruct HF8 as [HF8a HF8b].
change (2 ^ 47) with 140737488355328 in Hst4. unfold LF_FBYTES, LF_FRAME, LLVMF_STK in *.
exists ly', S', regsF, memF, mdF, e, B1, B2.
split. { unfold lc_cfg. rewrite lc6_base. reflexivity. }
split; [exact Ho|].
split.
{ refine (conj (lc6_core_regs cx ly' S' W' regs' regsF memF mdF e HCF HRK)
    (conj _ (conj _ (conj _ (conj HOK (conj HEV (conj HMT _))))))).
  - destruct HFR as [R18 R26]. split.
    + exact (eq_trans (HRK (Z_to_bv 5 18) ltac:(lc6_inK)) R18).
    + exact (eq_trans (HRK (Z_to_bv 5 26) ltac:(lc6_inK)) R26).
  - apply (lc_spills_kept cx _ (aview segs (w_H W') mem')); [| | exact HSP].
    + intros o Ho'. pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES; lia)) as HV.
      rewrite Forall_forall in HV. destruct (HV o Ho') as (_ & _ & H8 & H192). lia.
    + intros a Ha. apply HKM; [lia | intros HG; pose proof (GHI a HG); lia | lia].
  - apply (lc_fsh_kept cx (aview segs (w_H W') mem')); [| exact HFSH].
    intros a Ha. apply HKM; [lia | intros HG; pose proof (GHI a HG); lia | lia].
  - exact (eq_trans (HRK (Z_to_bv 5 21) ltac:(lc6_inK)) R21). }
split; [exact HOB|]. split; [exact HMC|]. split; [exact HTW|].
split. { destruct Hcur as [C24 C23]. split.
  - exact (eq_trans (HRK (Z_to_bv 5 24) ltac:(lc6_inK)) C24).
  - exact (eq_trans (HRK (Z_to_bv 5 23) ltac:(lc6_inK)) C23). }
split; [exact (eq_trans (HRK (Z_to_bv 5 20) ltac:(lc6_inK)) R20) |
  exact (eq_trans (HRK (Z_to_bv 5 22) ltac:(lc6_inK)) R22)].
Qed.

(* A payload byte of a row of TMAP_A is a byte of G (io_send_seg_world.v ios_inG_row). *)
Lemma lc6_inG_row : forall o b n a, In (o, b, n) TMAP_A -> b <= a < b + n -> inG TG.G_HARNESS a.
Proof.
intros o b n a Hin Ha. unfold inG. apply Exists_exists. exists (b, n).
split; [exact (TMAP_A_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* The registers of LC6_KEEP a symbolic state still holds as their own atoms. *)
Lemma lc6_rk_st : forall {fx : YK11.FPState} E ss (H : word -> bool) ms regs0 extra,
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok segs E ss (restrict H ms) ->
  env_agree 32 (Ereg regs0 extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) LC6_KEEP = true ->
  lc6_rk regs0 (ms_regs ms).
Proof.
intros fx E ss H ms regs0 extra HS HA Hl r Hr.
exact (regs_kept_of_st_ok segs E ss (restrict H ms) regs0 extra LC6_KEEP HS HA Hl r Hr).
Qed.

(* The fields of OW and M are bytes of G. *)
Lemma lc6_inG_OW : forall a, TA_OW <= a < TA_OW + 304 -> inG TG.G_HARNESS a.
Proof. intros a Ha. apply (lc6_inG_row _ _ _ a TMAP_A_OW). unfold TW.SZ_OW. lia. Qed.
Lemma lc6_inG_M : forall a, TA_M <= a < TA_M + 1648 -> inG TG.G_HARNESS a.
Proof. intros a Ha. apply (lc6_inG_row _ _ _ a TMAP_A_M). unfold TW.SZ_M. lia. Qed.

(* The state at +0x6b0 holds of the machine state there. *)
Lemma lc6_c1_entry : forall {fx : YK11.FPState} (W : world segs) regs mem X s1,
  YK11.getr regs (Z_to_bv 5 9) = w64 s1 -> YK11.getr regs (Z_to_bv 5 20) = w64 LF_S4 ->
  YK11.getr regs (Z_to_bv 5 25) = w64 TA_OW ->
  2 ^ 46 <= s1 -> s1 + 192 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  rdword (aview segs (w_H W) mem) (s1 + 184) = Some TA_M ->
  tw_at TMAP_A (aview segs (w_H W) mem) X ->
  st_ok_pi segs VAL (Eimg (PI := PI_transport) (Ereg regs (lc6_c1_ex X))) lc6_c1_ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LC6_C1)) mem (YK11.seg_rom segs))).
Proof.
intros fx W regs mem X s1 R9 R20 R25 Hs1a Hs1b Hs1c HSP Htw.
set (E := Eimg (PI := PI_transport) (Ereg regs (lc6_c1_ex X))).
pose proof lc6_lfs4 as EL. pose proof lc6_s4 as ES4.
assert (EM : TA_M = 6156640) by reflexivity. assert (EO : TA_OW = 6238304) by reflexivity.
assert (EG : TA_g_fail_next = 6156576) by reflexivity.
change (2 ^ 46) with 70368744177664 in Hs1a. change (2 ^ 47) with 140737488355328 in Hs1b.
assert (U9 : bv_unsigned (ew E 9%nat) = s1)
  by (unfold E; exact (lc6_U regs _ 9 (Z_to_bv 5 9) s1 eq_refl R9 ltac:(lia))).
assert (U20 : bv_unsigned (ew E 20%nat) = LF_S4)
  by (unfold E; exact (lc6_U regs _ 20 (Z_to_bv 5 20) LF_S4 eq_refl R20 ltac:(lia))).
assert (U25 : bv_unsigned (ew E 25%nat) = TA_OW)
  by (unfold E; exact (lc6_U regs _ 25 (Z_to_bv 5 25) TA_OW eq_refl R25 ltac:(lia))).
assert (U249 : bv_unsigned (ew E 249%nat) = TA_M).
{ unfold E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). change 249%nat with (A_OBJ 8).
  rewrite (proj1 lc6_vals). first [reflexivity | apply unsigned_lit_small; unfold TA_M; lia]. }
assert (U8 : bv_unsigned (ew E (A_OBJ 8)) = TA_M) by exact U249.
pose proof (TWL.u_at_range X TW.OFF_g_fail_next 1) as Rg. pose proof (TWL.u_at_range X TW.A_M_desk_known 4) as Rd.
pose proof (TWL.u_at_range X TW.A_M_foreign 4) as Rf. pose proof (TWL.u_at_range X TW.A_M_state 4) as Rs.
change (2 ^ (8 * Z.of_nat 1)) with 256 in Rg. change (2 ^ (8 * Z.of_nat 4)) with 4294967296 in Rd, Rf, Rs.
assert (E32 : ew E 32 = Z_to_bv 64 (TW.u_at X TW.OFF_g_fail_next 1))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (TW.u_at X TW.A_M_desk_known 4))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (TW.u_at X TW.A_M_foreign 4))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (TW.u_at X TW.A_M_state 4))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
rewrite restrict_mkst_fx. unfold lc6_c1_ss.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [lc6_c1_gfn lc6_c1_sp lc6_c1_dk lc6_c1_st lc6_c1_fr lc6_c1_fail lc6_c1_doff
      YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ LF_S4 (-1076) 1 (SOff 32 0) (TW.u_at X TW.OFF_g_fail_next 1));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
    replace (LF_S4 + -1076) with (TA_g_fail_next + 0) by lia.
    pose proof (tw_read_val segs (mrestrict (w_H W) mem) TMAP_A X TW.OFF_g_fail_next TA_g_fail_next 1 0 1 TMAP_A_ok
      Htw TMAP_A_g_fail_next ltac:(lia) ltac:(lia)) as HV.
    rewrite Z.add_0_r in HV. exact HV.
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ s1 184 8 (SOff (A_OBJ 8) 0) TA_M);
      [cbn [sv_denot]; rewrite ?U8, ?U249, Z.add_0_r; reflexivity | cbn; lia | lia |].
    exact (val_mem_of_rdword segs (w_H W) mem _ _ HSP).
  + rewrite ?U8, ?U249. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ TA_M 0 4 (SOff 33 0) (TW.u_at X TW.A_M_desk_known 4));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
    exact (tw_read_val segs (mrestrict (w_H W) mem) TMAP_A X TW.OFF_M TA_M TW.SZ_M 0 4 TMAP_A_ok Htw TMAP_A_M
      ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
  + rewrite ?U8, ?U249. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ TA_M 12 4 (SOff 35 0) (TW.u_at X TW.A_M_state 4));
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
    exact (tw_read_val segs (mrestrict (w_H W) mem) TMAP_A X TW.OFF_M TA_M TW.SZ_M 12 4 TMAP_A_ok Htw TMAP_A_M
      ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
  + rewrite ?U8, ?U249. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ TA_M 24 4 (SOff 34 0) (TW.u_at X TW.A_M_foreign 4));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
    exact (tw_read_val segs (mrestrict (w_H W) mem) TMAP_A X TW.OFF_M TA_M TW.SZ_M 24 4 TMAP_A_ok Htw TMAP_A_M
      ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
  + rewrite ?U8, ?U249. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply lc6_inG_M. lia.
  + rewrite U25. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw). apply lc6_inG_OW. lia.
- apply pairwise_disjoint_of_extents.
  unfold lc6_c1_gfn, lc6_c1_sp, lc6_c1_dk, lc6_c1_st, lc6_c1_fr, lc6_c1_fail, lc6_c1_doff, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U9, U20, U25, ?U8, ?U249.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold lc6_c1_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U20, U25, ?U8, ?U249, E32, E33, E34, E35, !unsigned_lit_small by lia.
  change (2 ^ 5) with 32. change (2 ^ 46) with 70368744177664. change (2 ^ 47) with 140737488355328.
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?EM, ?EO; first [lia | reflexivity].
Qed.

(* The state at +0xf78 holds of the machine state there (atom 32: M.state's 4 bytes at the world X). *)
Lemma lc6_d1_entry : forall {fx : YK11.FPState} (W : world segs) regs mem X,
  YK11.getr regs (Z_to_bv 5 16) = w64 TA_M -> tw_at TMAP_A (aview segs (w_H W) mem) X ->
  st_ok_pi segs VAL (Eimg (PI := PI_transport) (Ereg regs [Z_to_bv 64 (TW.u_at X TW.A_M_state 4)])) lc6_d1_ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LC6_D1)) mem (YK11.seg_rom segs))).
Proof.
intros fx W regs mem X R16 Htw.
set (v := TW.u_at X TW.A_M_state 4).
assert (Rv : 0 <= v < 2 ^ 32) by (pose proof (TWL.u_at_range X TW.A_M_state 4) as R; cbn in R; unfold v; lia).
set (E := Eimg (PI := PI_transport) (Ereg regs [Z_to_bv 64 v])).
assert (U16 : bv_unsigned (ew E 16%nat) = TA_M)
  by (unfold E; exact (lc6_U regs _ 16 (Z_to_bv 5 16) TA_M eq_refl R16 ltac:(unfold TA_M; lia))).
assert (E32 : ew E 32 = Z_to_bv 64 v)
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U32 : bv_unsigned (ew E 32) = v) by (rewrite E32; apply unsigned_lit_small; lia).
assert (EM : TA_M = 6156640) by reflexivity.
rewrite restrict_mkst_fx. unfold lc6_d1_ss.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [lc6_d1_st lc6_fly YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U16. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ TA_M 12 4 (SOff 32 0) v);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
    exact (tw_read_val segs (mrestrict (w_H W) mem) TMAP_A X TW.OFF_M TA_M TW.SZ_M 12 4 TMAP_A_ok Htw TMAP_A_M
      ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
  + rewrite U16. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply lc6_inG_M. lia.
- apply pairwise_disjoint_of_extents.
  unfold lc6_d1_st, lc6_fly, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U16. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold lc6_d1_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U16, U32. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?EM; first [lia | reflexivity].
Qed.

(* The state at +0x6e0. *)
Lemma lc6_c2c_entry : forall {fx : YK11.FPState} (W : world segs) regs mem,
  YK11.getr regs (Z_to_bv 5 16) = w64 TA_M ->
  st_ok_pi segs VAL (Eimg (PI := PI_transport) (Ereg regs [])) lc6_c2c_ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LC6_C2C)) mem (YK11.seg_rom segs))).
Proof.
intros fx W regs mem R16.
set (E := Eimg (PI := PI_transport) (Ereg regs [])).
assert (U16 : bv_unsigned (ew E 16%nat) = TA_M)
  by (unfold E; exact (lc6_U regs _ 16 (Z_to_bv 5 16) TA_M eq_refl R16 ltac:(unfold TA_M; lia))).
assert (EM : TA_M = 6156640) by reflexivity.
rewrite restrict_mkst_fx. unfold lc6_c2c_ss.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [lc6_fly YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U16. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply lc6_inG_M. lia.
- apply pairwise_disjoint_of_extents.
  unfold lc6_fly, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  cbn [zpairwise_disjoint zall_disjoint]. repeat split; exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U16. change (2 ^ 5) with 32.
  repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?EM; first [lia | reflexivity].
Qed.

(* The state at +0xf68 (OW.e3 is 0 at the world X). *)
Lemma lc6_c2e_entry : forall {fx : YK11.FPState} (W : world segs) regs mem X,
  YK11.getr regs (Z_to_bv 5 16) = w64 TA_M -> YK11.getr regs (Z_to_bv 5 25) = w64 TA_OW ->
  tw_at TMAP_A (aview segs (w_H W) mem) X -> TW.u_at X (TW.OFF_OW + 200) 4 = 0 ->
  st_ok_pi segs VAL (Eimg (PI := PI_transport) (Ereg regs [])) lc6_c2e_ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LC6_C2E)) mem (YK11.seg_rom segs))).
Proof.
intros fx W regs mem X R16 R25 Htw HZ.
set (E := Eimg (PI := PI_transport) (Ereg regs [])).
assert (U16 : bv_unsigned (ew E 16%nat) = TA_M)
  by (unfold E; exact (lc6_U regs _ 16 (Z_to_bv 5 16) TA_M eq_refl R16 ltac:(unfold TA_M; lia))).
assert (U25 : bv_unsigned (ew E 25%nat) = TA_OW)
  by (unfold E; exact (lc6_U regs _ 25 (Z_to_bv 5 25) TA_OW eq_refl R25 ltac:(unfold TA_OW; lia))).
assert (EO : TA_OW = 6238304) by reflexivity. assert (EM : TA_M = 6156640) by reflexivity.
rewrite restrict_mkst_fx. unfold lc6_c2e_ss.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [lc6_e3 lc6_fail YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U25. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw). apply lc6_inG_OW. lia.
    * constructor; [|constructor].
      apply (chunk_ok_val segs E _ TA_OW 200 4 (SLit 0) 0); [reflexivity | cbn; lia | lia |].
      pose proof (tw_read_val segs (mrestrict (w_H W) mem) TMAP_A X TW.OFF_OW TA_OW TW.SZ_OW 200 4 TMAP_A_ok Htw
        TMAP_A_OW ltac:(lia) ltac:(unfold TW.SZ_OW; lia)) as HV.
      rewrite HZ in HV. exact HV.
  + rewrite U16. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply lc6_inG_M. lia.
- apply pairwise_disjoint_of_extents.
  unfold lc6_e3, lc6_fail, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U25, U16. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U16, U25. change (2 ^ 5) with 32.
  repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?EM, ?EO; first [lia | reflexivity].
Qed.

(* The state at +0xf88 holds of the machine state there. *)
Lemma lc6_d2_entry : forall {fx : YK11.FPState} ly S (W : world segs) regs mem md X,
  @AR rc segs B ly S W mem md -> trans_recv_cells B ->
  YK11.getr regs (Z_to_bv 5 16) = w64 TA_M -> YK11.getr regs (Z_to_bv 5 25) = w64 TA_OW ->
  YK11.getr regs (Z_to_bv 5 26) = w64 SHADOW_OFF ->
  tw_at TMAP_A (aview segs (w_H W) mem) X -> TW.u_at X (TW.OFF_OW + 0) 4 = 0 ->
  st_ok_pi segs VAL (Eimg (PI := PI_transport) (Ereg regs [])) lc6_d2_ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LC6_D2)) mem (YK11.seg_rom segs))) /\
  sh_ok segs LC6_Bx LC6_SH (Eimg (PI := PI_transport) (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros fx ly S W regs mem md X HAR HRC R16 R25 R26 Htw HZ.
set (E := Eimg (PI := PI_transport) (Ereg regs [])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U16 : bv_unsigned (ew E 16) = TA_M)
  by (rewrite (EE 16%nat (Z_to_bv 5 16) eq_refl), R16; apply unsigned_lit_small; unfold TA_M; lia).
assert (U25 : bv_unsigned (ew E 25) = TA_OW)
  by (rewrite (EE 25%nat (Z_to_bv 5 25) eq_refl), R25; apply unsigned_lit_small; unfold TA_OW; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (rewrite (EE 26%nat (Z_to_bv 5 26) eq_refl), R26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (EO : TA_OW = 6238304) by reflexivity. assert (EM : TA_M = 6156640) by reflexivity.
split.
- rewrite restrict_mkst_fx. unfold lc6_d2_ss.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [lc6_d2_ow lc6_d2_st YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U25. split; [lia|]. split; [lia|]. split.
      -- intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw). apply lc6_inG_OW. lia.
      -- constructor; [|constructor].
         apply (chunk_ok_val segs E _ TA_OW 0 4 (SLit 0) 0); [reflexivity | cbn; lia | lia |].
         pose proof (tw_read_val segs (mrestrict (w_H W) mem) TMAP_A X TW.OFF_OW TA_OW TW.SZ_OW 0 4 TMAP_A_ok Htw
           TMAP_A_OW ltac:(lia) ltac:(unfold TW.SZ_OW; lia)) as HV.
         rewrite HZ in HV. exact HV.
    * rewrite U16. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw). apply lc6_inG_M. lia.
  + apply pairwise_disjoint_of_extents.
    unfold lc6_d2_ow, lc6_d2_st, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U25, U16. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  + unfold lc6_d2_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U16, U25, U26. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?EO, ?EM; unfold SHADOW_OFF;
    first [lia | reflexivity].
- destruct (lc6_sh_OW B HRC ly S W mem md HAR) as [HRA _].
  assert (UB : U E LC6_Bx = SHADOW_OFF).
  { unfold U, LC6_Bx. cbn [sv_denot]. rewrite U26, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, LC6_SH. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem E LC6_Bx 25 TA_OW 304 TA_OW 0 304 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U25, Z.add_0_r. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

Section op6.
Variable cx : lcx.
Variable op : lop.
Variable ly' : alayout.
Variable S' : astate.
Variable W' : world segs.
Variable regs' : bvmap 5 word.
Variable mem' : word -> option byte.
Variable md' : Model.
Variable e : Z.
Hypothesis HP : lp_prem B MT XL RLO RHI.
Hypothesis HB : lc_base B MT XL RLO RHI cx.
Hypothesis HL : lc_lcore B MT cx op false false (lo_k op) ly' S' W' regs' mem' md' e.
Hypothesis Ho : lc_opc (l_pl cx) (lo_c op) = 6.
Hypothesis Hcur : lc_cur cx regs' 24 23 (lc_oc (l_pl cx) (lo_c op)).
Hypothesis R20 : YK11.getr regs' 20 = w64 LF_S4.
Hypothesis R22 : YK11.getr regs' 22 = w64 7.
Hypothesis Htw0 : lc_tw W' mem' (lo_B op).

(* What every stretch carries: the core at the current memory (at the cut's registers), the kept registers and the
   kept view. *)
Definition lc6_st (regsX : bvmap 5 word) (memX : word -> option byte) (mdX : Model) : Prop :=
  lc_core B cx ly' S' W' regs' memX mdX e /\ lc6_rk regs' regsX /\ lc6_km cx W' mem' memX.

Local Abbreviation Q := (lc_st_cls B MT cx op).
Local Abbreviation cfgX regsX pc memX mdX :=
  (mkCfg (@YK11.mkst (l_fx cx) regsX (Z_to_bv 64 (BASE + pc)) memX (YK11.seg_rom segs)) mdX).

(* The stack: sp1, sp0 and the memsets' window. *)
Lemma lc6_sp : YM05.alloc_ceiling + 32432 <= lc_sp1 cx /\ lc_sp0 cx - 336 <= lc_sp1 cx <= lc_sp0 cx - 320 /\
  lc_sp0 cx <= 2 ^ 47 /\ (lc_sp1 cx - lc_sp0 cx) mod 16 = 0.
Proof.
pose proof HL as (HC & _).
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & Hsp1al & _).
destruct Hstk as (_ & _ & Hst3 & Hst4). unfold LF_FRAME in Hsp1.
split; [exact Hsp1c|]. split; [exact Hsp1|]. split; [lia|].
rewrite Zminus_mod. replace (lc_sp1 cx mod 16) with 0 by (Z.div_mod_to_equations; lia). rewrite Hsp0al. reflexivity.
Qed.

(* The step of the core over a memory the walk kept (lc_core_kept at X = 4096 and the cut's registers). *)
Ltac lc6_core HC HJ2 HKM HCn :=
  let KA := fresh "KA" in let KB := fresh "KB" in let KF := fresh "KF" in
  destruct (lc6_kabf _ _ _ _ _ _ _ _ _ (lp_laws _ _ _ _ _ HP) HB HC HKM) as (KA & KB & KF);
  pose proof (lc_core_kept B MT XL RLO RHI cx ly' S' W' regs' _ _ e 4096 ly' S' W' regs' _ _ e (lp_laws _ _ _ _ _ HP)
    HB HC HJ2 eq_refl (Permutation_refl _) (fun r _ => eq_refl) ltac:(unfold LLVMF_STK; lia) KA KB KF) as HCn;
  clear KA KB KF.

(* +0xf88 .. +0x1000: a2 = OW.n = 0, `blt 15, a2` (not taken), the checked stores OW.t[0] := {3, a3, 8} (the shadow
   of OW: 0), OW.n := 1, M.state := 3; the cut CLS. *)
Lemma lc6_D2 : forall X regsX memX mdX, lc6_st regsX memX mdX ->
  YK11.getr regsX (Z_to_bv 5 16) = w64 TA_M -> YK11.getr regsX (Z_to_bv 5 25) = w64 TA_OW ->
  YK11.getr regsX (Z_to_bv 5 13) = Z_to_bv 64 (TW.M_state X) ->
  Z.of_nat (length X) = TW.W_LEN -> TW.u_at X (TW.OFF_OW + 0) 4 = 0 ->
  lc_tw W' memX (TW.set_M_fly_on X 0) ->
  TC.m_close_m (lc6_B1 (lo_B op)) = Some (lc6_set (TW.set_M_fly_on X 0) (TW.M_state X), tt) ->
  SRr segs W' (cfgX regsX LC6_D2 memX mdX) Q.
Proof.
intros X regsX memX mdX (HC & HRK & HKM) R16 R25 R13 HLX HZ HTW HMC.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HL as (_ & HFR & _).
assert (R26 : YK11.getr regsX (Z_to_bv 5 26) = w64 SHADOW_OFF)
  by exact (eq_trans (HRK (Z_to_bv 5 26) ltac:(lc6_inK)) (proj2 HFR)).
pose proof HC as (HJ & _).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
assert (HZf : TW.u_at (TW.set_M_fly_on X 0) (TW.OFF_OW + 0) 4 = 0).
{ unfold TW.set_M_fly_on, TW.A_M_fly_on. rewrite lc6_u_out by first [exact HLX | lc6_lside]. exact HZ. }
destruct (lc6_d2_entry (fx := l_fx cx) ly' S' W' regsX memX mdX _ HAR (lp_recv_cells _ _ _ _ _ HP) R16 R25 R26 HTW HZf)
  as [HS SHOK].
set (E0 := Eimg (PI := PI_transport) (Ereg regsX [])) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
  0 []) as RUNTO.
assert (U16 : bv_unsigned (ew E0 16%nat) = TA_M)
  by (unfold E0; exact (lc6_U regsX [] 16 (Z_to_bv 5 16) TA_M eq_refl R16 ltac:(unfold TA_M; lia))).
assert (U25 : bv_unsigned (ew E0 25%nat) = TA_OW)
  by (unfold E0; exact (lc6_U regsX [] 25 (Z_to_bv 5 25) TA_OW eq_refl R25 ltac:(unfold TA_OW; lia))).
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_CLS.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U25 in Ha; apply lc6_inG_OW; lia |].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U16 in Ha; apply lc6_inG_M; lia |].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy mdX) mat mdX) in *. clearbody md1. clear mat.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ ((TA_OW <= a < TA_OW + 16) \/ (TA_M + 12 <= a < TA_M + 16)) ->
  aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') memX a).
{ intros a Ha Hn.
  apply (kept_of_frame _ _ _ _ _ (fun x => (TA_OW <= x < TA_OW + 16) \/ (TA_M + 12 <= x < TA_M + 16)) HFr);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. lc6_win Hin Hx ltac:(rewrite ?U25, ?U16 in Hx; lia). }
clear HF HFr HG.
(* the stored bytes, from the last state's chunks *)
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
assert (D13 : sv_denot E0 (SOff 13 0) = Z_to_bv 64 (TW.M_state X)).
{ cbn [sv_denot]. unfold E0. rewrite (can_ew_Eimg_Ereg_nat regsX [] 13 (Z_to_bv 5 13) eq_refl), Z.add_0_r,
    Z_to_bv_bv_unsigned. exact R13. }
pose proof (lc6_chunk _ _ _ _ _ _ _ _ _ TA_OW 0 (SLit 1) 1 RG0 U25 ltac:(cbn [In]; tauto) eq_refl) as VN.
pose proof (lc6_chunk _ _ _ _ _ _ _ _ _ TA_OW 12 (SLit 8) TC.R_CLOSED RG0 U25 ltac:(cbn [In]; tauto) eq_refl) as VR.
pose proof (lc6_chunk _ _ _ _ _ _ _ _ _ TA_OW 8 (SOff 13 0) (TW.M_state X) RG0 U25 ltac:(cbn [In]; tauto) D13) as VO.
pose proof (lc6_chunk _ _ _ _ _ _ _ _ _ TA_OW 4 (SLit 3) TC.S_CLOSED RG0 U25 ltac:(cbn [In]; tauto) eq_refl) as VS.
pose proof (lc6_chunk _ _ _ _ _ _ _ _ _ TA_M 12 (SLit 3) TC.S_CLOSED RG1 U16 ltac:(cbn [In]; tauto) eq_refl) as VM.
clear RG0 RG1.
assert (HTWF : lc_tw W' (ms_mem ms) (lc6_set (TW.set_M_fly_on X 0) (TW.M_state X))).
{ apply (lc6_w_d2 _ (aview segs (w_H W') memX) _ _ HTW VS VO VR VN VM).
  intros x Hx N1 N2. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  apply KR; [lia | intros [H1 | H1]; [exact (N1 H1) | exact (N2 H1)]]. }
assert (HKMr : lc6_km cx W' memX (ms_mem ms)).
{ intros a Ha HnG _. apply KR; [exact Ha|]. intros [H1 | H1]; apply HnG;
    [apply lc6_inG_OW | apply lc6_inG_M]; lia. }
lc6_core HC HJ HKMr HCF.
assert (HRKr : lc6_rk regsX (ms_regs ms)).
{ apply (lc6_rk_st _ _ _ ms regsX [] HS); [apply lc6_agree; [intros n Hn; reflexivity | reflexivity] |].
  vm_compute. reflexivity. }
pmkst HS.
apply (SRr_ret segs).
exact (lc6_cls cx op ly' S' W' regs' mem' md' e (ms_regs ms) (ms_mem ms) md1 (lc6_B1 (lo_B op))
  (lc6_set (TW.set_M_fly_on X 0) (TW.M_state X)) HB HL Ho Hcur R20 R22 HCF (lc6_rk_trans _ _ _ HRK HRKr)
  (lc6_km_trans _ _ _ _ _ HKM HKMr) (lc6_begin _) HMC HTWF).
Qed.

(* +0xf78 .. +0xf84: a3 = M.state, M.fly.on := 0, `beq a3, 3`: S_CLOSED goes to CLS (m_set_m returns at once), any
   other state to +0xf88 (lc6_D2). *)
Lemma lc6_D1 : forall X regsX memX mdX, lc6_st regsX memX mdX ->
  YK11.getr regsX (Z_to_bv 5 16) = w64 TA_M -> YK11.getr regsX (Z_to_bv 5 25) = w64 TA_OW ->
  Z.of_nat (length X) = TW.W_LEN -> TW.u_at X (TW.OFF_OW + 0) 4 = 0 -> lc_tw W' memX X ->
  TC.m_close_m (lc6_B1 (lo_B op)) = TC.m_set_m (TW.set_M_fly_on X 0) TC.S_CLOSED TC.R_CLOSED ->
  SRr segs W' (cfgX regsX LC6_D1 memX mdX) Q.
Proof.
intros X regsX memX mdX (HC & HRK & HKM) R16 R25 HLX HZ HTW HMC.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HC as (HJ & _).
set (v := TW.u_at X TW.A_M_state 4).
assert (Rv : 0 <= v < 2 ^ 32) by (pose proof (TWL.u_at_range X TW.A_M_state 4) as R; cbn in R; unfold v; lia).
pose proof (lc6_d1_entry (fx := l_fx cx) W' regsX memX X R16 HTW) as HS. fold v in HS.
set (E0 := Eimg (PI := PI_transport) (Ereg regsX [Z_to_bv 64 v])) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (SHOK : sh_ok segs LC6_Bx (@nil shent) E0 (mrestrict (w_H W') memX)) by constructor.
assert (U16 : bv_unsigned (ew E0 16%nat) = TA_M)
  by (unfold E0; exact (lc6_U regsX _ 16 (Z_to_bv 5 16) TA_M eq_refl R16 ltac:(unfold TA_M; lia))).
assert (E32 : ew E0 32 = Z_to_bv 64 v)
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsX _ 0)).
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
  0 []) as RUNTO.
pose proof (paj_branch (fx := l_fx cx) (PI := PI_transport)) as BR.
paj_run_tok RUN HS HJ SHOK (0, 0).
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U16 in Ha; apply lc6_inG_M; lia |].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy mdX) mat mdX) in *. clearbody md1. clear mat. rename ms into ms1.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 96 <= a < TA_M + 100) ->
  aview segs (w_H W') (ms_mem ms1) a = aview segs (w_H W') memX a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => TA_M + 96 <= x < TA_M + 100) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. lc6_win Hin Hx ltac:(rewrite ?U16 in Hx; lia). }
clear HF HFr HG.
assert (D3 : sv_denot E0 (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (TW.M_state X)) by exact (lc6_sext_den E0 32 v E32 Rv).
assert (SR : - 2 ^ 31 <= TW.M_state X < 2 ^ 31) by (unfold TW.M_state; apply TWL.s32_range).
pose proof (lc6_mset X HLX HZ) as EM.
(* what a run from the branch keeps, and the world it leaves *)
assert (POST : forall m2,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 96 <= a < TA_M + 100) ->
     aview segs (w_H W') m2 a = aview segs (w_H W') (ms_mem ms1) a) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W') m2 (TA_M + 96 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  lc6_km cx W' memX m2 /\ lc_tw W' m2 (TW.set_M_fly_on X 0)).
{ intros m2 KR2 VF.
  split.
  - intros a Ha HnG _. assert (Hn : ~ (TA_M + 96 <= a < TA_M + 100)) by (intros H1; apply HnG; apply lc6_inG_M; lia).
    rewrite (KR2 a Ha Hn). exact (KR1 a Ha Hn).
  - apply (lc6_w_fly X (aview segs (w_H W') memX) _ HTW VF).
    intros x Hx N1. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    rewrite (KR2 x ltac:(lia) N1). exact (KR1 x ltac:(lia) N1). }
psrr_branch_tok RUN BR HS SHOK (0, 0).
- (* M.state = S_CLOSED: m_set_m returns at once; `beq` to CLS *)
  rewrite D3 in Hc. change (sv_denot E0 (SLit 3)) with (Z_to_bv 64 3) in Hc. cbn [branch_taken] in Hc.
  rewrite (lc6_eqb _ 3 SR ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
  assert (Eq : (TW.M_state X =? TC.S_CLOSED) = true) by (apply Z.eqb_eq; exact Hc).
  rewrite Eq in EM. cbv beta iota in EM.
  paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LO_CLS.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
    apply awr_ok_x_cons_g;
      [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U16 in Ha; apply lc6_inG_M; lia |].
    apply awr_ok_x_nil. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
  pose proof (lc6_chunk _ _ _ _ _ _ _ _ _ TA_M 96 (SLit 0) 0 RG1 U16 ltac:(cbn [In]; tauto) eq_refl) as VF.
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 96 <= a < TA_M + 100) ->
    aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') (ms_mem ms1) a).
  { intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => TA_M + 96 <= x < TA_M + 100) HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx. lc6_win Hin Hx ltac:(rewrite ?U16 in Hx; lia). }
  destruct (POST (ms_mem ms) KR2 VF) as [HKMr HTWF]. clear HF HFr HG RG1 KR2 VF.
  lc6_core HC HJ HKMr HCF.
  assert (HRKr : lc6_rk regsX (ms_regs ms)).
  { apply (lc6_rk_st _ _ _ ms regsX [Z_to_bv 64 v] HS); [apply lc6_agree; [intros n Hn; reflexivity | reflexivity] |].
    vm_compute. reflexivity. }
  pmkst HS.
  apply (SRr_ret segs).
  exact (lc6_cls cx op ly' S' W' regs' mem' md' e (ms_regs ms) (ms_mem ms) md2 (lc6_B1 (lo_B op))
    (TW.set_M_fly_on X 0) HB HL Ho Hcur R20 R22 HCF (lc6_rk_trans _ _ _ HRK HRKr)
    (lc6_km_trans _ _ _ _ _ HKM HKMr) (lc6_begin _) (eq_trans HMC EM) HTWF).
- (* any other state: m_set_m's stores, +0xf88 *)
  rewrite D3 in Hc. change (sv_denot E0 (SLit 3)) with (Z_to_bv 64 3) in Hc. cbn [branch_taken] in Hc.
  rewrite (lc6_eqb _ 3 SR ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
  assert (Eq : (TW.M_state X =? TC.S_CLOSED) = false) by (apply Z.eqb_neq; exact Hc).
  rewrite Eq in EM. cbv beta iota in EM.
  paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LC6_D2.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
    apply awr_ok_x_cons_g;
      [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U16 in Ha; apply lc6_inG_M; lia |].
    apply awr_ok_x_nil. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
  pose proof (lc6_chunk _ _ _ _ _ _ _ _ _ TA_M 96 (SLit 0) 0 RG1 U16 ltac:(cbn [In]; tauto) eq_refl) as VF.
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 96 <= a < TA_M + 100) ->
    aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') (ms_mem ms1) a).
  { intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => TA_M + 96 <= x < TA_M + 100) HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx. lc6_win Hin Hx ltac:(rewrite ?U16 in Hx; lia). }
  destruct (POST (ms_mem ms) KR2 VF) as [HKMr HTWF]. clear HF HFr HG RG1 KR2 VF.
  lc6_core HC HJ HKMr HCF.
  assert (HRKr : lc6_rk regsX (ms_regs ms)).
  { apply (lc6_rk_st _ _ _ ms regsX [Z_to_bv 64 v] HS); [apply lc6_agree; [intros n Hn; reflexivity | reflexivity] |].
    vm_compute. reflexivity. }
  lc6_reg HS (Z_to_bv 5 16) (YK11.getr regsX (Z_to_bv 5 16)) Q16
    ltac:(cbn [sv_denot]; unfold E0; rewrite (can_ew_Eimg_Ereg_nat regsX _ 16 (Z_to_bv 5 16) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  lc6_reg HS (Z_to_bv 5 25) (YK11.getr regsX (Z_to_bv 5 25)) Q25
    ltac:(cbn [sv_denot]; unfold E0; rewrite (can_ew_Eimg_Ereg_nat regsX _ 25 (Z_to_bv 5 25) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
  lc6_reg HS (Z_to_bv 5 13) (Z_to_bv 64 (TW.M_state X)) Q13 ltac:(exact D3).
  pmkst HS.
  exact (lc6_D2 X (ms_regs ms) (ms_mem ms) md2 (conj HCF (conj (lc6_rk_trans _ _ _ HRK HRKr)
    (lc6_km_trans _ _ _ _ _ HKM HKMr))) (eq_trans Q16 R16) (eq_trans Q25 R25) Q13 HLX HZ HTWF (eq_trans HMC EM)).
Qed.

(* The length of the operation's start world. *)
Lemma lc6_lenB : Z.of_nat (length (lo_B op)) = TW.W_LEN.
Proof. rewrite (tw_len _ _ _ Htw0). rewrite Z2Nat.id; [reflexivity | unfold TW.W_LEN; lia]. Qed.

(* +0x6e0 .. +0x6e4 (desk known, not foreign, M.state = S_CLOSED: m_set_m returns at once): M.fly.on := 0, `j` to
   CLS. *)
Lemma lc6_C2c : forall regsX memX mdX, lc6_st regsX memX mdX ->
  YK11.getr regsX (Z_to_bv 5 16) = w64 TA_M -> lc_tw W' memX (lc6_B1 (lo_B op)) ->
  TW.M_state (lc6_B1 (lo_B op)) = TC.S_CLOSED ->
  SRr segs W' (cfgX regsX LC6_C2C memX mdX) Q.
Proof.
intros regsX memX mdX (HC & HRK & HKM) R16 HTW Hst.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HC as (HJ & _).
pose proof lc6_lenB as HLB. pose proof (lc6_len_B1 _ HLB) as HL1.
pose proof (lc6_c2c_entry (fx := l_fx cx) W' regsX memX R16) as HS.
set (E0 := Eimg (PI := PI_transport) (Ereg regsX [])) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (SHOK : sh_ok segs LC6_Bx (@nil shent) E0 (mrestrict (w_H W') memX)) by constructor.
assert (U16 : bv_unsigned (ew E0 16%nat) = TA_M)
  by (unfold E0; exact (lc6_U regsX _ 16 (Z_to_bv 5 16) TA_M eq_refl R16 ltac:(unfold TA_M; lia))).
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
  0 []) as RUNTO.
paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LO_CLS.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U16 in Ha; apply lc6_inG_M; lia |].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy mdX) mat mdX) in *. clearbody md1. clear mat.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
pose proof (lc6_chunk _ _ _ _ _ _ _ _ _ TA_M 96 (SLit 0) 0 RG0 U16 ltac:(cbn [In]; tauto) eq_refl) as VF.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (TA_M + 96 <= a < TA_M + 100) ->
  aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') memX a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => TA_M + 96 <= x < TA_M + 100) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. lc6_win Hin Hx ltac:(rewrite ?U16 in Hx; lia). }
clear HF HFr HG RG0.
assert (HKMr : lc6_km cx W' memX (ms_mem ms)).
{ intros a Ha HnG _. apply KR; [exact Ha|]. intros H1. apply HnG. apply lc6_inG_M. lia. }
assert (HTWF : lc_tw W' (ms_mem ms) (TW.set_M_fly_on (lc6_B1 (lo_B op)) 0)).
{ apply (lc6_w_fly _ (aview segs (w_H W') memX) _ HTW VF).
  intros x Hx N1. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  exact (KR x ltac:(lia) N1). }
lc6_core HC HJ HKMr HCF.
assert (HRKr : lc6_rk regsX (ms_regs ms)).
{ apply (lc6_rk_st _ _ _ ms regsX [] HS); [apply lc6_agree; [intros n Hn; reflexivity | reflexivity] |].
  vm_compute. reflexivity. }
(* the model: the test of :380 is false, m_set_m returns at once *)
pose proof (lc6_close_eq _ HLB) as EC. rewrite Hst, Z.eqb_refl, andb_false_r in EC. cbv beta iota in EC.
pose proof (lc6_mset _ HL1 (lc6_zero_B1 _ 0 HLB (or_introl eq_refl))) as EM.
rewrite Hst, Z.eqb_refl in EM. cbv beta iota in EM.
pmkst HS.
apply (SRr_ret segs).
exact (lc6_cls cx op ly' S' W' regs' mem' md' e (ms_regs ms) (ms_mem ms) md1 (lc6_B1 (lo_B op))
  (TW.set_M_fly_on (lc6_B1 (lo_B op)) 0) HB HL Ho Hcur R20 R22 HCF (lc6_rk_trans _ _ _ HRK HRKr)
  (lc6_km_trans _ _ _ _ _ HKM HKMr) (lc6_begin _) (eq_trans EC EM) HTWF).
Qed.

(* +0xf68 .. +0xf74 (desk known, not foreign, not closed: :381-382): OW.e3 := OW.e3 + 1 = 1, M.fail := 0; on to
   +0xf78 (lc6_D1) at m_close_m's world before m_set. *)
Lemma lc6_C2e : forall regsX memX mdX, lc6_st regsX memX mdX ->
  YK11.getr regsX (Z_to_bv 5 16) = w64 TA_M -> YK11.getr regsX (Z_to_bv 5 25) = w64 TA_OW ->
  lc_tw W' memX (lc6_B1 (lo_B op)) ->
  (TC.truth (TW.M_desk_known (lc6_B1 (lo_B op))) && negb (TC.truth (TW.M_foreign (lc6_B1 (lo_B op)))) &&
   negb (TW.M_state (lc6_B1 (lo_B op)) =? TC.S_CLOSED)) = true ->
  SRr segs W' (cfgX regsX LC6_C2E memX mdX) Q.
Proof.
intros regsX memX mdX (HC & HRK & HKM) R16 R25 HTW Hcnd.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HC as (HJ & _).
pose proof lc6_lenB as HLB. pose proof (lc6_len_B1 _ HLB) as HL1.
pose proof (lc6_c2e_entry (fx := l_fx cx) W' regsX memX _ R16 R25 HTW (lc6_zero_B1 _ 200 HLB (or_intror eq_refl)))
  as HS.
set (E0 := Eimg (PI := PI_transport) (Ereg regsX [])) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (SHOK : sh_ok segs LC6_Bx (@nil shent) E0 (mrestrict (w_H W') memX)) by constructor.
assert (U16 : bv_unsigned (ew E0 16%nat) = TA_M)
  by (unfold E0; exact (lc6_U regsX _ 16 (Z_to_bv 5 16) TA_M eq_refl R16 ltac:(unfold TA_M; lia))).
assert (U25 : bv_unsigned (ew E0 25%nat) = TA_OW)
  by (unfold E0; exact (lc6_U regsX _ 25 (Z_to_bv 5 25) TA_OW eq_refl R25 ltac:(unfold TA_OW; lia))).
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
  0 []) as RUNTO.
paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LC6_D1.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U25 in Ha; apply lc6_inG_OW; lia |].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U16 in Ha; apply lc6_inG_M; lia |].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy mdX) mat mdX) in *. clearbody md1. clear mat.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
pose proof (lc6_chunk _ _ _ _ _ _ _ _ _ TA_OW 200 _ 1 RG0 U25 ltac:(cbn [In]; left; reflexivity)
  ltac:(reflexivity)) as VE.
pose proof (lc6_chunk _ _ _ _ _ _ _ _ _ TA_M 88 (SLit 0) 0 RG1 U16 ltac:(cbn [In]; tauto) eq_refl) as VF.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ ((TA_OW + 200 <= a < TA_OW + 204) \/ (TA_M + 88 <= a < TA_M + 92)) ->
  aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') memX a).
{ intros a Ha Hn.
  apply (kept_of_frame _ _ _ _ _ (fun x => (TA_OW + 200 <= x < TA_OW + 204) \/ (TA_M + 88 <= x < TA_M + 92)) HFr);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. lc6_win Hin Hx ltac:(rewrite ?U16, ?U25 in Hx; lia). }
clear HF HFr HG RG0 RG1.
assert (HKMr : lc6_km cx W' memX (ms_mem ms)).
{ intros a Ha HnG _. apply KR; [exact Ha|]. intros [H1 | H1]; apply HnG; [apply lc6_inG_OW | apply lc6_inG_M]; lia. }
assert (HTWF : lc_tw W' (ms_mem ms) (lc6_B1e (lc6_B1 (lo_B op)))).
{ apply (lc6_w_c2e _ (aview segs (w_H W') memX) _ HTW VE VF).
  intros x Hx N1 N2. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  apply KR; [lia | intros [H1 | H1]; [exact (N1 H1) | exact (N2 H1)]]. }
lc6_core HC HJ HKMr HCF.
assert (HRKr : lc6_rk regsX (ms_regs ms)).
{ apply (lc6_rk_st _ _ _ ms regsX [] HS); [apply lc6_agree; [intros n Hn; reflexivity | reflexivity] |].
  vm_compute. reflexivity. }
lc6_reg HS (Z_to_bv 5 16) (YK11.getr regsX (Z_to_bv 5 16)) Q16
  ltac:(cbn [sv_denot]; unfold E0; rewrite (can_ew_Eimg_Ereg_nat regsX _ 16 (Z_to_bv 5 16) eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
lc6_reg HS (Z_to_bv 5 25) (YK11.getr regsX (Z_to_bv 5 25)) Q25
  ltac:(cbn [sv_denot]; unfold E0; rewrite (can_ew_Eimg_Ereg_nat regsX _ 25 (Z_to_bv 5 25) eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
(* the model: the test of :380 holds, OW.e3 + 1 = 1 and M.fail := 0 before m_set *)
pose proof (lc6_close_eq _ HLB) as EC. rewrite Hcnd in EC. cbv beta iota in EC.
pmkst HS.
exact (lc6_D1 (lc6_B1e (lc6_B1 (lo_B op))) (ms_regs ms) (ms_mem ms) md1
  (conj HCF (conj (lc6_rk_trans _ _ _ HRK HRKr) (lc6_km_trans _ _ _ _ _ HKM HKMr)))
  (eq_trans Q16 R16) (eq_trans Q25 R25) (lc6_len_B1e _ HL1)
  (lc6_zero_B1e _ HL1 (lc6_zero_B1 _ 0 HLB (or_introl eq_refl))) HTWF EC).
Qed.

(* The two stored fields and the registers at an exit of the stretch +0x6b0, from that state. *)
Ltac lc6_c1_exit HS HFr KRp ms HJ HCF HKMr HTWF HRKr Q16 Q25 U249 U25 POST DG DM1 HC regsX E0 memX EX :=
  let RG5 := fresh "RG" in let RG6 := fresh "RG" in let VF := fresh "VF" in let VD := fresh "VD" in
  let KR2 := fresh "KR" in
  pose proof (st_ok_pi_region_nth _ _ _ 5 _ HS eq_refl) as RG5; cbn [ms_mem restrict] in RG5;
  pose proof (st_ok_pi_region_nth _ _ _ 6 _ HS eq_refl) as RG6; cbn [ms_mem restrict] in RG6;
  pose proof (lc6_chunk _ _ _ _ _ _ _ _ _ TA_M 88 (SOff 32 0) _ RG5 U249 ltac:(cbn [In]; tauto) DG) as VF;
  pose proof (lc6_chunk _ _ _ _ _ _ _ _ _ TA_OW 232 (SLit 18446744073709551615) (-1) RG6 U25
    ltac:(cbn [In]; tauto) DM1) as VD;
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ ((TA_OW + 232 <= a < TA_OW + 236) \/ (TA_M + 88 <= a < TA_M + 92)) ->
    aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') memX a)
  by (intros a Ha Hn; rewrite <- (KRp a Ha Hn);
      apply (kept_of_frame _ _ _ _ _ (fun x => (TA_OW + 232 <= x < TA_OW + 236) \/ (TA_M + 88 <= x < TA_M + 92)) HFr);
      [| exact Ha | exact Hn];
      intros b wlo whi x Hin Hx; lc6_win Hin Hx ltac:(rewrite ?U25, ?U249 in Hx; lia));
  destruct (POST (ms_mem ms) KR2 VD VF) as [HKMr HTWF];
  clear RG5 RG6 VF VD KR2;
  lc6_core HC HJ HKMr HCF;
  assert (HRKr : lc6_rk regsX (ms_regs ms))
  by (apply (lc6_rk_st _ _ _ ms regsX EX HS); [apply lc6_agree; [intros n Hn; reflexivity | reflexivity] |];
      vm_compute; reflexivity);
  lc6_reg HS (Z_to_bv 5 16) (w64 TA_M) Q16 ltac:(cbn [sv_denot]; rewrite U249, Z.add_0_r; reflexivity);
  lc6_reg HS (Z_to_bv 5 25) (YK11.getr regsX (Z_to_bv 5 25)) Q25
    ltac:(cbn [sv_denot]; unfold E0; rewrite (can_ew_Eimg_Ereg_nat regsX _ 25 (Z_to_bv 5 25) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
Ltac lc6_c1_awr U249 U25 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  do 5 (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U249 in Ha; apply lc6_inG_M; lia |];
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U25 in Ha; apply lc6_inG_OW; lia |];
  apply awr_ok_x_nil.

(* +0x6b0 .. +0x6dc: the byte g_fail_next, a6 = M, a1 = M.desk_known, M.fail := the byte, OW.desk_off := -1 (op_begin's
   world), then the tests of :380: `beqz a1` and `bnez` M.foreign to +0xf78 (lc6_D1), `bne` M.state, 3 to +0xf68
   (lc6_C2e), else +0x6e0 (lc6_C2c). *)
Lemma lc6_C1 : forall regsX memX mdX, lc6_st regsX memX mdX ->
  YK11.getr regsX (Z_to_bv 5 25) = w64 TA_OW -> lc_tw W' memX (lc6_Bm (lo_B op)) ->
  SRr segs W' (cfgX regsX LC6_C1 memX mdX) Q.
Proof.
intros regsX memX mdX (HC & HRK & HKM) R25 HTW.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof lc6_sp as (Hsp1c & Hsp1 & Hsp0 & Ho16). destruct Hsp1 as [Hsp1a Hsp1b].
change (2 ^ 47) with 140737488355328 in Hsp0.
pose proof asan_consts as ((CVlo & CVhi) & _).
pose proof HC as (HJ & _ & _ & _ & _ & _ & R9c & _ & _ & _ & Hsp1al & _).
pose proof HL as (_ & _ & HSP & _).
pose proof lc6_lenB as HLB. pose proof (lc6_len_B1 _ HLB) as HL1.
assert (R9 : YK11.getr regsX (Z_to_bv 5 9) = w64 (lc_sp1 cx)) by exact (eq_trans (HRK (Z_to_bv 5 9) ltac:(lc6_inK)) R9c).
assert (R20X : YK11.getr regsX (Z_to_bv 5 20) = w64 LF_S4) by exact (eq_trans (HRK (Z_to_bv 5 20) ltac:(lc6_inK)) R20).
(* the spill slot of M, at this memory *)
assert (HSPM : rdword (aview segs (w_H W') memX) (lc_sp1 cx + 184) = Some TA_M).
{ unfold lc_spills in HSP. rewrite Forall_forall in HSP.
  pose proof (HSP (184, TA_M) ltac:(unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm; cbn [In app];
    repeat (first [left; reflexivity | right]))) as H184. cbn [fst snd] in H184. rewrite <- H184.
  apply rdword_ext. intros i Hi. apply HKM; [lia | | lia].
  intros HG. pose proof (proj2 (inG_G_HARNESS_hull _ HG)) as Hh. unfold TG.G_HARNESS_HI in Hh. lia. }
pose proof (lc6_c1_entry (fx := l_fx cx) W' regsX memX _ (lc_sp1 cx) R9 R20X R25 ltac:(lia) ltac:(lia) Hsp1al HSPM HTW)
  as HS.
set (E0 := Eimg (PI := PI_transport) (Ereg regsX (lc6_c1_ex (lc6_Bm (lo_B op))))) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (SHOK : sh_ok segs LC6_Bx (@nil shent) E0 (mrestrict (w_H W') memX)) by constructor.
assert (U25 : bv_unsigned (ew E0 25%nat) = TA_OW)
  by (unfold E0; exact (lc6_U regsX _ 25 (Z_to_bv 5 25) TA_OW eq_refl R25 ltac:(unfold TA_OW; lia))).
assert (U249 : bv_unsigned (ew E0 249%nat) = TA_M).
{ unfold E0. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). change 249%nat with (A_OBJ 8).
  rewrite (proj1 lc6_vals). first [reflexivity | apply unsigned_lit_small; unfold TA_M; lia]. }
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
  0 []) as RUNTO.
pose proof (paj_branch (fx := l_fx cx) (PI := PI_transport)) as BR.
paj_run_tok RUN HS HJ SHOK (0, 0).
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  do 5 (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U249 in Ha; apply lc6_inG_M; lia |].
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U25 in Ha; apply lc6_inG_OW; lia |].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy mdX) mat mdX) in *. clearbody md1. clear mat. rename ms into ms1.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ ((TA_OW + 232 <= a < TA_OW + 236) \/ (TA_M + 88 <= a < TA_M + 92)) ->
  aview segs (w_H W') (ms_mem ms1) a = aview segs (w_H W') memX a).
{ intros a Ha Hn.
  apply (kept_of_frame _ _ _ _ _ (fun x => (TA_OW + 232 <= x < TA_OW + 236) \/ (TA_M + 88 <= x < TA_M + 92)) HFr);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. lc6_win Hin Hx ltac:(rewrite ?U25, ?U249 in Hx; lia). }
clear HF HFr HG.
(* the values the stretch loads, and the model's view of them *)
set (Bm := lc6_Bm (lo_B op)) in *.
pose proof (TWL.u_at_range Bm TW.A_M_desk_known 4) as Rd. pose proof (TWL.u_at_range Bm TW.A_M_foreign 4) as Rf.
pose proof (TWL.u_at_range Bm TW.A_M_state 4) as Rs.
change (2 ^ (8 * Z.of_nat 4)) with 4294967296 in Rd, Rf, Rs.
assert (E32 : ew E0 32 = Z_to_bv 64 (TW.u_at Bm TW.OFF_g_fail_next 1))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsX _ 0)).
assert (E33 : ew E0 33 = Z_to_bv 64 (TW.u_at Bm TW.A_M_desk_known 4))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsX _ 1)).
assert (E34 : ew E0 34 = Z_to_bv 64 (TW.u_at Bm TW.A_M_foreign 4))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsX _ 2)).
assert (E35 : ew E0 35 = Z_to_bv 64 (TW.u_at Bm TW.A_M_state 4))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsX _ 3)).
pose proof (lc6_sext_den E0 33 _ E33 Rd) as D33. pose proof (lc6_sext_den E0 34 _ E34 Rf) as D34.
pose proof (lc6_sext_den E0 35 _ E35 Rs) as D35.
pose proof (TWL.s32_range Bm TW.A_M_desk_known) as S33. pose proof (TWL.s32_range Bm TW.A_M_foreign) as S34.
pose proof (TWL.s32_range Bm TW.A_M_state) as S35. unfold TW.s32_at in S33, S34, S35.
pose proof (lc6_fields_B1 _ HLB) as (EFd & EFf & EFs). fold Bm in EFd, EFf, EFs.
pose proof (lc6_close_eq _ HLB) as EC.
assert (DG : sv_denot E0 (SOff 32 0) = Z_to_bv 64 (TW.g_fail_next (lc6_B3 (lo_B op)))).
{ cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned, (lc6_gfn _ HLB). reflexivity. }
assert (DM1 : sv_denot E0 (SLit 18446744073709551615) = Z_to_bv 64 (-1)) by (apply bv_eq; reflexivity).
(* what a run from the first branch keeps, and op_begin's world *)
assert (POST : forall m2,
  (forall a, 0 <= a < 2 ^ 64 -> ~ ((TA_OW + 232 <= a < TA_OW + 236) \/ (TA_M + 88 <= a < TA_M + 92)) ->
     aview segs (w_H W') m2 a = aview segs (w_H W') memX a) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W') m2 (TA_OW + 232 + Z.of_nat j) = Some (YO0f.le_byte (-1) 4 j)) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W') m2 (TA_M + 88 + Z.of_nat j) =
     Some (YO0f.le_byte (TW.g_fail_next (lc6_B3 (lo_B op))) 4 j)) ->
  lc6_km cx W' memX m2 /\ lc_tw W' m2 (lc6_B1 (lo_B op))).
{ intros m2 KR2 VD VF. split.
  - intros a Ha HnG _. apply KR2; [exact Ha|]. intros [H1 | H1]; apply HnG; [apply lc6_inG_OW | apply lc6_inG_M]; lia.
  - apply (lc6_w_c1 _ (aview segs (w_H W') memX) _ HTW VD VF).
    intros x Hx N1 N2. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    apply KR2; [lia | intros [H1 | H1]; [exact (N1 H1) | exact (N2 H1)]]. }
psrr_branch_tok RUN BR HS SHOK (0, 0).
- (* M.desk_known = 0 (:380 false): +0xf78 *)
  rewrite D33 in Hc. change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hc. cbn [branch_taken] in Hc.
  rewrite (lc6_eqb _ 0 S33 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
  assert (Ecnd : (TC.truth (TW.M_desk_known (lc6_B1 (lo_B op))) && negb (TC.truth (TW.M_foreign (lc6_B1 (lo_B op)))) &&
    negb (TW.M_state (lc6_B1 (lo_B op)) =? TC.S_CLOSED)) = false)
    by (unfold TC.truth; rewrite EFd, Hc; reflexivity).
  rewrite Ecnd in EC. cbv beta iota in EC.
  paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LC6_D1.
  { lc6_c1_awr U249 U25. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  lc6_c1_exit HS HFr KR1 ms HJ HCF HKMr HTWF HRKr Q16 Q25 U249 U25 POST DG DM1 HC regsX E0 memX (lc6_c1_ex Bm).
  clear HF HFr HG.
  pmkst HS.
  exact (lc6_D1 (lc6_B1 (lo_B op)) (ms_regs ms) (ms_mem ms) md2
    (conj HCF (conj (lc6_rk_trans _ _ _ HRK HRKr) (lc6_km_trans _ _ _ _ _ HKM HKMr)))
    Q16 (eq_trans Q25 R25) HL1 (lc6_zero_B1 _ 0 HLB (or_introl eq_refl)) HTWF EC).
- (* desk known: M.foreign *)
  rewrite D33 in Hc. change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hc. cbn [branch_taken] in Hc.
  rewrite (lc6_eqb _ 0 S33 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc. rename Hc into Hdk.
  paj_run_tok RUN HS HJ SHOK (0, 0).
  { lc6_c1_awr U249 U25. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat. rename ms into ms2.
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ ((TA_OW + 232 <= a < TA_OW + 236) \/ (TA_M + 88 <= a < TA_M + 92)) ->
    aview segs (w_H W') (ms_mem ms2) a = aview segs (w_H W') memX a).
  { intros a Ha Hn. rewrite <- (KR1 a Ha Hn).
    apply (kept_of_frame _ _ _ _ _ (fun x => (TA_OW + 232 <= x < TA_OW + 236) \/ (TA_M + 88 <= x < TA_M + 92)) HFr);
      [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx. lc6_win Hin Hx ltac:(rewrite ?U25, ?U249 in Hx; lia). }
  clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  + (* M.foreign <> 0 (:380 false): +0xf78 *)
    rewrite D34 in Hc. change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hc. cbn [branch_taken] in Hc.
    rewrite (lc6_eqb _ 0 S34 ltac:(lia)) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
    assert (Ecnd : (TC.truth (TW.M_desk_known (lc6_B1 (lo_B op))) && negb (TC.truth (TW.M_foreign (lc6_B1 (lo_B op)))) &&
      negb (TW.M_state (lc6_B1 (lo_B op)) =? TC.S_CLOSED)) = false)
      by (unfold TC.truth; rewrite EFf, (proj2 (Z.eqb_neq _ _) Hc); cbn [negb]; rewrite andb_false_r; reflexivity).
    rewrite Ecnd in EC. cbv beta iota in EC.
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LC6_D1.
    { lc6_c1_awr U249 U25. }
    set (md3 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md3. clear mat.
    lc6_c1_exit HS HFr KR2 ms HJ HCF HKMr HTWF HRKr Q16 Q25 U249 U25 POST DG DM1 HC regsX E0 memX (lc6_c1_ex Bm).
    clear HF HFr HG.
    pmkst HS.
    exact (lc6_D1 (lc6_B1 (lo_B op)) (ms_regs ms) (ms_mem ms) md3
      (conj HCF (conj (lc6_rk_trans _ _ _ HRK HRKr) (lc6_km_trans _ _ _ _ _ HKM HKMr)))
      Q16 (eq_trans Q25 R25) HL1 (lc6_zero_B1 _ 0 HLB (or_introl eq_refl)) HTWF EC).
  + (* not foreign: M.state *)
    rewrite D34 in Hc. change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hc. cbn [branch_taken] in Hc.
    rewrite (lc6_eqb _ 0 S34 ltac:(lia)) in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hfr.
    paj_run_tok RUN HS HJ SHOK (0, 0).
    { lc6_c1_awr U249 U25. }
    set (md3 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md3. clear mat. rename ms into ms3.
    assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> ~ ((TA_OW + 232 <= a < TA_OW + 236) \/ (TA_M + 88 <= a < TA_M + 92)) ->
      aview segs (w_H W') (ms_mem ms3) a = aview segs (w_H W') memX a).
    { intros a Ha Hn. rewrite <- (KR2 a Ha Hn).
      apply (kept_of_frame _ _ _ _ _ (fun x => (TA_OW + 232 <= x < TA_OW + 236) \/ (TA_M + 88 <= x < TA_M + 92)) HFr);
        [| exact Ha | exact Hn].
      intros b wlo whi x Hin Hx. lc6_win Hin Hx ltac:(rewrite ?U25, ?U249 in Hx; lia). }
    clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK (0, 0).
    * (* M.state <> S_CLOSED (:380 true): +0xf68 *)
      rewrite D35 in Hc. change (sv_denot E0 (SLit 3)) with (Z_to_bv 64 3) in Hc. cbn [branch_taken] in Hc.
      rewrite (lc6_eqb _ 3 S35 ltac:(lia)) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LC6_C2E.
      { lc6_c1_awr U249 U25. }
      set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
      lc6_c1_exit HS HFr KR3 ms HJ HCF HKMr HTWF HRKr Q16 Q25 U249 U25 POST DG DM1 HC regsX E0 memX (lc6_c1_ex Bm).
      clear HF HFr HG.
      pmkst HS.
      apply (lc6_C2e (ms_regs ms) (ms_mem ms) md4
        (conj HCF (conj (lc6_rk_trans _ _ _ HRK HRKr) (lc6_km_trans _ _ _ _ _ HKM HKMr)))
        Q16 (eq_trans Q25 R25) HTWF).
      unfold TC.truth. change TC.S_CLOSED with 3.
      rewrite EFd, EFf, EFs, (proj2 (Z.eqb_neq _ _) Hdk), Hfr, (proj2 (Z.eqb_neq _ _) Hc).
      reflexivity.
    * (* M.state = S_CLOSED: +0x6e0 *)
      rewrite D35 in Hc. change (sv_denot E0 (SLit 3)) with (Z_to_bv 64 3) in Hc. cbn [branch_taken] in Hc.
      rewrite (lc6_eqb _ 3 S35 ltac:(lia)) in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LC6_C2C.
      { lc6_c1_awr U249 U25. }
      set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
      lc6_c1_exit HS HFr KR3 ms HJ HCF HKMr HTWF HRKr Q16 Q25 U249 U25 POST DG DM1 HC regsX E0 memX (lc6_c1_ex Bm).
      clear HF HFr HG.
      pmkst HS.
      exact (lc6_C2c (ms_regs ms) (ms_mem ms) md4
        (conj HCF (conj (lc6_rk_trans _ _ _ HRK HRKr) (lc6_km_trans _ _ _ _ _ HKM HKMr)))
        Q16 HTWF (eq_trans EFs Hc)).
Qed.

(* +0x69c .. +0x6ac: a0 = GOT, a1 = 0, a2 = 224, `jal __asan_memset`; then the memset (gx_intrin_at). *)
Lemma lc6_B : forall regsX memX mdX, lc6_st regsX memX mdX ->
  YK11.getr regsX (Z_to_bv 5 25) = w64 TA_OW -> lc_tw W' memX (lc6_Bo (lo_B op)) ->
  SRr segs W' (cfgX regsX LC6_B memX mdX) Q.
Proof.
intros regsX memX mdX (HC & HRK & HKM) R25 HTW.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof lc6_sp as (Hsp1c & Hsp1 & Hsp0 & Ho16).
pose proof asan_consts as ((CVlo & CVhi) & _).
pose proof HC as (HJ & _ & _ & _ & Rsp & _ & _ & Rgp & Rtp & _).
set (E0 := Eimg (PI := PI_transport) (Ereg regsX [])).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
pose proof (lc6_entry0 (fx := l_fx cx) W' regsX memX LC6_B) as HS. fold E0 in HS.
assert (SHOK : sh_ok segs (SOff 26 0) (@nil shent) E0 (mrestrict (w_H W') memX)) by constructor.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regsX r)
  by (intros n r Hn; unfold E0; apply can_ew_Eimg_Ereg_nat; exact Hn).
destruct lc6_vals as (V8 & V12 & V13).
assert (U13 : bv_unsigned (ew E0 254%nat) = TA_GOT).
{ unfold E0. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). change 254%nat with (A_OBJ 13). rewrite V13.
  apply unsigned_lit_small. unfold TA_GOT. lia. }
paj_run_tok RUN HS HJ SHOK (0, 0).
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy mdX) mat mdX) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') memX a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
  intros b wlo whi x Hin Hx. lc6_win Hin Hx ltac:(idtac). }
clear HF HFr HG.
pmkst HS.
lc6_reg HS (Z_to_bv 5 10) (Z_to_bv 64 TA_GOT) Q10 ltac:(cbn [sv_denot]; rewrite U13, Z.add_0_r; reflexivity).
lc6_reg HS (Z_to_bv 5 11) (Z_to_bv 64 0) Q11 ltac:(reflexivity).
lc6_reg HS (Z_to_bv 5 12) (Z_to_bv 64 224) Q12 ltac:(reflexivity).
lc6_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + LC6_C1)) R1 ltac:(apply codeptr_val; exact HEI).
assert (HRK1 : lc6_rk regsX (ms_regs ms)).
{ apply (lc6_rk_st _ _ _ ms regsX [] HS); [apply lc6_agree; [intros n Hn; reflexivity | reflexivity] |].
  vm_compute. reflexivity. }
assert (R25b : YK11.getr (ms_regs ms) (Z_to_bv 5 25) = w64 TA_OW).
{ lc6_reg HS (Z_to_bv 5 25) (YK11.getr regsX (Z_to_bv 5 25)) Q25
    ltac:(cbn [sv_denot]; rewrite (EE 25%nat (Z_to_bv 5 25) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  rewrite Q25. exact R25. }
assert (Rsp1 : YK11.getr (ms_regs ms) (Z_to_bv 5 2) = w64 (lc_sp1 cx))
  by exact (eq_trans (HRK1 (Z_to_bv 5 2) ltac:(lc6_inK)) (eq_trans (HRK (Z_to_bv 5 2) ltac:(lc6_inK)) Rsp)).
assert (R3 : YK11.getr (ms_regs ms) (Z_to_bv 5 3) = w64 (as_gp B))
  by exact (eq_trans (HRK1 (Z_to_bv 5 3) ltac:(lc6_inK)) (eq_trans (HRK (Z_to_bv 5 3) ltac:(lc6_inK)) Rgp)).
assert (R4 : YK11.getr (ms_regs ms) (Z_to_bv 5 4) = w64 (as_tp B))
  by exact (eq_trans (HRK1 (Z_to_bv 5 4) ltac:(lc6_inK)) (eq_trans (HRK (Z_to_bv 5 4) ltac:(lc6_inK)) Rtp)).
assert (HKM1 : lc6_km cx W' memX (ms_mem ms)) by (intros a Ha _ _; exact (KR1 a Ha)).
lc6_core HC HJ HKM1 HC1.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
destruct (lc6_sh_GOT B (lp_recv_cells _ _ _ _ _ HP) ly' S' W' (ms_mem ms) md1 HAR1) as [HRA HHULL].
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transport_sigma TS___asan_memset)) mm rom) mdx) Qx) end.
eapply SRr_bind.
{ apply (@gx_intrin_at (l_fx cx) rc tfib_sink_head segs B LAWS transport_segs_low OSet
    (transport_sigma TS___asan_memset) (lp_memset _ _ _ _ _ HP (l_fx cx)) TG.G_HARNESS W' (ms_regs ms) (ms_mem ms)
    _ _ _ _ _ _ _ _ _ ly' S' md1 e TA_GOT 0 224 (lc_sp1 cx - lc_sp0 cx) (Z_to_bv 64 (BASE + LC6_C1)) HGX G_HARNESS_rw
    HJ Q10 Q11 Q12).
  - lia.
  - unfold TA_GOT. lia.
  - unfold TA_GOT. lia.
  - unfold spZ. transitivity (bv_unsigned (w64 (lc_sp1 cx))); [f_equal; exact Rsp1|].
    unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact Ho16.
  - lia.
  - unfold ESTACK, LLVMF_STK. lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold LC6_C1; lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. intros a Ha. right.
    apply (lc6_inG_row _ _ _ a TMAP_A_GOT). unfold TW.SZ_GOT. lia.
  - left. unfold kLowMemEnd, TA_GOT. lia.
  - exact HRA.
  - intros _. exact HHULL.
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hset2 & Heff2 & Hgr2).
assert (HKM2 : lc6_km cx W' (ms_mem ms) mem2).
{ intros a Ha HnG Hw. apply Heff2; [exact Ha | | unfold ESTACK; lia].
  intros Hd. apply HnG. apply (lc6_inG_row _ _ _ a TMAP_A_GOT). unfold TW.SZ_GOT. lia. }
lc6_core HC1 HJ2 HKM2 HC2.
apply (lc6_C1 regs2 mem2 md2).
- split; [exact HC2|]. split.
  + exact (lc6_rk_trans _ _ _ HRK (lc6_rk_trans _ _ _ HRK1 (lc6_rk_pres _ _ HP2))).
  + exact (lc6_km_trans _ _ _ _ _ HKM (lc6_km_trans _ _ _ _ _ HKM1 HKM2)).
- rewrite (HP2 25 ltac:(unfold acallee_saved; lia)). exact R25b.
- unfold lc_tw. apply (lc6_w_set (aview segs (w_H W') memX) _ (lc6_Bo (lo_B op)) TW.OFF_GOT TA_GOT TW.SZ_GOT HTW TMAP_A_GOT).
  + unfold TW.SZ_GOT. lia.
  + intros i Hi. exact (Hset2 i Hi).
  + intros x Hx Hn. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    rewrite (Heff2 x ltac:(lia) Hn ltac:(unfold ESTACK; lia)). exact (KR1 x ltac:(lia)).
Qed.

(* +0x684 .. +0x698: s9 = OW, a0 = OW, a1 = 0, a2 = 304, `jal __asan_memset`; then the memset (gx_intrin_at). *)
Lemma lc6_A : SRr segs W' (cfgX regs' LC6_A mem' md') Q.
Proof.
pose proof HL as (HC & _).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof lc6_sp as (Hsp1c & Hsp1 & Hsp0 & Ho16).
pose proof asan_consts as ((CVlo & CVhi) & _).
pose proof HC as (HJ & _ & _ & _ & Rsp & _ & _ & Rgp & Rtp & _).
set (E0 := Eimg (PI := PI_transport) (Ereg regs' [])).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
pose proof (lc6_entry0 (fx := l_fx cx) W' regs' mem' LC6_A) as HS. fold E0 in HS.
assert (SHOK : sh_ok segs (SOff 26 0) (@nil shent) E0 (mrestrict (w_H W') mem')) by constructor.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
destruct lc6_vals as (V8 & V12 & V13).
assert (U12 : bv_unsigned (ew E0 253%nat) = TA_OW).
{ unfold E0. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). change 253%nat with (A_OBJ 12). rewrite V12.
  apply unsigned_lit_small. unfold TA_OW. lia. }
paj_run_tok RUN HS HJ SHOK (0, 0).
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md') mat md') in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') mem' a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
  intros b wlo whi x Hin Hx. lc6_win Hin Hx ltac:(idtac). }
clear HF HFr HG.
pmkst HS.
lc6_reg HS (Z_to_bv 5 10) (Z_to_bv 64 TA_OW) Q10 ltac:(cbn [sv_denot]; rewrite U12, Z.add_0_r; reflexivity).
lc6_reg HS (Z_to_bv 5 11) (Z_to_bv 64 0) Q11 ltac:(reflexivity).
lc6_reg HS (Z_to_bv 5 12) (Z_to_bv 64 304) Q12 ltac:(reflexivity).
lc6_reg HS (Z_to_bv 5 25) (Z_to_bv 64 TA_OW) Q25 ltac:(cbn [sv_denot]; rewrite U12, Z.add_0_r; reflexivity).
lc6_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + LC6_B)) R1 ltac:(apply codeptr_val; exact HEI).
assert (HRK1 : lc6_rk regs' (ms_regs ms)).
{ apply (lc6_rk_st _ _ _ ms regs' [] HS); [apply lc6_agree; [intros n Hn; reflexivity | reflexivity] |].
  vm_compute. reflexivity. }
assert (Rsp1 : YK11.getr (ms_regs ms) (Z_to_bv 5 2) = w64 (lc_sp1 cx))
  by exact (eq_trans (HRK1 (Z_to_bv 5 2) ltac:(lc6_inK)) Rsp).
assert (R3 : YK11.getr (ms_regs ms) (Z_to_bv 5 3) = w64 (as_gp B))
  by exact (eq_trans (HRK1 (Z_to_bv 5 3) ltac:(lc6_inK)) Rgp).
assert (R4 : YK11.getr (ms_regs ms) (Z_to_bv 5 4) = w64 (as_tp B))
  by exact (eq_trans (HRK1 (Z_to_bv 5 4) ltac:(lc6_inK)) Rtp).
assert (HKM1 : lc6_km cx W' mem' (ms_mem ms)) by (intros a Ha _ _; exact (KR1 a Ha)).
lc6_core HC HJ HKM1 HC1.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
destruct (lc6_sh_OW B (lp_recv_cells _ _ _ _ _ HP) ly' S' W' (ms_mem ms) md1 HAR1) as [HRA HHULL].
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transport_sigma TS___asan_memset)) mm rom) mdx) Qx) end.
eapply SRr_bind.
{ apply (@gx_intrin_at (l_fx cx) rc tfib_sink_head segs B LAWS transport_segs_low OSet
    (transport_sigma TS___asan_memset) (lp_memset _ _ _ _ _ HP (l_fx cx)) TG.G_HARNESS W' (ms_regs ms) (ms_mem ms)
    _ _ _ _ _ _ _ _ _ ly' S' md1 e TA_OW 0 304 (lc_sp1 cx - lc_sp0 cx) (Z_to_bv 64 (BASE + LC6_B)) HGX G_HARNESS_rw
    HJ Q10 Q11 Q12).
  - lia.
  - unfold TA_OW. lia.
  - unfold TA_OW. lia.
  - unfold spZ. transitivity (bv_unsigned (w64 (lc_sp1 cx))); [f_equal; exact Rsp1|].
    unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact Ho16.
  - lia.
  - unfold ESTACK, LLVMF_STK. lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold LC6_B; lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. intros a Ha. right.
    apply (lc6_inG_row _ _ _ a TMAP_A_OW). unfold TW.SZ_OW. lia.
  - left. unfold kLowMemEnd, TA_OW. lia.
  - exact HRA.
  - intros _. exact HHULL.
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hset2 & Heff2 & Hgr2).
assert (HKM2 : lc6_km cx W' (ms_mem ms) mem2).
{ intros a Ha HnG Hw. apply Heff2; [exact Ha | | unfold ESTACK; lia].
  intros Hd. apply HnG. apply (lc6_inG_row _ _ _ a TMAP_A_OW). unfold TW.SZ_OW. lia. }
lc6_core HC1 HJ2 HKM2 HC2.
apply (lc6_B regs2 mem2 md2).
- split; [exact HC2|]. split.
  + exact (lc6_rk_trans _ _ _ HRK1 (lc6_rk_pres _ _ HP2)).
  + exact (lc6_km_trans _ _ _ _ _ HKM1 HKM2).
- rewrite (HP2 25 ltac:(unfold acallee_saved; lia)). exact Q25.
- unfold lc_tw. apply (lc6_w_set (aview segs (w_H W') mem') _ (lo_B op) TW.OFF_OW TA_OW TW.SZ_OW Htw0 TMAP_A_OW).
  + unfold TW.SZ_OW. lia.
  + intros i Hi. exact (Hset2 i Hi).
  + intros x Hx Hn. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    rewrite (Heff2 x ltac:(lia) Hn ltac:(unfold ESTACK; lia)). exact (KR1 x ltac:(lia)).
Qed.

End op6.

Lemma lc_op6a_ok : lc_op6a_stmt B MT XL RLO RHI.
Proof.
unfold lc_op6a_stmt. intros HP cx op W' c' HB HA.
destruct HA as (ly' & S' & regs' & mem' & md' & e & Hc & Ho6 & HL & Htw & _ & Hcur & R20 & R22).
subst c'.
assert (Ho : lc_opc (l_pl cx) (lo_c op) = 6) by (symmetry; exact Ho6).
unfold lc_cfg. rewrite lc6_arm6, <- lc6_base. unfold w64.
exact (lc6_A cx op ly' S' W' regs' mem' md' e HP HB HL Ho Hcur R20 R22 Htw).
Qed.

End seg.
