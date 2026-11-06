(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 1111 of its 1210 lines of code are new or changed and 827 lines of the source are left out. *)
(* m_wake: Theorem transport_m_wake_cg_holds : the statement transport_m_wake_cg_holds_stmt of
   lib/B/Prog/m_wake_cg.v, the machine walk of m_wake on fuzz_transport.asan-ubsan at 0x83914 (136 bytes, frame 16),
   listing lib/B/Prog/DgnTransportBList.v slots 2461 .. 2494 (AF_m_wake = 0x2674).

   The walk is a G-form walk: it holds the caller's journal ajournal_gx G_HARNESS_B 0 [] (lib/A/W_journalG.v) from the
   entry to the return, and the runs are the symbolic runs of lib/A/Prog/PaShadow.v taken over that journal
   (lib/B/Prog/TransportGRunB.v paj_run_x). The stores into M and OW are allowed by the run's write right awr_ok_x
   (a byte of G). m_wake has no instrumented check (no shadow entry: SH = []). The code, as the listing gives it:

     +0x00 .. +0x04  addi sp, sp, -16; sd ra, 8(sp)
     +0x08 .. +0x0c  a0 = &M (A_OBJ 8 = TB_M)
     +0x10 .. +0x14  a1 = M.desk_known (lw M + 0); beqz a1, +0x28
     +0x18 .. +0x1c  a1 = M.foreign (lw M + 24); beqz a1, +0x30
     +0x20 .. +0x24  a0 = -10; j +0x78                            (M.foreign <> 0)
     +0x28 .. +0x2c  a0 = -1; j +0x78                             (M.desk_known = 0)
     +0x30 .. +0x34  a1 = auipc (A_HI 97); a3 = OW.e2 (lw A_OBJ 43 = TB_OW + 196)
     +0x38 .. +0x3c  a2 = auipc (A_HI 98); a4 = g_now (ld A_OBJ 28 = TB_g_now)
     +0x40           a2 = OW.e2 + 1 (addiw)
     +0x44 .. +0x48  sd zero, 16(a0) (M.e2_acked, M.e1_us); sd a4, 40(a0) (M.wake_sent)
     +0x4c           blt a2, a3, +0x84 (the unimp trap: OW.e2 = INT_MAX)
     +0x50           a3 = M.fail (lw M + 88)
     +0x54 .. +0x58  sw a2, 0x460(a1) (OW.e2: A_HI 97 + 0x460 = TB_OW + 196); sw zero, 88(a0) (M.fail)
     +0x5c           beqz a3, +0x68
     +0x60 .. +0x64  a0 = -5; j +0x78                             (old M.fail <> 0)
     +0x68 .. +0x70  a0 = 1; a1 = 1; call m_set (0x85224), return address +0x74
     +0x74           a0 = 0
     +0x78 .. +0x80  ld ra, 8(sp); addi sp, sp, 16; ret
     +0x84           unimp (0xc0001073)

   OW.e2 is read through A_OBJ 43 and written through the auipc register A_HI 97 with offset 0x460: the run's facts
   carry the alias (SOff (A_HI 97) 0x460, SOff (A_OBJ 43) 0), so the load and the store use one region.

   Runs and splits: run 1 to the desk_known test; run 2 to the foreign test; run 3 to the trap test, refuted by the
   model premise (TCb.v m_wake_m is None when OW.e2 = INT_MAX); run 4 to the fail test; run 5 to the call of m_set.
   The call is m_set's statement (the premise of the holds statement) on the same G journal at the model's world
   B4 = mwb_W Bw; its return state is the run's state after the call (DgnTransportBPaLib.v st_ok_pi_after_call,
   keeping the stack region, whose bytes the callee keeps: they lie above its window); run 6 is the epilogue.
   The posts: mwb_close (the three early returns) and mwb_close_call (the return after m_set: m_set's written range
   mset_st_wr B4 1 lies in mwake_wr Bw because B4 has Bw's M.state and OW.n, and the epilogue writes no byte of G). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h YC1i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg m_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TCb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TCB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.

(* ------------------------------------------------------------------ *)
(* 1. The model: m_wake_m as a flat cascade, and its world B4 in the    *)
(*    order the binary writes it.                                       *)
(* ------------------------------------------------------------------ *)

Lemma mwb_firstn_app_add : forall (l1 l2 : list byte) n, firstn (length l1 + n) (l1 ++ l2) = l1 ++ firstn n l2.
Proof. induction l1 as [|x l1 IH]; intros l2 n; cbn; [reflexivity | f_equal; apply IH]. Qed.

Lemma mwb_skipn_app_add : forall (l1 l2 : list byte) n, skipn (length l1 + n) (l1 ++ l2) = skipn n l2.
Proof. induction l1 as [|x l1 IH]; intros l2 n; cbn; [reflexivity | apply IH]. Qed.

Lemma mwb_firstn_app_self : forall (l1 l2 : list byte), firstn (length l1) (l1 ++ l2) = l1.
Proof. induction l1 as [|x l1 IH]; intros l2; cbn; [reflexivity | f_equal; apply IH]. Qed.

Lemma mwb_upd_app : forall (bs v w : list byte) k,
  0 <= k -> (Z.to_nat k + length v <= length bs)%nat ->
  TW.upd bs k (v ++ w) = TW.upd (TW.upd bs k v) (k + Z.of_nat (length v)) w.
Proof.
  intros bs v w k Hk Hl.
  assert (LL : length (firstn (Z.to_nat k) bs) = Z.to_nat k) by (rewrite length_firstn; lia).
  unfold TW.upd. rewrite length_app.
  replace (Z.to_nat (k + Z.of_nat (length v))) with (Z.to_nat k + length v)%nat by lia.
  replace (Z.to_nat k + length v)%nat with (length (firstn (Z.to_nat k) bs) + length v)%nat by lia.
  rewrite mwb_firstn_app_add, mwb_firstn_app_self.
  replace (length (firstn (Z.to_nat k) bs) + length v + length w)%nat
    with (length (firstn (Z.to_nat k) bs) + (length v + length w))%nat by lia.
  rewrite mwb_skipn_app_add, mwb_skipn_app_add, skipn_skipn.
  replace (length w + (length (firstn (Z.to_nat k) bs) + length v))%nat
    with (Z.to_nat k + (length v + length w))%nat by lia.
  rewrite <- !app_assoc. reflexivity.
Qed.

(* the 8-byte zeroing of M.e2_acked / M.e1_us (one sd) is the model's two 4-byte stores *)
Lemma mwb_upd_zero8 : forall (bs : list byte) k k', 0 <= k -> k' = k + 4 -> k + 8 <= Z.of_nat (length bs) ->
  TW.upd (TW.upd bs k (TW.put 4 0)) k' (TW.put 4 0) = TW.upd bs k (TW.put 8 0).
Proof.
  intros bs k k' Hk -> Hl.
  replace (TW.put 8 0) with (TW.put 4 0 ++ TW.put 4 0) by (vm_compute; reflexivity).
  rewrite (mwb_upd_app bs (TW.put 4 0) (TW.put 4 0) k) by (rewrite ?TWL.length_put; lia).
  rewrite TWL.length_put. reflexivity.
Qed.

Lemma mwb_wlen_upd : forall (bs : list byte) k n v,
  Z.of_nat (length bs) = 65616 -> 0 <= k -> k + Z.of_nat n <= 65616 ->
  Z.of_nat (length (TW.upd bs k (TW.put n v))) = 65616.
Proof. intros bs k n v H Hk Hn. rewrite TWL.length_upd_put; [exact H | lia | lia]. Qed.

Ltac mwb_wlen := repeat (apply mwb_wlen_upd; [ | lia | lia ]); assumption.
Ltac mwb_wside :=
  rewrite ?TWL.length_put;
  first [ lia
        | match goal with
          | |- context [Z.of_nat (length ?X)] =>
              let H := fresh "HW" in assert (H : Z.of_nat (length X) = 65616) by mwb_wlen; rewrite H; lia
          end ].

Lemma mwb_s32_peel : forall (bs : list byte) k n v k',
  Z.of_nat (length bs) = 65616 -> 0 <= k -> 0 <= k' -> k + Z.of_nat n <= 65616 ->
  (k' + 4 <= k \/ k + Z.of_nat n <= k') ->
  TW.s32_at (TW.upd bs k (TW.put n v)) k' = TW.s32_at bs k'.
Proof.
  intros bs k n v k' HL Hk Hk' Hn Hd.
  rewrite TWL.s32_at_upd_out; [reflexivity | lia | lia | rewrite TWL.length_put; lia | rewrite TWL.length_put; lia].
Qed.

Lemma mwb_u_peel : forall (bs : list byte) k n v k' n',
  Z.of_nat (length bs) = 65616 -> 0 <= k -> 0 <= k' -> k + Z.of_nat n <= 65616 ->
  (k' + Z.of_nat n' <= k \/ k + Z.of_nat n <= k') ->
  TW.u_at (TW.upd bs k (TW.put n v)) k' n' = TW.u_at bs k' n'.
Proof.
  intros bs k n v k' n' HL Hk Hk' Hn Hd.
  rewrite TWL.u_at_upd_out; [reflexivity | lia | lia | rewrite TWL.length_put; lia | rewrite TWL.length_put; lia].
Qed.

Ltac mwb_peelg :=
  repeat first [ rewrite mwb_s32_peel by (first [mwb_wlen | lia]) | rewrite mwb_u_peel by (first [mwb_wlen | lia]) ].

(* the model's world, re-ordered into the order the binary writes it *)
Ltac mwb_to_machine Bw :=
  mwb_peelg;
  rewrite (mwb_upd_zero8 _ 16 20) by (first [lia | mwb_wside]);
  rewrite (TWL.upd_upd_comm _ (TW.put 8 (TW.u_at Bw 65000 8)) (TW.put 4 (TW.s32_at Bw 65508 + 1)) 40 65508)
    by (first [lia | mwb_wside]);
  rewrite (TWL.upd_upd_comm _ (TW.put 8 0) (TW.put 4 (TW.s32_at Bw 65508 + 1)) 16 65508)
    by (first [lia | mwb_wside]).

(* The model's intermediate worlds, named exactly as TCb.v builds them, so that the characterisation below holds by
   conversion alone. mwb_W B is the world B4 at which m_wake calls m_set. *)
Definition mwb_B1 (B : list byte) : list byte := TW.set_M_e1_us (TW.set_M_e2_acked B 0) 0.
Definition mwb_B2 (B : list byte) : list byte := TW.set_M_wake_sent (mwb_B1 B) (TW.g_now (mwb_B1 B)).
Definition mwb_B3 (B : list byte) : list byte := TW.set_OW_e2 (mwb_B2 B) (TW.OW_e2 (mwb_B2 B) + 1).
Definition mwb_W (B : list byte) : list byte := TW.set_M_fail (mwb_B3 B) 0.

Lemma mwb_m_eq : forall B,
  TCB.m_wake_m B =
    (if TW.M_desk_known B =? 0 then Some (B, -1)
     else if negb (TW.M_foreign B =? 0) then Some (B, -10)
     else if TW.OW_e2 (mwb_B2 B) =? 2 ^ 31 - 1 then None
     else if negb (TW.M_fail (mwb_B3 B) =? 0) then Some (mwb_W B, -5)
     else match TCB.m_set_m (mwb_W B) 1 1 with Some (B5, _) => Some (B5, 0) | None => None end).
Proof.
  intros B.
  unfold mwb_W, mwb_B3, mwb_B2, mwb_B1.
  unfold TCB.m_wake_m, TCB.truth, TCB.int_inc.
  cbv zeta.
  set (b1 := TW.set_M_e1_us (TW.set_M_e2_acked B 0) 0) in *.
  set (b2 := TW.set_M_wake_sent b1 (TW.g_now b1)) in *.
  destruct (TW.M_desk_known B =? 0) eqn:E1; cbn [negb]; cbv iota; [reflexivity|].
  destruct (TW.M_foreign B =? 0) eqn:E2; cbn [negb]; cbv iota; [|reflexivity].
  destruct (TW.OW_e2 b2 =? 2 ^ 31 - 1) eqn:EO; unfold TCB.INT_MAX; rewrite ?EO; cbv iota; [reflexivity|].
  set (b3 := TW.set_OW_e2 b2 (TW.OW_e2 b2 + 1)) in *.
  destruct (TW.M_fail b3 =? 0) eqn:E3; cbn [negb]; cbv iota; [|reflexivity].
  reflexivity.
Qed.

(* the world B4, read off B and written in the binary's order *)
Definition mwbm_W (B : list byte) : list byte :=
  TW.upd (TW.upd (TW.upd (TW.upd B 65508 (TW.put 4 (TW.s32_at B 65508 + 1))) 16 (TW.put 8 0))
           40 (TW.put 8 (TW.u_at B 65000 8))) 88 (TW.put 4 0).

(* Getters and setters to their literal offsets by SYNTACTIC matching and [change]. *)
Ltac mwb_gs :=
  repeat match goal with
  | |- context [TW.M_desk_known ?x] => change (TW.M_desk_known x) with (TW.s32_at x 0)
  | |- context [TW.M_foreign ?x] => change (TW.M_foreign x) with (TW.s32_at x 24)
  | |- context [TW.M_fail ?x] => change (TW.M_fail x) with (TW.s32_at x 88)
  | |- context [TW.M_state ?x] => change (TW.M_state x) with (TW.s32_at x 12)
  | |- context [TW.OW_e2 ?x] => change (TW.OW_e2 x) with (TW.s32_at x 65508)
  | |- context [TW.OW_n ?x] => change (TW.OW_n x) with (TW.s32_at x 65312)
  | |- context [TW.g_now ?x] => change (TW.g_now x) with (TW.u_at x 65000 8)
  | |- context [TW.set_M_e2_acked ?x ?v] => change (TW.set_M_e2_acked x v) with (TW.upd x 16 (TW.put 4 v))
  | |- context [TW.set_M_e1_us ?x ?v] => change (TW.set_M_e1_us x v) with (TW.upd x 20 (TW.put 4 v))
  | |- context [TW.set_M_wake_sent ?x ?v] => change (TW.set_M_wake_sent x v) with (TW.upd x 40 (TW.put 8 v))
  | |- context [TW.set_OW_e2 ?x ?v] => change (TW.set_OW_e2 x v) with (TW.upd x 65508 (TW.put 4 v))
  | |- context [TW.set_M_fail ?x ?v] => change (TW.set_M_fail x v) with (TW.upd x 88 (TW.put 4 v))
  end.

Lemma mwb_e2 : forall B, Z.of_nat (length B) = 65616 -> TW.OW_e2 (mwb_B2 B) = TW.s32_at B 65508.
Proof. intros B HL. unfold mwb_B2, mwb_B1. mwb_gs. mwb_peelg. reflexivity. Qed.

Lemma mwb_fa : forall B, Z.of_nat (length B) = 65616 -> TW.M_fail (mwb_B3 B) = TW.s32_at B 88.
Proof. intros B HL. unfold mwb_B3, mwb_B2, mwb_B1. mwb_gs. mwb_peelg. reflexivity. Qed.

Lemma mwb_st : forall B, Z.of_nat (length B) = 65616 -> TW.M_state (mwb_W B) = TW.s32_at B 12.
Proof. intros B HL. unfold mwb_W, mwb_B3, mwb_B2, mwb_B1. mwb_gs. mwb_peelg. reflexivity. Qed.

Lemma mwb_on : forall B, Z.of_nat (length B) = 65616 -> TW.OW_n (mwb_W B) = TW.s32_at B 65312.
Proof. intros B HL. unfold mwb_W, mwb_B3, mwb_B2, mwb_B1. mwb_gs. mwb_peelg. reflexivity. Qed.

Lemma mwb_W_m : forall B, Z.of_nat (length B) = 65616 -> mwb_W B = mwbm_W B.
Proof. intros B HL. unfold mwb_W, mwb_B3, mwb_B2, mwb_B1, mwbm_W. mwb_gs. mwb_to_machine B. reflexivity. Qed.

(* A Some of a world and a code, read back by name (no injection on a world-carrying option in the walk). *)
Lemma mwb_some_inv : forall (x y : list byte) (a b : Z), Some (x, a) = Some (y, b) -> y = x /\ b = a.
Proof. intros x y a b H. injection H as H1 H2. split; symmetry; assumption. Qed.

(* m_set's written range at B4 lies in m_wake's written range at Bw on the path that calls m_set: B4 has Bw's
   M.state and OW.n (mwb_st, mwb_on), and the tests the path passed are mwake_wr's guards. *)
Lemma mwb_wr_sub : forall Bw a, Z.of_nat (length Bw) = 65616 ->
  (TW.s32_at Bw 0 =? 0) = false -> (TW.s32_at Bw 24 =? 0) = true -> (TW.s32_at Bw 88 =? 0) = true ->
  mset_st_wr (mwb_W Bw) 1 a -> mwake_wr Bw a.
Proof.
  intros Bw a HL H0 H24 H88 [Hst Hwr].
  unfold mwake_wr, TCB.truth.
  change (TW.M_desk_known Bw) with (TW.s32_at Bw 0). change (TW.M_foreign Bw) with (TW.s32_at Bw 24).
  change (TW.M_fail Bw) with (TW.s32_at Bw 88).
  rewrite H0, H24, H88. cbn [negb].
  split; [reflexivity|]. split; [reflexivity|].
  right; right; right; right. split; [reflexivity|].
  rewrite (mwb_st Bw HL) in Hst. change (TW.s32_at Bw 12) with (TW.M_state Bw) in Hst.
  split; [unfold TCB.S_WAKING; exact Hst|].
  unfold mset_wr in *. rewrite (mwb_on Bw HL) in Hwr. change (TW.s32_at Bw 65312) with (TW.OW_n Bw) in Hwr.
  exact Hwr.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The symbolic state at the entry                                  *)
(* ------------------------------------------------------------------ *)

(* Atoms: 0 .. 31 the registers at the entry, 32 the shadow base (no shadow entry), 33 .. 39 the world values the
   function reads or overwrites: M.desk_known, M.foreign, OW.e2, g_now, M.fail, M[16, 24) and M[40, 48). Regions: the
   16-byte frame below sp (the save of ra), the five spans of M, OW.e2 (object 43 = TB_OW + 196) and g_now (object 28).
   A span the function stores into is writable and covered by a chunk at the entry, so every byte of every window has
   a value in each later state; every byte outside the windows is kept. *)
Definition mwbR_dk : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition mwbR_ea : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 16 24 16 24 [YP09.mkChunk 16 (CVal 8 (SOff 38 0))].
Definition mwbR_fo : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 24 28 24 24 [YP09.mkChunk 24 (CVal 4 (SOff 34 0))].
Definition mwbR_ws : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 40 48 40 48 [YP09.mkChunk 40 (CVal 8 (SOff 39 0))].
Definition mwbR_fa : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 88 92 88 92 [YP09.mkChunk 88 (CVal 4 (SOff 37 0))].
Definition mwbR_e2 : YP09.region := YP09.mkRegion (Some (A_OBJ 43)) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 35 0))].
Definition mwbR_now : YP09.region := YP09.mkRegion (Some (A_OBJ 28)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 36 0))].
(* the four written spans after the stores of +0x44 .. +0x58 *)
Definition mwbR_ea4 : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 16 24 16 24 [YP09.mkChunk 16 (CVal 8 (SLit 0))].
Definition mwbR_ws4 : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 40 48 40 48 [YP09.mkChunk 40 (CVal 8 (SOff 36 0))].
Definition mwbR_fa4 : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 88 92 88 92 [YP09.mkChunk 88 (CVal 4 (SLit 0))].
Definition mwbR_e24 : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 43)) 0 4 0 4
    [YP09.mkChunk 0 (CVal 4 (SAluw ALU_ADD (SExt true 32 (SOff 35 0)) (SLit 1)))].

Definition mwb_regions : smem :=
  [stack_region 16; mwbR_dk; mwbR_ea; mwbR_fo; mwbR_ws; mwbR_fa; mwbR_e2; mwbR_now].
Definition mwb_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (A_OBJ 8, mkAF TB_M TB_M 5); (A_OBJ 43, mkAF (TB_OW + 196) (TB_OW + 196) 2);
           (33%nat, mkAF 0 (2 ^ 32 - 1) 0); (34%nat, mkAF 0 (2 ^ 32 - 1) 0); (35%nat, mkAF 0 (2 ^ 32 - 1) 0);
           (36%nat, mkAF 0 (2 ^ 64 - 1) 0); (37%nat, mkAF 0 (2 ^ 32 - 1) 0);
           (38%nat, mkAF 0 (2 ^ 64 - 1) 0); (39%nat, mkAF 0 (2 ^ 64 - 1) 0)] []
    [(SOff (A_HI 97) 0x460, SOff (A_OBJ 43) 0)].
Definition ss_mwb : sstate := mkSS AF_m_wake sr_atoms mwb_regions None mwb_facts.
Definition MWB_SH : list shent := [].
Definition MWB_Bx : sv := SOff 32 0.
(* the first atom the call's return state uses for the caller-saved registers *)
Definition MWB_K : nat := 48.

(* The bytes the walk may write: its stack window (its frame and m_set's), and bytes of G. *)
Definition mwb_Zs (sp : Z) (a : Z) : Prop := (sp - MWAKE_STK <= a < sp) \/ inG G_HARNESS_B a.
(* The windows of the runs before the call: the frame and the four spans of M and OW. *)
Definition mwb_wins (sp : Z) (a : Z) : Prop :=
  (sp - 16 <= a < sp) \/ (TB_M + 16 <= a < TB_M + 24) \/ (TB_M + 40 <= a < TB_M + 48) \/
  (TB_M + 88 <= a < TB_M + 92) \/ (TB_OW + 196 <= a < TB_OW + 200).

(* A payload byte of image B's world table is a byte of G. *)
Lemma mwb_inG_row : forall o b n a, In (o, b, n) TMAP_B -> b <= a < b + n -> inG G_HARNESS_B a.
Proof.
intros o b n a Hin Ha. apply Exists_exists. exists (b, n).
split; [exact (TMAP_B_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.
Lemma mwb_inG_M : forall a, TB_M <= a < TB_M + TW.SZ_M -> inG G_HARNESS_B a.
Proof. intros a Ha. exact (mwb_inG_row _ _ _ a TMAP_B_M Ha). Qed.
Lemma mwb_inG_OW : forall a, TB_OW <= a < TB_OW + TW.SZ_OW -> inG G_HARNESS_B a.
Proof. intros a Ha. exact (mwb_inG_row _ _ _ a TMAP_B_OW Ha). Qed.

Lemma mwb_wins_Zs : forall sp a, mwb_wins sp a -> mwb_Zs sp a.
Proof.
intros sp a [H | [H | [H | [H | H]]]]; unfold mwb_Zs;
  first [ left; unfold MWAKE_STK, MWAKE_FRAME, MSET_STK, MSET_FRAME; lia
        | right; apply mwb_inG_M; unfold TB_M, TW.SZ_M in *; lia
        | right; apply mwb_inG_OW; unfold TB_OW, TW.SZ_OW in *; lia ].
Qed.

(* The windows of every run before the call are those of the entry regions. *)
Lemma mwb_wins_of : forall (E : env) sp rs b wlo whi a,
  windows rs = windows mwb_regions ->
  bv_unsigned (ew E 2%nat) = sp -> bv_unsigned (ew E 249%nat) = TB_M -> bv_unsigned (ew E 284%nat) = TB_OW + 196 ->
  In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> mwb_wins sp a.
Proof.
intros E sp rs b wlo whi a Hw Hsp H8 H43 Hin Hx. rewrite Hw in Hin.
lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end.
cbn [In] in Hin. unfold mwb_wins.
repeat (destruct Hin as [Hin | Hin];
  [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?Hsp, ?H8, ?H43 in Hx;
   first [ lia | left; lia | right; left; lia | right; right; left; lia | right; right; right; left; lia
         | right; right; right; right; lia ] |]).
destruct Hin.
Qed.

(* A run leaves every byte outside its regions' windows as it was (A/Prog/YC4b.v kept_of_frame). *)
Lemma mwb_kept_of_frame : forall E rs H (m m' : word -> option byte) (Zs : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> Zs a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
intros E rs H m m' Zs HFR Hw a Ha Hn. apply (aview_eq_of tfibsegs). apply HFR. rewrite unsigned_lit_small by lia.
intros Hin. destruct (in_wrange_windows E rs a Hin) as (b & wlo & whi & Hi & Hr). exact (Hn (Hw b wlo whi a Hi Hr)).
Qed.

Section fxs. Context {fx : YK11.FPState}.
(* A region of a symbolic state (A/Prog/YC4b.v st_ok_region_nth). *)
Lemma mwb_st_ok_region_nth : forall E ss ms i r,
  st_ok tfibsegs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok tfibsegs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok tfibsegs E ss ms HS) as (_ & Hrs & _).
apply nth_error_In in Hi. exact (proj1 (Forall_forall _ _) Hrs r Hi).
Qed.
End fxs.

(* ---- the byte values a region's chunks give ---- *)

Lemma mwb_shr_mod : forall X N k, 0 <= X -> 0 <= k -> k + 8 <= N ->
  Z.shiftr (X mod 2 ^ N) k mod 256 = Z.shiftr X k mod 256.
Proof.
intros X N k HX Hk HN. rewrite !Z.shiftr_div_pow2 by lia.
assert (HP : 2 ^ N = 2 ^ (N - k) * 2 ^ k) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
rewrite (Z.mod_eq X (2 ^ N)) by (apply Z.pow_nonzero; lia).
replace (X - 2 ^ N * (X / 2 ^ N)) with (X + - (2 ^ (N - k) * (X / 2 ^ N)) * 2 ^ k) by (rewrite HP; ring).
rewrite Z.div_add by (apply Z.pow_nonzero; lia).
assert (HQ : 2 ^ (N - k) = 256 * 2 ^ (N - k - 8))
  by (replace 256 with (2 ^ 8) by reflexivity; rewrite <- Z.pow_add_r by lia; f_equal; lia).
rewrite HQ. replace (X / 2 ^ k + - (256 * 2 ^ (N - k - 8) * (X / 2 ^ N)))
  with (X / 2 ^ k + - (2 ^ (N - k - 8) * (X / 2 ^ N)) * 256) by ring.
apply Z_mod_plus_full.
Qed.

Lemma mwb_bow : forall X (w : N) i, 0 <= X -> Z.of_N w <= 8 -> 0 <= i < Z.of_N w ->
  bv_unsigned (YP09.byte_of_word (Z_to_bv 64 X) i) = YO0f.le_byte X (N.to_nat w) (Z.to_nat i).
Proof.
intros X w i HX Hw Hi. unfold YP09.byte_of_word, YO0f.le_byte.
rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64).
replace (8 * Z.of_nat (N.to_nat w)) with (8 * Z.of_N w) by (rewrite N_nat_Z; reflexivity).
replace (8 * Z.of_nat (Z.to_nat i)) with (8 * i) by (rewrite Z2Nat.id by lia; reflexivity).
rewrite (mwb_shr_mod X 64 (8 * i)) by lia.
rewrite (mwb_shr_mod X (8 * Z.of_N w) (8 * i)) by lia. reflexivity.
Qed.

Lemma mwb_le_byte_mod : forall X Y (m : nat) k, X mod 2 ^ (8 * Z.of_nat m) = Y mod 2 ^ (8 * Z.of_nat m) ->
  YO0f.le_byte X m k = YO0f.le_byte Y m k.
Proof. intros X Y m k H. unfold YO0f.le_byte. rewrite H. reflexivity. Qed.

(* ---- arithmetic of the tests ---- *)

Lemma mwb_u64 : forall v, bv_unsigned (Z_to_bv 64 v) = v mod 2 ^ 64.
Proof.
intros v. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). reflexivity.
Qed.

Lemma mwb_s32_mod_inj : forall v w, - 2 ^ 31 <= v < 2 ^ 31 -> - 2 ^ 31 <= w < 2 ^ 31 ->
  v mod 2 ^ 64 = w mod 2 ^ 64 -> v = w.
Proof. intros v w Hv Hw H. Z.div_mod_to_equations. lia. Qed.

Lemma mwb_eqb_s32 : forall v w, - 2 ^ 31 <= v < 2 ^ 31 -> - 2 ^ 31 <= w < 2 ^ 31 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 w) = (v =? w).
Proof.
  intros v w Hv Hw. unfold bv_eqb. rewrite !mwb_u64.
  destruct (Z.eqb_spec v w) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intro E. apply N. exact (mwb_s32_mod_inj v w Hv Hw E).
Qed.

Lemma mwb_signed_s32 : forall v, - 2 ^ 31 <= v < 2 ^ 31 -> bv_signed (Z_to_bv 64 v) = v.
Proof.
  intros v Hv. rewrite signed_is_swrap_unsigned, mwb_u64.
  unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
  rewrite Zplus_mod_idemp_l. rewrite (Z.mod_small (v + 2 ^ 63) (2 ^ 64)) by lia. lia.
Qed.

Lemma mwb_mod64 : forall x m, 0 <= m <= 64 -> (x mod 2 ^ 64) mod 2 ^ m = x mod 2 ^ m.
Proof.
intros x m Hm. symmetry.
apply Znumtheory.Zmod_div_mod; [apply Z.pow_pos_nonneg; lia | apply Z.pow_pos_nonneg; lia|].
exists (2 ^ (64 - m)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma mwb_sext_atom : forall (E : env) atom Bw o, ew E atom = w64 (TW.u_at Bw o 4) ->
  sv_denot E (SExt true 32 (SOff atom 0)) = Z_to_bv 64 (TW.s32_at Bw o).
Proof.
intros E atom Bw o Hew. pose proof (TWL.u_at_range Bw o 4) as HR. cbn [Z.of_nat] in HR.
cbn [sv_denot]. rewrite Hew, Z.add_0_r. unfold w64.
rewrite unsigned_lit_small by lia.
change (Z_to_bv 64 (TW.u_at Bw o 4)) with (le_bytes_to_word (TW.sub Bw o 4)).
apply lw_world.
Qed.

(* addiw a, a, 1 *)
Lemma mwb_denot_aluw1 : forall (E : env) (a : sv),
  sv_denot E (SAluw ALU_ADD a (SLit 1)) = Z_to_bv 64 (zalu32 ALU_ADD (bv_unsigned (sv_denot E a)) 1).
Proof. intros E a. cbn [sv_denot]. rewrite <- zalu32_sound. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma mwb_swrap32_mod : forall y, bv_swrap 32 y mod 2 ^ 32 = y mod 2 ^ 32.
Proof.
intros y. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite Zminus_mod_idemp_l. f_equal. ring.
Qed.

(* the stored increment of a sign-extended 4-byte value, modulo the stored width *)
Lemma mwb_u_addw1 : forall (E : env) (a : sv) z, sv_denot E a = Z_to_bv 64 z ->
  U E (SAluw ALU_ADD a (SLit 1)) mod 2 ^ 32 = (z + 1) mod 2 ^ 32.
Proof.
intros E a z Hd. unfold U. rewrite mwb_denot_aluw1, Hd, !mwb_u64.
unfold zalu32, zcanon, M64, zu32, M32. cbn [zalu_raw].
repeat rewrite (mwb_mod64 _ 32) by lia. rewrite mwb_swrap32_mod.
change (1 mod 2 ^ 32) with 1. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* the trap test at +0x4c: blt (OW.e2 + 1 as int) OW.e2 is taken only at INT_MAX *)
Lemma mwb_br_trap : forall (E : env) Bw, ew E 35%nat = w64 (TW.u_at Bw 65508 4) ->
  branch_taken BC_LT (sv_denot E (SAluw ALU_ADD (SExt true 32 (SOff 35 0)) (SLit 1)))
    (sv_denot E (SExt true 32 (SOff 35 0))) = true ->
  TW.s32_at Bw 65508 = 2 ^ 31 - 1.
Proof.
intros E Bw H35 Hb.
pose proof (TWL.s32_range Bw 65508) as R.
rewrite mwb_denot_aluw1 in Hb. rewrite (mwb_sext_atom E 35 Bw 65508 H35) in Hb.
set (x := TW.s32_at Bw 65508) in *.
cbn [branch_taken] in Hb. unfold bv_lts in Hb.
unfold zalu32 in Hb. rewrite Z_to_bv64_canon in Hb.
pose proof (bv_swrap_in_range 32 (zalu_raw 31 32 ALU_ADD (zu32 (bv_unsigned (Z_to_bv 64 x))) (zu32 1))
  ltac:(discriminate)) as RS.
change (bv_half_modulus 32) with (2 ^ 31) in RS.
rewrite !mwb_signed_s32 in Hb by lia.
apply Z.ltb_lt in Hb.
cbn [zalu_raw] in Hb. unfold zu32, M32 in Hb. rewrite mwb_u64, (mwb_mod64 x 32) in Hb by lia.
change (1 mod 2 ^ 32) with 1 in Hb.
unfold bv_swrap, bv_wrap in Hb. change (bv_half_modulus 32) with (2 ^ 31) in Hb.
change (bv_modulus 32) with (2 ^ 32) in Hb.
Z.div_mod_to_equations. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The walk's lemmas                                                *)
(* ------------------------------------------------------------------ *)

Section mwakeb. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma mwb_vals : VAL (A_OBJ 8) = TB_M /\ VAL (A_OBJ 43) = TB_OW + 196 /\ VAL (A_OBJ 28) = TB_g_now /\
  VAL (A_HI 97) = TB_OW + 196 - 0x460 /\ BASE + AF_m_wake = transportb_sigma TB_m_wake /\
  BASE + AF_m_wake + 0x74 = 539016.
Proof. vm_compute. repeat split. Qed.

(* The walk's valuation: the 32 registers at the entry, the shadow base and the seven world values. *)
Definition mwb_ex (Bw : list byte) : list word :=
  [w64 SHADOW_OFF; w64 (TW.u_at Bw 0 4); w64 (TW.u_at Bw 24 4); w64 (TW.u_at Bw 65508 4); w64 (TW.u_at Bw 65000 8);
   w64 (TW.u_at Bw 88 4); w64 (TW.u_at Bw 16 8); w64 (TW.u_at Bw 40 8)].
Definition mwb_E (regs : bvmap 5 word) (Bw : list byte) : env := Eimg (PI := PI_transportb) (Ereg regs (mwb_ex Bw)).

Lemma mwb_agree : forall regs Bw E, (forall n, (n < 32)%nat -> ew E n = ew (mwb_E regs Bw) n) ->
  ed E = ed (mwb_E regs Bw) -> env_agree 32 (Ereg regs (mwb_ex Bw)) E.
Proof.
  intros regs Bw E H1 H2. split.
  - intros n Hn. rewrite (H1 n Hn). unfold mwb_E. apply Eimg_low. unfold A_TEXT. lia.
  - rewrite H2. reflexivity.
Qed.

(* A region of a payload span whose base value is rb = bb + d (bb the row's base), writable where its bytes are
   bytes of G, with one chunk holding the span's world value. *)
Lemma mwb_reg : forall (W : world segs) memc Bw (E : env) (nb : nat) (rb : Z) o bb n d lo hi wlo whi k (w : N) atom,
  tw_at TMAP_B (aview segs (w_H W) memc) Bw -> In (o, bb, n) TMAP_B -> rb = bb + d ->
  bv_unsigned (ew E nb) = rb -> 0 <= rb + lo -> rb + hi <= 2 ^ 64 ->
  (forall a, rb + wlo <= a < rb + whi -> inG G_HARNESS_B a) ->
  0 <= d + k -> d + k + Z.of_N w <= n -> Z.of_N w <= 8 -> ew E atom = w64 (TW.u_at Bw (o + (d + k)) (N.to_nat w)) ->
  region_ok segs E (mrestrict (w_H W) memc)
    (YP09.mkRegion (Some nb) lo hi wlo whi [YP09.mkChunk k (CVal w (SOff atom 0))]).
Proof.
intros W memc Bw E nb rb o bb n d lo hi wlo whi k w atom Htw Hin Hrb Hbb Hlo Hhi HG Hk Hkw Hw8 Hew.
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hbb. split; [exact Hlo|]. split; [exact Hhi|].
split; [intros o0 Ho0; apply (gx_rw_writable segs G_HARNESS_B (rb + o0) G_HARNESS_B_rw); apply HG; lia|].
constructor; [|constructor].
pose proof (TWL.u_at_range Bw (o + (d + k)) (N.to_nat w)) as HR. rewrite N_nat_Z in HR.
assert (HP : 2 ^ (8 * Z.of_N w) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
apply (chunk_ok_val segs E (mrestrict (w_H W) memc) rb k w (SOff atom 0) (TW.u_at Bw (o + (d + k)) (N.to_nat w))).
- cbn [sv_denot]. rewrite Hew, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- exact HR.
- exact Hw8.
- replace (rb + k) with (bb + (d + k)) by lia.
  apply (tw_read_val segs (mrestrict (w_H W) memc) TMAP_B Bw o bb n (d + k) (N.to_nat w) TMAP_B_ok Htw Hin Hk).
  rewrite N_nat_Z. exact Hkw.
Qed.

(* ---- the entry state ---- *)

Lemma mwb_entry : forall (W : world segs) regs memc Bw,
  tw_at TMAP_B (aview segs (w_H W) memc) Bw ->
  (forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (mwb_E regs Bw) ss_mwb
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_m_wake)) memc (YK11.seg_rom segs))).
Proof.
intros W regs memc Bw Htw Hpres Hsp Hsp16.
destruct mwb_vals as (V8 & V43 & V28 & V97 & _).
pose proof (TWL.u_at_range Bw 0 4) as R33. pose proof (TWL.u_at_range Bw 24 4) as R34.
pose proof (TWL.u_at_range Bw 65508 4) as R35. pose proof (TWL.u_at_range Bw 65000 8) as R36.
pose proof (TWL.u_at_range Bw 88 4) as R37. pose proof (TWL.u_at_range Bw 16 8) as R38.
pose proof (TWL.u_at_range Bw 40 8) as R39.
cbn [Z.of_nat Z.mul Z.pow] in R33, R34, R35, R36, R37, R38, R39.
set (E := mwb_E regs Bw).
assert (EOB : forall j, (j < 97)%nat -> ew E (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
  by (intros j Hj; unfold E, mwb_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EH97 : ew E (A_HI 97) = Z_to_bv 64 (VAL (A_HI 97)))
  by (unfold E, mwb_E; apply Eimg_img; unfold A_HI, A_TEXT, A_LIM; lia).
assert (EXT : forall i, (i < 8)%nat -> ew E (32 + i) = nth i (mwb_ex Bw) (Z_to_bv 64 0))
  by (intros i Hi; unfold E, mwb_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by exact (EXT 0%nat ltac:(lia)).
assert (A33 : ew E 33 = w64 (TW.u_at Bw (TW.OFF_M + (0 + 0)) (N.to_nat 4))) by exact (EXT 1%nat ltac:(lia)).
assert (A34 : ew E 34 = w64 (TW.u_at Bw (TW.OFF_M + (0 + 24)) (N.to_nat 4))) by exact (EXT 2%nat ltac:(lia)).
assert (A35 : ew E 35 = w64 (TW.u_at Bw (TW.OFF_OW + (196 + 0)) (N.to_nat 4))) by exact (EXT 3%nat ltac:(lia)).
assert (A36 : ew E 36 = w64 (TW.u_at Bw (TW.OFF_g_now + (0 + 0)) (N.to_nat 8))) by exact (EXT 4%nat ltac:(lia)).
assert (A37 : ew E 37 = w64 (TW.u_at Bw (TW.OFF_M + (0 + 88)) (N.to_nat 4))) by exact (EXT 5%nat ltac:(lia)).
assert (A38 : ew E 38 = w64 (TW.u_at Bw (TW.OFF_M + (0 + 16)) (N.to_nat 8))) by exact (EXT 6%nat ltac:(lia)).
assert (A39 : ew E 39 = w64 (TW.u_at Bw (TW.OFF_M + (0 + 40)) (N.to_nat 8))) by exact (EXT 7%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (unfold E, mwb_E; rewrite (ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (U8 : bv_unsigned (ew E (A_OBJ 8)) = TB_M)
  by (rewrite (EOB 8%nat ltac:(lia)), V8; apply unsigned_lit_small; unfold TB_M; lia).
assert (U43 : bv_unsigned (ew E (A_OBJ 43)) = TB_OW + 196)
  by (rewrite (EOB 43%nat ltac:(lia)), V43; apply unsigned_lit_small; unfold TB_OW; lia).
assert (U28 : bv_unsigned (ew E (A_OBJ 28)) = TB_g_now)
  by (rewrite (EOB 28%nat ltac:(lia)), V28; apply unsigned_lit_small; unfold TB_g_now; lia).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF)
  by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E 33%nat) = TW.u_at Bw 0 4)
  by (rewrite A33; unfold w64, TW.OFF_M; apply unsigned_lit_small; cbn [Z.add N.to_nat Pos.to_nat]; lia).
assert (U34 : bv_unsigned (ew E 34%nat) = TW.u_at Bw 24 4)
  by (rewrite A34; unfold w64, TW.OFF_M; apply unsigned_lit_small; cbn [Z.add N.to_nat Pos.to_nat]; lia).
assert (U35 : bv_unsigned (ew E 35%nat) = TW.u_at Bw 65508 4)
  by (rewrite A35; unfold w64, TW.OFF_OW; apply unsigned_lit_small; cbn [Z.add N.to_nat Pos.to_nat]; lia).
assert (U36 : bv_unsigned (ew E 36%nat) = TW.u_at Bw 65000 8)
  by (rewrite A36; unfold w64, TW.OFF_g_now; apply unsigned_lit_small; cbn [Z.add N.to_nat Pos.to_nat]; lia).
assert (U37 : bv_unsigned (ew E 37%nat) = TW.u_at Bw 88 4)
  by (rewrite A37; unfold w64, TW.OFF_M; apply unsigned_lit_small; cbn [Z.add N.to_nat Pos.to_nat]; lia).
assert (U38 : bv_unsigned (ew E 38%nat) = TW.u_at Bw 16 8)
  by (rewrite A38; unfold w64, TW.OFF_M; apply unsigned_lit_small; cbn [Z.add N.to_nat Pos.to_nat]; lia).
assert (U39 : bv_unsigned (ew E 39%nat) = TW.u_at Bw 40 8)
  by (rewrite A39; unfold w64, TW.OFF_M; apply unsigned_lit_small; cbn [Z.add N.to_nat Pos.to_nat]; lia).
rewrite restrict_mkst_fx. unfold ss_mwb, mwb_regions.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons;
  [ unfold stack_region, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite Usp;
    split; [lia|]; split; [lia|]; split; [|constructor];
    intros o Ho; apply (apresent_writable segs); apply Hpres; lia |].
  apply Forall_cons;
  [ exact (mwb_reg W memc Bw _ (A_OBJ 8) TB_M TW.OFF_M TB_M TW.SZ_M 0 0 4 0 0 0 4 33 Htw TMAP_B_M ltac:(lia) U8
            ltac:(unfold TB_M; lia) ltac:(unfold TB_M; lia) ltac:(intros a Ha; lia)
            ltac:(lia) ltac:(unfold TW.SZ_M; lia) ltac:(lia) A33) |].
  apply Forall_cons;
  [ exact (mwb_reg W memc Bw _ (A_OBJ 8) TB_M TW.OFF_M TB_M TW.SZ_M 0 16 24 16 24 16 8 38 Htw TMAP_B_M ltac:(lia) U8
            ltac:(unfold TB_M; lia) ltac:(unfold TB_M; lia)
            ltac:(intros a Ha; apply mwb_inG_M; unfold TB_M, TW.SZ_M in *; lia)
            ltac:(lia) ltac:(unfold TW.SZ_M; lia) ltac:(lia) A38) |].
  apply Forall_cons;
  [ exact (mwb_reg W memc Bw _ (A_OBJ 8) TB_M TW.OFF_M TB_M TW.SZ_M 0 24 28 24 24 24 4 34 Htw TMAP_B_M ltac:(lia) U8
            ltac:(unfold TB_M; lia) ltac:(unfold TB_M; lia) ltac:(intros a Ha; lia)
            ltac:(lia) ltac:(unfold TW.SZ_M; lia) ltac:(lia) A34) |].
  apply Forall_cons;
  [ exact (mwb_reg W memc Bw _ (A_OBJ 8) TB_M TW.OFF_M TB_M TW.SZ_M 0 40 48 40 48 40 8 39 Htw TMAP_B_M ltac:(lia) U8
            ltac:(unfold TB_M; lia) ltac:(unfold TB_M; lia)
            ltac:(intros a Ha; apply mwb_inG_M; unfold TB_M, TW.SZ_M in *; lia)
            ltac:(lia) ltac:(unfold TW.SZ_M; lia) ltac:(lia) A39) |].
  apply Forall_cons;
  [ exact (mwb_reg W memc Bw _ (A_OBJ 8) TB_M TW.OFF_M TB_M TW.SZ_M 0 88 92 88 92 88 4 37 Htw TMAP_B_M ltac:(lia) U8
            ltac:(unfold TB_M; lia) ltac:(unfold TB_M; lia)
            ltac:(intros a Ha; apply mwb_inG_M; unfold TB_M, TW.SZ_M in *; lia)
            ltac:(lia) ltac:(unfold TW.SZ_M; lia) ltac:(lia) A37) |].
  apply Forall_cons;
  [ exact (mwb_reg W memc Bw _ (A_OBJ 43) (TB_OW + 196) TW.OFF_OW TB_OW TW.SZ_OW 196 0 4 0 4 0 4 35 Htw TMAP_B_OW
            ltac:(lia) U43 ltac:(unfold TB_OW; lia) ltac:(unfold TB_OW; lia)
            ltac:(intros a Ha; apply mwb_inG_OW; unfold TB_OW, TW.SZ_OW in *; lia)
            ltac:(lia) ltac:(unfold TW.SZ_OW; lia) ltac:(lia) A35) |].
  apply Forall_cons; [|apply Forall_nil].
  exact (mwb_reg W memc Bw _ (A_OBJ 28) TB_g_now TW.OFF_g_now TB_g_now TW.SZ_g_now 0 0 8 0 0 0 8 36 Htw TMAP_B_g_now
          ltac:(lia) U28 ltac:(unfold TB_g_now; lia) ltac:(unfold TB_g_now; lia) ltac:(intros a Ha; lia)
          ltac:(lia) ltac:(unfold TW.SZ_g_now; lia) ltac:(lia) A36).
- apply pairwise_disjoint_of_extents.
  unfold stack_region, mwbR_dk, mwbR_ea, mwbR_fo, mwbR_ws, mwbR_fa, mwbR_e2, mwbR_now, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  cbn [base_val]. rewrite Usp, U8, U43, U28.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold TB_M, TB_OW, TB_g_now in *.
  repeat split; first [exact I | lia].
- unfold mwb_facts, facts_ok. cbn [f_atoms f_conds f_alias].
  split; [|split; [first [exact I | cbn; exact I] |]].
  + cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, U32, U8, U43, U33, U34, U35, U36, U37, U38, U39.
    change (2 ^ 4) with 16. change (2 ^ 5) with 32. change (2 ^ 2) with 4.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold TB_M, TB_OW, SHADOW_OFF in *.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | reflexivity].
  + cbn [alias_ok]. split; [|exact I]. cbn [sv_denot].
    rewrite EH97, (EOB 43%nat ltac:(lia)). vm_compute. reflexivity.
Qed.


Ltac mwb_inc := cbv [mwbR_ea mwbR_ws mwbR_fa mwbR_e2 mwbR_ea4 mwbR_ws4 mwbR_fa4 mwbR_e24 YP09.r_chunks];
  cbn [In]; auto.

(* ---- the bytes of a written span, read off a region's chunk ---- *)

Lemma mwb_cval : forall (E : env) (W : world segs) (m : word -> option byte) (r : YP09.region) (nb : nat)
    (bb co : Z) (w : N) (v : sv) (X : Z),
  region_ok segs E (mrestrict (w_H W) m) r -> YP09.r_base r = Some nb -> bv_unsigned (ew E nb) = bb ->
  In (YP09.mkChunk co (CVal w v)) (YP09.r_chunks r) ->
  sv_denot E v = Z_to_bv 64 X -> 0 <= X -> Z.of_N w <= 8 ->
  forall j, (j < N.to_nat w)%nat ->
    aview segs (w_H W) m (bb + co + Z.of_nat j) = Some (YO0f.le_byte X (N.to_nat w) j).
Proof.
intros E W m r nb bb co w v X Hr Hb Hbb Hin Hden HX Hw j Hj.
assert (Hj' : Z.of_nat j < Z.of_N w) by (rewrite <- N_nat_Z; lia).
destruct Hr as (_ & _ & _ & HF). rewrite Forall_forall in HF. specialize (HF _ Hin).
unfold YP09.chunk_ok in HF.
destruct (HF (Z.of_nat j) ltac:(cbn [YP09.c_len YP09.c_off YP09.c_val YP09.cv_len]; lia)) as (bt & Hbt & Hm).
cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hbt, Hm. injection Hbt as <-.
rewrite Hb in Hm. cbn [base_val] in Hm. rewrite Hbb in Hm.
unfold aview. rewrite Hm. cbn [option_map]. f_equal.
rewrite Hden. rewrite (mwb_bow X w (Z.of_nat j)) by lia. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma mwb_win_val : forall (E : env) (W : world segs) (m : word -> option byte) r (nb : nat) (bb co : Z)
    (w : N) (v : sv),
  region_ok segs E (mrestrict (w_H W) m) r -> YP09.r_base r = Some nb -> bv_unsigned (ew E nb) = bb ->
  In (YP09.mkChunk co (CVal w v)) (YP09.r_chunks r) -> Z.of_N w <= 8 ->
  forall j, (j < N.to_nat w)%nat ->
    aview segs (w_H W) m (bb + co + Z.of_nat j) = Some (YO0f.le_byte (U E v) (N.to_nat w) j).
Proof.
intros E W m r nb bb co w v Hr Hb Hbb Hin Hw j Hj.
exact (mwb_cval E W m r nb bb co w v (U E v) Hr Hb Hbb Hin (denot_lit_U E v) (proj1 (U_range E v)) Hw j Hj).
Qed.

(* ---- the world, one span at a time ---- *)

Definition mwb_inrs (l : list (Z * Z)) (x : Z) : bool :=
  existsb (fun p => ((fst p <=? x) && (x <? snd p))%bool) l.
Definition mwb_rd (l : list (Z * Z)) (rd rd' : Z -> option Z) : Z -> option Z :=
  fun x => if mwb_inrs l x then rd' x else rd x.

Lemma mwb_step : forall l (rd rd' : Z -> option Z) Bw o b n k (m : nat) v,
  tw_at TMAP_B (mwb_rd l rd rd') Bw -> In (o, b, n) TMAP_B -> 0 <= k -> k + Z.of_nat m <= n ->
  (forall j, (j < m)%nat -> rd' (b + k + Z.of_nat j) = Some (YO0f.le_byte v m j)) ->
  tw_at TMAP_B (mwb_rd ((b + k, b + k + Z.of_nat m) :: l) rd rd') (TW.upd Bw (o + k) (TW.put m v)).
Proof.
intros l rd rd' Bw o b n k m v Hat Hin Hk Hkm Hnew.
apply (tw_write TMAP_B (mwb_rd l rd rd') (mwb_rd ((b + k, b + k + Z.of_nat m) :: l) rd rd') Bw o b n k m v
  TMAP_B_ok Hat Hin Hk Hkm).
- intros j Hj. unfold mwb_rd, mwb_inrs. cbn [existsb fst snd].
  replace ((b + k <=? b + k + Z.of_nat j) && (b + k + Z.of_nat j <? b + k + Z.of_nat m))%bool with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  cbn [orb]. exact (Hnew j Hj).
- intros x Hx Hn. unfold mwb_rd, mwb_inrs. cbn [existsb fst snd].
  replace ((b + k <=? x) && (x <? b + k + Z.of_nat m))%bool with false.
  + cbn [orb]. reflexivity.
  + symmetry. apply andb_false_iff.
    destruct (Z_lt_le_dec x (b + k)) as [H1 | H1]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
Qed.

Lemma mwb_fin_rd : forall l (rd rd' : Z -> option Z) Bw,
  tw_at TMAP_B (mwb_rd l rd rd') Bw ->
  (forall x, tw_in TMAP_B x -> mwb_inrs l x = false -> rd' x = rd x) ->
  tw_at TMAP_B rd' Bw.
Proof.
intros l rd rd' Bw Hat Hk. apply (tw_kept TMAP_B (mwb_rd l rd rd') rd' Bw Hat).
intros x Hx. unfold mwb_rd. destruct (mwb_inrs l x) eqn:Hi; [reflexivity | exact (Hk x Hx Hi)].
Qed.

(* A span whose chunk is still the entry atom: its bytes are the entry's. *)
Lemma mwb_keep_win : forall (E : env) (W : world segs) (m : word -> option byte) (rd : Z -> option Z)
    r (nb : nat) (rb co : Z) (w : N) (atom : nat) Bw o bb n d,
  region_ok segs E (mrestrict (w_H W) m) r -> YP09.r_base r = Some nb -> bv_unsigned (ew E nb) = rb ->
  In (YP09.mkChunk co (CVal w (SOff atom 0))) (YP09.r_chunks r) -> Z.of_N w <= 8 ->
  ew E atom = w64 (TW.u_at Bw (o + (d + co)) (N.to_nat w)) ->
  tw_at TMAP_B rd Bw -> In (o, bb, n) TMAP_B -> rb = bb + d -> 0 <= d + co -> d + co + Z.of_N w <= n ->
  forall x, rb + co <= x < rb + co + Z.of_N w -> aview segs (w_H W) m x = rd x.
Proof.
intros E W m rd r nb rb co w atom Bw o bb n d Hr Hb Hbb Hin Hw Hew Htw Hrow Hrb Hco Hcow x Hx.
pose proof (TWL.u_at_range Bw (o + (d + co)) (N.to_nat w)) as HR. rewrite N_nat_Z in HR.
assert (HP : 2 ^ (8 * Z.of_N w) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
assert (HU : U E (SOff atom 0) = TW.u_at Bw (o + (d + co)) (N.to_nat w))
  by (apply (U_atom E atom); [exact Hew | lia]).
replace x with (rb + co + Z.of_nat (Z.to_nat (x - (rb + co)))) by lia.
rewrite (mwb_win_val E W m r nb rb co w (SOff atom 0) Hr Hb Hbb Hin Hw (Z.to_nat (x - (rb + co)))
  ltac:(rewrite <- N_nat_Z in Hx; lia)).
replace (rb + co) with (bb + (d + co)) by lia.
rewrite (tw_read TMAP_B rd Bw o bb n (d + co) (N.to_nat w) (Z.to_nat (x - (bb + (d + co)))) TMAP_B_ok Htw Hrow Hco
  ltac:(rewrite N_nat_Z; exact Hcow) ltac:(rewrite <- N_nat_Z in Hx; lia)).
rewrite HU. reflexivity.
Qed.

(* The world after a path that wrote no byte of G: the four written spans still hold their entry atoms, every
   other byte of G is kept. *)
Lemma mwb_world_same : forall (E : env) (W : world segs) memc m Bw sp,
  tw_at TMAP_B (aview segs (w_H W) memc) Bw ->
  bv_unsigned (ew E 249%nat) = TB_M -> bv_unsigned (ew E 284%nat) = TB_OW + 196 ->
  ew E 35%nat = w64 (TW.u_at Bw 65508 4) -> ew E 37%nat = w64 (TW.u_at Bw 88 4) ->
  ew E 38%nat = w64 (TW.u_at Bw 16 8) -> ew E 39%nat = w64 (TW.u_at Bw 40 8) ->
  region_ok segs E (mrestrict (w_H W) m) mwbR_ea -> region_ok segs E (mrestrict (w_H W) m) mwbR_ws ->
  region_ok segs E (mrestrict (w_H W) m) mwbR_fa -> region_ok segs E (mrestrict (w_H W) m) mwbR_e2 ->
  G_HARNESS_B_HI <= sp - 16 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ mwb_wins sp a -> aview segs (w_H W) m a = aview segs (w_H W) memc a) ->
  tw_at TMAP_B (aview segs (w_H W) m) Bw.
Proof.
intros E W memc m Bw sp Htw U8 U43 A35 A37 A38 A39 Rea Rws Rfa Re2 Hsp KW.
apply (tw_kept TMAP_B (aview segs (w_H W) memc)); [exact Htw|].
intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold G_HARNESS_B_LO, G_HARNESS_B_HI in Hh, Hsp.
destruct (Classical_Prop.classic (mwb_wins sp x)) as [Hw | Hw].
- destruct Hw as [Hw | [Hw | [Hw | [Hw | Hw]]]].
  + exfalso. lia.
  + exact (mwb_keep_win E W m _ mwbR_ea (A_OBJ 8) TB_M 16 8%N 38 Bw TW.OFF_M TB_M TW.SZ_M 0 Rea eq_refl U8
      ltac:(mwb_inc) ltac:(cbn [Z.of_N]; lia) A38 Htw TMAP_B_M ltac:(lia) ltac:(lia)
      ltac:(unfold TW.SZ_M; cbn [Z.of_N]; lia) x ltac:(cbn [Z.of_N]; lia)).
  + exact (mwb_keep_win E W m _ mwbR_ws (A_OBJ 8) TB_M 40 8%N 39 Bw TW.OFF_M TB_M TW.SZ_M 0 Rws eq_refl U8
      ltac:(mwb_inc) ltac:(cbn [Z.of_N]; lia) A39 Htw TMAP_B_M ltac:(lia) ltac:(lia)
      ltac:(unfold TW.SZ_M; cbn [Z.of_N]; lia) x ltac:(cbn [Z.of_N]; lia)).
  + exact (mwb_keep_win E W m _ mwbR_fa (A_OBJ 8) TB_M 88 4%N 37 Bw TW.OFF_M TB_M TW.SZ_M 0 Rfa eq_refl U8
      ltac:(mwb_inc) ltac:(cbn [Z.of_N]; lia) A37 Htw TMAP_B_M ltac:(lia) ltac:(lia)
      ltac:(unfold TW.SZ_M; cbn [Z.of_N]; lia) x ltac:(cbn [Z.of_N]; lia)).
  + exact (mwb_keep_win E W m _ mwbR_e2 (A_OBJ 43) (TB_OW + 196) 0 4%N 35 Bw TW.OFF_OW TB_OW TW.SZ_OW 196 Re2 eq_refl
      U43 ltac:(mwb_inc) ltac:(cbn [Z.of_N]; lia) A35 Htw TMAP_B_OW ltac:(lia) ltac:(lia)
      ltac:(unfold TW.SZ_OW; cbn [Z.of_N]; lia) x ltac:(cbn [Z.of_N]; lia)).
- apply KW; [lia | exact Hw].
Qed.

(* The world after the four stores (+0x44 .. +0x58): B4 in the binary's order. *)
Lemma mwb_world_4 : forall (E : env) (W : world segs) memc m Bw sp,
  tw_at TMAP_B (aview segs (w_H W) memc) Bw ->
  bv_unsigned (ew E 249%nat) = TB_M -> bv_unsigned (ew E 284%nat) = TB_OW + 196 ->
  ew E 35%nat = w64 (TW.u_at Bw 65508 4) -> ew E 36%nat = w64 (TW.u_at Bw 65000 8) ->
  region_ok segs E (mrestrict (w_H W) m) mwbR_ea4 -> region_ok segs E (mrestrict (w_H W) m) mwbR_ws4 ->
  region_ok segs E (mrestrict (w_H W) m) mwbR_fa4 -> region_ok segs E (mrestrict (w_H W) m) mwbR_e24 ->
  G_HARNESS_B_HI <= sp - 16 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ mwb_wins sp a -> aview segs (w_H W) m a = aview segs (w_H W) memc a) ->
  tw_at TMAP_B (aview segs (w_H W) m) (mwbm_W Bw).
Proof.
intros E W memc m Bw sp Htw U8 U43 A35 A36 Rea Rws Rfa Re2 Hsp KW.
assert (V196 : forall j, (j < 4)%nat ->
  aview segs (w_H W) m (TB_OW + 196 + Z.of_nat j) = Some (YO0f.le_byte (TW.s32_at Bw 65508 + 1) 4 j)).
{ intros j Hj.
  replace (TB_OW + 196 + Z.of_nat j) with (TB_OW + 196 + 0 + Z.of_nat j) by lia.
  rewrite (mwb_win_val E W m mwbR_e24 (A_OBJ 43) (TB_OW + 196) 0 4%N
    (SAluw ALU_ADD (SExt true 32 (SOff 35 0)) (SLit 1)) Re2 eq_refl U43
    ltac:(mwb_inc) ltac:(cbn [Z.of_N]; lia) j ltac:(cbn; lia)).
  f_equal. apply mwb_le_byte_mod. change (8 * Z.of_nat (N.to_nat 4%N)) with 32.
  exact (mwb_u_addw1 E (SExt true 32 (SOff 35 0)) (TW.s32_at Bw 65508) (mwb_sext_atom E 35 Bw 65508 A35)). }
assert (V16 : forall j, (j < 8)%nat -> aview segs (w_H W) m (TB_M + 16 + Z.of_nat j) = Some (YO0f.le_byte 0 8 j)).
{ intros j Hj.
  exact (mwb_win_val E W m mwbR_ea4 (A_OBJ 8) TB_M 16 8%N (SLit 0) Rea eq_refl U8
    ltac:(mwb_inc) ltac:(cbn [Z.of_N]; lia) j ltac:(cbn; lia)). }
assert (V40 : forall j, (j < 8)%nat ->
  aview segs (w_H W) m (TB_M + 40 + Z.of_nat j) = Some (YO0f.le_byte (TW.u_at Bw 65000 8) 8 j)).
{ intros j Hj.
  rewrite (mwb_win_val E W m mwbR_ws4 (A_OBJ 8) TB_M 40 8%N (SOff 36 0) Rws eq_refl U8
    ltac:(mwb_inc) ltac:(cbn [Z.of_N]; lia) j ltac:(cbn; lia)).
  f_equal. apply mwb_le_byte_mod.
  rewrite (U_atom E 36 (TW.u_at Bw 65000 8) A36
    ltac:(pose proof (TWL.u_at_range Bw 65000 8) as HR; cbn [Z.of_nat] in HR; lia)). reflexivity. }
assert (V88 : forall j, (j < 4)%nat -> aview segs (w_H W) m (TB_M + 88 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)).
{ intros j Hj.
  exact (mwb_win_val E W m mwbR_fa4 (A_OBJ 8) TB_M 88 4%N (SLit 0) Rfa eq_refl U8
    ltac:(mwb_inc) ltac:(cbn [Z.of_N]; lia) j ltac:(cbn; lia)). }
pose proof (mwb_step [] (aview segs (w_H W) memc) (aview segs (w_H W) m) Bw
  TW.OFF_OW TB_OW TW.SZ_OW 196 4 (TW.s32_at Bw 65508 + 1) Htw TMAP_B_OW
  ltac:(lia) ltac:(unfold TW.SZ_OW; lia) V196) as T1.
pose proof (mwb_step _ (aview segs (w_H W) memc) (aview segs (w_H W) m) _
  TW.OFF_M TB_M TW.SZ_M 16 8 0 T1 TMAP_B_M ltac:(lia) ltac:(unfold TW.SZ_M; lia) V16) as T2.
pose proof (mwb_step _ (aview segs (w_H W) memc) (aview segs (w_H W) m) _
  TW.OFF_M TB_M TW.SZ_M 40 8 (TW.u_at Bw 65000 8) T2 TMAP_B_M ltac:(lia) ltac:(unfold TW.SZ_M; lia) V40) as T3.
pose proof (mwb_step _ (aview segs (w_H W) memc) (aview segs (w_H W) m) _
  TW.OFF_M TB_M TW.SZ_M 88 4 0 T3 TMAP_B_M ltac:(lia) ltac:(unfold TW.SZ_M; lia) V88) as T4.
unfold mwbm_W.
apply (mwb_fin_rd _ (aview segs (w_H W) memc) (aview segs (w_H W) m) _ T4).
intros x Hx Hni. pose proof (TMAP_B_hull x Hx) as Hh. unfold G_HARNESS_B_LO, G_HARNESS_B_HI in Hh, Hsp.
unfold mwb_inrs in Hni; cbn [existsb fst snd] in Hni;
repeat match goal with H : (_ || _)%bool = false |- _ => apply orb_false_iff in H; destruct H end;
repeat match goal with H : (_ && _)%bool = false |- _ => apply andb_false_iff in H end.
apply KW; [lia|].
unfold mwb_wins.
repeat match goal with H : (_ <=? _) = false \/ (_ <? _) = false |- _ =>
  destruct H as [H | H]; [apply Z.leb_gt in H | apply Z.ltb_ge in H] end.
all: unfold TB_M, TB_OW in *; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *; lia.
Qed.

(* ---- what the walk keeps ---- *)

(* m_wake's later memory (after m_set's return) differs from mem2 only in the call's stack window: acall_kept_g
   carries over (the blocks, image bytes and frames lie below alloc_ceiling, so outside the window). *)
Lemma mwb_kept_tail : forall lyc Sc (W : world segs) memc mdc (W2 : world segs) mem2 memF slo shi (Eo : Z -> Prop),
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc -> alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
  acall_kept_g segs B G_HARNESS_B lyc Sc W memc W2 mem2 slo shi Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> aview segs (w_H W2) memF a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) memF a) ->
  acall_kept_g segs B G_HARNESS_B lyc Sc W memc W2 memF slo shi Eo.
Proof.
intros lyc Sc W memc mdc W2 mem2 memF slo shi Eo LAWS HAR Hce Hshi (K1 & K2 & K3 & K4 & K5 & K6) Hk Hg.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw. rewrite Hk by lia. exact (K1 a Ha Hw).
- intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
  rewrite Hk by lia. exact (K2 b m i Hb Hi Hn).
- intros a Hi HnG Hno He. pose proof (transportb_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  rewrite Hk by lia. exact (K3 a Hi HnG Hno He).
- intros cid pos a Hin Hr Hn.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  assert (Ha : 0 <= a < alloc_ceiling).
  { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  rewrite Hk by lia. exact (K4 cid pos a Hin Hr Hn).
- intros a Ha Hw Hp. apply Hg. exact (K5 a Ha Hw Hp).
- intros a Ha. apply Hg. exact (K6 a Ha).
Qed.

(* The stack region of the call's return state: its bytes are above m_set's window, so m_set keeps them. *)
Lemma mwb_region_kept_stack : forall E lyc Sc (W : world segs) memc (W2 : world segs) mem2 slo shi (Er : Z -> Prop)
    n lo hi wlo whi cs sp0 sp STK FP ly S W0 mem md own ly2 S2 md2 k,
  acall_kept_g segs B G_HARNESS_B lyc Sc W memc W2 mem2 slo shi Er ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 k ->
  bv_unsigned (ew E n) = sp -> shi <= sp + lo -> sp0 - STK <= sp + lo -> sp + hi <= sp0 -> lo <= wlo -> whi <= hi ->
  region_kept segs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs sp0 sp STK FP ly S W0 mem md own ly2 S2 md2 k
  (K1 & _) HJ Hn Hshi Hlo Hhi Hw1 Hw2.
pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal & Hstk0 & Hceil & Hslo & Hsh & H47 & _) & _).
pose proof asan_consts as (C1 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). apply K1; lia.
- intros _. apply (apresent_writable segs). apply Hpres. lia.
Qed.

(* ---- the posts ---- *)

(* A return from the early paths (no call): every byte outside the stack window and G is kept. *)
Lemma mwb_close : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs Bw Bw' r
    regsF mF mdF,
  AR_laws segs B -> ameter_laws MT -> gx_ok segs B G_HARNESS_B ->
  @AR rc segs B lyc Sc W memc mdc ->
  (forall a, spZ regs - MWAKE_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  alloc_ceiling <= spZ regs - MWAKE_STK -> spZ regs <= 2 ^ 47 ->
  YK0s.ret_ok (YK11.getr regs 1) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own
    lyc Sc W mF mdF k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ mwb_Zs (spZ regs) a -> aview segs (w_H W) mF a = aview segs (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mF a) ->
  tw_at TMAP_B (aview segs (w_H W) mF) Bw' ->
  aregs_preserved regs regsF -> YK11.getr regsF 1 = YK11.getr regs 1 -> YK11.getr regsF 10 = w64 r ->
  forall mat, @transport_mwake_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r W
    (mkCfg (@YK11.mkst fx regsF (v_jalr (YK11.getr regsF 1) 0) mF (YK11.seg_rom segs))
      (with_vm_backing (m_vm_lazy mdF) mat mdF)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw' r regsF mF mdF
  LAWS MTL HGX HAR Hwin Hce Hsp47 Hra HJF KA GA HTW HPR RF1 RF10 mat.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (GLOW : forall a, inG G_HARNESS_B a -> 0 <= a < kLowMemEnd)
  by (intros a Ha; exact (transportb_segs_low a (proj1 (HGX a Ha)))).
unfold transport_mwake_post, transport_cg_post.
exists lyc, Sc, regsF, mF, (with_vm_backing (m_vm_lazy mdF) mat mdF), 0.
split. { rewrite RF1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split; [unfold MWAKE_EV, MSET_EV; lia|].
split; [rewrite Z.add_0_r; apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJF|].
split; [exact HPR|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split.
{ apply (dk_kept_step_g segs B LAWS transportb_segs_low G_HARNESS_B lyc Sc W memc mdc memc mF
    (spZ regs - MWAKE_STK) (spZ regs) (mwake_wr Bw) (mwb_Zs (spZ regs)) HAR).
  - apply dk_kept_refl_g. exact Hwin.
  - exact KA.
  - exact GA.
  - intros a [Hw | Hw] Hc; [exact Hw|]. exfalso. pose proof (GLOW a Hw) as Hl.
    unfold kLowMemEnd in Hl. lia.
  - intros b0 m0 i Hb Hi Hz. exfalso.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b0 m0 HAR Hb) as (_ & H4096 & Hbc & _).
    destruct Hz as [Hw | Hw]; [lia|].
    exact (blk_img segs B LAWS lyc Sc W memc mdc b0 m0 (b0 + i) HAR Hb
             ltac:(lia) (proj1 (HGX (b0 + i) Hw))).
  - intros a [Hw | Hw] Hi HnG _ _.
    + pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl. lia.
    + exact (HnG Hw).
  - intros cid pos a Hin Hr Hz. exfalso.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin)
      as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hz as [Hw | Hw].
    + destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8)
        by (apply Z.div_le_mono; lia).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
    + pose proof (GLOW a Hw) as Hl. unfold kLowMemEnd in Hl.
      destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
      * exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos a HAR Hin
                 ltac:(lia) (proj1 (HGX a Hw))).
      * assert (Hd0 : 0 <= frame_addr lyc cid pos / 8) by (apply Z.div_pos; lia).
        unfold shadow_addr, SHADOW_OFF in *. lia. }
split; [exact (mo_le_refl MT MTL Sc)|].
split; [exact RF10 | exact HTW].
Qed.

(* The return after m_set: m_set's post (on the same journal, from the call state memX) composed with what the walk
   kept up to the call and with the epilogue, which writes no byte of G. *)
Lemma mwb_close_call : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs Bw Bw'
    memX regsX (W2 : world segs) ly2 S2 mem2 e regsF mF mdF,
  AR_laws segs B -> ameter_laws MT -> gx_ok segs B G_HARNESS_B ->
  @AR rc segs B lyc Sc W memc mdc ->
  (forall a, spZ regs - MWAKE_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  alloc_ceiling <= spZ regs - MWAKE_STK -> spZ regs <= 2 ^ 47 ->
  YK0s.ret_ok (YK11.getr regs 1) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ mwb_Zs (spZ regs) a -> aview segs (w_H W) memX a = aview segs (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) memX a) ->
  spZ regsX = spZ regs - 16 ->
  0 <= e <= MSET_EV ->
  frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  acall_kept_g segs B G_HARNESS_B lyc Sc W memX W2 mem2 (spZ regsX - MSET_STK) (spZ regsX) (mset_st_wr (mwb_W Bw) 1) ->
  mo_le MT Sc S2 0 ->
  tw_at TMAP_B (aview segs (w_H W2) mem2) Bw' ->
  (forall a, mset_st_wr (mwb_W Bw) 1 a -> mwake_wr Bw a) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own
    ly2 S2 W2 mF mdF (k + e) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - MWAKE_STK <= a < spZ regs) ->
     aview segs (w_H W2) mF a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mF a) ->
  aregs_preserved regs regsF -> YK11.getr regsF 1 = YK11.getr regs 1 -> YK11.getr regsF 10 = w64 0 ->
  forall mat, @transport_mwake_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' 0 W2
    (mkCfg (@YK11.mkst fx regsF (v_jalr (YK11.getr regsF 1) 0) mF (YK11.seg_rom segs))
      (with_vm_backing (m_vm_lazy mdF) mat mdF)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw' memX regsX W2 ly2 S2 mem2 e regsF mF mdF
  LAWS MTL HGX HAR Hwin Hce Hsp47 Hra KA GA HspX He Hfr2 Hperm2 HK2 HMO2 HX2 Hsub HJF KF GF HPR RF1 RF10 mat.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : MWAKE_STK = 32) by reflexivity. assert (FM : MSET_STK = 16) by reflexivity.
assert (GLOW : forall a, inG G_HARNESS_B a -> 0 <= a < kLowMemEnd)
  by (intros a Ha; exact (transportb_segs_low a (proj1 (HGX a Ha)))).
unfold transport_mwake_post, transport_cg_post.
exists ly2, S2, regsF, mF, (with_vm_backing (m_vm_lazy mdF) mat mdF), e.
split. { rewrite RF1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split; [unfold MWAKE_EV; exact He|].
split; [apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJF|].
split; [exact HPR|].
split; [exact Hfr2|].
split; [exact Hperm2|].
split.
{ apply (mwb_kept_tail lyc Sc W memc mdc W2 mem2 mF (spZ regs - MWAKE_STK) (spZ regs) (mwake_wr Bw) LAWS HAR Hce
    ltac:(lia)); [| exact KF | exact GF].
  eapply dk_kept_trans_g with (W1 := W) (memX := memX) (slo' := spZ regsX - MSET_STK) (shi' := spZ regsX)
    (Eo' := mset_st_wr (mwb_W Bw) 1).
  - exact Hce.
  - lia.
  - apply (dk_kept_step_g segs B LAWS transportb_segs_low G_HARNESS_B lyc Sc W memc mdc memc memX
      (spZ regs - MWAKE_STK) (spZ regs) (mwake_wr Bw) (mwb_Zs (spZ regs)) HAR).
    + apply dk_kept_refl_g. exact Hwin.
    + exact KA.
    + exact GA.
    + intros a [Hw | Hw] Hc; [exact Hw|]. exfalso. pose proof (GLOW a Hw) as Hl.
      unfold kLowMemEnd in Hl. lia.
    + intros b0 m0 i Hb Hi Hz. exfalso.
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b0 m0 HAR Hb) as (_ & H4096 & Hbc & _).
      destruct Hz as [Hw | Hw]; [lia|].
      exact (blk_img segs B LAWS lyc Sc W memc mdc b0 m0 (b0 + i) HAR Hb
               ltac:(lia) (proj1 (HGX (b0 + i) Hw))).
    + intros a [Hw | Hw] Hi HnG _ _.
      * pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl. lia.
      * exact (HnG Hw).
    + intros cid pos a Hin Hr Hz. exfalso.
      destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin)
        as (F4096 & Fce & _).
      pose proof (fs_frame_bytes_nonneg cid) as Hfs.
      destruct Hz as [Hw | Hw].
      * destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
        pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
        assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8)
          by (apply Z.div_le_mono; lia).
        unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
      * pose proof (GLOW a Hw) as Hl. unfold kLowMemEnd in Hl.
        destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
        -- exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos a HAR Hin
                   ltac:(lia) (proj1 (HGX a Hw))).
        -- assert (Hd0 : 0 <= frame_addr lyc cid pos / 8) by (apply Z.div_pos; lia).
           unfold shadow_addr, SHADOW_OFF in *. lia.
  - exact HK2.
  - lia.
  - lia.
  - exact Hsub. }
split; [exact HMO2|].
split; [exact RF10|].
apply (tw_kept TMAP_B (aview segs (w_H W2) mem2)); [exact HX2|].
intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold G_HARNESS_B_LO, G_HARNESS_B_HI in Hh.
apply KF; lia.
Qed.


(* ---- the walk's tactics ---- *)

(* The write right of a run: the frame's bytes are the caller's stack window, the spans of M and OW are bytes of G. *)
Ltac mwb_awr Usp U8 U43 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      rewrite ?Usp, ?U8, ?U43 in Ha;
      first [ lia
            | left; split; [unfold awr_byte; left; lia | lia]
            | right; left; apply mwb_inG_M; unfold TB_M, TW.SZ_M in *; lia
            | right; left; apply mwb_inG_OW; unfold TB_OW, TW.SZ_OW in *; lia ]
    | ]);
  apply awr_ok_x_nil.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac mwb_regv HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "mwb_regv: no match for" T; fail
  end.

(* After a run before the call: the bytes outside the windows and the presence, carried to the run's memory. *)
Ltac mwb_kw KW GA Usp U8 U43 sp Wv mc :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rs (mrestrict ?H _) (mrestrict ?H ?mn), HG : mem_grows _ _ |- _ =>
    let KW' := fresh "KWn" in let GA' := fresh "GAn" in
    assert (KW' : forall a, 0 <= a < 2 ^ 64 -> ~ mwb_wins sp a ->
                    aview segs H mn a = aview segs (w_H Wv) mc a)
      by (intros a Ha Hn; etransitivity;
          [ exact (mwb_kept_of_frame Ex rs H _ mn (mwb_wins sp) HFr
              (fun b wlo whi x Hin Hx => mwb_wins_of Ex sp rs b wlo whi x
                 ltac:(vm_compute; reflexivity) Usp U8 U43 Hin Hx) a Ha Hn)
          | exact (KW a Ha Hn) ]);
    assert (GA' : forall a, apresent (w_H Wv) mc a -> apresent H mn a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA a Ha)));
    clear HFr HG KW GA; repeat match goal with HFx : frame_of _ _ _ _ |- _ => clear HFx end;
    rename KW' into KW; rename GA' into GA
  end.

(* ---- the walk ---- *)

Lemma mwb_holds : @transport_m_wake_cg_holds_stmt fx rc B MT.
Proof.
unfold transport_m_wake_cg_holds_stmt.
intros HCELLS LAWS MTL HGX HMSET.
unfold transport_m_wake_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw' r
  HJ Hra Hra4 Hgp Htp Hsp16 Hlo Hhi Htw Hm Hev.
pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : MWAKE_STK = 32) by reflexivity.
assert (FM : MSET_STK = 16) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hce : alloc_ceiling <= spZ regs - MWAKE_STK) by lia.
assert (Hwin : forall a, spZ regs - MWAKE_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (HGH : G_HARNESS_B_HI <= spZ regs - 32) by (unfold G_HARNESS_B_HI; lia).
assert (HLB : Z.of_nat (length Bw) = 65616)
  by (rewrite (tw_len TMAP_B (aview segs (w_H W) memc) Bw Htw); vm_compute; reflexivity).
pose proof (TWL.s32_range Bw 0) as S0. pose proof (TWL.s32_range Bw 24) as S24.
pose proof (TWL.s32_range Bw 88) as S88. pose proof (TWL.s32_range Bw 65508) as S65508.
(* the model as a flat cascade of tests on Bw *)
rewrite (mwb_m_eq Bw) in Hm.
change (TW.M_desk_known Bw) with (TW.s32_at Bw 0) in Hm.
change (TW.M_foreign Bw) with (TW.s32_at Bw 24) in Hm.
rewrite (mwb_e2 Bw HLB), (mwb_fa Bw HLB) in Hm.
(* the valuation of the walk and its atoms *)
destruct mwb_vals as (V8 & V43 & V28 & V97 & VSIG & VRET).
set (E0 := mwb_E regs Bw).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, mwb_E; apply Eimg_env).
assert (EOB : forall j, (j < 97)%nat -> ew E0 (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
  by (intros j Hj; unfold E0, mwb_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EXT : forall i, (i < 8)%nat -> ew E0 (32 + i) = nth i (mwb_ex Bw) (Z_to_bv 64 0))
  by (intros i Hi; unfold E0, mwb_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (Usp0 : bv_unsigned (ew E0 2) = spZ regs)
  by (unfold E0, mwb_E; rewrite (ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E0 n = YK11.getr regs rr)
  by (intros n rr Hn; unfold E0, mwb_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U8L : bv_unsigned (ew E0 249%nat) = TB_M).
{ change 249%nat with (A_OBJ 8). rewrite (EOB 8%nat ltac:(lia)), V8. apply unsigned_lit_small. unfold TB_M. lia. }
assert (U43L : bv_unsigned (ew E0 284%nat) = TB_OW + 196).
{ change 284%nat with (A_OBJ 43). rewrite (EOB 43%nat ltac:(lia)), V43. apply unsigned_lit_small. unfold TB_OW. lia. }
assert (A33 : ew E0 33 = w64 (TW.u_at Bw 0 4)) by exact (EXT 1%nat ltac:(lia)).
assert (A34 : ew E0 34 = w64 (TW.u_at Bw 24 4)) by exact (EXT 2%nat ltac:(lia)).
assert (A35 : ew E0 35 = w64 (TW.u_at Bw 65508 4)) by exact (EXT 3%nat ltac:(lia)).
assert (A36 : ew E0 36 = w64 (TW.u_at Bw 65000 8)) by exact (EXT 4%nat ltac:(lia)).
assert (A37 : ew E0 37 = w64 (TW.u_at Bw 88 4)) by exact (EXT 5%nat ltac:(lia)).
assert (A38 : ew E0 38 = w64 (TW.u_at Bw 16 8)) by exact (EXT 6%nat ltac:(lia)).
assert (A39 : ew E0 39 = w64 (TW.u_at Bw 40 8)) by exact (EXT 7%nat ltac:(lia)).
pose proof (mwb_entry W regs memc Bw Htw ltac:(intros a Ha; apply Hpres0; lia) Hsp Hsp16) as HS.
fold E0 in HS.
assert (SHOK : sh_ok segs MWB_Bx MWB_SH E0 (mrestrict (w_H W) memc)) by (unfold sh_ok, MWB_SH; apply Forall_nil).
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ mwb_wins (spZ regs) a ->
  aview segs (w_H W) memc a = aview segs (w_H W) memc a) by (intros; reflexivity).
assert (GA : forall a, apresent (w_H W) memc a -> apresent (w_H W) memc a) by (intros a Ha; exact Ha).
pose proof (@paj_run_x fx rc YE2k.tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  G_HARNESS_B HGX 0 []) as RUN.
pose (BR := paj_branch (PI := PI_transportb)).
pose proof (paj_ret_at (fx := fx) (PL := PL_transportb) (PI := PI_transportb)) as RET.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_m_wake)) memc (YK11.seg_rom segs)) mdc) Q)
  end.
(* run 1, +0x00 .. +0x14: the frame, the save of ra, a0 = &M, a1 = M.desk_known; stops at `beqz a1` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ mwb_awr Usp0 U8L U43L. }
mwb_kw KW GA Usp0 U8L U43L (spZ regs) W memc.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* M.desk_known = 0: a0 = -1 (SPEC_E_ARG), no store *)
  cbn [branch_taken] in Hc.
  rewrite (mwb_sext_atom E0 33 Bw 0 A33) in Hc.
  change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (mwb_eqb_s32 (TW.s32_at Bw 0) 0 ltac:(lia) ltac:(lia)) in Hc.
  rewrite Hc in Hm. cbv iota in Hm.
  destruct (mwb_some_inv _ _ _ _ Hm) as [HB Hr]. subst r. subst Bw'. clear Hm Hc.
  (* +0x28 .. +0x2c, +0x78 .. +0x80: a0 = -1, the epilogue *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { mwb_awr Usp0 U8L U43L. }
  mwb_kw KW GA Usp0 U8L U43L (spZ regs) W memc.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msF := msx) in * end.
  pose proof (st_ok_pi_region_nth E0 _ (restrict (w_H W) msF) 2 mwbR_ea HS eq_refl) as RGea.
  pose proof (st_ok_pi_region_nth E0 _ (restrict (w_H W) msF) 4 mwbR_ws HS eq_refl) as RGws.
  pose proof (st_ok_pi_region_nth E0 _ (restrict (w_H W) msF) 5 mwbR_fa HS eq_refl) as RGfa.
  pose proof (st_ok_pi_region_nth E0 _ (restrict (w_H W) msF) 6 mwbR_e2 HS eq_refl) as RGe2.
  pose proof (mwb_world_same E0 W memc (ms_mem msF) Bw (spZ regs) Htw U8L U43L A35 A37 A38 A39
    RGea RGws RGfa RGe2 ltac:(lia) KW) as HTW.
  mwb_regv HS (1%bv : bv 5) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  mwb_regv HS (Z_to_bv 5 10) (w64 (-1)) RF10 ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mwb_u64; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs msF)) by
    (apply (aregs_preserved_of_st_ok segs (w_H W) E0 _ msF regs (mwb_ex Bw) HS);
     [apply mwb_agree; [intros n Hn; reflexivity | reflexivity] | vm_compute; reflexivity]).
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ mwb_Zs (spZ regs) a ->
    aview segs (w_H W) (ms_mem msF) a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; apply KW; [exact Ha | intros Hc0; exact (Hn (mwb_wins_Zs _ a Hc0))]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  exact (mwb_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw (-1)
           (ms_regs msF) (ms_mem msF) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GA
           HTW HPF RF1 RF10 matF). }
(* M.desk_known <> 0 *)
cbn [branch_taken] in Hc.
rewrite (mwb_sext_atom E0 33 Bw 0 A33) in Hc.
change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hc.
rewrite (mwb_eqb_s32 (TW.s32_at Bw 0) 0 ltac:(lia) ltac:(lia)) in Hc.
rewrite Hc in Hm. cbv iota in Hm. rename Hc into Hdk.
(* run 2, +0x18 .. +0x1c: a1 = M.foreign; stops at `beqz a1` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ mwb_awr Usp0 U8L U43L. }
mwb_kw KW GA Usp0 U8L U43L (spZ regs) W memc.
psrr_branch_tok RUN BR HS SHOK Bspan.
2:{ (* M.foreign <> 0: a0 = -10 (SPEC_E_REFUSED), no store *)
  cbn [branch_taken] in Hc.
  rewrite (mwb_sext_atom E0 34 Bw 24 A34) in Hc.
  change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (mwb_eqb_s32 (TW.s32_at Bw 24) 0 ltac:(lia) ltac:(lia)) in Hc.
  rewrite Hc in Hm. cbn [negb] in Hm. cbv iota in Hm.
  destruct (mwb_some_inv _ _ _ _ Hm) as [HB Hr]. subst r. subst Bw'. clear Hm Hc.
  (* +0x20 .. +0x24, +0x78 .. +0x80: a0 = -10, the epilogue *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { mwb_awr Usp0 U8L U43L. }
  mwb_kw KW GA Usp0 U8L U43L (spZ regs) W memc.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msF := msx) in * end.
  pose proof (st_ok_pi_region_nth E0 _ (restrict (w_H W) msF) 2 mwbR_ea HS eq_refl) as RGea.
  pose proof (st_ok_pi_region_nth E0 _ (restrict (w_H W) msF) 4 mwbR_ws HS eq_refl) as RGws.
  pose proof (st_ok_pi_region_nth E0 _ (restrict (w_H W) msF) 5 mwbR_fa HS eq_refl) as RGfa.
  pose proof (st_ok_pi_region_nth E0 _ (restrict (w_H W) msF) 6 mwbR_e2 HS eq_refl) as RGe2.
  pose proof (mwb_world_same E0 W memc (ms_mem msF) Bw (spZ regs) Htw U8L U43L A35 A37 A38 A39
    RGea RGws RGfa RGe2 ltac:(lia) KW) as HTW.
  mwb_regv HS (1%bv : bv 5) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  mwb_regv HS (Z_to_bv 5 10) (w64 (-10)) RF10 ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mwb_u64; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs msF)) by
    (apply (aregs_preserved_of_st_ok segs (w_H W) E0 _ msF regs (mwb_ex Bw) HS);
     [apply mwb_agree; [intros n Hn; reflexivity | reflexivity] | vm_compute; reflexivity]).
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ mwb_Zs (spZ regs) a ->
    aview segs (w_H W) (ms_mem msF) a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; apply KW; [exact Ha | intros Hc0; exact (Hn (mwb_wins_Zs _ a Hc0))]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  exact (mwb_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw (-10)
           (ms_regs msF) (ms_mem msF) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GA
           HTW HPF RF1 RF10 matF). }
(* M.foreign = 0 *)
cbn [branch_taken] in Hc.
rewrite (mwb_sext_atom E0 34 Bw 24 A34) in Hc.
change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hc.
rewrite (mwb_eqb_s32 (TW.s32_at Bw 24) 0 ltac:(lia) ltac:(lia)) in Hc.
rewrite Hc in Hm. cbn [negb] in Hm. cbv iota in Hm. rename Hc into Hfo.
(* run 3, +0x30 .. +0x48: a3 = OW.e2, a4 = g_now, a2 = OW.e2 + 1, the stores at M + 16 and M + 40; stops at
   `blt a2, a3` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ mwb_awr Usp0 U8L U43L. }
mwb_kw KW GA Usp0 U8L U43L (spZ regs) W memc.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* OW.e2 = INT_MAX: the trap word; the model premise says m_wake_m is None there *)
  exfalso. apply (mwb_br_trap E0 Bw A35) in Hc. rewrite Hc in Hm. rewrite Z.eqb_refl in Hm. cbv iota in Hm.
  discriminate Hm. }
(* OW.e2 < INT_MAX *)
revert Hm. destruct (TW.s32_at Bw 65508 =? 2 ^ 31 - 1); cbv iota; intros Hm; [discriminate Hm|]. clear Hc.
(* run 4, +0x50 .. +0x58: a3 = M.fail, the stores of OW.e2 + 1 and of 0 at M + 88; stops at `beqz a3` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ mwb_awr Usp0 U8L U43L. }
mwb_kw KW GA Usp0 U8L U43L (spZ regs) W memc.
psrr_branch_tok RUN BR HS SHOK Bspan.
2:{ (* the old M.fail <> 0: a0 = -5 (- EIO) *)
  cbn [branch_taken] in Hc.
  rewrite (mwb_sext_atom E0 37 Bw 88 A37) in Hc.
  change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (mwb_eqb_s32 (TW.s32_at Bw 88) 0 ltac:(lia) ltac:(lia)) in Hc.
  rewrite Hc in Hm. cbn [negb] in Hm. cbv iota in Hm.
  destruct (mwb_some_inv _ _ _ _ Hm) as [HB Hr]. subst r. subst Bw'. clear Hm Hc.
  (* +0x60 .. +0x64, +0x78 .. +0x80: a0 = -5, the epilogue *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { mwb_awr Usp0 U8L U43L. }
  mwb_kw KW GA Usp0 U8L U43L (spZ regs) W memc.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msF := msx) in * end.
  pose proof (st_ok_pi_region_nth E0 _ (restrict (w_H W) msF) 2 mwbR_ea4 HS eq_refl) as RGea.
  pose proof (st_ok_pi_region_nth E0 _ (restrict (w_H W) msF) 4 mwbR_ws4 HS eq_refl) as RGws.
  pose proof (st_ok_pi_region_nth E0 _ (restrict (w_H W) msF) 5 mwbR_fa4 HS eq_refl) as RGfa.
  pose proof (st_ok_pi_region_nth E0 _ (restrict (w_H W) msF) 6 mwbR_e24 HS eq_refl) as RGe2.
  pose proof (mwb_world_4 E0 W memc (ms_mem msF) Bw (spZ regs) Htw U8L U43L A35 A36
    RGea RGws RGfa RGe2 ltac:(lia) KW) as HTW.
  rewrite (mwb_W_m Bw HLB).
  mwb_regv HS (1%bv : bv 5) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  mwb_regv HS (Z_to_bv 5 10) (w64 (-5)) RF10 ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mwb_u64; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs msF)) by
    (apply (aregs_preserved_of_st_ok segs (w_H W) E0 _ msF regs (mwb_ex Bw) HS);
     [apply mwb_agree; [intros n Hn; reflexivity | reflexivity] | vm_compute; reflexivity]).
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ mwb_Zs (spZ regs) a ->
    aview segs (w_H W) (ms_mem msF) a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; apply KW; [exact Ha | intros Hc0; exact (Hn (mwb_wins_Zs _ a Hc0))]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  exact (mwb_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (mwbm_W Bw) (-5)
           (ms_regs msF) (ms_mem msF) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GA
           HTW HPF RF1 RF10 matF). }
(* the old M.fail = 0: m_set (S_WAKING, R_WAKE) *)
cbn [branch_taken] in Hc.
rewrite (mwb_sext_atom E0 37 Bw 88 A37) in Hc.
change (sv_denot E0 (SLit 0)) with (Z_to_bv 64 0) in Hc.
rewrite (mwb_eqb_s32 (TW.s32_at Bw 88) 0 ltac:(lia) ltac:(lia)) in Hc.
rewrite Hc in Hm. cbn [negb] in Hm. cbv iota in Hm. rename Hc into Hfa.
revert Hm. destruct (TCB.m_set_m (mwb_W Bw) 1 1) as [[B5 u]|] eqn:HMS5; intros Hm; [|discriminate Hm].
destruct u. cbv iota in Hm.
destruct (mwb_some_inv _ _ _ _ Hm) as [HB Hr]. subst r. subst Bw'. clear Hm.
(* run 5, +0x68 .. +0x70: a0 = 1, a1 = 1, the call of m_set; stops at the call *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ mwb_awr Usp0 U8L U43L. }
mwb_kw KW GA Usp0 U8L U43L (spZ regs) W memc.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msC := msx) in * end.
(* the world at the call: B4 *)
pose proof (mwb_st_ok_region_nth E0 _ (restrict (w_H W) msC) 2 mwbR_ea4 HS eq_refl) as RGea.
pose proof (mwb_st_ok_region_nth E0 _ (restrict (w_H W) msC) 4 mwbR_ws4 HS eq_refl) as RGws.
pose proof (mwb_st_ok_region_nth E0 _ (restrict (w_H W) msC) 5 mwbR_fa4 HS eq_refl) as RGfa.
pose proof (mwb_st_ok_region_nth E0 _ (restrict (w_H W) msC) 6 mwbR_e24 HS eq_refl) as RGe2.
pose proof (mwb_world_4 E0 W memc (ms_mem msC) Bw (spZ regs) Htw U8L U43L A35 A36
  RGea RGws RGfa RGe2 ltac:(lia) KW) as HTW4.
rewrite <- (mwb_W_m Bw HLB) in HTW4.
assert (KAC : forall a, 0 <= a < 2 ^ 64 -> ~ mwb_Zs (spZ regs) a ->
  aview segs (w_H W) (ms_mem msC) a = aview segs (w_H W) memc a)
  by (intros a Ha Hn; apply KW; [exact Ha | intros Hc0; exact (Hn (mwb_wins_Zs _ a Hc0))]).
(* the registers at m_set's entry *)
assert (HBR : BASE + 9960 = 539016) by (vm_compute; reflexivity).
mwb_regv HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 9960)) R1 ltac:(cbn [sv_denot]; exact (img_env_codeptr E0 HEI 9960)).
mwb_regv HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 16)) R2
  ltac:(cbn [sv_denot]; rewrite Usp0; f_equal; lia).
mwb_regv HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
mwb_regv HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
mwb_regv HS (Z_to_bv 5 10) (Z_to_bv 64 1) R10 ltac:(reflexivity).
mwb_regv HS (Z_to_bv 5 11) (Z_to_bv 64 1) R11 ltac:(reflexivity).
assert (HspC : spZ (ms_regs msC) = spZ regs - 16).
{ pose proof (f_equal bv_unsigned R2) as HX.
  change (spZ (ms_regs msC) = bv_unsigned (Z_to_bv 64 (spZ regs - 16))) in HX.
  rewrite unsigned_lit_small in HX by lia. exact HX. }
assert (HretC : YK0s.ret_ok (Z_to_bv 64 (BASE + 9960))) by (apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4C : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + 9960))) by (rewrite HBR, unsigned_lit_small by lia; lia).
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx segs (transportb_sigma TB_m_set) rg mm mdx) Q) end.
(* the call: m_set's statement on the same journal *)
eapply SRr_bind.
{ exact (HMSET fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem msC) _ k (ms_regs msC) 1 1 (mwb_W Bw) B5 HJ
    (eq_ind_r YK0s.ret_ok HretC R1) (eq_ind_r (fun w => 4096 <= bv_unsigned w) Hra4C R1)
    R3 R4 R10 R11
    ltac:(rewrite HspC; rewrite Zminus_mod, Hsp16; reflexivity)
    ltac:(rewrite HspC; lia) ltac:(rewrite HspC; lia)
    HTW4 HMS5 ltac:(lia) ltac:(lia) ltac:(unfold MWAKE_EV in Hev; exact Hev)). }
cbv beta. intros W2 c2 HwW2 HQ.
unfold transport_mset_post, transport_cg_post in HQ.
destruct HQ as (ly2 & S2 & regs2 & mem2 & md2 & e & Hc2 & He & HJ2 & HP2 & Hfr2 & Hperm2 & HK2 & HMO2 & HX2).
subst c2.
assert (He0 : e = 0) by (unfold MSET_EV in He; lia). subst e.
(* the state after the call: the stack region (ra at sp - 8) kept, the caller-saved registers fresh atoms *)
assert (HKEPT : Forall (region_kept segs E0 (ms_mem (restrict (w_H W) msC)) (mrestrict (w_H W2) mem2))
   [YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]]).
{ constructor; [|constructor].
  exact (mwb_region_kept_stack E0 lyc Sc W (ms_mem msC) W2 mem2 _ _ _ 2 (-16) 0 (-16) 0 _ sp0 (spZ regs)
    STK FP ly S W0 mem0 md0 own ly2 S2 md2 (k + 0) HK2 HJ2 Usp0 ltac:(rewrite HspC; lia) ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(lia)). }
jafter_call_keep_pi HS MWB_K regs2 (mrestrict (w_H W2) mem2) HP2 [0%nat] HS2.
specialize (HS2 HKEPT).
rewrite <- restrict_mkst_fx in HS2.
lazymatch type of HS2 with st_ok_pi _ _ ?Ex _ _ => set (E1 := Ex) in HS2 end.
assert (HEIa : img_env VAL A_LIM E1)
  by (unfold E1; apply img_env_havoc; [exact HEI | rewrite length_map; vm_compute; lia]).
assert (HE1 : forall n, (n < MWB_K)%nat -> ew E1 n = ew E0 n) by (intros n Hn; unfold E1; apply ew_havoc_old; exact Hn).
assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite HE1 by (unfold MWB_K; lia); exact Usp0).
assert (SHOK1 : sh_ok segs MWB_Bx MWB_SH E1 (mrestrict (w_H W2) mem2)) by (unfold sh_ok, MWB_SH; apply Forall_nil).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg ?pc ?mm ?rom) ?mdx) ?Q =>
  replace pc with (Z_to_bv 64 (BASE + 9960)) by (symmetry; exact R1) end.
clear HS HJ SHOK HEI.
(* run 6, +0x74 .. +0x80: a0 = 0, ra reloaded, sp + 16; stops at `ret` *)
paj_run_tok RUN HS2 HJ2 SHOK1 Bspan.
{ mwb_awr Usp1 U8L U43L. }
lazymatch goal with
| HFr : frame_of ?Ex ?rs (mrestrict ?H _) (mrestrict ?H ?mn), HG : mem_grows _ _ |- SRr _ _ (mkCfg ?msx _) _ =>
  set (msF := msx) in *;
  assert (KWF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - MWAKE_STK <= a < spZ regs) ->
                aview segs (w_H W2) (ms_mem msF) a = aview segs (w_H W2) mem2 a)
    by (intros a Ha Hn;
        refine (mwb_kept_of_frame Ex rs H _ _ (fun x => spZ regs - MWAKE_STK <= x < spZ regs) HFr _ a Ha Hn);
        intros b0 wlo whi x Hin Hx;
        lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
        cbn [In] in Hin; destruct Hin as [Hin | []]; injection Hin as <- <- <-;
        cbn [base_val] in Hx; rewrite Usp1 in Hx; cbv beta; lia);
  assert (GAF : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msF) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha))
end.
mwb_regv HS2 (1%bv : bv 5) (YK11.getr regs 1) RF1
  ltac:(cbn [sv_denot]; rewrite HE1 by (unfold MWB_K; lia);
        rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
mwb_regv HS2 (Z_to_bv 5 10) (w64 0) RF10 ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mwb_u64; reflexivity).
assert (HPF : aregs_preserved regs (ms_regs msF)) by
  (apply (aregs_preserved_of_st_ok segs (w_H W2) E1 _ msF regs (mwb_ex Bw) HS2);
   [apply mwb_agree; [intros n Hn; apply HE1; unfold MWB_K; lia | reflexivity] | vm_compute; reflexivity]).
eapply (RET W2 _ _ _ _ _ HS2 eq_refl ltac:(vm_compute; reflexivity)).
intros matF.
exact (mwb_close_call STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw B5
  (ms_mem msC) (ms_regs msC) W2 ly2 S2 mem2 0 (ms_regs msF) (ms_mem msF) _
  LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra KAC GA HspC ltac:(unfold MSET_EV; lia) Hfr2 Hperm2 HK2 HMO2 HX2
  (fun a => mwb_wr_sub Bw a HLB Hdk Hfo Hfa) HJ2 KWF GAF HPF RF1 RF10 matF).
Qed.

End mwakeb.

(* The statement of lib/B/Prog/m_wake_cg.v. *)
Theorem transport_m_wake_cg_holds : forall fx rc B MT, @transport_m_wake_cg_holds_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@mwb_holds fx rc B MT). Qed.
