(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 1111 of its 1210 lines of code are new or changed and 827 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/m_wake_cgW.v, with its module paths, module names and numbers changed; 5310 of its 5612 lines of code are new or changed and 908 lines of the source are left out. *)
(* m_wake: Theorem transport_m_wake_cg_holds : the statement transport_m_wake_cg_holds_stmt of
   lib/A/Prog/m_wake_cg.v, the machine walk of m_wake on fuzz_transport.asan at 0x83d00 (328 bytes, frame 16).

   The walk is a G-form walk: it holds the caller's journal ajournal_gx G_HARNESS 0 [] (lib/A/W_journalG.v) from the
   entry to the return, and the runs are the symbolic runs of lib/A/Prog/PaShadow.v taken over that journal
   (lib/A/Prog/TransportGRunA.v paj_run_x). The stores into M and OW are allowed by the run's write right awr_ok_x
   (a byte of G). m_wake calls nothing, so there is no call lift; it has six runs and five branch splits:

     run 1 (+0x00 .. +0x10)  the frame, the save of ra, a2 = &M, a0 = M.desk_known; stops at `beqz a0`.
       split 1   a0 = 0:  a0 = -1 (SPEC_E_ARG) and the epilogue. No store.
     run 2 (+0x14 .. +0x18)  a0 = M.foreign; stops at `beqz a0`.
       split 2   a0 <> 0: a0 = -10 (SPEC_E_REFUSED) and the epilogue. No store.
     run 3 (+0x1c .. +0x64)  a3 = &OW, a1 = OW.e2, a0 = the GOT word, a4 = g_now, a5 = the shadow base through the
                             GOT word, the stores of OW.e2 + 1, of 0 at M + 16 (8 bytes), of g_now at M + 40 and of
                             0 at M + 88, and a1 = the OLD M.fail; stops at `beqz a1`.
       split 3   a1 <> 0: a0 = -5 (- EIO) and the epilogue.
     run 4 (+0x68 .. +0x70)  a6 = M.state; stops at `bne a6, 1`.
       split 4   a6 = 1:  a0 = 0 and the epilogue (m_set's early return).
     run 5 (+0x74 .. +0x8c)  a4 = OW.n; stops at `blt 15, a4`.
       split 5   15 < a4: a0 = 0, OW.n + 1, M.state = S_WAKING and the epilogue. No transition record.
     run 6 (+0x90 .. +0x110, one arm per value 0 .. 15 of OW.n)  the three checked stores of OW.t[OW.n], OW.n + 1,
                             M.state = S_WAKING and the epilogue.

   OW.n is pinned to a literal before run 6 so that each store's address is a literal offset of OW: with an open
   index the shadow check's address is not an offset of one atom and the token engine cannot decide it. The model
   premise gives 0 <= OW.n (m_set_m is None below 0), the branch gives OW.n <= 15.

   Every instrumented check (the three stores of OW.t[OW.n]) is decided by the run's shadow entry over OW's 304
   payload bytes (mw_shok, from trans_ow_cells B: the shadow of OW's 38 whole granules is 0), so no error path
   (errpath_store4) is reached and the runs leave no shadow obligation.

   The post: transport_cg_post over G_HARNESS (mw_close): the journal at the return, the callee-saved registers,
   acall_kept_g by TransportGCg.v dk_kept_step_g over the call's stack window and the bytes of G, and the world
   relation at the model's world. The model is characterised once (mw_m_eq, the shape of lib/Prog/T/m_wake.v's
   m_wake_m_eq) and its worlds are put in the binary's write order (mw_W_m, mw_fin_m, mw_fin_rec_m); the machine's
   side of each written span is read off the final state's region chunks (mw_byte), and the two are joined span by
   span by mw_step over TWorldG.v's tw_write. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg m_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TCb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TCB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.

(* ------------------------------------------------------------------ *)
(* 1. The model: m_wake_m as a flat cascade, and its worlds in the      *)
(*    order the binary writes them.                                     *)
(* ------------------------------------------------------------------ *)

Lemma mw_firstn_app_add : forall (l1 l2 : list byte) n, firstn (length l1 + n) (l1 ++ l2) = l1 ++ firstn n l2.
Proof. induction l1 as [|x l1 IH]; intros l2 n; cbn; [reflexivity | f_equal; apply IH]. Qed.

Lemma mw_skipn_app_add : forall (l1 l2 : list byte) n, skipn (length l1 + n) (l1 ++ l2) = skipn n l2.
Proof. induction l1 as [|x l1 IH]; intros l2 n; cbn; [reflexivity | apply IH]. Qed.

Lemma mw_firstn_app_self : forall (l1 l2 : list byte), firstn (length l1) (l1 ++ l2) = l1.
Proof. induction l1 as [|x l1 IH]; intros l2; cbn; [reflexivity | f_equal; apply IH]. Qed.

Lemma mw_upd_app : forall (bs v w : list byte) k,
  0 <= k -> (Z.to_nat k + length v <= length bs)%nat ->
  TW.upd bs k (v ++ w) = TW.upd (TW.upd bs k v) (k + Z.of_nat (length v)) w.
Proof.
  intros bs v w k Hk Hl.
  assert (LL : length (firstn (Z.to_nat k) bs) = Z.to_nat k) by (rewrite length_firstn; lia).
  unfold TW.upd. rewrite length_app.
  replace (Z.to_nat (k + Z.of_nat (length v))) with (Z.to_nat k + length v)%nat by lia.
  replace (Z.to_nat k + length v)%nat with (length (firstn (Z.to_nat k) bs) + length v)%nat by lia.
  rewrite mw_firstn_app_add, mw_firstn_app_self.
  replace (length (firstn (Z.to_nat k) bs) + length v + length w)%nat
    with (length (firstn (Z.to_nat k) bs) + (length v + length w))%nat by lia.
  rewrite mw_skipn_app_add, mw_skipn_app_add, skipn_skipn.
  replace (length w + (length (firstn (Z.to_nat k) bs) + length v))%nat
    with (Z.to_nat k + (length v + length w))%nat by lia.
  rewrite <- !app_assoc. reflexivity.
Qed.

(* the 8-byte zeroing of M.e2_acked / M.e1_us (one sd) is the model's two 4-byte stores *)
Lemma mw_upd_zero8 : forall (bs : list byte) k k', 0 <= k -> k' = k + 4 -> k + 8 <= Z.of_nat (length bs) ->
  TW.upd (TW.upd bs k (TW.put 4 0)) k' (TW.put 4 0) = TW.upd bs k (TW.put 8 0).
Proof.
  intros bs k k' Hk -> Hl.
  replace (TW.put 8 0) with (TW.put 4 0 ++ TW.put 4 0) by (vm_compute; reflexivity).
  rewrite (mw_upd_app bs (TW.put 4 0) (TW.put 4 0) k) by (rewrite ?TWL.length_put; lia).
  rewrite TWL.length_put. reflexivity.
Qed.

Lemma mw_wlen_upd : forall (bs : list byte) k n v,
  Z.of_nat (length bs) = 65616 -> 0 <= k -> k + Z.of_nat n <= 65616 ->
  Z.of_nat (length (TW.upd bs k (TW.put n v))) = 65616.
Proof. intros bs k n v H Hk Hn. rewrite TWL.length_upd_put; [exact H | lia | lia]. Qed.

Ltac mw_wlen := repeat (apply mw_wlen_upd; [ | lia | lia ]); assumption.
Ltac mw_wside :=
  rewrite ?TWL.length_put;
  first [ lia
        | match goal with
          | |- context [Z.of_nat (length ?X)] =>
              let H := fresh "HW" in assert (H : Z.of_nat (length X) = 65616) by mw_wlen; rewrite H; lia
          end ].

Lemma mw_s32_peel : forall (bs : list byte) k n v k',
  Z.of_nat (length bs) = 65616 -> 0 <= k -> 0 <= k' -> k + Z.of_nat n <= 65616 ->
  (k' + 4 <= k \/ k + Z.of_nat n <= k') ->
  TW.s32_at (TW.upd bs k (TW.put n v)) k' = TW.s32_at bs k'.
Proof.
  intros bs k n v k' HL Hk Hk' Hn Hd.
  rewrite TWL.s32_at_upd_out; [reflexivity | lia | lia | rewrite TWL.length_put; lia | rewrite TWL.length_put; lia].
Qed.

Lemma mw_u_peel : forall (bs : list byte) k n v k' n',
  Z.of_nat (length bs) = 65616 -> 0 <= k -> 0 <= k' -> k + Z.of_nat n <= 65616 ->
  (k' + Z.of_nat n' <= k \/ k + Z.of_nat n <= k') ->
  TW.u_at (TW.upd bs k (TW.put n v)) k' n' = TW.u_at bs k' n'.
Proof.
  intros bs k n v k' n' HL Hk Hk' Hn Hd.
  rewrite TWL.u_at_upd_out; [reflexivity | lia | lia | rewrite TWL.length_put; lia | rewrite TWL.length_put; lia].
Qed.

Ltac mw_peelg :=
  repeat first [ rewrite mw_s32_peel by (first [mw_wlen | lia]) | rewrite mw_u_peel by (first [mw_wlen | lia]) ].

(* OW.t[i]'s setters at their world offsets; not convertible to these for an open i, so proved *)
Lemma mw_s_ots : forall bs i v, TW.set_OW_t_state bs i v = TW.upd bs (65316 + 12 * i) (TW.put 4 v).
Proof. intros. unfold TW.set_OW_t_state, TW.A_OW_t_state, TW.OFF_OW. f_equal. lia. Qed.
Lemma mw_s_oto : forall bs i v, TW.set_OW_t_old bs i v = TW.upd bs (65320 + 12 * i) (TW.put 4 v).
Proof. intros. unfold TW.set_OW_t_old, TW.A_OW_t_old, TW.OFF_OW. f_equal. lia. Qed.
Lemma mw_s_otr : forall bs i v, TW.set_OW_t_reason bs i v = TW.upd bs (65324 + 12 * i) (TW.put 4 v).
Proof. intros. unfold TW.set_OW_t_reason, TW.A_OW_t_reason, TW.OFF_OW. f_equal. lia. Qed.

(* the model's world, re-ordered into the order the binary writes it *)
Ltac mw_to_machine Bw :=
  mw_peelg;
  rewrite (mw_upd_zero8 _ 16 20) by (first [lia | mw_wside]);
  rewrite (TWL.upd_upd_comm _ (TW.put 8 (TW.u_at Bw 65000 8)) (TW.put 4 (TW.s32_at Bw 65508 + 1)) 40 65508)
    by (first [lia | mw_wside]);
  rewrite (TWL.upd_upd_comm _ (TW.put 8 0) (TW.put 4 (TW.s32_at Bw 65508 + 1)) 16 65508)
    by (first [lia | mw_wside]).

(* The model's four intermediate worlds, named exactly as TCb.v builds them, so that the characterisation below
   holds by conversion alone. *)
Definition mw_B1 (B : list byte) : list byte := TW.set_M_e1_us (TW.set_M_e2_acked B 0) 0.
Definition mw_B2 (B : list byte) : list byte := TW.set_M_wake_sent (mw_B1 B) (TW.g_now (mw_B1 B)).
Definition mw_B3 (B : list byte) : list byte := TW.set_OW_e2 (mw_B2 B) (TW.OW_e2 (mw_B2 B) + 1).
Definition mw_W (B : list byte) : list byte := TW.set_M_fail (mw_B3 B) 0.
Definition mw_fin (B : list byte) : list byte :=
  TW.set_M_state (TW.set_OW_n (mw_W B) (TW.OW_n (mw_W B) + 1)) TCB.S_WAKING.
Definition mw_fin_rec (B : list byte) : list byte :=
  TW.set_M_state
    (TW.set_OW_n (TW.set_OW_t_reason (TW.set_OW_t_old (TW.set_OW_t_state (mw_W B) (TW.OW_n (mw_W B)) TCB.S_WAKING)
                                        (TW.OW_n (mw_W B)) (TW.M_state (mw_W B)))
                    (TW.OW_n (mw_W B)) TCB.R_WAKE)
       (TW.OW_n (mw_W B) + 1)) TCB.S_WAKING.

Lemma mw_m_eq : forall B,
  TCB.m_wake_m B =
    (if TW.M_desk_known B =? 0 then Some (B, -1)
     else if negb (TW.M_foreign B =? 0) then Some (B, -10)
     else if TW.OW_e2 (mw_B2 B) =? 2 ^ 31 - 1 then None
     else if negb (TW.M_fail (mw_B3 B) =? 0) then Some (mw_W B, -5)
     else if TW.M_state (mw_W B) =? 1 then Some (mw_W B, 0)
     else if TW.OW_n (mw_W B) <? 0 then None
     else if TW.OW_n (mw_W B) =? 2 ^ 31 - 1 then None
     else if 15 <? TW.OW_n (mw_W B) then Some (mw_fin B, 0)
     else Some (mw_fin_rec B, 0)).
Proof.
  intros B.
  unfold mw_fin_rec, mw_fin, mw_W, mw_B3, mw_B2, mw_B1.
  unfold TCB.m_wake_m, TCB.m_set_m, TCB.truth, TCB.int_inc.
  cbv zeta.
  set (b1 := TW.set_M_e1_us (TW.set_M_e2_acked B 0) 0) in *.
  set (b2 := TW.set_M_wake_sent b1 (TW.g_now b1)) in *.
  destruct (TW.M_desk_known B =? 0) eqn:E1; cbn [negb]; cbv iota; [reflexivity|].
  destruct (TW.M_foreign B =? 0) eqn:E2; cbn [negb]; cbv iota; [|reflexivity].
  destruct (TW.OW_e2 b2 =? 2 ^ 31 - 1) eqn:EO; unfold TCB.INT_MAX; rewrite ?EO; cbv iota; [reflexivity|].
  set (b3 := TW.set_OW_e2 b2 (TW.OW_e2 b2 + 1)) in *.
  destruct (TW.M_fail b3 =? 0) eqn:E3; cbn [negb]; cbv iota; [|reflexivity].
  set (b4 := TW.set_M_fail b3 0) in *.
  destruct (TW.M_state b4 =? 1) eqn:E4; unfold TCB.S_WAKING; rewrite ?E4; cbv iota; [reflexivity|].
  unfold TCB.TRANS_MAX, TCB.INT_MAX, TCB.R_WAKE.
  destruct (TW.OW_n b4 <? 0) eqn:EN.
  { apply Z.ltb_lt in EN.
    replace (TW.OW_n b4 <? 16) with true by (symmetry; apply Z.ltb_lt; lia).
    try rewrite (proj2 (Z.ltb_lt _ _) EN). cbv iota. reflexivity. }
  apply Z.ltb_ge in EN.
  destruct (TW.OW_n b4 =? 2 ^ 31 - 1) eqn:EI.
  { apply Z.eqb_eq in EI.
    replace (TW.OW_n b4 <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
    try rewrite (proj2 (Z.eqb_eq _ _) EI). cbv iota. reflexivity. }
  apply Z.eqb_neq in EI.
  try rewrite (proj2 (Z.eqb_neq _ _) EI).
  destruct (15 <? TW.OW_n b4) eqn:E5.
  { apply Z.ltb_lt in E5.
    replace (TW.OW_n b4 <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
    cbv iota. reflexivity. }
  { apply Z.ltb_ge in E5.
    replace (TW.OW_n b4 <? 16) with true by (symmetry; apply Z.ltb_lt; lia).
    try replace (TW.OW_n b4 <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    cbv iota. reflexivity. }
Qed.

(* The model's result, inverted on abstract terms: never injection / inversion on Some (Bw', r) itself,
   which reduces the 65616-byte world. *)
Lemma mw_some_inv : forall (x y : list byte) (u v : Z), Some (x, u) = Some (y, v) -> y = x /\ v = u.
Proof. intros x y u v H. injection H as H1 H2. split; [symmetry; exact H1 | symmetry; exact H2]. Qed.

(* the model's worlds, read off B and written in the binary's order *)
Definition mwm_W (B : list byte) : list byte :=
  TW.upd (TW.upd (TW.upd (TW.upd B 65508 (TW.put 4 (TW.s32_at B 65508 + 1))) 16 (TW.put 8 0))
           40 (TW.put 8 (TW.u_at B 65000 8))) 88 (TW.put 4 0).

(* Getters and setters to their literal offsets by SYNTACTIC matching and [change]: a [rewrite] loops, because
   rewrite unifies up to delta and the two sides are convertible. *)
Ltac mw_gs :=
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
  | |- context [TW.set_OW_n ?x ?v] => change (TW.set_OW_n x v) with (TW.upd x 65312 (TW.put 4 v))
  | |- context [TW.set_M_state ?x ?v] => change (TW.set_M_state x v) with (TW.upd x 12 (TW.put 4 v))
  end.

Lemma mw_e2 : forall B, Z.of_nat (length B) = 65616 -> TW.OW_e2 (mw_B2 B) = TW.s32_at B 65508.
Proof. intros B HL. unfold mw_B2, mw_B1. mw_gs. mw_peelg. reflexivity. Qed.

Lemma mw_fa : forall B, Z.of_nat (length B) = 65616 -> TW.M_fail (mw_B3 B) = TW.s32_at B 88.
Proof. intros B HL. unfold mw_B3, mw_B2, mw_B1. mw_gs. mw_peelg. reflexivity. Qed.

Lemma mw_st : forall B, Z.of_nat (length B) = 65616 -> TW.M_state (mw_W B) = TW.s32_at B 12.
Proof. intros B HL. unfold mw_W, mw_B3, mw_B2, mw_B1. mw_gs. mw_peelg. reflexivity. Qed.

Lemma mw_on : forall B, Z.of_nat (length B) = 65616 -> TW.OW_n (mw_W B) = TW.s32_at B 65312.
Proof. intros B HL. unfold mw_W, mw_B3, mw_B2, mw_B1. mw_gs. mw_peelg. reflexivity. Qed.

Lemma mw_W_m : forall B, Z.of_nat (length B) = 65616 -> mw_W B = mwm_W B.
Proof. intros B HL. unfold mw_W, mw_B3, mw_B2, mw_B1, mwm_W. mw_gs. mw_to_machine B. reflexivity. Qed.

Lemma mw_fin_m : forall B, Z.of_nat (length B) = 65616 ->
  mw_fin B = TW.upd (TW.upd (mwm_W B) 65312 (TW.put 4 (TW.s32_at B 65312 + 1))) 12 (TW.put 4 1).
Proof.
  intros B HL. unfold mw_fin. rewrite (mw_on B HL). rewrite (mw_W_m B HL). mw_gs.
  unfold TCB.S_WAKING. reflexivity.
Qed.

Lemma mw_fin_rec_m : forall B, Z.of_nat (length B) = 65616 ->
  mw_fin_rec B =
    TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W B) (65316 + 12 * TW.s32_at B 65312) (TW.put 4 1))
                             (65320 + 12 * TW.s32_at B 65312) (TW.put 4 (TW.s32_at B 12)))
                      (65324 + 12 * TW.s32_at B 65312) (TW.put 4 1))
             65312 (TW.put 4 (TW.s32_at B 65312 + 1))) 12 (TW.put 4 1).
Proof.
  intros B HL. unfold mw_fin_rec.
  rewrite (mw_on B HL). rewrite (mw_st B HL). rewrite (mw_W_m B HL). mw_gs.
  rewrite mw_s_ots. rewrite mw_s_oto. rewrite mw_s_otr.
  unfold TCB.S_WAKING, TCB.R_WAKE. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The symbolic state at the entry                                  *)
(* ------------------------------------------------------------------ *)

(* Atoms: 0 .. 31 the registers at the entry, 32 the shadow base, 33 .. 41 the world values the function reads:
   M.desk_known, M.foreign, M.state, M.fail, OW.e2, OW.n, g_now, M[16, 24) and M[40, 48). Regions: the 16-byte
   frame below sp (the save of ra), the shadow base's GOT word (object 1) and its cell (object 93), the six spans
   of M and the two spans of OW the function reads or writes, and g_now. A span the function stores into is
   writable and is covered by a chunk at the entry, so every byte of every window has a value in the final state;
   every byte outside the windows is kept. OW.t[OW.n]'s 12 bytes get their own region once OW.n is a literal. *)
Definition Rm_dk : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition Rm_st : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 12 16 12 16 [YP09.mkChunk 12 (CVal 4 (SOff 35 0))].
Definition Rm_ea : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 16 24 16 24 [YP09.mkChunk 16 (CVal 8 (SOff 40 0))].
Definition Rm_fo : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 24 28 24 24 [YP09.mkChunk 24 (CVal 4 (SOff 34 0))].
Definition Rm_ws : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 40 48 40 48 [YP09.mkChunk 40 (CVal 8 (SOff 41 0))].
Definition Rm_fa : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 88 92 88 92 [YP09.mkChunk 88 (CVal 4 (SOff 36 0))].
Definition Ro_n : YP09.region := YP09.mkRegion (Some (A_OBJ 12)) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 38 0))].
Definition Ro_e2 : YP09.region := YP09.mkRegion (Some (A_OBJ 12)) 196 200 196 200 [YP09.mkChunk 196 (CVal 4 (SOff 37 0))].
Definition Rg_now : YP09.region := YP09.mkRegion (Some (A_OBJ 27)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 39 0))].
Definition Ro_t (k : Z) : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 12)) (4 + 12 * k) (16 + 12 * k) (4 + 12 * k) (16 + 12 * k) [].

Definition mw_regions : smem :=
  [stack_region MWAKE_FRAME; got_regionP; bcell_regionP 32;
   Rm_dk; Rm_st; Rm_ea; Rm_fo; Rm_ws; Rm_fa; Ro_n; Ro_e2; Rg_now].
Definition mw_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (A_OBJ 8, mkAF TA_M TA_M 5); (A_OBJ 12, mkAF TA_OW TA_OW 5);
           (33%nat, mkAF 0 (2 ^ 32 - 1) 0); (34%nat, mkAF 0 (2 ^ 32 - 1) 0); (35%nat, mkAF 0 (2 ^ 32 - 1) 0);
           (36%nat, mkAF 0 (2 ^ 32 - 1) 0); (37%nat, mkAF 0 (2 ^ 32 - 1) 0); (38%nat, mkAF 0 (2 ^ 32 - 1) 0);
           (39%nat, mkAF 0 (2 ^ 64 - 1) 0); (40%nat, mkAF 0 (2 ^ 64 - 1) 0); (41%nat, mkAF 0 (2 ^ 64 - 1) 0)] [] [].
Definition ss_mw : sstate := mkSS AF_m_wake sr_atoms mw_regions None mw_facts.
Definition MW_SH : list shent := [mkSHE (A_OBJ 12) 0 304].
Definition MW_Bx : sv := SOff 32 0.

(* The bytes the walk may write: its stack window, and bytes of G. *)
Definition mw_Zs (sp : Z) (a : Z) : Prop := (sp - MWAKE_STK <= a < sp) \/ inG TG.G_HARNESS a.

(* A payload byte of image A's world table is a byte of G. *)
Lemma mw_inG_row : forall o b n a, In (o, b, n) TMAP_A -> b <= a < b + n -> inG TG.G_HARNESS a.
Proof.
intros o b n a Hin Ha. apply Exists_exists. exists (b, n).
split; [exact (TMAP_A_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.
Lemma mw_inG_M : forall a, TA_M <= a < TA_M + TW.SZ_M -> inG TG.G_HARNESS a.
Proof. intros a Ha. exact (mw_inG_row _ _ _ a TMAP_A_M Ha). Qed.
Lemma mw_inG_OW : forall a, TA_OW <= a < TA_OW + TW.SZ_OW -> inG TG.G_HARNESS a.
Proof. intros a Ha. exact (mw_inG_row _ _ _ a TMAP_A_OW Ha). Qed.
Lemma mw_tw_in_G : forall x, tw_in TMAP_A x -> inG TG.G_HARNESS x.
Proof. intros x (o & b & n & Hin & Hx). exact (mw_inG_row o b n x Hin Hx). Qed.

(* ---- the byte values a region's chunks give ---- *)

Lemma mw_shr_mod : forall X N k, 0 <= X -> 0 <= k -> k + 8 <= N ->
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

Lemma mw_bow : forall X (w : N) i, 0 <= X -> Z.of_N w <= 8 -> 0 <= i < Z.of_N w ->
  bv_unsigned (YP09.byte_of_word (Z_to_bv 64 X) i) = YO0f.le_byte X (N.to_nat w) (Z.to_nat i).
Proof.
intros X w i HX Hw Hi. unfold YP09.byte_of_word, YO0f.le_byte.
rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64).
replace (8 * Z.of_nat (N.to_nat w)) with (8 * Z.of_N w) by (rewrite N_nat_Z; reflexivity).
replace (8 * Z.of_nat (Z.to_nat i)) with (8 * i) by (rewrite Z2Nat.id by lia; reflexivity).
rewrite (mw_shr_mod X 64 (8 * i)) by lia.
rewrite (mw_shr_mod X (8 * Z.of_N w) (8 * i)) by lia. reflexivity.
Qed.

Lemma mw_le_byte_mod : forall X Y (m : nat) k, X mod 2 ^ (8 * Z.of_nat m) = Y mod 2 ^ (8 * Z.of_nat m) ->
  YO0f.le_byte X m k = YO0f.le_byte Y m k.
Proof. intros X Y m k H. unfold YO0f.le_byte. rewrite H. reflexivity. Qed.

Lemma mw_le_byte_small : forall X (m : nat) k, YO0f.le_byte X m k mod 256 = YO0f.le_byte X m k.
Proof. intros. unfold YO0f.le_byte. apply Z.mod_mod. lia. Qed.

(* ------------------------------------------------------------------ *)
(* 3. The walk                                                         *)
(* ------------------------------------------------------------------ *)

Section mwakew. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma mw_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 93) = FCells.CELL_K /\
  VAL (A_OBJ 8) = TA_M /\ VAL (A_OBJ 12) = TA_OW /\ VAL (A_OBJ 27) = TA_g_now /\
  BASE + AF_m_wake = transport_sigma TS_m_wake.
Proof. vm_compute. repeat split. Qed.

(* The two image regions hold what transport_cells says they hold, at any AR state. *)
Lemma mw_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 93) = Z_to_bv 64 (VAL (A_OBJ 93)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  region_ok segs E (mrestrict (w_H W) mem) got_regionP /\ region_ok segs E (mrestrict (w_H W) mem) (bcell_regionP 32).
Proof.
  intros ly S W mem md E HCELLS HAR E1 E93 E32.
  destruct (HCELLS ly) as (I1 & I2 & _).
  destruct mw_vals as (V1 & V93 & _).
  assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview segs (w_H W) mem) c).
  { intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
  assert (Kcell : rdword (aview segs (w_H W) mem) FCells.CELL_K = Some FCells.ASAN_K)
    by (apply (rdword_cell B ly); [unfold FCells.ASAN_K; lia | exact (CH _ I1)]).
  assert (Kgot : rdword (aview segs (w_H W) mem) FCells.GOT_CELL_K = Some FCells.CELL_K)
    by (apply (rdword_cell B ly); [unfold FCells.CELL_K; lia | exact (CH _ I2)]).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (R1 : 0 <= VAL (A_OBJ 1) < 2 ^ 47) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
  assert (R93 : 0 <= VAL (A_OBJ 93) < 2 ^ 47) by (rewrite V93; unfold FCells.CELL_K; lia).
  unfold got_regionP, bcell_regionP, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split.
  - rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 93) 0) (VAL (A_OBJ 93)));
    [cbn [sv_denot]; rewrite E93, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r, V1, V93. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
  - rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) E93) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (VAL (A_OBJ 93)) 0 8 (SOff 32 0) SHADOW_OFF);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
    rewrite Z.add_0_r, V93. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
Qed.

(* OW's 304 payload bytes are addressable at every AR state: its 38 granules are whole and their shadow is 0. *)
Lemma mw_ra : forall ly S (W : world segs) mem md,
  trans_ow_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF TA_OW 304.
Proof.
intros ly S W mem md HZ HAR x Hx.
assert (EC : TA_OW = 6238304) by reflexivity.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
unfold shadow_of_addr.
exists 0. split; [|left; reflexivity].
assert (Hz := decode_zshadow_rd B ly S W mem md TA_OW (TA_OW + 304) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(lia) ltac:(lia) HZ).
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The run's shadow entry holds at every AR state. *)
Lemma mw_shok : forall ly S (W : world segs) mem md (E : env),
  trans_ow_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 12) = Z_to_bv 64 TA_OW -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  sh_ok segs MW_Bx MW_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E HZ HAR E12 E32.
unfold sh_ok, MW_SH. constructor; [|constructor].
apply (shent_ok_of_range segs (w_H W) mem E MW_Bx (A_OBJ 12) TA_OW 304 TA_OW 0 304 (mw_ra ly S W mem md HZ HAR)).
- unfold U, MW_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned.
  apply unsigned_lit_small. unfold TA_OW. lia.
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, TA_OW in *. lia.
Qed.

(* The walk's valuation: the 32 registers at the entry, the shadow base and the nine world values it reads. *)
Definition mw_ex (Bw : list byte) : list word :=
  [w64 SHADOW_OFF; w64 (TW.u_at Bw 0 4); w64 (TW.u_at Bw 24 4); w64 (TW.u_at Bw 12 4); w64 (TW.u_at Bw 88 4);
   w64 (TW.u_at Bw 65508 4); w64 (TW.u_at Bw 65312 4); w64 (TW.u_at Bw 65000 8); w64 (TW.u_at Bw 16 8);
   w64 (TW.u_at Bw 40 8)].
Definition mw_E (regs : bvmap 5 word) (Bw : list byte) : env := Eimg (PI := PI_transport) (Ereg regs (mw_ex Bw)).

(* One entry chunk: the n bytes of a payload span, as the atom that holds their value. *)
Lemma mw_chunk_entry : forall (W : world segs) memc Bw (E : env) o b n k (w : N) (atom : nat),
  tw_at TMAP_A (aview segs (w_H W) memc) Bw -> In (o, b, n) TMAP_A -> 0 <= k -> k + Z.of_N w <= n ->
  Z.of_N w <= 8 -> ew E atom = w64 (TW.u_at Bw (o + k) (N.to_nat w)) ->
  YP09.chunk_ok segs E (mrestrict (w_H W) memc) b (YP09.mkChunk k (CVal w (SOff atom 0))).
Proof.
intros W memc Bw E o b n k w atom Htw Hin Hk Hkw Hw8 Hew.
pose proof (TWL.u_at_range Bw (o + k) (N.to_nat w)) as HR. rewrite N_nat_Z in HR.
assert (HP : 2 ^ (8 * Z.of_N w) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
apply (chunk_ok_val segs E (mrestrict (w_H W) memc) b k w (SOff atom 0) (TW.u_at Bw (o + k) (N.to_nat w))).
- cbn [sv_denot]. rewrite Hew, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- exact HR.
- exact Hw8.
- apply (tw_read_val segs (mrestrict (w_H W) memc) TMAP_A Bw o b n k (N.to_nat w) TMAP_A_ok Htw Hin Hk).
  rewrite N_nat_Z. exact Hkw.
Qed.

(* A whole region of a payload span: writable because its bytes are bytes of G, with one chunk. *)
Lemma mw_reg : forall (W : world segs) memc Bw (E : env) (nb : nat) (bb : Z) o n lo hi wlo whi k (w : N) atom,
  tw_at TMAP_A (aview segs (w_H W) memc) Bw -> In (o, bb, n) TMAP_A ->
  bv_unsigned (ew E nb) = bb -> 0 <= bb + lo -> bb + hi <= 2 ^ 64 ->
  (forall a, bb + wlo <= a < bb + whi -> inG TG.G_HARNESS a) ->
  0 <= k -> k + Z.of_N w <= n -> Z.of_N w <= 8 -> ew E atom = w64 (TW.u_at Bw (o + k) (N.to_nat w)) ->
  region_ok segs E (mrestrict (w_H W) memc)
    (YP09.mkRegion (Some nb) lo hi wlo whi [YP09.mkChunk k (CVal w (SOff atom 0))]).
Proof.
intros W memc Bw E nb bb o n lo hi wlo whi k w atom Htw Hin Hbb Hlo Hhi HG Hk Hkw Hw8 Hew.
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hbb. split; [exact Hlo|]. split; [exact Hhi|].
split; [intros o0 Ho0; apply (gx_rw_writable segs TG.G_HARNESS (bb + o0) G_HARNESS_rw); apply HG; lia|].
constructor; [|constructor].
exact (mw_chunk_entry W memc Bw E o bb n k w atom Htw Hin Hk Hkw Hw8 Hew).
Qed.

(* The value a chunk of the final state gives for each of its bytes. *)
Lemma mw_cval : forall (E : env) (W : world segs) (m : word -> option byte) (r : YP09.region) (nb : nat)
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
rewrite Hden. rewrite (mw_bow X w (Z.of_nat j)) by lia. rewrite Nat2Z.id. reflexivity.
Qed.

(* ---- the value of a sign-extended 4-byte world atom, and of its increment ---- *)

Lemma mw_sext_atom : forall (E : env) atom Bw o, ew E atom = w64 (TW.u_at Bw o 4) ->
  sv_denot E (SExt true 32 (SOff atom 0)) = Z_to_bv 64 (TW.s32_at Bw o).
Proof.
intros E atom Bw o Hew. pose proof (TWL.u_at_range Bw o 4) as HR. cbn [Z.of_nat] in HR.
cbn [sv_denot]. rewrite Hew, Z.add_0_r. unfold w64.
rewrite unsigned_lit_small by lia.
change (Z_to_bv 64 (TW.u_at Bw o 4)) with (le_bytes_to_word (TW.sub Bw o 4)).
apply lw_world.
Qed.

Lemma mw_mod64 : forall x m, 0 <= m <= 64 -> (x mod 2 ^ 64) mod 2 ^ m = x mod 2 ^ m.
Proof.
intros x m Hm. symmetry.
apply Znumtheory.Zmod_div_mod; [apply Z.pow_pos_nonneg; lia | apply Z.pow_pos_nonneg; lia|].
exists (2 ^ (64 - m)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma mw_add1_mod32 : forall a, (a mod 2 ^ 64 + 1) mod 2 ^ 32 = (a + 1) mod 2 ^ 32.
Proof.
intros a. rewrite <- (Zplus_mod_idemp_l (a mod 2 ^ 64) 1 (2 ^ 32)).
rewrite (mw_mod64 a 32 ltac:(lia)). rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* ---- the world at the return: one span at a time ---- *)

Definition mw_inrs (l : list (Z * Z)) (x : Z) : bool :=
  existsb (fun p => ((fst p <=? x) && (x <? snd p))%bool) l.
Definition mw_rd (l : list (Z * Z)) (rd rd' : Z -> option Z) : Z -> option Z :=
  fun x => if mw_inrs l x then rd' x else rd x.

Lemma mw_rd_nil : forall rd rd', mw_rd [] rd rd' = rd.
Proof. intros. reflexivity. Qed.

Lemma mw_inrs_true : forall l lo hi x, In (lo, hi) l -> lo <= x < hi -> mw_inrs l x = true.
Proof.
intros l lo hi x Hin Hx. unfold mw_inrs. apply existsb_exists. exists (lo, hi).
split; [exact Hin|]. cbn [fst snd]. apply andb_true_intro.
split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma mw_step : forall l (rd rd' : Z -> option Z) Bw o b n k (m : nat) v,
  tw_at TMAP_A (mw_rd l rd rd') Bw -> In (o, b, n) TMAP_A -> 0 <= k -> k + Z.of_nat m <= n ->
  (forall j, (j < m)%nat -> rd' (b + k + Z.of_nat j) = Some (YO0f.le_byte v m j)) ->
  tw_at TMAP_A (mw_rd ((b + k, b + k + Z.of_nat m) :: l) rd rd') (TW.upd Bw (o + k) (TW.put m v)).
Proof.
intros l rd rd' Bw o b n k m v Hat Hin Hk Hkm Hnew.
apply (tw_write TMAP_A (mw_rd l rd rd') (mw_rd ((b + k, b + k + Z.of_nat m) :: l) rd rd') Bw o b n k m v
  TMAP_A_ok Hat Hin Hk Hkm).
- intros j Hj. unfold mw_rd, mw_inrs. cbn [existsb fst snd].
  replace ((b + k <=? b + k + Z.of_nat j) && (b + k + Z.of_nat j <? b + k + Z.of_nat m))%bool with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  cbn [orb]. exact (Hnew j Hj).
- intros x Hx Hn. unfold mw_rd, mw_inrs. cbn [existsb fst snd].
  replace ((b + k <=? x) && (x <? b + k + Z.of_nat m))%bool with false.
  + cbn [orb]. reflexivity.
  + symmetry. apply andb_false_iff.
    destruct (Z_lt_le_dec x (b + k)) as [H1 | H1]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
Qed.

Lemma mw_fin_rd : forall l (rd rd' : Z -> option Z) Bw,
  tw_at TMAP_A (mw_rd l rd rd') Bw ->
  (forall x, tw_in TMAP_A x -> mw_inrs l x = false -> rd' x = rd x) ->
  tw_at TMAP_A rd' Bw.
Proof.
intros l rd rd' Bw Hat Hk. apply (tw_kept TMAP_A (mw_rd l rd rd') rd' Bw Hat).
intros x Hx. unfold mw_rd. destruct (mw_inrs l x) eqn:Hi; [reflexivity | exact (Hk x Hx Hi)].
Qed.

(* A span whose final bytes are the entry's: the chunk still holds the entry atom. *)
Lemma mw_same_range : forall (rd rd' : Z -> option Z) Bw o b n k (m : nat) X,
  tw_at TMAP_A rd Bw -> In (o, b, n) TMAP_A -> 0 <= k -> k + Z.of_nat m <= n ->
  (forall j, (j < m)%nat -> rd' (b + k + Z.of_nat j) = Some (YO0f.le_byte X m j)) ->
  X mod 2 ^ (8 * Z.of_nat m) = TW.u_at Bw (o + k) m mod 2 ^ (8 * Z.of_nat m) ->
  forall x, b + k <= x < b + k + Z.of_nat m -> rd' x = rd x.
Proof.
intros rd rd' Bw o b n k m X Hat Hin Hk Hkm Hnew Hmod x Hx.
replace x with (b + k + Z.of_nat (Z.to_nat (x - (b + k)))) by lia.
rewrite (Hnew (Z.to_nat (x - (b + k))) ltac:(lia)).
rewrite (tw_read TMAP_A rd Bw o b n k m (Z.to_nat (x - (b + k))) TMAP_A_ok Hat Hin Hk Hkm ltac:(lia)).
f_equal. apply mw_le_byte_mod. exact Hmod.
Qed.

(* ---- the entry state ---- *)

Lemma mw_entry : forall ly S (W : world segs) regs memc md Bw,
  transport_cells B -> trans_ow_cells B -> @AR rc segs B ly S W memc md ->
  tw_at TMAP_A (aview segs (w_H W) memc) Bw ->
  (forall a, spZ regs - MWAKE_FRAME <= a < spZ regs -> apresent (w_H W) memc a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (mw_E regs Bw) ss_mw
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_m_wake)) memc (YK11.seg_rom segs)))
  /\ sh_ok segs MW_Bx MW_SH (mw_E regs Bw) (mrestrict (w_H W) memc).
Proof.
intros ly S W regs memc md Bw HCELLS HOW HAR Htw Hpres Hsp Hsp16.
destruct mw_vals as (V1 & V93 & V8 & V12 & V27 & _).
pose proof (TWL.u_at_range Bw 0 4) as R33. pose proof (TWL.u_at_range Bw 24 4) as R34.
pose proof (TWL.u_at_range Bw 12 4) as R35. pose proof (TWL.u_at_range Bw 88 4) as R36.
pose proof (TWL.u_at_range Bw 65508 4) as R37. pose proof (TWL.u_at_range Bw 65312 4) as R38.
pose proof (TWL.u_at_range Bw 65000 8) as R39. pose proof (TWL.u_at_range Bw 16 8) as R40.
pose proof (TWL.u_at_range Bw 40 8) as R41.
cbn [Z.of_nat Z.mul Z.pow] in R33, R34, R35, R36, R37, R38, R39, R40, R41.
assert (EOB : forall j, (j < 95)%nat -> ew (mw_E regs Bw) (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
  by (intros j Hj; unfold mw_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EXT : forall i, (i < 10)%nat -> ew (mw_E regs Bw) (32 + i) = nth i (mw_ex Bw) (Z_to_bv 64 0))
  by (intros i Hi; unfold mw_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E32 : ew (mw_E regs Bw) 32 = Z_to_bv 64 SHADOW_OFF) by exact (EXT 0%nat ltac:(lia)).
assert (A33 : ew (mw_E regs Bw) 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4))) by exact (EXT 1%nat ltac:(lia)).
assert (A34 : ew (mw_E regs Bw) 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4))) by exact (EXT 2%nat ltac:(lia)).
assert (A35 : ew (mw_E regs Bw) 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4))) by exact (EXT 3%nat ltac:(lia)).
assert (A36 : ew (mw_E regs Bw) 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4))) by exact (EXT 4%nat ltac:(lia)).
assert (A37 : ew (mw_E regs Bw) 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
  by exact (EXT 5%nat ltac:(lia)).
assert (A38 : ew (mw_E regs Bw) 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
  by exact (EXT 6%nat ltac:(lia)).
assert (A39 : ew (mw_E regs Bw) 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
  by exact (EXT 7%nat ltac:(lia)).
assert (A40 : ew (mw_E regs Bw) 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8))) by exact (EXT 8%nat ltac:(lia)).
assert (A41 : ew (mw_E regs Bw) 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8))) by exact (EXT 9%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew (mw_E regs Bw) 2) = spZ regs)
  by (unfold mw_E; rewrite (ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (U8 : bv_unsigned (ew (mw_E regs Bw) (A_OBJ 8)) = TA_M)
  by (rewrite (EOB 8%nat ltac:(lia)), V8; apply unsigned_lit_small; unfold TA_M; lia).
assert (U12 : bv_unsigned (ew (mw_E regs Bw) (A_OBJ 12)) = TA_OW)
  by (rewrite (EOB 12%nat ltac:(lia)), V12; apply unsigned_lit_small; unfold TA_OW; lia).
assert (U27 : bv_unsigned (ew (mw_E regs Bw) (A_OBJ 27)) = TA_g_now)
  by (rewrite (EOB 27%nat ltac:(lia)), V27; apply unsigned_lit_small; unfold TA_g_now; lia).
assert (E12 : ew (mw_E regs Bw) (A_OBJ 12) = Z_to_bv 64 TA_OW)
  by (rewrite (EOB 12%nat ltac:(lia)), V12; reflexivity).
assert (U32 : bv_unsigned (ew (mw_E regs Bw) 32) = SHADOW_OFF)
  by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew (mw_E regs Bw) 33) = TW.u_at Bw 0 4)
  by (rewrite A33; unfold w64, TW.OFF_M; apply unsigned_lit_small; cbn [Z.add N.to_nat]; lia).
assert (U34 : bv_unsigned (ew (mw_E regs Bw) 34) = TW.u_at Bw 24 4)
  by (rewrite A34; unfold w64, TW.OFF_M; apply unsigned_lit_small; cbn [Z.add N.to_nat]; lia).
assert (U35 : bv_unsigned (ew (mw_E regs Bw) 35) = TW.u_at Bw 12 4)
  by (rewrite A35; unfold w64, TW.OFF_M; apply unsigned_lit_small; cbn [Z.add N.to_nat]; lia).
assert (U36 : bv_unsigned (ew (mw_E regs Bw) 36) = TW.u_at Bw 88 4)
  by (rewrite A36; unfold w64, TW.OFF_M; apply unsigned_lit_small; cbn [Z.add N.to_nat]; lia).
assert (U37 : bv_unsigned (ew (mw_E regs Bw) 37) = TW.u_at Bw 65508 4)
  by (rewrite A37; unfold w64, TW.OFF_OW; apply unsigned_lit_small; cbn [Z.add N.to_nat]; lia).
assert (U38 : bv_unsigned (ew (mw_E regs Bw) 38) = TW.u_at Bw 65312 4)
  by (rewrite A38; unfold w64, TW.OFF_OW; apply unsigned_lit_small; cbn [Z.add N.to_nat]; lia).
assert (U39 : bv_unsigned (ew (mw_E regs Bw) 39) = TW.u_at Bw 65000 8)
  by (rewrite A39; unfold w64, TW.OFF_g_now; apply unsigned_lit_small; cbn [Z.add N.to_nat]; lia).
assert (U40 : bv_unsigned (ew (mw_E regs Bw) 40) = TW.u_at Bw 16 8)
  by (rewrite A40; unfold w64, TW.OFF_M; apply unsigned_lit_small; cbn [Z.add N.to_nat]; lia).
assert (U41 : bv_unsigned (ew (mw_E regs Bw) 41) = TW.u_at Bw 40 8)
  by (rewrite A41; unfold w64, TW.OFF_M; apply unsigned_lit_small; cbn [Z.add N.to_nat]; lia).
destruct (mw_img_ok ly S W memc md (mw_E regs Bw) HCELLS HAR (EOB 1%nat ltac:(lia)) (EOB 93%nat ltac:(lia)) E32)
  as [RG RC].
assert (VB : forall n v0, ew (mw_E regs Bw) n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 ->
  base_val (mw_E regs Bw) (Some n) = v0)
  by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
split.
2:{ exact (mw_shok ly S W memc md (mw_E regs Bw) HOW HAR E12 E32). }
rewrite restrict_mkst_fx. unfold ss_mw, mw_regions.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons;
  [ unfold stack_region, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite Usp; unfold MWAKE_FRAME in *;
    split; [lia|]; split; [lia|]; split; [|constructor];
    intros o Ho; apply (apresent_writable segs); apply Hpres; lia |].
  apply Forall_cons; [exact RG|]. apply Forall_cons; [exact RC|].
  apply Forall_cons;
  [ exact (mw_reg W memc Bw _ (A_OBJ 8) TA_M TW.OFF_M TW.SZ_M 0 4 0 0 0 4 33 Htw TMAP_A_M U8
            ltac:(unfold TA_M; lia) ltac:(unfold TA_M; lia) ltac:(intros a Ha; lia)
            ltac:(lia) ltac:(unfold TW.SZ_M; lia) ltac:(lia) A33) |].
  apply Forall_cons;
  [ exact (mw_reg W memc Bw _ (A_OBJ 8) TA_M TW.OFF_M TW.SZ_M 12 16 12 16 12 4 35 Htw TMAP_A_M U8
            ltac:(unfold TA_M; lia) ltac:(unfold TA_M; lia)
            ltac:(intros a Ha; apply mw_inG_M; unfold TA_M, TW.SZ_M in *; lia)
            ltac:(lia) ltac:(unfold TW.SZ_M; lia) ltac:(lia) A35) |].
  apply Forall_cons;
  [ exact (mw_reg W memc Bw _ (A_OBJ 8) TA_M TW.OFF_M TW.SZ_M 16 24 16 24 16 8 40 Htw TMAP_A_M U8
            ltac:(unfold TA_M; lia) ltac:(unfold TA_M; lia)
            ltac:(intros a Ha; apply mw_inG_M; unfold TA_M, TW.SZ_M in *; lia)
            ltac:(lia) ltac:(unfold TW.SZ_M; lia) ltac:(lia) A40) |].
  apply Forall_cons;
  [ exact (mw_reg W memc Bw _ (A_OBJ 8) TA_M TW.OFF_M TW.SZ_M 24 28 24 24 24 4 34 Htw TMAP_A_M U8
            ltac:(unfold TA_M; lia) ltac:(unfold TA_M; lia) ltac:(intros a Ha; lia)
            ltac:(lia) ltac:(unfold TW.SZ_M; lia) ltac:(lia) A34) |].
  apply Forall_cons;
  [ exact (mw_reg W memc Bw _ (A_OBJ 8) TA_M TW.OFF_M TW.SZ_M 40 48 40 48 40 8 41 Htw TMAP_A_M U8
            ltac:(unfold TA_M; lia) ltac:(unfold TA_M; lia)
            ltac:(intros a Ha; apply mw_inG_M; unfold TA_M, TW.SZ_M in *; lia)
            ltac:(lia) ltac:(unfold TW.SZ_M; lia) ltac:(lia) A41) |].
  apply Forall_cons;
  [ exact (mw_reg W memc Bw _ (A_OBJ 8) TA_M TW.OFF_M TW.SZ_M 88 92 88 92 88 4 36 Htw TMAP_A_M U8
            ltac:(unfold TA_M; lia) ltac:(unfold TA_M; lia)
            ltac:(intros a Ha; apply mw_inG_M; unfold TA_M, TW.SZ_M in *; lia)
            ltac:(lia) ltac:(unfold TW.SZ_M; lia) ltac:(lia) A36) |].
  apply Forall_cons;
  [ exact (mw_reg W memc Bw _ (A_OBJ 12) TA_OW TW.OFF_OW TW.SZ_OW 0 4 0 4 0 4 38 Htw TMAP_A_OW U12
            ltac:(unfold TA_OW; lia) ltac:(unfold TA_OW; lia)
            ltac:(intros a Ha; apply mw_inG_OW; unfold TA_OW, TW.SZ_OW in *; lia)
            ltac:(lia) ltac:(unfold TW.SZ_OW; lia) ltac:(lia) A38) |].
  apply Forall_cons;
  [ exact (mw_reg W memc Bw _ (A_OBJ 12) TA_OW TW.OFF_OW TW.SZ_OW 196 200 196 200 196 4 37 Htw TMAP_A_OW U12
            ltac:(unfold TA_OW; lia) ltac:(unfold TA_OW; lia)
            ltac:(intros a Ha; apply mw_inG_OW; unfold TA_OW, TW.SZ_OW in *; lia)
            ltac:(lia) ltac:(unfold TW.SZ_OW; lia) ltac:(lia) A37) |].
  apply Forall_cons; [|apply Forall_nil].
  exact (mw_reg W memc Bw _ (A_OBJ 27) TA_g_now TW.OFF_g_now TW.SZ_g_now 0 8 0 0 0 8 39 Htw TMAP_A_g_now U27
          ltac:(unfold TA_g_now; lia) ltac:(unfold TA_g_now; lia) ltac:(intros a Ha; lia)
          ltac:(lia) ltac:(unfold TW.SZ_g_now; lia) ltac:(lia) A39).
- apply pairwise_disjoint_of_extents.
  unfold stack_region, got_regionP, bcell_regionP, Rm_dk, Rm_st, Rm_ea, Rm_fo, Rm_ws, Rm_fa, Ro_n, Ro_e2,
    Rg_now, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (EOB 1%nat ltac:(lia))) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
  rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) (EOB 93%nat ltac:(lia))) by (rewrite V93; unfold FCells.CELL_K; lia).
  cbn [base_val]. rewrite Usp, U8, U12, U27.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite V1, V93. unfold FCells.GOT_CELL_K, FCells.CELL_K, TA_M, TA_OW, TA_g_now, MWAKE_FRAME in *.
  repeat split; first [exact I | lia].
- unfold mw_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, U32, U8, U12, U33, U34, U35, U36, U37, U38, U39, U40, U41.
  change (2 ^ 4) with 16. change (2 ^ 5) with 32.
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold TA_M, TA_OW, SHADOW_OFF in *.
  repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | reflexivity].
Qed.

Lemma mw_agree : forall regs Bw E, (forall n, (n < 32)%nat -> ew E n = ew (mw_E regs Bw) n) ->
  ed E = ed (mw_E regs Bw) -> env_agree 32 (Ereg regs (mw_ex Bw)) E.
Proof.
  intros regs Bw E H1 H2. split.
  - intros n Hn. rewrite (H1 n Hn). unfold mw_E. apply Eimg_low. unfold A_TEXT. lia.
  - rewrite H2. reflexivity.
Qed.

(* ---- the post at the return ---- *)

Lemma mw_close : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs Bw Bw' r
    regsF mF mdF,
  AR_laws segs B -> ameter_laws MT -> gx_ok segs B TG.G_HARNESS ->
  @AR rc segs B lyc Sc W memc mdc ->
  (forall a, spZ regs - MWAKE_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  alloc_ceiling <= spZ regs - MWAKE_STK -> spZ regs <= 2 ^ 47 ->
  YK0s.ret_ok (YK11.getr regs 1) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own
    lyc Sc W mF mdF k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ mw_Zs (spZ regs) a -> aview segs (w_H W) mF a = aview segs (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mF a) ->
  tw_at TMAP_A (aview segs (w_H W) mF) Bw' ->
  aregs_preserved regs regsF -> YK11.getr regsF 1 = YK11.getr regs 1 -> YK11.getr regsF 10 = w64 r ->
  forall mat, @transport_mwake_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r W
    (mkCfg (@YK11.mkst fx regsF (v_jalr (YK11.getr regsF 1) 0) mF (YK11.seg_rom segs))
      (with_vm_backing (m_vm_lazy mdF) mat mdF)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw' r regsF mF mdF
  LAWS MTL HGX HAR Hwin Hce Hsp47 Hra HJF KA GA HTW HPR RF1 RF10 mat.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : MWAKE_STK = 16) by reflexivity.
assert (GLOW : forall a, inG TG.G_HARNESS a -> 0 <= a < kLowMemEnd)
  by (intros a Ha; exact (transport_segs_low a (proj1 (HGX a Ha)))).
unfold transport_mwake_post, transport_cg_post.
exists lyc, Sc, regsF, mF, (with_vm_backing (m_vm_lazy mdF) mat mdF), 0.
split. { rewrite RF1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split; [unfold MWAKE_EV; lia|].
split; [rewrite Z.add_0_r; apply (ajournal_gx_materialize segs B LAWS transport_segs_low); exact HJF|].
split; [exact HPR|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split.
{ apply (dk_kept_step_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc memc mF
    (spZ regs - MWAKE_STK) (spZ regs) (mwake_wr Bw) (mw_Zs (spZ regs)) HAR).
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
    + pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl. lia.
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

(* ---- the branches: every scalar the function tests is a C int ---- *)

Lemma mw_u64 : forall v, bv_unsigned (Z_to_bv 64 v) = v mod 2 ^ 64.
Proof.
intros v. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). reflexivity.
Qed.

Lemma mw_s32_mod_inj : forall v w, - 2 ^ 31 <= v < 2 ^ 31 -> - 2 ^ 31 <= w < 2 ^ 31 ->
  v mod 2 ^ 64 = w mod 2 ^ 64 -> v = w.
Proof. intros v w Hv Hw H. Z.div_mod_to_equations. lia. Qed.

Lemma mw_eqb_s32 : forall v w, - 2 ^ 31 <= v < 2 ^ 31 -> - 2 ^ 31 <= w < 2 ^ 31 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 w) = (v =? w).
Proof.
  intros v w Hv Hw. unfold bv_eqb. rewrite !mw_u64.
  destruct (Z.eqb_spec v w) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intro E. apply N. exact (mw_s32_mod_inj v w Hv Hw E).
Qed.

Lemma mw_signed_s32 : forall v, - 2 ^ 31 <= v < 2 ^ 31 -> bv_signed (Z_to_bv 64 v) = v.
Proof.
  intros v Hv. rewrite signed_is_swrap_unsigned, mw_u64.
  unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
  rewrite Zplus_mod_idemp_l. rewrite (Z.mod_small (v + 2 ^ 63) (2 ^ 64)) by lia. lia.
Qed.

Lemma mw_lts_s32 : forall v w, - 2 ^ 31 <= v < 2 ^ 31 -> - 2 ^ 31 <= w < 2 ^ 31 ->
  bv_lts (Z_to_bv 64 v) (Z_to_bv 64 w) = (v <? w).
Proof. intros v w Hv Hw. unfold bv_lts. rewrite !mw_signed_s32 by lia. reflexivity. Qed.

(* the increment of a sign-extended 4-byte value, modulo the stored width *)
Lemma mw_u_add1 : forall (E : env) (a : sv) z, sv_denot E a = Z_to_bv 64 z ->
  U E (SAlu ALU_ADD a (SLit 1)) mod 2 ^ 32 = (z + 1) mod 2 ^ 32.
Proof.
intros E a z Hd. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_lit E 1 ltac:(lia)).
assert (HA : U E a = z mod 2 ^ 64) by (unfold U; rewrite Hd; apply mw_u64).
rewrite HA. unfold zcanon, M64.
rewrite (mw_mod64 (z mod 2 ^ 64 + 1) 32 ltac:(lia)). apply mw_add1_mod32.
Qed.

(* The bytes a window of the final state holds, as the denotation of its chunk. *)
Lemma mw_win_val : forall (E : env) (W : world segs) (m : word -> option byte) r (nb : nat) (bb co : Z)
    (w : N) (v : sv),
  region_ok segs E (mrestrict (w_H W) m) r -> YP09.r_base r = Some nb -> bv_unsigned (ew E nb) = bb ->
  In (YP09.mkChunk co (CVal w v)) (YP09.r_chunks r) -> Z.of_N w <= 8 ->
  forall j, (j < N.to_nat w)%nat ->
    aview segs (w_H W) m (bb + co + Z.of_nat j) = Some (YO0f.le_byte (U E v) (N.to_nat w) j).
Proof.
intros E W m r nb bb co w v Hr Hb Hbb Hin Hw j Hj.
exact (mw_cval E W m r nb bb co w v (U E v) Hr Hb Hbb Hin (denot_lit_U E v) (proj1 (U_range E v)) Hw j Hj).
Qed.

(* The windows of the walk: its stack frame and the six spans of M and OW it may store into. *)
Definition mw_wins (sp : Z) (a : Z) : Prop :=
  (sp - MWAKE_STK <= a < sp) \/ (TA_M + 12 <= a < TA_M + 16) \/ (TA_M + 16 <= a < TA_M + 24) \/
  (TA_M + 40 <= a < TA_M + 48) \/ (TA_M + 88 <= a < TA_M + 92) \/
  (TA_OW + 0 <= a < TA_OW + 4) \/ (TA_OW + 196 <= a < TA_OW + 200).

Lemma mw_wins_Zs : forall sp a, mw_wins sp a -> mw_Zs sp a.
Proof.
intros sp a [H | [H | [H | [H | [H | [H | H]]]]]]; unfold mw_Zs;
  first [ left; exact H
        | right; apply mw_inG_M; unfold TA_M, TW.SZ_M in *; lia
        | right; apply mw_inG_OW; unfold TA_OW, TW.SZ_OW in *; lia ].
Qed.

(* A window whose chunk is still the entry atom: its bytes are the entry's. *)
Lemma mw_keep_win : forall (E : env) (W : world segs) (m : word -> option byte) (rd : Z -> option Z)
    r (nb : nat) (bb co : Z) (w : N) (atom : nat) Bw o n,
  region_ok segs E (mrestrict (w_H W) m) r -> YP09.r_base r = Some nb -> bv_unsigned (ew E nb) = bb ->
  In (YP09.mkChunk co (CVal w (SOff atom 0))) (YP09.r_chunks r) -> Z.of_N w <= 8 ->
  ew E atom = w64 (TW.u_at Bw (o + co) (N.to_nat w)) ->
  tw_at TMAP_A rd Bw -> In (o, bb, n) TMAP_A -> 0 <= co -> co + Z.of_N w <= n ->
  forall x, bb + co <= x < bb + co + Z.of_N w -> aview segs (w_H W) m x = rd x.
Proof.
intros E W m rd r nb bb co w atom Bw o n Hr Hb Hbb Hin Hw Hew Htw Hrow Hco Hcow x Hx.
pose proof (TWL.u_at_range Bw (o + co) (N.to_nat w)) as HR. rewrite N_nat_Z in HR.
assert (HP : 2 ^ (8 * Z.of_N w) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
assert (HU : U E (SOff atom 0) = TW.u_at Bw (o + co) (N.to_nat w))
  by (apply (U_atom E atom); [exact Hew | lia]).
apply (mw_same_range rd (aview segs (w_H W) m) Bw o bb n co (N.to_nat w)
  (TW.u_at Bw (o + co) (N.to_nat w)) Htw Hrow Hco ltac:(rewrite N_nat_Z; exact Hcow)).
- intros j Hj. rewrite (mw_win_val E W m r nb bb co w (SOff atom 0) Hr Hb Hbb Hin Hw j Hj), HU. reflexivity.
- reflexivity.
- rewrite N_nat_Z. exact Hx.
Qed.

(* ---- the walk's tactics ---- *)

Ltac mw_awr Usp U8 U12 U27 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      rewrite ?Usp, ?U8, ?U12, ?U27 in Ha;
      first [ lia
            | left; split; [unfold awr_byte; left; lia | lia]
            | right; left; apply mw_inG_M; unfold TW.SZ_M; lia
            | right; left; apply mw_inG_OW; unfold TW.SZ_OW; lia ]
    | ]);
  apply awr_ok_x_nil.

Ltac mw_wtac Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

Ltac mw_regv HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "mw_regv: no match for" T; fail
  end.

(* the value a leaf returns in a0 *)
Ltac mw_ret_val HS R H := mw_regv HS (Z_to_bv 5 10) (w64 R) H
  ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mw_u64; reflexivity).

(* ---- the world at each leaf ---- *)

Lemma mw_notin : forall lo hi x l, mw_inrs ((lo, hi) :: l) x = false -> ~ (lo <= x < hi) /\ mw_inrs l x = false.
Proof.
intros lo hi x l H. unfold mw_inrs in H. cbn [existsb fst snd] in H.
apply orb_false_iff in H as [H1 H2]. split; [|exact H2].
apply andb_false_iff in H1 as [H1 | H1]; [apply Z.leb_gt in H1 | apply Z.ltb_ge in H1]; lia.
Qed.

(* the four stores every path past the foreign test makes *)
Lemma mw_world4 : forall (W : world segs) memc mF Bw,
  tw_at TMAP_A (aview segs (w_H W) memc) Bw ->
  (forall j, (j < 4)%nat -> aview segs (w_H W) mF (TA_OW + 196 + Z.of_nat j)
     = Some (YO0f.le_byte (TW.s32_at Bw 65508 + 1) 4 j)) ->
  (forall j, (j < 8)%nat -> aview segs (w_H W) mF (TA_M + 16 + Z.of_nat j) = Some (YO0f.le_byte 0 8 j)) ->
  (forall j, (j < 8)%nat -> aview segs (w_H W) mF (TA_M + 40 + Z.of_nat j)
     = Some (YO0f.le_byte (TW.u_at Bw 65000 8) 8 j)) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W) mF (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  tw_at TMAP_A (mw_rd ((TA_M + 88, TA_M + 88 + Z.of_nat 4)
                       :: (TA_M + 40, TA_M + 40 + Z.of_nat 8)
                       :: (TA_M + 16, TA_M + 16 + Z.of_nat 8)
                       :: (TA_OW + 196, TA_OW + 196 + Z.of_nat 4) :: [])
                 (aview segs (w_H W) memc) (aview segs (w_H W) mF)) (mwm_W Bw).
Proof.
intros W memc mF Bw Htw H196 H16 H40 H88. unfold mwm_W.
pose proof (mw_step [] (aview segs (w_H W) memc) (aview segs (w_H W) mF) Bw
  TW.OFF_OW TA_OW TW.SZ_OW 196 4 (TW.s32_at Bw 65508 + 1) Htw TMAP_A_OW
  ltac:(lia) ltac:(unfold TW.SZ_OW; lia) H196) as T1.
pose proof (mw_step _ (aview segs (w_H W) memc) (aview segs (w_H W) mF) _
  TW.OFF_M TA_M TW.SZ_M 16 8 0 T1 TMAP_A_M
  ltac:(lia) ltac:(unfold TW.SZ_M; lia) H16) as T2.
pose proof (mw_step _ (aview segs (w_H W) memc) (aview segs (w_H W) mF) _
  TW.OFF_M TA_M TW.SZ_M 40 8 (TW.u_at Bw 65000 8) T2 TMAP_A_M
  ltac:(lia) ltac:(unfold TW.SZ_M; lia) H40) as T3.
pose proof (mw_step _ (aview segs (w_H W) memc) (aview segs (w_H W) mF) _
  TW.OFF_M TA_M TW.SZ_M 88 4 0 T3 TMAP_A_M
  ltac:(lia) ltac:(unfold TW.SZ_M; lia) H88) as T4.
exact T4.
Qed.

(* m_set's two stores when no transition record is written *)
Lemma mw_world6 : forall (W : world segs) memc mF Bw L nv,
  tw_at TMAP_A (mw_rd L (aview segs (w_H W) memc) (aview segs (w_H W) mF)) (mwm_W Bw) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W) mF (TA_OW + 0 + Z.of_nat j)
     = Some (YO0f.le_byte nv 4 j)) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W) mF (TA_M + 12 + Z.of_nat j) = Some (YO0f.le_byte 1 4 j)) ->
  tw_at TMAP_A (mw_rd ((TA_M + 12, TA_M + 12 + Z.of_nat 4) :: (TA_OW + 0, TA_OW + 0 + Z.of_nat 4) :: L)
                 (aview segs (w_H W) memc) (aview segs (w_H W) mF))
    (TW.upd (TW.upd (mwm_W Bw) 65312 (TW.put 4 nv)) 12 (TW.put 4 1)).
Proof.
intros W memc mF Bw L nv T4 H0 H12.
pose proof (mw_step L (aview segs (w_H W) memc) (aview segs (w_H W) mF) (mwm_W Bw)
  TW.OFF_OW TA_OW TW.SZ_OW 0 4 nv T4 TMAP_A_OW
  ltac:(lia) ltac:(unfold TW.SZ_OW; lia) H0) as T5.
pose proof (mw_step _ (aview segs (w_H W) memc) (aview segs (w_H W) mF) _
  TW.OFF_M TA_M TW.SZ_M 12 4 1 T5 TMAP_A_M
  ltac:(lia) ltac:(unfold TW.SZ_M; lia) H12) as T6.
exact T6.
Qed.

(* m_set's five stores when the transition record is written at index kk *)
Lemma mw_world9 : forall (W : world segs) memc mF Bw L kk nv,
  0 <= kk < 16 ->
  tw_at TMAP_A (mw_rd L (aview segs (w_H W) memc) (aview segs (w_H W) mF)) (mwm_W Bw) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W) mF (TA_OW + (4 + 12 * kk) + Z.of_nat j)
     = Some (YO0f.le_byte 1 4 j)) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W) mF (TA_OW + (8 + 12 * kk) + Z.of_nat j)
     = Some (YO0f.le_byte (TW.s32_at Bw 12) 4 j)) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W) mF (TA_OW + (12 + 12 * kk) + Z.of_nat j)
     = Some (YO0f.le_byte 1 4 j)) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W) mF (TA_OW + 0 + Z.of_nat j)
     = Some (YO0f.le_byte nv 4 j)) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W) mF (TA_M + 12 + Z.of_nat j) = Some (YO0f.le_byte 1 4 j)) ->
  tw_at TMAP_A (mw_rd ((TA_M + 12, TA_M + 12 + Z.of_nat 4) :: (TA_OW + 0, TA_OW + 0 + Z.of_nat 4)
                       :: (TA_OW + (12 + 12 * kk), TA_OW + (12 + 12 * kk) + Z.of_nat 4)
                       :: (TA_OW + (8 + 12 * kk), TA_OW + (8 + 12 * kk) + Z.of_nat 4)
                       :: (TA_OW + (4 + 12 * kk), TA_OW + (4 + 12 * kk) + Z.of_nat 4) :: L)
                 (aview segs (w_H W) memc) (aview segs (w_H W) mF))
    (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * kk) (TW.put 4 1))
                      (65320 + 12 * kk) (TW.put 4 (TW.s32_at Bw 12)))
               (65324 + 12 * kk) (TW.put 4 1))
        65312 (TW.put 4 nv)) 12 (TW.put 4 1)).
Proof.
intros W memc mF Bw L kk nv Hk T4 Ha Hb Hc H0 H12.
pose proof (mw_step L (aview segs (w_H W) memc) (aview segs (w_H W) mF) (mwm_W Bw)
  TW.OFF_OW TA_OW TW.SZ_OW (4 + 12 * kk) 4 1 T4 TMAP_A_OW
  ltac:(lia) ltac:(unfold TW.SZ_OW; lia) Ha) as T5.
replace (TW.OFF_OW + (4 + 12 * kk)) with (65316 + 12 * kk) in T5 by (unfold TW.OFF_OW; ring).
pose proof (mw_step _ (aview segs (w_H W) memc) (aview segs (w_H W) mF) _
  TW.OFF_OW TA_OW TW.SZ_OW (8 + 12 * kk) 4 (TW.s32_at Bw 12) T5 TMAP_A_OW
  ltac:(lia) ltac:(unfold TW.SZ_OW; lia) Hb) as T6.
replace (TW.OFF_OW + (8 + 12 * kk)) with (65320 + 12 * kk) in T6 by (unfold TW.OFF_OW; ring).
pose proof (mw_step _ (aview segs (w_H W) memc) (aview segs (w_H W) mF) _
  TW.OFF_OW TA_OW TW.SZ_OW (12 + 12 * kk) 4 1 T6 TMAP_A_OW
  ltac:(lia) ltac:(unfold TW.SZ_OW; lia) Hc) as T7.
replace (TW.OFF_OW + (12 + 12 * kk)) with (65324 + 12 * kk) in T7 by (unfold TW.OFF_OW; ring).
pose proof (mw_step _ (aview segs (w_H W) memc) (aview segs (w_H W) mF) _
  TW.OFF_OW TA_OW TW.SZ_OW 0 4 nv T7 TMAP_A_OW
  ltac:(lia) ltac:(unfold TW.SZ_OW; lia) H0) as T8.
pose proof (mw_step _ (aview segs (w_H W) memc) (aview segs (w_H W) mF) _
  TW.OFF_M TA_M TW.SZ_M 12 4 1 T8 TMAP_A_M
  ltac:(lia) ltac:(unfold TW.SZ_M; lia) H12) as T9.
exact T9.
Qed.

Definition mw_winsk (sp kk : Z) (a : Z) : Prop :=
  mw_wins sp a \/ (TA_OW + (4 + 12 * kk) <= a < TA_OW + (16 + 12 * kk)).

Lemma mw_winsk_Zs : forall sp kk a, 0 <= kk < 16 -> mw_winsk sp kk a -> mw_Zs sp a.
Proof.
intros sp kk a Hk [H | H]; [exact (mw_wins_Zs sp a H)|].
right. apply mw_inG_OW. unfold TA_OW, TW.SZ_OW in *. lia.
Qed.

(* ---- the walk ---- *)

Lemma mw_holds : @transport_m_wake_cg_holds_stmt fx rc B MT.
Proof.
unfold transport_m_wake_cg_holds_stmt.
intros HCELLS HOW LAWS MTL HGX.
unfold transport_m_wake_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw' r
  HJ Hra Hra4 Hgp Htp Hsp16 Hlo Hhi Htw Hm Hev.
pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : MWAKE_STK = 16) by reflexivity.
assert (FF : MWAKE_FRAME = 16) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hce : alloc_ceiling <= spZ regs - MWAKE_STK) by lia.
assert (Hwin : forall a, spZ regs - MWAKE_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (HLB : Z.of_nat (length Bw) = 65616)
  by (rewrite (tw_len TMAP_A (aview segs (w_H W) memc) Bw Htw); vm_compute; reflexivity).
pose proof (TWL.s32_range Bw 0) as S0. pose proof (TWL.s32_range Bw 24) as S24.
pose proof (TWL.s32_range Bw 12) as S12. pose proof (TWL.s32_range Bw 88) as S88.
pose proof (TWL.s32_range Bw 65508) as S65508. pose proof (TWL.s32_range Bw 65312) as S65312.
(* the model as a flat cascade of tests on Bw *)
rewrite (mw_m_eq Bw) in Hm.
change (TW.M_desk_known Bw) with (TW.s32_at Bw 0) in Hm.
change (TW.M_foreign Bw) with (TW.s32_at Bw 24) in Hm.
rewrite (mw_e2 Bw HLB), (mw_fa Bw HLB), (mw_st Bw HLB), (mw_on Bw HLB) in Hm.
(* the valuation of the walk and its atoms *)
destruct mw_vals as (V1 & V93 & V8 & V12 & V27 & VSIG).
set (E0 := mw_E regs Bw).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, mw_E; apply Eimg_env).
assert (EOB : forall j, (j < 95)%nat -> ew E0 (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
  by (intros j Hj; unfold E0, mw_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EXT : forall i, (i < 10)%nat -> ew E0 (32 + i) = nth i (mw_ex Bw) (Z_to_bv 64 0))
  by (intros i Hi; unfold E0, mw_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (Usp0 : bv_unsigned (ew E0 2) = spZ regs)
  by (unfold E0, mw_E; rewrite (ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E0 n = YK11.getr regs rr)
  by (intros n rr Hn; unfold E0, mw_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U8_0 : bv_unsigned (ew E0 (A_OBJ 8)) = TA_M)
  by (rewrite (EOB 8%nat ltac:(lia)), V8; apply unsigned_lit_small; unfold TA_M; lia).
assert (U12_0 : bv_unsigned (ew E0 (A_OBJ 12)) = TA_OW)
  by (rewrite (EOB 12%nat ltac:(lia)), V12; apply unsigned_lit_small; unfold TA_OW; lia).
assert (U27_0 : bv_unsigned (ew E0 (A_OBJ 27)) = TA_g_now)
  by (rewrite (EOB 27%nat ltac:(lia)), V27; apply unsigned_lit_small; unfold TA_g_now; lia).
assert (U8L : bv_unsigned (ew E0 249%nat) = TA_M) by exact U8_0.
assert (U12L : bv_unsigned (ew E0 253%nat) = TA_OW) by exact U12_0.
assert (U27L : bv_unsigned (ew E0 268%nat) = TA_g_now) by exact U27_0.
assert (U1L : bv_unsigned (ew E0 242%nat) = FCells.GOT_CELL_K).
{ change 242%nat with (A_OBJ 1). rewrite (EOB 1%nat ltac:(lia)), V1.
  apply unsigned_lit_small. unfold FCells.GOT_CELL_K. lia. }
assert (U93L : bv_unsigned (ew E0 334%nat) = FCells.CELL_K).
{ change 334%nat with (A_OBJ 93). rewrite (EOB 93%nat ltac:(lia)), V93.
  apply unsigned_lit_small. unfold FCells.CELL_K. lia. }
assert (A33_0 : ew E0 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4))) by exact (EXT 1%nat ltac:(lia)).
assert (A34_0 : ew E0 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4))) by exact (EXT 2%nat ltac:(lia)).
assert (A35_0 : ew E0 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4))) by exact (EXT 3%nat ltac:(lia)).
assert (A36_0 : ew E0 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4))) by exact (EXT 4%nat ltac:(lia)).
assert (A37_0 : ew E0 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4))) by exact (EXT 5%nat ltac:(lia)).
assert (A38_0 : ew E0 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4))) by exact (EXT 6%nat ltac:(lia)).
assert (A39_0 : ew E0 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8))) by exact (EXT 7%nat ltac:(lia)).
assert (A40_0 : ew E0 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8))) by exact (EXT 8%nat ltac:(lia)).
assert (A41_0 : ew E0 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8))) by exact (EXT 9%nat ltac:(lia)).
destruct (mw_entry lyc Sc W regs memc mdc Bw HCELLS HOW HAR Htw ltac:(intros a Ha; apply Hpres0; lia) Hsp Hsp16)
  as [HS SHOK].
fold E0 in HS, SHOK.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose (BR := paj_branch (PI := PI_transport)).
pose proof (paj_ret_at (fx := fx) (PL := PL_transport) (PI := PI_transport)) as RET.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_m_wake)) memc (YK11.seg_rom segs)) mdc) Q)
  end.
(* run 1: the frame, the save of ra, a2 = &M, a0 = M.desk_known; stops at `beqz a0` *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ mw_awr Usp0 U8L U12L U27L. }
set (md1 := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody md1. clear mat.
assert (KW1 : forall a, 0 <= a < 2 ^ 64 -> ~ mw_wins (spZ regs) a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) memc a).
{ intros a Ha Hn.
  eapply (kept_of_frame _ _ _ _ _ (mw_wins (spZ regs))).
  - exact HFr.
  - intros b0 wlo whi x Hin Hx. cbv beta.
    mw_wtac Hin Hx ltac:(rewrite ?Usp0, ?U8L, ?U12L, ?U27L in Hx; unfold mw_wins;
      first [ lia | left; lia | right; left; lia | right; right; left; lia
            | right; right; right; left; lia | right; right; right; right; left; lia
            | right; right; right; right; right; left; lia
            | right; right; right; right; right; right; lia ]).
  - exact Ha.
  - exact Hn. }
assert (GA1 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_r1 := mf) in *; set (E_r1 := EF) in HS, SHOK, HEI
  end.
  assert (HE_r1 : forall n, (n < 1024)%nat -> ew E_r1 n = ew E0 n)
    by (intros n Hn; unfold E_r1; repeat rewrite ew_ewset_other by lia; reflexivity).
  assert (A_r1_35 : ew E_r1 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_r1 by lia; exact A35_0).
  assert (A_r1_36 : ew E_r1 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_r1 by lia; exact A36_0).
  assert (A_r1_37 : ew E_r1 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_r1 by lia; exact A37_0).
  assert (A_r1_38 : ew E_r1 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_r1 by lia; exact A38_0).
  assert (A_r1_39 : ew E_r1 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_r1 by lia; exact A39_0).
  assert (A_r1_40 : ew E_r1 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_r1 by lia; exact A40_0).
  assert (A_r1_41 : ew E_r1 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_r1 by lia; exact A41_0).
  assert (A_r1_33 : ew E_r1 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_r1 by lia; exact A33_0).
  assert (A_r1_34 : ew E_r1 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_r1 by lia; exact A34_0).
  assert (U8_r1 : bv_unsigned (ew E_r1 249%nat) = TA_M) by (rewrite HE_r1 by lia; exact U8L).
  assert (U12_r1 : bv_unsigned (ew E_r1 253%nat) = TA_OW) by (rewrite HE_r1 by lia; exact U12L).
  assert (U27_r1 : bv_unsigned (ew E_r1 268%nat) = TA_g_now) by (rewrite HE_r1 by lia; exact U27L).
  assert (U1_r1 : bv_unsigned (ew E_r1 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_r1 by lia; exact U1L).
  assert (U93_r1 : bv_unsigned (ew E_r1 334%nat) = FCells.CELL_K) by (rewrite HE_r1 by lia; exact U93L).
  assert (Usp_r1 : bv_unsigned (ew E_r1 2) = spZ regs) by (rewrite HE_r1 by lia; exact Usp0).
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  { (* M.desk_known = 0: a0 = -1 (SPEC_E_ARG), no store *)
  cbn [branch_taken] in Hc.
  rewrite (mw_sext_atom E_r1 33 Bw 0 A_r1_33) in Hc.
  change (sv_denot E_r1 (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (mw_eqb_s32 (TW.s32_at Bw 0) 0 ltac:(lia) ltac:(lia)) in Hc.
  rewrite Hc in Hm. cbv iota in Hm.
  destruct (mw_some_inv _ _ _ _ Hm) as [HB Hr]. subst Bw'. subst r.
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r1 U8_r1 U12_r1 U12_r1. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KW2 : forall a, 0 <= a < 2 ^ 64 -> ~ mw_wins (spZ regs) a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity; [| exact (KW1 a Ha Hn)].
    eapply (kept_of_frame _ _ _ _ _ (mw_wins (spZ regs))).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r1, ?U8_r1, ?U12_r1 in Hx; unfold mw_wins;
        first [ lia | left; lia | right; left; lia | right; right; left; lia
              | right; right; right; left; lia | right; right; right; right; left; lia
              | right; right; right; right; right; left; lia
              | right; right; right; right; right; right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GA2 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA1 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_a := mf) in *; set (E_a := EF) in HS, SHOK, HEI
  end.
  assert (HE_a : forall n, (n < 1024)%nat -> ew E_a n = ew E0 n)
    by (intros n Hn; unfold E_a; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r1; lia]).
  assert (A_a_35 : ew E_a 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_a by lia; exact A35_0).
  assert (A_a_36 : ew E_a 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_a by lia; exact A36_0).
  assert (A_a_37 : ew E_a 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_a by lia; exact A37_0).
  assert (A_a_38 : ew E_a 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_a by lia; exact A38_0).
  assert (A_a_39 : ew E_a 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_a by lia; exact A39_0).
  assert (A_a_40 : ew E_a 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_a by lia; exact A40_0).
  assert (A_a_41 : ew E_a 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_a by lia; exact A41_0).
  assert (A_a_33 : ew E_a 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_a by lia; exact A33_0).
  assert (A_a_34 : ew E_a 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_a by lia; exact A34_0).
  assert (U8_a : bv_unsigned (ew E_a 249%nat) = TA_M) by (rewrite HE_a by lia; exact U8L).
  assert (U12_a : bv_unsigned (ew E_a 253%nat) = TA_OW) by (rewrite HE_a by lia; exact U12L).
  assert (U27_a : bv_unsigned (ew E_a 268%nat) = TA_g_now) by (rewrite HE_a by lia; exact U27L).
  assert (U1_a : bv_unsigned (ew E_a 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_a by lia; exact U1L).
  assert (U93_a : bv_unsigned (ew E_a 334%nat) = FCells.CELL_K) by (rewrite HE_a by lia; exact U93L).
  assert (Usp_a : bv_unsigned (ew E_a 2) = spZ regs) by (rewrite HE_a by lia; exact Usp0).
  pose proof (st_ok_pi_region_nth E_a _ (restrict (w_H W) ms_a) 4 _ HS eq_refl) as RG4.
  cbn [ms_mem restrict] in RG4.
  assert (KM12 : forall x, TA_M + 12 <= x < TA_M + 12 + Z.of_N 4%N ->
    aview segs (w_H W) (ms_mem ms_a) x = aview segs (w_H W) memc x)
    by (exact (mw_keep_win E_a W (ms_mem ms_a) (aview segs (w_H W) memc) _ 249%nat TA_M 12 4%N 35 Bw TW.OFF_M TW.SZ_M
         RG4 eq_refl U8_a ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) A_a_35 Htw TMAP_A_M
         ltac:(lia) ltac:(unfold TW.SZ_M; cbn [Z.of_N]; lia))).
  pose proof (st_ok_pi_region_nth E_a _ (restrict (w_H W) ms_a) 5 _ HS eq_refl) as RG5.
  cbn [ms_mem restrict] in RG5.
  assert (KM16 : forall x, TA_M + 16 <= x < TA_M + 16 + Z.of_N 8%N ->
    aview segs (w_H W) (ms_mem ms_a) x = aview segs (w_H W) memc x)
    by (exact (mw_keep_win E_a W (ms_mem ms_a) (aview segs (w_H W) memc) _ 249%nat TA_M 16 8%N 40 Bw TW.OFF_M TW.SZ_M
         RG5 eq_refl U8_a ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) A_a_40 Htw TMAP_A_M
         ltac:(lia) ltac:(unfold TW.SZ_M; cbn [Z.of_N]; lia))).
  pose proof (st_ok_pi_region_nth E_a _ (restrict (w_H W) ms_a) 7 _ HS eq_refl) as RG7.
  cbn [ms_mem restrict] in RG7.
  assert (KM40 : forall x, TA_M + 40 <= x < TA_M + 40 + Z.of_N 8%N ->
    aview segs (w_H W) (ms_mem ms_a) x = aview segs (w_H W) memc x)
    by (exact (mw_keep_win E_a W (ms_mem ms_a) (aview segs (w_H W) memc) _ 249%nat TA_M 40 8%N 41 Bw TW.OFF_M TW.SZ_M
         RG7 eq_refl U8_a ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) A_a_41 Htw TMAP_A_M
         ltac:(lia) ltac:(unfold TW.SZ_M; cbn [Z.of_N]; lia))).
  pose proof (st_ok_pi_region_nth E_a _ (restrict (w_H W) ms_a) 8 _ HS eq_refl) as RG8.
  cbn [ms_mem restrict] in RG8.
  assert (KM88 : forall x, TA_M + 88 <= x < TA_M + 88 + Z.of_N 4%N ->
    aview segs (w_H W) (ms_mem ms_a) x = aview segs (w_H W) memc x)
    by (exact (mw_keep_win E_a W (ms_mem ms_a) (aview segs (w_H W) memc) _ 249%nat TA_M 88 4%N 36 Bw TW.OFF_M TW.SZ_M
         RG8 eq_refl U8_a ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) A_a_36 Htw TMAP_A_M
         ltac:(lia) ltac:(unfold TW.SZ_M; cbn [Z.of_N]; lia))).
  pose proof (st_ok_pi_region_nth E_a _ (restrict (w_H W) ms_a) 9 _ HS eq_refl) as RG9.
  cbn [ms_mem restrict] in RG9.
  assert (KOW0 : forall x, TA_OW + 0 <= x < TA_OW + 0 + Z.of_N 4%N ->
    aview segs (w_H W) (ms_mem ms_a) x = aview segs (w_H W) memc x)
    by (exact (mw_keep_win E_a W (ms_mem ms_a) (aview segs (w_H W) memc) _ 253%nat TA_OW 0 4%N 38 Bw TW.OFF_OW TW.SZ_OW
         RG9 eq_refl U12_a ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) A_a_38 Htw TMAP_A_OW
         ltac:(lia) ltac:(unfold TW.SZ_OW; cbn [Z.of_N]; lia))).
  pose proof (st_ok_pi_region_nth E_a _ (restrict (w_H W) ms_a) 10 _ HS eq_refl) as RG10.
  cbn [ms_mem restrict] in RG10.
  assert (KOW196 : forall x, TA_OW + 196 <= x < TA_OW + 196 + Z.of_N 4%N ->
    aview segs (w_H W) (ms_mem ms_a) x = aview segs (w_H W) memc x)
    by (exact (mw_keep_win E_a W (ms_mem ms_a) (aview segs (w_H W) memc) _ 253%nat TA_OW 196 4%N 37 Bw TW.OFF_OW TW.SZ_OW
         RG10 eq_refl U12_a ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) A_a_37 Htw TMAP_A_OW
         ltac:(lia) ltac:(unfold TW.SZ_OW; cbn [Z.of_N]; lia))).
  assert (HTW : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms_a)) (Bw)).
  { apply (mw_fin_rd (@nil (Z * Z)) (aview segs (w_H W) memc) (aview segs (w_H W) (ms_mem ms_a)) _ Htw).
    intros x Hx Hni. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    destruct (Classical_Prop.classic (mw_wins (spZ regs) x)) as [Hw | Hw].
    - destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]].
      + exfalso. unfold MWAKE_STK, MWAKE_FRAME in Hw. lia.
      + exact (KM12 x Hw).
      + exact (KM16 x Hw).
      + exact (KM40 x Hw).
      + exact (KM88 x Hw).
      + exact (KOW0 x Hw).
      + exact (KOW196 x Hw).
    - apply KW2; [lia | exact Hw]. }
  mw_regv HS (Z_to_bv 5 1) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite HE_a by lia;
          rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  mw_regv HS (Z_to_bv 5 10) (w64 (-1)) RF10
    ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mw_u64; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms_a)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E_a _ ms_a regs (mw_ex Bw) HS).
    - apply mw_agree; [intros n Hn; rewrite HE_a by lia; reflexivity | reflexivity].
    - vm_compute. reflexivity. }
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ mw_Zs (spZ regs) a ->
    aview segs (w_H W) (ms_mem ms_a) a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; apply KW2; [exact Ha | intros Hc0; exact (Hn (mw_wins_Zs _ a Hc0))]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  exact (mw_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (Bw) (-1)
           (ms_regs ms_a) (ms_mem ms_a) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GA2
           HTW HPF RF1 RF10 matF).
  }
  { (* M.desk_known <> 0 *)
  cbn [branch_taken] in Hc.
  rewrite (mw_sext_atom E_r1 33 Bw 0 A_r1_33) in Hc.
  change (sv_denot E_r1 (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (mw_eqb_s32 (TW.s32_at Bw 0) 0 ltac:(lia) ltac:(lia)) in Hc.
  rewrite Hc in Hm. cbv iota in Hm.
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r1 U8_r1 U12_r1 U12_r1. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KW3 : forall a, 0 <= a < 2 ^ 64 -> ~ mw_wins (spZ regs) a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity; [| exact (KW1 a Ha Hn)].
    eapply (kept_of_frame _ _ _ _ _ (mw_wins (spZ regs))).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r1, ?U8_r1, ?U12_r1 in Hx; unfold mw_wins;
        first [ lia | left; lia | right; left; lia | right; right; left; lia
              | right; right; right; left; lia | right; right; right; right; left; lia
              | right; right; right; right; right; left; lia
              | right; right; right; right; right; right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GA3 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA1 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_r2 := mf) in *; set (E_r2 := EF) in HS, SHOK, HEI
  end.
  assert (HE_r2 : forall n, (n < 1024)%nat -> ew E_r2 n = ew E0 n)
    by (intros n Hn; unfold E_r2; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r1; lia]).
  assert (A_r2_35 : ew E_r2 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_r2 by lia; exact A35_0).
  assert (A_r2_36 : ew E_r2 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_r2 by lia; exact A36_0).
  assert (A_r2_37 : ew E_r2 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_r2 by lia; exact A37_0).
  assert (A_r2_38 : ew E_r2 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_r2 by lia; exact A38_0).
  assert (A_r2_39 : ew E_r2 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_r2 by lia; exact A39_0).
  assert (A_r2_40 : ew E_r2 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_r2 by lia; exact A40_0).
  assert (A_r2_41 : ew E_r2 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_r2 by lia; exact A41_0).
  assert (A_r2_33 : ew E_r2 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_r2 by lia; exact A33_0).
  assert (A_r2_34 : ew E_r2 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_r2 by lia; exact A34_0).
  assert (U8_r2 : bv_unsigned (ew E_r2 249%nat) = TA_M) by (rewrite HE_r2 by lia; exact U8L).
  assert (U12_r2 : bv_unsigned (ew E_r2 253%nat) = TA_OW) by (rewrite HE_r2 by lia; exact U12L).
  assert (U27_r2 : bv_unsigned (ew E_r2 268%nat) = TA_g_now) by (rewrite HE_r2 by lia; exact U27L).
  assert (U1_r2 : bv_unsigned (ew E_r2 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_r2 by lia; exact U1L).
  assert (U93_r2 : bv_unsigned (ew E_r2 334%nat) = FCells.CELL_K) by (rewrite HE_r2 by lia; exact U93L).
  assert (Usp_r2 : bv_unsigned (ew E_r2 2) = spZ regs) by (rewrite HE_r2 by lia; exact Usp0).
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  { (* M.foreign = 0 *)
  cbn [branch_taken] in Hc.
  rewrite (mw_sext_atom E_r2 34 Bw 24 A_r2_34) in Hc.
  change (sv_denot E_r2 (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (mw_eqb_s32 (TW.s32_at Bw 24) 0 ltac:(lia) ltac:(lia)) in Hc.
  rewrite Hc in Hm. cbn [negb] in Hm. cbv iota in Hm.
  destruct (TW.s32_at Bw 65508 =? 2 ^ 31 - 1) eqn:EO; [cbv iota in Hm; discriminate Hm|].
  cbv iota in Hm.
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r2 U8_r2 U12_r2 U12_r2. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KW4 : forall a, 0 <= a < 2 ^ 64 -> ~ mw_wins (spZ regs) a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity; [| exact (KW3 a Ha Hn)].
    eapply (kept_of_frame _ _ _ _ _ (mw_wins (spZ regs))).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r2, ?U8_r2, ?U12_r2 in Hx; unfold mw_wins;
        first [ lia | left; lia | right; left; lia | right; right; left; lia
              | right; right; right; left; lia | right; right; right; right; left; lia
              | right; right; right; right; right; left; lia
              | right; right; right; right; right; right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GA4 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA3 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_r3 := mf) in *; set (E_r3 := EF) in HS, SHOK, HEI
  end.
  assert (HE_r3 : forall n, (n < 1024)%nat -> ew E_r3 n = ew E0 n)
    by (intros n Hn; unfold E_r3; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r2; lia]).
  assert (A_r3_35 : ew E_r3 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_r3 by lia; exact A35_0).
  assert (A_r3_36 : ew E_r3 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_r3 by lia; exact A36_0).
  assert (A_r3_37 : ew E_r3 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_r3 by lia; exact A37_0).
  assert (A_r3_38 : ew E_r3 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_r3 by lia; exact A38_0).
  assert (A_r3_39 : ew E_r3 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_r3 by lia; exact A39_0).
  assert (A_r3_40 : ew E_r3 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_r3 by lia; exact A40_0).
  assert (A_r3_41 : ew E_r3 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_r3 by lia; exact A41_0).
  assert (A_r3_33 : ew E_r3 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_r3 by lia; exact A33_0).
  assert (A_r3_34 : ew E_r3 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_r3 by lia; exact A34_0).
  assert (U8_r3 : bv_unsigned (ew E_r3 249%nat) = TA_M) by (rewrite HE_r3 by lia; exact U8L).
  assert (U12_r3 : bv_unsigned (ew E_r3 253%nat) = TA_OW) by (rewrite HE_r3 by lia; exact U12L).
  assert (U27_r3 : bv_unsigned (ew E_r3 268%nat) = TA_g_now) by (rewrite HE_r3 by lia; exact U27L).
  assert (U1_r3 : bv_unsigned (ew E_r3 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_r3 by lia; exact U1L).
  assert (U93_r3 : bv_unsigned (ew E_r3 334%nat) = FCells.CELL_K) by (rewrite HE_r3 by lia; exact U93L).
  assert (Usp_r3 : bv_unsigned (ew E_r3 2) = spZ regs) by (rewrite HE_r3 by lia; exact Usp0).
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  { (* the old M.fail = 0 *)
  cbn [branch_taken] in Hc.
  rewrite (mw_sext_atom E_r3 36 Bw 88 A_r3_36) in Hc.
  change (sv_denot E_r3 (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (mw_eqb_s32 (TW.s32_at Bw 88) 0 ltac:(lia) ltac:(lia)) in Hc.
  rewrite Hc in Hm. cbn [negb] in Hm. cbv iota in Hm.
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r3 U8_r3 U12_r3 U12_r3. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KW5 : forall a, 0 <= a < 2 ^ 64 -> ~ mw_wins (spZ regs) a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity; [| exact (KW4 a Ha Hn)].
    eapply (kept_of_frame _ _ _ _ _ (mw_wins (spZ regs))).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r3, ?U8_r3, ?U12_r3 in Hx; unfold mw_wins;
        first [ lia | left; lia | right; left; lia | right; right; left; lia
              | right; right; right; left; lia | right; right; right; right; left; lia
              | right; right; right; right; right; left; lia
              | right; right; right; right; right; right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GA5 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA4 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_r4 := mf) in *; set (E_r4 := EF) in HS, SHOK, HEI
  end.
  assert (HE_r4 : forall n, (n < 1024)%nat -> ew E_r4 n = ew E0 n)
    by (intros n Hn; unfold E_r4; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r3; lia]).
  assert (A_r4_35 : ew E_r4 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_r4 by lia; exact A35_0).
  assert (A_r4_36 : ew E_r4 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_r4 by lia; exact A36_0).
  assert (A_r4_37 : ew E_r4 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_r4 by lia; exact A37_0).
  assert (A_r4_38 : ew E_r4 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_r4 by lia; exact A38_0).
  assert (A_r4_39 : ew E_r4 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_r4 by lia; exact A39_0).
  assert (A_r4_40 : ew E_r4 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_r4 by lia; exact A40_0).
  assert (A_r4_41 : ew E_r4 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_r4 by lia; exact A41_0).
  assert (A_r4_33 : ew E_r4 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_r4 by lia; exact A33_0).
  assert (A_r4_34 : ew E_r4 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_r4 by lia; exact A34_0).
  assert (U8_r4 : bv_unsigned (ew E_r4 249%nat) = TA_M) by (rewrite HE_r4 by lia; exact U8L).
  assert (U12_r4 : bv_unsigned (ew E_r4 253%nat) = TA_OW) by (rewrite HE_r4 by lia; exact U12L).
  assert (U27_r4 : bv_unsigned (ew E_r4 268%nat) = TA_g_now) by (rewrite HE_r4 by lia; exact U27L).
  assert (U1_r4 : bv_unsigned (ew E_r4 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_r4 by lia; exact U1L).
  assert (U93_r4 : bv_unsigned (ew E_r4 334%nat) = FCells.CELL_K) by (rewrite HE_r4 by lia; exact U93L).
  assert (Usp_r4 : bv_unsigned (ew E_r4 2) = spZ regs) by (rewrite HE_r4 by lia; exact Usp0).
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  { (* M.state <> S_WAKING: m_set records the transition *)
  cbn [branch_taken] in Hc.
  rewrite (mw_sext_atom E_r4 35 Bw 12 A_r4_35) in Hc.
  change (sv_denot E_r4 (SLit 1)) with (Z_to_bv 64 1) in Hc.
  rewrite (mw_eqb_s32 (TW.s32_at Bw 12) 1 ltac:(lia) ltac:(lia)) in Hc.
  apply negb_true_iff in Hc.
  rewrite Hc in Hm. cbv iota in Hm.
  destruct (TW.s32_at Bw 65312 <? 0) eqn:EN0; [cbv iota in Hm; discriminate Hm|].
  cbv iota in Hm.
  destruct (TW.s32_at Bw 65312 =? 2 ^ 31 - 1) eqn:EI; [cbv iota in Hm; discriminate Hm|].
  cbv iota in Hm.
  apply Z.ltb_ge in EN0.
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r4 U8_r4 U12_r4 U12_r4. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KW6 : forall a, 0 <= a < 2 ^ 64 -> ~ mw_wins (spZ regs) a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity; [| exact (KW5 a Ha Hn)].
    eapply (kept_of_frame _ _ _ _ _ (mw_wins (spZ regs))).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r4, ?U8_r4, ?U12_r4 in Hx; unfold mw_wins;
        first [ lia | left; lia | right; left; lia | right; right; left; lia
              | right; right; right; left; lia | right; right; right; right; left; lia
              | right; right; right; right; right; left; lia
              | right; right; right; right; right; right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GA6 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA5 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_r5 := mf) in *; set (E_r5 := EF) in HS, SHOK, HEI
  end.
  assert (HE_r5 : forall n, (n < 1024)%nat -> ew E_r5 n = ew E0 n)
    by (intros n Hn; unfold E_r5; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r4; lia]).
  assert (A_r5_35 : ew E_r5 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_r5 by lia; exact A35_0).
  assert (A_r5_36 : ew E_r5 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_r5 by lia; exact A36_0).
  assert (A_r5_37 : ew E_r5 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_r5 by lia; exact A37_0).
  assert (A_r5_38 : ew E_r5 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_r5 by lia; exact A38_0).
  assert (A_r5_39 : ew E_r5 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_r5 by lia; exact A39_0).
  assert (A_r5_40 : ew E_r5 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_r5 by lia; exact A40_0).
  assert (A_r5_41 : ew E_r5 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_r5 by lia; exact A41_0).
  assert (A_r5_33 : ew E_r5 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_r5 by lia; exact A33_0).
  assert (A_r5_34 : ew E_r5 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_r5 by lia; exact A34_0).
  assert (U8_r5 : bv_unsigned (ew E_r5 249%nat) = TA_M) by (rewrite HE_r5 by lia; exact U8L).
  assert (U12_r5 : bv_unsigned (ew E_r5 253%nat) = TA_OW) by (rewrite HE_r5 by lia; exact U12L).
  assert (U27_r5 : bv_unsigned (ew E_r5 268%nat) = TA_g_now) by (rewrite HE_r5 by lia; exact U27L).
  assert (U1_r5 : bv_unsigned (ew E_r5 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_r5 by lia; exact U1L).
  assert (U93_r5 : bv_unsigned (ew E_r5 334%nat) = FCells.CELL_K) by (rewrite HE_r5 by lia; exact U93L).
  assert (Usp_r5 : bv_unsigned (ew E_r5 2) = spZ regs) by (rewrite HE_r5 by lia; exact Usp0).
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  { (* 15 < OW.n: the record is dropped *)
  cbn [branch_taken] in Hc.
  rewrite (mw_sext_atom E_r5 38 Bw 65312 A_r5_38) in Hc.
  change (sv_denot E_r5 (SLit 15)) with (Z_to_bv 64 15) in Hc.
  rewrite (mw_lts_s32 15 (TW.s32_at Bw 65312) ltac:(lia) ltac:(lia)) in Hc.
  rewrite Hc in Hm. cbv iota in Hm. destruct (mw_some_inv _ _ _ _ Hm) as [HB Hr]. subst Bw'. subst r.
  rewrite (mw_fin_m Bw HLB).
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r5 U8_r5 U12_r5 U12_r5. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KW7 : forall a, 0 <= a < 2 ^ 64 -> ~ mw_wins (spZ regs) a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity; [| exact (KW6 a Ha Hn)].
    eapply (kept_of_frame _ _ _ _ _ (mw_wins (spZ regs))).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r5, ?U8_r5, ?U12_r5 in Hx; unfold mw_wins;
        first [ lia | left; lia | right; left; lia | right; right; left; lia
              | right; right; right; left; lia | right; right; right; right; left; lia
              | right; right; right; right; right; left; lia
              | right; right; right; right; right; right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GA7 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA6 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_d := mf) in *; set (E_d := EF) in HS, SHOK, HEI
  end.
  assert (HE_d : forall n, (n < 1024)%nat -> ew E_d n = ew E0 n)
    by (intros n Hn; unfold E_d; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r5; lia]).
  assert (A_d_35 : ew E_d 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_d by lia; exact A35_0).
  assert (A_d_36 : ew E_d 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_d by lia; exact A36_0).
  assert (A_d_37 : ew E_d 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_d by lia; exact A37_0).
  assert (A_d_38 : ew E_d 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_d by lia; exact A38_0).
  assert (A_d_39 : ew E_d 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_d by lia; exact A39_0).
  assert (A_d_40 : ew E_d 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_d by lia; exact A40_0).
  assert (A_d_41 : ew E_d 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_d by lia; exact A41_0).
  assert (A_d_33 : ew E_d 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_d by lia; exact A33_0).
  assert (A_d_34 : ew E_d 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_d by lia; exact A34_0).
  assert (U8_d : bv_unsigned (ew E_d 249%nat) = TA_M) by (rewrite HE_d by lia; exact U8L).
  assert (U12_d : bv_unsigned (ew E_d 253%nat) = TA_OW) by (rewrite HE_d by lia; exact U12L).
  assert (U27_d : bv_unsigned (ew E_d 268%nat) = TA_g_now) by (rewrite HE_d by lia; exact U27L).
  assert (U1_d : bv_unsigned (ew E_d 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_d by lia; exact U1L).
  assert (U93_d : bv_unsigned (ew E_d 334%nat) = FCells.CELL_K) by (rewrite HE_d by lia; exact U93L).
  assert (Usp_d : bv_unsigned (ew E_d 2) = spZ regs) by (rewrite HE_d by lia; exact Usp0).
  pose proof (st_ok_pi_region_nth E_d _ (restrict (w_H W) ms_d) 10 _ HS eq_refl) as RG10.
  cbn [ms_mem restrict] in RG10.
  assert (VOW196 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_d) (TA_OW + 196 + Z.of_nat j) = Some (YO0f.le_byte (TW.s32_at Bw 65508 + 1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_d W (ms_mem ms_d) _ 253%nat TA_OW 196 4%N (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 1)) RG10 eq_refl U12_d
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. change (8 * Z.of_nat (N.to_nat 4%N)) with 32.
    exact (mw_u_add1 E_d (SExt true 32 (SOff 37 0)) (TW.s32_at Bw 65508) (mw_sext_atom E_d 37 Bw 65508 A_d_37)). }
  pose proof (st_ok_pi_region_nth E_d _ (restrict (w_H W) ms_d) 5 _ HS eq_refl) as RG5.
  cbn [ms_mem restrict] in RG5.
  assert (VM16 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_d) (TA_M + 16 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_d W (ms_mem ms_d) _ 249%nat TA_M 16 8%N (SLit 0) RG5 eq_refl U8_d
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_d _ (restrict (w_H W) ms_d) 7 _ HS eq_refl) as RG7.
  cbn [ms_mem restrict] in RG7.
  assert (VM40 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_d) (TA_M + 40 + Z.of_nat j) = Some (YO0f.le_byte (TW.u_at Bw 65000 8) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_d W (ms_mem ms_d) _ 249%nat TA_M 40 8%N (SOff 39 0) RG7 eq_refl U8_d
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. rewrite (U_atom E_d 39 (TW.u_at Bw 65000 8) A_d_39 ltac:(pose proof (TWL.u_at_range Bw 65000 8) as HR;
      cbn [Z.of_nat] in HR; lia)). reflexivity. }
  pose proof (st_ok_pi_region_nth E_d _ (restrict (w_H W) ms_d) 8 _ HS eq_refl) as RG8.
  cbn [ms_mem restrict] in RG8.
  assert (VM88 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_d) (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_d W (ms_mem ms_d) _ 249%nat TA_M 88 4%N (SLit 0) RG8 eq_refl U8_d
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_d _ (restrict (w_H W) ms_d) 9 _ HS eq_refl) as RG9.
  cbn [ms_mem restrict] in RG9.
  assert (VOW0 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_d) (TA_OW + 0 + Z.of_nat j) = Some (YO0f.le_byte (TW.s32_at Bw 65312 + 1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_d W (ms_mem ms_d) _ 253%nat TA_OW 0 4%N (SAlu ALU_ADD (SExt true 32 (SOff 38 0)) (SLit 1)) RG9 eq_refl U12_d
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. change (8 * Z.of_nat (N.to_nat 4%N)) with 32.
    exact (mw_u_add1 E_d (SExt true 32 (SOff 38 0)) (TW.s32_at Bw 65312) (mw_sext_atom E_d 38 Bw 65312 A_d_38)). }
  pose proof (st_ok_pi_region_nth E_d _ (restrict (w_H W) ms_d) 4 _ HS eq_refl) as RG4.
  cbn [ms_mem restrict] in RG4.
  assert (VM12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_d) (TA_M + 12 + Z.of_nat j) = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_d W (ms_mem ms_d) _ 249%nat TA_M 12 4%N (SLit 1) RG4 eq_refl U8_d
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (HTW : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms_d)) (TW.upd (TW.upd (mwm_W Bw) 65312 (TW.put 4 (TW.s32_at Bw 65312 + 1))) 12 (TW.put 4 1))).
  { apply (mw_fin_rd _ (aview segs (w_H W) memc) (aview segs (w_H W) (ms_mem ms_d)) _ (mw_world6 W memc (ms_mem ms_d) Bw _ (TW.s32_at Bw 65312 + 1) (mw_world4 W memc (ms_mem ms_d) Bw Htw VOW196 VM16 VM40 VM88) VOW0 VM12)).
    intros x Hx Hni. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    destruct (Classical_Prop.classic (mw_wins (spZ regs) x)) as [Hw | Hw].
    - destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]].
      + exfalso. unfold MWAKE_STK, MWAKE_FRAME in Hw. lia.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 12) (TA_M + 12 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 16) (TA_M + 16 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 40) (TA_M + 40 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 88) (TA_M + 88 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 0) (TA_OW + 0 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 196) (TA_OW + 196 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
    - apply KW7; [lia | exact Hw]. }
  mw_regv HS (Z_to_bv 5 1) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite HE_d by lia;
          rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  mw_regv HS (Z_to_bv 5 10) (w64 (0)) RF10
    ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mw_u64; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms_d)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E_d _ ms_d regs (mw_ex Bw) HS).
    - apply mw_agree; [intros n Hn; rewrite HE_d by lia; reflexivity | reflexivity].
    - vm_compute. reflexivity. }
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ mw_Zs (spZ regs) a ->
    aview segs (w_H W) (ms_mem ms_d) a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; apply KW7; [exact Ha | intros Hc0; exact (Hn (mw_wins_Zs _ a Hc0))]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  exact (mw_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (TW.upd (TW.upd (mwm_W Bw) 65312 (TW.put 4 (TW.s32_at Bw 65312 + 1))) 12 (TW.put 4 1)) (0)
           (ms_regs ms_d) (ms_mem ms_d) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GA7
           HTW HPF RF1 RF10 matF).
  }
  { (* OW.n <= 15: the transition record at OW.t[OW.n] *)
  cbn [branch_taken] in Hc.
  rewrite (mw_sext_atom E_r5 38 Bw 65312 A_r5_38) in Hc.
  change (sv_denot E_r5 (SLit 15)) with (Z_to_bv 64 15) in Hc.
  rewrite (mw_lts_s32 15 (TW.s32_at Bw 65312) ltac:(lia) ltac:(lia)) in Hc.
  rewrite Hc in Hm. cbv iota in Hm. destruct (mw_some_inv _ _ _ _ Hm) as [HB Hr]. subst Bw'. subst r.
  apply Z.ltb_ge in Hc.
  rewrite (mw_fin_rec_m Bw HLB).
  assert (HN : TW.s32_at Bw 65312 = 0 \/ TW.s32_at Bw 65312 = 1 \/ TW.s32_at Bw 65312 = 2 \/
    TW.s32_at Bw 65312 = 3 \/ TW.s32_at Bw 65312 = 4 \/ TW.s32_at Bw 65312 = 5 \/
    TW.s32_at Bw 65312 = 6 \/ TW.s32_at Bw 65312 = 7 \/ TW.s32_at Bw 65312 = 8 \/
    TW.s32_at Bw 65312 = 9 \/ TW.s32_at Bw 65312 = 10 \/ TW.s32_at Bw 65312 = 11 \/
    TW.s32_at Bw 65312 = 12 \/ TW.s32_at Bw 65312 = 13 \/ TW.s32_at Bw 65312 = 14 \/
    TW.s32_at Bw 65312 = 15) by lia.
  destruct HN as [En|[En|[En|[En|[En|[En|[En|[En|[En|[En|[En|[En|[En|[En|[En|En]]]]]]]]]]]]]]].
  { (* arm 0 *)
  (* OW.n = 0 *)
  rewrite !En.
  mw_regv HS (Z_to_bv 5 14) (Z_to_bv 64 0) HN14
    ltac:(rewrite (mw_sext_atom E_r5 38 Bw 65312 A_r5_38), En; reflexivity).
  apply (fun HQ => st_ok_pi_pin_reg' E_r5 _ (restrict (w_H W) ms_r5) (Z_to_bv 5 14) 0 HQ HN14 ltac:(reflexivity)) in HS.
  assert (RTOK : region_ok segs E_r5 (ms_mem (restrict (w_H W) ms_r5)) (Ro_t 0)).
  { unfold Ro_t, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict A_OBJ].
    change (A_OBJ 12) with 253%nat. rewrite U12_r5. split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw).
    apply mw_inG_OW. unfold TW.SZ_OW. lia. }
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ssx _ => assert (RTD : all_disjoint E_r5 (Ro_t 0) (ss_mem ssx))
  end.
  { clear - Hsp Usp_r5 U8_r5 U12_r5 U27_r5 U1_r5 U93_r5.
    cbn [ss_mem all_disjoint add_cond]. unfold Ro_t, extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (A_OBJ 12) with 253%nat.
    rewrite ?Usp_r5, ?U8_r5, ?U12_r5, ?U27_r5, ?U1_r5, ?U93_r5.
    unfold TA_M, TA_OW, TA_g_now, FCells.GOT_CELL_K, FCells.CELL_K.
    repeat split; first [exact I | lia]. }
  apply (fun HQ => st_ok_pi_add_region E_r5 _ _ (Ro_t 0) HQ ltac:(vm_compute; reflexivity) RTOK RTD) in HS.
  clear RTOK HN14.
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r5 U8_r5 U12_r5 U12_r5. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KWk : forall a, 0 <= a < 2 ^ 64 -> ~ mw_winsk (spZ regs) 0 a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity;
      [| exact (KW6 a Ha ltac:(intros Hc0; apply Hn; left; exact Hc0))].
    eapply (kept_of_frame _ _ _ _ _ (mw_winsk (spZ regs) 0)).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r5, ?U8_r5, ?U12_r5 in Hx;
        unfold mw_winsk, mw_wins;
        first [ lia | left; left; lia | left; right; left; lia | left; right; right; left; lia
              | left; right; right; right; left; lia | left; right; right; right; right; left; lia
              | left; right; right; right; right; right; left; lia
              | left; right; right; right; right; right; right; lia | right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GAk : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA6 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_k := mf) in *; set (E_k := EF) in HS, SHOK, HEI
  end.
  assert (HE_k : forall n, (n < 1024)%nat -> ew E_k n = ew E0 n)
    by (intros n Hn; unfold E_k; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r5; lia]).
  assert (A_k_35 : ew E_k 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A35_0).
  assert (A_k_36 : ew E_k 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A36_0).
  assert (A_k_37 : ew E_k 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A37_0).
  assert (A_k_38 : ew E_k 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A38_0).
  assert (A_k_39 : ew E_k 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A39_0).
  assert (A_k_40 : ew E_k 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A40_0).
  assert (A_k_41 : ew E_k 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A41_0).
  assert (A_k_33 : ew E_k 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A33_0).
  assert (A_k_34 : ew E_k 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A34_0).
  assert (U8_k : bv_unsigned (ew E_k 249%nat) = TA_M) by (rewrite HE_k by lia; exact U8L).
  assert (U12_k : bv_unsigned (ew E_k 253%nat) = TA_OW) by (rewrite HE_k by lia; exact U12L).
  assert (U27_k : bv_unsigned (ew E_k 268%nat) = TA_g_now) by (rewrite HE_k by lia; exact U27L).
  assert (U1_k : bv_unsigned (ew E_k 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_k by lia; exact U1L).
  assert (U93_k : bv_unsigned (ew E_k 334%nat) = FCells.CELL_K) by (rewrite HE_k by lia; exact U93L).
  assert (Usp_k : bv_unsigned (ew E_k 2) = spZ regs) by (rewrite HE_k by lia; exact Usp0).
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 0 _ HS eq_refl) as RG0.
  cbn [ms_mem restrict] in RG0.
  assert (Vt4 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 4 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 4 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (Vt8 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 8 + Z.of_nat j)
      = Some (YO0f.le_byte (TW.s32_at Bw 12) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 8 4%N (SExt true 32 (SOff 35 0)) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. unfold U. rewrite (mw_sext_atom E_k 35 Bw 12 A_k_35), mw_u64.
    change (8 * Z.of_nat (N.to_nat 4%N)) with 32. apply mw_mod64. lia. }
  assert (Vt12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 12 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 12 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 11 _ HS eq_refl) as RG11.
  cbn [ms_mem restrict] in RG11.
  assert (VOW196 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 196 + Z.of_nat j) = Some (YO0f.le_byte (TW.s32_at Bw 65508 + 1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 196 4%N (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 1)) RG11 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. change (8 * Z.of_nat (N.to_nat 4%N)) with 32.
    exact (mw_u_add1 E_k (SExt true 32 (SOff 37 0)) (TW.s32_at Bw 65508) (mw_sext_atom E_k 37 Bw 65508 A_k_37)). }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 6 _ HS eq_refl) as RG6.
  cbn [ms_mem restrict] in RG6.
  assert (VM16 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 16 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 16 8%N (SLit 0) RG6 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 8 _ HS eq_refl) as RG8.
  cbn [ms_mem restrict] in RG8.
  assert (VM40 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 40 + Z.of_nat j) = Some (YO0f.le_byte (TW.u_at Bw 65000 8) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 40 8%N (SOff 39 0) RG8 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. rewrite (U_atom E_k 39 (TW.u_at Bw 65000 8) A_k_39 ltac:(pose proof (TWL.u_at_range Bw 65000 8) as HR;
      cbn [Z.of_nat] in HR; lia)). reflexivity. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 9 _ HS eq_refl) as RG9.
  cbn [ms_mem restrict] in RG9.
  assert (VM88 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 88 4%N (SLit 0) RG9 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 10 _ HS eq_refl) as RG10.
  cbn [ms_mem restrict] in RG10.
  assert (VOW0 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 0 + Z.of_nat j) = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 0 4%N (SLit 1) RG10 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 5 _ HS eq_refl) as RG5.
  cbn [ms_mem restrict] in RG5.
  assert (VM12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 12 + Z.of_nat j) = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 12 4%N (SLit 1) RG5 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (HTW : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms_k)) (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 0) (TW.put 4 1))
             (65320 + 12 * 0) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 0) (TW.put 4 1))
        65312 (TW.put 4 1)) 12 (TW.put 4 1))).
  { apply (mw_fin_rd _ (aview segs (w_H W) memc) (aview segs (w_H W) (ms_mem ms_k)) _ (mw_world9 W memc (ms_mem ms_k) Bw _ 0 1 ltac:(lia)
      (mw_world4 W memc (ms_mem ms_k) Bw Htw VOW196 VM16 VM40 VM88) Vt4 Vt8 Vt12 VOW0 VM12)).
    intros x Hx Hni. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    destruct (Classical_Prop.classic (mw_winsk (spZ regs) 0 x)) as [Hw | Hw].
    - destruct Hw as [[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]] | Hw].
      + exfalso. unfold MWAKE_STK, MWAKE_FRAME in Hw. lia.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 12) (TA_M + 12 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 16) (TA_M + 16 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 40) (TA_M + 40 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 88) (TA_M + 88 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 0) (TA_OW + 0 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 196) (TA_OW + 196 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. destruct (Z_lt_le_dec x (TA_OW + (8 + 12 * 0))) as [D1|D1]; [| destruct (Z_lt_le_dec x (TA_OW + (12 + 12 * 0))) as [D2|D2]].
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (4 + 12 * 0)) (TA_OW + (4 + 12 * 0) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (8 + 12 * 0)) (TA_OW + (8 + 12 * 0) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (12 + 12 * 0)) (TA_OW + (12 + 12 * 0) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
    - apply KWk; [lia | exact Hw]. }
  mw_regv HS (Z_to_bv 5 1) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite HE_k by lia;
          rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  mw_regv HS (Z_to_bv 5 10) (w64 0) RF10
    ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mw_u64; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms_k)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E_k _ ms_k regs (mw_ex Bw) HS).
    - apply mw_agree; [intros n Hn; rewrite HE_k by lia; reflexivity | reflexivity].
    - vm_compute. reflexivity. }
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ mw_Zs (spZ regs) a ->
    aview segs (w_H W) (ms_mem ms_k) a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; apply KWk; [exact Ha
        | intros Hc0; exact (Hn (mw_winsk_Zs _ 0 a ltac:(lia) Hc0))]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  exact (mw_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 0) (TW.put 4 1))
             (65320 + 12 * 0) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 0) (TW.put 4 1))
        65312 (TW.put 4 1)) 12 (TW.put 4 1)) 0
           (ms_regs ms_k) (ms_mem ms_k) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GAk
           HTW HPF RF1 RF10 matF).
  }
  { (* arm 1 *)
  (* OW.n = 1 *)
  rewrite !En.
  mw_regv HS (Z_to_bv 5 14) (Z_to_bv 64 1) HN14
    ltac:(rewrite (mw_sext_atom E_r5 38 Bw 65312 A_r5_38), En; reflexivity).
  apply (fun HQ => st_ok_pi_pin_reg' E_r5 _ (restrict (w_H W) ms_r5) (Z_to_bv 5 14) 1 HQ HN14 ltac:(reflexivity)) in HS.
  assert (RTOK : region_ok segs E_r5 (ms_mem (restrict (w_H W) ms_r5)) (Ro_t 1)).
  { unfold Ro_t, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict A_OBJ].
    change (A_OBJ 12) with 253%nat. rewrite U12_r5. split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw).
    apply mw_inG_OW. unfold TW.SZ_OW. lia. }
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ssx _ => assert (RTD : all_disjoint E_r5 (Ro_t 1) (ss_mem ssx))
  end.
  { clear - Hsp Usp_r5 U8_r5 U12_r5 U27_r5 U1_r5 U93_r5.
    cbn [ss_mem all_disjoint add_cond]. unfold Ro_t, extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (A_OBJ 12) with 253%nat.
    rewrite ?Usp_r5, ?U8_r5, ?U12_r5, ?U27_r5, ?U1_r5, ?U93_r5.
    unfold TA_M, TA_OW, TA_g_now, FCells.GOT_CELL_K, FCells.CELL_K.
    repeat split; first [exact I | lia]. }
  apply (fun HQ => st_ok_pi_add_region E_r5 _ _ (Ro_t 1) HQ ltac:(vm_compute; reflexivity) RTOK RTD) in HS.
  clear RTOK HN14.
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r5 U8_r5 U12_r5 U12_r5. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KWk : forall a, 0 <= a < 2 ^ 64 -> ~ mw_winsk (spZ regs) 1 a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity;
      [| exact (KW6 a Ha ltac:(intros Hc0; apply Hn; left; exact Hc0))].
    eapply (kept_of_frame _ _ _ _ _ (mw_winsk (spZ regs) 1)).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r5, ?U8_r5, ?U12_r5 in Hx;
        unfold mw_winsk, mw_wins;
        first [ lia | left; left; lia | left; right; left; lia | left; right; right; left; lia
              | left; right; right; right; left; lia | left; right; right; right; right; left; lia
              | left; right; right; right; right; right; left; lia
              | left; right; right; right; right; right; right; lia | right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GAk : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA6 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_k := mf) in *; set (E_k := EF) in HS, SHOK, HEI
  end.
  assert (HE_k : forall n, (n < 1024)%nat -> ew E_k n = ew E0 n)
    by (intros n Hn; unfold E_k; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r5; lia]).
  assert (A_k_35 : ew E_k 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A35_0).
  assert (A_k_36 : ew E_k 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A36_0).
  assert (A_k_37 : ew E_k 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A37_0).
  assert (A_k_38 : ew E_k 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A38_0).
  assert (A_k_39 : ew E_k 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A39_0).
  assert (A_k_40 : ew E_k 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A40_0).
  assert (A_k_41 : ew E_k 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A41_0).
  assert (A_k_33 : ew E_k 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A33_0).
  assert (A_k_34 : ew E_k 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A34_0).
  assert (U8_k : bv_unsigned (ew E_k 249%nat) = TA_M) by (rewrite HE_k by lia; exact U8L).
  assert (U12_k : bv_unsigned (ew E_k 253%nat) = TA_OW) by (rewrite HE_k by lia; exact U12L).
  assert (U27_k : bv_unsigned (ew E_k 268%nat) = TA_g_now) by (rewrite HE_k by lia; exact U27L).
  assert (U1_k : bv_unsigned (ew E_k 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_k by lia; exact U1L).
  assert (U93_k : bv_unsigned (ew E_k 334%nat) = FCells.CELL_K) by (rewrite HE_k by lia; exact U93L).
  assert (Usp_k : bv_unsigned (ew E_k 2) = spZ regs) by (rewrite HE_k by lia; exact Usp0).
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 0 _ HS eq_refl) as RG0.
  cbn [ms_mem restrict] in RG0.
  assert (Vt4 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 16 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 16 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (Vt8 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 20 + Z.of_nat j)
      = Some (YO0f.le_byte (TW.s32_at Bw 12) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 20 4%N (SExt true 32 (SOff 35 0)) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. unfold U. rewrite (mw_sext_atom E_k 35 Bw 12 A_k_35), mw_u64.
    change (8 * Z.of_nat (N.to_nat 4%N)) with 32. apply mw_mod64. lia. }
  assert (Vt12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 24 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 24 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 11 _ HS eq_refl) as RG11.
  cbn [ms_mem restrict] in RG11.
  assert (VOW196 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 196 + Z.of_nat j) = Some (YO0f.le_byte (TW.s32_at Bw 65508 + 1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 196 4%N (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 1)) RG11 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. change (8 * Z.of_nat (N.to_nat 4%N)) with 32.
    exact (mw_u_add1 E_k (SExt true 32 (SOff 37 0)) (TW.s32_at Bw 65508) (mw_sext_atom E_k 37 Bw 65508 A_k_37)). }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 6 _ HS eq_refl) as RG6.
  cbn [ms_mem restrict] in RG6.
  assert (VM16 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 16 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 16 8%N (SLit 0) RG6 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 8 _ HS eq_refl) as RG8.
  cbn [ms_mem restrict] in RG8.
  assert (VM40 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 40 + Z.of_nat j) = Some (YO0f.le_byte (TW.u_at Bw 65000 8) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 40 8%N (SOff 39 0) RG8 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. rewrite (U_atom E_k 39 (TW.u_at Bw 65000 8) A_k_39 ltac:(pose proof (TWL.u_at_range Bw 65000 8) as HR;
      cbn [Z.of_nat] in HR; lia)). reflexivity. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 9 _ HS eq_refl) as RG9.
  cbn [ms_mem restrict] in RG9.
  assert (VM88 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 88 4%N (SLit 0) RG9 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 10 _ HS eq_refl) as RG10.
  cbn [ms_mem restrict] in RG10.
  assert (VOW0 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 0 + Z.of_nat j) = Some (YO0f.le_byte (2) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 0 4%N (SLit 2) RG10 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 5 _ HS eq_refl) as RG5.
  cbn [ms_mem restrict] in RG5.
  assert (VM12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 12 + Z.of_nat j) = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 12 4%N (SLit 1) RG5 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (HTW : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms_k)) (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 1) (TW.put 4 1))
             (65320 + 12 * 1) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 1) (TW.put 4 1))
        65312 (TW.put 4 2)) 12 (TW.put 4 1))).
  { apply (mw_fin_rd _ (aview segs (w_H W) memc) (aview segs (w_H W) (ms_mem ms_k)) _ (mw_world9 W memc (ms_mem ms_k) Bw _ 1 2 ltac:(lia)
      (mw_world4 W memc (ms_mem ms_k) Bw Htw VOW196 VM16 VM40 VM88) Vt4 Vt8 Vt12 VOW0 VM12)).
    intros x Hx Hni. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    destruct (Classical_Prop.classic (mw_winsk (spZ regs) 1 x)) as [Hw | Hw].
    - destruct Hw as [[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]] | Hw].
      + exfalso. unfold MWAKE_STK, MWAKE_FRAME in Hw. lia.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 12) (TA_M + 12 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 16) (TA_M + 16 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 40) (TA_M + 40 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 88) (TA_M + 88 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 0) (TA_OW + 0 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 196) (TA_OW + 196 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. destruct (Z_lt_le_dec x (TA_OW + (8 + 12 * 1))) as [D1|D1]; [| destruct (Z_lt_le_dec x (TA_OW + (12 + 12 * 1))) as [D2|D2]].
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (4 + 12 * 1)) (TA_OW + (4 + 12 * 1) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (8 + 12 * 1)) (TA_OW + (8 + 12 * 1) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (12 + 12 * 1)) (TA_OW + (12 + 12 * 1) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
    - apply KWk; [lia | exact Hw]. }
  mw_regv HS (Z_to_bv 5 1) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite HE_k by lia;
          rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  mw_regv HS (Z_to_bv 5 10) (w64 0) RF10
    ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mw_u64; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms_k)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E_k _ ms_k regs (mw_ex Bw) HS).
    - apply mw_agree; [intros n Hn; rewrite HE_k by lia; reflexivity | reflexivity].
    - vm_compute. reflexivity. }
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ mw_Zs (spZ regs) a ->
    aview segs (w_H W) (ms_mem ms_k) a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; apply KWk; [exact Ha
        | intros Hc0; exact (Hn (mw_winsk_Zs _ 1 a ltac:(lia) Hc0))]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  exact (mw_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 1) (TW.put 4 1))
             (65320 + 12 * 1) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 1) (TW.put 4 1))
        65312 (TW.put 4 2)) 12 (TW.put 4 1)) 0
           (ms_regs ms_k) (ms_mem ms_k) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GAk
           HTW HPF RF1 RF10 matF).
  }
  { (* arm 2 *)
  (* OW.n = 2 *)
  rewrite !En.
  mw_regv HS (Z_to_bv 5 14) (Z_to_bv 64 2) HN14
    ltac:(rewrite (mw_sext_atom E_r5 38 Bw 65312 A_r5_38), En; reflexivity).
  apply (fun HQ => st_ok_pi_pin_reg' E_r5 _ (restrict (w_H W) ms_r5) (Z_to_bv 5 14) 2 HQ HN14 ltac:(reflexivity)) in HS.
  assert (RTOK : region_ok segs E_r5 (ms_mem (restrict (w_H W) ms_r5)) (Ro_t 2)).
  { unfold Ro_t, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict A_OBJ].
    change (A_OBJ 12) with 253%nat. rewrite U12_r5. split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw).
    apply mw_inG_OW. unfold TW.SZ_OW. lia. }
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ssx _ => assert (RTD : all_disjoint E_r5 (Ro_t 2) (ss_mem ssx))
  end.
  { clear - Hsp Usp_r5 U8_r5 U12_r5 U27_r5 U1_r5 U93_r5.
    cbn [ss_mem all_disjoint add_cond]. unfold Ro_t, extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (A_OBJ 12) with 253%nat.
    rewrite ?Usp_r5, ?U8_r5, ?U12_r5, ?U27_r5, ?U1_r5, ?U93_r5.
    unfold TA_M, TA_OW, TA_g_now, FCells.GOT_CELL_K, FCells.CELL_K.
    repeat split; first [exact I | lia]. }
  apply (fun HQ => st_ok_pi_add_region E_r5 _ _ (Ro_t 2) HQ ltac:(vm_compute; reflexivity) RTOK RTD) in HS.
  clear RTOK HN14.
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r5 U8_r5 U12_r5 U12_r5. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KWk : forall a, 0 <= a < 2 ^ 64 -> ~ mw_winsk (spZ regs) 2 a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity;
      [| exact (KW6 a Ha ltac:(intros Hc0; apply Hn; left; exact Hc0))].
    eapply (kept_of_frame _ _ _ _ _ (mw_winsk (spZ regs) 2)).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r5, ?U8_r5, ?U12_r5 in Hx;
        unfold mw_winsk, mw_wins;
        first [ lia | left; left; lia | left; right; left; lia | left; right; right; left; lia
              | left; right; right; right; left; lia | left; right; right; right; right; left; lia
              | left; right; right; right; right; right; left; lia
              | left; right; right; right; right; right; right; lia | right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GAk : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA6 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_k := mf) in *; set (E_k := EF) in HS, SHOK, HEI
  end.
  assert (HE_k : forall n, (n < 1024)%nat -> ew E_k n = ew E0 n)
    by (intros n Hn; unfold E_k; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r5; lia]).
  assert (A_k_35 : ew E_k 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A35_0).
  assert (A_k_36 : ew E_k 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A36_0).
  assert (A_k_37 : ew E_k 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A37_0).
  assert (A_k_38 : ew E_k 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A38_0).
  assert (A_k_39 : ew E_k 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A39_0).
  assert (A_k_40 : ew E_k 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A40_0).
  assert (A_k_41 : ew E_k 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A41_0).
  assert (A_k_33 : ew E_k 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A33_0).
  assert (A_k_34 : ew E_k 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A34_0).
  assert (U8_k : bv_unsigned (ew E_k 249%nat) = TA_M) by (rewrite HE_k by lia; exact U8L).
  assert (U12_k : bv_unsigned (ew E_k 253%nat) = TA_OW) by (rewrite HE_k by lia; exact U12L).
  assert (U27_k : bv_unsigned (ew E_k 268%nat) = TA_g_now) by (rewrite HE_k by lia; exact U27L).
  assert (U1_k : bv_unsigned (ew E_k 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_k by lia; exact U1L).
  assert (U93_k : bv_unsigned (ew E_k 334%nat) = FCells.CELL_K) by (rewrite HE_k by lia; exact U93L).
  assert (Usp_k : bv_unsigned (ew E_k 2) = spZ regs) by (rewrite HE_k by lia; exact Usp0).
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 0 _ HS eq_refl) as RG0.
  cbn [ms_mem restrict] in RG0.
  assert (Vt4 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 28 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 28 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (Vt8 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 32 + Z.of_nat j)
      = Some (YO0f.le_byte (TW.s32_at Bw 12) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 32 4%N (SExt true 32 (SOff 35 0)) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. unfold U. rewrite (mw_sext_atom E_k 35 Bw 12 A_k_35), mw_u64.
    change (8 * Z.of_nat (N.to_nat 4%N)) with 32. apply mw_mod64. lia. }
  assert (Vt12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 36 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 36 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 11 _ HS eq_refl) as RG11.
  cbn [ms_mem restrict] in RG11.
  assert (VOW196 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 196 + Z.of_nat j) = Some (YO0f.le_byte (TW.s32_at Bw 65508 + 1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 196 4%N (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 1)) RG11 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. change (8 * Z.of_nat (N.to_nat 4%N)) with 32.
    exact (mw_u_add1 E_k (SExt true 32 (SOff 37 0)) (TW.s32_at Bw 65508) (mw_sext_atom E_k 37 Bw 65508 A_k_37)). }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 6 _ HS eq_refl) as RG6.
  cbn [ms_mem restrict] in RG6.
  assert (VM16 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 16 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 16 8%N (SLit 0) RG6 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 8 _ HS eq_refl) as RG8.
  cbn [ms_mem restrict] in RG8.
  assert (VM40 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 40 + Z.of_nat j) = Some (YO0f.le_byte (TW.u_at Bw 65000 8) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 40 8%N (SOff 39 0) RG8 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. rewrite (U_atom E_k 39 (TW.u_at Bw 65000 8) A_k_39 ltac:(pose proof (TWL.u_at_range Bw 65000 8) as HR;
      cbn [Z.of_nat] in HR; lia)). reflexivity. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 9 _ HS eq_refl) as RG9.
  cbn [ms_mem restrict] in RG9.
  assert (VM88 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 88 4%N (SLit 0) RG9 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 10 _ HS eq_refl) as RG10.
  cbn [ms_mem restrict] in RG10.
  assert (VOW0 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 0 + Z.of_nat j) = Some (YO0f.le_byte (3) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 0 4%N (SLit 3) RG10 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 5 _ HS eq_refl) as RG5.
  cbn [ms_mem restrict] in RG5.
  assert (VM12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 12 + Z.of_nat j) = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 12 4%N (SLit 1) RG5 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (HTW : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms_k)) (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 2) (TW.put 4 1))
             (65320 + 12 * 2) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 2) (TW.put 4 1))
        65312 (TW.put 4 3)) 12 (TW.put 4 1))).
  { apply (mw_fin_rd _ (aview segs (w_H W) memc) (aview segs (w_H W) (ms_mem ms_k)) _ (mw_world9 W memc (ms_mem ms_k) Bw _ 2 3 ltac:(lia)
      (mw_world4 W memc (ms_mem ms_k) Bw Htw VOW196 VM16 VM40 VM88) Vt4 Vt8 Vt12 VOW0 VM12)).
    intros x Hx Hni. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    destruct (Classical_Prop.classic (mw_winsk (spZ regs) 2 x)) as [Hw | Hw].
    - destruct Hw as [[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]] | Hw].
      + exfalso. unfold MWAKE_STK, MWAKE_FRAME in Hw. lia.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 12) (TA_M + 12 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 16) (TA_M + 16 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 40) (TA_M + 40 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 88) (TA_M + 88 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 0) (TA_OW + 0 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 196) (TA_OW + 196 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. destruct (Z_lt_le_dec x (TA_OW + (8 + 12 * 2))) as [D1|D1]; [| destruct (Z_lt_le_dec x (TA_OW + (12 + 12 * 2))) as [D2|D2]].
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (4 + 12 * 2)) (TA_OW + (4 + 12 * 2) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (8 + 12 * 2)) (TA_OW + (8 + 12 * 2) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (12 + 12 * 2)) (TA_OW + (12 + 12 * 2) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
    - apply KWk; [lia | exact Hw]. }
  mw_regv HS (Z_to_bv 5 1) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite HE_k by lia;
          rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  mw_regv HS (Z_to_bv 5 10) (w64 0) RF10
    ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mw_u64; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms_k)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E_k _ ms_k regs (mw_ex Bw) HS).
    - apply mw_agree; [intros n Hn; rewrite HE_k by lia; reflexivity | reflexivity].
    - vm_compute. reflexivity. }
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ mw_Zs (spZ regs) a ->
    aview segs (w_H W) (ms_mem ms_k) a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; apply KWk; [exact Ha
        | intros Hc0; exact (Hn (mw_winsk_Zs _ 2 a ltac:(lia) Hc0))]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  exact (mw_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 2) (TW.put 4 1))
             (65320 + 12 * 2) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 2) (TW.put 4 1))
        65312 (TW.put 4 3)) 12 (TW.put 4 1)) 0
           (ms_regs ms_k) (ms_mem ms_k) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GAk
           HTW HPF RF1 RF10 matF).
  }
  { (* arm 3 *)
  (* OW.n = 3 *)
  rewrite !En.
  mw_regv HS (Z_to_bv 5 14) (Z_to_bv 64 3) HN14
    ltac:(rewrite (mw_sext_atom E_r5 38 Bw 65312 A_r5_38), En; reflexivity).
  apply (fun HQ => st_ok_pi_pin_reg' E_r5 _ (restrict (w_H W) ms_r5) (Z_to_bv 5 14) 3 HQ HN14 ltac:(reflexivity)) in HS.
  assert (RTOK : region_ok segs E_r5 (ms_mem (restrict (w_H W) ms_r5)) (Ro_t 3)).
  { unfold Ro_t, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict A_OBJ].
    change (A_OBJ 12) with 253%nat. rewrite U12_r5. split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw).
    apply mw_inG_OW. unfold TW.SZ_OW. lia. }
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ssx _ => assert (RTD : all_disjoint E_r5 (Ro_t 3) (ss_mem ssx))
  end.
  { clear - Hsp Usp_r5 U8_r5 U12_r5 U27_r5 U1_r5 U93_r5.
    cbn [ss_mem all_disjoint add_cond]. unfold Ro_t, extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (A_OBJ 12) with 253%nat.
    rewrite ?Usp_r5, ?U8_r5, ?U12_r5, ?U27_r5, ?U1_r5, ?U93_r5.
    unfold TA_M, TA_OW, TA_g_now, FCells.GOT_CELL_K, FCells.CELL_K.
    repeat split; first [exact I | lia]. }
  apply (fun HQ => st_ok_pi_add_region E_r5 _ _ (Ro_t 3) HQ ltac:(vm_compute; reflexivity) RTOK RTD) in HS.
  clear RTOK HN14.
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r5 U8_r5 U12_r5 U12_r5. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KWk : forall a, 0 <= a < 2 ^ 64 -> ~ mw_winsk (spZ regs) 3 a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity;
      [| exact (KW6 a Ha ltac:(intros Hc0; apply Hn; left; exact Hc0))].
    eapply (kept_of_frame _ _ _ _ _ (mw_winsk (spZ regs) 3)).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r5, ?U8_r5, ?U12_r5 in Hx;
        unfold mw_winsk, mw_wins;
        first [ lia | left; left; lia | left; right; left; lia | left; right; right; left; lia
              | left; right; right; right; left; lia | left; right; right; right; right; left; lia
              | left; right; right; right; right; right; left; lia
              | left; right; right; right; right; right; right; lia | right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GAk : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA6 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_k := mf) in *; set (E_k := EF) in HS, SHOK, HEI
  end.
  assert (HE_k : forall n, (n < 1024)%nat -> ew E_k n = ew E0 n)
    by (intros n Hn; unfold E_k; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r5; lia]).
  assert (A_k_35 : ew E_k 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A35_0).
  assert (A_k_36 : ew E_k 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A36_0).
  assert (A_k_37 : ew E_k 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A37_0).
  assert (A_k_38 : ew E_k 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A38_0).
  assert (A_k_39 : ew E_k 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A39_0).
  assert (A_k_40 : ew E_k 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A40_0).
  assert (A_k_41 : ew E_k 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A41_0).
  assert (A_k_33 : ew E_k 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A33_0).
  assert (A_k_34 : ew E_k 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A34_0).
  assert (U8_k : bv_unsigned (ew E_k 249%nat) = TA_M) by (rewrite HE_k by lia; exact U8L).
  assert (U12_k : bv_unsigned (ew E_k 253%nat) = TA_OW) by (rewrite HE_k by lia; exact U12L).
  assert (U27_k : bv_unsigned (ew E_k 268%nat) = TA_g_now) by (rewrite HE_k by lia; exact U27L).
  assert (U1_k : bv_unsigned (ew E_k 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_k by lia; exact U1L).
  assert (U93_k : bv_unsigned (ew E_k 334%nat) = FCells.CELL_K) by (rewrite HE_k by lia; exact U93L).
  assert (Usp_k : bv_unsigned (ew E_k 2) = spZ regs) by (rewrite HE_k by lia; exact Usp0).
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 0 _ HS eq_refl) as RG0.
  cbn [ms_mem restrict] in RG0.
  assert (Vt4 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 40 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 40 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (Vt8 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 44 + Z.of_nat j)
      = Some (YO0f.le_byte (TW.s32_at Bw 12) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 44 4%N (SExt true 32 (SOff 35 0)) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. unfold U. rewrite (mw_sext_atom E_k 35 Bw 12 A_k_35), mw_u64.
    change (8 * Z.of_nat (N.to_nat 4%N)) with 32. apply mw_mod64. lia. }
  assert (Vt12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 48 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 48 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 11 _ HS eq_refl) as RG11.
  cbn [ms_mem restrict] in RG11.
  assert (VOW196 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 196 + Z.of_nat j) = Some (YO0f.le_byte (TW.s32_at Bw 65508 + 1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 196 4%N (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 1)) RG11 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. change (8 * Z.of_nat (N.to_nat 4%N)) with 32.
    exact (mw_u_add1 E_k (SExt true 32 (SOff 37 0)) (TW.s32_at Bw 65508) (mw_sext_atom E_k 37 Bw 65508 A_k_37)). }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 6 _ HS eq_refl) as RG6.
  cbn [ms_mem restrict] in RG6.
  assert (VM16 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 16 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 16 8%N (SLit 0) RG6 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 8 _ HS eq_refl) as RG8.
  cbn [ms_mem restrict] in RG8.
  assert (VM40 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 40 + Z.of_nat j) = Some (YO0f.le_byte (TW.u_at Bw 65000 8) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 40 8%N (SOff 39 0) RG8 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. rewrite (U_atom E_k 39 (TW.u_at Bw 65000 8) A_k_39 ltac:(pose proof (TWL.u_at_range Bw 65000 8) as HR;
      cbn [Z.of_nat] in HR; lia)). reflexivity. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 9 _ HS eq_refl) as RG9.
  cbn [ms_mem restrict] in RG9.
  assert (VM88 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 88 4%N (SLit 0) RG9 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 10 _ HS eq_refl) as RG10.
  cbn [ms_mem restrict] in RG10.
  assert (VOW0 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 0 + Z.of_nat j) = Some (YO0f.le_byte (4) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 0 4%N (SLit 4) RG10 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 5 _ HS eq_refl) as RG5.
  cbn [ms_mem restrict] in RG5.
  assert (VM12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 12 + Z.of_nat j) = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 12 4%N (SLit 1) RG5 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (HTW : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms_k)) (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 3) (TW.put 4 1))
             (65320 + 12 * 3) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 3) (TW.put 4 1))
        65312 (TW.put 4 4)) 12 (TW.put 4 1))).
  { apply (mw_fin_rd _ (aview segs (w_H W) memc) (aview segs (w_H W) (ms_mem ms_k)) _ (mw_world9 W memc (ms_mem ms_k) Bw _ 3 4 ltac:(lia)
      (mw_world4 W memc (ms_mem ms_k) Bw Htw VOW196 VM16 VM40 VM88) Vt4 Vt8 Vt12 VOW0 VM12)).
    intros x Hx Hni. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    destruct (Classical_Prop.classic (mw_winsk (spZ regs) 3 x)) as [Hw | Hw].
    - destruct Hw as [[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]] | Hw].
      + exfalso. unfold MWAKE_STK, MWAKE_FRAME in Hw. lia.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 12) (TA_M + 12 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 16) (TA_M + 16 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 40) (TA_M + 40 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 88) (TA_M + 88 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 0) (TA_OW + 0 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 196) (TA_OW + 196 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. destruct (Z_lt_le_dec x (TA_OW + (8 + 12 * 3))) as [D1|D1]; [| destruct (Z_lt_le_dec x (TA_OW + (12 + 12 * 3))) as [D2|D2]].
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (4 + 12 * 3)) (TA_OW + (4 + 12 * 3) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (8 + 12 * 3)) (TA_OW + (8 + 12 * 3) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (12 + 12 * 3)) (TA_OW + (12 + 12 * 3) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
    - apply KWk; [lia | exact Hw]. }
  mw_regv HS (Z_to_bv 5 1) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite HE_k by lia;
          rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  mw_regv HS (Z_to_bv 5 10) (w64 0) RF10
    ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mw_u64; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms_k)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E_k _ ms_k regs (mw_ex Bw) HS).
    - apply mw_agree; [intros n Hn; rewrite HE_k by lia; reflexivity | reflexivity].
    - vm_compute. reflexivity. }
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ mw_Zs (spZ regs) a ->
    aview segs (w_H W) (ms_mem ms_k) a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; apply KWk; [exact Ha
        | intros Hc0; exact (Hn (mw_winsk_Zs _ 3 a ltac:(lia) Hc0))]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  exact (mw_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 3) (TW.put 4 1))
             (65320 + 12 * 3) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 3) (TW.put 4 1))
        65312 (TW.put 4 4)) 12 (TW.put 4 1)) 0
           (ms_regs ms_k) (ms_mem ms_k) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GAk
           HTW HPF RF1 RF10 matF).
  }
  { (* arm 4 *)
  (* OW.n = 4 *)
  rewrite !En.
  mw_regv HS (Z_to_bv 5 14) (Z_to_bv 64 4) HN14
    ltac:(rewrite (mw_sext_atom E_r5 38 Bw 65312 A_r5_38), En; reflexivity).
  apply (fun HQ => st_ok_pi_pin_reg' E_r5 _ (restrict (w_H W) ms_r5) (Z_to_bv 5 14) 4 HQ HN14 ltac:(reflexivity)) in HS.
  assert (RTOK : region_ok segs E_r5 (ms_mem (restrict (w_H W) ms_r5)) (Ro_t 4)).
  { unfold Ro_t, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict A_OBJ].
    change (A_OBJ 12) with 253%nat. rewrite U12_r5. split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw).
    apply mw_inG_OW. unfold TW.SZ_OW. lia. }
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ssx _ => assert (RTD : all_disjoint E_r5 (Ro_t 4) (ss_mem ssx))
  end.
  { clear - Hsp Usp_r5 U8_r5 U12_r5 U27_r5 U1_r5 U93_r5.
    cbn [ss_mem all_disjoint add_cond]. unfold Ro_t, extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (A_OBJ 12) with 253%nat.
    rewrite ?Usp_r5, ?U8_r5, ?U12_r5, ?U27_r5, ?U1_r5, ?U93_r5.
    unfold TA_M, TA_OW, TA_g_now, FCells.GOT_CELL_K, FCells.CELL_K.
    repeat split; first [exact I | lia]. }
  apply (fun HQ => st_ok_pi_add_region E_r5 _ _ (Ro_t 4) HQ ltac:(vm_compute; reflexivity) RTOK RTD) in HS.
  clear RTOK HN14.
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r5 U8_r5 U12_r5 U12_r5. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KWk : forall a, 0 <= a < 2 ^ 64 -> ~ mw_winsk (spZ regs) 4 a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity;
      [| exact (KW6 a Ha ltac:(intros Hc0; apply Hn; left; exact Hc0))].
    eapply (kept_of_frame _ _ _ _ _ (mw_winsk (spZ regs) 4)).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r5, ?U8_r5, ?U12_r5 in Hx;
        unfold mw_winsk, mw_wins;
        first [ lia | left; left; lia | left; right; left; lia | left; right; right; left; lia
              | left; right; right; right; left; lia | left; right; right; right; right; left; lia
              | left; right; right; right; right; right; left; lia
              | left; right; right; right; right; right; right; lia | right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GAk : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA6 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_k := mf) in *; set (E_k := EF) in HS, SHOK, HEI
  end.
  assert (HE_k : forall n, (n < 1024)%nat -> ew E_k n = ew E0 n)
    by (intros n Hn; unfold E_k; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r5; lia]).
  assert (A_k_35 : ew E_k 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A35_0).
  assert (A_k_36 : ew E_k 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A36_0).
  assert (A_k_37 : ew E_k 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A37_0).
  assert (A_k_38 : ew E_k 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A38_0).
  assert (A_k_39 : ew E_k 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A39_0).
  assert (A_k_40 : ew E_k 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A40_0).
  assert (A_k_41 : ew E_k 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A41_0).
  assert (A_k_33 : ew E_k 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A33_0).
  assert (A_k_34 : ew E_k 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A34_0).
  assert (U8_k : bv_unsigned (ew E_k 249%nat) = TA_M) by (rewrite HE_k by lia; exact U8L).
  assert (U12_k : bv_unsigned (ew E_k 253%nat) = TA_OW) by (rewrite HE_k by lia; exact U12L).
  assert (U27_k : bv_unsigned (ew E_k 268%nat) = TA_g_now) by (rewrite HE_k by lia; exact U27L).
  assert (U1_k : bv_unsigned (ew E_k 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_k by lia; exact U1L).
  assert (U93_k : bv_unsigned (ew E_k 334%nat) = FCells.CELL_K) by (rewrite HE_k by lia; exact U93L).
  assert (Usp_k : bv_unsigned (ew E_k 2) = spZ regs) by (rewrite HE_k by lia; exact Usp0).
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 0 _ HS eq_refl) as RG0.
  cbn [ms_mem restrict] in RG0.
  assert (Vt4 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 52 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 52 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (Vt8 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 56 + Z.of_nat j)
      = Some (YO0f.le_byte (TW.s32_at Bw 12) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 56 4%N (SExt true 32 (SOff 35 0)) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. unfold U. rewrite (mw_sext_atom E_k 35 Bw 12 A_k_35), mw_u64.
    change (8 * Z.of_nat (N.to_nat 4%N)) with 32. apply mw_mod64. lia. }
  assert (Vt12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 60 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 60 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 11 _ HS eq_refl) as RG11.
  cbn [ms_mem restrict] in RG11.
  assert (VOW196 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 196 + Z.of_nat j) = Some (YO0f.le_byte (TW.s32_at Bw 65508 + 1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 196 4%N (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 1)) RG11 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. change (8 * Z.of_nat (N.to_nat 4%N)) with 32.
    exact (mw_u_add1 E_k (SExt true 32 (SOff 37 0)) (TW.s32_at Bw 65508) (mw_sext_atom E_k 37 Bw 65508 A_k_37)). }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 6 _ HS eq_refl) as RG6.
  cbn [ms_mem restrict] in RG6.
  assert (VM16 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 16 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 16 8%N (SLit 0) RG6 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 8 _ HS eq_refl) as RG8.
  cbn [ms_mem restrict] in RG8.
  assert (VM40 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 40 + Z.of_nat j) = Some (YO0f.le_byte (TW.u_at Bw 65000 8) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 40 8%N (SOff 39 0) RG8 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. rewrite (U_atom E_k 39 (TW.u_at Bw 65000 8) A_k_39 ltac:(pose proof (TWL.u_at_range Bw 65000 8) as HR;
      cbn [Z.of_nat] in HR; lia)). reflexivity. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 9 _ HS eq_refl) as RG9.
  cbn [ms_mem restrict] in RG9.
  assert (VM88 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 88 4%N (SLit 0) RG9 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 10 _ HS eq_refl) as RG10.
  cbn [ms_mem restrict] in RG10.
  assert (VOW0 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 0 + Z.of_nat j) = Some (YO0f.le_byte (5) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 0 4%N (SLit 5) RG10 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 5 _ HS eq_refl) as RG5.
  cbn [ms_mem restrict] in RG5.
  assert (VM12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 12 + Z.of_nat j) = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 12 4%N (SLit 1) RG5 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (HTW : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms_k)) (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 4) (TW.put 4 1))
             (65320 + 12 * 4) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 4) (TW.put 4 1))
        65312 (TW.put 4 5)) 12 (TW.put 4 1))).
  { apply (mw_fin_rd _ (aview segs (w_H W) memc) (aview segs (w_H W) (ms_mem ms_k)) _ (mw_world9 W memc (ms_mem ms_k) Bw _ 4 5 ltac:(lia)
      (mw_world4 W memc (ms_mem ms_k) Bw Htw VOW196 VM16 VM40 VM88) Vt4 Vt8 Vt12 VOW0 VM12)).
    intros x Hx Hni. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    destruct (Classical_Prop.classic (mw_winsk (spZ regs) 4 x)) as [Hw | Hw].
    - destruct Hw as [[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]] | Hw].
      + exfalso. unfold MWAKE_STK, MWAKE_FRAME in Hw. lia.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 12) (TA_M + 12 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 16) (TA_M + 16 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 40) (TA_M + 40 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 88) (TA_M + 88 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 0) (TA_OW + 0 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 196) (TA_OW + 196 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. destruct (Z_lt_le_dec x (TA_OW + (8 + 12 * 4))) as [D1|D1]; [| destruct (Z_lt_le_dec x (TA_OW + (12 + 12 * 4))) as [D2|D2]].
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (4 + 12 * 4)) (TA_OW + (4 + 12 * 4) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (8 + 12 * 4)) (TA_OW + (8 + 12 * 4) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (12 + 12 * 4)) (TA_OW + (12 + 12 * 4) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
    - apply KWk; [lia | exact Hw]. }
  mw_regv HS (Z_to_bv 5 1) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite HE_k by lia;
          rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  mw_regv HS (Z_to_bv 5 10) (w64 0) RF10
    ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mw_u64; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms_k)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E_k _ ms_k regs (mw_ex Bw) HS).
    - apply mw_agree; [intros n Hn; rewrite HE_k by lia; reflexivity | reflexivity].
    - vm_compute. reflexivity. }
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ mw_Zs (spZ regs) a ->
    aview segs (w_H W) (ms_mem ms_k) a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; apply KWk; [exact Ha
        | intros Hc0; exact (Hn (mw_winsk_Zs _ 4 a ltac:(lia) Hc0))]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  exact (mw_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 4) (TW.put 4 1))
             (65320 + 12 * 4) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 4) (TW.put 4 1))
        65312 (TW.put 4 5)) 12 (TW.put 4 1)) 0
           (ms_regs ms_k) (ms_mem ms_k) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GAk
           HTW HPF RF1 RF10 matF).
  }
  { (* arm 5 *)
  (* OW.n = 5 *)
  rewrite !En.
  mw_regv HS (Z_to_bv 5 14) (Z_to_bv 64 5) HN14
    ltac:(rewrite (mw_sext_atom E_r5 38 Bw 65312 A_r5_38), En; reflexivity).
  apply (fun HQ => st_ok_pi_pin_reg' E_r5 _ (restrict (w_H W) ms_r5) (Z_to_bv 5 14) 5 HQ HN14 ltac:(reflexivity)) in HS.
  assert (RTOK : region_ok segs E_r5 (ms_mem (restrict (w_H W) ms_r5)) (Ro_t 5)).
  { unfold Ro_t, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict A_OBJ].
    change (A_OBJ 12) with 253%nat. rewrite U12_r5. split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw).
    apply mw_inG_OW. unfold TW.SZ_OW. lia. }
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ssx _ => assert (RTD : all_disjoint E_r5 (Ro_t 5) (ss_mem ssx))
  end.
  { clear - Hsp Usp_r5 U8_r5 U12_r5 U27_r5 U1_r5 U93_r5.
    cbn [ss_mem all_disjoint add_cond]. unfold Ro_t, extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (A_OBJ 12) with 253%nat.
    rewrite ?Usp_r5, ?U8_r5, ?U12_r5, ?U27_r5, ?U1_r5, ?U93_r5.
    unfold TA_M, TA_OW, TA_g_now, FCells.GOT_CELL_K, FCells.CELL_K.
    repeat split; first [exact I | lia]. }
  apply (fun HQ => st_ok_pi_add_region E_r5 _ _ (Ro_t 5) HQ ltac:(vm_compute; reflexivity) RTOK RTD) in HS.
  clear RTOK HN14.
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r5 U8_r5 U12_r5 U12_r5. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KWk : forall a, 0 <= a < 2 ^ 64 -> ~ mw_winsk (spZ regs) 5 a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity;
      [| exact (KW6 a Ha ltac:(intros Hc0; apply Hn; left; exact Hc0))].
    eapply (kept_of_frame _ _ _ _ _ (mw_winsk (spZ regs) 5)).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r5, ?U8_r5, ?U12_r5 in Hx;
        unfold mw_winsk, mw_wins;
        first [ lia | left; left; lia | left; right; left; lia | left; right; right; left; lia
              | left; right; right; right; left; lia | left; right; right; right; right; left; lia
              | left; right; right; right; right; right; left; lia
              | left; right; right; right; right; right; right; lia | right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GAk : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA6 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_k := mf) in *; set (E_k := EF) in HS, SHOK, HEI
  end.
  assert (HE_k : forall n, (n < 1024)%nat -> ew E_k n = ew E0 n)
    by (intros n Hn; unfold E_k; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r5; lia]).
  assert (A_k_35 : ew E_k 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A35_0).
  assert (A_k_36 : ew E_k 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A36_0).
  assert (A_k_37 : ew E_k 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A37_0).
  assert (A_k_38 : ew E_k 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A38_0).
  assert (A_k_39 : ew E_k 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A39_0).
  assert (A_k_40 : ew E_k 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A40_0).
  assert (A_k_41 : ew E_k 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A41_0).
  assert (A_k_33 : ew E_k 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A33_0).
  assert (A_k_34 : ew E_k 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A34_0).
  assert (U8_k : bv_unsigned (ew E_k 249%nat) = TA_M) by (rewrite HE_k by lia; exact U8L).
  assert (U12_k : bv_unsigned (ew E_k 253%nat) = TA_OW) by (rewrite HE_k by lia; exact U12L).
  assert (U27_k : bv_unsigned (ew E_k 268%nat) = TA_g_now) by (rewrite HE_k by lia; exact U27L).
  assert (U1_k : bv_unsigned (ew E_k 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_k by lia; exact U1L).
  assert (U93_k : bv_unsigned (ew E_k 334%nat) = FCells.CELL_K) by (rewrite HE_k by lia; exact U93L).
  assert (Usp_k : bv_unsigned (ew E_k 2) = spZ regs) by (rewrite HE_k by lia; exact Usp0).
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 0 _ HS eq_refl) as RG0.
  cbn [ms_mem restrict] in RG0.
  assert (Vt4 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 64 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 64 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (Vt8 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 68 + Z.of_nat j)
      = Some (YO0f.le_byte (TW.s32_at Bw 12) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 68 4%N (SExt true 32 (SOff 35 0)) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. unfold U. rewrite (mw_sext_atom E_k 35 Bw 12 A_k_35), mw_u64.
    change (8 * Z.of_nat (N.to_nat 4%N)) with 32. apply mw_mod64. lia. }
  assert (Vt12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 72 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 72 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 11 _ HS eq_refl) as RG11.
  cbn [ms_mem restrict] in RG11.
  assert (VOW196 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 196 + Z.of_nat j) = Some (YO0f.le_byte (TW.s32_at Bw 65508 + 1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 196 4%N (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 1)) RG11 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. change (8 * Z.of_nat (N.to_nat 4%N)) with 32.
    exact (mw_u_add1 E_k (SExt true 32 (SOff 37 0)) (TW.s32_at Bw 65508) (mw_sext_atom E_k 37 Bw 65508 A_k_37)). }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 6 _ HS eq_refl) as RG6.
  cbn [ms_mem restrict] in RG6.
  assert (VM16 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 16 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 16 8%N (SLit 0) RG6 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 8 _ HS eq_refl) as RG8.
  cbn [ms_mem restrict] in RG8.
  assert (VM40 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 40 + Z.of_nat j) = Some (YO0f.le_byte (TW.u_at Bw 65000 8) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 40 8%N (SOff 39 0) RG8 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. rewrite (U_atom E_k 39 (TW.u_at Bw 65000 8) A_k_39 ltac:(pose proof (TWL.u_at_range Bw 65000 8) as HR;
      cbn [Z.of_nat] in HR; lia)). reflexivity. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 9 _ HS eq_refl) as RG9.
  cbn [ms_mem restrict] in RG9.
  assert (VM88 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 88 4%N (SLit 0) RG9 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 10 _ HS eq_refl) as RG10.
  cbn [ms_mem restrict] in RG10.
  assert (VOW0 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 0 + Z.of_nat j) = Some (YO0f.le_byte (6) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 0 4%N (SLit 6) RG10 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 5 _ HS eq_refl) as RG5.
  cbn [ms_mem restrict] in RG5.
  assert (VM12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 12 + Z.of_nat j) = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 12 4%N (SLit 1) RG5 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (HTW : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms_k)) (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 5) (TW.put 4 1))
             (65320 + 12 * 5) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 5) (TW.put 4 1))
        65312 (TW.put 4 6)) 12 (TW.put 4 1))).
  { apply (mw_fin_rd _ (aview segs (w_H W) memc) (aview segs (w_H W) (ms_mem ms_k)) _ (mw_world9 W memc (ms_mem ms_k) Bw _ 5 6 ltac:(lia)
      (mw_world4 W memc (ms_mem ms_k) Bw Htw VOW196 VM16 VM40 VM88) Vt4 Vt8 Vt12 VOW0 VM12)).
    intros x Hx Hni. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    destruct (Classical_Prop.classic (mw_winsk (spZ regs) 5 x)) as [Hw | Hw].
    - destruct Hw as [[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]] | Hw].
      + exfalso. unfold MWAKE_STK, MWAKE_FRAME in Hw. lia.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 12) (TA_M + 12 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 16) (TA_M + 16 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 40) (TA_M + 40 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 88) (TA_M + 88 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 0) (TA_OW + 0 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 196) (TA_OW + 196 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. destruct (Z_lt_le_dec x (TA_OW + (8 + 12 * 5))) as [D1|D1]; [| destruct (Z_lt_le_dec x (TA_OW + (12 + 12 * 5))) as [D2|D2]].
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (4 + 12 * 5)) (TA_OW + (4 + 12 * 5) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (8 + 12 * 5)) (TA_OW + (8 + 12 * 5) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (12 + 12 * 5)) (TA_OW + (12 + 12 * 5) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
    - apply KWk; [lia | exact Hw]. }
  mw_regv HS (Z_to_bv 5 1) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite HE_k by lia;
          rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  mw_regv HS (Z_to_bv 5 10) (w64 0) RF10
    ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mw_u64; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms_k)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E_k _ ms_k regs (mw_ex Bw) HS).
    - apply mw_agree; [intros n Hn; rewrite HE_k by lia; reflexivity | reflexivity].
    - vm_compute. reflexivity. }
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ mw_Zs (spZ regs) a ->
    aview segs (w_H W) (ms_mem ms_k) a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; apply KWk; [exact Ha
        | intros Hc0; exact (Hn (mw_winsk_Zs _ 5 a ltac:(lia) Hc0))]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  exact (mw_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 5) (TW.put 4 1))
             (65320 + 12 * 5) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 5) (TW.put 4 1))
        65312 (TW.put 4 6)) 12 (TW.put 4 1)) 0
           (ms_regs ms_k) (ms_mem ms_k) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GAk
           HTW HPF RF1 RF10 matF).
  }
  { (* arm 6 *)
  (* OW.n = 6 *)
  rewrite !En.
  mw_regv HS (Z_to_bv 5 14) (Z_to_bv 64 6) HN14
    ltac:(rewrite (mw_sext_atom E_r5 38 Bw 65312 A_r5_38), En; reflexivity).
  apply (fun HQ => st_ok_pi_pin_reg' E_r5 _ (restrict (w_H W) ms_r5) (Z_to_bv 5 14) 6 HQ HN14 ltac:(reflexivity)) in HS.
  assert (RTOK : region_ok segs E_r5 (ms_mem (restrict (w_H W) ms_r5)) (Ro_t 6)).
  { unfold Ro_t, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict A_OBJ].
    change (A_OBJ 12) with 253%nat. rewrite U12_r5. split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw).
    apply mw_inG_OW. unfold TW.SZ_OW. lia. }
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ssx _ => assert (RTD : all_disjoint E_r5 (Ro_t 6) (ss_mem ssx))
  end.
  { clear - Hsp Usp_r5 U8_r5 U12_r5 U27_r5 U1_r5 U93_r5.
    cbn [ss_mem all_disjoint add_cond]. unfold Ro_t, extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (A_OBJ 12) with 253%nat.
    rewrite ?Usp_r5, ?U8_r5, ?U12_r5, ?U27_r5, ?U1_r5, ?U93_r5.
    unfold TA_M, TA_OW, TA_g_now, FCells.GOT_CELL_K, FCells.CELL_K.
    repeat split; first [exact I | lia]. }
  apply (fun HQ => st_ok_pi_add_region E_r5 _ _ (Ro_t 6) HQ ltac:(vm_compute; reflexivity) RTOK RTD) in HS.
  clear RTOK HN14.
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r5 U8_r5 U12_r5 U12_r5. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KWk : forall a, 0 <= a < 2 ^ 64 -> ~ mw_winsk (spZ regs) 6 a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity;
      [| exact (KW6 a Ha ltac:(intros Hc0; apply Hn; left; exact Hc0))].
    eapply (kept_of_frame _ _ _ _ _ (mw_winsk (spZ regs) 6)).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r5, ?U8_r5, ?U12_r5 in Hx;
        unfold mw_winsk, mw_wins;
        first [ lia | left; left; lia | left; right; left; lia | left; right; right; left; lia
              | left; right; right; right; left; lia | left; right; right; right; right; left; lia
              | left; right; right; right; right; right; left; lia
              | left; right; right; right; right; right; right; lia | right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GAk : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA6 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_k := mf) in *; set (E_k := EF) in HS, SHOK, HEI
  end.
  assert (HE_k : forall n, (n < 1024)%nat -> ew E_k n = ew E0 n)
    by (intros n Hn; unfold E_k; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r5; lia]).
  assert (A_k_35 : ew E_k 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A35_0).
  assert (A_k_36 : ew E_k 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A36_0).
  assert (A_k_37 : ew E_k 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A37_0).
  assert (A_k_38 : ew E_k 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A38_0).
  assert (A_k_39 : ew E_k 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A39_0).
  assert (A_k_40 : ew E_k 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A40_0).
  assert (A_k_41 : ew E_k 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A41_0).
  assert (A_k_33 : ew E_k 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A33_0).
  assert (A_k_34 : ew E_k 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A34_0).
  assert (U8_k : bv_unsigned (ew E_k 249%nat) = TA_M) by (rewrite HE_k by lia; exact U8L).
  assert (U12_k : bv_unsigned (ew E_k 253%nat) = TA_OW) by (rewrite HE_k by lia; exact U12L).
  assert (U27_k : bv_unsigned (ew E_k 268%nat) = TA_g_now) by (rewrite HE_k by lia; exact U27L).
  assert (U1_k : bv_unsigned (ew E_k 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_k by lia; exact U1L).
  assert (U93_k : bv_unsigned (ew E_k 334%nat) = FCells.CELL_K) by (rewrite HE_k by lia; exact U93L).
  assert (Usp_k : bv_unsigned (ew E_k 2) = spZ regs) by (rewrite HE_k by lia; exact Usp0).
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 0 _ HS eq_refl) as RG0.
  cbn [ms_mem restrict] in RG0.
  assert (Vt4 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 76 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 76 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (Vt8 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 80 + Z.of_nat j)
      = Some (YO0f.le_byte (TW.s32_at Bw 12) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 80 4%N (SExt true 32 (SOff 35 0)) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. unfold U. rewrite (mw_sext_atom E_k 35 Bw 12 A_k_35), mw_u64.
    change (8 * Z.of_nat (N.to_nat 4%N)) with 32. apply mw_mod64. lia. }
  assert (Vt12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 84 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 84 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 11 _ HS eq_refl) as RG11.
  cbn [ms_mem restrict] in RG11.
  assert (VOW196 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 196 + Z.of_nat j) = Some (YO0f.le_byte (TW.s32_at Bw 65508 + 1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 196 4%N (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 1)) RG11 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. change (8 * Z.of_nat (N.to_nat 4%N)) with 32.
    exact (mw_u_add1 E_k (SExt true 32 (SOff 37 0)) (TW.s32_at Bw 65508) (mw_sext_atom E_k 37 Bw 65508 A_k_37)). }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 6 _ HS eq_refl) as RG6.
  cbn [ms_mem restrict] in RG6.
  assert (VM16 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 16 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 16 8%N (SLit 0) RG6 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 8 _ HS eq_refl) as RG8.
  cbn [ms_mem restrict] in RG8.
  assert (VM40 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 40 + Z.of_nat j) = Some (YO0f.le_byte (TW.u_at Bw 65000 8) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 40 8%N (SOff 39 0) RG8 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. rewrite (U_atom E_k 39 (TW.u_at Bw 65000 8) A_k_39 ltac:(pose proof (TWL.u_at_range Bw 65000 8) as HR;
      cbn [Z.of_nat] in HR; lia)). reflexivity. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 9 _ HS eq_refl) as RG9.
  cbn [ms_mem restrict] in RG9.
  assert (VM88 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 88 4%N (SLit 0) RG9 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 10 _ HS eq_refl) as RG10.
  cbn [ms_mem restrict] in RG10.
  assert (VOW0 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 0 + Z.of_nat j) = Some (YO0f.le_byte (7) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 0 4%N (SLit 7) RG10 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 5 _ HS eq_refl) as RG5.
  cbn [ms_mem restrict] in RG5.
  assert (VM12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 12 + Z.of_nat j) = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 12 4%N (SLit 1) RG5 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (HTW : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms_k)) (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 6) (TW.put 4 1))
             (65320 + 12 * 6) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 6) (TW.put 4 1))
        65312 (TW.put 4 7)) 12 (TW.put 4 1))).
  { apply (mw_fin_rd _ (aview segs (w_H W) memc) (aview segs (w_H W) (ms_mem ms_k)) _ (mw_world9 W memc (ms_mem ms_k) Bw _ 6 7 ltac:(lia)
      (mw_world4 W memc (ms_mem ms_k) Bw Htw VOW196 VM16 VM40 VM88) Vt4 Vt8 Vt12 VOW0 VM12)).
    intros x Hx Hni. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    destruct (Classical_Prop.classic (mw_winsk (spZ regs) 6 x)) as [Hw | Hw].
    - destruct Hw as [[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]] | Hw].
      + exfalso. unfold MWAKE_STK, MWAKE_FRAME in Hw. lia.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 12) (TA_M + 12 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 16) (TA_M + 16 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 40) (TA_M + 40 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 88) (TA_M + 88 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 0) (TA_OW + 0 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 196) (TA_OW + 196 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. destruct (Z_lt_le_dec x (TA_OW + (8 + 12 * 6))) as [D1|D1]; [| destruct (Z_lt_le_dec x (TA_OW + (12 + 12 * 6))) as [D2|D2]].
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (4 + 12 * 6)) (TA_OW + (4 + 12 * 6) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (8 + 12 * 6)) (TA_OW + (8 + 12 * 6) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (12 + 12 * 6)) (TA_OW + (12 + 12 * 6) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
    - apply KWk; [lia | exact Hw]. }
  mw_regv HS (Z_to_bv 5 1) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite HE_k by lia;
          rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  mw_regv HS (Z_to_bv 5 10) (w64 0) RF10
    ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mw_u64; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms_k)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E_k _ ms_k regs (mw_ex Bw) HS).
    - apply mw_agree; [intros n Hn; rewrite HE_k by lia; reflexivity | reflexivity].
    - vm_compute. reflexivity. }
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ mw_Zs (spZ regs) a ->
    aview segs (w_H W) (ms_mem ms_k) a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; apply KWk; [exact Ha
        | intros Hc0; exact (Hn (mw_winsk_Zs _ 6 a ltac:(lia) Hc0))]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  exact (mw_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 6) (TW.put 4 1))
             (65320 + 12 * 6) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 6) (TW.put 4 1))
        65312 (TW.put 4 7)) 12 (TW.put 4 1)) 0
           (ms_regs ms_k) (ms_mem ms_k) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GAk
           HTW HPF RF1 RF10 matF).
  }
  { (* arm 7 *)
  (* OW.n = 7 *)
  rewrite !En.
  mw_regv HS (Z_to_bv 5 14) (Z_to_bv 64 7) HN14
    ltac:(rewrite (mw_sext_atom E_r5 38 Bw 65312 A_r5_38), En; reflexivity).
  apply (fun HQ => st_ok_pi_pin_reg' E_r5 _ (restrict (w_H W) ms_r5) (Z_to_bv 5 14) 7 HQ HN14 ltac:(reflexivity)) in HS.
  assert (RTOK : region_ok segs E_r5 (ms_mem (restrict (w_H W) ms_r5)) (Ro_t 7)).
  { unfold Ro_t, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict A_OBJ].
    change (A_OBJ 12) with 253%nat. rewrite U12_r5. split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw).
    apply mw_inG_OW. unfold TW.SZ_OW. lia. }
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ssx _ => assert (RTD : all_disjoint E_r5 (Ro_t 7) (ss_mem ssx))
  end.
  { clear - Hsp Usp_r5 U8_r5 U12_r5 U27_r5 U1_r5 U93_r5.
    cbn [ss_mem all_disjoint add_cond]. unfold Ro_t, extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (A_OBJ 12) with 253%nat.
    rewrite ?Usp_r5, ?U8_r5, ?U12_r5, ?U27_r5, ?U1_r5, ?U93_r5.
    unfold TA_M, TA_OW, TA_g_now, FCells.GOT_CELL_K, FCells.CELL_K.
    repeat split; first [exact I | lia]. }
  apply (fun HQ => st_ok_pi_add_region E_r5 _ _ (Ro_t 7) HQ ltac:(vm_compute; reflexivity) RTOK RTD) in HS.
  clear RTOK HN14.
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r5 U8_r5 U12_r5 U12_r5. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KWk : forall a, 0 <= a < 2 ^ 64 -> ~ mw_winsk (spZ regs) 7 a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity;
      [| exact (KW6 a Ha ltac:(intros Hc0; apply Hn; left; exact Hc0))].
    eapply (kept_of_frame _ _ _ _ _ (mw_winsk (spZ regs) 7)).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r5, ?U8_r5, ?U12_r5 in Hx;
        unfold mw_winsk, mw_wins;
        first [ lia | left; left; lia | left; right; left; lia | left; right; right; left; lia
              | left; right; right; right; left; lia | left; right; right; right; right; left; lia
              | left; right; right; right; right; right; left; lia
              | left; right; right; right; right; right; right; lia | right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GAk : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA6 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_k := mf) in *; set (E_k := EF) in HS, SHOK, HEI
  end.
  assert (HE_k : forall n, (n < 1024)%nat -> ew E_k n = ew E0 n)
    by (intros n Hn; unfold E_k; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r5; lia]).
  assert (A_k_35 : ew E_k 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A35_0).
  assert (A_k_36 : ew E_k 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A36_0).
  assert (A_k_37 : ew E_k 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A37_0).
  assert (A_k_38 : ew E_k 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A38_0).
  assert (A_k_39 : ew E_k 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A39_0).
  assert (A_k_40 : ew E_k 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A40_0).
  assert (A_k_41 : ew E_k 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A41_0).
  assert (A_k_33 : ew E_k 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A33_0).
  assert (A_k_34 : ew E_k 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A34_0).
  assert (U8_k : bv_unsigned (ew E_k 249%nat) = TA_M) by (rewrite HE_k by lia; exact U8L).
  assert (U12_k : bv_unsigned (ew E_k 253%nat) = TA_OW) by (rewrite HE_k by lia; exact U12L).
  assert (U27_k : bv_unsigned (ew E_k 268%nat) = TA_g_now) by (rewrite HE_k by lia; exact U27L).
  assert (U1_k : bv_unsigned (ew E_k 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_k by lia; exact U1L).
  assert (U93_k : bv_unsigned (ew E_k 334%nat) = FCells.CELL_K) by (rewrite HE_k by lia; exact U93L).
  assert (Usp_k : bv_unsigned (ew E_k 2) = spZ regs) by (rewrite HE_k by lia; exact Usp0).
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 0 _ HS eq_refl) as RG0.
  cbn [ms_mem restrict] in RG0.
  assert (Vt4 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 88 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 88 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (Vt8 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 92 + Z.of_nat j)
      = Some (YO0f.le_byte (TW.s32_at Bw 12) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 92 4%N (SExt true 32 (SOff 35 0)) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. unfold U. rewrite (mw_sext_atom E_k 35 Bw 12 A_k_35), mw_u64.
    change (8 * Z.of_nat (N.to_nat 4%N)) with 32. apply mw_mod64. lia. }
  assert (Vt12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 96 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 96 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 11 _ HS eq_refl) as RG11.
  cbn [ms_mem restrict] in RG11.
  assert (VOW196 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 196 + Z.of_nat j) = Some (YO0f.le_byte (TW.s32_at Bw 65508 + 1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 196 4%N (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 1)) RG11 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. change (8 * Z.of_nat (N.to_nat 4%N)) with 32.
    exact (mw_u_add1 E_k (SExt true 32 (SOff 37 0)) (TW.s32_at Bw 65508) (mw_sext_atom E_k 37 Bw 65508 A_k_37)). }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 6 _ HS eq_refl) as RG6.
  cbn [ms_mem restrict] in RG6.
  assert (VM16 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 16 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 16 8%N (SLit 0) RG6 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 8 _ HS eq_refl) as RG8.
  cbn [ms_mem restrict] in RG8.
  assert (VM40 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 40 + Z.of_nat j) = Some (YO0f.le_byte (TW.u_at Bw 65000 8) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 40 8%N (SOff 39 0) RG8 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. rewrite (U_atom E_k 39 (TW.u_at Bw 65000 8) A_k_39 ltac:(pose proof (TWL.u_at_range Bw 65000 8) as HR;
      cbn [Z.of_nat] in HR; lia)). reflexivity. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 9 _ HS eq_refl) as RG9.
  cbn [ms_mem restrict] in RG9.
  assert (VM88 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 88 4%N (SLit 0) RG9 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 10 _ HS eq_refl) as RG10.
  cbn [ms_mem restrict] in RG10.
  assert (VOW0 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 0 + Z.of_nat j) = Some (YO0f.le_byte (8) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 0 4%N (SLit 8) RG10 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 5 _ HS eq_refl) as RG5.
  cbn [ms_mem restrict] in RG5.
  assert (VM12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 12 + Z.of_nat j) = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 12 4%N (SLit 1) RG5 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (HTW : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms_k)) (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 7) (TW.put 4 1))
             (65320 + 12 * 7) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 7) (TW.put 4 1))
        65312 (TW.put 4 8)) 12 (TW.put 4 1))).
  { apply (mw_fin_rd _ (aview segs (w_H W) memc) (aview segs (w_H W) (ms_mem ms_k)) _ (mw_world9 W memc (ms_mem ms_k) Bw _ 7 8 ltac:(lia)
      (mw_world4 W memc (ms_mem ms_k) Bw Htw VOW196 VM16 VM40 VM88) Vt4 Vt8 Vt12 VOW0 VM12)).
    intros x Hx Hni. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    destruct (Classical_Prop.classic (mw_winsk (spZ regs) 7 x)) as [Hw | Hw].
    - destruct Hw as [[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]] | Hw].
      + exfalso. unfold MWAKE_STK, MWAKE_FRAME in Hw. lia.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 12) (TA_M + 12 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 16) (TA_M + 16 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 40) (TA_M + 40 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 88) (TA_M + 88 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 0) (TA_OW + 0 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 196) (TA_OW + 196 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. destruct (Z_lt_le_dec x (TA_OW + (8 + 12 * 7))) as [D1|D1]; [| destruct (Z_lt_le_dec x (TA_OW + (12 + 12 * 7))) as [D2|D2]].
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (4 + 12 * 7)) (TA_OW + (4 + 12 * 7) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (8 + 12 * 7)) (TA_OW + (8 + 12 * 7) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (12 + 12 * 7)) (TA_OW + (12 + 12 * 7) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
    - apply KWk; [lia | exact Hw]. }
  mw_regv HS (Z_to_bv 5 1) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite HE_k by lia;
          rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  mw_regv HS (Z_to_bv 5 10) (w64 0) RF10
    ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mw_u64; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms_k)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E_k _ ms_k regs (mw_ex Bw) HS).
    - apply mw_agree; [intros n Hn; rewrite HE_k by lia; reflexivity | reflexivity].
    - vm_compute. reflexivity. }
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ mw_Zs (spZ regs) a ->
    aview segs (w_H W) (ms_mem ms_k) a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; apply KWk; [exact Ha
        | intros Hc0; exact (Hn (mw_winsk_Zs _ 7 a ltac:(lia) Hc0))]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  exact (mw_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 7) (TW.put 4 1))
             (65320 + 12 * 7) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 7) (TW.put 4 1))
        65312 (TW.put 4 8)) 12 (TW.put 4 1)) 0
           (ms_regs ms_k) (ms_mem ms_k) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GAk
           HTW HPF RF1 RF10 matF).
  }
  { (* arm 8 *)
  (* OW.n = 8 *)
  rewrite !En.
  mw_regv HS (Z_to_bv 5 14) (Z_to_bv 64 8) HN14
    ltac:(rewrite (mw_sext_atom E_r5 38 Bw 65312 A_r5_38), En; reflexivity).
  apply (fun HQ => st_ok_pi_pin_reg' E_r5 _ (restrict (w_H W) ms_r5) (Z_to_bv 5 14) 8 HQ HN14 ltac:(reflexivity)) in HS.
  assert (RTOK : region_ok segs E_r5 (ms_mem (restrict (w_H W) ms_r5)) (Ro_t 8)).
  { unfold Ro_t, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict A_OBJ].
    change (A_OBJ 12) with 253%nat. rewrite U12_r5. split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw).
    apply mw_inG_OW. unfold TW.SZ_OW. lia. }
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ssx _ => assert (RTD : all_disjoint E_r5 (Ro_t 8) (ss_mem ssx))
  end.
  { clear - Hsp Usp_r5 U8_r5 U12_r5 U27_r5 U1_r5 U93_r5.
    cbn [ss_mem all_disjoint add_cond]. unfold Ro_t, extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (A_OBJ 12) with 253%nat.
    rewrite ?Usp_r5, ?U8_r5, ?U12_r5, ?U27_r5, ?U1_r5, ?U93_r5.
    unfold TA_M, TA_OW, TA_g_now, FCells.GOT_CELL_K, FCells.CELL_K.
    repeat split; first [exact I | lia]. }
  apply (fun HQ => st_ok_pi_add_region E_r5 _ _ (Ro_t 8) HQ ltac:(vm_compute; reflexivity) RTOK RTD) in HS.
  clear RTOK HN14.
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r5 U8_r5 U12_r5 U12_r5. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KWk : forall a, 0 <= a < 2 ^ 64 -> ~ mw_winsk (spZ regs) 8 a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity;
      [| exact (KW6 a Ha ltac:(intros Hc0; apply Hn; left; exact Hc0))].
    eapply (kept_of_frame _ _ _ _ _ (mw_winsk (spZ regs) 8)).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r5, ?U8_r5, ?U12_r5 in Hx;
        unfold mw_winsk, mw_wins;
        first [ lia | left; left; lia | left; right; left; lia | left; right; right; left; lia
              | left; right; right; right; left; lia | left; right; right; right; right; left; lia
              | left; right; right; right; right; right; left; lia
              | left; right; right; right; right; right; right; lia | right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GAk : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA6 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_k := mf) in *; set (E_k := EF) in HS, SHOK, HEI
  end.
  assert (HE_k : forall n, (n < 1024)%nat -> ew E_k n = ew E0 n)
    by (intros n Hn; unfold E_k; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r5; lia]).
  assert (A_k_35 : ew E_k 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A35_0).
  assert (A_k_36 : ew E_k 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A36_0).
  assert (A_k_37 : ew E_k 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A37_0).
  assert (A_k_38 : ew E_k 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A38_0).
  assert (A_k_39 : ew E_k 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A39_0).
  assert (A_k_40 : ew E_k 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A40_0).
  assert (A_k_41 : ew E_k 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A41_0).
  assert (A_k_33 : ew E_k 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A33_0).
  assert (A_k_34 : ew E_k 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A34_0).
  assert (U8_k : bv_unsigned (ew E_k 249%nat) = TA_M) by (rewrite HE_k by lia; exact U8L).
  assert (U12_k : bv_unsigned (ew E_k 253%nat) = TA_OW) by (rewrite HE_k by lia; exact U12L).
  assert (U27_k : bv_unsigned (ew E_k 268%nat) = TA_g_now) by (rewrite HE_k by lia; exact U27L).
  assert (U1_k : bv_unsigned (ew E_k 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_k by lia; exact U1L).
  assert (U93_k : bv_unsigned (ew E_k 334%nat) = FCells.CELL_K) by (rewrite HE_k by lia; exact U93L).
  assert (Usp_k : bv_unsigned (ew E_k 2) = spZ regs) by (rewrite HE_k by lia; exact Usp0).
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 0 _ HS eq_refl) as RG0.
  cbn [ms_mem restrict] in RG0.
  assert (Vt4 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 100 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 100 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (Vt8 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 104 + Z.of_nat j)
      = Some (YO0f.le_byte (TW.s32_at Bw 12) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 104 4%N (SExt true 32 (SOff 35 0)) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. unfold U. rewrite (mw_sext_atom E_k 35 Bw 12 A_k_35), mw_u64.
    change (8 * Z.of_nat (N.to_nat 4%N)) with 32. apply mw_mod64. lia. }
  assert (Vt12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 108 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 108 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 11 _ HS eq_refl) as RG11.
  cbn [ms_mem restrict] in RG11.
  assert (VOW196 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 196 + Z.of_nat j) = Some (YO0f.le_byte (TW.s32_at Bw 65508 + 1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 196 4%N (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 1)) RG11 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. change (8 * Z.of_nat (N.to_nat 4%N)) with 32.
    exact (mw_u_add1 E_k (SExt true 32 (SOff 37 0)) (TW.s32_at Bw 65508) (mw_sext_atom E_k 37 Bw 65508 A_k_37)). }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 6 _ HS eq_refl) as RG6.
  cbn [ms_mem restrict] in RG6.
  assert (VM16 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 16 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 16 8%N (SLit 0) RG6 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 8 _ HS eq_refl) as RG8.
  cbn [ms_mem restrict] in RG8.
  assert (VM40 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 40 + Z.of_nat j) = Some (YO0f.le_byte (TW.u_at Bw 65000 8) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 40 8%N (SOff 39 0) RG8 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. rewrite (U_atom E_k 39 (TW.u_at Bw 65000 8) A_k_39 ltac:(pose proof (TWL.u_at_range Bw 65000 8) as HR;
      cbn [Z.of_nat] in HR; lia)). reflexivity. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 9 _ HS eq_refl) as RG9.
  cbn [ms_mem restrict] in RG9.
  assert (VM88 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 88 4%N (SLit 0) RG9 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 10 _ HS eq_refl) as RG10.
  cbn [ms_mem restrict] in RG10.
  assert (VOW0 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 0 + Z.of_nat j) = Some (YO0f.le_byte (9) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 0 4%N (SLit 9) RG10 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 5 _ HS eq_refl) as RG5.
  cbn [ms_mem restrict] in RG5.
  assert (VM12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 12 + Z.of_nat j) = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 12 4%N (SLit 1) RG5 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (HTW : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms_k)) (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 8) (TW.put 4 1))
             (65320 + 12 * 8) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 8) (TW.put 4 1))
        65312 (TW.put 4 9)) 12 (TW.put 4 1))).
  { apply (mw_fin_rd _ (aview segs (w_H W) memc) (aview segs (w_H W) (ms_mem ms_k)) _ (mw_world9 W memc (ms_mem ms_k) Bw _ 8 9 ltac:(lia)
      (mw_world4 W memc (ms_mem ms_k) Bw Htw VOW196 VM16 VM40 VM88) Vt4 Vt8 Vt12 VOW0 VM12)).
    intros x Hx Hni. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    destruct (Classical_Prop.classic (mw_winsk (spZ regs) 8 x)) as [Hw | Hw].
    - destruct Hw as [[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]] | Hw].
      + exfalso. unfold MWAKE_STK, MWAKE_FRAME in Hw. lia.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 12) (TA_M + 12 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 16) (TA_M + 16 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 40) (TA_M + 40 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 88) (TA_M + 88 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 0) (TA_OW + 0 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 196) (TA_OW + 196 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. destruct (Z_lt_le_dec x (TA_OW + (8 + 12 * 8))) as [D1|D1]; [| destruct (Z_lt_le_dec x (TA_OW + (12 + 12 * 8))) as [D2|D2]].
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (4 + 12 * 8)) (TA_OW + (4 + 12 * 8) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (8 + 12 * 8)) (TA_OW + (8 + 12 * 8) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (12 + 12 * 8)) (TA_OW + (12 + 12 * 8) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
    - apply KWk; [lia | exact Hw]. }
  mw_regv HS (Z_to_bv 5 1) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite HE_k by lia;
          rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  mw_regv HS (Z_to_bv 5 10) (w64 0) RF10
    ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mw_u64; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms_k)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E_k _ ms_k regs (mw_ex Bw) HS).
    - apply mw_agree; [intros n Hn; rewrite HE_k by lia; reflexivity | reflexivity].
    - vm_compute. reflexivity. }
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ mw_Zs (spZ regs) a ->
    aview segs (w_H W) (ms_mem ms_k) a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; apply KWk; [exact Ha
        | intros Hc0; exact (Hn (mw_winsk_Zs _ 8 a ltac:(lia) Hc0))]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  exact (mw_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 8) (TW.put 4 1))
             (65320 + 12 * 8) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 8) (TW.put 4 1))
        65312 (TW.put 4 9)) 12 (TW.put 4 1)) 0
           (ms_regs ms_k) (ms_mem ms_k) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GAk
           HTW HPF RF1 RF10 matF).
  }
  { (* arm 9 *)
  (* OW.n = 9 *)
  rewrite !En.
  mw_regv HS (Z_to_bv 5 14) (Z_to_bv 64 9) HN14
    ltac:(rewrite (mw_sext_atom E_r5 38 Bw 65312 A_r5_38), En; reflexivity).
  apply (fun HQ => st_ok_pi_pin_reg' E_r5 _ (restrict (w_H W) ms_r5) (Z_to_bv 5 14) 9 HQ HN14 ltac:(reflexivity)) in HS.
  assert (RTOK : region_ok segs E_r5 (ms_mem (restrict (w_H W) ms_r5)) (Ro_t 9)).
  { unfold Ro_t, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict A_OBJ].
    change (A_OBJ 12) with 253%nat. rewrite U12_r5. split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw).
    apply mw_inG_OW. unfold TW.SZ_OW. lia. }
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ssx _ => assert (RTD : all_disjoint E_r5 (Ro_t 9) (ss_mem ssx))
  end.
  { clear - Hsp Usp_r5 U8_r5 U12_r5 U27_r5 U1_r5 U93_r5.
    cbn [ss_mem all_disjoint add_cond]. unfold Ro_t, extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (A_OBJ 12) with 253%nat.
    rewrite ?Usp_r5, ?U8_r5, ?U12_r5, ?U27_r5, ?U1_r5, ?U93_r5.
    unfold TA_M, TA_OW, TA_g_now, FCells.GOT_CELL_K, FCells.CELL_K.
    repeat split; first [exact I | lia]. }
  apply (fun HQ => st_ok_pi_add_region E_r5 _ _ (Ro_t 9) HQ ltac:(vm_compute; reflexivity) RTOK RTD) in HS.
  clear RTOK HN14.
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r5 U8_r5 U12_r5 U12_r5. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KWk : forall a, 0 <= a < 2 ^ 64 -> ~ mw_winsk (spZ regs) 9 a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity;
      [| exact (KW6 a Ha ltac:(intros Hc0; apply Hn; left; exact Hc0))].
    eapply (kept_of_frame _ _ _ _ _ (mw_winsk (spZ regs) 9)).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r5, ?U8_r5, ?U12_r5 in Hx;
        unfold mw_winsk, mw_wins;
        first [ lia | left; left; lia | left; right; left; lia | left; right; right; left; lia
              | left; right; right; right; left; lia | left; right; right; right; right; left; lia
              | left; right; right; right; right; right; left; lia
              | left; right; right; right; right; right; right; lia | right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GAk : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA6 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_k := mf) in *; set (E_k := EF) in HS, SHOK, HEI
  end.
  assert (HE_k : forall n, (n < 1024)%nat -> ew E_k n = ew E0 n)
    by (intros n Hn; unfold E_k; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r5; lia]).
  assert (A_k_35 : ew E_k 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A35_0).
  assert (A_k_36 : ew E_k 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A36_0).
  assert (A_k_37 : ew E_k 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A37_0).
  assert (A_k_38 : ew E_k 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A38_0).
  assert (A_k_39 : ew E_k 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A39_0).
  assert (A_k_40 : ew E_k 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A40_0).
  assert (A_k_41 : ew E_k 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A41_0).
  assert (A_k_33 : ew E_k 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A33_0).
  assert (A_k_34 : ew E_k 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A34_0).
  assert (U8_k : bv_unsigned (ew E_k 249%nat) = TA_M) by (rewrite HE_k by lia; exact U8L).
  assert (U12_k : bv_unsigned (ew E_k 253%nat) = TA_OW) by (rewrite HE_k by lia; exact U12L).
  assert (U27_k : bv_unsigned (ew E_k 268%nat) = TA_g_now) by (rewrite HE_k by lia; exact U27L).
  assert (U1_k : bv_unsigned (ew E_k 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_k by lia; exact U1L).
  assert (U93_k : bv_unsigned (ew E_k 334%nat) = FCells.CELL_K) by (rewrite HE_k by lia; exact U93L).
  assert (Usp_k : bv_unsigned (ew E_k 2) = spZ regs) by (rewrite HE_k by lia; exact Usp0).
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 0 _ HS eq_refl) as RG0.
  cbn [ms_mem restrict] in RG0.
  assert (Vt4 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 112 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 112 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (Vt8 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 116 + Z.of_nat j)
      = Some (YO0f.le_byte (TW.s32_at Bw 12) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 116 4%N (SExt true 32 (SOff 35 0)) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. unfold U. rewrite (mw_sext_atom E_k 35 Bw 12 A_k_35), mw_u64.
    change (8 * Z.of_nat (N.to_nat 4%N)) with 32. apply mw_mod64. lia. }
  assert (Vt12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 120 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 120 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 11 _ HS eq_refl) as RG11.
  cbn [ms_mem restrict] in RG11.
  assert (VOW196 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 196 + Z.of_nat j) = Some (YO0f.le_byte (TW.s32_at Bw 65508 + 1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 196 4%N (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 1)) RG11 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. change (8 * Z.of_nat (N.to_nat 4%N)) with 32.
    exact (mw_u_add1 E_k (SExt true 32 (SOff 37 0)) (TW.s32_at Bw 65508) (mw_sext_atom E_k 37 Bw 65508 A_k_37)). }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 6 _ HS eq_refl) as RG6.
  cbn [ms_mem restrict] in RG6.
  assert (VM16 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 16 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 16 8%N (SLit 0) RG6 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 8 _ HS eq_refl) as RG8.
  cbn [ms_mem restrict] in RG8.
  assert (VM40 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 40 + Z.of_nat j) = Some (YO0f.le_byte (TW.u_at Bw 65000 8) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 40 8%N (SOff 39 0) RG8 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. rewrite (U_atom E_k 39 (TW.u_at Bw 65000 8) A_k_39 ltac:(pose proof (TWL.u_at_range Bw 65000 8) as HR;
      cbn [Z.of_nat] in HR; lia)). reflexivity. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 9 _ HS eq_refl) as RG9.
  cbn [ms_mem restrict] in RG9.
  assert (VM88 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 88 4%N (SLit 0) RG9 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 10 _ HS eq_refl) as RG10.
  cbn [ms_mem restrict] in RG10.
  assert (VOW0 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 0 + Z.of_nat j) = Some (YO0f.le_byte (10) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 0 4%N (SLit 10) RG10 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 5 _ HS eq_refl) as RG5.
  cbn [ms_mem restrict] in RG5.
  assert (VM12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 12 + Z.of_nat j) = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 12 4%N (SLit 1) RG5 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (HTW : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms_k)) (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 9) (TW.put 4 1))
             (65320 + 12 * 9) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 9) (TW.put 4 1))
        65312 (TW.put 4 10)) 12 (TW.put 4 1))).
  { apply (mw_fin_rd _ (aview segs (w_H W) memc) (aview segs (w_H W) (ms_mem ms_k)) _ (mw_world9 W memc (ms_mem ms_k) Bw _ 9 10 ltac:(lia)
      (mw_world4 W memc (ms_mem ms_k) Bw Htw VOW196 VM16 VM40 VM88) Vt4 Vt8 Vt12 VOW0 VM12)).
    intros x Hx Hni. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    destruct (Classical_Prop.classic (mw_winsk (spZ regs) 9 x)) as [Hw | Hw].
    - destruct Hw as [[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]] | Hw].
      + exfalso. unfold MWAKE_STK, MWAKE_FRAME in Hw. lia.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 12) (TA_M + 12 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 16) (TA_M + 16 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 40) (TA_M + 40 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 88) (TA_M + 88 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 0) (TA_OW + 0 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 196) (TA_OW + 196 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. destruct (Z_lt_le_dec x (TA_OW + (8 + 12 * 9))) as [D1|D1]; [| destruct (Z_lt_le_dec x (TA_OW + (12 + 12 * 9))) as [D2|D2]].
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (4 + 12 * 9)) (TA_OW + (4 + 12 * 9) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (8 + 12 * 9)) (TA_OW + (8 + 12 * 9) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (12 + 12 * 9)) (TA_OW + (12 + 12 * 9) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
    - apply KWk; [lia | exact Hw]. }
  mw_regv HS (Z_to_bv 5 1) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite HE_k by lia;
          rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  mw_regv HS (Z_to_bv 5 10) (w64 0) RF10
    ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mw_u64; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms_k)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E_k _ ms_k regs (mw_ex Bw) HS).
    - apply mw_agree; [intros n Hn; rewrite HE_k by lia; reflexivity | reflexivity].
    - vm_compute. reflexivity. }
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ mw_Zs (spZ regs) a ->
    aview segs (w_H W) (ms_mem ms_k) a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; apply KWk; [exact Ha
        | intros Hc0; exact (Hn (mw_winsk_Zs _ 9 a ltac:(lia) Hc0))]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  exact (mw_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 9) (TW.put 4 1))
             (65320 + 12 * 9) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 9) (TW.put 4 1))
        65312 (TW.put 4 10)) 12 (TW.put 4 1)) 0
           (ms_regs ms_k) (ms_mem ms_k) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GAk
           HTW HPF RF1 RF10 matF).
  }
  { (* arm 10 *)
  (* OW.n = 10 *)
  rewrite !En.
  mw_regv HS (Z_to_bv 5 14) (Z_to_bv 64 10) HN14
    ltac:(rewrite (mw_sext_atom E_r5 38 Bw 65312 A_r5_38), En; reflexivity).
  apply (fun HQ => st_ok_pi_pin_reg' E_r5 _ (restrict (w_H W) ms_r5) (Z_to_bv 5 14) 10 HQ HN14 ltac:(reflexivity)) in HS.
  assert (RTOK : region_ok segs E_r5 (ms_mem (restrict (w_H W) ms_r5)) (Ro_t 10)).
  { unfold Ro_t, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict A_OBJ].
    change (A_OBJ 12) with 253%nat. rewrite U12_r5. split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw).
    apply mw_inG_OW. unfold TW.SZ_OW. lia. }
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ssx _ => assert (RTD : all_disjoint E_r5 (Ro_t 10) (ss_mem ssx))
  end.
  { clear - Hsp Usp_r5 U8_r5 U12_r5 U27_r5 U1_r5 U93_r5.
    cbn [ss_mem all_disjoint add_cond]. unfold Ro_t, extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (A_OBJ 12) with 253%nat.
    rewrite ?Usp_r5, ?U8_r5, ?U12_r5, ?U27_r5, ?U1_r5, ?U93_r5.
    unfold TA_M, TA_OW, TA_g_now, FCells.GOT_CELL_K, FCells.CELL_K.
    repeat split; first [exact I | lia]. }
  apply (fun HQ => st_ok_pi_add_region E_r5 _ _ (Ro_t 10) HQ ltac:(vm_compute; reflexivity) RTOK RTD) in HS.
  clear RTOK HN14.
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r5 U8_r5 U12_r5 U12_r5. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KWk : forall a, 0 <= a < 2 ^ 64 -> ~ mw_winsk (spZ regs) 10 a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity;
      [| exact (KW6 a Ha ltac:(intros Hc0; apply Hn; left; exact Hc0))].
    eapply (kept_of_frame _ _ _ _ _ (mw_winsk (spZ regs) 10)).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r5, ?U8_r5, ?U12_r5 in Hx;
        unfold mw_winsk, mw_wins;
        first [ lia | left; left; lia | left; right; left; lia | left; right; right; left; lia
              | left; right; right; right; left; lia | left; right; right; right; right; left; lia
              | left; right; right; right; right; right; left; lia
              | left; right; right; right; right; right; right; lia | right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GAk : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA6 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_k := mf) in *; set (E_k := EF) in HS, SHOK, HEI
  end.
  assert (HE_k : forall n, (n < 1024)%nat -> ew E_k n = ew E0 n)
    by (intros n Hn; unfold E_k; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r5; lia]).
  assert (A_k_35 : ew E_k 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A35_0).
  assert (A_k_36 : ew E_k 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A36_0).
  assert (A_k_37 : ew E_k 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A37_0).
  assert (A_k_38 : ew E_k 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A38_0).
  assert (A_k_39 : ew E_k 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A39_0).
  assert (A_k_40 : ew E_k 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A40_0).
  assert (A_k_41 : ew E_k 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A41_0).
  assert (A_k_33 : ew E_k 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A33_0).
  assert (A_k_34 : ew E_k 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A34_0).
  assert (U8_k : bv_unsigned (ew E_k 249%nat) = TA_M) by (rewrite HE_k by lia; exact U8L).
  assert (U12_k : bv_unsigned (ew E_k 253%nat) = TA_OW) by (rewrite HE_k by lia; exact U12L).
  assert (U27_k : bv_unsigned (ew E_k 268%nat) = TA_g_now) by (rewrite HE_k by lia; exact U27L).
  assert (U1_k : bv_unsigned (ew E_k 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_k by lia; exact U1L).
  assert (U93_k : bv_unsigned (ew E_k 334%nat) = FCells.CELL_K) by (rewrite HE_k by lia; exact U93L).
  assert (Usp_k : bv_unsigned (ew E_k 2) = spZ regs) by (rewrite HE_k by lia; exact Usp0).
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 0 _ HS eq_refl) as RG0.
  cbn [ms_mem restrict] in RG0.
  assert (Vt4 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 124 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 124 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (Vt8 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 128 + Z.of_nat j)
      = Some (YO0f.le_byte (TW.s32_at Bw 12) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 128 4%N (SExt true 32 (SOff 35 0)) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. unfold U. rewrite (mw_sext_atom E_k 35 Bw 12 A_k_35), mw_u64.
    change (8 * Z.of_nat (N.to_nat 4%N)) with 32. apply mw_mod64. lia. }
  assert (Vt12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 132 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 132 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 11 _ HS eq_refl) as RG11.
  cbn [ms_mem restrict] in RG11.
  assert (VOW196 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 196 + Z.of_nat j) = Some (YO0f.le_byte (TW.s32_at Bw 65508 + 1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 196 4%N (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 1)) RG11 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. change (8 * Z.of_nat (N.to_nat 4%N)) with 32.
    exact (mw_u_add1 E_k (SExt true 32 (SOff 37 0)) (TW.s32_at Bw 65508) (mw_sext_atom E_k 37 Bw 65508 A_k_37)). }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 6 _ HS eq_refl) as RG6.
  cbn [ms_mem restrict] in RG6.
  assert (VM16 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 16 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 16 8%N (SLit 0) RG6 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 8 _ HS eq_refl) as RG8.
  cbn [ms_mem restrict] in RG8.
  assert (VM40 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 40 + Z.of_nat j) = Some (YO0f.le_byte (TW.u_at Bw 65000 8) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 40 8%N (SOff 39 0) RG8 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. rewrite (U_atom E_k 39 (TW.u_at Bw 65000 8) A_k_39 ltac:(pose proof (TWL.u_at_range Bw 65000 8) as HR;
      cbn [Z.of_nat] in HR; lia)). reflexivity. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 9 _ HS eq_refl) as RG9.
  cbn [ms_mem restrict] in RG9.
  assert (VM88 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 88 4%N (SLit 0) RG9 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 10 _ HS eq_refl) as RG10.
  cbn [ms_mem restrict] in RG10.
  assert (VOW0 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 0 + Z.of_nat j) = Some (YO0f.le_byte (11) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 0 4%N (SLit 11) RG10 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 5 _ HS eq_refl) as RG5.
  cbn [ms_mem restrict] in RG5.
  assert (VM12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 12 + Z.of_nat j) = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 12 4%N (SLit 1) RG5 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (HTW : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms_k)) (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 10) (TW.put 4 1))
             (65320 + 12 * 10) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 10) (TW.put 4 1))
        65312 (TW.put 4 11)) 12 (TW.put 4 1))).
  { apply (mw_fin_rd _ (aview segs (w_H W) memc) (aview segs (w_H W) (ms_mem ms_k)) _ (mw_world9 W memc (ms_mem ms_k) Bw _ 10 11 ltac:(lia)
      (mw_world4 W memc (ms_mem ms_k) Bw Htw VOW196 VM16 VM40 VM88) Vt4 Vt8 Vt12 VOW0 VM12)).
    intros x Hx Hni. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    destruct (Classical_Prop.classic (mw_winsk (spZ regs) 10 x)) as [Hw | Hw].
    - destruct Hw as [[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]] | Hw].
      + exfalso. unfold MWAKE_STK, MWAKE_FRAME in Hw. lia.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 12) (TA_M + 12 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 16) (TA_M + 16 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 40) (TA_M + 40 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 88) (TA_M + 88 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 0) (TA_OW + 0 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 196) (TA_OW + 196 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. destruct (Z_lt_le_dec x (TA_OW + (8 + 12 * 10))) as [D1|D1]; [| destruct (Z_lt_le_dec x (TA_OW + (12 + 12 * 10))) as [D2|D2]].
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (4 + 12 * 10)) (TA_OW + (4 + 12 * 10) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (8 + 12 * 10)) (TA_OW + (8 + 12 * 10) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (12 + 12 * 10)) (TA_OW + (12 + 12 * 10) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
    - apply KWk; [lia | exact Hw]. }
  mw_regv HS (Z_to_bv 5 1) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite HE_k by lia;
          rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  mw_regv HS (Z_to_bv 5 10) (w64 0) RF10
    ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mw_u64; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms_k)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E_k _ ms_k regs (mw_ex Bw) HS).
    - apply mw_agree; [intros n Hn; rewrite HE_k by lia; reflexivity | reflexivity].
    - vm_compute. reflexivity. }
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ mw_Zs (spZ regs) a ->
    aview segs (w_H W) (ms_mem ms_k) a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; apply KWk; [exact Ha
        | intros Hc0; exact (Hn (mw_winsk_Zs _ 10 a ltac:(lia) Hc0))]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  exact (mw_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 10) (TW.put 4 1))
             (65320 + 12 * 10) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 10) (TW.put 4 1))
        65312 (TW.put 4 11)) 12 (TW.put 4 1)) 0
           (ms_regs ms_k) (ms_mem ms_k) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GAk
           HTW HPF RF1 RF10 matF).
  }
  { (* arm 11 *)
  (* OW.n = 11 *)
  rewrite !En.
  mw_regv HS (Z_to_bv 5 14) (Z_to_bv 64 11) HN14
    ltac:(rewrite (mw_sext_atom E_r5 38 Bw 65312 A_r5_38), En; reflexivity).
  apply (fun HQ => st_ok_pi_pin_reg' E_r5 _ (restrict (w_H W) ms_r5) (Z_to_bv 5 14) 11 HQ HN14 ltac:(reflexivity)) in HS.
  assert (RTOK : region_ok segs E_r5 (ms_mem (restrict (w_H W) ms_r5)) (Ro_t 11)).
  { unfold Ro_t, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict A_OBJ].
    change (A_OBJ 12) with 253%nat. rewrite U12_r5. split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw).
    apply mw_inG_OW. unfold TW.SZ_OW. lia. }
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ssx _ => assert (RTD : all_disjoint E_r5 (Ro_t 11) (ss_mem ssx))
  end.
  { clear - Hsp Usp_r5 U8_r5 U12_r5 U27_r5 U1_r5 U93_r5.
    cbn [ss_mem all_disjoint add_cond]. unfold Ro_t, extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (A_OBJ 12) with 253%nat.
    rewrite ?Usp_r5, ?U8_r5, ?U12_r5, ?U27_r5, ?U1_r5, ?U93_r5.
    unfold TA_M, TA_OW, TA_g_now, FCells.GOT_CELL_K, FCells.CELL_K.
    repeat split; first [exact I | lia]. }
  apply (fun HQ => st_ok_pi_add_region E_r5 _ _ (Ro_t 11) HQ ltac:(vm_compute; reflexivity) RTOK RTD) in HS.
  clear RTOK HN14.
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r5 U8_r5 U12_r5 U12_r5. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KWk : forall a, 0 <= a < 2 ^ 64 -> ~ mw_winsk (spZ regs) 11 a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity;
      [| exact (KW6 a Ha ltac:(intros Hc0; apply Hn; left; exact Hc0))].
    eapply (kept_of_frame _ _ _ _ _ (mw_winsk (spZ regs) 11)).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r5, ?U8_r5, ?U12_r5 in Hx;
        unfold mw_winsk, mw_wins;
        first [ lia | left; left; lia | left; right; left; lia | left; right; right; left; lia
              | left; right; right; right; left; lia | left; right; right; right; right; left; lia
              | left; right; right; right; right; right; left; lia
              | left; right; right; right; right; right; right; lia | right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GAk : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA6 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_k := mf) in *; set (E_k := EF) in HS, SHOK, HEI
  end.
  assert (HE_k : forall n, (n < 1024)%nat -> ew E_k n = ew E0 n)
    by (intros n Hn; unfold E_k; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r5; lia]).
  assert (A_k_35 : ew E_k 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A35_0).
  assert (A_k_36 : ew E_k 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A36_0).
  assert (A_k_37 : ew E_k 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A37_0).
  assert (A_k_38 : ew E_k 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A38_0).
  assert (A_k_39 : ew E_k 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A39_0).
  assert (A_k_40 : ew E_k 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A40_0).
  assert (A_k_41 : ew E_k 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A41_0).
  assert (A_k_33 : ew E_k 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A33_0).
  assert (A_k_34 : ew E_k 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A34_0).
  assert (U8_k : bv_unsigned (ew E_k 249%nat) = TA_M) by (rewrite HE_k by lia; exact U8L).
  assert (U12_k : bv_unsigned (ew E_k 253%nat) = TA_OW) by (rewrite HE_k by lia; exact U12L).
  assert (U27_k : bv_unsigned (ew E_k 268%nat) = TA_g_now) by (rewrite HE_k by lia; exact U27L).
  assert (U1_k : bv_unsigned (ew E_k 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_k by lia; exact U1L).
  assert (U93_k : bv_unsigned (ew E_k 334%nat) = FCells.CELL_K) by (rewrite HE_k by lia; exact U93L).
  assert (Usp_k : bv_unsigned (ew E_k 2) = spZ regs) by (rewrite HE_k by lia; exact Usp0).
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 0 _ HS eq_refl) as RG0.
  cbn [ms_mem restrict] in RG0.
  assert (Vt4 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 136 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 136 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (Vt8 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 140 + Z.of_nat j)
      = Some (YO0f.le_byte (TW.s32_at Bw 12) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 140 4%N (SExt true 32 (SOff 35 0)) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. unfold U. rewrite (mw_sext_atom E_k 35 Bw 12 A_k_35), mw_u64.
    change (8 * Z.of_nat (N.to_nat 4%N)) with 32. apply mw_mod64. lia. }
  assert (Vt12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 144 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 144 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 11 _ HS eq_refl) as RG11.
  cbn [ms_mem restrict] in RG11.
  assert (VOW196 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 196 + Z.of_nat j) = Some (YO0f.le_byte (TW.s32_at Bw 65508 + 1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 196 4%N (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 1)) RG11 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. change (8 * Z.of_nat (N.to_nat 4%N)) with 32.
    exact (mw_u_add1 E_k (SExt true 32 (SOff 37 0)) (TW.s32_at Bw 65508) (mw_sext_atom E_k 37 Bw 65508 A_k_37)). }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 6 _ HS eq_refl) as RG6.
  cbn [ms_mem restrict] in RG6.
  assert (VM16 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 16 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 16 8%N (SLit 0) RG6 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 8 _ HS eq_refl) as RG8.
  cbn [ms_mem restrict] in RG8.
  assert (VM40 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 40 + Z.of_nat j) = Some (YO0f.le_byte (TW.u_at Bw 65000 8) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 40 8%N (SOff 39 0) RG8 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. rewrite (U_atom E_k 39 (TW.u_at Bw 65000 8) A_k_39 ltac:(pose proof (TWL.u_at_range Bw 65000 8) as HR;
      cbn [Z.of_nat] in HR; lia)). reflexivity. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 9 _ HS eq_refl) as RG9.
  cbn [ms_mem restrict] in RG9.
  assert (VM88 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 88 4%N (SLit 0) RG9 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 10 _ HS eq_refl) as RG10.
  cbn [ms_mem restrict] in RG10.
  assert (VOW0 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 0 + Z.of_nat j) = Some (YO0f.le_byte (12) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 0 4%N (SLit 12) RG10 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 5 _ HS eq_refl) as RG5.
  cbn [ms_mem restrict] in RG5.
  assert (VM12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 12 + Z.of_nat j) = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 12 4%N (SLit 1) RG5 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (HTW : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms_k)) (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 11) (TW.put 4 1))
             (65320 + 12 * 11) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 11) (TW.put 4 1))
        65312 (TW.put 4 12)) 12 (TW.put 4 1))).
  { apply (mw_fin_rd _ (aview segs (w_H W) memc) (aview segs (w_H W) (ms_mem ms_k)) _ (mw_world9 W memc (ms_mem ms_k) Bw _ 11 12 ltac:(lia)
      (mw_world4 W memc (ms_mem ms_k) Bw Htw VOW196 VM16 VM40 VM88) Vt4 Vt8 Vt12 VOW0 VM12)).
    intros x Hx Hni. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    destruct (Classical_Prop.classic (mw_winsk (spZ regs) 11 x)) as [Hw | Hw].
    - destruct Hw as [[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]] | Hw].
      + exfalso. unfold MWAKE_STK, MWAKE_FRAME in Hw. lia.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 12) (TA_M + 12 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 16) (TA_M + 16 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 40) (TA_M + 40 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 88) (TA_M + 88 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 0) (TA_OW + 0 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 196) (TA_OW + 196 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. destruct (Z_lt_le_dec x (TA_OW + (8 + 12 * 11))) as [D1|D1]; [| destruct (Z_lt_le_dec x (TA_OW + (12 + 12 * 11))) as [D2|D2]].
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (4 + 12 * 11)) (TA_OW + (4 + 12 * 11) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (8 + 12 * 11)) (TA_OW + (8 + 12 * 11) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (12 + 12 * 11)) (TA_OW + (12 + 12 * 11) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
    - apply KWk; [lia | exact Hw]. }
  mw_regv HS (Z_to_bv 5 1) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite HE_k by lia;
          rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  mw_regv HS (Z_to_bv 5 10) (w64 0) RF10
    ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mw_u64; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms_k)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E_k _ ms_k regs (mw_ex Bw) HS).
    - apply mw_agree; [intros n Hn; rewrite HE_k by lia; reflexivity | reflexivity].
    - vm_compute. reflexivity. }
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ mw_Zs (spZ regs) a ->
    aview segs (w_H W) (ms_mem ms_k) a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; apply KWk; [exact Ha
        | intros Hc0; exact (Hn (mw_winsk_Zs _ 11 a ltac:(lia) Hc0))]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  exact (mw_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 11) (TW.put 4 1))
             (65320 + 12 * 11) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 11) (TW.put 4 1))
        65312 (TW.put 4 12)) 12 (TW.put 4 1)) 0
           (ms_regs ms_k) (ms_mem ms_k) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GAk
           HTW HPF RF1 RF10 matF).
  }
  { (* arm 12 *)
  (* OW.n = 12 *)
  rewrite !En.
  mw_regv HS (Z_to_bv 5 14) (Z_to_bv 64 12) HN14
    ltac:(rewrite (mw_sext_atom E_r5 38 Bw 65312 A_r5_38), En; reflexivity).
  apply (fun HQ => st_ok_pi_pin_reg' E_r5 _ (restrict (w_H W) ms_r5) (Z_to_bv 5 14) 12 HQ HN14 ltac:(reflexivity)) in HS.
  assert (RTOK : region_ok segs E_r5 (ms_mem (restrict (w_H W) ms_r5)) (Ro_t 12)).
  { unfold Ro_t, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict A_OBJ].
    change (A_OBJ 12) with 253%nat. rewrite U12_r5. split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw).
    apply mw_inG_OW. unfold TW.SZ_OW. lia. }
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ssx _ => assert (RTD : all_disjoint E_r5 (Ro_t 12) (ss_mem ssx))
  end.
  { clear - Hsp Usp_r5 U8_r5 U12_r5 U27_r5 U1_r5 U93_r5.
    cbn [ss_mem all_disjoint add_cond]. unfold Ro_t, extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (A_OBJ 12) with 253%nat.
    rewrite ?Usp_r5, ?U8_r5, ?U12_r5, ?U27_r5, ?U1_r5, ?U93_r5.
    unfold TA_M, TA_OW, TA_g_now, FCells.GOT_CELL_K, FCells.CELL_K.
    repeat split; first [exact I | lia]. }
  apply (fun HQ => st_ok_pi_add_region E_r5 _ _ (Ro_t 12) HQ ltac:(vm_compute; reflexivity) RTOK RTD) in HS.
  clear RTOK HN14.
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r5 U8_r5 U12_r5 U12_r5. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KWk : forall a, 0 <= a < 2 ^ 64 -> ~ mw_winsk (spZ regs) 12 a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity;
      [| exact (KW6 a Ha ltac:(intros Hc0; apply Hn; left; exact Hc0))].
    eapply (kept_of_frame _ _ _ _ _ (mw_winsk (spZ regs) 12)).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r5, ?U8_r5, ?U12_r5 in Hx;
        unfold mw_winsk, mw_wins;
        first [ lia | left; left; lia | left; right; left; lia | left; right; right; left; lia
              | left; right; right; right; left; lia | left; right; right; right; right; left; lia
              | left; right; right; right; right; right; left; lia
              | left; right; right; right; right; right; right; lia | right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GAk : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA6 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_k := mf) in *; set (E_k := EF) in HS, SHOK, HEI
  end.
  assert (HE_k : forall n, (n < 1024)%nat -> ew E_k n = ew E0 n)
    by (intros n Hn; unfold E_k; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r5; lia]).
  assert (A_k_35 : ew E_k 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A35_0).
  assert (A_k_36 : ew E_k 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A36_0).
  assert (A_k_37 : ew E_k 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A37_0).
  assert (A_k_38 : ew E_k 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A38_0).
  assert (A_k_39 : ew E_k 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A39_0).
  assert (A_k_40 : ew E_k 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A40_0).
  assert (A_k_41 : ew E_k 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A41_0).
  assert (A_k_33 : ew E_k 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A33_0).
  assert (A_k_34 : ew E_k 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A34_0).
  assert (U8_k : bv_unsigned (ew E_k 249%nat) = TA_M) by (rewrite HE_k by lia; exact U8L).
  assert (U12_k : bv_unsigned (ew E_k 253%nat) = TA_OW) by (rewrite HE_k by lia; exact U12L).
  assert (U27_k : bv_unsigned (ew E_k 268%nat) = TA_g_now) by (rewrite HE_k by lia; exact U27L).
  assert (U1_k : bv_unsigned (ew E_k 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_k by lia; exact U1L).
  assert (U93_k : bv_unsigned (ew E_k 334%nat) = FCells.CELL_K) by (rewrite HE_k by lia; exact U93L).
  assert (Usp_k : bv_unsigned (ew E_k 2) = spZ regs) by (rewrite HE_k by lia; exact Usp0).
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 0 _ HS eq_refl) as RG0.
  cbn [ms_mem restrict] in RG0.
  assert (Vt4 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 148 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 148 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (Vt8 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 152 + Z.of_nat j)
      = Some (YO0f.le_byte (TW.s32_at Bw 12) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 152 4%N (SExt true 32 (SOff 35 0)) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. unfold U. rewrite (mw_sext_atom E_k 35 Bw 12 A_k_35), mw_u64.
    change (8 * Z.of_nat (N.to_nat 4%N)) with 32. apply mw_mod64. lia. }
  assert (Vt12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 156 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 156 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 11 _ HS eq_refl) as RG11.
  cbn [ms_mem restrict] in RG11.
  assert (VOW196 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 196 + Z.of_nat j) = Some (YO0f.le_byte (TW.s32_at Bw 65508 + 1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 196 4%N (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 1)) RG11 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. change (8 * Z.of_nat (N.to_nat 4%N)) with 32.
    exact (mw_u_add1 E_k (SExt true 32 (SOff 37 0)) (TW.s32_at Bw 65508) (mw_sext_atom E_k 37 Bw 65508 A_k_37)). }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 6 _ HS eq_refl) as RG6.
  cbn [ms_mem restrict] in RG6.
  assert (VM16 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 16 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 16 8%N (SLit 0) RG6 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 8 _ HS eq_refl) as RG8.
  cbn [ms_mem restrict] in RG8.
  assert (VM40 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 40 + Z.of_nat j) = Some (YO0f.le_byte (TW.u_at Bw 65000 8) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 40 8%N (SOff 39 0) RG8 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. rewrite (U_atom E_k 39 (TW.u_at Bw 65000 8) A_k_39 ltac:(pose proof (TWL.u_at_range Bw 65000 8) as HR;
      cbn [Z.of_nat] in HR; lia)). reflexivity. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 9 _ HS eq_refl) as RG9.
  cbn [ms_mem restrict] in RG9.
  assert (VM88 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 88 4%N (SLit 0) RG9 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 10 _ HS eq_refl) as RG10.
  cbn [ms_mem restrict] in RG10.
  assert (VOW0 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 0 + Z.of_nat j) = Some (YO0f.le_byte (13) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 0 4%N (SLit 13) RG10 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 5 _ HS eq_refl) as RG5.
  cbn [ms_mem restrict] in RG5.
  assert (VM12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 12 + Z.of_nat j) = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 12 4%N (SLit 1) RG5 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (HTW : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms_k)) (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 12) (TW.put 4 1))
             (65320 + 12 * 12) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 12) (TW.put 4 1))
        65312 (TW.put 4 13)) 12 (TW.put 4 1))).
  { apply (mw_fin_rd _ (aview segs (w_H W) memc) (aview segs (w_H W) (ms_mem ms_k)) _ (mw_world9 W memc (ms_mem ms_k) Bw _ 12 13 ltac:(lia)
      (mw_world4 W memc (ms_mem ms_k) Bw Htw VOW196 VM16 VM40 VM88) Vt4 Vt8 Vt12 VOW0 VM12)).
    intros x Hx Hni. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    destruct (Classical_Prop.classic (mw_winsk (spZ regs) 12 x)) as [Hw | Hw].
    - destruct Hw as [[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]] | Hw].
      + exfalso. unfold MWAKE_STK, MWAKE_FRAME in Hw. lia.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 12) (TA_M + 12 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 16) (TA_M + 16 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 40) (TA_M + 40 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 88) (TA_M + 88 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 0) (TA_OW + 0 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 196) (TA_OW + 196 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. destruct (Z_lt_le_dec x (TA_OW + (8 + 12 * 12))) as [D1|D1]; [| destruct (Z_lt_le_dec x (TA_OW + (12 + 12 * 12))) as [D2|D2]].
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (4 + 12 * 12)) (TA_OW + (4 + 12 * 12) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (8 + 12 * 12)) (TA_OW + (8 + 12 * 12) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (12 + 12 * 12)) (TA_OW + (12 + 12 * 12) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
    - apply KWk; [lia | exact Hw]. }
  mw_regv HS (Z_to_bv 5 1) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite HE_k by lia;
          rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  mw_regv HS (Z_to_bv 5 10) (w64 0) RF10
    ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mw_u64; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms_k)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E_k _ ms_k regs (mw_ex Bw) HS).
    - apply mw_agree; [intros n Hn; rewrite HE_k by lia; reflexivity | reflexivity].
    - vm_compute. reflexivity. }
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ mw_Zs (spZ regs) a ->
    aview segs (w_H W) (ms_mem ms_k) a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; apply KWk; [exact Ha
        | intros Hc0; exact (Hn (mw_winsk_Zs _ 12 a ltac:(lia) Hc0))]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  exact (mw_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 12) (TW.put 4 1))
             (65320 + 12 * 12) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 12) (TW.put 4 1))
        65312 (TW.put 4 13)) 12 (TW.put 4 1)) 0
           (ms_regs ms_k) (ms_mem ms_k) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GAk
           HTW HPF RF1 RF10 matF).
  }
  { (* arm 13 *)
  (* OW.n = 13 *)
  rewrite !En.
  mw_regv HS (Z_to_bv 5 14) (Z_to_bv 64 13) HN14
    ltac:(rewrite (mw_sext_atom E_r5 38 Bw 65312 A_r5_38), En; reflexivity).
  apply (fun HQ => st_ok_pi_pin_reg' E_r5 _ (restrict (w_H W) ms_r5) (Z_to_bv 5 14) 13 HQ HN14 ltac:(reflexivity)) in HS.
  assert (RTOK : region_ok segs E_r5 (ms_mem (restrict (w_H W) ms_r5)) (Ro_t 13)).
  { unfold Ro_t, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict A_OBJ].
    change (A_OBJ 12) with 253%nat. rewrite U12_r5. split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw).
    apply mw_inG_OW. unfold TW.SZ_OW. lia. }
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ssx _ => assert (RTD : all_disjoint E_r5 (Ro_t 13) (ss_mem ssx))
  end.
  { clear - Hsp Usp_r5 U8_r5 U12_r5 U27_r5 U1_r5 U93_r5.
    cbn [ss_mem all_disjoint add_cond]. unfold Ro_t, extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (A_OBJ 12) with 253%nat.
    rewrite ?Usp_r5, ?U8_r5, ?U12_r5, ?U27_r5, ?U1_r5, ?U93_r5.
    unfold TA_M, TA_OW, TA_g_now, FCells.GOT_CELL_K, FCells.CELL_K.
    repeat split; first [exact I | lia]. }
  apply (fun HQ => st_ok_pi_add_region E_r5 _ _ (Ro_t 13) HQ ltac:(vm_compute; reflexivity) RTOK RTD) in HS.
  clear RTOK HN14.
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r5 U8_r5 U12_r5 U12_r5. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KWk : forall a, 0 <= a < 2 ^ 64 -> ~ mw_winsk (spZ regs) 13 a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity;
      [| exact (KW6 a Ha ltac:(intros Hc0; apply Hn; left; exact Hc0))].
    eapply (kept_of_frame _ _ _ _ _ (mw_winsk (spZ regs) 13)).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r5, ?U8_r5, ?U12_r5 in Hx;
        unfold mw_winsk, mw_wins;
        first [ lia | left; left; lia | left; right; left; lia | left; right; right; left; lia
              | left; right; right; right; left; lia | left; right; right; right; right; left; lia
              | left; right; right; right; right; right; left; lia
              | left; right; right; right; right; right; right; lia | right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GAk : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA6 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_k := mf) in *; set (E_k := EF) in HS, SHOK, HEI
  end.
  assert (HE_k : forall n, (n < 1024)%nat -> ew E_k n = ew E0 n)
    by (intros n Hn; unfold E_k; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r5; lia]).
  assert (A_k_35 : ew E_k 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A35_0).
  assert (A_k_36 : ew E_k 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A36_0).
  assert (A_k_37 : ew E_k 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A37_0).
  assert (A_k_38 : ew E_k 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A38_0).
  assert (A_k_39 : ew E_k 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A39_0).
  assert (A_k_40 : ew E_k 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A40_0).
  assert (A_k_41 : ew E_k 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A41_0).
  assert (A_k_33 : ew E_k 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A33_0).
  assert (A_k_34 : ew E_k 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A34_0).
  assert (U8_k : bv_unsigned (ew E_k 249%nat) = TA_M) by (rewrite HE_k by lia; exact U8L).
  assert (U12_k : bv_unsigned (ew E_k 253%nat) = TA_OW) by (rewrite HE_k by lia; exact U12L).
  assert (U27_k : bv_unsigned (ew E_k 268%nat) = TA_g_now) by (rewrite HE_k by lia; exact U27L).
  assert (U1_k : bv_unsigned (ew E_k 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_k by lia; exact U1L).
  assert (U93_k : bv_unsigned (ew E_k 334%nat) = FCells.CELL_K) by (rewrite HE_k by lia; exact U93L).
  assert (Usp_k : bv_unsigned (ew E_k 2) = spZ regs) by (rewrite HE_k by lia; exact Usp0).
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 0 _ HS eq_refl) as RG0.
  cbn [ms_mem restrict] in RG0.
  assert (Vt4 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 160 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 160 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (Vt8 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 164 + Z.of_nat j)
      = Some (YO0f.le_byte (TW.s32_at Bw 12) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 164 4%N (SExt true 32 (SOff 35 0)) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. unfold U. rewrite (mw_sext_atom E_k 35 Bw 12 A_k_35), mw_u64.
    change (8 * Z.of_nat (N.to_nat 4%N)) with 32. apply mw_mod64. lia. }
  assert (Vt12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 168 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 168 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 11 _ HS eq_refl) as RG11.
  cbn [ms_mem restrict] in RG11.
  assert (VOW196 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 196 + Z.of_nat j) = Some (YO0f.le_byte (TW.s32_at Bw 65508 + 1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 196 4%N (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 1)) RG11 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. change (8 * Z.of_nat (N.to_nat 4%N)) with 32.
    exact (mw_u_add1 E_k (SExt true 32 (SOff 37 0)) (TW.s32_at Bw 65508) (mw_sext_atom E_k 37 Bw 65508 A_k_37)). }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 6 _ HS eq_refl) as RG6.
  cbn [ms_mem restrict] in RG6.
  assert (VM16 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 16 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 16 8%N (SLit 0) RG6 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 8 _ HS eq_refl) as RG8.
  cbn [ms_mem restrict] in RG8.
  assert (VM40 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 40 + Z.of_nat j) = Some (YO0f.le_byte (TW.u_at Bw 65000 8) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 40 8%N (SOff 39 0) RG8 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. rewrite (U_atom E_k 39 (TW.u_at Bw 65000 8) A_k_39 ltac:(pose proof (TWL.u_at_range Bw 65000 8) as HR;
      cbn [Z.of_nat] in HR; lia)). reflexivity. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 9 _ HS eq_refl) as RG9.
  cbn [ms_mem restrict] in RG9.
  assert (VM88 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 88 4%N (SLit 0) RG9 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 10 _ HS eq_refl) as RG10.
  cbn [ms_mem restrict] in RG10.
  assert (VOW0 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 0 + Z.of_nat j) = Some (YO0f.le_byte (14) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 0 4%N (SLit 14) RG10 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 5 _ HS eq_refl) as RG5.
  cbn [ms_mem restrict] in RG5.
  assert (VM12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 12 + Z.of_nat j) = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 12 4%N (SLit 1) RG5 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (HTW : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms_k)) (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 13) (TW.put 4 1))
             (65320 + 12 * 13) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 13) (TW.put 4 1))
        65312 (TW.put 4 14)) 12 (TW.put 4 1))).
  { apply (mw_fin_rd _ (aview segs (w_H W) memc) (aview segs (w_H W) (ms_mem ms_k)) _ (mw_world9 W memc (ms_mem ms_k) Bw _ 13 14 ltac:(lia)
      (mw_world4 W memc (ms_mem ms_k) Bw Htw VOW196 VM16 VM40 VM88) Vt4 Vt8 Vt12 VOW0 VM12)).
    intros x Hx Hni. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    destruct (Classical_Prop.classic (mw_winsk (spZ regs) 13 x)) as [Hw | Hw].
    - destruct Hw as [[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]] | Hw].
      + exfalso. unfold MWAKE_STK, MWAKE_FRAME in Hw. lia.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 12) (TA_M + 12 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 16) (TA_M + 16 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 40) (TA_M + 40 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 88) (TA_M + 88 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 0) (TA_OW + 0 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 196) (TA_OW + 196 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. destruct (Z_lt_le_dec x (TA_OW + (8 + 12 * 13))) as [D1|D1]; [| destruct (Z_lt_le_dec x (TA_OW + (12 + 12 * 13))) as [D2|D2]].
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (4 + 12 * 13)) (TA_OW + (4 + 12 * 13) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (8 + 12 * 13)) (TA_OW + (8 + 12 * 13) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (12 + 12 * 13)) (TA_OW + (12 + 12 * 13) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
    - apply KWk; [lia | exact Hw]. }
  mw_regv HS (Z_to_bv 5 1) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite HE_k by lia;
          rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  mw_regv HS (Z_to_bv 5 10) (w64 0) RF10
    ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mw_u64; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms_k)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E_k _ ms_k regs (mw_ex Bw) HS).
    - apply mw_agree; [intros n Hn; rewrite HE_k by lia; reflexivity | reflexivity].
    - vm_compute. reflexivity. }
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ mw_Zs (spZ regs) a ->
    aview segs (w_H W) (ms_mem ms_k) a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; apply KWk; [exact Ha
        | intros Hc0; exact (Hn (mw_winsk_Zs _ 13 a ltac:(lia) Hc0))]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  exact (mw_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 13) (TW.put 4 1))
             (65320 + 12 * 13) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 13) (TW.put 4 1))
        65312 (TW.put 4 14)) 12 (TW.put 4 1)) 0
           (ms_regs ms_k) (ms_mem ms_k) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GAk
           HTW HPF RF1 RF10 matF).
  }
  { (* arm 14 *)
  (* OW.n = 14 *)
  rewrite !En.
  mw_regv HS (Z_to_bv 5 14) (Z_to_bv 64 14) HN14
    ltac:(rewrite (mw_sext_atom E_r5 38 Bw 65312 A_r5_38), En; reflexivity).
  apply (fun HQ => st_ok_pi_pin_reg' E_r5 _ (restrict (w_H W) ms_r5) (Z_to_bv 5 14) 14 HQ HN14 ltac:(reflexivity)) in HS.
  assert (RTOK : region_ok segs E_r5 (ms_mem (restrict (w_H W) ms_r5)) (Ro_t 14)).
  { unfold Ro_t, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict A_OBJ].
    change (A_OBJ 12) with 253%nat. rewrite U12_r5. split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw).
    apply mw_inG_OW. unfold TW.SZ_OW. lia. }
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ssx _ => assert (RTD : all_disjoint E_r5 (Ro_t 14) (ss_mem ssx))
  end.
  { clear - Hsp Usp_r5 U8_r5 U12_r5 U27_r5 U1_r5 U93_r5.
    cbn [ss_mem all_disjoint add_cond]. unfold Ro_t, extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (A_OBJ 12) with 253%nat.
    rewrite ?Usp_r5, ?U8_r5, ?U12_r5, ?U27_r5, ?U1_r5, ?U93_r5.
    unfold TA_M, TA_OW, TA_g_now, FCells.GOT_CELL_K, FCells.CELL_K.
    repeat split; first [exact I | lia]. }
  apply (fun HQ => st_ok_pi_add_region E_r5 _ _ (Ro_t 14) HQ ltac:(vm_compute; reflexivity) RTOK RTD) in HS.
  clear RTOK HN14.
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r5 U8_r5 U12_r5 U12_r5. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KWk : forall a, 0 <= a < 2 ^ 64 -> ~ mw_winsk (spZ regs) 14 a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity;
      [| exact (KW6 a Ha ltac:(intros Hc0; apply Hn; left; exact Hc0))].
    eapply (kept_of_frame _ _ _ _ _ (mw_winsk (spZ regs) 14)).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r5, ?U8_r5, ?U12_r5 in Hx;
        unfold mw_winsk, mw_wins;
        first [ lia | left; left; lia | left; right; left; lia | left; right; right; left; lia
              | left; right; right; right; left; lia | left; right; right; right; right; left; lia
              | left; right; right; right; right; right; left; lia
              | left; right; right; right; right; right; right; lia | right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GAk : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA6 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_k := mf) in *; set (E_k := EF) in HS, SHOK, HEI
  end.
  assert (HE_k : forall n, (n < 1024)%nat -> ew E_k n = ew E0 n)
    by (intros n Hn; unfold E_k; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r5; lia]).
  assert (A_k_35 : ew E_k 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A35_0).
  assert (A_k_36 : ew E_k 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A36_0).
  assert (A_k_37 : ew E_k 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A37_0).
  assert (A_k_38 : ew E_k 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A38_0).
  assert (A_k_39 : ew E_k 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A39_0).
  assert (A_k_40 : ew E_k 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A40_0).
  assert (A_k_41 : ew E_k 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A41_0).
  assert (A_k_33 : ew E_k 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A33_0).
  assert (A_k_34 : ew E_k 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A34_0).
  assert (U8_k : bv_unsigned (ew E_k 249%nat) = TA_M) by (rewrite HE_k by lia; exact U8L).
  assert (U12_k : bv_unsigned (ew E_k 253%nat) = TA_OW) by (rewrite HE_k by lia; exact U12L).
  assert (U27_k : bv_unsigned (ew E_k 268%nat) = TA_g_now) by (rewrite HE_k by lia; exact U27L).
  assert (U1_k : bv_unsigned (ew E_k 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_k by lia; exact U1L).
  assert (U93_k : bv_unsigned (ew E_k 334%nat) = FCells.CELL_K) by (rewrite HE_k by lia; exact U93L).
  assert (Usp_k : bv_unsigned (ew E_k 2) = spZ regs) by (rewrite HE_k by lia; exact Usp0).
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 0 _ HS eq_refl) as RG0.
  cbn [ms_mem restrict] in RG0.
  assert (Vt4 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 172 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 172 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (Vt8 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 176 + Z.of_nat j)
      = Some (YO0f.le_byte (TW.s32_at Bw 12) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 176 4%N (SExt true 32 (SOff 35 0)) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. unfold U. rewrite (mw_sext_atom E_k 35 Bw 12 A_k_35), mw_u64.
    change (8 * Z.of_nat (N.to_nat 4%N)) with 32. apply mw_mod64. lia. }
  assert (Vt12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 180 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 180 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 11 _ HS eq_refl) as RG11.
  cbn [ms_mem restrict] in RG11.
  assert (VOW196 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 196 + Z.of_nat j) = Some (YO0f.le_byte (TW.s32_at Bw 65508 + 1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 196 4%N (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 1)) RG11 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. change (8 * Z.of_nat (N.to_nat 4%N)) with 32.
    exact (mw_u_add1 E_k (SExt true 32 (SOff 37 0)) (TW.s32_at Bw 65508) (mw_sext_atom E_k 37 Bw 65508 A_k_37)). }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 6 _ HS eq_refl) as RG6.
  cbn [ms_mem restrict] in RG6.
  assert (VM16 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 16 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 16 8%N (SLit 0) RG6 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 8 _ HS eq_refl) as RG8.
  cbn [ms_mem restrict] in RG8.
  assert (VM40 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 40 + Z.of_nat j) = Some (YO0f.le_byte (TW.u_at Bw 65000 8) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 40 8%N (SOff 39 0) RG8 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. rewrite (U_atom E_k 39 (TW.u_at Bw 65000 8) A_k_39 ltac:(pose proof (TWL.u_at_range Bw 65000 8) as HR;
      cbn [Z.of_nat] in HR; lia)). reflexivity. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 9 _ HS eq_refl) as RG9.
  cbn [ms_mem restrict] in RG9.
  assert (VM88 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 88 4%N (SLit 0) RG9 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 10 _ HS eq_refl) as RG10.
  cbn [ms_mem restrict] in RG10.
  assert (VOW0 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 0 + Z.of_nat j) = Some (YO0f.le_byte (15) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 0 4%N (SLit 15) RG10 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 5 _ HS eq_refl) as RG5.
  cbn [ms_mem restrict] in RG5.
  assert (VM12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 12 + Z.of_nat j) = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 12 4%N (SLit 1) RG5 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (HTW : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms_k)) (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 14) (TW.put 4 1))
             (65320 + 12 * 14) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 14) (TW.put 4 1))
        65312 (TW.put 4 15)) 12 (TW.put 4 1))).
  { apply (mw_fin_rd _ (aview segs (w_H W) memc) (aview segs (w_H W) (ms_mem ms_k)) _ (mw_world9 W memc (ms_mem ms_k) Bw _ 14 15 ltac:(lia)
      (mw_world4 W memc (ms_mem ms_k) Bw Htw VOW196 VM16 VM40 VM88) Vt4 Vt8 Vt12 VOW0 VM12)).
    intros x Hx Hni. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    destruct (Classical_Prop.classic (mw_winsk (spZ regs) 14 x)) as [Hw | Hw].
    - destruct Hw as [[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]] | Hw].
      + exfalso. unfold MWAKE_STK, MWAKE_FRAME in Hw. lia.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 12) (TA_M + 12 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 16) (TA_M + 16 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 40) (TA_M + 40 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 88) (TA_M + 88 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 0) (TA_OW + 0 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 196) (TA_OW + 196 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. destruct (Z_lt_le_dec x (TA_OW + (8 + 12 * 14))) as [D1|D1]; [| destruct (Z_lt_le_dec x (TA_OW + (12 + 12 * 14))) as [D2|D2]].
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (4 + 12 * 14)) (TA_OW + (4 + 12 * 14) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (8 + 12 * 14)) (TA_OW + (8 + 12 * 14) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (12 + 12 * 14)) (TA_OW + (12 + 12 * 14) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
    - apply KWk; [lia | exact Hw]. }
  mw_regv HS (Z_to_bv 5 1) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite HE_k by lia;
          rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  mw_regv HS (Z_to_bv 5 10) (w64 0) RF10
    ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mw_u64; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms_k)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E_k _ ms_k regs (mw_ex Bw) HS).
    - apply mw_agree; [intros n Hn; rewrite HE_k by lia; reflexivity | reflexivity].
    - vm_compute. reflexivity. }
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ mw_Zs (spZ regs) a ->
    aview segs (w_H W) (ms_mem ms_k) a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; apply KWk; [exact Ha
        | intros Hc0; exact (Hn (mw_winsk_Zs _ 14 a ltac:(lia) Hc0))]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  exact (mw_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 14) (TW.put 4 1))
             (65320 + 12 * 14) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 14) (TW.put 4 1))
        65312 (TW.put 4 15)) 12 (TW.put 4 1)) 0
           (ms_regs ms_k) (ms_mem ms_k) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GAk
           HTW HPF RF1 RF10 matF).
  }
  { (* arm 15 *)
  (* OW.n = 15 *)
  rewrite !En.
  mw_regv HS (Z_to_bv 5 14) (Z_to_bv 64 15) HN14
    ltac:(rewrite (mw_sext_atom E_r5 38 Bw 65312 A_r5_38), En; reflexivity).
  apply (fun HQ => st_ok_pi_pin_reg' E_r5 _ (restrict (w_H W) ms_r5) (Z_to_bv 5 14) 15 HQ HN14 ltac:(reflexivity)) in HS.
  assert (RTOK : region_ok segs E_r5 (ms_mem (restrict (w_H W) ms_r5)) (Ro_t 15)).
  { unfold Ro_t, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict A_OBJ].
    change (A_OBJ 12) with 253%nat. rewrite U12_r5. split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw).
    apply mw_inG_OW. unfold TW.SZ_OW. lia. }
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ssx _ => assert (RTD : all_disjoint E_r5 (Ro_t 15) (ss_mem ssx))
  end.
  { clear - Hsp Usp_r5 U8_r5 U12_r5 U27_r5 U1_r5 U93_r5.
    cbn [ss_mem all_disjoint add_cond]. unfold Ro_t, extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (A_OBJ 12) with 253%nat.
    rewrite ?Usp_r5, ?U8_r5, ?U12_r5, ?U27_r5, ?U1_r5, ?U93_r5.
    unfold TA_M, TA_OW, TA_g_now, FCells.GOT_CELL_K, FCells.CELL_K.
    repeat split; first [exact I | lia]. }
  apply (fun HQ => st_ok_pi_add_region E_r5 _ _ (Ro_t 15) HQ ltac:(vm_compute; reflexivity) RTOK RTD) in HS.
  clear RTOK HN14.
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r5 U8_r5 U12_r5 U12_r5. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KWk : forall a, 0 <= a < 2 ^ 64 -> ~ mw_winsk (spZ regs) 15 a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity;
      [| exact (KW6 a Ha ltac:(intros Hc0; apply Hn; left; exact Hc0))].
    eapply (kept_of_frame _ _ _ _ _ (mw_winsk (spZ regs) 15)).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r5, ?U8_r5, ?U12_r5 in Hx;
        unfold mw_winsk, mw_wins;
        first [ lia | left; left; lia | left; right; left; lia | left; right; right; left; lia
              | left; right; right; right; left; lia | left; right; right; right; right; left; lia
              | left; right; right; right; right; right; left; lia
              | left; right; right; right; right; right; right; lia | right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GAk : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA6 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_k := mf) in *; set (E_k := EF) in HS, SHOK, HEI
  end.
  assert (HE_k : forall n, (n < 1024)%nat -> ew E_k n = ew E0 n)
    by (intros n Hn; unfold E_k; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r5; lia]).
  assert (A_k_35 : ew E_k 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A35_0).
  assert (A_k_36 : ew E_k 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A36_0).
  assert (A_k_37 : ew E_k 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A37_0).
  assert (A_k_38 : ew E_k 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A38_0).
  assert (A_k_39 : ew E_k 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A39_0).
  assert (A_k_40 : ew E_k 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A40_0).
  assert (A_k_41 : ew E_k 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_k by lia; exact A41_0).
  assert (A_k_33 : ew E_k 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A33_0).
  assert (A_k_34 : ew E_k 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_k by lia; exact A34_0).
  assert (U8_k : bv_unsigned (ew E_k 249%nat) = TA_M) by (rewrite HE_k by lia; exact U8L).
  assert (U12_k : bv_unsigned (ew E_k 253%nat) = TA_OW) by (rewrite HE_k by lia; exact U12L).
  assert (U27_k : bv_unsigned (ew E_k 268%nat) = TA_g_now) by (rewrite HE_k by lia; exact U27L).
  assert (U1_k : bv_unsigned (ew E_k 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_k by lia; exact U1L).
  assert (U93_k : bv_unsigned (ew E_k 334%nat) = FCells.CELL_K) by (rewrite HE_k by lia; exact U93L).
  assert (Usp_k : bv_unsigned (ew E_k 2) = spZ regs) by (rewrite HE_k by lia; exact Usp0).
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 0 _ HS eq_refl) as RG0.
  cbn [ms_mem restrict] in RG0.
  assert (Vt4 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 184 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 184 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (Vt8 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 188 + Z.of_nat j)
      = Some (YO0f.le_byte (TW.s32_at Bw 12) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 188 4%N (SExt true 32 (SOff 35 0)) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. unfold U. rewrite (mw_sext_atom E_k 35 Bw 12 A_k_35), mw_u64.
    change (8 * Z.of_nat (N.to_nat 4%N)) with 32. apply mw_mod64. lia. }
  assert (Vt12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 192 + Z.of_nat j)
      = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 192 4%N (SLit 1) RG0 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto 10) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 11 _ HS eq_refl) as RG11.
  cbn [ms_mem restrict] in RG11.
  assert (VOW196 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 196 + Z.of_nat j) = Some (YO0f.le_byte (TW.s32_at Bw 65508 + 1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 196 4%N (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 1)) RG11 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. change (8 * Z.of_nat (N.to_nat 4%N)) with 32.
    exact (mw_u_add1 E_k (SExt true 32 (SOff 37 0)) (TW.s32_at Bw 65508) (mw_sext_atom E_k 37 Bw 65508 A_k_37)). }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 6 _ HS eq_refl) as RG6.
  cbn [ms_mem restrict] in RG6.
  assert (VM16 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 16 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 16 8%N (SLit 0) RG6 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 8 _ HS eq_refl) as RG8.
  cbn [ms_mem restrict] in RG8.
  assert (VM40 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 40 + Z.of_nat j) = Some (YO0f.le_byte (TW.u_at Bw 65000 8) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 40 8%N (SOff 39 0) RG8 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. rewrite (U_atom E_k 39 (TW.u_at Bw 65000 8) A_k_39 ltac:(pose proof (TWL.u_at_range Bw 65000 8) as HR;
      cbn [Z.of_nat] in HR; lia)). reflexivity. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 9 _ HS eq_refl) as RG9.
  cbn [ms_mem restrict] in RG9.
  assert (VM88 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 88 4%N (SLit 0) RG9 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 10 _ HS eq_refl) as RG10.
  cbn [ms_mem restrict] in RG10.
  assert (VOW0 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_OW + 0 + Z.of_nat j) = Some (YO0f.le_byte (16) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 253%nat TA_OW 0 4%N (SLit 16) RG10 eq_refl U12_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_k _ (restrict (w_H W) ms_k) 5 _ HS eq_refl) as RG5.
  cbn [ms_mem restrict] in RG5.
  assert (VM12 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_k) (TA_M + 12 + Z.of_nat j) = Some (YO0f.le_byte (1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_k W (ms_mem ms_k) _ 249%nat TA_M 12 4%N (SLit 1) RG5 eq_refl U8_k
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (HTW : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms_k)) (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 15) (TW.put 4 1))
             (65320 + 12 * 15) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 15) (TW.put 4 1))
        65312 (TW.put 4 16)) 12 (TW.put 4 1))).
  { apply (mw_fin_rd _ (aview segs (w_H W) memc) (aview segs (w_H W) (ms_mem ms_k)) _ (mw_world9 W memc (ms_mem ms_k) Bw _ 15 16 ltac:(lia)
      (mw_world4 W memc (ms_mem ms_k) Bw Htw VOW196 VM16 VM40 VM88) Vt4 Vt8 Vt12 VOW0 VM12)).
    intros x Hx Hni. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    destruct (Classical_Prop.classic (mw_winsk (spZ regs) 15 x)) as [Hw | Hw].
    - destruct Hw as [[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]] | Hw].
      + exfalso. unfold MWAKE_STK, MWAKE_FRAME in Hw. lia.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 12) (TA_M + 12 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 16) (TA_M + 16 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 40) (TA_M + 40 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 88) (TA_M + 88 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 0) (TA_OW + 0 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 196) (TA_OW + 196 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. destruct (Z_lt_le_dec x (TA_OW + (8 + 12 * 15))) as [D1|D1]; [| destruct (Z_lt_le_dec x (TA_OW + (12 + 12 * 15))) as [D2|D2]].
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (4 + 12 * 15)) (TA_OW + (4 + 12 * 15) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (8 + 12 * 15)) (TA_OW + (8 + 12 * 15) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
        * lazymatch type of Hni with mw_inrs ?l x = false =>
            rewrite (mw_inrs_true l (TA_OW + (12 + 12 * 15)) (TA_OW + (12 + 12 * 15) + Z.of_nat 4) x
              ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
          discriminate Hni.
    - apply KWk; [lia | exact Hw]. }
  mw_regv HS (Z_to_bv 5 1) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite HE_k by lia;
          rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  mw_regv HS (Z_to_bv 5 10) (w64 0) RF10
    ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mw_u64; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms_k)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E_k _ ms_k regs (mw_ex Bw) HS).
    - apply mw_agree; [intros n Hn; rewrite HE_k by lia; reflexivity | reflexivity].
    - vm_compute. reflexivity. }
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ mw_Zs (spZ regs) a ->
    aview segs (w_H W) (ms_mem ms_k) a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; apply KWk; [exact Ha
        | intros Hc0; exact (Hn (mw_winsk_Zs _ 15 a ltac:(lia) Hc0))]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  exact (mw_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (mwm_W Bw) (65316 + 12 * 15) (TW.put 4 1))
             (65320 + 12 * 15) (TW.put 4 (TW.s32_at Bw 12))) (65324 + 12 * 15) (TW.put 4 1))
        65312 (TW.put 4 16)) 12 (TW.put 4 1)) 0
           (ms_regs ms_k) (ms_mem ms_k) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GAk
           HTW HPF RF1 RF10 matF).
  }
  }
  }
  { (* M.state = S_WAKING: m_set returns at once *)
  cbn [branch_taken] in Hc.
  rewrite (mw_sext_atom E_r4 35 Bw 12 A_r4_35) in Hc.
  change (sv_denot E_r4 (SLit 1)) with (Z_to_bv 64 1) in Hc.
  rewrite (mw_eqb_s32 (TW.s32_at Bw 12) 1 ltac:(lia) ltac:(lia)) in Hc.
  apply negb_false_iff in Hc.
  rewrite Hc in Hm. cbv iota in Hm. destruct (mw_some_inv _ _ _ _ Hm) as [HB Hr]. subst Bw'. subst r.
  rewrite (mw_W_m Bw HLB).
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r4 U8_r4 U12_r4 U12_r4. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KW8 : forall a, 0 <= a < 2 ^ 64 -> ~ mw_wins (spZ regs) a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity; [| exact (KW5 a Ha Hn)].
    eapply (kept_of_frame _ _ _ _ _ (mw_wins (spZ regs))).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r4, ?U8_r4, ?U12_r4 in Hx; unfold mw_wins;
        first [ lia | left; lia | right; left; lia | right; right; left; lia
              | right; right; right; left; lia | right; right; right; right; left; lia
              | right; right; right; right; right; left; lia
              | right; right; right; right; right; right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GA8 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA5 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_c := mf) in *; set (E_c := EF) in HS, SHOK, HEI
  end.
  assert (HE_c : forall n, (n < 1024)%nat -> ew E_c n = ew E0 n)
    by (intros n Hn; unfold E_c; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r4; lia]).
  assert (A_c_35 : ew E_c 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_c by lia; exact A35_0).
  assert (A_c_36 : ew E_c 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_c by lia; exact A36_0).
  assert (A_c_37 : ew E_c 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_c by lia; exact A37_0).
  assert (A_c_38 : ew E_c 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_c by lia; exact A38_0).
  assert (A_c_39 : ew E_c 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_c by lia; exact A39_0).
  assert (A_c_40 : ew E_c 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_c by lia; exact A40_0).
  assert (A_c_41 : ew E_c 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_c by lia; exact A41_0).
  assert (A_c_33 : ew E_c 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_c by lia; exact A33_0).
  assert (A_c_34 : ew E_c 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_c by lia; exact A34_0).
  assert (U8_c : bv_unsigned (ew E_c 249%nat) = TA_M) by (rewrite HE_c by lia; exact U8L).
  assert (U12_c : bv_unsigned (ew E_c 253%nat) = TA_OW) by (rewrite HE_c by lia; exact U12L).
  assert (U27_c : bv_unsigned (ew E_c 268%nat) = TA_g_now) by (rewrite HE_c by lia; exact U27L).
  assert (U1_c : bv_unsigned (ew E_c 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_c by lia; exact U1L).
  assert (U93_c : bv_unsigned (ew E_c 334%nat) = FCells.CELL_K) by (rewrite HE_c by lia; exact U93L).
  assert (Usp_c : bv_unsigned (ew E_c 2) = spZ regs) by (rewrite HE_c by lia; exact Usp0).
  pose proof (st_ok_pi_region_nth E_c _ (restrict (w_H W) ms_c) 4 _ HS eq_refl) as RG4.
  cbn [ms_mem restrict] in RG4.
  assert (KM12 : forall x, TA_M + 12 <= x < TA_M + 12 + Z.of_N 4%N ->
    aview segs (w_H W) (ms_mem ms_c) x = aview segs (w_H W) memc x)
    by (exact (mw_keep_win E_c W (ms_mem ms_c) (aview segs (w_H W) memc) _ 249%nat TA_M 12 4%N 35 Bw TW.OFF_M TW.SZ_M
         RG4 eq_refl U8_c ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) A_c_35 Htw TMAP_A_M
         ltac:(lia) ltac:(unfold TW.SZ_M; cbn [Z.of_N]; lia))).
  pose proof (st_ok_pi_region_nth E_c _ (restrict (w_H W) ms_c) 9 _ HS eq_refl) as RG9.
  cbn [ms_mem restrict] in RG9.
  assert (KOW0 : forall x, TA_OW + 0 <= x < TA_OW + 0 + Z.of_N 4%N ->
    aview segs (w_H W) (ms_mem ms_c) x = aview segs (w_H W) memc x)
    by (exact (mw_keep_win E_c W (ms_mem ms_c) (aview segs (w_H W) memc) _ 253%nat TA_OW 0 4%N 38 Bw TW.OFF_OW TW.SZ_OW
         RG9 eq_refl U12_c ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) A_c_38 Htw TMAP_A_OW
         ltac:(lia) ltac:(unfold TW.SZ_OW; cbn [Z.of_N]; lia))).
  pose proof (st_ok_pi_region_nth E_c _ (restrict (w_H W) ms_c) 10 _ HS eq_refl) as RG10.
  cbn [ms_mem restrict] in RG10.
  assert (VOW196 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_c) (TA_OW + 196 + Z.of_nat j) = Some (YO0f.le_byte (TW.s32_at Bw 65508 + 1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_c W (ms_mem ms_c) _ 253%nat TA_OW 196 4%N (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 1)) RG10 eq_refl U12_c
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. change (8 * Z.of_nat (N.to_nat 4%N)) with 32.
    exact (mw_u_add1 E_c (SExt true 32 (SOff 37 0)) (TW.s32_at Bw 65508) (mw_sext_atom E_c 37 Bw 65508 A_c_37)). }
  pose proof (st_ok_pi_region_nth E_c _ (restrict (w_H W) ms_c) 5 _ HS eq_refl) as RG5.
  cbn [ms_mem restrict] in RG5.
  assert (VM16 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_c) (TA_M + 16 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_c W (ms_mem ms_c) _ 249%nat TA_M 16 8%N (SLit 0) RG5 eq_refl U8_c
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_c _ (restrict (w_H W) ms_c) 7 _ HS eq_refl) as RG7.
  cbn [ms_mem restrict] in RG7.
  assert (VM40 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_c) (TA_M + 40 + Z.of_nat j) = Some (YO0f.le_byte (TW.u_at Bw 65000 8) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_c W (ms_mem ms_c) _ 249%nat TA_M 40 8%N (SOff 39 0) RG7 eq_refl U8_c
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. rewrite (U_atom E_c 39 (TW.u_at Bw 65000 8) A_c_39 ltac:(pose proof (TWL.u_at_range Bw 65000 8) as HR;
      cbn [Z.of_nat] in HR; lia)). reflexivity. }
  pose proof (st_ok_pi_region_nth E_c _ (restrict (w_H W) ms_c) 8 _ HS eq_refl) as RG8.
  cbn [ms_mem restrict] in RG8.
  assert (VM88 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_c) (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_c W (ms_mem ms_c) _ 249%nat TA_M 88 4%N (SLit 0) RG8 eq_refl U8_c
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (HTW : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms_c)) (mwm_W Bw)).
  { apply (mw_fin_rd _ (aview segs (w_H W) memc) (aview segs (w_H W) (ms_mem ms_c)) _ (mw_world4 W memc (ms_mem ms_c) Bw Htw VOW196 VM16 VM40 VM88)).
    intros x Hx Hni. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    destruct (Classical_Prop.classic (mw_wins (spZ regs) x)) as [Hw | Hw].
    - destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]].
      + exfalso. unfold MWAKE_STK, MWAKE_FRAME in Hw. lia.
      + exact (KM12 x Hw).
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 16) (TA_M + 16 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 40) (TA_M + 40 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 88) (TA_M + 88 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exact (KOW0 x Hw).
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 196) (TA_OW + 196 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
    - apply KW8; [lia | exact Hw]. }
  mw_regv HS (Z_to_bv 5 1) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite HE_c by lia;
          rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  mw_regv HS (Z_to_bv 5 10) (w64 (0)) RF10
    ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mw_u64; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms_c)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E_c _ ms_c regs (mw_ex Bw) HS).
    - apply mw_agree; [intros n Hn; rewrite HE_c by lia; reflexivity | reflexivity].
    - vm_compute. reflexivity. }
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ mw_Zs (spZ regs) a ->
    aview segs (w_H W) (ms_mem ms_c) a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; apply KW8; [exact Ha | intros Hc0; exact (Hn (mw_wins_Zs _ a Hc0))]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  exact (mw_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (mwm_W Bw) (0)
           (ms_regs ms_c) (ms_mem ms_c) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GA8
           HTW HPF RF1 RF10 matF).
  }
  }
  { (* the old M.fail <> 0: a0 = -5 *)
  cbn [branch_taken] in Hc.
  rewrite (mw_sext_atom E_r3 36 Bw 88 A_r3_36) in Hc.
  change (sv_denot E_r3 (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (mw_eqb_s32 (TW.s32_at Bw 88) 0 ltac:(lia) ltac:(lia)) in Hc.
  rewrite Hc in Hm. cbn [negb] in Hm. cbv iota in Hm. destruct (mw_some_inv _ _ _ _ Hm) as [HB Hr]. subst Bw'. subst r.
  rewrite (mw_W_m Bw HLB).
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r3 U8_r3 U12_r3 U12_r3. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KW9 : forall a, 0 <= a < 2 ^ 64 -> ~ mw_wins (spZ regs) a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity; [| exact (KW4 a Ha Hn)].
    eapply (kept_of_frame _ _ _ _ _ (mw_wins (spZ regs))).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r3, ?U8_r3, ?U12_r3 in Hx; unfold mw_wins;
        first [ lia | left; lia | right; left; lia | right; right; left; lia
              | right; right; right; left; lia | right; right; right; right; left; lia
              | right; right; right; right; right; left; lia
              | right; right; right; right; right; right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GA9 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA4 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_b := mf) in *; set (E_b := EF) in HS, SHOK, HEI
  end.
  assert (HE_b : forall n, (n < 1024)%nat -> ew E_b n = ew E0 n)
    by (intros n Hn; unfold E_b; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r3; lia]).
  assert (A_b_35 : ew E_b 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_b by lia; exact A35_0).
  assert (A_b_36 : ew E_b 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_b by lia; exact A36_0).
  assert (A_b_37 : ew E_b 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_b by lia; exact A37_0).
  assert (A_b_38 : ew E_b 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_b by lia; exact A38_0).
  assert (A_b_39 : ew E_b 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_b by lia; exact A39_0).
  assert (A_b_40 : ew E_b 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_b by lia; exact A40_0).
  assert (A_b_41 : ew E_b 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_b by lia; exact A41_0).
  assert (A_b_33 : ew E_b 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_b by lia; exact A33_0).
  assert (A_b_34 : ew E_b 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_b by lia; exact A34_0).
  assert (U8_b : bv_unsigned (ew E_b 249%nat) = TA_M) by (rewrite HE_b by lia; exact U8L).
  assert (U12_b : bv_unsigned (ew E_b 253%nat) = TA_OW) by (rewrite HE_b by lia; exact U12L).
  assert (U27_b : bv_unsigned (ew E_b 268%nat) = TA_g_now) by (rewrite HE_b by lia; exact U27L).
  assert (U1_b : bv_unsigned (ew E_b 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_b by lia; exact U1L).
  assert (U93_b : bv_unsigned (ew E_b 334%nat) = FCells.CELL_K) by (rewrite HE_b by lia; exact U93L).
  assert (Usp_b : bv_unsigned (ew E_b 2) = spZ regs) by (rewrite HE_b by lia; exact Usp0).
  pose proof (st_ok_pi_region_nth E_b _ (restrict (w_H W) ms_b) 4 _ HS eq_refl) as RG4.
  cbn [ms_mem restrict] in RG4.
  assert (KM12 : forall x, TA_M + 12 <= x < TA_M + 12 + Z.of_N 4%N ->
    aview segs (w_H W) (ms_mem ms_b) x = aview segs (w_H W) memc x)
    by (exact (mw_keep_win E_b W (ms_mem ms_b) (aview segs (w_H W) memc) _ 249%nat TA_M 12 4%N 35 Bw TW.OFF_M TW.SZ_M
         RG4 eq_refl U8_b ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) A_b_35 Htw TMAP_A_M
         ltac:(lia) ltac:(unfold TW.SZ_M; cbn [Z.of_N]; lia))).
  pose proof (st_ok_pi_region_nth E_b _ (restrict (w_H W) ms_b) 9 _ HS eq_refl) as RG9.
  cbn [ms_mem restrict] in RG9.
  assert (KOW0 : forall x, TA_OW + 0 <= x < TA_OW + 0 + Z.of_N 4%N ->
    aview segs (w_H W) (ms_mem ms_b) x = aview segs (w_H W) memc x)
    by (exact (mw_keep_win E_b W (ms_mem ms_b) (aview segs (w_H W) memc) _ 253%nat TA_OW 0 4%N 38 Bw TW.OFF_OW TW.SZ_OW
         RG9 eq_refl U12_b ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) A_b_38 Htw TMAP_A_OW
         ltac:(lia) ltac:(unfold TW.SZ_OW; cbn [Z.of_N]; lia))).
  pose proof (st_ok_pi_region_nth E_b _ (restrict (w_H W) ms_b) 10 _ HS eq_refl) as RG10.
  cbn [ms_mem restrict] in RG10.
  assert (VOW196 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_b) (TA_OW + 196 + Z.of_nat j) = Some (YO0f.le_byte (TW.s32_at Bw 65508 + 1) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_b W (ms_mem ms_b) _ 253%nat TA_OW 196 4%N (SAlu ALU_ADD (SExt true 32 (SOff 37 0)) (SLit 1)) RG10 eq_refl U12_b
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. change (8 * Z.of_nat (N.to_nat 4%N)) with 32.
    exact (mw_u_add1 E_b (SExt true 32 (SOff 37 0)) (TW.s32_at Bw 65508) (mw_sext_atom E_b 37 Bw 65508 A_b_37)). }
  pose proof (st_ok_pi_region_nth E_b _ (restrict (w_H W) ms_b) 5 _ HS eq_refl) as RG5.
  cbn [ms_mem restrict] in RG5.
  assert (VM16 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_b) (TA_M + 16 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_b W (ms_mem ms_b) _ 249%nat TA_M 16 8%N (SLit 0) RG5 eq_refl U8_b
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  pose proof (st_ok_pi_region_nth E_b _ (restrict (w_H W) ms_b) 7 _ HS eq_refl) as RG7.
  cbn [ms_mem restrict] in RG7.
  assert (VM40 : forall j, (j < N.to_nat 8%N)%nat ->
    aview segs (w_H W) (ms_mem ms_b) (TA_M + 40 + Z.of_nat j) = Some (YO0f.le_byte (TW.u_at Bw 65000 8) (N.to_nat 8%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_b W (ms_mem ms_b) _ 249%nat TA_M 40 8%N (SOff 39 0) RG7 eq_refl U8_b
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. apply mw_le_byte_mod. rewrite (U_atom E_b 39 (TW.u_at Bw 65000 8) A_b_39 ltac:(pose proof (TWL.u_at_range Bw 65000 8) as HR;
      cbn [Z.of_nat] in HR; lia)). reflexivity. }
  pose proof (st_ok_pi_region_nth E_b _ (restrict (w_H W) ms_b) 8 _ HS eq_refl) as RG8.
  cbn [ms_mem restrict] in RG8.
  assert (VM88 : forall j, (j < N.to_nat 4%N)%nat ->
    aview segs (w_H W) (ms_mem ms_b) (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte (0) (N.to_nat 4%N) j)).
  { intros j Hj.
    rewrite (mw_win_val E_b W (ms_mem ms_b) _ 249%nat TA_M 88 4%N (SLit 0) RG8 eq_refl U8_b
      ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) j Hj).
    f_equal. }
  assert (HTW : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms_b)) (mwm_W Bw)).
  { apply (mw_fin_rd _ (aview segs (w_H W) memc) (aview segs (w_H W) (ms_mem ms_b)) _ (mw_world4 W memc (ms_mem ms_b) Bw Htw VOW196 VM16 VM40 VM88)).
    intros x Hx Hni. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    destruct (Classical_Prop.classic (mw_wins (spZ regs) x)) as [Hw | Hw].
    - destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]].
      + exfalso. unfold MWAKE_STK, MWAKE_FRAME in Hw. lia.
      + exact (KM12 x Hw).
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 16) (TA_M + 16 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 40) (TA_M + 40 + Z.of_nat 8) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_M + 88) (TA_M + 88 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
      + exact (KOW0 x Hw).
      + exfalso. lazymatch type of Hni with mw_inrs ?l x = false =>
          rewrite (mw_inrs_true l (TA_OW + 196) (TA_OW + 196 + Z.of_nat 4) x
            ltac:(cbn [In]; auto 20) ltac:(cbn [Z.of_nat]; lia)) in Hni end.
        discriminate Hni.
    - apply KW9; [lia | exact Hw]. }
  mw_regv HS (Z_to_bv 5 1) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite HE_b by lia;
          rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  mw_regv HS (Z_to_bv 5 10) (w64 (-5)) RF10
    ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mw_u64; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms_b)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E_b _ ms_b regs (mw_ex Bw) HS).
    - apply mw_agree; [intros n Hn; rewrite HE_b by lia; reflexivity | reflexivity].
    - vm_compute. reflexivity. }
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ mw_Zs (spZ regs) a ->
    aview segs (w_H W) (ms_mem ms_b) a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; apply KW9; [exact Ha | intros Hc0; exact (Hn (mw_wins_Zs _ a Hc0))]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  exact (mw_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (mwm_W Bw) (-5)
           (ms_regs ms_b) (ms_mem ms_b) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GA9
           HTW HPF RF1 RF10 matF).
  }
  }
  { (* M.foreign <> 0: a0 = -10 (SPEC_E_REFUSED), no store *)
  cbn [branch_taken] in Hc.
  rewrite (mw_sext_atom E_r2 34 Bw 24 A_r2_34) in Hc.
  change (sv_denot E_r2 (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (mw_eqb_s32 (TW.s32_at Bw 24) 0 ltac:(lia) ltac:(lia)) in Hc.
  rewrite Hc in Hm. cbn [negb] in Hm. cbv iota in Hm. destruct (mw_some_inv _ _ _ _ Hm) as [HB Hr]. subst Bw'. subst r.
  try clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mw_awr Usp_r2 U8_r2 U12_r2 U12_r2. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KW10 : forall a, 0 <= a < 2 ^ 64 -> ~ mw_wins (spZ regs) a ->
      aview segs (w_H W) (ms_mem msx) a = aview segs (w_H W) memc a)
  end.
  { intros a Ha Hn. etransitivity; [| exact (KW3 a Ha Hn)].
    eapply (kept_of_frame _ _ _ _ _ (mw_wins (spZ regs))).
    - exact HFr.
    - intros b0 wlo whi x Hin Hx. cbv beta.
      mw_wtac Hin Hx ltac:(rewrite ?Usp_r2, ?U8_r2, ?U12_r2 in Hx; unfold mw_wins;
        first [ lia | left; lia | right; left; lia | right; right; left; lia
              | right; right; right; left; lia | right; right; right; right; left; lia
              | right; right; right; right; right; left; lia
              | right; right; right; right; right; right; lia ]).
    - exact Ha.
    - exact Hn. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (GA10 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a)
  end.
  { intros a Ha. exact (apresent_grows _ _ _ a HG (GA3 a Ha)). }
  clear HF HFr HG.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ms_f := mf) in *; set (E_f := EF) in HS, SHOK, HEI
  end.
  assert (HE_f : forall n, (n < 1024)%nat -> ew E_f n = ew E0 n)
    by (intros n Hn; unfold E_f; repeat rewrite ew_ewset_other by lia;
        first [reflexivity | apply HE_r2; lia]).
  assert (A_f_35 : ew E_f 35 = w64 (TW.u_at Bw (TW.OFF_M + 12) (N.to_nat 4)))
    by (rewrite HE_f by lia; exact A35_0).
  assert (A_f_36 : ew E_f 36 = w64 (TW.u_at Bw (TW.OFF_M + 88) (N.to_nat 4)))
    by (rewrite HE_f by lia; exact A36_0).
  assert (A_f_37 : ew E_f 37 = w64 (TW.u_at Bw (TW.OFF_OW + 196) (N.to_nat 4)))
    by (rewrite HE_f by lia; exact A37_0).
  assert (A_f_38 : ew E_f 38 = w64 (TW.u_at Bw (TW.OFF_OW + 0) (N.to_nat 4)))
    by (rewrite HE_f by lia; exact A38_0).
  assert (A_f_39 : ew E_f 39 = w64 (TW.u_at Bw (TW.OFF_g_now + 0) (N.to_nat 8)))
    by (rewrite HE_f by lia; exact A39_0).
  assert (A_f_40 : ew E_f 40 = w64 (TW.u_at Bw (TW.OFF_M + 16) (N.to_nat 8)))
    by (rewrite HE_f by lia; exact A40_0).
  assert (A_f_41 : ew E_f 41 = w64 (TW.u_at Bw (TW.OFF_M + 40) (N.to_nat 8)))
    by (rewrite HE_f by lia; exact A41_0).
  assert (A_f_33 : ew E_f 33 = w64 (TW.u_at Bw (TW.OFF_M + 0) (N.to_nat 4)))
    by (rewrite HE_f by lia; exact A33_0).
  assert (A_f_34 : ew E_f 34 = w64 (TW.u_at Bw (TW.OFF_M + 24) (N.to_nat 4)))
    by (rewrite HE_f by lia; exact A34_0).
  assert (U8_f : bv_unsigned (ew E_f 249%nat) = TA_M) by (rewrite HE_f by lia; exact U8L).
  assert (U12_f : bv_unsigned (ew E_f 253%nat) = TA_OW) by (rewrite HE_f by lia; exact U12L).
  assert (U27_f : bv_unsigned (ew E_f 268%nat) = TA_g_now) by (rewrite HE_f by lia; exact U27L).
  assert (U1_f : bv_unsigned (ew E_f 242%nat) = FCells.GOT_CELL_K) by (rewrite HE_f by lia; exact U1L).
  assert (U93_f : bv_unsigned (ew E_f 334%nat) = FCells.CELL_K) by (rewrite HE_f by lia; exact U93L).
  assert (Usp_f : bv_unsigned (ew E_f 2) = spZ regs) by (rewrite HE_f by lia; exact Usp0).
  pose proof (st_ok_pi_region_nth E_f _ (restrict (w_H W) ms_f) 4 _ HS eq_refl) as RG4.
  cbn [ms_mem restrict] in RG4.
  assert (KM12 : forall x, TA_M + 12 <= x < TA_M + 12 + Z.of_N 4%N ->
    aview segs (w_H W) (ms_mem ms_f) x = aview segs (w_H W) memc x)
    by (exact (mw_keep_win E_f W (ms_mem ms_f) (aview segs (w_H W) memc) _ 249%nat TA_M 12 4%N 35 Bw TW.OFF_M TW.SZ_M
         RG4 eq_refl U8_f ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) A_f_35 Htw TMAP_A_M
         ltac:(lia) ltac:(unfold TW.SZ_M; cbn [Z.of_N]; lia))).
  pose proof (st_ok_pi_region_nth E_f _ (restrict (w_H W) ms_f) 5 _ HS eq_refl) as RG5.
  cbn [ms_mem restrict] in RG5.
  assert (KM16 : forall x, TA_M + 16 <= x < TA_M + 16 + Z.of_N 8%N ->
    aview segs (w_H W) (ms_mem ms_f) x = aview segs (w_H W) memc x)
    by (exact (mw_keep_win E_f W (ms_mem ms_f) (aview segs (w_H W) memc) _ 249%nat TA_M 16 8%N 40 Bw TW.OFF_M TW.SZ_M
         RG5 eq_refl U8_f ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) A_f_40 Htw TMAP_A_M
         ltac:(lia) ltac:(unfold TW.SZ_M; cbn [Z.of_N]; lia))).
  pose proof (st_ok_pi_region_nth E_f _ (restrict (w_H W) ms_f) 7 _ HS eq_refl) as RG7.
  cbn [ms_mem restrict] in RG7.
  assert (KM40 : forall x, TA_M + 40 <= x < TA_M + 40 + Z.of_N 8%N ->
    aview segs (w_H W) (ms_mem ms_f) x = aview segs (w_H W) memc x)
    by (exact (mw_keep_win E_f W (ms_mem ms_f) (aview segs (w_H W) memc) _ 249%nat TA_M 40 8%N 41 Bw TW.OFF_M TW.SZ_M
         RG7 eq_refl U8_f ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) A_f_41 Htw TMAP_A_M
         ltac:(lia) ltac:(unfold TW.SZ_M; cbn [Z.of_N]; lia))).
  pose proof (st_ok_pi_region_nth E_f _ (restrict (w_H W) ms_f) 8 _ HS eq_refl) as RG8.
  cbn [ms_mem restrict] in RG8.
  assert (KM88 : forall x, TA_M + 88 <= x < TA_M + 88 + Z.of_N 4%N ->
    aview segs (w_H W) (ms_mem ms_f) x = aview segs (w_H W) memc x)
    by (exact (mw_keep_win E_f W (ms_mem ms_f) (aview segs (w_H W) memc) _ 249%nat TA_M 88 4%N 36 Bw TW.OFF_M TW.SZ_M
         RG8 eq_refl U8_f ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) A_f_36 Htw TMAP_A_M
         ltac:(lia) ltac:(unfold TW.SZ_M; cbn [Z.of_N]; lia))).
  pose proof (st_ok_pi_region_nth E_f _ (restrict (w_H W) ms_f) 9 _ HS eq_refl) as RG9.
  cbn [ms_mem restrict] in RG9.
  assert (KOW0 : forall x, TA_OW + 0 <= x < TA_OW + 0 + Z.of_N 4%N ->
    aview segs (w_H W) (ms_mem ms_f) x = aview segs (w_H W) memc x)
    by (exact (mw_keep_win E_f W (ms_mem ms_f) (aview segs (w_H W) memc) _ 253%nat TA_OW 0 4%N 38 Bw TW.OFF_OW TW.SZ_OW
         RG9 eq_refl U12_f ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) A_f_38 Htw TMAP_A_OW
         ltac:(lia) ltac:(unfold TW.SZ_OW; cbn [Z.of_N]; lia))).
  pose proof (st_ok_pi_region_nth E_f _ (restrict (w_H W) ms_f) 10 _ HS eq_refl) as RG10.
  cbn [ms_mem restrict] in RG10.
  assert (KOW196 : forall x, TA_OW + 196 <= x < TA_OW + 196 + Z.of_N 4%N ->
    aview segs (w_H W) (ms_mem ms_f) x = aview segs (w_H W) memc x)
    by (exact (mw_keep_win E_f W (ms_mem ms_f) (aview segs (w_H W) memc) _ 253%nat TA_OW 196 4%N 37 Bw TW.OFF_OW TW.SZ_OW
         RG10 eq_refl U12_f ltac:(cbn [YP09.r_chunks In]; auto) ltac:(cbn [Z.of_N]; lia) A_f_37 Htw TMAP_A_OW
         ltac:(lia) ltac:(unfold TW.SZ_OW; cbn [Z.of_N]; lia))).
  assert (HTW : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms_f)) (Bw)).
  { apply (mw_fin_rd (@nil (Z * Z)) (aview segs (w_H W) memc) (aview segs (w_H W) (ms_mem ms_f)) _ Htw).
    intros x Hx Hni. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    destruct (Classical_Prop.classic (mw_wins (spZ regs) x)) as [Hw | Hw].
    - destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]].
      + exfalso. unfold MWAKE_STK, MWAKE_FRAME in Hw. lia.
      + exact (KM12 x Hw).
      + exact (KM16 x Hw).
      + exact (KM40 x Hw).
      + exact (KM88 x Hw).
      + exact (KOW0 x Hw).
      + exact (KOW196 x Hw).
    - apply KW10; [lia | exact Hw]. }
  mw_regv HS (Z_to_bv 5 1) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite HE_f by lia;
          rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  mw_regv HS (Z_to_bv 5 10) (w64 (-10)) RF10
    ltac:(cbn [sv_denot]; apply bv_eq; rewrite !mw_u64; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms_f)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E_f _ ms_f regs (mw_ex Bw) HS).
    - apply mw_agree; [intros n Hn; rewrite HE_f by lia; reflexivity | reflexivity].
    - vm_compute. reflexivity. }
  assert (KAF : forall a, 0 <= a < 2 ^ 64 -> ~ mw_Zs (spZ regs) a ->
    aview segs (w_H W) (ms_mem ms_f) a = aview segs (w_H W) memc a)
    by (intros a Ha Hn; apply KW10; [exact Ha | intros Hc0; exact (Hn (mw_wins_Zs _ a Hc0))]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  exact (mw_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (Bw) (-10)
           (ms_regs ms_f) (ms_mem ms_f) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ KAF GA10
           HTW HPF RF1 RF10 matF).
  }
  }
Qed.


End mwakew.

(* The statement of lib/A/Prog/m_wake_cg.v. *)
Theorem transport_m_wake_cg_holds :
  forall fx rc B MT, @transport_m_wake_cg_holds_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@mw_holds fx rc B MT). Qed.
