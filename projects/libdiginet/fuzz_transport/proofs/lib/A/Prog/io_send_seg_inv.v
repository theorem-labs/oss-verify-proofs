(* io_send_seg_inv: the command-length invariant of lib/A/Prog/io_send_cg.v (its premise
   `forall s, 0 <= s < g_ncmd Bw -> Cmd_st Bw s = PENDING -> Cmd_len Bw s <= SPEC_CMD_MAX`) at the world
   check_latest_sent is handed on io_send's DATA path:
     B5 = set_g_last_counter (set_M_host_counter (ios_B0 Bw) send) send
   (lib/A/Prog/io_send_segs.v; ios_B0 Bw = set_g_fail_next Bw 0). B5 differs from Bw only at the world offsets
   0xfdc8 (g_fail_next, 1 byte), 0x54 .. 0x57 (M.host_counter) and 0xfdd0 .. 0xfdd3 (g_last_counter); the invariant
   reads g_ncmd (0xfdd8 .. 0xfddb) and, for each command s >= 0, the 4 bytes of Cmd_st at 0x4dc8 + 40 s and the byte
   of Cmd_len at 0x4dc8 + 40 s + 36, none of which is a written offset for any integer s (ios_B5_u_at's side
   conditions, decided by lia). This is io_send_cg.v's header argument at lines 56-64, proved. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_segs.
Import ListNotations.
Open Scope Z_scope.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.

(* A read of B5 that misses the three written fields is the read of Bw. *)
Lemma ios_B5_u_at : forall Bw send, length Bw = Z.to_nat TW.W_LEN -> forall k' (n : nat),
  0 <= k' ->
  (k' + Z.of_nat n <= TW.OFF_g_fail_next \/ TW.OFF_g_fail_next + 1 <= k') ->
  (k' + Z.of_nat n <= TW.A_M_host_counter \/ TW.A_M_host_counter + 4 <= k') ->
  (k' + Z.of_nat n <= TW.OFF_g_last_counter \/ TW.OFF_g_last_counter + 4 <= k') ->
  TW.u_at (TW.set_g_last_counter (TW.set_M_host_counter (ios_B0 Bw) send) send) k' n = TW.u_at Bw k' n.
Proof.
  intros Bw send HL k' n Hk H1 H2 H3.
  assert (LZ : Z.of_nat (length Bw) = 65616) by (rewrite HL; reflexivity).
  assert (L0 : length (ios_B0 Bw) = length Bw).
  { unfold ios_B0, TW.set_g_fail_next. apply TWL.length_upd_put; unfold TW.OFF_g_fail_next; lia. }
  assert (L1 : length (TW.set_M_host_counter (ios_B0 Bw) send) = length Bw).
  { unfold TW.set_M_host_counter. rewrite TWL.length_upd_put; [exact L0 | unfold TW.A_M_host_counter, TW.OFF_M; lia |].
    rewrite L0. unfold TW.A_M_host_counter, TW.OFF_M. lia. }
  unfold TW.set_g_last_counter.
  rewrite TWL.u_at_upd_out; [| unfold TW.OFF_g_last_counter; lia | exact Hk
                             | rewrite TWL.length_put; exact H3
                             | rewrite TWL.length_put, L1; unfold TW.OFF_g_last_counter; lia ].
  unfold TW.set_M_host_counter.
  rewrite TWL.u_at_upd_out; [| unfold TW.A_M_host_counter, TW.OFF_M; lia | exact Hk
                             | rewrite TWL.length_put; exact H2
                             | rewrite TWL.length_put, L0; unfold TW.A_M_host_counter, TW.OFF_M; lia ].
  unfold ios_B0, TW.set_g_fail_next.
  rewrite TWL.u_at_upd_out; [reflexivity | unfold TW.OFF_g_fail_next; lia | exact Hk
                             | rewrite TWL.length_put; exact H1
                             | rewrite TWL.length_put; unfold TW.OFF_g_fail_next; lia ].
Qed.

Ltac ios_inv_side :=
  unfold TW.OFF_g_ncmd, TW.A_Cmd_st, TW.A_Cmd_len, TW.OFF_g_cmd, TW.OFF_g_fail_next, TW.A_M_host_counter,
    TW.OFF_M, TW.OFF_g_last_counter; lia.

(* The invariant at B5 is the invariant at Bw. *)
Lemma ios_cmdinv_B5 : forall Bw send, length Bw = Z.to_nat TW.W_LEN ->
  (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) ->
  let B5 := TW.set_g_last_counter (TW.set_M_host_counter (ios_B0 Bw) send) send in
  (forall s, 0 <= s < TW.g_ncmd B5 -> TW.Cmd_st B5 s = TC.PENDING -> TW.Cmd_len B5 s <= DSpec.SPEC_CMD_MAX).
Proof.
  intros Bw send HL Hinv. cbv zeta. intros s Hs Hst.
  assert (EN : TW.g_ncmd (TW.set_g_last_counter (TW.set_M_host_counter (ios_B0 Bw) send) send) = TW.g_ncmd Bw)
    by (unfold TW.g_ncmd; apply (ios_B5_u_at Bw send HL); ios_inv_side).
  assert (ES : TW.Cmd_st (TW.set_g_last_counter (TW.set_M_host_counter (ios_B0 Bw) send) send) s = TW.Cmd_st Bw s).
  { unfold TW.Cmd_st, TW.s32_at. f_equal. apply (ios_B5_u_at Bw send HL); ios_inv_side. }
  assert (EL : TW.Cmd_len (TW.set_g_last_counter (TW.set_M_host_counter (ios_B0 Bw) send) send) s = TW.Cmd_len Bw s)
    by (unfold TW.Cmd_len; apply (ios_B5_u_at Bw send HL); ios_inv_side).
  rewrite EN in Hs. rewrite ES in Hst. rewrite EL. exact (Hinv s Hs Hst).
Qed.
