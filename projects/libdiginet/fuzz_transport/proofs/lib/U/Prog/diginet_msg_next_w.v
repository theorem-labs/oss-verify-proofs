(* proves the wide UBSan contract of diginet_msg_next (fuzz_transport.ubsan, 0x18844) and that it gives the narrow one. *)
(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame proofs/libdiginet/fuzz_frame/lib/U/Prog/diginet_msg_next_w.v at bb3053036017d1d92db6eca9e973ce610be16c08 to fuzz_transport's images *)
(* Walk of diginet_msg_next (src/diginet_msg.c:27-103 at 835f336c) in fuzz_transport.ubsan for
   U/Prog/diginet_msg_next_w_c.v. With no bytes the position is 0 = len: after the tests of c
   and mp against 0 and of c & 7 (0x18854, not taken: c mod 8 = 0), 0x18860 goes to 0x1890c
   and the function returns 0 with no store, before every check of the body; this is the first
   part of mn_main in U/Prog/diginet_msg_next.v. With bytes, the premise gives body <> 0 and the
   narrow walk applies. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import diginet_cursor_init_c diginet_msg_next_c
  diginet_msg_next_w_c diginet_msg_next.
Import ListNotations.
Open Scope Z_scope.

Theorem diginet_msg_next_contract_of_w : diginet_msg_next_contract_w -> diginet_msg_next_contract.
Proof.
  unfold diginet_msg_next_contract_w, diginet_msg_next_contract.
  intros W ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    c mp body bb mj pos st Hc Hmp Hc8 Hm8 Hb Hpos Hst CC BB CM D1 D2 D3 MI.
  apply W; try assumption. left; exact Hb.
Qed.

Theorem diginet_msg_next_holds_w : diginet_msg_next_contract_w.
Proof.
  unfold diginet_msg_next_contract_w.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    c mp body bb mj pos st Hc Hmp Hc8 Hm8 Hb Hpos Hst CC BB CM D1 D2 D3 MI.
  destruct (Nat.eq_dec (length bb) 0) as [L0|L0].
  2: { (* bytes: body is not 0, the narrow walk *)
       pose proof diginet_msg_next_holds as N. unfold diginet_msg_next_contract in N.
       apply N; try assumption. destruct Hb; [assumption | lia]. }
  (* no bytes: pos = len = 0 *)
  unfold DIGINET_MSG_NEXT.
  assert (P0 : pos = 0%nat) by lia. subst pos.
  pose proof (rw_cells_bound rsegs m c _ CC) as BCc. cbn [cells_size csize cursor_cells Nat.add] in BCc.
  pose proof (rw_cells_bound rsegs m mp _ CM) as BMm. cbn [cells_size csize Nat.add] in BMm.
  pose proof (bytes_at_bound rsegs m body bb BB) as BBb.
  pose proof (munch_refl [(c, c + 25); (mp, mp + 40)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (RS : msg_step bb 0 st = mr_plain MkEnd 0 0 st 0)
    by (unfold msg_step; rewrite L0; reflexivity).
  rewrite RS. cbn [mr_code mr_pos mr_st mr_plain mr_kind msg_cells is_end].
  unfold cursor_cells in CC.
  (* 0x18844 .. 0x18854: c and mp are not 0, c & 7 is 0 *)
  step. step. br false.
  step. br false.
  step. rewrite (land7 c) by lia. step. br false.
  (* 0x18858 .. 0x18860: len = 0, pos = 0, pos >= len *)
  step. step. step.
  br true.
  (* 0x1890c .. 0x18a1c: a0 = 0 *)
  step. step. step. step.
  apply evt_done. cbv beta.
  do 12 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact CC|]. exact CM.
Qed.
