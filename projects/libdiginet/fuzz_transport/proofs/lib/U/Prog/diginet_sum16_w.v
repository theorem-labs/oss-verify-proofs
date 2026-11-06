(* proves the wide UBSan contract of diginet_sum16 (fuzz_transport.ubsan, 0x17f60) and that it gives the narrow one. *)
(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame proofs/libdiginet/fuzz_frame/lib/U/Prog/diginet_sum16_w.v at bb3053036017d1d92db6eca9e973ce610be16c08 to fuzz_transport's images *)
(* Walk of diginet_sum16 (src/diginet_frame.c:42-48 at 835f336c) in fuzz_transport.ubsan for
   U/Prog/diginet_sum16_w_c.v. With no bytes, 0x17f64 (beqz a1) leaves before the loop and its
   three trap branches, whatever p is; with bytes, the premise gives p <> 0 and the narrow walk
   U/Prog/diginet_sum16.v applies. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import diginet_sum16_c diginet_sum16_w_c
  diginet_sum16.
Import ListNotations.
Open Scope Z_scope.

Theorem diginet_sum16_contract_of_w : diginet_sum16_contract_w -> diginet_sum16_contract.
Proof.
  unfold diginet_sum16_contract_w, diginet_sum16_contract.
  intros W ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p bb
    Hp BA.
  apply W; [left; exact Hp | exact BA].
Qed.

Theorem diginet_sum16_holds_w : diginet_sum16_contract_w.
Proof.
  unfold diginet_sum16_contract_w.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p bb
    Hp BA.
  destruct (Nat.eq_dec (length bb) 0) as [L0|L0].
  - (* no bytes: 0x17f60 mv a2, zero; 0x17f64 beqz a1 goes to 0x17fa0 *)
    unfold DIGINET_SUM16.
    pose proof (bytes_at_bound rsegs m p bb BA) as BB.
    assert (LB : 0 <= Z.of_nat (length bb) < 2^64) by lia.
    step. step.
    if_cases K.
    + assert (E0 : lib_sum16 bb = 0) by (destruct bb as [|x bb]; [reflexivity | cbn [length] in L0; lia]).
      rewrite E0.
      step. step. step.
      apply evt_done. do 6 eexists. reflexivity.
    + unfold bv_eqb in K. rewrite (unsigned_lit _ LB) in K. apply Z.eqb_neq in K.
      change (bv_unsigned (Z_to_bv 64 0)) with 0 in K. lia.
  - (* bytes: p is not 0, the narrow walk *)
    pose proof diginet_sum16_holds as N. unfold diginet_sum16_contract in N.
    apply N; [destruct Hp; [assumption | lia] | exact BA].
Qed.
