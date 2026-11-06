(* The operations of the loop of LLVMFuzzerTestOneInput that receive (fuzz_transport.c:1169-1214, TOps.v
   LLVMFuzzerTestOneInput_op_m): 0 (a record received, FT:1171-1174), 1 (op_frame, FT:1035-1050), 2 (op_announce,
   FT:1052-1066) and 8 (a record received by poll, FT:1209-1214, handed over once or twice by flags bit 0). From
   agree at the loop head each is Some (no abort, no UBSan trap) and agree holds with one operation more. RxOpLib.v
   proves them from rx_ok's and rx_ok_g's statements (RxOk.v); this file instantiates them. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links QueueFacts RxOk RxOpLib.
Open Scope Z_scope.

Theorem rx_op0_ok : forall (HL : links) I ops B a bytes,
  agree I ops B -> 0 <= ops < OPS_MAX -> 0 < a -> a + Z.of_nat (length bytes) < 2 ^ 64 ->
  exists B', receive_m I B a bytes 0 0 = Some (B', tt) /\ agree I (ops + 1) B'.
Proof. intros HL. exact (rxop_receive0 (rx_ok HL)). Qed.

Theorem rx_op8_ok : forall (HL : links) I ops B a bytes pf,
  agree I ops B -> 0 <= ops < OPS_MAX -> 0 < a -> a + Z.of_nat (length bytes) < 2 ^ 64 ->
  exists B', receive_m I B a bytes 1 pf = Some (B', tt) /\ agree I (ops + 1) B'.
Proof. intros HL. exact (rxop_receive8 HL (rx_ok_g HL)). Qed.

Theorem op_frame_ok : forall (HL : links) I ops B D a c,
  agree I ops B -> 0 <= ops < OPS_MAX -> 0 < a -> a + 1514 < 2 ^ 64 -> fuzz_in_ok D c ->
  exists B' c', op_frame_m I B D a c = Some (B', c') /\ agree I (ops + 1) B' /\ fuzz_in_ok D c'.
Proof. intros HL. exact (rxop_frame_of (rx_op0_ok HL)). Qed.

Theorem op_announce_ok : forall (HL : links) I ops B D a c,
  agree I ops B -> 0 <= ops < OPS_MAX -> 0 < a -> a + 1514 < 2 ^ 64 -> fuzz_in_ok D c ->
  exists B' c', op_announce_m I B D a c = Some (B', c') /\ agree I (ops + 1) B' /\ fuzz_in_ok D c'.
Proof. intros HL. exact (rxop_announce_of (rx_op0_ok HL)). Qed.

Theorem rx_op_ok : forall (HL : links) I ops B A D c k,
  agree I ops B -> 0 <= ops < OPS_MAX -> fuzz_in_ok D c -> fi_n c <> 0 ->
  0 < A k -> A k + 65536 <= 2 ^ 64 ->
  let op := snd (fuzz_u8_m D c) mod 9 in
  (op = 0 \/ op = 1 \/ op = 2 \/ op = 8) ->
  exists B' c' k', LLVMFuzzerTestOneInput_op_m I B A D c k = Some (B', (c', k')) /\ agree I (ops + 1) B' /\
    fuzz_in_ok D c'.
Proof. intros HL. exact (rxop_op_of (rx_op0_ok HL) (rx_op8_ok HL)). Qed.
