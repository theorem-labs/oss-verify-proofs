(* The loop of LLVMFuzzerTestOneInput (fuzz_transport.c, FT:1168-1216; TOps.v LLVMFuzzerTestOneInput_op_m and
   LLVMFuzzerTestOneInput_loop_m) never fails, given agree at its head (Agree.v).
   op_ok: one operation from agree I ops B (ops < OPS_MAX), a nonempty cursor in range and a nonzero heap address
     is Some and gives agree I (ops + 1); a case split over the op byte mod 9, each case one per-op lemma:
     0, 1, 2, 8 RxOp.rx_op_ok; 3 Op3Ok.op3_ok; 4 SubmitOk.op_submit_ok; 5, 6, 7 WakeOps.op5_ok / op6_ok / op7_ok.
     Every op byte is covered: on the patched harness model op 8 holds for every poll flags (RxOp.rx_op8_ok).
   op_k_of: an operation receives at most once, so the receive count k stays <= ops and every heap address the
     loop reads has k < OPS_MAX (heap_ok).
   loop_ok: by induction over the fuel OPS_MAX - ops. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links QueueFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require RxOp Op3Ok SubmitOk WakeOps.
Open Scope Z_scope.

(* every heap address of the run (the k-th receive's malloc, TOps.v A; k < OPS_MAX) is nonzero and has room for
   the 65535 bytes of one record *)
Definition heap_ok (A : nat -> Z) : Prop :=
  forall k : nat, Z.of_nat k < OPS_MAX -> 0 < A k /\ A k + 65536 <= 2 ^ 64.

(* ---------------------------------------------------------------- the receive count of one operation *)

(* split every match of the goal (outermost first), dropping each branch whose premise is None = Some _ *)
Local Ltac cur_split :=
  repeat first
    [ let H := fresh "H" in intros H; discriminate H
    | match goal with |- context [match ?x with _ => _ end] => destruct x; cbv beta iota zeta end ].

(* one operation receives at most once (cases 0, 1, 2, 8 once, the others never) *)
Lemma op_k_of : forall I B A D c k B' c' k',
  LLVMFuzzerTestOneInput_op_m I B A D c k = Some (B', (c', k')) -> k' = k \/ k' = S k.
Proof.
  intros I B A D c k B' c' k'. unfold LLVMFuzzerTestOneInput_op_m.
  destruct (fuzz_u8_m D c) as [c1 opb]. cbv beta iota zeta.
  destruct (opb mod 9 =? 0); cbv beta iota.
  { destruct (fuzz_record_m D c1) as [[c2 off] n]. cbv beta iota.
    destruct (receive_m _ _ _ _ _ _) as [[B1 u]|]; cbv beta iota; intros H; [|discriminate H].
    injection H as _ _ <-. right; reflexivity. }
  destruct (opb mod 9 =? 1); cbv beta iota.
  { destruct (op_frame_m I B D (A k) c1) as [[B1 c2]|]; cbv beta iota; intros H; [|discriminate H].
    injection H as _ _ <-. right; reflexivity. }
  destruct (opb mod 9 =? 2); cbv beta iota.
  { destruct (op_announce_m I B D (A k) c1) as [[B1 c2]|]; cbv beta iota; intros H; [|discriminate H].
    injection H as _ _ <-. right; reflexivity. }
  destruct (opb mod 9 =? 3); cbv beta iota.
  { cur_split. intros H. injection H as _ _ <-. left; reflexivity. }
  destruct (opb mod 9 =? 4); cbv beta iota.
  { destruct (op_submit_m B D c1) as [[B1 c2]|]; cbv beta iota; intros H; [|discriminate H].
    injection H as _ _ <-. left; reflexivity. }
  destruct (opb mod 9 =? 5); cbv beta iota.
  { cur_split. intros H. injection H as _ _ <-. left; reflexivity. }
  destruct (opb mod 9 =? 6); cbv beta iota.
  { cur_split. intros H. injection H as _ _ <-. left; reflexivity. }
  destruct (opb mod 9 =? 7); cbv beta iota.
  { intros H. injection H as _ _ <-. left; reflexivity. }
  destruct (fuzz_u8_m D c1) as [c2 pf]. cbv beta iota zeta.
  destruct (fuzz_record_m D c2) as [[c3 off] n]. cbv beta iota.
  destruct (receive_m _ _ _ _ _ _) as [[B1 u]|]; cbv beta iota; intros H; [|discriminate H].
  injection H as _ _ <-. right; reflexivity.
Qed.

(* ---------------------------------------------------------------- one operation, the loop *)

(* one operation of the loop (FT:1169-1215) *)
Lemma op_ok : forall (HL : links) I ops B A D c k,
  agree I ops B -> 0 <= ops < OPS_MAX -> fuzz_in_ok D c -> fi_n c <> 0 ->
  0 < A k -> A k + 65536 <= 2 ^ 64 ->
  exists B' c' k', LLVMFuzzerTestOneInput_op_m I B A D c k = Some (B', (c', k')) /\
    agree I (ops + 1) B' /\ fuzz_in_ok D c'.
Proof.
  intros HL I ops B A D c k HA Hops Hc Hn Ha1 Ha2.
  assert (Hr : 0 <= snd (fuzz_u8_m D c) mod 9 < 9) by (apply Z.mod_pos_bound; lia).
  assert (Hcase : snd (fuzz_u8_m D c) mod 9 = 0 \/ snd (fuzz_u8_m D c) mod 9 = 1 \/
                  snd (fuzz_u8_m D c) mod 9 = 2 \/ snd (fuzz_u8_m D c) mod 9 = 3 \/
                  snd (fuzz_u8_m D c) mod 9 = 4 \/ snd (fuzz_u8_m D c) mod 9 = 5 \/
                  snd (fuzz_u8_m D c) mod 9 = 6 \/ snd (fuzz_u8_m D c) mod 9 = 7 \/
                  snd (fuzz_u8_m D c) mod 9 = 8) by lia.
  destruct Hcase as [E | [E | [E | [E | [E | [E | [E | [E | E]]]]]]]].
  - exact (RxOp.rx_op_ok HL I ops B A D c k HA Hops Hc Hn Ha1 Ha2 (or_introl E)).
  - exact (RxOp.rx_op_ok HL I ops B A D c k HA Hops Hc Hn Ha1 Ha2 (or_intror (or_introl E))).
  - exact (RxOp.rx_op_ok HL I ops B A D c k HA Hops Hc Hn Ha1 Ha2 (or_intror (or_intror (or_introl E)))).
  - destruct (Op3Ok.op3_ok HL I ops B A D c k HA (proj2 Hops) Hc E) as (B' & c' & Eo & HA' & Hc').
    exists B', c', k. exact (conj Eo (conj HA' Hc')).
  - destruct (fuzz_u8_ok D c Hc) as (c1 & opb & E1 & Hc1 & _).
    destruct (SubmitOk.op_submit_ok I ops B D c1 HL HA (proj2 Hops) Hc1) as (B' & c' & Es & HA' & Hc').
    exists B', c', k. split; [|exact (conj HA' Hc')].
    rewrite E1 in E. cbn [snd] in E.
    unfold LLVMFuzzerTestOneInput_op_m. rewrite E1. cbv beta iota zeta. rewrite E.
    change (4 =? 0) with false. change (4 =? 1) with false. change (4 =? 2) with false.
    change (4 =? 3) with false. change (4 =? 4) with true. cbv beta iota.
    rewrite Es. reflexivity.
  - destruct (WakeOps.op5_ok HL I ops B A D c k HA Hops Hc E) as (B' & c' & Eo & HA' & Hc').
    exists B', c', k. exact (conj Eo (conj HA' Hc')).
  - destruct (WakeOps.op6_ok HL I ops B A D c k HA Hops Hc E) as (B' & c' & Eo & HA' & Hc').
    exists B', c', k. exact (conj Eo (conj HA' Hc')).
  - destruct (WakeOps.op7_ok I ops B A D c k HA Hops Hc E) as (B' & c' & Eo & HA' & Hc').
    exists B', c', k. exact (conj Eo (conj HA' Hc')).
  - exact (RxOp.rx_op_ok HL I ops B A D c k HA Hops Hc Hn Ha1 Ha2 (or_intror (or_intror (or_intror E)))).
Qed.

(* the loop (FT:1168): from agree I ops B with fuel = OPS_MAX - ops operations left, k <= ops receives done *)
Lemma loop_ok : forall (HL : links) I A D, heap_ok A -> forall fuel B c k ops,
  agree I ops B -> 0 <= ops -> ops + Z.of_nat fuel = OPS_MAX -> Z.of_nat k <= ops -> fuzz_in_ok D c ->
  exists B', LLVMFuzzerTestOneInput_loop_m fuel I B A D c k = Some (B', tt).
Proof.
  intros HL I A D HH. induction fuel as [|f IH]; intros B c k ops HA H0 Hf Hk Hc.
  - exists B. reflexivity.
  - cbn [LLVMFuzzerTestOneInput_loop_m].
    destruct (Z.eqb_spec (fi_n c) 0) as [Hn|Hn]; [exists B; reflexivity|].
    destruct (HH k ltac:(lia)) as (Ha1 & Ha2).
    destruct (op_ok HL I ops B A D c k HA ltac:(lia) Hc Hn Ha1 Ha2) as (B1 & c1 & k1 & E & HA1 & Hc1).
    pose proof (op_k_of I B A D c k B1 c1 k1 E) as Hk1.
    rewrite E. cbv beta iota.
    exact (IH B1 c1 k1 (ops + 1) HA1 ltac:(lia) ltac:(lia) ltac:(destruct Hk1 as [-> | ->]; lia) Hc1).
Qed.
