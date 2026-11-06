(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* The walk of check_refusal (fuzz/fuzz_decode.c:265-276), fuzz_decode.plain 0x13a90 (32
   instructions, 16-byte frame), against lib/Prog/check_refusal_c.v: check_refusal_of takes
   diginet_body_check's contract (lib/Prog/diginet_body_check_c.v) as the hypothesis for the `jal` at
   0x13ae4, and check_refusal_holds discharges it with the walks diginet_body_check_holds,
   diginet_cursor_init_holds and diginet_msg_next_holds.
   The inlined spec_system_at loop at 0x13abc-0x13adc is the lemma loop below (by induction on the
   remaining count, each turn the lemma iter): it leaves at 0x13afc with sys_hit bb i for some
   i + 3 < len, or at 0x13ae0 with system_at bb = false (DgnSpec.system_at_true / _false).
   A len under 4 skips the loop to 0x13ae0. At 0x13afc, i < len < 2^63 makes slti give 0, so s0 is
   -10; at 0x13ae0 s0 is 0. diginet_body_check returns body_check bb, which body_check_spec makes
   -10 when system_at bb and 0 else, so the `bne a0, s0` at 0x13ae8 never goes to the `jal abort`.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnChkLib FrameBytes
  diginet_cursor_init_c diginet_msg_next_c diginet_body_check_c diginet_cursor_init diginet_msg_next
  diginet_body_check check_refusal_c.
Import ListNotations.
Open Scope Z_scope.

(* lbu k(w) of the byte at index i of bb *)
Lemma rdb : forall m body bb (w : word) k i, bytes_at rsegs m body bb -> (i < length bb)%nat ->
  bv_unsigned w + k = body + Z.of_nat i ->
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned w + k)) 1 = Some [nth i bb (Z_to_bv 8 0)].
Proof. intros m body bb w k i H Hi E. rewrite E. exact (rd1 m body bb i H Hi). Qed.

Lemma rdb0 : forall m body bb (w : word) i, bytes_at rsegs m body bb -> (i < length bb)%nat ->
  bv_unsigned w = body + Z.of_nat i ->
  ov_read_bytes rsegs m w 1 = Some [nth i bb (Z_to_bv 8 0)].
Proof.
  intros m body bb w i H Hi E. rewrite <- (Z_to_bv_lit_self w), E. exact (rd1 m body bb i H Hi).
Qed.

(* beq / bne of the loaded byte against a constant register *)
Lemma eqb_at8 : forall bb i (w : word) k, bv_unsigned w = k ->
  bv_eqb (zxb (nth i bb (Z_to_bv 8 0))) w = (at8 bb i =? k).
Proof.
  intros bb i w k E. unfold bv_eqb, zxb. rewrite E.
  pose proof (byte_range (nth i bb (Z_to_bv 8 0))) as R.
  rewrite unsigned_lit by lia. reflexivity.
Qed.

(* slti a2, a2, 0 of an index below 2^63 *)
Lemma slti0 : forall (x : word) z, bv_unsigned x = z -> 0 <= z < 2^63 -> v_slti x 0 = Z_to_bv 64 0.
Proof.
  intros x z E H. unfold v_slti, zsig. rewrite zb_signed, E.
  destruct (Z.ltb_spec z (2^63)) as [_|C]; [|lia].
  destruct (Z.ltb_spec z 0) as [C|_]; [lia|reflexivity].
Qed.

(* a test whose condition is closed *)
Local Ltac lit_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
      let v := eval vm_compute in cnd in
      replace cnd with v by (vm_compute; reflexivity); cbv iota
  end.

Section Loop.
Variables (ra sp gp tp t1 t2 s0 s1 a0 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (body : Z) (bb : list byte)
  (Q : machine_state -> Prop).
Hypothesis BA : bytes_at rsegs m body bb.
Hypothesis HL : Z.of_nat (length bb) < 2^63.
Hypothesis Ha4 : bv_unsigned a4 = Z.of_nat (length bb) - 3.
Hypothesis Ha5 : bv_unsigned a5 = 0xf0.
Hypothesis Ha6 : bv_unsigned a6 = 0x13.
Hypothesis Ha7 : bv_unsigned a7 = 0x70.

Local Abbreviation ST pc t0 a2 a3 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* one turn at index i, 0x13abc .. 0x13ad8: the hit leaves for 0x13afc, else a2 and a3 step *)
Lemma iter : forall i (t0 a2 a3 : word),
  (i + 3 < length bb)%nat -> bv_unsigned a2 = Z.of_nat i -> bv_unsigned a3 = body + 1 + Z.of_nat i ->
  (sys_hit bb i = true -> forall t0' : word, evt rsegs Q (ST 0x13afc t0' a2 a3)) ->
  (sys_hit bb i = false -> forall t0' a2' a3' : word, bv_unsigned a2' = Z.of_nat (S i) ->
     bv_unsigned a3' = body + 1 + Z.of_nat (S i) -> evt rsegs Q (ST 0x13adc t0' a2' a3')) ->
  evt rsegs Q (ST 0x13abc t0 a2 a3).
Proof.
  intros i t0 a2 a3 Hi Ha2 Ha3 KH KM.
  pose proof BA as (Hb0 & Hb1 & _).
  pose proof (u64_range a2) as R2. pose proof (u64_range a3) as R3.
  (* lbu t0, -1(a3); bne t0, a5: b[i] = F0 *)
  pose proof (rdb m body bb a3 (-1) i BA ltac:(lia) ltac:(lia)) as R. step. clear R.
  step. rewrite (eqb_at8 bb i a5 240 Ha5).
  destruct (Z.eqb_spec (at8 bb i) 240) as [E0|E0]; cbv beta iota delta [negb].
  2:{ step. step. apply KM.
      - unfold sys_hit. rewrite (proj2 (Z.eqb_neq _ _) E0). reflexivity.
      - rewrite unsigned_lit by lia. lia.
      - rewrite unsigned_lit by lia. lia. }
  (* lbu t0, 0(a3); bne t0, a6: b[i + 1] = 13 *)
  pose proof (rdb0 m body bb a3 (S i) BA ltac:(lia) ltac:(lia)) as R. step. clear R.
  step. rewrite (eqb_at8 bb (S i) a6 19 Ha6).
  destruct (Z.eqb_spec (at8 bb (S i)) 19) as [E1|E1]; cbv beta iota delta [negb].
  2:{ step. step. apply KM.
      - unfold sys_hit. rewrite (proj2 (Z.eqb_eq _ _) E0), (proj2 (Z.eqb_neq _ _) E1). reflexivity.
      - rewrite unsigned_lit by lia. lia.
      - rewrite unsigned_lit by lia. lia. }
  (* lbu t0, 2(a3); beq t0, a7: b[i + 3] = 70 *)
  pose proof (rdb m body bb a3 2 (S (S (S i))) BA ltac:(lia) ltac:(lia)) as R. step. clear R.
  step. rewrite (eqb_at8 bb (S (S (S i))) a7 112 Ha7).
  destruct (Z.eqb_spec (at8 bb (S (S (S i)))) 112) as [E3|E3]; cbv beta iota.
  - apply KH. unfold sys_hit.
    rewrite (proj2 (Z.eqb_eq _ _) E0), (proj2 (Z.eqb_eq _ _) E1), (proj2 (Z.eqb_eq _ _) E3). reflexivity.
  - step. step. apply KM.
    + unfold sys_hit.
      rewrite (proj2 (Z.eqb_eq _ _) E0), (proj2 (Z.eqb_eq _ _) E1), (proj2 (Z.eqb_neq _ _) E3). reflexivity.
    + rewrite unsigned_lit by lia. lia.
    + rewrite unsigned_lit by lia. lia.
Qed.

(* the loop from index i with S n turns left, 0x13abc .. 0x13adc; bne a4, a2 at 0x13adc *)
Lemma loop :
  (forall i (t0 a2 a3 : word), (i + 3 < length bb)%nat -> bv_unsigned a2 = Z.of_nat i ->
     sys_hit bb i = true -> evt rsegs Q (ST 0x13afc t0 a2 a3)) ->
  (forall t0 a2 a3 : word, system_at bb = false -> evt rsegs Q (ST 0x13ae0 t0 a2 a3)) ->
  forall n i (t0 a2 a3 : word), (i + S n + 3 = length bb)%nat ->
  (forall j, (j < i)%nat -> sys_hit bb j = false) ->
  bv_unsigned a2 = Z.of_nat i -> bv_unsigned a3 = body + 1 + Z.of_nat i ->
  evt rsegs Q (ST 0x13abc t0 a2 a3).
Proof.
  intros KH KM n. induction n as [|n IH]; intros i t0 a2 a3 Hn Hp Ha2 Ha3.
  all: apply (iter i t0 a2 a3); [lia | exact Ha2 | exact Ha3 | intros Hh t0'; apply (KH i); [lia | exact Ha2 | exact Hh] | ].
  all: intros Hm t0' a2' a3' Ha2' Ha3'.
  all: step; unfold bv_eqb; rewrite Ha4, Ha2'.
  - destruct (Z.eqb_spec (Z.of_nat (length bb) - 3) (Z.of_nat (S i))) as [_|C]; [|lia].
    cbv beta iota delta [negb].
    apply KM. apply system_at_false. intros j Hj.
    destruct (Nat.eq_dec j i) as [->|N]; [exact Hm | apply Hp; lia].
  - destruct (Z.eqb_spec (Z.of_nat (length bb) - 3) (Z.of_nat (S i))) as [C|_]; [lia|].
    cbv beta iota delta [negb].
    apply (IH (S i)); [lia | | exact Ha2' | exact Ha3'].
    intros j Hj. destruct (Nat.eq_dec j i) as [->|N]; [exact Hm | apply Hp; lia].
Qed.

End Loop.

Theorem check_refusal_of : diginet_body_check_contract -> check_refusal_contract.
Proof.
  intros BC. unfold diginet_body_check_contract, DIGINET_BODY_CHECK in BC.
  unfold check_refusal_contract, CHECK_REFUSAL, CHECK_REFUSAL_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    body lo bb HNZ BA HL ST HLO DJ MI.
  pose proof ST as (Hlo0 & _ & _). pose proof (u64_range sp) as Hsp.
  pose proof BA as (Hb0 & Hb1 & _).
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  step. step. step.                                        (* addi sp; sd ra; sd s0 *)
  step. step.                                              (* addi a2, zero, 4; bltu a1, a2 *)
  rewrite bv_ltu_Z, (unsigned_lit (Z.of_nat (length bb))) by lia.
  change (bv_unsigned (Z_to_bv 64 4)) with 4.
  destruct (Z.ltb_spec (Z.of_nat (length bb)) 4) as [HS|HS]; cbv iota.
  (* len < 4: no index; mv s0, zero at 0x13ae0 *)
  1: assert (SA : system_at bb = false) by (apply system_at_false; intros j Hj; lia).
  1: step.
  (* len >= 4: a2 = 0, a3 = body + 1, a4 = len - 3, a5 a6 a7, then the loop *)
  2: do 6 step.
  2: eapply loop with (body := body) (bb := bb) (n := (length bb - 4)%nat) (i := 0%nat);
     try first [ assumption | reflexivity | (rewrite unsigned_lit by lia; lia) | lia | (intros; lia) ].
  (* 0x13afc: a hit at index i < len < 2^63; slti, addi, andi give s0 = -10 *)
  2: intros i t0' a2' a3' Hi Ha2' Hh.
  2: assert (SA : system_at bb = true) by (apply system_at_true; exists i; split; assumption).
  2: step.
  2: rewrite (slti0 a2' (Z.of_nat i) Ha2') by lia.
  2: do 3 step.
  (* 0x13ae0: no hit; mv s0, zero *)
  3: intros t0' a2' a3' SA.
  3: step.
  (* 0x13ae4 .. 0x13af8 in the three cases, with SA : system_at bb = b and s0 the closed value set
     above: jal diginet_body_check (its contract BC, a0 and a1 unchanged, callee sp = sp - 16), then
     bne a0, s0 compares two equal closed words, then the epilogue *)
  all: step.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    eapply evt_cut;
    [ eapply BC | ];
    [ exact HNZ | exact BA | rewrite unsigned_lit by lia; exact ST
    | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | exact MI | ];
    intros ? (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MUc & WMc & MIc & STc);
    rewrite unsigned_lit in MUc, STc by lia;
    transport_after_call rsegs m1 m2 MUc WMc; clear MUc WMc;
    repeat match goal with H : mem_inv rsegs m1 |- _ => clear H end
  end.
  all: rename STc into ST.
  all: lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  all: rewrite body_check_spec, SA.
  all: step; lit_if.                                       (* bne a0, s0 *)
  all: step; step; step; step.                             (* ld ra; ld s0; addi sp; ret *)
  all: apply evt_done; do 16 eexists; split; [reflexivity|];
       split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
       release_frame FR ST (bv_unsigned sp); exact ST.
Qed.

Theorem check_refusal_holds : check_refusal_contract.
Proof.
  exact (check_refusal_of (diginet_body_check_holds diginet_cursor_init_holds diginet_msg_next_holds)).
Qed.
