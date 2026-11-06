(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* The walk of check_refusal (fuzz/fuzz_decode.c:265-276) on fuzz_decode.ubsan, at 0x13b08 (45 words, 16-byte
   frame holding ra and s0), against lib/U/Prog/check_refusal_c.v. 42 instructions are walked: the prologue and the
   length test (0x13b08-0x13b18), the loop set-up (0x13b1c-0x13b38), the inlined spec_system_at loop
   (0x13b3c-0x13b80, scan_step / scan_loop, one iteration per index i), the found branch (0x13ba0-0x13bac), and the
   call of diginet_body_check with the epilogue (0x13b84-0x13b9c, refusal_tail). The unimp at 0x13bb0, the
   `jal abort` at 0x13bb4 and the unimp at 0x13bb8 are not reached.
   The callee's contract (lib/U/Prog/diginet_body_check_c.v, the UBSan contract of diginet_body_check at 0x13e04
   with its 144-byte frame) is an argument of check_refusal_holds, as in the plain twin lib/Prog/check_refusal.v,
   used only in refusal_tail; the top applies it to the callee's walk. refusal_tail passes it the contract's own
   0 < lo, and (sp - 16) mod 8 = 0 from sp mod 16 = 0.
   Abort site: the `bne a0, s0` at 0x13b8c to the `jal abort` at 0x13bb4 is not taken. The loop leaves s0 = -10
   when it finds F0 13 xx 70 at an index i with i + 3 < len (DgnSpec.sys_hit, so system_at bb = true by
   system_at_true; the found branch computes -10 from slti of i, which is 0 because i < len < 2^63), and s0 = 0
   when it finds none (len < 4, or every index tested, so system_at bb = false by system_at_false). The callee
   returns a0 = body_check bb, which DgnLib.body_check_spec makes -10 exactly when system_at bb and 0 otherwise.
   UBSan traps (each to the unimp at 0x13bb0), not taken at any index i of the loop, with i + 3 < length bb:
   - 0x13b40 `bltu t2, a0` with t2 = body + i: body + i < 2^64 (bytes_at: body + length bb <= 2^64);
   - 0x13b44-0x13b4c `seqz` / `xor` / `beqz`: snez body = 1 (body <> 0) and seqz (body + i) = 0 (body + i > 0);
   - 0x13b50 `beqz a0`: body <> 0;
   - 0x13b60 `bgeu a2, a3` with a2 = i, a3 = not body = 2^64 - 1 - body: i < 2^64 - 1 - body (bytes_at);
   - 0x13b6c-0x13b70 `bltu a3, t3` with t3 = i + 3: i + 3 <= 2^64 - 1 - body (bytes_at).
   The callee's own checks are its contract's business; its premises (body <> 0, bytes_at, its entry sp - 16
   8-aligned from sp mod 16 = 0, the stack, disjointness) are discharged at the call from this contract's
   premises. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnChkLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import diginet_body_check_c check_refusal_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- bytes of the body ---- *)

Lemma at8_range : forall l i, 0 <= at8 l i < 256.
Proof.
  intros l i. unfold at8, bz. pose proof (bv_unsigned_in_range 8 (nth i l (b8 0))) as H.
  unfold bv_modulus in H. change (2 ^ Z.of_N 8) with 256 in H. exact H.
Qed.

(* lbu of byte i of the body *)
Lemma rd_at8 : forall m a bb (i : nat), bytes_at rsegs m a bb -> (i < length bb)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat i)) 1 = Some [b8 (at8 bb i)].
Proof.
  intros m a bb i H Hi. rewrite (bytes_at_ov_read rsegs m a bb i 1 H) by lia. f_equal.
  unfold at8, bz, b8.
  replace (Z_to_bv 8 (bv_unsigned (nth i bb (Z_to_bv 8 0)))) with (nth i bb (Z_to_bv 8 0))
    by (symmetry; apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range).
  clear H. revert i Hi. induction bb as [|x bb IH]; intros i Hi; [cbn in Hi; lia|].
  destruct i as [|i]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in Hi. lia.
Qed.

(* fewer than 4 bytes: spec_system_at tests no index *)
Lemma sys_short : forall bb, (length bb < 4)%nat -> system_at bb = false.
Proof. intros bb H. unfold system_at. replace (length bb - 3)%nat with 0%nat by lia. reflexivity. Qed.

(* the callee's entry sp - 16 is 8-aligned when sp is 16-aligned *)
Lemma mod8_sub16 : forall x, x mod 16 = 0 -> (x + -16) mod 8 = 0.
Proof.
  intros x H. pose proof (Z.div_mod x 16 ltac:(lia)) as E. rewrite H, Z.add_0_r in E. rewrite E.
  replace (16 * (x / 16) + -16) with ((2 * (x / 16) - 2) * 8) by lia. apply Z_mod_mult.
Qed.

(* ---- tests over Z (as the UBSan templates' `take`) ---- *)

Local Ltac wsub :=
  repeat match goal with H : bv_unsigned ?w = _ |- context [bv_unsigned ?w] => is_var w; rewrite H end.
Local Ltac usub :=
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.
Local Ltac norm := wsub; usub; zb_fold_lits; usub.
Local Ltac solve_c :=
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu;
  rewrite ?zb_signed, ?v_sltu_b2z, ?v_sltiu_b2z;
  norm; rewrite ?zb_lxor_ones by lia; norm;
  do 3 (decide_tests; cbv beta iota; cbn [Z.b2z negb andb orb]; zb_fold_lits; norm);
  first [ reflexivity | vm_compute; reflexivity ].
Local Ltac take b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_c]
  end.
(* a register's value over Z *)
Local Ltac fact :=
  cbv beta; rewrite ?v_sltu_b2z, ?v_sltiu_b2z; norm; rewrite ?zb_lxor_ones by lia; norm;
  decide_tests; cbn [Z.b2z]; norm; first [ reflexivity | lia | vm_compute; reflexivity ].
(* 0x13ba0-0x13ba8: slti a2, a2, 0; addi a2, a2, -1; andi s0, a2, -10 with 0 <= a2 < 2^63 *)
Local Ltac slti_fact :=
  unfold v_slti, zsig; rewrite zb_signed; wsub;
  do 2 (decide_tests; cbv beta iota); vm_compute; reflexivity.

(* ---- 0x13b88-0x13b9c: the call of diginet_body_check, the abort test, the epilogue ---- *)

Lemma refusal_tail : diginet_body_check_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s0' s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (body lo : Z) (bb : list byte)
         (Q : machine_state -> Prop),
    body <> 0 -> bytes_at rsegs m body bb ->
    stk rsegs m lo (bv_unsigned sp + -16) -> 0 < lo -> lo + 160 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    body + Z.of_nat (length bb) <= bv_unsigned sp - 160 \/ bv_unsigned sp <= body ->
    mem_inv rsegs m ->
    rw_cells rsegs m (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
    munch [(bv_unsigned sp - 160, bv_unsigned sp)] m0 m -> wmono rsegs m0 m ->
    bv_unsigned s0' = (if system_at bb then 2^64 - 10 else 0) ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       munch [(bv_unsigned sp - 160, bv_unsigned sp)] m0 m' -> wmono rsegs m0 m' -> mem_inv rsegs m' ->
       stk rsegs m' lo (bv_unsigned sp) ->
       Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0' s1 (Z_to_bv 64 body)
               (Z_to_bv 64 (Z.of_nat (length bb))) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13b88) fc None m (seg_rom rsegs)).
Proof.
  intros BC ra sp gp tp t0 t1 t2 s0 s0' s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m
    body lo bb Q HB0 BA ST LO0 HLO AL DJ MI FR MU WM HS0 HQ.
  unfold diginet_body_check_contract, DIGINET_BODY_CHECK in BC.
  pose proof ST as (Hlo0 & _ & _).
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  (* 0x13b88 jal diginet_body_check, with a0 = body, a1 = length bb and the callee's sp = sp - 16 *)
  step.
  eapply evt_cut; [eapply BC with (body := body) (lo := lo) (bb := bb) |];
    [ exact HB0 | exact BA | rewrite unsigned_lit by lia; apply mod8_sub16; exact AL
    | rewrite unsigned_lit by lia; exact ST | exact LO0 | rewrite unsigned_lit by lia; lia
    | rewrite unsigned_lit by lia; lia
    | exact MI | ];
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> &
                MUc & WMc & MIc & STc);
    rewrite unsigned_lit in MUc, STc by lia;
    transport_after_call rsegs m m2 MUc WMc; clear MUc WMc;
    repeat match goal with H : mem_inv rsegs m |- _ => clear H end;
    repeat match goal with H : stk rsegs m _ _ |- _ => clear H end;
    rename MIc into MI; rename STc into ST.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  (* 0x13b8c bne a0, s0 to the `jal abort` at 0x13bb4: a0 = body_check bb, s0 = -10 when system_at bb else 0 *)
  step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false;
      [ cbv iota
      | symmetry; unfold bv_eqb; rewrite HS0, body_check_spec; destruct (system_at bb); vm_compute; reflexivity ]
  end.
  (* epilogue: ld ra; ld s0; addi sp, sp, 16; ret *)
  step. step. step. step.
  apply evt_done. eapply HQ; [ exact MU | exact WM | exact MI | ].
  release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

(* ---- 0x13b3c-0x13b7c: one iteration of the inlined spec_system_at loop, at index i ---- *)

Lemma scan_step :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (body : Z) (bb : list byte) (i : nat)
         (Q : machine_state -> Prop),
    body <> 0 -> bytes_at rsegs m body bb -> Z.of_nat (length bb) < 2^63 ->
    bv_unsigned a2 = Z.of_nat i -> (i + 3 < length bb)%nat ->
    bv_unsigned a3 = 18446744073709551615 - body -> bv_unsigned a5 = body + 1 -> bv_unsigned a6 = 1 ->
    bv_unsigned a7 = 240 -> bv_unsigned t0 = 19 -> bv_unsigned t1 = 112 ->
    (sys_hit bb i = true -> forall s0' t2' t3' a2' : word, bv_unsigned s0' = 2^64 - 10 ->
       evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2' s0' s1 (Z_to_bv 64 body) a1 a2' a3 a4 a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
                       F (Z_to_bv 64 0x13b88) fc None m (seg_rom rsegs))) ->
    (sys_hit bb i = false -> forall t2' t3' : word,
       evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2' s0 s1 (Z_to_bv 64 body) a1 a2 a3 a4 a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
                       F (Z_to_bv 64 0x13b7c) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 body) a1 a2 a3 a4 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x13b3c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m body bb i
    Q HB0 BA HL Ha2 Hi Ha3 Ha5 Ha6 Ha7 Ht0 Ht1 KH KN.
  pose proof (bytes_at_bound rsegs m body bb BA) as [Hb0 Hb1].
  pose proof (at8_range bb i) as R0.
  pose proof (at8_range bb (S i)) as R1.
  pose proof (at8_range bb (S (S (S i)))) as R3.
  step. step. take false.                         (* add t2, a0, a2; 0x13b40 bltu t2, a0 *)
  step. step. step. take false.                   (* seqz; xor; 0x13b4c beqz t2 *)
  step. take false.                               (* 0x13b50 beqz a0 *)
  step.                                           (* add t2, a5, a2 *)
  pose proof (rd_at8 m body bb i BA ltac:(lia)) as HR. step. clear HR.       (* lbu t3, -1(t2): b[i] *)
  rewrite (zxb_b8 (at8 bb i)) by lia.
  step.                                           (* bne t3, a7: b[i] <> F0 *)
  destruct (Z.eqb_spec (at8 bb i) 240) as [E0|N0].
  2: { take true. apply KN. unfold sys_hit.
       replace (at8 bb i =? 240) with false by (symmetry; apply Z.eqb_neq; exact N0). reflexivity. }
  take false.
  step. take false.                               (* 0x13b60 bgeu a2, a3 *)
  pose proof (rd_at8 m body bb (S i) BA ltac:(lia)) as HR. step. clear HR.   (* lbu t3, 0(t2): b[i + 1] *)
  rewrite (zxb_b8 (at8 bb (S i))) by lia.
  step.                                           (* bne t3, t0: b[i + 1] <> 13 *)
  destruct (Z.eqb_spec (at8 bb (S i)) 19) as [E1|N1].
  2: { take true. apply KN. unfold sys_hit. rewrite E0.
       replace (at8 bb (S i) =? 19) with false by (symmetry; apply Z.eqb_neq; exact N1). reflexivity. }
  take false.
  step. step. take false.                         (* addi t3, a2, 3; 0x13b70 bltu a3, t3 *)
  pose proof (rd_at8 m body bb (S (S (S i))) BA ltac:(lia)) as HR. step. clear HR.  (* lbu t2, 2(t2): b[i + 3] *)
  rewrite (zxb_b8 (at8 bb (S (S (S i))))) by lia.
  step.                                           (* beq t2, t1: b[i + 3] = 70 *)
  destruct (Z.eqb_spec (at8 bb (S (S (S i)))) 112) as [E3|N3].
  - take true.
    step. step. step. step.                       (* slti; addi; andi s0; j 0x13b88 *)
    eapply KH; [ unfold sys_hit; rewrite E0, E1, E3; reflexivity | slti_fact ].
  - take false. apply KN. unfold sys_hit. rewrite E0, E1.
    replace (at8 bb (S (S (S i))) =? 112) with false by (symmetry; apply Z.eqb_neq; exact N3). reflexivity.
Qed.

(* ---- the loop: from index i with no hit below i, to 0x13b88 with s0 = -10 or 0 as system_at bb ---- *)

Lemma scan_loop :
  forall (ra sp gp tp t0 t1 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (body : Z) (bb : list byte)
         (Q : machine_state -> Prop),
    body <> 0 -> bytes_at rsegs m body bb -> Z.of_nat (length bb) < 2^63 ->
    bv_unsigned a3 = 18446744073709551615 - body -> bv_unsigned a4 = Z.of_nat (length bb) - 3 ->
    bv_unsigned a5 = body + 1 -> bv_unsigned a6 = 1 -> bv_unsigned a7 = 240 ->
    bv_unsigned t0 = 19 -> bv_unsigned t1 = 112 ->
    (forall s0' t2' t3' a2' : word, bv_unsigned s0' = (if system_at bb then 2^64 - 10 else 0) ->
       evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2' s0' s1 (Z_to_bv 64 body) a1 a2' a3 a4 a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
                       F (Z_to_bv 64 0x13b88) fc None m (seg_rom rsegs))) ->
    forall (n i : nat) (s0 t2 t3 a2 : word),
    bv_unsigned a2 = Z.of_nat i -> (i + S n = length bb - 3)%nat -> (4 <= length bb)%nat ->
    (forall j, (j < i)%nat -> sys_hit bb j = false) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 body) a1 a2 a3 a4 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x13b3c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc m body bb Q
    HB0 BA HL Ha3 Ha4 Ha5 Ha6 Ha7 Ht0 Ht1 K n.
  pose proof (bytes_at_bound rsegs m body bb BA) as [Hb0 Hb1].
  induction n as [|n IH]; intros i s0 t2 t3 a2 Ha2 Hn H4 Hno.
  all: eapply scan_step with (bb := bb) (i := i); try eassumption; [ lia | | ].
  all: try (intros Hh s0' t2' t3' a2' Hs0; apply K;
            rewrite (proj2 (system_at_true bb)) by (exists i; split; [lia | exact Hh]); exact Hs0).
  - (* the last index: bne a4, a2 at 0x13b80 is not taken, and no index has a hit *)
    intros Hh t2' t3'.
    step. step. take false.                       (* addi a2, a2, 1; 0x13b80 bne a4, a2 *)
    step.                                         (* 0x13b84 mv s0, zero *)
    apply K.
    rewrite (proj2 (system_at_false bb)); [ first [ reflexivity | vm_compute; reflexivity ] | ].
    intros j Hj. destruct (Nat.eq_dec j i) as [->|Hne]; [ exact Hh | apply Hno; lia ].
  - (* another index: back to 0x13b3c with i + 1 *)
    intros Hh t2' t3'.
    step. step. take true.                        (* addi a2, a2, 1; 0x13b80 bne a4, a2 *)
    apply (IH (S i)); [ fact | lia | lia | ].
    intros j Hj. destruct (Nat.eq_dec j i) as [->|Hne]; [ exact Hh | apply Hno; lia ].
Qed.

(* ---- the contract's post, from the callee-free continuation of refusal_tail ---- *)

Local Ltac post_q :=
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? HMU HWM HMI HST; cbv beta;
  do 16 eexists; split; [ reflexivity | ];
  split; [ exact HMU | ]; split; [ exact HWM | ]; split; [ exact HMI | exact HST ].

Theorem check_refusal_holds : diginet_body_check_contract -> check_refusal_contract.
Proof.
  intros BC. unfold check_refusal_contract, CHECK_REFUSAL, CHECK_REFUSAL_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m body lo bb
    HB0 BA HL ST LO0 HLO AL DJ MI.
  pose proof (bytes_at_bound rsegs m body bb BA) as [Hb0 Hb1].
  pose proof ST as (Hlo0 & Hsp64 & _).
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  step. step. step.                               (* addi sp, sp, -16; sd ra, 8(sp); sd s0, 0(sp) *)
  step. step.                                     (* addi a2, zero, 4; 0x13b18 bltu a1, a2 *)
  destruct (Z.ltb_spec (Z.of_nat (length bb)) 4) as [L4|G4].
  - (* len < 4: no index to test, s0 = 0 *)
    take true.
    step.                                         (* 0x13b84 mv s0, zero *)
    eapply (refusal_tail BC) with (s0 := s0) (m0 := m) (lo := lo);
      first [ eassumption | post_q
            | rewrite (sys_short bb) by lia; first [ reflexivity | vm_compute; reflexivity ] ].
  - take false.
    do 8 step.                                    (* 0x13b1c-0x13b38: i = 0, ~body, len - 3, body + 1, snez body,
                                                     F0, 13, 70 *)
    eapply scan_loop with (bb := bb) (n := (length bb - 4)%nat) (i := 0%nat).
    all: lazymatch goal with
         | |- forall _ : word, _ =>
             intros s0' t2' t3' a2' HS0;
             eapply (refusal_tail BC) with (s0 := s0) (m0 := m) (lo := lo); first [ eassumption | post_q ]
         | |- forall _ : nat, _ => intros j Hj; exfalso; lia
         | _ => first [ assumption | fact | lia ]
         end.
Qed.
