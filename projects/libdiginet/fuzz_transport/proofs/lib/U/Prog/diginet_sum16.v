(* proves the UBSan contract of diginet_sum16 (fuzz_transport.ubsan, 0x17f60), with its three pointer traps not taken. *)
(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame proofs/libdiginet/fuzz_frame/lib/U/Prog/diginet_sum16.v at 9bd29914ffdef650a37285056a472ff186b4331a to fuzz_transport's images *)
(* Walk of diginet_sum16 (src/diginet_frame.c:42-48 at 835f336c) in fuzz_transport.ubsan, 0x17f60.
   Each turn of the loop at 0x17f74 checks p + i before it reads p[i]: 0x17f74 (p + i < p),
   0x17f80 ((p != 0) == (p + i == 0)) and 0x17f84 (p == 0) branch to the trap at 0x17fac.
   bytes_at gives p + length bb <= 2^64 and p is not 0, so for i < length bb no branch is taken. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import FrameBytes diginet_sum16_c.
Import ListNotations.
Open Scope Z_scope.

Ltac uns := rewrite ?unsigned_lit by lia.
Ltac br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uns; solve_cond_rec]
  end.

Lemma sum_firstn_S : forall (l : list byte) i, (i < length l)%nat ->
  sum_bytes (firstn (S i) l) = sum_bytes (firstn i l) + bz (nth i l (Z_to_bv 8 0)).
Proof.
  induction l as [|x l IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; cbn [firstn sum_bytes nth].
  - rewrite firstn_O. cbn [sum_bytes]. lia.
  - rewrite IH by lia. lia.
Qed.

(* slli 0x30 then srli 0x30 at 0x17fa0: the low 16 bits. *)
Lemma sh48 : forall z,
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 48))) 48)
  = Z_to_bv 64 (z mod 2^16).
Proof.
  intros z. f_equal. rewrite !unsigned_lit_wrap.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  Z.div_mod_to_equations. lia.
Qed.

Lemma lib_sum16_mod : forall l, lib_sum16 l = sum_bytes l mod 2^16.
Proof. intros l. unfold lib_sum16. Z.div_mod_to_equations. lia. Qed.

(* The loop at 0x17f74, from the turn i with k > 0 turns left: a1 = k, a2 = the sum of the
   first i bytes, a3 = (p != 0), a4 = a5 = p + i. *)
Lemma sum16_loop : forall (k : nat)
    (ra sp gp tp t0 t1 t2 s0 s1 a3v a6v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z) (bb : list byte)
    (i : nat) (r s q4 q5 : Z),
  p <> 0 -> bytes_at rsegs m p bb -> (i + k)%nat = length bb -> (0 < k)%nat ->
  a3v = Z_to_bv 64 1 -> r = Z.of_nat k -> s = sum_bytes (firstn i bb) ->
  q4 = p + Z.of_nat i -> q5 = p + Z.of_nat i ->
  evt rsegs
    (fun ms' => exists a1' a2' a3' a4' a5' a6' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lib_sum16 bb)) a1' a2' a3' a4' a5' a6' a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 r) (Z_to_bv 64 s) a3v
             (Z_to_bv 64 q4) (Z_to_bv 64 q5) a6v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17f74) fc None m (seg_rom rsegs)).
Proof.
  intros k. induction k as [|k IH];
    intros ra sp gp tp t0 t1 t2 s0 s1 a3v a6v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p bb i r s q4 q5
      Hp BA Hik Hk Ha3 Hr Hs Hq4 Hq5; [lia|].
  subst a3v r s q4 q5.
  pose proof (bytes_at_bound rsegs m p bb BA) as BB.
  assert (Hi : (i < length bb)%nat) by lia.
  pose proof (rd1 m p bb i BA Hi) as RI.
  remember (nth i bb (Z_to_bv 8 0)) as b eqn:Eb.
  assert (SL : v_sltiu (Z_to_bv 64 (p + Z.of_nat i)) 1 = Z_to_bv 64 0).
  { unfold v_sltiu. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
    replace (p + Z.of_nat i <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  (* 0x17f74 bltu a4, a0: p + i does not wrap. *)
  step. br false.
  (* 0x17f78 seqz, 0x17f7c xor; 0x17f80 beqz a6: p is not 0 and p + i is not 0. *)
  step. step. step.
  rewrite SL.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false; [cbv iota | symmetry; vm_compute; reflexivity]
  end.
  (* 0x17f84 beqz a0: p is not 0. *)
  step. br false.
  (* 0x17f88 lbu p[i]; a1 - 1; a5 + 1; a2 + p[i]; a4 + 1. *)
  step. step. step. step. step.
  (* 0x17f9c bnez a1. *)
  step.
  assert (ES : sum_bytes (firstn i bb) + bv_unsigned (zxb b) = sum_bytes (firstn (S i) bb)).
  { rewrite sum_firstn_S by exact Hi. rewrite <- Eb. unfold zxb, bz. rewrite zxb_u. reflexivity. }
  destruct k as [|k].
  - br false.
    assert (EL : firstn (S i) bb = bb) by (replace (S i) with (length bb) by lia; apply firstn_all).
    rewrite ES, EL.
    step. step.
    rewrite sh48, <- lib_sum16_mod.
    step.
    apply evt_done. do 6 eexists. reflexivity.
  - br true.
    eapply IH with (i := S i); [exact Hp | exact BA | lia | lia | reflexivity | lia | | lia | lia].
    rewrite <- ES. reflexivity.
Qed.

Theorem diginet_sum16_holds : diginet_sum16_contract.
Proof.
  unfold diginet_sum16_contract, DIGINET_SUM16.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p bb
    Hp BA.
  pose proof (bytes_at_bound rsegs m p bb BA) as BB.
  assert (LB : 0 <= Z.of_nat (length bb) < 2^64) by lia.
  (* 0x17f60 mv a2, zero; 0x17f64 beqz a1: the empty input returns before the loop. *)
  step. step.
  if_cases K.
  - unfold bv_eqb in K. rewrite (unsigned_lit _ LB) in K. apply Z.eqb_eq in K.
    change (bv_unsigned (Z_to_bv 64 0)) with 0 in K.
    assert (E0 : lib_sum16 bb = 0) by (destruct bb as [|x bb]; [reflexivity | cbn [length] in K; lia]).
    rewrite E0.
    step. step. step.
    apply evt_done. do 6 eexists. reflexivity.
  - unfold bv_eqb in K. rewrite (unsigned_lit _ LB) in K. apply Z.eqb_neq in K.
    change (bv_unsigned (Z_to_bv 64 0)) with 0 in K.
    (* 0x17f68 snez a3, a0; 0x17f6c mv a4, a0; 0x17f70 mv a5, a0. *)
    step. step. step.
    eapply (sum16_loop (length bb)) with (i := 0%nat); [exact Hp | exact BA | lia | lia | | | | |].
    + unfold v_sltu, c_ltu, bv_ltu. rewrite (unsigned_lit p) by lia. fold_lit_ux.
      replace (0 <? p) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    + reflexivity.
    + reflexivity.
    + lia.
    + lia.
Qed.
