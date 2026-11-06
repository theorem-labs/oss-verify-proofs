(* Walk of the harness's static [number] (fuzz_lock.c:64-75) in fuzz_lock.ubsan, 0x131cc: the walk of
   lib/U/Prog/digits.v (the same instructions, shifted by -0x374).
   The UBSan trap [unimp] at 0x13254 is reached from five branches; none is taken:
   - 0x131f8 [bltu a6,a0]: a6 = s + i >= a0 = s (s + len <= 2^64, no wrap);
   - 0x13204 [beqz t0], t0 = (s <> 0) xor (s + i = 0): 0 < s and s + i < 2^64 (seqz_ok);
   - 0x13208 [beqz a0]: 0 < s;
   - 0x13224 [bne t2,a2]: the signed product v * 10 does not overflow, as v < 10^17 (at most 17 digits read
     before the 18th) (mul_ok);
   - 0x13238 [bne t0,t1]: the signed sum v * 10 + d does not overflow, 0 <= d <= 9 (add_ok).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Spec Require Import StrFun LockSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import DigitsMach number_c.
Import ListNotations.
Open Scope Z_scope.

Ltac uns := rewrite ?unsigned_lit by lia.
Ltac br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uns; solve_cond_rec]
  end.

Section D.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (s : Z) (l : list byte).
Hypothesis Hs : 0 < s.
Hypothesis BL : bytes_at rsegs m s l.
Hypothesis MI : mem_inv rsegs m.

Local Notation ST pc t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s) a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Local Notation Q := (number_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m l).

(* 0x1324c: mv a0,a2; ret *)
Lemma fin : forall (t0 t1 t2 a1 a3 a4 a5 a6 a7 : word) (w : Z), w = digits l ->
  evt rsegs Q (ST 0x1324c t0 t1 t2 a1 (Z_to_bv 64 w) a3 a4 a5 a6 a7).
Proof.
  intros t0 t1 t2 a1 a3 a4 a5 a6 a7 w ->.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  step. step. rewrite ?Z.add_0_r.
  apply evt_done. do 11 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|exact MI].
Qed.

(* 0x131d8: li a2,-1; j 0x1324c *)
Lemma bad : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 : word), digits l = -1 ->
  evt rsegs Q (ST 0x131d8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7).
Proof.
  intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 H.
  step. step. eapply fin. rewrite H. first [reflexivity | lia | (vm_compute; reflexivity)].
Qed.

(* the loop of fuzz_lock.c:69-73, at 0x131f8: i bytes read, value v, r = S k bytes left, a6 = a7 = s + i *)
Lemma loop : forall k (i : nat) (t0 t1 t2 a3 : word) (r v p : Z),
  (i + S k = length l)%nat -> (length l <= 18)%nat ->
  digits l = dig_go (skipn i l) v -> 0 <= v < 10 ^ Z.of_nat i ->
  r = Z.of_nat (S k) -> p = s + Z.of_nat i -> a3 = Z_to_bv 64 1 ->
  evt rsegs Q (ST 0x131f8 t0 t1 t2 (Z_to_bv 64 r) (Z_to_bv 64 v) a3 (Z_to_bv 64 (-10)) (Z_to_bv 64 10)
                  (Z_to_bv 64 p) (Z_to_bv 64 p)).
Proof.
  pose proof (bytes_at_bound rsegs m s l BL) as HB.
  induction k as [|k IH]; intros i t0 t1 t2 a3 r v p Hk H18 Hd Hv -> -> ->.
  all: destruct (byte_at l i ltac:(lia)) as [b Nb].
  all: pose proof (rdb m s l i b BL Nb) as R; pose proof (skipn_nth l i b Nb) as SK.
  all: rewrite SK in Hd; cbn [dig_go] in Hd.
  all: assert (V17 : 0 <= v < 10 ^ 17) by (pose proof (pow_le17 i ltac:(lia)); lia).
  (* 0x131f8 bltu a6,a0 (trap): s + i < s is false *)
  all: step; br false.
  (* 0x131fc-0x13204 seqz/xor/beqz (trap): s + i <> 0 *)
  all: step; step; step; if_false_by (seqz_ok (s + Z.of_nat i) ltac:(lia)).
  (* 0x13208 beqz a0 (trap): s <> 0 *)
  all: step; br false.
  (* 0x1320c lbu; 0x13210 addi; 0x13214 bltu: not a digit -> 0x131d8 *)
  all: step; step; step; rewrite (dig_test b).
  all: destruct ((48 <=? bz b) && (bz b <=? 57)) eqn:D; cbn [negb]; cbv iota; try rewrite D in Hd; cbv iota in Hd.
  2, 4: (apply bad; exact Hd).
  (* 0x13218-0x13224 mulh/mul/srai/bne (trap): v * 10 does not overflow *)
  all: step; step; step; step; if_false_by (mul_ok v V17).
  (* 0x13228-0x13238 andi/add/slt/slti/bne (trap): v * 10 + d does not overflow *)
  all: step; step; step; step; step; if_false_by (add_ok v b V17 D).
  all: rewrite (dval v b V17 D).
  all: pose proof (dig_bound i v b Hv D) as VB.
  (* 0x1323c-0x13248 addi a1; addi a7; addi a6; bnez a1 *)
  all: step; step; step; step.
  - br false. eapply fin. rewrite Hd.
    assert (E : skipn (S i) l = []) by (apply skipn_all2; lia). rewrite E. reflexivity.
  - br true.
    eapply IH with (i := S i); [lia | exact H18 | exact Hd | exact VB | lia | lia | reflexivity].
Qed.

End D.

Theorem number_holds : number_contract.
Proof.
  unfold number_contract, NUMBER.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s l
    Hs BL MI.
  pose proof (bytes_at_bound rsegs m s l BL) as HB.
  (* 0x131cc addi a2,a1,-19; 0x131d0 li a3,-18; 0x131d4 bgeu a2,a3: 1 <= len <= 18 *)
  step. step. step.
  rewrite (len_test (Z.of_nat (length l))) by lia.
  destruct ((Z.of_nat (length l) =? 0) || (18 <? Z.of_nat (length l))) eqn:LT; cbn [negb]; cbv iota.
  - assert (Hd : digits l = -1).
    { unfold digits.
      replace ((length l =? 0)%nat || (18 <? length l)%nat) with true; [reflexivity|].
      symmetry. apply orb_true_iff in LT. apply orb_true_iff.
      destruct LT as [E|E]; [left; apply Nat.eqb_eq; apply Z.eqb_eq in E; lia
                            | right; apply Nat.ltb_lt; apply Z.ltb_lt in E; lia]. }
    eapply bad; eassumption.
  - apply orb_false_iff in LT. destruct LT as [L1 L2]. apply Z.eqb_neq in L1. apply Z.ltb_ge in L2.
    assert (E : ((length l =? 0)%nat || (18 <? length l)%nat) = false).
    { apply orb_false_iff. split; [apply Nat.eqb_neq; lia | apply Nat.ltb_ge; lia]. }
    (* 0x131e0 li a2,0; snez a3,a0; li a4,-10; li a5,10; mv a6,a0; mv a7,a0 *)
    step. step. step. step. step. step.
    eapply loop with (k := (length l - 1)%nat) (i := 0%nat).
    all: lazymatch goal with
         | |- digits _ = _ => unfold digits; rewrite E; reflexivity
         | |- _ = Z_to_bv 64 1 => apply snez_ok; lia
         | |- 0 <= _ < _ => cbn; lia
         | _ => first [ eassumption | lia | reflexivity ]
         end.
Qed.
