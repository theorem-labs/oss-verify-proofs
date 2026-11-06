(* The inlined spec_system_at of check_round_trip in fuzz_frame.plain (0x13124 .. 0x1315c):
   the loop over the body bytes bb at B leaves s0 = 1 when system_at bb, else 0.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac
  ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import crt_m1_lib.
Import ListNotations.
Open Scope Z_scope.

Lemma crt_byte_at : forall (l : list byte) i, (i < length l)%nat -> exists x, nth_error l i = Some x.
Proof. intros l i Hi. destruct (nth_error l i) eqn:N; [eexists; reflexivity|]. apply nth_error_None in N. lia. Qed.

Lemma crt_firstn1_skipn : forall {X} (l : list X) i b, nth_error l i = Some b -> firstn 1 (skipn i l) = [b].
Proof.
  intros X l; induction l as [|c l IH]; intros [|i] b N; cbn in *; try discriminate.
  - injection N as ->. reflexivity.
  - apply IH; exact N.
Qed.

Lemma crt_rdb : forall m A l (i : nat) b, bytes_at rsegs m A l -> nth_error l i = Some b ->
  ov_read_bytes rsegs m (wa (A + Z.of_nat i)) 1 = Some [b].
Proof.
  intros m A l i b BL N. pose proof (nth_error_Some l i) as NS. rewrite N in NS.
  assert (Hi : (i < length l)%nat) by (apply NS; discriminate).
  rewrite (bytes_at_ov_read rsegs m A l i 1 BL ltac:(lia)). f_equal. apply crt_firstn1_skipn. exact N.
Qed.

Lemma crt_at8_nth : forall l i x, nth_error l i = Some x -> at8 l i = bv_unsigned x.
Proof. intros l i x H. unfold at8, bz. f_equal. apply nth_error_nth. exact H. Qed.

Lemma crt_sys_hit_bytes : forall bb i x0 x1 x3, nth_error bb i = Some x0 -> nth_error bb (S i) = Some x1 ->
  nth_error bb (S (S (S i))) = Some x3 ->
  sys_hit bb i = (bv_unsigned x0 =? 240) && (bv_unsigned x1 =? 19) && (bv_unsigned x3 =? 112).
Proof.
  intros bb i x0 x1 x3 N0 N1 N3. unfold sys_hit.
  rewrite (crt_at8_nth bb i x0 N0), (crt_at8_nth bb (S i) x1 N1), (crt_at8_nth bb (S (S (S i))) x3 N3).
  reflexivity.
Qed.

Section SYS.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word)
  (fc : bv 32) (m : word -> option byte) (P : machine_state -> Prop) (B : Z) (bb : list byte).
Hypothesis HB0 : 0 <= B.
Hypothesis HB1 : B + Z.of_nat (length bb) < 2^64.
Hypothesis HB2 : Z.of_nat (length bb) < 2^63.
Hypothesis BB : bytes_at rsegs m B bb.
Hypothesis K : forall (x0 x1 x2 x3 x4 x5 x6 : word) (v : Z), v = (if system_at bb then 1 else 0) ->
  evt rsegs P (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 v) s1 x0 x1 x2 x3 x4 x5 x6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
                       s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x1315c) fc None m (seg_rom rsegs)).

(* One turn of the loop at 0x13124, for the byte i: a hit ends at 0x1315c with s0 = 1;
   else the walk goes on at 0x1313c. *)
Lemma crt_sys_iter : forall (i : nat) (a6 : word),
  (i + 3 < length bb)%nat ->
  (sys_hit bb i = false -> forall a6' : word,
     evt rsegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat i))
                          (Z_to_bv 64 (Z.of_nat (length bb) - 3)) (Z_to_bv 64 240) (Z_to_bv 64 19)
                          (Z_to_bv 64 (B + 1 + Z.of_nat i)) (Z_to_bv 64 112) a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1313c) fc None m (seg_rom rsegs))) ->
  evt rsegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat i))
                       (Z_to_bv 64 (Z.of_nat (length bb) - 3)) (Z_to_bv 64 240) (Z_to_bv 64 19)
                       (Z_to_bv 64 (B + 1 + Z.of_nat i)) (Z_to_bv 64 112) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13124) fc None m (seg_rom rsegs)).
Proof.
  intros i a6 Hi NEXT.
  pose proof (bytes_at_bound rsegs m B bb BB) as HBB.
  destruct (crt_byte_at bb i ltac:(lia)) as [x0 N0].
  destruct (crt_byte_at bb (S i) ltac:(lia)) as [x1 N1].
  destruct (crt_byte_at bb (S (S (S i))) ltac:(lia)) as [x3 N3].
  pose proof (crt_rdb m B bb i x0 BB N0) as R0.
  pose proof (crt_rdb m B bb (S i) x1 BB N1) as R1.
  pose proof (crt_rdb m B bb (S (S (S i))) x3 BB N3) as R3.
  pose proof (crt_sys_hit_bytes bb i x0 x1 x3 N0 N1 N3) as Hit.
  assert (X0 : 0 <= bv_unsigned x0 < 256) by exact (bz_range x0).
  assert (X1 : 0 <= bv_unsigned x1 < 256) by exact (bz_range x1).
  assert (X3 : 0 <= bv_unsigned x3 < 256) by exact (bz_range x3).
  step. unfold zxb. step.
  destruct (Z.eqb_spec (bv_unsigned x0) 240) as [E0|E0].
  2: { crt_br true. apply NEXT. rewrite Hit. reflexivity. }
  crt_br false. step. unfold zxb. step.
  destruct (Z.eqb_spec (bv_unsigned x1) 19) as [E1|E1].
  2: { crt_br true. apply NEXT. rewrite Hit. reflexivity. }
  crt_br false. step. unfold zxb. step.
  destruct (Z.eqb_spec (bv_unsigned x3) 112) as [E3|E3].
  2: { crt_br false. apply NEXT. rewrite Hit. reflexivity. }
  crt_br true. step. step. step.
  assert (SA : system_at bb = true).
  { apply system_at_true. exists i. split; [lia|]. rewrite Hit. reflexivity. }
  eapply K. rewrite SA, slti_small by lia.
  destruct (Z.ltb_spec (Z.of_nat i) 0) as [Ln|_]; [lia|]. reflexivity.
Qed.

(* The loop at 0x13124: i bytes tested, k + 1 left. *)
Lemma crt_sys_loop : forall k (i : nat) (a6 : word) (v0 v1 v2 v3 v4 v5 : Z),
  (i + S k + 3 = length bb)%nat ->
  (forall j, (j < i)%nat -> sys_hit bb j = false) ->
  v0 = Z.of_nat i -> v1 = Z.of_nat (length bb) - 3 -> v2 = 240 -> v3 = 19 -> v4 = B + 1 + Z.of_nat i -> v5 = 112 ->
  evt rsegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v0) (Z_to_bv 64 v1) (Z_to_bv 64 v2) (Z_to_bv 64 v3)
                       (Z_to_bv 64 v4) (Z_to_bv 64 v5) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13124) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH]; intros i a6 v0 v1 v2 v3 v4 v5 Hk Hpre -> -> -> -> -> ->;
    (apply crt_sys_iter; [lia|]; intros Hhit a6').
  - step. step. step. crt_br false. step. step. step. step.
    assert (SA : system_at bb = false).
    { apply system_at_false. intros j Hj. destruct (Nat.lt_ge_cases j i) as [Lt|Ge]; [exact (Hpre j Lt)|].
      replace j with i by lia. exact Hhit. }
    eapply K. rewrite SA. vm_compute. reflexivity.
  - step. step. step. crt_br true.
    eapply (IH (S i)).
    all: lazymatch goal with
         | |- forall _ : nat, _ =>
             intros j Hj; destruct (Nat.eq_dec j i) as [->|Ne]; [exact Hhit | apply Hpre; lia]
         | |- _ => first [reflexivity | lia]
         end.
Qed.

End SYS.
