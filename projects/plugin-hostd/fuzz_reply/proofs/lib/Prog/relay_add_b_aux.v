From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import pthread_mutex_lock_c pthread_mutex_unlock_c memset_c.
Import ListNotations.
Open Scope Z_scope.

Lemma ra_pre : forall m A (s t : list byte), bytes_at rsegs m A (s ++ t) -> bytes_at rsegs m A s.
Proof. intros m A s t H. apply bytes_at_app in H. exact (proj1 H). Qed.

Lemma ra_cut : forall m A cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[W B] (H0 & H1 & H)].
  apply cells_wf_app in W. destruct W as [W1 W2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 B2].
  rewrite (cells_bytes_length cs1 W1) in B2. rewrite cells_size_app in H1, H.
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply H. lia.
Qed.

Lemma ra_join : forall m A B cs1 cs2, rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] (H0 & H1 & H)] [[W2 B2] (G0 & G1 & G)] ->.
  split; split.
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite (cells_bytes_length cs1 W1). exact B2.
  - lia.
  - rewrite cells_size_app. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))) as [Hlt|Hge]; [apply H; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply G. lia.
Qed.

Ltac fold_sx :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?z)] => is_Zlit z;
      let v := eval vm_compute in (bv_unsigned (sx32 (Z_to_bv 64 z))) in
      replace (sx32 (Z_to_bv 64 z)) with (Z_to_bv 64 v) by (vm_compute; reflexivity)
  end.

Definition ra_ret (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (v : word) (W : list (Z * Z)) (m : word -> option byte) (P : (word -> option byte) -> Prop) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ P m'.

Lemma ra_neg : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 64 <= bv_unsigned sp -> bv_signed a0 < 0 -> mem_inv rsegs m ->
  evt rsegs (ra_ret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 (-1))
               [(bv_unsigned sp - 64, bv_unsigned sp)] m (fun _ => True))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1332c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ST LO NEG MI.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  carve_frame 64%nat ST.
  do 10 step. if_true.
  do 10 step.
  apply evt_done. unfold ra_ret. do 15 eexists.
  split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|exact I].
Qed.

Tactic Notation "call_rw" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply SPEC
      | let ms' := fresh "ms'" in let PO := fresh "PO" in
        intros ms' PO;
        unfold memset_post, pthread_mutex_unlock_post, pthread_mutex_lock_post in PO;
        rewrite ?unsigned_lit in PO by lia;
        try change (Z.to_nat 56) with 56%nat in PO;
        try change (0 mod 256) with 0 in PO;
        revert ms' PO; post_call segs mm ]
  end.

Lemma rw_cells_nil : forall m A, 0 <= A <= 2 ^ 64 -> rw_cells rsegs m A [CB 0 []].
Proof.
  intros m A H. split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes app]. apply bytes_at_nil. lia.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
Qed.

Ltac fold_tonat :=
  repeat match goal with
  | H : context [Z.to_nat ?x] |- _ => is_Zlit x;
      let v := eval vm_compute in (Z.to_nat x) in progress change (Z.to_nat x) with v in H
  | |- context [Z.to_nat ?x] => is_Zlit x;
      let v := eval vm_compute in (Z.to_nat x) in progress change (Z.to_nat x) with v
  end.

Lemma ra_c16 : pthread_mutex_lock_contract -> pthread_mutex_unlock_contract -> memset_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo N G : Z) (pre junk post : list byte),
  stk rsegs m lo (bv_unsigned sp) -> lo + 160 <= bv_unsigned sp -> 0x100000 <= lo ->
  0 <= bv_signed a0 -> mem_inv rsegs m ->
  rw_cells rsegs m 0x31018 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  bytes_at rsegs m 0x20d44 (le4 (Z_to_bv 64 (-1))) ->
  rw_cells rsegs m 0x30fd8 [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 16)] ->
  rw_cells rsegs m 0x30ff0 [C8 (Z_to_bv 64 G)] ->
  0 <= N < 4 -> 0 <= G ->
  rw_cells rsegs m G [CB (Z.to_nat (56 * N)) pre] ->
  rw_cells rsegs m (G + 56 * N) [CB 56 junk] ->
  rw_cells rsegs m (G + 56 * N + 56) [CB (Z.to_nat (840 - 56 * N)) post] ->
  (G + 896 <= 0x20d44 \/ 0x20d48 <= G) ->
  (G + 896 <= 0x30fc0 \/ 0x31040 <= G) ->
  G + 896 <= lo ->
  evt rsegs (ra_ret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 0)
               [(bv_unsigned sp - 160, bv_unsigned sp); (0x3101c, 0x31020); (0x30fd8, 0x30fdc);
                (G + 56 * N, G + 56 * N + 56)] m
               (fun m' => rw_cells rsegs m' 0x31018 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
                  bytes_at rsegs m' 0x20d44 (le4 (Z_to_bv 64 (-1))) /\
                  rw_cells rsegs m' 0x30fd8 [C4 (Z_to_bv 64 (N + 1)); C4 (Z_to_bv 64 16)] /\
                  rw_cells rsegs m' 0x30ff0 [C8 (Z_to_bv 64 G)] /\
                  rw_cells rsegs m' G [CB (Z.to_nat (56 * N)) pre] /\
                  rw_cells rsegs m' (G + 56 * N) [C4 a0; CB 52 (repeat (Z_to_bv 8 0) 52)] /\
                  rw_cells rsegs m' (G + 56 * N + 56) [CB (Z.to_nat (840 - 56 * N)) post]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1332c) fc None m (seg_rom rsegs)).
Proof.
  intros SPL SPU MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo N G pre junk post ST LO HI FD MI GL WK NS GS NR G0 TP TE TQ D1 D2 D3.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (0x3101c, 0x31020); (0x30fd8, 0x30fdc);
                (G + 56 * N, G + 56 * N + 56)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct (ra_cut _ _ [_] [_; _] GL) as [GL0 GL12]. clear GL.
  destruct (ra_cut _ _ [_] [_] GL12) as [GL1 GL2]. clear GL12.
  assert (TB : bytes_at rsegs m 200728 [hd (Z_to_bv 8 0) (le4 (Z_to_bv 64 0))]).
  { pose proof (proj2 (proj1 GL0)) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    rewrite <- (firstn_skipn 1 (le4 (Z_to_bv 64 0))) in B. exact (ra_pre _ _ _ _ B). }
  carve_frame 64%nat ST.
  do 10 step. if_false.
  do 6 step.
  call (SPL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            200728 (hd (Z_to_bv 8 0) (le4 (Z_to_bv 64 0)))).
  1: reflexivity.
  1: exact TB.
  1: reflexivity.
  1: exact GL1.
  1: assumption.
  cbv delta [mkR].
  match goal with H : rw_cells _ _ _ [C4 (Z_to_bv 64 16)] |- _ => rename H into L16 end.
  assert (NC : N = 0 \/ N = 1 \/ N = 2 \/ N = 3) by lia.
  destruct NC as [E|[E|[E|E]]]; subst N;
    [ replace (G + 56 * 0) with G in * by lia;
      assert (pre = []) as -> by (destruct TP as [[W _] _]; cbn in W; destruct pre; [reflexivity | cbn in W; lia]);
      clear TP
    | replace (G + 56 * 1) with (G + 56) in * by lia; replace (G + 56 + 56) with (G + 112) in * by lia
    | replace (G + 56 * 2) with (G + 112) in * by lia; replace (G + 112 + 56) with (G + 168) in * by lia
    | replace (G + 56 * 3) with (G + 168) in * by lia; replace (G + 168 + 56) with (G + 224) in * by lia ];
    fold_tonat.
  all: step; fold_sx; step; fold_sx; step; step; if_true.
  all: do 8 step.
  all: call_rw (MSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ junk);
    [ rewrite ?unsigned_lit by lia; exact TE | assumption | ].
  all: do 5 step.
  all: call_rw (SPU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 200728 lo);
    [ reflexivity
    | exact (ra_join _ _ _ [_] [_; _] GL0 (ra_join _ _ _ [_] [_] L16 GL2 eq_refl) eq_refl)
    | rewrite ?unsigned_lit by lia; eassumption
    | rewrite ?unsigned_lit by lia; lia
    | rewrite ?unsigned_lit by lia; lia
    | assumption
    | ].
  all: match goal with
  | H : bytes_at rsegs ?mm 134468 _ |- _ =>
      assert (RD : ov_read_bytes rsegs mm (wa 134468) 4 = Some (le4 (Z_to_bv 64 (-1))));
      [ replace (wa 134468) with (wa (134468 + 0)) by reflexivity;
        rewrite (bytes_at_read rsegs mm 134468 (le4 (Z_to_bv 64 (-1))) 0 4 H ltac:(lia)) by (rewrite length_le4; lia);
        reflexivity
      | ]
  end.
  all: step; step; fold_sx; step.
  all: change (le1 (Z_to_bv 64 0)) with (le1 (zxb (Z_to_bv 8 0))); mem_after_store.
  all: step; if_true.
  all: do 11 step.
  all: apply evt_done; unfold ra_ret; do 15 eexists; split; [reflexivity|].
  all: split; [eassumption|]; split; [eassumption|]; split; [eassumption|].
  all: split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|].
  all: split; [first [eassumption | apply rw_cells_nil; lia]|]; split; [eassumption|]; eassumption.
Qed.

Definition ra_g1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (fd : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' junk,
    ms' = MS (mkR (Z_to_bv 64 0x1339c) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 fd (Z_to_bv 64 0x31018)
                  (Z_to_bv 64 0) (Z_to_bv 64 896) a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 (-1)) (Z_to_bv 64 0x30fc0) (Z_to_bv 64 0) (Z_to_bv 64 16) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x17010) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (0x3101c, 0x31020)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned sp + -64) [CB 8 junk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk rsegs m' lo (bv_unsigned sp + -64)
    /\ rw_cells rsegs m' 0x31018 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)]
    /\ bytes_at rsegs m' 0x20d44 (le4 (Z_to_bv 64 (-1)))
    /\ rw_cells rsegs m' 0x30fd8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells rsegs m' 0x30ff0 [C8 (Z_to_bv 64 0)].

Lemma ra_g1 : pthread_mutex_lock_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 160 <= bv_unsigned sp -> 0x100000 <= lo ->
  0 <= bv_signed a0 -> mem_inv rsegs m ->
  rw_cells rsegs m 0x31018 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  bytes_at rsegs m 0x20d44 (le4 (Z_to_bv 64 (-1))) ->
  rw_cells rsegs m 0x30fd8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m 0x30ff0 [C8 (Z_to_bv 64 0)] ->
  evt rsegs (ra_g1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1332c) fc None m (seg_rom rsegs)).
Proof.
  intros SPL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO HI FD MI GL WK NS GS.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (0x3101c, 0x31020)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct (ra_cut _ _ [_] [_; _] GL) as [GL0 GL12]. clear GL.
  destruct (ra_cut _ _ [_] [_] GL12) as [GL1 GL2]. clear GL12.
  assert (TB : bytes_at rsegs m 200728 [hd (Z_to_bv 8 0) (le4 (Z_to_bv 64 0))]).
  { pose proof (proj2 (proj1 GL0)) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    rewrite <- (firstn_skipn 1 (le4 (Z_to_bv 64 0))) in B. exact (ra_pre _ _ _ _ B). }
  carve_frame 64%nat ST.
  do 10 step. if_false.
  do 6 step.
  call (SPL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            200728 (hd (Z_to_bv 8 0) (le4 (Z_to_bv 64 0)))).
  1: reflexivity.
  1: exact TB.
  1: reflexivity.
  1: exact GL1.
  1: assumption.
  cbv delta [mkR].
  match goal with H : rw_cells _ _ _ [C4 (Z_to_bv 64 16)] |- _ => rename H into L16 end.
  step; fold_sx; step; fold_sx; step; step; if_false.
  step; if_false.
  do 6 step.
  apply evt_done. unfold ra_g1_post. cbv beta delta [mkR].
  do 15 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [eassumption|].
  split; [exact (ra_join _ _ _ [_] [_; _] GL0 (ra_join _ _ _ [_] [_] L16 GL2 eq_refl) eq_refl)|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma ra_g2 : pthread_mutex_unlock_contract -> memset_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 fd
    (F : bvmap 5 word) fc (m : word -> option byte) (lo R : Z) (junk jt post : list byte),
  rw_cells rsegs m (bv_unsigned sp + -64) [CB 8 junk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (bv_unsigned sp + -64) -> lo + 160 <= bv_unsigned sp -> 0x100000 <= lo ->
  0 <= bv_signed fd -> mem_inv rsegs m ->
  rw_cells rsegs m 0x31018 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)] ->
  bytes_at rsegs m 0x20d44 (le4 (Z_to_bv 64 (-1))) ->
  rw_cells rsegs m 0x30fd8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m 0x30ff0 [C8 (Z_to_bv 64 0)] ->
  0 < R ->
  rw_cells rsegs m R [CB 56 jt] ->
  rw_cells rsegs m (R + 56) [CB 840 post] ->
  (R + 896 <= 0x20d44 \/ 0x20d48 <= R) ->
  (R + 896 <= 0x30fc0 \/ 0x31040 <= R) ->
  R + 896 <= lo ->
  evt rsegs (ra_ret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 0)
               [(bv_unsigned sp - 160, bv_unsigned sp); (0x3101c, 0x31020); (0x30fd8, 0x30fe0); (0x30ff0, 0x30ff8);
                (R, R + 56)] m
               (fun m' => rw_cells rsegs m' 0x31018 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
                  bytes_at rsegs m' 0x20d44 (le4 (Z_to_bv 64 (-1))) /\
                  rw_cells rsegs m' 0x30fd8 [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 16)] /\
                  rw_cells rsegs m' 0x30ff0 [C8 (Z_to_bv 64 R)] /\
                  rw_cells rsegs m' R [C4 fd; CB 52 (repeat (Z_to_bv 8 0) 52)] /\
                  rw_cells rsegs m' (R + 56) [CB 840 post]))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 fd (Z_to_bv 64 0x31018) (Z_to_bv 64 R)
             a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 0x30fc0) (Z_to_bv 64 0) (Z_to_bv 64 16)
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1339c) fc None m (seg_rom rsegs)).
Proof.
  intros SPU MSET ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 fd
    F fc m lo R junk jt post FR ST LO HI FD MI GL WK NS GS R0 TE TQ D1 D2 D3.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (0x3101c, 0x31020); (0x30fd8, 0x30fe0);
                (0x30ff0, 0x30ff8); (R, R + 56)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct (ra_cut _ _ [_] [_; _] GL) as [GL0 GL12]. clear GL.
  destruct (ra_cut _ _ [_] [_] GL12) as [L16 GL2]. clear GL12.
  assert (UR : bv_unsigned (Z_to_bv 64 R) = R) by (apply unsigned_lit; lia).
  step. if_cases K; [exfalso; zify_cond K; rewrite ?UR in K; lia | ].
  step; fold_sx; step; step.
  do 8 step.
  call_rw (MSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ jt);
    [ rewrite ?unsigned_lit by lia; exact TE | assumption | ].
  do 5 step.
  call_rw (SPU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 200728 lo);
    [ reflexivity
    | exact (ra_join _ _ _ [_] [_; _] GL0 (ra_join _ _ _ [_] [_] L16 GL2 eq_refl) eq_refl)
    | rewrite ?unsigned_lit by lia; eassumption
    | rewrite ?unsigned_lit by lia; lia
    | rewrite ?unsigned_lit by lia; lia
    | assumption
    | ].
  match goal with
  | H : bytes_at rsegs ?mm 134468 _ |- _ =>
      assert (RD : ov_read_bytes rsegs mm (wa 134468) 4 = Some (le4 (Z_to_bv 64 (-1))));
      [ replace (wa 134468) with (wa (134468 + 0)) by reflexivity;
        rewrite (bytes_at_read rsegs mm 134468 (le4 (Z_to_bv 64 (-1))) 0 4 H ltac:(lia)) by (rewrite length_le4; lia);
        reflexivity
      | ]
  end.
  step; step; fold_sx; step.
  change (le1 (Z_to_bv 64 0)) with (le1 (zxb (Z_to_bv 8 0))); mem_after_store.
  step; if_true.
  do 11 step.
  apply evt_done; unfold ra_ret; do 15 eexists; split; [reflexivity|].
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|].
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|].
  split; [eassumption|]; eassumption.
Qed.
