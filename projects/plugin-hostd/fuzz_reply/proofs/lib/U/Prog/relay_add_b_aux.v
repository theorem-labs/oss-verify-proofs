From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import
  pthread_mutex_lock_c pthread_mutex_unlock_c memset_c wake_c.
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

Lemma rw_cells_nil : forall m A, 0 <= A <= 2 ^ 64 -> rw_cells rsegs m A [CB 0 []].
Proof.
  intros m A H. split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes app]. apply bytes_at_nil. lia.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
Qed.

Ltac fold_sx :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?z)] => is_Zlit z;
      let v := eval vm_compute in (bv_unsigned (sx32 (Z_to_bv 64 z))) in
      replace (sx32 (Z_to_bv 64 z)) with (Z_to_bv 64 v) by (vm_compute; reflexivity)
  end.

Ltac fold_tonat :=
  repeat match goal with
  | H : context [Z.to_nat ?x] |- _ => is_Zlit x;
      let v := eval vm_compute in (Z.to_nat x) in progress change (Z.to_nat x) with v in H
  | |- context [Z.to_nat ?x] => is_Zlit x;
      let v := eval vm_compute in (Z.to_nat x) in progress change (Z.to_nat x) with v
  end.

Ltac cmp_val :=
  repeat match goal with
  | |- context [v_slti (Z_to_bv 64 ?x) ?i] => is_Zlit x; is_Zlit i;
      let v := eval vm_compute in (bv_unsigned (v_slti (Z_to_bv 64 x) i)) in
      replace (v_slti (Z_to_bv 64 x) i) with (Z_to_bv 64 v) by (vm_compute; reflexivity)
  | |- context [v_sltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] =>
      first
        [ replace (v_sltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with (Z_to_bv 64 1)
            by (unfold v_sltu, c_ltu, bv_ltu; rewrite !unsigned_lit by lia;
                replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity)
        | replace (v_sltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with (Z_to_bv 64 0)
            by (unfold v_sltu, c_ltu, bv_ltu; rewrite !unsigned_lit by lia;
                replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity) ]
  | |- context [v_sltiu (Z_to_bv 64 ?x) 1] =>
      first
        [ replace (v_sltiu (Z_to_bv 64 x) 1) with (Z_to_bv 64 1)
            by (unfold v_sltiu; rewrite unsigned_lit by lia; change (bv_wrap 64 1) with 1;
                replace (x <? 1) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity)
        | replace (v_sltiu (Z_to_bv 64 x) 1) with (Z_to_bv 64 0)
            by (unfold v_sltiu; rewrite unsigned_lit by lia; change (bv_wrap 64 1) with 1;
                replace (x <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity) ]
  end.

Ltac land_val :=
  repeat match goal with
  | |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 7] =>
      replace (Z.land (bv_unsigned (Z_to_bv 64 x)) 7) with 0
        by (rewrite unsigned_lit by lia; change 7 with (Z.ones 3); rewrite Z.land_ones by lia;
            Z.div_mod_to_equations; lia)
  end.

Ltac comm_base G :=
  repeat match goal with
  | |- context [Z_to_bv 64 (0 + G)] => replace (0 + G) with G by lia
  | |- context [Z_to_bv 64 (?c + G)] => is_Zlit c; replace (c + G) with (G + c) by lia
  end.

Ltac if_f :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false; [cbv iota | symmetry; unfold_cond; rewrite ?unsigned_lit by lia; fold_lit_ux; solve_cond_rec]
  end.

Definition ra_ret (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (v : word) (W : list (Z * Z)) (m : word -> option byte) (P : (word -> option byte) -> Prop) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch W m m' /\ wmono rsegs m m' /\ P m'.

Lemma ra_neg : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 64 <= bv_unsigned sp -> bv_signed a0 < 0 ->
  evt rsegs (ra_ret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 (-1))
               [(bv_unsigned sp - 64, bv_unsigned sp)] m (fun _ => True))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13504) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ST LO NEG.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  carve_frame 64%nat ST.
  do 11 step. if_true.
  do 11 step.
  apply evt_done. unfold ra_ret. do 15 eexists.
  split; [reflexivity|]. split; [eassumption|]. split; [eassumption|exact I].
Qed.

Tactic Notation "call_rw" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply SPEC
      | let ms' := fresh "ms'" in let PO := fresh "PO" in
        intros ms' PO;
        unfold memset_post, pthread_mutex_unlock_post, pthread_mutex_lock_post in PO;
        try unfold WAKE_FRAME, wake_c.G_WAKE1 in PO;
        rewrite ?unsigned_lit in PO by lia;
        try change (Z.to_nat 56) with 56%nat in PO;
        try change (0 mod 256) with 0 in PO;
        revert ms' PO; post_call segs mm ]
  end.

Ltac wake_call WK lo :=
  call_rw (WK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo);
    [ unfold WAKE_FRAME; rewrite ?unsigned_lit by lia; eassumption
    | unfold WAKE_FRAME; rewrite ?unsigned_lit by lia; lia
    | unfold wake_c.G_WAKE1; eassumption
    | unfold wake_c.G_WAKE1, WAKE_FRAME; rewrite ?unsigned_lit by lia; lia
    | ].

Lemma ra_c16 : pthread_mutex_lock_contract -> pthread_mutex_unlock_contract -> memset_contract -> wake_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo N G : Z) (pre junk post : list byte),
  stk rsegs m lo (bv_unsigned sp) -> lo + 160 <= bv_unsigned sp -> 0x100000 <= lo ->
  0 <= bv_signed a0 -> mem_inv rsegs m ->
  rw_cells rsegs m 0x318f8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  bytes_at rsegs m 0x2162c (le4 (Z_to_bv 64 (-1))) ->
  rw_cells rsegs m 0x318b8 [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 16)] ->
  rw_cells rsegs m 0x318d0 [C8 (Z_to_bv 64 G)] ->
  0 <= N < 4 -> 0 < G -> G mod 8 = 0 ->
  rw_cells rsegs m G [CB (Z.to_nat (56 * N)) pre] ->
  rw_cells rsegs m (G + 56 * N) [CB 56 junk] ->
  rw_cells rsegs m (G + 56 * N + 56) [CB (Z.to_nat (840 - 56 * N)) post] ->
  (G + 896 <= 0x2162c \/ 0x21630 <= G) ->
  (G + 896 <= 0x318a0 \/ 0x31920 <= G) ->
  G + 896 <= lo ->
  evt rsegs (ra_ret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 0)
               [(bv_unsigned sp - 160, bv_unsigned sp); (0x318fc, 0x31900); (0x318b8, 0x318bc);
                (G + 56 * N, G + 56 * N + 56)] m
               (fun m' => rw_cells rsegs m' 0x318f8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
                  bytes_at rsegs m' 0x2162c (le4 (Z_to_bv 64 (-1))) /\
                  rw_cells rsegs m' 0x318b8 [C4 (Z_to_bv 64 (N + 1)); C4 (Z_to_bv 64 16)] /\
                  rw_cells rsegs m' 0x318d0 [C8 (Z_to_bv 64 G)] /\
                  rw_cells rsegs m' G [CB (Z.to_nat (56 * N)) pre] /\
                  rw_cells rsegs m' (G + 56 * N) [C4 a0; CB 52 (repeat (Z_to_bv 8 0) 52)] /\
                  rw_cells rsegs m' (G + 56 * N + 56) [CB (Z.to_nat (840 - 56 * N)) post]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13504) fc None m (seg_rom rsegs)).
Proof.
  intros SPL SPU MSET WAKEC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo N G pre junk post ST LO HI FD MI GL WK NS GS NR G0 GA TP TE TQ D1 D2 D3.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (0x318fc, 0x31900); (0x318b8, 0x318bc);
                (G + 56 * N, G + 56 * N + 56)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct (ra_cut _ _ [_] [_; _] GL) as [GL0 GL12]. clear GL.
  destruct (ra_cut _ _ [_] [_] GL12) as [GL1 GL2]. clear GL12.
  assert (TB : bytes_at rsegs m 0x318f8 [hd (Z_to_bv 8 0) (le4 (Z_to_bv 64 0))]).
  { pose proof (proj2 (proj1 GL0)) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    rewrite <- (firstn_skipn 1 (le4 (Z_to_bv 64 0))) in B. exact (ra_pre _ _ _ _ B). }
  carve_frame 64%nat ST.
  do 11 step. if_false.
  do 6 step.
  call (SPL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            0x318f8 (hd (Z_to_bv 8 0) (le4 (Z_to_bv 64 0)))).
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
  all: step; fold_sx; step; fold_sx; step; if_true.
  all: step; step.
  all: do 4 step; comm_base G.
  all: step; cmp_val; step; cmp_val; step; if_false.
  all: step; cmp_val; step; cmp_val; step; step; step; if_false.
  all: do 4 step.
  all: call_rw (MSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ junk);
    [ rewrite ?unsigned_lit by lia; exact TE | assumption | ].
  all: step; step; if_false.
  all: step; step; if_f.
  all: step; land_val; step; if_false.
  all: do 3 step.
  all: call_rw (SPU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0x318f8 lo);
    [ reflexivity
    | exact (ra_join _ _ _ [_] [_; _] GL0 (ra_join _ _ _ [_] [_] L16 GL2 eq_refl) eq_refl)
    | rewrite ?unsigned_lit by lia; eassumption
    | rewrite ?unsigned_lit by lia; lia
    | rewrite ?unsigned_lit by lia; lia
    | assumption
    | ].
  all: step.
  all: wake_call WAKEC lo.
  all: do 12 step.
  all: apply evt_done; unfold ra_ret; do 15 eexists; split; [reflexivity|].
  all: split; [eassumption|]; split; [eassumption|].
  all: split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|].
  all: split; [first [eassumption | apply rw_cells_nil; lia]|]; split; [eassumption|]; eassumption.
Qed.

Definition ra_g1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (fd : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x1358c) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 fd (Z_to_bv 64 0x318f8)
                  (Z_to_bv 64 0) (Z_to_bv 64 896) a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 (-1)) s3 (Z_to_bv 64 0x318a0) (Z_to_bv 64 0) (Z_to_bv 64 16) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x178f8) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (0x318fc, 0x31900)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk rsegs m' lo (bv_unsigned sp + -64)
    /\ rw_cells rsegs m' 0x318f8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)]
    /\ bytes_at rsegs m' 0x2162c (le4 (Z_to_bv 64 (-1)))
    /\ rw_cells rsegs m' 0x318b8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells rsegs m' 0x318d0 [C8 (Z_to_bv 64 0)].

Lemma ra_g1 : pthread_mutex_lock_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 160 <= bv_unsigned sp -> 0x100000 <= lo ->
  0 <= bv_signed a0 -> mem_inv rsegs m ->
  rw_cells rsegs m 0x318f8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  bytes_at rsegs m 0x2162c (le4 (Z_to_bv 64 (-1))) ->
  rw_cells rsegs m 0x318b8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m 0x318d0 [C8 (Z_to_bv 64 0)] ->
  evt rsegs (ra_g1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13504) fc None m (seg_rom rsegs)).
Proof.
  intros SPL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO HI FD MI GL WK NS GS.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (0x318fc, 0x31900)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct (ra_cut _ _ [_] [_; _] GL) as [GL0 GL12]. clear GL.
  destruct (ra_cut _ _ [_] [_] GL12) as [GL1 GL2]. clear GL12.
  assert (TB : bytes_at rsegs m 0x318f8 [hd (Z_to_bv 8 0) (le4 (Z_to_bv 64 0))]).
  { pose proof (proj2 (proj1 GL0)) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    rewrite <- (firstn_skipn 1 (le4 (Z_to_bv 64 0))) in B. exact (ra_pre _ _ _ _ B). }
  carve_frame 64%nat ST.
  do 11 step. if_false.
  do 6 step.
  call (SPL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            0x318f8 (hd (Z_to_bv 8 0) (le4 (Z_to_bv 64 0)))).
  1: reflexivity.
  1: exact TB.
  1: reflexivity.
  1: exact GL1.
  1: assumption.
  cbv delta [mkR].
  match goal with H : rw_cells _ _ _ [C4 (Z_to_bv 64 16)] |- _ => rename H into L16 end.
  step; fold_sx; step; fold_sx; step; if_false.
  step; if_true.
  do 6 step.
  apply evt_done. unfold ra_g1_post. cbv beta delta [mkR].
  do 14 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [eassumption|].
  split; [exact (ra_join _ _ _ [_] [_; _] GL0 (ra_join _ _ _ [_] [_] L16 GL2 eq_refl) eq_refl)|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma ra_g2 : pthread_mutex_unlock_contract -> memset_contract -> wake_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 fd
    (F : bvmap 5 word) fc (m : word -> option byte) (lo R : Z) (jt post : list byte),
  rw_cells rsegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (bv_unsigned sp + -64) -> lo + 160 <= bv_unsigned sp -> 0x100000 <= lo ->
  0 <= bv_signed fd -> mem_inv rsegs m ->
  rw_cells rsegs m 0x318f8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)] ->
  bytes_at rsegs m 0x2162c (le4 (Z_to_bv 64 (-1))) ->
  rw_cells rsegs m 0x318b8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m 0x318d0 [C8 (Z_to_bv 64 0)] ->
  0 < R -> R mod 8 = 0 ->
  rw_cells rsegs m R [CB 56 jt] ->
  rw_cells rsegs m (R + 56) [CB 840 post] ->
  (R + 896 <= 0x2162c \/ 0x21630 <= R) ->
  (R + 896 <= 0x318a0 \/ 0x31920 <= R) ->
  R + 896 <= lo ->
  evt rsegs (ra_ret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 0)
               [(bv_unsigned sp - 160, bv_unsigned sp); (0x318fc, 0x31900); (0x318b8, 0x318c0); (0x318d0, 0x318d8);
                (R, R + 56)] m
               (fun m' => rw_cells rsegs m' 0x318f8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
                  bytes_at rsegs m' 0x2162c (le4 (Z_to_bv 64 (-1))) /\
                  rw_cells rsegs m' 0x318b8 [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 16)] /\
                  rw_cells rsegs m' 0x318d0 [C8 (Z_to_bv 64 R)] /\
                  rw_cells rsegs m' R [C4 fd; CB 52 (repeat (Z_to_bv 8 0) 52)] /\
                  rw_cells rsegs m' (R + 56) [CB 840 post]))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 fd (Z_to_bv 64 0x318f8) (Z_to_bv 64 R)
             a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 (Z_to_bv 64 0x318a0) (Z_to_bv 64 0) (Z_to_bv 64 16)
             s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1358c) fc None m (seg_rom rsegs)).
Proof.
  intros SPU MSET WAKEC ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    x1 fd F fc m lo R jt post FR ST LO HI FD MI GL WK NS GS R0 RA TE TQ D1 D2 D3.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (0x318fc, 0x31900); (0x318b8, 0x318c0);
                (0x318d0, 0x318d8); (R, R + 56)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct (ra_cut _ _ [_] [_; _] GL) as [GL0 GL12]. clear GL.
  destruct (ra_cut _ _ [_] [_] GL12) as [L16 GL2]. clear GL12.
  assert (UR : bv_unsigned (Z_to_bv 64 R) = R) by (apply unsigned_lit; lia).
  step. if_cases K; [exfalso; zify_cond K; rewrite ?UR in K; lia | clear K].
  step; step; fold_sx.
  step; step.
  do 4 step; comm_base R.
  step; cmp_val; step; cmp_val; step; if_false.
  step; cmp_val; step; cmp_val; step; step; step; if_false.
  do 4 step.
  call_rw (MSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ jt);
    [ rewrite ?unsigned_lit by lia; exact TE | assumption | ].
  step; step; if_false.
  step; step; if_f.
  step; land_val; step; if_false.
  do 3 step.
  call_rw (SPU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0x318f8 lo);
    [ reflexivity
    | exact (ra_join _ _ _ [_] [_; _] GL0 (ra_join _ _ _ [_] [_] L16 GL2 eq_refl) eq_refl)
    | rewrite ?unsigned_lit by lia; eassumption
    | rewrite ?unsigned_lit by lia; lia
    | rewrite ?unsigned_lit by lia; lia
    | assumption
    | ].
  step.
  wake_call WAKEC lo.
  do 12 step.
  apply evt_done; unfold ra_ret; do 15 eexists; split; [reflexivity|].
  split; [eassumption|]; split; [eassumption|].
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|].
  split; [eassumption|]; eassumption.
Qed.
