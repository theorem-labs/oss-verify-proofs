From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes FP Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import pthread_mutex_lock_c pthread_mutex_unlock_c
  strlen_c strncmp_c snprintf_c printf_facts_c send_line_c relay_event_c gesture_end_c RelayModel RelayKeys.
Import ListNotations.
Open Scope Z_scope.

Definition RIG_FMT : Z := 0x102a2.
Definition RIG_KEY : Z := 0x103e6.
Definition RIG_S6 : Z := 0x30fc0.
Definition RIG_GSRC : Z := 0x30ff0.
Definition RIG_NSRC : Z := 0x30fd8.
Definition RIG_FREE : Z := 0x15664.
Definition RIG_DRAIN : Z := 0x135d0.

Lemma rigc_cut : forall m A B cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m B cs2.
Proof.
  intros m A B cs1 cs2 [[W Bs] (H0 & H1 & H)] ->.
  apply cells_wf_app in W. destruct W as [W1 W2].
  rewrite cells_bytes_app in Bs. apply bytes_at_app in Bs. destruct Bs as [B1 B2].
  rewrite (cells_bytes_length cs1 W1) in B2. rewrite cells_size_app in H1, H.
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply H. lia.
Qed.

Lemma rigc_join : forall m A B cs1 cs2, rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 ->
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

Lemma rigc_bytes_pre : forall m A (s t : list byte), bytes_at rsegs m A (s ++ t) -> bytes_at rsegs m A s.
Proof. intros m A s t H. apply bytes_at_app in H. exact (proj1 H). Qed.

Lemma rigc_sx32_small : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma rigc_lts_small : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed. rewrite !unsigned_lit by lia.
  destruct (x <? 2 ^ 63) eqn:E1; [|apply Z.ltb_ge in E1; lia].
  destruct (y <? 2 ^ 63) eqn:E2; [|apply Z.ltb_ge in E2; lia].
  reflexivity.
Qed.

Definition rig_pre (id : Z) : list Z := K_GESTURE ++ [32] ++ pf_dec id ++ [32].

Definition rig_postA (ra sp gp tp a0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (N : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms => exists x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31
                   (m' : word -> option byte),
    ms = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - 160)) gp tp x5 x6 x7 a0 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 (Z_to_bv 64 RIG_S6) x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 (if N =? 0 then 0x13590 else 0x134bc)) fc None m' (seg_rom rsegs) /\
    (N <> 0 -> x18 = Z_to_bv 64 RIG_FMT /\ x19 = Z_to_bv 64 RIG_KEY /\ x23 = Z_to_bv 64 0) /\
    munch [(bv_unsigned sp - 160, bv_unsigned sp); (G_LOCK + 4, G_LOCK + 8)] m m' /\ wmono rsegs m m' /\
    mem_inv rsegs m' /\
    rw_cells rsegs m' (bv_unsigned sp - 160) [C8 (Z_to_bv 64 G_LOCK)] /\
    rw_cells rsegs m' (bv_unsigned sp - 104)
      [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    rw_cells rsegs m' G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)].

Lemma rig_segA : pthread_mutex_lock_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo N : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 160 <= bv_unsigned sp -> G_LOCK_HI <= lo ->
  mem_inv rsegs m ->
  rw_cells rsegs m G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m RIG_NSRC [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 16)] -> 0 <= N <= 4 ->
  evt rsegs (rig_postA ra sp gp tp a0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc N m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13450) fc None m (seg_rom rsegs)).
Proof.
  intros SPL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo N ST LO LOG MI GL NS NB.
  unfold G_LOCK_HI in LOG. unfold RIG_NSRC in NS. unfold G_LOCK in GL.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  destruct (rigc_cut _ _ (200728 + 4) [_] [_; _] GL eq_refl) as [GL0 GL12]. clear GL.
  destruct (rigc_cut _ _ (200728 + 4 + 4) [_] [_] GL12 eq_refl) as [GL1 GL2]. clear GL12.
  assert (TB : bytes_at rsegs m 200728 [hd (Z_to_bv 8 0) (le4 (Z_to_bv 64 0))]).
  { pose proof (proj2 (proj1 GL0)) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    rewrite <- (firstn_skipn 1 (le4 (Z_to_bv 64 0))) in B. exact (rigc_bytes_pre _ _ _ _ B). }
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (200732, 200736)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 160%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 160%nat junk [] [8; 48; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR;
    [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step.
  step.
  call (SPL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            200728 (hd (Z_to_bv 8 0) (le4 (Z_to_bv 64 0)))).
  1: reflexivity.
  1: exact TB.
  1: reflexivity.
  1: exact GL1.
  1: assumption.
  cbv delta [mkR].
  match goal with H : rw_cells _ _ _ [C4 (Z_to_bv 64 16)] |- _ => rename H into L16 end.
  step.
  rewrite (rigc_sx32_small N) by lia.
  step.
  rewrite (rigc_lts_small 0 N) by lia.
  destruct (rigc_cut _ _ (bv_unsigned sp - 152) [_] _ FR ltac:(cbn [cells_size csize]; lia)) as [F0 FR1].
  destruct (rigc_cut _ _ (bv_unsigned sp - 104) [_] _ FR1 ltac:(cbn [cells_size csize]; lia)) as [F1 F2].
  clear FR FR1 F1.
  pose proof (rigc_join _ _ _ [_] [_] L16 GL2 eq_refl) as GL12.
  pose proof (rigc_join _ _ _ [_] [_; _] GL0 GL12 eq_refl) as GLF.
  clear GL0 GL2 GL12 L16.
  destruct (0 <? N) eqn:HC; cbn [negb]; cbv iota.
  - apply Z.ltb_lt in HC. step. step. step. step. step.
    apply evt_done. unfold rig_postA. rewrite (proj2 (Z.eqb_neq N 0)) by lia.
    do 27 eexists. split; [reflexivity|].
    split; [intros _; split; [reflexivity|]; split; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [exact F0|]. split; [exact F2|]. exact GLF.
  - apply Z.ltb_ge in HC. assert (N = 0) by lia. subst N.
    apply evt_done. unfold rig_postA.
    do 27 eexists. split; [reflexivity|].
    split; [intros H0; exfalso; apply H0; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [exact F0|]. split; [exact F2|]. exact GLF.
Qed.

Lemma rig_sx32_small : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma rig_lts : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed, !unsigned_lit by lia.
  replace (x <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (y <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma rig_shl3 : forall z, 0 <= z < 2 ^ 60 -> Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 3) = Z_to_bv 64 (8 * z).
Proof. intros z Hz. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal. change (2 ^ 3) with 8. ring. Qed.

Lemma rig_shl6 : forall z, 0 <= z < 2 ^ 57 -> Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 6) = Z_to_bv 64 (64 * z).
Proof. intros z Hz. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal. change (2 ^ 6) with 64. ring. Qed.

Lemma rig_addiw : forall z, 1 <= z < 2 ^ 31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + -1)) = Z_to_bv 64 (z - 1).
Proof.
  intros z Hz. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma rig_eqb0 : forall v, - 2 ^ 63 <= v < 2 ^ 63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec v 0) as [->|Hn]; [reflexivity|].
  apply Z.eqb_neq. rewrite (Z.mod_small 0) by lia. intros E.
  pose proof (Z.div_mod v (2 ^ 64) ltac:(lia)) as D. rewrite E in D. lia.
Qed.

Lemma rig_rd8 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (Z_to_bv 64 a) 8 = Some (le8 v).
Proof.
  intros m a v H.
  assert (L : (0 + 8 <= length (le8 v))%nat) by (rewrite length_le8; lia).
  pose proof (bytes_at_ov_read rsegs m a (le8 v) 0 8 H L) as R.
  pose proof (length_le8 v) as L8.
  assert (E : firstn 8 (skipn 0 (le8 v)) = le8 v) by (apply firstn_all2; cbn [skipn]; lia).
  rewrite E in R. unfold wa in R. cbn [Z.of_nat] in R. rewrite Z.add_0_r in R. exact R.
Qed.

Lemma rig_segB : forall x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P G i fd eof : Z),
  rw_cells rsegs m RIG_GSRC [C8 (Z_to_bv 64 G)] ->
  rw_cells rsegs m (G + 56 * i) [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 eof)] ->
  0 <= i < 16 -> (eof = 0 \/ eof = 1) -> 0 <= P < 2 ^ 64 ->
  evt rsegs (fun ms => exists x10' x12',
      (eof = 0 /\
       ms = MS (mkR (Z_to_bv 64 0x134dc) (Z_to_bv 64 P) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (G + 56 * i)) (Z_to_bv 64 G) x12'
                    x13 x14 x15 x16 x17 (Z_to_bv 64 RIG_FMT) (Z_to_bv 64 RIG_KEY) x20 x21 (Z_to_bv 64 RIG_S6) (Z_to_bv 64 i)
                    (Z_to_bv 64 (56 * i)) x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 RIG_DRAIN) fc None m (seg_rom rsegs)) \/
      (eof = 1 /\
       ms = MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 x8 x9 x10' (Z_to_bv 64 G) x12'
                    x13 x14 x15 x16 x17 (Z_to_bv 64 RIG_FMT) (Z_to_bv 64 RIG_KEY) x20 x21 (Z_to_bv 64 RIG_S6) (Z_to_bv 64 i)
                    (Z_to_bv 64 (56 * i)) x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x134e0) fc None m (seg_rom rsegs)))
    (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 RIG_FMT) (Z_to_bv 64 RIG_KEY) x20 x21 (Z_to_bv 64 RIG_S6) (Z_to_bv 64 i) x24 x25 x26 x27
             x28 x29 x30 x31)
        F (Z_to_bv 64 0x134bc) fc None m (seg_rom rsegs)).
Proof.
  intros x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m P G i fd eof HG HE HI HEOF HP.
  unfold RIG_S6, RIG_GSRC in *.
  pose proof (rw_cells_bound _ _ _ _ HE) as EB. cbn [cells_size csize] in EB.
  step.
  step. rewrite (rig_shl3 i) by lia.
  step. rewrite (rig_shl6 i) by lia.
  step. rewrite (unsigned_lit (64 * i)), (unsigned_lit (8 * i)) by lia.
  replace (64 * i - 8 * i) with (56 * i) by lia.
  step.
  step. rewrite (rig_sx32_small eof) by lia.
  step.
  destruct HEOF as [-> | ->].
  - if_false. step. apply evt_done. exists (Z_to_bv 64 0), (Z_to_bv 64 0). left. split; reflexivity.
  - if_true. apply evt_done. exists (Z_to_bv 64 (G + 56 * i)), (Z_to_bv 64 1). right. split; reflexivity.
Qed.

Lemma rig_segB2 : forall x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (G : Z),
  rw_cells rsegs m RIG_GSRC [C8 (Z_to_bv 64 G)] ->
  evt rsegs (fun ms =>
      ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 G) x12 x13 x14 x15 x16 x17
                   x18 x19 x20 x21 (Z_to_bv 64 RIG_S6) x23 x24 x25 x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x134e0) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 (Z_to_bv 64 RIG_S6) x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x134dc) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m G HG.
  unfold RIG_S6, RIG_GSRC in *.
  step. apply evt_done. reflexivity.
Qed.

Lemma rigc_lit_at : forall m A bs,
  mem_inv rsegs m -> ro_bytes_b rsegs A bs = true -> 0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  bytes_at rsegs m A bs.
Proof.
  intros m A bs HI Hb HA Hl.
  destruct (ro_cells_image rsegs m A bs HI Hb HA Hl) as [_ H].
  cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.

Lemma rigc_img_free : forall D n, 2 ^ 21 <= D -> pf_img_free D n.
Proof.
  intros D n HD i Hi s Hs.
  match type of Hs with In _ ?L =>
    assert (H : forallb (fun s => bv_unsigned (fst s) + bv_unsigned (snd s) <=? 2 ^ 21) L = true)
      by (vm_compute; reflexivity) end.
  rewrite forallb_forall in H. specialize (H s Hs). apply Z.leb_le in H. lia.
Qed.

Lemma rigc_signed_mod : forall x : word, bv_unsigned x mod 2 ^ 32 = bv_signed x mod 2 ^ 32.
Proof.
  intros x. rewrite zb_signed. destruct (_ <? _); [reflexivity|].
  replace (bv_unsigned x - 2 ^ 64) with (bv_unsigned x + (- 2 ^ 32) * 2 ^ 32) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma rigc_digits_len : forall f x acc, (length (pf_digits f x acc) <= f + length acc)%nat.
Proof.
  induction f as [|f IH]; intros x acc; cbn [pf_digits]; [lia|].
  destruct (x <? 10); cbn [length]; [lia|].
  specialize (IH (x / 10) ((48 + x mod 10) :: acc)). cbn [length] in IH. lia.
Qed.

Lemma rigc_dec_len : forall c, (length (pf_dec c) <= 12)%nat.
Proof.
  intros c. unfold pf_dec. destruct (c <? 0); cbn [length].
  - pose proof (rigc_digits_len 11 (- c) []) as H. cbn [length] in H. lia.
  - pose proof (rigc_digits_len 11 c []) as H. cbn [length] in H. lia.
Qed.

Lemma rigc_digits_range : forall f x acc, 0 <= x -> Forall (fun c => 0 < c < 256) acc ->
  Forall (fun c => 0 < c < 256) (pf_digits f x acc).
Proof.
  induction f as [|f IH]; intros x acc Hx Hacc; cbn [pf_digits]; [exact Hacc|].
  destruct (x <? 10) eqn:E.
  - apply Z.ltb_lt in E. constructor; [cbv beta; lia|exact Hacc].
  - apply Z.ltb_ge in E. apply IH; [apply Z.div_pos; lia|].
    pose proof (Z.mod_pos_bound x 10 ltac:(lia)). constructor; [cbv beta; lia|exact Hacc].
Qed.

Lemma rigc_pre_nz : forall v, Forall (fun c => 0 < c < 256) (rig_pre v).
Proof.
  intros v. unfold rig_pre, K_GESTURE. cbn [app].
  repeat (apply Forall_cons; [cbv beta; lia|]).
  apply Forall_app. split; [|apply Forall_cons; [cbv beta; lia|apply Forall_nil]].
  unfold pf_dec. destruct (v <? 0) eqn:E.
  - apply Z.ltb_lt in E. constructor; [cbv beta; lia|]. apply rigc_digits_range; [lia|constructor].
  - apply Z.ltb_ge in E. apply rigc_digits_range; [lia|constructor].
Qed.

Lemma rigc_nz_bytes : forall T, Forall (fun c => 0 < c < 256) T -> ~ In (Z_to_bv 8 0) (pf_bytes T).
Proof.
  intros T H Hin. unfold pf_bytes in Hin. apply in_map_iff in Hin. destruct Hin as (c & Hc & Hin).
  rewrite Forall_forall in H. specialize (H c Hin). cbv beta in H.
  apply (f_equal bv_unsigned) in Hc. rewrite !Z_to_bv_unsigned in Hc. unfold bv_wrap in Hc.
  change (bv_modulus 8) with 256 in Hc. rewrite (Z.mod_small c 256) in Hc by lia.
  change (0 mod 256) with 0 in Hc. lia.
Qed.

Lemma rigc_cb_after : forall W m m' A n (junk bs : list byte),
  rw_cells rsegs m A [CB n junk] -> munch W m m' -> wmono rsegs m m' ->
  bytes_at rsegs m' A bs -> (length bs <= n)%nat ->
  disjoint_from W (A + Z.of_nat (length bs)) (Z.of_nat n - Z.of_nat (length bs)) ->
  rw_cells rsegs m' A [CB n (bs ++ skipn (length bs) junk)].
Proof.
  intros W m m' A n junk bs [[Wf Bj] Wr] MU WM Hb Hl Hd.
  destruct Wf as [Wf _]. cbn [cell_wf] in Wf.
  cbn [cells_bytes cbytes] in Bj. rewrite app_nil_r in Bj.
  rewrite <- (firstn_skipn (length bs) junk) in Bj. apply bytes_at_app in Bj. destruct Bj as [_ B2].
  rewrite firstn_length_le in B2 by lia.
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [|exact I]. rewrite length_app, length_skipn. lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact Hb|].
    eapply bytes_at_transport; [exact B2 | exact MU |].
    rewrite length_skipn. replace (Z.of_nat (length junk - length bs)) with (Z.of_nat n - Z.of_nat (length bs)) by lia.
    exact Hd.
  - eapply wr_at_transport; [|exact WM]. cbn [cells_size csize] in Wr |- *. exact Wr.
Qed.

Lemma rigc_cb_bytes : forall m A n T rest, rw_cells rsegs m A [CB n (pf_bytes (T ++ [0]) ++ rest)] ->
  bytes_at rsegs m A (pf_bytes T ++ Z_to_bv 8 0 :: rest).
Proof.
  intros m A n T rest [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  unfold pf_bytes in *. rewrite map_app, <- app_assoc in B. exact B.
Qed.

Lemma rigc_hk_tr : forall W m m' (nh hp k0 lo : Z),
  (0 < nh -> 0 <= hp /\ hp + 8 <= lo /\ bytes_at rsegs m hp (le8 (Z_to_bv 64 k0))) -> munch W m m' ->
  (forall a, a + 8 <= lo -> disjoint_from W a 8) ->
  0 < nh -> 0 <= hp /\ hp + 8 <= lo /\ bytes_at rsegs m' hp (le8 (Z_to_bv 64 k0)).
Proof.
  intros W m m' nh hp k0 lo H MU D NZ. destruct (H NZ) as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
  eapply bytes_at_transport; [exact H3 | exact MU |]. rewrite length_le8. change (Z.of_nat 8) with 8. apply D. exact H2.
Qed.

Definition rig_postC (gp tp x8 : word) (P i EA nh hp k0 lo : Z) (T : list Z) (junk : list byte)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms => exists x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x25 x26 x27 x28 x29 x30 x31
                   (Ft : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
    ms = MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 RIG_FMT) (Z_to_bv 64 RIG_KEY) x20 x21 (Z_to_bv 64 RIG_S6) (Z_to_bv 64 i)
                 (Z_to_bv 64 EA) x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 (if nh =? 0 then 0x13584 else 0x13524)) fc' None m' (seg_rom rsegs) /\
    frm0 fc' /\
    (nh <> 0 -> x9 = Z_to_bv 64 0 /\ x20 = Z_to_bv 64 (Z.of_nat (length T)) /\ x21 = Z_to_bv 64 k0 /\
                x25 = Z_to_bv 64 0 /\ x26 = Z_to_bv 64 nh /\ x27 = Z_to_bv 64 hp) /\
    munch [(lo, P); (P + 8, P + 56)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    rw_cells rsegs m' (P + 8) [CB 48 (pf_bytes (T ++ [0]) ++ skipn (length T + 1) junk)].

Lemma rig_segC : snprintf_contract -> strlen_contract ->
  forall x1 gp tp x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x20 x21 x25 x26 x27 x28 x29 x30 x31
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P lo G i nh hp k0 : Z) (junk : list byte) (canary : word),
  let EA := G + 56 * i in
  let ID := bv_signed x8 in
  stk rsegs m lo P -> lo + SNPRINTF_K <= P -> IMG_END <= lo -> 2 ^ 21 <= lo -> P < 2 ^ 63 ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
  rw_cells rsegs m (P + 8) [CB 48 junk] ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  - 2 ^ 31 <= ID < 2 ^ 31 ->
  0 <= i < 16 -> 0 <= G -> EA + 56 <= lo ->
  rw_cells rsegs m (EA + 40) [C8 (Z_to_bv 64 hp); C4 (Z_to_bv 64 nh)] -> 0 <= nh < 2 ^ 26 ->
  (0 < nh -> 0 <= hp /\ hp + 8 <= lo /\ bytes_at rsegs m hp (le8 (Z_to_bv 64 k0))) ->
  evt rsegs (rig_postC gp tp x8 P i EA nh hp k0 lo (rig_pre ID) junk m)
    (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 G) x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 RIG_FMT) (Z_to_bv 64 RIG_KEY) x20 x21 (Z_to_bv 64 RIG_S6) (Z_to_bv 64 i) (Z_to_bv 64 (56 * i))
             x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x134e0) fc None m (seg_rom rsegs)).
Proof.
  intros SNP SLEN x1 gp tp x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x20 x21 x25 x26 x27 x28 x29 x30 x31
    F fc m P lo G i nh hp k0 junk canary.
  cbv zeta.
  intros ST LOK IE L21 P63 FRM MI TM CBJ GG GU IDR IR G0 EAL HS NHR HK.
  unfold snprintf_contract in SNP. unfold SNPRINTF_K in LOK. unfold IMG_END in IE.
  unfold RIG_FMT, RIG_KEY.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (rw_cells_bound _ _ _ _ HS) as HSB. cbn [cells_size csize] in HSB.
  assert (JL : length junk = 48%nat) by (destruct CBJ as [[[W _] _] _]; exact W).
  assert (SPv : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
  assert (DPv : bv_unsigned (Z_to_bv 64 (P + 8)) = P + 8) by (apply unsigned_lit; lia).
  pose proof (rigc_lit_at m 66210 (pf_bytes ([37; 115; 32; 37; 100; 32] ++ [0])) MI ltac:(vm_compute; reflexivity)
                ltac:(lia) ltac:(apply Z.leb_le; vm_compute; reflexivity)) as HF.
  pose proof (rigc_lit_at m 66534 (pf_bytes (K_GESTURE ++ [0]) ++ pf_bytes [47; 100; 101; 118]) MI
                ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(apply Z.leb_le; vm_compute; reflexivity)) as HKY.
  remember (rig_pre (bv_signed x8)) as T eqn:ET.
  assert (LT : (length T <= 27)%nat).
  { rewrite ET. unfold rig_pre, K_GESTURE. rewrite !length_app. cbn [length].
    pose proof (rigc_dec_len (bv_signed x8)). lia. }
  step. step. step. step. step. step. step.
  eapply evt_cut.
  { eapply SNP with (lo := lo) (canary := canary) (fmt := [37; 115; 32; 37; 100; 32])
      (ps := [Ps; PLit 32; Pd; PLit 32]) (args := [APtr K_GESTURE; AInt (bv_signed x8)]) (T := T) (junk := junk).
    - rewrite (unsigned_lit 66210) by lia. exact HF.
    - apply Z.leb_le. vm_compute. reflexivity.
    - apply Z.leb_le. vm_compute. reflexivity.
    - reflexivity.
    - rewrite SPv, DPv. cbn [pf_args_ok pf_arg_ok].
      split; [split|split; [|exact I]].
      + unfold K_GESTURE. repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil.
      + exists (pf_bytes [47; 100; 101; 118]).
        rewrite (unsigned_lit 66534) by lia.
        split; [exact HKY|].
        split; [apply Z.leb_le; vm_compute; reflexivity|].
        split; [lia|].
        change (Z.of_nat (length K_GESTURE)) with 13.
        change (Z.of_nat (length (pf_bytes [47; 100; 101; 118]))) with 4.
        split; left; lia.
      + split; [exact IDR|]. apply rigc_signed_mod.
    - rewrite ET. reflexivity.
    - rewrite DPv. exact CBJ.
    - rewrite (unsigned_lit 48) by lia. lia.
    - lia.
    - rewrite DPv. lia.
    - rewrite SPv, DPv. right. lia.
    - rewrite DPv. apply rigc_img_free. lia.
    - rewrite SPv. exact ST.
    - rewrite SPv. unfold SNPRINTF_K. lia.
    - unfold IMG_END. lia.
    - rewrite SPv. lia.
    - exact FRM.
    - exact MI.
    - exact TM.
    - exact GG.
    - exact GU. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m2 &
              E & MU2 & WM2 & MI2 & TM2 & FRM2 & FEQ & ST2 & HT).
  subst ms'. clear FEQ HF HKY GG GU TM2 TM.
  rewrite SPv in MU2, ST2. rewrite DPv in MU2, HT.
  replace (Z.to_nat (bv_unsigned (Z_to_bv 64 48) - 1)) with 47%nat in MU2, HT by reflexivity.
  rewrite firstn_all2 in MU2, HT by lia.
  assert (CB2 : rw_cells rsegs m2 (P + 8) [CB 48 (pf_bytes (T ++ [0]) ++ skipn (length T + 1) junk)]).
  { replace (length T + 1)%nat with (length (pf_bytes (T ++ [0])))
      by (unfold pf_bytes; rewrite length_map, length_app; reflexivity).
    eapply (rigc_cb_after _ m); [exact CBJ | exact MU2 | exact WM2 | exact HT | |].
    - unfold pf_bytes. rewrite length_map, length_app. cbn [length]. lia.
    - unfold pf_bytes. rewrite length_map, length_app. cbn [length disjoint_from].
      split; [lia|split; [lia|exact I]]. }
  assert (HK2 : 0 < nh -> 0 <= hp /\ hp + 8 <= lo /\ bytes_at rsegs m2 hp (le8 (Z_to_bv 64 k0))).
  { apply (rigc_hk_tr _ _ _ _ _ _ _ HK MU2). intros a Ha. cbn [disjoint_from]. split; [lia|split; [lia|exact I]]. }
  assert (MU : munch [(lo, P); (P + 8, P + 56)] m m2).
  { eapply munch_weaken; [|exact MU2]. unfold sub_fp. cbn [outside]. intros x [H1 [H2 _]].
    split; [exact H1|]. split; [lia|exact I]. }
  clear HK HT.
  transport_after_call rsegs m m2 MU2 WM2.
  clear MU2 MI.
  rename WM2 into WM.
  replace (ret_pc (Z_to_bv 64 0x134fc)) with (Z_to_bv 64 0x134fc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  step. step.
  eapply evt_cut.
  { eapply (SLEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              (pf_bytes T) (skipn (length T + 1) junk)).
    - rewrite DPv. exact (rigc_cb_bytes _ _ _ _ _ CB2).
    - apply rigc_nz_bytes. rewrite ET. apply rigc_pre_nz.
    - rewrite DPv. unfold pf_bytes. rewrite length_map, length_skipn, JL.
      pose proof (Z.mod_pos_bound (- (P + 8 + Z.of_nat (length T) + 1)) 8 ltac:(lia)). lia.
    - exact MI2. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3 &
              E & MU3 & WM3 & MI3 & HB3).
  subst ms'. clear HB3.
  assert (HK3 : 0 < nh -> 0 <= hp /\ hp + 8 <= lo /\ bytes_at rsegs m3 hp (le8 (Z_to_bv 64 k0))).
  { apply (rigc_hk_tr _ _ _ _ _ _ _ HK2 MU3). intros a Ha. exact I. }
  clear HK2.
  transport_after_call rsegs m2 m3 MU3 WM3.
  clear MU3 WM3 MI2.
  replace (ret_pc (Z_to_bv 64 0x13504)) with (Z_to_bv 64 0x13504) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  replace (length (pf_bytes T)) with (length T) by (unfold pf_bytes; rewrite length_map; reflexivity).
  step.
  rewrite (rigc_sx32_small nh) by lia.
  step.
  rewrite (rigc_lts_small 0 nh) by lia.
  destruct (0 <? nh) eqn:HC; cbn [negb]; cbv iota.
  - apply Z.ltb_lt in HC. destruct (HK3 HC) as (HP0 & HPL & HPB). clear HK3.
    assert (RK : ro_cells rsegs m3 hp [C8 (Z_to_bv 64 k0)]).
    { split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HPB. }
    clear HPB.
    step. step. step. step. step. step.
    apply evt_done. unfold rig_postC. rewrite (proj2 (Z.eqb_neq nh 0)) by lia.
    do 25 eexists. split; [reflexivity|].
    split; [exact FRM2|].
    split; [intros _; repeat (split; [reflexivity|]); reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact CB2.
  - apply Z.ltb_ge in HC. assert (nh = 0) by lia. subst nh.
    apply evt_done. unfold rig_postC.
    do 25 eexists. split; [reflexivity|].
    split; [exact FRM2|].
    split; [intros H0; exfalso; apply H0; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact CB2.
Qed.

Lemma rig_segD : forall x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (i N : Z),
  rw_cells rsegs m RIG_NSRC [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 16)] -> 0 <= i < N -> N <= 4 ->
  evt rsegs (fun ms =>
      ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 N) x11 x12 x13 x14 x15 x16 x17
                   x18 x19 x20 x21 (Z_to_bv 64 RIG_S6) (Z_to_bv 64 (i + 1)) x24 x25 x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 (if i + 1 <? N then 0x134bc else 0x13590)) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 (Z_to_bv 64 RIG_S6) (Z_to_bv 64 i) x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13584) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m i N HN HI HN4.
  unfold RIG_S6, RIG_NSRC in *.
  step. rewrite (rig_sx32_small N) by lia.
  step.
  step. rewrite (rig_lts (i + 1) N) by lia.
  apply evt_done. destruct (i + 1 <? N); reflexivity.
Qed.

Definition rig_postE (gp tp x8 x18 x19 x22 x23 x24 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
    (P plen n nh hp ka knext : Z) (match_ : bool) (m : word -> option byte) : machine_state -> Prop :=
  fun ms => exists x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (m' : word -> option byte),
    munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    ((match_ = true /\
      ms = MS (mkR (Z_to_bv 64 0x13540) (Z_to_bv 64 P) gp tp x5 x6 x7 x8 (Z_to_bv 64 n) (Z_to_bv 64 ka) x11 x12 x13
                   x14 x15 x16 x17 x18 x19 (Z_to_bv 64 plen) (Z_to_bv 64 ka) x22 x23 x24 (Z_to_bv 64 (8 * n))
                   x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 GESTURE_END) fc None m' (seg_rom rsegs)) \/
     (match_ = false /\ n + 1 < nh /\
      ms = MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 x8 (Z_to_bv 64 (n + 1)) x10 x11 x12 x13
                   x14 x15 x16 x17 x18 x19 (Z_to_bv 64 plen) (Z_to_bv 64 knext) x22 x23 x24 (Z_to_bv 64 (8 * (n + 1)))
                   x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x13524) fc None m' (seg_rom rsegs)) \/
     (match_ = false /\ n + 1 = nh /\
      ms = MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 x8 (Z_to_bv 64 (n + 1)) x10 x11 x12 x13
                   x14 x15 x16 x17 x18 x19 (Z_to_bv 64 plen) (Z_to_bv 64 ka) x22 x23 x24 (Z_to_bv 64 (8 * n))
                   x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x13584) fc None m' (seg_rom rsegs))).

Lemma rig_u8_lit : forall t, 0 <= t < 256 -> bv_unsigned (Z_to_bv 8 t) = t.
Proof. intros t Ht. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. Qed.

Lemma rig_byte0 : forall b : byte, bv_unsigned b = 0 -> b = Z_to_bv 8 0.
Proof. intros b H. apply bv_eq. rewrite H, (rig_u8_lit 0) by lia. reflexivity. Qed.

Lemma rig_walk : forall (T : list Z) (x : list byte), T <> [] -> Forall (fun c => 0 < c < 256) T ->
  ~ In (Z_to_bv 8 0) x ->
  exists v, strncmp_walk (x ++ [Z_to_bv 8 0]) (pf_bytes (T ++ [0])) (pred (length T)) = Some v /\
    -256 < v < 256 /\ (v = 0 <-> firstn (length T) (map (fun b : byte => bv_unsigned b) x) = T).
Proof.
  unfold pf_bytes.
  induction T as [|t T IH]; intros x HT HF HX; [congruence|].
  apply Forall_cons_iff in HF. destruct HF as [Ht HF].
  assert (Ut : bv_unsigned (Z_to_bv 8 t) = t) by (apply rig_u8_lit; lia).
  destruct x as [|c x].
  - exists (0 - t). cbn [app map length pred strncmp_walk].
    rewrite Ut, (rig_u8_lit 0) by lia. cbn [Z.eqb orb].
    split; [reflexivity|]. split; [lia|]. cbn [firstn map]. split; [lia | intros H; discriminate H].
  - assert (Hc : bv_unsigned c <> 0) by (intros E; apply HX; left; apply rig_byte0; exact E).
    pose proof (bv_unsigned_in_range 8 c) as Rc. change (bv_modulus 8) with 256 in Rc.
    assert (HX' : ~ In (Z_to_bv 8 0) x) by (intros I; apply HX; right; exact I).
    cbn [app map length pred strncmp_walk]. rewrite Ut.
    rewrite (proj2 (Z.eqb_neq _ 0) Hc), (proj2 (Z.eqb_neq t 0)) by lia. cbn [orb].
    destruct T as [|t2 T2].
    + exists (bv_unsigned c - t). cbn [Nat.eqb orb length]. split; [reflexivity|]. split; [lia|].
      cbn [length firstn map]. split; [intros E; f_equal; lia | intros E; injection E; lia].
    + destruct (Z.eqb_spec (bv_unsigned c) t) as [E|E].
      * destruct (IH x ltac:(congruence) HF HX') as (v & Hv & Rv & Ev).
        cbn [app map length pred] in Hv, Ev.
        exists v. cbn [negb orb Nat.eqb length]. split; [exact Hv|]. split; [exact Rv|].
        cbn [firstn map length]. rewrite Ev. split.
        -- intros H. rewrite H, E. reflexivity.
        -- intros H. injection H as _ H. exact H.
      * exists (bv_unsigned c - t). cbn [negb orb Nat.eqb length]. split; [reflexivity|]. split; [lia|].
        cbn [firstn map length]. split; [lia | intros H; injection H; lia].
Qed.

Lemma rig_strncmp : forall (T : list Z) (x : list byte), Forall (fun c => 0 < c < 256) T ->
  1 <= Z.of_nat (length T) -> ~ In (Z_to_bv 8 0) x ->
  exists v, strncmp_model (x ++ [Z_to_bv 8 0]) (pf_bytes (T ++ [0])) (Z.of_nat (length T)) = Some v /\
    -256 < v < 256 /\ (v = 0 <-> has_prefix T (map (fun b : byte => bv_unsigned b) x) = true).
Proof.
  intros T x HF HL HX.
  destruct (rig_walk T x ltac:(intros E; subst T; cbn in HL; lia) HF HX) as (v & Hv & Rv & Ev).
  exists v. unfold strncmp_model.
  replace (Z.of_nat (length T) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (Z.to_nat (Z.of_nat (length T) - 1)) with (pred (length T)) by lia.
  split; [exact Hv|]. split; [exact Rv|].
  rewrite Ev. unfold has_prefix. split.
  - intros H. rewrite H. apply list_eqb_refl.
  - apply list_eqb_true.
Qed.

Lemma rig_segE : strncmp_contract ->
  forall x1 gp tp x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x28 x29 x30 x31
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P n nh hp ka knext : Z) (T : list Z) (x : list byte),
  mem_inv rsegs m ->
  bytes_at rsegs m ka (x ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) x ->
  bytes_at rsegs m (P + 8) (pf_bytes (T ++ [0])) -> Forall (fun c => 0 < c < 256) T -> 1 <= Z.of_nat (length T) < 48 ->
  0 <= n < nh -> nh < 2 ^ 26 -> 0 <= hp -> hp + 8 * nh <= 2 ^ 64 -> 0 <= P < 2 ^ 64 ->
  (n + 1 < nh -> bytes_at rsegs m (hp + 8 * (n + 1)) (le8 (Z_to_bv 64 knext))) ->
  evt rsegs (rig_postE gp tp x8 x18 x19 x22 x23 x24 (Z_to_bv 64 nh) (Z_to_bv 64 hp) F fc
               P (Z.of_nat (length T)) n nh hp ka knext (has_prefix T (map (fun b : byte => bv_unsigned b) x)) m)
    (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 x8 (Z_to_bv 64 n) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 (Z_to_bv 64 (Z.of_nat (length T))) (Z_to_bv 64 ka) x22 x23 x24 (Z_to_bv 64 (8 * n))
             (Z_to_bv 64 nh) (Z_to_bv 64 hp) x28 x29 x30 x31)
        F (Z_to_bv 64 0x13524) fc None m (seg_rom rsegs)).
Proof.
  intros SNC x1 gp tp x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x28 x29 x30 x31
    F fc m P n nh hp ka knext T x MI HK HX HT HTF HTL Hn Hnh Hhp Hhb HP HN.
  pose proof (bytes_at_bound _ _ _ _ HK) as KB. rewrite length_app in KB. cbn [length] in KB.
  pose proof (bytes_at_bound _ _ _ _ HT) as TB. unfold pf_bytes in TB. rewrite length_map, length_app in TB.
  cbn [length] in TB.
  destruct (rig_strncmp T x HTF ltac:(lia) HX) as (v & HV & RV & EV).
  pose proof (munch_refl [] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (SNC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               (x ++ [Z_to_bv 8 0]) (pf_bytes (T ++ [0])) v);
      rewrite ?unsigned_lit by lia; first [eassumption | lia]
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold strncmp_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO;
      post_call rsegs mm ]
  end.
  cbv delta [mkR].
  step. rewrite (rig_eqb0 v) by lia.
  destruct (Z.eqb_spec v 0) as [V0|V0]; cbn [negb]; cbv iota.
  - assert (HP1 : has_prefix T (map (fun b : byte => bv_unsigned b) x) = true) by (apply EV; exact V0).
    step. step.
    apply evt_done. unfold rig_postE. rewrite HP1.
    exists (Z_to_bv 64 0). do 3 eexists. exists (Z_to_bv 64 0). do 12 eexists.
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    left. split; reflexivity.
  - assert (HP0 : has_prefix T (map (fun b : byte => bv_unsigned b) x) = false).
    { apply Bool.not_true_iff_false. intros E. apply V0. apply EV. exact E. }
    step.
    step. rewrite (rig_lts (n + 1) nh) by lia.
    destruct (n + 1 <? nh) eqn:C; cbv iota.
    + apply Z.ltb_lt in C.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (rig_rd8 mm _ _ (bytes_at_transport rsegs [] m mm _ _ (HN C) MU I)) as HR
      end.
      step. rewrite (rig_shl3 (n + 1)) by lia.
      step. step.
      apply evt_done. unfold rig_postE. rewrite HP0.
      do 17 eexists.
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      right. left. split; [reflexivity|]. split; [exact C|]. reflexivity.
    + apply Z.ltb_ge in C.
      apply evt_done. unfold rig_postE. rewrite HP0.
      do 17 eexists.
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      right. right. split; [reflexivity|]. split; [lia|]. reflexivity.
Qed.

Lemma rig_segF : forall x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (EA n hp nh ka : Z),
  rw_cells rsegs m (EA + 40) [C8 (Z_to_bv 64 hp); C4 (Z_to_bv 64 nh)] ->
  bytes_at rsegs m (hp + 8 * n) (le8 (Z_to_bv 64 ka)) -> 0 <= n -> 0 <= hp -> 0 <= EA ->
  evt rsegs (fun ms =>
      ms = MS (mkR (Z_to_bv 64 0x13550) sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 ka) x11 x12 x13 x14 x15 x16 x17
                   x18 x19 x20 x21 x22 x23 (Z_to_bv 64 EA) (Z_to_bv 64 (8 * n)) x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 RIG_FREE) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 (Z_to_bv 64 EA) (Z_to_bv 64 (8 * n)) x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13540) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x26 x27
    x28 x29 x30 x31 F fc m EA n hp nh ka HC HK Hn Hhp HEA.
  pose proof (rw_cells_bound _ _ _ _ HC) as CB. cbn [cells_size csize] in CB.
  pose proof (bytes_at_bound _ _ _ _ HK) as KB. rewrite length_le8 in KB.
  pose proof (rig_rd8 _ _ _ HK) as HR.
  step. step. step. step.
  apply evt_done. reflexivity.
Qed.

Definition rig_postG (x1 sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (EA n hp nh klast : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms => exists x10 (m' : word -> option byte),
    ms = MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 klast) x22 x23
                 (Z_to_bv 64 EA) (Z_to_bv 64 (8 * n)) (Z_to_bv 64 (nh - 1)) (Z_to_bv 64 hp) x28 x29 x30 x31)
            F (Z_to_bv 64 (if n <? nh - 1 then 0x13524 else 0x13584)) fc None m' (seg_rom rsegs) /\
    munch [(EA + 48, EA + 52); (hp + 8 * n, hp + 8 * n + 8)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    rw_cells rsegs m' (EA + 40) [C8 (Z_to_bv 64 hp); C4 (Z_to_bv 64 (nh - 1))] /\
    rw_cells rsegs m' (hp + 8 * n) [C8 (Z_to_bv 64 klast)].

Lemma rig_segG : forall x1 sp gp tp x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (EA n hp nh klast : Z) (w : word),
  mem_inv rsegs m ->
  rw_cells rsegs m (EA + 40) [C8 (Z_to_bv 64 hp); C4 (Z_to_bv 64 nh)] ->
  bytes_at rsegs m (hp + 8 * (nh - 1)) (le8 (Z_to_bv 64 klast)) ->
  rw_cells rsegs m (hp + 8 * n) [C8 w] ->
  0 <= n < nh -> nh < 2 ^ 26 -> 0 <= hp -> hp + 8 * nh <= 2 ^ 64 -> 0 <= EA ->
  (EA + 52 <= hp \/ hp + 8 * nh <= EA + 40) ->
  evt rsegs (rig_postG x1 sp gp tp x5 x6 x7 x8 (Z_to_bv 64 n) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23
               x28 x29 x30 x31 F fc EA n hp nh klast m)
    (MS (mkR x1 sp gp tp x5 x6 x7 x8 (Z_to_bv 64 n) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 (Z_to_bv 64 EA) (Z_to_bv 64 (8 * n)) x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13550) fc None m (seg_rom rsegs)).
Proof.
  intros x1 sp gp tp x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x26 x27
    x28 x29 x30 x31 F fc m EA n hp nh klast w MI HC HK HW Hn Hnh Hhp Hhb HEA HD.
  pose proof (rw_cells_bound _ _ _ _ HC) as CB. cbn [cells_size csize] in CB.
  pose proof (rw_cells_bound _ _ _ _ HW) as WB. cbn [cells_size csize] in WB.
  pose proof (rig_rd8 _ _ _ HK) as HR. clear HK.
  pose proof (munch_refl [(EA + 48, EA + 52); (hp + 8 * n, hp + 8 * n + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  remember (hp + 8 * n) as B eqn:EB.
  step. rewrite (rig_sx32_small nh) by lia.
  step.
  step. rewrite (rig_addiw nh) by lia.
  step. rewrite (rig_shl3 (nh - 1)) by lia.
  step.
  step.
  step.
  step. rewrite <- EB.
  step.
  step. rewrite (rig_lts n (nh - 1)) by lia.
  destruct (n <? nh - 1) eqn:C; cbv iota.
  - apply evt_done. unfold rig_postG. rewrite C. subst B. do 2 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
  - step. apply evt_done. unfold rig_postG. rewrite C. subst B. do 2 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma rig_segH : pthread_mutex_unlock_contract ->
  forall x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S lo : Z)
    (w1 w8 w9 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 : word),
  rw_cells rsegs m (S - 160) [C8 (Z_to_bv 64 G_LOCK)] ->
  rw_cells rsegs m (S - 104) [C8 w27; C8 w26; C8 w25; C8 w24; C8 w23; C8 w22; C8 w21; C8 w20; C8 w19; C8 w18;
                              C8 w9; C8 w8; C8 w1] ->
  rw_cells rsegs m G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)] ->
  stk rsegs m lo S -> lo + 96 <= S -> G_LOCK_HI <= lo -> S < 2 ^ 64 ->
  mem_inv rsegs m ->
  evt rsegs (pthread_mutex_unlock_post w1 (Z_to_bv 64 S) gp tp w8 w9 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27
               F fc G_LOCK lo m)
    (MS (mkR x1 (Z_to_bv 64 (S - 160)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13590) fc None m (seg_rom rsegs)).
Proof.
  intros SPU x1 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m S lo w1 w8 w9 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 C0 CS GL ST LO LOG SHI MI.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold G_LOCK_HI in LOG.
  replace (S - 104) with (S - 160 + 56) in CS by lia.
  step. step. step. step. step. step. step. step. step. step. step. step. step. step. step.
  replace (Z_to_bv 64 (S - 160 + 160)) with (Z_to_bv 64 S) by (f_equal; lia).
  step.
  eapply (SPU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G_LOCK lo).
  - reflexivity.
  - exact GL.
  - rewrite unsigned_lit by lia. exact ST.
  - rewrite unsigned_lit by lia. lia.
  - rewrite unsigned_lit by lia. left. unfold G_LOCK. lia.
  - exact MI.
Qed.
