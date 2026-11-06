From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require YL01 YO0x YO0u.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract Img0 KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger ReaderRes fuzz_realloc_c grow_c.
Import YM05.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac cur_mem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.

Lemma grow_rd8 : forall m a x, bytes_at rsegs m a (le8 x) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 x).
Proof.
  intros m a x H.
  replace (wa a) with (wa (a + Z.of_nat 0)) by (f_equal; lia).
  rewrite (bytes_at_ov_read rsegs m a (le8 x) 0 8 H) by (rewrite length_le8; lia).
  cbn [skipn]. reflexivity.
Qed.

Lemma grow_rd4 : forall m a x, bytes_at rsegs m a (le4 x) -> ov_read_bytes rsegs m (wa a) 4 = Some (le4 x).
Proof.
  intros m a x H.
  replace (wa a) with (wa (a + Z.of_nat 0)) by (f_equal; lia).
  rewrite (bytes_at_ov_read rsegs m a (le4 x) 0 4 H) by (rewrite length_le4; lia).
  cbn [skipn]. reflexivity.
Qed.

Lemma grow_shl : forall x k, 0 <= x -> 0 <= k -> x * 2 ^ k < 2 ^ 64 ->
  Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) k) = Z_to_bv 64 (x * 2 ^ k).
Proof. intros x k H0 H1 H2. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Lemma cap2_range : forall cap, 0 <= cap <= 2 ^ 54 -> 0 < cap2 cap <= 2 ^ 55 /\ cap < cap2 cap.
Proof. intros cap H. unfold cap2. destruct (Z.eqb_spec cap 0); lia. Qed.

Lemma g_write_some : forall bs m a x, m x <> None -> write_to_mem m a bs x <> None.
Proof.
  induction bs as [|b bs IH]; intros m a x H; cbn; [exact H|].
  apply IH. destruct (bv_eqb x a); [discriminate | exact H].
Qed.

Lemma grow_munch2 : forall a b c d m m', munch [(a, b)] m m' -> munch [(a, b); (c, d)] m m'.
Proof. intros a b c d m m' H x Hx. apply H. cbn in *. tauto. Qed.

Local Ltac store_bw BW :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?M ?a ?bs) _) =>
      let E := addr_expr a in
      assert (BW : bytes_at rsegs (write_to_mem M (wa E) bs) E bs)
        by (apply bytes_at_write_same; rewrite ?length_le8; lia);
      try (lazymatch goal with
           | PM : forall x : word, ?m0 x <> None -> M x <> None |- _ =>
               let P := fresh "P" in
               pose proof (fun (x : word) (H : m0 x <> None) => g_write_some bs M (wa E) x (PM x H)) as P;
               clear PM; rename P into PM
           end)
  end;
  store_done.

Definition seg1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (v kids n cap : Z) (ms' : machine_state) : Prop :=
  (n < cap /\
   exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs) /\
     munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono rsegs m m')
  \/
  (n = cap /\
   exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte) (j : list byte),
     ms' = MS (mkR (Z_to_bv 64 0x1676c) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0' t1' t2' (Z_to_bv 64 v) s1
                   (Z_to_bv 64 kids) (Z_to_bv 64 (56 * cap2 cap)) a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 (8 * cap2 cap)) (Z_to_bv 64 (cap2 cap)) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 FUZZ_REALLOC) fc None m' (seg_rom rsegs) /\
     munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
     rw_cells rsegs m' (bv_unsigned sp - 48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

Definition seg2_post (rra sp gp tp r0 r1 r2 r3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (v ty keys nc res : Z) (j : list byte) (ms' : machine_state) : Prop :=
  (res = 0 /\
   exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     ms' = MS (mkR rra (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0' t1' t2' r0 r1 (Z_to_bv 64 (-1))
                   a1' a2' a3' a4' a5' a6' a7' r2 r3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
              F (ret_pc rra) fc None m (seg_rom rsegs))
  \/
  (res <> 0 /\ ty = 5 /\
   exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     ms' = MS (mkR rra (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0' t1' t2' r0 r1 (Z_to_bv 64 0)
                   a1' a2' a3' a4' a5' a6' a7' r2 r3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
              F (ret_pc rra) fc None m' (seg_rom rsegs) /\
     munch [(v + 24, v + 32); (v + 48, v + 56)] m m' /\ wmono rsegs m m' /\
     (forall x, m x <> None -> m' x <> None) /\
     bytes_at rsegs m' (v + 24) (le8 (Z_to_bv 64 res)) /\ bytes_at rsegs m' (v + 48) (le8 (Z_to_bv 64 nc)))
  \/
  (res <> 0 /\ ty = 6 /\
   exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     ms' = MS (mkR (Z_to_bv 64 0x16790) sp gp tp t0' t1' t2' (Z_to_bv 64 v) (Z_to_bv 64 (-1))
                   (Z_to_bv 64 keys) (Z_to_bv 64 (8 * nc)) a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 (8 * nc)) (Z_to_bv 64 nc) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 FUZZ_REALLOC) fc None m' (seg_rom rsegs) /\
     munch [(v + 24, v + 32)] m m' /\ wmono rsegs m m' /\ (forall x, m x <> None -> m' x <> None) /\
     bytes_at rsegs m' (v + 24) (le8 (Z_to_bv 64 res)) /\
     rw_cells rsegs m' (bv_unsigned sp) [CB 8 j; C8 r3; C8 r2; C8 r1; C8 r0; C8 rra]).

Definition seg3_post (rra sp gp tp r0 r1 r2 r3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (v nc res : Z) (ms' : machine_state) : Prop :=
  (res = 0 /\
   exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     ms' = MS (mkR rra (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0' t1' t2' r0 r1 (Z_to_bv 64 (-1))
                   a1' a2' a3' a4' a5' a6' a7' r2 r3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
              F (ret_pc rra) fc None m (seg_rom rsegs))
  \/
  (res <> 0 /\
   exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     ms' = MS (mkR rra (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0' t1' t2' r0 r1 (Z_to_bv 64 0)
                   a1' a2' a3' a4' a5' a6' a7' r2 r3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
              F (ret_pc rra) fc None m' (seg_rom rsegs) /\
     munch [(v + 32, v + 40); (v + 48, v + 56)] m m' /\ wmono rsegs m m' /\
     (forall x, m x <> None -> m' x <> None) /\
     bytes_at rsegs m' (v + 32) (le8 (Z_to_bv 64 res)) /\ bytes_at rsegs m' (v + 48) (le8 (Z_to_bv 64 nc))).

Lemma seg1_shape : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m v kids n cap ms,
  seg1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m v kids n cap ms ->
  exists R pc' m', ms = MS R F pc' fc None m' (seg_rom rsegs).
Proof. intros until ms. intros Hp. unfold seg1_post in Hp. repeat match goal with H : exists _, _ |- _ => destruct H | H : _ /\ _ |- _ => destruct H | H : _ \/ _ |- _ => destruct H end; subst ms; do 3 eexists; reflexivity. Qed.

Lemma seg2_shape : forall rra sp gp tp r0 r1 r2 r3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m v ty keys nc res j ms,
  seg2_post rra sp gp tp r0 r1 r2 r3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m v ty keys nc res j ms ->
  exists R pc' m', ms = MS R F pc' fc None m' (seg_rom rsegs).
Proof. intros until ms. intros Hp. unfold seg2_post in Hp. repeat match goal with H : exists _, _ |- _ => destruct H | H : _ /\ _ |- _ => destruct H | H : _ \/ _ |- _ => destruct H end; subst ms; do 3 eexists; reflexivity. Qed.

Lemma seg3_shape : forall rra sp gp tp r0 r1 r2 r3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m v nc res ms,
  seg3_post rra sp gp tp r0 r1 r2 r3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m v nc res ms ->
  exists R pc' m', ms = MS R F pc' fc None m' (seg_rom rsegs).
Proof. intros until ms. intros Hp. unfold seg3_post in Hp. repeat match goal with H : exists _, _ |- _ => destruct H | H : _ /\ _ |- _ => destruct H | H : _ \/ _ |- _ => destruct H end; subst ms; do 3 eexists; reflexivity. Qed.

Lemma gr_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma grow_seg1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v kids n cap : Z),
  a0 = Z_to_bv 64 v -> v <> 0 -> v mod 8 = 0 -> 0 <= v ->
  bytes_at rsegs m (v + 24) (le8 (Z_to_bv 64 kids)) ->
  bytes_at rsegs m (v + 40) (le8 (Z_to_bv 64 n)) ->
  bytes_at rsegs m (v + 48) (le8 (Z_to_bv 64 cap)) ->
  0 <= kids < 2 ^ 64 -> 0 <= n <= cap -> cap <= 2 ^ 54 ->
  stk rsegs m (bv_unsigned sp - 48) (bv_unsigned sp) -> 48 <= bv_unsigned sp ->
  (v + 56 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= v) ->
  evt rsegs (seg1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m v kids n cap)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 GROW) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    v kids n cap E0 V0 V8 VP H24 H40 H48 KR NR CR ST S48 VD.
  subst a0. unfold GROW, FUZZ_REALLOC.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (bytes_at_bound rsegs m _ _ H24) as B24. rewrite length_le8 in B24.
  pose proof (bytes_at_bound rsegs m _ _ H48) as B48. rewrite length_le8 in B48.
  carve_frame 48%nat ST.
  do 6 step.
  step. if_cases HB0; [zify_cond HB0; rewrite ?(unsigned_lit v) in HB0 by lia; lia|].
  step. step. step. if_cases HB1.
  { zify_cond HB1. rewrite ?(unsigned_lit v) in HB1 by lia. rewrite gr_land7 in HB1. contradiction. }
  let mm := cur_mem in pose proof (grow_rd8 mm _ _ H40) as R40; pose proof (grow_rd8 mm _ _ H48) as R48.
  step. step. step.
  if_cases HC; zify_cond HC; rewrite ?(unsigned_lit n), ?(unsigned_lit cap) in HC by lia.
  - assert (EN : n = cap) by lia. subst n.
    let mm := cur_mem in pose proof (grow_rd8 mm _ _ H24) as R24.
    step.
    if_cases HZ; zify_cond HZ; rewrite ?(unsigned_lit cap) in HZ by lia.
    + assert (C2 : cap2 cap = cap * 2 ^ 1) by (unfold cap2; rewrite (proj2 (Z.eqb_neq cap 0)) by lia; lia).
      step. do 5 step.
      rewrite (grow_shl cap 1) by lia. rewrite <- C2.
      pose proof (cap2_range cap ltac:(lia)) as CR2.
      rewrite (grow_shl (cap2 cap) 3), (grow_shl (cap2 cap) 6) by lia.
      rewrite (unsigned_lit (cap2 cap * 2 ^ 6)), (unsigned_lit (cap2 cap * 2 ^ 3)) by lia.
      replace (cap2 cap * 2 ^ 6 - cap2 cap * 2 ^ 3) with (56 * cap2 cap) by lia.
      replace (cap2 cap * 2 ^ 3) with (8 * cap2 cap) by lia.
      apply evt_done. unfold seg1_post. right. split; [reflexivity|].
      do 15 eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. eassumption.
    + assert (C0 : cap = 0) by lia. subst cap.
      step. step. do 5 step.
      apply evt_done. unfold seg1_post. right. split; [reflexivity|].
      do 15 eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. eassumption.
  - assert (EN : n < cap) by lia.
    do 10 step.
    apply evt_done. unfold seg1_post. left. split; [exact EN|].
    do 15 eexists. split; [reflexivity|]. split; [eassumption|]. eassumption.
Qed.

Lemma grow_seg2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v ty keys nc res : Z) (j : list byte)
    (rra r0 r1 r2 r3 : word),
  a0 = Z_to_bv 64 res -> s0 = Z_to_bv 64 v -> s2 = Z_to_bv 64 (8 * nc) -> s3 = Z_to_bv 64 nc ->
  0 <= res < 2 ^ 64 -> 0 <= nc < 2 ^ 64 -> (ty = 5 \/ ty = 6) ->
  bytes_at rsegs m v (le4 (Z_to_bv 64 ty)) ->
  bytes_at rsegs m (v + 32) (le8 (Z_to_bv 64 keys)) ->
  wr_at rsegs m v 56 ->
  rw_cells rsegs m (bv_unsigned sp) [CB 8 j; C8 r3; C8 r2; C8 r1; C8 r0; C8 rra] ->
  (v + 56 <= bv_unsigned sp \/ bv_unsigned sp + 48 <= v) ->
  evt rsegs (seg2_post rra sp gp tp r0 r1 r2 r3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m v ty keys nc res j)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1676c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    v ty keys nc res j rra r0 r1 r2 r3 E0 E8 E18 E19 RR NC TY H0 H32 WR FR VD.
  subst a0 s0 s2 s3. unfold FUZZ_REALLOC.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (munch_refl [(v + 24, v + 32)] m) as MU.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof WR as (WR0 & WR1 & _).
  step. step.
  if_cases HZ; zify_cond HZ; rewrite ?(unsigned_lit res) in HZ by lia.
  - do 8 step.
    apply evt_done. unfold seg2_post. left. split; [lia|].
    do 14 eexists. reflexivity.
  - assert (S24 : store_ok rsegs m (wa (v + 24)) 8 = true) by (apply (wr_at_store_ok rsegs m v 56 24 8 WR); lia).
    pose proof (fun (x : word) (H : m x <> None) => H) as PM.
    let mm := cur_mem in pose proof (grow_rd4 mm _ _ H0) as R0.
    destruct TY as [TY|TY]; subst ty.
    + step. step. step. store_bw BW. step. if_true.
      pose proof (grow_munch2 _ _ (v + 48) (v + 56) _ _ MU) as MU2.
      clear MU.
      let mm := cur_mem in
      assert (S48 : store_ok rsegs mm (wa (v + 48)) 8 = true) by (apply (wr_at_store_ok rsegs mm v 56 48 8 WR); lia).
      step. step. store_bw BW2.
      do 8 step.
      apply evt_done. unfold seg2_post. right. left. split; [lia|]. split; [reflexivity|].
      do 15 eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|].
      split; [exact PM|]. split; [exact BW | exact BW2].
    + step. step. step. store_bw BW. step. if_false.
      let mm := cur_mem in pose proof (grow_rd8 mm _ _ H32) as R32.
      do 3 step.
      apply evt_done. unfold seg2_post. right. right. split; [lia|]. split; [reflexivity|].
      do 14 eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|].
      split; [exact PM|]. split; [exact BW | eassumption].
Qed.

Lemma grow_seg3 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v nc res : Z) (j : list byte)
    (rra r0 r1 r2 r3 : word),
  a0 = Z_to_bv 64 res -> s0 = Z_to_bv 64 v -> s1 = Z_to_bv 64 (-1) -> s3 = Z_to_bv 64 nc ->
  0 <= res < 2 ^ 64 -> 0 <= nc < 2 ^ 64 ->
  wr_at rsegs m v 56 ->
  rw_cells rsegs m (bv_unsigned sp) [CB 8 j; C8 r3; C8 r2; C8 r1; C8 r0; C8 rra] ->
  (v + 56 <= bv_unsigned sp \/ bv_unsigned sp + 48 <= v) ->
  evt rsegs (seg3_post rra sp gp tp r0 r1 r2 r3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m v nc res)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16790) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    v nc res j rra r0 r1 r2 r3 E0 E8 E9 E19 RR NC WR FR VD.
  subst a0 s0 s1 s3.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (munch_refl [(v + 32, v + 40); (v + 48, v + 56)] m) as MU.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof WR as (WR0 & WR1 & _).
  step.
  if_cases HZ; zify_cond HZ; rewrite ?(unsigned_lit res) in HZ by lia.
  - do 8 step.
    apply evt_done. unfold seg3_post. left. split; [lia|].
    do 14 eexists. reflexivity.
  - assert (S32 : store_ok rsegs m (wa (v + 32)) 8 = true) by (apply (wr_at_store_ok rsegs m v 56 32 8 WR); lia).
    pose proof (fun (x : word) (H : m x <> None) => H) as PM.
    step. store_bw BW.
    let mm := cur_mem in
    assert (S48 : store_ok rsegs mm (wa (v + 48)) 8 = true) by (apply (wr_at_store_ok rsegs mm v 56 48 8 WR); lia).
    step. step. store_bw BW2.
    do 8 step.
    apply evt_done. unfold seg3_post. right. split; [lia|].
    do 15 eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|].
    split; [exact PM|]. split; [exact BW | exact BW2].
Qed.

Ltac cs_cases tac :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; unfold callee_saved in Hr;
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [tac .. |];
  let Hr' := fresh "Hr" in
  assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
    by lia;
  destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; tac.

Lemma g_out : forall W x, (~ Frame.outside W x -> False) -> Frame.outside W x.
Proof. intros W x H. destruct (kb_outside_dec W x) as [Ho|Ho]; [exact Ho | exfalso; exact (H Ho)]. Qed.

Lemma g_pw : forall (l : list (Z * Z)) x y, pairwise ranges_disjoint l -> In x l -> In y l -> x <> y ->
  ranges_disjoint x y.
Proof.
  induction l as [|z l IH]; intros x y H Hx Hy Hne; [destruct Hx|].
  cbn [pairwise] in H. destruct H as [Hz Hl]. destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - exfalso. apply Hne. reflexivity.
  - exact (Hz y Hy).
  - pose proof (Hz x Hx) as D. unfold ranges_disjoint in *. lia.
  - exact (IH x y Hl Hx Hy Hne).
Qed.

Lemma g_pw_dup : forall (c1 c2 : list (Z * Z)) x, pairwise ranges_disjoint (c1 ++ x :: c2) -> In x (c1 ++ c2) ->
  snd x <= 0.
Proof.
  induction c1 as [|z c1 IH]; intros c2 x H Hin; cbn [app pairwise] in H, Hin.
  - destruct H as [H _]. pose proof (H x Hin) as D. unfold ranges_disjoint in D. lia.
  - destruct H as [Hz H]. destruct Hin as [<-|Hin].
    + pose proof (Hz z (in_or_app c1 (z :: c2) z (or_intror (in_eq z c2)))) as D. unfold ranges_disjoint in D. lia.
    + exact (IH c2 x H Hin).
Qed.

Lemma g_old : forall segs m p k, 0 <= k -> (forall i, 0 <= i < k -> mbyte segs m (p + i) <> None) ->
  exists old : list byte, Z.of_nat (length old) = k /\
    forall i, 0 <= i < k -> mbyte segs m (p + i) = nth_error old (Z.to_nat i).
Proof.
  intros segs m p k Hk H.
  assert (G : forall nn : nat, Z.of_nat nn <= k -> exists old : list byte, length old = nn /\
    forall i, 0 <= i < Z.of_nat nn -> mbyte segs m (p + i) = nth_error old (Z.to_nat i)).
  { induction nn as [|nn IH]; intros Hn.
    - exists []. split; [reflexivity|]. intros i Hi. lia.
    - destruct (IH ltac:(lia)) as (old & Hl & Ho).
      destruct (mbyte segs m (p + Z.of_nat nn)) as [bb|] eqn:Eb; [|exfalso; exact (H (Z.of_nat nn) ltac:(lia) Eb)].
      exists (old ++ [bb]). split; [rewrite length_app; cbn [length]; lia|].
      intros i Hi. destruct (Z.eq_dec i (Z.of_nat nn)) as [->|Hne].
      + rewrite Nat2Z.id, nth_error_app2 by lia. rewrite Hl, Nat.sub_diag. cbn [nth_error]. exact Eb.
      + rewrite nth_error_app1 by lia. apply Ho. lia. }
  destruct (G (Z.to_nat k) ltac:(lia)) as (old & Hl & Ho). exists old. split; [lia|]. intros i Hi. apply Ho. lia.
Qed.

Lemma g_nout1 : forall lo hi x, ~ Frame.outside [(lo, hi)] x -> lo <= x < hi.
Proof.
  intros lo hi x H. destruct (Z_le_gt_dec lo x); destruct (Z_lt_ge_dec x hi); try lia;
    exfalso; apply H; cbn; refine (conj _ I); lia.
Qed.

Lemma g_nout2 : forall a b c d x, ~ Frame.outside [(a, b); (c, d)] x -> a <= x < b \/ c <= x < d.
Proof.
  intros a b c d x H. destruct (Z_le_gt_dec a x); destruct (Z_lt_ge_dec x b); try (left; lia);
    destruct (Z_le_gt_dec c x); destruct (Z_lt_ge_dec x d); try (right; lia);
    exfalso; apply H; cbn; refine (conj _ (conj _ I)); lia.
Qed.

Lemma g_lsum_app : forall l1 l2, lsum (l1 ++ l2) = lsum l1 + lsum l2.
Proof. induction l1 as [|[a k] l1 IH]; intros l2; cbn [app lsum]; [lia | rewrite IH; lia]. Qed.

Lemma g_lsum_perm : forall l l', Permutation l l' -> lsum l = lsum l'.
Proof.
  intros l l' H. induction H as [|[a k] l l' H IH|[a k] [a' k'] l|l l' l'' H1 IH1 H2 IH2]; cbn [lsum]; lia.
Qed.

Lemma g_kids_lsum : forall kids cap, 0 <= cap -> lsum (kids_blk kids cap) = 56 * cap.
Proof. intros kids cap H. unfold kids_blk. destruct (Z.eqb_spec cap 0); cbn [lsum]; lia. Qed.

Lemma g_keys_lsum : forall keys cap, 0 <= cap -> lsum (keys_blk 6 keys cap) = 8 * cap.
Proof. intros keys cap H. unfold keys_blk. destruct (Z.eqb_spec cap 0); cbn; lia. Qed.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.

Lemma g_img : ms_segs B = rsegs -> img_low B.
Proof.
  intros HS. apply (img_low_of_check B 140735332483072).
  - unfold img_check. rewrite HS. vm_compute. reflexivity.
  - pose proof alloc_ceiling_value. lia.
Qed.

Lemma g_blocks_user : forall L A p k, In (p, k) (blocks L A) -> exists q, In (q, k) (user_blocks A) /\ ptr_addr L q = p.
Proof.
  intros L A p k Hin. unfold blocks in Hin. apply in_map_iff in Hin.
  destruct Hin as ([q k'] & E & Hq). cbn [fst snd] in E. injection E as E1 E2. subst k'.
  exists q. split; [exact Hq | exact E1].
Qed.

Lemma g_user_blocks : forall L A q k, In (q, k) (user_blocks A) -> In (ptr_addr L q, k) (blocks L A).
Proof. intros L A q k H. unfold blocks. apply in_map_iff. exists (q, k). split; [reflexivity | exact H]. Qed.

Lemma g_blk_range : forall L A mem md p k, aa_MR API L A mem md -> In (p, k) (blocks L A) ->
  4096 <= p /\ p + k <= alloc_ceiling.
Proof.
  intros L A mem md p k HM Hin. destruct (g_blocks_user L A p k Hin) as (q & Hq & <-).
  exact (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q k HM Hq).
Qed.

Lemma g_disj : forall L A mem md a k a' k', aa_MR API L A mem md -> In (a, k) (blocks L A) ->
  In (a', k') (blocks L A) -> (a, k) <> (a', k') -> a + k <= a' \/ a' + k' <= a.
Proof.
  intros L A mem md a k a' k' HM H1 H2 Hne.
  exact (g_pw _ _ _ (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM) H1 H2 Hne).
Qed.

Lemma g_ptr : forall L L' A p n, WF A -> In (p, n) (user_blocks A) -> layout_le A L L' -> ptr_addr L' p = ptr_addr L p.
Proof.
  intros L L' A p n HW Hin (_ & _ & _ & HR).
  destruct (YO0x.user_blocks_frame A p n HW Hin) as (g & am & idx & fr & Hu & _ & _ & _ & _ & ->).
  pose proof (YO0u.used_group_prid_lt [] None U0 A g am HW Hu) as Hlt.
  unfold frame_ptr, slot_start, ptr_addr. destruct (am_mem am) as [r o]. cbn in Hlt |- *.
  rewrite (HR r Hlt). reflexivity.
Qed.

Lemma g_vm : forall vm1 vm2 md, with_vmmaps vm2 (with_vmmaps vm1 md) = with_vmmaps vm2 md.
Proof. intros vm1 vm2 md. reflexivity. Qed.

Lemma g_bytes : forall m m' a bs, bytes_at (ms_segs B) m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte (ms_segs B) m' x = mbyte (ms_segs B) m x) ->
  bytes_at (ms_segs B) m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) Hm. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite <- (H i Hi). exact (Hm (a + Z.of_nat i) ltac:(lia)).
Qed.

Lemma g_wr : forall m a n, 0 <= a -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> writable_at (ms_segs B) m (a + i)) -> wr_at (ms_segs B) m a n.
Proof. intros m a n H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros i Hi. exact (H i Hi). Qed.

Lemma g_rw_cells : forall m m' a cs, Step.rw_cells (ms_segs B) m a cs ->
  (forall x, a <= x < a + Z.of_nat (cells_size cs) -> mbyte (ms_segs B) m' x = mbyte (ms_segs B) m x /\
     (writable_at (ms_segs B) m x -> writable_at (ms_segs B) m' x)) ->
  Step.rw_cells (ms_segs B) m' a cs.
Proof.
  intros m m' a cs ((Hwf & Hb) & (W0 & W1 & W)) H.
  split; [split; [exact Hwf|]|].
  - apply (g_bytes m m' a _ Hb). intros x Hx. rewrite (cells_bytes_length cs Hwf) in Hx. exact (proj1 (H x Hx)).
  - split; [exact W0|]. split; [exact W1|]. intros i Hi. apply (proj2 (H (a + i) ltac:(lia))). exact (W i Hi).
Qed.

Lemma g_bytes_some : forall m a bs x, bytes_at (ms_segs B) m a bs -> a <= x < a + Z.of_nat (length bs) ->
  mbyte (ms_segs B) m x <> None.
Proof.
  intros m a bs x (_ & _ & H) Hx Hn. pose proof (H (Z.to_nat (x - a)) ltac:(lia)) as E.
  replace (a + Z.of_nat (Z.to_nat (x - a))) with x in E by lia.
  assert (E2 : mbyte (ms_segs B) m x = nth_error bs (Z.to_nat (x - a))) by exact E.
  rewrite Hn in E2. symmetry in E2. apply nth_error_None in E2. lia.
Qed.

Lemma g_seg_img : ms_segs B = rsegs -> forall x seg, find_segment (ms_segs B) x 1 = Some seg -> in_img B x.
Proof.
  intros HSEG x seg E. destruct (kb_find_segment _ x 1 seg E) as (Hin & H1 & H2).
  assert (C : forallb (fun s => existsb (fun rr => (bv_unsigned (fst rr) <=? Z.of_N (seg_base s)) &&
      (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? bv_unsigned (fst rr) + bv_unsigned (snd rr)))
      (segments_reserved (ms_segs B))) (ms_segs B) = true) by (rewrite HSEG; vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C seg Hin). apply existsb_exists in C. destruct C as (rr & Hr & Hc).
  apply andb_prop in Hc as (Hc1 & Hc2). apply Z.leb_le in Hc1, Hc2.
  split; [intros E'; rewrite E' in Hin; destruct Hin | exists rr; split; [exact Hr | lia]].
Qed.

Lemma g_ro_notimg : ms_segs B = rsegs -> forall a, 0 <= a < 2 ^ 64 -> ~ in_img B a ->
  ro_addr (ms_segs B) (Z_to_bv 64 a) = false.
Proof.
  intros HSEG a Ha Hn. unfold ro_addr. rewrite unsigned_lit by lia.
  destruct (find_segment (ms_segs B) a 1) as [seg|] eqn:E; [exfalso; exact (Hn (g_seg_img HSEG a seg E)) | reflexivity].
Qed.

Lemma g_ro_low : img_low B -> forall a, alloc_ceiling <= a < 2 ^ 64 -> ro_addr (ms_segs B) (Z_to_bv 64 a) = false.
Proof.
  intros HIL a Ha. pose proof alloc_ceiling_value. unfold ro_addr. rewrite unsigned_lit by lia.
  destruct (find_segment (ms_segs B) a 1) as [seg|] eqn:E; [exfalso; pose proof (proj2 HIL a seg E); lia | reflexivity].
Qed.

Lemma g_ro_munch : forall W m m', U.MemNorm.ro_agree (ms_segs B) m -> Frame.munch W m m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Frame.outside W a -> ro_addr (ms_segs B) (Z_to_bv 64 a) = false) ->
  U.MemNorm.ro_agree (ms_segs B) m'.
Proof.
  intros W m m' H HM HW a Ha. destruct (kb_outside_dec W (bv_unsigned a)) as [Ho|Ho].
  - pose proof (H a Ha) as E. unfold mrd in *. rewrite (HM a Ho). exact E.
  - exfalso. pose proof (bv_unsigned_in_range 64 a) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    pose proof (HW (bv_unsigned a) Hr Ho) as E. rewrite Step.Z_to_bv_lit_self in E. congruence.
Qed.

Lemma g_ledger_munch : forall L A mem md mem' Lam peak cnt fail W,
  aa_MR API L A mem md -> ledger B L A mem Lam peak cnt fail -> Frame.munch W mem mem' ->
  (forall x, ~ Frame.outside W x -> ~ alloc_statics x /\ forall a k, In (a, k) Lam -> ~ (a - 16 <= x < a - 8)) ->
  ledger B L A mem' Lam peak cnt fail.
Proof.
  intros L A mem md mem' Lam peak cnt fail W HM HL Hm HW.
  destruct HL as ((H1 & H2 & H3 & H4) & H5 & H6 & H7 & H8 & H9).
  assert (Hst : forall a v, word_mem (ms_segs B) mem a v -> (forall k, 0 <= k < 8 -> alloc_statics (a + k)) ->
    word_mem (ms_segs B) mem' a v).
  { intros a v Hw Hs. apply (kb_word_munch (ms_segs B) mem mem' W a v Hw Hm). intros k Hk.
    pose proof (Hs k Hk) as Hsk. split; [unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hsk; lia|].
    apply g_out. intros Hn. exact (proj1 (HW _ Hn) Hsk). }
  split; [|split; [exact H5|]; split; [exact H6|]; split; [exact H7|]; split; [exact H8|]].
  - split; [apply Hst; [exact H1 | intros k Hk; unfold alloc_statics; lia]|].
    split; [apply Hst; [exact H2 | intros k Hk; unfold alloc_statics; lia]|].
    split; [apply Hst; [exact H3 | intros k Hk; unfold alloc_statics; lia]|].
    apply Hst; [exact H4 | intros k Hk; unfold alloc_statics; lia].
  - rewrite Forall_forall in H9 |- *. intros [a k] Hin. destruct (H9 _ Hin) as (Hk & Hb & Hw & Hi). cbn [fst snd] in *.
    split; [exact Hk|]. split; [exact Hb|]. split; [|exact Hi].
    destruct (g_blk_range L A mem md _ _ HM Hb) as [R1 R2].
    apply (kb_word_munch (ms_segs B) mem mem' W (a - 16) k Hw Hm). intros j Hj.
    pose proof alloc_ceiling_lt. split; [lia|].
    apply g_out. intros Hn. exact (proj2 (HW _ Hn) a k Hin ltac:(lia)).
Qed.

Lemma g_kept_blk : forall K1 L1 A1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 g a k,
  call_post_k B (aa_MR API) K1 L1 A1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 ->
  ublocks_kept L1 A1 A2 g -> In (a, k) (blocks L1 A1) -> (a, k) <> g -> In (a, k) (blocks L2 A2).
Proof.
  intros K1 L1 A1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 g a k HP Hub Hin Hne.
  destruct (g_blocks_user L1 A1 a k Hin) as (q & Hq & Eq).
  pose proof HP as (_ & _ & _ & _ & C5 & _).
  assert (Hq2 : In (q, k) (user_blocks A2)) by (apply Hub; [exact Hq | rewrite Eq; exact Hne]).
  rewrite <- Eq, <- (C5 q k Hq Hq2). apply g_user_blocks. exact Hq2.
Qed.

Lemma g_fresh : forall L1 A1 L2 A2 mem2 md2 p k res nn,
  aa_MR API L2 A2 mem2 md2 -> 0 < nn + 16 ->
  (p = 0 /\ (exists b1 b2, blocks L2 A2 = b1 ++ (res - 16, nn + 16) :: b2 /\ blocks L1 A1 = b1 ++ b2)
   \/ p <> 0 /\ (exists b1 b2 c1 c2, blocks L1 A1 = b1 ++ (p - 16, k + 16) :: b2 /\
         blocks L2 A2 = c1 ++ (res - 16, nn + 16) :: c2 /\ c1 ++ c2 = b1 ++ b2)) ->
  (res - 16, nn + 16) <> (p - 16, k + 16) ->
  ~ In (res - 16, nn + 16) (blocks L1 A1) /\ In (res - 16, nn + 16) (blocks L2 A2).
Proof.
  intros L1 A1 L2 A2 mem2 md2 p k res nn HM Hn Hsh Hne.
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM) as PW. fold (blocks L2 A2) in PW.
  destruct Hsh as [(_ & b1 & b2 & E2 & E1) | (_ & b1 & b2 & c1 & c2 & E1 & E2 & E12)];
    (split; [| rewrite E2; apply in_or_app; right; left; reflexivity]); intros Hin; rewrite E2 in PW.
  - rewrite E1 in Hin. pose proof (g_pw_dup b1 b2 _ PW Hin). cbn [snd] in *. lia.
  - rewrite E1 in Hin. apply in_app_or in Hin. destruct Hin as [Hin|[Heq|Hin]].
    + pose proof (g_pw_dup c1 c2 _ PW ltac:(rewrite E12; apply in_or_app; left; exact Hin)). cbn [snd] in *. lia.
    + exact (Hne (eq_sym Heq)).
    + pose proof (g_pw_dup c1 c2 _ PW ltac:(rewrite E12; apply in_or_app; right; exact Hin)). cbn [snd] in *. lia.
Qed.

Lemma g_auxv_keep : forall sec lo mem mem', auxv_pre B sec lo mem ->
  (forall i, 0 <= i < 8 -> mbyte (ms_segs B) mem' (ms_libc B + 8 + i) = mbyte (ms_segs B) mem (ms_libc B + 8 + i)) ->
  (forall a, lo <= a < 2 ^ 63 -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a) ->
  auxv_pre B sec lo mem'.
Proof.
  intros sec lo mem mem' (av & ar & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) Hl Hh.
  exists av, ar.
  split; [apply (word_mem_frame (ms_segs B) mem mem' _ _ H1); intros k Hk; apply Hl; lia|].
  split; [intros k Hk; apply (word_mem_frame (ms_segs B) mem mem' _ _ (H2 k Hk)); intros j Hj; apply Hh; lia|].
  split; [apply (word_mem_frame (ms_segs B) mem mem' _ _ H3); intros j Hj; apply Hh; lia|].
  split; [apply (word_mem_frame (ms_segs B) mem mem' _ _ H4); intros j Hj; apply Hh; lia|].
  repeat (split; [assumption|]); assumption.
Qed.

Definition vloc (L : layout) (A : astate) (Lam : list (Z * Z)) (S v r rk : Z) : Prop :=
  (S <= v /\ v + 56 <= 2 ^ 64 /\ r = 0 /\ rk = -1) \/
  (In (r, rk) (blocks L A) /\ r <= v /\ v + 56 <= r + rk /\
   (forall a k, In (a, k) Lam -> a - 8 <= v \/ v + 56 <= a - 16)).

Lemma vloc_own : forall L A Lam mem md S v r rk x, vloc L A Lam S v r rk -> aa_MR API L A mem md ->
  alloc_ceiling <= S -> v <= x < v + 56 -> ~ static_owned B x -> ~ owned B L A x.
Proof.
  intros L A Lam mem md S v r rk x [(Hs & _ & _ & _)|(Hin & H1 & H2 & _)] HM Hc Hx Hst Ho.
  - pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ x HM Ho). lia.
  - destruct Ho as [Ho|Ho]; [|exact (Hst Ho)]. destruct Ho as [_ Hn]. apply Hn.
    destruct (g_blocks_user L A r rk Hin) as (q & Hq & Eq).
    exists (q, rk). split; [exact Hq|]. cbn [fst snd]. unfold ptr_addr in Eq. rewrite Eq. lia.
Qed.

Lemma vloc_heads : forall L A Lam mem md peak cnt fail S v r rk a k, vloc L A Lam S v r rk ->
  aa_MR API L A mem md -> ledger B L A mem Lam peak cnt fail -> alloc_ceiling <= S -> In (a, k) Lam ->
  a - 8 <= v \/ v + 56 <= a - 16.
Proof.
  intros L A Lam mem md peak cnt fail S v r rk a k [(Hs & _ & _ & _)|(_ & _ & _ & Hh)] HM HL Hc Hin;
    [|exact (Hh a k Hin)].
  pose proof (ledger_block_range B API L A mem md Lam peak cnt fail a k HM HL Hin) as (R1 & R2 & _).
  pose proof HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF. destruct (HF _ Hin) as (Hk & _).
  cbn [snd] in Hk. lia.
Qed.

Lemma vloc_call : forall L1 A1 Lam1 S v r rk K1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 g Lam2 peak2 cnt2 fail2,
  vloc L1 A1 Lam1 S v r rk ->
  call_post_k B (aa_MR API) K1 L1 A1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 ->
  ublocks_kept L1 A1 A2 g -> (r, rk) <> g ->
  ledger B L2 A2 mem2 Lam2 peak2 cnt2 fail2 ->
  (forall a k, In (a, k) Lam2 -> In (a, k) Lam1 \/ ~ In (a - 16, k + 16) (blocks L1 A1)) ->
  vloc L2 A2 Lam2 S v r rk.
Proof.
  intros L1 A1 Lam1 S v r rk K1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 g Lam2 peak2 cnt2 fail2
    [Hs|(Hin & H1 & H2 & Hh)] HP Hub Hne HL Hsub; [left; exact Hs|].
  right. pose proof (g_kept_blk K1 L1 A1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 g r rk HP Hub Hin Hne) as Hin2.
  split; [exact Hin2|]. split; [exact H1|]. split; [exact H2|].
  intros a k Hak. destruct (Hsub a k Hak) as [Ho|Hn]; [exact (Hh a k Ho)|].
  pose proof HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF. destruct (HF _ Hak) as (Hk & Hb & _).
  cbn [fst snd] in *.
  assert (Hd : (a - 16, k + 16) <> (r, rk)) by (intros E; rewrite E in Hn; exact (Hn Hin)).
  pose proof HP as (HM2 & _).
  destruct (g_disj L2 A2 mem2 md2 _ _ _ _ HM2 Hb Hin2 Hd); lia.
Qed.

Lemma vloc_bytes : forall L1 A1 Lam1 S v r rk K1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 g x,
  vloc L1 A1 Lam1 S v r rk -> aa_MR API L1 A1 mem1 md1 ->
  call_post_k B (aa_MR API) K1 L1 A1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 ->
  ublocks_kept L1 A1 A2 g -> (r, rk) <> g ->
  alloc_ceiling <= S -> spZ regs1 <= S -> (forall a, E1 a -> a < alloc_ceiling) ->
  ~ (errno_addr B <= x < errno_addr B + 4) -> v <= x < v + 56 ->
  mbyte (ms_segs B) mem2 x = mbyte (ms_segs B) mem1 x /\
  (writable_at (ms_segs B) mem1 x -> writable_at (ms_segs B) mem2 x).
Proof.
  intros L1 A1 Lam1 S v r rk K1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 g x
    HV HM1 HP Hub Hne Hc Hsp HE1 Herr Hx.
  pose proof HP as (C1 & _ & _ & _ & C5 & _ & _ & C8 & C9 & _).
  destruct HV as [(Hs & Hv & _ & _)|(Hin & H1 & H2 & _)].
  - assert (No1 : ~ owned B L1 A1 x) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM1 Ho); lia).
    assert (No2 : ~ owned B L2 A2 x) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ C1 Ho); lia).
    destruct (C8 x ltac:(left; lia) No1 No2 ltac:(unfold scratch_k; lia)
      ltac:(intros HE; pose proof (HE1 x HE); lia)) as [E1' E2'].
    split; [exact E1' | apply E2'].
  - destruct (g_blocks_user L1 A1 r rk Hin) as (q & Hq & Eq).
    assert (Hq2 : In (q, rk) (user_blocks A2)) by (apply Hub; [exact Hq | rewrite Eq; exact Hne]).
    split.
    + pose proof (C9 q rk (x - r) Hq Hq2 ltac:(lia)) as E. rewrite Eq in E.
      replace (r + (x - r)) with x in E by lia. exact E.
    + intros _. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q rk (x - r) C1 Hq2 ltac:(lia)) as (P & _).
      rewrite (C5 q rk Hq Hq2), Eq in P. replace (r + (x - r)) with x in P by lia.
      exact (present_writable B mem2 x P).
Qed.

Lemma vloc_ne : forall L A Lam S v r rk a k, vloc L A Lam S v r rk -> ~ In (a, k) (blocks L A) -> 0 < k ->
  (r, rk) <> (a, k).
Proof.
  intros L A Lam S v r rk a k [(_ & _ & _ & Hr)|(Hin & _)] Hn Hk E; injection E as E1 E2.
  - lia.
  - subst a k. exact (Hn Hin).
Qed.

Lemma vloc_disj : forall L A Lam mem md S v r rk a k x, vloc L A Lam S v r rk -> aa_MR API L A mem md ->
  alloc_ceiling <= S -> In (a, k) (blocks L A) -> (a, k) <> (r, rk) -> a <= x < a + k -> x < v \/ v + 56 <= x.
Proof.
  intros L A Lam mem md S v r rk a k x [(Hs & _)|(Hin & H1 & H2 & _)] HM Hc Hak Hne Hx.
  - pose proof (g_blk_range L A mem md a k HM Hak). lia.
  - destruct (g_disj L A mem md a k r rk HM Hak Hin Hne); lia.
Qed.

Lemma g_vloc0 : forall L A mem md Lam peak cnt fail S v ty kids keys cap,
  aa_MR API L A mem md -> ledger B L A mem Lam peak cnt fail -> alloc_ceiling <= S ->
  pj_place (lin Lam) (fun a k => In (a, k) (blocks L A)) S (2 ^ 64) v ->
  pj_apart (kids_blk kids cap ++ keys_blk ty keys cap) v ->
  0 <= cap -> (0 < cap -> lin Lam kids (56 * cap) /\ (ty = 6 -> lin Lam keys (8 * cap))) ->
  exists r rk, vloc L A Lam S v r rk /\ (r, rk) <> (kids - 16, 56 * cap + 16) /\
    (ty = 6 -> (r, rk) <> (keys - 16, 8 * cap + 16)).
Proof.
  intros L A mem md Lam peak cnt fail S v ty kids keys cap HM HL Hc Hpl Hap Hcap Hcp.
  pose proof HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
  destruct Hpl as [(H1 & H2)|[(a & k & Hb & Hnl & H1 & H2)|(a & k & Hl & H1 & H2)]].
  - exists 0, (-1). split; [left; lia|].
    split; [intros E; injection E; lia | intros _ E; injection E; lia].
  - exists a, k. split.
    + right. split; [exact Hb|]. split; [lia|]. split; [lia|].
      intros a' k' Hin. destruct (HF _ Hin) as (Hk' & Hb' & _). cbn [fst snd] in *.
      assert (Hne : (a' - 16, k' + 16) <> (a, k)).
      { intros E. injection E as E1 E2. apply Hnl. unfold lin.
        replace (a + 16) with a' by lia. replace (k - 16) with k' by lia. exact Hin. }
      destruct (g_disj L A mem md _ _ _ _ HM Hb' Hb Hne); lia.
    + split.
      * intros E. injection E as E1 E2. destruct (Z.eq_dec cap 0) as [->|Hc0]; [lia|].
        apply Hnl. unfold lin. replace (a + 16) with kids by lia. replace (k - 16) with (56 * cap) by lia.
        exact (proj1 (Hcp ltac:(lia))).
      * intros Hty E. injection E as E1 E2. destruct (Z.eq_dec cap 0) as [->|Hc0]; [lia|].
        apply Hnl. unfold lin. replace (a + 16) with keys by lia. replace (k - 16) with (8 * cap) by lia.
        exact (proj2 (Hcp ltac:(lia)) Hty).
  - destruct (HF _ Hl) as (Hk & Hb & _). cbn [fst snd] in *.
    exists (a - 16), (k + 16). split.
    + right. split; [exact Hb|]. split; [lia|]. split; [lia|].
      intros a' k' Hin. destruct (HF _ Hin) as (Hk' & Hb' & _). cbn [fst snd] in *.
      destruct (Z.eq_dec a' a) as [->|Ha'].
      * left; lia.
      * assert (Hne : (a' - 16, k' + 16) <> (a - 16, k + 16)) by (intros E; injection E; lia).
        destruct (g_disj L A mem md _ _ _ _ HM Hb' Hb Hne); lia.
    + split.
      * intros E. injection E as E1 E2. destruct (Z.eq_dec cap 0) as [->|Hc0]; [lia|].
        apply (Hap (kids, 56 * cap) v); [| unfold pj_holds; cbn [fst snd]; lia | lia].
        apply in_or_app. left. unfold kids_blk. rewrite (proj2 (Z.eqb_neq cap 0) Hc0). left. reflexivity.
      * intros Hty E. injection E as E1 E2. destruct (Z.eq_dec cap 0) as [->|Hc0]; [lia|].
        apply (Hap (keys, 8 * cap) v); [| unfold pj_holds; cbn [fst snd]; lia | lia].
        apply in_or_app. right. unfold keys_blk. rewrite (proj2 (Z.eqb_neq cap 0) Hc0), Hty. cbn. left. reflexivity.
Qed.

Lemma g_stk : forall m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall x, lo <= x < hi -> writable_at (ms_segs B) m x /\ mbyte (ms_segs B) m x <> None) ->
  stk (ms_segs B) m lo hi.
Proof.
  intros m lo hi H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros a Ha. destruct (H a Ha) as [Hw Hm].
  split; [exact Hw|]. destruct (mbyte (ms_segs B) m a) as [bb|] eqn:E; [exists bb; exact E | contradiction].
Qed.

Lemma g_hdr : forall mem mem' p ty num str kids keys n cap kids' keys' cap',
  pj_hdr (ms_segs B) mem p ty num str kids keys n cap ->
  (forall x, p <= x < p + 56 -> writable_at (ms_segs B) mem' x /\ mbyte (ms_segs B) mem' x <> None) ->
  (forall x, (p <= x < p + 24 \/ p + 40 <= x < p + 48) -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x) ->
  pj_u64 (ms_segs B) mem' (p + 24) kids' -> pj_u64 (ms_segs B) mem' (p + 32) keys' ->
  pj_u64 (ms_segs B) mem' (p + 48) cap' ->
  pj_hdr (ms_segs B) mem' p ty num str kids' keys' n cap'.
Proof.
  intros mem mem' p ty num str kids keys n cap kids' keys' cap'
    ((Hp8 & HS) & (Ht & Bt) & (Hn1 & Bn1) & (Hs & Bs) & _ & _ & (Hn & Bn) & _) Hw He Hk Hy Hc.
  pose proof HS as (S0 & S1 & _).
  split; [split; [exact Hp8 | apply g_stk; [lia | lia | exact Hw]]|].
  split; [split; [exact Ht | apply (g_bytes mem); [exact Bt | intros x Hx; rewrite length_le4 in Hx; apply He; lia]]|].
  split; [split; [exact Hn1 | apply (g_bytes mem); [exact Bn1 | intros x Hx; rewrite length_le8 in Hx; apply He; lia]]|].
  split; [split; [exact Hs | apply (g_bytes mem); [exact Bs | intros x Hx; rewrite length_le8 in Hx; apply He; lia]]|].
  split; [exact Hk|]. split; [exact Hy|].
  split; [split; [exact Hn | apply (g_bytes mem); [exact Bn | intros x Hx; rewrite length_le8 in Hx; apply He; lia]]|].
  exact Hc.
Qed.

Lemma rp_refl : forall K L A regs mem md E gone,
  call_pre_k B (aa_MR API) K L A regs mem md ->
  rpost B API K L A regs mem md E gone L A regs mem md.
Proof.
  intros K L A regs mem md E gone (HM & HW & HB & _ & _ & _ & _ & HS & _ & HE & _).
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [apply layout_le_refl|].
  split; [tauto|]. split; [intros _ i _; reflexivity|]. split; [lia|].
  split; [intros p n Hp _; exact Hp|]. split; [intros; reflexivity|].
  split; [intros r _; reflexivity|]. split; [exists (m_vmmaps md); symmetry; apply kb_vm_id|].
  split; [intros; split; [reflexivity | tauto]|]. split; [intros; split; [reflexivity | tauto]|].
  split; [intros; reflexivity|].
  intros a [Ha|Ha]; [apply HS; exact Ha | apply HE; exact Ha].
Qed.

Lemma rp_regs : forall K L A regs mem md E gone L' A' mem' md' regs',
  rpost B API K L A regs mem md E gone L' A' regs mem' md' -> regs_preserved regs regs' ->
  rpost B API K L A regs mem md E gone L' A' regs' mem' md'.
Proof.
  intros K L A regs mem md E gone L' A' mem' md' regs'
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & _ & H11 & H12 & H13 & H14 & H15) Hr.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj Hr
    (conj H11 (conj H12 (conj H13 (conj H14 H15)))))))))))))).
Qed.

Lemma rp_A : img_low B -> forall K L A regs mem md E gone L1 A1 mem1 md1 mem2 W,
  aa_MR API L A mem md -> alloc_ceiling + K <= spZ regs ->
  rpost B API K L A regs mem md E gone L1 A1 regs mem1 md1 ->
  Frame.munch W mem1 mem2 -> Frame.wmono (ms_segs B) mem1 mem2 ->
  (forall x, 0 <= x < alloc_ceiling -> ~ Frame.outside W x -> mem1 (Z_to_bv 64 x) <> None ->
     mem2 (Z_to_bv 64 x) <> None) ->
  (forall x, ~ Frame.outside W x -> ((spZ regs - K <= x < spZ regs) \/ E x) /\ ~ owned B L1 A1 x) ->
  rpost B API K L A regs mem md E gone L1 A1 regs mem2 md1.
Proof.
  intros HIL K L A regs mem md E gone L1 A1 mem1 md1 mem2 W HM0 Hsp
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) Hm Hw Hp HW.
  pose proof alloc_ceiling_lt as Hc.
  assert (Ho : forall a, owned B L1 A1 a -> Frame.outside W a).
  { intros a Ha. apply g_out. intros Hn. exact (proj2 (HW a Hn) Ha). }
  assert (Hol : forall a, owned B L1 A1 a -> 0 <= a < alloc_ceiling)
    by (intros a Ha; exact (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ H1 Ha)).
  assert (Hq : forall a, ~ scratch_k B K regs a -> ~ E a -> Frame.outside W a).
  { intros a Hs He. apply g_out. intros Hn. destruct (HW a Hn) as [[Hx|Hx] _];
      [apply Hs; left; exact Hx | exact (He Hx)]. }
  split.
  { destruct (mr_model _ _ (aa_laws API) _ _ _ _ H1) as (Hh & Hl & Hmat).
    apply (mr_frame _ _ (aa_laws API) L1 A1 mem1 mem2 md1 md1 H1).
    - intros a Ha. pose proof (Hol a Ha). apply (mbyte_munch (ms_segs B) W); [exact Hm | lia | exact (Ho a Ha)].
    - intros a Ha Hpr. pose proof (Hol a Ha).
      apply (present_munch W mem1); [exact Hm | lia | exact (Ho a Ha) | exact Hpr].
    - intros q n i Hin Hi. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q n i H1 Hin Hi) as ((b0 & Hb) & R1 & R2 & _).
      destruct (kb_outside_dec W (ptr_addr L1 q + i)) as [Hout|Hout].
      + exists b0. rewrite (Hm (Z_to_bv 64 (ptr_addr L1 q + i))); [exact Hb|]. rewrite unsigned_lit by lia. exact Hout.
      + destruct (mem2 (Z_to_bv 64 (ptr_addr L1 q + i))) as [b'|] eqn:E2; [exists b'; exact E2|].
        exfalso. refine (Hp (ptr_addr L1 q + i) ltac:(lia) Hout _ E2). rewrite Hb. discriminate.
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split.
  { intros Hd i Hi. rewrite <- (H6 Hd i Hi).
    assert (Hs : owned B L1 A1 (ms_libc B + 8 + i)) by (right; unfold static_owned; right; right; left; lia).
    pose proof (Hol _ Hs). apply (mbyte_munch (ms_segs B) W); [exact Hm | lia | exact (Ho _ Hs)]. }
  split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|]. split; [exact H11|].
  split.
  { intros a Ha Hs He. destruct (H12 a Ha Hs He) as [E1 E2]. pose proof (Hq a Hs He) as Hout.
    pose proof alloc_ceiling_value.
    split; [rewrite (mbyte_munch (ms_segs B) W mem1 mem2 a Hm ltac:(lia) Hout); exact E1|].
    rewrite E2. exact (writable_munch (ms_segs B) W mem1 mem2 a Hm ltac:(lia) Hout). }
  split.
  { intros a Ha Hn Hs He. destruct (H13 a Ha Hn Hs He) as [E1 E2].
    pose proof (proj1 HIL a Ha) as Har. pose proof (Hq a Hs He) as Hout.
    split; [rewrite (mbyte_munch (ms_segs B) W mem1 mem2 a Hm ltac:(lia) Hout); exact E1|].
    rewrite E2. exact (writable_munch (ms_segs B) W mem1 mem2 a Hm ltac:(lia) Hout). }
  split.
  { intros p n i Hin Hin1 Hi He. rewrite <- (H14 p n i Hin Hin1 Hi He).
    destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM0 Hin Hi) as (_ & R1 & R2 & _).
    apply (mbyte_munch (ms_segs B) W); [exact Hm | lia |]. apply g_out. intros Hn.
    destruct (HW _ Hn) as [[Hx|Hx] _]; [lia | exact (He Hx)]. }
  intros a Ha. unfold writable_at. apply Hw. exact (H15 a Ha).
Qed.

Lemma rp_call : img_low B -> forall K L A regs mem md E gone L1 A1 mem1 md1 K1 regs1 E1 g1 L2 A2 regs2 mem2 md2,
  aa_MR API L A mem md -> WF A -> alloc_ceiling + K <= spZ regs -> spZ regs <= 2 ^ 64 ->
  spZ regs - K <= spZ regs1 - K1 -> spZ regs1 <= spZ regs ->
  rpost B API K L A regs mem md E gone L1 A1 regs mem1 md1 ->
  call_post_k B (aa_MR API) K1 L1 A1 regs1 mem1 md1 E1 L2 A2 regs2 mem2 md2 ->
  (st_init_done A1 = true -> st_init_done A2 = true) ->
  (st_init_done A2 = false -> forall i, 0 <= i < 8 ->
     mbyte (ms_segs B) mem2 (ms_libc B + 8 + i) = mbyte (ms_segs B) mem1 (ms_libc B + 8 + i)) ->
  (length (st_regions A1) <= length (st_regions A2))%nat ->
  ublocks_kept L1 A1 A2 g1 ->
  (forall a, E1 a -> a < alloc_ceiling /\ (in_img B a -> E a)) ->
  (forall p n, In (p, n) (user_blocks A) -> (ptr_addr L p, n) = g1 -> gone (ptr_addr L p) n) ->
  (forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n -> gone (ptr_addr L p) n -> E (ptr_addr L p + i)) ->
  rpost B API K L A regs mem md E gone L2 A2 regs mem2 md2.
Proof.
  intros HIL K L A regs mem md E gone L1 A1 mem1 md1 K1 regs1 E1 g1 L2 A2 regs2 mem2 md2
    HM0 HWF0 Hsp Hsp2 Hk1 Hk2
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15)
    (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10) Hi Hav Hlen Hub HE1 Hg Hge.
  pose proof alloc_ceiling_lt as Hc.
  assert (Hscr : forall a, ~ scratch_k B K regs a -> ~ scratch_k B K1 regs1 a).
  { intros a Hs [Hx|Hx]; apply Hs; [left; lia | right; exact Hx]. }
  assert (Hlay : layout_le A L L2).
  { destruct H4 as (a1 & a2 & a3 & a4). destruct C4 as (b1 & b2 & b3 & b4).
    split; [congruence|]. split; [congruence|]. split; [congruence|].
    intros r Hr. rewrite (b4 r ltac:(lia)). exact (a4 r Hr). }
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact Hlay|].
  split; [intros Hd; exact (Hi (H5 Hd))|].
  split.
  { intros Hd i Hr. rewrite (Hav Hd i Hr). apply H6; [|exact Hr].
    destruct (st_init_done A1) eqn:Ed; [rewrite (Hi eq_refl) in Hd; discriminate | reflexivity]. }
  split; [lia|].
  split.
  { intros p n Hin Hng. pose proof (H8 p n Hin Hng) as Hin1. apply Hub; [exact Hin1|].
    rewrite (H9 p n Hin Hin1). intros Heq. exact (Hng (Hg p n Hin Heq)). }
  split; [intros p n Hin _; exact (g_ptr L L2 A p n HWF0 Hin Hlay)|].
  split; [exact H10|].
  split; [destruct C7 as (vm2 & ->); destruct H11 as (vm1 & ->); exists vm2; apply g_vm|].
  split.
  { intros a Ha Hs He. destruct (H12 a Ha Hs He) as [E1a E1w].
    assert (No1 : ~ owned B L1 A1 a) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ H1 Ho); lia).
    assert (No2 : ~ owned B L2 A2 a) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ C1 Ho); lia).
    destruct (C8 a (or_introl Ha) No1 No2 (Hscr a Hs) ltac:(intros HE; pose proof (proj1 (HE1 a HE)); lia))
      as [E2a E2w].
    split; [congruence | tauto]. }
  split.
  { intros a Ha Hn Hs He. destruct (H13 a Ha Hn Hs He) as [E1a E1w].
    destruct (C8 a (or_intror Ha) (Hn _ _ _ _ H1) (Hn _ _ _ _ C1) (Hscr a Hs)
      ltac:(intros HE; exact (He (proj2 (HE1 a HE) Ha)))) as [E2a E2w].
    split; [congruence | tauto]. }
  split.
  { intros p n i Hin Hin2 Hi' He.
    assert (Hng : ~ gone (ptr_addr L p) n) by (intros Hgo; exact (He (Hge p n i Hin Hi' Hgo))).
    pose proof (H8 p n Hin Hng) as Hin1.
    rewrite <- (H14 p n i Hin Hin1 Hi' He). rewrite <- (H9 p n Hin Hin1). exact (C9 p n i Hin1 Hin2 Hi'). }
  intros a Ha.
  assert (D : scratch_k B K1 regs1 a \/ ~ scratch_k B K1 regs1 a) by (unfold scratch_k; lia).
  destruct D as [D|D]; [exact (C10 a D)|].
  destruct Ha as [Ha|Ha]; [|exfalso; apply D; right; exact Ha].
  assert (No1 : ~ owned B L1 A1 a) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ H1 Ho); lia).
  assert (No2 : ~ owned B L2 A2 a) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ C1 Ho); lia).
  destruct (C8 a ltac:(left; lia) No1 No2 D ltac:(intros HE; pose proof (proj1 (HE1 a HE)); lia)) as [_ Ew].
  apply Ew. apply H15. left. exact Ha.
Qed.

End G.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.

Local Notation getr := YK11.getr.
Theorem grow_holds : U.Reusable.YL01.AllocExtra B (aa_MR API) -> fuzz_realloc_contract B API F -> grow_contract B API F.
Proof.
  intros AX FR. unfold grow_contract.
  intros L A regs mem md Lam peak cnt fail b v ty num str kids keys n cap
    HE HL Hres Ha0 Hv0 HH HSL HAP HPL HD Hcnt Hroom.
  destruct HE as (HSEG & Htp & Herrno & Hgot & Hguard & Hpre & Hsp47 & Hglob & Hfrm & HRD).
  destruct HRD as (Hro0 & _ & _).
  pose proof (g_img B HSEG) as HIL.
  pose proof Hpre as (HMR & HWF & Hbd & Hra & Hsp16 & Hspc & Hsp63 & Hstk & Htpr & Herr & Haux).
  pose proof alloc_ceiling_value as Hceil.
  assert (HGK : GROW_K = 8352) by reflexivity.
  assert (HRS : REALLOC_STACK = 8256) by reflexivity.
  assert (HSP : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as HSPr. unfold bv_modulus in HSPr.
  unfold U.Prog.strtod_c.STRTOD_GLOBALS_TOP in Hglob.
  pose proof HH as ((Hv8 & HvS) & (Hty & Bty) & (Hnum & Bnum) & (Hstr & Bstr) & (Hkid & Bkid) & (Hkey & Bkey) &
    (Hn & Bn) & (Hcap & Bcap)).
  destruct HSL as (Hty56 & (Hnc & Hc54) & Hcap0 & Hcapp).
  destruct HPL as (Hplace & Hauxv & Hvx).
  cbn [Frame.disjoint_from] in HD.
  assert (Hvsx : forall x, v <= x < v + 56 -> ~ static_owned B x /\ ~ alloc_statics x /\
      ~ (errno_addr B <= x < errno_addr B + 4) /\ ~ in_img B x).
  { intros x Hx. destruct (Hvx (x - v) ltac:(lia)) as (H1 & H2 & H3 & H4). replace (v + (x - v)) with x in * by lia.
    split; [intros Hs; exact (H1 (or_intror Hs))|]. split; [exact H2|]. split; [exact H3 | exact H4]. }
  pose proof HvS as (HvS0 & HvS1 & HvS2).
  assert (Hvm : forall x, v <= x < v + 56 -> writable_at (ms_segs B) mem x /\ mbyte (ms_segs B) mem x <> None).
  { intros x Hx. destruct (HvS2 x Hx) as (Hw & bb & Hb). split; [exact Hw|]. intros Hn0.
    assert (Eb : mbyte (ms_segs B) mem x = Some bb) by exact Hb. congruence. }
  destruct (g_vloc0 B API L A mem md Lam peak cnt fail (spZ regs) v ty kids keys cap HMR HL ltac:(lia) Hplace HAP
    ltac:(lia) Hcapp) as (r & rk & HV0 & Hrk & Hrky).
  assert (HK48 : stk rsegs mem (spZ regs - 48) (spZ regs)).
  { assert (HK : stk (ms_segs B) mem (spZ regs - GROW_K) (spZ regs)) by (apply (kb_stk B API HIL _ L A regs mem md Hpre); lia).
    destruct (stk_split _ mem _ (spZ regs - 48) (spZ regs) HK ltac:(lia)) as [_ H]. rewrite <- HSEG. exact H. }
  assert (HRA : forall m2, munch [(spZ regs - 48, spZ regs)] mem m2 -> wmono rsegs mem m2 ->
     rpost B API GROW_K L A regs mem md (grow_writes v ty kids keys n cap) (grow_gone ty kids keys n cap) L A regs m2 md).
  { intros m2 Hm Hw. rewrite <- HSEG in Hw.
    apply (rp_A B API HIL GROW_K L A regs mem md _ _ L A mem md m2 _ HMR ltac:(lia) (rp_refl B API _ _ _ _ _ _ _ _ Hpre) Hm Hw).
    - intros x Hx Ho. exfalso. pose proof (g_nout1 _ _ _ Ho). lia.
    - intros x Ho. pose proof (g_nout1 _ _ _ Ho) as Hx. split; [left; lia|].
      intros Hown. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HMR Hown). lia. }
  assert (HLA : forall m2, munch [(spZ regs - 48, spZ regs)] mem m2 -> ledger B L A m2 Lam peak cnt fail).
  { intros m2 Hm. apply (g_ledger_munch B API L A mem md m2 Lam peak cnt fail _ HMR HL Hm).
    intros x Ho. pose proof (g_nout1 _ _ _ Ho) as Hx. split.
    - unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. lia.
    - intros a k Hin. pose proof (ledger_block_range B API L A mem md Lam peak cnt fail a k HMR HL Hin).
      pose proof HL as (_ & _ & _ & _ & _ & HF0). rewrite Forall_forall in HF0. destruct (HF0 _ Hin) as (Hk0 & _).
      cbn [snd] in Hk0. lia. }
  assert (HROA : forall m2, munch [(spZ regs - 48, spZ regs)] mem m2 -> U.MemNorm.ro_agree (ms_segs B) m2).
  { intros m2 Hm. apply (g_ro_munch B _ mem m2 Hro0 Hm). intros a Ha Ho. pose proof (g_nout1 _ _ _ Ho).
    apply (g_ro_low B HIL). lia. }
  assert (HMA : forall m2, munch [(spZ regs - 48, spZ regs)] mem m2 -> forall x, 0 <= x < 2 ^ 64 ->
     ~ (spZ regs - 48 <= x < spZ regs) -> mbyte (ms_segs B) m2 x = mbyte (ms_segs B) mem x).
  { intros m2 Hm x Hx Hn0. apply (mbyte_munch (ms_segs B) _ mem m2 x Hm Hx). cbn [Frame.outside]. split; [lia | exact I]. }
  destruct (kb_md B API L A mem md HMR) as (Hh0 & Hz0).
  apply (kb_run B regs _ mem md
    (fun R pc' mem' => seg1_post (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 8) (getr regs 9)
       (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
       (getr regs 25) (getr regs 26) (getr regs 27) fp_regs fp_csr mem v kids n cap
       (MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs))) _ Hh0 Hz0).
  { unfold rmk. rewrite HSEG. eapply evt_mono.
    - apply (grow_seg1 (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
        (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
        (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
        (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
        (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr mem v kids n cap Ha0 Hv0 Hv8
        ltac:(destruct HvS as (HvP & _); exact HvP));
        [rewrite <- HSEG; exact Bkid | rewrite <- HSEG; exact Bn | rewrite <- HSEG; exact Bcap | lia | lia | lia
        | exact HK48 | lia | lia].
    - intros ms Hp. pose proof Hp as Hp'. apply seg1_shape in Hp'. destruct Hp' as (R & pc' & mm & ->).
      exists R, pc', mm. split; [reflexivity | exact Hp]. }
  intros R pc1 mem1 regs1 HK1 Hg1.
  unfold seg1_post in HK1.
  destruct HK1 as [(Hlt & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & E & MU & WM)
                  |(Heq & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & m' & j & E & MU & WM & FR1)];
    pose proof (f_equal ms_regs E) as ER; pose proof (f_equal ms_pc_val E) as EP; pose proof (f_equal ms_mem E) as EM;
    cbn [ms_regs ms_pc_val ms_mem MS] in ER, EP, EM; subst R pc1 mem1; clear E.
  - pose proof (HRA m' MU WM) as HR1.
    apply SR_ret. exists L, A, regs1, m', md, Lam, peak, cnt, fail, b, 0.
    split; [rewrite (kb_ret_pc _ Hra); reflexivity|].
    split; [eapply rp_regs; [exact HR1 | cs_cases ltac:(rewrite Hg1; reflexivity)]|].
    split.
    { split; [exact (HROA m' MU)|]. pose proof HR1 as (HM1' & _).
      destruct (U.Reusable.YL01.ax_statics AX L A m' md HM1') as (Hg & (g & _ & Hgw) & _). split; [exact Hg | exists g; exact Hgw]. }
    split; [rewrite Hg1; reflexivity|].
    split; [exact (HLA m' MU)|].
    split; [exact Hres|].
    left. split; [exact Hlt|]. do 8 (split; [reflexivity|]).
    apply (pj_hdr_eq (ms_segs B) mem m' v ty num str kids keys n cap HH).
    intros x Hx. apply MU. cbn [Frame.outside]. split; [lia | exact I].
  - subst n. rewrite <- HSEG in WM.
    pose proof (HRA m' MU) as HR1. rewrite <- HSEG in HR1. specialize (HR1 WM). pose proof HR1 as (HMR1 & _).
    pose proof (HLA m' MU) as HL1. pose proof (HROA m' MU) as Hro1. pose proof (HMA m' MU) as HM1.
    assert (G1 : getr regs1 1 = Z_to_bv 64 0x1676c) by (rewrite Hg1; reflexivity).
    assert (G2 : getr regs1 2 = Z_to_bv 64 (spZ regs - 48)) by (rewrite Hg1; reflexivity).
    assert (G8 : getr regs1 8 = Z_to_bv 64 v) by (rewrite Hg1; reflexivity).
    assert (G9 : getr regs1 9 = getr regs 9) by (rewrite Hg1; reflexivity).
    assert (G10 : getr regs1 10 = Z_to_bv 64 kids) by (rewrite Hg1; reflexivity).
    assert (G11 : getr regs1 11 = Z_to_bv 64 (56 * cap2 cap)) by (rewrite Hg1; reflexivity).
    assert (G18 : getr regs1 18 = Z_to_bv 64 (8 * cap2 cap)) by (rewrite Hg1; reflexivity).
    assert (G19 : getr regs1 19 = Z_to_bv 64 (cap2 cap)) by (rewrite Hg1; reflexivity).
    assert (Hs1 : spZ regs1 = spZ regs - 48) by (unfold spZ at 1; rewrite G2, unsigned_lit by lia; reflexivity).
    destruct (Hroom eq_refl) as (Hrm1 & Hsz & Hrm2).
    pose proof (cap2_range cap ltac:(lia)) as Hc2.
    assert (Hkb : (cap = 0 /\ kids = 0) \/ (0 < cap /\ In (kids, 56 * cap) Lam)).
    { destruct (Z.eq_dec cap 0) as [Hc0|Hc0]; [left; split; [exact Hc0 | exact (proj1 (Hcap0 Hc0))]|].
      right. split; [lia | exact (proj1 (Hcapp ltac:(lia)))]. }
    pose proof HL as (_ & _ & Hcr & _ & _ & HFL). rewrite Forall_forall in HFL.
    assert (Hkr : cap = 0 \/ (0 < cap /\ 4112 <= kids /\ kids + 56 * cap <= alloc_ceiling /\
        In (kids - 16, 56 * cap + 16) (blocks L A))).
    { destruct Hkb as [(Hc0 & _)|(Hcp & Hin)]; [left; exact Hc0|right].
      pose proof (ledger_block_range B API L A mem md Lam peak cnt fail _ _ HMR HL Hin) as (R1 & R2 & _).
      destruct (HFL _ Hin) as (_ & Hb & _). cbn [fst snd] in Hb. split; [lia|]. split; [lia|]. split; [lia | exact Hb]. }
    assert (Hkyr : ty = 6 -> cap = 0 \/ (0 < cap /\ 4112 <= keys /\ keys + 8 * cap <= alloc_ceiling /\
        In (keys, 8 * cap) Lam /\ In (keys - 16, 8 * cap + 16) (blocks L A))).
    { intros Ht6. destruct (Z.eq_dec cap 0) as [Hc0|Hc0]; [left; exact Hc0|right].
      pose proof (proj2 (Hcapp ltac:(lia)) Ht6) as Hin.
      pose proof (ledger_block_range B API L A mem md Lam peak cnt fail _ _ HMR HL Hin) as (R1 & R2 & _).
      destruct (HFL _ Hin) as (_ & Hb & _). cbn [fst snd] in Hb. split; [lia|]. split; [lia|]. split; [lia|].
      split; [exact Hin | exact Hb]. }
    assert (Hold0 : forall i, 0 <= i < 56 * cap -> mbyte (ms_segs B) m' (kids + i) <> None).
    { intros i Hi. destruct Hkb as [(Hc0 & _)|(Hcp & Hin)]; [lia|].
      destruct (ledger_block_present B API L A m' md Lam peak cnt fail kids (56 * cap) i HMR1 HL1 Hin Hi) as (bb & Hbb).
      unfold mbyte. rewrite Hbb. discriminate. }
    destruct (g_old (ms_segs B) m' kids (56 * cap) ltac:(lia) Hold0) as (old & Hlo & Hold).
    eapply SR_bind; [apply (FR L A regs1 m' md kids (56 * cap) (56 * cap2 cap) old b Lam peak cnt fail) |].
    { eapply (kb_pre_A B API GROW_K 48 (REALLOC_STACK + 48) L A regs mem md regs1 m');
        [exact Hpre | lia | lia | lia | exact Hs1 | | rewrite Hg1; reflexivity | | exact MU | exact WM | | ].
      - rewrite Hs1. replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16.
      - rewrite G1. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity.
      - intros x Hx Hs. cbn [Frame.outside]. split; [lia | exact I].
      - intros x Hx Ho. cbn [Frame.outside]. split; [lia | exact I]. }
    { exact G10. }
    { exact G11. }
    { lia. }
    { exact HL1. }
    { exact Hro1. }
    { destruct Hkb as [(-> & ->)|(_ & Hin)]; [left; split; reflexivity | right; exact Hin]. }
    { exact Hlo. }
    { exact Hold. }
    { exact Hres. }
    { exact Hrm1. }
    { lia. }
    intros cc2 HC2.
    destruct HC2 as (L2 & A2 & regs2 & mem2 & md2 & res & -> & Hro2 & _ & Hin2 & Hav2 & Hpost2 & Hlen2 & Hr2 & _ & Harm2).
    pose proof Hpost2 as (HMR2 & HWF2 & Hbd2 & Hle2 & Hptr2 & Hp12 & (vm2 & Emd2) & Hfr2 & Hblk2 & Hscr2).
    assert (Hresr : res = 0 \/ (4112 <= res /\ res + 56 * cap2 cap <= alloc_ceiling /\
        (forall i, 0 <= i < 56 * cap2 cap + 16 -> ~ in_img B (res - 16 + i)))).
    { destruct Harm2 as [(_ & Hr0 & _)|(_ & _ & _ & _ & Himg & _ & _ & _ & l1 & l2 & _ & _ & HLn)]; [left; exact Hr0|].
      right. pose proof (ledger_block_range B API L2 A2 mem2 md2 _ _ _ _ res (56 * cap2 cap) HMR2 HLn (in_eq _ _))
        as (R1 & R2 & _).
      split; [lia|]. split; [lia | exact Himg]. }
    assert (HE1 : forall a, realloc_writes kids (56 * cap) res a -> a < alloc_ceiling /\
        (in_img B a -> grow_writes v ty kids keys cap cap a)).
    { intros a [Ha|[(Hk0 & Ha)|(Hr0 & Ha)]].
      - split; [unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha; lia|]. intros _. split; [reflexivity|].
        right; right; right; exact Ha.
      - destruct Hkr as [Hc0|(Hcp & R1 & R2 & Hb)]; [destruct Hkb as [(_ & Hk)|(Hcp & _)]; lia|].
        split; [lia|]. intros _. split; [reflexivity|]. right; right; left.
        exists kids, (56 * cap). split; [|lia]. apply in_or_app. left. unfold kids_blk.
        rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left. reflexivity.
      - destruct Hresr as [Hr00|(R1 & R2 & Ri)]; [lia|]. split; [lia|]. intros Hi. exfalso.
        apply (Ri (a - res + 16)); [lia|]. replace (res - 16 + (a - res + 16)) with a by lia. exact Hi. }
    assert (Hug : exists g1, ublocks_kept L A A2 g1 /\ (g1 = (0, 0) \/ g1 = (kids - 16, 56 * cap + 16))).
    { destruct Harm2 as [(_ & _ & _ & _ & _ & _ & _ & _ & _ & Hub & _)|(_ & _ & _ & _ & _ & _ & Hub & _)].
      - exists (0, 0). split; [exact Hub | left; reflexivity].
      - exists (kids - 16, 56 * cap + 16). split; [exact Hub | right; reflexivity]. }
    destruct Hug as (g1 & Hub1 & Hg1v).
    assert (Hrg1 : (r, rk) <> g1).
    { destruct Hg1v as [->| ->]; [|exact Hrk]. intros Eq. injection Eq as E1 E2. subst r rk.
      destruct HV0 as [(_ & _ & _ & E')|(Hin & _)]; [lia|].
      pose proof (g_blk_range B API L A mem md 0 0 HMR Hin). lia. }
    assert (HR2 : rpost B API GROW_K L A regs mem md (grow_writes v ty kids keys cap cap) (grow_gone ty kids keys cap cap)
        L2 A2 regs mem2 md2).
    { apply (rp_call B API HIL GROW_K L A regs mem md _ _ L A m' md (REALLOC_STACK + 48) regs1 _ g1 L2 A2 regs2 mem2 md2
        HMR HWF ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HR1 Hpost2 Hin2 Hav2 Hlen2 Hub1 HE1).
      - intros p nn Hp Heq. destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p nn HMR Hp) as (P1 & P2).
        destruct Hg1v as [->| ->]; injection Heq as E1 E2; [lia|].
        split; [reflexivity|]. unfold freed. destruct Hkr as [Hc0|(Hcp & R1 & R2 & Hb)].
        + destruct Hkb as [(_ & Hk)|(Hcp & _)]; lia.
        + apply in_or_app. left. unfold kids_blk. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left. f_equal; lia.
      - intros p nn i Hp Hi (_ & Hfr). split; [reflexivity|]. right; right; left.
        exists (ptr_addr L p + 16), (nn - 16). split; [exact Hfr | lia]. }
    assert (HVB : forall x, v <= x < v + 56 ->
       mbyte (ms_segs B) mem2 x = mbyte (ms_segs B) mem x /\ writable_at (ms_segs B) mem2 x).
    { intros x Hx. destruct (Hvsx x Hx) as (_ & _ & Hxe & _).
      destruct (vloc_bytes B API L A Lam (spZ regs) v r rk _ regs1 m' md _ L2 A2 regs2 mem2 md2 g1 x HV0 HMR1 Hpost2
        Hub1 Hrg1 ltac:(lia) ltac:(lia) (fun a Ha => proj1 (HE1 a Ha)) Hxe Hx) as (E1 & E2).
      assert (Ex : mbyte (ms_segs B) m' x = mbyte (ms_segs B) mem x) by (apply HM1; lia).
      split; [congruence|]. apply E2. apply WM. exact (proj1 (Hvm x Hx)). }
    assert (HFC : forall x, spZ regs - 48 <= x < spZ regs ->
       mbyte (ms_segs B) mem2 x = mbyte (ms_segs B) m' x /\
       (writable_at (ms_segs B) m' x -> writable_at (ms_segs B) mem2 x)).
    { intros x Hx.
      assert (No1 : ~ owned B L A x) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HMR1 Ho); lia).
      assert (No2 : ~ owned B L2 A2 x) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HMR2 Ho); lia).
      destruct (Hfr2 x ltac:(left; lia) No1 No2
        ltac:(unfold scratch_k; rewrite Hs1, Herrno; unfold U.Prog.strtod_c.STRTOD_ERRNO; lia)
        ltac:(intros HE; pose proof (proj1 (HE1 x HE)); lia)) as [E1 E2].
      split; [exact E1 | apply E2]. }
    assert (G2' : getr regs2 2 = Z_to_bv 64 (spZ regs - 48)) by (rewrite <- G2; apply (Hp12 2); unfold callee_saved; lia).
    assert (G8' : getr regs2 8 = Z_to_bv 64 v) by (rewrite <- G8; apply (Hp12 8); unfold callee_saved; lia).
    assert (G9' : getr regs2 9 = getr regs 9) by (rewrite <- G9; apply (Hp12 9); unfold callee_saved; lia).
    assert (G18' : getr regs2 18 = Z_to_bv 64 (8 * cap2 cap)) by (rewrite <- G18; apply (Hp12 18); unfold callee_saved; lia).
    assert (G19' : getr regs2 19 = Z_to_bv 64 (cap2 cap)) by (rewrite <- G19; apply (Hp12 19); unfold callee_saved; lia).
    assert (Hs2 : bv_unsigned (getr regs2 2) = spZ regs - 48) by (rewrite G2', unsigned_lit by lia; reflexivity).
    assert (HRR : 0 <= res < 2 ^ 64) by (destruct Hresr as [->|(R1 & R2 & _)]; lia).
    rewrite G1.
    destruct (kb_md B API L2 A2 mem2 md2 HMR2) as (Hh2 & Hz2).
    apply (kb_run B regs2 _ mem2 md2
      (fun R pc' mem' => seg2_post (getr regs 1) (getr regs2 2) (getr regs2 3) (getr regs2 4) (getr regs 8) (getr regs 9)
         (getr regs 18) (getr regs 19) (getr regs2 20) (getr regs2 21) (getr regs2 22) (getr regs2 23) (getr regs2 24)
         (getr regs2 25) (getr regs2 26) (getr regs2 27) fp_regs fp_csr mem2 v ty keys (cap2 cap) res j
         (MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs))) _ Hh2 Hz2).
    { unfold rmk. rewrite HSEG. eapply evt_mono.
      - apply (grow_seg2 (getr regs2 1) (getr regs2 2) (getr regs2 3) (getr regs2 4) (getr regs2 5) (getr regs2 6)
          (getr regs2 7) (getr regs2 8) (getr regs2 9) (getr regs2 10) (getr regs2 11) (getr regs2 12) (getr regs2 13)
          (getr regs2 14) (getr regs2 15) (getr regs2 16) (getr regs2 17) (getr regs2 18) (getr regs2 19) (getr regs2 20)
          (getr regs2 21) (getr regs2 22) (getr regs2 23) (getr regs2 24) (getr regs2 25) (getr regs2 26) (getr regs2 27)
          (getr regs2 28) (getr regs2 29) (getr regs2 30) (getr regs2 31) fp_regs fp_csr mem2 v ty keys (cap2 cap) res j
          (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) Hr2 G8' G18' G19' HRR).
        + lia.
        + exact Hty56.
        + rewrite <- HSEG. apply (g_bytes B mem); [exact Bty|]. intros x Hx. rewrite length_le4 in Hx.
          exact (proj1 (HVB x ltac:(lia))).
        + rewrite <- HSEG. apply (g_bytes B mem); [exact Bkey|]. intros x Hx. rewrite length_le8 in Hx.
          exact (proj1 (HVB x ltac:(lia))).
        + rewrite <- HSEG. apply (g_wr B); [lia | lia|]. intros i Hi. exact (proj2 (HVB (v + i) ltac:(lia))).
        + rewrite Hs2. rewrite <- HSEG. apply (g_rw_cells B m'); [rewrite HSEG; exact FR1|].
          intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply HFC. lia.
        + rewrite Hs2. lia.
      - intros ms Hp. pose proof Hp as Hp'. apply seg2_shape in Hp'. destruct Hp' as (R & pc' & mm & ->).
        exists R, pc', mm. split; [reflexivity | exact Hp]. }
    intros R pc3 mem3 regs3 HK3 Hg3. unfold seg2_post in HK3.
    destruct HK3 as [(Hr0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & E)
                    |[(Hrnz & Hty5 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m3 & E &
                       MU3 & WM3 & PM3 & BW1 & BW2)
                     |(Hrnz & Hty6 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m3 & E &
                       MU3 & WM3 & PM3 & BW1 & FR3)]];
      pose proof (f_equal ms_regs E) as ER; pose proof (f_equal ms_pc_val E) as EP; pose proof (f_equal ms_mem E) as EM;
      cbn [ms_regs ms_pc_val ms_mem MS] in ER, EP, EM; subst R pc3 mem3; clear E.
    + destruct Harm2 as [(Hcf & _ & _ & _ & _ & Hrf2 & _ & _ & Hkeeps & _ & HLn)|(_ & Hrnz & _)]; [|lia].
      apply SR_ret. exists L2, A2, regs3, mem2, md2, Lam, peak, ((cnt + 1) mod 2 ^ 64), (2 ^ 64 - 1), b, (-1).
      split; [rewrite (kb_ret_pc _ Hra); reflexivity|].
      split.
      { eapply rp_regs; [exact HR2|].
        cs_cases ltac:(rewrite Hg3; first
          [ reflexivity
          | match goal with |- getr _ (Z_to_bv 5 2) = _ =>
              transitivity (Z_to_bv 64 (bv_unsigned (getr regs2 2) + 48)); [reflexivity|];
              rewrite Hs2; replace (spZ regs - 48 + 48) with (spZ regs) by lia; apply Step.Z_to_bv_lit_self end
          | match goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
              transitivity (getr regs2 (Z_to_bv 5 k)); [reflexivity|];
              rewrite (Hp12 k ltac:(unfold callee_saved; lia)), Hg1; reflexivity end ]). }
      split.
      { split; [exact Hro2|]. destruct (U.Reusable.YL01.ax_statics AX L2 A2 mem2 md2 HMR2) as (Hg & (g & _ & Hgw) & _).
        split; [exact Hg | exists g; exact Hgw]. }
      split; [rewrite Hg3; reflexivity|].
      split; [exact HLn|].
      split; [exact Hrf2|].
      right; left.
      split; [reflexivity|]. split; [exact Hcf|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [rewrite Z.mod_small by lia; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split.
      { apply (g_hdr B mem mem2 v ty num str kids keys cap cap kids keys cap HH).
        - intros x Hx. destruct (HVB x Hx) as (E1 & E2). split; [exact E2|]. rewrite E1. exact (proj2 (Hvm x Hx)).
        - intros x Hx. exact (proj1 (HVB x ltac:(lia))).
        - split; [exact Hkid|]. apply (g_bytes B mem); [exact Bkid|]. intros x Hx. rewrite length_le8 in Hx.
          exact (proj1 (HVB x ltac:(lia))).
        - split; [exact Hkey|]. apply (g_bytes B mem); [exact Bkey|]. intros x Hx. rewrite length_le8 in Hx.
          exact (proj1 (HVB x ltac:(lia))).
        - split; [exact Hcap|]. apply (g_bytes B mem); [exact Bcap|]. intros x Hx. rewrite length_le8 in Hx.
          exact (proj1 (HVB x ltac:(lia))). }
      split.
      { intros i Hi. destruct Hkr as [Hc0|(Hcp & R1 & R2 & Hb)]; [lia|].
        pose proof (Hkeeps (kids - 16) (56 * cap + 16) (i + 16) Hb ltac:(lia) ltac:(lia)) as Ek.
        replace (kids - 16 + (i + 16)) with (kids + i) in Ek by lia. rewrite Ek. apply HM1; lia. }
      { intros Ht6 i Hi. destruct (Hkyr Ht6) as [Hc0|(Hcp & R1 & R2 & Hin & Hb)]; [lia|].
        pose proof (Hkeeps (keys - 16) (8 * cap + 16) (i + 16) Hb ltac:(lia) ltac:(lia)) as Ek.
        replace (keys - 16 + (i + 16)) with (keys + i) in Ek by lia. rewrite Ek. apply HM1; lia. }
    + destruct Harm2 as [(_ & Hr0 & _)|(Hcf & _ & Hr16 & Hrst & Himg & Hkeeps & Hub & Hold2 & l1 & l2 & Hsh & Hnin & HLn)];
        [lia|].
      subst ty. rewrite <- HSEG in WM3, BW1, BW2.
      destruct Hresr as [Hr00|(Rr1 & Rr2 & Ri)]; [lia|].
      assert (Hsh' : kids = 0 /\ (exists b1 b2, blocks L2 A2 = b1 ++ (res - 16, 56 * cap2 cap + 16) :: b2 /\
            blocks L A = b1 ++ b2)
          \/ kids <> 0 /\ (exists b1 b2 c1 c2, blocks L A = b1 ++ (kids - 16, 56 * cap + 16) :: b2 /\
            blocks L2 A2 = c1 ++ (res - 16, 56 * cap2 cap + 16) :: c2 /\ c1 ++ c2 = b1 ++ b2)).
      { destruct Hsh as [(H1 & _ & _ & _ & H2)|(H1 & _ & _ & H2)]; [left | right]; split; assumption. }
      destruct (g_fresh B API L A L2 A2 mem2 md2 kids (56 * cap) res (56 * cap2 cap) HMR2 ltac:(lia) Hsh')
        as (Hfr & Hnb); [intros Eq; injection Eq; lia|].
      assert (HLsub : forall a k, In (a, k) ((res, 56 * cap2 cap) :: l1 ++ l2) ->
          In (a, k) Lam \/ ~ In (a - 16, k + 16) (blocks L A)).
      { intros a k [Eq|Hin]; [injection Eq as <- <-; right; exact Hfr|left].
        destruct Hsh as [(_ & -> & -> & _)|(_ & -> & _)]; [exact Hin|].
        apply in_app_or in Hin. apply in_or_app. destruct Hin as [Hin|Hin]; [left; exact Hin | right; right; exact Hin]. }
      pose proof (vloc_call B API L A Lam (spZ regs) v r rk _ regs1 m' md _ L2 A2 regs2 mem2 md2 _ _ _ _ _
        HV0 Hpost2 Hub Hrk HLn HLsub) as HV2.
      assert (HR3 : rpost B API GROW_K L A regs mem md (grow_writes v 5 kids keys cap cap) (grow_gone 5 kids keys cap cap)
          L2 A2 regs m3 md2).
      { apply (rp_A B API HIL GROW_K L A regs mem md _ _ L2 A2 mem2 md2 m3 _ HMR ltac:(lia) HR2 MU3 WM3).
        - intros x Hx Ho Hn0. exact (PM3 _ Hn0).
        - intros x Ho. pose proof (g_nout2 _ _ _ _ _ Ho) as Hx. split.
          + right. split; [reflexivity|]. destruct Hx as [Hx|Hx]; [left; lia | right; left; lia].
          + apply (vloc_own B API L2 A2 _ mem2 md2 (spZ regs) v r rk x HV2 HMR2); [lia | lia |].
            exact (proj1 (Hvsx x ltac:(lia))). }
      assert (Hro3 : U.MemNorm.ro_agree (ms_segs B) m3).
      { apply (g_ro_munch B _ mem2 m3 Hro2 MU3). intros a Ha Ho. pose proof (g_nout2 _ _ _ _ _ Ho).
        apply (g_ro_notimg B HSEG); [lia|]. exact (proj2 (proj2 (proj2 (Hvsx a ltac:(lia))))). }
      assert (HL3 : ledger B L2 A2 m3 ((res, 56 * cap2 cap) :: l1 ++ l2)
          (Z.max peak (lsum (l1 ++ l2) + 56 * cap2 cap)) ((cnt + 1) mod 2 ^ 64) fail).
      { apply (g_ledger_munch B API L2 A2 mem2 md2 m3 _ _ _ _ _ HMR2 HLn MU3).
        intros x Ho. pose proof (g_nout2 _ _ _ _ _ Ho) as Hx. split; [exact (proj1 (proj2 (Hvsx x ltac:(lia))))|].
        intros a k Hin Ha.
        destruct (vloc_heads B API L2 A2 _ mem2 md2 _ _ _ (spZ regs) v r rk a k HV2 HMR2 HLn ltac:(lia) Hin); lia. }
      assert (Hmv : forall i, 0 <= i < 56 * cap -> mbyte (ms_segs B) m3 (res + i) = mbyte (ms_segs B) mem (kids + i)).
      { intros i Hi.
        destruct Hkr as [Hc0|(Hcp & Rk1 & Rk2 & Hb)]; [lia|].
        assert (Hne : (res - 16, 56 * cap2 cap + 16) <> (r, rk)).
        { intros Eq. apply (vloc_ne L A Lam (spZ regs) v r rk _ _ HV0 Hfr ltac:(lia)). symmetry. exact Eq. }
        assert (Hout : res + i < v \/ v + 56 <= res + i).
        { apply (vloc_disj B API L2 A2 _ mem2 md2 (spZ regs) v r rk (res - 16) (56 * cap2 cap + 16) (res + i)
            HV2 HMR2 ltac:(lia) Hnb Hne). lia. }
        assert (Ho3 : Frame.outside [(v + 24, v + 32); (v + 48, v + 56)] (res + i))
          by (cbn [Frame.outside]; refine (conj _ (conj _ I)); lia).
        rewrite (mbyte_munch (ms_segs B) _ mem2 m3 (res + i) MU3 ltac:(lia) Ho3).
        rewrite (Hold2 i ltac:(lia)), <- (Hold i Hi). apply HM1; lia. }
      apply SR_ret. exists L2, A2, regs3, m3, md2, ((res, 56 * cap2 cap) :: l1 ++ l2),
        (Z.max peak (lsum (l1 ++ l2) + 56 * cap2 cap)), ((cnt + 1) mod 2 ^ 64), fail,
        (rf_grow F b (56 * cap) (56 * cap2 cap)), 0.
      split; [rewrite (kb_ret_pc _ Hra); reflexivity|].
      split.
      { eapply rp_regs; [exact HR3|].
        cs_cases ltac:(rewrite Hg3; first
          [ reflexivity
          | match goal with |- getr _ (Z_to_bv 5 2) = _ =>
              transitivity (Z_to_bv 64 (bv_unsigned (getr regs2 2) + 48)); [reflexivity|];
              rewrite Hs2; replace (spZ regs - 48 + 48) with (spZ regs) by lia; apply Step.Z_to_bv_lit_self end
          | match goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
              transitivity (getr regs2 (Z_to_bv 5 k)); [reflexivity|];
              rewrite (Hp12 k ltac:(unfold callee_saved; lia)), Hg1; reflexivity end ]). }
      split.
      { split; [exact Hro3|]. pose proof HR3 as (HM3' & _).
        destruct (U.Reusable.YL01.ax_statics AX L2 A2 m3 md2 HM3') as (Hg & (g & _ & Hgw) & _).
        split; [exact Hg | exists g; exact Hgw]. }
      split; [rewrite Hg3; reflexivity|].
      split; [exact HL3|].
      split.
      { destruct Hsh as [(Hk0 & _ & _ & Hrf & _)|(Hk0 & _ & Hrf & _)]; unfold rf_grow.
        - destruct Hkr as [Hc0|(Hcp & Rk1 & _)]; [|lia].
          rewrite (proj2 (Z.eqb_eq (56 * cap) 0)) by lia. exact Hrf.
        - destruct Hkr as [Hc0|(Hcp & _)]; [destruct Hkb as [(_ & Hk)|(Hcp & _)]; lia|].
          rewrite (proj2 (Z.eqb_neq (56 * cap) 0)) by lia. exact Hrf. }
      right; right; left.
      split; [reflexivity|]. split; [exact Hcf|]. split; [lia|]. split; [reflexivity|].
      exists res, (l1 ++ l2).
      split; [lia|]. split; [exact Hr16|].
      split; [intros a k [Eq|[]]; injection Eq as <- <-; exact Hfr|].
      split.
      { destruct Hsh as [(Hk0 & -> & -> & _)|(Hk0 & ELam & _)].
        - destruct Hkr as [Hc0|(Hcp & Rk1 & _)]; [|lia]. unfold kids_blk. rewrite (proj2 (Z.eqb_eq cap 0) Hc0).
          cbn [app]. apply Permutation_refl.
        - destruct Hkr as [Hc0|(Hcp & _)]; [destruct Hkb as [(_ & Hk)|(Hcp & _)]; lia|].
          unfold kids_blk. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. rewrite ELam. cbn [app].
          apply Permutation_sym, Permutation_middle. }
      split; [apply Permutation_refl|].
      split; [cbn [lsum]; lia|].
      split; [rewrite Z.mod_small by lia; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [exact Hmv|].
      split.
      { apply (g_hdr B mem m3 v 5 num str kids keys cap cap res keys (cap2 cap) HH).
        - intros x Hx. split.
          + apply WM3. exact (proj2 (HVB x Hx)).
          + destruct (kb_outside_dec [(v + 24, v + 32); (v + 48, v + 56)] x) as [Ho|Ho].
            * rewrite (mbyte_munch (ms_segs B) _ mem2 m3 x MU3 ltac:(lia) Ho), (proj1 (HVB x Hx)).
              exact (proj2 (Hvm x Hx)).
            * destruct (g_nout2 _ _ _ _ _ Ho) as [Hx'|Hx'].
              -- apply (g_bytes_some B m3 (v + 24) _ x BW1). rewrite length_le8. lia.
              -- apply (g_bytes_some B m3 (v + 48) _ x BW2). rewrite length_le8. lia.
        - intros x Hx.
          assert (Ho3 : Frame.outside [(v + 24, v + 32); (v + 48, v + 56)] x)
            by (cbn [Frame.outside]; refine (conj _ (conj _ I)); lia).
          rewrite (mbyte_munch (ms_segs B) _ mem2 m3 x MU3 ltac:(lia) Ho3). exact (proj1 (HVB x ltac:(lia))).
        - split; [lia | exact BW1].
        - split; [exact Hkey|]. apply (g_bytes B mem); [exact Bkey|]. intros x Hx. rewrite length_le8 in Hx.
          assert (Ho3 : Frame.outside [(v + 24, v + 32); (v + 48, v + 56)] x)
            by (cbn [Frame.outside]; refine (conj _ (conj _ I)); lia).
          rewrite (mbyte_munch (ms_segs B) _ mem2 m3 x MU3 ltac:(lia) Ho3). exact (proj1 (HVB x ltac:(lia))).
        - split; [lia | exact BW2]. }
      split; [left; reflexivity|]. split; [lia|]. split; [lia|].
      intros _. split; [unfold lin; left; reflexivity | lia].
    + destruct Harm2 as [(_ & Hr0 & _)|(Hcf & _ & Hr16 & Hrst & Himg & Hkeeps & Hub & Hold2 & l1 & l2 & Hsh & Hnin & HLn)];
        [lia|].
      subst ty. rewrite <- HSEG in WM3, BW1, FR3. rewrite Hs2 in FR3.
      destruct Hresr as [Hr00|(Rr1 & Rr2 & Ri)]; [lia|].
      assert (Hsh' : kids = 0 /\ (exists b1 b2, blocks L2 A2 = b1 ++ (res - 16, 56 * cap2 cap + 16) :: b2 /\
            blocks L A = b1 ++ b2)
          \/ kids <> 0 /\ (exists b1 b2 c1 c2, blocks L A = b1 ++ (kids - 16, 56 * cap + 16) :: b2 /\
            blocks L2 A2 = c1 ++ (res - 16, 56 * cap2 cap + 16) :: c2 /\ c1 ++ c2 = b1 ++ b2)).
      { destruct Hsh as [(H1 & _ & _ & _ & H2)|(H1 & _ & _ & H2)]; [left | right]; split; assumption. }
      assert (Hrf1 : rf_ok F A2 (rf_grow F b (56 * cap) (56 * cap2 cap))).
      { destruct Hsh as [(Hk0 & _ & _ & Hrf & _)|(Hk0 & _ & Hrf & _)]; unfold rf_grow.
        - destruct Hkr as [Hc0|(Hcp & Rk1 & _)]; [|lia].
          rewrite (proj2 (Z.eqb_eq (56 * cap) 0)) by lia. exact Hrf.
        - destruct Hkr as [Hc0|(Hcp & _)]; [destruct Hkb as [(_ & Hk)|(Hcp & _)]; lia|].
          rewrite (proj2 (Z.eqb_neq (56 * cap) 0)) by lia. exact Hrf. }
      destruct (g_fresh B API L A L2 A2 mem2 md2 kids (56 * cap) res (56 * cap2 cap) HMR2 ltac:(lia) Hsh')
        as (Hfr & Hnb); [intros Eq; injection Eq; lia|].
      assert (HLsub : forall a k, In (a, k) ((res, 56 * cap2 cap) :: l1 ++ l2) ->
          In (a, k) Lam \/ ~ In (a - 16, k + 16) (blocks L A)).
      { intros a k [Eq|Hin]; [injection Eq as <- <-; right; exact Hfr|left].
        destruct Hsh as [(_ & -> & -> & _)|(_ & -> & _)]; [exact Hin|].
        apply in_app_or in Hin. apply in_or_app. destruct Hin as [Hin|Hin]; [left; exact Hin | right; right; exact Hin]. }
      pose proof (vloc_call B API L A Lam (spZ regs) v r rk _ regs1 m' md _ L2 A2 regs2 mem2 md2 _ _ _ _ _
        HV0 Hpost2 Hub Hrk HLn HLsub) as HV2.
      assert (HP1 : Permutation Lam (kids_blk kids cap ++ l1 ++ l2)).
      { destruct Hsh as [(Hk0 & -> & -> & _)|(Hk0 & ELam & _)].
        - destruct Hkr as [Hc0|(Hcp & Rk1 & _)]; [|lia]. unfold kids_blk. rewrite (proj2 (Z.eqb_eq cap 0) Hc0).
          cbn [app]. apply Permutation_refl.
        - destruct Hkr as [Hc0|(Hcp & _)]; [destruct Hkb as [(_ & Hk)|(Hcp & _)]; lia|].
          unfold kids_blk. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. rewrite ELam. cbn [app].
          apply Permutation_sym, Permutation_middle. }
      assert (Hmv2 : forall i, 0 <= i < 56 * cap -> mbyte (ms_segs B) mem2 (res + i) = mbyte (ms_segs B) mem (kids + i)).
      { intros i Hi. destruct Hkr as [Hc0|(Hcp & Rk1 & Rk2 & _)]; [lia|].
        rewrite (Hold2 i ltac:(lia)), <- (Hold i Hi). apply HM1; lia. }
      assert (Hne1 : (res - 16, 56 * cap2 cap + 16) <> (r, rk)).
      { intros Eq. apply (vloc_ne L A Lam (spZ regs) v r rk _ _ HV0 Hfr ltac:(lia)). symmetry. exact Eq. }
      assert (Hdres : forall i, 0 <= i < 56 * cap2 cap -> res + i < v \/ v + 56 <= res + i).
      { intros i Hi. apply (vloc_disj B API L2 A2 _ mem2 md2 (spZ regs) v r rk (res - 16) (56 * cap2 cap + 16) (res + i)
          HV2 HMR2 ltac:(lia) Hnb Hne1). lia. }
      assert (HR3 : rpost B API GROW_K L A regs mem md (grow_writes v 6 kids keys cap cap) (grow_gone 6 kids keys cap cap)
          L2 A2 regs m3 md2).
      { apply (rp_A B API HIL GROW_K L A regs mem md _ _ L2 A2 mem2 md2 m3 _ HMR ltac:(lia) HR2 MU3 WM3).
        - intros x Hx Ho Hn0. exact (PM3 _ Hn0).
        - intros x Ho. pose proof (g_nout1 _ _ _ Ho) as Hx. split.
          + right. split; [reflexivity|]. left; lia.
          + apply (vloc_own B API L2 A2 _ mem2 md2 (spZ regs) v r rk x HV2 HMR2); [lia | lia |].
            exact (proj1 (Hvsx x ltac:(lia))). }
      pose proof HR3 as (HMR3 & _).
      assert (Hro3 : U.MemNorm.ro_agree (ms_segs B) m3).
      { apply (g_ro_munch B _ mem2 m3 Hro2 MU3). intros a Ha Ho. pose proof (g_nout1 _ _ _ Ho).
        apply (g_ro_notimg B HSEG); [lia|]. exact (proj2 (proj2 (proj2 (Hvsx a ltac:(lia))))). }
      assert (HL3 : ledger B L2 A2 m3 ((res, 56 * cap2 cap) :: l1 ++ l2)
          (Z.max peak (lsum (l1 ++ l2) + 56 * cap2 cap)) ((cnt + 1) mod 2 ^ 64) fail).
      { apply (g_ledger_munch B API L2 A2 mem2 md2 m3 _ _ _ _ _ HMR2 HLn MU3).
        intros x Ho. pose proof (g_nout1 _ _ _ Ho) as Hx. split; [exact (proj1 (proj2 (Hvsx x ltac:(lia))))|].
        intros a k Hin Ha.
        destruct (vloc_heads B API L2 A2 _ mem2 md2 _ _ _ (spZ regs) v r rk a k HV2 HMR2 HLn ltac:(lia) Hin); lia. }
      assert (HV3m : forall x, v <= x < v + 56 -> ~ (v + 24 <= x < v + 32) ->
          mbyte (ms_segs B) m3 x = mbyte (ms_segs B) mem x).
      { intros x Hx Hn0. assert (Ho3 : Frame.outside [(v + 24, v + 32)] x) by (cbn [Frame.outside]; refine (conj _ I); lia).
        rewrite (mbyte_munch (ms_segs B) _ mem2 m3 x MU3 ltac:(lia) Ho3). exact (proj1 (HVB x Hx)). }
      assert (HV3w : forall x, v <= x < v + 56 -> writable_at (ms_segs B) m3 x).
      { intros x Hx. apply WM3. exact (proj2 (HVB x Hx)). }
      assert (Hbk : forall a0 k0, In (a0, k0) (kids_blk kids cap ++ keys_blk 6 keys cap) ->
          4112 <= a0 /\ a0 + k0 <= alloc_ceiling).
      { intros a0 k0 Hin0. unfold kids_blk, keys_blk in Hin0. destruct (Z.eqb_spec cap 0) as [Hc0|Hc0]; cbn in Hin0;
          [destruct Hin0|].
        destruct Hkr as [Hc0'|(Hcp & Rk1 & Rk2 & _)]; [lia|].
        destruct (Hkyr eq_refl) as [Hc0'|(_ & Ry1 & Ry2 & _)]; [lia|].
        destruct Hin0 as [Eq|[Eq|[]]]; injection Eq as <- <-; lia. }
      assert (Hky2 : keys = 0 /\ 8 * cap = 0 \/ In (keys, 8 * cap) ((res, 56 * cap2 cap) :: l1 ++ l2)).
      { destruct (Hkyr eq_refl) as [Hc0|(Hcp & Ry1 & Ry2 & HinL & Hb)].
        - left. split; [exact (proj2 (Hcap0 Hc0) eq_refl) | lia].
        - right. right. destruct Hsh as [(Hk0 & _)|(Hk0 & ELam & _)].
          + destruct Hkr as [Hc0|(_ & Rk1 & _)]; lia.
          + rewrite ELam in HinL. apply in_app_or in HinL. apply in_or_app.
            destruct HinL as [H|[Eq|H]]; [left; exact H | exfalso; injection Eq; lia | right; exact H]. }
      assert (Hold3 : forall i, 0 <= i < 8 * cap -> mbyte (ms_segs B) m3 (keys + i) <> None).
      { intros i Hi. destruct Hky2 as [(_ & Hz)|HinL2]; [lia|].
        destruct (ledger_block_present B API L2 A2 m3 md2 _ _ _ _ keys (8 * cap) i HMR3 HL3 HinL2 Hi) as (bb & Hbb).
        unfold mbyte. rewrite Hbb. discriminate. }
      destruct (g_old (ms_segs B) m3 keys (8 * cap) ltac:(lia) Hold3) as (old2 & Hlo2 & Hold2b).
      assert (Hs3 : spZ regs3 = spZ regs - 48) by (unfold spZ; rewrite Hg3; exact Hs2).
      assert (Hpre3 : call_pre_k B (aa_MR API) (REALLOC_STACK + 48) L2 A2 regs3 m3 md2).
      { pose proof HR3 as (_ & HW3 & HB3 & HLy3 & HI3 & HAv3 & _ & _ & _ & _ & _ & HHi3 & _ & _ & HSc3).
        split; [exact HMR3|]. split; [exact HW3|]. split; [exact HB3|].
        split; [rewrite Hg3; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity|].
        split; [rewrite Hs3; replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia; rewrite Z_mod_plus_full;
          exact Hsp16|].
        split; [rewrite Hs3; lia|]. split; [rewrite Hs3; lia|].
        split; [intros a Ha; apply HSc3; left; rewrite Hs3 in Ha; lia|].
        split.
        { rewrite Hg3. transitivity (getr regs2 (Z_to_bv 5 4)); [reflexivity|].
          rewrite (Hp12 4) by (unfold callee_saved; lia). rewrite Hg1. exact Htpr. }
        split; [intros a Ha; apply HSc3; right; exact Ha|].
        intros Hd.
        assert (HdA : st_init_done A = false)
          by (destruct (st_init_done A) eqn:Ed; [rewrite (HI3 eq_refl) in Hd; discriminate | reflexivity]).
        destruct HLy3 as (_ & Hsec & _ & _). rewrite Hsec, Hs3.
        assert (Hlox : exists lo, spZ regs <= lo /\ auxv_pre B (ly_sec L) lo mem /\
            (v + 56 <= lo \/ v + 56 <= spZ regs - GROW_K)).
        { destruct (Z_le_gt_dec (spZ regs) v) as [Hsv|Hsv].
          - exists (v + 56). split; [lia|]. split; [exact (Hauxv Hsv HdA) | left; lia].
          - exists (spZ regs). split; [lia|]. split; [exact (Haux HdA) | right; lia]. }
        destruct Hlox as (lo & Hlo1 & Hlo2' & Hlo3).
        apply (auxv_pre_mono B (ly_sec L) lo (spZ regs - 48) m3); [lia|].
        apply (g_auxv_keep B (ly_sec L) lo mem m3 Hlo2').
        - intros i Hi. exact (HAv3 Hd i Hi).
        - intros a Ha.
          assert (Hns : ~ scratch_k B GROW_K regs a)
            by (unfold scratch_k; rewrite Herrno; unfold U.Prog.strtod_c.STRTOD_ERRNO; lia).
          assert (HnE : ~ grow_writes v 6 kids keys cap cap a).
          { intros (_ & [Hx|[Hx|[(a0 & k0 & Hin0 & Hx)|Hx]]]).
            + lia.
            + lia.
            + destruct (Hbk a0 k0 Hin0). lia.
            + unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hx. lia. }
          exact (proj1 (HHi3 a ltac:(lia) Hns HnE)). }
      eapply SR_bind; [apply (FR L2 A2 regs3 m3 md2 keys (8 * cap) (8 * cap2 cap) old2 (rf_grow F b (56 * cap) (56 * cap2 cap))
        ((res, 56 * cap2 cap) :: l1 ++ l2) (Z.max peak (lsum (l1 ++ l2) + 56 * cap2 cap)) ((cnt + 1) mod 2 ^ 64) fail)|].
      { exact Hpre3. }
      { rewrite Hg3. reflexivity. }
      { rewrite Hg3. reflexivity. }
      { lia. }
      { exact HL3. }
      { exact Hro3. }
      { exact Hky2. }
      { exact Hlo2. }
      { exact Hold2b. }
      { exact Hrf1. }
      { exact (Hrm2 eq_refl). }
      { lia. }
      intros cc4 HC4.
      destruct HC4 as (L4 & A4 & regs4 & mem4 & md4 & res2 & -> & Hro4 & _ & Hin4 & Hav4 & Hpost4 & Hlen4 & Hr4 & _ & Harm4).
      pose proof Hpost4 as (HMR4 & HWF4 & Hbd4 & Hle4 & Hptr4 & Hp34 & (vm4 & Emd4) & Hfr4 & Hblk4 & Hscr4).
      assert (Hresr2 : res2 = 0 \/ (4112 <= res2 /\ res2 + 8 * cap2 cap <= alloc_ceiling /\
          (forall i, 0 <= i < 8 * cap2 cap + 16 -> ~ in_img B (res2 - 16 + i)))).
      { destruct Harm4 as [(_ & Hr0 & _)|(_ & _ & _ & _ & Himg2 & _ & _ & _ & l1' & l2' & _ & _ & HLn4)];
          [left; exact Hr0|].
        right. pose proof (ledger_block_range B API L4 A4 mem4 md4 _ _ _ _ res2 (8 * cap2 cap) HMR4 HLn4 (in_eq _ _))
          as (R1 & R2 & _).
        split; [lia|]. split; [lia | exact Himg2]. }
      assert (HE2 : forall a, realloc_writes keys (8 * cap) res2 a -> a < alloc_ceiling /\
          (in_img B a -> grow_writes v 6 kids keys cap cap a)).
      { intros a [Ha|[(Hk0 & Ha)|(Hr0 & Ha)]].
        - split; [unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha; lia|]. intros _. split; [reflexivity|].
          right; right; right; exact Ha.
        - destruct (Hkyr eq_refl) as [Hc0|(Hcp & Ry1 & Ry2 & HinL & Hb)].
          + exfalso. exact (Hk0 (proj2 (Hcap0 Hc0) eq_refl)).
          + split; [lia|]. intros _. split; [reflexivity|]. right; right; left.
            exists keys, (8 * cap). split; [|lia]. apply in_or_app. right. unfold keys_blk.
            rewrite (proj2 (Z.eqb_neq cap 0)) by lia. cbn. left. reflexivity.
        - destruct Hresr2 as [Hr00|(R1 & R2 & Ri2)]; [lia|]. split; [lia|]. intros Hi. exfalso.
          apply (Ri2 (a - res2 + 16)); [lia|]. replace (res2 - 16 + (a - res2 + 16)) with a by lia. exact Hi. }
      assert (Hug2 : exists g2, ublocks_kept L2 A2 A4 g2 /\ (g2 = (0, 0) \/ g2 = (keys - 16, 8 * cap + 16))).
      { destruct Harm4 as [(_ & _ & _ & _ & _ & _ & _ & _ & _ & Hub' & _)|(_ & _ & _ & _ & _ & _ & Hub' & _)].
        - exists (0, 0). split; [exact Hub' | left; reflexivity].
        - exists (keys - 16, 8 * cap + 16). split; [exact Hub' | right; reflexivity]. }
      destruct Hug2 as (g2 & Hub2 & Hg2v).
      assert (Hrg2 : (r, rk) <> g2).
      { destruct Hg2v as [->| ->]; [|exact (Hrky eq_refl)]. intros Eq. injection Eq as E1 E2. subst r rk.
        destruct HV0 as [(_ & _ & _ & E')|(Hin & _)]; [lia|].
        pose proof (g_blk_range B API L A mem md 0 0 HMR Hin). lia. }
      assert (HR4 : rpost B API GROW_K L A regs mem md (grow_writes v 6 kids keys cap cap)
          (grow_gone 6 kids keys cap cap) L4 A4 regs mem4 md4).
      { apply (rp_call B API HIL GROW_K L A regs mem md _ _ L2 A2 m3 md2 (REALLOC_STACK + 48) regs3 _ g2 L4 A4 regs4 mem4 md4
          HMR HWF ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HR3 Hpost4 Hin4 Hav4 Hlen4 Hub2 HE2).
        - intros p nn Hp Heq. destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p nn HMR Hp) as (P1 & P2).
          destruct Hg2v as [->| ->]; injection Heq as E1 E2; [lia|].
          split; [reflexivity|]. unfold freed. destruct (Hkyr eq_refl) as [Hc0|(Hcp & Ry1 & Ry2 & HinL & Hb)].
          + pose proof (proj2 (Hcap0 Hc0) eq_refl). lia.
          + assert (Ekb : keys_blk 6 keys cap = [(keys, 8 * cap)])
              by (unfold keys_blk; rewrite (proj2 (Z.eqb_neq cap 0)) by lia; reflexivity).
            apply in_or_app. right. rewrite Ekb. left. f_equal; lia.
        - intros p nn i Hp Hi (_ & Hfr'). split; [reflexivity|]. right; right; left.
          exists (ptr_addr L p + 16), (nn - 16). split; [exact Hfr' | lia]. }
      assert (HVB4 : forall x, v <= x < v + 56 ->
          mbyte (ms_segs B) mem4 x = mbyte (ms_segs B) m3 x /\ writable_at (ms_segs B) mem4 x).
      { intros x Hx. destruct (Hvsx x Hx) as (_ & _ & Hxe & _).
        destruct (vloc_bytes B API L2 A2 _ (spZ regs) v r rk _ regs3 m3 md2 _ L4 A4 regs4 mem4 md4 g2 x HV2 HMR3 Hpost4
          Hub2 Hrg2 ltac:(lia) ltac:(lia) (fun a Ha => proj1 (HE2 a Ha)) Hxe Hx) as (E1 & E2).
        split; [exact E1 | apply E2; exact (HV3w x Hx)]. }
      assert (HFC2 : forall x, spZ regs - 48 <= x < spZ regs ->
          mbyte (ms_segs B) mem4 x = mbyte (ms_segs B) m3 x /\
          (writable_at (ms_segs B) m3 x -> writable_at (ms_segs B) mem4 x)).
      { intros x Hx.
        assert (No1 : ~ owned B L2 A2 x) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HMR3 Ho); lia).
        assert (No2 : ~ owned B L4 A4 x) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HMR4 Ho); lia).
        destruct (Hfr4 x ltac:(left; lia) No1 No2
          ltac:(unfold scratch_k; rewrite Hs3, Herrno; unfold U.Prog.strtod_c.STRTOD_ERRNO; lia)
          ltac:(intros HE; pose proof (proj1 (HE2 x HE)); lia)) as [E1 E2].
        split; [exact E1 | apply E2]. }
      assert (Hkm : forall i, 0 <= i < 8 * cap -> mbyte (ms_segs B) m3 (keys + i) = mbyte (ms_segs B) mem (keys + i)).
      { intros i Hi. destruct (Hkyr eq_refl) as [Hc0|(Hcp & Ry1 & Ry2 & HinL & Hb)]; [lia|].
        destruct Hkr as [Hc0|(_ & Rk1 & Rk2 & Hbk')]; [lia|].
        assert (Ekb : keys_blk 6 keys cap = [(keys, 8 * cap)])
          by (unfold keys_blk; rewrite (proj2 (Z.eqb_neq cap 0)) by lia; reflexivity).
        assert (Hap : ~ (v <= keys + i < v + 56)).
        { apply (HAP (keys, 8 * cap) (keys + i)); [| unfold pj_holds; cbn [fst snd]; lia].
          apply in_or_app. right. rewrite Ekb. left. reflexivity. }
        assert (Hkk : keys - 16 <> kids - 16).
        { intros Ek. assert (Hne : (keys - 16, 8 * cap + 16) <> (kids - 16, 56 * cap + 16)) by (intros Eq; injection Eq; lia).
          destruct (g_disj B API L A mem md _ _ _ _ HMR Hb Hbk' Hne); lia. }
        assert (Ho3 : Frame.outside [(v + 24, v + 32)] (keys + i)) by (cbn [Frame.outside]; refine (conj _ I); lia).
        rewrite (mbyte_munch (ms_segs B) _ mem2 m3 (keys + i) MU3 ltac:(lia) Ho3).
        pose proof (Hkeeps (keys - 16) (8 * cap + 16) (i + 16) Hb Hkk ltac:(lia)) as Ek.
        replace (keys - 16 + (i + 16)) with (keys + i) in Ek by lia. rewrite Ek. apply HM1; lia. }
      assert (Hkb2 : 0 < cap -> In (keys - 16, 8 * cap + 16) (blocks L2 A2)).
      { intros Hcp. destruct (Hkyr eq_refl) as [Hc0|(_ & Ry1 & Ry2 & HinL & Hb)]; [lia|].
        apply (g_kept_blk B API _ L A regs1 m' md _ L2 A2 regs2 mem2 md2 _ _ _ Hpost2 Hub Hb).
        intros Eq. injection Eq; lia. }
      assert (G8'' : getr regs4 8 = Z_to_bv 64 v).
      { transitivity (getr regs3 (Z_to_bv 5 8)); [apply (Hp34 8); unfold callee_saved; lia | rewrite Hg3; reflexivity]. }
      assert (G9'' : getr regs4 9 = Z_to_bv 64 (-1)).
      { transitivity (getr regs3 (Z_to_bv 5 9)); [apply (Hp34 9); unfold callee_saved; lia | rewrite Hg3; reflexivity]. }
      assert (G19'' : getr regs4 19 = Z_to_bv 64 (cap2 cap)).
      { transitivity (getr regs3 (Z_to_bv 5 19)); [apply (Hp34 19); unfold callee_saved; lia | rewrite Hg3; reflexivity]. }
      assert (G2'' : getr regs4 2 = getr regs2 2).
      { transitivity (getr regs3 (Z_to_bv 5 2)); [apply (Hp34 2); unfold callee_saved; lia | rewrite Hg3; reflexivity]. }
      assert (Hs4 : bv_unsigned (getr regs4 2) = spZ regs - 48) by (rewrite G2''; exact Hs2).
      assert (HRR2 : 0 <= res2 < 2 ^ 64) by (destruct Hresr2 as [->|(R1 & R2 & _)]; lia).
      assert (G31 : getr regs3 1 = Z_to_bv 64 0x16790) by (rewrite Hg3; reflexivity).
      rewrite G31.
      destruct (kb_md B API L4 A4 mem4 md4 HMR4) as (Hh4 & Hz4).
      apply (kb_run B regs4 _ mem4 md4
        (fun R pc' mem' => seg3_post (getr regs 1) (getr regs4 2) (getr regs4 3) (getr regs4 4) (getr regs 8)
           (getr regs 9) (getr regs 18) (getr regs 19) (getr regs4 20) (getr regs4 21) (getr regs4 22) (getr regs4 23)
           (getr regs4 24) (getr regs4 25) (getr regs4 26) (getr regs4 27) fp_regs fp_csr mem4 v (cap2 cap) res2
           (MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs))) _ Hh4 Hz4).
      { unfold rmk. rewrite HSEG. eapply evt_mono.
        - apply (grow_seg3 (getr regs4 1) (getr regs4 2) (getr regs4 3) (getr regs4 4) (getr regs4 5) (getr regs4 6)
            (getr regs4 7) (getr regs4 8) (getr regs4 9) (getr regs4 10) (getr regs4 11) (getr regs4 12)
            (getr regs4 13) (getr regs4 14) (getr regs4 15) (getr regs4 16) (getr regs4 17) (getr regs4 18)
            (getr regs4 19) (getr regs4 20) (getr regs4 21) (getr regs4 22) (getr regs4 23) (getr regs4 24)
            (getr regs4 25) (getr regs4 26) (getr regs4 27) (getr regs4 28) (getr regs4 29) (getr regs4 30)
            (getr regs4 31) fp_regs fp_csr mem4 v (cap2 cap) res2 j
            (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) Hr4 G8'' G9'' G19'' HRR2).
          + lia.
          + rewrite <- HSEG. apply (g_wr B); [lia | lia|]. intros i Hi. exact (proj2 (HVB4 (v + i) ltac:(lia))).
          + rewrite Hs4. rewrite <- HSEG. apply (g_rw_cells B m3); [exact FR3|].
            intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply HFC2. lia.
          + rewrite Hs4. lia.
        - intros ms Hp. pose proof Hp as Hp'. apply seg3_shape in Hp'. destruct Hp' as (R & pc' & mm & ->).
          exists R, pc', mm. split; [reflexivity | exact Hp]. }
      intros R pc5 mem5 regs5 HK5 Hg5. unfold seg3_post in HK5.
      destruct HK5 as [(Hr02 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & E)
                      |(Hrnz2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m5 & E &
                        MU5 & WM5 & PM5 & BW3 & BW4)];
        pose proof (f_equal ms_regs E) as ER; pose proof (f_equal ms_pc_val E) as EP; pose proof (f_equal ms_mem E) as EM;
        cbn [ms_regs ms_pc_val ms_mem MS] in ER, EP, EM; subst R pc5 mem5; clear E.
      * destruct Harm4 as [(Hcf2 & _ & _ & _ & _ & Hrf4 & _ & _ & Hkeeps4 & _ & HLn4)|(_ & Hrnz2 & _)]; [|lia].
        assert (Hcf2' : cnt + 1 = fail) by (rewrite Z.mod_small in Hcf2 by lia; exact Hcf2).
        apply SR_ret. exists L4, A4, regs5, mem4, md4, ((res, 56 * cap2 cap) :: l1 ++ l2),
          (Z.max peak (lsum (l1 ++ l2) + 56 * cap2 cap)), (((cnt + 1) mod 2 ^ 64 + 1) mod 2 ^ 64), (2 ^ 64 - 1),
          (rf_grow F b (56 * cap) (56 * cap2 cap)), (-1).
        split; [rewrite (kb_ret_pc _ Hra); reflexivity|].
        split.
        { eapply rp_regs; [exact HR4|].
          cs_cases ltac:(rewrite Hg5; first
            [ reflexivity
            | match goal with |- getr _ (Z_to_bv 5 2) = _ =>
                transitivity (Z_to_bv 64 (bv_unsigned (getr regs4 2) + 48)); [reflexivity|];
                rewrite Hs4; replace (spZ regs - 48 + 48) with (spZ regs) by lia; apply Step.Z_to_bv_lit_self end
            | match goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
                transitivity (getr regs4 (Z_to_bv 5 k)); [reflexivity|];
                rewrite (Hp34 k ltac:(unfold callee_saved; lia)), Hg3;
                transitivity (getr regs2 (Z_to_bv 5 k)); [reflexivity|];
                rewrite (Hp12 k ltac:(unfold callee_saved; lia)), Hg1; reflexivity end ]). }
        split.
        { split; [exact Hro4|]. destruct (U.Reusable.YL01.ax_statics AX L4 A4 mem4 md4 HMR4) as (Hg & (g & _ & Hgw) & _).
          split; [exact Hg | exists g; exact Hgw]. }
        split; [rewrite Hg5; reflexivity|].
        split; [exact HLn4|].
        split; [exact Hrf4|].
        right; right; right; left.
        split; [reflexivity|]. split; [exact Hcf|]. split; [reflexivity|]. split; [exact Hcf2'|].
        split; [reflexivity|].
        exists res, (l1 ++ l2).
        split; [lia|]. split; [exact Hr16|].
        split; [intros a k [Eq|[]]; injection Eq as <- <-; exact Hfr|].
        split; [exact HP1|].
        split; [apply Permutation_refl|].
        split; [cbn [lsum]; lia|].
        split; [rewrite (Z.mod_small (cnt + 1)) by lia; rewrite Z.mod_small by lia; lia|].
        split; [reflexivity|]. split; [reflexivity|].
        split.
        { intros i Hi. destruct Hkr as [Hc0|(Hcp & _)]; [lia|].
          pose proof (Hkeeps4 (res - 16) (56 * cap2 cap + 16) (i + 16) Hnb ltac:(lia) ltac:(lia)) as Ek.
          replace (res - 16 + (i + 16)) with (res + i) in Ek by lia. rewrite Ek.
          assert (Ho3 : Frame.outside [(v + 24, v + 32)] (res + i))
            by (cbn [Frame.outside]; refine (conj _ I); destruct (Hdres i ltac:(lia)); lia).
          rewrite (mbyte_munch (ms_segs B) _ mem2 m3 (res + i) MU3 ltac:(lia) Ho3). exact (Hmv2 i Hi). }
        split.
        { apply (g_hdr B mem mem4 v 6 num str kids keys cap cap res keys cap HH).
          - intros x Hx. destruct (HVB4 x Hx) as (E1 & E2). split; [exact E2|]. rewrite E1.
            destruct (Z_le_gt_dec (v + 24) x); [destruct (Z_lt_ge_dec x (v + 32))|].
            + apply (g_bytes_some B m3 (v + 24) _ x BW1). rewrite length_le8. lia.
            + rewrite (HV3m x Hx) by lia. exact (proj2 (Hvm x Hx)).
            + rewrite (HV3m x Hx) by lia. exact (proj2 (Hvm x Hx)).
          - intros x Hx. rewrite (proj1 (HVB4 x ltac:(lia))). apply HV3m; lia.
          - split; [lia|]. apply (g_bytes B m3); [exact BW1|]. intros x Hx. rewrite length_le8 in Hx.
            exact (proj1 (HVB4 x ltac:(lia))).
          - split; [exact Hkey|]. apply (g_bytes B mem); [exact Bkey|]. intros x Hx. rewrite length_le8 in Hx.
            rewrite (proj1 (HVB4 x ltac:(lia))). apply HV3m; lia.
          - split; [exact Hcap|]. apply (g_bytes B mem); [exact Bcap|]. intros x Hx. rewrite length_le8 in Hx.
            rewrite (proj1 (HVB4 x ltac:(lia))). apply HV3m; lia. }
        { intros i Hi. assert (Hcp : 0 < cap) by lia.
          pose proof (Hkeeps4 (keys - 16) (8 * cap + 16) (i + 16) (Hkb2 Hcp) ltac:(destruct (Hkyr eq_refl) as
            [Hc0|(_ & Ry1 & _)]; lia) ltac:(lia)) as Ek.
          replace (keys - 16 + (i + 16)) with (keys + i) in Ek by lia. rewrite Ek. exact (Hkm i Hi). }
      * destruct Harm4 as [(_ & Hr0' & _)|(Hcf2 & _ & Hr16b & Hrstb & Himgb & Hkeeps4 & Hub4 & Hold4 & l1' & l2' & Hsh2 &
          Hnin2 & HLn4)]; [lia|].
        rewrite <- HSEG in WM5, BW3, BW4.
        destruct Hresr2 as [Hr00'|(Rs1 & Rs2 & Ri2)]; [lia|].
        assert (Hcf2' : cnt + 1 <> fail) by (rewrite Z.mod_small in Hcf2 by lia; exact Hcf2).
        assert (Hsh2' : keys = 0 /\ (exists b1 b2, blocks L4 A4 = b1 ++ (res2 - 16, 8 * cap2 cap + 16) :: b2 /\
              blocks L2 A2 = b1 ++ b2)
            \/ keys <> 0 /\ (exists b1 b2 c1 c2, blocks L2 A2 = b1 ++ (keys - 16, 8 * cap + 16) :: b2 /\
              blocks L4 A4 = c1 ++ (res2 - 16, 8 * cap2 cap + 16) :: c2 /\ c1 ++ c2 = b1 ++ b2)).
        { destruct Hsh2 as [(H1 & _ & _ & _ & H2)|(H1 & _ & _ & H2)]; [left | right]; split; assumption. }
        destruct (g_fresh B API L2 A2 L4 A4 mem4 md4 keys (8 * cap) res2 (8 * cap2 cap) HMR4 ltac:(lia) Hsh2')
          as (Hfy2 & Hny2); [intros Eq; injection Eq; lia|].
        assert (HL00 : exists L00, l1' ++ l2' = (res, 56 * cap2 cap) :: L00 /\
            Permutation Lam (kids_blk kids cap ++ keys_blk 6 keys cap ++ L00)).
        { destruct Hsh2 as [(Hk0 & -> & -> & _)|(Hk0 & ELam2 & _)].
          - exists (l1 ++ l2). split; [reflexivity|].
            destruct (Hkyr eq_refl) as [Hc0|(Hcp & Ry1 & _)]; [|lia].
            assert (Ekb : keys_blk 6 keys cap = []) by (unfold keys_blk; rewrite (proj2 (Z.eqb_eq cap 0) Hc0); reflexivity).
            rewrite Ekb. cbn [app]. exact HP1.
          - destruct l1' as [|x l1''].
            + cbn [app] in ELam2. injection ELam2 as E1 E2 E3. exfalso. lia.
            + cbn [app] in ELam2. injection ELam2 as Ex El. subst x.
              exists (l1'' ++ l2'). split; [reflexivity|].
              destruct (Hkyr eq_refl) as [Hc0|(Hcp & Ry1 & _)]; [pose proof (proj2 (Hcap0 Hc0) eq_refl); lia|].
              assert (Ekb : keys_blk 6 keys cap = [(keys, 8 * cap)])
                by (unfold keys_blk; rewrite (proj2 (Z.eqb_neq cap 0)) by lia; reflexivity).
              rewrite Ekb. rewrite El in HP1. eapply Permutation_trans; [exact HP1|]. apply Permutation_app_head.
              cbn [app]. apply Permutation_sym, Permutation_middle. }
        destruct HL00 as (L00 & ELam4 & HP2).
        assert (HLsub2 : forall a k, In (a, k) ((res2, 8 * cap2 cap) :: l1' ++ l2') ->
            In (a, k) ((res, 56 * cap2 cap) :: l1 ++ l2) \/ ~ In (a - 16, k + 16) (blocks L2 A2)).
        { intros a k [Eq|Hin]; [injection Eq as <- <-; right; exact Hfy2|left].
          destruct Hsh2 as [(_ & -> & -> & _)|(_ & -> & _)]; [exact Hin|].
          apply in_app_or in Hin. apply in_or_app. destruct Hin as [Hin|Hin]; [left; exact Hin | right; right; exact Hin]. }
        pose proof (vloc_call B API L2 A2 _ (spZ regs) v r rk _ regs3 m3 md2 _ L4 A4 regs4 mem4 md4 _ _ _ _ _
          HV2 Hpost4 Hub4 (Hrky eq_refl) HLn4 HLsub2) as HV4.
        assert (Hne2 : (res2 - 16, 8 * cap2 cap + 16) <> (r, rk)).
        { intros Eq. apply (vloc_ne L2 A2 _ (spZ regs) v r rk _ _ HV2 Hfy2 ltac:(lia)). symmetry. exact Eq. }
        assert (Hdres2 : forall i, 0 <= i < 8 * cap2 cap -> res2 + i < v \/ v + 56 <= res2 + i).
        { intros i Hi. apply (vloc_disj B API L4 A4 _ mem4 md4 (spZ regs) v r rk (res2 - 16) (8 * cap2 cap + 16) (res2 + i)
            HV4 HMR4 ltac:(lia) Hny2 Hne2). lia. }
        assert (HR5 : rpost B API GROW_K L A regs mem md (grow_writes v 6 kids keys cap cap)
            (grow_gone 6 kids keys cap cap) L4 A4 regs m5 md4).
        { apply (rp_A B API HIL GROW_K L A regs mem md _ _ L4 A4 mem4 md4 m5 _ HMR ltac:(lia) HR4 MU5 WM5).
          - intros x Hx Ho Hn0. exact (PM5 _ Hn0).
          - intros x Ho. pose proof (g_nout2 _ _ _ _ _ Ho) as Hx. split.
            + right. split; [reflexivity|]. destruct Hx as [Hx|Hx]; [left; lia | right; left; lia].
            + apply (vloc_own B API L4 A4 _ mem4 md4 (spZ regs) v r rk x HV4 HMR4); [lia | lia |].
              exact (proj1 (Hvsx x ltac:(lia))). }
        assert (Hro5 : U.MemNorm.ro_agree (ms_segs B) m5).
        { apply (g_ro_munch B _ mem4 m5 Hro4 MU5). intros a Ha Ho. pose proof (g_nout2 _ _ _ _ _ Ho).
          apply (g_ro_notimg B HSEG); [lia|]. exact (proj2 (proj2 (proj2 (Hvsx a ltac:(lia))))). }
        assert (HL5 : ledger B L4 A4 m5 ((res2, 8 * cap2 cap) :: l1' ++ l2')
            (Z.max (Z.max peak (lsum (l1 ++ l2) + 56 * cap2 cap)) (lsum (l1' ++ l2') + 8 * cap2 cap))
            (((cnt + 1) mod 2 ^ 64 + 1) mod 2 ^ 64) fail).
        { apply (g_ledger_munch B API L4 A4 mem4 md4 m5 _ _ _ _ _ HMR4 HLn4 MU5).
          intros x Ho. pose proof (g_nout2 _ _ _ _ _ Ho) as Hx. split; [exact (proj1 (proj2 (Hvsx x ltac:(lia))))|].
          intros a k Hin Ha.
          destruct (vloc_heads B API L4 A4 _ mem4 md4 _ _ _ (spZ regs) v r rk a k HV4 HMR4 HLn4 ltac:(lia) Hin); lia. }
        assert (Hrk2 : res - 16 <> keys - 16).
        { intros Ek. destruct (Hkyr eq_refl) as [Hc0|(Hcp & Ry1 & Ry2 & HinL & Hb)].
          - pose proof (proj2 (Hcap0 Hc0) eq_refl). lia.
          - assert (Hne : (res - 16, 56 * cap2 cap + 16) <> (keys - 16, 8 * cap + 16)) by (intros Eq; injection Eq; lia).
            destruct (g_disj B API L2 A2 mem2 md2 _ _ _ _ HMR2 Hnb (Hkb2 Hcp) Hne); lia. }
        apply SR_ret. exists L4, A4, regs5, m5, md4, ((res2, 8 * cap2 cap) :: l1' ++ l2'),
          (Z.max (Z.max peak (lsum (l1 ++ l2) + 56 * cap2 cap)) (lsum (l1' ++ l2') + 8 * cap2 cap)),
          (((cnt + 1) mod 2 ^ 64 + 1) mod 2 ^ 64), fail,
          (rf_grow F (rf_grow F b (56 * cap) (56 * cap2 cap)) (8 * cap) (8 * cap2 cap)), 0.
        split; [rewrite (kb_ret_pc _ Hra); reflexivity|].
        split.
        { eapply rp_regs; [exact HR5|].
          cs_cases ltac:(rewrite Hg5; first
            [ reflexivity
            | match goal with |- getr _ (Z_to_bv 5 2) = _ =>
                transitivity (Z_to_bv 64 (bv_unsigned (getr regs4 2) + 48)); [reflexivity|];
                rewrite Hs4; replace (spZ regs - 48 + 48) with (spZ regs) by lia; apply Step.Z_to_bv_lit_self end
            | match goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
                transitivity (getr regs4 (Z_to_bv 5 k)); [reflexivity|];
                rewrite (Hp34 k ltac:(unfold callee_saved; lia)), Hg3;
                transitivity (getr regs2 (Z_to_bv 5 k)); [reflexivity|];
                rewrite (Hp12 k ltac:(unfold callee_saved; lia)), Hg1; reflexivity end ]). }
        split.
        { split; [exact Hro5|]. pose proof HR5 as (HM5' & _).
          destruct (U.Reusable.YL01.ax_statics AX L4 A4 m5 md4 HM5') as (Hg & (g & _ & Hgw) & _).
          split; [exact Hg | exists g; exact Hgw]. }
        split; [rewrite Hg5; reflexivity|].
        split; [exact HL5|].
        split.
        { destruct Hsh2 as [(Hy0 & _ & _ & Hrf & _)|(Hy0 & _ & Hrf & _)]; unfold rf_grow at 1.
          - destruct (Hkyr eq_refl) as [Hc0|(Hcp & Ry1 & _)]; [|lia].
            rewrite (proj2 (Z.eqb_eq (8 * cap) 0)) by lia. exact Hrf.
          - destruct (Hkyr eq_refl) as [Hc0|(Hcp & _)]; [pose proof (proj2 (Hcap0 Hc0) eq_refl); lia|].
            rewrite (proj2 (Z.eqb_neq (8 * cap) 0)) by lia. exact Hrf. }
        right; right; right; right.
        split; [reflexivity|]. split; [exact Hcf|]. split; [reflexivity|]. split; [exact Hcf2'|].
        split; [reflexivity|].
        exists res, res2, L00.
        split; [lia|]. split; [exact Hr16|]. split; [lia|]. split; [exact Hr16b|].
        split.
        { intros a k [Eq|[Eq|[]]]; injection Eq as <- <-.
          - intros Hin. apply Hfy2. apply (g_kept_blk B API _ L A regs1 m' md _ L2 A2 regs2 mem2 md2 _ _ _ Hpost2 Hub Hin).
            intros Eq. injection Eq as E1 E2. revert E2. unfold cap2. destruct (Z.eqb_spec cap 0); lia.
          - exact Hfr. }
        split; [exact HP2|].
        split; [rewrite ELam4; apply Permutation_refl|].
        split.
        { rewrite (g_lsum_perm _ _ HP1), (g_lsum_app (kids_blk kids cap) (l1 ++ l2)), (g_kids_lsum kids cap) by lia.
          cbn [lsum]. lia. }
        split; [rewrite (Z.mod_small (cnt + 1)) by lia; rewrite Z.mod_small by lia; lia|].
        split; [reflexivity|]. split; [reflexivity|].
        split.
        { intros i Hi. destruct Hkr as [Hc0|(Hcp & _)]; [lia|].
          assert (Ho5 : Frame.outside [(v + 32, v + 40); (v + 48, v + 56)] (res + i))
            by (cbn [Frame.outside]; refine (conj _ (conj _ I)); destruct (Hdres i ltac:(lia)); lia).
          rewrite (mbyte_munch (ms_segs B) _ mem4 m5 (res + i) MU5 ltac:(lia) Ho5).
          pose proof (Hkeeps4 (res - 16) (56 * cap2 cap + 16) (i + 16) Hnb Hrk2 ltac:(lia)) as Ek.
          replace (res - 16 + (i + 16)) with (res + i) in Ek by lia. rewrite Ek.
          assert (Ho3 : Frame.outside [(v + 24, v + 32)] (res + i))
            by (cbn [Frame.outside]; refine (conj _ I); destruct (Hdres i ltac:(lia)); lia).
          rewrite (mbyte_munch (ms_segs B) _ mem2 m3 (res + i) MU3 ltac:(lia) Ho3). exact (Hmv2 i Hi). }
        split.
        { intros i Hi.
          assert (Ho5 : Frame.outside [(v + 32, v + 40); (v + 48, v + 56)] (res2 + i))
            by (cbn [Frame.outside]; refine (conj _ (conj _ I)); destruct (Hdres2 i ltac:(lia)); lia).
          rewrite (mbyte_munch (ms_segs B) _ mem4 m5 (res2 + i) MU5 ltac:(lia) Ho5).
          rewrite (Hold4 i ltac:(lia)), <- (Hold2b i Hi). exact (Hkm i Hi). }
        split.
        { apply (g_hdr B mem m5 v 6 num str kids keys cap cap res res2 (cap2 cap) HH).
          - intros x Hx. split.
            + apply WM5. exact (proj2 (HVB4 x Hx)).
            + destruct (kb_outside_dec [(v + 32, v + 40); (v + 48, v + 56)] x) as [Ho|Ho].
              * rewrite (mbyte_munch (ms_segs B) _ mem4 m5 x MU5 ltac:(lia) Ho), (proj1 (HVB4 x Hx)).
                destruct (Z_le_gt_dec (v + 24) x); [destruct (Z_lt_ge_dec x (v + 32))|].
                -- apply (g_bytes_some B m3 (v + 24) _ x BW1). rewrite length_le8. lia.
                -- rewrite (HV3m x Hx) by lia. exact (proj2 (Hvm x Hx)).
                -- rewrite (HV3m x Hx) by lia. exact (proj2 (Hvm x Hx)).
              * destruct (g_nout2 _ _ _ _ _ Ho) as [Hx'|Hx'].
                -- apply (g_bytes_some B m5 (v + 32) _ x BW3). rewrite length_le8. lia.
                -- apply (g_bytes_some B m5 (v + 48) _ x BW4). rewrite length_le8. lia.
          - intros x Hx.
            assert (Ho5 : Frame.outside [(v + 32, v + 40); (v + 48, v + 56)] x)
              by (cbn [Frame.outside]; refine (conj _ (conj _ I)); lia).
            rewrite (mbyte_munch (ms_segs B) _ mem4 m5 x MU5 ltac:(lia) Ho5), (proj1 (HVB4 x ltac:(lia))).
            apply HV3m; lia.
          - split; [lia|]. apply (g_bytes B m3); [exact BW1|]. intros x Hx. rewrite length_le8 in Hx.
            assert (Ho5 : Frame.outside [(v + 32, v + 40); (v + 48, v + 56)] x)
              by (cbn [Frame.outside]; refine (conj _ (conj _ I)); lia).
            rewrite (mbyte_munch (ms_segs B) _ mem4 m5 x MU5 ltac:(lia) Ho5). exact (proj1 (HVB4 x ltac:(lia))).
          - split; [lia | exact BW3].
          - split; [lia | exact BW4]. }
        split; [right; reflexivity|]. split; [lia|]. split; [lia|].
        intros _. split.
        { unfold lin. right. rewrite ELam4. left. reflexivity. }
        { intros _. unfold lin. left. reflexivity. }
Qed.

End P.
