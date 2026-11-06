From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Arr
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel SlotNeeds_c GrantSlotPlan SlotBridge
  NextModel NextLemmas reac_headamp_tx_arm_scene_c reac_headamp_tx_set_resweep_c reac_headamp_tx_next_c
  reac_headamp_tx_effective_c reac_headamp_default_c memset_c.
Import ListNotations.
Open Scope Z_scope.

Lemma canon_regs : forall ms, ms_svc_pending ms = None ->
  canonical_register_state ms =
  MS (mkR (rg ms 1) (rg ms 2) (rg ms 3) (rg ms 4) (rg ms 5) (rg ms 6) (rg ms 7) (rg ms 8) (rg ms 9) (rg ms 10)
          (rg ms 11) (rg ms 12) (rg ms 13) (rg ms 14) (rg ms 15) (rg ms 16) (rg ms 17) (rg ms 18) (rg ms 19)
          (rg ms 20) (rg ms 21) (rg ms 22) (rg ms 23) (rg ms 24) (rg ms 25) (rg ms 26) (rg ms 27) (rg ms 28)
          (rg ms 29) (rg ms 30) (rg ms 31))
     (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms) (ms_mem ms) (ms_rom ms).
Proof. intros ms H. rewrite canon_MS by exact H. unfold mkR_of, rg, PropExec.getr. reflexivity. Qed.

Lemma cb_u8 : forall m A n bs, rw_cells rsegs m A [CB n bs] -> u8arr rsegs m A bs /\ length bs = n.
Proof.
  intros m A n bs H. split; [eapply u8arr_of_rw_cells; exact H|].
  destruct H as [[Hwf _] _]. cbn in Hwf. tauto.
Qed.

Lemma u8_cb : forall m A n bs, u8arr rsegs m A bs -> length bs = n -> rw_cells rsegs m A [CB n bs].
Proof. intros m A n bs H <-. apply rw_cells_of_u8arr. exact H. Qed.

Lemma stk_cell : forall m lo hi a (n : nat), stk rsegs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  exists junk, rw_cells rsegs m a [CB n junk].
Proof.
  intros m lo hi a n (H1 & H2 & H) Ha Hn.
  assert (S1 : stk rsegs m lo (a + Z.of_nat n)) by (split; [lia | split; [lia | intros; apply H; lia]]).
  destruct (stk_carve rsegs m lo (a + Z.of_nat n) n S1 ltac:(lia)) as [_ [junk FR]].
  exists junk. replace a with (a + Z.of_nat n - Z.of_nat n) by lia. exact FR.
Qed.

Lemma stk_split3 : forall m lo hi a (n : nat), stk rsegs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  stk rsegs m lo a /\ (exists junk, rw_cells rsegs m a [CB n junk]) /\ stk rsegs m (a + Z.of_nat n) hi.
Proof.
  intros m lo hi a n HS Ha Hn.
  destruct (stk_split rsegs m lo a hi HS ltac:(lia)) as [S1 S2].
  destruct (stk_split rsegs m a (a + Z.of_nat n) hi S2 ltac:(lia)) as [S3 S4].
  split; [exact S1|]. split; [|exact S4].
  destruct (stk_carve rsegs m a (a + Z.of_nat n) n S3 ltac:(lia)) as [_ [junk FR]].
  exists junk. replace (a + Z.of_nat n - Z.of_nat n) with a in FR by lia. exact FR.
Qed.

Fixpoint zfrom (k : Z) (n : nat) : list Z := match n with O => [] | S n' => k :: zfrom (k + 1) n' end.

Lemma zfrom_in : forall n k a, k <= a < k + Z.of_nat n -> In a (zfrom k n).
Proof.
  induction n as [|n IH]; intros k a Ha; [lia|]. cbn [zfrom].
  destruct (Z.eq_dec a k) as [E|E]; [left; lia | right; apply IH; lia].
Qed.

Lemma brute : forall (N : Z) (f : Z -> bool), forallb f (zfrom 0 (Z.to_nat N)) = true ->
  forall a, 0 <= a < N -> f a = true.
Proof. intros N f H a Ha. rewrite forallb_forall in H. apply H. apply zfrom_in. lia. Qed.

Lemma outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_le_dec lo x) as [H1|H1]; [destruct (Z_lt_dec x hi) as [H2|H2]|].
  - right. intros [H3 _]. lia.
  - left. split; [lia | exact H].
  - left. split; [lia | exact H].
Qed.

Lemma mem_inv_munch : forall W m m', mem_inv rsegs m -> munch W m m' ->
  (forall a : word, ~ outside W (bv_unsigned a) -> wview rsegs m a <> None) -> mem_inv rsegs m'.
Proof.
  intros W m m' HI MU HW a b Hb.
  destruct (outside_dec W (bv_unsigned a)) as [O|O].
  - rewrite MU in Hb by exact O. exact (HI a b Hb).
  - specialize (HW a O). destruct (m a) as [b'|] eqn:E.
    + exact (HI a b' E).
    + exact (wview_not_ro rsegs m a HW E).
Qed.

Lemma wr_wview : forall m A n (a : word), wr_at rsegs m A n -> A <= bv_unsigned a < A + n ->
  wview rsegs m a <> None.
Proof.
  intros m A n a (HA & Hn & H) Ha. specialize (H (bv_unsigned a - A) ltac:(lia)).
  replace (wa (A + (bv_unsigned a - A))) with a in H; [exact H|].
  unfold wa. replace (A + (bv_unsigned a - A)) with (bv_unsigned a) by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma mem_inv_munch1 : forall A n m m', mem_inv rsegs m -> munch [(A, A + n)] m m' -> wr_at rsegs m A n ->
  mem_inv rsegs m'.
Proof.
  intros A n m m' HI MU HW. apply (mem_inv_munch _ m m' HI MU). intros a Ha.
  apply (wr_wview m A n a HW). cbn in Ha.
  destruct (Z_le_dec A (bv_unsigned a)); destruct (Z_lt_dec (bv_unsigned a) (A + n));
    first [lia | exfalso; apply Ha; split; [lia | exact I]].
Qed.

Ltac lenT := first [ assumption | apply len_setb; [lenT | lia] | apply len_set4; [lenT | lia | lia] ].

Lemma arm_T_eq : forall T b w, arm_T T b w =
  set4 (setb (setb (setb (set4 (set4 (setb (setb T 436 b) 437 (arm_w b w)) 440 0) 444 0) 448 0) 449 b) 450
    (arm_w b w)) 456 0.
Proof. reflexivity. Qed.

Lemma set_resweep_T_eq : forall T per, set_resweep_T T (Z_to_bv 64 per) = set4 (set4 T 452 per) 456 0.
Proof. reflexivity. Qed.

Definition Tarm (T : list byte) (b w : Z) : list byte := if (w =? 0) || (48 <=? b) then T else arm_T T b w.

Lemma len_Tarm : forall T b w, length T = 460%nat -> length (Tarm T b w) = 460%nat.
Proof. intros T b w HL. unfold Tarm. destruct (_ || _); [exact HL|]. rewrite arm_T_eq. lenT. Qed.

Lemma cb_post : forall m m' A n T T', rw_cells rsegs m A [CB n T] -> bytes_at rsegs m' A T' -> wmono rsegs m m' ->
  length T' = n -> rw_cells rsegs m' A [CB n T'].
Proof.
  intros m m' A n T T' H HB WM HL. destruct (cb_u8 _ _ _ _ H) as [[_ HW] HL0].
  apply u8_cb; [|exact HL]. split; [exact HB|]. rewrite HL, <- HL0. eapply wr_at_transport; eauto.
Qed.

Lemma arm_call : reac_headamp_tx_arm_scene_contract -> forall (t b w : Z) (T : list byte),
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 w -> 0 <= b < 256 -> 0 <= w < 256 ->
    rw_cells rsegs m t [CB 460 T] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(t, t + 460)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ rw_cells rsegs m' t [CB 460 (Tarm T b w)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_HEADAMP_TX_ARM_SCENE) fc None m (seg_rom rsegs)).
Proof.
  intros ARM t b w T ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Ha0 Ha1 Ha2 Hb Hw HT HI.
  destruct (cb_u8 _ _ _ _ HT) as [[HB HW] HL].
  eapply evt_mono; [eapply (ARM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                              t3 t4 t5 t6 F fc m t b w T); eauto; rewrite HL in HW; exact HW |].
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & Hp).
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [reflexivity|].
  unfold Tarm. destruct ((w =? 0) || (48 <=? b)).
  - subst m'. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact HI|exact HT].
  - destruct Hp as (HB' & MU & WM). split; [exact MU|]. split; [exact WM|]. split.
    + eapply mem_inv_munch1; [exact HI | exact MU |]. rewrite HL in HW. exact HW.
    + eapply cb_post; [exact HT | exact HB' | exact WM |]. rewrite arm_T_eq. lenT.
Qed.

Lemma rsw_call : reac_headamp_tx_set_resweep_contract -> forall (t per : Z) (T : list byte),
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 t -> bv_unsigned a1 mod 4294967296 = per mod 4294967296 ->
    rw_cells rsegs m t [CB 460 T] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(t, t + 460)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         rw_cells rsegs m' t [CB 460 (set_resweep_T T (Z_to_bv 64 per))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_HEADAMP_TX_SET_RESWEEP) fc None m (seg_rom rsegs)).
Proof.
  intros RSW t per T ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Ha0 Ha1 HT HI.
  destruct (cb_u8 _ _ _ _ HT) as [[HB HW] HL].
  eapply evt_mono; [eapply (RSW ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                              t3 t4 t5 t6 F fc m t T); eauto; rewrite HL in HW; exact HW |].
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & HB' & MU & WM).
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [reflexivity|].
  assert (E : set_resweep_T T a1 = set_resweep_T T (Z_to_bv 64 per)).
  { unfold set_resweep_T. f_equal. f_equal. rewrite <- (Z_to_bv_lit_self a1). apply le4_eqm. exact Ha1. }
  rewrite E in HB'.
  split; [exact MU|]. split; [exact WM|]. split.
  - eapply mem_inv_munch1; [exact HI | exact MU |]. rewrite HL in HW. exact HW.
  - eapply cb_post; [exact HT | exact HB' | exact WM |]. rewrite set_resweep_T_eq. lenT.
Qed.

Lemma memset_call : memset_contract -> forall (A : Z) (n : nat) (junk : list byte),
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 (Z.of_nat n) -> 0 <= A -> A + Z.of_nat n < 2 ^ 64 ->
    rw_cells rsegs m A [CB n junk] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(A, A + Z.of_nat n)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         rw_cells rsegs m' A [CB n (repeat (Z_to_bv 8 0) n)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 MEMSET) fc None m (seg_rom rsegs)).
Proof.
  intros MEMSET A n junk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Ha0 Ha1 Ha2 HA HAn HJ HI.
  assert (U0 : bv_unsigned a0 = A) by (subst a0; apply unsigned_lit; lia).
  assert (U2 : bv_unsigned a2 = Z.of_nat n) by (subst a2; apply unsigned_lit; lia).
  assert (U1 : bv_unsigned a1 mod 256 = 0) by (subst a1; reflexivity).
  eapply evt_mono.
  - apply (MEMSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m junk); [rewrite U0, U2, Nat2Z.id; exact HJ | exact HI].
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                -> & MU & WM & MI & RW).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [reflexivity|].
    rewrite U0, U2, U1, Nat2Z.id in *. split; [exact MU|]. split; [exact WM|]. split; [exact MI|exact RW].
Qed.

Lemma stk_merge3 : forall m lo a b hi (n : nat) bs, stk rsegs m lo a -> rw_cells rsegs m a [CB n bs] ->
  stk rsegs m b hi -> b = a + Z.of_nat n -> lo <= a -> b <= hi -> stk rsegs m lo hi.
Proof.
  intros m lo a b hi n bs S1 C S2 Eb Ha Hb. subst b.
  pose proof (stk_of_rw_cells rsegs m a _ C) as S3. cbn [cells_size csize] in S3. rewrite Nat.add_0_r in S3.
  eapply stk_merge; [eapply stk_merge; [exact S1 | exact S3 | ] | exact S2 | ];
    pose proof (rw_cells_bound rsegs m a _ C) as B; cbn [cells_size csize] in B; lia.
Qed.

Lemma cells_size_C8 : forall l, cells_size (map C8 l) = (8 * length l)%nat.
Proof. induction l as [|v l IH]; cbn [map cells_size csize length]; [reflexivity|]. rewrite IH. lia. Qed.
