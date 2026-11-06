From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import CtrlParsed disco_classify_c disco_table_c hunt_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_table_init_c reac_disco_gate_init_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_peer_lock_init_c reac_hunt_init_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_hunt_pin_c reac_hunt_silence_proven_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_lib slot_exit slot_R0_R3.
Import ListNotations.
Open Scope Z_scope.

Lemma mem_inv_munch_wr : forall m m' A n, mem_inv rsegs m -> wr_at rsegs m A n -> munch [(A, A + n)] m m' ->
  mem_inv rsegs m'.
Proof.
  intros m m' A n MI (HA & HN & HW) MU x b Hx.
  destruct (Z.le_gt_cases A (bv_unsigned x)) as [L1|L1];
    [destruct (Z.lt_ge_cases (bv_unsigned x) (A + n)) as [L2|L2]|].
  - assert (Ex : x = wa (A + (bv_unsigned x - A))).
    { unfold wa. replace (A + (bv_unsigned x - A)) with (bv_unsigned x) by lia. apply bv_eq.
      rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity | apply bv_unsigned_in_range]. }
    pose proof (HW (bv_unsigned x - A) ltac:(lia)) as W. rewrite <- Ex in W.
    destruct (m x) as [b0|] eqn:E.
    + exact (MI x b0 E).
    + exact (wview_not_ro rsegs m x W E).
  - rewrite (MU x) in Hx by (cbn; split; [lia | exact I]). exact (MI x b Hx).
  - rewrite (MU x) in Hx by (cbn; split; [lia | exact I]). exact (MI x b Hx).
Qed.

Definition R3 : Z := 0x133a8.

Lemma slot_R3 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X n h : Z) (jsp : list byte),
  sp = Z_to_bv 64 X -> s3 = Z_to_bv 64 n -> s4 = Z_to_bv 64 h ->
  0 <= X -> X + 2592 <= 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  rw_cells rsegs m X [CB 236 jsp] -> mem_inv rsegs m ->
  evt rsegs
    (fun ms' =>
       (n = 0 /\ ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 EXIT) fc None m (seg_rom rsegs)) \/
       (n <> 0 /\ exists (a0' a1' a2' a3' a5' a6' : word) (m' : word -> option byte) (j0 j1 j2 j3 j4 : list byte),
          ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 32) (Z_to_bv 64 0) a0' a1' a2' a3' (Z_to_bv 64 STALE_NS) a5' a6' a7
                        (Z_to_bv 64 WS_MASK) s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 NOW0) t3 t4 t5 t6)
                   F (Z_to_bv 64 HDR) fc None m' (seg_rom rsegs) /\
          munch [(X, X + 236)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
          rw_cells rsegs m' X (spill_cells j0 j1 j2 j3 j4 h)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R3) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X n h jsp Esp Es3 Es4 HX0 HX1 Hn SP MI.
  subst sp s3. unfold R3, EXIT, HDR.
  pose proof (munch_refl [(X, X + 236)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite eqb_lit by lia.
  destruct (Z.eqb_spec n 0) as [N0|N0]; cbn [negb].
  - step. apply evt_done. left. split; [exact N0 | reflexivity].
  - step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step.
    step. step. step. step. step. step. step. step.
    apply evt_done. right. split; [exact N0|]. unfold spill_cells.
    do 12 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. subst s4. exact SP.
Qed.

Lemma si_bat_addr : forall m a b bs, bytes_at rsegs m a bs -> a = b -> bytes_at rsegs m b bs.
Proof. intros; subst; assumption. Qed.

Lemma si_bat_app : forall m a b bs1 bs2, bytes_at rsegs m a bs1 -> bytes_at rsegs m b bs2 ->
  b = a + Z.of_nat (length bs1) -> bytes_at rsegs m a (bs1 ++ bs2).
Proof. intros m a b bs1 bs2 B1 B2 E. subst b. apply bytes_at_app. split; assumption. Qed.

Lemma si_wr_sub : forall m a n k j, wr_at rsegs m a n -> 0 <= k -> k + j <= n -> 0 <= j -> wr_at rsegs m (a + k) j.
Proof.
  intros m a n k j (Ha & Hn & H) Hk Hkj Hj. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + k + i) with (a + (k + i)) by lia. apply H. lia.
Qed.

Lemma si_rwc_bytes : forall m a n bs, rw_cells rsegs m a [CB n bs] -> bytes_at rsegs m a bs.
Proof. intros m a n bs [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. Qed.

Lemma si_rwc_of : forall m a n bs, bytes_at rsegs m a bs -> length bs = n -> wr_at rsegs m a (Z.of_nat n) ->
  rw_cells rsegs m a [CB n bs].
Proof.
  intros m a n bs B L W. split.
  - split; [cbn; split; [exact L | exact I]|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact W.
Qed.

Lemma si_firstn_l : forall {A} (l1 l2 : list A) n, (n <= length l1)%nat -> firstn n (l1 ++ l2) = firstn n l1.
Proof.
  intros A l1 l2 n H. rewrite firstn_app. replace (n - length l1)%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Lemma si_skipn_l : forall {A} (l1 l2 : list A) n, (n <= length l1)%nat -> skipn n (l1 ++ l2) = skipn n l1 ++ l2.
Proof. intros A l1 l2 n H. rewrite skipn_app. replace (n - length l1)%nat with 0%nat by lia. reflexivity. Qed.

Lemma si_pre412 : forall x : list byte,
  firstn 400 (repeat (Z_to_bv 8 0) 412 ++ x) = repeat (Z_to_bv 8 0) 400 /\
  firstn 12 (skipn 400 (repeat (Z_to_bv 8 0) 412 ++ x)) = repeat (Z_to_bv 8 0) 12.
Proof.
  intros x. split.
  - rewrite si_firstn_l by (rewrite repeat_length; lia). reflexivity.
  - rewrite si_skipn_l by (rewrite repeat_length; lia).
    rewrite si_firstn_l by (rewrite length_skipn, repeat_length; lia). reflexivity.
Qed.

Lemma si_hib_split : forall m h U now, length U = 6%nat -> bytes_at rsegs m h (hunt_init_bytes U now) ->
  bytes_at rsegs m h (repeat (Z_to_bv 8 0) 412 ++ U ++ repeat (Z_to_bv 8 0) 2) /\
  bytes_at rsegs m (h + 420) (repeat (Z_to_bv 8 0) 4) /\
  bytes_at rsegs m (h + 424) (le8 (Z_to_bv 64 now)) /\
  bytes_at rsegs m (h + 432) (repeat (Z_to_bv 8 0) 8) /\
  bytes_at rsegs m (h + 440) (repeat (Z_to_bv 8 0) 40).
Proof.
  intros m h U now LU B. unfold hunt_init_bytes in B.
  replace (repeat (Z_to_bv 8 0) 412 ++ U ++ repeat (Z_to_bv 8 0) 6 ++ le8 (Z_to_bv 64 now) ++ repeat (Z_to_bv 8 0) 48)
    with ((repeat (Z_to_bv 8 0) 412 ++ U ++ repeat (Z_to_bv 8 0) 2) ++ repeat (Z_to_bv 8 0) 4 ++
          le8 (Z_to_bv 64 now) ++ repeat (Z_to_bv 8 0) 8 ++ repeat (Z_to_bv 8 0) 40) in B
    by (rewrite <- !app_assoc; reflexivity).
  apply bytes_at_app in B as [B1 B]. apply bytes_at_app in B as [B2 B].
  apply bytes_at_app in B as [B3 B]. apply bytes_at_app in B as [B4 B5].
  assert (EL : forall k, length (repeat (Z_to_bv 8 0) k) = k) by (intros; apply repeat_length).
  split; [exact B1|].
  split; [eapply si_bat_addr; [exact B2 | rewrite !length_app, !EL, LU; lia]|].
  split; [eapply si_bat_addr; [exact B3 | rewrite !length_app, !EL, LU; lia]|].
  split; [eapply si_bat_addr; [exact B4 | rewrite !length_app, !EL, LU, length_le8; lia]|].
  eapply si_bat_addr; [exact B5 | rewrite !length_app, !EL, LU, length_le8; lia].
Qed.

Lemma si_hunt_pieces : forall m h U Q420 Q432 now,
  bytes_at rsegs m h (repeat (Z_to_bv 8 0) 412 ++ U ++ repeat (Z_to_bv 8 0) 2) ->
  bytes_at rsegs m (h + 420) Q420 -> bytes_at rsegs m (h + 424) (le8 (Z_to_bv 64 now)) ->
  bytes_at rsegs m (h + 432) Q432 -> bytes_at rsegs m (h + 440) (repeat (Z_to_bv 8 0) 40) ->
  length U = 6%nat -> length Q420 = 4%nat -> length Q432 = 8%nat ->
  wr_at rsegs m h 480 ->
  table_ok (firstn 400 (hunt_init_bytes U now)) -> lock_ok (firstn 12 (skipn 400 (hunt_init_bytes U now))) ->
  exists H, rw_cells rsegs m h [CB 480 H] /\ hunt_ok H /\ sub H 412 6 = U.
Proof.
  intros m h U Q420 Q432 now B1 B2 B3 B4 B5 LU L4 L8 WH TK LK.
  set (Rest := U ++ repeat (Z_to_bv 8 0) 2 ++ Q420 ++ le8 (Z_to_bv 64 now) ++ Q432 ++ repeat (Z_to_bv 8 0) 40).
  assert (LR : length Rest = 68%nat).
  { unfold Rest. rewrite !length_app, !repeat_length, LU, L4, L8, length_le8. reflexivity. }
  exists (repeat (Z_to_bv 8 0) 412 ++ Rest).
  assert (BA : bytes_at rsegs m h (repeat (Z_to_bv 8 0) 412 ++ Rest)).
  { unfold Rest.
    replace (repeat (Z_to_bv 8 0) 412 ++ U ++ repeat (Z_to_bv 8 0) 2 ++ Q420 ++ le8 (Z_to_bv 64 now) ++ Q432 ++
             repeat (Z_to_bv 8 0) 40)
      with ((repeat (Z_to_bv 8 0) 412 ++ U ++ repeat (Z_to_bv 8 0) 2) ++ Q420 ++ le8 (Z_to_bv 64 now) ++ Q432 ++
            repeat (Z_to_bv 8 0) 40) by (rewrite <- !app_assoc; reflexivity).
    apply (si_bat_app m h (h + 420)); [exact B1 | | rewrite !length_app, !repeat_length, LU; lia].
    apply (si_bat_app m (h + 420) (h + 424)); [exact B2 | | rewrite L4; lia].
    apply (si_bat_app m (h + 424) (h + 432)); [exact B3 | | rewrite length_le8; lia].
    apply (si_bat_app m (h + 432) (h + 440)); [exact B4 | exact B5 | rewrite L8; lia]. }
  assert (LH : length (repeat (Z_to_bv 8 0) 412 ++ Rest) = 480%nat) by (rewrite length_app, repeat_length, LR; reflexivity).
  split; [apply si_rwc_of; [exact BA | exact LH | exact WH]|].
  unfold hunt_init_bytes in TK, LK. rewrite (proj1 (si_pre412 _)) in TK. rewrite (proj2 (si_pre412 _)) in LK.
  split.
  - split; [exact LH|]. rewrite (proj1 (si_pre412 _)), (proj2 (si_pre412 _)). split; [exact TK|]. split; [exact LK|].
    assert (E440 : repeat (Z_to_bv 8 0) 412 ++ Rest =
                   (repeat (Z_to_bv 8 0) 412 ++ U ++ repeat (Z_to_bv 8 0) 2 ++ Q420 ++ le8 (Z_to_bv 64 now) ++ Q432)
                   ++ repeat (Z_to_bv 8 0) 40) by (unfold Rest; rewrite <- !app_assoc; reflexivity).
    unfold s32_at, u_at, sub. rewrite E440.
    match goal with |- context [skipn _ (?P ++ repeat (Z_to_bv 8 0) 40)] =>
      replace (Z.to_nat 440) with (length P)
        by (rewrite !length_app, !repeat_length, LU, L4, L8, length_le8; reflexivity)
    end.
    rewrite skipn_app_exact.
    match goal with |- context [bv_swrap 32 ?x] => replace (bv_swrap 32 x) with 0 by (vm_compute; reflexivity) end.
    lia.
  - unfold sub. rewrite si_skipn_l by (rewrite repeat_length; lia).
    rewrite skipn_all2 by (rewrite repeat_length; lia). cbn [app]. unfold Rest.
    rewrite si_firstn_l by lia. apply firstn_all2. lia.
Qed.

Ltac si_wq := first [ reflexivity | (f_equal; lia) | (rewrite ?unsigned_lit by lia; f_equal; lia) ].

Ltac si_fin := do 19 eexists; split; [reflexivity|]; repeat (split; [eassumption|]); eassumption.

Lemma si_bat_before : forall m m' A bs lo hi, bytes_at rsegs m A bs -> munch [(lo, hi)] m m' ->
  A + Z.of_nat (length bs) <= lo -> bytes_at rsegs m' A bs.
Proof. intros m m' A bs lo hi B MU L. eapply bytes_at_transport; [exact B | exact MU |]. cbn. split; [lia | exact I]. Qed.

Ltac si_len := rewrite ?length_app, ?repeat_length; cbn [length]; lia.

Lemma slot_R2 : reac_disco_table_init_contract -> reac_disco_gate_init_contract ->
  reac_disco_peer_lock_init_contract -> reac_hunt_init_contract ->
  reac_hunt_pin_contract -> reac_hunt_silence_proven_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X lo h : Z) (U jt jg jl jh : list byte),
  sp = Z_to_bv 64 X -> a0 = Z_to_bv 64 h ->
  0 < X -> X mod 16 = 0 -> X + 2592 < 2 ^ 63 ->
  0 < h -> h mod 16 = 0 -> h + 480 <= lo -> lo + 32 <= X ->
  rw_cells rsegs m (X + 236) [CB 12 jl] -> rw_cells rsegs m (X + 248) [CB 264 jg] ->
  rw_cells rsegs m (X + 512) [CB 400 jt] -> rw_cells rsegs m (X + 914) [CB 6 U] ->
  rw_cells rsegs m h [CB 480 jh] ->
  mem_inv rsegs m -> stk rsegs m lo X ->
  evt rsegs
    (fun ms' => exists (ra' s0' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                       (m' : word -> option byte) (H : list byte),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1 a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 (Z_to_bv 64 h) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 R3) fc None m' (seg_rom rsegs) /\
       munch [(lo, X); (X + 236, X + 912); (h, h + 480)] m m' /\ wmono rsegs m m' /\
       mem_inv rsegs m' /\ stk rsegs m' lo X /\
       rw_cells rsegs m' (X + 236) [CB 12 (repeat (zb 0) 12)] /\
       rw_cells rsegs m' (X + 248) [CB 264 (repeat (zb 0) 264)] /\
       rw_cells rsegs m' (X + 512) [CB 400 zero_table] /\
       rw_cells rsegs m' (X + 914) [CB 6 U] /\
       rw_cells rsegs m' h [CB 480 H] /\
       lock_ok (repeat (zb 0) 12) /\ gate_ok (repeat (zb 0) 264) /\ table_ok zero_table /\
       hunt_ok H /\ sub H 412 6 = U)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R2_RET) fc None m (seg_rom rsegs)).
Proof.
  intros TIC GIC LIC HIC PIC SIC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m X lo h U jt jg jl jh Esp Ea0 HX0 HX16 HX1 Hh0 Hh16 Hhlo Hlo RL RG RT RU RH MI ST.
  subst sp a0. unfold R3, R2_RET.
  assert (LU : length U = 6%nat) by exact (proj1 (proj1 (proj1 RU))).
  destruct U as [|u0 [|u1 [|u2 [|u3 [|u4 [|u5 [|u6 U']]]]]]]; cbn in LU; try lia. clear LU.
  assert (WL : wr_at rsegs m (X + 236) 12) by exact (proj2 RL).
  assert (WH : wr_at rsegs m h 480) by exact (proj2 RH).
  clear RL.
  pose proof (munch_refl [(lo, X); (X + 236, X + 912); (h, h + 480)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite eqb_lit by lia. replace (h =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
  step. step. step.
  eapply evt_cut.
  { eapply TIC with (t := X + 512) (junk := jt); [si_wq | lia | Z.div_mod_to_equations; lia | exact RT | exact MI]. }
  intros ms' (x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 &
              Eq & MU1 & WM1 & MI1 & RT1 & TOK). subst ms'.
  transport_after_call rsegs m m1 MU1 WM1. clear MU1 WM1 MI.
  rewrite (ret_pc_even 78684) by (first [lia | reflexivity]).
  step. step.
  eapply evt_cut.
  { eapply GIC with (g := X + 248) (junk := jg); [si_wq | exact RG | exact MI1]. }
  intros ms' (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 &
              Eq & MU2 & WM2 & MI2 & RG2 & GOK). subst ms'.
  transport_after_call rsegs m1 m2 MU2 WM2. clear MU2 WM2 MI1.
  rewrite (ret_pc_even 78692) by (first [lia | reflexivity]).
  step. step.
  eapply evt_cut.
  { eapply LIC with (l := X + 236); [si_wq | Z.div_mod_to_equations; lia | exact WL | exact MI2]. }
  intros ms' (m3 & Eq & MU3 & WM3 & MI3 & BL3 & LOK). subst ms'.
  transport_after_call rsegs m2 m3 MU3 WM3. clear MU3 WM3 MI2.
  pose proof (si_rwc_of m3 (X + 236) 12 _ BL3 eq_refl WL) as RL3. clear BL3.
  rewrite (ret_pc_even 78700) by (first [lia | reflexivity]).
  step. step. step. step. step.
  eapply evt_cut.
  { eapply HIC with (h := h) (our := X + 914) (now := NOW0) (lo := lo) (junk := jh)
      (ob := [u0; u1; u2; u3; u4; u5]).
    - reflexivity.
    - lia.
    - Z.div_mod_to_equations; lia.
    - exact RH.
    - si_wq.
    - lia.
    - intros _. split; [exact (si_rwc_bytes _ _ _ _ RU)|]. split; [reflexivity|]. split; [lia|].
      right. rewrite unsigned_lit by lia. lia.
    - unfold NOW0. si_wq.
    - unfold NOW0. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia.
    - left. lia.
    - exact MI3. }
  intros ms' (z5 & z6 & z7 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m4 &
              Eq & MU4 & WM4 & MI4 & ST4 & BH4 & TKH & LKH). subst ms'.
  rewrite (unsigned_lit X) in MU4, ST4 by lia.
  transport_after_call rsegs m3 m4 MU4 WM4. clear MU4 WM4 MI3.
  replace (X + 914 =? 0) with false in BH4, TKH, LKH by (symmetry; apply Z.eqb_neq; lia).
  cbv iota in BH4, TKH, LKH.
  destruct (si_hib_split m4 h [u0; u1; u2; u3; u4; u5] NOW0 eq_refl BH4) as (P1 & P2 & P3 & P4 & P5). clear BH4.
  rewrite (ret_pc_even 78720) by (first [lia | reflexivity]).
  step. step.
  match goal with |- context [bv_eqb ?x ?y] => destruct (bv_eqb x y) end; cbn [negb].
  - step. step. match goal with |- context [bv_eqb ?x ?y] => destruct (bv_eqb x y) end; cbn [negb].
    + apply evt_done.
      destruct (si_hunt_pieces m4 _ _ _ _ NOW0 P1 P2 P3 P4 P5 eq_refl eq_refl eq_refl WH TKH LKH)
        as (HH & RHH & HOKH & HSUBH).
      si_fin.
    + step. step.
      eapply evt_cut.
      { eapply SIC with (h := h);
          [ reflexivity | lia | Z.div_mod_to_equations; lia | apply (si_wr_sub m4 h 480 420 4 WH); lia ]. }
      intros ms' (a1x & m6 & Eq & MU6 & WM6 & B420). subst ms'.
      assert (MI6 : mem_inv rsegs m6)
        by (apply (mem_inv_munch_wr m4 m6 (h + 420) 4 MI4);
            [ apply (si_wr_sub m4 h 480 420 4 WH); lia | replace (h + 420 + 4) with (h + 424) by lia; exact MU6 ]).
      pose proof (si_bat_before m4 m6 _ _ _ _ P1 MU6 ltac:(si_len)) as Q1. clear P1. rename Q1 into P1.
      transport_after_call rsegs m4 m6 MU6 WM6. clear MU6 WM6 MI4.
      rewrite (ret_pc_even 78760) by (first [lia | reflexivity]).
      apply evt_done.
      destruct (si_hunt_pieces m6 _ _ _ _ NOW0 P1 B420 P3 P4 P5 eq_refl eq_refl eq_refl WH TKH LKH)
        as (HH & RHH & HOKH & HSUBH).
      si_fin.
  - step. step. step. step.
    eapply evt_cut.
    { eapply PIC with (h := h);
        [ reflexivity | lia | Z.div_mod_to_equations; lia | apply (si_wr_sub m4 h 480 432 8 WH); lia ]. }
    intros ms' (a2x & m5 & Eq & MU5 & WM5 & B432 & B436). subst ms'.
    assert (MI5 : mem_inv rsegs m5)
      by (apply (mem_inv_munch_wr m4 m5 (h + 432) 8 MI4);
          [ apply (si_wr_sub m4 h 480 432 8 WH); lia | replace (h + 432 + 8) with (h + 440) by lia; exact MU5 ]).
    pose proof (si_bat_before m4 m5 _ _ _ _ P1 MU5 ltac:(si_len)) as Q1. clear P1. rename Q1 into P1.
    pose proof (si_bat_before m4 m5 _ _ _ _ P2 MU5 ltac:(si_len)) as Q2. clear P2. rename Q2 into P2.
    transport_after_call rsegs m4 m5 MU5 WM5. clear MU5 WM5 MI4.
    pose proof (si_bat_app m5 (h + 432) (h + 436) _ _ B432 B436 ltac:(rewrite length_le4; lia)) as P4.
    clear B432 B436.
    rewrite (ret_pc_even 78744) by (first [lia | reflexivity]).
    step. step. match goal with |- context [bv_eqb ?x ?y] => destruct (bv_eqb x y) end; cbn [negb].
    + apply evt_done.
      destruct (si_hunt_pieces m5 _ _ _ _ NOW0 P1 P2 P3 P4 P5 eq_refl eq_refl eq_refl WH TKH LKH)
        as (HH & RHH & HOKH & HSUBH).
      si_fin.
    + step. step.
      eapply evt_cut.
      { eapply SIC with (h := h);
          [ reflexivity | lia | Z.div_mod_to_equations; lia | apply (si_wr_sub m5 h 480 420 4 WH); lia ]. }
      intros ms' (a1x & m6 & Eq & MU6 & WM6 & B420). subst ms'.
      assert (MI6 : mem_inv rsegs m6)
        by (apply (mem_inv_munch_wr m5 m6 (h + 420) 4 MI5);
            [ apply (si_wr_sub m5 h 480 420 4 WH); lia | replace (h + 420 + 4) with (h + 424) by lia; exact MU6 ]).
      pose proof (si_bat_before m5 m6 _ _ _ _ P1 MU6 ltac:(si_len)) as Q1. clear P1. rename Q1 into P1.
      transport_after_call rsegs m5 m6 MU6 WM6. clear MU6 WM6 MI5.
      rewrite (ret_pc_even 78760) by (first [lia | reflexivity]).
      apply evt_done.
      destruct (si_hunt_pieces m6 _ _ _ _ NOW0 P1 B420 P3 P4 P5 eq_refl eq_refl eq_refl WH TKH LKH)
        as (HH & RHH & HOKH & HSUBH).
      si_fin.
Qed.
