From Stdlib Require Import String ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import mix_call_c RecGlue RecStub RecSeq.
Import ListNotations.
Open Scope Z_scope.

Lemma da_seg_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (n : nat),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat ->
  evt rsegs (fun ms' => exists b0 b1 b2 m',
       ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10)
                     (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) b0 b1 b2 a3 a4 a5 a6 a7
                     a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1711c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (0x33d50, 0x33d54)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 32)
       /\ rw_cells rsegs m' (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x170c0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n ST LO LO2 NC Hn.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x33d50, 0x33d54)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 11 step.
  rewrite sx32_lit by lia.
  assert (C1 : negb (bv_eqb (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 16)) = true).
  { unfold bv_eqb. rewrite !unsigned_lit by lia. apply negb_true_iff, Z.eqb_neq. lia. }
  rewrite C1. cbv iota.
  do 7 step.
  rewrite da_addr by lia.
  apply evt_done.
  do 4 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma da_seg_eq :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 16)] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x170f8) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10)
                     s1 (Z_to_bv 64 0x33d10) (Z_to_bv 64 1) (Z_to_bv 64 16) a3 a4 a5 a6 a7
                     a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x155f0) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 32)
       /\ rw_cells rsegs m' (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x170c0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2 NC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 11 step.
  rewrite sx32_lit by lia.
  if_false.
  do 3 step.
  apply evt_done.
  eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma da_seg_tail :
  forall ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (junk : list byte),
  rw_cells rsegs m e [CB 8 junk] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x17138) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 e) (sel_null s2) a1 a2 a3 a4 a5 a6 a7
                     (sel_null s2) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m' (seg_rom rsegs)
       /\ munch [(e, e + 8)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' e [C4 (Z_to_bv 64 22); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 e) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x1711c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e junk EW.
  pose proof (rw_cells_bound _ _ _ _ EW) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (munch_refl [(e, e + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 2 step.
  apply (rw_cells_same_bytes _ _ _ [C4 (Z_to_bv 64 22); C4 (Z_to_bv 64 0)]) in EW;
    [| cbn; tauto | vm_compute; reflexivity | reflexivity].
  step.
  destruct (Z.eq_dec (bv_unsigned s2) 0) as [Z2|Z2].
  - if_false. do 4 step.
    unfold sel_null, NULL_LIT. rewrite (proj2 (Z.eqb_eq _ _) Z2).
    apply evt_done. eexists. split; [reflexivity|].
    split; [eassumption|]. split; eassumption.
  - if_true. do 2 step.
    unfold sel_null, NULL_LIT. rewrite (proj2 (Z.eqb_neq _ _) Z2).
    apply evt_done. eexists. split; [reflexivity|].
    split; [eassumption|]. split; eassumption.
Qed.

Lemma da_seg_rcf :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Q : machine_state -> Prop),
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) (Z_to_bv 64 0x33d10) a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x1711c) fc None m (seg_rom rsegs)) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x170f8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Q H.
  do 2 step. exact H.
Qed.

Lemma da_seg_xs :
  forall ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (junk : list byte) (st : word),
  rw_cells rsegs m (e + 4) [C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (e + 8) [CB 8 junk] ->
  rw_cells rsegs m 0x340f8 [C8 st] ->
  evt rsegs (fun ms' => exists b2 b3 m',
       ms' = MS (mkR (Z_to_bv 64 0x17160) sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) (Z_to_bv 64 e)
                     st (Z_to_bv 64 e) b2 b3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15ccc) fc None m' (seg_rom rsegs)
       /\ munch [(e + 4, e + 16)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (e + 4) [C4 (Z_to_bv 64 1)]
       /\ rw_cells rsegs m' (e + 8) [C8 a0])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) (Z_to_bv 64 e) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17138) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e junk st EN EA ES.
  pose proof (rw_cells_bound _ _ _ _ EN) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (rw_cells_bound _ _ _ _ EA) as EB8. cbn [cells_size csize Nat.add] in EB8.
  pose proof (munch_refl [(e + 4, e + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 5 step.
  rewrite sx32_lit by lia.
  replace (Z.shiftl (bv_unsigned (Z_to_bv 64 0)) 3) with 0 by reflexivity. rewrite Z.add_0_r.
  replace (bv_unsigned (Z_to_bv 64 0) + 1) with 1 by reflexivity.
  do 5 step.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma da_mix_ret : mix_call_contract ->
  forall gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo e p h : Z) (x slack : list byte)
    (sp1 ra0 s00 s01 s02 : word),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp1) -> lo + 80 <= bv_unsigned sp1 -> 0x34100 <= lo ->
  rw_cells rsegs m (bv_unsigned sp1) [C8 s02; C8 s01; C8 s00; C8 ra0] ->
  bytes_at rsegs m e (le4 (Z_to_bv 64 22) ++ le4 (Z_to_bv 64 1)) ->
  bytes_at rsegs m (e + 8) (le8 (Z_to_bv 64 p)) -> 0x33d10 <= e -> e + 56 <= 0x340f8 ->
  rw_cells rsegs m 0x340f8 [C8 (Z_to_bv 64 h)] -> 0 <= h < 2 ^ 64 -> 0 <= p < 2 ^ 64 ->
  bytes_at rsegs m p (x ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) x -> Z.of_nat (length x) <= LMAX ->
  (- (p + Z.of_nat (length x) + 1)) mod 8 <= Z.of_nat (length slack) ->
  p + Z.of_nat (length x) + 1 + Z.of_nat (length slack) <= bv_unsigned sp1 - 80 \/ bv_unsigned sp1 <= p ->
  evt rsegs (fun ms' => exists t0' t1' t2' b0 b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' m',
       ms' = MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp1 + 32)) gp tp t0' t1' t2' s00 s01 b0 b1 b2 b3 b4 b5 b6 b7
                     s02 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra0) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp1 - 80, bv_unsigned sp1); (0x340f8, 0x34100)] m m'
       /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x340f8 [C8 (Z_to_bv 64 (mixcall h 22 [x]))])
    (MS (mkR (Z_to_bv 64 0x17160) sp1 gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) (Z_to_bv 64 e)
             (Z_to_bv 64 h) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15ccc) fc None m (seg_rom rsegs)).
Proof.
  intros MIX gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo e p h x slack sp1 ra0 s00 s01 s02 MI ST LO LO2 FR EF EA E0 E16 ES Hh Hp HP NZ LX AL PW.
  assert (MIX' := MIX). unfold mix_call_contract, MIX_CALL_FRAME in MIX'.
  pose proof (bv_unsigned_in_range 64 sp1) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (munch_refl [(bv_unsigned sp1 - 80, bv_unsigned sp1); (0x340f8, 0x34100)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  call (MIX' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 22 [(Z_to_bv 64 p, x)]).
  - exact MI.
  - exact ST.
  - lia.
  - lia.
  - cbn. lia.
  - rewrite unsigned_lit by lia. exact EF.
  - rewrite unsigned_lit by lia. lia.
  - intros k p0 Hk. destruct k as [|k]; [|destruct k; discriminate].
    cbn in Hk. injection Hk as <-. unfold mc_arg. cbn [fst snd].
    rewrite !unsigned_lit by lia.
    split; [|split; [exact NZ|split; [exact LX|]]].
    + replace (e + 8 + 8 * Z.of_nat 0) with (e + 8) by lia. exact EA.
    + exists slack. split; [exact HP|]. split; [exact AL|]. exact PW.
  - eapply ro_bytes_at; [exact MI | unfold FNV_B0_ADDR; lia | rewrite length_le8; unfold FNV_B0_ADDR; lia |].
    apply ro_bytes_b_sound. vm_compute. reflexivity.
  - unfold FNV_B0_ADDR. lia.
  - rewrite (unsigned_lit h) by lia. cbn [map snd].
    do 7 step.
    apply evt_done. do 16 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma da_pre_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (n : nat),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat ->
  evt rsegs (fun ms' => exists b1 b2 m',
       ms' = MS (mkR (Z_to_bv 64 0x17138) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10)
                     (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) (sel_null a0) b1 b2 a3 a4 a5 a6 a7
                     (sel_null a0) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (0x33d50, 0x33d54);
                 (0x33d58 + 56 * Z.of_nat n, 0x33d58 + 56 * Z.of_nat n + 8)] m m'
       /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 32)
       /\ rw_cells rsegs m' (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))]
       /\ rw_cells rsegs m' (0x33d58 + 56 * Z.of_nat n) [C4 (Z_to_bv 64 22); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x170c0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n ST LO LO2 NC Hn.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  eapply evt_cut; [eapply da_seg_lt; eassumption|].
  intros ms (b0 & b1 & b2 & m1 & -> & MU1 & WM1 & ST1 & FR1 & NC1).
  destruct (glob_rw_cells m1 (0x33d58 + 56 * Z.of_nat n) 8) as [junk EW]; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia|].
  eapply evt_mono; [eapply da_seg_tail; exact EW|].
  intros ms' (m2 & -> & MU2 & WM2 & EF2).
  exists b1, b2, m2. split; [reflexivity|].
  split.
  { eapply munch_trans; [eapply munch_weaken; [|exact MU1] | eapply munch_weaken; [|exact MU2]];
      unfold sub_fp; cbn [outside]; intros; tauto. }
  split; [eapply wmono_trans; eassumption|].
  split.
  { eapply stk_transport_disjoint; [exact ST1 | exact MU2 | exact WM2 |]. cbn [disjoint_from]. split; [lia | exact I]. }
  split.
  { eapply rw_cells_transport; [exact FR1 | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize]. split; [lia | exact I]. }
  split.
  { eapply rw_cells_transport; [exact NC1 | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize]. split; [lia | exact I]. }
  exact EF2.
Qed.

Lemma da_tail : mix_call_contract ->
  forall ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo e p h : Z) (x slack junk : list byte)
    (sp1 ra0 s00 s01 s02 : word),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp1) -> lo + 80 <= bv_unsigned sp1 -> 0x34100 <= lo ->
  rw_cells rsegs m (bv_unsigned sp1) [C8 s02; C8 s01; C8 s00; C8 ra0] ->
  rw_cells rsegs m e [C4 (Z_to_bv 64 22); C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (e + 8) [CB 8 junk] -> 0x33d10 <= e -> e + 56 <= 0x340f8 ->
  rw_cells rsegs m 0x340f8 [C8 (Z_to_bv 64 h)] -> 0 <= h < 2 ^ 64 -> 0 <= p < 2 ^ 64 ->
  bytes_at rsegs m p (x ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) x -> Z.of_nat (length x) <= LMAX ->
  (- (p + Z.of_nat (length x) + 1)) mod 8 <= Z.of_nat (length slack) ->
  p + Z.of_nat (length x) + 1 + Z.of_nat (length slack) <= bv_unsigned sp1 - 80 \/ bv_unsigned sp1 <= p ->
  p + Z.of_nat (length x) + 1 + Z.of_nat (length slack) <= e + 4 \/ e + 16 <= p ->
  evt rsegs (fun ms' => exists t0' t1' t2' b0 b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' m',
       ms' = MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp1 + 32)) gp tp t0' t1' t2' s00 s01 b0 b1 b2 b3 b4 b5 b6 b7
                     s02 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra0) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp1 - 80, bv_unsigned sp1); (e + 4, e + 16); (0x340f8, 0x34100)] m m'
       /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (e + 4) [C4 (Z_to_bv 64 1)]
       /\ rw_cells rsegs m' (e + 8) [C8 (Z_to_bv 64 p)]
       /\ rw_cells rsegs m' 0x340f8 [C8 (Z_to_bv 64 (mixcall h 22 [x]))])
    (MS (mkR ra sp1 gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) (Z_to_bv 64 e) (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17138) fc None m (seg_rom rsegs)).
Proof.
  intros MIX ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo e p h x slack junk sp1 ra0 s00 s01 s02 MI ST LO LO2 FR EN EA E0 E56 ES Hh Hp HP NZ LX AL PW PE.
  pose proof (bv_unsigned_in_range 64 sp1) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (bytes_at_bound _ _ _ _ HP) as PB. rewrite length_app in PB. cbn [length] in PB.
  pose proof EN as EN'. apply cells_bytes_at in EN'. cbn [cells_bytes cbytes] in EN'. rewrite app_nil_r in EN'.
  apply bytes_at_app in EN' as [EF E4]. rewrite length_le4 in E4. change (Z.of_nat 4) with 4 in E4.
  assert (EN4 : rw_cells rsegs m (e + 4) [C4 (Z_to_bv 64 0)])
    by (apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia | exact E4]).
  eapply evt_cut; [eapply da_seg_xs; [exact EN4 | exact EA | exact ES] |].
  intros ms1 (b2' & b3' & m1 & -> & MU1 & WM1 & NA1 & AR1).
  assert (MI1 : mem_inv rsegs m1).
  { intros y b Hy. destruct (outside_dec [(e + 4, e + 16)] (bv_unsigned y)) as [O|O].
    - rewrite (MU1 y O) in Hy. exact (MI y b Hy).
    - pose proof (bv_unsigned_in_range 64 y) as Ry. unfold bv_modulus in Ry. cbn [outside] in O.
      assert (G : GLOB_LO <= bv_unsigned y < GLOB_LO + Z.of_nat GLOB_N) by (unfold GLOB_LO, GLOB_N; lia).
      pose proof (glob_ro_false _ G) as Hr. unfold wa in Hr. rewrite Z_to_bv_bv_unsigned in Hr. exact Hr. }
  assert (ST1 : stk rsegs m1 lo (bv_unsigned sp1)).
  { eapply stk_transport_disjoint; [exact ST | exact MU1 | exact WM1 |]. cbn [disjoint_from]. split; [lia | exact I]. }
  assert (FR1 : rw_cells rsegs m1 (bv_unsigned sp1) [C8 s02; C8 s01; C8 s00; C8 ra0]).
  { eapply rw_cells_transport; [exact FR | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add].
    split; [lia | exact I]. }
  assert (ES1 : rw_cells rsegs m1 0x340f8 [C8 (Z_to_bv 64 h)]).
  { eapply rw_cells_transport; [exact ES | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add].
    split; [lia | exact I]. }
  assert (EF1 : bytes_at rsegs m1 e (le4 (Z_to_bv 64 22) ++ le4 (Z_to_bv 64 1))).
  { apply bytes_at_app. rewrite length_le4. change (Z.of_nat 4) with 4. split.
    - eapply bytes_at_transport; [exact EF | exact MU1 |]. rewrite length_le4. cbn [disjoint_from].
      split; [lia | exact I].
    - apply cells_bytes_at in NA1. cbn [cells_bytes cbytes] in NA1. rewrite app_nil_r in NA1. exact NA1. }
  assert (EA1 : bytes_at rsegs m1 (e + 8) (le8 (Z_to_bv 64 p))).
  { apply cells_bytes_at in AR1. cbn [cells_bytes cbytes] in AR1. rewrite app_nil_r in AR1. exact AR1. }
  assert (HP1 : bytes_at rsegs m1 p (x ++ Z_to_bv 8 0 :: slack)).
  { eapply bytes_at_transport; [exact HP | exact MU1 |]. rewrite length_app. cbn [length disjoint_from].
    split; [lia | exact I]. }
  eapply evt_mono.
  { eapply (da_mix_ret MIX); [exact MI1 | exact ST1 | exact LO | exact LO2 | exact FR1 | exact EF1 | exact EA1 |
      exact E0 | exact E56 | exact ES1 | exact Hh | exact Hp | exact HP1 | exact NZ | exact LX | exact AL | exact PW]. }
  intros ms2 (t0' & t1' & t2' & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & ES2).
  exists t0', t1', t2', c0, c1, c2, c3, c4, c5, c6, c7, t3', t4', t5', t6', m2. split; [reflexivity|].
  split.
  { eapply munch_trans; [eapply munch_weaken; [|exact MU1] | eapply munch_weaken; [|exact MU2]];
      unfold sub_fp; cbn [outside]; intros; tauto. }
  split; [eapply wmono_trans; eassumption|].
  split.
  { eapply rw_cells_transport; [exact NA1 | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add].
    split; [lia | split; [lia | exact I]]. }
  split; [|exact ES2].
  eapply rw_cells_transport; [exact AR1 | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add].
  split; [lia | split; [lia | exact I]].
Qed.

From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK14 YP09 YO0i YO0f YO0d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecInvP RecKindB RecStep.

Lemma rw_cells_norm_hi : forall m a cs, ro_agree rsegs m -> 2 ^ 20 <= a -> rw_cells rsegs m a cs ->
  rw_cells rsegs (normalize rsegs m) a cs.
Proof.
  intros m a cs RA Ha [[Hwf Hb] Hw]. split; [split; [exact Hwf | exact (bytes_at_normalize rsegs m _ _ RA Hb)]|].
  apply (wr_at_norm rsegs m); [exact (mem_rel_normalize rsegs m RA) | exact Hw |].
  intros i Hi. destruct Hw as (H1 & H2 & _). unfold wa. apply ro_addr_hi. lia.
Qed.

Lemma rw_cells_norm_glob : forall m a cs, ro_agree rsegs m -> GLOB_LO <= a ->
  a + Z.of_nat (cells_size cs) <= GLOB_LO + Z.of_nat GLOB_N -> rw_cells rsegs m a cs ->
  rw_cells rsegs (normalize rsegs m) a cs.
Proof.
  intros m a cs RA H1 H2 [[Hwf Hb] Hw]. split; [split; [exact Hwf | exact (bytes_at_normalize rsegs m _ _ RA Hb)]|].
  apply (wr_at_norm rsegs m); [exact (mem_rel_normalize rsegs m RA) | exact Hw |].
  intros i Hi. apply glob_ro_false. lia.
Qed.

Lemma slack_rebuild : forall m s x, bytes_at rsegs m s (x ++ [Z_to_bv 8 0]) -> 0 <= s ->
  s + Z.of_nat (length x) + 1 + 8 <= 2 ^ 64 ->
  (forall a, s + (Z.of_nat (length x) + 1) <= a < 8 * ((s + (Z.of_nat (length x) + 1) + 7) / 8) -> present m a) ->
  exists slack, bytes_at rsegs m s (x ++ Z_to_bv 8 0 :: slack) /\
    (- (s + Z.of_nat (length x) + 1)) mod 8 <= Z.of_nat (length slack) /\ Z.of_nat (length slack) <= 7 /\
    Z.of_nat (length slack) = (- (s + Z.of_nat (length x) + 1)) mod 8.
Proof.
  intros m s x H H0 H1 HP.
  destruct (slack_bytes rsegs m s (Z.of_nat (length x) + 1) (x ++ [Z_to_bv 8 0]) H
              ltac:(rewrite length_app; cbn [length]; lia) H0 ltac:(lia) HP) as (sl & HB & HL).
  exists sl. rewrite <- app_assoc in HB. cbn [app] in HB. split; [exact HB|].
  rewrite HL. split; [|split]; Z.div_mod_to_equations; lia.
Qed.

Lemma present_of_mbyte : forall m a b, mbyte rsegs m a = Some b -> seg_rom rsegs (Z_to_bv 64 a) = None -> present m a.
Proof.
  intros m a b H N. unfold mbyte in H. unfold present.
  destruct (m (Z_to_bv 64 a)) as [c|]; [exists c; reflexivity | rewrite N in H; discriminate].
Qed.

Definition st_ovl (m1 m2 : word -> option byte) : word -> option byte :=
  fun y => if (0x340f8 <=? bv_unsigned y) && (bv_unsigned y <? 0x34100) then m1 y else m2 y.

Lemma st_ovl_munch_r : forall m1 m2, munch [(0x340f8, 0x34100)] (st_ovl m1 m2) m2.
Proof.
  intros m1 m2 y Hy. cbn [outside] in Hy. unfold st_ovl.
  destruct ((0x340f8 <=? bv_unsigned y) && (bv_unsigned y <? 0x34100)) eqn:E; [|reflexivity].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. exfalso. apply (proj1 Hy). lia.
Qed.

Lemma st_ovl_munch_l : forall W m1 m2, munch ((0x340f8, 0x34100) :: W) m1 m2 -> munch W m1 (st_ovl m1 m2).
Proof.
  intros W m1 m2 MU y Hy. unfold st_ovl.
  destruct ((0x340f8 <=? bv_unsigned y) && (bv_unsigned y <? 0x34100)) eqn:E; [reflexivity|].
  apply MU. cbn [outside]. split; [|exact Hy]. intros (H1 & H2).
  apply andb_false_iff in E. destruct E as [E|E]; [apply Z.leb_gt in E | apply Z.ltb_ge in E]; lia.
Qed.

Lemma st_ovl_munch_r2 : forall m1 m2, munch [(0x340f8, 0x34100)] m2 (st_ovl m1 m2).
Proof.
  intros m1 m2 y Hy. symmetry. exact (st_ovl_munch_r m1 m2 y Hy).
Qed.

Lemma mbyte_ovl_in : forall m1 m2 a, 0x340f8 <= a < 0x34100 -> mbyte rsegs (st_ovl m1 m2) a = mbyte rsegs m1 a.
Proof.
  intros m1 m2 a Ha. unfold mbyte, st_ovl. rewrite unsigned_lit by lia.
  rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma mbyte_ovl_out : forall m1 m2 a, 0 <= a < 2 ^ 64 -> ~ (0x340f8 <= a < 0x34100) ->
  mbyte rsegs (st_ovl m1 m2) a = mbyte rsegs m2 a.
Proof.
  intros m1 m2 a Ha N. unfold mbyte, st_ovl. rewrite unsigned_lit by lia.
  destruct ((0x340f8 <=? a) && (a <? 0x34100)) eqn:E; [|reflexivity].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

Lemma da_rec : forall L A mc L' A' mf R O x p k,
  rec_rep rsegs G_REC REC_SC L A mc (rec_record R 22 []) O -> 0 <= r_state R < 2 ^ 64 ->
  bytes_at rsegs mf (rec_entry G_REC REC_SC R + 4) (le4 (Z_to_bv 64 1)) ->
  bytes_at rsegs mf (rec_entry G_REC REC_SC R + 8) (le8 (Z_to_bv 64 p)) ->
  bytes_at rsegs mf 0x340f8 (le8 (Z_to_bv 64 (mixcall (r_state R) 22 [x]))) ->
  (forall a, rec_area a -> ~ (rec_entry G_REC REC_SC R + 4 <= a < rec_entry G_REC REC_SC R + 16) ->
     ~ (0x340f8 <= a < 0x34100) -> mbyte rsegs mf a = mbyte rsegs mc a) ->
  (forall pn, In pn O -> In pn (blocks L' A') /\
     forall i, 0 <= i < snd pn -> mbyte rsegs mf (fst pn + i) = mbyte rsegs mc (fst pn + i)) ->
  (forall pn i, In pn O -> 0 <= i < snd pn -> 0 <= fst pn + i < 2 ^ 64 /\ ~ (0x340f8 <= fst pn + i < 0x34100)) ->
  ~ In p (map fst O) -> p <> 0 -> In (p, k) (blocks L' A') ->
  no0 x -> Z.of_nat (length x) <= LMAX -> k = Z.of_nat (length x) + 1 -> 0 <= p ->
  bytes_at rsegs mf p (x ++ [Z_to_bv 8 0]) ->
  iv_apart p k G_REC REC_SIZE -> iv_apart p k REC_SC SC_SIZE ->
  rec_rep rsegs G_REC REC_SC L' A' mf (rec_stub_mix R 22 [x]) (O ++ [(p, k)]).
Proof.
  intros L A mc L' A' mf R O x p k HR HS BN BA BS KG KB KO NI P0 IN N0 LX EK PL BX AP1 AP2.
  subst k.
  pose proof (bytes_at_bound _ _ _ _ BX) as XB. rewrite length_app in XB. cbn [length] in XB.
  assert (EB : 0x33d10 <= rec_entry G_REC REC_SC R /\ rec_entry G_REC REC_SC R + 56 <= 0x340f8).
  { unfold rec_entry. destruct (Nat.ltb (length (r_calls R)) 16) eqn:E.
    - apply Nat.ltb_lt in E. unfold G_REC, OFF_CALLS, CALL_SIZE. lia.
    - unfold REC_SC. lia. }
  set (e := rec_entry G_REC REC_SC R) in *.
  assert (HR1 : rec_rep rsegs G_REC REC_SC L' A' (st_ovl mc mf) (rec_record R 22 ([] ++ [x])) (O ++ [(p, Z.of_nat (length x) + 1)])).
  { apply (rec_rep_arg rsegs G_REC REC_SC L A mc L' A' (st_ovl mc mf) R 22 [] O x p (Z.of_nat (length x) + 1) HR).
    - cbn. lia.
    - fold e. unfold CALL_OFF_NARGS. cbn [length]. change (Z.of_nat 0 + 1) with 1.
      eapply bytes_at_transport; [exact BN | exact (st_ovl_munch_r2 mc mf) |]. rewrite length_le4.
      cbn [disjoint_from]. split; [lia | exact I].
    - fold e. unfold CALL_OFF_ARGS. cbn [length]. change (8 * Z.of_nat 0) with 0. rewrite Z.add_0_r.
      eapply bytes_at_transport; [exact BA | exact (st_ovl_munch_r2 mc mf) |]. rewrite length_le8.
      cbn [disjoint_from]. split; [lia | exact I].
    - fold e. intros a Ha N1 N2. unfold CALL_OFF_NARGS, CALL_OFF_ARGS in *. cbn [length] in N2.
      unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha.
      destruct (Z_lt_ge_dec a 0x340f8) as [D|D]; [|destruct (Z_lt_ge_dec a 0x34100) as [D'|D']].
      + rewrite mbyte_ovl_out by lia. apply KG; [unfold rec_area, G_REC, REC_SIZE, REC_SC, SC_SIZE; lia | lia | lia].
      + rewrite mbyte_ovl_in by lia. reflexivity.
      + rewrite mbyte_ovl_out by lia. apply KG; [unfold rec_area, G_REC, REC_SIZE, REC_SC, SC_SIZE; lia | lia | lia].
    - intros a Ha _. apply glob_writable. unfold G_REC, REC_SIZE, REC_SC, SC_SIZE, GLOB_LO, GLOB_N in *. lia.
    - intros pn Hpn. destruct (KB pn Hpn) as [Hb Hk]. split; [exact Hb|]. intros i Hi.
      destruct (KO pn i Hpn Hi) as [R1 R2]. rewrite mbyte_ovl_out by assumption. exact (Hk i Hi).
    - exact NI.
    - exact P0.
    - exact IN.
    - exact N0.
    - exact LX.
    - lia.
    - eapply bytes_at_transport; [exact BX | exact (st_ovl_munch_r2 mc mf) |]. rewrite length_app. cbn [length].
      cbn [disjoint_from]. split; [unfold iv_apart, G_REC, REC_SIZE in AP1; lia | exact I].
    - exact AP1.
    - exact AP2. }
  cbn [app] in HR1.
  assert (HR2 : rec_rep rsegs G_REC REC_SC L' A' mf (set_state (rec_record R 22 [x]) (mixcall (r_state R) 22 [x]))
                  (O ++ [(p, Z.of_nat (length x) + 1)])).
  { apply (rec_rep_set_state rsegs G_REC REC_SC L' A' (st_ovl mc mf) mf _ _ _ HR1).
    - apply mixcall_range. exact HS.
    - unfold G_REC, OFF_STATE. change (0x33d48 + 944) with 0x340f8. exact BS.
    - intros a Ha N. unfold G_REC, OFF_STATE, REC_SIZE, REC_SC, SC_SIZE in *.
      rewrite mbyte_ovl_out by lia. reflexivity.
    - intros a Ha _. apply glob_writable. unfold G_REC, REC_SIZE, REC_SC, SC_SIZE, GLOB_LO, GLOB_N in *. lia.
    - intros q n i Hq Hi. apply in_app_or in Hq as [Hq|[Hq|[]]].
      + destruct (KO (q, n) i Hq Hi) as [R1 R2]. cbn [fst snd] in *. rewrite mbyte_ovl_out by assumption. reflexivity.
      + injection Hq as <- <-. unfold iv_apart, G_REC, REC_SIZE in AP1.
        rewrite mbyte_ovl_out by lia. reflexivity. }
  unfold rec_stub_mix, rec_mix. cbn [fst snd]. rewrite r_state_record. exact HR2.
Qed.


From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK15 YM06 YO05 YO0p YO0j YO0m YO0l
YO0n YO0k YO09 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecCore.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecAnsB RecTail snprintf_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import xstrdup_c rec_calls_free_c descriptors_add_c.
Open Scope Z_scope.

Lemma da_glob : forall a, 0x33d10 <= a < 0x3410c -> GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N.
Proof. intros a H. unfold GLOB_LO. change (Z.of_nat GLOB_N) with 1020. lia. Qed.

Lemma da_cell8 : forall m a v, GLOB_LO <= a -> a + 8 <= GLOB_LO + Z.of_nat GLOB_N ->
  bytes_at rsegs m a (le8 v) -> rw_cells rsegs m a [C8 v].
Proof.
  intros m a v H1 H2 H. apply (rw_cells_same_bytes _ _ [CB (length (le8 v)) (le8 v)]).
  - apply bytes_rw_cells; [lia | rewrite length_le8; lia | exact H].
  - cbn. split; exact I.
  - reflexivity.
  - cbn [cells_size csize]. rewrite length_le8. reflexivity.
Qed.

Lemma da_nra_apart : forall s Ln lo hi, (forall a, s <= a < s + Ln -> ~ rec_area a) ->
  REC_SC <= lo -> hi <= G_REC + REC_SIZE -> lo < hi -> 0 < Ln -> s + Ln <= lo \/ hi <= s.
Proof.
  intros s Ln lo hi H H1 H2 H3 H4. destruct (Z_le_gt_dec (s + Ln) lo) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec hi s) as [D'|D']; [right; exact D'|]. exfalso.
  unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in *.
  destruct (Z_le_gt_dec s lo) as [D1|D1].
  - apply (H lo); [lia|]. destruct (Z_lt_ge_dec lo 212296); [left | right]; lia.
  - apply (H s); [lia|]. destruct (Z_lt_ge_dec s 212296); [left | right]; lia.
Qed.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22a68.
Hypothesis GRD : ms_guard B = 0x54450.
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis GERR : forall a, in_globals frame_G a -> ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis RCF : rec_calls_free_contract B API.
Hypothesis XSD : xstrdup_contract B API.
Hypothesis MIX : mix_call_contract.

Definition da_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (uri : option (list byte)) (R : rstate) (O : list (Z * Z)) (b : sbound) (c' : config) : Prop :=
  exists L' A' regs' mem' md' O',
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\
    call_post_rec B (aa_MR API) DESCRIPTORS_ADD_K L A regs mem md rec_area (fun a => In a (map fst O))
      L' A' regs' mem' md' /\
    g_rec_rep rsegs L' A' mem' (descriptors_add_m R uri) O' /\ owns_new L A O O' /\
    (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O') /\
    others_kept rsegs L A mem L' A' mem' O /\
    ro_agree rsegs mem' /\ f18_words rsegs mem' /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    sb_le (sb_shift b A A') (sb_mallocs b (descriptors_add_sizes uri)) /\
    res_ok_slots A' (sb_shift b A A').

Lemma da_arg : forall L A regs mem md uri R O b Lc Ac mc mdc Oc regs_c s slack,
  call_pre_k B (aa_MR API) DESCRIPTORS_ADD_K L A regs mem md ->
  sinv B API 8288 (spZ regs) L A mem md O Lc Ac mc mdc (rec_record R 22 []) Oc b ->
  sb_le (sb_shift b A Ac) b ->
  room_slots (sb_mallocs b (descriptors_add_sizes uri)) (LMAX + 1) ->
  rw_cells rsegs mc (spZ regs - 32) [C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] ->
  rw_cells rsegs mc (rec_entry G_REC REC_SC R) [C4 (Z_to_bv 64 22); C4 (Z_to_bv 64 0)] ->
  bytes_at rsegs mc s (sarg uri ++ Z_to_bv 8 0 :: slack) ->
  no0 (sarg uri) -> Z.of_nat (length (sarg uri)) <= LMAX ->
  (- (s + Z.of_nat (length (sarg uri)) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (s + Z.of_nat (length (sarg uri ++ Z_to_bv 8 0 :: slack)) <= spZ regs - 8288 \/ spZ regs <= s) ->
  str_home B Lc Ac (spZ regs) s (Z.of_nat (length (sarg uri)) + 1) ->
  getr regs_c 1 = Z_to_bv 64 0x17138 -> getr regs_c 2 = Z_to_bv 64 (spZ regs - 32) ->
  getr regs_c 8 = Z_to_bv 64 0x33d10 -> getr regs_c 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  getr regs_c 10 = Z_to_bv 64 s ->
  kept_ex [2; 8; 9; 18] regs regs_c ->
  SR rsegs (mkCfg (mkst regs_c (Z_to_bv 64 XSTRDUP) mc (seg_rom rsegs)) mdc) (da_ret L A regs mem md uri R O b).
Proof using SEGS ERRNO_LOW GOTG GRD GOWN GERR AX CTX SLACK XSD MIX.
  intros L A regs mem md uri R O b Lc Ac mc mdc Oc regs_c s slack PRE SI BLE ROOM FR EN BS N0 LX AL DJ HOME
    C1 C2 HC8 HC9 C10 KE.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold DESCRIPTORS_ADD_K in HCEIL, HWS.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  pose proof RJ as (HM & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  set (x := sarg uri) in *.
  assert (EB : 0x33d10 <= rec_entry G_REC REC_SC R /\ rec_entry G_REC REC_SC R + 56 <= 0x340f8).
  { unfold rec_entry. destruct (Nat.ltb (length (r_calls R)) 16) eqn:E.
    - apply Nat.ltb_lt in E. unfold G_REC, OFF_CALLS, CALL_SIZE. lia.
    - unfold REC_SC. lia. }
  set (e := rec_entry G_REC REC_SC R) in *.
  destruct EB as (EB1 & EB2).
  pose proof GR as (Q & HRep & HO).
  pose proof HRep as (HS & HC & HA & HP & HX & HW).
  destruct HX as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10).
  rewrite r_state_record in Y4, Y9. unfold G_REC, OFF_STATE in Y4.
  assert (SPc : spZ regs_c = bv_unsigned sp - 32) by (unfold spZ; rewrite C2; apply unsigned_lit; lia).
  assert (PREc : call_pre_k B (aa_MR API) XSTRDUP_K Lc Ac regs_c mc mdc).
  { apply (call_pre_k_of_rjr B _ 8288 (bv_unsigned sp) rec_area _ L A mem md Lc Ac mc mdc XSTRDUP_K regs_c RJ).
    - rewrite C1. apply bv_eq. vm_compute. reflexivity.
    - rewrite SPc. replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring.
      rewrite Z.mod_add by lia. exact HAL.
    - unfold XSTRDUP_K, ALLOC_STACK. lia.
    - rewrite SPc. unfold XSTRDUP_K, ALLOC_STACK. lia.
    - rewrite SPc. lia.
    - exact (eq_trans (KE 4 ltac:(unfold callee_saved; lia) ltac:(cbn [In]; lia)) HTP). }
  set (k := Z.of_nat (length x) + 1) in *.
  assert (ROOM0 : room_slots (sb_malloc (sb_shift b A Ac) k) k).
  { unfold sb_mallocs, descriptors_add_sizes in ROOM. cbn [fold_left] in ROOM. fold x k in ROOM.
    apply (room_slots_mono _ (sb_malloc b k) k (LMAX + 1)); [exact (sb_malloc_mono _ _ _ BLE) | unfold k, LMAX in *; lia |
      exact ROOM]. }
  pose proof XSD as XS. unfold xstrdup_contract in XS. rewrite SEGS in XS.
  eapply SR_bind.
  { apply (XS Lc Ac regs_c mc mdc s x slack (sb_shift b A Ac) PREc C10 BS N0 LX AL).
    - rewrite SPc. unfold XSTRDUP_K, ALLOC_STACK. destruct DJ; [left; lia | right; lia].
    - rewrite SPc. unfold str_home in HOME |- *.
      destruct HOME as [H|[H|H]]; [left; lia | right; left; exact H | right; right; exact H].
    - exact RS.
    - exact ROOM0.
    - exact RA. }
  intros c2 RET.
  destruct RET as (L2 & A2 & R2 & m2 & md2 & p & -> & POST & A0' & PNZ & PAL & FRESH & (l1 & l2 & BL2 & BL1) & BKP & UB
    & BYP & BYS & RA2 & GK & INIT & RGN & RES2).
  unfold blocks_kept in BKP. rewrite SEGS in BKP, BYP, RA2.
  pose proof POST as (PM & PW & PB' & PL & PA & PR & PV & PF & PK & PS).
  rewrite SEGS in PF.
  destruct FRESH as (FP1 & FP2 & FP3).
  assert (PG : p + k <= 0x33d10 \/ 0x3410c <= p).
  { destruct (Z_le_gt_dec (p + k) 0x33d10) as [D|D]; [left; exact D|].
    destruct (Z_le_gt_dec 0x3410c p) as [D'|D']; [right; exact D'|]. exfalso.
    apply (FP3 (Z.max p 0x33d10 - p)); [unfold k in *; lia|]. replace (p + (Z.max p 0x33d10 - p)) with (Z.max p 0x33d10) by ring.
    apply (glob_in_img B SEGS). apply da_glob. unfold k in *; lia. }
  assert (KST : forall a, bv_unsigned sp - 32 <= a < bv_unsigned sp ->
            mbyte rsegs m2 a = mbyte rsegs mc a /\ (writable_at rsegs mc a <-> writable_at rsegs m2 a)).
  { intros a Ha. apply PF.
    - left. lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS Lc Ac mc mdc a HM Ho). lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS L2 A2 m2 md2 a PM Ho). lia.
    - intros [Hs|He]; [rewrite SPc in Hs; lia | lia].
    - cbv beta. lia. }
  assert (KG : forall a, 0x33d10 <= a < 0x3410c -> mbyte rsegs m2 a = mbyte rsegs mc a).
  { intros a Ha. pose proof (da_glob a Ha) as GA. apply PF.
    - right. exact (glob_in_img B SEGS a GA).
    - exact (GOWN _ _ _ _ a HM (glob_in a GA)).
    - exact (GOWN _ _ _ _ a PM (glob_in a GA)).
    - intros [Hs|He]; [rewrite SPc in Hs; unfold XSTRDUP_K, ALLOC_STACK in Hs; lia | exact (GERR a (glob_in a GA) He)].
    - cbv beta. lia. }
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 32) [C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transfer rsegs mc); [exact FR|]. intros i Hi. cbn in Hi.
    destruct (KST (bv_unsigned sp - 32 + i) ltac:(lia)) as [E1 E2]. split; [exact E1 | exact (proj1 E2)]. }
  assert (EN2 : rw_cells rsegs m2 e [C4 (Z_to_bv 64 22); C4 (Z_to_bv 64 0)]).
  { apply (rw_cells_transfer rsegs mc); [exact EN|]. intros i Hi. cbn in Hi.
    split; [apply KG; lia | intros _; apply glob_writable; apply da_glob; lia]. }
  assert (ST2 : bytes_at rsegs m2 0x340f8 (le8 (Z_to_bv 64 (r_state R)))).
  { apply (bytes_at_transfer rsegs mc); [exact Y4|]. intros i Hi. rewrite length_le8 in Hi. apply KG. lia. }
  destruct (mr_model B _ LAWS L2 A2 m2 md2 PM) as (Hh2 & Hl2 & _).
  assert (RJ2 : rjr B (aa_MR API) 8288 (bv_unsigned sp) rec_area (fun pn => In pn O) L A mem md L2 A2 m2 md2).
  { apply (rjr_post B _ SEGS LAWS AX ERRNO_LOW 8288 (bv_unsigned sp) rec_area _ L A mem md Lc Ac mc mdc XSTRDUP_K regs_c
             _ (fun _ => False) L2 A2 R2 m2 md2 RJ (call_post_k_rec B _ _ _ _ _ _ _ _ _ _ _ _ _ POST)).
    - rewrite SPc. unfold XSTRDUP_K, ALLOC_STACK. lia.
    - rewrite SPc. lia.
    - intros a Ha Hf. exfalso. cbv beta in Ha. destruct Hf as [Hf|(Hf & _)]; [lia|].
      apply (FP3 (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact Hf.
    - intros p0 n0 _ _ _ [].
    - intros p0 n0 _ H1 H2. exfalso. exact (H2 (UB p0 n0 H1)).
    - exact RGN.
    - intros Hf. rewrite INIT in Hf. discriminate. }
  assert (PIN : In (p, k) (blocks L2 A2)) by (rewrite BL2; apply in_or_app; right; left; reflexivity).
  destruct (slack_rebuild m2 p x BYP ltac:(lia) ltac:(unfold k in *; lia)
              (fun a Ha => SLACK L2 A2 m2 md2 p k a PM PIN Ha)) as (slp & BP & ALp & SL7 & SLe).
  assert (Q2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp - 32)) by exact (eq_trans (PR 2 ltac:(unfold callee_saved; lia)) C2).
  assert (Q8 : reg_get R2 8 = Z_to_bv 64 0x33d10) by exact (eq_trans (PR 8 ltac:(unfold callee_saved; lia)) HC8).
  assert (Q9 : reg_get R2 9 = Z_to_bv 64 e) by exact (eq_trans (PR 9 ltac:(unfold callee_saved; lia)) HC9).
  assert (Q10 : reg_get R2 10 = Z_to_bv 64 p) by exact A0'.
  assert (SP1v : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 32)) = bv_unsigned sp - 32) by (apply unsigned_lit; lia).
  destruct (glob_rw_cells (normalize rsegs m2) (e + 8) 8 ltac:(unfold GLOB_LO; lia) ltac:(unfold GLOB_LO, GLOB_N; lia))
    as [junk EA].
  pose proof RJ2 as (_ & _ & _ & _ & _ & HLen2 & _ & _ & _ & _ & _ & _ & _ & HSC2 & _).
  rewrite SEGS, C1.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q2, Q8, Q9, Q10.
    eapply (evt_normalize rsegs); [exact wx_apart_rsegs | exact RA2 |].
    eapply (da_tail MIX) with (lo := bv_unsigned sp - 8288).
    - apply mem_inv_normalize.
    - rewrite SP1v. apply stk_norm; [lia | lia |]. intros a Ha. rewrite <- SEGS. apply HSC2. left. lia.
    - rewrite SP1v. lia.
    - lia.
    - rewrite SP1v. apply rw_cells_norm_hi; [exact RA2 | lia | exact FR2].
    - apply rw_cells_norm_glob; [exact RA2 | unfold GLOB_LO; lia | cbn [cells_size csize Nat.add]; unfold GLOB_LO, GLOB_N; lia |
        exact EN2].
    - exact EA.
    - lia.
    - lia.
    - apply da_cell8; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia |]. apply (bytes_at_normalize rsegs m2 _ _ RA2). exact ST2.
    - exact Y9.
    - lia.
    - apply (bytes_at_normalize rsegs m2 _ _ RA2). exact BP.
    - exact N0.
    - exact LX.
    - exact ALp.
    - left. rewrite SP1v. unfold k in *. lia.
    - unfold k in PG. destruct PG as [PG|PG]; [left | right; lia]. rewrite SLe. Z.div_mod_to_equations. lia. }
  intros ms3 (can3 & (s3 & Q3 & REL3 & RO3) & EQ3).
  destruct Q3 as (t0' & t1' & t2' & c0 & c1 & c2' & c3 & c4 & c5 & c6 & c7 & t3' & t4' & t5' & t6' & m3n & -> & MU3n & WM3n
    & NA3n & AR3n & ES3n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL3) as [EC3 MR3r].
  revert EC3 MR3r RO3 EQ3. generalize (ms_mem can3) as m3. intros m3 EC3 MR3r RO3 EQ3. subst can3.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m2 RA2) MR3r RO3 MU3n) as MU3.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m2 RA2) MR3r RO3 WM3n) as WM3.
  pose proof (ro_agree_same rsegs _ _ RA2 RO3) as RA3.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR3r NA3n) as NA3.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR3r AR3n) as AR3.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR3r ES3n) as ES3.
  clear MU3n WM3n NA3n AR3n ES3n MR3r.
  rewrite SP1v in MU3.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  apply SR_ret. unfold da_ret.
  set (W3 := [(bv_unsigned sp - 32 - 80, bv_unsigned sp - 32); (e + 4, e + 16); (0x340f8, 0x34100)]) in *.
  assert (HW3 : forall a, 0 <= a < 2 ^ 64 -> ~ outside W3 a -> bv_unsigned sp - 8288 <= a < bv_unsigned sp \/ rec_area a).
  { intros a Ra Hm. unfold W3 in Hm. cbn [outside] in Hm. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE. lia. }
  pose proof (rjr_win B API SEGS GOWN AX 8288 (bv_unsigned sp) O L A mem md L2 A2 m2 md2 m3 W3 RJ2 MU3 WM3 HW3) as RJ3.
  assert (RP3 : regs_preserved regs R3).
  { apply (kept_ex_pres [2; 8; 9; 18]).
    - apply (kept_ex_trans _ regs regs_c R3 KE).
      apply (kept_ex_trans _ regs_c R2 R3 (kept_ex_of_pres _ _ _ PR)).
      kept_ex_tac X3.
    - intros r Hr. cbn [In] in Hr. destruct Hr as [<-|Hr].
      + match goal with |- getr _ ?kk = _ => rewrite (getr_of_eqv _ _ kk X3 eq_refl) end. simp_regs.
        rewrite SP1v. replace (bv_unsigned sp - 32 + 32) with (bv_unsigned sp) by ring. rewrite Z_to_bv_bv_unsigned.
        first [reflexivity | unfold getr; reflexivity].
      + destruct Hr as [<-|[<-|[<-|[]]]];
          match goal with |- getr _ ?kk = _ => rewrite (getr_of_eqv _ _ kk X3 eq_refl) end;
          simp_regs; first [reflexivity | unfold getr; reflexivity]. }
  assert (INB : forall pn, In pn (blocks Lc Ac) -> In pn (blocks L2 A2)).
  { intros pn Hb. rewrite BL2. rewrite BL1 in Hb.
    apply in_app_or in Hb as [H|H]; apply in_or_app; [left; exact H | right; right; exact H]. }
  assert (DJ' : forall a n, In (a, n) (blocks Lc Ac) -> 0 < n -> a <> p).
  { intros a n Hin Hn Ea. subst a.
    pose proof (mr_blocks_disjoint B _ LAWS L2 A2 m2 md2 PM) as PD. rewrite BL2 in PD. rewrite BL1 in Hin.
    destruct (YI04.pairwise_app_mid _ _ _ _ _ PD Hin) as [D|D]; unfold ranges_disjoint in D; cbn [fst snd] in D;
      unfold k in D; lia. }
  pose proof (cells_bytes_at _ _ _ _ NA3) as NB. cbn [cells_bytes cbytes] in NB. rewrite app_nil_r in NB.
  pose proof (cells_bytes_at _ _ _ _ AR3) as AB. cbn [cells_bytes cbytes] in AB. rewrite app_nil_r in AB.
  pose proof (cells_bytes_at _ _ _ _ ES3) as SB3. cbn [cells_bytes cbytes] in SB3. rewrite app_nil_r in SB3.
  exists L2, A2, R3, m3, md2, (Oc ++ [(p, k)]).
  split; [rewrite (ret_pc_of_ok _ HRA); reflexivity|].
  split.
  { apply (rjr_final B (aa_MR API) CTX 8288 rec_area (fun pn => In pn O) (fun a => In a (map fst O)) L A regs mem md
             L2 A2 R3 m3 md2 PRE RJ3 RP3).
    intros a0 k0 G. exact (in_map fst O (a0, k0) G). }
  split.
  { unfold g_rec_rep, descriptors_add_m. fold x.
    apply (da_rec Lc Ac mc L2 A2 m3 R Oc x p k GR Y9 NB AB SB3).
    - intros a Ha N1 N2. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in Ha.
      rewrite (munch_mbyte rsegs W3 m2 m3 a MU3 ltac:(lia)); [apply KG; lia|].
      unfold W3. cbn [outside]. repeat split; lia.
    - intros [a n] Hpn. pose proof (INB _ (rec_rep_O_in _ _ _ _ _ _ _ _ (a, n) GR Hpn)) as Hb2.
      split; [exact Hb2|]. intros i Hi. cbn [fst snd] in *.
      destruct (rjr_blk_out B API SEGS AX 8288 (bv_unsigned sp) O L A mem md L2 A2 m2 md2 W3 RJ2 HW3 a n i Hb2 Hi)
        as [Ra Oa].
      rewrite (munch_mbyte rsegs W3 m2 m3 _ MU3 Ra Oa).
      exact (BKP a n i (rec_rep_O_in _ _ _ _ _ _ _ _ (a, n) GR Hpn) (fun f => f) Hi).
    - intros [a n] i Hpn Hi. cbn [fst snd] in *. pose proof (INB _ (rec_rep_O_in _ _ _ _ _ _ _ _ (a, n) GR Hpn)) as Hb2.
      destruct (rjr_blk_out B API SEGS AX 8288 (bv_unsigned sp) O L A mem md L2 A2 m2 md2 W3 RJ2 HW3 a n i Hb2 Hi)
        as [Ra Oa].
      split; [exact Ra|]. unfold W3 in Oa. cbn [outside] in Oa. exact (proj1 (proj2 (proj2 Oa))).
    - intros Hin. apply in_map_iff in Hin as ([a n] & Ea & Hin). cbn [fst] in Ea.
      exact (DJ' a n (rec_rep_O_in _ _ _ _ _ _ _ _ (a, n) GR Hin) (RecTail.rec_rep_pos _ _ _ _ _ _ _ _ (a, n) GR Hin) Ea).
    - exact PNZ.
    - exact PIN.
    - exact N0.
    - exact LX.
    - reflexivity.
    - lia.
    - eapply bytes_at_transport; [exact BYP | exact MU3 |]. rewrite length_app. cbn [length].
      unfold W3. cbn [disjoint_from]. unfold k in PG. destruct PG as [PG|PG]; repeat split; lia.
    - unfold iv_apart, G_REC, REC_SIZE. unfold k in PG. lia.
    - unfold iv_apart, REC_SC, SC_SIZE. unfold k in PG. lia. }
  split.
  { intros pn Hpn. apply in_app_or in Hpn as [H|[H|[]]]; [exact (ON pn H)|]. subst pn.
    destruct (in_dec RecTail.pair_dec (p, k) O) as [H|H]; [left; exact H|].
    right. intros Hb.
    destruct (in_dec RecTail.pair_dec (p, k) (blocks Lc Ac)) as [H2|H2].
    - exact (DJ' _ _ H2 ltac:(unfold k; lia) eq_refl).
    - exact (H (B2 _ Hb H2)). }
  split.
  { intros pn Hpn. rewrite BL2 in Hpn. apply in_app_or in Hpn as [H|[H|H]].
    - destruct (B1 pn ltac:(rewrite BL1; apply in_or_app; left; exact H)) as [X|X];
        [left; exact X | right; apply in_or_app; left; exact X].
    - right. apply in_or_app. right. left. exact H.
    - destruct (B1 pn ltac:(rewrite BL1; apply in_or_app; right; exact H)) as [X|X];
        [left; exact X | right; apply in_or_app; left; exact X]. }
  split.
  { pose proof (rjr_others_kept B (aa_MR API) 8288 (bv_unsigned sp) rec_area (fun pn => In pn O) L A mem md L2 A2 m3 md2 O
                  RJ3 (fun pn H => H)) as OK.
    rewrite SEGS in OK. exact OK. }
  split; [exact RA3|].
  split.
  { assert (F182 : f18_words rsegs m2).
    { destruct (ax_statics AX L2 A2 m2 md2 PM) as (_ & (g & Hg & HGW) & _).
      apply (RecAnsB.f18_words_after mc m2 g F18); [| exact Hg | rewrite SEGS, GRD in HGW; exact HGW].
      intros i Hi. unfold snprintf_c.GOT_GUARD. pose proof (GK i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
    apply (f18_out W3 m2 m3 F182 MU3). intros i Hi. unfold W3, snprintf_c.GOT_GUARD, snprintf_c.GUARD.
    cbn [outside]. split; repeat split; lia. }
  split; [exact INIT|].
  split; [pose proof RJ3 as (_ & _ & _ & _ & _ & HLen3 & _); exact HLen3|].
  assert (EQB : sb_shift b A A2 = sb_malloc (sb_shift b A Ac) k).
  { unfold k. rewrite (sb_shift_add (sb_shift b A Ac) Lc Ac L2 A2 l1 l2 p _ BL2 BL1). symmetry. apply sb_shift_trans. }
  split.
  - rewrite EQB. unfold sb_mallocs, descriptors_add_sizes. cbn [fold_left]. fold x k. exact (sb_malloc_mono _ _ _ BLE).
  - rewrite EQB. exact RES2.
Qed.

Lemma da_lt : forall L A regs mem md pu uri R O b,
  call_pre_k B (aa_MR API) DESCRIPTORS_ADD_K L A regs mem md ->
  getr regs 10 = Z_to_bv 64 pu ->
  str_arg B L A O (spZ regs) DESCRIPTORS_ADD_K mem pu uri ->
  g_rec_rep rsegs L A mem R O -> ro_agree rsegs mem -> f18_words rsegs mem -> res_ok_slots A b ->
  room_slots (sb_mallocs b (descriptors_add_sizes uri)) (LMAX + 1) ->
  (length (r_calls R) < 16)%nat ->
  SR rsegs (mkCfg (mkst regs (Z_to_bv 64 DESCRIPTORS_ADD) mem (seg_rom rsegs)) md) (da_ret L A regs mem md uri R O b).
Proof using SEGS ERRNO_LOW GOTG GRD GOWN GERR AX CTX SLACK XSD MIX.
  intros L A regs mem md pu uri R O b PRE A0 SA GR RA F18 RES ROOM Hn.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold DESCRIPTORS_ADD_K in HCEIL, HWS, SA.
  rewrite SEGS in HWS.
  pose proof (sinv_init B API 8288 L A regs mem md R O b PRE ltac:(lia) GR RA F18 RES) as SI0.
  destruct (sarg_src B SEGS L A O (spZ regs) 8288 mem pu uri RA ltac:(lia) ltac:(unfold NULL_LIT; lia) SA)
    as (s & slack & PU & SEL & S0 & BS & N0 & LX & AL & DJ & HOME & NRA).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (ST : stk rsegs mem (bv_unsigned sp - 8288) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  pose proof GR as (Q & HRep & HO).
  pose proof HRep as (HS & (G1 & G2 & G3 & G4 & G5 & G6) & _ & _ & HX & _).
  set (n := length (r_calls R)) in *.
  assert (NC : rw_cells rsegs mem 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))])
    by (apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia | exact G3]).
  assert (EE : rec_entry G_REC REC_SC R = 0x33d58 + 56 * Z.of_nat n)
    by (rewrite (rec_entry_lt G_REC REC_SC R Hn); fold n; unfold G_REC, OFF_CALLS, CALL_SIZE; lia).
  assert (SELW : sel_null (Z_to_bv 64 pu) = Z_to_bv 64 s)
    by (unfold sel_null; rewrite unsigned_lit by lia; rewrite <- SEL; destruct (pu =? 0); reflexivity).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    eapply da_pre_lt; [exact ST | lia | lia | exact NC | exact Hn]. }
  intros ms1 (can1 & (b1 & b2 & m1 & -> & MU1 & WM1 & ST1 & FR1 & NC1 & EF1) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & XR1).
  pose proof (sinv_record_lt B API SEGS GOWN AX 8288 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _
                22 SI0 Hn ltac:(unfold REC_FN_COUNT; lia) MU1 WM1 ltac:(intros a Ra Hm; cbn in Hm; lia) NC1 EF1) as SI1.
  pose proof (bytes_at_bound _ _ _ _ BS) as SB.
  assert (LP : 0 < Z.of_nat (length (sarg uri ++ Z_to_bv 8 0 :: slack)))
    by (rewrite length_app; cbn [length]; lia).
  assert (BS1 : bytes_at rsegs m1 s (sarg uri ++ Z_to_bv 8 0 :: slack)).
  { eapply bytes_at_transport; [exact BS | exact MU1 |]. cbn [disjoint_from].
    split; [lia|]. split; [apply da_nra_apart; [exact NRA | unfold REC_SC; lia | unfold G_REC, REC_SIZE; lia | lia | exact LP]|].
    split; [apply da_nra_apart; [exact NRA | unfold REC_SC; lia | unfold G_REC, REC_SIZE; lia | lia | exact LP] | exact I]. }
  apply (da_arg L A regs mem md uri R O b L A m1 md O R1 s slack PRE SI1
           ltac:(rewrite sb_shift_refl; apply sb_le_refl) ROOM).
  - exact FR1.
  - rewrite EE. exact EF1.
  - exact BS1.
  - exact N0.
  - exact LX.
  - exact AL.
  - exact DJ.
  - exact HOME.
  - rewrite (getr_of_eqv _ _ 1 XR1 eq_refl); simp_regs; reflexivity.
  - rewrite (getr_of_eqv _ _ 2 XR1 eq_refl); simp_regs; reflexivity.
  - rewrite (getr_of_eqv _ _ 8 XR1 eq_refl); simp_regs; reflexivity.
  - rewrite EE, (getr_of_eqv _ _ 9 XR1 eq_refl); simp_regs; reflexivity.
  - rewrite (getr_of_eqv _ _ 10 XR1 eq_refl); simp_regs.
    assert (R10 : reg_get regs 10 = Z_to_bv 64 pu) by exact A0. rewrite R10. exact SELW.
  - kept_ex_tac XR1.
Qed.


Lemma da_eq : forall L A regs mem md pu uri R O b,
  call_pre_k B (aa_MR API) DESCRIPTORS_ADD_K L A regs mem md ->
  getr regs 10 = Z_to_bv 64 pu ->
  str_arg B L A O (spZ regs) DESCRIPTORS_ADD_K mem pu uri ->
  g_rec_rep rsegs L A mem R O -> ro_agree rsegs mem -> f18_words rsegs mem -> res_ok_slots A b ->
  room_slots (sb_mallocs b (descriptors_add_sizes uri)) (LMAX + 1) ->
  (16 <= length (r_calls R))%nat ->
  SR rsegs (mkCfg (mkst regs (Z_to_bv 64 DESCRIPTORS_ADD) mem (seg_rom rsegs)) md) (da_ret L A regs mem md uri R O b).
Proof using SEGS ERRNO_LOW GOTG GRD GOWN GERR AX CTX SLACK RCF XSD MIX.
  intros L A regs mem md pu uri R O b PRE A0 SA GR RA F18 RES ROOM Hn.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold DESCRIPTORS_ADD_K in HCEIL, HWS, SA.
  rewrite SEGS in HWS.
  pose proof (sinv_init B API 8288 L A regs mem md R O b PRE ltac:(lia) GR RA F18 RES) as SI0.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (ST : stk rsegs mem (bv_unsigned sp - 8288) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  pose proof GR as (Q & HRep & HO).
  pose proof HRep as (HS & (G1 & G2 & G3 & G4 & G5 & G6) & _ & _ & HX & _).
  set (n := length (r_calls R)) in *.
  assert (NC : rw_cells rsegs mem 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))])
    by (apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia | exact G3]).
  assert (H16 : n = 16%nat) by lia.
  assert (NC16 : rw_cells rsegs mem 0x33d50 [C4 (Z_to_bv 64 16)]) by (rewrite H16 in NC; exact NC).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    eapply da_seg_eq; [exact ST | lia | lia | exact NC16]. }
  intros ms1 (can1 & (m1 & -> & MU1 & WM1 & ST1 & FR1) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x170f8) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 0x33d10) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_9 : getr R1 9 = getr regs 9) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 0x33d10)
    by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_11 : getr R1 11 = Z_to_bv 64 1) by (rewrite (getr_of_eqv _ _ 11 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_18 : getr R1 18 = getr regs 10) by (rewrite (getr_of_eqv _ _ 18 X1 eq_refl); simp_regs; reflexivity).
  assert (SP1 : spZ R1 = bv_unsigned sp - 32) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  pose proof (sinv_stack B API SEGS GOWN AX 8288 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI1.
  apply (sinv_rcf B API SEGS ERRNO_LOW GOTG GRD GOWN AX RCF 8288 (bv_unsigned sp) L A mem md O L A m1 md R O b R1 _
           SI1 H16 E1_10 E1_11).
  - rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
  - rewrite SP1. replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring.
    rewrite Z.mod_add by lia. exact HAL.
  - rewrite SP1. unfold RCF_K, ALLOC_STACK. lia.
  - rewrite SP1. lia.
  - rewrite E1_4. exact HTP.
  - intros L' A' regs' m' md' RP' POST FRK.
    rewrite E1_1.
    pose proof POST as (RJ' & _ & _ & _ & _ & RA' & _ & _ & BLE & _).
    destruct (mr_model B _ LAWS L' A' m' md' (proj1 RJ')) as (Hh' & Hl' & _).
    assert (R2' : getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32))
      by exact (eq_trans (RP' 2 ltac:(unfold callee_saved; lia)) E1_2).
    assert (R8' : getr regs' 8 = Z_to_bv 64 0x33d10) by exact (eq_trans (RP' 8 ltac:(unfold callee_saved; lia)) E1_8).
    assert (R18' : getr regs' 18 = getr regs 10) by exact (eq_trans (RP' 18 ltac:(unfold callee_saved; lia)) E1_18).
    assert (FR' : rw_cells rsegs m' (bv_unsigned sp - 32)
                    [C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
    { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
      apply FRK. rewrite SP1. lia. }
    destruct (glob_rw_cells m' 0x33d10 8 ltac:(unfold GLOB_LO; lia) ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk EW].
    eapply evt_SR_canon; [ | exact Hh' | exact Hl' | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of.
      assert (Q8 : reg_get regs' 8 = Z_to_bv 64 0x33d10) by exact R8'.
      rewrite Q8. eapply da_seg_rcf. eapply da_seg_tail. exact EW. }
    intros ms2 (can2 & (m2 & -> & MU2 & WM2 & EN2) & EQ2).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
    destruct (sinv_record_full B API SEGS GOWN AX 8288 (bv_unsigned sp) L A mem md O L A m1 R O b L' A' m' md' m2
                _ 22 POST ltac:(unfold REC_FN_COUNT; lia) MU2 WM2
                ltac:(intros a Ra Hm; cbn in Hm; unfold REC_SC; lia) EN2) as (Oc' & SI2).
    destruct (sinv_str B API SEGS ERRNO_LOW SLACK 8288 (bv_unsigned sp) L A mem md O L' A' m2 md' (rec_record R 22 []) Oc' b
                pu uri SI2 RA ltac:(unfold NULL_LIT; lia) SA)
      as (s & slack & PU & SEL & S0 & BS & N0 & LX & AL & DJ & HOME & NRA).
    assert (SELW : sel_null (Z_to_bv 64 pu) = Z_to_bv 64 s)
      by (unfold sel_null; rewrite unsigned_lit by lia; rewrite <- SEL; destruct (pu =? 0); reflexivity).
    apply (da_arg L A regs mem md uri R O b L' A' m2 md' Oc' R2 s slack PRE SI2
             ltac:(rewrite sb_shift_refl in BLE; exact BLE) ROOM).
    + apply (rw_cells_transport rsegs [(0x33d10, 0x33d10 + 8)] m' m2 _ _ FR' MU2 WM2).
      cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia.
    + rewrite (rec_entry_full G_REC REC_SC R H16). exact EN2.
    + exact BS.
    + exact N0.
    + exact LX.
    + exact AL.
    + exact DJ.
    + exact HOME.
    + rewrite (getr_of_eqv _ _ 1 X2 eq_refl); simp_regs; reflexivity.
    + rewrite (getr_of_eqv _ _ 2 X2 eq_refl); simp_regs. exact R2'.
    + rewrite (getr_of_eqv _ _ 8 X2 eq_refl); simp_regs; reflexivity.
    + rewrite (rec_entry_full G_REC REC_SC R H16), (getr_of_eqv _ _ 9 X2 eq_refl); simp_regs; reflexivity.
    + rewrite (getr_of_eqv _ _ 10 X2 eq_refl); simp_regs.
      assert (Q18 : reg_get regs' 18 = Z_to_bv 64 pu) by exact (eq_trans R18' A0). rewrite Q18. exact SELW.
    + apply (kept_ex_trans _ regs R1 R2); [kept_ex_tac X1|].
      apply (kept_ex_trans _ R1 regs' R2 (kept_ex_of_pres _ _ _ RP')). kept_ex_tac X2.
Qed.

Theorem descriptors_add_holds : descriptors_add_contract B API.
Proof using SEGS ERRNO_LOW GOTG GRD GOWN GERR AX CTX SLACK RCF XSD MIX.
  unfold descriptors_add_contract, descriptors_add_ret.
  intros L A regs mem md pu uri R O b PRE A0 SA GR RA F18 RES ROOM.
  rewrite SEGS in GR, RA, F18 |- *.
  destruct (Nat.lt_ge_cases (length (r_calls R)) 16) as [Hn|Hn].
  - exact (da_lt L A regs mem md pu uri R O b PRE A0 SA GR RA F18 RES ROOM Hn).
  - exact (da_eq L A regs mem md pu uri R O b PRE A0 SA GR RA F18 RES ROOM Hn).
Qed.

End P.