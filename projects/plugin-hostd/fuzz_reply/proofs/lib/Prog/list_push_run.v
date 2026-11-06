From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import memcpy_c ListStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition lp_mid1 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 b1 b2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' j0,
    ms' = MS (mkR (Z_to_bv 64 0x142e4) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 a2 a0
                  (Z_to_bv 64 (bv_unsigned a2 + 1)) b1 b2 a3 a4 a5 a6 a7 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x157a4) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m'
    /\ rw_cells rsegs m' (bv_unsigned sp - 48)%Z [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma lp_run1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo V N CAP : Z),
  stk rsegs m lo (bv_unsigned sp) -> (lo + 48 <= bv_unsigned sp)%Z ->
  rw_cells rsegs m (bv_unsigned a0) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)] ->
  (bv_unsigned a0 + 16 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (0 <= N < CAP)%Z -> (CAP < 2 ^ 30)%Z -> (bv_unsigned a2 + 1 < 2 ^ 64)%Z ->
  evt rsegs (lp_mid1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14284) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo V N CAP ST LO LC DJ NC CB N1.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 a2) as RA2. unfold bv_modulus in RA2. cbn in RA2.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 48%nat junk [] [8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 11 step.
  rewrite ?ls_sx32 by lia.
  step. br true.
  do 2 step.
  apply evt_done. unfold lp_mid1.
  do 16 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. exact FR.
Qed.

Definition lp_mid1g (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (V G : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 b2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' j0,
    ms' = MS (mkR (Z_to_bv 64 0x142d0) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 a2 a0
                  (Z_to_bv 64 V) (Z_to_bv 64 (16 * G)) b2 a3 a4 a5 a6 a7 a1 (Z_to_bv 64 G)
                  s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x17010) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m'
    /\ rw_cells rsegs m' (bv_unsigned sp - 48)%Z [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma lp_run1g : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo V N G : Z),
  stk rsegs m lo (bv_unsigned sp) -> (lo + 48 <= bv_unsigned sp)%Z ->
  rw_cells rsegs m (bv_unsigned a0) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 N)] ->
  (bv_unsigned a0 + 16 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (0 <= N < 2 ^ 29)%Z -> G = (if (N =? 0)%Z then 8 else 2 * N)%Z ->
  evt rsegs (lp_mid1g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 V G m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14284) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo V N G ST LO LC DJ NC EG.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 48%nat junk [] [8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 11 step.
  rewrite ?ls_sx32 by lia.
  step. br false.
  step.
  destruct (Z.eq_dec N 0) as [N0|N0].
  - subst N. cbn in EG. subst G. br false.
    step. step.
    step. step. step.
    apply evt_done. unfold lp_mid1g.
    do 15 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. exact FR.
  - rewrite (proj2 (Z.eqb_neq N 0) N0) in EG. subst G. br true.
    step.
    rewrite (ls_slliw1 N) by lia.
    step. step.
    rewrite (ls_slli4 (2 * N)) by lia.
    step.
    apply evt_done. unfold lp_mid1g.
    do 15 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. exact FR.
Qed.

Definition lp_mid2 (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (sp1 : word) (LA V N G : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x142e4) sp1 gp tp t0 t1 t2 s0 s1
                  (Z_to_bv 64 (bv_unsigned s0 + 1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x157a4) fc None m' (seg_rom rsegs)
    /\ munch [(LA, LA + 16)]%Z m m' /\ wmono rsegs m m'
    /\ rw_cells rsegs m' LA [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 G)].

Lemma lp_run2 : forall ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s0 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp1 : word) (LA V0 V N CAP G : Z),
  rw_cells rsegs m LA [C8 (Z_to_bv 64 V0); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)] ->
  (0 < V < 2 ^ 64)%Z -> (0 <= LA)%Z -> (LA + 16 <= 2 ^ 64)%Z -> (0 <= G < 2 ^ 31)%Z ->
  (bv_unsigned s0 + 1 < 2 ^ 64)%Z ->
  evt rsegs (lp_mid2 gp tp s0 (Z_to_bv 64 LA) s2 (Z_to_bv 64 G) s4 s5 s6 s7 s8 s9 s10 s11 F fc sp1 LA V N G m)
    (MS (mkR ra sp1 gp tp t0 t1 t2 s0 (Z_to_bv 64 LA) (Z_to_bv 64 V) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 G)
             s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x142d0) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s0 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp1 LA V0 V N CAP G LC RV RL RL2 RG RS.
  pose proof (munch_refl [(LA, LA + 16)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. br false.
  step. step.
  step. step.
  apply evt_done. unfold lp_mid2.
  do 15 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Definition lp_end (ra0 sp0 gp tp s00 s01 s02 s03 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LA V N G d n : Z) (x : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s01 a0 a1 a2 a3 a4 a5 a6 a7
                  s02 s03 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra0) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp0 - 48, bv_unsigned sp0); (LA, LA + 16); (V + 16 * N, V + 16 * N + 16); (d, d + n + 1)]%Z m m'
    /\ wmono rsegs m m'
    /\ rw_cells rsegs m' LA [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 (N + 1)); C4 (Z_to_bv 64 G)]
    /\ rw_cells rsegs m' (V + 16 * N)%Z [C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 n)]
    /\ rw_cells rsegs m' d [CB (length x) x]
    /\ rw_cells rsegs m' (d + n)%Z [C1 (Z_to_bv 8 0)].

Lemma lp_run3 : memcpy_contract ->
  forall ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 s02 s03 : word)
    (LA SRC V N G d n : Z) (x junk1 junk2 j1 j0 : list byte),
  rw_cells rsegs m (bv_unsigned sp0 - 48) [CB 8 j0; C8 s03; C8 s02; C8 s01; C8 s00; C8 ra0] ->
  rw_cells rsegs m LA [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 G)] ->
  rw_cells rsegs m (V + 16 * N)%Z [CB 16 junk1] ->
  rw_cells rsegs m d [CB (length x) junk2] ->
  rw_cells rsegs m (d + n)%Z [CB 1 j1] ->
  bytes_at rsegs m SRC x -> Z.of_nat (length x) = n ->
  (0 <= N < 2 ^ 30)%Z -> (0 <= V)%Z -> (V + 16 * N + 16 <= 2 ^ 64)%Z -> (0 < d)%Z -> (d + n + 1 <= 2 ^ 64)%Z ->
  (0 <= LA)%Z -> (LA + 16 <= 2 ^ 64)%Z -> (0 <= SRC < 2 ^ 64)%Z -> (48 <= bv_unsigned sp0)%Z ->
  (LA + 16 <= V + 16 * N \/ V + 16 * N + 16 <= LA)%Z ->
  (LA + 16 <= d \/ d + n + 1 <= LA)%Z ->
  (V + 16 * N + 16 <= d \/ d + n + 1 <= V + 16 * N)%Z ->
  (SRC + n <= d \/ d + n <= SRC)%Z ->
  (SRC + n <= LA \/ LA + 16 <= SRC)%Z ->
  (SRC + n <= V + 16 * N \/ V + 16 * N + 16 <= SRC)%Z ->
  (LA + 16 <= bv_unsigned sp0 - 48 \/ bv_unsigned sp0 <= LA)%Z ->
  (V + 16 * N + 16 <= bv_unsigned sp0 - 48 \/ bv_unsigned sp0 <= V + 16 * N)%Z ->
  (d + n + 1 <= bv_unsigned sp0 - 48 \/ bv_unsigned sp0 <= d)%Z ->
  mem_inv rsegs m ->
  evt rsegs (lp_end ra0 sp0 gp tp s00 s01 s02 s03 s4 s5 s6 s7 s8 s9 s10 s11 F fc LA V N G d n x m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 LA)
             (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 SRC) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x142e4) fc None m (seg_rom rsegs)).
Proof.
  intros MCPY ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 s02 s03 LA SRC V N G d n x junk1 junk2 j1 j0
    FR LC SL DST DZ SRCB LX RN RV RV2 RD RD2 RL RL2 RS RSP D1 D2 D3 D4 D5 D6 D7 D8 D9 MI.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP0. unfold bv_modulus in RSP0. cbn in RSP0.
  pose proof (munch_refl [(bv_unsigned sp0 - 48, bv_unsigned sp0); (LA, LA + 16); (V + 16 * N, V + 16 * N + 16); (d, d + n + 1)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (US : bv_unsigned (Z_to_bv 64 SRC) = SRC) by (apply unsigned_lit; lia).
  assert (UD : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (TN : Z.to_nat n = length x) by lia.
  step.
  rewrite ?ls_sx32 by lia.
  step. step. step.
  rewrite (ls_idx V N) by lia.
  remember (V + 16 * N)%Z as P eqn:HP.
  step.
  step. br false.
  step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (MCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x junk2);
      [ rewrite US; exact SRCB | rewrite UN, TN; reflexivity | rewrite UD, UN, TN; exact DST
      | rewrite US, UD, UN; lia | assumption ]
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold memcpy_post in PO; rewrite ?US, ?UD, ?UN, ?TN in PO; revert ms' PO;
      post_call rsegs mm ]
  end.
  cbv delta [mkR].
  step.
  rewrite ?ls_sx32 by lia.
  step. step. step.
  rewrite (ls_idx V N) by lia. rewrite <- HP.
  step. step.
  remember (d + n)%Z as Dn eqn:HDn.
  step.
  change (le1 (Z_to_bv 64 0)) with (le1 (zxb (Z_to_bv 8 0))). mem_after_store.
  step.
  rewrite ?ls_sx32 by lia.
  step. step. step. step.
  rewrite (ls_idx V N) by lia. rewrite <- HP.
  step.
  step.
  do 7 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 48 + 48)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. unfold lp_end. subst P Dn.
  do 16 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; eassumption.
Qed.
