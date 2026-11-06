(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpRepA AWKit HttpAllocA AWRng.
Import ListNotations.
Open Scope Z_scope.

Section W.
Context {HC : HasCeiling}.

Definition seg1_post (lo : Z) (ra : word) (q : Z) (gp tp s0 s1 s2 s3 : word) (SRC n : Z)
    (t0 t1 t2 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists m' (pad : list byte),
    ms' = MS (mkR (wz 0x8bebc) (wz (q + -48)) gp tp t0 t1 t2 (wz n) (wz SRC) (wz (n + 1)) (wz n) a2 a3 a4 a5 a6 a7
                  s2 (wz 0x7fff8000) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz A0_malloc) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (q + -48)
    /\ rw_cells asegs m' (q + -48) [CB 8 pad; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

#[using="Type"] Lemma seg1 : forall (lo SRC n : Z) ra (q : Z) gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 48 -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  0 <= SRC < 2^64 -> 0 <= n /\ n + 1 < 2^32 ->
  evt asegs (seg1_post lo ra q gp tp s0 s1 s2 s3 SRC n t0 t1 t2 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz SRC) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz str_alloc_entryA) fc None m (seg_rom asegs)).
Proof.
  intros lo SRC n ra q gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI AE0 HS HN. unfold str_alloc_entryA.
  a0_prologue AE0 [(lo, q)]%Z m.
  carve_frame 48%nat ST.
  step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
  zstep. zstep. step. step. step. zstep. zstep.
  apply evt_done. unfold seg1_post, A0_malloc. do 2 eexists. split; [reflexivity|].
  repeat (split; [assumption|]). exact FR.
Qed.
Hypothesis IC : icpt_contracts.

Definition seg2_post (lo U n : Z) (src : list byte) (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz U) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(U, U + (n + 1)); (lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ rw_cells asegs m' U [CB (Z.to_nat (n + 1)) (src ++ [Z_to_bv 8 0])].

#[using="IC"] Lemma seg2 : forall (lo SRC n U : Z) (src junk pad : list byte) ra (q : Z) gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk asegs m lo (q + -48) -> alloc_ceiling <= lo -> lo <= q - 48 - A0_RT_STACK -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m (q + -48) [CB 8 pad; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  bytes_at asegs m SRC src -> Z.of_nat (length src) = n -> n + 1 < 2^32 ->
  rw_cells asegs m U [CB (Z.to_nat (n + 1)) junk] ->
  shw m U (n + 1) -> shw m SRC n ->
  0x609000 <= U -> U + (n + 1) <= alloc_ceiling -> U mod 8 = 0 -> SRC + n <= alloc_ceiling ->
  (SRC + n <= U \/ U + (n + 1) <= SRC) ->
  evt asegs (seg2_post lo U n src ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR (wz 0x8bebc) (wz (q + -48)) gp tp t0 t1 t2 (wz n) (wz SRC) (wz U) a1 a2 a3 a4 a5 a6 a7 s2 (wz 0x7fff8000) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x8bebc) fc None m (seg_rom asegs)).
Proof.
  intros lo SRC n U src junk pad ra q gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI AE0 FR SRCB LEN HN BLK SHWU SHWS UHI UCE UAL SCE DJ.
  unfold A0_RT_STACK in LO.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (munch_refl [(U, U + (n + 1)); (lo, q)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ SRCB) as BB.
  assert (N0 : 0 <= n) by lia.
  zstep. if_cases K; zify_cond K.
  { exfalso. lia. }
  zstep. zstep. zstep. step.

  apply (rw_cells_split_CB asegs m U [] (Z.to_nat (n + 1)) junk [] [Z.to_nat n; 1%nat]) in BLK; [| cbn; lia].
  cbn [app mk_CB_cells] in BLK.
  lazymatch type of BLK with rw_cells _ _ _ [?c1; ?c2] =>
    destruct (proj1 (rw_cells_app asegs m U [c1] [c2]) BLK) as [BLK1 BLK2] end. clear BLK.
  cbn [cells_size csize] in BLK2. rewrite Nat.add_0_r, Z2Nat.id in BLK2 by lia.
  pose proof SHWU as SHWU1. pose proof SHWS as SHWS1. shw_now SHWU1 MU. shw_now SHWS1 MU. env_now AE0 MU WM.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (ic_memcpy IC) with (D := U) (S := SRC) (n := n) (lo := lo) (src := src);
      first [ rng_tac | exact BLK1 | exact SRCB | exact LEN | exact DJ | exact MI | exact AE | exact ST | reflexivity
            | (eapply accessible_sub; [exact (proj1 SHWU1) | lia | lia])
            | (eapply sh_readable_sub; [exact (proj1 (proj2 SHWU1)) | lia | lia | lia])
            | exact (proj1 SHWS1) | exact (proj1 (proj2 SHWS1))
            | lia | (unfold A0_RT_STACK; lia)
            | (unfold env_safe; apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]) ]
    | post_call asegs mm ] end.
  clear SHWU1 SHWS1.
  zstep. zstep. zstep. zstep.
  pose proof SHWU as SHWU1. shw_now SHWU1 MU.
  pose proof (proj1 SHWU1 (U + n) ltac:(lia)) as HACC. clear SHWU1.
  acc_chk 11 (U + n) HACC k SHR Hk. clear HACC.
  destruct Hk as [-> | [K1 K2]].
  - step. step. lit_branch.
    remember (U + n)%Z as V eqn:EV.
    step. fix_lit_store. subst V.
    assert (BLK : rw_cells asegs m0 U [CB (Z.to_nat (n + 1)) (src ++ [Z_to_bv 8 0])]).
    { pose proof (proj2 (rw_cells_app asegs m0 U [CB (Z.to_nat n) src] [C1 (Z_to_bv 8 0)])) as J.
      cbn [cells_size csize Nat.add] in J. rewrite Nat.add_0_r, Z2Nat.id in J by lia.
      specialize (J (conj PC1 BLK2)).
      pose proof (rw_cells_merge asegs m0 U [] ([CB (Z.to_nat n) src] ++ [C1 (Z_to_bv 8 0)]) []) as M.
      rewrite !app_nil_r in M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
      replace (Z.to_nat n + 1)%nat with (Z.to_nat (n + 1)) in M by lia.
      apply M. cbn [app] in J. exact J. }
    clear PC1 BLK2.
    step. step. step. step. step. step. env_now AE0 MU WM. release_to q. step.
    apply evt_done. unfold seg2_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. repeat (split; [assumption|]). exact BLK.
  - step. step. rewrite (sxb_small k) by lia. if_cases K3; zify_cond K3.
    + zstep. zstep. if_cases K4; zify_cond K4; zify_granule K4; [| exfalso; lia].
      remember (U + n)%Z as V eqn:EV.
      step. fix_lit_store. subst V.
      assert (BLK : rw_cells asegs m0 U [CB (Z.to_nat (n + 1)) (src ++ [Z_to_bv 8 0])]).
      { pose proof (proj2 (rw_cells_app asegs m0 U [CB (Z.to_nat n) src] [C1 (Z_to_bv 8 0)])) as J.
        cbn [cells_size csize Nat.add] in J. rewrite Nat.add_0_r, Z2Nat.id in J by lia.
        specialize (J (conj PC1 BLK2)).
        pose proof (rw_cells_merge asegs m0 U [] ([CB (Z.to_nat n) src] ++ [C1 (Z_to_bv 8 0)]) []) as M.
        rewrite !app_nil_r in M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
        replace (Z.to_nat n + 1)%nat with (Z.to_nat (n + 1)) in M by lia.
        apply M. cbn [app] in J. exact J. }
      clear PC1 BLK2.
      step. step. step. step. step. step. env_now AE0 MU WM. release_to q. step.
      apply evt_done. unfold seg2_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. repeat (split; [assumption|]). exact BLK.
    + exfalso. lia.
Qed.

Variable FI : fs_if.
Variable AI : am_if FI.
Variable J : a0_judg FI AI.
Variable AC : am_contracts FI AI J.
Hypothesis ASL : forall lo hi, am_static FI AI lo hi -> a0_static lo hi.
Local Notation K := (am_K FI AI).

#[using="IC AC ASL"] Theorem str_alloc_spec_A : str_alloc_stmt_A FI AI J.
Proof.
  intros ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB st SRC n lo src bsrc.
  intros HR RF AE ST CLO LO QAL QTOP MI SRCB LEN HN BUD HIN B1 B2 -> ->.
  pose proof (bytes_at_bound _ _ _ _ SRCB) as BB.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
  destruct (am_block_range FI AI s LB m bsrc HR HIN) as (R1 & R2 & R3 & R4 & R5 & R5d & R6).
  assert (N0 : 0 <= n) by lia.
  unfold A0_RT_STACK in LO.

  eapply (aj_evt FI AI J). { eapply (seg1 lo SRC n); try eassumption; lia. }
  intros ms' (m1 & pad & -> & MU1 & WM1 & MI1 & ST1 & FR1).
  assert (SEG1 : seg_okA FI AI LB q [(lo, q)]) by (constructor; [left; cbn; lia| constructor]).
  assert (BIV1 : Forall (blk_iv FI AI LB) [(lo, q)]) by (constructor; [left; cbn; lia| constructor]).
  pose proof (rheap_blk_write FI AI s LB m m1 _ HR MU1 WM1 BIV1) as HR1.
  pose proof (rfake_blk_write FI AI s LB st m m1 _ HR RF MU1 WM1 ltac:(constructor; [split; [left; cbn; lia| cbn; lia]| constructor])) as RF1.
  pose proof (asan_env_frame asegs m m1 _ AE MU1 WM1 (env_safe_blk FI AI s LB m _ HR BIV1)) as AE1.
  pose proof (bytes_at_transport asegs _ m m1 _ _ SRCB MU1 ltac:(cbn; lia)) as SRCB1.
  pose proof (apres_seg FI AI ASL s LB LB q _ m m m1 HR ltac:(auto) MU1 WM1 SEG1) as AP1.

  eapply (aj_bind FI AI J).
  { eapply (ac_malloc FI AI J AC) with (lo := lo) (n := n + 1) (ras := []) (st := st);
      first [ exact HR1 | exact AE1 | exact RF1 | exact ST1 | exact MI1 | exact CLO | exact BUD | reflexivity
            | (unfold A0_RT_STACK; lia) | (unfold A0_MAXREQ; lia) | lia
            | (clear - QAL; Z.div_mod_to_equations; lia)
            | (cbn [fpchain]; unfold valid_frame; rewrite unsigned_lit by lia; lia)
            | (rewrite unsigned_lit by lia; cbn; tauto) ]. }
  intros s' LB' ms'' POST. unfold malloc_post_A in POST.
  destruct POST as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & k & U & junk & -> & AFR & -> & HR2 & BLK & NBSH & WM2 & NS2).
  destruct AFR as (MI2 & ST2 & AE2 & RF2 & AP2).
  replace (ret_pc (Z_to_bv 64 573116)) with (Z_to_bv 64 573116) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (NEW : In (k, U, n + 1) ((k, U, n + 1) :: LB)) by (left; reflexivity).
  destruct (am_block_range FI AI s' _ m2 _ HR2 NEW) as (U1 & U2 & U3 & U4 & U5 & U5d & U6). cbn [blk_addr blk_size fst snd] in U1, U2, U3, U4, U5, U5d, U6.

  pose proof (apres_rw_cells FI AI _ _ _ _ _ _ AP2 FR1 ltac:(apply aclient_range_above; cbn; lia)) as FR2.
  pose proof (apres_bytes_at FI AI _ _ _ _ _ _ AP2 SRCB1 ltac:(eapply aclient_range_block; [exact HIN| lia| lia])) as SRCB2.
  pose proof (fresh_block_apart FI AI s' LB (k, U, n + 1) bsrc m2 SRC n HR2 HIN B1 B2) as DJ. cbn [blk_addr blk_size fst snd] in DJ.
  pose proof (block_shw FI AI s' _ m2 (k, U, n + 1) U (n + 1) HR2 NEW ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)) as SHWU.
  pose proof (block_shw FI AI s' _ m2 bsrc SRC n HR2 (or_intror HIN) B1 B2 N0) as SHWS.
  eapply (aj_evt FI AI J).
  { eapply (seg2 lo SRC n U src junk pad); try eassumption; lia. }
  intros ms' P2. unfold seg2_post in P2.
  destruct P2 as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & AE3 & BLK3).
  assert (BIV3 : Forall (blk_iv FI AI ((k, U, n + 1) :: LB)) [(U, U + (n + 1)); (lo, q)]).
  { constructor; [right; exists (k, U, n + 1); split; [exact NEW| cbn; lia]| constructor; [left; cbn; lia| constructor]]. }
  apply (aj_ret FI AI J). unfold str_alloc_post_A.
  do 14 eexists. exists m3, k, U. split; [reflexivity|].
  split.
  { split; [exact MI3|]. split; [exact ST3|]. split; [exact AE3|].
    split. { eapply (rfake_blk_write FI AI s' _ st m2 m3 _ HR2 RF2 MU3 WM3). constructor; [split; [right; exists (k, U, n + 1); split; [exact NEW| cbn; lia]| cbn; lia]| constructor; [split; [left; cbn; lia| cbn; lia]| constructor]]. }
    eapply (apres_trans FI AI); [exact AP1|]. eapply (apres_trans FI AI).
    - eapply (apres_weaken FI AI); [exact AP2| lia| auto].
    - eapply (apres_seg FI AI ASL s' _ LB q _ m2 m2 m3 HR2 ltac:(intros b0 Hb0; right; exact Hb0) MU3 WM3).
      constructor; [| constructor; [left; cbn; lia| constructor]].
      right. cbn [fst snd]. intros a Ha.
      eapply (fresh_block_not_aclient FI AI ASL s' _ LB (k, U, n + 1) q m2 a HR2 NEW (cons_old FI AI s' LB _ m2 HR2)); [lia| cbn; lia]. }
  split; [reflexivity|]. split; [| split; [exact BLK3| exact NS2]].
  eapply (rheap_blk_write FI AI s' _ m2 m3 _ HR2 MU3 WM3 BIV3).
Qed.
End W.
