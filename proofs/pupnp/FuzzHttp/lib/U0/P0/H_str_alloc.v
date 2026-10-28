(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach AllocIF SReach AllocSpec.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac HttpAlloc.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_memcpy HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Definition str_alloc_entry := 0x16508%Z.
Ltac sstep := step; fix_lit_store.
Ltac lit_branch :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    first [ replace (if c then a else b) with a by (vm_compute; reflexivity)
          | replace (if c then a else b) with b by (vm_compute; reflexivity) ] end.

Definition memcpy_zpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D SX n : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(D, D + n)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' D [CB (Z.to_nat n) src]
    /\ bytes_at rsegs m' SX src.
Lemma memcpy_call : forall (D SX n : Z) (src junk : list byte)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
  bytes_at rsegs m SX src -> Z.of_nat (length src) = n ->
  rw_cells rsegs m D [CB (Z.to_nat n) junk] ->
  (SX + n <= D \/ D + n <= SX)%Z -> (0 <= D /\ D + n < 2^64)%Z -> (0 <= n)%Z -> (SX < 2^64)%Z ->
  mem_inv rsegs m -> a0 = wz D -> a1 = wz SX -> a2 = wz n ->
  evt rsegs (memcpy_zpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D SX n src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x240e0) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros B L BLK DJ HD HN HSX MI -> -> ->.
  pose proof (bytes_at_bound _ _ _ _ B) as BB.
  assert (E0 : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (E1 : bv_unsigned (Z_to_bv 64 SX) = SX) by (apply unsigned_lit; lia).
  pose proof (rw_cells_bound rsegs _ _ _ BLK) as DB. cbn [cells_size csize Nat.add] in DB.
  assert (E2 : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (memcpy_spec _ _ _ _ _ _ _ _ _ (Z_to_bv 64 D) (Z_to_bv 64 SX) (Z_to_bv 64 n)); rewrite ?E0, ?E1, ?E2; eauto; lia. }
  intros ms' P. unfold memcpy_post in P. rewrite !E0, !E1, !E2 in P. exact P.
Qed.

Definition seg1_post (lo : Z) (ra sp gp tp s0 s1 s2 : word) (SRC n : Z)
    (t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR (wz 0x1652c) (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz n) (wz SRC) (wz (n + 1)) (wz n) a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x180f0) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp + -32)
    /\ rw_cells rsegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra].

Lemma seg1 : forall (lo SRC n : Z) ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp) -> (lo + 32 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  (0 <= SRC < 2^64)%Z -> (0 <= n /\ n + 1 < 2^32)%Z ->
  evt rsegs (seg1_post lo ra sp gp tp s0 s1 s2 SRC n t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz SRC) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz str_alloc_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI HS HN. unfold str_alloc_entry.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (word_lt64 sp) as SPB.
  carve_frame 32%nat ST.
  do 5 sstep. zstep. zstep. zstep. zstep.
  apply evt_done. unfold seg1_post. eexists. split; [reflexivity|].
  repeat (split; [assumption|]). exact FR.
Qed.

Lemma seg2_null : forall (lo SRC n : Z) ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp + -32) -> (lo + 32 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom rsegs)
                       /\ stk rsegs m lo (bv_unsigned sp))
    (MS (mkR (wz 0x1652c) (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz n) (wz SRC) (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x1652c) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI FR. pose proof (word_lt64 sp) as SPB.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. lit_branch. do 5 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep. apply evt_done. split; [reflexivity| exact ST].
Qed.

Definition seg2_post (lo U n : Z) (src : list byte) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz U) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (U, U + (n + 1))]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' U [CB (Z.to_nat (n + 1)) (src ++ [Z_to_bv 8 0])].

Lemma seg2_ok : forall (lo SRC n U : Z) (src junk : list byte) ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp + -32) -> (lo + 32 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
  bytes_at rsegs m SRC src -> Z.of_nat (length src) = n -> (0 <= n /\ n + 1 < 2^32)%Z ->
  rw_cells rsegs m U [CB (Z.to_nat (n + 1)) junk] -> (0 < U)%Z -> (U + (n + 1) <= lo)%Z ->
  (SRC + n <= U \/ U + (n + 1) <= SRC)%Z -> (SRC + n <= bv_unsigned sp - 32)%Z ->
  evt rsegs (seg2_post lo U n src ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR (wz 0x1652c) (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz n) (wz SRC) (wz U) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x1652c) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI FR BSRC LEN HN BLK U0 UHI DJ DJ2. pose proof (word_lt64 sp) as SPB.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (U, U + (n + 1))]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ BSRC) as BB.

  apply (rw_cells_split_CB rsegs m U [] (Z.to_nat (n + 1)) junk [] [Z.to_nat n; 1%nat]) in BLK; [| cbn; lia].
  cbn [app mk_CB_cells] in BLK.
  lazymatch type of BLK with rw_cells _ _ _ [?c1; ?c2] =>
    destruct (proj1 (rw_cells_app rsegs m U [c1] [c2]) BLK) as [BLK1 BLK2] end. clear BLK.
  cbn [cells_size csize] in BLK2. rewrite Nat.add_0_r, Z2Nat.id in BLK2 by lia.
  zstep. if_cases K0; zify_cond K0. { exfalso; lia. }
  zstep. zstep. zstep. zstep.
  call (memcpy_call U SRC n src).
  all: side (first [exact BSRC | exact BLK1 | exact MI | reflexivity | lia]).
  zstep. step. ubr. zstep. zstep.
  remember (U + n)%Z as V eqn:EV.
  sstep. subst V.
  assert (BLK : rw_cells rsegs m0 U [CB (Z.to_nat (n + 1)) (src ++ [Z_to_bv 8 0])]).
  { pose proof (proj2 (rw_cells_app rsegs m0 U [CB (Z.to_nat n) src] [C1 (Z_to_bv 8 0)])) as J.
    cbn [cells_size csize Nat.add] in J. rewrite Nat.add_0_r, Z2Nat.id in J by lia.
    specialize (J (conj PC BLK2)).
    pose proof (rw_cells_merge rsegs m0 U [] ([CB (Z.to_nat n) src] ++ [C1 (Z_to_bv 8 0)]) []) as M.
    rewrite !app_nil_r in M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
    replace (Z.to_nat n + 1)%nat with (Z.to_nat (n + 1)) in M by lia.
    apply M. cbn [app] in J. exact J. }
  clear PC BLK2.
  do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. unfold seg2_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. repeat (split; [assumption|]). exact BLK.
Qed.

Section W.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Variable AC : alloc_contracts AI.
  Notation L := (ai_L rsegs AI).
  Notation K := (ai_K rsegs AI).
  Hypothesis LOK : layout_ok AI.
  Hypothesis MALPC : al_malloc_pc L = 0x180f0.

  Definition str_alloc_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list (block K)) (n lo B : Z) (src : list byte) (m : mem)
      : ai_PS rsegs AI -> list (block K) -> machine_state -> Prop :=
    fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z),
      ms' = MS (mkR ra sp gp (wz (al_tp L)) t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ alloc_frame AI sp lo B m m' LB
      /\ ( (r = 0 /\ LB' = LB /\ RHEAP rsegs AI s' LB m')
         \/ (exists k, LB' = (k, r, n + 1) :: LB /\ block_range AI r (n + 1) /\ RHEAP rsegs AI s' LB' m'
               /\ rw_cells rsegs m' r [CB (Z.to_nat (n + 1)) (src ++ [Z_to_bv 8 0])]) ).

  #[using="AC LOK MALPC"] Theorem str_alloc_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m s LB (SRC n lo B : Z) (src : list byte) (errv : word) (bsrc : block K),
    RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> (bv_unsigned sp <= B)%Z ->
    stk rsegs m lo (bv_unsigned sp) -> (alloc_ceiling <= lo)%Z -> (lo <= bv_unsigned sp - 32 - al_stack L)%Z -> (0 <= al_stack L)%Z ->
    rw_cells rsegs m (al_errno L) [C4 errv] -> mem_inv rsegs m ->
    bytes_at rsegs m SRC src -> Z.of_nat (length src) = n -> (n + 1 < 2^32)%Z ->
    In bsrc LB -> (blk_addr bsrc <= SRC)%Z -> (SRC + n <= blk_addr bsrc + blk_size bsrc)%Z ->
    a0 = wz SRC -> a1 = wz n ->
    SREACH AI (str_alloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB n lo B src m)
      (MS (mkR ra sp gp (wz (al_tp L)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz str_alloc_entry) fc None m (seg_rom rsegs)) s LB.
  Proof.
    intros until bsrc. intros HR HE SPB ST CEIL LO STK ERR MI BSRC LEN HN HIN B1 B2 -> ->.
    pose proof (word_lt64 sp) as SPR. pose proof (bytes_at_bound _ _ _ _ BSRC) as BB.
    destruct (ai_block_range rsegs AI s LB m bsrc HR HIN) as (R1 & R2 & R3 & R4 & R5).
    destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3.
    pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.

    eapply sreach_evt. { eapply (seg1 lo SRC n); try eassumption; lia. }
    intros ms' (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (HR1 : RHEAP rsegs AI s LB m1).
    { eapply (ai_heap_frame rsegs AI); [exact HR| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
    assert (HE1 : RENV rsegs AI m1 B).
    { eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
    pose proof (rw_cells_transport rsegs _ m m1 _ _ ERR MU1 WM1 ltac:(cbn; lia)) as ERR1.
    pose proof (bytes_at_transport rsegs _ m m1 _ _ BSRC MU1 ltac:(cbn; lia)) as BSRC1.

    eapply sreach_bind.
    { rewrite <- MALPC. eapply (ac_malloc rsegs AI AC) with (lo := lo) (B := B); try eassumption; try reflexivity;
        rewrite ?unsigned_lit by lia; try lia; try eassumption. }
    intros s' LB' ms'' POST. unfold malloc_post in POST. destruct_exs POST.
    destruct POST as (-> & AF & CASES).
    destruct AF as (MI2 & ST2 & HE2 & [errv2 ERR2] & HP2). rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HP2 by lia.
    lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
    replace (ret_pc (Z_to_bv 64 91436)) with (Z_to_bv 64 91436) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HP2 FR1 ltac:(apply client_range_above; cbn; lia)) as FR2.
    pose proof (heap_pres_bytes_at rsegs AI _ _ _ _ _ _ HP2 BSRC1 ltac:(eapply client_range_block; [exact HIN| lia| lia])) as BSRC2.

    assert (HP1 : heap_pres AI LB (bv_unsigned sp) m m1).
    { eapply (heap_pres_seg rsegs AI); [exact LOK| exact HR| auto| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
    assert (HP02 : heap_pres AI LB (bv_unsigned sp) m m2).
    { eapply (heap_pres_trans rsegs AI); [exact HP1|]. eapply (heap_pres_weaken rsegs AI); [exact HP2| lia| auto]. }
    destruct CASES as [(-> & -> & HR2)|(k & U & junk & -> & -> & BR & HR2 & BLK)].
    -
      eapply sreach_evt. { eapply (seg2_null lo SRC n); try eassumption; lia. }
      intros ms' [-> ST3]. apply sreach_ret. unfold str_alloc_post.
      repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
      split. { split; [exact MI2|]. split; [exact ST3|]. split; [exact HE2|]. split; [eexists; exact ERR2| exact HP02]. }
      left. auto.
    -
      destruct BR as (U1 & U2 & U3 & U4 & U5).
      assert (NEW : In (k, U, n + 1) ((k, U, n + 1) :: LB)) by (left; reflexivity).
      assert (OLD : forall b0, In b0 LB -> In b0 ((k, U, n + 1) :: LB) /\ b0 <> (k, U, n + 1)).
      { intros b0 Hb0. split; [right; exact Hb0|]. intros ->.
        pose proof (ai_blocks_nodup rsegs AI _ _ _ HR2) as ND. cbn in ND. inversion ND as [|xk xl NI ND']; subst.
        apply NI. apply base.list_elem_of_In. exact (in_map blk_id _ _ Hb0). }
      assert (DJ : SRC + n <= U \/ U + (n + 1) <= SRC).
      { destruct (OLD bsrc HIN) as [HIN' NE].
        pose proof (ai_blocks_disjoint rsegs AI _ _ _ _ _ HR2 HIN' NEW NE) as D. cbn in D. unfold blk_addr, blk_size in D, B1, B2. cbn in D, B1, B2. lia. }
      eapply sreach_evt. { eapply (seg2_ok lo SRC n U src junk); try eassumption; try LiaTuning.alia. }
      intros ms' P2. unfold seg2_post in P2. destruct_exs P2. destruct P2 as (-> & MU3 & WM3 & MI3 & ST3 & BLK3).
      lazymatch type of MI3 with mem_inv _ ?mm => rename mm into m3 end.
      pose proof (fresh_block_disjoint_errno rsegs AI _ _ _ _ LOK HR2 NEW) as DE. cbn in DE.
      pose proof (rw_cells_transport rsegs _ m2 m3 _ _ ERR2 MU3 WM3 ltac:(cbn; lia)) as ERR3.
      apply sreach_ret. unfold str_alloc_post.
      repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
      split.
      { split; [exact MI3|]. split; [exact ST3|]. split.
        { eapply (ai_env_frame rsegs AI); [exact HR2| exact HE2| exact MU3| exact WM3|].
          constructor. { left. cbn. lia. } constructor; [| constructor]. right; right; right. exists (k, U, n + 1). split; [exact NEW|]. cbn. lia. }
        split; [eexists; exact ERR3|].
        eapply (heap_pres_trans rsegs AI); [exact HP02|].
        eapply (heap_pres_seg rsegs AI); [exact LOK| exact HR| auto| exact MU3| exact WM3|].
        constructor. { left. cbn. lia. } constructor; [| constructor]. right. cbn. intros a Ha.
        eapply (fresh_block_not_client rsegs AI); [exact LOK| exact HR2| exact NEW| exact OLD| lia| cbn; lia]. }
      right. exists k. split; [reflexivity|]. split; [exact (conj U1 (conj U2 (conj U3 (conj U4 U5))))|]. split; [| exact BLK3].
      eapply (ai_heap_frame rsegs AI); [exact HR2| exact MU3| exact WM3|].
      constructor. { left. cbn. lia. } constructor; [| constructor]. right; right; right. exists (k, U, n + 1). split; [exact NEW|]. cbn. lia.
  Qed.
End W.
