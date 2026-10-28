(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach AllocIF SReach AllocSpec.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac HttpAlloc HttpAllocX.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Definition membuffer_destroy_entry := 0x166b8%Z.
Ltac sstep := step; fix_lit_store.

Definition dseg1_post (lo MB A len cap : Z) (ra sp gp tp s0 : word)
    (t0 t1 t2 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR (wz 0x166e0) (wz (bv_unsigned sp + -16)) gp tp t0 t1 t2 (wz MB) s1 (wz A) (wz A) a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x17fb0) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp + -16)
    /\ rw_cells rsegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ rw_cells rsegs m' MB (mbuf_cells A len cap).

Lemma dseg1 : forall (lo MB A len cap : Z) ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp) -> (lo + 16 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  rw_cells rsegs m MB (mbuf_cells A len cap) -> (MB + 32 <= lo \/ bv_unsigned sp <= MB)%Z -> (0 < MB /\ MB + 32 < 2^64)%Z -> (MB mod 8 = 0)%Z ->
  evt rsegs (dseg1_post lo MB A len cap ra sp gp tp s0 t0 t1 t2 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz MB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz membuffer_destroy_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI MBC MBHI MBR MBA. unfold membuffer_destroy_entry. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (word_lt64 sp) as SPB.
  zstep. if_cases K0; zify_cond K0. { exfalso; lia. }
  ub_align.
  carve_frame 16%nat ST.
  sstep. sstep. sstep. zstep. zstep. zstep. zstep.
  apply evt_done. unfold dseg1_post. eexists. split; [reflexivity|].
  repeat (split; [assumption|]). exact MBC.
Qed.

Lemma dseg2 : forall (lo MB A len cap : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp + -16) -> (lo + 16 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
  rw_cells rsegs m MB (mbuf_cells A len cap) -> (MB + 32 <= lo \/ bv_unsigned sp <= MB)%Z -> (0 < MB /\ MB + 32 < 2^64)%Z ->
  evt rsegs (fun ms' => exists a0' m',
               ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra) fc None m' (seg_rom rsegs)
               /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (MB, MB + 32)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
               /\ stk rsegs m' lo (bv_unsigned sp)
               /\ rw_cells rsegs m' MB (mbuf_cells 0 0 0))
    (MS (mkR (wz 0x166e0) (wz (bv_unsigned sp + -16)) gp tp t0 t1 t2 (wz MB) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x166e0) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI FR MBC MBHI MBR. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (MB, MB + 32)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (word_lt64 sp) as SPB.
  zstep. sstep. sstep. sstep. sstep. zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. eexists _, _. split; [reflexivity|]. repeat (split; [assumption|]). exact MBC.
Qed.

Section W.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Variable AC : alloc_contracts AI.
  Notation L := (ai_L rsegs AI).
  Notation K := (ai_K rsegs AI).
  Hypothesis LOK : layout_ok AI.
  Hypothesis FREEPC : al_free_pc L = 0x17fb0.

  Definition membuffer_destroy_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LBrest : list (block K)) (MB lo B : Z) (m : mem)
      : ai_PS rsegs AI -> list (block K) -> machine_state -> Prop :=
    fun s' LB' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp (wz (al_tp L)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ RENV rsegs AI m' B
      /\ (exists errv', rw_cells rsegs m' (al_errno L) [C4 errv'])
      /\ hpx AI [(MB, MB + 32)] LBrest (bv_unsigned sp) m m'
      /\ LB' = LBrest /\ RHEAP rsegs AI s' LBrest m'
      /\ rw_cells rsegs m' MB (mbuf_cells 0 0 0).

  #[using="AC LOK FREEPC"] Theorem membuffer_destroy_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m s LB (LBrest : list (block K)) (MB A len cap lo B : Z) (errv : word),
    RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> (bv_unsigned sp <= B)%Z ->
    stk rsegs m lo (bv_unsigned sp) -> (alloc_ceiling <= lo)%Z -> (lo <= bv_unsigned sp - 16 - al_stack L)%Z -> (0 <= al_stack L)%Z ->
    rw_cells rsegs m (al_errno L) [C4 errv] -> mem_inv rsegs m ->
    rw_cells rsegs m MB (mbuf_cells A len cap) -> mbloc AI LBrest (bv_unsigned sp) B MB 32 -> (B < 2^64)%Z -> (MB mod 8 = 0)%Z ->
    ((A = 0 /\ LBrest = LB) \/ (exists k, In (k, A, cap + 1) LB /\ LBrest = lb_remove (ai_K_eqb rsegs AI) k LB)) ->
    a0 = wz MB ->
    SREACH AI (membuffer_destroy_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBrest MB lo B m)
      (MS (mkR ra sp gp (wz (al_tp L)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz membuffer_destroy_entry) fc None m (seg_rom rsegs)) s LB.
  Proof.
    intros until errv. intros HR HE SPB ST CEIL LO STK ERR MI MBC MBL BHI MBA CASE ->.
    pose proof (word_lt64 sp) as SPR.
    assert (SUB : forall b, In b LBrest -> In b LB).
    { destruct CASE as [[_ ->]|(k & _ & ->)]; [auto|]. intros b Hb. eapply lb_remove_sub. exact Hb. }
    destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3.
    pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    pose proof (mbloc_lo rsegs AI _ _ _ _ _ _ _ _ HR SUB MBL) as MBLO.
    pose proof (mbloc_pos rsegs AI _ _ _ _ _ _ _ _ HR SUB MBL ltac:(lia)) as MBP.
    pose proof (mbloc_errno rsegs AI _ _ _ _ _ _ _ _ LOK HR SUB MBL ltac:(lia)) as MBE.
    assert (MBB : (MB + 32 <= B)%Z).
    { destruct MBL as [H|(b & Hb & H1 & H2)]; [lia|]. destruct (ai_block_range rsegs AI _ _ _ _ HR (SUB b Hb)) as (_ & _ & _ & R4 & _). cbn in R4. lia. }

    eapply sreach_evt. { eapply (dseg1 lo MB A len cap); try eassumption; lia. }
    intros ms' (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & MBC1).
    assert (HR1 : RHEAP rsegs AI s LB m1).
    { eapply (ai_heap_frame rsegs AI); [exact HR| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
    assert (HE1 : RENV rsegs AI m1 B).
    { eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
    pose proof (rw_cells_transport rsegs _ m m1 _ _ ERR MU1 WM1 ltac:(cbn; lia)) as ERR1.
    assert (HP1 : hpx AI [(MB, MB + 32)]%Z LBrest (bv_unsigned sp) m m1).
    { eapply (hpx_seg rsegs AI); [exact LOK| exact HR| exact SUB| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }

    assert (TAIL : forall sx m2 (a0' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) errv2,
      mem_inv rsegs m2 -> stk rsegs m2 lo (bv_unsigned sp + -16) -> RENV rsegs AI m2 B ->
      rw_cells rsegs m2 (al_errno L) [C4 errv2] -> RHEAP rsegs AI sx LBrest m2 ->
      rw_cells rsegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra] -> rw_cells rsegs m2 MB (mbuf_cells A len cap) ->
      hpx AI [(MB, MB + 32)]%Z LBrest (bv_unsigned sp) m m2 ->
      SREACH AI (membuffer_destroy_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBrest MB lo B m)
        (MS (mkR (wz 0x166e0) (wz (bv_unsigned sp + -16)) gp (wz (al_tp L)) t0' t1' t2' (wz MB) s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (wz 0x166e0) fc None m2 (seg_rom rsegs)) sx LBrest).
    { intros until errv2. intros MI2 ST2 HE2 ERR2 HR2 FR2 MBC2 HP2.
      eapply sreach_evt. { eapply (dseg2 lo MB A len cap); try eassumption; lia. }
      intros ms' (a0'' & m3 & -> & MU3 & WM3 & MI3 & ST3 & MBC3).
      pose proof (rw_cells_transport rsegs _ m2 m3 _ _ ERR2 MU3 WM3 ltac:(cbn; lia)) as ERR3.
      apply sreach_ret. unfold membuffer_destroy_post.
      repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
      split; [exact MI3|]. split; [exact ST3|]. split.
      { eapply (ai_env_frame rsegs AI); [exact HR2| exact HE2| exact MU3| exact WM3|].
        constructor. { left. cbn. lia. } constructor; [| constructor]. eapply (mbloc_ef rsegs AI); [exact MBL| lia| auto]. }
      split; [eexists; exact ERR3|]. split.
      { eapply (hpx_trans rsegs AI); [exact HP2|].
        eapply (hpx_seg rsegs AI); [exact LOK| exact HR2| auto| exact MU3| exact WM3|].
        constructor. { left. cbn. lia. } constructor; [| constructor]. right; right. cbn. lia. }
      split; [reflexivity|]. split; [| exact MBC3].
      eapply (ai_heap_frame rsegs AI); [exact HR2| exact MU3| exact WM3|].
      constructor. { left. cbn. lia. } constructor; [| constructor]. eapply (mbloc_hf rsegs AI); [exact MBL| lia| auto]. }
    destruct CASE as [[-> ->]|(k & HIN & ->)].
    -
      eapply sreach_evt. { rewrite <- FREEPC. eapply (ac_free_null rsegs AI AC). reflexivity. }
      intros ms' P. destruct_exs P. subst ms'.
      replace (ret_pc (Z_to_bv 64 91872)) with (Z_to_bv 64 91872) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply TAIL; try eassumption.
    -
      eapply sreach_bind.
      { rewrite <- FREEPC. eapply (ac_free rsegs AI AC) with (lo := lo) (B := B); try eassumption; try reflexivity;
          rewrite ?unsigned_lit by lia; try lia; try eassumption. }
      intros s' LB' ms'' POST. unfold free_post in POST. destruct_exs POST.
      destruct POST as (-> & AF & -> & HR2).
      destruct AF as (MI2 & ST2 & HE2 & [errv2 ERR2] & HPF). rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPF by lia.
      replace (ret_pc (Z_to_bv 64 91872)) with (Z_to_bv 64 91872) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF FR1 ltac:(apply client_range_above; cbn; lia)) as FR2.
      lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
      assert (MBC2 : rw_cells rsegs m2 MB (mbuf_cells A len cap)).
      { eapply (heap_pres_rw_cells rsegs AI); [exact HPF| exact MBC1|]. unfold mbuf_cells. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul].
        eapply (mbloc_client rsegs AI). eapply (mbloc_weaken rsegs AI); [exact MBL| lia| auto]. }
      eapply TAIL; try eassumption.
      eapply (hpx_trans rsegs AI); [exact HP1|]. apply hpx_of_heap_pres. eapply (heap_pres_weaken rsegs AI); [exact HPF| lia| auto].
  Qed.
End W.
