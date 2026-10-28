(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3 RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Pj_rtkA Pj_defsA Pj_os_defsA Pj_os_dtorA El_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section OsDtor.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis ROA : forall Σ m, ART RT Σ m -> pj_os_roA m.

Definition osdtor_cps2A : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (OS q lo fO : Z) (kO : nat)
         (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  In (fO, kO) (rt_frames RT Σ) -> fO <= OS -> OS + 288 <= fO + fs_size kO - 8 -> OS mod 16 = 0 -> unwind_ok ra s0 (wz q) ->
  OSDUMPA m OS -> bytes_at asegs m (shad OS) (repeat z8 36) -> LOCBA m -> libc_nl m -> lockwA m ->
  ART RT Σ m -> mem_inv asegs m -> stk asegs m lo q -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + EL_OSDTOR_STACK_A <= q ->
  q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  (forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ m' -> mem_inv asegs m' -> stk asegs m' lo q -> (exists jos, rw_cells asegs m' OS [CB 288 jos]) -> LOCBA m' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(OS, OS + 288)] m m' ->
     aevt RT PMc Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F' (ret_pc ra) fc None m' (seg_rom asegs))) ->
  aevt RT PMc Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz OS) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz EL_OSDTOR_A) fc None m (seg_rom asegs)).

Local Ltac ul := unfold EL_OSDTOR_STACK_A, PJ_IOS_DTOR_STACK_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Theorem osdtor_okA : osdtor_cps2A.
Proof using AF RC ROA.
  unfold osdtor_cps2A. intros until m. intros FDO MST INF FLO FHI AL16 UNW OSD SHZ LOC NL LW ART0 MI ST LOW LOR SPT SP16 HK.
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & FSEG & FLIVE).
  pose proof (fframe_ranges RT AF Σ m fO kO ART0 INF) as (_ & _ & FSZ0 & SHB0 & SHT).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (proj2 (af_fshadow_apart RT AF Σ m fO kO ART0 INF) fO kO INF) as FSELF.
  pose proof (ROA Σ m ART0) as (_ & GVT & _ & _).
  remember (fs_size kO) as FSZ eqn:EFSZ.
  assert (LO32 : lo <= q - 32) by ul. assert (Q0 : 0 <= q - 32) by (destruct ST; ul).
  assert (UQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; ul).
  assert (UQ32 : bv_unsigned (wz (q + -32)) = q + -32) by (apply unsigned_lit; ul).
  assert (EOS : bv_unsigned (wz OS) = OS) by (apply unsigned_lit; ul).
  assert (SHOS : shad fO <= shad OS /\ shad OS + 36 <= shad (fO + FSZ)) by (unfold shad in *; Z.div_mod_to_equations; lia).
  destruct OSD as (pb & pp & ep & fill & dum & j148 & j284 & OSC).
  pose proof (munch_refl [(q - 32, q); (OS, OS + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.

  unfold os_cellsA, sb_cellsA, ios_cellsA in OSC. cbn [app] in OSC.
  pose proof (shb_cells_of_art RT AF Σ m ART0) as [G1 G2].
  assert (LOQ : 7118848 <= q - 32) by ul. assert (SHQ : shad OS + 36 <= q - 32) by ul. assert (QH : q < 2^47) by ul.
  unfold PJ_GOT_VT_A in GVT. change (id (bytes_at asegs m (shad OS) (repeat z8 36))) in SHZ.
  apply (aevt_evt RT AF PMc MST).

  unfold EL_OSDTOR_A. zstep. carve_frame 32%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  lstep. lstep. lstep.

  zstep. step. step.

  zstep. astep. zstep. zstep. zstep. zstep. zstep.

  assert (FPC : fp_client RT Σ lo [(q - 32, q); (OS, OS + 8)]%Z).
  { constructor. { left. cbn [fst snd]. ul. } constructor. { right; right. exists fO, kO. cbn [fst snd]. split; [exact INF| lia]. } constructor. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (ARTx : ART RT Σ mx) by (exact (art_fp_client RT AF Σ m mx lo _ ART0 LOW FPC MU WM));
    assert (SHZx : bytes_at asegs mx (shad OS) (repeat z8 36))
      by (unfold id in SHZ; apply (bytes_at_agree asegs m mx _ _ SHZ); apply (agree_of_munch _ _ _ _ MU); intros x Hx; rewrite repeat_length in Hx; cbn [outside]; split; [clear - Hx SHQ; lia| split; [clear - Hx FSELF SHOS FLO FHI EFSZ; subst FSZ; lia| exact I]]);
    assert (SZO : shz mx OS 288)
      by (apply (fobj_shz RT AF Σ mx OS 288 ARTx); split; [Z.div_mod_to_equations; lia|]; split; [lia|]; split; [exists fO, kO; split; [exact INF| subst FSZ; lia]| exact SHZx])
  end.
  shz_pose SZO OS. zstep. rewrite ?shr3_div. zstep. zstep. shz_norm. step. if_false.

  zstep. step. zstep. lstep.

  astep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (MIx : mem_inv asegs mx) by assumption;
    assert (IMP : rw_cells asegs mx (OS + 8) [C8 (wz PJ_LOC_IMP_A)])
      by (lazymatch goal with H : rw_cells asegs mx OS (?c0 :: ?c1 :: ?rest) |- _ =>
            pose proof H as X; change (c0 :: c1 :: rest) with ([c0] ++ [c1] ++ rest) in X;
            apply Sj_stage1_kit.rw_cells_app in X; destruct X as [_ X]; apply Sj_stage1_kit.rw_cells_app in X; destruct X as [X _];
            cbn [cells_size csize Nat.add] in X; replace (OS + Z.of_nat 8) with (OS + 8) in X by lia; exact X end);
    assert (LBx : LOCBA mx) by (apply (LOCBA_agree m mx LOC); apply (agree_of_munch _ _ _ _ MU); intros x Hx; cbv beta in Hx; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx; cbn [outside];
                                 split; [clear - Hx LOQ; lia| split; [clear - Hx FSEG FLO FHI F0 EFSZ; subst FSZ; unfold SEGTOP_A in FSEG; lia| exact I]])
  end.

  eapply evt_cut.
  { eapply (locdtor_evtA_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (OS + 8)%Z); [exact IMP| exact LBx| exact MIx]. }
  cbv beta. intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & ->).
  rewrite (ret_pc_even 0xb4600) by lia.

  astep. step. step. step. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (STx : stk asegs mx lo (q + -32)) by assumption;
    assert (STq : stk asegs mx lo q)
      by (pose proof (stk_release asegs mx lo _ _ STx FR ltac:(lia)) as X; cbn [cells_size csize Nat.add] in X; replace (q + -32 + Z.of_nat 32) with q in X by lia; exact X);
    assert (ART2 : ART RT Σ mx) by (exact (art_fp_client RT AF Σ m mx lo _ ART0 LOW FPC MU WM));
    assert (SHZ2 : bytes_at asegs mx (shad OS) (repeat z8 36))
      by (unfold id in SHZ; apply (bytes_at_agree asegs m mx _ _ SHZ); apply (agree_of_munch _ _ _ _ MU); intros x Hx; rewrite repeat_length in Hx; cbn [outside];
          split; [clear - Hx SHQ; lia| split; [clear - Hx FSELF SHOS FLO FHI EFSZ; subst FSZ; lia| exact I]]);
    rename mx into m2
  end.

  lazymatch goal with H : rw_cells asegs m2 OS (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?rest) |- _ =>
    pose proof H as OSC2; pose proof H as IOS2;
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: rest) with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9] ++ rest) in IOS2 end.
  apply Sj_stage1_kit.rw_cells_app in IOS2. destruct IOS2 as [_ IOS2]. cbn [cells_size csize Nat.add] in IOS2. replace (OS + Z.of_nat 136) with (OS + 136) in IOS2 by lia.
  destruct (rw_cells_forget asegs m2 OS _ OSC2) as [bo HULL2]. cbn [cells_size csize Nat.add] in HULL2.
  apply evt_done.
  eapply (iosdtor_cpsA_proof RT AF RC PMc FDO MST Σ K OS q lo fO kO ra gp _ _ _ s0 s1 _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 FDO MST INF FLO ltac:(subst FSZ; exact FHI) AL16);
    [exists PJ_IOS_VPTR_A, fill, j148, j284; exact IOS2| exact (conj (ex_intro _ bo HULL2) SHZ2)| exact LBx| exact UNW| exact ART2| assumption| exact STq| exact LOW
    | clear - LOR; ul| exact SPT| exact SP16|].
  intros w0 w1 w2 d0 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F' m' ART' MI' ST' HULL' PRES'.
  apply (HK w0 w1 w2 d0 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F' m' ART' MI' ST' (proj1 HULL')).
  - apply (LOCBA_agree m2 m' LBx). intros a Ha. cbv beta in Ha. apply PRES'; [right; left; apply client_static_intro; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Ha; clear - Ha; lia|].
    cbn [outside]. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Ha. clear - Ha FSEG FLO FHI F0 EFSZ. subst FSZ. unfold SEGTOP_A in FSEG. split; [lia| exact I].
  - intros a Ha Ho. cbn [outside] in Ho. rewrite (PRES' a Ha); [| cbn [outside]; split; [clear - Ho; lia| exact I]].
    apply MU. cbn [outside]. pose proof (aclient_split_c RT AF Σ m q (bv_unsigned a) ART0 Ha) as SPL. split; [clear - SPL LOW LOR; ul| split; [clear - Ho; lia| exact I]].
Qed.
End OsDtor.
