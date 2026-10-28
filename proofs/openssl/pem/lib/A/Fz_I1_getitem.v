(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Th_mutex Fz_T_lock Fz_I1_img Fz_I1_hash Fz_I1_defs Fz_I1_getrn Fz_I1_retrieve Fz_I1_insert Fz_I1_loadw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition e_get_item : Z := 0x1ff180.
Definition e_T_read_lock : Z := 0x1f6028.
Definition IGI_LOCK_RET : Z := 0x1ff1ac.       (* [comment removed for export] *)
Definition IGI_RETR_RET : Z := 0x1ff1c0.       (* [comment removed for export] *)
Definition IGI_UNLOCK_RET : Z := 0x1ff1d0.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition igi_w0_post (sp gp tp t0 t1 t2 s0 a0 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s1 s2 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (LK : Z) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 IGI_LOCK_RET) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp a0 (Z_to_bv 64 LK) (Z_to_bv 64 LK) a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 0xb9f198) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_T_read_lock) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' lo (bv_unsigned sp + -32).

Lemma igi_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo LK : Z),
  rw_cells asegs m G_ERR_LOCK [C8 (Z_to_bv 64 LK)] -> 0 <= LK < 2^64 ->
  img_untouched m ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (igi_w0_post sp gp tp t0 t1 t2 s0 a0 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s1 s2 F fc lo m LK)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_get_item) fc None m (seg_rom asegs)).
Proof.
  intros until LK. intros LKC LKR UT ST LO0 LO HTOP MI.
  unfold e_get_item. unfold G_ERR_LOCK in LKC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  do 11 zstep.
  apply evt_done. unfold igi_w0_post, IGI_LOCK_RET, e_T_read_lock. eexists.
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
Lemma igi_w1 : forall (sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s1 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo lh : Z),
  rw_cells asegs m G_ERR_HASH [C8 (Z_to_bv 64 lh)] -> 0 <= lh < 2^64 ->
  img_untouched m ->
  stk asegs m lo (bv_unsigned sp + -32) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR (Z_to_bv 64 IGI_RETR_RET) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 lh) s1 a2 a3 a4 a5 a6 a7
                                   (Z_to_bv 64 0xb9f198) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 e_lh_retrieve) fc None m (seg_rom asegs))
      (MS (mkR (Z_to_bv 64 IGI_LOCK_RET) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0xb9f198) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 IGI_LOCK_RET) fc None m (seg_rom asegs)).
Proof.
  intros until lh. intros LHC LHR UT ST LO0 LO HTOP MI.
  unfold IGI_LOCK_RET in *. unfold G_ERR_HASH in LHC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  zstep. th_if_lit.
  do 3 zstep. zstep.
  apply evt_done. unfold IGI_RETR_RET, e_lh_retrieve. cbv delta [mkR]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma igi_w2 : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo LK v : Z),
  rw_cells asegs m G_ERR_LOCK [C8 (Z_to_bv 64 LK)] -> 0 <= LK < 2^64 -> 0 <= v < 2^64 ->
  img_untouched m ->
  stk asegs m lo (bv_unsigned sp + -32) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR (Z_to_bv 64 IGI_UNLOCK_RET) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 v) (Z_to_bv 64 LK) (Z_to_bv 64 LK) a2 a3 a4 a5 a6 a7
                                   (Z_to_bv 64 0xb9f198) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 e_T_unlock) fc None m (seg_rom asegs))
      (MS (mkR (Z_to_bv 64 IGI_RETR_RET) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0xb9f198) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 IGI_RETR_RET) fc None m (seg_rom asegs)).
Proof.
  intros until v. intros LKC LKR VR UT ST LO0 LO HTOP MI.
  unfold IGI_RETR_RET in *. unfold G_ERR_LOCK in LKC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  do 3 zstep. zstep.
  apply evt_done. unfold IGI_UNLOCK_RET, e_T_unlock. cbv delta [mkR]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma igi_w3 : forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo : Z) (rav s0v s1v s2v : word),
  rw_cells asegs m (bv_unsigned sp + -32) [C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk asegs m lo (bv_unsigned sp + -32) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v s1 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (ret_pc rav) fc None m (seg_rom asegs)
                       /\ stk asegs m lo (bv_unsigned sp))
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 IGI_UNLOCK_RET) fc None m (seg_rom asegs)).
Proof.
  intros until s2v. intros FR ST LO0 LO HTOP MI.
  unfold IGI_UNLOCK_RET in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) (-32) EU1.
  zstep. zstep. do 4 zstep.
  pose proof FR as FR'. eapply stk_release in FR'; [| exact ST| lia]. cbn [cells_size csize Nat.add] in FR'.
  replace (bv_unsigned sp + -32 + Z.of_nat 32) with (bv_unsigned sp) in FR' by lia.
  zstep. zstep. apply evt_done. split; [| exact FR']. cbv delta [mkR].
  replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia. rewrite ?(Z_to_bv_bv_unsigned sp). reflexivity.
Qed.

Section GetItem.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.

(* [comment removed for export] *)
Definition igi_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (L REST : list (Z * Z)) (lh B : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (LK data fd : Z) (kd : nat) (kw : word),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 data -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 176 <= bv_unsigned sp ->
  rw_cells asegs m G_ERR_LOCK [C8 (Z_to_bv 64 LK)] -> rw_cells asegs m G_ERR_HASH [C8 (Z_to_bv 64 lh)] ->
  In (LK, 40) REST -> LK mod 4 = 0 -> rw_cells asegs m LK (mutex_cells z64 z64) ->
  lh_repE GOBJ m L lh B g bks -> Permutation (rt_live RT Σ) (L ++ REST) -> Forall (fun x => 0 < snd x) REST ->
  In (fd, kd) (rt_frames RT Σ) -> fd <= data -> data + 8 <= fd + fs_size kd - 8 -> rw_cells asegs m data [C8 kw] -> acc asegs m data 8 -> data mod 8 = 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_get_item m)))
    (fun c => exists v : Z,
       ASTA RT Σ PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 v) m' ms
           /\ rt_after_f RT Σ (bv_unsigned sp) lo m m'
           /\ rt_pres_fp REST (rt_frames RT Σ) (bv_unsigned sp) [(LK + 4, LK + 8)] m m'
           /\ lh_repE GOBJ m' L lh B g bks /\ rw_cells asegs m' LK (mutex_cells z64 z64) /\ rw_cells asegs m' data [C8 kw]) c
       /\ (v = 0 \/ DVerr GOBJ v)).

Theorem igi_cps : igi_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo L REST lh B g bks LK data fd kd kw
    FDO MST -> -> ART0 MI0 CALL HSTK LKC LHC INLK AL4 MC REPE PERM RPOS KIN KF1 KF2 KC KA KAL.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 176 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ SEGTOP_A <= lo) by (unfold RT_STACK, STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
  cl_eu usp (-32) EU1.
  unfold G_ERR_LOCK in LKC. unfold G_ERR_HASH in LHC.
  assert (INR : forall x, In x REST -> In x (rt_live RT Σ)) by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact PERM| apply in_or_app; right; exact Hx]).
  assert (INL : forall x, In x L -> In x (rt_live RT Σ)) by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact PERM| apply in_or_app; left; exact Hx]).
  pose proof (af_live_range RT AF Σ m LK 40 ART0 (INR _ INLK)) as (LK0 & LKLO & _). pose proof (afp_live_hi RT GOBJ AFP Σ m LK 40 ART0 (INR _ INLK) ltac:(lia)) as LKHI.
  assert (LKR : 0 <= LK < 2^64) by (unfold STACK_WIN, USTACK_TOP in *; lia).
  assert (LO0 : 0x10007fff8000 <= lo) by lia. assert (HT1 : bv_unsigned sp <= 2 ^ 47) by (fold usp; unfold USTACK_TOP in *; lia).
  pose proof (af_frames_range RT AF Σ m fd kd ART0 KIN) as (FD0 & FDLO & _ & FDAP).
  destruct REPE as (REP & PERML & ALN). pose proof (lh_geo_bounds g (proj1 REP)) as GB.
  assert (INLH : In (lh, 104) (rt_live RT Σ)) by (apply INL; eapply Permutation_in; [apply Permutation_sym; exact PERML| left; reflexivity]).
  assert (INB : In (B, 8 * g_na g) (rt_live RT Σ)) by (apply INL; eapply Permutation_in; [apply Permutation_sym; exact PERML| right; left; reflexivity]).
  pose proof (af_live_range RT AF Σ m lh 104 ART0 INLH) as (L0 & LLO & _). pose proof (afp_live_hi RT GOBJ AFP Σ m lh 104 ART0 INLH ltac:(lia)) as LHI.
  pose proof (af_live_range RT AF Σ m B (8 * g_na g) ART0 INB) as (B0 & BLO & _). pose proof (afp_live_hi RT GOBJ AFP Σ m B (8 * g_na g) ART0 INB ltac:(lia)) as BHI.
  assert (LHR : 0 <= lh < 2^64) by (unfold STACK_WIN, USTACK_TOP in *; lia).
  pose proof (FDAP lh 104 INLH) as KSEP0.
  (* [comment removed for export] *)
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (igi_w0 ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 (Z_to_bv 64 data) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo LK
                LKC LKR UT ST LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1. fold usp in MU1, ST1, FR1, Hc1'.
  assert (MU1' : munch ([] ++ [(usp - 32, usp)]) m m1) by (eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside app]; intros; lia).
  pose proof (cl_seg_ART RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1' ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  assert (BELOW1 : forall P : Z -> Prop, (forall x, P x -> x < usp - 32) -> agree_on P m m1) by (intros P HP a Ha; apply MU1; cbn [outside]; pose proof (HP _ Ha); split; [lia| exact I]).
  assert (MC1 : rw_cells asegs m1 LK (mutex_cells z64 z64)) by (apply (rw_cells_agree asegs m m1 _ _ MC); [apply BELOW1; cbn [cells_size csize Nat.add mutex_cells]; intros; lia| exact WM1]).
  (* [comment removed for export] *)
  pose proof (T_read_lock_proof (Z_to_bv 64 IGI_LOCK_RET) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 data) (Z_to_bv 64 LK) (Z_to_bv 64 LK) a2 a3 a4 a5 a6 a7
                (Z_to_bv 64 0xb9f198) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo) as WL.
  rewrite (unsigned_lit LK), EU1 in WL by lia. specialize (WL MC1 AL4 ST1 ltac:(lia) ltac:(unfold RT_STACK in *; lia) ltac:(left; lia) MI1).
  cl_lift WL Hc1' c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (a1' & a2' & a3' & a4' & a5' & m2 & -> & MU2 & WM2 & MI2 & ST2 & MC2) & Hc2'). clear Hc2.
  rewrite (ret_pc_even IGI_LOCK_RET) in Hc2' by (unfold IGI_LOCK_RET; lia).
  assert (MU02 : munch [(usp - 48, usp); (LK + 4, LK + 8)] m m2).
  { apply (munch_trans _ m m1 m2); [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside app]; intros; lia. }
  pose proof (wmono_trans asegs _ _ _ WM1 WM2) as WM02.
  assert (ART2 : ART RT Σ m2).
  { apply (af_frame RT AF Σ m m2 (usp - 48) ART0 ltac:(lia)); [| exact WM02]. intros a Ha. apply MU02. cbn [outside].
    split; [intros X; apply Ha; left; unfold USTACK_TOP in *; lia|]. split; [| exact I]. intros X. apply Ha. right; right; left. exists LK, 40. split; [exact (INR _ INLK)| lia]. }
  assert (OFF2 : forall P : Z -> Prop, (forall x, P x -> ~ (usp - 48 <= x < usp) /\ ~ (LK + 4 <= x < LK + 8)) -> agree_on P m m2).
  { intros P HP a Ha. apply MU02. cbn [outside]. destruct (HP _ Ha) as [X1 X2]. repeat split; try exact I; lia. }
  assert (OFF12 : forall P : Z -> Prop, (forall x, P x -> ~ (usp - 48 <= x < usp - 32) /\ ~ (LK + 4 <= x < LK + 8)) -> agree_on P m1 m2).
  { intros P HP a Ha. apply MU2. cbn [outside]. destruct (HP _ Ha) as [X1 X2]. repeat split; try exact I; lia. }
  eassert (FR2 : rw_cells asegs m2 (usp + -32) _) by (apply (rw_cells_agree asegs m1 m2 _ _ FR1); [apply OFF12; cbn [cells_size csize Nat.add]; intros; lia| exact WM2]).
  assert (LKC2 : rw_cells asegs m2 G_ERR_LOCK [C8 (Z_to_bv 64 LK)]) by (apply (rw_cells_agree asegs m m2 _ _ LKC); [apply OFF2; cbn [cells_size csize Nat.add]; unfold STACK_WIN in *; intros; lia| exact WM02]).
  assert (LHC2 : rw_cells asegs m2 G_ERR_HASH [C8 (Z_to_bv 64 lh)]) by (apply (rw_cells_agree asegs m m2 _ _ LHC); [apply OFF2; cbn [cells_size csize Nat.add]; unfold STACK_WIN in *; intros; lia| exact WM02]).
  pose proof (FDAP LK 40 (INR _ INLK)) as KLK.
  assert (KC2 : rw_cells asegs m2 data [C8 kw]) by (apply (rw_cells_agree asegs m m2 _ _ KC); [apply OFF2; cbn [cells_size csize Nat.add]; unfold STACK_WIN in *; intros; lia| exact WM02]).
  assert (KA2 : acc asegs m2 data 8) by (apply (acc_agree m m2 _ _ KA ltac:(lia)); apply OFF2; cbv beta; unfold shad, SHB, STACK_WIN in *; intros; lia).
  (* [comment removed for export] *)
  assert (LAP : lapart L) by exact (live_lapart RT AF Σ m L ART0 INL).
  destruct (lh_sep asegs LH_CEIL _ _ _ _ _ _ _ _ _ _ _ (ownL_apart L LAP) REP) as (S_LB & S_N & S_X & S_F).
  assert (NODESF : forall q A, In (q, A) (concat bks) -> In (A, 24) L /\ A + 24 <= lo /\ 0x10007fff8000 <= A /\ A mod 16 = 0 /\ (A + 24 <= LK \/ LK + 40 <= A)).
  { intros q A Hq. destruct (lh_rep_owned asegs LH_CEIL _ _ _ _ _ _ _ _ _ _ _ REP q A Hq) as [O _].
    pose proof (af_live_range RT AF Σ m A 24 ART0 (INL _ O)) as (_ & R1 & _). pose proof (afp_live_hi RT GOBJ AFP Σ m A 24 ART0 (INL _ O) ltac:(lia)) as R2.
    pose proof (proj1 (Forall_forall _ _) ALN (A, 24) O) as R3. cbn [fst] in R3.
    split; [exact O|]. split; [lia|]. split; [exact R2|]. split; [exact R3|]. exact (lrest_apart RT AF Σ m L REST A 24 LK 40 ART0 PERM O INLK ltac:(lia) ltac:(lia)). }
  pose proof (lrest_apart RT AF Σ m L REST lh 104 LK 40 ART0 PERM ltac:(eapply Permutation_in; [apply Permutation_sym; exact PERML| left; reflexivity]) INLK ltac:(lia) ltac:(lia)) as APLH.
  pose proof (lrest_apart RT AF Σ m L REST B (8 * g_na g) LK 40 ART0 PERM ltac:(eapply Permutation_in; [apply Permutation_sym; exact PERML| right; left; reflexivity]) INLK ltac:(lia) ltac:(lia)) as APB.
  assert (REP2 : lh_rep asegs LH_CEIL (DVerr GOBJ) m2 (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks)
    by (eapply lh_rep_agree; [exact REP| | intros ? ? ? ? _ X; exact X];
        eapply LhRep.agree_on_mono; [exact (LhRep.agree_on_of_munch asegs _ _ _ MU02 WM02)|];
        intros a [Ha|[Ha|(q & A & Hq & Ha)]]; cbn [outside]; [unfold STACK_WIN in *; repeat split; try exact I; lia| unfold STACK_WIN in *; repeat split; try exact I; lia|];
        destruct (NODESF q A Hq) as (_ & X2 & X3 & _ & X5); unfold STACK_WIN, RT_STACK in *; repeat split; try exact I; lia).
  assert (NODES2 : forall q A, In (q, A) (concat bks) -> acc asegs m2 A 24 /\ A mod 8 = 0 /\ A + 24 <= lo)
    by (intros q A Hq; destruct (NODESF q A Hq) as (O & X2 & X3 & X4 & X5); destruct (af_acc_live RT AF Σ m2 A 24 ART2 (INL _ O)) as [_ X1]; split; [exact X1|];
        split; [clear - X4; Z.div_mod_to_equations; lia| exact X2]).
  assert (DVF2 : forall d, DVerr GOBJ d -> (exists e : word, ro_cells asegs m2 d [C8 e]) /\ acc asegs m2 d 8)
    by (intros d Hd; destruct (dverr_cells RT GOBJ AF AFP Σ m2 d ART2 Hd) as (X1 & X2 & _); exact (conj X1 X2)).
  destruct (af_acc_live RT AF Σ m2 lh 104 ART2 INLH) as [_ ACL2]; destruct (af_acc_live RT AF Σ m2 B (8 * g_na g) ART2 INB) as [_ ACB2].
  assert (ALL : lh mod 8 = 0) by (pose proof (proj1 (Forall_forall _ _) ALN (lh, 104) ltac:(eapply Permutation_in; [apply Permutation_sym; exact PERML| left; reflexivity])) as X; cbn [fst] in X; clear - X; Z.div_mod_to_equations; lia).
  assert (ALB : B mod 8 = 0) by (pose proof (proj1 (Forall_forall _ _) ALN (B, 8 * g_na g) ltac:(eapply Permutation_in; [apply Permutation_sym; exact PERML| right; left; reflexivity])) as X; cbn [fst] in X; clear - X; Z.div_mod_to_equations; lia).
  pose proof (af_acc_stack RT AF Σ m2 (usp - 64) 32 ART2 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia)) as ACCF2.
  destruct (af_client_consts RT AF Σ m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (igi_w1 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp a1' a2' a3' a4' a5' a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (Z_to_bv 64 data) F fc m2 lo lh
                     LHC2 LHR UT2 ST2 LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI2) as W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & -> & Hc3'); clear Hc3.
  (* [comment removed for export] *)
  pose proof (lh_retrieve_proof (Z_to_bv 64 IGI_RETR_RET) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 data) (Z_to_bv 64 lh) (Z_to_bv 64 data) a2' a3' a4' a5' a6 a7
                     (Z_to_bv 64 0xb9f198) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 GOBJ L lh B g bks data lo kw
                     REP2 LAP ACL2 ALL ltac:(lia) LHI ACB2 ALB ltac:(lia) NODES2 DVF2 ltac:(unfold IMG_UT_HI, SEGTOP_A in *; lia) eq_refl eq_refl
                     (proj1 KC2) KA2 KAL ltac:(lia) ltac:(lia) ltac:(lia)) as WR.
  rewrite EU1 in WR; specialize (WR ltac:(replace (usp + -32 - 32) with (usp - 64) by lia; exact ACCF2) ltac:(clear - SPA; Z.div_mod_to_equations; lia) UT2 SHC2 ST2 LO0
                                          ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) MI2).
  cl_lift WR Hc3' c4 Hc4.
  destruct (ASTA_unpack RT Σ _ _ c4 Hc4) as (ms4 & (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & m4 & v & -> & MU4 & WM4 & MI4 & ST4 & REP4 & VOK) & Hc4'); clear Hc4.
  rewrite (ret_pc_even IGI_RETR_RET) in Hc4' by (unfold IGI_RETR_RET; lia). rewrite EU1 in ST4, MU4.
  replace (usp + -32 - 144) with (usp - 176) in MU4 by lia.
  assert (ART4 : ART RT Σ m4)
    by (apply (af_frame RT AF Σ m2 m4 (usp - 176) ART2 ltac:(lia)); [| exact WM4]; intros a Ha; apply MU4; cbn [outside];
        split; [intros X; apply Ha; left; unfold USTACK_TOP in *; lia|]; split; [| exact I]; intros X; apply Ha; right; right; left; exists lh, 104; split; [exact INLH| lia]).
  assert (OFF24 : forall P : Z -> Prop, (forall x, P x -> ~ (usp - 176 <= x < usp - 32) /\ ~ (lh + 96 <= x < lh + 100)) -> agree_on P m2 m4)
    by (intros P HP a Ha; apply MU4; cbn [outside]; destruct (HP _ Ha) as [X1 X2]; repeat split; try exact I; lia).
  assert (VR : 0 <= v < 2^64) by (destruct VOK as [->|(_ & V1 & V2 & _)]; [lia| unfold IMG_UT_LO, IMG_UT_HI in *; lia]).
  eassert (FR4 : rw_cells asegs m4 (usp + -32) _) by (apply (rw_cells_agree asegs m2 m4 _ _ FR2); [apply OFF24; cbn [cells_size csize Nat.add]; unfold STACK_WIN in *; intros; lia| exact WM4]).
  assert (LKC4 : rw_cells asegs m4 G_ERR_LOCK [C8 (Z_to_bv 64 LK)]) by (apply (rw_cells_agree asegs m2 m4 _ _ LKC2); [apply OFF24; cbn [cells_size csize Nat.add]; unfold G_ERR_LOCK, STACK_WIN in *; intros; lia| exact WM4]).
  assert (MC4 : rw_cells asegs m4 LK (mutex_cells z64 (Z_to_bv 64 16))) by (apply (rw_cells_agree asegs m2 m4 _ _ MC2); [apply OFF24; cbn [cells_size csize Nat.add mutex_cells]; unfold STACK_WIN in *; intros; lia| exact WM4]).
  assert (KC4 : rw_cells asegs m4 data [C8 kw]) by (apply (rw_cells_agree asegs m2 m4 _ _ KC2); [apply OFF24; cbn [cells_size csize Nat.add]; unfold STACK_WIN in *; intros; lia| exact WM4]).
  destruct (af_client_consts RT AF Σ m4 ART4) as (_ & _ & _ & _ & UT4).
  (* [comment removed for export] *)
  pose proof (igi_w2 sp gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp (Z_to_bv 64 data) e1 e2 e3 e4 e5 e6 e7 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F fc m4 lo LK v
                     LKC4 LKR VR UT4 ST4 LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI4) as W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ _ _ c5 Hc5) as (ms5 & -> & Hc5'); clear Hc5.
  (* [comment removed for export] *)
  pose proof (T_unlock_proof (Z_to_bv 64 IGI_UNLOCK_RET) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp (Z_to_bv 64 v) (Z_to_bv 64 LK) (Z_to_bv 64 LK) e2 e3 e4 e5 e6 e7
                     (Z_to_bv 64 0xb9f198) s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F fc m4 lo) as WU.
  rewrite (unsigned_lit LK), EU1 in WU by lia; specialize (WU MC4 AL4 ST4 ltac:(lia) ltac:(unfold RT_STACK in *; lia) ltac:(left; lia) MI4).
  cl_lift WU Hc5' c6 Hc6.
  destruct (ASTA_unpack RT Σ _ _ c6 Hc6) as (ms6 & (b1 & b2 & b3 & m6 & -> & MU6 & WM6 & MI6 & ST6 & MC6) & Hc6'); clear Hc6.
  rewrite (ret_pc_even IGI_UNLOCK_RET) in Hc6' by (unfold IGI_UNLOCK_RET; lia). rewrite ?EU1 in ST6, MU6.
  replace (usp + -32 - 112) with (usp - 144) in MU6 by lia.
  assert (ART6 : ART RT Σ m6)
    by (apply (af_frame RT AF Σ m4 m6 (usp - 144) ART4 ltac:(lia)); [| exact WM6]; intros a Ha; apply MU6; cbn [outside];
        split; [intros X; apply Ha; left; unfold USTACK_TOP in *; lia|]; split; [| exact I]; intros X; apply Ha; right; right; left; exists LK, 40; split; [exact (INR _ INLK)| lia]).
  assert (OFF46 : forall P : Z -> Prop, (forall x, P x -> ~ (usp - 144 <= x < usp - 32) /\ ~ (LK + 4 <= x < LK + 8)) -> agree_on P m4 m6)
    by (intros P HP a Ha; apply MU6; cbn [outside]; destruct (HP _ Ha) as [X1 X2]; repeat split; try exact I; lia).
  eassert (FR6 : rw_cells asegs m6 (usp + -32) _) by (apply (rw_cells_agree asegs m4 m6 _ _ FR4); [apply OFF46; cbn [cells_size csize Nat.add]; intros; lia| exact WM6]).
  assert (KC6 : rw_cells asegs m6 data [C8 kw]) by (apply (rw_cells_agree asegs m4 m6 _ _ KC4); [apply OFF46; cbn [cells_size csize Nat.add]; unfold STACK_WIN in *; intros; lia| exact WM6]).
  (* [comment removed for export] *)
  pose proof (igi_w3 (Z_to_bv 64 IGI_UNLOCK_RET) sp gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp (Z_to_bv 64 v) (Z_to_bv 64 1) b1 b2 b3 e4 e5 e6 e7 (Z_to_bv 64 0xb9f198) s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F fc m6 lo ra s0 s1 s2
                     FR6 ST6 LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI6) as W3.
  cl_lift W3 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ _ _ c7 Hc7) as (ms7 & (-> & ST7) & Hc7'); clear Hc7.
  apply Hk; exists v; split; [| exact VOK].
  apply (ASTA_conseq RT Σ PMc _ _ c7 Hc7'); intros ms7 <-; exists m6; fold usp in ST7.
  split; [exists w0, w1, w2, b1, b2, b3, e4, e5, e6, e7, w3, w4, w5, w6, F, fc; reflexivity|].
  split; [exact (conj ART6 (conj MI6 ST7))|].
  assert (OFFS : forall a, aclient REST (rt_frames RT Σ) usp a -> usp <= a \/ a < usp - 176)
    by (intros a Ha; apply (cl_split RT AF Σ m usp 176 a ART0 ltac:(lia) ltac:(lia)); apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact INR| intros e He; exact He| lia]).
  assert (OFFL : forall a, aclient REST (rt_frames RT Σ) usp a -> ~ (lh + 96 <= a < lh + 100))
    by (intros a Ha X; exact (lblock_not_rest RT AF Σ m L REST lh 104 usp a ART0 PERM RPOS ltac:(lia) ltac:(eapply Permutation_in; [apply Permutation_sym; exact PERML| left; reflexivity]) ltac:(lia) Ha)).
  split.
  try (intros a Ha Ho; cbn [outside] in Ho; destruct (OFFS _ Ha) as [X|X]; pose proof (OFFL _ Ha) as Y;
            rewrite (MU6 a ltac:(cbn [outside]; repeat split; try exact I; lia)); rewrite (MU4 a ltac:(cbn [outside]; repeat split; try exact I; lia));
            apply MU02; cbn [outside]; repeat split; try exact I; lia).
  split; [| exact (conj MC6 KC6)].
  split; [| exact (conj PERML ALN)].
  eapply lh_rep_agree; [exact REP4| | intros ? ? ? ? _ X; exact X].
  eapply LhRep.agree_on_mono; [exact (LhRep.agree_on_of_munch asegs _ _ _ MU6 WM6)|].
  intros a [Ha|[Ha|(q & A & Hq & Ha)]]; cbn [outside]; [unfold STACK_WIN in *; repeat split; try exact I; lia| unfold STACK_WIN in *; repeat split; try exact I; lia|].
  destruct (NODESF q A Hq) as (_ & X2 & X3 & _ & X5); unfold STACK_WIN, RT_STACK in *; repeat split; try exact I; lia.
Qed.
End GetItem.
