(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut Fz_chk RT_iface_pem I_lkit Fz_G_kit .
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac wg_T := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => ifT | |- _ => idtac end.
Local Ltac wg_F := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => ifF | |- _ => idtac end.
Local Ltac zstore := zstep; fix_lit_store.
Local Ltac wg_raw H := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => rewrite H; cbv iota end.
Local Ltac wg_at p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => unify p q | |- _ => fail "wgen: unexpected pc" end.

Definition e_OPENSSL_LH_set_thunks : Z := 0x1ffe00.

(* [comment removed for export] *)
Definition OPENSSL_LH_set_thunks_s0_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (p0 : Z) (jba0_1 : list byte) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j1 : list byte) (j2 : list byte) (m' : mem),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p0) (Z_to_bv 64 (p0 + 48)) (Z_to_bv 64 0) a3 a4 (Z_to_bv 64 0) (Z_to_bv 64 2147450880) (Z_to_bv 64 0) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(p0, p0 + 104); (bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' p0 [CB 24 j1; C8 a1; C8 a2; C8 a3; C8 a4; CB 48 j2]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma OPENSSL_LH_set_thunks_s0_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (p0 : Z) (jba0_1 : list byte) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  img_untouched m ->
  ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m p0 [CB 104 jba0_1] ->
  acc asegs m p0 104 ->
  p0 mod 8 = 0 ->
  0x10007fff8000 <= p0 ->
  p0 + 104 <= 2 ^ 47 ->
  p0 + 104 <= lo ->
  (negb (bv_eqb (Z_to_bv 64 (Z.land p0 7)) (Z_to_bv 64 0))) = false ->
  mem_inv asegs m ->
  evt asegs (OPENSSL_LH_set_thunks_s0_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 p0 jba0_1 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ffe00) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP UT G1 HBa0 ACCa0 PALa0 HIa0 TOPa0 STKa0 BR0_2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(p0, p0 + 104); (bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  zstep.
  do 2 zstore.
  zstep.
  zstep. wg_F.
  do 7 zstep.
  zstep. wg_F.
  zstore.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  do 4 zstep.
  release_frame FR ST (bv_unsigned sp).
  unfold OPENSSL_LH_set_thunks_s0_post. apply evt_done. do 3 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

Section OPENSSL_LH_set_thunks_cps.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.

Definition OPENSSL_LH_set_thunks_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (p0 : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p0 -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + 16 <= bv_unsigned sp ->
  In (p0, 104) (rt_live RT Σ) -> p0 mod 16 = 0 ->
  (negb (bv_eqb (Z_to_bv 64 (Z.land p0 7)) (Z_to_bv 64 0))) = false ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_OPENSSL_LH_set_thunks m)))
    (fun c => ASTA RT Σ PMc (fun ms => exists (j1 : list byte) (j2 : list byte) (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p0) m' ms
           /\ rt_after RT Σ (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(p0, p0 + 104)] m m'
           /\ rw_cells asegs m' p0 [CB 24 j1; C8 a1; C8 a2; C8 a3; C8 a4; CB 48 j2]) c).

Theorem OPENSSL_LH_set_thunks_cps : OPENSSL_LH_set_thunks_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo p0
    FDO MST -> -> ART0 MI0 CALL HSTK INP_p0 P16_p0 BRW0.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 16 /\ 0x10007fff8000 < usp - 16 /\ usp <= USTACK_TOP /\ 0x10007fff8000 <= lo /\ usp <= 2 ^ 47)
    by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  cl_eu usp (-16) EU1.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m p0 104 ART0 INP_p0) as (_ & PHI_p0 & _).
  pose proof (afp_live_mem RT GOBJ AFP Σ m p0 104 ART0 INP_p0 ltac:(lia)) as (_ & PT_p0).
  pose proof (afp_live_hi RT GOBJ AFP Σ m p0 104 ART0 INP_p0 ltac:(lia)) as PHH_p0.
  pose proof (wg_mod16_8 _ P16_p0) as PAL_p0. assert (PR64_p0 : 0 <= p0 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  pose proof (af_acc_live RT AF Σ m p0 104 ART0 INP_p0) as (WR_p0_1 & ACC_p0_1).
  destruct (wr_at_rw_CB m p0 104 WR_p0_1 ltac:(lia)) as (jba0_1 & HB_p0_1). change (Z.to_nat 104) with 104%nat in HB_p0_1.
  (* [comment removed for export] *)
  pose proof (OPENSSL_LH_set_thunks_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 p0 jba0_1 F fc m lo
                ST ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; lia) UT SHC HB_p0_1 ACC_p0_1 PAL_p0 PHH_p0 PT_p0 ltac:(unfold STACK_WIN in *; lia) BRW0 MI0) as W1.
  cl_lift W1 HA c1 Hc1.
  apply Hk.
  apply (ASTA_conseq RT Σ PMc _ _ c1 Hc1). intros ms1 (j1 & j2 & m1 & -> & MU1 & WM1 & MI1 & H1_0 & H1_1 & ST1). fold usp in MU1, ST1.
  exists j1, j2, m1.
  split; [exists t0, t1, t2, (Z_to_bv 64 (p0 + 48)), (Z_to_bv 64 0), a3, a4, (Z_to_bv 64 0), (Z_to_bv 64 2147450880), (Z_to_bv 64 0), t3, t4, t5, t6, F, fc; reflexivity|].
  assert (ART1 : ART RT Σ m1).
  { apply (wg_seg_ART RT AF Σ m m1 usp 16 [(p0, p0 + 104)] ART0 ltac:(lia) ltac:(lia) MU1); [|exact WM1].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists p0, 104; split; [exact INP_p0 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  split; [split; [exact ART1|]; split; [exact MI1|]; split; [exact WM1 | exact ST1]|].
  split.
  { intros a Ha Ho.
    pose proof (cl_split RT AF Σ m usp 16 _ ART0 ltac:(lia) ltac:(lia) Ha) as SPL.
    rewrite (MU1 a ltac:(cbn [app outside] in Ho |- *; repeat (split; [lia|]); exact I)).
    reflexivity. }
  exact H1_0.
Qed.
End OPENSSL_LH_set_thunks_cps.
