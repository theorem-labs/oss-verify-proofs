(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_ut RT_iface_pem Fz_kit Fz_chk Fz_M_malloc Fz_env.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.


Definition e_OPENSSL_cleanse : Z := 0x202e70.

Definition cleanse_post (ra sp gp tp t0 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (d n lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra sp gp tp t0 (Z_to_bv 64 e_memset) t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 0) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_memset) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma cleanse_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (d n lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> SEGTOP_A <= lo -> bv_unsigned sp <= 2^47 ->
  ro_cells asegs m CL_MEMSET_FUNC [C8 (Z_to_bv 64 e_wrap_memset)] -> mem_inv asegs m ->
  evt asegs (cleanse_post ra sp gp tp t0 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc d n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_OPENSSL_cleanse) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG SPH MSF MI. unfold e_OPENSSL_cleanse, CL_MEMSET_FUNC, e_wrap_memset, SEGTOP_A in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 16, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  do 11 zstep.
  release_frame FR ST SP.
  zstep.
  unfold cleanse_post, e_memset. apply evt_done. eexists. split; [subst SP; rewrite ?Z_to_bv_bv_unsigned; reflexivity|].
  rewrite (unsigned_lit SP) by lia. replace (SP - 16) with (SP + -16) by lia. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Section CCleanse.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MSET : memset_icontract RT e_memset.

(* [comment removed for export] *)
Definition openssl_cleanse_env_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (d n lo : Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 n -> tp = Z_to_bv 64 0xba3ef0 ->
  0 <= d -> d + n <= 2^47 -> 0 <= n < 2^40 -> checked_dst RT Σ m sp d n -> (forall x, cl_cell x -> ~ (d <= x < d + n)) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_OPENSSL_cleanse m)))
    (ASTA RT Σ PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) m' ms
         /\ rt_after RT Σ (bv_unsigned sp) lo m m'
         /\ rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) d n m m'
         /\ bytes_at asegs m' d (repeat (Z_to_bv 8 0) (Z.to_nat n)) /\ cl_env m' lb canary)).

Theorem openssl_cleanse_cps : openssl_cleanse_env_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d n lo lb canary
    FDO MST -> -> -> Hd0 Hd47 Hn CHK OFF ART0 MI0 CALL ENV.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 16 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  pose proof (cleanse_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d n lo
                ST ltac:(fold usp; unfold RT_STACK in *; lia) HLOI ltac:(fold usp; unfold USTACK_TOP in *; lia) (cl_env_msf m lb canary ENV) MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, ST1.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  pose proof (cl_env_seg _ m m1 lb canary ENV MU1 ltac:(cl_fp_lia)) as ENV1.
  destruct CHK as (CK1 & CK2 & CK3).
  apply (MSET Σ PMc ra sp gp (Z_to_bv 64 0xba3ef0) t0 (Z_to_bv 64 e_memset) t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 0) (Z_to_bv 64 n) a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 d n (Z_to_bv 8 0) lo FDO MST eq_refl eq_refl eq_refl ltac:(lia) Hn).
  { split; [intros Hn0; destruct (CK1 Hn0) as (ACC & RC); split; [| exact RC];
            apply (acc_munch_sh _ m m1 d n ACC MU1); [apply sh_fp_cons; [right; unfold RT_STACK in *; lia | apply sh_fp_nil] | lia | lia]|].
    split; [exact CK2 | exact (wr_at_wm m m1 _ _ CK3 WM1)]. }
  { exact ART1. } { exact MI1. }
  { unfold call_ok. split; [exact ST1|]. split; [exact LOW|]. split; [exact LOR|]. split; [exact SPT | exact SPA]. }
  { exact Hc1'. }
  clear Hc1'. intros c2 Hc2. apply Hk.
  apply (ASTA_conseq RT Σ PMc _ _ c2 Hc2). intros ms (m2 & RS & (ART2 & MI2 & WM2 & ST2) & PRES & ZER). exists m2.
  split; [exact RS|]. split; [exact (conj ART2 (conj MI2 (conj (wmono_trans asegs _ _ _ WM1 WM2) ST2)))|].
  split; [intros a Ha Hnd; rewrite (PRES a Ha Hnd); exact (PR1 a Ha I)|].
  split; [exact ZER|].
  exact (cl_env_pres_ex _ _ _ d n m1 m2 lb canary ENV1 PRES OFF).
Qed.

End CCleanse.
