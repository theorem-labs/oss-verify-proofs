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

Definition e_ossl_lib_ctx_get_concrete : Z := 0x1f6b18.

(* [comment removed for export] *)
Definition ossl_lib_ctx_get_concrete_s0_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma ossl_lib_ctx_get_concrete_s0_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  (bv_eqb a0 (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_lib_ctx_get_concrete_s0_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1f6b18) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP BR0_1 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  zstep.
  do 2 zstore.
  zstep.
  zstep. wg_raw BR0_1.
  do 4 zstep.
  release_frame FR ST (bv_unsigned sp).
  unfold ossl_lib_ctx_get_concrete_s0_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

Section ossl_lib_ctx_get_concrete_cps.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.

Definition ossl_lib_ctx_get_concrete_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + 16 <= bv_unsigned sp ->
  (bv_eqb a0 (Z_to_bv 64 0)) = false ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_ossl_lib_ctx_get_concrete m)))
    (fun c => ASTA RT Σ PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 m' ms
           /\ rt_after RT Σ (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [] m m') c).

Theorem ossl_lib_ctx_get_concrete_cps : ossl_lib_ctx_get_concrete_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    FDO MST -> ART0 MI0 CALL HSTK BRW0.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 16 /\ 0x10007fff8000 < usp - 16 /\ usp <= USTACK_TOP /\ 0x10007fff8000 <= lo /\ usp <= 2 ^ 47)
    by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  cl_eu usp (-16) EU1.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  (* [comment removed for export] *)
  pose proof (ossl_lib_ctx_get_concrete_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; lia) BRW0 MI0) as W1.
  cl_lift W1 HA c1 Hc1.
  apply Hk.
  apply (ASTA_conseq RT Σ PMc _ _ c1 Hc1). intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1). fold usp in MU1, ST1.
  exists m1.
  split; [exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F, fc; reflexivity|].
  assert (ART1 : ART RT Σ m1).
  { apply (wg_seg_ART RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1); [|exact WM1].
    intros x Hx. exfalso; apply Hx; exact I. }
  split; [split; [exact ART1|]; split; [exact MI1|]; split; [exact WM1 | exact ST1]|].
  intros a Ha Ho.
    pose proof (cl_split RT AF Σ m usp 16 _ ART0 ltac:(lia) ltac:(lia) Ha) as SPL.
    rewrite (MU1 a ltac:(cbn [app outside] in Ho |- *; repeat (split; [lia|]); exact I)).
    reflexivity.
Qed.
End ossl_lib_ctx_get_concrete_cps.
