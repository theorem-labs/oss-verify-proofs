(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_elemwA Atp_elemxA Atp_elemA Atp_walkA Atp_objhA El_arm26wA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition root_preA (RT : rt_sig) (E : aenvA) (Σ : rts RT) (m : mem) (q out node i : Z) (jo : list byte) (need cost : Z) (frames : nat) : Prop :=
  rw_cells asegs m node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] /\ 0 < node /\ node + 16 <= ae_lo E /\ node mod 8 = 0
  /\ rw_cells asegs m out [CB 24 jo] /\ q <= out /\ out + 24 <= ae_hi E /\ out mod 8 = 0
  /\ (forall m', munch (elem_W q out) m m' -> wmono asegs m m' -> fobj RT Σ m' node 16)
  /\ ART RT Σ m /\ mem_inv asegs m /\ stk asegs m (ae_lo E) q /\ ae_lo E + need <= q /\ q mod 16 = 0
  /\ (length (rt_frames RT Σ) + frames <= FRAMES_MAX2)%nat /\ cost <= rt_credit RT Σ
  /\ (Z.of_nat (length (rt_live RT Σ)) + 1 <= LIVE_MAX /\ lposA (rt_live RT Σ)).

Definition atp_root_cpsA (RT : rt_sig) (E : aenvA) (d : nat) : Prop :=
  forall (Σ : rts RT) PMc (ptr : list Z) (i j : Z) (q out node P : Z)
         (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (jo : list byte),
    fdfs_only PMc -> mat_stable PMc -> a_live RT Σ E -> AINV_A E m -> ptr_atA E P ptr ->
    elem (ae_T E) (ae_S E) (ae_sn E) ck_any d i j -> 0 <= i -> j <= ae_n E - 1 ->
    root_preA RT E Σ m q out node i jo (elem_needA d) (elem_costA d (zlength ptr)) d -> frm0 fc ->
    cps_f (ASTA RT Σ PMc (eq (lvl_entry ATP_ELEM_A ra q gp t0 t1 t2 s0 s1 out node P (zlength ptr)
                                      a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)))
      (lvl_postA RT E Σ PMc ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 out m (elem_costA d (zlength ptr))).

Lemma fobj_src : forall (RT : rt_sig) (Σ : rts RT) (m : mem) (sp : word) (lo a n : Z),
  fobj RT Σ m a n -> 0 <= a -> a + n <= lo -> 0 < n -> checked_src RT Σ m sp lo a n.
Proof.
  intros RT Σ m sp lo a n (A8 & N0 & (f & k & INF & FL & FH) & HB) A0 ALO NP.
  pose proof (acc_zero_run asegs m a _ A8 A0 HB) as AC. rewrite Z2Nat.id in AC by (Z.div_mod_to_equations; lia).
  split; [| left; exact ALO]. intros _. split.
  - apply (acc_sub asegs m a (8 * ((n + 7) / 8))); [exact AC| lia| Z.div_mod_to_equations; lia].
  - right; left. exists f, k. split; [exact INF|]. split; [exact FL|]. Z.div_mod_to_equations; lia.
Qed.

Section RootLevel.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RC : rt_contracts RT.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.
  Hypothesis HOBJ : forall d', d = S d' -> atp_obj_cpsA RT E d'.
  Hypothesis HARR : forall d', d = S d' -> atp_arr_cpsA RT E d'.

  Local Ltac ul := unfold obj_needA, arr_needA, elem_needA, ATP_LEAFB, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

  Theorem atp_rootA : atp_root_cpsA RT E d.
  Proof using AF RC OK HOBJ HARR.
    intros Σ PMc ptr i j q out node P ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m jo
      FDO MST LV AI PAT EL I0 JN PRE FRM.
    destruct PRE as (NODE & N0 & NB & N8 & OUT & QO & OB & O8 & NO & ART0 & MI0 & ST0 & LOR & Q16 & FRB & CRB & LVB).
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ PTRR P0' (D8 & DF & DL & DS & DT) LOW0 [HL HT]].
    pose proof LV as (_ & _ & _ & _ & LWIN). pose proof (af_sp0_range RT AF Σ m ART0) as SP0R0.
    assert (ELM64 : ae_lo E + 65600 <= q) by ul.
    assert (FPW : fp_client RT Σ (ae_lo E) (elem_W q out)) by (apply fp_client_stack2; ul).
    apply (atp_elem_core RT AF RC E OK d HOBJ HARR Σ PMc ptr i j q out node P ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m jo
             FDO MST LV AI PAT EL I0 JN NODE N0 ltac:(lia) (or_intror NB) OUT QO OB O8 ltac:(left; lia) ART0 MI0 ST0 LOR Q16 FRB CRB LVB); [| | exact FRM].
    - intros m' MU WM. exact (fobj_shz RT AF Σ m' node 16 (lvl_art_munch RT AF E Σ _ m m' ART0 LV FPW MU WM) (NO m' MU WM)).
    - intros m' MU WM. apply (fobj_src RT Σ m' _ (ae_lo E) node 16 (NO m' MU WM)); lia.
  Qed.
End RootLevel.

Section RootClosed.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RC2 : rt_contracts2 RT.
  Theorem atp_root_levelA : forall E, aenvA_ok E -> forall d, atp_root_cpsA RT E d.
  Proof using AF RC2.
    intros E OK d. apply (atp_rootA RT AF (rc2_rt RT RC2) E OK d); intros d' ->.
    - exact (atp_obj_levelA RT AF RC2 (esc_okA_closed RT AF RC2) E OK d').
    - exact (atp_arr_levelA RT AF RC2 (esc_okA_closed RT AF RC2) E OK d').
  Qed.
End RootClosed.
