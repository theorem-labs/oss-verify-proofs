(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BStrFun.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BsAtomics B_memset BllocWalkKit BW_DepotFrame BW_Leaves BW_InitCache.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BllocTacX.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

End HCW.

Ltac deadK K := first [ exfalso; apply K; reflexivity
                      | exfalso; revert K; vm_compute; discriminate
                      | exfalso; revert K; rewrite ?unsigned_lit by lia; lia ].

Section HCW2.
  Context {HCEIL : HeapCeil}.

Lemma max_count_facts : forall c, 1 <= c <= 31 -> 2 <= max_count c <= 16 /\ Z.even (max_count c) = true.
Proof.
  intros c Hc.
  assert (CASES : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16
                  \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30 \/ c = 31) by lia.
  clear Hc. repeat match type of CASES with _ \/ _ => destruct CASES as [EC|CASES] | _ => rename CASES into EC end.
  all: subst c; match goal with |- context [max_count ?x] => let v := eval vm_compute in (max_count x) in change (max_count x) with v end; split; [lia| reflexivity].
Qed.

Lemma refill_go : forall (ra sp gp tp t0 t1 t2 s1 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (CA P c : Z),
  1 <= c <= 31 -> 0 <= CA /\ CA + 2592 <= aceil ->
  evt asegs (fun ms' => ms' = MS (mkR (wz 0x97384) sp gp tp t0 t1 t2 (wz P) (wz (max_count c / 2)) (wz AINST) (wz (CA + 2560)) (wz c) (wz (P + 16)) (wz (max_count c / 2)) a5 a6 a7
                                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 0x97444) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (wz P) s1 (wz CA) (wz (max_count c)) (wz AINST) a3 (wz c) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x97364) fc None m (seg_rom asegs)).
Proof.
  intros until c. intros Hc CAR. unfold AHI_LO in CAR. acb.
  pose proof (max_count_facts c Hc) as [MCB MCE]. unfold wz, AINST.

  step.
  match goal with |- context [Z_to_bv 64 (bv_swrap 32 ?x)] => replace (Z_to_bv 64 (bv_swrap 32 x)) with (Z_to_bv 64 (max_count c / 2)) end.
  2:{ f_equal. rewrite (unsigned_lit (max_count c)) by lia. unfold bv_wrap. change (bv_modulus 32) with (2^32). rewrite (Z.mod_small (max_count c)) by lia.
      rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2. symmetry. apply swrap32_small. lia. }
  step. step. step. step. step. step. step.
  replace (CA + 2047 + 513) with (CA + 2560) by lia.
  apply evt_done. reflexivity.
Qed.

Definition refill_head_post (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (W : list (Z * Z)) (lo CA P c : Z) : machine_state -> Prop :=
  fun ms' => exists m' (j8 : list byte),
    ms' = MS (mkR (wz 0x97384) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz P) (wz (max_count c / 2)) (wz AINST) (wz (CA + 2560)) (wz c) (wz (P + 16)) (wz (max_count c / 2)) a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x97444) fc None m' (seg_rom asegs)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -32)
    /\ rw_cells asegs m' (bv_unsigned sp + -32) [CB 8 j8; C8 s1; C8 s0; C8 ra].

Section Head.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (cnt : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo CA c : Z).
  Let P := CA + PCLASS_SIZE * c.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 32 <= bv_unsigned sp.
  Hypothesis CR : 1 <= c <= 31.
  Hypothesis CAR : akobj CA 2592 /\ CA + 2592 <= aceil /\ CA mod 16 = 0.
  Hypothesis PC1 : rw_cells asegs m P [C4 cnt; C4 (wz (max_count c))].

  Let CAE : 4096 <= CA /\ CA + 2592 <= aceil. Proof. exact (akobj_env _ _ (proj1 CAR) ltac:(clear; lia)). Qed.
  Theorem refill_head :
    evt asegs (refill_head_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m [(bv_unsigned sp - 32, bv_unsigned sp)]%Z lo CA P c)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz CA) (wz P) (wz AINST) (wz c) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x97344) fc None m (seg_rom asegs)).
  Proof.
    unfold AHI_LO, PCLASS_SIZE in *. acb.
    pose proof (max_count_facts c CR) as [MCB MCE].
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold wz in *.

    step. carve_frame 32%nat ST. step. step. step. step. step. step. rewrite ?sx32_wz by (clear - MCB; try acb; lia).
    step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by (clear - MCB; try acb; lia). clear - MCB; try acb. lia. } clear K.
    eapply evt_cut. { eapply (refill_go _ _ gp tp); [exact CR|]. unfold AHI_LO. acb. clear - CAR; try acb. aunf; lia. }
    intros ms' ->. apply evt_done. unfold refill_head_post. do 2 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption| exact FR].
  Qed.
End Head.

Lemma icW_disjoint_high : forall CA A n, CA + 2576 <= A -> disjoint_from (icW CA) A n.
Proof. intros CA A n H. cbn. repeat split; lia. Qed.

Section HeadInit.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo CA c : Z).
  Let P := CA + PCLASS_SIZE * c.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 32 <= bv_unsigned sp.
  Hypothesis CR : 1 <= c <= 31.
  Hypothesis CAR : akobj CA 2592 /\ CA + 2592 <= aceil /\ CA mod 16 = 0.
  Hypothesis MC0 : rw_cells asegs m (P + 4) [C4 (wz 0)].
  Hypothesis FAM : forall c', 1 <= c' <= 31 -> exists mc cs, rw_cells asegs m (CA + 80 * c' + 4) [C4 mc] /\ rw_cells asegs m (CA + 80 * c' + 8) [C8 cs].

  Let CAE : 4096 <= CA /\ CA + 2592 <= aceil. Proof. exact (akobj_env _ _ (proj1 CAR) ltac:(clear; lia)). Qed.
  Theorem refill_head_init :
    evt asegs (fun ms' => (exists t3' t4' t5', refill_head_post ra sp gp tp (wz 16) (wz 17) (wz 512) s0 s1 (Z_to_bv 64 16) (wz 15) (wz 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6 F fc m
                             ((bv_unsigned sp - 32, bv_unsigned sp) :: icW CA)%Z lo CA P c ms')
                          /\ (forall c', 1 <= c' <= 31 -> rw_cells asegs (ms_mem ms') (CA + 80 * c' + 4) [C4 (wz (max_count c'))]
                                                      /\ rw_cells asegs (ms_mem ms') (CA + 80 * c' + 8) [C8 (wz (class_size c'))]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz CA) (wz P) (wz AINST) (wz c) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x97344) fc None m (seg_rom asegs)).
  Proof.
    unfold AHI_LO, PCLASS_SIZE in *. acb.
    pose proof (max_count_facts c CR) as [MCB MCE].
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold wz in *. replace (CA + 80 * c + 4) with (P + 4) in MC0 by (subst P; clear; lia).

    step. carve_frame 32%nat ST. step. step. step. step. step. step. rewrite ?sx32_wz by (clear; lia).
    step. if_cases K; zify_cond K. 2:{ deadK K. } clear K.

    do 9 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m0 end.
    assert (FAM0 : forall c', 1 <= c' <= 31 -> exists mc cs, rw_cells asegs m0 (CA + 80 * c' + 4) [C4 mc] /\ rw_cells asegs m0 (CA + 80 * c' + 8) [C8 cs]).
    { intros c' Hc'. destruct (FAM c' Hc') as (mc & cs & A & B). exists mc, cs. split.
      - eapply rw_cells_transport; [exact A| exact MU| exact WM|]. cbn. clear - Hc' CAR LO HI; try acb. aunf; lia.
      - eapply rw_cells_transport; [exact B| exact MU| exact WM|]. cbn. clear - Hc' CAR LO HI; try acb. aunf; lia. }
    clear FAM MC0.
    replace (Z_to_bv 64 (CA + 88)) with (Z_to_bv 64 (CA + 80 * 1 + 8)) by (f_equal; clear; lia).
    eapply evt_cut.
    { eapply (ic_loop _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 CA _ (Z.to_nat 31) 1 _ _ _ m0 eq_refl ltac:(hci; clear; lia) ltac:(hci; assumption) (munch_refl _ m0) (wmono_refl asegs m0)).
      - intros c' Hc'. exfalso. clear - Hc'; try acb. lia.
      - exact FAM0. }
    Unshelve. all: try (unfold AHI_LO; acb; clear - CAR; try acb; aunf; lia).
    cbv beta. intros ms' PO. destruct PO as (t3' & t4' & t5' & m1 & -> & MU1 & WM1 & MI1 & DONE).
    eapply (rw_cells_transport asegs (icW CA) m0 m1) in FR; [| exact MU1| exact WM1| apply icW_disjoint_high; clear - CAR LO HI; try acb; aunf; lia].
    eapply (stk_transport_disjoint asegs (icW CA) m0 m1) in ST; [| exact MU1| exact WM1| apply icW_disjoint_high; clear - CAR LO HI; try acb; aunf; lia].
    destruct (DONE c CR) as [MCc CSc]. replace (CA + 80 * c + 4) with (P + 4) in MCc by (subst P; clear; lia).
    unfold wz in MCc.

    step. rewrite ?sx32_wz by (clear - MCB; try acb; lia). step.
    eapply evt_cut. { eapply (refill_go _ _ gp tp); [exact CR|]. unfold AHI_LO. acb. clear - CAR; try acb. aunf; lia. }
    cbv beta. intros ms' ->. apply evt_done. split.
    - exists t3', t4', t5'. unfold refill_head_post. exists m1, (take 8 (take 16 (take 24 junk))).
      split; [reflexivity|]. split.
      { eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU1]].
        - intros x OUT. cbn in OUT |- *. clear - OUT; try acb. tauto.
        - intros x OUT. cbn in OUT |- *. clear - OUT; try acb. tauto. }
      split; [eapply wmono_trans; [exact WM| exact WM1]|]. split; [exact MI1|]. split; [exact ST| exact FR].
    - cbn [ms_mem]. unfold wz. exact DONE.
  Qed.
End HeadInit.

Section Back.
  Variables (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (cnt : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (j8 : list byte) (f1 f0 fra : word).
  Variables (lo P n : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo. Hypothesis HI : lo <= bv_unsigned sp. Hypothesis SPH : bv_unsigned sp + 32 < 2^64.
  Hypothesis FR : rw_cells asegs m (bv_unsigned sp) [CB 8 j8; C8 f1; C8 f0; C8 fra].
  Hypothesis PR : akobj P 80 /\ P + 80 <= aceil.
  Hypothesis NR : 0 <= n < 2^31.
  Hypothesis PC : rw_cells asegs m P [C4 cnt].

  Let PRE : 4096 <= P /\ P + 80 <= aceil. Proof. exact (akobj_env _ _ (proj1 PR) ltac:(clear; lia)). Qed.
  Theorem refill_back :
    evt asegs (fun ms' => exists m',
                 ms' = MS (mkR fra (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp t0 t1 t2 f0 f1 (wz 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc fra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp, bv_unsigned sp + 32); (P, P + 4)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp + 32)
                 /\ rw_cells asegs m' P [C4 (wz n)])
      (MS (mkR (wz 0x97384) sp gp tp t0 t1 t2 (wz P) (wz n) (wz 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x97384) fc None m (seg_rom asegs)).
  Proof.
    unfold AHI_LO in PR. acb.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof (munch_refl [(bv_unsigned sp, bv_unsigned sp + 32); (P, P + 4)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold wz in *.

    step. if_cases K; zify_cond K. { deadK K. } clear K.
    step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp + 32).
    apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
    lazymatch goal with H : rw_cells asegs _ P _ |- _ => exact H end.
  Qed.
End Back.

End HCW2.

