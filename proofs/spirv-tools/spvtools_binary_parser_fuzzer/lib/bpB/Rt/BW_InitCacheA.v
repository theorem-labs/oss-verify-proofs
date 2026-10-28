(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BStrFun.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BsAtomics B_memset BllocWalkKit BW_DepotFrame BW_Leaves.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

End HCW.

Ltac deadK K := first [ exfalso; apply K; reflexivity
                      | exfalso; revert K; vm_compute; discriminate
                      | exfalso; revert K; rewrite ?unsigned_lit by lia; lia ].

Ltac cbr := let K := fresh "K" in if_cases K; zify_cond K; first [ deadK K | clear K ].

Ltac lits :=
  repeat match goal with
         | |- context [v_sltiu ?a ?b] => let v := eval vm_compute in (v_sltiu a b) in change (v_sltiu a b) with v
         | |- context [v_sltu ?a ?b] => let v := eval vm_compute in (v_sltu a b) in change (v_sltu a b) with v
         end;
  fold_closed_in_goal; zb_fold_lits.

Ltac run_to tgt :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 tgt) _ _ _ _) => fail
          | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; fix_lit_store; lits; try cbr
          end).

Ltac zc c lo hi :=
  let b := eval vm_compute in (Z.ltb hi lo) in
  lazymatch b with
  | true => exfalso; lia
  | false => let lo' := eval vm_compute in (lo + 1)%Z in destruct (Z.eq_dec c lo) as [-> | ?]; [| zc c lo' hi]
  end.

Ltac brz c lo hi b cl :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?cond then _ else _) _ _ _ _) =>
    replace cond with b by (symmetry; cl; zc c lo hi; vm_compute; reflexivity); cbv iota end.

Section HCW2.
  Context {HCEIL : HeapCeil}.

Definition ic_trip_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (A c : Z) : machine_state -> Prop :=
  fun ms' => exists (t3 t4 t5 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz (A + 88)) a2 (wz (32 * c + 32)) a4 (Z_to_bv 64 (c - 15)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 (if c =? 31 then 0x9743c else 0x973e8)) fc None m' (seg_rom asegs)
    /\ munch [(A + 4, A + 16)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (A + 4) [C4 (wz (max_count c))] /\ rw_cells asegs m' (A + 8) [C8 (wz (class_size c))].

Section TripA.
  Variables (ra sp gp tp s0 s1 a0 a2 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (mc0 : word) (cs0 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (A c : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis AR : akobj A 96 /\ A + 96 <= aceil /\ A mod 8 = 0.
  Hypothesis MC : rw_cells asegs m (A + 4) [C4 mc0].
  Hypothesis CS : rw_cells asegs m (A + 8) [C8 cs0].

  Let ARE : 4096 <= A /\ A + 96 <= aceil. Proof. exact (akobj_env _ _ (proj1 AR) ltac:(clear; lia)). Qed.
  Lemma ic_trip_lo : 1 <= c <= 16 ->
    evt asegs (ic_trip_post ra sp gp tp (wz 16) (wz 17) (wz 512) s0 s1 a0 a2 a4 (wz 15) (wz 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc m A c)
      (MS (mkR ra sp gp tp (wz 16) (wz 17) (wz 512) s0 s1 a0 (wz (A + 8)) a2 (wz (32 * c)) a4 (Z_to_bv 64 (c - 16)) (wz 15) (wz 1024)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x973e8) fc None m (seg_rom asegs)).
  Proof.
    intros Hc. unfold AHI_LO in AR. acb.
    pose proof (munch_refl [(A + 4, A + 16)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold wz in *.

    step. if_cases K; zify_cond K. { exfalso. clear - K Hc. zc c 1 16; revert K; vm_compute; discriminate. } clear K.

    step. step. step. if_cases K; zify_cond K. 2:{ exfalso. clear - K Hc. zc c 1 16; revert K; vm_compute; intros K; apply K; reflexivity. } clear K.

    step. step. step.
    destruct (Z.le_gt_cases c 4) as [C4|C5].
    -
      brz c 1 4 false ltac:(clear - Hc C4). step. step.

      step. step. step. step. step. step. step. step. step.
      brz c 1 4 false ltac:(clear - Hc C4).
      match type of MC with rw_cells _ _ _ [BCells.C4 ?v] =>
        replace v with (Z_to_bv 64 (max_count c)) in MC by (clear - Hc C4; zc c 1 4; apply bv_eq; vm_compute; reflexivity) end.
      match type of CS with rw_cells _ _ _ [BCells.C8 ?v] =>
        replace v with (Z_to_bv 64 (class_size c)) in CS by (clear - Hc C4; zc c 1 4; apply bv_eq; vm_compute; reflexivity) end.
      replace (A + 8 + 80) with (A + 88) by (clear; lia). replace (c - 16 + 1) with (c - 15) by (clear; lia).
      apply evt_done; unfold ic_trip_post. replace (c =? 31) with false by (symmetry; apply Z.eqb_neq; clear - Hc; lia). cbv iota. do 4 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; assumption.
    -
      brz c 5 16 true ltac:(clear - Hc C5).
      step. step. step. step. step. step. step. step. step.
      brz c 5 16 false ltac:(clear - Hc C5).
      match type of MC with rw_cells _ _ _ [BCells.C4 ?v] =>
        replace v with (Z_to_bv 64 (max_count c)) in MC by (clear - Hc C5; zc c 5 16; apply bv_eq; vm_compute; reflexivity) end.
      match type of CS with rw_cells _ _ _ [BCells.C8 ?v] =>
        replace v with (Z_to_bv 64 (class_size c)) in CS by (clear - Hc C5; zc c 5 16; apply bv_eq; vm_compute; reflexivity) end.
      replace (A + 8 + 80) with (A + 88) by (clear; lia). replace (c - 16 + 1) with (c - 15) by (clear; lia).
      apply evt_done; unfold ic_trip_post. replace (c =? 31) with false by (symmetry; apply Z.eqb_neq; clear - Hc; lia). cbv iota. do 4 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; assumption.
  Qed.
End TripA.

End HCW2.

