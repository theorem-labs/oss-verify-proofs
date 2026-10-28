(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics F_memset AllocWalkKit AW_DepotFrame AW_Leaves AW_InitCacheA.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocTacX.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Ltac deadK K := first [ exfalso; apply K; reflexivity
                      | exfalso; revert K; vm_compute; discriminate
                      | exfalso; revert K; rewrite ?unsigned_lit by lia; lia ].
(* [comment removed for export] *)
Ltac cbr := let K := fresh "K" in if_cases K; zify_cond K; first [ deadK K | clear K ].
(* [comment removed for export] *)
Ltac lits :=
  repeat match goal with
         | |- context [v_sltiu ?a ?b] => let v := eval vm_compute in (v_sltiu a b) in change (v_sltiu a b) with v
         | |- context [v_sltu ?a ?b] => let v := eval vm_compute in (v_sltu a b) in change (v_sltu a b) with v
         end;
  fold_closed_in_goal; zb_fold_lits.
(* [comment removed for export] *)
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
(* [comment removed for export] *)
Ltac brz c lo hi b cl :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?cond then _ else _) _ _ _ _) =>
    replace cond with b by (symmetry; cl; zc c lo hi; vm_compute; reflexivity); cbv iota end.

Section TripB.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp s0 s1 a0 a2 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (mc0 : word) (cs0 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (A c : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis AR : akobj A 96 /\ A + 96 <= aceil /\ A mod 8 = 0.
  Hypothesis MC : rw_cells asegs m (A + 4) [C4 mc0].
  Hypothesis CS : rw_cells asegs m (A + 8) [C8 cs0].

  Let ARE : 4096 <= A /\ A + 96 <= aceil. Proof. exact (akobj_env _ _ (proj1 AR) ltac:(clear; lia)). Qed.   (* [comment removed for export] *)
  Lemma ic_trip_hi : 17 <= c <= 31 ->
    evt asegs (ic_trip_post ra sp gp tp (wz 16) (wz 17) (wz 512) s0 s1 a0 a2 a4 (wz 15) (wz 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc m A c)
      (MS (mkR ra sp gp tp (wz 16) (wz 17) (wz 512) s0 s1 a0 (wz (A + 8)) a2 (wz (32 * c)) a4 (Z_to_bv 64 (c - 16)) (wz 15) (wz 1024)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19be50) fc None m (seg_rom asegs)).
  Proof.
    intros Hc. unfold AHI_LO in AR. acb.
    pose proof (munch_refl [(A + 4, A + 16)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold wz in *.
    (* [comment removed for export] *)
    destruct (Z.eq_dec c 31) as [EC|NE].
    - clear Hc. subst c; lits; run_to 0x19be2c;
         lazymatch goal with |- evt _ (ic_trip_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?cc) _ =>
           let tgt := eval vm_compute in (if cc =? 31 then 0x19bea4 else 0x19be50) in run_to tgt end;
         replace (A + 8 + 80) with (A + 88) by (clear; lia);
         apply evt_done; unfold ic_trip_post; do 4 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; assumption.
    - assert (Hc' : 17 <= c <= 30) by (clear - Hc NE; lia). clear Hc NE.
      (* [comment removed for export] *)
      step. brz c 17 30 false ltac:(clear - Hc').
      step. step. step. brz c 17 30 false ltac:(clear - Hc').
      (* [comment removed for export] *)
      do 7 step. step. step. step. brz c 17 30 true ltac:(clear - Hc').
      (* [comment removed for export] *)
      step. step. step. step. step. step. step. step. step.
      brz c 17 30 false ltac:(clear - Hc').
      match type of MC with rw_cells _ _ _ [Cells.C4 ?v] =>
        replace v with (Z_to_bv 64 (max_count c)) in MC by (clear - Hc'; zc c 17 30; apply bv_eq; vm_compute; reflexivity) end.
      match type of CS with rw_cells _ _ _ [Cells.C8 ?v] =>
        replace v with (Z_to_bv 64 (class_size c)) in CS by (clear - Hc'; zc c 17 30; apply bv_eq; vm_compute; reflexivity) end.
      replace (A + 8 + 80) with (A + 88) by (clear; lia). replace (c - 16 + 1) with (c - 15) by (clear; lia).
      apply evt_done; unfold ic_trip_post. replace (c =? 31) with false by (symmetry; apply Z.eqb_neq; clear - Hc'; lia). cbv iota. do 4 eexists;
        split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; assumption.
  Qed.
End TripB.

