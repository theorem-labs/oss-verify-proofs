(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Common/CliDriver/SymDriveX.v: the block tactic run_block_gen over the budget carrier rzb (run_block_gen_b, applying SymDriveB.rzb_run). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg MmapSim SymExec MemSplit RefMemcpyLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import SymExec2 SymExec2Sound SymRun SymDrive.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import SymDriveX.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.BudgetWit Require Import Rzb SymDriveB.

Ltac p6_run_b HR HK fuel stops scr NX keep segs E sr R M kn pc rom model T ssn scs scr' knn scs2 hs2 :=
  eapply (rzb_run segs fuel stops scr pc sr kn NX ssn scs scr' knn scs2 hs2 E M rom R model T);
  [ vm_cast_no_check (@eq_refl _ (ssn, scs, scr'))
  | vm_cast_no_check (@eq_refl _ (knn, scs2, hs2))
  | exact HR | exact HK
  | split_foralls
  | split_foralls
  | try reflexivity; try assumption
  | try reflexivity; try assumption
  | clear HR HK;
    let R' := fresh "R" in let M' := fresh "M" in let EQM := fresh "EQM" in
    intros R' M' HR HK EQM; cbn [s_pc s_regs s_log] in HR, EQM |- *;
    lazymatch keep with
    | true => idtac
    | false => clear EQM; try clear R; try clear M;
               try rename R' into R; try rename M' into M
    end;
    tryif is_var kn then try clear kn else idtac;
    tryif is_var sr then try clear sr else idtac ].

Ltac run_block_with_b HR HK fuel stops scr NX keep :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- rzb _ (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) ?T =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (SS ?pc' ?sr' ?log' ?kn0 ?nx', ?scs, ?scr') =>
          let c := eval vm_compute in (carry log' kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            let SRn := fresh "P6_SR" in
            pose (SRn := sr');
            let ssn := constr:(SS pc' SRn log' kn nx') in
            let knb := p6_body kn in
            tryif constr_eq knb kn'
            then p6_run_b HR HK fuel stops scr NX keep segs E sr R M kn pc rom model T ssn scs scr' kn scs2 hs2
            else (let KNn := fresh "P6_KN" in
                  pose (KNn := kn');
                  p6_run_b HR HK fuel stops scr NX keep segs E sr R M kn pc rom model T ssn scs scr' KNn scs2 hs2)
          end
        end
      end
    end
  end.

Tactic Notation "run_block_gen_b" constr(fuel) constr(stops) constr(scr) constr(NX) constr(keep) :=
  match goal with
  | HR : regs_ok _ _ _, HK : know_ok _ _ _ _ |- _ => run_block_with_b HR HK fuel stops scr NX keep
  end.
