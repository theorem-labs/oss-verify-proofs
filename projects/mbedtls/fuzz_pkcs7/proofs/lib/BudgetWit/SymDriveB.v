(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from BB/SymDrive.v's rz_run, BB/SymDriveX.v's run_block_with and run_block_gen, and P/P_mainleaf_openfail_tail.v's run_blk and run_blk_keep, over BudgetWit.Rzb.realizes; the tactics take a B suffix so that they cannot be confused with the released ones. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import SimInv ExitSim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StoreOk ShapeX MmapSim SymExec SymExec2 SymExec2Sound SymRun SymDrive MemSplit MemcpyLib.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import BBFrame SymDriveX.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require P_mainleaf_openfail_defs.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BudgetWit Require Import Rzb.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Section Drive.
Variable segs : list Segment.

#[using="Type"] Theorem rz_run : forall fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
                         E M rom R model T,
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  carry (s_log ss') kn [] = (kn', scs2, hs2) ->
  regs_ok E sr R -> know_ok segs E M kn ->
  scs_denot segs M E scs -> scs_denot segs M E scs2 ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall R' M', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
     M' = mem_denot E M (s_log ss') ->
     realizes segs (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) M' rom) model) T) ->
  realizes segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) T.
Proof.
  intros fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T
         Hex Hc HR HK Hsc Hsc2 Hh Hlazy Hcont.
  destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
    as (R' & HR' & Hlf & Hms).
  eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |].
  apply (Hcont R' _ HR'); [|reflexivity].
  eapply carry_after; eassumption.
Qed.

End Drive.

Ltac run_block_withB HR HK fuel stops scr NX keep :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- realizes _ (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) ?T =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
          let c := eval vm_compute in (carry (s_log ss') kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            eapply (rz_run segs fuel stops scr pc sr kn NX ss' scs scr' kn' scs2 hs2 E M rom R model T);
            [ vm_cast_no_check (@eq_refl _ (ss', scs, scr'))
            | vm_cast_no_check (@eq_refl _ (kn', scs2, hs2))
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
              end ]
          end
        end
      end
    end
  end.

Tactic Notation "run_block_genB" constr(fuel) constr(stops) constr(scr) constr(NX) constr(keep) :=
  match goal with
  | HR : regs_ok _ _ _, HK : know_ok _ _ _ _ |- _ => run_block_withB HR HK fuel stops scr NX keep
  end.

Tactic Notation "run_blkB" constr(scr) constr(NX) :=
  run_block_genB P_mainleaf_openfail_defs.FUEL P_mainleaf_openfail_defs.STOPS scr NX false.
Tactic Notation "run_blk_keepB" constr(scr) constr(NX) :=
  run_block_genB P_mainleaf_openfail_defs.FUEL P_mainleaf_openfail_defs.STOPS scr NX true.
