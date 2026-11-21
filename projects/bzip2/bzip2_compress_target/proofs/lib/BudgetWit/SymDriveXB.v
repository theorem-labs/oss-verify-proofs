(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from SymDriveX.v: the block-running tactic run_block_with restated over the budget carrier (rzb_run in place of rz_run), with twin modules imported last. *)

From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec CatSim SeqExec StoreOk SimInv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require CatSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ShapeAlg MmapSim SymExec SymExec2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun SymDrive MemSplit RefMemcpyLib.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SimInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim.ExitSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MemSplit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import SymDriveX.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.BudgetWit Require Import Rzb SymDriveB.

(** [SymDriveX.run_block_with] over [rzb]: the goal pattern is [rzb], and the
    lemma it applies is [SymDriveB.rzb_run].  The rest is the released text. *)
Ltac run_block_with_b HR HK fuel stops scr NX keep :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- Rzb.rzb _ (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) ?T =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
          let c := eval vm_compute in (carry (s_log ss') kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            eapply (SymDriveB.rzb_run segs fuel stops scr pc sr kn NX ss' scs scr' kn' scs2 hs2 E M rom R model T);
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

Tactic Notation "run_block_gen_b" constr(fuel) constr(stops) constr(scr) constr(NX) constr(keep) :=
  match goal with
  | HR : regs_ok _ _ _, HK : know_ok _ _ _ _ |- _ => run_block_with_b HR HK fuel stops scr NX keep
  end.
