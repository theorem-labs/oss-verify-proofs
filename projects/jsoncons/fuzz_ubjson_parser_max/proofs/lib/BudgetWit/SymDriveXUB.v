(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from SymDriveX.v and Ju0OpenFail_tail.v: the block-running tactic run_block_with and the run_blk notations restated over the budget carrier (rz_run_b in place of rz_run). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg DivergeSim SpinAlg SpinAlgX MmapSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive MemSplit RefMemcpyLib SymDriveX.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Ju0OpenFail_defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BudgetWit Require Import SpinAlgB SymDriveB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

(** [SymDriveX.run_block_with] over [rzb]: the goal pattern is [rzb], and the
    lemma it applies is [SymDriveB.rz_run_b].  The rest is the released text. *)
Ltac run_block_with_ub HR HK fuel stops scr NX keep :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- SpinAlgB.rzb _ ?scfg (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) ?T =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
          let c := eval vm_compute in (carry (s_log ss') kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            eapply (SymDriveB.rz_run_b segs scfg fuel stops scr pc sr kn NX ss' scs scr' kn' scs2 hs2 E M rom R model T);
            [ vm_compute; reflexivity
            | vm_compute; reflexivity
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

Tactic Notation "run_block_gen_ub" constr(fuel) constr(stops) constr(scr) constr(NX) constr(keep) :=
  match goal with
  | HR : regs_ok _ _ _, HK : know_ok _ _ _ _ |- _ => run_block_with_ub HR HK fuel stops scr NX keep
  end.

(** [Ju0OpenFail_tail]'s [run_blk] and [run_blk_keep], over [rzb]. *)
Tactic Notation "run_blk_ub" constr(scr) constr(NX) :=
  run_block_gen_ub Ju0OpenFail_defs.FUEL Ju0OpenFail_defs.STOPS scr NX false.
Tactic Notation "run_blk_keep_ub" constr(scr) constr(NX) :=
  run_block_gen_ub Ju0OpenFail_defs.FUEL Ju0OpenFail_defs.STOPS scr NX true.
