(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg MmapSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive MemSplit RefMemcpyLib SymDriveX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac run_block_with_kn HR HK fuel stops scr NX keep :=
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
            let KN := fresh "KN" in
            pose (KN := kn');
            eapply (rz_run segs fuel stops scr pc sr kn NX ss' scs scr' KN scs2 hs2 E M rom R model T);
            [ vm_cast_no_check (@eq_refl _ (ss', scs, scr'))
            | vm_cast_no_check (@eq_refl _ (KN, scs2, hs2))
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

Ltac run_block_gen_kn fuel stops scr NX keep :=
  match goal with
  | HR : regs_ok _ _ _, HK : know_ok _ _ _ _ |- _ => run_block_with_kn HR HK fuel stops scr NX keep
  end.
