(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-11: made from SymDrive.v and SymDriveX.v: the R-typed declarations restated over the budget carrier, with twin modules imported last; SymDriveX's block tactic run_block_with restated over rzb_run. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg SymExec Frame RefMemcpyLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SymExec2 SymExec2Sound SymRun.
Import ListNotations.
Import SX2.
Import SX2S.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SymDrive SymDriveX.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.BudgetWit Require Import Rzb.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope bv_scope.
Section FPW_1.
Context {fx : PropExec.FPState}.
Section Drive.
Variable segs : list Segment.
Theorem rzb_run : forall fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
                         E M rom R model T,
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  carry (s_log ss') kn [] = (kn', scs2, hs2) ->
  regs_ok E sr R -> know_ok segs E M kn ->
  scs_denot segs M E scs -> scs_denot segs M E scs2 ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall R' M', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
     M' = mem_denot E M (s_log ss') ->
     Rzb.rzb segs (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) M' rom) model) T) ->
  Rzb.rzb segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) T.
Proof.
  intros fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T
         Hex Hc HR HK Hsc Hsc2 Hh Hlazy Hcont.
  destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
    as (R' & HR' & Hlf & Hms).
  eapply Rzb.rzb_msteps; [exact Hh | exact Hlazy | exact Hms |].
  apply (Hcont R' _ HR'); [|reflexivity].
  eapply carry_after; eassumption.
Qed.
End Drive.
End FPW_1.

(** SymDriveX's [run_block_with] and [run_block_gen], over [rzb] and
    [rzb_run]: the same symbolic run of one basic block, its result checked
    by [vm_compute], applied to an [rzb] goal. *)
Ltac run_block_with_b HR HK fuel stops scr NX keep :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- Rzb.rzb _ (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) ?T =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (SS ?pc' ?sr' ?log' ?knx ?nx', ?scs, ?scr') =>
          let c := eval vm_compute in (carry log' kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            sx_find_def sr ident:(SRH) ltac:(fun SRv =>
            sx_find_def kn ident:(KNH) ltac:(fun KNv =>
            sx_find_def sr' ident:(SRH) ltac:(fun SRv' =>
            sx_find_def log' ident:(LOGH) ltac:(fun LOGv =>
            sx_find_def knx ident:(KNH) ltac:(fun KNx =>
            sx_find_def kn' ident:(KNH) ltac:(fun KNv' =>
            eapply (rzb_run segs fuel stops scr pc SRv KNv NX (SS pc' SRv' LOGv KNx nx') scs scr' KNv' scs2 hs2 E M rom R model T);
            [ vm_cast_no_check (@eq_refl _ (SS pc' SRv' LOGv KNx nx', scs, scr'))
            | vm_cast_no_check (@eq_refl _ (KNv', scs2, hs2))
            | exact HR | exact HK
            | split_foralls
            | split_foralls
            | try reflexivity; try assumption
            | try reflexivity; try assumption
            | clear HR HK;
              let R' := fresh "R" in let M' := fresh "M" in let EQM := fresh "EQM" in
              intros R' M' HR HK EQM; cbn [s_pc s_regs s_log] in HR, EQM |- *;
              change (regs_ok E sr' R') in HR; change (know_ok segs E M' kn') in HK;
              change (M' = mem_denot E M log') in EQM;
              try clear LOGv; try clear KNx; try clear KNv; try clear SRv;
              lazymatch keep with
              | true => idtac
              | false => clear EQM; try clear R; try clear M;
                         try rename R' into R; try rename M' into M
              end ]))))))
          end
        end
      end
    end
  end.

Tactic Notation "run_block_gen_b" constr(fuel) constr(stops) constr(scr) constr(NX) constr(keep) :=
  match goal with
  | HR : regs_ok _ _ _, HK : know_ok _ _ _ _ |- _ => run_block_with_b HR HK fuel stops scr NX keep
  end.
