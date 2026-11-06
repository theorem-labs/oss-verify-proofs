(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg MmapSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive MemSplit RefMemcpyLib SymDriveX PerfNats.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Section WFP. Context {FP : PropExec.FPState}.
Theorem rz_run2 : forall segs fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T,
  (let r := sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] in (r, carry (s_log (fst (fst r))) kn []))
    = ((ss', scs, scr'), (kn', scs2, hs2)) ->
  regs_ok E sr R -> know_ok segs E M kn ->
  scs_denot segs M E scs -> scs_denot segs M E scs2 ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall R' M', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
     M' = mem_denot E M (s_log ss') ->
     realizes segs (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) M' rom) model) T) ->
  realizes segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) T.
Proof.
  intros segs fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T H.
  cbv zeta in H. injection H as H1 H2. rewrite H1 in H2. cbn [fst] in H2.
  exact (rz_run segs fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T H1 H2).
Qed.
End WFP.

Ltac run_block_with_bz HR HK fuel stops scr NX keep :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- realizes _ (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) ?T =>
        let fN := eval vm_compute in (N.of_nat fuel) in
        let fuelB := constr:(N.to_nat fN) in
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
          let c := eval vm_compute in (carry (s_log ss') kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            let pc' := eval cbv [s_pc] in (s_pc ss') in
            let sr' := eval cbv [s_regs] in (s_regs ss') in
            let log' := eval cbv [s_log] in (s_log ss') in
            let SR0 := fresh "SR0" in let KN0 := fresh "KN0" in let SSX := fresh "SSX" in let KNX := fresh "KNX" in let KNB := fresh "KNB" in
            (* [comment removed for export] *)
            binarize_k constr:((sr, kn, ss', kn')) ltac:(fun T =>
              lazymatch T with (?srB, ?knB, ?ssB, ?knxB) =>
                pose (SR0 := srB); pose (KN0 := knB);
                lazymatch ssB with
                | SS ?pcx ?srx ?logx _ ?nxx => pose (SSX := SS pcx srx logx KN0 nxx)
                end;
                pose (KNB := knxB); pose (KNX := kn') end);   (* [comment removed for export] *)
            eapply (rz_run2 segs fuelB stops scr pc SR0 KN0 NX SSX scs scr' KNB scs2 hs2 E M rom R model T);
            [ vm_cast_no_check (@eq_refl _ ((SSX, scs, scr'), (KNB, scs2, hs2)))
            | exact HR | exact HK
            | clear SR0 KN0 SSX KNB KNX; split_foralls
            | clear SR0 KN0 SSX KNB KNX; split_foralls
            | clear SR0 KN0 SSX KNB KNX; try reflexivity; try assumption
            | clear SR0 KN0 SSX KNB KNX; try reflexivity; try assumption
            | clear HR HK;
              let R' := fresh "R" in let M' := fresh "M" in let EQM := fresh "EQM" in
              intros R' M' HR HK EQM;
              change (regs_ok E sr' R') in HR;
              change (know_ok segs E M' KNX) in HK;
              change (M' = mem_denot E M log') in EQM;
              change (realizes segs (mkCfg (mkst R' (Z_to_bv 64 pc') M' rom) model) T);
              clear SR0 SSX KNB; clear KN0; (lazymatch kn with ?v => tryif is_var v then try clear v else idtac end);
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
