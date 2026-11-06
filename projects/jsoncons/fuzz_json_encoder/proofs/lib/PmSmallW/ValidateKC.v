(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core PmLibDefs PmEncSpecs PmLibSpecsW PmRef RelLeaf.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutL5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseBridges ParseBridges2.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure SmallWin.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmallW Require Import SmallPtW ValidateKW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_validate_xsrc_T Cut_validate_xsrc.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module VKC.
Module G := Cut_validate_xsrc.
Module GT := Cut_validate_xsrc_T.
Definition delta_of (s : CC.subst) : option Z := find (fun d => expr_eqb (CC.slook s 32) (APC.eaddz VKW.JV (- d))) [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12].
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in
  if Nat.eqb i 0 then
    match t with
    | CC.TGoto j s => Nat.eqb j 1 && expr_eqb (CC.slook s 32) (EVar 11)
    | CC.TOther _ => match SP.reg_of ps 11 with Some e => expr_eqb e (EVar 11) | None => false end && PB.prove cells (KRange (EVar 11) 0 0)
    end
  else
    Nat.eqb i 1 && PB.has cells (KImg 65536 813152) &&
    match t with
    | CC.TGoto j s => Nat.eqb j 1 && match delta_of s with Some d => VKW.goto_chk cells d | None => false end
    | CC.TOther _ => match SP.reg_of ps 11 with Some (ELit c) => VKW.exit_chk cells c | _ => false end
    end%bool.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma nx_ok : CC.cps_all G.CPS (fun i c => Nat.leb (if Nat.eqb i 0 then 32 else 40) (CC.cp_nx c)) = true.
Proof. vm_compute. reflexivity. Qed.
End VKC.
