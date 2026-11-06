(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core Pm10PlanKit PmLibDefs PmLibSpecs PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm10CutKit CutHeap2 CutL5 CutAutoX.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseSums ParseSums2 ParseSomeKn ParseSpecs ParseProve ParseBridges ParseBridges2 ParseBridges3 ParseBridges4 ParseSomeChk ParseSomeChk2 ParseSomeChk3 ParseSomeA ParseSomeChk4 ParseSomeChk5 ParseSomeChk6.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import PSMC. Import PSM2. Import PSM3.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module PSMV.
Definition vis_leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      if (Z.eqb pc VNULL || Z.eqb pc VBOOL)%bool then
        match CH2.ret_of G.RETS i k with
        | Some j =>
            match kind_of i, kind_of j, PSM5.rview i c ps j (CC.cp_nx (cutn j) - APC.NCS)%nat with
            | KInv, KVis, Some (pv, lv, pe, ce, d) =>
                (PSM5.same_state d && rng_is (SR.ps_cells ps) (PB4.pv_more pv) 1 && rng_in (SR.ps_cells ps) (PB4.pv_st pv) 18 27
                 && CH2.blocks_eqb (nth j G.BLS []) (nth i G.BLS [])
                 && (if Z.eqb pc VBOOL then match nth 11 (CA.ps_reglist ps) (ELit 0) with ELit x => ((x =? 0) || (x =? 1))%bool | _ => false end else true))%bool
            | _, _, _ => false
            end
        | None => false
        end
      else true
  | _ => true
  end.
End PSMV.
Lemma vis_leaf_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS PSMV.vis_leaf_chk = true.
Proof. vmc_refl. Qed.
