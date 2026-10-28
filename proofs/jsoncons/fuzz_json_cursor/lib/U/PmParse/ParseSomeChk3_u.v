(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums2_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSpecs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u ParseBridges2_u ParseBridges3_u ParseBridges4_u ParseSomeChk_u ParseSomeChk2_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import PSMC. Import PSM2.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module PSM3.

Definition geu_chk (cells : list kentry) (a b : expr) : bool := PB.has cells (KRange (EAlu Instr.ALU_SLTU a b) 0 0).
Definition is_none {A} (o : option A) : bool := match o with None => true | Some _ => false end.
Definition is_lit (o : option expr) (z : Z) : bool := match o with Some (ELit v) => Z.eqb v z | _ => false end.
Definition is_z (o : option Z) (z : Z) : bool := match o with Some v => Z.eqb v z | None => false end.
Definition nxg_of (c : CC.cutpoint) : nat := (CC.cp_nx c - APC.NCS - 5)%nat.
Definition a0v_of (c : CC.cutpoint) : nat := (CC.cp_nx c - APC.NCS + 4)%nat.
Definition exit_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      if Z.eqb pc RETPC then
        let cells := SR.ps_cells ps in
        (PB.exit_base_chk GT.NF RETPC c ps &&
         match kind_of i with
         | KPt => (ne_chk cells (EVar (nxg_of c)) 0 && (if cur_cut i then PB.has cells (KWord (SA Pb 200) 8 (EVar (a0v_of c))) else Nat.eqb (length (CC.cp_F c)) 1) && Nat.leb 70 (CC.cp_nx c)
                   && match CC.cp_F c with [_; (_, o1, _)] => Z.eqb o1 200 | _ => true end)%bool
         | kd =>
             match ldelta i c ps with
             | Some (pv, lv, pe, ce, d) =>
                 (is_none (d_sst d) && is_none (d_nst d) && negb (d_clr d) &&
                  match kd with
                  | KInv => (PB.has cells (KWord (SA Eb 0) 4 (ELit 0)) &&
                             ((Nat.eqb i 0 && rng_is cells (PB4.pv_st pv) 2 && is_lit (d_st d) 29 && is_z (d_more d) 0 && is_z (d_done d) 1 && (d_adv d =? 0))
                              || (negb (Nat.eqb i 0) && (in_loop i || Nat.eqb i I_L0) && is_none (d_st d) && is_none (d_more d) && is_none (d_done d) && (d_adv d =? 0) && (rng_is cells (PB4.pv_more pv) 0 || geu_chk cells (PB4.pv_wptr lv) WEND)
                                  && (foot2 c || let '(lo, hi) := rng_of cells (PB4.pv_st pv) in negb ((lo <=? 17) && (17 <=? hi))))))%bool
                  | KErr => (is_none (d_st d) && is_none (d_more d) && is_none (d_done d))%bool
                  | KSetEc => (is_none (d_st d) && (is_z (d_more d) 0 || (is_none (d_more d) && expr_eqb (PB4.pv_more pv) (ELit 0))) && is_none (d_done d))%bool
                  | _ => false
                  end)%bool
             | None => false
             end
         end)%bool
      else true
  | _ => true
  end.

Definition dead_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      if Z.eqb pc DEADPC then
        match kind_of i, ldelta i c ps with
        | KInv, Some (pv, lv, pe, ce, d) =>
            let cells := SR.ps_cells ps in let '(lo, hi) := rng_of cells (PB4.pv_st pv) in
            (rng_is cells (PB4.pv_more pv) 1 && (hi <=? 255) &&
             (forallb (fun s => negb (handledb s)) (zseq lo hi)
              || (PB.has cells (KRange (EAlu Instr.ALU_SLTU (ELit 27) (APC.eaddz (PB4.pv_st pv) (-1))) 1 1) && forallb (fun s => negb (handledb s) || ((1 <=? s) && (s <=? 28))) (zseq lo hi))))%bool
        | _, _ => false
        end
      else true
  | _ => true
  end.
End PSM3.
Lemma dead_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS PSM3.dead_chk = true.
Proof. vmc_refl. Qed.
Lemma exit_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS PSM3.exit_chk = true.
Proof. vmc_refl. Qed.
