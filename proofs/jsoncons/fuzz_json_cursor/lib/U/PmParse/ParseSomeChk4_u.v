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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums2_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSpecs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u ParseBridges2_u ParseBridges3_u ParseBridges4_u ParseSomeChk_u ParseSomeChk2_u ParseSomeChk3_u ParseSomeA_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import PSMC. Import PSM2. Import PSM3.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module PSM4.

Definition CURJ : expr := APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 49).

Definition MEXP (z0 : Z) : expr := APC.eaddz (APC.eadd (APC.escale 64 (EVar 49)) (APC.escale 8 (EVar 50))) z0.
Definition lit_of (e : expr) : option Z := match e with ELit z => Some z | _ => None end.
Definition meas_cls (c : CC.cutpoint) : option (Z + Z) :=
  match lit_of (CC.cp_meas c) with
  | Some z => if ((0 <=? z) && (z <? 4611686018427387904))%bool then Some (inl z) else None
  | None => match find (fun z0 => expr_eqb (CC.cp_meas c) (MEXP z0)) [5; 6; 7; 8; 9] with
         | Some z0 => if ((PB.has (CC.cp_know c) (KRange (EVar 49) 0 16384) || PB.has (CC.cp_know c) (KRange (EVar 49) 1 16384))
                          && PB.has (CC.cp_know c) (KRange (APC.esub (EVar 33) (EVar 49)) 0 16384) && PB.has (CC.cp_know c) (KRange (EVar 50) 0 3))%bool then Some (inr z0) else None
         | None => None
         end
  end.

Definition d0_of (pv : PB4.pvals2) : option Z := if expr_eqb (PB4.pv_wptr pv) CURJ then Some 0 else if expr_eqb (PB4.pv_wptr pv) (APC.eaddz CURJ 1) then Some 1 else None.

Definition nums_chk (cells : list kentry) (lv : PB4.pvals2) (ce : expr) : bool :=
  (rng_in cells (PB4.pv_level lv) 0 1025 && rng_in cells (PB4.pv_st lv) 0 255 && rng_in cells (PB4.pv_sst lv) 0 255 && rng_in cells (PB4.pv_nst lv) 0 255
   && rng_in cells (PB4.pv_size lv) 0 67108863 && rng_in cells ce 264 134217728)%bool.

Definition reH_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      if Z.eqb pc HPC then
        let cells := SR.ps_cells ps in
        match kind_of i, ldelta i c ps, meas_cls c with
        | KInv, Some (pv, lv, pe, ce, d), Some cls =>
            ((Nat.eqb i I_L0 || Nat.eqb i I_L) && Z.eqb (SR.ps_pc ps) pc && CH2.all_regs_chk ps && PB.has cells (KWord (SA Eb 0) 4 (ELit 0))
             && is_none (d_st d) && is_none (d_sst d) && is_none (d_nst d) && is_none (d_more d) && is_none (d_done d) && negb (d_clr d) && (d_adv d =? 0)
             && nums_chk cells lv ce && lo_ge cells (EVar 49) 1 && expr_eqb (nth 11 (CA.ps_reglist ps) (ELit 0)) (PB4.pv_wptr lv) && foot2 c
             && expr_eqb (PB4.pv_wptr pv) CURJ && PB.has (CC.cp_know c) (KRange (APC.esub (EVar 33) (EVar 49)) 0 16384) && PB.has (CC.cp_know c) (KRange (EVar 49) 0 16384)
             && match cls with inl z => Z.eqb z 1073741824 | inr z0 => Z.eqb z0 9 end)%bool
        | _, _, _ => false
        end
      else true
  | _ => true
  end.

Definition reL_common (c : CC.cutpoint) (ps : SR.post_spec) (pc : Z) (lv : PB4.pvals2) (ce : expr) : bool :=
  (Z.eqb (SR.ps_pc ps) pc && CH2.all_regs_chk ps && PB.has (SR.ps_cells ps) (KWord (SA Eb 0) 4 (ELit 0)) && nums_chk (SR.ps_cells ps) lv ce)%bool.
Definition reAcc_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      if (Z.eqb pc LPC && match kind_of i with KInv => true | _ => false end)%bool then
        let cells := SR.ps_cells ps in
        match ldelta i c ps, meas_cls c with
        | Some (pv, lv, pe, ce, d), Some (inr z0) =>
            (reL_common c ps pc lv ce && in_loop i && is_lit (d_st d) 29 && is_z (d_more d) 0 && is_z (d_done d) 1 && is_none (d_sst d) && is_none (d_nst d) && negb (d_clr d) && (d_adv d =? 0)
             && rng_is cells (PB4.pv_st pv) 2 && rng_is cells (PB4.pv_more pv) 1 && expr_eqb (PB4.pv_wptr pv) CURJ && (z0 =? 8) && (Nat.eqb i I_HLO || Nat.eqb i I_HHI || Nat.eqb i I_HN))%bool
        | _, _ => false
        end
      else true
  | _ => true
  end.

Definition ghost1 (c : CC.cutpoint) : nat := (CC.cp_nx c - APC.NCS - 1)%nat.
Definition rePop_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      if ((Z.eqb pc LPC || Z.eqb pc L0PC) && match kind_of i with KPop => true | _ => false end)%bool then
        let cells := SR.ps_cells ps in
        match ldelta i c ps, meas_cls c with
        | Some (pv, lv, pe, ce, d), Some cls =>
            let '(lo, hi) := rng_of cells (PB4.pv_st pv) in
            (reL_common c ps pc lv ce && match d_st d with Some (EVar v) => Nat.eqb v (ghost1 c) | _ => false end && Nat.ltb (ghost1 c) (CC.cp_nx c)
             && is_none (d_more d) && is_none (d_done d) && is_none (d_sst d) && is_none (d_nst d) && negb (d_clr d)
             && rng_is cells (PB4.pv_more pv) 1 && forallb ccrb (zseq lo hi) && (hi <=? 255)
             && match cls with
                | inr z0 => (Z.eqb pc LPC && in_loop i && (5 <=? z0) && match d0_of pv with Some d0 => (1 <=? d0 + d_adv d) || forallb (fun s => (s =? 4) || (s =? 28)) (zseq lo hi) | None => false end)%bool
                | inl z => (Z.eqb pc L0PC && (1073741824 <? z) && expr_eqb (PB4.pv_wptr pv) SEG && (d_adv d =? 0) && rng_is cells (EVar 42) 28 && negb (in_loop i))%bool
                end)%bool
        | _, _ => false
        end
      else true
  | _ => true
  end.
Definition reVec_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      if (Z.eqb pc LPC && match kind_of i with KVec => true | _ => false end)%bool then
        let cells := SR.ps_cells ps in
        match ldelta i c ps, meas_cls c, CAX.cell_at (CC.cp_know c) (EVar 2) (-120) 1 with
        | Some (pv, lv, pe, ce, d), Some (inr z0), Some (ELit x) =>
            (reL_common c ps pc lv ce && in_loop i && (5 <=? z0) && is_none (d_more d) && is_none (d_done d) && is_none (d_sst d) && is_none (d_nst d) && negb (d_clr d)
             && rng_is cells (PB4.pv_more pv) 1 && rng_is cells (PB4.pv_st pv) x
             && ((is_lit (d_st d) 3 && existsb (Z.eqb x) [1; 7; 9; 10; 11; 12; 13]) || (is_lit (d_st d) 28 && (x =? 5)))
             && match d0_of pv with Some d0 => (1 <=? d0 + d_adv d) | None => false end)%bool
        | _, _, _ => false
        end
      else true
  | _ => true
  end.

Definition rePt_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      if ((Z.eqb pc LPC || Z.eqb pc L2PC || Z.eqb pc L0PC) && match kind_of i with KPt => true | _ => false end)%bool then
        let cells := SR.ps_cells ps in
        (Z.eqb (SR.ps_pc ps) pc && CH2.all_regs_chk ps && (rng_is cells (EVar (nxg_of c)) 0 || PSI.skip_cut i)
         && (if cur_cut i then PB.has cells (KWord (SA Pb 200) 8 (EVar (a0v_of c))) else Nat.eqb (length (CC.cp_F c)) 1) && Nat.leb 70 (CC.cp_nx c)
         && match CC.cp_F c with [_; (_, o1, _)] => Z.eqb o1 200 | _ => true end && Z.eqb (reent_pc i) pc
         && match meas_cls c with
            | Some (inr z0) => (in_loop i && (5 <=? z0) && (Z.eqb pc LPC || Z.eqb pc L2PC) && (if Z.eqb pc L2PC then PB.has (CC.cp_know c) (KRange (EVar 49) 1 16384) else true))%bool
            | Some (inl z) => (under0 i && negb (in_loop i) && Z.eqb pc L0PC && (1073741824 <? z) && rng_is cells (EVar 42) 17)%bool
            | None => false
            end)%bool
      else true
  | _ => true
  end.
End PSM4.
Lemma rePt_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS PSM4.rePt_chk = true.
Proof. vmc_refl. Qed.
Lemma rePop_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS PSM4.rePop_chk = true.
Proof. vmc_refl. Qed.
Lemma reVec_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS PSM4.reVec_chk = true.
Proof. vmc_refl. Qed.
Lemma reAcc_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS PSM4.reAcc_chk = true.
Proof. vmc_refl. Qed.
Lemma reH_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS PSM4.reH_chk = true.
Proof. vmc_refl. Qed.
