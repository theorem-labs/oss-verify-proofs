(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSums_u5 ParseSums2_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSpecs_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5 ParseBridges3_u5 ParseBridges4_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParseW Require Import ParseSomeChk_u5 ParseSomeChk2_u5 ParseSomeChk3_u5 ParseSomeA_u5 ParseSomeChk4_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import PSMC. Import PSM2. Import PSM3. Import PSM4.
Module PSM5.
(* [comment removed for export] *)
Definition rview (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) (j : nat) (nxj : nat) : option (PB4.pvals2 * PB4.pvals2 * expr * expr * delta) :=
  match ldelta i c ps, vw j with
  | Some (pv, lv, pe, ce, d), Some (pvj, pej, cej) =>
      if (forallb (fun ab : expr * expr => expr_eqb (fst ab) (snd ab)) (combine (flds pvj) (flds lv)) && expr_eqb pej pe && expr_eqb cej ce
          && forallb (APC.expr_vars_lt nxj) (pe :: ce :: flds lv))%bool then Some (pv, lv, pe, ce, d) else None
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition setec_chk2 (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      if Z.eqb pc SETEC then
        match CH2.ret_of G.RETS i k with
        | Some j =>
            match kind_of i, kind_of j, rview i c ps j (CC.cp_nx (cutn j) - APC.NCS)%nat with
            | KInv, KSetEc, Some (pv, lv, pe, ce, d) | KParent, KSetEc, Some (pv, lv, pe, ce, d) => (is_none (d_st d) && is_none (d_sst d) && is_none (d_nst d) && negb (d_clr d) && match d_more d with None => true | Some z => (z =? 0) end && match d_done d with None => true | Some z => (z =? 0) || (z =? 1) end)%bool      (* [comment removed for export] *)
            | _, _, _ => false
            end
        | None => Nat.eqb i 0      (* [comment removed for export] *)
        end
      else true
  | _ => true
  end.
(* [comment removed for export] *)
Definition set_send (lv : PB4.pvals2) (e : expr) : PB4.pvals2 :=
  PB4.PV2 (PB4.pv_level lv) (PB4.pv_wend lv) (PB4.pv_wptr lv) (PB4.pv_st lv) (PB4.pv_sst lv) (PB4.pv_nst lv) (PB4.pv_more lv) (PB4.pv_done lv) (PB4.pv_size lv) (PB4.pv_sb lv) e (PB4.pv_scend lv).
Definition rviewp (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) (j : nat) (nxj : nat) : option (PB4.pvals2 * PB4.pvals2 * expr * expr * delta) :=
  match ldelta i c ps, vw j with
  | Some (pv, lv, pe, ce, d), Some (pvj, pej, cej) =>
      if (forallb (fun ab : expr * expr => expr_eqb (fst ab) (snd ab)) (combine (flds pvj) (flds (set_send lv (APC.eaddz (PB4.pv_send lv) (-1))))) && expr_eqb pej pe && expr_eqb cej ce
          && forallb (APC.expr_vars_lt nxj) (pe :: ce :: flds lv))%bool then Some (pv, lv, pe, ce, d) else None
  | _, _ => None
  end.
Definition same_state (d : delta) : bool := (is_none (d_st d) && is_none (d_sst d) && is_none (d_nst d) && is_none (d_more d) && is_none (d_done d) && negb (d_clr d))%bool.
Definition pure_chk2 (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      if Z.eqb pc POP then
        match CH2.ret_of G.RETS i k with
        | Some j =>
            match kind_of i, kind_of j, rviewp i c ps j (CC.cp_nx (cutn j) - APC.NCS - 1)%nat with
            | KInv, KPop, Some (pv, lv, pe, ce, d) =>
                (same_state d && rng_is (SR.ps_cells ps) (PB4.pv_more pv) 1
                 && implb (in_loop j) ((Nat.eqb i I_HLO || Nat.eqb i I_HHI || Nat.eqb i I_HN || Nat.eqb i I_L || Nat.eqb i I_HS) && Nat.ltb 54 (CC.cp_nx c) && Nat.ltb 54 (CC.cp_nx (cutn j) - APC.NCS - 1))
                 && (let '(lo, hi) := rng_of (SR.ps_cells ps) (PB4.pv_st pv) in (hi <? 17) || (17 <? lo))
                 && match CAX.cell_at (SR.ps_cells ps) Pb 256 8 with Some c8 => expr_eqb c8 (PB4.pv_send lv) | None => false end)%bool
            | _, _, _ => false
            end
        | None => false
        end
      else if Z.eqb pc PARENT then
        match CH2.ret_of G.RETS i k with
        | Some j =>
            match kind_of i, kind_of j, rview i c ps j (CC.cp_nx (cutn j) - APC.NCS - 1)%nat with
            | KInv, KParent, Some (pv, lv, pe, ce, d) | KParent, KParent, Some (pv, lv, pe, ce, d) =>
                (same_state d && rng_is (SR.ps_cells ps) (PB4.pv_more pv) 1 && (let '(lo, hi) := rng_of (SR.ps_cells ps) (PB4.pv_st pv) in (hi <? 17) || (17 <? lo)))%bool
            | _, _, _ => false
            end
        | None => false
        end
      else true
  | _ => true
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition set_vec (lv : PB4.pvals2) (sb send scend : expr) : PB4.pvals2 :=
  PB4.PV2 (PB4.pv_level lv) (PB4.pv_wend lv) (PB4.pv_wptr lv) (PB4.pv_st lv) (PB4.pv_sst lv) (PB4.pv_nst lv) (PB4.pv_more lv) (PB4.pv_done lv) (PB4.pv_size lv) sb send scend.
Definition rviewv (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) (j : nat) (nxj : nat) : option (PB4.pvals2 * PB4.pvals2 * expr * expr * delta) :=
  match ldelta i c ps, vw j with
  | Some (pv, lv, pe, ce, d), Some (pvj, pej, cej) =>
      let gb := EVar nxj in let gc := EVar (nxj + 1) in let slen' := APC.eaddz (PSU2.esub (PB4.pv_send lv) (PB4.pv_sb lv)) 1 in
      if (forallb (fun ab : expr * expr => expr_eqb (fst ab) (snd ab)) (combine (flds pvj) (flds (set_vec lv gb (PSU2.eadd gb slen') (PSU2.eadd gb gc)))) && expr_eqb pej pe && expr_eqb cej ce
          && forallb (APC.expr_vars_lt nxj) (pe :: ce :: flds lv))%bool then Some (pv, lv, pe, ce, d) else None
  | _, _ => None
  end.
Definition pushed_lit (ps : SR.post_spec) (j : nat) : option Z :=
  match CAX.cell_at (SR.ps_cells ps) (EVar 2) (-120) 1, CAX.cell_at (CC.cp_know (cutn j)) (EVar 2) (-120) 1 with
  | Some (ELit a), Some (ELit b) => if ((a =? b) && (0 <=? a) && (a <? 256))%bool then Some a else None
  | _, _ => None
  end.
Definition vec_chk2 (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      if Z.eqb pc VECPUSH then
        match CH2.ret_of G.RETS i k with
        | Some j =>
            match kind_of i, kind_of j, rviewv i c ps j (CC.cp_nx (cutn j) - APC.NCS - 2)%nat with
            | KInv, KVec, Some (pv, lv, pe, ce, d) =>
                (same_state d && rng_is (SR.ps_cells ps) (PB4.pv_more pv) 1 && (let '(lo, hi) := rng_of (SR.ps_cells ps) (PB4.pv_st pv) in (hi <? 17))
                 && (snd (split_lit (nth 11 (CA.ps_reglist ps) (ELit 0))) =? -120) && isSome (pushed_lit ps j)
                 && match CAX.cell_at (SR.ps_cells ps) Pb 256 8 with Some c8 => expr_eqb c8 (PB4.pv_send lv) | None => false end
                 && match pushed_lit ps j with      (* [comment removed for export] *)
                    | Some a => let '(lo, hi) := rng_of (SR.ps_cells ps) (PB4.pv_st pv) in (((a =? 16) && (9 <=? lo) && (hi <=? 10)) || ((lo =? hi) && (a =? lo)))
                    | None => false end)%bool
            | _, _, _ => false
            end
        | None => false
        end
      else true
  | _ => true
  end.
(* [comment removed for export] *)
Definition ng_of (pc : Z) : nat := if Z.eqb pc SETEC then 0 else if (Z.eqb pc POP || Z.eqb pc PARENT)%bool then 1 else if (Z.eqb pc VECPUSH || Z.eqb pc PUSHB)%bool then 2 else 5.
Definition callc_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      match CH2.ret_of G.RETS i k with
      | Some j => (implb (in_loop j) (in_loop i) && (if Nat.eqb i 0 then ne_chk (SR.ps_cells ps) (EVar 42) 2 else true) && Nat.leb GT.NF (CC.cp_nx (cutn j) - APC.NCS - ng_of pc))%bool
      | None => true
      end
  | _ => true
  end.
End PSM5.
Lemma setec2_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS PSM5.setec_chk2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma callc_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS PSM5.callc_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pure2_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS PSM5.pure_chk2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma vec2_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS PSM5.vec_chk2 = true.
Proof. vm_compute. reflexivity. Qed.
