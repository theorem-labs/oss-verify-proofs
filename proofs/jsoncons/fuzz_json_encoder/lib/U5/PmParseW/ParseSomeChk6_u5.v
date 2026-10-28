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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParseW Require Import ParseSomeChk_u5 ParseSomeChk2_u5 ParseSomeChk3_u5 ParseSomeA_u5 ParseSomeChk4_u5 ParseSomeChk5_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import PSMC. Import PSM2. Import PSM3. Import PSM4. Import PSM5.
Module PSM6.
(* [comment removed for export] *)
Definition set_size (lv : PB4.pvals2) (e : expr) : PB4.pvals2 :=
  PB4.PV2 (PB4.pv_level lv) (PB4.pv_wend lv) (PB4.pv_wptr lv) (PB4.pv_st lv) (PB4.pv_sst lv) (PB4.pv_nst lv) (PB4.pv_more lv) (PB4.pv_done lv) e (PB4.pv_sb lv) (PB4.pv_send lv) (PB4.pv_scend lv).
Definition rviewb (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) (j : nat) (nxj : nat) : option (PB4.pvals2 * PB4.pvals2 * expr * expr * delta) :=
  match ldelta i c ps, vw j with
  | Some (pv, lv, pe, ce, d), Some (pvj, pej, cej) =>
      if (forallb (fun ab : expr * expr => expr_eqb (fst ab) (snd ab)) (combine (flds pvj) (flds (set_size lv (APC.eaddz (PB4.pv_size lv) 1)))) && expr_eqb pej (EVar nxj) && expr_eqb cej (PSU.emul2 (EVar (nxj + 1)))
          && forallb (APC.expr_vars_lt nxj) (pe :: ce :: flds lv))%bool then Some (pv, lv, pe, ce, d) else None
  | _, _ => None
  end.
Definition pushb_chk2 (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      if Z.eqb pc PUSHB then
        match CH2.ret_of G.RETS i k with
        | Some j =>
            match kind_of i, kind_of j, rviewb i c ps j (CC.cp_nx (cutn j) - APC.NCS - 2)%nat with
            | KInv, KPushB, Some (pv, lv, pe, ce, d) =>
                (is_none (d_st d) && is_none (d_sst d) && is_none (d_nst d) && is_none (d_more d) && is_none (d_done d) && d_clr d
                 && rng_is (SR.ps_cells ps) (PB4.pv_more pv) 1 && (let '(lo, hi) := rng_of (SR.ps_cells ps) (PB4.pv_st pv) in (hi <? 17))
                 && expr_eqb (pushed_of j) (nth 11 (CA.ps_reglist ps) (ELit 0)) && APC.expr_vars_lt (CC.cp_nx (cutn j) - APC.NCS - 2)%nat (pushed_of j)
                 && match CAX.cell_at (SR.ps_cells ps) Pb (224 + 8) 8 with Some se => expr_eqb se (PB4.pv_size lv) | None => false end)%bool
            | _, _, _ => false
            end
        | None => false
        end
      else true
  | _ => true
  end.

(* [comment removed for export] *)
Definition is_cur (pc : Z) : bool := (Z.eqb pc PML.PC_PARSE_STRING || Z.eqb pc PML.PC_PARSE_NUMBER || Z.eqb pc PML.PC_PARSE_TRUE || Z.eqb pc PML.PC_PARSE_FALSE)%bool.
Definition is_expectb (x : Z) : bool := existsb (Z.eqb x) [1; 7; 9; 10; 11; 12; 13].
Definition wsb (x : Z) : bool := existsb (Z.eqb x) [9; 10; 13; 32].
Definition all_in (cells : list kentry) (e : expr) (f : Z -> bool) : bool := let '(lo, hi) := rng_of cells e in ((hi - lo <=? 64) && forallb f (zseq lo hi))%bool.
(* [comment removed for export] *)
Inductive dcls : Type := D0 | D1 | D2 | D3 (kk : Z).
Definition plainb (s : Z) : bool := (negb (ccrb s) && negb (s =? 15))%bool.
Definition dclass (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) (pv lv : PB4.pvals2) (d : delta) : option dcls :=
  let cells := SR.ps_cells ps in
  match kind_of i with
  | KInv =>
      if same_state d then (if (all_in cells (PB4.pv_st pv) (fun s => negb (s =? 17)) || foot2 c)%bool then Some D0 else None)
      else match d_st d, d_sst d, d_nst d, d_more d, d_done d, d_clr d with
           | Some (ELit 15), Some 0, None, None, None, true => if all_in cells (PB4.pv_st pv) plainb then Some D1 else None
           | _, _, _, _, _, _ => None
           end
  | KVec =>
      match d_st d, d_sst d, d_nst d, d_more d, d_done d, d_clr d, CAX.cell_at (CC.cp_know c) (EVar 2) (-120) 1 with
      | Some (ELit 15), Some 0, None, None, None, true, Some (ELit 16) => if all_in cells (PB4.pv_st pv) (fun s => (s =? 9) || (s =? 10))%bool then Some D2 else None
      | _, _, _, _, _, _, _ => None
      end
  | KPushB =>
      match d_st d, d_sst d, d_nst d, d_more d, d_done d, d_clr d with
      | Some (ELit 17), None, Some kk, None, None, false =>
          let '(blo, bhi) := rng_of cells (pushed_of i) in
          if (all_in cells (PB4.pv_st pv) plainb && foot2 c && (d_adv d =? 1) && APC.expr_vars_lt (CC.cp_nx c) (pushed_of i)
              && ((kk =? 0) && (blo =? 45) && (bhi =? 45) || (kk =? 1) && (blo =? 48) && (bhi =? 48) || (kk =? 2) && (49 <=? blo) && (bhi <=? 57)))%bool then Some (D3 kk) else None
      | _, _, _, _, _, _ => None
      end
  | _ => None
  end.
Definition regs_std (ps : SR.post_spec) : bool := let r := CA.ps_reglist ps in (expr_eqb (nth 10 r (ELit 0)) Pb && expr_eqb (nth 11 r (ELit 0)) Vb && expr_eqb (nth 12 r (ELit 0)) Eb)%bool.
Definition regs_cur (ps : SR.post_spec) (lv : PB4.pvals2) : bool :=
  let r := CA.ps_reglist ps in (expr_eqb (nth 10 r (ELit 0)) Pb && expr_eqb (nth 11 r (ELit 0)) (PB4.pv_wptr lv) && expr_eqb (nth 12 r (ELit 0)) Vb && expr_eqb (nth 13 r (ELit 0)) Eb)%bool.
(* [comment removed for export] *)
Definition loop_chk (c : CC.cutpoint) (ps : SR.post_spec) (pv : PB4.pvals2) (d : delta) (nxj : nat) : option Z :=
  let cells := SR.ps_cells ps in
  match d0_of pv with
  | Some d0 => if (PB.has cells (KRange (APC.esub (EVar 33) (EVar 53)) 0 16384) && rng_in cells (EVar 53) 1 16384 && Nat.ltb 54 (CC.cp_nx c) && Nat.ltb 54 nxj)%bool then Some (d0 + d_adv d) else None
  | None => None
  end.
Definition callee_chk (pc : Z) (i j : nat) (c : CC.cutpoint) (ps : SR.post_spec) (pv lv : PB4.pvals2) (cls : dcls) (slack : option Z) (adv : Z) : bool :=
  let cells := SR.ps_cells ps in let r := CA.ps_reglist ps in
  let is0 := match slack with Some 0 => true | _ => false end in let ge1 := match slack with Some z => 1 <=? z | None => false end in
  let d0c := match cls with D0 => true | _ => false end in
  if Z.eqb pc PML.PC_SKIP_SPACE then
    (d0c && expr_eqb (nth 10 r (ELit 0)) Pb && expr_eqb (nth 11 r (ELit 0)) (APC.eaddz Pb 200) && all_in cells (PB4.pv_st pv) is_expectb && is0
     && match CAX.cell_at cells (PB4.pv_wptr lv) 0 1 with Some bv => all_in cells bv wsb | None => false end)%bool
  else if Z.eqb pc PML.PC_PARSE_NULL then (d0c && regs_std ps && all_in cells (PB4.pv_st pv) is_expectb && is0)%bool
  else if (Z.eqb pc PML.PC_PARSE_TRUE || Z.eqb pc PML.PC_PARSE_FALSE)%bool then (d0c && regs_cur ps lv && all_in cells (PB4.pv_st pv) is_expectb && is0)%bool
  else if (Z.eqb pc PML.PC_BEGIN_OBJECT || Z.eqb pc PML.PC_BEGIN_ARRAY || Z.eqb pc PML.PC_END_OBJECT || Z.eqb pc PML.PC_END_ARRAY)%bool then (d0c && regs_std ps && all_in cells (PB4.pv_st pv) plainb && ge1)%bool
  else if Z.eqb pc PML.PC_BEGIN_MEMBER then
    (d0c && expr_eqb (nth 10 r (ELit 0)) Pb && expr_eqb (nth 11 r (ELit 0)) Eb && all_in cells (PB4.pv_st pv) (fun s => s =? 7) && is0 && Z.eqb (reent_pc j) L2PC)%bool
  else if Z.eqb pc PML.PC_PARSE_STRING then
    (regs_cur ps lv && match cls with D0 => all_in cells (PB4.pv_st pv) (fun s => s =? 15) | D1 | D2 => true | D3 _ => false end && (is0 || ge1))%bool
  else if Z.eqb pc PML.PC_PARSE_NUMBER then
    (regs_cur ps lv && match cls with D0 => (all_in cells (PB4.pv_st pv) (fun s => s =? 17) && is0 && (Nat.eqb i I_HLO || Nat.eqb i I_HHI || Nat.eqb i I_HN || Nat.eqb i I_L || Nat.eqb i I_HS))%bool | D3 _ => ge1 | _ => false end)%bool
  else if (Z.eqb pc PML.PC_END_INT || Z.eqb pc PML.PC_END_FRAC)%bool then
    (d0c && regs_std ps && all_in cells (PB4.pv_st pv) (fun s => s =? 17) && all_in cells (PB4.pv_nst pv) (fun s => existsb (Z.eqb s) [1; 2; 4; 7]) && under0 j && negb (in_loop j)
     && expr_eqb (PB4.pv_wptr pv) SEG && (adv =? 0))%bool
  else false.
Definition pt_chk2 (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      match pt_of pc, CH2.ret_of G.RETS i k with
      | Some _, Some j =>
          match ldelta i c ps with
          | Some (pv, lv, pe, ce, d) =>
              let cells := SR.ps_cells ps in let nxj := (CC.cp_nx (cutn j) - APC.NCS - 5)%nat in
              match dclass i c ps pv lv d with
              | Some cls =>
                  let slack := if in_loop j then loop_chk c ps pv d nxj else None in
                  (kind_eqb (kind_of j) KPt && Bool.eqb (cur_cut j) (is_cur pc) && Bool.eqb (PSI.skip_cut j) (Z.eqb pc PML.PC_SKIP_SPACE) && rng_is cells (PB4.pv_more pv) 1
                   && PB.has cells (KWord (SA Vb 0) 8 (ELit PML.VT_VISITOR)) && PB.has cells (KWord (SA Eb 0) 4 (ELit 0))
                   && (in_loop j || under0 j) && implb (in_loop j) (isSome slack) && (Z.eqb (reent_pc j) L2PC || negb (Z.eqb pc PML.PC_BEGIN_MEMBER)) && implb (Z.eqb (reent_pc j) L2PC) (Z.eqb pc PML.PC_BEGIN_MEMBER)
                   && implb (under0 j) (Z.eqb pc PML.PC_END_INT || Z.eqb pc PML.PC_END_FRAC)
                   && callee_chk pc i j c ps pv lv cls slack (d_adv d))%bool
              | None => false
              end
          | None => false
          end
      | _, _ => true
      end
  | _ => true
  end.
End PSM6.
Lemma pushb2_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS PSM6.pushb_chk2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pt2_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS PSM6.pt_chk2 = true.
Proof. vm_compute. reflexivity. Qed.
