(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore AsanPlanSound LibSym SegRun SegPlan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmEncSpecs_u5 PmLibSpecsW_u5 PmRef_u5 PmRefFacts_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RelLeaf.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSums_u5 ParseSums2_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSpecs_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5 ParseBridges3_u5 ParseBridges4_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParseW Require Import ParseSomeChk_u5 ParseSomeChk2_u5 ParseSomeChkW_u5 ParseSomeChk3_u5 ParseSomeChk4_u5 ParseSomeChk5_u5 ParseSomeChk6_u5 ParseSomeYK_u5.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import PSMC.

Module PSYJK.
(* [comment removed for export] *)
Definition pc_of_act (a : PMR.act) : option Z :=
  match a with
  | PMR.ASkip => Some PML.PC_SKIP_SPACE
  | PMR.ABegin true => Some PML.PC_BEGIN_ARRAY | PMR.ABegin false => Some PML.PC_BEGIN_OBJECT
  | PMR.AEnd true => Some PML.PC_END_ARRAY | PMR.AEnd false => Some PML.PC_END_OBJECT
  | PMR.AString _ => Some PML.PC_PARSE_STRING | PMR.AParseString => Some PML.PC_PARSE_STRING
  | PMR.ANumber => Some PML.PC_PARSE_NUMBER | PMR.AParseNumber => Some PML.PC_PARSE_NUMBER
  | PMR.ALit w => Some (if w =? 0 then PML.PC_PARSE_NULL else if w =? 1 then PML.PC_PARSE_TRUE else PML.PC_PARSE_FALSE)
  | PMR.AComma => Some PML.PC_BEGIN_MEMBER
  | _ => None
  end.
(* [comment removed for export] *)
Definition adv_of (a : PMR.act) : Z := match a with PMR.ABegin _ | PMR.AEnd _ | PMR.AString _ | PMR.ANumber => 1 | _ => 0 end.
Definition ptoff_of (a : PMR.act) : Z := match a with PMR.AComma => 1 | _ => 0 end.
Definition pc_is (a : PMR.act) (pc : Z) : bool := match pc_of_act a with Some p => p =? pc | None => false end.

Definition callw_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      match pt_of pc, CH2.ret_of G.RETS i k with
      | Some _, Some j =>
          match PSM2.ldelta i c ps with
          | Some (pv, lv, pe, ce, d) =>
              let cells := SR.ps_cells ps in
              PSM2.rng_is cells (PB4.pv_more pv) 1 && APC.expr_vars_lt (CC.cp_nx c) (PB4.pv_wptr pv) &&
              match kind_of i with
              | KInv =>
                  if Nat.eqb i I_ENTRY then      (* [comment removed for export] *)
                    (Z.eqb pc PML.PC_END_INT || Z.eqb pc PML.PC_END_FRAC) && (PSYK.PTOFF j =? 0) && PSM5.same_state d && (PSM2.d_adv d =? 0) &&
                    PSM2.rng_is cells (EVar 33) 0 && PSM2.rng_is cells (EVar 45) 1 && expr_eqb (PB4.pv_st pv) (EVar 42) && expr_eqb (PB4.pv_nst pv) (EVar 44) &&
                    PSYK.adm_all 42 cells 0 256 (fun st => PSYK.adm_all 44 cells 0 8 (fun nst => PSYK.pro_class st nst =? 0))
                  else
                    match PSCW.lact i k with
                    | Some (st, Some bv, a) =>      (* [comment removed for export] *)
                        pc_is a pc && (PSM2.d_adv d =? adv_of a) && (PSCW.OFF i =? 0) && (PSYK.PTOFF j =? ptoff_of a) &&
                        match a with
                        | PMR.AString false =>
                            PB.has cells (KWord (SA Pb 220) 1 (ELit 1)) &&      (* [comment removed for export] *)
                            match PSM2.d_st d, PSM2.d_sst d, PSM2.d_clr d, PSM2.d_more d, PSM2.d_done d with Some (ELit 15), Some 0, true, None, None => true | _, _, _, _, _ => false end
                        | PMR.AString true | PMR.ANumber | PMR.AParseString | PMR.AParseNumber => false
                        | _ => PSM5.same_state d
                        end
                    | Some (st, None, a) =>      (* [comment removed for export] *)
                        Nat.eqb i I_HLO && (st =? PML.ST_STRING) && PSM2.rng_is cells (PB4.pv_st pv) PML.ST_STRING
                    | None =>      (* [comment removed for export] *)
                        PSM5.same_state d && (PSM2.d_adv d =? 0) && (PSCW.OFF i =? 0) && (PSYK.PTOFF j =? 0) &&
                        PB.prove cells (KRange (APC.esub WEND (PB4.pv_wptr pv)) 1 16384) &&
                        ((Nat.eqb i I_HN && Z.eqb pc PML.PC_PARSE_NUMBER && PSM2.rng_is cells (PB4.pv_st pv) PML.ST_NUMBER)
                         || (Nat.eqb i I_HS && Z.eqb pc PML.PC_PARSE_STRING && PSM2.rng_is cells (PB4.pv_st pv) PML.ST_STRING && PSM2.foot2 c &&
                             PB.has cells (KWord (SA Pb 220) 1 (EVar 69)) && Nat.ltb 69 (CC.cp_nx c)))      (* [comment removed for export] *)
                    end
              | KVec =>      (* [comment removed for export] *)
                  match PSCW.ract i with Some (PMR.AString true) => true | _ => false end && Z.eqb pc PML.PC_PARSE_STRING &&
                  PB.has cells (KWord (SA Pb 220) 1 (ELit 1)) &&      (* [comment removed for export] *)
                  (PSCW.OFF i =? 0) && (PSM2.d_adv d =? 0) && (PSYK.PTOFF j =? 0) &&
                  match PSM2.d_st d, PSM2.d_sst d, PSM2.d_clr d, PSM2.d_more d, PSM2.d_done d with Some (ELit 15), Some 0, true, None, None => true | _, _, _, _, _ => false end
              | KPushB =>    (* [comment removed for export] *)
                  Z.eqb pc PML.PC_PARSE_NUMBER && (PSCW.OFF i =? 1) && (PSM2.d_adv d =? 1) && (PSYK.PTOFF j =? 0) &&
                  match PSM2.d_st d, PSM2.d_sst d, PSM2.d_clr d, PSM2.d_more d, PSM2.d_done d with Some (ELit 17), None, false, None, None => true | _, _, _, _, _ => false end &&
                  APC.expr_vars_lt (CC.cp_nx c) (PSM2.pushed_of i) &&
                  (let '(blo, bhi) := PSM2.rng_of cells (PSM2.pushed_of i) in
                   match PSM2.d_nst d with
                   | Some 0 => (blo =? 45) && (bhi =? 45) | Some 1 => (blo =? 48) && (bhi =? 48) | Some 2 => (49 <=? blo) && (bhi <=? 57) | _ => false end)
              | _ => false
              end
          | None => false
          end
      | Some _, None => false
      | None, _ => true
      end
  | _ => true
  end.
Lemma callw_ok : CH2.leaves_all G.CPS G.TAGS callw_chk = true.
Proof. vm_compute. reflexivity. Qed.
End PSYJK.
