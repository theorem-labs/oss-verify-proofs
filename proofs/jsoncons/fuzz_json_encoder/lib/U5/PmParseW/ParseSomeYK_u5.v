(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore AsanPlanSound LibSym SegRun SegPlan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmEncSpecs_u5 PmLibSpecsW_u5 PmRef_u5 PmRefFacts_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RelLeaf.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSums_u5 ParseSums2_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSpecs_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5 ParseBridges3_u5 ParseBridges4_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParseW Require Import ParseSomeChk_u5 ParseSomeChk2_u5 ParseSomeChkW_u5 ParseSomeChk3_u5 ParseSomeChk4_u5 ParseSomeChk5_u5.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import PSMC.

Module PSYK.
(* [comment removed for export] *)
Definition PTOFF (i : nat) : Z := match nth i PSCW.RACT None with Some PMR.AComma => 1 | _ => 0 end.

(* [comment removed for export] *)
Definition adm_all (v : nat) (cells : list kentry) (lo : Z) (n : nat) (f : Z -> bool) : bool := RLF.forall_b lo n (fun z => negb (RLF.byte_adm v cells z) || f z).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition srcb_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match PSCW.lact i k with
  | Some (st, Some bv, a) =>
      match PSM2.ldelta i c ps with
      | Some (pv, lv, pe, ce, d) =>
          (PSCW.OFF i =? 0) &&
          (let cells := SR.ps_cells ps in
           PSM2.rng_is cells (PB4.pv_st pv) st && PSM2.rng_is cells (PB4.pv_more pv) 1 && APC.expr_vars_lt (CC.cp_nx c) (PB4.pv_wptr pv) &&
           PB.has cells (KWord (SA (PB4.pv_wptr pv) 0) 1 (EVar bv)) && PB.has cells (KRange (EVar bv) 0 255) && PB.has cells (KBlob (SA (EVar 32) 0) (EVar 33) 1) &&
           PB.prove cells (KRange (APC.esub WEND (PB4.pv_wptr pv)) 1 16384) &&
           if SR.ps_pc ps =? PARENT then
             match PSCW.leaf_b0 i k with
             | Some b0 => RLF.all_bytes (fun b => negb (RLF.byte_adm bv cells b) || PSCW.all_parents (fun p => PSCW.act_eqb (PMR.dispatch st p b) (PMR.dispatch st p b0)))
             | None => false end
           else RLF.all_bytes (fun b => negb (RLF.byte_adm bv cells b) || PSCW.all_parents (fun p => PSCW.act_eqb (PMR.dispatch st p b) a)))
      | None => false
      end
  | _ => true
  end.
Lemma srcb_ok : CH2.leaves_all G.CPS G.TAGS srcb_chk = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition srcn_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match PSCW.lact i k with
  | Some (st, None, a) =>
      match PSM2.ldelta i c ps with
      | Some (pv, lv, pe, ce, d) =>
          (PSCW.OFF i =? 0) &&
          (let cells := SR.ps_cells ps in
           PSM2.rng_is cells (PB4.pv_st pv) st && PSM2.rng_is cells (PB4.pv_more pv) 1 && APC.expr_vars_lt (CC.cp_nx c) (PB4.pv_wptr pv) &&
           PB.prove cells (KRange (APC.esub WEND (PB4.pv_wptr pv)) 1 16384) &&
           RLF.all_bytes (fun b => PSCW.all_parents (fun p => PSCW.act_eqb (PMR.dispatch st p b) a)))
      | None => false
      end
  | _ => true
  end.
Lemma srcn_ok : CH2.leaves_all G.CPS G.TAGS srcn_chk = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition visw_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      if (Z.eqb pc VNULL || Z.eqb pc VBOOL)%bool then
        match CH2.ret_of G.RETS i k, PSCW.lact i k, PSM2.ldelta i c ps with
        | Some j, Some (st, Some bv, PMR.ALitDone), Some (pv, lv, pe, ce, d) =>
            match kind_of j with KVis => true | _ => false end && negb (Nat.eqb i I_ENTRY) && (PSCW.OFF i =? 0) &&
            (PSM2.d_adv d + PSCW.OFF j =? 1) && negb (st =? PML.ST_STRING) && negb (st =? PML.ST_NUMBER) &&
            match PSM2.d_st d, PSM2.d_sst d, PSM2.d_nst d, PSM2.d_more d, PSM2.d_done d with None, None, None, None, None => true | _, _, _, _, _ => false end && negb (PSM2.d_clr d) &&
            match PSM2.vw j with Some (pvj, pej, cej) => forallb (fun ab : expr * expr => expr_eqb (fst ab) (snd ab)) (combine (pej :: cej :: PSM2.flds pvj) (pe :: ce :: PSM2.flds lv)) &&
                                                          forallb (APC.expr_vars_lt (CC.cp_nx (PSM2.cutn j) - APC.NCS)) (pe :: ce :: PSM2.flds lv) | None => false end &&
            (let cells := SR.ps_cells ps in
             PSM2.rng_is cells (PB4.pv_st pv) st && PSM2.rng_is cells (PB4.pv_more pv) 1 && APC.expr_vars_lt (CC.cp_nx c) (PB4.pv_wptr pv) &&
             PB.has cells (KWord (SA (PB4.pv_wptr pv) 0) 1 (EVar bv)) && PB.has cells (KRange (EVar bv) 0 255) && PB.has cells (KBlob (SA (EVar 32) 0) (EVar 33) 1) &&
             PB.prove cells (KRange (APC.esub WEND (PB4.pv_wptr pv)) 1 16384) &&
             RLF.all_bytes (fun b => negb (RLF.byte_adm bv cells b) || PSCW.all_parents (fun p => PSCW.act_eqb (PMR.dispatch st p b) PMR.ALitDone)))
        | _, _, _ => false
        end
      else true
  | _ => true
  end.
Lemma visw_ok : CH2.leaves_all G.CPS G.TAGS visw_chk = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition exitw_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      if Z.eqb pc RETPC then
        match kind_of i, PSM2.ldelta i c ps with
        | KInv, Some (pv, _, _, _, _) =>
            (PSCW.OFF i =? 0) &&
            (PSM2.foot2 c || Nat.eqb i I_HLO || (let '(lo, hi) := PSM2.rng_of (SR.ps_cells ps) (PB4.pv_st pv) in (hi <? PML.ST_STRING) || (PML.ST_STRING <? lo)))
        | KInv, None => false
        | _, _ => true
        end
      else true
  | _ => true
  end.
Lemma exitw_ok : CH2.leaves_all G.CPS G.TAGS exitw_chk = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pro_class (st nst : Z) : Z :=
  if st =? PML.ST_NUMBER then (if (nst =? 1) || (nst =? 2) || (nst =? 4) || (nst =? 7) then 0 else 1)
  else if st =? PML.ST_ACCEPT then 2 else if st =? PML.ST_START then 1 else if st =? PML.ST_DONE then 2 else if st =? PML.ST_CR then 3 else 1.
Definition entry_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      if Nat.eqb i I_ENTRY && (Z.eqb pc SETEC || Z.eqb pc POP) then
        let cells := SR.ps_cells ps in
        PSM2.rng_is cells (EVar 33) 0 && PSM2.rng_is cells (EVar 45) 1 &&
        (if Z.eqb pc SETEC then
           match nth 11 (CA.ps_reglist ps) (ELit 0) with ELit 1 => true | _ => false end &&
           adm_all 42 cells 0 256 (fun st => adm_all 44 cells 0 8 (fun nst => pro_class st nst =? 1))
         else PSM2.rng_is cells (EVar 42) PML.ST_CR)
      else true
  | _ => true
  end.
Lemma entry_ok : CH2.leaves_all G.CPS G.TAGS entry_chk = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition setec_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      if Z.eqb pc SETEC then
        match nth 11 (CA.ps_reglist ps) (ELit 0) with
        | ELit code =>
            match kind_of i with
            | KInv => if Nat.eqb i I_ENTRY then true
                      else match PSCW.lact i k with Some (_, Some _, PMR.AErr code' _) => code' =? code | _ => false end
            | KParent =>
                match PSCW.PPAR i, PSCW.A0 i with
                | Some (st, b0, snd), EVar av =>
                    Nat.ltb av (CC.cp_nx c) && (let '(lo, hi) := PSM2.rng_of (SR.ps_cells ps) (EVar av) in (0 <=? lo) && (hi <? 256)) &&
                    adm_all av (SR.ps_cells ps) 0 256 (fun p => (snd && (p =? PML.ST_ARRAY)) || match PMR.dispatch st p b0 with PMR.AErr code' _ => code' =? code | _ => false end)
                | _, _ => false
                end
            | _ => false
            end
        | _ => false
        end
      else true
  | _ => true
  end.
Lemma setec_ok : CH2.leaves_all G.CPS G.TAGS setec_chk = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition call2_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      if (Z.eqb pc VECPUSH || Z.eqb pc PUSHB || Z.eqb pc POP || Z.eqb pc PARENT)%bool then
        match CH2.ret_of G.RETS i k with
        | Some j =>
            match kind_of i with
            | KInv =>
                if Nat.eqb i I_ENTRY then Z.eqb pc POP && match kind_of j with KPop => true | _ => false end
                else
                match PSCW.lact i k, PSM2.ldelta i c ps with
                | Some (st, Some bv, a), Some (pv, lv, pe, ce, d) =>
                    match PSCW.ract j with Some a' => PSCW.act_eqb a' a | None => false end &&
                    match a, kind_of j with
                    | PMR.ASlash, KVec | PMR.APushCr, KVec => (PSM2.d_adv d + PSCW.OFF j =? 1) && (st <? PML.ST_STRING) && match PSM5.pushed_lit ps j with Some x => x =? st | None => false end
                    | PMR.AString true, KVec => (PSM2.d_adv d + PSCW.OFF j =? 1) && (st <? PML.ST_STRING) && match PSM5.pushed_lit ps j with Some x => x =? PML.ST_MEMBER_NAME | None => false end
                    | PMR.ANumber, KPushB => (PSM2.d_adv d + PSCW.OFF j =? 1) && (st <? PML.ST_STRING) &&
                        match PSM2.pushed_of j with
                        | EVar v => Nat.eqb v bv && Nat.ltb bv (CC.cp_nx (PSM2.cutn j) - APC.NCS - 2)
                        | ELit z => RLF.all_bytes (fun b => negb (RLF.byte_adm bv (SR.ps_cells ps) b) || (b =? z))      (* [comment removed for export] *)
                        | _ => false end
                    | PMR.APop cns, KPop => (PSM2.d_adv d + PSCW.OFF j =? (if cns then 1 else 0))
                    | PMR.AErr _ _, KParent =>      (* [comment removed for export] *)
                        match PSCW.PPAR j, PSCW.leaf_b0 i k with Some (st', b0', false), Some b0 => (st' =? st) && (b0' =? b0) | _, _ => false end && (st <? PML.ST_STRING) &&
                        expr_eqb (PSCW.A0 j) (EVar (CC.cp_nx (PSM2.cutn j) - APC.NCS - 1))
                    | _, _ => false
                    end
                | _, _ => false
                end
            | KParent =>      (* [comment removed for export] *)
                Z.eqb pc PARENT && match kind_of j with KParent => true | _ => false end &&
                match PSCW.PPAR i, PSCW.PPAR j, PSCW.A0 i, PSM2.ldelta i c ps with
                | Some (st, b0, false), Some (st', b0', true), EVar av, Some (pv, lv, pe, ce, d) =>
                    (st' =? st) && (b0' =? b0) && Nat.ltb av (CC.cp_nx c) && PSM2.ne_chk (SR.ps_cells ps) (EVar av) PML.ST_ARRAY &&
                    (let '(lo, hi) := PSM2.rng_of (SR.ps_cells ps) (PB4.pv_st pv) in hi <? PML.ST_STRING) && expr_eqb (PSCW.A0 j) (EVar (CC.cp_nx (PSM2.cutn j) - APC.NCS - 1))
                | _, _, _, _ => false
                end
            | _ => false
            end
        | None => false
        end
      else true
  | _ => true
  end.
Lemma call2_ok : CH2.leaves_all G.CPS G.TAGS call2_chk = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tagv (i : nat) : option nat := if Nat.eqb i I_ENTRY then Some 49%nat else if (Nat.eqb i I_L0 || Nat.eqb i I_HS)%bool then Some 69%nat else None.
Definition footw (c : CC.cutpoint) : bool := match CC.cp_F c with [_] => true | [_; (_, o1, _)] => (o1 =? 200) | _ => false end.
Definition tagl_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match kind_of i with
  | KInv =>
      footw c
      || match tagv i with Some v => PB.has (SR.ps_cells ps) (KWord (SA Pb 220) 1 (EVar v)) && Nat.ltb v (CC.cp_nx c) | None => false end
      || Nat.eqb i I_HLO || Nat.eqb i I_L2
      || match PSM2.ldelta i c ps with
         | Some (pv, _, _, _, _) => let '(lo, hi) := PSM2.rng_of (SR.ps_cells ps) (PB4.pv_st pv) in (hi <? PML.ST_STRING) || (PML.ST_STRING <? lo)
         | None => false end
  | _ => true
  end%bool.
Lemma tagl_ok : CH2.leaves_all G.CPS G.TAGS tagl_chk = true.
Proof. vm_compute. reflexivity. Qed.

Definition reent_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      if (Z.eqb pc LPC || Z.eqb pc L0PC || Z.eqb pc L2PC || Z.eqb pc HPC)%bool then
        match kind_of i with
        | KPop => match PSM2.ldelta i c ps with Some (_, _, _, _, d) => (PSM2.d_adv d =? PSCW.OFF i) | None => false end
        | KVec => match PSM2.ldelta i c ps, PSCW.ract i with
                  | Some (pv, _, _, _, d), Some a => (PSM2.d_adv d =? PSCW.OFF i) && Z.eqb pc LPC &&
                       match a, PSM2.d_st d with PMR.ASlash, Some (ELit 3) | PMR.APushCr, Some (ELit 28) => true | _, _ => false end
                  | _, _ => false end
        | KPt => if Z.eqb pc L2PC then PTOFF i =? 1 else PTOFF i =? 0
        | KInv => if Z.eqb pc LPC then match PSCW.lact i k with Some (_, None, PMR.AAccept) => true | _ => false end
                  else if Z.eqb pc HPC then (Nat.eqb i I_L0 || Nat.eqb i I_L) && PSM2.foot2 c else true
        | _ => true
        end
      else true
  | _ => true
  end.
Lemma reent_ok : CH2.leaves_all G.CPS G.TAGS reent_chk = true.
Proof. vm_compute. reflexivity. Qed.
End PSYK.
