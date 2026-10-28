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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSpecs_u ParseBridges_u ParseBridges2_u ParseBridges3_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_pn_csrc_T_u Cut_pn_csrc_D_u Cut_pn_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module PNC.
Module G := Cut_pn_csrc_D_u.
Module GT := Cut_pn_csrc_T_u.
Definition RETPC : Z := 0x3e890.
Definition APPR : Z := PML.PC_APPEND_RANGE.  Definition SETEC : Z := PML.PC_SET_EC.  Definition ENDI : Z := PML.PC_END_INT.  Definition ENDF : Z := PML.PC_END_FRAC.

Definition Pb : expr := EVar 10.  Definition SEG : expr := EVar 11.  Definition Vb : expr := EVar 12.  Definition Eb : expr := EVar 13.
Definition WLEN : expr := EVar 32.  Definition BX : expr := EVar 33.  Definition K0 : expr := EVar 34.  Definition SIZE0 : expr := EVar 35.  Definition P0 : expr := EVar 36.
Definition SBx : expr := EVar 37.  Definition SLEN : expr := EVar 38.  Definition SCAP : expr := EVar 39.
Definition LVL : expr := EVar 40.  Definition SST : expr := EVar 41.  Definition NST0 : expr := EVar 42.  Definition DONE : expr := EVar 43.
Definition JV : expr := EVar 46.
Definition WEND : expr := APC.eadd SEG WLEN.
Definition CURJ : expr := APC.esub WEND JV.
Definition SCR : Z := 9568.
Definition ENDNUM_SCR : Z := 9456.

Inductive kind : Set := KPre | KApp | KSetEc | KEnd.
Definition kind_eqb (a b : kind) : bool := match a, b with KPre, KPre | KApp, KApp | KSetEc, KSetEc | KEnd, KEnd => true | _, _ => false end.
Lemma kind_eqb_eq : forall a b, kind_eqb a b = true -> a = b.
Proof. intros [] [] H; try discriminate; reflexivity. Qed.
Definition kind_of (j : nat) : kind :=
  match find (fun r : nat * nat * nat * Z => let '(j', _, _, _) := r in Nat.eqb j j') G.RETS with
  | Some (_, _, _, pc) => if Z.eqb pc SETEC then KSetEc else if Z.eqb pc APPR then KApp else if (Z.eqb pc ENDI || Z.eqb pc ENDF)%bool then KEnd else KPre
  | None => KPre
  end.

Definition cut_states (i : nat) : option (list Z) :=
  nth i [None; Some [0]; Some [1]; Some [1; 2]; Some [3]; Some [4]; Some [5]; Some [6]; Some [7]; Some [3]; Some [4]; Some [1; 2]; Some [7]; Some [1]; Some [4]; Some [1; 2]; Some [7];
         None; None; None; None; None;   Some [1]; Some [1; 2]; Some [3]; Some [4]; Some [5]; Some [6]; Some [7]] None.
Definition entry_states (c : Z) : list Z := if Z.eqb c 2 then [1; 2] else [c].
Definition nst_ok (c k : Z) : bool := (Z.eqb k c || (Z.eqb c 2 && Z.eqb k 1))%bool.
Definition final_ok (k : Z) : bool := existsb (Z.eqb k) [1; 2; 4; 7].
Definition zseq (lo hi : Z) : list Z := map (fun n => lo + Z.of_nat n) (seq 0 (Z.to_nat (hi - lo + 1))).
Definition step_chk (Si : list Z) (lo hi : Z) (okf : Z -> bool) : bool :=
  forallb (fun v => forallb (fun k => match PML.nl_step k v with Some k' => okf k' | None => false end) Si) (zseq lo hi).

Definition rng_is (cells : list kentry) (e : expr) (v : Z) : bool := match CX.range3 cells e with Some (lo, hi) => (Z.eqb lo v && Z.eqb hi v)%bool | None => false end.
Definition lo_ge (cells : list kentry) (e : expr) (v : Z) : bool := match CX.range3 cells e with Some (lo, _) => Z.leb v lo | None => false end.

Definition named_at (cells : list kentry) (cur : expr) : option (saddr * expr * Z * Z) :=
  match find (fun X => match X with KWord a 1 _ => rng_is cells (APC.esub (APC.eaddz (a_base a) (a_off a)) cur) 0 | _ => false end) cells with
  | Some (KWord a 1 v) => match CX.range3 cells v with
                          | Some (lo, hi) => if (Z.leb 0 lo && Z.leb hi 255)%bool then Some (a, v, lo, hi) else None
                          | None => None end
  | _ => None
  end.

Definition content_chk (i : nat) (cells : list kentry) (tgt : expr) (okf : Z -> bool) : bool :=
  match cut_states i with
  | None => false
  | Some Si =>
      if rng_is cells (APC.esub tgt CURJ) 0 then forallb okf Si
      else if (rng_is cells (APC.esub tgt CURJ) 1 && (lo_ge cells JV 1 || (rng_is cells (APC.esub WLEN JV) 0 && lo_ge cells WLEN 1)) && PB.has cells (KBlob (SA SEG 0) WLEN 1))%bool then
        match named_at cells CURJ with Some (_, _, lo, hi) => step_chk Si lo hi okf | None => false end
      else false
  end.
Definition lit_nst (cells : list kentry) : option Z := match CAX.cell_at cells Pb 210 1 with Some (ELit c) => Some c | _ => None end.

Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition stack_reg_eqb (r : SGP.region) : bool := let '(b, lo, len) := r in (expr_eqb b (EVar 2) && Z.eqb lo (- SCR) && expr_eqb len (ELit SCR))%bool.
Definition pobj_reg_eqb (r : SGP.region) : bool := let '(b, lo, len) := r in (expr_eqb b Pb && Z.eqb lo 0 && expr_eqb len (ELit 272))%bool.
Definition foot_pre_chk (c : CC.cutpoint) : bool := forallb (fun r => (stack_reg_eqb r || pobj_reg_eqb r)%bool) (CC.cp_F c).
Definition foot_end_chk (c : CC.cutpoint) : bool := forallb stack_reg_eqb (CC.cp_F c).

Definition cells16 (cells : list kentry) : list kentry :=
  match CAX.cell_at cells Pb 210 1, know_byte_lit PML.RSEGS cells Pb 210, know_byte_lit PML.RSEGS cells Pb 211 with
  | None, Some b0, Some b1 => KWord (SA Pb 210) 1 (ELit b0) :: KWord (SA Pb 211) 1 (ELit b1) :: cells
  | _, _, _ => cells
  end.

Definition blk2 (BL : CA.blocks) : option (expr * expr) :=
  match BL with [(pe, ce); (sb, sc)] => if (expr_eqb sb SBx && expr_eqb sc SCAP)%bool then Some (pe, ce) else None | _ => None end.
Definition view_chk (more_lit : Z) (cells : list kentry) (BL : CA.blocks) : option (expr * expr * PB2.pvals) :=
  match blk2 BL with
  | Some (pe, ce) =>
      match PB2.pview cells Pb pe ce SBx SLEN SCAP with
      | Some pv =>
          if (expr_eqb (PB2.pv_st pv) (ELit 17) && expr_eqb (PB2.pv_more pv) (ELit more_lit) && expr_eqb (PB2.pv_done pv) DONE && expr_eqb (PB2.pv_sst pv) SST
              && expr_eqb (PB2.pv_level pv) LVL && expr_eqb (PB2.pv_wptr pv) SEG && expr_eqb (PB2.pv_wend pv) WEND && PB.prove cells (KRange (PB2.pv_nst pv) 0 7))%bool
          then Some (pe, ce, pv) else None
      | None => None
      end
  | None => None
  end.
Definition sz_of (c : CC.cutpoint) : expr := match CAX.cell_at (CC.cp_know c) Pb 232 8 with Some e => e | None => ELit 0 end.
Definition nstc_of (c : CC.cutpoint) : option expr := CAX.cell_at (CC.cp_know c) Pb 210 1.

Definition exit_pre_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in let a0e := nth 10 (CA.ps_reglist ps) (ELit 0) in
  (PB.exit_base_chk GT.NF RETPC c ps && CH2.all_regs_chk ps && foot_pre_chk c && CH2.blocks_vars_lt (CC.cp_nx c) (nth i G.BLS []) && Nat.ltb 46 (CC.cp_nx c) &&
   match view_chk 1 cells (nth i G.BLS []), cut_states i with
   | Some (pe, ce, pv), Some Si =>
       match PB2.pv_nst pv with
       | ELit cn => (Z.leb 0 cn && Z.leb cn 7 && PB.has cells (KWord (SA Eb 0) 4 (ELit 0)) && expr_eqb pe P0 && expr_eqb (PB2.pv_size pv) SIZE0 && forallb (nst_ok cn) Si
                     && PB.prove cells (KRange (APC.esub WLEN JV) 0 0) && PB.prove cells (KRange (APC.esub a0e SEG) 0 16384) && PB.prove cells (KRange (APC.esub WEND a0e) 0 0)
                     && PB.prove cells (KRange (APC.esub BX SIZE0) 0 67108864))%bool
       | _ => false
       end
   | _, _ => false
   end)%bool.
Definition exit_app_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in let a0e := nth 10 (CA.ps_reglist ps) (ELit 0) in
  (PB.exit_base_chk GT.NF RETPC c ps && CH2.all_regs_chk ps && foot_pre_chk c && CH2.blocks_vars_lt (CC.cp_nx c) (nth i G.BLS []) &&
   match view_chk 1 cells (nth i G.BLS []), nstc_of c with
   | Some (pe, ce, pv), Some (ELit cn) =>
       (Z.leb 0 cn && Z.leb cn 7 && PB.has cells (KWord (SA Eb 0) 4 (ELit 0)) && expr_eqb (PB2.pv_nst pv) (ELit cn) && expr_eqb (PB2.pv_size pv) (sz_of c) && APC.expr_vars_lt (CC.cp_nx c) (sz_of c)
        && PB.prove cells (KRange (APC.esub a0e SEG) 0 16384) && PB.prove cells (KRange (APC.esub WEND a0e) 0 0)
        && PB.prove cells (KRange (APC.esub (APC.esub a0e SEG) (APC.esub (sz_of c) SIZE0)) 0 0)
        && PB.prove cells (KRange (APC.esub BX (sz_of c)) 0 67108864))%bool
   | _, _ => false
   end)%bool.
Definition exit_setec_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := cells16 (SR.ps_cells ps) in let a0e := nth 10 (CA.ps_reglist ps) (ELit 0) in
  (PB.exit_base_chk GT.NF RETPC c ps && CH2.all_regs_chk ps && foot_pre_chk c && CH2.blocks_vars_lt (CC.cp_nx c) (nth i G.BLS []) &&
   match view_chk 0 cells (nth i G.BLS []) with
   | Some (pe, ce, pv) =>
       match CAX.cell_at cells Eb 0 4 with
       | Some (ELit code) => (Z.leb 1 code && Z.leb code 31 && PB.has cells (KWord (SA Eb 8) 8 (ELit PML.OBJ_JSON_CATEGORY)) && expr_eqb (PB2.pv_size pv) SIZE0
                              && PB.prove cells (KRange (APC.esub a0e SEG) 0 16384) && PB.prove cells (KRange (APC.esub WEND a0e) 0 16384)
                              && PB.prove cells (KRange (APC.esub BX (APC.eadd SIZE0 (APC.esub WEND a0e))) 0 67108864))%bool
       | _ => false
       end
   | None => false
   end)%bool.
Definition ghost_of (c : CC.cutpoint) : nat := (CC.cp_nx c - APC.NCS - 5)%nat.
Definition exit_end_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in let a0e := nth 10 (CA.ps_reglist ps) (ELit 0) in
  (PB.exit_base_chk GT.NF RETPC c ps && CH2.all_regs_chk ps && foot_end_chk c && CH2.blocks_vars_lt (CC.cp_nx c) (nth i G.BLS []) && Nat.ltb (ghost_of c) (CC.cp_nx c) && Nat.ltb 46 (CC.cp_nx c)
   && PB.prove cells (KRange (APC.esub a0e CURJ) 0 0))%bool.

Definition app_leaf_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) : bool :=
  let cells := SR.ps_cells ps in let regs := CA.ps_reglist ps in
  let a1e := nth 11 regs (ELit 0) in let a2e := nth 12 regs (ELit 0) in
  (expr_eqb a1e SEG && PB.has cells (KBlob (SA SEG 0) WLEN 1) && Nat.ltb 46 (CC.cp_nx c)
   && match blk2 (nth i G.BLS []) with Some (pe, ce) => expr_eqb pe P0 | None => false end
   && APC.expr_vars_lt (CC.cp_nx cj - APC.NCS - 2) a2e && Nat.leb GT.NF (CC.cp_nx cj - APC.NCS - 2)
   && match CAX.cell_at cells Pb 232 8 with Some se => (expr_eqb se SIZE0 && expr_eqb (sz_of cj) (PSU.eadd se (PSU.esub a2e a1e)))%bool | None => false end
   && match CAX.cell_at cells Pb 210 1, nstc_of cj with
      | Some (ELit cn), Some (ELit cn') => (Z.eqb cn cn' && Z.leb 0 cn && Z.leb cn 7 && content_chk i cells a2e (nst_ok cn))%bool
      | Some (EVar v), Some (EVar v') => (Nat.eqb v v' && content_chk i cells a2e final_ok)%bool
      | _, _ => false
      end)%bool.
Definition end_leaf_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) : bool :=
  let cells := SR.ps_cells ps in let regs := CA.ps_reglist ps in
  (CH2.blocks_vars_lt (CC.cp_nx c) (nth i G.BLS []) && expr_eqb (nth 10 regs (ELit 0)) Pb && expr_eqb (nth 11 regs (ELit 0)) Vb && expr_eqb (nth 12 regs (ELit 0)) Eb && Nat.ltb 46 (CC.cp_nx c)
   && Nat.ltb 46 (CC.cp_nx cj - APC.NCS - 5) &&
   match view_chk 1 cells (nth i G.BLS []), nstc_of c with
   | Some (pe, ce, pv), Some (EVar _) =>
       (PB.has cells (KWord (SA Eb 0) 4 (ELit 0)) && PB.has cells (KWord (SA Vb 0) 8 (ELit PML.VT_VISITOR)) && PB.has cells (KUnk (SA SEG 0) WLEN)
        && expr_eqb (PB2.pv_size pv) (sz_of c) && APC.expr_vars_lt (CC.cp_nx c) (sz_of c)
        && PB.prove cells (KRange (APC.esub CURJ SEG) 0 16384) && PB.prove cells (KRange (APC.esub WEND CURJ) 0 16384)
        && PB.prove cells (KRange (APC.esub (APC.esub CURJ SEG) (APC.esub (sz_of c) SIZE0)) 0 0)
        && PB.prove cells (KRange (APC.esub BX (APC.eadd (sz_of c) (APC.esub WEND CURJ))) 0 67108864))%bool
   | _, _ => false
   end)%bool.

Definition goto_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) (j : nat) (s : CC.subst) : bool :=
  let cells := SR.ps_cells ps in let jj := CC.esubstL GT.NF s JV in
  (kind_eqb (kind_of i) KPre && kind_eqb (kind_of j) KPre && foot_pre_chk c && Nat.ltb 0 j && Nat.ltb j 29 && (Nat.eqb i 0 || Nat.ltb 46 (CC.cp_nx c)) &&
   match cut_states j with
   | None => true
   | Some Sj =>
       if Nat.eqb i 0 then
         match CX.range3 cells NST0 with
         | Some (cn, cn') => (Z.eqb cn cn' && forallb (fun k => existsb (Z.eqb k) Sj) (entry_states cn) && rng_is cells (APC.esub WLEN jj) 0)%bool
         | None => false
         end
       else content_chk i cells (APC.esub WEND jj) (fun k => existsb (Z.eqb k) Sj)
   end)%bool.

Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto j s => goto_chk i c ps j s
  | CC.TOther pc =>
      if Z.eqb pc RETPC then
        match kind_of i with KPre => exit_pre_chk i c ps | KApp => exit_app_chk i c ps | KSetEc => exit_setec_chk i c ps | KEnd => exit_end_chk i c ps end
      else
        (foot_pre_chk c && Z.eqb (SR.ps_pc ps) pc &&
         match CH2.ret_of G.RETS i k with
         | Some j => match nth_error G.CPS j with
                     | Some cj =>
                         if Z.eqb pc APPR then (kind_eqb (kind_of i) KPre && kind_eqb (kind_of j) KApp && Nat.ltb 0 i
                                                && isSome (PB3.appendr_chk GT.NF G.HDECL Pb 224 SEG WLEN 132 c ps cj (nth i G.BLS []) (nth j G.BLS [])) && app_leaf_chk i c ps cj)%bool
                         else if Z.eqb pc SETEC then (kind_eqb (kind_of i) KPre && kind_eqb (kind_of j) KSetEc && isSome (PB2.setec_chk GT.NF G.HDECL Eb 0 c ps cj (nth i G.BLS []) (nth j G.BLS [])))%bool
                         else if (Z.eqb pc ENDI || Z.eqb pc ENDF)%bool then
                           (kind_eqb (kind_of i) KApp && kind_eqb (kind_of j) KEnd
                            && isSome (PB2.ptrans_chkc GT.NF G.HDECL Eb 0 Pb 0 ENDNUM_SCR Vb 0 12 c ps cj (nth i G.BLS []) (nth j G.BLS [])) && end_leaf_chk i c ps cj)%bool
                         else false
                     | None => false end
         | None => false end)%bool
  end.
End PNC.

Lemma heap_ok3 : CH2.heap_chk3 PNC.GT.NF PNC.G.HDECL PNC.G.BLS PNC.G.CPS PNC.G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma leaf_ok : CH2.leaves_all PNC.G.CPS PNC.G.TAGS PNC.leaf_chk = true.
Proof. vmc_refl. Qed.
