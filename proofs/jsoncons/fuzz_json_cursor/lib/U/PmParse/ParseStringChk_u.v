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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSpecs_u ParseBridges_u ParseBridges2_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_ps_csrc_T_u Cut_ps_csrc_D_u Cut_ps_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module PSC.
Module G := Cut_ps_csrc_D_u.
Module GT := Cut_ps_csrc_T_u.
Definition RETPC : Z := 0x3e0d4.
Definition PUSHB : Z := PML.PC_STR_PUSH_BACK.  Definition APPEND : Z := PML.PC_STR_APPEND.  Definition SETEC : Z := PML.PC_SET_EC.  Definition ESV : Z := PML.PC_END_STRING.

Definition Pb : expr := EVar 10.  Definition SEG : expr := EVar 11.  Definition Vb : expr := EVar 12.  Definition Eb : expr := EVar 13.
Definition WLEN : expr := EVar 32.  Definition BX : expr := EVar 33.  Definition SBx : expr := EVar 37.  Definition SLEN : expr := EVar 38.  Definition SCAP : expr := EVar 39.
Definition LVL : expr := EVar 40.  Definition NST : expr := EVar 42.  Definition DONE : expr := EVar 43.
Definition WEND : expr := APC.eadd SEG WLEN.
Definition SCR : Z := 8752.

Inductive kind : Set := KPre | KSetEc | KEsv.
Definition kind_eqb (a b : kind) : bool := match a, b with KPre, KPre | KSetEc, KSetEc | KEsv, KEsv => true | _, _ => false end.
Lemma kind_eqb_eq : forall a b, kind_eqb a b = true -> a = b.
Proof. intros [] [] H; try discriminate; reflexivity. Qed.
Definition kind_of (j : nat) : kind :=
  match find (fun r : nat * nat * nat * Z => let '(j', _, _, _) := r in Nat.eqb j j') G.RETS with
  | Some (_, _, _, pc) => if Z.eqb pc SETEC then KSetEc else if Z.eqb pc ESV then KEsv else KPre
  | None => KPre
  end.

Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition stack_reg_eqb (r : SGP.region) : bool := let '(b, lo, len) := r in (expr_eqb b (EVar 2) && Z.eqb lo (- SCR) && expr_eqb len (ELit SCR))%bool.
Definition pobj_reg_eqb (r : SGP.region) : bool := let '(b, lo, len) := r in (expr_eqb b Pb && Z.eqb lo 0 && expr_eqb len (ELit 272))%bool.

Definition foot_pre_chk (c : CC.cutpoint) : bool := forallb (fun r => (stack_reg_eqb r || pobj_reg_eqb r)%bool) (CC.cp_F c).
Definition foot_esv_chk (c : CC.cutpoint) : bool := forallb stack_reg_eqb (CC.cp_F c).

Definition blk2 (BL : CA.blocks) : option (expr * expr) :=
  match BL with [(pe, ce); (sb, sc)] => if (expr_eqb sb SBx && expr_eqb sc SCAP)%bool then Some (pe, ce) else None | _ => None end.
Definition view_chk (more_lit : Z) (cells : list kentry) (BL : CA.blocks) : option (expr * expr * PB2.pvals) :=
  match blk2 BL with
  | Some (pe, ce) =>
      match PB2.pview cells Pb pe ce SBx SLEN SCAP with
      | Some pv =>
          if (expr_eqb (PB2.pv_st pv) (ELit 15) && expr_eqb (PB2.pv_more pv) (ELit more_lit) && expr_eqb (PB2.pv_done pv) DONE && expr_eqb (PB2.pv_nst pv) NST
              && expr_eqb (PB2.pv_level pv) LVL && expr_eqb (PB2.pv_wptr pv) SEG && expr_eqb (PB2.pv_wend pv) WEND && PB.prove cells (KRange (PB2.pv_sst pv) 0 11))%bool
          then Some (pe, ce, pv) else None
      | None => None
      end
  | None => None
  end.
Definition ESC_NEED : list Z := [0; 0; 0; 1; 2; 3; 0; 0; 0; 1; 2; 3].
Definition need_of (sst : expr) : option Z := match sst with ELit z => if (Z.leb 0 z && Z.leb z 11)%bool then Some (nth (Z.to_nat z) ESC_NEED 0) else None | _ => None end.

Definition cur_chk (cells : list kentry) (a0e se : expr) (need : Z) : bool :=
  (PB.prove cells (KRange (APC.esub a0e SEG) 0 16384) && PB.prove cells (KRange (APC.esub WEND a0e) 0 16384)
   && PB.prove cells (KRange (APC.esub BX (APC.eaddz (APC.eadd se (APC.esub WEND a0e)) need)) 0 67108864))%bool.
Definition progress_chk (cells : list kentry) (a0e : expr) : bool :=
  (PB.prove cells (KRange (APC.esub a0e SEG) 1 16384) || PB.prove cells (KRange (APC.esub WEND a0e) 0 0))%bool.

Definition exit_pre_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in let a0e := nth 10 (CA.ps_reglist ps) (ELit 0) in
  (PB.exit_base_chk GT.NF RETPC c ps && CH2.all_regs_chk ps && foot_pre_chk c && CH2.blocks_vars_lt (CC.cp_nx c) (nth i G.BLS []) &&
   match view_chk 1 cells (nth i G.BLS []) with
   | Some (pe, ce, pv) =>
       match need_of (PB2.pv_sst pv) with
       | Some need => (PB.has cells (KWord (SA Eb 0) 4 (ELit 0)) && cur_chk cells a0e (PB2.pv_size pv) need && progress_chk cells a0e)%bool
       | None => false
       end
   | None => false
   end)%bool.
Definition exit_setec_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in let a0e := nth 10 (CA.ps_reglist ps) (ELit 0) in
  (PB.exit_base_chk GT.NF RETPC c ps && CH2.all_regs_chk ps && foot_pre_chk c && CH2.blocks_vars_lt (CC.cp_nx c) (nth i G.BLS []) &&
   match view_chk 0 cells (nth i G.BLS []) with
   | Some (pe, ce, pv) =>
       match CAX.cell_at cells Eb 0 4 with
       | Some (ELit code) => (Z.leb 1 code && Z.leb code 31 && PB.has cells (KWord (SA Eb 8) 8 (ELit PML.OBJ_JSON_CATEGORY)) && cur_chk cells a0e (PB2.pv_size pv) 0)%bool
       | _ => false
       end
   | None => false
   end)%bool.
Definition ghost_of (c : CC.cutpoint) : nat := (CC.cp_nx c - APC.NCS - 5)%nat.
Definition s1_of (c : CC.cutpoint) : expr := nth 21 (CC.cp_regs c) (ELit 0).
Definition exit_esv_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in let a0e := nth 10 (CA.ps_reglist ps) (ELit 0) in let g := EVar (ghost_of c) in
  (PB.exit_base_chk GT.NF RETPC c ps && CH2.all_regs_chk ps && foot_esv_chk c && CH2.blocks_vars_lt (CC.cp_nx c) (nth i G.BLS []) && APC.expr_vars_lt (CC.cp_nx c) (s1_of c) && Nat.ltb (ghost_of c) (CC.cp_nx c)
   && ((PB.prove cells (KRange g 0 0) && PB.prove cells (KRange (APC.esub a0e (s1_of c)) 1 1)) || (PB.prove cells (KRange g 1 31) && PB.prove cells (KRange (APC.esub a0e (s1_of c)) 0 0))))%bool.

Definition esv_leaf_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) : bool :=
  let cells := SR.ps_cells ps in let regs := CA.ps_reglist ps in
  let s1 := nth 21 regs (ELit 0) in let a1e := nth 11 regs (ELit 0) in let a2e := nth 12 regs (ELit 0) in
  (CH2.blocks_vars_lt (CC.cp_nx c) (nth i G.BLS []) && expr_eqb (nth 10 regs (ELit 0)) Pb && expr_eqb (nth 13 regs (ELit 0)) Vb && expr_eqb (nth 14 regs (ELit 0)) Eb && expr_eqb (s1_of cj) s1 &&
   match view_chk 1 cells (nth i G.BLS []) with
   | Some (pe, ce, pv) =>
       (PB.has cells (KWord (SA Eb 0) 4 (ELit 0)) && PB.has cells (KWord (SA Vb 0) 8 (ELit PML.VT_VISITOR)) && PB.has cells (KUnk (SA SEG 0) WLEN)
        && PB.prove cells (KRange (APC.esub s1 SEG) 0 16384) && PB.prove cells (KRange (APC.esub WEND s1) 1 16384)
        && PB.prove cells (KRange (APC.esub BX (APC.eadd (PB2.pv_size pv) (APC.esub WEND s1))) 0 67108864)
        && ((expr_eqb a1e pe && expr_eqb a2e (PB2.pv_size pv))
            || (PB.prove cells (KRange (APC.esub a1e SEG) 0 16384) && PB.prove cells (KRange (APC.esub WEND (APC.eadd a1e a2e)) 0 16384) && PB.prove cells (KRange a2e 0 16384)

                && PB.prove cells (KRange (APC.esub s1 a1e) 0 16384) && PB.prove cells (KRange (APC.esub BX (APC.eadd (PB2.pv_size pv) (APC.esub WEND a1e))) 0 67108864))))%bool
   | None => false
   end)%bool.

Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto j _ => (kind_eqb (kind_of i) KPre && kind_eqb (kind_of j) KPre && foot_pre_chk c)%bool
  | CC.TOther pc =>
      if Z.eqb pc RETPC then
        match kind_of i with KPre => exit_pre_chk i c ps | KSetEc => exit_setec_chk i c ps | KEsv => exit_esv_chk i c ps end
      else
        (kind_eqb (kind_of i) KPre && foot_pre_chk c && Z.eqb (SR.ps_pc ps) pc &&
         match CH2.ret_of G.RETS i k with
         | Some j => match nth_error G.CPS j with
                     | Some cj =>
                         if Z.eqb pc PUSHB then (kind_eqb (kind_of j) KPre && isSome (PB.pushb_chk GT.NF G.HDECL Pb 224 132 c ps cj (nth i G.BLS []) (nth j G.BLS [])))%bool
                         else if Z.eqb pc APPEND then (kind_eqb (kind_of j) KPre && isSome (PB.appendb_chk GT.NF G.HDECL Pb 224 SEG WLEN 132 c ps cj (nth i G.BLS []) (nth j G.BLS [])))%bool
                         else if Z.eqb pc SETEC then (kind_eqb (kind_of j) KSetEc && isSome (PB2.setec_chk GT.NF G.HDECL Eb 0 c ps cj (nth i G.BLS []) (nth j G.BLS [])))%bool
                         else if Z.eqb pc ESV then (kind_eqb (kind_of j) KEsv && isSome (PB2.ptrans_chkc GT.NF G.HDECL Eb 0 Pb 0 512 Vb 0 14 c ps cj (nth i G.BLS []) (nth j G.BLS []))
                                                    && esv_leaf_chk i c ps cj)%bool
                         else false
                     | None => false end
         | None => false end)%bool
  end.
End PSC.

Lemma heap_ok3 : CH2.heap_chk3 PSC.GT.NF PSC.G.HDECL PSC.G.BLS PSC.G.CPS PSC.G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma leaf_ok : CH2.leaves_all PSC.G.CPS PSC.G.TAGS PSC.leaf_chk = true.
Proof. vmc_refl. Qed.
