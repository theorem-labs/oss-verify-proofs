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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSums_u5 ParseSums2_u5 ParseSums2X_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSpecs_u5 ParseBridges_u5 ParseBridges2_u5 ParseBridges3_u5 ParseBridges4_u5 ParseBridgesX_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmEncSpecs_u5 PmLibSpecsX_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallKnX VisitSumsX. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmall Require Import VisitBridgeX_u5.      (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_psome_xsrcw_T_u5 Cut_psome_xsrcw_D_u5 Cut_psome_xsrcw_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PSMC.
Module G := Cut_psome_xsrcw_D_u5.
Module GT := Cut_psome_xsrcw_T_u5.
(* [comment removed for export] *)
Definition RETPC : Z := 0x48bc4.  Definition DEADPC : Z := 0x48bc8.  Definition L0PC : Z := 0x47cb4.  Definition HPC : Z := 0x47cdc.  Definition LPC : Z := 0x4873c.  Definition L2PC : Z := 0x4803c.
(* [comment removed for export] *)
Definition I_ENTRY := 0%nat.  Definition I_L0 := 1%nat.  Definition I_HLO := 2%nat.  Definition I_HHI := 3%nat.  Definition I_HN := 4%nat.  Definition I_L := 5%nat.  Definition I_L2 := 6%nat.  Definition I_L0X := 7%nat.
Definition I_HS := 8%nat.      (* [comment removed for export] *)
Definition VECPUSH : Z := PML.PC_VEC_PUSH.  Definition PUSHB : Z := PML.PC_STR_PUSH_BACK.  Definition POP : Z := PML.PC_POP_STATE.  Definition PARENT : Z := PML.PC_PARENT.  Definition SETEC : Z := PML.PC_SET_EC.
(* [comment removed for export] *)
Definition VNULL : Z := PMES.PC_VISIT_NULL.  Definition VBOOL : Z := PMES.PC_VISIT_BOOL.  Definition VIS_SCR : Z := 10624.  Definition LIT_LO : Z := PML.LIT_LO.
(* [comment removed for export] *)
Definition PF_SCR : Z := 9968.  Definition PFX_SCR : Z := 12672.  Definition ENDNUMX_SCR : Z := 11136.      (* [comment removed for export] *)
Definition PTS : list (Z * (Z * nat * bool)) :=
  [(PML.PC_SKIP_SPACE, (PF_SCR, 8%nat, false)); (PML.PC_BEGIN_MEMBER, (PF_SCR, 11%nat, false));
   (PML.PC_BEGIN_OBJECT, (PFX_SCR, 12%nat, true)); (PML.PC_BEGIN_ARRAY, (PFX_SCR, 12%nat, true)); (PML.PC_END_OBJECT, (PFX_SCR, 12%nat, true)); (PML.PC_END_ARRAY, (PFX_SCR, 12%nat, true)); (PML.PC_PARSE_NULL, (PFX_SCR, 12%nat, true));
   (PML.PC_PARSE_STRING, (PFX_SCR, 13%nat, true)); (PML.PC_PARSE_NUMBER, (PFX_SCR, 13%nat, true)); (PML.PC_PARSE_TRUE, (PFX_SCR, 13%nat, true)); (PML.PC_PARSE_FALSE, (PFX_SCR, 13%nat, true));
   (PML.PC_END_INT, (ENDNUMX_SCR, 12%nat, true)); (PML.PC_END_FRAC, (ENDNUMX_SCR, 12%nat, true))].
Definition pt_of (pc : Z) : option (Z * nat * bool) := match find (fun x : Z * (Z * nat * bool) => Z.eqb (fst x) pc) PTS with Some x => Some (snd x) | None => None end.
(* [comment removed for export] *)
Definition Pb : expr := EVar 10.  Definition Vb : expr := EVar 11.  Definition Eb : expr := EVar 12.  Definition SEG : expr := EVar 32.  Definition WLEN : expr := EVar 33.
Definition WEND : expr := APC.eadd SEG WLEN.

Inductive kind : Set := KInv | KErr | KVec | KPushB | KPop | KParent | KSetEc | KPt | KVis.
Definition kind_eqb (a b : kind) : bool :=
  match a, b with KInv, KInv | KErr, KErr | KVec, KVec | KPushB, KPushB | KPop, KPop | KParent, KParent | KSetEc, KSetEc | KPt, KPt | KVis, KVis => true | _, _ => false end.
Lemma kind_eqb_eq : forall a b, kind_eqb a b = true -> a = b.
Proof. intros [] [] H; try discriminate; reflexivity. Qed.
Definition ret_src (j : nat) : option (nat * nat * Z) :=
  match find (fun r : nat * nat * nat * Z => let '(j', _, _, _) := r in Nat.eqb j j') G.RETS with Some (_, i, k, pc) => Some (i, k, pc) | None => None end.
Definition kind_of (j : nat) : kind :=
  match ret_src j with
  | Some (_, _, pc) => if Z.eqb pc VECPUSH then KVec else if Z.eqb pc PUSHB then KPushB else if Z.eqb pc POP then KPop else if Z.eqb pc PARENT then KParent else if Z.eqb pc SETEC then KSetEc else if (Z.eqb pc VNULL || Z.eqb pc VBOOL)%bool then KVis else KPt
  | None => if Nat.eqb j I_L0X then KErr else KInv
  end.
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.

(* [comment removed for export] *)
Definition pop_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in let nx := (CC.cp_nx cj - APC.NCS - 1)%nat in
  match CAX.cell_at (SR.ps_cells ps) Pb 256 8 with
  | Some c8 => if (expr_eqb (nth 10 regs (ELit 0)) Pb && CH2.blocks_eqb BLj BLi)%bool
               then CH2.custom_chk GT.NF G.HDECL 48 1 BLi [(Pb, 256, ELit 8)] [KWord (SA Pb 256) 8 (APC.eaddz c8 (-1)); KRange (EVar nx) 0 255] (Some (EVar nx)) c ps cj BLi
               else None
  | None => None
  end.
Definition parent_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in let nx := (CC.cp_nx cj - APC.NCS - 1)%nat in
  if (expr_eqb (nth 10 regs (ELit 0)) Pb && CH2.blocks_eqb BLj BLi)%bool
  then CH2.custom_chk GT.NF G.HDECL 48 1 BLi [] [KRange (EVar nx) 0 255] (Some (EVar nx)) c ps cj BLi
  else None.

(* [comment removed for export] *)
Definition call_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (pc : Z) : bool :=
  match CH2.ret_of G.RETS i k with
  | Some j =>
      match nth_error G.CPS j with
      | Some cj =>
          let BLi := nth i G.BLS [] in let BLj := nth j G.BLS [] in
          (Z.eqb (SR.ps_pc ps) pc &&
           (if Z.eqb pc VECPUSH then isSome (PB4.vecpush_chk GT.NF G.HDECL Pb 248 c ps cj BLi BLj)
            else if Z.eqb pc PUSHB then isSome (PB4.pushbc_chk GT.NF G.HDECL Pb 224 132 c ps cj BLi BLj)
            else if Z.eqb pc POP then isSome (pop_chk c ps cj BLi BLj)
            else if Z.eqb pc PARENT then isSome (parent_chk c ps cj BLi BLj)
            else if Z.eqb pc SETEC then isSome (PB2.setec_chk GT.NF G.HDECL Eb 0 c ps cj BLi BLj)
            else if (Z.eqb pc VNULL || Z.eqb pc VBOOL)%bool then isSome (VBX.vis_chk GT.NF G.HDECL Vb c ps cj BLi BLj)      (* [comment removed for export] *)
            else match pt_of pc with
                 | Some (scr, ereg, false) => isSome (PB2.ptrans_chk GT.NF G.HDECL Eb 0 Pb 0 scr ereg c ps cj BLi BLj)
                 | Some (scr, ereg, true) => isSome (PBX.ptrans_chkx GT.NF G.HDECL Eb 0 Pb 0 scr Vb LIT_LO ereg c ps cj BLi BLj)      (* [comment removed for export] *)
                 | None => false
                 end))%bool
      | None => false
      end
  | None => (Z.eqb pc SETEC && Nat.eqb i 0)%bool      (* [comment removed for export] *)
  end.
Definition is_exit_pc (pc : Z) : bool := (Z.eqb pc RETPC || Z.eqb pc DEADPC || Z.eqb pc L0PC || Z.eqb pc HPC || Z.eqb pc LPC || Z.eqb pc L2PC)%bool.
Definition struct_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto j _ => true
  | CC.TOther pc => if is_exit_pc pc then Z.eqb (SR.ps_pc ps) pc else call_chk i c k ps pc
  end.
(* [comment removed for export] *)
Definition CONSTS : PSK.consts := PSK.CONSTS 803024 804528 803536 65536 1040384 65536 827984 12800 [(-8, 1%nat); (-16, 8%nat); (-24, 9%nat); (-32, 18%nat); (-40, 19%nat); (-48, 20%nat); (-56, 21%nat); (-64, 22%nat); (-72, 23%nat); (-80, 24%nat); (-88, 25%nat); (-96, 26%nat)] 96.
(* [comment removed for export] *)
Definition FRZ : list kentry := List.filter (fun X => match X with KUnk (SA (EVar 2) _) _ => false | _ => true end) (PSK.pkn_frz CONSTS true Pb Vb Eb (EVar 2) SEG WLEN).
Definition target_of (pc : Z) : nat := if Z.eqb pc L0PC then I_L0 else if Z.eqb pc HPC then I_HLO else if Z.eqb pc LPC then I_L else I_L2.
Definition live_reg_chk (tr lr : expr) : bool := match tr with EVar n => if Nat.leb GT.NF n then true else expr_eqb tr lr | _ => (APC.expr_vars_lt GT.NF tr && expr_eqb tr lr)%bool end.
Definition reent_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      if (Z.eqb pc L0PC || Z.eqb pc HPC || Z.eqb pc LPC || Z.eqb pc L2PC)%bool then
        let cj := nth (target_of pc) G.CPS CA.dummy_cp in
        (forallb (fun X => (PB.has (SR.ps_cells ps) X && APC.kentry_vars_lt GT.NF X)%bool) FRZ
         && forallb (fun r => if Z.eqb pc HPC then (if Nat.eqb r 11 then true else live_reg_chk (nth r (CC.cp_regs cj) (ELit 0)) (nth r (CA.ps_reglist ps) (ELit 0)))
                              else live_reg_chk (nth r (CC.cp_regs cj) (ELit 0)) (nth r (CA.ps_reglist ps) (ELit 0))) (seq 1 31))%bool
      else true
  | _ => true
  end.
(* [comment removed for export] *)
Definition fails (chk : nat -> CC.cutpoint -> nat -> SR.post_spec -> CC.tag -> bool) : list (nat * nat * Z) :=
  flat_map (fun ic : nat * (CC.cutpoint * list CC.tag) => let '(i, (c, tags)) := ic in
            flat_map (fun kpt : nat * (SR.post_spec * CC.tag) => let '(k, (ps, t)) := kpt in
                      if chk i c k ps t then [] else [(i, k, match t with CC.TGoto j _ => Z.of_nat j | CC.TOther pc => pc end)])
                     (combine (seq 0 (length tags)) (combine (CC.cp_PSS c) tags)))
           (combine (seq 0 (length G.CPS)) (combine G.CPS G.TAGS)).
End PSMC.
(* [comment removed for export] *)
Lemma heap_ok3 : CH2.heap_chk3 PSMC.GT.NF PSMC.G.HDECL PSMC.G.BLS PSMC.G.CPS PSMC.G.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma reent_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS PSMC.reent_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma struct_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS PSMC.struct_chk = true.
Proof. vm_compute. reflexivity. Qed.
