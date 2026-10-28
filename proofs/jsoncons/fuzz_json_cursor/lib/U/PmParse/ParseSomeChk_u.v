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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums2_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSpecs_u ParseBridges_u ParseBridges2_u ParseBridges3_u ParseBridges4_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import VisitSums.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_psome_csrc_T_u Cut_psome_csrc_D_u Cut_psome_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module PSMC.
Module G := Cut_psome_csrc_D_u.
Module GT := Cut_psome_csrc_T_u.

Definition RETPC : Z := 0x3d588.  Definition DEADPC : Z := 0x3d58c.  Definition L0PC : Z := 0x3c678.  Definition HPC : Z := 0x3c6a0.  Definition LPC : Z := 0x3d100.  Definition L2PC : Z := 0x3ca00.

Definition I_ENTRY := 0%nat.  Definition I_L0 := 1%nat.  Definition I_HLO := 2%nat.  Definition I_HHI := 3%nat.  Definition I_HN := 4%nat.  Definition I_L := 5%nat.  Definition I_L2 := 6%nat.  Definition I_L0X := 7%nat.
Definition VECPUSH : Z := PML.PC_VEC_PUSH.  Definition PUSHB : Z := PML.PC_STR_PUSH_BACK.  Definition POP : Z := PML.PC_POP_STATE.  Definition PARENT : Z := PML.PC_PARENT.  Definition SETEC : Z := PML.PC_SET_EC.

Definition VNULL : Z := PMS.PC_VIS_NULL.  Definition VBOOL : Z := PMS.PC_VIS_BOOL.

Definition PF_SCR : Z := 9968.  Definition ENDNUM_SCR : Z := 9456.
Definition PTS : list (Z * (Z * nat)) :=
  [(PML.PC_SKIP_SPACE, (PF_SCR, 8%nat)); (PML.PC_BEGIN_MEMBER, (PF_SCR, 11%nat));
   (PML.PC_BEGIN_OBJECT, (PF_SCR, 12%nat)); (PML.PC_BEGIN_ARRAY, (PF_SCR, 12%nat)); (PML.PC_END_OBJECT, (PF_SCR, 12%nat)); (PML.PC_END_ARRAY, (PF_SCR, 12%nat)); (PML.PC_PARSE_NULL, (PF_SCR, 12%nat));
   (PML.PC_PARSE_STRING, (PF_SCR, 13%nat)); (PML.PC_PARSE_NUMBER, (PF_SCR, 13%nat)); (PML.PC_PARSE_TRUE, (PF_SCR, 13%nat)); (PML.PC_PARSE_FALSE, (PF_SCR, 13%nat));
   (PML.PC_END_INT, (ENDNUM_SCR, 12%nat)); (PML.PC_END_FRAC, (ENDNUM_SCR, 12%nat))].
Definition pt_of (pc : Z) : option (Z * nat) := match find (fun x : Z * (Z * nat) => Z.eqb (fst x) pc) PTS with Some x => Some (snd x) | None => None end.

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

Definition vis_news (pc : Z) (regs : list expr) : list kentry := if Z.eqb pc VNULL then VSU.const_news Vb 0 4 else VSU.bool_news Vb 0 (nth 11 regs (ELit 0)).
Definition vis_chk (pc : Z) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  if (expr_eqb (nth 10 regs (ELit 0)) Vb && CH2.blocks_eqb BLj BLi && PB.has (SR.ps_cells ps) (KWord (SA Vb 0) 8 (ELit PML.VT_VISITOR)))%bool
  then CH2.custom_chk GT.NF G.HDECL PMS.VIS_SCR 0 BLi [(Vb, 8, ELit 40)] (vis_news pc regs) (Some (ELit 1)) c ps cj BLi
  else None.

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
            else if (Z.eqb pc VNULL || Z.eqb pc VBOOL)%bool then (match vis_chk pc c ps cj BLi BLj with Some ci => Nat.leb (CC.cp_nx c) (CH2.ci_nx ci) | None => false end)
            else match pt_of pc with
                 | Some (scr, ereg) => isSome (PB2.ptrans_chkc GT.NF G.HDECL Eb 0 Pb 0 scr Vb 0 ereg c ps cj BLi BLj)
                 | None => false
                 end))%bool
      | None => false
      end
  | None => (Z.eqb pc SETEC && Nat.eqb i 0)%bool
  end.
Definition is_exit_pc (pc : Z) : bool := (Z.eqb pc RETPC || Z.eqb pc DEADPC || Z.eqb pc L0PC || Z.eqb pc HPC || Z.eqb pc LPC || Z.eqb pc L2PC)%bool.
Definition struct_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto j _ => true
  | CC.TOther pc => if is_exit_pc pc then Z.eqb (SR.ps_pc ps) pc else call_chk i c k ps pc
  end.

Definition CONSTS : PSK.consts := PSK.CONSTS 776856 777808 778104 65536 1015808 65536 801400 10096 [(-8, 1%nat); (-16, 8%nat); (-24, 9%nat); (-32, 18%nat); (-40, 19%nat); (-48, 20%nat); (-56, 21%nat); (-64, 22%nat); (-72, 23%nat); (-80, 24%nat); (-88, 25%nat); (-96, 26%nat)] 96.

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

Definition fails (chk : nat -> CC.cutpoint -> nat -> SR.post_spec -> CC.tag -> bool) : list (nat * nat * Z) :=
  flat_map (fun ic : nat * (CC.cutpoint * list CC.tag) => let '(i, (c, tags)) := ic in
            flat_map (fun kpt : nat * (SR.post_spec * CC.tag) => let '(k, (ps, t)) := kpt in
                      if chk i c k ps t then [] else [(i, k, match t with CC.TGoto j _ => Z.of_nat j | CC.TOther pc => pc end)])
                     (combine (seq 0 (length tags)) (combine (CC.cp_PSS c) tags)))
           (combine (seq 0 (length G.CPS)) (combine G.CPS G.TAGS)).
End PSMC.

Lemma heap_ok3 : CH2.heap_chk3 PSMC.GT.NF PSMC.G.HDECL PSMC.G.BLS PSMC.G.CPS PSMC.G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma reent_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS PSMC.reent_chk = true.
Proof. vmc_refl. Qed.
Lemma struct_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS PSMC.struct_chk = true.
Proof. vmc_refl. Qed.
