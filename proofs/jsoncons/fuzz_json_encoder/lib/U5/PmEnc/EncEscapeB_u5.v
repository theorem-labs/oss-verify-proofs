(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5 EncKit_u5 EncSinkBridges_u5 EncEscK_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_escape_string_xsrc_T_u5 Cut_escape_string_xsrc_u5 Cut_escape_string_zero_xsrc_T_u5 Cut_escape_string_zero_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EESB.
Import PMES.
Module G := Cut_escape_string_xsrc_u5.
Module GT := Cut_escape_string_xsrc_T_u5.
Module GZ := Cut_escape_string_zero_xsrc_u5.
Module GZT := Cut_escape_string_zero_xsrc_T_u5.
Abbreviation RSEGS := PML.RSEGS.
Definition RETPC : Z := Eval vm_compute in hd 0 GT.ENDS.
Definition S2E : expr := EVar 32.
Definition QE : expr := EVar 10.
Definition LNE : expr := EVar 11.
Definition KE : expr := EVar 48.
Definition CNTE : expr := EVar 49.
Definition CE : expr := EVar 69.
(* [comment removed for export] *)
Definition ITE : expr := EAlu ALU_ADD (EVar 10) (EAlu ALU_ADD (EVar 11) (EMd M_MUL (ELit (-1)) (EVar 48))).
Definition ENDE : expr := EAlu ALU_ADD (EVar 10) (EVar 11).
Definition CPCE : expr := EAlu ALU_ADD (EVar 2) (ELit (-108)).
Definition SCRW : Z := 8640.                 (* [comment removed for export] *)
Definition F0 : list SGP.region := [(EVar 2, -8640, ELit 8640)].
(* [comment removed for export] *)
Definition PT : list Z := [0; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 2; 2; 1; 1; 2; 2; 2; 1; 2; 2; 2; 2; 2; 3; 3; 3; 4; 4; 4; 5; 5; 5; 6; 6; 6; 6].
Definition P (i : nat) : Z := nth i PT 0.

Lemma heap_ok3 : CH2.heap_chk3 GT.NF G.HDECL G.BLS G.CPS G.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
(* [comment removed for export] *)
Definition ret_j (i k : nat) : option nat := CH2.ret_of G.RETS i k.
Definition call_j (f : CC.cutpoint -> SR.post_spec -> CC.cutpoint -> CA.blocks -> CA.blocks -> option CH2.cinfo) (dP : Z) (i k : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  match ret_j i k with
  | Some j => match nth_error G.CPS j with
              | Some cj => (isSome (f c ps cj (nth i G.BLS []) (nth j G.BLS [])) && Z.eqb (P j) (P i + dP) && Nat.leb 2 j && Nat.leb 86 (CC.cp_nx cj))%bool
              | None => false end
  | None => false
  end.
(* [comment removed for export] *)
Definition byte_facts (cells : list kentry) : bool :=
  (PB.has cells (KWord (SA ITE 0) 1 CE) && PB.has cells (KRange CE 0 255) && PB.has cells (KBlob (SA QE 0) LNE 0))%bool.
(* [comment removed for export] *)
Definition tocp_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  let nx := (CC.cp_nx cj - APC.NCS)%nat in
  if (CH2.blocks_eqb BLj BLi && expr_eqb (nth 10 regs (ELit 0)) ITE && expr_eqb (nth 11 regs (ELit 0)) ENDE && expr_eqb (nth 12 regs (ELit 0)) CPCE &&
      expr_eqb (nth 13 regs (ELit 0)) (ELit 0) && expr_eqb (nth 22 regs (ELit 0)) CE && expr_eqb (nth 2 regs (ELit 0)) (EAlu ALU_ADD (EVar 2) (ELit (-144))))%bool
  then CH2.custom_chk GT.NF G.HDECL 0 0 BLi [(EVar 2, -108, ELit 4)] [KWord (SA (EVar 2) (-108)) 4 CE; KRange (EVar (nx + 5)) 0 0] (Some (APC.eaddz ITE 1)) c ps cj BLi
  else None.

Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in let regs := CA.ps_reglist ps in
  (SP.F_sub (CC.cp_F c) F0 && Nat.leb GT.NF (CC.cp_nx c) && (Nat.eqb i 0 || (Nat.leb 69 (CC.cp_nx c) && (Nat.eqb i 1 || Nat.leb 86 (CC.cp_nx c))))) &&
  match t with
  | CC.TGoto j s =>
      (Nat.eqb j 1 &&
       if Nat.eqb i 0 then (expr_eqb (CC.slook s 48) LNE && expr_eqb (CC.slook s 49) (ELit 0))
       else (byte_facts cells && expr_eqb (CC.slook s 48) (APC.eaddz KE (-1)) && expr_eqb (CC.slook s 49) (APC.eaddz CNTE (P i)) &&
             PB.has cells (KRange KE 2 140737488355328) && EEK.pred_chk 69 cells (fun cv => Z.eqb (esc_cls cv) (P i))))%bool
  | CC.TOther pc =>
      (negb (Nat.eqb i 0) && byte_facts cells &&
       if EEK.contra_chk 69 cells then true
       else if Z.eqb pc PML.PC_STR_PUSH_BACK then
         (Z.eqb (SR.ps_pc ps) PML.PC_STR_PUSH_BACK && call_j (ESB.pushb_chk GT.NF G.HDECL S2E 0) 1 i k c ps)
       else if Z.eqb pc PC_TO_CODEPOINT then
         (Z.eqb (SR.ps_pc ps) PC_TO_CODEPOINT && call_j tocp_chk 0 i k c ps && EEK.pred_chk 69 cells (fun cv => Z.ltb cv 128))
       else (Z.eqb pc RETPC && PB.exit_base_chk GT.NF RETPC c ps && CL.ps_reg_is ps 10 (APC.eaddz CNTE (P i)) && PB.has cells (KRange KE 1 1) &&
             EEK.pred_chk 69 cells (fun cv => Z.eqb (esc_cls cv) (P i))))%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma heap_ok3z : CH2.heap_chk3 GZT.NF GZ.HDECL GZ.BLS GZ.CPS GZ.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Definition leaf_chkz (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  (SP.F_sub (CC.cp_F c) F0 && Nat.leb GZT.NF (CC.cp_nx c)) &&
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc => (Nat.eqb i 0 && Z.eqb pc RETPC && PB.exit_base_chk GZT.NF RETPC c ps && CL.ps_reg_is ps 10 (ELit 0))%bool
  end.
Lemma leaf_okz : CH2.leaves_all GZ.CPS GZ.TAGS leaf_chkz = true.
Proof. vm_compute. reflexivity. Qed.
End EESB.
