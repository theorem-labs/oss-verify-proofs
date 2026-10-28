(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core StreamSim. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncKit_u5 EncBridges_u5 EncHtrans_u5 EncTail_u5 EncVisitNullB_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_visit_string_nested_xsrc_T_u5 Cut_visit_string_nested_xsrc_u5 Cut_visit_string_root_xsrc_T_u5 Cut_visit_string_root_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EVStrB.
Import PMES.
(* [comment removed for export] *)
Import EVNB.
Module GN := Cut_visit_string_nested_xsrc_u5.  Module GNT := Cut_visit_string_nested_xsrc_T_u5.
Module GR := Cut_visit_string_root_xsrc_u5.    Module GRT := Cut_visit_string_root_xsrc_T_u5.
Abbreviation RSEGS := PML.RSEGS.
Definition RETPC : Z := Eval vm_compute in hd 0 GNT.ENDS.
Definition VSCR : Z := 1024 + Z.max STRX_SCR WD_SCR_X.   (* [comment removed for export] *)
Definition WSSCR : Z := 8704.        (* [comment removed for export] *)
(* [comment removed for export] *)
Definition NEWS_WS : list kentry :=
  [KWord (SA ENDE (-32)) 4 (EVar 38); KWord (SA ENDE (-28)) 1 (ELit 0); KWord (SA ENDE (-8)) 8 (EVar 36); KWr (SA ENDE (-8)) (ELit 8); KUnk (SA ENDE (-32)) (ELit 32)].

Lemma heap_ok3n : CH2.heap_chk3 GNT.NF GN.HDECL GN.BLS GN.CPS GN.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma heap_ok3r : CH2.heap_chk3 GRT.NF GR.HDECL GR.BLS GR.CPS GR.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

(* [comment removed for export] *)
Definition PA (i : nat) : bool := match i with 1 | 3 => true | _ => false end%nat.
Definition FI (i : nat) : bool := match i with 2 | 3 => true | _ => false end%nat.

Definition leaf_chkn (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in let regs := CA.ps_reglist ps in
  (SP.F_sub (CC.cp_F c) F0N && Nat.leb GNT.NF (CC.cp_nx c) && CH2.blocks_eqb (nth i GN.BLS []) BL1 &&
   PB.has cells (KRange (EVar 38) (if PA i || (Nat.eqb i 0 && Z.eqb (SR.ps_pc ps) PC_BEGIN_SCALAR) then 1 else 0)%bool (if PA i || (Nat.eqb i 0 && Z.eqb (SR.ps_pc ps) PC_BEGIN_SCALAR) then 1 else 0)%bool) &&
   PB.has cells (KWord (SA ENDE (-8)) 8 (if Z.eqb (SR.ps_pc ps) RETPC then EAlu ALU_ADD (EVar 36) (ELit 1) else EVar 36))) &&
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if Z.eqb pc PC_BEGIN_SCALAR then
        (Nat.eqb i 0 && Z.eqb (SR.ps_pc ps) PC_BEGIN_SCALAR && call_j GN.RETS GN.CPS GN.BLS (EHT.hcall_chk GNT.NF GN.HDECL S2E BSSCR NEWS_BS) (fun j cj => Nat.eqb j 1 && Nat.leb 64 (CC.cp_nx cj))%bool i k c ps &&
         PB.has cells (KWord (SA ENDE (-26)) 1 (EVar 40)))%bool
      else if Z.eqb pc PC_WRITE_STRING then
        (Z.eqb (SR.ps_pc ps) PC_WRITE_STRING && negb (FI i) &&
         call_j GN.RETS GN.CPS GN.BLS (EHT.hcall_chk GNT.NF GN.HDECL S2E WSSCR NEWS_WS) (fun j cj => Bool.eqb (PA j) (PA i) && FI j && Nat.leb 64 (CC.cp_nx cj) && negb (Nat.eqb j 0))%bool i k c ps &&
         expr_eqb (nth 11 regs (ELit 0)) (EVar 11) && expr_eqb (nth 12 regs (ELit 0)) (EVar 12) &&
         PB.has cells (KWord (SA ENDE (-26)) 1 (if PA i then ELit 1 else EVar 40)))%bool
      else
        (Z.eqb pc RETPC && FI i && PB.exit_base_chk GNT.NF RETPC c ps && CL.ps_reg_is ps 10 (ELit 1) &&
         PB.has cells (KWord (SA ENDE (-8)) 8 (EAlu ALU_ADD (EVar 36) (ELit 1))) &&
         PB.has cells (KWord (SA ENDE (-32)) 4 (EVar 38)) && PB.has cells (KWord (SA ENDE (-28)) 1 (ELit 0)))%bool
  end.
Lemma leaf_okn : CH2.leaves_all GN.CPS GN.TAGS leaf_chkn = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition FIr (i : nat) : bool := Nat.leb 1 i.
Definition leaf_chkr (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in let regs := CA.ps_reglist ps in
  (SP.F_sub (CC.cp_F c) F0R && Nat.leb GRT.NF (CC.cp_nx c) && CH2.blocks_eqb (nth i GR.BLS []) []) &&
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if Z.eqb pc PC_WRITE_STRING then
        (Z.eqb (SR.ps_pc ps) PC_WRITE_STRING && Nat.eqb i 0 &&
         call_j GR.RETS GR.CPS GR.BLS (EHT.hcall_chk GRT.NF GR.HDECL S2E WSSCR []) (fun j cj => Nat.eqb j 1 && Nat.leb 64 (CC.cp_nx cj))%bool i k c ps &&
         expr_eqb (nth 11 regs (ELit 0)) (EVar 11) && expr_eqb (nth 12 regs (ELit 0)) (EVar 12))%bool
      else
        (Z.eqb pc RETPC && Nat.eqb i 1 && PB.exit_base_chk GRT.NF RETPC c ps && CL.ps_reg_is ps 10 (ELit 1))%bool
  end.
Lemma leaf_okr : CH2.leaves_all GR.CPS GR.TAGS leaf_chkr = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma pow2_10 : forall k, 0 <= k <= 10 -> 32 <= 32 * 2 ^ k <= 32768.
Proof.
  intros k Hk. assert (1 <= 2 ^ k) by (apply (Z.pow_le_mono_r 2 0 k); lia). assert (2 ^ k <= 2 ^ 10) by (apply Z.pow_le_mono_r; lia). change (2 ^ 10) with 1024 in *. lia.
Qed.
Lemma custom_chk_nx : forall NF d scr ng BLk wregs news a0x c ps cj BLi ci,
  CH2.custom_chk NF d scr ng BLk wregs news a0x c ps cj BLi = Some ci -> CH2.ci_nx ci = (CC.cp_nx cj - APC.NCS - ng)%nat.
Proof.
  intros NF d scr ng BLk wregs news a0x c ps cj BLi ci H. unfold CH2.custom_chk in H.
  destruct (CH2.common_chk_x NF d scr ng c ps cj BLi) as [ci0|] eqn:Hc; [|discriminate].
  lazymatch type of H with (if ?b then _ else _) = _ => destruct b; [|discriminate] end. injection H as <-.
  unfold CH2.common_chk_x in Hc. destruct (nth 1 (CA.ps_reglist ps) (ELit 0)); try discriminate.
  destruct (split_lit (nth 2 (CA.ps_reglist ps) (ELit 0))) as [eb csp]. destruct eb; try discriminate. destruct n as [|[|[|n]]]; try discriminate.
  lazymatch type of Hc with (if ?b then _ else _) = _ => destruct b; [|discriminate] end. injection Hc as <-. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma sv_outside_Wh : forall (L : heap_layout) (sp sv V S2 : Z),
  PML.apart sv 16 V ENC_SIZE -> PML.apart sv 16 S2 24 -> objs_enc L sp V S2 -> hl_sptop L - 2 ^ 23 + 10624 <= sp ->
  forall a, (sv <= a < sv + 16 \/ a < hl_ceil L) -> L5.outside (W_h V S2) a.
Proof.
  intros L sp sv V S2 AV AS ((O1 & _) & (O2 & _) & _) K a Ha w [<-|[<-|[]]]; unfold L5.in_rng, O_COLUMN, PML.apart, ENC_SIZE in *; cbn [fst snd]; lia.
Qed.
End EVStrB.
