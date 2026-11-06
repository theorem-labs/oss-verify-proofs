(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm5PlanKit Pm5L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutHeapV CutShA CutShB CutShC.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncSumsXB EncSums3XB EncSinkBridgesXB EncEscKXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_escape_string_xboth_T Cut_escape_string_xboth Cut_escape_string_zero_xboth_T Cut_escape_string_zero_xboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EESBA.
Import PMES.
Module G := Cut_escape_string_xboth.
Module GT := Cut_escape_string_xboth_T.
Module GZ := Cut_escape_string_zero_xboth.
Module GZT := Cut_escape_string_zero_xboth_T.
Abbreviation RSEGS := Pm5PlanKit.RSEGS.

Definition PC_ESCAPE : Z := 785716.           (* [comment removed for export] *)
Definition PC_PUSHB : Z := 1056004.           (* [comment removed for export] *)
Definition PC_TOCP : Z := 822120.             (* [comment removed for export] *)
Definition RETPC : Z := Eval vm_compute in hd 0 GT.ENDS.      (* [comment removed for export] *)
Definition SHLB : Z := 785876.                (* [comment removed for export] *)
Definition SBz : Z := 2147450880.
Definition S2E : expr := EVar 32.
Definition QE : expr := EVar 10.
Definition LNE : expr := EVar 11.
Definition BE : expr := EVar 33.              (* [comment removed for export] *)
Definition GE : expr := EVar 34.              (* [comment removed for export] *)
Definition KE : expr := EVar 48.
Definition CNTE : expr := EVar 49.
Definition CE : expr := EVar 68.              (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ITE : expr := EAlu ALU_ADD (EVar 10) (EAlu ALU_ADD (EVar 11) (EMd M_MUL (ELit (-1)) (EVar 48))).
Definition ENDE : expr := EAlu ALU_ADD (EVar 10) (EVar 11).
Definition CPCE : expr := EAlu ALU_ADD (EVar 2) (ELit (-108)).
Definition SCRW : Z := 4528.                 (* [comment removed for export] *)
Definition F0 : list SGP.region := [(EVar 2, -4528, ELit 4528)].
Definition FFS : list (list (expr * Z * Z)) := map (fun _ => @nil (expr * Z * Z)) (seq 0 39).
Definition STAT : list kentry := ESA.STATICS.
(* [comment removed for export] *)
Definition PT : list Z := [0; 0; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 2; 2; 1; 1; 2; 2; 2; 1; 2; 2; 2; 2; 2; 3; 3; 3; 4; 4; 4; 5; 5; 5; 6; 6; 6; 6].
Definition P (i : nat) : Z := nth i PT 0.

Lemma heap_okA : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stat_ok : forallb (CHA.static_chk GT.SCELLS GT.GLO GT.GHI) STAT = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
Lemma bls_i : forall i, nth i G.BLS [] = [].
Proof. intros i. unfold G.BLS. do 39 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Lemma ffs_i : forall i, nth i FFS [] = [].
Proof. intros i. unfold FFS. do 39 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Lemma NF_48 : GT.NF = 48%nat. Proof. reflexivity. Qed.

Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.
(* [comment removed for export] *)
Definition ret_j (i k : nat) : option nat := CH2.ret_of G.RETS i k.
Definition call_j (f : CC.cutpoint -> SR.post_spec -> CC.cutpoint -> CA.blocks -> list (expr * Z * Z) -> CA.blocks -> list (expr * Z * Z) -> option CH2.cinfo)
           (dP : Z) (i k : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  match ret_j i k with
  | Some j => match nth_error G.CPS j with
              | Some cj => (isSome (f c ps cj (nth i G.BLS []) (nth i FFS []) (nth j G.BLS []) (nth j FFS [])) && Z.eqb (P j) (P i + dP) && Nat.leb 3 j && Nat.leb 85 (CC.cp_nx cj))%bool
              | None => false end
  | None => false
  end.
(* [comment removed for export] *)
Definition blob_fact (cells : list kentry) : bool := has cells (KBlob (SA QE 0) LNE 0).
Definition byte_facts (cells : list kentry) : bool :=
  (has cells (KWord (SA ITE 0) 1 CE) && has cells (KRange CE 0 255) && blob_fact cells)%bool.
(* [comment removed for export] *)
Definition pushb_chk := ESBA.pushb_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI STAT S2E [].
(* [comment removed for export] *)
Definition tocp_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi : CA.blocks) (FFi : list (expr * Z * Z)) (BLj : CA.blocks) (FFj : list (expr * Z * Z)) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  let nx := (CC.cp_nx cj - APC.NCS)%nat in
  if (CH2.blocks_eqb BLj BLi && CHA.frames_eqb FFj FFi && expr_eqb (nth 10 regs (ELit 0)) ITE && expr_eqb (nth 11 regs (ELit 0)) ENDE && expr_eqb (nth 12 regs (ELit 0)) CPCE &&
      expr_eqb (nth 13 regs (ELit 0)) (ELit 0) && expr_eqb (nth 22 regs (ELit 0)) CE && expr_eqb (nth 2 regs (ELit 0)) (EAlu ALU_ADD (EVar 2) (ELit (-160))))%bool
  then CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 16 0 BLi FFi [(EVar 2, -112, ELit 8)] (KWord (SA (EVar 2) (-108)) 4 CE :: KRange (EVar (nx + 5)) 0 0 :: STAT) (Some (APC.eaddz ITE 1)) c ps cj BLi FFi BLj FFj
  else None.
(* [comment removed for export] *)
Definition SID : CC.subst := map (fun k => (k, EVar k)) (seq 48 20).
Definition ROW1 : CSLR.row := CSLR.ROW 1 SHLB 2 SID 10 10 ITE 64 62 false.
Definition KZB : kentry := KZero (SA (EAlu ALU_SRL BE (ELit 3)) SBz) GE.
Definition LENB : Z := 1099511627776.        (* [comment removed for export] *)
Definition row_chk := CSLR.row_chk GT.NF G.HDECL G.CPS G.BLS FFS F0 SBz 48 QE ENDE LENB KZB 0 0 (KZero (SA (ELit 0) SBz) (ELit 0)).   (* [comment removed for export] *)
Lemma sites_ok : CSLR.sites_ok RSEGS [ROW1] = true.
Proof. vm_compute. reflexivity. Qed.

Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in let regs := CA.ps_reglist ps in
  (CBA.regions_eqb (CC.cp_F c) F0 && Nat.leb GT.NF (CC.cp_nx c) && (Nat.eqb i 0 || (Nat.leb 68 (CC.cp_nx c) && (Nat.leb i 2 || Nat.leb 85 (CC.cp_nx c)))) && blob_fact cells &&
   CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS [])) &&
  match t with
  | CC.TGoto j s =>
      (Nat.eqb j 1 &&
       if Nat.eqb i 0 then (expr_eqb (CC.slook s 48) LNE && expr_eqb (CC.slook s 49) (ELit 0))
       else (Nat.leb 3 i && byte_facts cells && expr_eqb (CC.slook s 48) (APC.eaddz KE (-1)) && expr_eqb (CC.slook s 49) (APC.eaddz CNTE (P i)) &&
             has cells (KRange KE 2 1099511627776) && EEK.pred_chk 68 cells (fun cv => Z.eqb (esc_cls cv) (P i))))%bool
  | CC.TOther pc =>
      if Nat.eqb i 1 then (Z.eqb pc SHLB && row_chk i c ps ROW1)%bool
      else
      (Nat.leb 2 i && byte_facts cells &&
       if EEK.contra_chk 68 cells then true
       else if Z.eqb pc PC_PUSHB then
         (Z.eqb (SR.ps_pc ps) PC_PUSHB && call_j pushb_chk 1 i k c ps && EEK.pred_chk 68 cells (fun cv => Z.ltb (P i) (esc_cls cv)))      (* [comment removed for export] *)
       else if Z.eqb pc PC_TOCP then
         (Z.eqb (SR.ps_pc ps) PC_TOCP && call_j tocp_chk 0 i k c ps && EEK.pred_chk 68 cells (fun cv => Z.ltb cv 128))
       else (Z.eqb pc RETPC && CBA.exit_base_chk GT.NF RETPC c ps && CL.ps_reg_is ps 10 (APC.eaddz CNTE (P i)) && has cells (KRange KE 1 1) &&
             EEK.pred_chk 68 cells (fun cv => Z.eqb (esc_cls cv) (P i))))%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition FFSZ : list (list (expr * Z * Z)) := [[]].
Lemma heap_okAz : CHA.heap_chkA GZT.NF GZ.HDECL GZ.BLS FFSZ GZ.CPS GZ.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Definition leaf_chkz (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  (CBA.regions_eqb (CC.cp_F c) F0 && Nat.leb GZT.NF (CC.cp_nx c) && CHA.foot_chk GZT.NF GZ.HDECL c (nth i GZ.BLS []) (nth i FFSZ [])) &&
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc => (Nat.eqb i 0 && Z.eqb pc RETPC && CBA.exit_base_chk GZT.NF RETPC c ps && CL.ps_reg_is ps 10 (ELit 0))%bool
  end.
Lemma leaf_okz : CH2.leaves_all GZ.CPS GZ.TAGS leaf_chkz = true.
Proof. vm_compute. reflexivity. Qed.
End EESBA.
