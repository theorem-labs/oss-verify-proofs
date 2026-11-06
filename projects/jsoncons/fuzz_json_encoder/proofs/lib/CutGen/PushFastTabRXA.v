(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm4PlanKit Pm4L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA PmEncSpecs2A.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncSumsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_push_fast_root_xasan_T Cut_push_fast_root_xasan Cut_push_fast_root_xasan_D.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module G := Cut_push_fast_root_xasan.
Module GD := Cut_push_fast_root_xasan_D.
Module GT := Cut_push_fast_root_xasan_T.

Module PFR.
Definition PC : Z := 0xca1ac.            (* [comment removed for export] *)
Definition RETPC : Z := 0xca54c.
Definition PC_ANN : Z := 540712.         (* [comment removed for export] *)
Definition SBz : Z := 2147450880.
Definition SCR : Z := 4304.              (* [comment removed for export] *)
Definition stkE := EVar 10. Definition bE := EVar 32. Definition cE := EVar 33. Definition dE := EVar 38.    (* [comment removed for export] *)
Definition ENDE : expr := EAlu Instr.ALU_ADD bE dE.                                                  (* [comment removed for export] *)
Definition CAPE : expr := EAlu Instr.ALU_ADD bE cE.                                                  (* [comment removed for export] *)
Definition E32 : expr := EAlu Instr.ALU_ADD ENDE (ELit 32).                                           (* [comment removed for export] *)
Definition LREST : expr := EAlu Instr.ALU_SUB (EAlu Instr.ALU_SUB cE dE) (ELit 32).                 (* [comment removed for export] *)
Definition GC : expr := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD cE (ELit 7)) (ELit 3).                (* [comment removed for export] *)
Definition BOLD : list (expr * expr) := [(bE, cE)].
Definition BLKS (i : nat) : list (expr * expr) := BOLD.
Definition FFS : list (list (expr * Z * Z)) := map (fun _ => []) GD.CPS.
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1482488) 8 (ELit SBz)].
Definition CPF0 : list SGP.region := [(EVar 2, -4304, ELit 4304); (stkE, 0, ELit 24); (bE, 0, cE)].
(* [comment removed for export] *)
Definition NEWS_ANN : list kentry := STAT ++ [KZero (SA (CHA.SRL3 ENDE) SBz) (ELit 4); KZero (SA (CHA.SRL3 (EAlu Instr.ALU_ADD ENDE (ELit 4))) SBz) (ELit 1);
                                              KZero (SA (CHA.SRL3 (EAlu Instr.ALU_ADD ENDE (ELit 5))) SBz) (ELit 1); KZero (SA (CHA.SRL3 (EAlu Instr.ALU_ADD ENDE (ELit 6))) SBz) (ELit 1)].
Definition WSH_ANN : list SGP.region := [(CHA.SRL3 bE, SBz, GC)].
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.
Definition EXITC : list kentry :=
  [KWord (SA stkE 0) 8 bE; KWord (SA stkE 8) 8 E32; KWord (SA stkE 16) 8 CAPE;
   KBlob (SA bE 0) dE 0; KBlob (SA ENDE 32) LREST 1;
   KWord (SA ENDE 0) 4 (EVar 34); KWord (SA ENDE 4) 1 (ELit 0); KWord (SA ENDE 5) 1 (EVar 35); KWord (SA ENDE 6) 1 (ELit 0);
   KWord (SA ENDE 24) 8 (ELit 0)].
Definition CHK (i j : nat) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (scr : Z) (BLk : list (expr * expr)) (wregs : list SGP.region) (news : list kentry) (a0x : option expr) : bool :=
  isSome (CHA.custom_chk GT.NF GD.HDECL GT.SCELLS GT.GLO GT.GHI scr 0 BLk [] wregs news a0x c ps cj (BLKS i) [] (BLKS j) []).
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      let cells := SR.ps_cells ps in
      match CH2.ret_of GD.RETS i k with
      | Some j =>
          match nth_error GD.CPS j with
          | Some cj =>
              (CH2.blocks_eqb (nth i GD.BLS []) (BLKS i) && CH2.blocks_eqb (nth j GD.BLS []) (BLKS j) && CHA.foot_chk GT.NF GD.HDECL c (BLKS i) [] && Nat.leb GT.NF (CC.cp_nx c) &&
               if Z.eqb pc PC_ANN then
                 (Z.eqb (SR.ps_pc ps) PC_ANN && Nat.eqb i 0 && Nat.eqb j 1 && CBA.regions_eqb (CC.cp_F c) CPF0
                  && CHK i j c ps cj 4096 BOLD WSH_ANN NEWS_ANN None
                  && CL.ps_reg_is ps 10 bE && CL.ps_reg_is ps 11 CAPE && CL.ps_reg_is ps 12 ENDE && CL.ps_reg_is ps 13 E32)%bool
               else false)%bool
          | None => false
          end
      | None =>
          (Z.eqb pc RETPC && CBA.exit_base_chk GT.NF RETPC c ps && CHA.foot_chk GT.NF GD.HDECL c BOLD [] && Nat.eqb i 1 && CH2.blocks_eqb (nth i GD.BLS []) BOLD
           && CBA.regions_eqb (CC.cp_F c) CPF0 && CL.ps_reg_is ps 10 ENDE && forallb (has cells) EXITC)%bool
      end
  end.
Lemma leaf_ok : CH2.leaves_all GD.CPS GD.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF GD.HDECL GD.BLS FFS GD.CPS GD.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stat_ok : forallb (CHA.static_chk GT.SCELLS GT.GLO GT.GHI) STAT = true.
Proof. vm_compute. reflexivity. Qed.
Lemma bls_i : forall i, (i < 2)%nat -> nth i GD.BLS [] = BLKS i.
Proof. intros i Hi. do 2 (destruct i as [|i]; [vm_compute; reflexivity|]). lia. Qed.
Lemma ffs_i : forall i, nth i FFS [] = [].
Proof. intros i. do 2 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
End PFR.
