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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_push_slow_root_d1_xasan_T Cut_push_slow_root_d1_xasan Cut_push_slow_root_d1_xasan_D.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module G := Cut_push_slow_root_d1_xasan.
Module GD := Cut_push_slow_root_d1_xasan_D.
Module GT := Cut_push_slow_root_d1_xasan_T.

Module PSR1.
Definition PC : Z := 0xca1ac.            (* [comment removed for export] *)
Definition RETPC : Z := 0xca54c.
Definition PC_OPNEW : Z := 1414360.      (* [comment removed for export] *)
Definition PC_MC : Z := 524864.          (* [comment removed for export] *)
Definition PC_ANN : Z := 540712.         (* [comment removed for export] *)
Definition PC_OPDEL : Z := 1031544.      (* [comment removed for export] *)
Definition SBz : Z := 2147450880.
Definition SCR : Z := 4304.              (* [comment removed for export] *)
Definition stkE := EVar 10. Definition nbE := EVar 52. Definition bE := EVar 32.
Definition BNEW : list (expr * expr) := [(nbE, ELit 64)].
Definition BOLD : list (expr * expr) := [(bE, ELit 32)].
Definition BLKS (i : nat) : list (expr * expr) := match i with 0%nat => BOLD | 5%nat => BNEW | _ => BNEW ++ BOLD end.
Definition FFS : list (list (expr * Z * Z)) := map (fun _ => []) GD.CPS.
Definition SHWIN : kentry := KZero (SA (CHA.SRL3 (EVar 2)) (SBz - 16)) (ELit 6).
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1482488) 8 (ELit SBz)].
Definition STATW : list kentry := STAT ++ [SHWIN].
Definition CPF0 : list SGP.region := [(EVar 2, -4304, ELit 4304); (stkE, 0, ELit 24)].
Definition CPF1 : list SGP.region := CPF0 ++ [(nbE, 0, ELit 64)].
(* [comment removed for export] *)
Definition news_of (nb : nat) (cj : CC.cutpoint) : list kentry := List.filter (fun X => negb (APC.kentry_vars_lt nb X)) (CC.cp_know cj).
Definition crb_ok (cells : list kentry) (nx : nat) (X : kentry) : bool := (CHA.static_chk GT.SCELLS GT.GLO GT.GHI X || CRB.ablock_fact_ok 65536 7077888 GD.HDECL cells nx BOLD [] (nx + 4) (ELit 64) X)%bool.
(* [comment removed for export] *)
Definition HAND1 : list kentry := [SHWIN; KAlign nbE 8; KZero (SA (CHA.SRL3 (EAlu Instr.ALU_ADD nbE (ELit 36))) SBz) (ELit 1);
                                   KZero (SA (CHA.SRL3 (EAlu Instr.ALU_ADD nbE (ELit 37))) SBz) (ELit 1); KZero (SA (CHA.SRL3 (EAlu Instr.ALU_ADD nbE (ELit 38))) SBz) (ELit 1);
                                   KDisj (SA (CHA.SRL3 nbE) SBz) (ELit 8) (SA (CHA.SRL3 bE) SBz) (ELit 4); KDisj (SA nbE 0) (ELit 64) (SA (CHA.SRL3 bE) SBz) (ELit 4)].
(* [comment removed for export] *)
Definition NEWS_ANN1 : list kentry := STATW ++ [KZero (SA (CHA.SRL3 nbE) SBz) (ELit 8)].
Definition WSH_ANN1 : list SGP.region := [(CHA.SRL3 bE, SBz, ELit 4)].
Definition NEWS_MC : list kentry := STATW ++ [KBlob (SA nbE 0) (ELit 32) 0].
Definition NEWS_ANN2 : list kentry := STATW ++ [KZero (SA (CHA.SRL3 nbE) SBz) (ELit 8)].
Definition WSH_ANN2 : list SGP.region := [(CHA.SRL3 nbE, SBz, ELit 8)].
Definition NEWS_DEL : list kentry := STATW.
Definition E32 : expr := EAlu Instr.ALU_ADD bE (ELit 32).
Definition E64 : expr := EAlu Instr.ALU_ADD nbE (ELit 64).
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.
(* [comment removed for export] *)
Definition EXITC : list kentry :=
  [KWord (SA stkE 0) 8 nbE; KWord (SA stkE 8) 8 E64; KWord (SA stkE 16) 8 E64;
   KBlob (SA nbE 0) (ELit 32) 0;
   KWord (SA nbE 32) 4 (EVar 34); KWord (SA nbE 36) 1 (ELit 0); KWord (SA nbE 37) 1 (EVar 35); KWord (SA nbE 38) 1 (ELit 0);
   KWord (SA nbE 56) 8 (ELit 0); KRange nbE 4096 140737479966719; KAlign nbE 16].
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
               if Z.eqb pc PC_OPNEW then
                 let nx := (CC.cp_nx cj - APC.NCS)%nat in let news := news_of (nx + 4) cj in
                 (Z.eqb (SR.ps_pc ps) PC_OPNEW && Nat.eqb i 0 && Nat.eqb j 1 && Nat.eqb nx 48 && CBA.regions_eqb (CC.cp_F c) CPF0
                  && CHK i j c ps cj 4112 BOLD [] (STATW ++ news) None
                  && forallb (fun X => crb_ok cells nx X || has HAND1 X)%bool news
                  && CL.ps_reg_is ps 10 (ELit 64))%bool
               else if Z.eqb pc PC_MC then
                 (Z.eqb (SR.ps_pc ps) PC_MC && Nat.eqb i 2 && Nat.eqb j 3 && CBA.regions_eqb (CC.cp_F c) CPF1
                  && CHK i j c ps cj 2560 (BNEW ++ BOLD) [(nbE, 0, ELit 32)] NEWS_MC (Some nbE)
                  && CL.ps_reg_is ps 10 nbE && CL.ps_reg_is ps 11 bE && CL.ps_reg_is ps 12 (ELit 32) && has cells (KBlob (SA bE 0) (ELit 32) 0))%bool
               else if Z.eqb pc PC_ANN then
                 ((Z.eqb (SR.ps_pc ps) PC_ANN && Nat.eqb i 1 && Nat.eqb j 2 && CBA.regions_eqb (CC.cp_F c) CPF1
                   && CHK i j c ps cj 4096 (BNEW ++ BOLD) WSH_ANN1 NEWS_ANN1 None
                   && CL.ps_reg_is ps 10 bE && CL.ps_reg_is ps 11 E32 && CL.ps_reg_is ps 12 E32 && CL.ps_reg_is ps 13 E32)
                  || (Z.eqb (SR.ps_pc ps) PC_ANN && Nat.eqb i 3 && Nat.eqb j 4 && CBA.regions_eqb (CC.cp_F c) CPF1
                   && CHK i j c ps cj 4096 (BNEW ++ BOLD) WSH_ANN2 NEWS_ANN2 None
                   && CL.ps_reg_is ps 10 nbE && CL.ps_reg_is ps 11 E64 && CL.ps_reg_is ps 12 E64 && CL.ps_reg_is ps 13 E64))%bool
               else if Z.eqb pc PC_OPDEL then
                 (Z.eqb (SR.ps_pc ps) PC_OPDEL && Nat.eqb i 4 && Nat.eqb j 5 && CBA.regions_eqb (CC.cp_F c) CPF1
                  && CHK i j c ps cj 4096 BNEW [] NEWS_DEL None
                  && CL.ps_reg_is ps 10 bE && CL.ps_reg_is ps 11 (ELit 32))%bool
               else false)%bool
          | None => false
          end
      | None =>
          (Z.eqb pc RETPC && CBA.exit_base_chk GT.NF RETPC c ps && CHA.foot_chk GT.NF GD.HDECL c BNEW [] && Nat.eqb i 5 && CH2.blocks_eqb (nth i GD.BLS []) BNEW
           && CBA.regions_eqb (CC.cp_F c) CPF1 && CL.ps_reg_is ps 10 (EAlu Instr.ALU_ADD nbE (ELit 32)) && forallb (has cells) EXITC)%bool
      end
  end.
Lemma leaf_ok : CH2.leaves_all GD.CPS GD.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF GD.HDECL GD.BLS FFS GD.CPS GD.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stat_ok : forallb (CHA.static_chk GT.SCELLS GT.GLO GT.GHI) STAT = true.
Proof. vm_compute. reflexivity. Qed.
Lemma bls_i : forall i, (i < 6)%nat -> nth i GD.BLS [] = BLKS i.
Proof. intros i Hi. do 6 (destruct i as [|i]; [vm_compute; reflexivity|]). lia. Qed.
Lemma ffs_i : forall i, nth i FFS [] = [].
Proof. intros i. do 6 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
End PSR1.
