(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm5PlanKit Pm5L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA PmEncSpecs2A.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_push_slow_root_d0_xboth_T Cut_push_slow_root_d0_xboth Cut_push_slow_root_d0_xboth_D.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module G := Cut_push_slow_root_d0_xboth.
Module GD := Cut_push_slow_root_d0_xboth_D.
Module GT := Cut_push_slow_root_d0_xboth_T.

Module PSR0.
Definition PC : Z := 0xce9ec.            (* [comment removed for export] *)
Definition RETPC : Z := 0xceb44.
Definition PC_OPNEW : Z := 1429232.      (* [comment removed for export] *)
Definition PC_MC : Z := 527120.          (* [comment removed for export] *)
Definition PC_ANN : Z := 542968.         (* [comment removed for export] *)
Definition SBz : Z := 2147450880.
Definition SCR : Z := 4304.              (* [comment removed for export] *)
Definition stkE := EVar 10. Definition nbE := EVar 52.
Definition BNEW : list (expr * expr) := [(nbE, ELit 32)].
Definition BLKS (i : nat) : list (expr * expr) := match i with 0%nat => [] | _ => BNEW end.
Definition FFS : list (list (expr * Z * Z)) := map (fun _ => []) GD.CPS.
Definition SHWIN : kentry := KZero (SA (CHA.SRL3 (EVar 2)) (SBz - 14)) (ELit 5).
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1497016) 8 (ELit SBz)].
Definition STATW : list kentry := STAT ++ [SHWIN].
Definition CPF0 : list SGP.region := [(EVar 2, -4304, ELit 4304); (stkE, 0, ELit 24)].
Definition CPF1 : list SGP.region := CPF0 ++ [(nbE, 0, ELit 32)].
(* [comment removed for export] *)
Definition news_of (nb : nat) (cj : CC.cutpoint) : list kentry := List.filter (fun X => negb (APC.kentry_vars_lt nb X)) (CC.cp_know cj).
(* [comment removed for export] *)
Definition crb_ok (cells : list kentry) (nx : nat) (X : kentry) : bool := (CHA.static_chk GT.SCELLS GT.GLO GT.GHI X || CRB.ablock_fact_ok 65536 7094272 GD.HDECL cells nx [] [] (nx + 4) (ELit 32) X)%bool.
Definition NEWS_MC : list kentry := STATW ++ [KBlob (SA nbE 0) (ELit 0) 0].
Definition NEWS_ANN : list kentry := STATW ++ [KZero (SA (CHA.SRL3 nbE) SBz) (ELit 4)].
Definition WSH_ANN : list SGP.region := [(CHA.SRL3 nbE, SBz, CHA.SRL3 (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SUB (EAlu Instr.ALU_ADD nbE (ELit 32)) nbE) (ELit 7)))].
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.
(* [comment removed for export] *)
Definition EXITC : list kentry :=
  [KWord (SA stkE 0) 8 nbE; KWord (SA stkE 8) 8 (EAlu Instr.ALU_ADD nbE (ELit 32)); KWord (SA stkE 16) 8 (EAlu Instr.ALU_ADD nbE (ELit 32));
   KWord (SA nbE 0) 4 (EVar 34); KWord (SA nbE 4) 1 (ELit 0); KWord (SA nbE 5) 1 (EVar 35); KWord (SA nbE 6) 1 (ELit 0);
   KWord (SA nbE 8) 8 (EVar 37); KWord (SA nbE 16) 8 (EVar 36); KWord (SA nbE 24) 8 (ELit 0); KUnk (SA nbE 7) (ELit 1);
   KZero (SA (CHA.SRL3 nbE) SBz) (ELit 4); KRange nbE 4096 140737479966719; KAlign nbE 16].
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
                  && isSome (CHA.custom_chk GT.NF GD.HDECL GT.SCELLS GT.GLO GT.GHI 4112 0 [] [] [] (STATW ++ news) None c ps cj [] [] BNEW [])
                  && forallb (fun X => crb_ok cells nx X || has [SHWIN; KAlign nbE 8; KZero (SA (CHA.SRL3 (EAlu Instr.ALU_ADD nbE (ELit 4))) SBz) (ELit 1);
                                                              KZero (SA (CHA.SRL3 (EAlu Instr.ALU_ADD nbE (ELit 5))) SBz) (ELit 1); KZero (SA (CHA.SRL3 (EAlu Instr.ALU_ADD nbE (ELit 6))) SBz) (ELit 1)] X)%bool news
                  && CL.ps_reg_is ps 10 (ELit 32))%bool
               else if Z.eqb pc PC_MC then
                 (Z.eqb (SR.ps_pc ps) PC_MC && Nat.eqb i 1 && Nat.eqb j 2 && CBA.regions_eqb (CC.cp_F c) CPF1
                  && isSome (CHA.custom_chk GT.NF GD.HDECL GT.SCELLS GT.GLO GT.GHI 2560 0 BNEW [] [(nbE, 0, ELit 0)] NEWS_MC (Some nbE) c ps cj BNEW [] BNEW [])
                  && CL.ps_reg_is ps 10 nbE && CL.ps_reg_is ps 11 (ELit 0) && CL.ps_reg_is ps 12 (ELit 0))%bool
               else if Z.eqb pc PC_ANN then
                 (Z.eqb (SR.ps_pc ps) PC_ANN && Nat.eqb i 2 && Nat.eqb j 3 && CBA.regions_eqb (CC.cp_F c) CPF1
                  && isSome (CHA.custom_chk GT.NF GD.HDECL GT.SCELLS GT.GLO GT.GHI 4096 0 BNEW [] WSH_ANN NEWS_ANN None c ps cj BNEW [] BNEW [])
                  && CL.ps_reg_is ps 10 nbE && CL.ps_reg_is ps 11 (EAlu Instr.ALU_ADD nbE (ELit 32)) && CL.ps_reg_is ps 12 (EAlu Instr.ALU_ADD nbE (ELit 32)) && CL.ps_reg_is ps 13 (EAlu Instr.ALU_ADD nbE (ELit 32)))%bool
               else false)%bool
          | None => false
          end
      | None =>
          (Z.eqb pc RETPC && CBA.exit_base_chk GT.NF RETPC c ps && CHA.foot_chk GT.NF GD.HDECL c BNEW [] && Nat.eqb i 3 && CH2.blocks_eqb (nth i GD.BLS []) BNEW
           && CBA.regions_eqb (CC.cp_F c) CPF1 && CL.ps_reg_is ps 10 (EAlu Instr.ALU_ADD nbE (ELit 32)) && forallb (has cells) EXITC)%bool
      end
  end.
Lemma leaf_ok : CH2.leaves_all GD.CPS GD.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF GD.HDECL GD.BLS FFS GD.CPS GD.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stat_ok : forallb (CHA.static_chk GT.SCELLS GT.GLO GT.GHI) STAT = true.
Proof. vm_compute. reflexivity. Qed.
Lemma bls_i : forall i, (i < 4)%nat -> nth i GD.BLS [] = BLKS i.
Proof. intros i Hi. do 4 (destruct i as [|i]; [vm_compute; reflexivity|]). lia. Qed.
Lemma ffs_i : forall i, nth i FFS [] = [].
Proof. intros i. do 4 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
End PSR0.
