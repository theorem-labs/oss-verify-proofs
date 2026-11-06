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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_push_slow_root_d2_xasan_T Cut_push_slow_root_d2_xasan Cut_push_slow_root_d2_xasan_D.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module G := Cut_push_slow_root_d2_xasan.
Module GD := Cut_push_slow_root_d2_xasan_D.
Module GT := Cut_push_slow_root_d2_xasan_T.

Module PSR2.
Definition PC : Z := 0xca1ac.            (* [comment removed for export] *)
Definition RETPC : Z := 0xca54c.
Definition PC_OPNEW : Z := 1414360.      (* [comment removed for export] *)
Definition PC_MC : Z := 524864.          (* [comment removed for export] *)
Definition PC_ANN : Z := 540712.         (* [comment removed for export] *)
Definition PC_OPDEL : Z := 1031544.      (* [comment removed for export] *)
Definition SBz : Z := 2147450880.
Definition SCR : Z := 4304.              (* [comment removed for export] *)
Definition stkE := EVar 10. Definition nbE := EVar 52. Definition bE := EVar 32. Definition cE := EVar 33.    (* [comment removed for export] *)
Definition NN : expr := EMd Instr.M_MUL (ELit 32) (EAlu Instr.ALU_SRA cE (ELit 4)).                  (* [comment removed for export] *)
Definition NNF : expr := EAlu Instr.ALU_SLL (EAlu Instr.ALU_SRA cE (ELit 4)) (ELit 5).              (* [comment removed for export] *)
Definition CB : expr := EAlu Instr.ALU_ADD cE nbE.                                                    (* [comment removed for export] *)
Definition EBC : expr := EAlu Instr.ALU_ADD bE cE.                                                    (* [comment removed for export] *)
Definition ENN : expr := EAlu Instr.ALU_ADD nbE NN.                                                   (* [comment removed for export] *)
Definition ENM : expr := EAlu Instr.ALU_ADD nbE (EMd Instr.M_MUL (ELit 32) (EAlu Instr.ALU_SRA (EAlu Instr.ALU_ADD cE (ELit 32)) (ELit 5))).   (* [comment removed for export] *)
Definition EEND : expr := EAlu Instr.ALU_ADD CB (ELit 32).                                            (* [comment removed for export] *)
Definition G32 : expr := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD cE (ELit 32)) (ELit 3).              (* [comment removed for export] *)
Definition GC : expr := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD cE (ELit 7)) (ELit 3).                (* [comment removed for export] *)
Definition GNN : expr := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD NN (ELit 7)) (ELit 3).              (* [comment removed for export] *)
Definition BNEW : list (expr * expr) := [(nbE, NN)].
Definition BOLD : list (expr * expr) := [(bE, cE)].
Definition BLKS (i : nat) : list (expr * expr) := match i with 0%nat => BOLD | 5%nat => BNEW | _ => BNEW ++ BOLD end.
Definition FFS : list (list (expr * Z * Z)) := map (fun _ => []) GD.CPS.
Definition SHWIN : kentry := KZero (SA (CHA.SRL3 (EVar 2)) (SBz - 16)) (ELit 6).
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1482488) 8 (ELit SBz)].
Definition STATW : list kentry := STAT ++ [SHWIN].
Definition CPF0 : list SGP.region := [(EVar 2, -4304, ELit 4304); (stkE, 0, ELit 24)].
Definition CPF1 : list SGP.region := CPF0 ++ [(nbE, 0, NNF)].
Definition news_of (nb : nat) (cj : CC.cutpoint) : list kentry := List.filter (fun X => negb (APC.kentry_vars_lt nb X)) (CC.cp_know cj).
Definition crb_ok (cells : list kentry) (nx : nat) (X : kentry) : bool := (CHA.static_chk GT.SCELLS GT.GLO GT.GHI X || CRB.ablock_fact_ok 65536 7077888 GD.HDECL cells nx BOLD [] (nx + 4) NN X)%bool.
(* [comment removed for export] *)
Definition HAND1 : list kentry := [SHWIN; KAlign nbE 8;
  KDisj {| a_base := EAlu ALU_SRL (EVar 10) (ELit 3); a_off := 2147450880 |} (ELit 5) {| a_base := EAlu ALU_SRL (EVar 52) (ELit 3); a_off := 2147450880 |} (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EAlu ALU_SRA (EVar 33) (ELit 4))) (ELit 7)) (ELit 3));
  KDisj {| a_base := EVar 10; a_off := 0 |} (ELit 24) {| a_base := EAlu ALU_SRL (EVar 52) (ELit 3); a_off := 2147450880 |} (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EAlu ALU_SRA (EVar 33) (ELit 4))) (ELit 7)) (ELit 3));
  KDisj {| a_base := EVar 10; a_off := 24 |} (ELit 16) {| a_base := EAlu ALU_SRL (EVar 52) (ELit 3); a_off := 2147450880 |} (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EAlu ALU_SRA (EVar 33) (ELit 4))) (ELit 7)) (ELit 3));
  KDisj {| a_base := EVar 2; a_off := -4304 |} (ELit 4304) {| a_base := EAlu ALU_SRL (EVar 52) (ELit 3); a_off := 2147450880 |} (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EAlu ALU_SRA (EVar 33) (ELit 4))) (ELit 7)) (ELit 3));
  KDisj {| a_base := EAlu ALU_SRL (EVar 2) (ELit 3); a_off := 2147450864 |} (ELit 6) {| a_base := EAlu ALU_SRL (EVar 52) (ELit 3); a_off := 2147450880 |} (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EAlu ALU_SRA (EVar 33) (ELit 4))) (ELit 7)) (ELit 3));
  KDisj {| a_base := EAlu ALU_SRL (EVar 11) (ELit 3); a_off := 2147450880 |} (ELit 1) {| a_base := EAlu ALU_SRL (EVar 52) (ELit 3); a_off := 2147450880 |} (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EAlu ALU_SRA (EVar 33) (ELit 4))) (ELit 7)) (ELit 3));
  KDisj {| a_base := EAlu ALU_SRL (EVar 12) (ELit 3); a_off := 2147450880 |} (ELit 1) {| a_base := EAlu ALU_SRL (EVar 52) (ELit 3); a_off := 2147450880 |} (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EAlu ALU_SRA (EVar 33) (ELit 4))) (ELit 7)) (ELit 3));
  KDisj {| a_base := EAlu ALU_SRL (EVar 13) (ELit 3); a_off := 2147450880 |} (ELit 1) {| a_base := EAlu ALU_SRL (EVar 52) (ELit 3); a_off := 2147450880 |} (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EAlu ALU_SRA (EVar 33) (ELit 4))) (ELit 7)) (ELit 3));
  KDisj {| a_base := EAlu ALU_SRL (EVar 15) (ELit 3); a_off := 2147450880 |} (ELit 1) {| a_base := EAlu ALU_SRL (EVar 52) (ELit 3); a_off := 2147450880 |} (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EAlu ALU_SRA (EVar 33) (ELit 4))) (ELit 7)) (ELit 3));
  KDisj {| a_base := EVar 11; a_off := 0 |} (ELit 4) {| a_base := EAlu ALU_SRL (EVar 52) (ELit 3); a_off := 2147450880 |} (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EAlu ALU_SRA (EVar 33) (ELit 4))) (ELit 7)) (ELit 3));
  KDisj {| a_base := EVar 12; a_off := 0 |} (ELit 1) {| a_base := EAlu ALU_SRL (EVar 52) (ELit 3); a_off := 2147450880 |} (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EAlu ALU_SRA (EVar 33) (ELit 4))) (ELit 7)) (ELit 3));
  KDisj {| a_base := EVar 13; a_off := 0 |} (ELit 1) {| a_base := EAlu ALU_SRL (EVar 52) (ELit 3); a_off := 2147450880 |} (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EAlu ALU_SRA (EVar 33) (ELit 4))) (ELit 7)) (ELit 3));
  KDisj {| a_base := EVar 15; a_off := 0 |} (ELit 8) {| a_base := EAlu ALU_SRL (EVar 52) (ELit 3); a_off := 2147450880 |} (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EAlu ALU_SRA (EVar 33) (ELit 4))) (ELit 7)) (ELit 3));
  KDisj {| a_base := EAlu ALU_SRL (EVar 52) (ELit 3); a_off := 2147450880 |} (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EAlu ALU_SRA (EVar 33) (ELit 4))) (ELit 7)) (ELit 3)) {| a_base := EAlu ALU_SRL (EVar 32) (ELit 3); a_off := 2147450880 |} (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit 7)) (ELit 3));
  KDisj {| a_base := EVar 32; a_off := 0 |} (EVar 33) {| a_base := EAlu ALU_SRL (EVar 52) (ELit 3); a_off := 2147450880 |} (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EAlu ALU_SRA (EVar 33) (ELit 4))) (ELit 7)) (ELit 3));
  KDisj {| a_base := EVar 52; a_off := 0 |} (EMd M_MUL (ELit 32) (EAlu ALU_SRA (EVar 33) (ELit 4))) {| a_base := EAlu ALU_SRL (EVar 32) (ELit 3); a_off := 2147450880 |} (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit 7)) (ELit 3))].
Definition NEWS_ANN1 : list kentry := STATW ++ [KZero (SA (CHA.SRL3 nbE) SBz) G32].
Definition WSH_ANN1 : list SGP.region := [(CHA.SRL3 bE, SBz, GC)].
Definition NEWS_MC : list kentry := STATW ++ [KBlob (SA nbE 0) cE 0].
Definition NEWS_ANN2 : list kentry := STATW ++ [KZero (SA (CHA.SRL3 nbE) SBz) G32].
Definition WSH_ANN2 : list SGP.region := [(CHA.SRL3 nbE, SBz, GNN)].
Definition NEWS_DEL : list kentry := STATW.
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.
Definition EXITC : list kentry :=
  [KWord (SA stkE 0) 8 nbE; KWord (SA stkE 8) 8 EEND; KWord (SA stkE 16) 8 ENN;
   KBlob (SA nbE 0) cE 0;
   KWord (SA CB 0) 4 (EVar 34); KWord (SA CB 4) 1 (ELit 0); KWord (SA CB 5) 1 (EVar 35); KWord (SA CB 6) 1 (ELit 0);
   KWord (SA CB 24) 8 (ELit 0); KRange nbE 4096 140737479966719; KAlign nbE 16].
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
                  && CL.ps_reg_is ps 10 NN)%bool
               else if Z.eqb pc PC_MC then
                 (Z.eqb (SR.ps_pc ps) PC_MC && Nat.eqb i 2 && Nat.eqb j 3 && CBA.regions_eqb (CC.cp_F c) CPF1
                  && CHK i j c ps cj 2560 (BNEW ++ BOLD) [(nbE, 0, cE)] NEWS_MC (Some nbE)
                  && CL.ps_reg_is ps 10 nbE && CL.ps_reg_is ps 11 bE && CL.ps_reg_is ps 12 cE && has cells (KBlob (SA bE 0) cE 0))%bool
               else if Z.eqb pc PC_ANN then
                 ((Z.eqb (SR.ps_pc ps) PC_ANN && Nat.eqb i 1 && Nat.eqb j 2 && CBA.regions_eqb (CC.cp_F c) CPF1
                   && CHK i j c ps cj 4096 (BNEW ++ BOLD) WSH_ANN1 NEWS_ANN1 None
                   && CL.ps_reg_is ps 10 bE && CL.ps_reg_is ps 11 EBC && CL.ps_reg_is ps 12 EBC && CL.ps_reg_is ps 13 EBC)
                  || (Z.eqb (SR.ps_pc ps) PC_ANN && Nat.eqb i 3 && Nat.eqb j 4 && CBA.regions_eqb (CC.cp_F c) CPF1
                   && CHK i j c ps cj 4096 (BNEW ++ BOLD) WSH_ANN2 NEWS_ANN2 None
                   && CL.ps_reg_is ps 10 nbE && CL.ps_reg_is ps 11 ENN && CL.ps_reg_is ps 12 ENN && CL.ps_reg_is ps 13 ENM))%bool
               else if Z.eqb pc PC_OPDEL then
                 (Z.eqb (SR.ps_pc ps) PC_OPDEL && Nat.eqb i 4 && Nat.eqb j 5 && CBA.regions_eqb (CC.cp_F c) CPF1
                  && CHK i j c ps cj 4096 BNEW [] NEWS_DEL None
                  && CL.ps_reg_is ps 10 bE && CL.ps_reg_is ps 11 cE)%bool
               else false)%bool
          | None => false
          end
      | None =>
          (Z.eqb pc RETPC && CBA.exit_base_chk GT.NF RETPC c ps && CHA.foot_chk GT.NF GD.HDECL c BNEW [] && Nat.eqb i 5 && CH2.blocks_eqb (nth i GD.BLS []) BNEW
           && CBA.regions_eqb (CC.cp_F c) CPF1 && CL.ps_reg_is ps 10 CB && forallb (has cells) EXITC)%bool
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
End PSR2.
