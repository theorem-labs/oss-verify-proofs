(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm4PlanKit Pm4L5DefsA FPSteps.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB CutRtD CutShA CutInlA CutHeapV.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmLibStaticsA PmEncSpecsA PmFloatXSpecsA PmFloatXTuA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncSumsA EncKitA EncBridgesA EncHtransA EncKit2A EncPureA EncStransA EncSinkBridgesA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatXA Require Import CutInlFA DumpBufXA FxKitXA DtoaFalseXA VdKitXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_vd_nested_xasan_T Cut_vd_nested_xasan Cut_vd_nested_xasan_D.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
#[local] Ltac lia ::= L5FastLia.plia.

Module G := Cut_vd_nested_xasan.
Module GD := Cut_vd_nested_xasan_D.
Module GT := Cut_vd_nested_xasan_T.

Module EVDNA.
Import PMES.
Definition PC : Z := 739980.              (* [comment removed for export] *)
Definition RETPC : Z := 742780.           (* [comment removed for export] *)
Definition PC_SM : Z := 419004.           (* [comment removed for export] *)
Definition PC_SETSH : Z := 540344.        (* [comment removed for export] *)
Definition PC_APPEND : Z := 1040708.      (* [comment removed for export] *)
Definition PC_BEGIN_SCALAR : Z := 765616. (* [comment removed for export] *)
Definition PC_NULL_LIT : Z := 770528.     (* [comment removed for export] *)
Definition PC_WD : Z := 772144.           (* [comment removed for export] *)
Definition TP : Z := 6938576.             (* [comment removed for export] *)
Definition ERRNO : Z := 6938412.          (* [comment removed for export] *)
Definition LS_ : Z := 6931848.            (* [comment removed for export] *)
Definition LTXT : Z := 154272.            (* [comment removed for export] *)
Definition LLEN : Z := 4.
Definition VBOFF : Z := 1420120.          (* [comment removed for export] *)
Definition VBOFF_SHA : Z := 2147628395.   (* [comment removed for export] *)
Definition SBz : Z := 2147450880.
Definition FSLO : Z := 7077888.           (* [comment removed for export] *)
Definition SCRT : Z := 13824.             (* [comment removed for export] *)
Definition VE := EVar 10. Definition S2E := EVar 32. Definition E16E := EVar 41. Definition DPE := EVar 42. Definition FLE := EVar 49. Definition FE := EVar 54.
Definition ENDE : expr := APC.eadd (EVar 34) (APC.escale 32 (EVar 33)).
Definition SHF : expr := EAlu Instr.ALU_ADD (CHA.SRL3 FE) (ELit SBz).
Definition BL1 : CA.blocks := [(EVar 34, EVar 35)].
Definition inset (i : nat) (l : list nat) : bool := existsb (Nat.eqb i) l.
(* [comment removed for export] *)
Definition NCUT : nat := 46.
Definition PRE0 (i : nat) : bool := inset i [0; 1; 2]%nat.
Definition FR (i : nat) : bool := inset i [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 40; 41; 42; 43; 44; 45]%nat.
Definition PA (i : nat) : bool := inset i [3; 5; 8; 9; 13; 14; 15; 20; 21; 22; 23; 27; 28; 29; 33; 34; 35; 39; 40; 41; 44; 45]%nat.
Definition LD (i : nat) : bool := inset i [11; 14; 17; 18; 19; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 40; 41; 42; 43; 44; 45]%nat.
Definition AD (i : nat) : bool := inset i [24; 27; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 40; 41; 42; 43; 44; 45]%nat.
Definition WDD (i : nat) : bool := inset i [10; 13; 16; 20]%nat.
Definition FLG (i : nat) : bool := inset i [16; 20; 36; 39; 42; 43; 44; 45]%nat.
Definition INLJ (i j : nat) : bool := (match i, j with 0, 1 | 2, 4 | 3, 5 | 4, 6 | 4, 7 | 5, 8 | 5, 9 | 7, 12 | 9, 15 => true | _, _ => false end)%nat.
(* [comment removed for export] *)
Definition FRR : expr * Z * Z := (FE, 4, -192).
Definition FFS : list (list (expr * Z * Z)) := map (fun i => if Nat.ltb i 2 then [] else [FRR]) (seq 0 NCUT).
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1482488) 8 (ELit SBz)].
Definition STATU : list kentry := STAT ++ [KWord (SA (ELit 0) 1482496) 4 (ELit 1)].
Definition FLAG : list kentry := [KWord (SA FE 1016) 8 FLE; KWr (SA FLE 0) (ELit 1)].
Definition ISHZ : kentry := KZero (SA (ELit 0) VBOFF_SHA) (ELit 1).
Definition SHK (k : Z) : kentry := KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz ENDE k) (ELit 3)) SBz) (ELit 1).
Definition SHN : list kentry := [SHK (-32); SHK (-28); SHK (-26); SHK (-8)].
(* [comment removed for export] *)
Definition SHA (k : Z) : kentry := KDisj (SA (CHA.SRL3 FE) SBz) (ELit 128) (SA (EAlu Instr.ALU_SRL (APC.eaddz ENDE k) (ELit 3)) SBz) (ELit 1).
Definition SHAP : list kentry := [SHA (-32); SHA (-28); SHA (-26); SHA (-8)].
(* [comment removed for export] *)
Definition UNEWS : list kentry := ISHZ :: SHN ++ FLAG.
Definition NEWS_BS : list kentry :=
  ISHZ :: SHN ++ [KWord (SA ENDE (-32)) 4 (EVar 38); KWord (SA ENDE (-28)) 1 (ELit 0); KWord (SA ENDE (-26)) 1 (ELit 1); KWord (SA ENDE (-8)) 8 (EVar 36); KWr (SA ENDE (-8)) (ELit 8); KUnk (SA ENDE (-32)) (ELit 32)] ++ FLAG.
Definition ERRW : SGP.region := (ELit 0, ERRNO, ELit 4).
Definition CPF0 : list SGP.region := [(EVar 2, -13824, ELit 13824); (VE, 296, ELit 8); (ENDE, -8, ELit 8)].
Definition FXV : list SGP.region := [(FE, 0, ELit 24); (FE, 32, ELit 984); (CHA.SRL3 FE, SBz, ELit 128)].
Definition FALL : list SGP.region := CPF0 ++ FXV ++ [(FLE, 0, ELit 1)].
Definition CPF (i : nat) : list SGP.region := if Nat.ltb i 2 then CPF0 else if FLG i then FALL else CPF0 ++ FXV.
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.
(* [comment removed for export] *)
Definition DEADPC (pc : Z) : bool := existsb (Z.eqb pc) [741144; 741204; 741264; 741756; 742900; 743088].
Definition DMASK (m : Z) : kentry := KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND E16E (ELit m)) (ELit 0)) (ELit 1)) 0 0.
Definition dead_chk (cells : list kentry) : bool := existsb (fun m => has cells (DMASK m)) [1; 2; 6; 8; 16; 48].
(* [comment removed for export] *)
Definition isU (X : kentry) : bool := CC.has_cell (ISHZ :: SHN ++ SHAP) X.
Definition sm_ok (ps : SR.post_spec) (i : nat) (X : kentry) : bool :=
  (CHA.static_chk GT.SCELLS GT.GLO GT.GHI X || CRA.smalloc_fact_ok FSLO GD.HDECL (SR.ps_cells ps) 49 (nth i GD.BLS []) (nth i FFS []) 4 54 49 X || isU X)%bool.
Definition lit_chk := EPA.lit_chk GT.NF GD.HDECL GT.SCELLS GT.GLO GT.GHI STAT LS_ LTXT LLEN UNEWS.
Definition wd_chk := VDK.wd_chk GT.NF GD.HDECL GT.SCELLS GT.GLO GT.GHI STAT S2E ERRNO 12800 UNEWS.
Definition call_j (f : CC.cutpoint -> SR.post_spec -> CC.cutpoint -> CA.blocks -> list (expr * Z * Z) -> CA.blocks -> list (expr * Z * Z) -> option CH2.cinfo)
           (cond : nat -> CC.cutpoint -> CH2.cinfo -> bool) (i k : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  match CH2.ret_of GD.RETS i k with
  | Some j => match nth_error GD.CPS j with
              | Some cj => match f c ps cj (nth i GD.BLS []) (nth i FFS []) (nth j GD.BLS []) (nth j FFS []) with Some ci => cond j cj ci | None => false end
              | None => false end
  | None => false
  end.
(* [comment removed for export] *)
Definition tyv (i : nat) (pc : Z) : option Z := if PRE0 i then (if Z.eqb pc PC_BEGIN_SCALAR then Some 1 else if Z.eqb pc 740864 then Some 0 else None) else Some (if PA i then 1 else 0).
(* [comment removed for export] *)
Definition bumped (i : nat) (pc : Z) : bool := (FLG i || Z.eqb pc PC_SETSH || Z.eqb pc RETPC)%bool.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in let regs := CA.ps_reglist ps in
  (CBA.regions_eqb (CC.cp_F c) (CPF i) && (Nat.ltb 54 (CC.cp_nx c) || Nat.ltb i 2) && Nat.leb GT.NF (CC.cp_nx c) && CH2.blocks_eqb (nth i GD.BLS []) BL1 &&
   match tyv i (SR.ps_pc ps) with Some tv => has cells (KRange (EVar 38) tv tv) | None => true end &&
   has cells (KWord (SA ENDE (-8)) 8 (if bumped i (SR.ps_pc ps) then EAlu ALU_ADD (EVar 36) (ELit 1) else EVar 36)) &&
   (PRE0 i || has cells (KWord (SA ENDE (-26)) 1 (if PA i then ELit 1 else EVar 40))) &&
   (Nat.ltb i 2 || has cells (KWord (SA FE 1016) 8 FLE))) &&
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if Z.eqb pc RETPC then
        (FLG i && CBA.exit_base_chk GT.NF RETPC c ps
         && match CHA.retire_chk GT.NF GD.HDECL c (nth i GD.BLS []) (nth i FFS []) with Some fle => expr_eqb fle FLE | None => false end
         && has cells (KWord (SA FLE 0) 1 (ELit 0)) && CL.ps_reg_is ps 10 (ELit 1)
         && has cells (KWord (SA ENDE (-32)) 4 (EVar 38)) && has cells (KWord (SA ENDE (-28)) 1 (ELit 0)))%bool
      else if DEADPC pc then (negb (PRE0 i) && dead_chk cells)%bool
      else
       (negb (FLG i) && CHA.foot_chk GT.NF GD.HDECL c (nth i GD.BLS []) (nth i FFS []) && Z.eqb (SR.ps_pc ps) pc &&
        match CIFA.fp_site RSEGS pc with
        | Some hv => match CH2.ret_of GD.RETS i k with
                     | Some j => match nth_error GD.CPS j with
                                 | Some cj => (CIFA.inlF_chk GT.NF c ps cj 4 hv && CIA.same_chk GT.NF GD.HDECL c (nth i GD.BLS []) (nth j GD.BLS []) (nth i FFS []) (nth j FFS [])
                                               && INLJ i j && CBA.regions_eqb (CC.cp_F c) (CC.cp_F cj) && Bool.eqb (PA j) (PA i) && Bool.eqb (AD j) (AD i) && Bool.eqb (WDD j) (WDD i) && Bool.eqb (LD j) (LD i) && negb (FLG j)
                                               && negb (FLG i) && (negb (PRE0 i && negb (PRE0 j)) || has cells (KRange (EVar 38) 0 0)) && Z.leb 0 pc && Z.ltb pc 4294967296)%bool
                                 | None => false end
                     | None => false end
        | None =>
        if Z.eqb pc PC_SM then
          (Nat.eqb i 1 &&
           call_j (fun c ps cj BLi FFi BLj FFj => CHA.custom_chk GT.NF GD.HDECL GT.SCELLS GT.GLO GT.GHI 512 1 BLi FFi [] (List.filter (sm_ok ps i) (CC.cp_know cj)) None c ps cj BLi FFi BLj FFj)
                  (fun j cj ci => Nat.eqb j 2 && Nat.eqb (CH2.ci_nx ci) 49 && Z.eqb (CH2.ci_csp ci) (-192) && CHA.frames_eqb (nth j FFS []) ((EVar (CH2.ci_nx ci + 5), 4, CH2.ci_csp ci) :: nth i FFS [])
                                  && CH2.blocks_eqb (nth j GD.BLS []) (nth i GD.BLS [])
                                  && forallb (fun X => CHA.static_chk GT.SCELLS GT.GLO GT.GHI X || CRA.smalloc_fact_ok FSLO GD.HDECL cells (CH2.ci_nx ci) (nth i GD.BLS []) (nth i FFS []) 4 (CH2.ci_nx ci + 5) (CH2.ci_nx ci) X || isU X)%bool
                                             (List.filter (sm_ok ps i) (CC.cp_know cj))
                                  && forallb (CC.has_cell (CC.cp_know cj)) (ISHZ :: SHN ++ SHAP))%bool i k c ps
           && CL.ps_reg_is ps 10 (ELit 800))%bool
        else if Z.eqb pc PC_BEGIN_SCALAR then
          (Nat.eqb i 2 &&
           call_j (EHTA.hcall_chk GT.NF GD.HDECL GT.SCELLS GT.GLO GT.GHI STAT S2E 4624 NEWS_BS) (fun j cj ci => PA j && Nat.ltb 54 (CC.cp_nx cj) && Z.eqb (CH2.ci_csp ci) (-192))%bool i k c ps
           && CL.ps_reg_is ps 10 VE)%bool
        else if Z.eqb pc PC_NULL_LIT then
          (negb (PRE0 i) &&
           call_j lit_chk (fun j cj ci => Bool.eqb (PA j) (PA i) && Nat.ltb 54 (CC.cp_nx cj) && Bool.eqb (AD j) (AD i) && LD j && negb (WDD j) && negb (WDD i) && negb (FLG j) && Z.eqb (CH2.ci_csp ci) (-192))%bool i k c ps)%bool
        else if Z.eqb pc PC_APPEND then
          (negb (PRE0 i) && LD i && negb (AD i) && negb (WDD i) &&
           call_j (EBA.sink_chk GT.NF GD.HDECL GT.SCELLS GT.GLO GT.GHI STAT S2E UNEWS) (fun j cj ci => Bool.eqb (PA j) (PA i) && AD j && LD j && negb (WDD j) && negb (FLG j) && Nat.ltb 54 (CC.cp_nx cj) && Z.eqb (CH2.ci_csp ci) (-192))%bool i k c ps
           && expr_eqb (nth 11 regs (ELit 0)) (ELit LTXT) && expr_eqb (nth 12 regs (ELit 0)) (ELit 4))%bool
        else if Z.eqb pc PC_WD then
          (negb (PRE0 i) && negb (AD i) && negb (WDD i) && negb (LD i) &&
           call_j wd_chk (fun j cj ci => Bool.eqb (PA j) (PA i) && WDD j && negb (AD j) && negb (LD j) && negb (FLG j) && Nat.ltb 54 (CC.cp_nx cj) && Z.eqb (CH2.ci_csp ci) (-192))%bool i k c ps
           && CL.ps_reg_is ps 10 (EAlu ALU_ADD VE (ELit 252)) && CL.ps_reg_is ps 11 (EAlu ALU_ADD VE (ELit 8))
           && has cells (KWord (SA VE 252) 1 (ELit 0)) && has cells (KWord (SA VE 256) 4 (ELit 0)) && has cells (KWord (SA VE 260) 1 DPE))%bool
        else if Z.eqb pc PC_SETSH then
          (negb (PRE0 i) &&
           call_j (fun c ps cj BLi FFi BLj FFj => CHA.custom_chk GT.NF GD.HDECL GT.SCELLS GT.GLO GT.GHI 256 0 BLi FFi [(CHA.SRL3 FE, SB, ELit (ff_bytes 4 / 8))] (STATU ++ FLAG) None c ps cj BLi FFi BLj FFj)
                  (fun j cj ci => FLG j && Bool.eqb (PA j) (PA i) && Bool.eqb (AD j) (AD i) && Bool.eqb (WDD j) (WDD i) && Bool.eqb (LD j) (LD i) && (AD i || WDD i) && CHA.frames_eqb (nth j FFS []) (nth i FFS []) && CH2.blocks_eqb (nth j GD.BLS []) (nth i GD.BLS [])
                                  && Nat.ltb 54 (CC.cp_nx cj))%bool i k c ps
           && CL.ps_reg_is ps 10 SHF && CL.ps_reg_is ps 11 (ELit (ff_bytes 4 / 8))
          )%bool
        else false
        end)%bool
  end.
Lemma leaf_ok : CH2.leaves_all GD.CPS GD.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF GD.HDECL GD.BLS FFS GD.CPS GD.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stat_ok : forallb (CHA.static_chk GT.SCELLS GT.GLO GT.GHI) STAT = true.
Proof. vm_compute. reflexivity. Qed.
Lemma statu_ok : forallb (CHA.static_chk GT.SCELLS GT.GLO GT.GHI) STATU = true.
Proof. vm_compute. reflexivity. Qed.
Lemma bls_i : forall i, (i < 46)%nat -> nth i GD.BLS [] = BL1.
Proof. intros i H. do 46 (destruct i as [|i]; [reflexivity|]). lia. Qed.
Lemma ffs_i : forall i, (i < 46)%nat -> nth i FFS [] = (if Nat.ltb i 2 then [] else [FRR]).
Proof. intros i H. do 46 (destruct i as [|i]; [reflexivity|]). lia. Qed.
Lemma nx_all : forall i c, nth_error GD.CPS i = Some c -> (54 < CC.cp_nx c \/ i < 2)%nat.
Proof.
  intros i c H. unfold GD.CPS in H. do 46 (destruct i as [|i]; [cbn [nth_error] in H; injection H as <-; first [left; apply Nat.ltb_lt; vm_compute; reflexivity | right; lia]|]).
  destruct i; cbn [nth_error] in H; discriminate H.
Qed.
Lemma bvn : CH2.blocks_vars_lt GT.NF BL1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma txt_null : L5.bytes_at RSEGS (fun _ => None) LTXT [110; 117; 108; 108].
Proof. intros i Hi. cbn [length] in Hi. repeat (destruct i as [|i]; [vm_compute; reflexivity|]). exfalso. lia. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
Lemma lit_wr : StreamSim.wseg_ok RSEGS (Z_to_bv 64 LS_) 18 = true.
Proof. vm_compute. reflexivity. Qed.
End EVDNA.
