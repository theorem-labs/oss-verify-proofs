(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep FxChFix FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AXG_put AXG_put3 AXG_np AXG_nf1 AXG_npf.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcMrg.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHand.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcCarve AcSteps AcEntry AcMALp AcHand AcUnwApp0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcDepDen AcAst AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcCarveP AcMALlib AcPutN AcTbl AcConv AcConvG.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChAdd.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFixNew.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcNPop.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHand.AcMrg0 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcCarve OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcSteps OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcEntry OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHand OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp0 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcShapes0.AcPutAppG OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcShapes0.AcShapes OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcShapes0 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib.AcFacts OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcCarveP OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPutN OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcTbl OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConv OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvG OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvA.AcRdw OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd.AcAddOwn OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvA OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFixNew.AcFixS OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcNPop.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Fixpoint tcls_acc (k : nat) (c nd : Z) : Z :=
  match k with O => 0 | Datatypes.S k' => if Z.leb nd (sz_tbl c) then c else tcls_acc k' (c + 1) nd end.
Definition tcls (nd : Z) : Z := tcls_acc 30 1 nd.
Definition crange (clo chi : Z) : list Z := List.map (fun i => clo + Z.of_nat i) (seq 0 (Z.to_nat (chi - clo + 1))).

(* [comment removed for export] *)
Fixpoint set_classes (vj : positive) (cs : list Z) (pri : list lin) : list lin :=
  match cs with
  | [] => pri
  | c :: r => set_classes (vj + 2) r (set_nth (6 + 2 * cidx c) (lvar (vj + 1)) (set_nth (5 + 2 * cidx c) (lvar vj) pri))
  end.
Fixpoint class_facts (fs : list fact) (a : ast) (vj : positive) (cs : list Z) : list fact :=
  match cs with
  | [] => []
  | c :: r => FRange (lvar vj) (fst (irange fs (p_j a c))) (snd (irange fs (p_j a c)) + 1) :: FRange (lvar (vj + 1)) 0 262144 ::
              (* [comment removed for export] *)
              FRange (lsub (lvar vj) (p_j a c)) 0 1 ::
              class_facts fs a (vj + 2) r
  end.
(* [comment removed for export] *)
Definition a_gstep (a : ast) (pri : list lin) (ext : region) : ast :=
  let a0 := with_pri a (a_own a) pri in
  AST (a_on a) (ext :: a_rgs a) (a_fcts a) (own_of (fst (a_dep a)) (snd (a_dep a)) ++ pri_own a0) (a_dep a) (a_nl a) (a_live a) pri.

Definition np_front_f (S : sst) (n : positive) (rgs : list region) (fs : list fact) : sst := SST 0x43ce8 (s_regs S) rgs fs n RNone.

Definition apost_npopg0 (LIMIT : Z) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  let SPl := rget (s_regs S) (rk 2) in let fs := s_facts S in let ND := rget (s_regs S) (rk 12) in
  obool (a_on a &&& Nat.eqb (List.length (a_pri a)) PRI_LEN &&& Z.eqb (s_pc S) 0x43ce8 &&& rsv_none_b (s_resv S) &&&
         list_eqb pair_eqb (sm_own M) (a_own a)) (
  obind (ldiv8 ND) (fun ND8 =>
  obind (find_stk (s_rgs S) SPl) (fun stk =>
  obind (find_ro (s_rgs S)) (fun ro =>
  obind (find_rg_acc' (rg_is (laddc (p_tg a) 2872) 16 RW) (s_rgs S) O) (fun ist =>
  obind (nth_error (s_rgs S) stk) (fun R =>
  obind (lin_off SPl (rg_base R)) (fun o =>
  obind (carve_of S stk [o - 2048; o] [Datatypes.S stk; ro_split ro stk 2; ro_split ist stk 2]) (fun cv =>
  obind (find_grant (sm_maps M) (p_pg a) PG_SIZE) (fun jP =>
  obind (find_grant (sm_maps M) (p_tg a) TG_SIZE) (fun jT =>
  obind (nth_error (sm_maps M) jP) (fun gP =>
  let front := firstn 3 (carve_rgs cv) in let rest := skipn 3 (carve_rgs cv) in
  let L := np_front S (s_next S) front in
  let Sp := np_rest S rest in
  let lohi := irange fs SPl in let ndr := irange fs ND in let sbr := irange fs (p_sb a) in
  let clo := tcls (fst ndr) in let chi := tcls (snd ndr) in let cs := crange clo chi in
  (* [comment removed for export] *)
  let VC := s_next S in let n0 := (s_next S + 1)%positive in
  let Lg := np_front_f S n0 front [FRange (lvar VC) clo chi] in
  let rbg := ladd (p_sb a) (lscale 4294967296 (lvar VC)) in
  let L1 := ecall_tpl Lg [0%nat; 2%nat] rbg in
  let L2 := ecall_tpl (fix_post L1 rbg) [0%nat; 2%nat] (laddc rbg 3758096384) in
  (* [comment removed for export] *)
  let Lb := np_front S (n0 + 66) front in
  let VGC := (n0 + 99)%positive in let vj0 := (VGC + 1)%positive in
  let nfin := (vj0 + Pos.of_nat (2 * List.length cs))%positive in
  let chl := lscale 8 (lvar VGC) in
  let X := with_reg (mrg (hand_post Lb 0x43f08 KALLk [0%nat; 2%nat]) Sp) (rk 10) chl in
  let ixb := inv_ix (cv_ix cv) (length (cv_split cv)) in
  let a' := a_gstep a (set_classes vj0 cs (a_pri a)) (ext_rg chl ND) in
  let M' := with_own M (a_own a') in
  let newrgs := [RG chl ND RZ TEmpty; RG (laddc (lvar VGC) SH_OFF) ND8 RW (tset 1%positive (BK 250) TEmpty)] in
  let newfacts := FRange (lvar VGC) ((fst sbr + 4294967296 * clo) / 8) ((snd sbr + 4294967296 * chi + 262144) / 8) ::
                  FMod (lvar VGC) 2 0 ::
                  (* [comment removed for export] *)
                  FRange (lsub chl (p_sb a)) (4294967296 * clo) (4294967296 * chi + 262144) :: class_facts fs a vj0 cs in
  obool (perm_ix_ok (length (cv_split cv)) (cv_ix cv) &&&
         lin_eqb (rget (s_regs S) (rk 10)) (lconst 923480) &&& lin_eqb (rget (s_regs S) (rk 11)) (p_ca a) &&& lin_eqb (rget (s_regs S) (rk 13)) (lconst 8) &&&
         Z.leb 1 (fst ndr) &&& Z.leb (snd ndr) 65536 &&&
         Z.leb (snd (irange fs ND8)) 8192 &&&      (* [comment removed for export] *)
         Z.leb 1 clo &&& Z.leb clo chi &&& Z.leb chi 30 &&&
         fact_implied fs (FMod SPl 4 0) &&& Z.leb (2^46 + 8192) (fst lohi) &&& Z.leb (snd lohi) (2^47) &&&
         rg_hdr_b (nth_error front 0) (laddc SPl (-2048)) (lconst 2048) RW &&& ro_b (nth_error front 1) &&&
         rg_hdr_b (nth_error front 2) (laddc (p_tg a) 2872) (lconst 16) RW &&&
         sb_words_ok (s_rgs S) a &&&
         forallb (fun c => Z.leb (snd (irange fs (p_j a c)) + mc_tbl c / 2 + 1) (262144 / sz_tbl c)) cs &&&   (* [comment removed for export] *)
         gkind_eqb (snd gP) GE &&& band_ok (s_facts S) M SPl &&&
         state_wf L &&& state_wf Lg &&&
         perm_ix_ok (length (s_rgs X)) ixb &&& awf nfin a' &&&
         forallb_l (pri_sep_c fs (sm_maps M) ASEGSR jP jT (sm_sp M) a) (s_rgs (mrg L Sp)) &&&
         (if forallb (fun c => Z.ltb 0 (fst (irange fs (p_j a c)))) cs then true    (* [comment removed for export] *)
          else (fu_words_ok (s_rgs S) &&& fu_tls_ok Sp (sm_maps M) a &&& envc_ok (s_rgs Sp) &&&
                fixkeep_ok_s LIMIT ASEGSR (mrg L1 Sp) M 262144 false jP GE &&&
                fixkeep_ok_s LIMIT ASEGSR (mrg L2 Sp) M 262144 false jP GE))) (
  obind (steps_rgs (s_next X) (s_facts X) (List.map (fun t => nth t (s_rgs X) (RG lc0 lc0 RW TEmpty)) ixb) (List.repeat (RMergeCC stk) 2)) (fun l'' =>
  Some (SST (s_pc X) (s_regs X) (newrgs ++ l'') (s_facts X ++ newfacts) nfin (s_resv X), M', a')))))))))))))).
(* [comment removed for export] *)
Definition apost_npopg (LIMIT : Z) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  apost_npopg0 LIMIT (with_facts S (s_facts S ++ [sp_fact M])) M a.
