(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall FxEnt FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChEntM FxChSubst FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEntM OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSubst OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanEntry AsanPlan AsanStart AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF AsanMainWF.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainWF.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcFam AcSubst AcPri AcConvA AcNPop AcNPopG.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcFam2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcSubst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPopG OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2.AcExt OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanQcsX FxMchr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxQNode FxMNode AsanPNodes FxPNodesX AsanTblH2 AsanBodyE AsanBodyG AsanBNodes AsanPrefixG AsanPrefixLg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQcsX OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanPNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxPNodesX OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTblH2 OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyE OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanPrefixG OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanPrefixLg.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition VP : positive := Pos.succ VR.
Definition VS : positive := Pos.succ VP.
Definition MPU : positive := 30005%positive.      (* [comment removed for export] *)
Definition UBU : positive := 30006%positive.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition front_list (fr : list nat) (n : nat) : list nat := fr ++ List.filter (fun i => negb (existsb (Nat.eqb i) fr)) (List.seq 0 n).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FRONT5 (k : MCQ) : MCQ := BN (BFront 5) (BN (BFront 5) (BN (BFront 8) (BN (BFront 5) (BN (BFront 5) k)))).
Definition SURGL (sh : lshape) (k : MCQ) : MCQ :=
  if ls_r0 sh then
    BN (BSplit2 0 6128) (BN (BSplit2 6 255) (BN (BTrack1 7) (BN (BSplitZ 4 (laddc (QF VP VS sh) (-1))) (BN (BTrack1 5)
      (FRONT5 (BN (BMergeTZ 2) k))))))
  else
    BN (BSplit2 0 6128) (BN (BSplit2 7 255) (BN (BTrack1 8) (FRONT5 (BN (BMergeTZ 2) k)))).
Definition KINT (sh : lshape) (k : MCQ) : MCQ :=
  BN (BMergeS 1) (BN (BSplitReg 1 10 12) (BN (BFront 2) (BN BOvl
    (SEG 0x639d4 (BN BRpS) (SEG 0x639d4 (BN BRpS) (SEG 0xd4500 (BN BCps) (SEG 0x8fe04 ID (SURGL sh k)))))))).
(* [comment removed for export] *)
Fixpoint find_pri (gs : list (lin * lin * gkind)) (i : nat) : nat :=
  match gs with
  | [] => i
  | g :: r => match is_const (snd (fst g)) with Some 137439023104 => i | _ => find_pri r (Datatypes.S i) end
  end.
Definition IPRI_G : nat := Eval vm_compute in Datatypes.S (find_pri (sm_maps TG0_M) 0).
(* [comment removed for export] *)
Definition ZMAXL : Z := 8389632.
Definition KLG (sh : lshape) : MCQ := KLARGE A1Q BN (A1Q NPut) P_MAL_U VP VS IPRI_G sh (KINT sh (MAllowW 0 ZMAXL MEnd)).

(* [comment removed for export] *)
Definition ls1m_final (x : fin3) : bool :=
  match l_t (rget (s_regs (fst (fst x))) (rkey (xr 8))) with [_; _; _] => true | _ => false end.     (* [comment removed for export] *)
Definition norm_ul (x : fin3) : fin3 :=
  let '((F, M), al) := x in
  let σ := tset VP (laddc (lvar MPU) (-3)) (tset VS (LIN 1536 [(QU, 1); (MPU, 18446744073709551104)]) (tset VR (laddc (lvar TU) 1) TEmpty)) in
  (ssubst σ (Pos.max (s_next F) (Pos.succ MPU)) F, msubst σ M, List.map (lsubst σ) al).
Definition XF_UL : list fact :=
  [FRange (lvar QU) 8063 8388607; FRange (lvar TU) 0 7; FRange (lvar SBU) 0 7; FRange (lvar XU) 0 255; FRange (lvar MPU) 17 16386;
   FRange (lsub (laddc (lvar TU) 1) (lvar SBU)) 0 8; FMod (lsub (laddc (lvar TU) 1) (lvar SBU)) 3 0;
   FRange (LIN 18446744073709543416 [(QU, 18446744073709551608); (MPU, 4096)]) 0 4088;      (* [comment removed for export] *)
   FRange (lvar UBU) 0 34359738367].
Definition var_pub_ul (x : positive) : bool := if Pos.ltb x VQ then true else if Pos.eqb x QU then true else if Pos.eqb x TU then true else if Pos.eqb x MPU then true else Pos.eqb x UBU.
Definition gen_ul (L : list (sst * smodel)) (As : list (list lin)) : option (sst * smodel * list lin) :=
  let N0 := List.map (fun '((F, M), al) => ((F, M), al)) (List.combine L As) in
  let N := List.map norm_ul (List.filter ls1m_final N0) in
  match genLA (List.map (fun x => fst x) N) (List.map (fun x => snd x) N) with
  | Some (P0, MP0, als0) =>
      let P1a := ssubst sh_sig (Pos.add VQ 21001%positive) P0 in let MPa := msubst sh_sig MP0 in let alsa := List.map (lsubst sh_sig) als0 in
      (* [comment removed for export] *)
      let σb := match sm_maps MPa with
                | g :: _ => match l_t (fst (fst g)) with [(v1, 65536); (v2, 4096)] => tset v1 (lconst 0) (tset v2 (lvar UBU) TEmpty) | _ => TEmpty end
                | [] => TEmpty
                end in
      let P1 := ssubst σb (s_next P1a) P1a in let MP := msubst σb MPa in let als := List.map (lsubst σb) alsa in
      let P := SST (s_pc P1) (s_regs P1) (patch_ab (s_rgs P1)) (s_facts P1) (s_next P1) (s_resv P1) in
      let Fσ := List.map (fun '((F, M), al) => (F, matchLA F M al P MP als)) (List.combine L As) in
      let oth := List.map (fun x => (s_facts (fst x), snd x)) Fσ in
      let base := match N with x :: _ => s_facts (fst (fst x)) | [] => [] end in
      let dedup (l : list fact) : list fact := List.rev (fold_left (fun acc f => if existsb (fact_eqb f) acc then acc else f :: acc) l []) in
      let cf := List.flat_map (fun f => if forallb var_pub_ul (fvars f) then
                                          (if all_imply oth f then [f] else match f with FRange l _ _ => hull_fact oth l | _ => [] end) else []) base in
      let fs0 := dedup (XF_UL ++ List.filter (all_imply oth) (s_facts P) ++ cf) in
      let rgs' := fix_cells P Fσ in
      let LS := live_set (SST (s_pc P) (s_regs P) rgs' [] (s_next P) (s_resv P)) MP FSDone (ShEmit [] 0) (List.concat (List.map lin_vars als)) in
      let fs := List.filter (fact_live 1%positive LS) fs0 in
      Some (SST (s_pc P) (s_regs P) rgs' fs (s_next P) (s_resv P), MP, als)
  | None => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KPRE_Lg (gen : list (sst * smodel) -> list (list lin) -> option (sst * smodel * list lin)) (kf : MCQ) : MCQ :=
  BN (BPlaceW 0) (BN (BDec VN 3) (BN (BDec VQ 9)
    (MJoinG gen
       (MSplit (lvar VR) 0
          (BN (BConc VR) (MSplit (lvar VS) 0 (BN (BConc VS) (KLG LS_00)) (KLG LS_0M)))
          (MSplit (lvar VS) 510 (KLG LS_1M) (BN (BConc VS) (KLG LS_1X))))
       0x8fe04 kf))).
Definition KPRE_L (kf : MCQ) : MCQ := KPRE_Lg gen_ul kf.
(* [comment removed for export] *)
