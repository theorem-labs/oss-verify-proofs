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
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxQNode FxMNode FxRunPostM AsanCpS.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanQcsNode.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanQcsNode AsanQSSites AsanPNodes FxPNodesX AsanTblH2 AsanBodyE AsanBodyG AsanBNodes.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQcsX OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxRunPostM OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCpS OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQcsNode.AsanRpNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQcsNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQSSites OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanPNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxPNodesX OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTblH2 OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyE OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyG OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBNodes.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition NQ : Type := (anode2 + xnode) + (pnode + bnode).
Definition MCQ : Type := @mchain NQ.
Definition apostQ : NQ -> sst -> smodel -> ast -> option (sst * smodel * ast) :=
  apostP (apostS (apost_alloc2 LIM) (apost_x IMGMd)) (FxPNodesX.ppostS (ppostA IMGMd QSITES_P MCSITES_P) (ppostB IMGH)).
Definition A1Q (nk : anode) (k : MCQ) : MCQ := MCall (inl (inl (A1 nk))) k.
Definition XN (x : xnode) (k : MCQ) : MCQ := MCall (inl (inr x)) k.
Definition A2 (n : anode2) (k : MCQ) : MCQ := MCall (inl (inl n)) k.
Definition PN (p : pnode) (k : MCQ) : MCQ := MCall (inr (inl p)) k.
Definition BN (b : bnode) (k : MCQ) : MCQ := MCall (inr (inr b)) k.

Definition STOPS_Q : list Z := [0x44004; 0x73c38; 0x81f7c; 0x82908; 0x401d8; 0x4467c; 0xd4904; 0x639d4; 0xd4500; 0x8fe04; 0x5329c; 0x61420; 0x61468; 0x615bc; 0x3fd4c; 0x613f8; 0x3fdf8; 0x3ff50].
Definition SEG (pc : Z) (node : MCQ -> MCQ) (k : MCQ) : MCQ := MSegK 20 (PRun F60000 STOPS_Q []) (KCons pc 0 (node k) KNil).
Definition ID (k : MCQ) : MCQ := k.
Definition TG_VN : lin := rget (s_regs TG0_S) (rkey (xr 8)).
Definition VN : positive := match l_t TG_VN with (x, _) :: _ => x | [] => 1%positive end.
Definition VQ : positive := s_next TG0_S.
Definition VR : positive := Pos.succ VQ.

(* [comment removed for export] *)
Definition VGC_of (F : sst) : option (positive * Z) :=
  match l_t (rget (s_regs F) (rkey (xr 10))) with [(v, 8)] => Some (v, l_c (rget (s_regs F) (rkey (xr 10))) / 8) | _ => None end.
Definition VGS : positive := 30000%positive.
Definition VQS : positive := 30001%positive.
Definition fin3 : Type := (sst * smodel * list lin)%type.
(* [comment removed for export] *)
Definition norm1 (F : sst) (M : smodel) (al : list lin) : fin3 :=
  match VGC_of F with
  | Some (v, c) => let σ := tset v (laddc (lvar VGS) (- c)) TEmpty in
                   (ssubst σ (Pos.max (s_next F) (Pos.succ VGS)) F, msubst σ M, List.map (lsubst σ) al)
  | None => (F, M, al)
  end.
(* [comment removed for export] *)
Definition sym_final (x : fin3) : bool :=
  match is_const (rget (s_regs (fst (fst x))) (rkey (xr 8))) with Some _ => false | None => true end.
Definition norm_q (x : fin3) : fin3 :=
  let '((F, M), al) := x in
  let σ := tset VQ (lvar VQS) TEmpty in
  (ssubst σ (Pos.max (s_next F) (Pos.succ VQS)) F, msubst σ M, List.map (lsubst σ) al).
Definition sh_sig : tree lin :=
  fold_left (fun σ i => let v := Pos.of_nat (Pos.to_nat VQ + i) in tset v (lvar (Pos.add v 20000%positive)) σ) (List.seq 0 1000) TEmpty.
(* [comment removed for export] *)
Definition fvars (f : fact) : list positive :=
  match f with
  | FCond _ a b _ => List.map fst (l_t a) ++ List.map fst (l_t b)
  | FRange l _ _ | FMod l _ _ | FBits l _ _ => List.map fst (l_t l)
  | FByte x v _ => List.map fst (l_t x) ++ List.map fst (l_t v)
  | FBytes x bs => xH :: List.map fst (l_t x)          (* [comment removed for export] *)
  end.
Definition var_pub (x : positive) : bool := if Pos.ltb x VQ then true else if Pos.eqb x VQ then true else if Pos.eqb x VR then true else if Pos.eqb x VQS then true else Pos.eqb x VGS.
(* [comment removed for export] *)
Definition hull_fact (oth : list (list fact * tree lin)) (l : lin) : list fact :=
  let rs := List.map (fun o => irange (fst o) (lsubst (snd o) l)) oth in
  match rs with
  | [] => []
  | r0 :: rr => let lo := fold_left Z.min (List.map fst rr) (fst r0) in let hi := fold_left Z.max (List.map snd rr) (snd r0) in
                if (Z.leb 0 lo && Z.ltb hi (two64 - 1))%bool then [FRange l lo hi] else []
  end.
Definition all_imply (oth : list (list fact * tree lin)) (f : fact) : bool := forallb (fun o => fact_implied (fst o) (fsubst (snd o) f)) oth.
Definition common_facts (base : list fact) (oth : list (list fact * tree lin)) : list fact :=
  List.flat_map (fun f => if forallb var_pub (fvars f) then
                            (if all_imply oth f then [f] else match f with FRange l _ _ => hull_fact oth l | _ => [] end) else []) base.
(* [comment removed for export] *)
Definition fix_cells (P : sst) (cst : list (sst * tree lin)) : list region :=
  let cell_ok (i : nat) (kv : positive * bval) : bool :=
    forallb (fun Fσ => match nth_error (s_rgs (fst Fσ)) i with
                       | Some Ri => match tget (fst kv) (rg_cont Ri) with Some v => bval_ent v (bsubst (snd Fσ) (snd kv)) | None => false end
                       | None => false
                       end) cst in
  (* [comment removed for export] *)
  let fix_rg (i : nat) (R : region) : region :=
    match rg_kind R with
    | RW | RZ => let el := FxCall.telems (rg_cont R) in
                 if forallb (cell_ok i) el then R
                 else RG (rg_base R) (rg_size R) RW (fold_left (fun t kv => tset (fst kv) (snd kv) t) (List.filter (cell_ok i) el) TEmpty)
    | _ => R
    end in
  List.map (fun ir => fix_rg (fst ir) (snd ir)) (List.combine (List.seq 0 (List.length (s_rgs P))) (s_rgs P)).
(* [comment removed for export] *)
Definition gen_core (ren : bool) (xf : list fact) (L : list (sst * smodel)) (As : list (list lin)) : option (sst * smodel * list lin) :=
  let N0 := List.map (fun '((F, M), al) => norm1 F M al) (List.combine L As) in
  let N := if ren then List.map norm_q (List.filter sym_final N0) else N0 in
  match genLA (List.map (fun x => fst x) N) (List.map (fun x => snd x) N) with
  | Some (P0, MP0, als0) =>
      let '(P, MP, als) := if ren then (ssubst sh_sig (Pos.add VQ 21001%positive) P0, msubst sh_sig MP0, List.map (lsubst sh_sig) als0) else (P0, MP0, als0) in
      (* [comment removed for export] *)
      let Fσ := List.map (fun '((F, M), al) => (F, matchLA F M al P MP als)) (List.combine L As) in
      let oth := List.map (fun x => (s_facts (fst x), snd x)) Fσ in
      let base := match N with x :: _ => s_facts (fst (fst x)) | [] => [] end in
      let dedup (l : list fact) : list fact := List.rev (fold_left (fun acc f => if existsb (fact_eqb f) acc then acc else f :: acc) l []) in
      let fs := dedup (xf ++ hull_fact oth (lvar VGS) ++ List.filter (all_imply oth) (s_facts P) ++ common_facts base oth) in
      Some (SST (s_pc P) (s_regs P) (fix_cells P Fσ) fs (s_next P) (s_resv P), MP, als)
  | None => None
  end.
Definition gen_vg (qlo qhi : Z) := gen_core false [FRange (lvar VQ) qlo qhi].
Definition gen_vgq (qlo qhi : Z) := gen_core true [FRange (lvar VQS) qlo qhi].
Definition gen_vg0 := gen_core false [].

(* [comment removed for export] *)
Definition SURG (rz : Z) (r0 q0 : bool) (k : MCQ) : MCQ :=
  let cut (k : MCQ) := if Z.eqb rz 16 then k else BN (BSplit2 0 (rz - 16)) k in
  let h : nat := if Z.eqb rz 16 then 0%nat else 1%nat in           (* [comment removed for export] *)
  let lsh : nat := if r0 then (h + 2)%nat else (h + 3)%nat in      (* [comment removed for export] *)
  let give1 := if Z.eqb rz 16 then [lsh] else [0%nat; lsh] in
  let h' : nat := 0%nat in                                         (* [comment removed for export] *)
  if r0 then cut (A2 (NGiveX give1) (A2 (NExtHull 0 h' (h' + 1)) k))
  else cut (A2 (NGiveX give1) (A2 (NExtHull 0 h' (h' + 2)) (A2 (NGiveX [(h' + 2)%nat]) k))).

(* [comment removed for export] *)
Fixpoint bucket_tree (bk : list Z) (leaf : MCQ) : MCQ :=
  match bk with [] => leaf | b :: r => MSplit (lvar VQ) b leaf (bucket_tree r leaf) end.
Definition KSTATS (bk : list Z) (k : MCQ) : MCQ :=
  match bk with
  | [] => SEG 0x3ff50 ID k
  | _ => MJoinL (bucket_tree bk (SEG 0x3ff50 ID MEnd)) 0x3ff50 k
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KCHK (inl_chk q0 : bool) (k : MCQ) : MCQ :=
  if inl_chk then SEG 0x61420 (BN (BQrS 3)) (SEG 0x61468 (fun k => if q0 then BN (BSplit2 3 2) (XN (XQcs 1) k) else XN (XQcs 1) k) k)
  else SEG 0x639d4 (BN BRpS) (SEG 0x639d4 (BN BRpS) k).
(* [comment removed for export] *)
Definition KBIG (r0 : bool) (k : MCQ) : MCQ := BN (BMergeS 1) (BN (BSplitReg 1 10 12) (BN (BFront (if r0 then 1%nat else 2%nat)) k)).
Definition KGRPg (sg : MCQ) (rz : Z) (r0 q0 inl_chk big : bool) (bk : list Z) : MCQ :=
  let tail := SEG 0x3fdf8 ID (KSTATS bk (SEG 0xd4904 (A1Q NMsetC) (SEG 0x613f8 (fun k => if big then KBIG r0 (BN BOvl k) else BN BOvl k) (KCHK inl_chk q0
                (SEG 0xd4500 (BN BCps) (SEG 0x8fe04 ID sg)))))) in
  MSegK 20 P_MAL_U (KCons 0x82908 0 (A1Q NUnw
    (SEG 0x44004 (A2 NPopG) (SEG 0x81f7c (A1Q NPut) (SEG 0x3fd4c (BN (BBand 0))
      (if q0 then tail else SEG 0xd4904 (A1Q NMset) tail))))) KNil).
Definition KGRPb (rz : Z) (r0 q0 inl_chk big : bool) (bk : list Z) : MCQ := KGRPg (SURG rz r0 q0 MEnd) rz r0 q0 inl_chk big bk.
Definition KGRP (rz : Z) (r0 q0 inl_chk : bool) (bk : list Z) : MCQ := KGRPg (SURG rz r0 q0 MEnd) rz r0 q0 inl_chk false bk.

(* [comment removed for export] *)
Fixpoint qtree (l : list (Z * MCQ)) (last : MCQ) : MCQ :=
  match l with [] => last | (b, k) :: r => MSplit (lvar VQ) b k (qtree r last) end.
(* [comment removed for export] *)
Definition GROUPS_R1 : list (Z * MCQ) :=
  [(0, KGRP 16 false true true []); (5, KGRP 16 false false true []); (7, KGRP 32 false false true []); (11, KGRP 32 false false false []);
   (55, KGRP 64 false false false []); (495, KGRP 128 false false false [110; 238; 494]);
   (511, KGRP 256 false false false []); (2015, KGRPb 256 false false false true [990; 2014]);          (* [comment removed for export] *)
   (4031, KGRPb 512 false false false true [4030]); (8063, KGRPb 1024 false false false true [8062])].
(* [comment removed for export] *)
Definition GROUPS_R0 : list (Z * MCQ) :=
  [(0, MVoid);                                                                                           (* [comment removed for export] *)
   (1, BN (BConc VQ) (KGRP 16 true false true []));                                                      (* [comment removed for export] *)
   (6, KGRP 16 true false true []); (8, KGRP 32 true false true []); (12, KGRP 32 true false false []);
   (56, KGRP 64 true false false []); (496, KGRP 128 true false false [111; 239; 495]);
   (511, KGRP 256 true false false []); (512, BN (BConc VQ) (KGRP 256 true false false []));           (* [comment removed for export] *)
   (2016, KGRPb 256 true false false true [991; 2015]);
   (4032, KGRPb 512 true false false true [4031]); (8064, KGRPb 1024 true false false true [8063])].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KPRE_R1 (kf : MCQ) : MCQ := MJoinG (gen_vg 1 8063) (qtree (List.tl GROUPS_R1) MEnd) 0x8fe04 kf.
Definition KPRE_Q0 (kf : MCQ) : MCQ := BN (BConc VQ) (MJoinG gen_vg0 (KGRP 16 false true true []) 0x8fe04 kf).
Definition KPRE_R0 (kf : MCQ) : MCQ := BN (BConc VR) (MJoinG (gen_vgq 1 8064) (qtree GROUPS_R0 MEnd) 0x8fe04 kf).
(* [comment removed for export] *)
Definition KPRE_C (k0 k1 kq : MCQ) : MCQ := BN (BPlaceW 0) (BN (BDec VN 3) (MSplit (lvar VR) 0 (KPRE_R0 k0) (MSplit (lvar VQ) 0 (KPRE_Q0 kq) (KPRE_R1 k1)))).
Definition KPRE (k0 k1 kq : MCQ) : MCQ := BN (BDec VN 3) (A2 NConvA (MSplit (lvar VR) 0 (KPRE_R0 k0) (MSplit (lvar VQ) 0 (KPRE_Q0 kq) (KPRE_R1 k1)))).

(* [comment removed for export] *)
Definition QU : positive := 30001%positive.
Definition TU : positive := 30002%positive.
Definition SBU : positive := 30003%positive.
Definition XU : positive := 30004%positive.
(* [comment removed for export] *)
Definition SURG_U (rz : Z) (r0 q0 : bool) (spl : option lin) (k : MCQ) : MCQ :=
  let cut (k : MCQ) := if Z.eqb rz 16 then k else BN (BSplit2 0 (rz - 16)) k in
  let h : nat := if Z.eqb rz 16 then 0%nat else 1%nat in           (* [comment removed for export] *)
  let lsh : nat := if r0 then (h + 2)%nat else (h + 3)%nat in      (* [comment removed for export] *)
  let fin (k : MCQ) := k in
  cut (BN (BSplit2 lsh (rz / 8 - 1)) (BN (BTrack1 (lsh + 1))
    (if r0 then
       match spl with
       | Some m =>    (* [comment removed for export] *)
           BN (BSplitZ (lsh + 2) m) (BN (BTrack1 (lsh + 3)) (BN (BMergeTZ (lsh + 1))        (* [comment removed for export] *)
             (A2 (NGiveX (if Z.eqb rz 16 then [lsh] else [0%nat; lsh])) (A2 (NExtHull 0 0 1) k))))
       | None =>      (* [comment removed for export] *)
           BN (BTrack1 (lsh + 2)) (A2 (NGiveX [lsh]) (A2 (NExtHull 0 0 1) k))
       end
     else if q0 then  (* [comment removed for export] *)
       A2 (NGiveX [lsh]) (A2 (NExtHull 0 0 2) (BN (BMergeS 1) k))      (* [comment removed for export] *)
     else             (* [comment removed for export] *)
       BN (BMergeTZ (lsh + 1)) (A2 (NGiveX (if Z.eqb rz 16 then [lsh] else [0%nat; lsh])) (A2 (NExtHull 0 0 2) (BN (BMergeS 1) k)))))).
Definition SPLQ : option lin := Some (laddc (lvar VQ) (-1)).
Definition KU (rz : Z) (r0 q0 inl_chk big : bool) (spl : option lin) (bk : list Z) : MCQ := KGRPg (SURG_U rz r0 q0 spl MEnd) rz r0 q0 inl_chk big bk.
Definition GROUPS_R1U : list (Z * MCQ) :=
  [(5, KU 16 false false true false None []); (7, KU 32 false false true false None []); (11, KU 32 false false false false None []);
   (55, KU 64 false false false false None []); (495, KU 128 false false false false None [110; 238; 494]);
   (511, KU 256 false false false false None []); (2015, KU 256 false false false true None [990; 2014]);
   (4031, KU 512 false false false true None [4030]); (8063, KU 1024 false false false true None [8062])].
Definition GROUPS_R0U : list (Z * MCQ) :=
  [(0, MVoid); (1, BN (BConc VQ) (KU 16 true false true false None []));
   (6, KU 16 true false true false SPLQ []); (8, KU 32 true false true false SPLQ []); (12, KU 32 true false false false SPLQ []);
   (56, KU 64 true false false false SPLQ []); (496, KU 128 true false false false SPLQ [111; 239; 495]);
   (511, KU 256 true false false false SPLQ []); (512, BN (BConc VQ) (KU 256 true false false false (Some (lconst 511)) []));
   (2016, KU 256 true false false true SPLQ [991; 2015]);
   (4032, KU 512 true false false true SPLQ [4031]); (8064, KU 1024 true false false true SPLQ [8063])].
(* [comment removed for export] *)
Definition r1_final (x : fin3) : bool := match l_t (rget (s_regs (fst (fst x))) (rkey (xr 8))) with [_; _] => true | _ => false end.
Definition norm_u (x : fin3) : fin3 :=
  let '((F, M), al) := x in
  let σ := tset VQ (lvar QU) (tset VR (laddc (lvar TU) 1) TEmpty) in
  (ssubst σ (Pos.max (s_next F) (Pos.succ XU)) F, msubst σ M, List.map (lsubst σ) al).
Definition set_cell1 (R : region) (v : bval) : region := RG (rg_base R) (rg_size R) (rg_kind R) (tset 1%positive v TEmpty).
Definition patch_ab (rgs : list region) : list region :=
  match rgs with
  | H :: U :: A :: B :: rest => H :: U :: set_cell1 A (BV (lvar XU) 0) :: set_cell1 B (BV (lvar SBU) 0) :: rest
  | _ => rgs
  end.
Definition XF_U : list fact :=
  [FRange (lvar QU) 0 8063; FRange (lvar TU) 0 7; FRange (lvar SBU) 0 7; FRange (lvar XU) 0 255;
   FRange (lsub (laddc (lvar TU) 1) (lvar SBU)) 0 8; FMod (lsub (laddc (lvar TU) 1) (lvar SBU)) 3 0].
Definition var_pub_u (x : positive) : bool := if Pos.ltb x VQ then true else if Pos.eqb x VGS then true else if Pos.eqb x QU then true else Pos.eqb x TU.
Definition gen_u (L : list (sst * smodel)) (As : list (list lin)) : option (sst * smodel * list lin) :=
  let N0 := List.map (fun '((F, M), al) => norm1 F M al) (List.combine L As) in
  let N := List.map norm_u (List.filter r1_final N0) in
  match genLA (List.map (fun x => fst x) N) (List.map (fun x => snd x) N) with
  | Some (P0, MP0, als0) =>
      let P1 := ssubst sh_sig (Pos.add VQ 21001%positive) P0 in let MP := msubst sh_sig MP0 in let als := List.map (lsubst sh_sig) als0 in
      let P := SST (s_pc P1) (s_regs P1) (patch_ab (s_rgs P1)) (s_facts P1) (s_next P1) (s_resv P1) in
      let Fσ := List.map (fun '((F, M), al) => (F, matchLA F M al P MP als)) (List.combine L As) in
      let oth := List.map (fun x => (s_facts (fst x), snd x)) Fσ in
      let base := match N with x :: _ => s_facts (fst (fst x)) | [] => [] end in
      let dedup (l : list fact) : list fact := List.rev (fold_left (fun acc f => if existsb (fact_eqb f) acc then acc else f :: acc) l []) in
      let cf := List.flat_map (fun f => if forallb var_pub_u (fvars f) then
                                          (if all_imply oth f then [f] else match f with FRange l _ _ => hull_fact oth l | _ => [] end) else []) base in
      let fs0 := dedup (XF_U ++ hull_fact oth (lvar VGS) ++ List.filter (all_imply oth) (s_facts P) ++ cf) in
      (* [comment removed for export] *)
      let rgs' := fix_cells P Fσ in
      let LS := live_set (SST (s_pc P) (s_regs P) rgs' [] (s_next P) (s_resv P)) MP FSDone (ShEmit [] 0) (List.concat (List.map lin_vars als)) in
      let fs := List.filter (fact_live 1%positive LS) fs0 in
      Some (SST (s_pc P) (s_regs P) rgs' fs (s_next P) (s_resv P), MP, als)
  | None => None
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KPRE_ULg (gen : list (sst * smodel) -> list (list lin) -> option (sst * smodel * list lin)) (conv : bool) (kl0 kl1 kf : MCQ) : MCQ :=
  BN (BPlaceW 0) (BN (BDec VN 3) ((fun k => if conv then A2 NConvA k else k)
    (MJoinG gen (MSplit (lvar VR) 0 (BN (BConc VR) (qtree GROUPS_R0U kl0))
                     (MSplit (lvar VQ) 0 (BN (BConc VQ) (KU 16 false true true false None [])) (qtree GROUPS_R1U kl1))) 0x8fe04 kf))).
Definition KPRE_UL (conv : bool) (kl0 kl1 kf : MCQ) : MCQ := KPRE_ULg gen_u conv kl0 kl1 kf.
Definition KPRE_U (conv : bool) (kf : MCQ) : MCQ := KPRE_UL conv MEnd MEnd kf.
(* [comment removed for export] *)
Definition TG_GP : sst := add_fact TG0_S (FRange TG_VN 1 64512).
(* [comment removed for export] *)
Definition TG_GL : sst := add_fact TG0_S (FRange TG_VN 64513 67108857).
(* [comment removed for export] *)
