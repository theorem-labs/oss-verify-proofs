(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Znumtheory List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec SeqExec CatExec CatSim.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Frame MemSplit RefMemcpyLib MuslStrlen ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare OSSVerify.Proofs.fast_float.from_chars.lib.Common.Frame OSSVerify.Proofs.fast_float.from_chars.lib.Common.MemSplit OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib OSSVerify.Proofs.fast_float.from_chars.lib.Common.MuslStrlen OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.PlacementCount OSSVerify.Proofs.fast_float.from_chars.lib.Common.AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEnt FxChStart FxChFix FxChWv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChWv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxQNode FxQRNode.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxMchr.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxMchr FxMNode FxRunPost FxSNodes AsanSNodes AsanRegP.

Module AsanRpNode.
(* [comment removed for export] *)
From Stdlib Require Import ZArith Znumtheory List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec SeqExec CatExec CatSim.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Frame MemSplit RefMemcpyLib ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare OSSVerify.Proofs.fast_float.from_chars.lib.Common.Frame OSSVerify.Proofs.fast_float.from_chars.lib.Common.MemSplit OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.PlacementCount OSSVerify.Proofs.fast_float.from_chars.lib.Common.AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEnt FxChStart FxChFix FxChWv FxChTwoC.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChWv OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChTwoC.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxQNode FxMchr FxMNode FxRunPost FxSNodes AsanSNodes AsanRegP.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxRunPost OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanRegP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Notation existsb := existsb_lz (only parsing).
Local Lemma existsb_exists : forall {A} (f : A -> bool) (l : list A), existsb_lz f l = true <-> exists x, In x l /\ f x = true.
Proof. intros A f l. rewrite existsb_lz_eq. apply List.existsb_exists. Qed.
(* [comment removed for export] *)
Local Lemma existsb_cf_exists : forall {A} (c f : A -> bool) (l : list A), existsb_cf c f l = true <-> exists x, In x l /\ f x = true.
Proof. intros A c f l. rewrite existsb_cf_eq. apply List.existsb_exists. Qed.
Import ListNotations.
Local Open Scope Z_scope.

Definition RP_PC : Z := 0x639e0.
Definition RP_HAVS : list reg := List.map xr [5; 11; 12; 13; 14; 15; 16; 17].
Definition rp_cells_list : list (Z * Z) :=
  [(0xdcc10, 0xe4db8); (0xe4db8, SB); (0xdcc18, 0xe5aa8); (0xe5aa8, 0); (0xdcc20, 0xe5ab0); (0xe5ab0, 0); (0xdcc28, 0xe5aa0); (0xe5aa0, kHighEnd)].
Definition cells_chk (img : tree Z) (fs : list fact) (rgs : list region) : bool :=
  forallb (fun p => match load_at img fs rgs (lconst (fst p)) SZ8 false with Some (Some l) => lin_eqb l (lconst (snd p)) | _ => false end) rp_cells_list.
(* [comment removed for export] *)
Fixpoint find_frame (rgs : list region) (sp : lin) (j : nat) : option (nat * Z) :=
  match rgs with
  | [] => None
  | R :: rs => match rg_kind R, is_const (rg_size R), lin_off sp (rg_base R) with
               | RW, Some sz, Some d => if (Z.leb 72 d && Z.ltb d sz)%bool then Some (j, d) else find_frame rs sp (Datatypes.S j)
               | _, _, _ => find_frame rs sp (Datatypes.S j)
               end
  end.

(* [comment removed for export] *)
Definition rp_za (S : sst) (M : smodel) (b nl : lin) : bool :=
  let fs := s_facts S in
  let '(dlo, dhi) := irange fs (lsub b (sm_sp M)) in let '(elo, ehi) := irange fs (lsub (ladd b nl) (sm_sp M)) in
  if (((Z.leb 0 dlo && Z.leb dhi (2 ^ 22)) || (Z.leb (two64 - 2 ^ 20) dlo && Z.ltb dhi two64)) &&
      ((Z.leb 0 elo && Z.leb ehi (2 ^ 22)) || (Z.leb (two64 - 2 ^ 20) elo && Z.ltb ehi two64)) &&
      existsb (fun z => (Z.eqb (fst z) HSHB && Z.eqb (snd z) SH_HI)%bool) (sm_zr M) &&
      existsb hshb_g (sm_maps M))%bool
  then (qc_allow_scan fs (sm_sp M) (sm_allow M) && forallb (qc_own2 fs (sm_maps M)) (sm_own M) && forallb (qc_rg fs (sm_maps M)) (s_rgs S))%bool      (* [comment removed for export] *)
  else false.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lal8 (b : lin) : bool := forallb (fun p => Z.eqb (snd p mod 8) 0) (l_t b).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition end_hi (fs : list fact) (b nl base : lin) (dhi nhi : Z) : Z :=
  if Z.ltb nhi (2 ^ 40) then Z.min (dhi + nhi) (snd (irange fs (lsub (ladd b nl) base))) else dhi + nhi.
Definition rp_zc1 (fs : list fact) (rgs : list region) (b nl : lin) (R0 : region) : bool :=
  let base := rg_base R0 in
  if (lal8 base && Z.eqb (l_c base mod 8) 0)%bool then
    let '(dlo, dhi) := irange fs (lsub b base) in
    if (Z.leb 0 dlo && Z.ltb dhi (2 ^ 40) && Z.ltb (snd (irange fs base) + 2 ^ 41) two64)%bool then
      match srl_lin fs 3 base with
      | Some q => existsb_cf (fun R => cand_t q (rg_base R))
                    (zero_ov fs (laddc q (SH_OFF + dlo / 8)) ((end_hi fs b nl base dhi (snd (irange fs nl)) - 1) / 8 - dlo / 8 + 1)) rgs
      | None => false
      end
    else false
  else false.
Definition rp_zc (fs : list fact) (rgs : list region) (b nl : lin) : bool := existsb_cf (fun R0 => cand_t b (rg_base R0)) (rp_zc1 fs rgs b nl) rgs.
Definition rp_zb (fs : list fact) (rgs : list region) (b nl : lin) : bool :=
  match is_const b with
  | Some c => existsb_cf (fun R => cand_t b (rg_base R)) (zero_ov fs (lconst (SH_OFF + c / 8)) ((c + snd (irange fs nl) - 1) / 8 - c / 8 + 1)) rgs
  | None =>
      if match srl_lin fs 3 b with
         | Some q => if lal8 b then existsb_cf (fun R => cand_t q (rg_base R)) (zero_ov fs (laddc q SH_OFF) ((l_c b mod 8 + snd (irange fs nl) - 1) / 8 + 1)) rgs else false
         | None => false
         end
      then true else rp_zc fs rgs b nl
  end.
(* [comment removed for export] *)
Definition rp_ze1_ref (fs : list fact) (nl q : lin) (R : region) : bool :=
  match rg_kind R with
  | RZ => let '(lo, hi) := irange fs (lsub (lscale 8 (rg_size R)) nl) in
          (lin_eqb (rg_base R) (laddc q SH_OFF) && range_zero (rg_cont R) 0 two64 && Z.leb 0 lo && Z.ltb hi (2 ^ 62) &&
           Z.ltb (snd (irange fs (rg_size R))) (2 ^ 40))%bool
  | _ => false
  end.
(* [comment removed for export] *)
Definition rp_ze1 (fs : list fact) (nl q : lin) (R : region) : bool :=
  match rg_kind R with
  | RZ => if lin_eqb (rg_base R) (laddc q SH_OFF) then
            if range_zero (rg_cont R) 0 two64 then
              let '(lo, hi) := irange fs (lsub (lscale 8 (rg_size R)) nl) in
              (Z.leb 0 lo && Z.ltb hi (2 ^ 62) && Z.ltb (snd (irange fs (rg_size R))) (2 ^ 40))%bool
            else false
          else false
  | _ => false
  end.
Lemma rp_ze1_eq : forall fs nl q R, rp_ze1 fs nl q R = rp_ze1_ref fs nl q R.
Proof.
  intros fs nl q R. unfold rp_ze1, rp_ze1_ref. destruct (rg_kind R); try reflexivity.
  destruct (irange fs (lsub (lscale 8 (rg_size R)) nl)) as [lo hi].
  destruct (lin_eqb (rg_base R) (laddc q SH_OFF)), (range_zero (rg_cont R) 0 two64); reflexivity.
Qed.
Definition rp_ze (fs : list fact) (rgs : list region) (b nl : lin) : bool :=
  match srl_lin fs 3 b, lowb fs b 3 with
  | Some q, Some 0 => existsb (rp_ze1 fs nl q) rgs
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition rp_zbx (fs : list fact) (rgs : list region) (b nl : lin) : bool := if rp_ze fs rgs b nl then true else rp_zb fs rgs b nl.
Lemma rp_zbx_ref_eq : forall fs rgs b nl, rp_zbx fs rgs b nl = (if rp_zb fs rgs b nl then true else rp_ze fs rgs b nl).
Proof. intros fs rgs b nl. unfold rp_zbx. destruct (rp_ze fs rgs b nl), (rp_zb fs rgs b nl); reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rp_ref1 (fs : list fact) (b : lin) (acc : Z * Z) (R0 : region) : Z * Z :=
  let base := rg_base R0 in
  let '(dlo, dhi) := irange fs (lsub b base) in
  if Z.leb 0 dlo then
    if Z.ltb dhi (2 ^ 40) then
      let '(blo0, bhi0) := irange fs base in
      if Z.ltb (bhi0 + 2 ^ 41) two64 then (Z.max (fst acc) (blo0 + dlo), Z.min (snd acc) (bhi0 + dhi)) else acc
    else acc
  else acc.
Definition rp_brange (fs : list fact) (rgs : list region) (b : lin) : Z * Z := fold_left (rp_ref1 fs b) rgs (irange fs b).
(* [comment removed for export] *)
Definition rp_zp1 (fs : list fact) (rgs : list region) (b nl : lin) (R : region) : bool :=
  match tget 1%positive (rg_cont R) with
  | Some (BV l 0) =>
      let nl8 := lsub nl l in
      match srl_lin fs 3 (ladd b nl8) with
      | Some q =>
          let '(llo, lhi) := irange fs l in let '(nlo8, nhi8) := irange fs nl8 in
          (* [comment removed for export] *)
          if lin_eqb (rg_base R) (laddc q SH_OFF) then
            (Z.leb 1 llo && Z.leb lhi 7 &&
             match lowb fs (ladd b nl8) 3 with Some 0 => true | _ => false end &&
             Z.leb 0 nlo8 && Z.ltb nhi8 (2 ^ 40) &&
             (if Z.eqb nhi8 0 then true else if Z.leb 1 nlo8 then rp_zbx fs rgs b nl8 else false))%bool
          else false
      | None => false
      end
  | _ => false
  end.
Definition rp_zp (fs : list fact) (rgs : list region) (b nl : lin) : bool := existsb (rp_zp1 fs rgs b nl) rgs.
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint wrap_hi (fs : list fact) (g : lin) : option Z :=
  match fs with
  | [] => None
  | FRange g' _ hi :: r => if lin_eqb g' g then Some hi else wrap_hi r g
  | _ :: r => wrap_hi r g
  end.
Definition rp_wrap1 (fs : list fact) (b nl : lin) (nhi : Z) (R0 : region) : bool :=
  let base := rg_base R0 in
  let '(dlo, dhi) := irange fs (lsub b base) in
  if (Z.leb 0 dlo && Z.ltb dhi (2 ^ 40) && Z.ltb (snd (irange fs base) + 2 ^ 41) two64)%bool then
    match wrap_hi fs (laddc base (- SH_HI)) with
    | Some whi => Z.leb (end_hi fs b nl base dhi nhi + 8) (two64 + SH_LO - SH_HI - whi)
    | None => false
    end
  else false.
Definition rp_wrap_rg (fs : list fact) (rgs : list region) (b nl : lin) (nhi : Z) : bool := existsb_cf (fun R0 => cand_t b (rg_base R0)) (rp_wrap1 fs b nl nhi) rgs.
(* [comment removed for export] *)
Definition rp_wrap (fs : list fact) (rgs : list region) (b nl : lin) (nhi : Z) : bool :=
  if rp_wrap_rg fs rgs b nl nhi then true else twoc_ns fs b (nhi + 8).
Definition rp_rngb (fs : list fact) (rgs : list region) (b nl : lin) (blo nhi ehi' : Z) : bool :=
  if (Z.leb SH_HI blo && Z.leb (ehi' + 8) kHighEnd)%bool then true
  else if Z.leb (ehi' + 8) kLowEnd then true
  else if Z.leb (ehi' + 8) kHighEnd then rp_wrap fs rgs b nl nhi else false.
(* [comment removed for export] *)
Definition rp_any (S : sst) (M : smodel) (fs : list fact) (rgs : list region) (b nl : lin) : bool :=
  if rp_za S M b nl then true else if rp_zp fs rgs b nl then true else rp_zbx fs rgs b nl.
Lemma rp_any_eq : forall S M fs rgs b nl,
  rp_any S M fs rgs b nl = (if rp_zp fs rgs b nl then true else if rp_zbx fs rgs b nl then true else rp_za S M b nl).
Proof. intros S M fs rgs b nl. unfold rp_any. destruct (rp_za S M b nl), (rp_zp fs rgs b nl), (rp_zbx fs rgs b nl); reflexivity. Qed.
Definition rp_chk_ref (img : tree Z) (S : sst) (M : smodel) : bool :=
  let fs := s_facts S in let rgs := s_rgs S in
  let b := rget (s_regs S) (rkey (xr 10)) in let nl := rget (s_regs S) (rkey (xr 11)) in let sp := rget (s_regs S) (rkey (xr 2)) in
  match rg_is S 1, s_resv S, find_frame rgs sp O with
  | Some r, RNone, Some (j0, d) =>
      let '(blo, bhi) := rp_brange fs rgs b in let '(nlo, nhi) := irange fs nl in
      let '(slo, shi) := irange fs sp in let ehi' := Z.min (snd (irange fs (ladd b nl))) (bhi + nhi) in
      if (Z.eqb (s_pc S) RP_PC && Z.eqb (r mod 2) 0 && Z.leb 1 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (bhi + nhi) two64 &&
          rp_rngb fs rgs b nl blo nhi ehi' &&
          Z.leb 80 slo && Z.ltb shi two64 && Z.ltb (SH_OFF + (bhi + nhi - 1) / 8) (slo - 72) &&
          lwf (s_next S) b && lwf (s_next S) nl && cells_chk img fs rgs)%bool
      then rp_any S M fs rgs b nl
      else false
  | _, _, _ => false
  end.

(* [comment removed for export] *)
Definition rp_rng0 (blo ehi' : Z) : bool :=
  if (Z.leb SH_HI blo && Z.leb (ehi' + 8) kHighEnd)%bool then true else Z.leb (ehi' + 8) kLowEnd.
Lemma rp_rng0_rngb : forall fs rgs b nl blo nhi e, rp_rng0 blo e = true -> rp_rngb fs rgs b nl blo nhi e = true.
Proof.
  intros fs rgs b nl blo nhi e H. unfold rp_rng0 in H. unfold rp_rngb.
  destruct (Z.leb SH_HI blo && Z.leb (e + 8) kHighEnd)%bool; [reflexivity|]. rewrite H. reflexivity.
Qed.
Lemma rp_rngb_mono : forall fs rgs b nl blo blo' nhi e e', blo <= blo' -> e' <= e ->
  rp_rngb fs rgs b nl blo nhi e = true -> rp_rngb fs rgs b nl blo' nhi e' = true.
Proof.
  intros fs rgs b nl blo blo' nhi e e' Hlo He H2. unfold rp_rngb in *.
  destruct (Z.leb SH_HI blo && Z.leb (e + 8) kHighEnd)%bool eqn:C1.
  - apply andb_prop in C1 as [A B]. apply Z.leb_le in A, B.
    replace (Z.leb SH_HI blo' && Z.leb (e' + 8) kHighEnd)%bool with true; [reflexivity|].
    symmetry. apply andb_true_intro. split; apply Z.leb_le; lia.
  - destruct (Z.leb SH_HI blo' && Z.leb (e' + 8) kHighEnd)%bool; [reflexivity|].
    destruct (Z.leb (e + 8) kLowEnd) eqn:C2.
    + apply Z.leb_le in C2. replace (Z.leb (e' + 8) kLowEnd) with true; [reflexivity|]. symmetry. apply Z.leb_le. lia.
    + destruct (Z.leb (e' + 8) kLowEnd); [reflexivity|].
      destruct (Z.leb (e + 8) kHighEnd) eqn:C3; [|discriminate H2]. apply Z.leb_le in C3.
      replace (Z.leb (e' + 8) kHighEnd) with true; [exact H2|]. symmetry. apply Z.leb_le. lia.
Qed.
Definition rp_t1c (nhi slo eh : Z) (r : Z * Z) : bool :=
  (Z.ltb (snd r + nhi) two64 && rp_rng0 (fst r) (Z.min eh (snd r + nhi)) && Z.ltb (SH_OFF + (snd r + nhi - 1) / 8) (slo - 72))%bool.
Definition rp_t1g (rng : Z -> Z -> Z -> bool) (nhi slo eh : Z) (r : Z * Z) : bool :=
  (Z.ltb (snd r + nhi) two64 && rng (fst r) nhi (Z.min eh (snd r + nhi)) && Z.ltb (SH_OFF + (snd r + nhi - 1) / 8) (slo - 72))%bool.
Lemma rp_ref1_sub : forall fs b acc R0, fst acc <= fst (rp_ref1 fs b acc R0) /\ snd (rp_ref1 fs b acc R0) <= snd acc.
Proof.
  intros fs b acc R0. unfold rp_ref1. destruct (irange fs (lsub b (rg_base R0))) as [dlo dhi].
  destruct (Z.leb 0 dlo); [|lia]. destruct (Z.ltb dhi (2 ^ 40)); [|lia]. destruct (irange fs (rg_base R0)) as [blo0 bhi0].
  destruct (Z.ltb (bhi0 + 2 ^ 41) two64); cbn [fst snd]; lia.
Qed.
Lemma rp_fold_sub : forall fs b rgs acc, fst acc <= fst (fold_left (rp_ref1 fs b) rgs acc) /\ snd (fold_left (rp_ref1 fs b) rgs acc) <= snd acc.
Proof.
  intros fs b rgs. induction rgs as [|R0 rgs IH]; intros acc; cbn [fold_left]; [lia|].
  pose proof (rp_ref1_sub fs b acc R0) as H1. pose proof (IH (rp_ref1 fs b acc R0)) as H2. lia.
Qed.
Lemma rp_t1_lazy : forall (rng : Z -> Z -> Z -> bool) nhi slo eh r r',
  (forall blo e, rp_rng0 blo e = true -> rng blo nhi e = true) ->
  (forall blo blo' e e', blo <= blo' -> e' <= e -> rng blo nhi e = true -> rng blo' nhi e' = true) ->
  fst r <= fst r' -> snd r' <= snd r ->
  (if rp_t1c nhi slo eh r then true else rp_t1g rng nhi slo eh r') = rp_t1g rng nhi slo eh r'.
Proof.
  intros rng nhi slo eh r r' H0 Hm Hlo Hhi. destruct (rp_t1c nhi slo eh r) eqn:H; [|reflexivity]. symmetry.
  unfold rp_t1c in H. unfold rp_t1g. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.ltb_lt in H1, H3.
  assert (Hd : (snd r' + nhi - 1) / 8 <= (snd r + nhi - 1) / 8) by (apply Z.div_le_mono; lia).
  apply andb_true_intro. split; [apply andb_true_intro; split|]; [apply Z.ltb_lt; lia | | apply Z.ltb_lt; lia].
  apply (Hm (fst r) (fst r') (Z.min eh (snd r + nhi)) (Z.min eh (snd r' + nhi)) Hlo ltac:(lia)). exact (H0 _ _ H2).
Qed.
Lemma rp_bool_shuffle : forall (c1 c2 c3 c4 c5 c6 c7 c8 c9 A B C X : bool),
  (if (c1 && c2 && c3 && c4 && c5 && c6 && c7 && c8 && c9)%bool then (if (A && B && C)%bool then X else false) else false) =
  (if (c1 && c2 && c3 && c4 && A && B && c5 && c6 && C && c7 && c8 && c9)%bool then X else false).
Proof.
  intros c1 c2 c3 c4 c5 c6 c7 c8 c9 A B C X.
  destruct c1; [|reflexivity]. destruct c2; [|reflexivity]. destruct c3; [|reflexivity]. destruct c4; [|reflexivity]. cbn [andb].
  destruct A; [|destruct c5, c6, c7, c8, c9; reflexivity]. destruct B; [|destruct c5, c6, c7, c8, c9; reflexivity]. cbn [andb].
  destruct c5; [|reflexivity]. destruct c6; [|reflexivity]. cbn [andb].
  destruct C; [|destruct c7, c8, c9; reflexivity]. reflexivity.
Qed.
Definition rp_chk (img : tree Z) (S : sst) (M : smodel) : bool :=
  let fs := s_facts S in let rgs := s_rgs S in
  let b := rget (s_regs S) (rkey (xr 10)) in let nl := rget (s_regs S) (rkey (xr 11)) in let sp := rget (s_regs S) (rkey (xr 2)) in
  match rg_is S 1, s_resv S, find_frame rgs sp O with
  | Some r, RNone, Some (j0, d) =>
      let '(nlo, nhi) := irange fs nl in let '(slo, shi) := irange fs sp in let eh := snd (irange fs (ladd b nl)) in
      if (Z.eqb (s_pc S) RP_PC && Z.eqb (r mod 2) 0 && Z.leb 1 nlo && Z.leb nhi (2 ^ 40) && Z.leb 80 slo && Z.ltb shi two64 &&
          lwf (s_next S) b && lwf (s_next S) nl && cells_chk img fs rgs)%bool
      then (let r0 := irange fs b in
            if (if rp_t1c nhi slo eh r0 then true else rp_t1g (rp_rngb fs rgs b nl) nhi slo eh (fold_left (rp_ref1 fs b) rgs r0))
            then rp_any S M fs rgs b nl else false)
      else false
  | _, _, _ => false
  end.
Lemma rp_chk_eq : forall img S M, rp_chk img S M = rp_chk_ref img S M.
Proof.
  intros img S M. unfold rp_chk, rp_chk_ref. cbv zeta.
  destruct (rg_is S 1) as [r|]; [|reflexivity]. destruct (s_resv S); try reflexivity.
  destruct (find_frame (s_rgs S) (rget (s_regs S) (rkey (xr 2))) 0) as [[j0 d]|]; [|reflexivity].
  unfold rp_brange.
  set (fs := s_facts S). set (rgs := s_rgs S). set (b := rget (s_regs S) (rkey (xr 10))). set (nl := rget (s_regs S) (rkey (xr 11))).
  set (sp := rget (s_regs S) (rkey (xr 2))).
  pose proof (rp_fold_sub fs b rgs (irange fs b)) as [Hs1 Hs2].
  set (r0 := irange fs b) in *. set (rr := fold_left (rp_ref1 fs b) rgs r0) in *.
  destruct (irange fs nl) as [nlo nhi]. destruct (irange fs sp) as [slo shi].
  set (eh := snd (irange fs (ladd b nl))).
  rewrite (rp_t1_lazy (rp_rngb fs rgs b nl) nhi slo eh r0 rr (fun blo e => rp_rng0_rngb fs rgs b nl blo nhi e)
             (fun blo blo' e e' => rp_rngb_mono fs rgs b nl blo blo' nhi e e') Hs1 Hs2).
  unfold rp_t1g. destruct rr as [blo bhi]. cbn [fst snd]. apply rp_bool_shuffle.
Qed.
Definition rp_post (S : sst) : sst :=
  match rg_is S 1, find_frame (s_rgs S) (rget (s_regs S) (rkey (xr 2))) O with
  | Some r, Some (j0, d) => run_post_fw S r [(xr 10, lconst 0)] RP_HAVS j0 (d - 72) d
  | _, _ => S
  end.

Lemma find_frame_spec : forall rgs sp j j0 d, find_frame rgs sp j = Some (j0, d) ->
  exists R sz, nth_error rgs (j0 - j) = Some R /\ (j <= j0)%nat /\ rg_kind R = RW /\ is_const (rg_size R) = Some sz /\
    lin_off sp (rg_base R) = Some d /\ 72 <= d < sz.
Proof.
  induction rgs as [|R rs IH]; intros sp j j0 d H; cbn [find_frame] in H; [discriminate|].
  destruct (rg_kind R) eqn:Hk; try (destruct (IH sp (Datatypes.S j) j0 d H) as (R' & sz & Hn & Hj & X); exists R', sz;
      replace (j0 - j)%nat with (Datatypes.S (j0 - Datatypes.S j)) by lia; split; [exact Hn|]; split; [lia | exact X]).
  destruct (is_const (rg_size R)) as [sz|] eqn:Hs; [|destruct (IH sp (Datatypes.S j) j0 d H) as (R' & sz & Hn & Hj & X); exists R', sz;
      replace (j0 - j)%nat with (Datatypes.S (j0 - Datatypes.S j)) by lia; split; [exact Hn|]; split; [lia | exact X]].
  destruct (lin_off sp (rg_base R)) as [d0|] eqn:Hd; [|destruct (IH sp (Datatypes.S j) j0 d H) as (R' & sz' & Hn & Hj & X); exists R', sz';
      replace (j0 - j)%nat with (Datatypes.S (j0 - Datatypes.S j)) by lia; split; [exact Hn|]; split; [lia | exact X]].
  destruct (Z.leb 72 d0 && Z.ltb d0 sz)%bool eqn:Hc.
  - injection H as <- <-. apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
    exists R, sz. rewrite Nat.sub_diag. split; [reflexivity|]. split; [lia|]. split; [exact Hk|]. split; [exact Hs|]. split; [exact Hd|]. lia.
  - destruct (IH sp (Datatypes.S j) j0 d H) as (R' & sz' & Hn & Hj & X). exists R', sz'.
    replace (j0 - j)%nat with (Datatypes.S (j0 - Datatypes.S j)) by lia. split; [exact Hn|]. split; [lia | exact X].
Qed.

(* [comment removed for export] *)
Lemma wbytes_or : forall bs m (a w : word), wbytes m a bs w = m w \/ exists bb, wbytes m a bs w = Some bb.
Proof.
  induction bs as [|b rest IH]; intros m a w; cbn [wbytes]; [left; reflexivity|].
  destruct (IH (fun x => if bv_eqb x a then Some b else m x) (a + 1)%bv w) as [H|H]; [|right; exact H].
  rewrite H. destruct (bv_eqb w a); [right; exists b; reflexivity | left; reflexivity].
Qed.
Lemma len_wle8 : forall x : word, length (word_to_le_bytes 8 x) = 8%nat. Proof. intros x. reflexivity. Qed.
Lemma rp_frame_out : forall m usp (ra s0 s1 s2 s3 s4 s5 : word) (w : word), 72 <= usp < 2 ^ 64 ->
  ~ (usp - 72 <= bv_unsigned w < usp) -> rp_frame m usp ra s0 s1 s2 s3 s4 s5 w = m w.
Proof.
  intros m usp ra s0 s1 s2 s3 s4 s5 w Hu Hw. unfold rp_frame.
  assert (X : forall (mm : word -> option byte) (k : Z) (v : word), 8 <= k <= 72 -> k mod 8 = 0 ->
            wbytes mm (Z_to_bv 64 (usp - k)) (word_to_le_bytes 8 v) w = mm w).
  { intros mm k v Hk Hk8. apply wbytes_outside; rewrite len_wle8; unfold in_rng; rewrite u_small by (unfold two64; lia); lia. }
  rewrite (X _ 72), (X _ 56), (X _ 48), (X _ 40), (X _ 32), (X _ 24), (X _ 16), (X _ 8); (reflexivity || lia).
Qed.
Lemma wbytes_or2 : forall bs (m m' : word -> option byte) (a w : word), (m' w = m w \/ exists bb, m' w = Some bb) ->
  wbytes m' a bs w = m w \/ exists bb, wbytes m' a bs w = Some bb.
Proof.
  intros bs m m' a w H. destruct (wbytes_or bs m' a w) as [X|X]; [rewrite X; exact H | right; exact X].
Qed.
Lemma rp_frame_or : forall m usp (ra s0 s1 s2 s3 s4 s5 : word) (w : word),
  rp_frame m usp ra s0 s1 s2 s3 s4 s5 w = m w \/ exists bb, rp_frame m usp ra s0 s1 s2 s3 s4 s5 w = Some bb.
Proof.
  intros. unfold rp_frame.
  repeat apply wbytes_or2. left; reflexivity.
Qed.

Lemma rp_frame_rd1 : forall segs m usp (ra s0 s1 s2 s3 s4 s5 : word) (w : word),
  rd1 segs m w <> None -> rd1 segs (rp_frame m usp ra s0 s1 s2 s3 s4 s5) w <> None.
Proof.
  intros segs m usp ra s0 s1 s2 s3 s4 s5 w H. unfold rd1 in *.
  destruct (rp_frame_or m usp ra s0 s1 s2 s3 s4 s5 w) as [X|(bb & X)]; rewrite X; [exact H | discriminate].
Qed.
Lemma rp_frame_wview : forall segs m usp (ra s0 s1 s2 s3 s4 s5 : word) (w : word),
  wview segs m w <> None -> wview segs (rp_frame m usp ra s0 s1 s2 s3 s4 s5) w <> None.
Proof.
  intros segs m usp ra s0 s1 s2 s3 s4 s5 w H. unfold wview in *.
  destruct (rp_frame_or m usp ra s0 s1 s2 s3 s4 s5 w) as [X|(bb & X)]; rewrite X; [exact H | discriminate].
Qed.

Lemma rp_frame7_out : forall m usp (ra s0 s1 s2 s3 s4 s5 : word) (w : word), 72 <= usp < 2 ^ 64 ->
  ~ (usp - 72 <= bv_unsigned w < usp) -> rp_frame7 m usp ra s0 s1 s2 s3 s4 s5 w = m w.
Proof.
  intros m usp ra s0 s1 s2 s3 s4 s5 w Hu Hw. unfold rp_frame7.
  assert (X : forall (mm : word -> option byte) (k : Z) (v : word), 8 <= k <= 72 -> k mod 8 = 0 ->
            wbytes mm (Z_to_bv 64 (usp - k)) (word_to_le_bytes 8 v) w = mm w).
  { intros mm k v Hk Hk8. apply wbytes_outside; rewrite len_wle8; unfold in_rng; rewrite u_small by (unfold two64; lia); lia. }
  rewrite (X _ 56), (X _ 48), (X _ 40), (X _ 32), (X _ 24), (X _ 16), (X _ 8); (reflexivity || lia).
Qed.
Lemma rp_frame7_or : forall m usp (ra s0 s1 s2 s3 s4 s5 : word) (w : word),
  rp_frame7 m usp ra s0 s1 s2 s3 s4 s5 w = m w \/ exists bb, rp_frame7 m usp ra s0 s1 s2 s3 s4 s5 w = Some bb.
Proof.
  intros. unfold rp_frame7.
  repeat apply wbytes_or2. left; reflexivity.
Qed.
Lemma mm_or_rd1 : forall segs (m m' : word -> option byte) (w : word), (m' w = m w \/ exists bb, m' w = Some bb) ->
  rd1 segs m w <> None -> rd1 segs m' w <> None.
Proof. intros segs m m' w [X|(bb & X)] H; unfold rd1 in *; rewrite X; [exact H | discriminate]. Qed.
Lemma mm_or_wview : forall segs (m m' : word -> option byte) (w : word), (m' w = m w \/ exists bb, m' w = Some bb) ->
  wview segs m w <> None -> wview segs m' w <> None.
Proof. intros segs m m' w [X|(bb & X)] H; unfold wview in *; rewrite X; [exact H | discriminate]. Qed.

Lemma asegs_below : segs_below_b ASEGSN 0x1000000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rd1_hi : forall m (x : Z) b, 0x1000000 <= x < two64 -> rd1 ASEGSN m (Z_to_bv 64 x) = Some b -> m (Z_to_bv 64 x) = Some b.
Proof.
  intros m x b Hx H. unfold rd1 in H. destruct (m (Z_to_bv 64 x)) as [b'|] eqn:Hm; [exact H|].
  rewrite seg_rom_none in H; [discriminate|]. apply (find_segment1_none_above _ 0x1000000 _ asegs_below).
  rewrite u_small by lia. lia.
Qed.

Lemma le8_of_lez : forall (bs : list byte) (v : Z), length bs = 8%nat -> lez bs = v -> 0 <= v < two64 ->
  bs = word_to_le_bytes 8 (Z_to_bv 64 v).
Proof.
  intros bs v Hl Hz Hv. unfold word_to_le_bytes. rewrite u_small by exact Hv. rewrite <- Hz, <- Hl. symmetry. apply Z_to_le_bytes_lez.
Qed.

Lemma cells_chk_sound : forall E img fs rgs m, img_ok ASEGSN img -> Forall (rg_ok ASEGSN E m) rgs -> Forall (fact_ok E) fs ->
  cells_chk img fs rgs = true -> forall p, In p rp_cells_list -> cell m (fst p) (snd p).
Proof.
  intros E img fs rgs m Himg HG HF Hc p Hp. unfold cells_chk in Hc. rewrite forallb_forall in Hc. specialize (Hc p Hp).
  destruct (load_at img fs rgs (lconst (fst p)) SZ8 false) as [[l|]|] eqn:Hl; try discriminate. apply lin_eqb_eq in Hc. subst l.
  destruct (load_at_sound ASEGSN E img fs rgs _ SZ8 false _ m Himg HG HF Hl) as (bs & Hr & Hv). specialize (Hv _ eq_refl).
  rewrite ov_rdn in Hr. cbn [nbytes] in Hr. rewrite lden_lconst in Hr.
  assert (Hlb : length bs = 8%nat) by exact (rdn_length _ _ _ _ _ Hr).
  assert (Hvr : 0 <= snd p < two64) by (unfold rp_cells_list in Hp; cbn [In] in Hp;
    repeat (destruct Hp as [<-|Hp]; [cbn [snd]; unfold SB, kHighEnd, two64; lia|]); destruct Hp).
  pose proof (ld8_val bs _ Hlb (eq_sym Hv)) as Hz. rewrite lden_lconst, u_small in Hz by exact Hvr.
  unfold cell. rewrite Hr. f_equal. exact (le8_of_lez bs (snd p) Hlb Hz Hvr).
Qed.

Lemma zero_ov_in : forall E fs a n R, Forall (fact_ok E) fs -> zero_ov fs a n R = true -> 0 <= n ->
  uE E (rg_base R) + rsz E R <= two64 ->
  forall w, uE E a <= w < uE E a + n -> uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R.
Proof.
  intros E fs a n R HF H Hn HRw w Hin. unfold zero_ov in H. destruct (rg_kind R); try discriminate.
  pose proof (irange_sound E fs (lsub a (rg_base R)) HF) as Hr. destruct (irange fs (lsub a (rg_base R))) as [lo hi] eqn:Hir.
  cbn [fst snd] in Hr. apply andb_prop in H as [H Hz]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2.
  pose proof (size_lo_sound E fs R HF) as Hsz. fold (uE E (lsub a (rg_base R))) in Hr.
  pose proof (uE_range E a). pose proof (uE_range E (rg_base R)).
  destruct (small_diff E a (rg_base R) lo hi Hr) as [[Hl He]|[Hl He]]; unfold two64 in *; lia.
Qed.

Lemma uE_laddc3 : forall E l c, 0 <= c -> uE E l + c < two64 -> uE E (laddc l c) = uE E l + c.
Proof. intros E l c Hc H. unfold uE. rewrite lden_laddc. apply u_small. pose proof (uE_range E l). unfold uE in *. lia. Qed.
Lemma tsum_al8 : forall E t, forallb (fun p => Z.eqb (snd p mod 8) 0) t = true -> tsum E t mod 8 = 0.
Proof.
  intros E t. induction t as [|[x c] t IH]; intros H; [reflexivity|]. cbn [forallb] in H. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. cbn [tsum]. rewrite Z.add_mod by lia. rewrite (IH H2), Z.add_0_r. rewrite Z.mul_mod by lia. cbn [snd] in H1. rewrite H1. reflexivity.
Qed.
Lemma lal8_sound : forall E b, lal8 b = true -> uE E b mod 8 = l_c b mod 8.
Proof.
  intros E b H. unfold uE, lden. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
  rewrite <- (Zmod_div_mod 8 two64 (lz E b)) by (first [lia | exists 2305843009213693952; reflexivity | unfold two64; lia]).
  unfold lz. rewrite Z.add_mod by lia. rewrite (tsum_al8 E _ H), Z.add_0_r. apply Z.mod_mod. lia.
Qed.
Lemma end_hi_sound : forall E fs b nl base dhi nhi, Forall (fact_ok E) fs ->
  uE E b = uE E base + uE E (lsub b base) -> uE E (lsub b base) <= dhi -> dhi < 2 ^ 40 -> uE E base + 2 ^ 41 < two64 -> uE E nl <= nhi ->
  uE E (lsub b base) + uE E nl <= end_hi fs b nl base dhi nhi.
Proof.
  intros E fs b nl base dhi nhi HF HB HD Hdhi Hbase HN. unfold end_hi. destruct (Z.ltb nhi (2 ^ 40)) eqn:Hn; [|lia].
  apply Z.ltb_lt in Hn. apply Z.min_glb; [lia|].
  pose proof (irange_sound E fs (lsub (ladd b nl) base) HF) as Rr. fold (uE E (lsub (ladd b nl) base)) in Rr.
  pose proof (uE_range E (lsub b base)) as RD. pose proof (uE_range E nl) as RN. pose proof (uE_range E base) as RB.
  assert (Hbn : uE E (ladd b nl) = uE E b + uE E nl) by (unfold uE; apply ladd_u2; fold (uE E b) (uE E nl); unfold two64 in *; lia).
  assert (He : uE E (lsub (ladd b nl) base) = uE E (lsub b base) + uE E nl).
  { rewrite u_lsub_mod, Hbn, HB. replace (uE E base + uE E (lsub b base) + uE E nl - uE E base) with (uE E (lsub b base) + uE E nl) by ring.
    apply Z.mod_small. unfold two64 in *. lia. }
  lia.
Qed.

Lemma rp_zb_spec : forall E fs rgs b nl, Forall (fact_ok E) fs -> rp_zb fs rgs b nl = true ->
  1 <= uE E nl <= snd (irange fs nl) ->
  exists sf k R, In R rgs /\ zero_ov fs sf k R = true /\ uE E sf <= SH_OFF + uE E b / 8 /\
    SH_OFF + (uE E b + uE E nl - 1) / 8 < uE E sf + k.
Proof.
  intros E fs rgs b nl HF Hzb HN. pose proof (uE_range E b) as RB.
  unfold rp_zb in Hzb. destruct (is_const b) as [c|] eqn:Hbc.
  - apply existsb_cf_exists in Hzb as (R & HRin & HzR). destruct (is_const_sound E b c Hbc) as [Hbv Hc64].
    assert (HBc : uE E b = c) by (unfold uE; rewrite Hbv; apply u_small; exact Hc64).
    exists (lconst (SH_OFF + c / 8)), ((c + snd (irange fs nl) - 1) / 8 - c / 8 + 1), R. split; [exact HRin|]. split; [exact HzR|].
    assert (Hsfv : uE E (lconst (SH_OFF + c / 8)) = SH_OFF + c / 8).
    { unfold uE at 1. rewrite lden_lconst. apply u_small. pose proof (Z.div_pos c 8 ltac:(lia) ltac:(lia)).
      assert (c / 8 < 2 ^ 61) by (apply Z.div_lt_upper_bound; unfold two64 in *; lia). unfold SH_OFF, two64 in *; lia. }
    rewrite Hsfv, HBc. split; [lia|].
    assert ((c + uE E nl - 1) / 8 <= (c + snd (irange fs nl) - 1) / 8) by (apply Z.div_le_mono; lia). lia.
  - destruct (match srl_lin fs 3 b with
              | Some q => if lal8 b then existsb_cf (fun R => cand_t q (rg_base R)) (zero_ov fs (laddc q SH_OFF) ((l_c b mod 8 + snd (irange fs nl) - 1) / 8 + 1)) rgs else false
              | None => false
              end) eqn:Hb1.
    + clear Hzb. destruct (srl_lin fs 3 b) as [q|] eqn:Hq; [|discriminate]. destruct (lal8 b) eqn:Hal; [|discriminate].
      apply existsb_cf_exists in Hb1 as (R & HRin & HzR).
      pose proof (srl_lin_sound E fs 3 b q HF ltac:(lia) Hq) as Hqv. rewrite Z.shiftr_div_pow2 in Hqv by lia. change (2 ^ 3) with 8 in Hqv.
      fold (uE E q) (uE E b) in Hqv.
      exists (laddc q SH_OFF), ((l_c b mod 8 + snd (irange fs nl) - 1) / 8 + 1), R. split; [exact HRin|]. split; [exact HzR|].
      assert (Hqb : uE E q < 2 ^ 61) by (rewrite Hqv; apply Z.div_lt_upper_bound; unfold two64 in *; lia).
      assert (Hsfv : uE E (laddc q SH_OFF) = SH_OFF + uE E b / 8).
      { pose proof (uE_range E q). rewrite uE_laddc3 by (unfold SH_OFF, two64 in *; lia). rewrite Hqv. lia. }
      rewrite Hsfv. split; [lia|].
      pose proof (lal8_sound E b Hal) as Hm. pose proof (Z.div_mod (uE E b) 8 ltac:(lia)) as Hdm.
      pose proof (Z.mod_pos_bound (uE E b) 8 ltac:(lia)) as Hmb. pose proof (Z.mod_pos_bound (l_c b) 8 ltac:(lia)) as Hmb2.
      assert (Hx : (uE E b + uE E nl - 1) / 8 = uE E b / 8 + (uE E b mod 8 + uE E nl - 1) / 8).
      { rewrite Hdm at 1. replace (8 * (uE E b / 8) + uE E b mod 8 + uE E nl - 1) with ((uE E b mod 8 + uE E nl - 1) + (uE E b / 8) * 8) by ring.
        rewrite Z.div_add by lia. ring. }
      rewrite Hx, Hm. assert ((l_c b mod 8 + uE E nl - 1) / 8 <= (l_c b mod 8 + snd (irange fs nl) - 1) / 8) by (apply Z.div_le_mono; lia). lia.
    + (* [comment removed for export] *)
      unfold rp_zc in Hzb. apply existsb_cf_exists in Hzb as (R0 & HR0in & Hz1). unfold rp_zc1 in Hz1.
      set (base := rg_base R0) in *.
      destruct (lal8 base && Z.eqb (l_c base mod 8) 0)%bool eqn:Hal; [|discriminate].
      apply andb_prop in Hal as [Hal Hc8]. apply Z.eqb_eq in Hc8.
      destruct (irange fs (lsub b base)) as [dlo dhi] eqn:Hdr.
      destruct (Z.leb 0 dlo && Z.ltb dhi (2 ^ 40) && Z.ltb (snd (irange fs base) + 2 ^ 41) two64)%bool eqn:Hck; [|discriminate].
      apply andb_prop in Hck as [Hck H3]. apply andb_prop in Hck as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2, H3.
      destruct (srl_lin fs 3 base) as [q|] eqn:Hq; [|discriminate].
      apply existsb_cf_exists in Hz1 as (R & HRin & HzR).
      pose proof (srl_lin_sound E fs 3 base q HF ltac:(lia) Hq) as Hqv. rewrite Z.shiftr_div_pow2 in Hqv by lia. change (2 ^ 3) with 8 in Hqv.
      fold (uE E q) (uE E base) in Hqv.
      pose proof (lal8_sound E base Hal) as Hm. rewrite Hc8 in Hm.
      pose proof (irange_sound E fs base HF) as Rb0. cbn [fst snd] in Rb0. fold (uE E base) in Rb0.
      pose proof (irange_sound E fs (lsub b base) HF) as Rd. rewrite Hdr in Rd. cbn [fst snd] in Rd. fold (uE E (lsub b base)) in Rd.
      pose proof (uE_range E base) as RB0. pose proof (uE_range E q) as RQ.
      destruct (small_diff E b base dlo dhi Rd) as [[Hl He]|[Hl He]].
      * set (D := uE E (lsub b base)) in *.
        assert (HB : uE E b = uE E base + D) by lia.
        pose proof (Z.div_mod (uE E base) 8 ltac:(lia)) as Hdm. rewrite Hm, Z.add_0_r in Hdm.
        assert (Hdiv : uE E b / 8 = uE E base / 8 + D / 8).
        { rewrite HB, Hdm at 1. replace (8 * (uE E base / 8) + D) with (D + (uE E base / 8) * 8) by ring. rewrite Z.div_add by lia. ring. }
        assert (Hdiv2 : (uE E b + uE E nl - 1) / 8 = uE E base / 8 + (D + uE E nl - 1) / 8).
        { rewrite HB, Hdm at 1. replace (8 * (uE E base / 8) + D + uE E nl - 1) with ((D + uE E nl - 1) + (uE E base / 8) * 8) by ring.
          rewrite Z.div_add by lia. ring. }
        exists (laddc q (SH_OFF + dlo / 8)), ((end_hi fs b nl base dhi (snd (irange fs nl)) - 1) / 8 - dlo / 8 + 1), R. split; [exact HRin|]. split; [exact HzR|].
        pose proof (end_hi_sound E fs b nl base dhi (snd (irange fs nl)) HF ltac:(fold D; lia) ltac:(fold D; lia) H2 ltac:(lia) ltac:(lia)) as Hend. fold D in Hend.
        assert (Hqb : uE E q < 2 ^ 61) by (rewrite Hqv; apply Z.div_lt_upper_bound; unfold two64 in *; lia).
        assert (Hd8 : 0 <= dlo / 8 < 2 ^ 40) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
        assert (Hsfv : uE E (laddc q (SH_OFF + dlo / 8)) = uE E q + (SH_OFF + dlo / 8)).
        { apply uE_laddc3; unfold SH_OFF, two64 in *; lia. }
        rewrite Hsfv, Hqv. split.
        -- rewrite Hdiv. assert (dlo / 8 <= D / 8) by (apply Z.div_le_mono; lia). lia.
        -- rewrite Hdiv2. assert ((D + uE E nl - 1) / 8 <= (end_hi fs b nl base dhi (snd (irange fs nl)) - 1) / 8) by (apply Z.div_le_mono; lia). lia.
      * exfalso. unfold two64 in *. lia.
Qed.

Lemma rp_ze_zero : forall E fs rgs (mm : word -> option byte) b nl g, Forall (fact_ok E) fs ->
  (forall R, In R rgs -> rg_ok ASEGSN E mm R) -> rp_ze fs rgs b nl = true -> 1 <= uE E nl -> uE E b + uE E nl <= 2 ^ 47 ->
  uE E b / 8 <= g <= (uE E b + uE E nl - 1) / 8 -> rd1 ASEGSN mm (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0).
Proof.
  intros E fs rgs mm b nl g HF HG Hze HN1 HBN Hg. unfold rp_ze in Hze.
  destruct (srl_lin fs 3 b) as [q|] eqn:Hq; [|discriminate]. destruct (lowb fs b 3) as [[|?|?]|] eqn:Hlb; try discriminate.
  apply existsb_exists in Hze as (R & HRin & H1). rewrite rp_ze1_eq in H1. unfold rp_ze1_ref in H1. destruct (rg_kind R) eqn:HkR; try discriminate.
  destruct (irange fs (lsub (lscale 8 (rg_size R)) nl)) as [lo hi] eqn:Hir.
  repeat match type of H1 with ((_ && _)%bool = true) => apply andb_prop in H1 as [H1 ?Hc] end.
  apply lin_eqb_eq in H1. apply Z.leb_le in Hc1. apply Z.ltb_lt in Hc, Hc0.
  pose proof (srl_lin_sound E fs 3 b q HF ltac:(lia) Hq) as Hqv. rewrite Z.shiftr_div_pow2 in Hqv by lia. change (2 ^ 3) with 8 in Hqv.
  fold (uE E q) (uE E b) in Hqv.
  pose proof (lowb_sound E fs b 3 0 HF Hlb) as Hal. fold (uE E b) in Hal. change (2 ^ 3) with 8 in Hal.
  pose proof (uE_range E b) as RB. pose proof (uE_range E nl) as RN. set (B := uE E b) in *. set (N := uE E nl) in *.
  assert (HB8 : 0 <= B / 8 <= B) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (Hbase : uE E (rg_base R) = SB + B / 8).
  { rewrite H1. rewrite uE_laddc3; [rewrite Hqv; unfold SB, SH_OFF; lia | unfold SH_OFF; lia | rewrite Hqv; unfold SH_OFF, two64; lia]. }
  pose proof (irange_sound E fs (rg_size R) HF) as Rs. fold (uE E (rg_size R)) in Rs. pose proof (uE_range E (rg_size R)) as RS.
  set (Z0 := uE E (rg_size R)) in *.
  assert (H8 : uE E (lscale 8 (rg_size R)) = 8 * Z0).
  { unfold uE. rewrite lden_lscale. fold (uE E (rg_size R)). fold Z0. apply u_small. unfold two64. lia. }
  pose proof (irange_sound E fs (lsub (lscale 8 (rg_size R)) nl) HF) as Rd. rewrite Hir in Rd. cbn [fst snd] in Rd.
  fold (uE E (lsub (lscale 8 (rg_size R)) nl)) in Rd.
  assert (HNZ : N <= 8 * Z0).
  { destruct (small_diff E (lscale 8 (rg_size R)) nl lo hi Rd) as [[Hl He]|[Hl He]]; rewrite H8 in Hl, He; fold N in Hl, He; [lia|].
    exfalso. unfold two64 in *. lia. }
  assert (Hgx : (B + N - 1) / 8 - B / 8 < Z0).
  { pose proof (Z.div_mod B 8 ltac:(lia)) as Hdm. rewrite Hal, Z.add_0_r in Hdm.
    replace (B + N - 1) with ((N - 1) + (B / 8) * 8) by lia. rewrite Z.div_add by lia.
    assert ((N - 1) / 8 < Z0) by (apply Z.div_lt_upper_bound; lia). lia. }
  destruct (HG R HRin) as (Hrs0 & Hrw & Hpts & Hcont).
  apply (qc_rgz_zero ASEGSN E mm R (SB + g) HkR Hc2 Hrs0 Hrw Hpts Hcont). rewrite Hbase. unfold rsz. fold (uE E (rg_size R)). fold Z0. lia.
Qed.

Lemma rp_brange_sound : forall E fs rgs b, Forall (fact_ok E) fs ->
  fst (rp_brange fs rgs b) <= uE E b <= snd (rp_brange fs rgs b).
Proof.
  intros E fs rgs b HF. unfold rp_brange.
  assert (Hg : forall l acc, fst acc <= uE E b <= snd acc -> fst (fold_left (rp_ref1 fs b) l acc) <= uE E b <= snd (fold_left (rp_ref1 fs b) l acc)).
  { induction l as [|R0 l IH]; intros acc Hacc; cbn [fold_left]; [exact Hacc|]. apply IH.
    unfold rp_ref1. set (base := rg_base R0).
    pose proof (irange_sound E fs (lsub b base) HF) as Rd. pose proof (irange_sound E fs base HF) as Rb0.
    destruct (irange fs (lsub b base)) as [dlo dhi] eqn:Hdr. destruct (irange fs base) as [blo0 bhi0] eqn:Hbr0.
    cbn [fst snd] in Rd, Rb0. fold (uE E (lsub b base)) in Rd. fold (uE E base) in Rb0.
    destruct (Z.leb 0 dlo) eqn:H1; [|exact Hacc]. destruct (Z.ltb dhi (2 ^ 40)) eqn:H2; [|exact Hacc].
    destruct (Z.ltb (bhi0 + 2 ^ 41) two64) eqn:H3; [|exact Hacc]. apply Z.leb_le in H1. apply Z.ltb_lt in H2, H3.
    pose proof (uE_range E b) as RB. pose proof (uE_range E base) as RB0.
    destruct (small_diff E b base dlo dhi Rd) as [[Hl He]|[Hl He]]; cbn [fst snd]; unfold two64 in *; lia. }
  apply Hg. exact (irange_sound E fs b HF).
Qed.

(* [comment removed for export] *)
Lemma partial_arith : forall B N K, 0 <= B -> 1 <= K <= 7 -> K <= N -> (B + (N - K)) mod 8 = 0 ->
  (B + N - 1) / 8 = (B + (N - K)) / 8 /\ (B + N - 1) mod 8 = K - 1 /\
  (N - K = 0 -> B / 8 = (B + N - 1) / 8) /\ (1 <= N - K -> (B + (N - K) - 1) / 8 = (B + (N - K)) / 8 - 1).
Proof.
  intros B N K HB HK HKN Hal.
  pose proof (Z.div_mod (B + (N - K)) 8 ltac:(lia)) as Hdm. rewrite Hal, Z.add_0_r in Hdm.
  set (G := (B + (N - K)) / 8) in *.
  assert (H1 : (B + N - 1) / 8 = G).
  { replace (B + N - 1) with ((K - 1) + G * 8) by lia. rewrite Z.div_add by lia. rewrite (Z.div_small (K - 1) 8) by lia. lia. }
  assert (H2 : (B + N - 1) mod 8 = K - 1).
  { replace (B + N - 1) with ((K - 1) + G * 8) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  split; [exact H1|]. split; [exact H2|]. split.
  - intros H0. rewrite H1. unfold G. f_equal. lia.
  - intros H0. replace (B + (N - K) - 1) with (7 + (G - 1) * 8) by lia. rewrite Z.div_add by lia. rewrite (Z.div_small 7 8) by lia. lia.
Qed.
Lemma sub_nowrap : forall N K lo hi, 0 <= N < two64 -> 0 <= K <= 7 -> 0 <= lo -> hi < 2 ^ 40 -> lo <= (N - K) mod two64 <= hi ->
  (N - K) mod two64 = N - K /\ K <= N.
Proof.
  intros N K lo hi HN HK Hlo Hhi Hr. destruct (Z_lt_le_dec (N - K) 0) as [Hneg|Hpos].
  - exfalso. replace ((N - K) mod two64) with (N - K + two64) in Hr by (apply Z.mod_unique with (-1); unfold two64 in *; lia). unfold two64 in *. lia.
  - split; [apply Z.mod_small; unfold two64 in *; lia | lia].
Qed.

(* [comment removed for export] *)
Section Node.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Variable img : tree Z.
Hypothesis Hwx : wx_segs_nowrap ASEGSN.
Hypothesis Himg : img_ok ASEGSN img.

#[using="Type"] Lemma rp_wrap_spec : forall E fs rgs b nl nhi, Forall (fact_ok E) fs -> rp_wrap fs rgs b nl nhi = true -> uE E nl <= nhi ->
  uE E b + uE E nl + 8 < two64 -> uE E b + uE E nl + 8 <= kLowEnd \/ SH_HI <= uE E b.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E fs rgs b nl nhi HF H Hn Hnw. unfold rp_wrap in H. destruct (rp_wrap_rg fs rgs b nl nhi) eqn:Hrg.
  2:{ pose proof (uE_range E nl) as RN.
      destruct (twoc_ns_sound E fs b (nhi + 8) HF H ltac:(lia)) as [L|[Hh _]]; [left; unfold kLowEnd, SH_LO in *; lia | right; exact Hh]. }
  clear H. rename Hrg into H. unfold rp_wrap_rg in H. apply existsb_cf_exists in H as (R0 & _ & H1). unfold rp_wrap1 in H1.
  set (base := rg_base R0) in *. destruct (irange fs (lsub b base)) as [dlo dhi] eqn:Hdr.
  destruct (Z.leb 0 dlo && Z.ltb dhi (2 ^ 40) && Z.ltb (snd (irange fs base) + 2 ^ 41) two64)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hc C3]. apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2, C3.
  destruct (wrap_hi fs (laddc base (- SH_HI))) as [whi|] eqn:Hwh; [|discriminate]. apply Z.leb_le in H1.
  pose proof (irange_sound E fs (lsub b base) HF) as Rd. rewrite Hdr in Rd. cbn [fst snd] in Rd. fold (uE E (lsub b base)) in Rd.
  pose proof (irange_sound E fs base HF) as Rb. fold (uE E base) in Rb.
  assert (Rw : uE E (laddc base (- SH_HI)) <= whi).
  { clear - HF Hwh. induction fs as [|f fs IH]; [discriminate|]. inversion HF as [|? ? Hf HF']; subst.
    destruct f; cbn [wrap_hi] in Hwh; try exact (IH HF' Hwh).
    destruct (lin_eqb l (laddc base (- SH_HI))) eqn:He; [|exact (IH HF' Hwh)].
    injection Hwh as <-. apply lin_eqb_eq in He. subst l. cbn [fact_ok] in Hf. unfold uE. lia. }
  pose proof (uE_range E b) as RB. pose proof (uE_range E base) as RBa.
  assert (HB : uE E b = uE E base + uE E (lsub b base)).
  { destruct (small_diff E b base dlo dhi Rd) as [[Hl He]|[Hl He]]; [lia | exfalso; unfold two64 in *; lia]. }
  assert (HW : uE E (laddc base (- SH_HI)) = (uE E base - SH_HI) mod two64).
  { unfold uE. rewrite lden_laddc, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. reflexivity. }
  destruct (Z_le_gt_dec SH_HI (uE E base)) as [Hhi|Hlo]; [right; lia|]. left.
  assert (HW2 : (uE E base - SH_HI) mod two64 = uE E base - SH_HI + two64).
  { symmetry. apply (Z.mod_unique _ _ (-1)); unfold SH_HI, two64 in *; lia. }
  pose proof (end_hi_sound E fs b nl base dhi nhi HF HB ltac:(lia) C2 ltac:(lia) Hn) as Hend.
  rewrite HW, HW2 in Rw. unfold kLowEnd, SH_LO, SH_HI, two64 in *. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rp_shadow_spec : forall S M E ms model b nl,
  DEN ASEGSN LIMIT model0 mem0 E S M ms model ->
  (if rp_zp (s_facts S) (s_rgs S) b nl then true else if rp_zbx (s_facts S) (s_rgs S) b nl then true else rp_za S M b nl) = true ->
  1 <= fst (irange (s_facts S) nl) ->
  uE E b + uE E nl + 8 <= kHighEnd ->
  exists b1 : byte, mrestrict (Hof E M model) (ms_mem ms) (Z_to_bv 64 (SB + (uE E b + uE E nl - 1) / 8)) = Some b1 /\
    (bv_unsigned b1 = 0 \/ (uE E b + uE E nl - 1) mod 8 < bv_unsigned b1 <= 7) /\
    forall g, uE E b / 8 <= g < (uE E b + uE E nl - 1) / 8 ->
      mrestrict (Hof E M model) (ms_mem ms) (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S M E ms model b nl Hd Hzz Hnlo Hend0.
  set (fs := s_facts S) in *.
  destruct (irange fs nl) as [nlo nhi] eqn:Hnr. cbn [fst] in Hnlo.
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh0 Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  set (B := uE E b) in *. set (N := uE E nl) in *. set (SP0 := uE E (sm_sp M)) in *.
  pose proof (irange_sound E fs nl HF) as Rn. rewrite Hnr in Rn. fold (uE E nl) N in Rn. cbn [fst snd] in Rn.
  pose proof (uE_range E b) as RB. pose proof (uE_range E nl) as RN. pose proof (uE_range E (sm_sp M)) as RS0. fold B N SP0 in RB, RN, RS0.
  destruct Hspok as [Hspo Hsh]. unfold sp_window_hi in Hsh. rewrite Hsp in Hsh. fold (uE E (sm_sp M)) SP0 in Hsh.
  assert (HBN : uE E (ladd b nl) = B + N).
  { unfold uE. rewrite lden_ladd, bv_add_unsigned. fold (uE E b) (uE E nl). fold B N. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. unfold kHighEnd, two64 in *. lia. }
  assert (Hend : B + N + 8 <= kHighEnd /\ True) by (split; [exact Hend0 | exact I]).
  assert (Hc : 1 <= nlo) by exact Hnlo.
  set (mm := mrestrict H (ms_mem ms)).
  rewrite Forall_forall in HG.
  (* [comment removed for export] *)
  assert (HzB : forall nl', rp_zbx fs (s_rgs S) b nl' = true -> 1 <= uE E nl' <= snd (irange fs nl') -> uE E nl' <= N ->
                forall g, B / 8 <= g <= (B + uE E nl' - 1) / 8 -> mm (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0)).
  { intros nl' Hzbx HN' HNN g Hg.
    assert (Hgb : (B + uE E nl' - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; [lia|]; unfold kHighEnd in Hend; lia).
    apply rd1_hi; [unfold SB, two64; pose proof (Z.div_pos B 8 ltac:(lia) ltac:(lia)); split; lia|].
    rewrite rp_zbx_ref_eq in Hzbx. destruct (rp_zb fs (s_rgs S) b nl') eqn:Hzb;
      [|exact (rp_ze_zero E fs (s_rgs S) mm b nl' g HF HG Hzbx (proj1 HN') ltac:(fold B; unfold kHighEnd in Hend; lia) ltac:(fold B; exact Hg))].
      destruct (rp_zb_spec E fs (s_rgs S) b nl' HF Hzb HN') as (sf & k & R & HRin & HzR & Hsf & Hkk).
      fold B in Hsf, Hkk.
      pose proof (HG R HRin) as HRok. pose proof HRok as HRok0. destruct HRok0 as (Hrs & Hrw & Hpts & Hcont).
      assert (Hin : uE E sf <= SB + g < uE E sf + k) by (unfold SB, SH_OFF in *; lia).
      assert (Hk0 : 0 <= k) by lia.
      pose proof (zero_ov_in E fs _ _ R HF HzR Hk0 Hrw _ Hin) as HwR.
      destruct (zero_ov_sound E fs _ _ R HF HzR Hk0 Hrw _ HwR Hin) as (HkR & [Ht|Ht]).
      + specialize (Hpts (SB + g - uE E (rg_base R)) ltac:(lia)). rewrite HkR in Hpts. destruct Hpts as (_ & Hz).
        specialize (Hz Ht). unfold uE in Hz. replace (bv_unsigned (lden E (rg_base R)) + (SB + g - bv_unsigned (lden E (rg_base R)))) with (SB + g) in Hz by lia.
        exact Hz.
      + destruct (Hcont _ _ Ht) as (_ & Hv). rewrite okey_pos in Hv by lia. cbn [bden] in Hv.
        unfold uE in Hv. replace (bv_unsigned (lden E (rg_base R)) + (SB + g - bv_unsigned (lden E (rg_base R)))) with (SB + g) in Hv by lia.
        exact Hv.
  }
  destruct (rp_zp fs (s_rgs S) b nl) eqn:Hzp.
    - (* [comment removed for export] *)
      clear Hzz. unfold rp_zp in Hzp. apply existsb_exists in Hzp as (R & HRin & Hz1). unfold rp_zp1 in Hz1.
      destruct (tget 1%positive (rg_cont R)) as [[bk|l j]|] eqn:Ht; try discriminate. destruct j; try discriminate.
      set (nl8 := lsub nl l) in *.
      destruct (srl_lin fs 3 (ladd b nl8)) as [q|] eqn:Hq; [|discriminate].
      destruct (irange fs l) as [llo lhi] eqn:Hlr. destruct (irange fs nl8) as [nlo8 nhi8] eqn:Hn8r.
      destruct (lin_eqb (rg_base R) (laddc q SH_OFF)) eqn:Hbq; [|discriminate].
      repeat match type of Hz1 with ((_ && _)%bool = true) => apply andb_prop in Hz1 as [Hz1 ?Hc] end.
      match goal with Hx : (if Z.eqb nhi8 0 then true else _) = true |- _ => rename Hx into Hz8i end.
      assert (Hz8o : (Z.eqb nhi8 0 || (Z.leb 1 nlo8 && rp_zbx fs (s_rgs S) b nl8))%bool = true)
        by (revert Hz8i; destruct (Z.eqb nhi8 0); [reflexivity|]; destruct (Z.leb 1 nlo8); intros Hz8i; [exact Hz8i | discriminate Hz8i]).
      clear Hz8i. rename Hz1 into Hllo. apply lin_eqb_eq in Hbq. rename Hbq into Hz1.
      repeat match goal with
             | Hx : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx
             | Hx : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hx
             end.
      match goal with Hx : match lowb fs (ladd b nl8) 3 with Some _ => _ | None => _ end = true |- _ => rename Hx into Hlow end.
      destruct (lowb fs (ladd b nl8) 3) as [[|?|?]|] eqn:Hlb; try discriminate. clear Hlow.
      match goal with Hx : (Z.eqb nhi8 0 || _)%bool = true |- _ => rename Hx into Hz8 end.
      assert (F1 : 1 <= llo) by assumption. assert (F2 : lhi <= 7) by assumption.
      assert (F3 : 0 <= nlo8) by assumption. assert (F4 : nhi8 < 2 ^ 40) by assumption.
      pose proof (uE_range E (ladd b nl)) as RBN. rewrite HBN in RBN.
      pose proof (irange_sound E fs l HF) as Rl. rewrite Hlr in Rl. cbn [fst snd] in Rl. fold (uE E l) in Rl. set (K := uE E l) in *.
      pose proof (irange_sound E fs nl8 HF) as Rn8. rewrite Hn8r in Rn8. cbn [fst snd] in Rn8. fold (uE E nl8) in Rn8.
      assert (HN8K : uE E nl8 = N - K /\ K <= N).
      { unfold nl8 in Rn8 |- *. unfold uE in Rn8 |- *. rewrite lden_lsub, bv_sub_unsigned in Rn8 |- *. fold (uE E nl) (uE E l) in Rn8 |- *. fold N K in Rn8 |- *.
        unfold bv_wrap, bv_modulus in Rn8 |- *. change (2 ^ Z.of_N 64) with two64 in Rn8 |- *.
        clear - Rn8 RN Rl F1 F2 F3 F4. apply (sub_nowrap N K nlo8 nhi8); lia. }
      destruct HN8K as [HN8 HKN].
      assert (HBN8 : uE E (ladd b nl8) = B + (N - K)).
      { unfold uE. rewrite lden_ladd, bv_add_unsigned. fold (uE E b) (uE E nl8). fold B. rewrite HN8. unfold bv_wrap, bv_modulus.
        change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. clear - RB RBN HKN Rl F1. lia. }
      pose proof (lowb_sound E fs (ladd b nl8) 3 0 HF Hlb) as Hal. fold (uE E (ladd b nl8)) in Hal. rewrite HBN8 in Hal. change (2 ^ 3) with 8 in Hal.
      pose proof (srl_lin_sound E fs 3 (ladd b nl8) q HF ltac:(lia) Hq) as Hqv. rewrite Z.shiftr_div_pow2 in Hqv by lia. change (2 ^ 3) with 8 in Hqv.
      fold (uE E q) (uE E (ladd b nl8)) in Hqv. rewrite HBN8 in Hqv.
      assert (HK17 : 1 <= K <= 7) by (clear - Rl F1 F2; lia).
      destruct (partial_arith B N K (proj1 RB) HK17 HKN Hal) as (Hg1 & Hm1 & Hg0 & Hg8).
      assert (Hgb : (B + N - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; [lia|]; clear - Hend; unfold kHighEnd in Hend; lia).
      assert (Hg1n : 0 <= (B + N - 1) / 8) by (apply Z.div_pos; [clear - RB HKN HK17; lia | lia]).
      assert (Hbase : uE E (rg_base R) = SB + (B + N - 1) / 8).
      { rewrite Hz1. pose proof (uE_range E q) as RQ. rewrite uE_laddc3; [rewrite Hqv, <- Hg1; clear; unfold SB, SH_OFF; lia | unfold SH_OFF; lia |].
        rewrite Hqv, <- Hg1. clear - Hgb Hg1n. unfold SH_OFF, two64. lia. }
      pose proof (HG R HRin) as HRok. destruct HRok as (Hrs & Hrw & Hpts & Hcont).
      destruct (Hcont _ _ Ht) as (Hk1 & Hv). change (Zpos 1 - 1) with 0 in Hv. rewrite Z.add_0_r in Hv. cbn [bden] in Hv.
      fold (uE E (rg_base R)) in Hv. rewrite Hbase in Hv. change (8 * 0) with 0 in Hv. rewrite Z.shiftr_0_r in Hv. fold (uE E l) K in Hv.
      exists (Z_to_bv 8 K). split; [|split].
      + apply rd1_hi; [clear - Hgb Hg1n; unfold SB, two64; lia | exact Hv].
      + right. rewrite Hm1. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
        rewrite Z.mod_small by (clear - HK17; lia). clear - HK17. lia.
      + intros g Hg. apply orb_prop in Hz8 as [Hz8|Hz8].
        * apply Z.eqb_eq in Hz8. exfalso. assert (H0 : N - K = 0) by (clear - Hz8 Rn8 HN8 F3; lia).
          specialize (Hg0 H0). clear - Hg Hg0. lia.
        * apply andb_prop in Hz8 as [Hlo8 Hzb8]. apply Z.leb_le in Hlo8.
          assert (H1 : 1 <= N - K) by (clear - Hlo8 Rn8 HN8; lia).
          apply (HzB nl8 Hzb8); [rewrite Hn8r; cbn [snd]; clear - Rn8 HN8 H1; lia | clear - HN8 HK17; lia |]. rewrite HN8, (Hg8 H1).
          clear - Hg Hg1. lia.
    - (* [comment removed for export] *)
      assert (Hzero : forall g, B / 8 <= g <= (B + N - 1) / 8 -> mm (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0)).
      { intros g Hg. assert (Hgb : (B + N - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; [lia|]; unfold kHighEnd in Hend; lia).
        destruct (rp_zbx fs (s_rgs S) b nl) eqn:Hzb.
        - exact (HzB nl Hzb ltac:(fold N; rewrite Hnr; cbn [snd]; lia) ltac:(fold N; lia) g Hg).
        - apply rd1_hi; [unfold SB, two64; pose proof (Z.div_pos B 8 ltac:(lia) ltac:(lia)); split; lia|].
      change (rp_za S M b nl = true) in Hzz. unfold rp_za in Hzz. cbv zeta in Hzz. change (s_facts S) with fs in Hzz.
          destruct (irange fs (lsub b (sm_sp M))) as [dlo dhi] eqn:Hdr.
          destruct (irange fs (lsub (ladd b nl) (sm_sp M))) as [elo ehi] eqn:Her.
          match type of Hzz with ((if ?c then ?x else false) = true) =>
            assert (Hz2 : (c && x)%bool = true) by (destruct c; [exact Hzz | discriminate Hzz]) end.
          clear Hzz. apply andb_prop in Hz2 as [Hz Hxx]. apply andb_prop in Hxx as [Hxx Hsep]. apply andb_prop in Hxx as [Hal Hoq].
          repeat match type of Hz with ((_ && _)%bool = true) => apply andb_prop in Hz as [Hz ?Hc] end.
          match goal with Hx : existsb hshb_g (sm_maps M) = true |- _ => rename Hx into Hhs end.
          match goal with Hx : existsb (fun z => (Z.eqb (fst z) HSHB && _)%bool) (sm_zr M) = true |- _ => rename Hx into Hzre end.
          match goal with Hx : ((Z.leb 0 dlo && _) || _)%bool = true |- _ => rename Hx into Hdw end.
          match goal with Hx : ((Z.leb 0 elo && _) || _)%bool = true |- _ => rename Hx into Hew end.
          pose proof (irange_sound E fs (lsub b (sm_sp M)) HF) as Rd. rewrite Hdr in Rd. cbn [fst snd] in Rd.
          pose proof (irange_sound E fs (lsub (ladd b nl) (sm_sp M)) HF) as Re. rewrite Her in Re. cbn [fst snd] in Re.
          pose proof (proj1 Hend) as HendX. unfold kHighEnd in HendX.
          assert (HdB : SP0 - 2 ^ 20 <= B <= SP0 + 2 ^ 22).
          { fold (uE E (lsub b (sm_sp M))) in Rd.
            apply orb_prop in Hdw as [Hdw|Hdw]; apply andb_prop in Hdw as [D1 D2]; [apply Z.leb_le in D1, D2 | apply Z.leb_le in D1; apply Z.ltb_lt in D2];
            destruct (small_diff E b (sm_sp M) dlo dhi Rd) as [[Hl He]|[Hl He]]; fold B SP0 in Hl, He; unfold two64 in *; lia. }
          assert (HdE : SP0 - 2 ^ 20 <= B + N <= SP0 + 2 ^ 22).
          { fold (uE E (lsub (ladd b nl) (sm_sp M))) in Re.
            apply orb_prop in Hew as [Hew|Hew]; apply andb_prop in Hew as [D1 D2]; [apply Z.leb_le in D1, D2 | apply Z.leb_le in D1; apply Z.ltb_lt in D2];
            destruct (small_diff E (ladd b nl) (sm_sp M) elo ehi Re) as [[Hl He]|[Hl He]]; rewrite HBN in Hl, He; fold SP0 in Hl, He;
              unfold two64 in *; lia. }
          unfold mm, H. rewrite existsb_lz_eq in Hzre, Hhs. rewrite qc_allow_scan_eq in Hal. apply (den_shzero ASEGSN LIMIT model0 mem0 S M E ms model (SB + g) Hd Hzre Hhs Hal Hoq Hsep).
          + fold SP0. unfold SB, SH_OFF. assert ((SP0 - 2 ^ 20) / 8 <= B / 8) by (apply Z.div_le_mono; lia). lia.
          + fold SP0. unfold SB, SH_OFF. assert ((B + N - 1) / 8 <= (SP0 + 2 ^ 22 + 128) / 8) by (apply Z.div_le_mono; lia). lia.
          + unfold SB, SH_HI. lia. }
      exists (Z_to_bv 8 0). split; [apply Hzero; split; [apply Z.div_le_mono; lia | lia]|]. split; [left; reflexivity|].
      intros g Hg. apply Hzero. lia. 
Qed.

#[using="Hwx Himg"] Theorem den_rp : forall S M E ms model T,
  rp_chk img S M = true -> DEN ASEGSN LIMIT model0 mem0 E S M ms model ->
  (forall E' ms' model', agree (s_next S) E E' -> DEN ASEGSN LIMIT model0 mem0 E' (rp_post S) M ms' model' ->
      realizes_cfg ASEGSN cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGSN cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Himg : LiaFast.U) => LiaFast.u0).
  intros S M E ms model T Hck Hd Hk.
  rewrite rp_chk_eq in Hck. unfold rp_chk_ref in Hck. unfold rp_post in Hk.
  set (fs := s_facts S) in *. set (b := rget (s_regs S) (rkey (xr 10))) in *. set (nl := rget (s_regs S) (rkey (xr 11))) in *.
  set (sp := rget (s_regs S) (rkey (xr 2))) in *.
  destruct (rg_is S 1) as [r|] eqn:R1; [|discriminate].
  destruct (s_resv S) eqn:Hrv; try discriminate.
  destruct (find_frame (s_rgs S) sp O) as [[j0 d]|] eqn:Hff; [|discriminate].
  destruct (rp_brange fs (s_rgs S) b) as [blo bhi] eqn:Hbr. destruct (irange fs nl) as [nlo nhi] eqn:Hnr.
  destruct (irange fs sp) as [slo shi] eqn:Hsr.
  match type of Hck with ((if ?c then ?x else false) = true) =>
    assert (Hck2 : (c && x)%bool = true) by (destruct c; [exact Hck | discriminate Hck]) end.
  clear Hck. apply andb_prop in Hck2 as [Hck Hzz]. rewrite rp_any_eq in Hzz.
  repeat match type of Hck with ((_ && _)%bool = true) => apply andb_prop in Hck as [Hck ?Hc] end.
  rename Hck into Hpc0.
  match goal with Hx : rp_rngb _ _ _ _ _ _ _ = true |- _ => rename Hx into Hrng end.
  repeat match goal with
         | Hx : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in Hx
         | Hx : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx
         | Hx : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hx
         end.
  match goal with Hx : lwf (s_next S) b = true |- _ => rename Hx into Hwb end.
  match goal with Hx : lwf (s_next S) nl = true |- _ => rename Hx into Hwn end.
  match goal with Hx : cells_chk img fs (s_rgs S) = true |- _ => rename Hx into Hcells end.
  (* [comment removed for export] *)
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh0 Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hrsv. cbn [rsv_ok] in Hrsv.
  cbn [restrict ms_pc_val ms_svc_pending ms_resv ms_regs] in Hpc, Hsvc, Hrsv, HR.
  set (B := uE E b) in *. set (N := uE E nl) in *. set (USP := uE E sp) in *. set (SP0 := uE E (sm_sp M)) in *.
  pose proof (rp_brange_sound E fs (s_rgs S) b HF) as Rb. rewrite Hbr in Rb. fold B in Rb. cbn [fst snd] in Rb.
  pose proof (irange_sound E fs nl HF) as Rn. rewrite Hnr in Rn. fold (uE E nl) N in Rn. cbn [fst snd] in Rn.
  pose proof (irange_sound E fs sp HF) as Rs. rewrite Hsr in Rs. fold (uE E sp) USP in Rs. cbn [fst snd] in Rs.
  pose proof (irange_sound E fs (ladd b nl) HF) as Rbn. fold (uE E (ladd b nl)) in Rbn.
  pose proof (uE_range E b) as RB. pose proof (uE_range E nl) as RN. pose proof (uE_range E sp) as RS.
  pose proof (uE_range E (sm_sp M)) as RS0. fold B N USP SP0 in RB, RN, RS, RS0.
  destruct Hspok as [Hspo Hsh]. unfold sp_window_hi in Hsh. rewrite Hsp in Hsh. fold (uE E (sm_sp M)) SP0 in Hsh.
  assert (HBN : uE E (ladd b nl) = B + N).
  { unfold uE. rewrite lden_ladd, bv_add_unsigned. fold (uE E b) (uE E nl). fold B N. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. lia. }
  rewrite HBN in Rbn.
  assert (Hend : B + N + 8 <= kHighEnd /\ (B + N + 8 <= kLowEnd \/ SH_HI <= B)).
  { unfold rp_rngb in Hrng.
    match type of Hrng with ((if (?c1 && ?c2)%bool then _ else if ?c3 then _ else if ?c4 then _ else _) = true) =>
      destruct (c1 && c2)%bool eqn:Hx1; [| destruct c3 eqn:Hx2; [| destruct c4 eqn:Hx3; [|discriminate Hrng]]] end.
    - apply andb_prop in Hx1 as [X1 X2]. apply Z.leb_le in X1, X2. unfold kHighEnd, kLowEnd, SH_HI in *. lia.
    - apply Z.leb_le in Hx2. unfold kHighEnd, kLowEnd, SH_HI in *. lia.
    - apply Z.leb_le in Hx3. split; [unfold kHighEnd in *; lia|].
      exact (rp_wrap_spec E fs (s_rgs S) b nl nhi HF Hrng ltac:(fold N; lia) ltac:(fold B N; unfold kHighEnd, two64 in *; lia)). }
  set (mm := mrestrict H (ms_mem ms)).
  rewrite Forall_forall in HG.
  assert (Hzl : exists b1 : byte, mm (Z_to_bv 64 (SB + (B + N - 1) / 8)) = Some b1 /\
                  (bv_unsigned b1 = 0 \/ (B + N - 1) mod 8 < bv_unsigned b1 <= 7) /\
                  forall g, B / 8 <= g < (B + N - 1) / 8 -> mm (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0))
    by exact (rp_shadow_spec S M E ms model b nl Hd Hzz ltac:(change (1 <= fst (irange fs nl)); rewrite Hnr; cbn [fst]; lia) (proj1 Hend)).
  destruct Hzl as (b1 & Hl1 & Hb1c & Hzero').
  (* [comment removed for export] *)
  destruct (find_frame_spec _ _ _ _ _ Hff) as (R0 & sz & Hj0 & _ & Hk0 & Hsz0 & Hoff0 & Hd72). rewrite Nat.sub_0_r in Hj0.
  destruct (is_const_sound E _ sz Hsz0) as [Hsz1 Hsz64].
  assert (Hrs0 : rsz E R0 = sz) by (unfold rsz; rewrite Hsz1; apply u_small; exact Hsz64).
  pose proof (HG R0 (nth_error_In _ _ Hj0)) as HR0. pose proof HR0 as HR00.
  destruct HR00 as (Hrsz & Hrw & Hpts & _). rewrite Hrs0 in Hrsz, Hrw, Hpts.
  set (BASE := uE E (rg_base R0)) in *.
  assert (HUSP : USP = BASE + d) by (unfold USP, BASE, uE; apply lin_off_u; [exact Hoff0 | unfold uE in Hrw; lia]).
  (* [comment removed for export] *)
  assert (Hx : forall k, 0 <= k < 32 -> (Z_to_bv 5 k : reg) = xr k) by (intros k Hk32; reflexivity).
  destruct (is_const_sound E _ r R1) as [Hr1 Hr64].
  assert (Hra : getr (ms_regs ms) 1%bv = Z_to_bv 64 r) by (replace (1%bv : reg) with (xr 1) by (apply bv_eq; reflexivity); rewrite (HR (xr 1)); exact Hr1).
  assert (H2 : getr (ms_regs ms) 2%bv = Z_to_bv 64 USP).
  { replace (2%bv : reg) with (xr 2) by (apply bv_eq; reflexivity). rewrite (HR (xr 2)). fold sp. unfold USP, uE. symmetry. apply u64_of. }
  assert (H10 : getr (ms_regs ms) 10%bv = Z_to_bv 64 B).
  { replace (10%bv : reg) with (xr 10) by (apply bv_eq; reflexivity). rewrite (HR (xr 10)). fold b. unfold B, uE. symmetry. apply u64_of. }
  assert (H11 : getr (ms_regs ms) 11%bv = Z_to_bv 64 N).
  { replace (11%bv : reg) with (xr 11) by (apply bv_eq; reflexivity). rewrite (HR (xr 11)). fold nl. unfold N, uE. symmetry. apply u64_of. }
  assert (Hret : ret_ok (Z_to_bv 64 r)) by (apply ret_ok_even; rewrite u_small by exact Hr64; assumption).
  (* [comment removed for export] *)
  assert (HrpH : rpH mm B N USP b1).
  { constructor.
    - lia.
    - lia.
    - destruct Hend as [Hend1 [Hend2|Hend2]]; [left; lia | right; unfold kHighBeg, SH_HI in *; lia].
    - unfold two64 in *. lia.
    - assert ((B + N - 1) / 8 <= (bhi + nhi - 1) / 8) by (apply Z.div_le_mono; lia). unfold SB, SH_OFF in *. lia.
    - intros g Hg. apply Hzero'. lia.
    - exact Hl1.
    - exact Hb1c.
    - intros a Ha. apply store_ok_from; [lia | cbn [Z.of_nat Pos.of_succ_nat]; unfold two64 in *; lia|].
      intros i Hi. cbn [Z.of_nat Pos.of_succ_nat] in Hi. replace (a + i) with (BASE + (a - BASE + i)) by lia.
      specialize (Hpts (a - BASE + i) ltac:(lia)). rewrite Hk0 in Hpts. exact (proj2 Hpts).
    - unfold cells. pose proof (cells_chk_sound E img fs (s_rgs S) mm Himg (proj2 (Forall_forall _ _) HG) HF Hcells) as X.
      assert (X' : forall a v, In (a, v) rp_cells_list -> cell mm a v) by (intros a v Hin; exact (X (a, v) Hin)).
      refine (conj (X' 0xdcc10 0xe4db8 _) (conj (X' 0xe4db8 SB _) (conj (X' 0xdcc18 0xe5aa8 _) (conj (X' 0xe5aa8 0 _)
               (conj (X' 0xdcc20 0xe5ab0 _) (conj (X' 0xe5ab0 0 _) (conj (X' 0xdcc28 0xe5aa0 _) (X' 0xe5aa0 kHighEnd _))))))));
        unfold rp_cells_list; cbn [In]; repeat (first [left; reflexivity | right]). }
  destruct (@as_region_is_poisoned (mkFP (ms_fregs ms) (ms_fcsr ms)) mm (ms_rom ms) B N USP b1 HrpH (ms_regs ms)
              (Z_to_bv 64 r) Hret Hra H2 H10 H11) as (regs' & mm' & Hms & Hmm & P10 & P2 & P1 & Pk).
  assert (Hmsr : restrict H ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (0x639e0 : word) mm (ms_rom ms)).
  { destruct ms as [rg fr pcv sv rv fc mem rom]. cbn [ms_pc_val ms_svc_pending ms_resv] in Hsvc, Hrsv, Hpc. subst sv rv.
    cbn [ms_pc_val] in Hpc. rewrite Hpc0 in Hpc. unfold RP_PC in Hpc. subst pcv.
    unfold restrict, mkst, mm. cbn. f_equal. apply bv_eq. reflexivity. }
  apply (den_run_post_fw ASEGSN cfg LIMIT model0 mem0 Hwx E S M ms model T regs' r [(xr 10, lconst 0)] RP_HAVS j0 R0 (d - 72) d
           mm' Hd Hrv Hj0 Hk0).
  - lia.
  - lia.
  - rewrite Hrs0. lia.
  - fold H. rewrite Hmsr. apply fx_isteps_of_msteps. exact Hms.
  - intros w Hw. destruct Hmm as [-> | ->]; [apply rp_frame_out | apply rp_frame7_out]; (unfold two64 in *; lia) || (fold BASE; rewrite HUSP; lia).
  - intros i Hi. specialize (Hpts i ltac:(lia)). rewrite Hk0 in Hpts. fold BASE in Hpts |- *. destruct Hpts as [P1' P2'].
    assert (Hor : forall w, mm' w = mm w \/ exists bb, mm' w = Some bb)
      by (intros w; destruct Hmm as [-> | ->]; [apply rp_frame_or | apply rp_frame7_or]).
    split; [exact (mm_or_rd1 _ _ _ _ (Hor _) P1') | exact (mm_or_wview _ _ _ _ (Hor _) P2')].
  - apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    split; [intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate|].
    split; [reflexivity|].
    replace (xr 10) with (10%bv : reg) by (apply bv_eq; reflexivity). rewrite P10. rewrite lden_lconst. reflexivity.
  - unfold RP_HAVS. repeat constructor; intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate.
  - intros rr Es Eh.
    assert (Hex : exists k, 0 <= k < 32 /\ rr = Z_to_bv 5 k).
    { exists (bv_unsigned rr). split; [pose proof (bv_unsigned_in_range _ rr) as X; change (bv_modulus 5) with 32 in X; lia|].
      symmetry; apply Z_to_bv_bv_unsigned. }
    destruct Hex as (k & Hk32 & ->). apply Pk. unfold rp_clob.
    assert (Hc : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31) by lia.
    destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ].
    all: first [ (vm_compute in Es; discriminate Es) | (vm_compute in Eh; discriminate Eh) | (vm_compute; reflexivity) ].
  - intros E' ms' model' Ha' Hd'. exact (Hk E' ms' model' Ha' Hd').
Qed.
End Node.
End AsanRpNode.

Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxQRNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMchr.FxQcsChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxRunPost OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanRegP OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQcsNode.AsanRpNode.
Import ListNotations.

Module AsanRpNodeS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith Znumtheory List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec SeqExec CatExec CatSim.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Frame MemSplit RefMemcpyLib ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare OSSVerify.Proofs.fast_float.from_chars.lib.Common.Frame OSSVerify.Proofs.fast_float.from_chars.lib.Common.MemSplit OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.PlacementCount OSSVerify.Proofs.fast_float.from_chars.lib.Common.AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEnt FxChStart FxChFix FxChWv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChWv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxQNode FxMchr FxMNode FxRunPost FxSNodes AsanSNodes AsanRegP.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxRunPost OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanRegP OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQcsNode.AsanRpNode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
(* [comment removed for export] *)
Local Notation existsb := existsb_lz (only parsing).
Local Lemma existsb_exists : forall {A} (f : A -> bool) (l : list A), existsb_lz f l = true <-> exists x, In x l /\ f x = true.
Proof. intros A f l. rewrite existsb_lz_eq. apply List.existsb_exists. Qed.

(* [comment removed for export] *)
Definition rp_zs1_ref (fs : list fact) (b nl : lin) (R : region) : bool :=
  match rg_kind R with
  | RZ =>
      let base8 := lscale 8 (laddc (rg_base R) (- SH_OFF)) in
      let '(blo, bhi) := irange fs (rg_base R) in
      let '(dlo, dhi) := irange fs (lsub b base8) in
      let '(elo, ehi) := irange fs (lsub (ladd base8 (lscale 8 (rg_size R))) (ladd b nl)) in
      if range_zero (rg_cont R) 0 two64 then
        (Z.leb SH_OFF blo && Z.ltb bhi (SH_OFF + 2 ^ 44) && Z.leb 0 dlo && Z.ltb dhi (2 ^ 48) && Z.leb 0 elo && Z.ltb ehi (2 ^ 48) &&
         Z.ltb (snd (irange fs (rg_size R))) (2 ^ 44))%bool
      else false
  | _ => false
  end.
(* [comment removed for export] *)
Definition rp_zs1 (fs : list fact) (b nl : lin) (R : region) : bool :=
  match rg_kind R with
  | RZ =>
      if range_zero (rg_cont R) 0 two64 then
        let '(blo, bhi) := irange fs (rg_base R) in
        if Z.leb SH_OFF blo then if Z.ltb bhi (SH_OFF + 2 ^ 44) then
          let base8 := lscale 8 (laddc (rg_base R) (- SH_OFF)) in
          let '(dlo, dhi) := irange fs (lsub b base8) in
          if Z.leb 0 dlo then if Z.ltb dhi (2 ^ 48) then
            let '(elo, ehi) := irange fs (lsub (ladd base8 (lscale 8 (rg_size R))) (ladd b nl)) in
            (Z.leb 0 elo && Z.ltb ehi (2 ^ 48) && Z.ltb (snd (irange fs (rg_size R))) (2 ^ 44))%bool
          else false else false
        else false else false
      else false
  | _ => false
  end.
Lemma rp_zs1_eq : forall fs b nl R, rp_zs1 fs b nl R = rp_zs1_ref fs b nl R.
Proof.
  intros fs b nl R. unfold rp_zs1, rp_zs1_ref. destruct (rg_kind R); try reflexivity. cbv zeta.
  destruct (irange fs (rg_base R)) as [blo bhi]. destruct (irange fs (lsub b (lscale 8 (laddc (rg_base R) (- SH_OFF))))) as [dlo dhi].
  destruct (irange fs (lsub (ladd (lscale 8 (laddc (rg_base R) (- SH_OFF))) (lscale 8 (rg_size R))) (ladd b nl))) as [elo ehi].
  destruct (range_zero (rg_cont R) 0 two64); [|reflexivity].
  destruct (Z.leb SH_OFF blo), (Z.ltb bhi (SH_OFF + 2 ^ 44)), (Z.leb 0 dlo), (Z.ltb dhi (2 ^ 48)); reflexivity.
Qed.
Definition rp_zs (fs : list fact) (rgs : list region) (b nl : lin) : bool := existsb (rp_zs1 fs b nl) rgs.

(* [comment removed for export] *)
Definition rp_wrap_e1_ref (fs : list fact) (b nl : lin) (R0 : region) : bool :=
  let base := rg_base R0 in let z := rg_size R0 in
  let '(dlo, dhi) := irange fs (lsub b base) in
  let '(elo, ehi) := irange fs (lsub (ladd base z) (ladd b nl)) in
  if (Z.leb 0 dlo && Z.ltb dhi (2 ^ 40) && Z.leb 9 elo && Z.ltb ehi (2 ^ 40) && Z.ltb (snd (irange fs base) + 2 ^ 41) two64 &&
      Z.ltb (snd (irange fs z)) (2 ^ 40) && Z.leb (snd (irange fs (ladd base z))) (kHighEnd + 1))%bool then
    match wrap_hi fs (laddc base (- SH_HI)), wrap_hi fs (laddc (ladd base z) (- SH_HI)) with
    | Some wa, Some wb => (Z.leb wa (two64 + SH_LO - SH_HI - 1) && Z.leb wb (two64 + SH_LO - SH_HI))%bool
    | _, _ => false
    end
  else false.
(* [comment removed for export] *)
Definition rp_wrap_e1 (fs : list fact) (b nl : lin) (R0 : region) : bool :=
  let base := rg_base R0 in let z := rg_size R0 in
  let '(dlo, dhi) := irange fs (lsub b base) in
  if Z.leb 0 dlo then if Z.ltb dhi (2 ^ 40) then
    let '(elo, ehi) := irange fs (lsub (ladd base z) (ladd b nl)) in
    if Z.leb 9 elo then if Z.ltb ehi (2 ^ 40) then
      if (Z.ltb (snd (irange fs base) + 2 ^ 41) two64 && Z.ltb (snd (irange fs z)) (2 ^ 40) && Z.leb (snd (irange fs (ladd base z))) (kHighEnd + 1))%bool then
        match wrap_hi fs (laddc base (- SH_HI)), wrap_hi fs (laddc (ladd base z) (- SH_HI)) with
        | Some wa, Some wb => (Z.leb wa (two64 + SH_LO - SH_HI - 1) && Z.leb wb (two64 + SH_LO - SH_HI))%bool
        | _, _ => false
        end
      else false
    else false else false
  else false else false.
Lemma rp_wrap_e1_eq : forall fs b nl R0, rp_wrap_e1 fs b nl R0 = rp_wrap_e1_ref fs b nl R0.
Proof.
  intros fs b nl R0. unfold rp_wrap_e1, rp_wrap_e1_ref. cbv zeta.
  destruct (irange fs (lsub b (rg_base R0))) as [dlo dhi]. destruct (irange fs (lsub (ladd (rg_base R0) (rg_size R0)) (ladd b nl))) as [elo ehi].
  destruct (Z.leb 0 dlo), (Z.ltb dhi (2 ^ 40)), (Z.leb 9 elo), (Z.ltb ehi (2 ^ 40)); reflexivity.
Qed.
Definition rp_wrap_e (fs : list fact) (rgs : list region) (b nl : lin) : bool := existsb (rp_wrap_e1 fs b nl) rgs.
Definition rps_rngb (fs : list fact) (rgs : list region) (b nl : lin) (blo nhi ehi' : Z) : bool :=
  if rp_rngb fs rgs b nl blo nhi ehi' then true else rp_wrap_e fs rgs b nl.

Definition rps_chk_ref (img : tree Z) (S : sst) (M : smodel) : bool :=
  let fs := s_facts S in let rgs := s_rgs S in
  let b := rget (s_regs S) (rkey (xr 10)) in let nl := rget (s_regs S) (rkey (xr 11)) in let sp := rget (s_regs S) (rkey (xr 2)) in
  match rg_is S 1, s_resv S, find_frame rgs sp O with
  | Some r, RNone, Some (j0, d) =>
      let '(blo, bhi) := rp_brange fs rgs b in let '(nlo, nhi) := irange fs nl in
      let '(slo, shi) := irange fs sp in let ehi' := Z.min (snd (irange fs (ladd b nl))) (bhi + nhi) in
      if (Z.eqb (s_pc S) RP_PC && Z.eqb (r mod 2) 0 && Z.leb 1 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (bhi + nhi) two64 &&
          rps_rngb fs rgs b nl blo nhi ehi' &&
          Z.leb 80 slo && Z.ltb shi two64 && Z.ltb (SH_OFF + (bhi + nhi - 1) / 8) (slo - 72) &&
          lwf (s_next S) b && lwf (s_next S) nl && cells_chk img fs rgs)%bool
      then (if rp_zs fs rgs b nl then true else rp_any S M fs rgs b nl)
      else false
  | _, _, _ => false
  end.
Lemma rps_rng0_rngb : forall fs rgs b nl blo nhi e, rp_rng0 blo e = true -> rps_rngb fs rgs b nl blo nhi e = true.
Proof. intros fs rgs b nl blo nhi e H. unfold rps_rngb. rewrite (rp_rng0_rngb fs rgs b nl blo nhi e H). reflexivity. Qed.
Lemma rps_rngb_mono : forall fs rgs b nl blo blo' nhi e e', blo <= blo' -> e' <= e ->
  rps_rngb fs rgs b nl blo nhi e = true -> rps_rngb fs rgs b nl blo' nhi e' = true.
Proof.
  intros fs rgs b nl blo blo' nhi e e' Hlo He H. unfold rps_rngb in *.
  destruct (rp_rngb fs rgs b nl blo nhi e) eqn:H1; [rewrite (rp_rngb_mono fs rgs b nl blo blo' nhi e e' Hlo He H1); reflexivity|].
  destruct (rp_rngb fs rgs b nl blo' nhi e'); [reflexivity | exact H].
Qed.
Definition rps_chk (img : tree Z) (S : sst) (M : smodel) : bool :=
  let fs := s_facts S in let rgs := s_rgs S in
  let b := rget (s_regs S) (rkey (xr 10)) in let nl := rget (s_regs S) (rkey (xr 11)) in let sp := rget (s_regs S) (rkey (xr 2)) in
  match rg_is S 1, s_resv S, find_frame rgs sp O with
  | Some r, RNone, Some (j0, d) =>
      let '(nlo, nhi) := irange fs nl in let '(slo, shi) := irange fs sp in let eh := snd (irange fs (ladd b nl)) in
      if (Z.eqb (s_pc S) RP_PC && Z.eqb (r mod 2) 0 && Z.leb 1 nlo && Z.leb nhi (2 ^ 40) && Z.leb 80 slo && Z.ltb shi two64 &&
          lwf (s_next S) b && lwf (s_next S) nl && cells_chk img fs rgs)%bool
      then (let r0 := irange fs b in
            if (if rp_t1c nhi slo eh r0 then true else rp_t1g (rps_rngb fs rgs b nl) nhi slo eh (fold_left (rp_ref1 fs b) rgs r0))
            then (if rp_zs fs rgs b nl then true else rp_any S M fs rgs b nl) else false)
      else false
  | _, _, _ => false
  end.
Lemma rps_chk_eq : forall img S M, rps_chk img S M = rps_chk_ref img S M.
Proof.
  intros img S M. unfold rps_chk, rps_chk_ref. cbv zeta.
  destruct (rg_is S 1) as [r|]; [|reflexivity]. destruct (s_resv S); try reflexivity.
  destruct (find_frame (s_rgs S) (rget (s_regs S) (rkey (xr 2))) 0) as [[j0 d]|]; [|reflexivity].
  unfold rp_brange.
  set (fs := s_facts S). set (rgs := s_rgs S). set (b := rget (s_regs S) (rkey (xr 10))). set (nl := rget (s_regs S) (rkey (xr 11))).
  set (sp := rget (s_regs S) (rkey (xr 2))).
  pose proof (rp_fold_sub fs b rgs (irange fs b)) as [Hs1 Hs2].
  set (r0 := irange fs b) in *. set (rr := fold_left (rp_ref1 fs b) rgs r0) in *.
  destruct (irange fs nl) as [nlo nhi]. destruct (irange fs sp) as [slo shi].
  set (eh := snd (irange fs (ladd b nl))).
  rewrite (rp_t1_lazy (rps_rngb fs rgs b nl) nhi slo eh r0 rr (fun blo e => rps_rng0_rngb fs rgs b nl blo nhi e)
             (fun blo blo' e e' => rps_rngb_mono fs rgs b nl blo blo' nhi e e') Hs1 Hs2).
  unfold rp_t1g. destruct rr as [blo bhi]. cbn [fst snd]. apply rp_bool_shuffle.
Qed.

Lemma wrap_hi_le : forall E fs g whi, Forall (fact_ok E) fs -> wrap_hi fs g = Some whi -> uE E g <= whi.
Proof.
  intros E fs g whi HF Hwh. induction fs as [|f fs IH]; [discriminate|]. inversion HF as [|? ? Hf HF']; subst.
  destruct f; cbn [wrap_hi] in Hwh; try exact (IH HF' Hwh).
  destruct (lin_eqb l g) eqn:He; [|exact (IH HF' Hwh)].
  injection Hwh as <-. apply lin_eqb_eq in He. subst l. cbn [fact_ok] in Hf. unfold uE. lia.
Qed.
Lemma rp_wrap_e_spec : forall E fs rgs b nl, Forall (fact_ok E) fs -> rp_wrap_e fs rgs b nl = true -> uE E nl <= 2 ^ 40 ->
  uE E b + uE E nl < two64 -> uE E b + uE E nl + 8 <= kHighEnd /\ (uE E b + uE E nl + 8 <= kLowEnd \/ SH_HI <= uE E b).
Proof.
  intros E fs rgs b nl HF H Hn Hnw. unfold rp_wrap_e in H. apply existsb_exists in H as (R0 & _ & H1). rewrite rp_wrap_e1_eq in H1. unfold rp_wrap_e1_ref in H1.
  set (base := rg_base R0) in *. set (z := rg_size R0) in *.
  destruct (irange fs (lsub b base)) as [dlo dhi] eqn:Hdr. destruct (irange fs (lsub (ladd base z) (ladd b nl))) as [elo ehi] eqn:Her.
  match type of H1 with ((if ?c then _ else _) = true) => destruct c eqn:Hc; [|discriminate] end.
  repeat match type of Hc with ((_ && _)%bool = true) => apply andb_prop in Hc as [Hc ?C] end.
  apply Z.leb_le in Hc, C3, C. apply Z.ltb_lt in C0, C1, C2, C4.
  destruct (wrap_hi fs (laddc base (- SH_HI))) as [wa|] eqn:Hwa; [|discriminate].
  destruct (wrap_hi fs (laddc (ladd base z) (- SH_HI))) as [wb|] eqn:Hwb; [|discriminate].
  apply andb_prop in H1 as [W1 W2]. apply Z.leb_le in W1, W2.
  pose proof (wrap_hi_le E fs _ wa HF Hwa) as RA. pose proof (wrap_hi_le E fs _ wb HF Hwb) as RBw.
  pose proof (irange_sound E fs (lsub b base) HF) as Rd. rewrite Hdr in Rd. cbn [fst snd] in Rd. fold (uE E (lsub b base)) in Rd.
  pose proof (irange_sound E fs (lsub (ladd base z) (ladd b nl)) HF) as Re. rewrite Her in Re. cbn [fst snd] in Re.
  fold (uE E (lsub (ladd base z) (ladd b nl))) in Re.
  pose proof (irange_sound E fs base HF) as Rb. fold (uE E base) in Rb. pose proof (irange_sound E fs z HF) as Rz. fold (uE E z) in Rz.
  pose proof (irange_sound E fs (ladd base z) HF) as Rez. fold (uE E (ladd base z)) in Rez.
  pose proof (uE_range E b) as RB. pose proof (uE_range E base) as RBa. pose proof (uE_range E z) as RZ. pose proof (uE_range E nl) as RN.
  set (B := uE E b) in *. set (N := uE E nl) in *. set (Ba := uE E base) in *. set (Z0 := uE E z) in *.
  assert (HB : B = Ba + uE E (lsub b base)).
  { destruct (small_diff E b base dlo dhi Rd) as [[Hl He]|[Hl He]]; fold B Ba in Hl, He; [lia | exfalso; unfold two64 in *; lia]. }
  assert (HvE : uE E (ladd base z) = Ba + Z0).
  { unfold uE. rewrite lden_ladd, bv_add_unsigned. fold (uE E base) (uE E z). fold Ba Z0. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
    apply Z.mod_small. unfold two64 in *. lia. }
  assert (HvBN : uE E (ladd b nl) = B + N).
  { unfold uE. rewrite lden_ladd, bv_add_unsigned. fold (uE E b) (uE E nl). fold B N. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
    apply Z.mod_small. unfold two64 in *. lia. }
  assert (HEnd : B + N + 9 <= Ba + Z0).
  { destruct (small_diff E (ladd base z) (ladd b nl) elo ehi Re) as [[Hl He]|[Hl He]]; rewrite HvE, HvBN in Hl, He; [lia | exfalso; unfold two64 in *; lia]. }
  assert (HWA : uE E (laddc base (- SH_HI)) = (Ba - SH_HI) mod two64).
  { unfold uE. rewrite lden_laddc, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. reflexivity. }
  assert (HWB : uE E (laddc (ladd base z) (- SH_HI)) = (Ba + Z0 - SH_HI) mod two64).
  { unfold uE. rewrite lden_laddc. fold (uE E (ladd base z)). rewrite HvE, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. reflexivity. }
  rewrite HvE in Rez. split; [unfold kHighEnd in *; lia|].
  destruct (Z_le_gt_dec SH_HI Ba) as [Hhi|Hlo]; [right; lia|]. left.
  assert (HW2 : (Ba - SH_HI) mod two64 = Ba - SH_HI + two64) by (symmetry; apply (Z.mod_unique _ _ (-1)); unfold SH_HI, two64 in *; lia).
  rewrite HWA, HW2 in RA.
  assert (HBaLo : Ba < SH_LO) by (unfold SH_LO, SH_HI, two64 in *; lia).
  assert (HW3 : (Ba + Z0 - SH_HI) mod two64 = Ba + Z0 - SH_HI + two64) by (symmetry; apply (Z.mod_unique _ _ (-1)); unfold SH_LO, SH_HI, two64 in *; lia).
  rewrite HWB, HW3 in RBw. unfold kLowEnd, SH_LO, SH_HI, two64 in *. lia.
Qed.

Lemma rp_zs_zero : forall E fs rgs (mm : word -> option byte) b nl g, Forall (fact_ok E) fs ->
  (forall R, In R rgs -> rg_ok ASEGSN E mm R) -> rp_zs fs rgs b nl = true -> 1 <= uE E nl -> uE E b + uE E nl <= 2 ^ 47 ->
  uE E b / 8 <= g <= (uE E b + uE E nl - 1) / 8 -> rd1 ASEGSN mm (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0).
Proof.
  intros E fs rgs mm b nl g HF HG Hzs HN1 HBN Hg. unfold rp_zs in Hzs.
  apply existsb_exists in Hzs as (R & HRin & H1). rewrite rp_zs1_eq in H1. unfold rp_zs1_ref in H1. destruct (rg_kind R) eqn:HkR; try discriminate.
  set (base8 := lscale 8 (laddc (rg_base R) (- SH_OFF))) in *.
  destruct (irange fs (rg_base R)) as [blo bhi] eqn:Hbr. destruct (irange fs (lsub b base8)) as [dlo dhi] eqn:Hdr.
  destruct (irange fs (lsub (ladd base8 (lscale 8 (rg_size R))) (ladd b nl))) as [elo ehi] eqn:Her.
  destruct (range_zero (rg_cont R) 0 two64) eqn:Hrz; [|discriminate].
  repeat match type of H1 with ((_ && _)%bool = true) => apply andb_prop in H1 as [H1 ?Hc] end.
  apply Z.leb_le in H1, Hc1, Hc3. apply Z.ltb_lt in Hc, Hc0, Hc2, Hc4.
  pose proof (irange_sound E fs (rg_base R) HF) as Rb. rewrite Hbr in Rb. cbn [fst snd] in Rb. fold (uE E (rg_base R)) in Rb.
  pose proof (irange_sound E fs (rg_size R) HF) as Rs. fold (uE E (rg_size R)) in Rs.
  pose proof (irange_sound E fs (lsub b base8) HF) as Rd. rewrite Hdr in Rd. cbn [fst snd] in Rd. fold (uE E (lsub b base8)) in Rd.
  pose proof (irange_sound E fs (lsub (ladd base8 (lscale 8 (rg_size R))) (ladd b nl)) HF) as Re. rewrite Her in Re. cbn [fst snd] in Re.
  fold (uE E (lsub (ladd base8 (lscale 8 (rg_size R))) (ladd b nl))) in Re.
  pose proof (uE_range E b) as RB. pose proof (uE_range E nl) as RN. pose proof (uE_range E (rg_size R)) as RS.
  set (B := uE E b) in *. set (N := uE E nl) in *. set (BZ := uE E (rg_base R)) in *. set (Z0 := uE E (rg_size R)) in *.
  assert (Hb8 : uE E base8 = 8 * (BZ - SH_OFF)).
  { unfold base8, uE. rewrite lden_lscale, lden_laddc. fold (uE E (rg_base R)). fold BZ.
    rewrite (u_small64 (BZ + - SH_OFF)) by (unfold SH_OFF, two64 in *; lia). apply u_small64. unfold SH_OFF, two64 in *. lia. }
  assert (Hz8 : uE E (lscale 8 (rg_size R)) = 8 * Z0).
  { unfold uE. rewrite lden_lscale. fold (uE E (rg_size R)). fold Z0. apply u_small64. unfold two64. lia. }
  assert (He8 : uE E (ladd base8 (lscale 8 (rg_size R))) = 8 * (BZ - SH_OFF) + 8 * Z0).
  { unfold uE. rewrite lden_ladd, bv_add_unsigned. fold (uE E base8) (uE E (lscale 8 (rg_size R))). rewrite Hb8, Hz8.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. unfold SH_OFF, two64 in *. lia. }
  assert (HBNv : uE E (ladd b nl) = B + N).
  { unfold uE. rewrite lden_ladd, bv_add_unsigned. fold (uE E b) (uE E nl). fold B N. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. unfold two64. lia. }
  assert (HD : 8 * (BZ - SH_OFF) <= B).
  { destruct (small_diff E b base8 dlo dhi Rd) as [[Hl He]|[Hl He]]; rewrite Hb8 in Hl; fold B in Hl; [exact Hl|].
    exfalso. rewrite Hb8 in He. fold B in He. unfold SH_OFF, two64 in *. lia. }
  assert (HEv : B + N <= 8 * (BZ - SH_OFF) + 8 * Z0).
  { destruct (small_diff E (ladd base8 (lscale 8 (rg_size R))) (ladd b nl) elo ehi Re) as [[Hl He]|[Hl He]]; rewrite He8, HBNv in Hl; [exact Hl|].
    exfalso. rewrite He8, HBNv in He. unfold SH_OFF, two64 in *. lia. }
  destruct (HG R HRin) as (Hrs0 & Hrw & Hpts & Hcont).
  apply (qc_rgz_zero ASEGSN E mm R (SB + g) HkR Hrz Hrs0 Hrw Hpts Hcont). fold BZ. unfold rsz. fold (uE E (rg_size R)). fold Z0.
  assert (G1 : BZ - SH_OFF <= B / 8) by (apply Z.div_le_lower_bound; lia).
  assert (G2 : (B + N - 1) / 8 < BZ - SH_OFF + Z0) by (apply Z.div_lt_upper_bound; lia).
  unfold SB, SH_OFF in *. lia.
Qed.

Section NodeS.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Variable img : tree Z.
Hypothesis Hwx : wx_segs_nowrap ASEGSN.
Hypothesis Himg : img_ok ASEGSN img.

#[using="Type"] Lemma rps_shadow_spec : forall S M E ms model b nl,
  DEN ASEGSN LIMIT model0 mem0 E S M ms model ->
  (if rp_zs (s_facts S) (s_rgs S) b nl then true else
   if rp_zp (s_facts S) (s_rgs S) b nl then true else if rp_zbx (s_facts S) (s_rgs S) b nl then true else rp_za S M b nl) = true ->
  1 <= fst (irange (s_facts S) nl) ->
  uE E b + uE E nl + 8 <= kHighEnd ->
  exists b1 : byte, mrestrict (Hof E M model) (ms_mem ms) (Z_to_bv 64 (SB + (uE E b + uE E nl - 1) / 8)) = Some b1 /\
    (bv_unsigned b1 = 0 \/ (uE E b + uE E nl - 1) mod 8 < bv_unsigned b1 <= 7) /\
    forall g, uE E b / 8 <= g < (uE E b + uE E nl - 1) / 8 ->
      mrestrict (Hof E M model) (ms_mem ms) (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S M E ms model b nl Hd Hzz Hnlo Hend0.
  destruct (rp_zs (s_facts S) (s_rgs S) b nl) eqn:Hzs; [|exact (rp_shadow_spec LIMIT model0 mem0 S M E ms model b nl Hd Hzz Hnlo Hend0)].
  clear Hzz. pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh0 Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  rewrite Forall_forall in HG.
  pose proof (irange_sound E (s_facts S) nl HF) as Rn. fold (uE E nl) in Rn.
  pose proof (uE_range E b) as RB. pose proof (uE_range E nl) as RN.
  set (B := uE E b) in *. set (N := uE E nl) in *. set (mm := mrestrict (Hof E M model) (ms_mem ms)).
  assert (HN1 : 1 <= N) by lia.
  assert (Hz : forall g, B / 8 <= g <= (B + N - 1) / 8 -> mm (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0)).
  { intros g Hg. assert (Hgb : (B + N - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; [lia|]; unfold kHighEnd in Hend0; lia).
    apply rd1_hi; [unfold SB, two64; pose proof (Z.div_pos B 8 ltac:(lia) ltac:(lia)); split; lia|].
    exact (rp_zs_zero E (s_facts S) (s_rgs S) mm b nl g HF HG Hzs HN1 ltac:(fold B N; unfold kHighEnd in Hend0; lia) Hg). }
  exists (Z_to_bv 8 0). split; [apply Hz; split; [apply Z.div_le_mono; lia | lia]|]. split; [left; reflexivity|].
  intros g Hg. apply Hz. lia.
Qed.

#[using="Hwx Himg"] Theorem den_rps : forall S M E ms model T,
  rps_chk img S M = true -> DEN ASEGSN LIMIT model0 mem0 E S M ms model ->
  (forall E' ms' model', agree (s_next S) E E' -> DEN ASEGSN LIMIT model0 mem0 E' (rp_post S) M ms' model' ->
      realizes_cfg ASEGSN cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGSN cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Himg : LiaFast.U) => LiaFast.u0).
  intros S M E ms model T Hck Hd Hk.
  rewrite rps_chk_eq in Hck. unfold rps_chk_ref in Hck. unfold rp_post in Hk.
  set (fs := s_facts S) in *. set (b := rget (s_regs S) (rkey (xr 10))) in *. set (nl := rget (s_regs S) (rkey (xr 11))) in *.
  set (sp := rget (s_regs S) (rkey (xr 2))) in *.
  destruct (rg_is S 1) as [r|] eqn:R1; [|discriminate].
  destruct (s_resv S) eqn:Hrv; try discriminate.
  destruct (find_frame (s_rgs S) sp O) as [[j0 d]|] eqn:Hff; [|discriminate].
  destruct (rp_brange fs (s_rgs S) b) as [blo bhi] eqn:Hbr. destruct (irange fs nl) as [nlo nhi] eqn:Hnr.
  destruct (irange fs sp) as [slo shi] eqn:Hsr.
  match type of Hck with ((if ?c then ?x else false) = true) =>
    assert (Hck2 : (c && x)%bool = true) by (destruct c; [exact Hck | discriminate Hck]) end.
  clear Hck. apply andb_prop in Hck2 as [Hck Hzz]. rewrite rp_any_eq in Hzz.
  repeat match type of Hck with ((_ && _)%bool = true) => apply andb_prop in Hck as [Hck ?Hc] end.
  rename Hck into Hpc0.
  match goal with Hx : rps_rngb _ _ _ _ _ _ _ = true |- _ => rename Hx into Hrng end.
  match goal with Hx : Z.leb nhi (2 ^ 40) = true |- _ => pose proof (proj1 (Z.leb_le _ _) Hx) as Hnhi40 end.
  repeat match goal with
         | Hx : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in Hx
         | Hx : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx
         | Hx : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hx
         end.
  match goal with Hx : lwf (s_next S) b = true |- _ => rename Hx into Hwb end.
  match goal with Hx : lwf (s_next S) nl = true |- _ => rename Hx into Hwn end.
  match goal with Hx : cells_chk img fs (s_rgs S) = true |- _ => rename Hx into Hcells end.
  (* [comment removed for export] *)
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh0 Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hrsv. cbn [rsv_ok] in Hrsv.
  cbn [restrict ms_pc_val ms_svc_pending ms_resv ms_regs] in Hpc, Hsvc, Hrsv, HR.
  set (B := uE E b) in *. set (N := uE E nl) in *. set (USP := uE E sp) in *. set (SP0 := uE E (sm_sp M)) in *.
  pose proof (rp_brange_sound E fs (s_rgs S) b HF) as Rb. rewrite Hbr in Rb. fold B in Rb. cbn [fst snd] in Rb.
  pose proof (irange_sound E fs nl HF) as Rn. rewrite Hnr in Rn. fold (uE E nl) N in Rn. cbn [fst snd] in Rn.
  pose proof (irange_sound E fs sp HF) as Rs. rewrite Hsr in Rs. fold (uE E sp) USP in Rs. cbn [fst snd] in Rs.
  pose proof (irange_sound E fs (ladd b nl) HF) as Rbn. fold (uE E (ladd b nl)) in Rbn.
  pose proof (uE_range E b) as RB. pose proof (uE_range E nl) as RN. pose proof (uE_range E sp) as RS.
  pose proof (uE_range E (sm_sp M)) as RS0. fold B N USP SP0 in RB, RN, RS, RS0.
  destruct Hspok as [Hspo Hsh]. unfold sp_window_hi in Hsh. rewrite Hsp in Hsh. fold (uE E (sm_sp M)) SP0 in Hsh.
  assert (HBN : uE E (ladd b nl) = B + N).
  { unfold uE. rewrite lden_ladd, bv_add_unsigned. fold (uE E b) (uE E nl). fold B N. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. lia. }
  rewrite HBN in Rbn.
  assert (Hend : B + N + 8 <= kHighEnd /\ (B + N + 8 <= kLowEnd \/ SH_HI <= B)).
  { unfold rps_rngb in Hrng.
    destruct (rp_rngb fs (s_rgs S) b nl blo nhi (Z.min (snd (irange fs (ladd b nl))) (bhi + nhi))) eqn:Hrng0;
      [clear Hrng; rename Hrng0 into Hrng | clear Hrng0;
       exact (rp_wrap_e_spec E fs (s_rgs S) b nl HF Hrng ltac:(fold N; lia) ltac:(fold B N; lia))].
    unfold rp_rngb in Hrng.
    match type of Hrng with ((if (?c1 && ?c2)%bool then _ else if ?c3 then _ else if ?c4 then _ else _) = true) =>
      destruct (c1 && c2)%bool eqn:Hx1; [| destruct c3 eqn:Hx2; [| destruct c4 eqn:Hx3; [|discriminate Hrng]]] end.
    - apply andb_prop in Hx1 as [X1 X2]. apply Z.leb_le in X1, X2. unfold kHighEnd, kLowEnd, SH_HI in *. lia.
    - apply Z.leb_le in Hx2. unfold kHighEnd, kLowEnd, SH_HI in *. lia.
    - apply Z.leb_le in Hx3. split; [unfold kHighEnd in *; lia|].
      exact (rp_wrap_spec E fs (s_rgs S) b nl nhi HF Hrng ltac:(fold N; lia) ltac:(fold B N; unfold kHighEnd, two64 in *; lia)). }
  set (mm := mrestrict H (ms_mem ms)).
  rewrite Forall_forall in HG.
  assert (Hzl : exists b1 : byte, mm (Z_to_bv 64 (SB + (B + N - 1) / 8)) = Some b1 /\
                  (bv_unsigned b1 = 0 \/ (B + N - 1) mod 8 < bv_unsigned b1 <= 7) /\
                  forall g, B / 8 <= g < (B + N - 1) / 8 -> mm (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0))
    by exact (rps_shadow_spec S M E ms model b nl Hd Hzz ltac:(change (1 <= fst (irange fs nl)); rewrite Hnr; cbn [fst]; lia) (proj1 Hend)).
  destruct Hzl as (b1 & Hl1 & Hb1c & Hzero').
  (* [comment removed for export] *)
  destruct (find_frame_spec _ _ _ _ _ Hff) as (R0 & sz & Hj0 & _ & Hk0 & Hsz0 & Hoff0 & Hd72). rewrite Nat.sub_0_r in Hj0.
  destruct (is_const_sound E _ sz Hsz0) as [Hsz1 Hsz64].
  assert (Hrs0 : rsz E R0 = sz) by (unfold rsz; rewrite Hsz1; apply u_small; exact Hsz64).
  pose proof (HG R0 (nth_error_In _ _ Hj0)) as HR0. pose proof HR0 as HR00.
  destruct HR00 as (Hrsz & Hrw & Hpts & _). rewrite Hrs0 in Hrsz, Hrw, Hpts.
  set (BASE := uE E (rg_base R0)) in *.
  assert (HUSP : USP = BASE + d) by (unfold USP, BASE, uE; apply lin_off_u; [exact Hoff0 | unfold uE in Hrw; lia]).
  (* [comment removed for export] *)
  assert (Hx : forall k, 0 <= k < 32 -> (Z_to_bv 5 k : reg) = xr k) by (intros k Hk32; reflexivity).
  destruct (is_const_sound E _ r R1) as [Hr1 Hr64].
  assert (Hra : getr (ms_regs ms) 1%bv = Z_to_bv 64 r) by (replace (1%bv : reg) with (xr 1) by (apply bv_eq; reflexivity); rewrite (HR (xr 1)); exact Hr1).
  assert (H2 : getr (ms_regs ms) 2%bv = Z_to_bv 64 USP).
  { replace (2%bv : reg) with (xr 2) by (apply bv_eq; reflexivity). rewrite (HR (xr 2)). fold sp. unfold USP, uE. symmetry. apply u64_of. }
  assert (H10 : getr (ms_regs ms) 10%bv = Z_to_bv 64 B).
  { replace (10%bv : reg) with (xr 10) by (apply bv_eq; reflexivity). rewrite (HR (xr 10)). fold b. unfold B, uE. symmetry. apply u64_of. }
  assert (H11 : getr (ms_regs ms) 11%bv = Z_to_bv 64 N).
  { replace (11%bv : reg) with (xr 11) by (apply bv_eq; reflexivity). rewrite (HR (xr 11)). fold nl. unfold N, uE. symmetry. apply u64_of. }
  assert (Hret : ret_ok (Z_to_bv 64 r)) by (apply ret_ok_even; rewrite u_small by exact Hr64; assumption).
  (* [comment removed for export] *)
  assert (HrpH : rpH mm B N USP b1).
  { constructor.
    - lia.
    - lia.
    - destruct Hend as [Hend1 [Hend2|Hend2]]; [left; lia | right; unfold kHighBeg, SH_HI in *; lia].
    - unfold two64 in *. lia.
    - assert ((B + N - 1) / 8 <= (bhi + nhi - 1) / 8) by (apply Z.div_le_mono; lia). unfold SB, SH_OFF in *. lia.
    - intros g Hg. apply Hzero'. lia.
    - exact Hl1.
    - exact Hb1c.
    - intros a Ha. apply store_ok_from; [lia | cbn [Z.of_nat Pos.of_succ_nat]; unfold two64 in *; lia|].
      intros i Hi. cbn [Z.of_nat Pos.of_succ_nat] in Hi. replace (a + i) with (BASE + (a - BASE + i)) by lia.
      specialize (Hpts (a - BASE + i) ltac:(lia)). rewrite Hk0 in Hpts. exact (proj2 Hpts).
    - unfold cells. pose proof (cells_chk_sound E img fs (s_rgs S) mm Himg (proj2 (Forall_forall _ _) HG) HF Hcells) as X.
      assert (X' : forall a v, In (a, v) rp_cells_list -> cell mm a v) by (intros a v Hin; exact (X (a, v) Hin)).
      refine (conj (X' 0xdcc10 0xe4db8 _) (conj (X' 0xe4db8 SB _) (conj (X' 0xdcc18 0xe5aa8 _) (conj (X' 0xe5aa8 0 _)
               (conj (X' 0xdcc20 0xe5ab0 _) (conj (X' 0xe5ab0 0 _) (conj (X' 0xdcc28 0xe5aa0 _) (X' 0xe5aa0 kHighEnd _))))))));
        unfold rp_cells_list; cbn [In]; repeat (first [left; reflexivity | right]). }
  destruct (@as_region_is_poisoned (mkFP (ms_fregs ms) (ms_fcsr ms)) mm (ms_rom ms) B N USP b1 HrpH (ms_regs ms)
              (Z_to_bv 64 r) Hret Hra H2 H10 H11) as (regs' & mm' & Hms & Hmm & P10 & P2 & P1 & Pk).
  assert (Hmsr : restrict H ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (0x639e0 : word) mm (ms_rom ms)).
  { destruct ms as [rg fr pcv sv rv fc mem rom]. cbn [ms_pc_val ms_svc_pending ms_resv] in Hsvc, Hrsv, Hpc. subst sv rv.
    cbn [ms_pc_val] in Hpc. rewrite Hpc0 in Hpc. unfold RP_PC in Hpc. subst pcv.
    unfold restrict, mkst, mm. cbn. f_equal. apply bv_eq. reflexivity. }
  apply (den_run_post_fw ASEGSN cfg LIMIT model0 mem0 Hwx E S M ms model T regs' r [(xr 10, lconst 0)] RP_HAVS j0 R0 (d - 72) d
           mm' Hd Hrv Hj0 Hk0).
  - lia.
  - lia.
  - rewrite Hrs0. lia.
  - fold H. rewrite Hmsr. apply fx_isteps_of_msteps. exact Hms.
  - intros w Hw. destruct Hmm as [-> | ->]; [apply rp_frame_out | apply rp_frame7_out]; (unfold two64 in *; lia) || (fold BASE; rewrite HUSP; lia).
  - intros i Hi. specialize (Hpts i ltac:(lia)). rewrite Hk0 in Hpts. fold BASE in Hpts |- *. destruct Hpts as [P1' P2'].
    assert (Hor : forall w, mm' w = mm w \/ exists bb, mm' w = Some bb)
      by (intros w; destruct Hmm as [-> | ->]; [apply rp_frame_or | apply rp_frame7_or]).
    split; [exact (mm_or_rd1 _ _ _ _ (Hor _) P1') | exact (mm_or_wview _ _ _ _ (Hor _) P2')].
  - apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    split; [intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate|].
    split; [reflexivity|].
    replace (xr 10) with (10%bv : reg) by (apply bv_eq; reflexivity). rewrite P10. rewrite lden_lconst. reflexivity.
  - unfold RP_HAVS. repeat constructor; intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate.
  - intros rr Es Eh.
    assert (Hex : exists k, 0 <= k < 32 /\ rr = Z_to_bv 5 k).
    { exists (bv_unsigned rr). split; [pose proof (bv_unsigned_in_range _ rr) as X; change (bv_modulus 5) with 32 in X; lia|].
      symmetry; apply Z_to_bv_bv_unsigned. }
    destruct Hex as (k & Hk32 & ->). apply Pk. unfold rp_clob.
    assert (Hc : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31) by lia.
    destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ].
    all: first [ (vm_compute in Es; discriminate Es) | (vm_compute in Eh; discriminate Eh) | (vm_compute; reflexivity) ].
  - intros E' ms' model' Ha' Hd'. exact (Hk E' ms' model' Ha' Hd').
Qed.
End NodeS.
End AsanRpNodeS.

Module FxWrapOut.
(* [comment removed for export] *)
From Stdlib Require Import ZArith Znumtheory List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep FxChTwoC.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChTwoC.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxQNode AsanRegP.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanRegP OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQcsNode.AsanRpNode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition wrap_out1 (fs : list fact) (b nl : lin) (nhi : Z) (R0 : region) : bool :=
  let base := rg_base R0 in
  let '(dlo, dhi) := irange fs (lsub b base) in
  if (Z.leb 0 dlo && Z.ltb dhi (2 ^ 40) && Z.ltb (snd (irange fs base) + 2 ^ 41) two64)%bool then
    match wrap_hi fs (laddc base (- SH_HI)) with
    | Some whi => Z.leb (end_hi fs b nl base dhi nhi) (two64 + SH_LO - SH_HI - whi)
    | None => false
    end
  else false.
Definition wrap_out (fs : list fact) (rgs : list region) (b nl : lin) (nhi : Z) : bool := existsb (wrap_out1 fs b nl nhi) rgs.

Lemma rp_wrap_spec_lo : forall E fs rgs b nl nhi, Forall (fact_ok E) fs -> rp_wrap fs rgs b nl nhi = true -> uE E nl <= nhi ->
  uE E b + uE E nl + 8 < two64 -> uE E b + uE E nl + 8 <= SH_LO \/ SH_HI <= uE E b.
Proof.
  intros E fs rgs b nl nhi HF H Hn Hnw. unfold rp_wrap in H. destruct (rp_wrap_rg fs rgs b nl nhi) eqn:Hrg.
  2:{ pose proof (uE_range E nl) as RN.
      destruct (twoc_ns_sound E fs b (nhi + 8) HF H ltac:(lia)) as [L|[Hh _]]; [left; lia | right; exact Hh]. }
  clear H. rename Hrg into H. unfold rp_wrap_rg in H.
  try rewrite FxQNode.existsb_cf_eq in H. try rewrite FxChDen.existsb_lz_eq in H. apply existsb_exists in H as (R0 & _ & H1). unfold rp_wrap1 in H1.
  set (base := rg_base R0) in *. destruct (irange fs (lsub b base)) as [dlo dhi] eqn:Hdr.
  destruct (Z.leb 0 dlo && Z.ltb dhi (2 ^ 40) && Z.ltb (snd (irange fs base) + 2 ^ 41) two64)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hc C3]. apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2, C3.
  destruct (wrap_hi fs (laddc base (- SH_HI))) as [whi|] eqn:Hwh; [|discriminate]. apply Z.leb_le in H1.
  pose proof (irange_sound E fs (lsub b base) HF) as Rd. rewrite Hdr in Rd. cbn [fst snd] in Rd. fold (uE E (lsub b base)) in Rd.
  pose proof (irange_sound E fs base HF) as Rb. fold (uE E base) in Rb.
  assert (Rw : uE E (laddc base (- SH_HI)) <= whi).
  { clear - HF Hwh. induction fs as [|f fs IH]; [discriminate|]. inversion HF as [|? ? Hf HF']; subst.
    destruct f; cbn [wrap_hi] in Hwh; try exact (IH HF' Hwh).
    destruct (lin_eqb l (laddc base (- SH_HI))) eqn:He; [|exact (IH HF' Hwh)].
    injection Hwh as <-. apply lin_eqb_eq in He. subst l. cbn [fact_ok] in Hf. unfold uE. lia. }
  pose proof (uE_range E b) as RB. pose proof (uE_range E base) as RBa.
  assert (HB : uE E b = uE E base + uE E (lsub b base)).
  { destruct (small_diff E b base dlo dhi Rd) as [[Hl He]|[Hl He]]; [lia | exfalso; unfold two64 in *; lia]. }
  assert (HW : uE E (laddc base (- SH_HI)) = (uE E base - SH_HI) mod two64).
  { unfold uE. rewrite lden_laddc, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. reflexivity. }
  destruct (Z_le_gt_dec SH_HI (uE E base)) as [Hhi|Hlo]; [right; lia|]. left.
  assert (HW2 : (uE E base - SH_HI) mod two64 = uE E base - SH_HI + two64).
  { symmetry. apply (Z.mod_unique _ _ (-1)); unfold SH_HI, two64 in *; lia. }
  pose proof (end_hi_sound E fs b nl base dhi nhi HF HB ltac:(lia) C2 ltac:(lia) Hn) as Hend.
  rewrite HW, HW2 in Rw. unfold SH_LO, SH_HI, two64 in *. lia.
Qed.

Lemma wrap_out_spec : forall E fs rgs b nl nhi, Forall (fact_ok E) fs -> wrap_out fs rgs b nl nhi = true -> uE E nl <= nhi ->
  uE E b + uE E nl < two64 -> uE E b + uE E nl <= SH_LO \/ SH_HI <= uE E b.
Proof.
  intros E fs rgs b nl nhi HF H Hn Hnw. unfold wrap_out in H. apply existsb_exists in H as (R0 & _ & H1). unfold wrap_out1 in H1.
  set (base := rg_base R0) in *. destruct (irange fs (lsub b base)) as [dlo dhi] eqn:Hdr.
  destruct (Z.leb 0 dlo && Z.ltb dhi (2 ^ 40) && Z.ltb (snd (irange fs base) + 2 ^ 41) two64)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hc C3]. apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2, C3.
  destruct (wrap_hi fs (laddc base (- SH_HI))) as [whi|] eqn:Hwh; [|discriminate]. apply Z.leb_le in H1.
  pose proof (irange_sound E fs (lsub b base) HF) as Rd. rewrite Hdr in Rd. cbn [fst snd] in Rd. fold (uE E (lsub b base)) in Rd.
  pose proof (irange_sound E fs base HF) as Rb. fold (uE E base) in Rb.
  assert (Rw : uE E (laddc base (- SH_HI)) <= whi).
  { clear - HF Hwh. induction fs as [|f fs IH]; [discriminate|]. inversion HF as [|? ? Hf HF']; subst.
    destruct f; cbn [wrap_hi] in Hwh; try exact (IH HF' Hwh).
    destruct (lin_eqb l (laddc base (- SH_HI))) eqn:He; [|exact (IH HF' Hwh)].
    injection Hwh as <-. apply lin_eqb_eq in He. subst l. cbn [fact_ok] in Hf. unfold uE. lia. }
  pose proof (uE_range E b) as RB. pose proof (uE_range E base) as RBa.
  assert (HB : uE E b = uE E base + uE E (lsub b base)).
  { destruct (small_diff E b base dlo dhi Rd) as [[Hl He]|[Hl He]]; [lia | exfalso; unfold two64 in *; lia]. }
  assert (HW : uE E (laddc base (- SH_HI)) = (uE E base - SH_HI) mod two64).
  { unfold uE. rewrite lden_laddc, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. reflexivity. }
  destruct (Z_le_gt_dec SH_HI (uE E base)) as [Hhi|Hlo]; [right; lia|]. left.
  assert (HW2 : (uE E base - SH_HI) mod two64 = uE E base - SH_HI + two64).
  { symmetry. apply (Z.mod_unique _ _ (-1)); unfold SH_HI, two64 in *; lia. }
  pose proof (end_hi_sound E fs b nl base dhi nhi HF HB ltac:(lia) C2 ltac:(lia) Hn) as Hend.
  rewrite HW, HW2 in Rw. unfold SH_LO, SH_HI, two64 in *. lia.
Qed.
End FxWrapOut.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Record qssite : Type := QSS { qss_q : qsite; qss_pcs : Z; qss_rV : reg; qss_rT : reg; qss_rU : reg; qss_rF : reg; qss_rL : reg;
                              qss_bok : bv 13 }.
Definition qssite_ok (segs : list Segment) (s : qssite) : Prop :=
  let '(QSS q pcs rV rT rU rF rL bok) := s in
  qsite_ok segs q /\
  let '(QS pc0 rP rA rB rY rZ rW ord bim beq) := q in
  (rP <> 0%bv /\ rV <> 0%bv /\ rT <> 0%bv /\ rU <> 0%bv /\ rF <> 0%bv /\ rL <> 0%bv) /\
  (rV <> rY /\ rV <> rA /\ rV <> rP) /\ (rT <> rY /\ rT <> rP /\ rT <> rV) /\ (rU <> rY /\ rU <> rP /\ rU <> rV /\ rU <> rT) /\
  (rF <> rY /\ rF <> rP /\ rF <> rU) /\ (rL <> rY /\ rL <> rP /\ rL <> rF) /\ rP <> rY /\
  qins segs pcs 0 (Load SZ1 true rV rY (Z_to_bv 12 0)) /\ qins segs pcs 1 (OpImm ALU_AND rT rA (Z_to_bv 12 7)) /\
  qins segs pcs 2 (Op ALU_SLTU rU (Z_to_bv 5 0) rV) /\ qins segs pcs 3 (Op ALU_SLT rF rT rV) /\
  qins segs pcs 4 (OpImm ALU_XOR rF rF (Z_to_bv 12 1)) /\ qins segs pcs 5 (Op ALU_AND rF rU rF) /\
  qins segs pcs 6 (Branch BC_GEU rP rY (Z_to_bv 13 20)) /\ qins segs pcs 7 (Load SZ1 false rL rP (Z_to_bv 12 0)) /\
  qins segs pcs 8 (OpImm ALU_ADD rP rP (Z_to_bv 12 1)) /\ qins segs pcs 9 (Op ALU_OR rF rL rF) /\
  qins segs pcs 10 (Branch BC_NE rP rY (Z_to_bv 13 8180)) /\ qins segs pcs 11 (OpImm ALU_AND rP rF (Z_to_bv 12 255)) /\
  qins segs pcs 12 (Branch BC_EQ rP (Z_to_bv 5 0) bok) /\
  qfail2 pc0 bim beq = qpc pcs 0 /\ sok pcs bok = qok2 pc0 bim beq.

(* [comment removed for export] *)
Definition qss_havs (s : qssite) : list reg :=
  let q := qss_q s in [qs_rP q; qs_rA q; qs_rY q; qs_rZ q; qs_rW q; qss_rV s; qss_rT s; qss_rU s; qss_rF s; qss_rL s].

(* [comment removed for export] *)
Definition in_rg (fs : list fact) (a : lin) (R : region) : bool :=
  let '(dlo, dhi) := irange fs (lsub a (rg_base R)) in
  (Z.leb 0 dlo && Z.ltb dhi (fst (irange fs (rg_size R))) && Z.ltb dhi (2 ^ 40) && Z.ltb (snd (irange fs (rg_base R)) + 2 ^ 41) two64)%bool.
Definition end_ge (fs : list fact) (R : region) (e : lin) : bool :=
  let '(lo, hi) := irange fs (lsub (ladd (rg_base R) (rg_size R)) e) in
  (Z.leb 0 lo && Z.ltb hi (2 ^ 40) && Z.ltb (snd (irange fs e) + 2 ^ 41) two64 &&
   Z.ltb (snd (irange fs (rg_base R)) + snd (irange fs (rg_size R))) two64)%bool.
Fixpoint cov (fs : list fact) (rgs : list region) (fuel : nat) (a e : lin) : bool :=
  match fuel with
  | O => false
  | Datatypes.S f => existsb (fun R => if in_rg fs a R then (if end_ge fs R e then true else cov fs rgs f (ladd (rg_base R) (rg_size R)) e) else false) rgs
  end.

Lemma rg_rd : forall E mm R x, rg_ok ASEGSN E mm R -> uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R ->
  rd1 ASEGSN mm (Z_to_bv 64 x) <> None.
Proof.
  intros E mm R x (Hrs & Hrw & Hpts & _) Hx. specialize (Hpts (x - uE E (rg_base R)) ltac:(lia)).
  unfold uE in *. replace (bv_unsigned (lden E (rg_base R)) + (x - bv_unsigned (lden E (rg_base R)))) with x in Hpts by lia.
  destruct (rg_kind R).
  - exact (proj1 Hpts).
  - unfold rd1. rewrite (proj1 Hpts). exact (proj2 Hpts).
  - exact (proj1 (proj1 Hpts)).
  - exact (proj1 (proj1 Hpts)).
  - exact Hpts.
Qed.

Lemma in_rg_sound : forall E fs a R, Forall (fact_ok E) fs -> in_rg fs a R = true ->
  uE E (rg_base R) <= uE E a < uE E (rg_base R) + rsz E R.
Proof.
  intros E fs a R HF H. unfold in_rg in H. destruct (irange fs (lsub a (rg_base R))) as [dlo dhi] eqn:Hd.
  repeat match type of H with ((_ && _)%bool = true) => apply andb_prop in H as [H ?Hc] end.
  apply Z.leb_le in H. apply Z.ltb_lt in Hc, Hc0, Hc1.
  pose proof (irange_sound E fs (lsub a (rg_base R)) HF) as Rd. rewrite Hd in Rd. cbn [fst snd] in Rd. fold (uE E (lsub a (rg_base R))) in Rd.
  pose proof (irange_sound E fs (rg_size R) HF) as Rs. fold (uE E (rg_size R)) in Rs.
  pose proof (irange_sound E fs (rg_base R) HF) as Rb. fold (uE E (rg_base R)) in Rb.
  pose proof (uE_range E a). pose proof (uE_range E (rg_base R)).
  unfold rsz. fold (uE E (rg_size R)).
  destruct (small_diff E a (rg_base R) dlo dhi Rd) as [[Hl He]|[Hl He]]; unfold two64 in *; lia.
Qed.

Lemma end_ge_sound : forall E fs R e, Forall (fact_ok E) fs -> end_ge fs R e = true ->
  uE E e <= uE E (rg_base R) + rsz E R /\ uE E (ladd (rg_base R) (rg_size R)) = uE E (rg_base R) + rsz E R.
Proof.
  intros E fs R e HF H. unfold end_ge in H. destruct (irange fs (lsub (ladd (rg_base R) (rg_size R)) e)) as [lo hi] eqn:Hd.
  repeat match type of H with ((_ && _)%bool = true) => apply andb_prop in H as [H ?Hc] end.
  apply Z.leb_le in H. apply Z.ltb_lt in Hc, Hc0, Hc1.
  pose proof (irange_sound E fs (lsub (ladd (rg_base R) (rg_size R)) e) HF) as Rd. rewrite Hd in Rd. cbn [fst snd] in Rd.
  fold (uE E (lsub (ladd (rg_base R) (rg_size R)) e)) in Rd.
  pose proof (irange_sound E fs (rg_size R) HF) as Rs. fold (uE E (rg_size R)) in Rs.
  pose proof (irange_sound E fs (rg_base R) HF) as Rb. fold (uE E (rg_base R)) in Rb.
  pose proof (irange_sound E fs e HF) as Re. fold (uE E e) in Re.
  pose proof (uE_range E e). pose proof (uE_range E (rg_base R)). pose proof (uE_range E (rg_size R)).
  assert (Hend : uE E (ladd (rg_base R) (rg_size R)) = uE E (rg_base R) + rsz E R).
  { unfold uE, rsz. rewrite lden_ladd, bv_add_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
    apply Z.mod_small. unfold uE in *. lia. }
  split; [|exact Hend].
  assert (Hrz : rsz E R = uE E (rg_size R)) by reflexivity.
  destruct (small_diff E (ladd (rg_base R) (rg_size R)) e lo hi Rd) as [[Hl He]|[Hl He]]; rewrite Hend in Hl, He; [lia|].
  exfalso. rewrite Hrz in *. unfold two64 in *. lia.
Qed.

Lemma cov_sound : forall E fs rgs mm, Forall (fact_ok E) fs -> (forall R, In R rgs -> rg_ok ASEGSN E mm R) ->
  forall fuel a e, cov fs rgs fuel a e = true -> forall x, uE E a <= x < uE E e -> rd1 ASEGSN mm (Z_to_bv 64 x) <> None.
Proof.
  intros E fs rgs mm HF HG. induction fuel as [|f IH]; intros a e H x Hx; [discriminate|].
  cbn [cov] in H. apply existsb_exists in H as (R & HRin & HR).
  destruct (in_rg fs a R) eqn:Hin; [|discriminate].
  pose proof (in_rg_sound E fs a R HF Hin) as Ha. pose proof (HG R HRin) as HRok.
  destruct (Z_lt_dec x (uE E (rg_base R) + rsz E R)) as [Hlt|Hge].
  - apply (rg_rd E mm R x HRok). lia.
  - destruct (end_ge fs R e) eqn:Hend.
    + destruct (end_ge_sound E fs R e HF Hend) as [He _]. lia.
    + apply (IH _ _ HR x). split; [|lia].
      destruct HRok as (Hrs & Hrw & _). pose proof (uE_range E e).
      assert (Hend2 : uE E (ladd (rg_base R) (rg_size R)) = uE E (rg_base R) + rsz E R).
      { unfold uE, rsz. rewrite lden_ladd, bv_add_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
        apply Z.mod_small. unfold uE, rsz in *. pose proof (bv_unsigned_in_range _ (lden E (rg_base R))). lia. }
      rewrite Hend2. lia.
Qed.

(* [comment removed for export] *)
Definition in_rgL (fs : list fact) (a : lin) (R : region) : bool :=
  let '(dlo, dhi) := irange fs (lsub a (rg_base R)) in
  if Z.leb 0 dlo then (if Z.ltb dhi (2 ^ 40) then (if Z.ltb dhi (fst (irange fs (rg_size R))) then Z.ltb (snd (irange fs (rg_base R)) + 2 ^ 41) two64 else false) else false)
  else false.
Lemma in_rgL_eq : forall fs a R, in_rgL fs a R = in_rg fs a R.
Proof.
  intros fs a R. unfold in_rgL, in_rg. destruct (irange fs (lsub a (rg_base R))) as [dlo dhi].
  destruct (Z.leb 0 dlo); [|reflexivity]. cbn [andb].
  destruct (Z.ltb dhi (2 ^ 40)); [|rewrite andb_false_r; reflexivity].
  destruct (Z.ltb dhi (fst (irange fs (rg_size R)))); reflexivity.
Qed.
Definition end_geL (fs : list fact) (R : region) (e : lin) : bool :=
  let '(lo, hi) := irange fs (lsub (ladd (rg_base R) (rg_size R)) e) in
  if Z.leb 0 lo then (if Z.ltb hi (2 ^ 40) then (if Z.ltb (snd (irange fs e) + 2 ^ 41) two64
                                                  then Z.ltb (snd (irange fs (rg_base R)) + snd (irange fs (rg_size R))) two64 else false) else false)
  else false.
Lemma end_geL_eq : forall fs R e, end_geL fs R e = end_ge fs R e.
Proof.
  intros fs R e. unfold end_geL, end_ge. destruct (irange fs (lsub (ladd (rg_base R) (rg_size R)) e)) as [lo hi].
  destruct (Z.leb 0 lo); [|reflexivity]. cbn [andb]. destruct (Z.ltb hi (2 ^ 40)); [|reflexivity]. cbn [andb].
  destruct (Z.ltb (snd (irange fs e) + 2 ^ 41) two64); reflexivity.
Qed.
Fixpoint covL (fs : list fact) (rgs : list region) (fuel : nat) (a e : lin) : bool :=
  match fuel with
  | O => false
  | Datatypes.S f => existsb_cf (fun R => cand_t a (rg_base R))
                       (fun R => if in_rgL fs a R then (if end_geL fs R e then true else covL fs rgs f (ladd (rg_base R) (rg_size R)) e) else false) rgs
  end.
Lemma existsb_ext_q : forall {A : Type} (f g : A -> bool) (l : list A), (forall x, f x = g x) -> List.existsb f l = List.existsb g l.
Proof. intros A f g l H. induction l as [|x r IH]; [reflexivity|]. cbn [List.existsb]. rewrite H, IH. reflexivity. Qed.
Lemma covL_eq : forall fs rgs fuel a e, covL fs rgs fuel a e = cov fs rgs fuel a e.
Proof.
  intros fs rgs. induction fuel as [|f IH]; intros a e; [reflexivity|]. cbn [covL cov]. rewrite existsb_cf_eq.
  apply existsb_ext_q. intros R. rewrite in_rgL_eq, end_geL_eq, IH. reflexivity.
Qed.

(* [comment removed for export] *)
Definition qcs_win (fs : list fact) (b : lin) (nhi : Z) : option (lin * lin) :=
  match srl_lin fs 3 b with
  | Some q => let s1 := laddc q SH_OFF in
              let dmax := (match lowb fs b 3 with Some rb => rb | None => 7 end + nhi - 1) / 8 in
              match lowb fs s1 3 with
              | Some r => Some (laddc s1 (- r), laddc s1 (- r + 8 * ((r + dmax) / 8) + 8))
              | None => Some (laddc s1 (-7), laddc s1 (dmax + 8))
              end
  | None => None
  end.
Definition QCS_FUEL : nat := 8.
Definition words_rd (fs : list fact) (rgs : list region) (b : lin) (nhi : Z) : bool :=
  match qcs_win fs b nhi with Some (a, e) => covL fs rgs QCS_FUEL a e | None => false end.

Lemma uE_laddc_gen : forall E l c, 0 <= uE E l + c < two64 -> uE E (laddc l c) = uE E l + c.
Proof. intros E l c H. unfold uE. rewrite lden_laddc. apply u_small. unfold uE in H. exact H. Qed.

Lemma qcs_win_sound : forall E fs b nhi a e n, Forall (fact_ok E) fs -> qcs_win fs b nhi = Some (a, e) ->
  1 <= n <= nhi -> nhi <= 64 -> uE E b + n <= 0x800000000000 ->
  uE E a <= 8 * ((SH_OFF + uE E b / 8) / 8) /\ 8 * ((SH_OFF + (uE E b + n - 1) / 8) / 8) + 8 <= uE E e.
Proof.
  intros E fs b nhi a e n HF H Hn Hnhi Hbn. unfold qcs_win in H.
  destruct (srl_lin fs 3 b) as [q|] eqn:Hq; [|discriminate].
  pose proof (srl_lin_sound E fs 3 b q HF ltac:(lia) Hq) as Hqv. rewrite Z.shiftr_div_pow2 in Hqv by lia. change (2 ^ 3) with 8 in Hqv.
  fold (uE E q) (uE E b) in Hqv. pose proof (uE_range E b) as RB. set (B := uE E b) in *.
  assert (HB8 : 0 <= B / 8 <= B) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  set (s1 := laddc q SH_OFF) in *.
  assert (Hs1 : uE E s1 = SH_OFF + B / 8) by (unfold s1; rewrite uE_laddc_gen; [lia | rewrite Hqv; unfold SH_OFF, two64 in *; lia]).
  set (rb := match lowb fs b 3 with Some rb => rb | None => 7 end) in *.
  pose proof (Z.mod_pos_bound B 8 ltac:(lia)) as Hmb.
  assert (Hrb : B mod 8 <= rb <= 7).
  { unfold rb. destruct (lowb fs b 3) as [r0|] eqn:Hlb0; [|lia].
    pose proof (lowb_sound E fs b 3 r0 HF Hlb0) as Hr0. fold (uE E b) B in Hr0. change (2 ^ 3) with 8 in Hr0. lia. }
  set (dmax := (rb + nhi - 1) / 8) in *.
  assert (Hd0 : 0 <= dmax <= 8).
  { unfold dmax. split; [apply Z.div_pos; lia|]. assert (X : (rb + nhi - 1) / 8 <= 70 / 8) by (apply Z.div_le_mono; lia). exact X. }
  assert (Hlast : B / 8 <= (B + n - 1) / 8 <= B / 8 + dmax).
  { split; [apply Z.div_le_mono; lia|]. unfold dmax.
    pose proof (Z.div_mod B 8 ltac:(lia)) as Hdm.
    replace (B + n - 1) with ((B mod 8 + n - 1) + (B / 8) * 8) by lia. rewrite Z.div_add by lia.
    assert ((B mod 8 + n - 1) / 8 <= (rb + nhi - 1) / 8) by (apply Z.div_le_mono; lia). lia. }
  set (S1 := SH_OFF + B / 8) in *. set (S2 := SH_OFF + (B + n - 1) / 8).
  assert (HS12 : S1 <= S2 <= S1 + dmax) by (unfold S1, S2; lia).
  assert (HS1 : 0 <= S1 < 2 ^ 48) by (unfold S1, SH_OFF; lia).
  pose proof (Z.mul_div_le S1 8 ltac:(lia)) as L1. pose proof (Z.mod_pos_bound S1 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod S1 8 ltac:(lia)) as DM1.
  pose proof (Z.mul_div_le S2 8 ltac:(lia)) as L2.
  destruct (lowb fs s1 3) as [r|] eqn:Hlb.
  - pose proof (lowb_sound E fs s1 3 r HF Hlb) as Hr. fold (uE E s1) in Hr. rewrite Hs1 in Hr. change (2 ^ 3) with 8 in Hr. fold S1 in Hr.
    injection H as <- <-.
    assert (Hr8 : 0 <= r < 8) by lia.
    assert (Hdr : 0 <= (r + dmax) / 8 <= 2) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    rewrite !uE_laddc_gen by (rewrite Hs1; fold S1; unfold two64; lia). rewrite Hs1. fold S1.
    split; [lia|].
    assert (S2 / 8 <= (S1 + dmax) / 8) by (apply Z.div_le_mono; lia).
    assert (E8 : (S1 + dmax) / 8 = S1 / 8 + (r + dmax) / 8).
    { replace (S1 + dmax) with ((r + dmax) + (S1 / 8) * 8) by lia. rewrite Z.div_add by lia. lia. }
    lia.
  - injection H as <- <-.
    rewrite !uE_laddc_gen by (rewrite Hs1; fold S1; unfold two64, SH_OFF in *; lia). rewrite Hs1. fold S1.
    split; [lia|]. lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_of_rd1 : forall m k (a : word), bv_unsigned a + Z.of_nat k < two64 ->
  (forall i, 0 <= i < Z.of_nat k -> rd1 ASEGSN m (Z_to_bv 64 (bv_unsigned a + i)) <> None) ->
  exists bs, rdn ASEGSN m a k = Some bs /\ length bs = k.
Proof.
  intros m. induction k as [|k IH]; intros a Ha Hall; [exists []; split; reflexivity|].
  cbn [rdn].
  assert (H0 : rd1 ASEGSN m a <> None) by (specialize (Hall 0 ltac:(lia)); rewrite Z.add_0_r, Z_to_bv_bv_unsigned in Hall; exact Hall).
  unfold rd1 in H0. destruct (match m a with Some b => Some b | None => seg_rom ASEGSN a end) as [b0|] eqn:Hb; [|contradiction].
  assert (Ha1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1).
  { rewrite bv_add_unsigned. change (bv_unsigned (1 : word)) with 1. unfold bv_wrap. change (bv_modulus 64) with two64.
    apply Z.mod_small. pose proof (bv_unsigned_in_range _ a). lia. }
  destruct (IH (a + 1)%bv) as (bs & Hbs & Hl).
  - rewrite Ha1. lia.
  - intros i Hi. rewrite Ha1. replace (bv_unsigned a + 1 + i) with (bv_unsigned a + (i + 1)) by lia. apply Hall. lia.
  - exists (b0 :: bs). rewrite Hbs. split; [reflexivity | cbn [length]; rewrite Hl; reflexivity].
Qed.

(* [comment removed for export] *)
Definition qcs_chk (img : tree Z) (s : qssite) (S : sst) (M : smodel) : bool :=
  let q := qss_q s in
  let fs := s_facts S in let rgs := s_rgs S in
  let b := rget (s_regs S) (rkey (qs_rB q)) in
  let ra := rget (s_regs S) (rkey (qs_rA q)) in
  let nl := lsub ra b in
  match s_resv S, is_const (rget (s_regs S) (rkey (qs_rP q))) with
  | RNone, Some P =>
      let '(nlo, nhi) := irange fs nl in
      if (Z.eqb (s_pc S) (qs_pc0 q) && Z.leb 1 nlo && Z.leb nhi 64 &&
          match load_at img fs rgs (lconst P) SZ8 false with Some (Some sl) => lin_eqb sl (lconst SH_OFF) | _ => false end &&
          Z.leb (snd (irange fs ra)) 0x7fffffffff00 && Z.leb (snd (irange fs b)) 0x7fffffffff00 &&
          words_rd fs rgs b nhi)%bool
      then (if rp_zp fs rgs b nl then true else if rp_zbx fs rgs b nl then true else rp_za S M b nl)
      else false
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition qcs_chk0 (img : tree Z) (s : qssite) (S : sst) (M : smodel) : bool :=
  let q := qss_q s in
  let fs := s_facts S in let rgs := s_rgs S in
  let b := rget (s_regs S) (rkey (qs_rB q)) in
  let ra := rget (s_regs S) (rkey (qs_rA q)) in
  let nl := lsub ra b in
  match s_resv S, is_const (rget (s_regs S) (rkey (qs_rP q))) with
  | RNone, Some P =>
      let '(nlo, nhi) := irange fs nl in
      if (Z.eqb (s_pc S) (qs_pc0 q) && Z.leb 1 nlo && Z.leb nhi 64 &&
          match load_at img fs rgs (lconst P) SZ8 false with Some (Some sl) => lin_eqb sl (lconst SH_OFF) | _ => false end &&
          Z.leb (snd (irange fs ra)) 0x7fffffffff00 && Z.leb (snd (irange fs b)) 0x7fffffffff00)%bool
      then (if rp_zp fs rgs b nl then true else if rp_zbx fs rgs b nl then true else rp_za S M b nl)
      else false
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition qcs_words (B n x : Z) : Prop :=
  8 * ((SH_OFF + B / 8) / 8) <= x < 8 * ((SH_OFF + B / 8) / 8) + 8 \/
  8 * ((SH_OFF + (B + n - 1) / 8) / 8) <= x < 8 * ((SH_OFF + (B + n - 1) / 8) / 8) + 8.
Definition qcs_post (s : qssite) (S : sst) : sst := run_post S (qs_ok (qss_q s)) [] (qss_havs s).

Section NodeS.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Variable img : tree Z.
Hypothesis Hwx : wx_segs_nowrap ASEGSN.
Hypothesis Himg : img_ok ASEGSN img.

#[using="Hwx Himg"] Theorem den_qcs_core : forall s S M E ms model T,
  qssite_ok ASEGSN s -> qcs_chk0 img s S M = true -> DEN ASEGSN LIMIT model0 mem0 E S M ms model ->
  (forall x, qcs_words (uE E (rget (s_regs S) (rkey (qs_rB (qss_q s)))))
                       (uE E (lsub (rget (s_regs S) (rkey (qs_rA (qss_q s)))) (rget (s_regs S) (rkey (qs_rB (qss_q s)))))) x ->
             rd1 ASEGSN (mrestrict (Hof E M model) (ms_mem ms)) (Z_to_bv 64 x) <> None) ->
  (forall E' ms' model', agree (s_next S) E E' -> DEN ASEGSN LIMIT model0 mem0 E' (qcs_post s S) M ms' model' ->
      realizes_cfg ASEGSN cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGSN cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Himg : LiaFast.U) => LiaFast.u0).
  intros s S M E ms model T Hs Hck Hd Hrdw Hk.
  destruct s as [q pcs rV rT rU rF rL bok]. destruct q as [pc0 rP rA rB rY rZ rW ord bim beq].
  cbn [qssite_ok] in Hs. destruct Hs as (Hq & Hs).
  pose proof Hq as Hq0. cbn [qsite_ok] in Hq0.
  destruct Hq0 as (Hnz & Hd1 & Hd2 & I0 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11).
  destruct Hs as (Hsnz & HdV & HdT & HdU & HdF & HdL & HdPY & J0 & J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11 & J12 & Hlk1 & Hlk2).
  unfold qcs_chk0 in Hck. cbn [qss_q qs_rB qs_rA qs_rP qs_pc0] in Hck, Hrdw.
  set (fs := s_facts S) in *. set (b := rget (s_regs S) (rkey rB)) in *. set (ra := rget (s_regs S) (rkey rA)) in *.
  set (nl := lsub ra b) in *.
  destruct (s_resv S) eqn:Hrv; try discriminate.
  destruct (is_const (rget (s_regs S) (rkey rP))) as [P|] eqn:HP; [|discriminate].
  destruct (irange fs nl) as [nlo nhi] eqn:Hnr.
  match type of Hck with ((if ?c then ?x else false) = true) =>
    assert (Hck2 : (c && x)%bool = true) by (destruct c; [exact Hck | discriminate Hck]) end.
  clear Hck. apply andb_prop in Hck2 as [Hck Hzz].
  destruct (load_at img fs (s_rgs S) (lconst P) SZ8 false) as [[sl|]|] eqn:HlP;
    [|rewrite ?andb_false_r, ?andb_false_l in Hck; discriminate | rewrite ?andb_false_r, ?andb_false_l in Hck; discriminate].
  repeat match type of Hck with ((_ && _)%bool = true) => apply andb_prop in Hck as [Hck ?Hc] end.
  rename Hck into Hpc0.
  repeat match goal with
         | Hx : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in Hx
         | Hx : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx
         | Hx : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in Hx
         end.
  subst sl.
  (* [comment removed for export] *)
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hrsv. cbn [rsv_ok] in Hrsv.
  cbn [restrict ms_pc_val ms_svc_pending ms_resv ms_regs] in Hpc, Hsvc, Hrsv, HR.
  set (mm := mrestrict H (ms_mem ms)) in *.
  set (bw := lden E b).
  assert (HB : getr (ms_regs ms) rB = bw) by exact (HR rB).
  set (n := uE E nl).
  assert (HnE : lden E (lsub ra b) = Z_to_bv 64 n) by (unfold n, uE; symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (irange_sound E fs nl HF) as Rn. rewrite Hnr in Rn. cbn [fst snd] in Rn. fold (uE E nl) n in Rn.
  assert (Hn1 : 1 <= n <= 64) by lia.
  assert (HA : getr (ms_regs ms) rA = v_add bw (Z_to_bv 64 n)) by (rewrite (HR rA); exact (lsub_const_add E _ b n HnE)).
  assert (HPr : getr (ms_regs ms) rP = Z_to_bv 64 P) by (rewrite (HR rP); exact (proj1 (is_const_sound E _ P HP))).
  pose proof (bv_unsigned_in_range _ bw) as Rbw. unfold bv_modulus in Rbw. change (2 ^ Z.of_N 64) with two64 in Rbw.
  assert (Hbw0 : 0 <= bv_unsigned bw) by lia.
  assert (Hb2 : bv_unsigned bw + n <= 0x7fffffffff00).
  { pose proof (irange_sound E fs ra HF) as RA. pose proof (irange_sound E fs b HF) as RBb. fold bw in RBb.
    assert (HvA : bv_unsigned (lden E ra) = bv_unsigned bw + n).
    { unfold ra. rewrite <- (HR rA), HA. unfold v_add. rewrite (u_small n) by (unfold two64; lia). apply u_small. unfold two64 in *. lia. }
    rewrite HvA in RA. lia. }
  assert (Hb3 : bv_unsigned bw + n <= 0x800000000000) by lia.
  (* [comment removed for export] *)
  destruct (load_at_sound ASEGSN E img fs (s_rgs S) _ SZ8 false _ (ms_mem (restrict H ms)) Himg HG HF HlP) as (bsP & HrP & HvP).
  specialize (HvP _ eq_refl). rewrite ov_rdn in HrP. cbn [nbytes] in HrP.
  assert (HlbP : length bsP = 8%nat) by exact (rdn_length _ _ _ _ _ HrP).
  set (Pw := Z_to_bv 64 P).
  set (sh := Z_to_bv 64 SH_OFF).
  assert (HPv : bytes_le_to_Z bsP = bv_unsigned sh) by (apply ld8_val; [exact HlbP | rewrite <- HvP, lden_lconst; reflexivity]).
  rewrite lden_lconst in HrP. fold Pw in HrP.
  cbn [restrict ms_mem] in HrP. fold mm in HrP.
  (* [comment removed for export] *)
  assert (Hcov : forall x, qcs_words (bv_unsigned bw) n x -> rd1 ASEGSN mm (Z_to_bv 64 x) <> None) by (intros x Hx; exact (Hrdw x Hx)).
  pose proof (hull_bounds (bv_unsigned bw) n Hbw0 Hn1 Hb3) as [Hh1a Hh1b].
  pose proof (hull_bounds2 (bv_unsigned bw) n Hbw0 Hn1 Hb3) as [Hh2a Hh2b].
  assert (Hw12 : 8 * ((SH_OFF + bv_unsigned bw / 8) / 8) <= 8 * ((SH_OFF + (bv_unsigned bw + n - 1) / 8) / 8)).
  { assert (bv_unsigned bw / 8 <= (bv_unsigned bw + n - 1) / 8) by (apply Z.div_le_mono; lia).
    assert ((SH_OFF + bv_unsigned bw / 8) / 8 <= (SH_OFF + (bv_unsigned bw + n - 1) / 8) / 8) by (apply Z.div_le_mono; lia). lia. }
  assert (HW1 : exists bs1, rdn ASEGSN mm (qw1 sh bw) 8 = Some bs1 /\ length bs1 = 8%nat).
  { apply rdn_of_rd1; [unfold sh; rewrite (qrw1_u bw Hbw0 ltac:(lia)); cbn [Z.of_nat Pos.of_succ_nat]; lia|].
    intros i Hi. cbn [Z.of_nat Pos.of_succ_nat] in Hi. unfold sh. rewrite (qrw1_u bw Hbw0 ltac:(lia)). apply Hcov. left. lia. }
  assert (HW2 : exists bs2, rdn ASEGSN mm (qw2 sh bw n) 8 = Some bs2 /\ length bs2 = 8%nat).
  { apply rdn_of_rd1; [unfold sh; rewrite (qrw2_u' bw n Hbw0 Hn1 Hb3); cbn [Z.of_nat Pos.of_succ_nat]; lia|].
    intros i Hi. cbn [Z.of_nat Pos.of_succ_nat] in Hi. unfold sh. rewrite (qrw2_u' bw n Hbw0 Hn1 Hb3). apply Hcov. right. lia. }
  destruct HW1 as (bs1 & HW1 & Hl1). destruct HW2 as (bs2 & HW2 & Hl2).
  pose proof (bytes_le_to_Z_range bs1 Hl1) as Rv1. pose proof (bytes_le_to_Z_range bs2 Hl2) as Rv2.
  set (v1 := Z_to_bv 64 (bytes_le_to_Z bs1)). set (v2 := Z_to_bv 64 (bytes_le_to_Z bs2)).
  assert (HV1 : bytes_le_to_Z bs1 = bv_unsigned v1) by (unfold v1; rewrite u_small by (unfold two64; lia); reflexivity).
  assert (HV2 : bytes_le_to_Z bs2 = bv_unsigned v2) by (unfold v2; rewrite u_small by (unfold two64; lia); reflexivity).
  (* [comment removed for export] *)
  assert (Hend0 : uE E b + uE E nl + 8 <= kHighEnd) by (change (uE E b) with (bv_unsigned bw); fold n; unfold kHighEnd; lia).
  destruct (rp_shadow_spec LIMIT model0 mem0 S M E ms model b nl Hd Hzz ltac:(change (1 <= fst (irange fs nl)); rewrite Hnr; cbn [fst]; lia) Hend0)
    as (b1 & Hlb1 & Hb1c & Hzero).
  change (uE E b) with (bv_unsigned bw) in Hlb1, Hb1c, Hzero. fold n H mm in Hlb1, Hb1c, Hzero.
  rewrite SB_val in Hlb1, Hzero. change 2147450880 with SH_OFF in Hlb1, Hzero.
  (* [comment removed for export] *)
  destruct (@qc2g_isteps (mkFP (ms_fregs ms) (ms_fcsr ms)) ASEGSN pc0 rP rA rB rY rZ rW ord Hnz Hd1 Hd2
              I0 I1 I2 I3 I4 I5 I6 I7 I8 I9 I10
              (ms_regs ms) mm (ms_rom ms) bw n Pw sh v1 v2 bsP bs1 bs2 HB HPr HA HrP HPv HW1 HV1 HW2 HV2)
    as (regs1 & Hst1 & R1p & R1y & R1a & R1z & R1w & R1o).
  pose proof (@qc2g_branch (mkFP (ms_fregs ms) (ms_fcsr ms)) ASEGSN pc0 rZ bim beq I11 regs1 mm (ms_rom ms) (v_or v2 v1) R1z) as Hbr.
  assert (Hrun : exists regs', FxStep.isteps ASEGSN (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (qpc pc0 0) mm (ms_rom ms))
                                 (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs' (qok2 pc0 bim beq) mm (ms_rom ms)) /\
            (forall r, r <> rP -> r <> rA -> r <> rY -> r <> rZ -> r <> rW -> r <> rV -> r <> rT -> r <> rU -> r <> rF -> r <> rL ->
               getr regs' r = getr (ms_regs ms) r)).
  { destruct (Z.eqb (bv_unsigned (v_or v2 v1)) 0) eqn:Hor.
    - exists regs1. split; [exact (FxStep.isteps_trans _ _ _ _ Hst1 Hbr)|].
      intros r H1 H2 H3 H4 H5 _ _ _ _ _. exact (R1o r H1 H2 H3 H4 H5).
    - rewrite Hlk1 in Hbr.
      set (X := SH_OFF + bv_unsigned bw / 8). set (Y := SH_OFF + (bv_unsigned bw + n - 1) / 8).
      assert (HXY : 0 <= X <= Y) by (unfold X, Y; assert (bv_unsigned bw / 8 <= (bv_unsigned bw + n - 1) / 8) by (apply Z.div_le_mono; lia);
                                     pose proof (Z.div_pos (bv_unsigned bw) 8 ltac:(lia) ltac:(lia)); unfold SH_OFF; lia).
      assert (HY : Y < two64).
      { unfold Y. assert ((bv_unsigned bw + n - 1) / 8 <= bv_unsigned bw + n - 1) by (apply Z.div_le_upper_bound; lia). unfold SH_OFF, two64. lia. }
      assert (G1P : getr regs1 rP = Z_to_bv 64 X) by (rewrite R1p; unfold X; rewrite <- (qrX_u bw n Hbw0 Hn1 Hb3); symmetry; apply Z_to_bv_bv_unsigned).
      assert (G1Y : getr regs1 rY = Z_to_bv 64 Y) by (rewrite R1y; unfold Y; rewrite <- (qrY_u bw n Hbw0 Hn1 Hb3); symmetry; apply Z_to_bv_bv_unsigned).
      assert (HzX : forall x, X <= x < Y -> rdn ASEGSN mm (Z_to_bv 64 x) 1 = Some [Z_to_bv 8 0]).
      { intros x Hx. cbn [rdn]. replace x with (SH_OFF + (x - SH_OFF)) by lia.
        rewrite (Hzero (x - SH_OFF) ltac:(unfold X, Y in Hx; lia)). reflexivity. }
      assert (HlY : rdn ASEGSN mm (Z_to_bv 64 Y) 1 = Some [b1]) by (cbn [rdn]; unfold Y; rewrite Hlb1; reflexivity).
      assert (HbA : bv_unsigned b1 = 0 \/ bv_unsigned (qlast bw n) mod 8 < bv_unsigned b1 <= 7) by (rewrite (qrlast_u bw n Hbw0 Hn1 Hb3); exact Hb1c).
      destruct (@qslow_isteps (mkFP (ms_fregs ms) (ms_fcsr ms)) ASEGSN pcs rP rY rA rV rT rU rF rL bok Hsnz HdV HdT HdU HdF HdL HdPY
                  J0 J1 J2 J3 J4 J5 J6 J7 J8 J9 J10 J11 J12 regs1 mm (ms_rom ms) X Y (qlast bw n) b1 G1P G1Y R1a HXY HY HzX HlY HbA)
        as (regs2 & Hst2 & R2o).
      rewrite Hlk2 in Hst2.
      exists regs2. split; [exact (FxStep.isteps_trans _ _ _ _ Hst1 (FxStep.isteps_trans _ _ _ _ Hbr Hst2))|].
      intros r H1 H2 H3 H4 H5 H6 H7 H8 H9 H10. rewrite (R2o r H1 H6 H7 H8 H9 H10). exact (R1o r H1 H2 H3 H4 H5). }
  destruct Hrun as (regs' & Hst & Ro).
  assert (Hmsr : restrict H ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (qpc pc0 0) mm (ms_rom ms)).
  { destruct ms as [rg fr pcv sv rv fc mem rom]. cbn [ms_pc_val ms_svc_pending ms_resv] in Hsvc, Hrsv, Hpc. subst sv rv.
    cbn [ms_pc_val] in Hpc. rewrite Hpc0 in Hpc. subst pcv.
    unfold restrict, mkst, qpc, mm. cbn [ms_regs ms_fregs ms_fcsr ms_mem ms_rom fp_regs fp_csr ms_pc_val ms_svc_pending ms_resv].
    replace (pc0 + 4 * 0) with pc0 by lia. reflexivity. }
  set (qq := QS pc0 rP rA rB rY rZ rW ord bim beq).
  assert (Hqk : Z_to_bv 64 (qs_ok qq) = qok2 pc0 bim beq) by (unfold qs_ok; cbn [qs_pc0 qs_bim qs_beq]; apply Z_to_bv_bv_unsigned).
  apply (den_run_post ASEGSN cfg LIMIT model0 mem0 Hwx E S M ms model T regs' (qs_ok qq) [] (qss_havs (QSS qq pcs rV rT rU rF rL bok)) Hd Hrv).
  - fold H. rewrite Hmsr, Hqk. fold mm. exact Hst.
  - apply Forall_nil.
  - destruct Hnz as (NP & NA & NY & NZ & NW). destruct Hsnz as (_ & NV & NT & NU & NF & NL).
    unfold qss_havs. cbn [qss_q qs_rP qs_rA qs_rY qs_rZ qs_rW qss_rV qss_rT qss_rU qss_rF qss_rL].
    repeat (apply Forall_cons; [assumption|]). apply Forall_nil.
  - intros r _ Hhv. unfold qss_havs in Hhv. cbn [qss_q qs_rP qs_rA qs_rY qs_rZ qs_rW qss_rV qss_rT qss_rU qss_rF qss_rL existsb] in Hhv.
    repeat match type of Hhv with ((_ || _)%bool = false) => apply orb_false_elim in Hhv as [?Hn Hhv] end.
    assert (Hne : forall h : reg, bv_eqb h r = false -> r <> h) by (intros h Hb Hcx; subst h; rewrite bv_eqb_refl in Hb; discriminate).
    apply Ro; apply Hne; assumption.
  - exact Hk.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma qcs_chk_parts : forall s S M, qcs_chk img s S M = true ->
  qcs_chk0 img s S M = true /\
  words_rd (s_facts S) (s_rgs S) (rget (s_regs S) (rkey (qs_rB (qss_q s))))
           (snd (irange (s_facts S) (lsub (rget (s_regs S) (rkey (qs_rA (qss_q s)))) (rget (s_regs S) (rkey (qs_rB (qss_q s))))))) = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros s S M H. unfold qcs_chk in H. unfold qcs_chk0. cbv zeta in *.
  destruct (s_resv S); try discriminate. destruct (is_const (rget (s_regs S) (rkey (qs_rP (qss_q s))))) as [P|]; [|discriminate].
  destruct (irange (s_facts S) (lsub (rget (s_regs S) (rkey (qs_rA (qss_q s)))) (rget (s_regs S) (rkey (qs_rB (qss_q s)))))) as [nlo nhi] eqn:Hir.
  cbn [snd].
  match type of H with ((if (?c && ?w)%bool then ?x else false) = true) =>
    destruct c eqn:Hcc; [|discriminate H]; destruct w eqn:Hww; [|discriminate H]; cbn [andb] in H end.
  split; [exact H | reflexivity].
Qed.
#[using="Hwx Himg"] Theorem den_qcs : forall s S M E ms model T,
  qssite_ok ASEGSN s -> qcs_chk img s S M = true -> DEN ASEGSN LIMIT model0 mem0 E S M ms model ->
  (forall E' ms' model', agree (s_next S) E E' -> DEN ASEGSN LIMIT model0 mem0 E' (qcs_post s S) M ms' model' ->
      realizes_cfg ASEGSN cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGSN cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Himg : LiaFast.U) => LiaFast.u0).
  intros s S M E ms model T Hs Hck Hd Hk. destruct (qcs_chk_parts s S M Hck) as [Hck0 Hwr].
  apply (den_qcs_core s S M E ms model T Hs Hck0 Hd); [|exact Hk].
  set (b := rget (s_regs S) (rkey (qs_rB (qss_q s)))) in *. set (nl := lsub (rget (s_regs S) (rkey (qs_rA (qss_q s)))) b) in *.
  set (fs := s_facts S) in *.
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & HG & _ & HF & _).
  cbn [restrict ms_mem] in HG. set (mm := mrestrict (Hof E M model) (ms_mem ms)) in *.
  assert (HGf : forall R, In R (s_rgs S) -> rg_ok ASEGSN E mm R) by (rewrite Forall_forall in HG; exact HG).
  (* [comment removed for export] *)
  unfold qcs_chk0 in Hck0. cbv zeta in Hck0. fold b nl fs in Hck0.
  destruct (s_resv S); try discriminate. destruct (is_const (rget (s_regs S) (rkey (qs_rP (qss_q s))))) as [P|]; [|discriminate].
  destruct (irange fs nl) as [nlo nhi] eqn:Hnr. cbn [snd] in Hwr.
  match type of Hck0 with ((if ?c then ?x else false) = true) => destruct c eqn:Hc; [|discriminate Hck0] end.
  repeat match type of Hc with ((_ && _)%bool = true) => apply andb_prop in Hc as [Hc ?Hx] end.
  repeat match goal with Hx : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx end.
  pose proof (irange_sound E fs nl HF) as Rn. rewrite Hnr in Rn. cbn [fst snd] in Rn. fold (uE E nl) in Rn.
  pose proof (irange_sound E fs (rget (s_regs S) (rkey (qs_rA (qss_q s)))) HF) as RA.
  pose proof (irange_sound E fs b HF) as RB. fold (uE E b) in RB.
  assert (Hn1 : 1 <= uE E nl <= 64) by lia.
  pose proof (uE_range E b) as Rb0.
  assert (Hb3 : uE E b + uE E nl <= 0x800000000000).
  { (* [comment removed for export] *)
    pose proof (uE_range E nl) as Rnl.
    assert (Hra : bv_unsigned (lden E (rget (s_regs S) (rkey (qs_rA (qss_q s))))) = (uE E b + uE E nl) mod two64).
    { assert (Hl : lden E (rget (s_regs S) (rkey (qs_rA (qss_q s)))) = bv_add (lden E b) (lden E nl)).
      { unfold nl. rewrite lden_lsub. apply bv_eq. rewrite bv_add_unsigned, bv_sub_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
        rewrite Zplus_mod_idemp_r. replace (bv_unsigned (lden E b) + (bv_unsigned (lden E (rget (s_regs S) (rkey (qs_rA (qss_q s))))) - bv_unsigned (lden E b)))
          with (bv_unsigned (lden E (rget (s_regs S) (rkey (qs_rA (qss_q s)))))) by lia.
        symmetry. apply Z.mod_small. pose proof (bv_unsigned_in_range _ (lden E (rget (s_regs S) (rkey (qs_rA (qss_q s)))))) as X. unfold bv_modulus in X. exact X. }
      rewrite Hl, bv_add_unsigned. unfold bv_wrap, bv_modulus. reflexivity. }
    rewrite Z.mod_small in Hra by (unfold two64 in *; lia). lia. }
  unfold words_rd in Hwr. destruct (qcs_win fs b nhi) as [[wa we]|] eqn:Hwin; [|discriminate].
  destruct (qcs_win_sound E fs b nhi wa we (uE E nl) HF Hwin ltac:(lia) ltac:(lia) Hb3) as [Hwlo Hwhi].
  rewrite covL_eq in Hwr.
  pose proof (cov_sound E fs (s_rgs S) mm HF HGf QCS_FUEL wa we Hwr) as Hcov.
  pose proof (hull_bounds (uE E b) (uE E nl) ltac:(lia) Hn1 Hb3) as [Hh1a Hh1b].
  pose proof (hull_bounds2 (uE E b) (uE E nl) ltac:(lia) Hn1 Hb3) as [Hh2a Hh2b].
  assert (Hw12 : 8 * ((SH_OFF + uE E b / 8) / 8) <= 8 * ((SH_OFF + (uE E b + uE E nl - 1) / 8) / 8)).
  { assert (uE E b / 8 <= (uE E b + uE E nl - 1) / 8) by (apply Z.div_le_mono; lia).
    assert ((SH_OFF + uE E b / 8) / 8 <= (SH_OFF + (uE E b + uE E nl - 1) / 8) / 8) by (apply Z.div_le_mono; lia). lia. }
  intros x Hqw. apply Hcov. unfold qcs_words in Hqw. lia.
Qed.
End NodeS.
