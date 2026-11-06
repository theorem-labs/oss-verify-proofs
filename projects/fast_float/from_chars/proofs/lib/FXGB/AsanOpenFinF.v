(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxPlan FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxWvC FxChMain FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTbl AsanTblM AsanTblMd AsanEntry AsanPlan AsanStart AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF AsanMainWF.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainWF.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcFam AcSubst AcMALlib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanPNodes.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition KOPEN : MCF := TOPK (MSegK 20 P_OPEN (KCons 0xd51d0 56 MEnd (KCons 0x8fc54 0 MVoid KNil))).
Definition open_fins (lo hi : Z) : option (list (sst * smodel * fstate * shp * ast)) :=
  mcheck ASEGS LIM TBLMd IMGMd PV lo hi false (Some H0) apostF anil aeqb awf acopy_alloc asubst ag_ok alins_a aset_a amod_a [] [] KOPEN (S1c lo hi) M1c FSClosed SHWF A1c.
(* [comment removed for export] *)
Definition open_state_of (r : option (list (sst * smodel * fstate * shp * ast))) : option (sst * smodel) :=
  match r with
  | Some l => match List.find (fun '(St, _, _, _, _) => Z.eqb (s_pc St) 0xd51d0) l with Some (St, Mx, _, _, _) => Some (St, Mx) | None => None end
  | None => None
  end.
Definition open_state (lo hi : Z) : option (sst * smodel) := open_state_of (open_fins lo hi).
(* [comment removed for export] *)
Definition OPEN_W : option (sst * smodel) := open_state 6 65535.
Definition st_of (r : option (sst * smodel)) : sst := match r with Some (St, _) => St | None => S1WF end.
Definition md_ok (r : option (sst * smodel)) : bool := match r with Some (_, Mx) => sm_eqb Mx M1c | None => false end.
Definition S_OPEN_W : sst := Eval vm_compute in st_of OPEN_W.
Definition FACT16W : fact := FRange (hvar 16) 6 65535.
Definition S_OPEN_T : sst :=
  SST (s_pc S_OPEN_W) (s_regs S_OPEN_W) (s_rgs S_OPEN_W) (List.filter (fun f => negb (fact_eqb f FACT16W)) (s_facts S_OPEN_W))
      (s_next S_OPEN_W) (s_resv S_OPEN_W).
(* [comment removed for export] *)
(* [comment removed for export] *)
