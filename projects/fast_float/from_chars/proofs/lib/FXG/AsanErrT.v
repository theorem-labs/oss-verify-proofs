(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxPlan FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChEnt FxChain FxWvC FxChMain FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTbl AsanTblM AsanTblMd AsanEntry AsanPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF AsanMainWF AsanOpenFinF.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanOpenFinF.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcFam AcSubst AcMALlib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require Import AsanPNodes.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition LPATH : lin := hvar 17.
Definition RANDP16 : lin := {| l_c := 8; l_t := [(1%positive, 32768); (2%positive, 4096); (7%positive, 64); (15%positive, 8)] |}.
Definition FV8C : fact := FRange PV 140735332483072 140737488355326.
Definition FV8SPC : fact := FRange (lsub PV (sm_sp MMAIN)) 0 4194304.
Definition FENDP0 : fact := FRange (ladd PV LPATH) 0x7fff7f800000 (0x800000000000 - 17).
Definition FENDP2 : fact := FRange (lsub (ladd PV LPATH) (sm_sp MMAIN)) 0 4194304.
Definition FRZP : fact := FRange (lsub (laddc RANDP16 (-16)) (ladd PV LPATH)) 1 4194304.
Definition FPV0 : fact := FRange (lsub PV P0) 1 4194304.
Definition FSC : list fact := [FV8C; FV8SPC; FENDP0; FENDP2; FRZP; FPV0].
Fixpoint add_facts (S : sst) (fs : list fact) : sst := match fs with [] => S | f :: r => add_facts (add_fact S f) r end.

Definition S1c2 (lo hi : Z) : sst :=
  let S := S1c lo hi in add_facts (SST (s_pc S) (s_regs S) (s_rgs S) (FRange ARGC 2 2 :: s_facts S) (s_next S) (s_resv S)) FSC.
Definition TERR_S : sst := add_facts (ret_gen S_OPEN_T ERRLO ERRHI) FSC.     (* [comment removed for export] *)
Definition TERR_C : sst * smodel * fstate * shp * ast := (TERR_S, M1c, FSClosed, SH_CANNOT, A1c).
Definition TERR_NB : positive := Eval vm_compute in s_next TERR_S.
Definition KERR {N : Type} (i : nat) : @mchain N := MCont i TERR_NB.
