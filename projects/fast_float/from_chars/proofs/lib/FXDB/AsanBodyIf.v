(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall FxEnt FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChEntM FxChSubst FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEntM OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSubst OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require Import AsanLit.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcFam AcSubst AcPri AcFam2 AcFam3 AcMALlib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxMchr AsanBNodes AsanBodyFam AsanTailCh AsanBodyCh.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanTblH2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanCallTE AsanCallTP AsanCallTL.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyFam OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTailCh OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyCh OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTblH2.AsanTailDefs OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCallTE OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCallTP OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCallTL.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanCallTE.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require HETH.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanCallTP.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require HPFP HPTH HPFHARN.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCallTE.HEFP OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HETH OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCallTP.HEFH OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HPFP OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HPTH OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HPFHARN.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HLB Require HPFP HPTH HPFHARN.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition NX : Type := NB.
Definition MCX : Type := @mchain NX.
Definition apostX : NX -> sst -> smodel -> ast -> option (sst * smodel * ast) := apostB.
Definition A1X (nk : anode) (k : MCX) : MCX := A1B nk k.
Definition A2X (n : anode2) (k : MCX) : MCX := A2B n k.
Definition A3X (n : anode3) (k : MCX) : MCX := A3B n k.
Definition BX (b : bnode) (k : MCX) : MCX := BB b k.
(* [comment removed for export] *)
Definition ret_fin (T : sst) : sst :=
  SST 0x8fe58 (tset (rkey (xr 1)) (lconst 0x8fe58) (tset (rkey (xr 10)) (lconst 0) (s_regs T))) (s_rgs T) (s_facts T) (s_next T) (s_resv T).
(* [comment removed for export] *)
Definition PREPF_L : list (sst * smodel * ast) := [(M4HLB.HPFP.HPFP_S, M4HLB.HPFP.HPFP_M, M4HLB.HPFP.HPFP_A)].
Definition HFINS_L : list (sst * smodel * ast) := [(M4HLB.HPFHARN.HPFHARN_S, M4HLB.HPFHARN.HPFHARN_M, M4HLB.HPFHARN.HPFHARN_A)].
(* [comment removed for export] *)
Definition PREPF_P : list (sst * smodel * ast) := [(HPFP_S, HPFP_M, HPFP_A)].
Definition HFINS_P : list (sst * smodel * ast) := [(HPFHARN_S, HPFHARN_M, HPFHARN_A)].
(* [comment removed for export] *)
Definition PREPF_E : list (sst * smodel * ast) := [(HEFP_S, HEFP_M, HEFP_A)].
Definition HFINS_E : list (sst * smodel * ast) := [(HEFH_S, HEFH_M, HEFH_A)].
(* [comment removed for export] *)
Definition sub_t : Type := (sst * smodel * ast * list (sst * smodel * ast))%type.
Definition SUBH_E0 : sub_t := (TCE_S, TCE_M, TCE_A, PREPF_E).   Definition SUBH_P0 : sub_t := (TCP_S, TCP_M, TCP_A, PREPF_P).   Definition SUBH_L0 : sub_t := (TCL_S, TCL_M, TCL_A, PREPF_L).
Definition SUBH_E1 : sub_t := (HETH_S, HETH_M, HETH_A, HFINS_E).   Definition SUBH_P1 : sub_t := (HPTH_S, HPTH_M, HPTH_A, HFINS_P).
Definition SUBH_L1 : sub_t := (M4HLB.HPTH.HPTH_S, M4HLB.HPTH.HPTH_M, M4HLB.HPTH.HPTH_A, HFINS_L).
Definition SUBS_H : list sub_t := [SUBH_E0; SUBH_P0; SUBH_L0; SUBH_E1; SUBH_P1; SUBH_L1].
(* [comment removed for export] *)
Definition SUBS_HE : list sub_t := [SUBH_E0; SUBH_E0; SUBH_E0; SUBH_E1; SUBH_E1; SUBH_E1].
Definition SUBS_HP : list sub_t := [SUBH_P0; SUBH_P0; SUBH_P0; SUBH_P1; SUBH_P1; SUBH_P1].
Definition SUBS_HL : list sub_t := [SUBH_L0; SUBH_L0; SUBH_L0; SUBH_L1; SUBH_L1; SUBH_L1].
Definition HARN_E (k : MCX) : MCX := WNORM BX false (MUse (3 + JH0) NB_G (WNORM BX true k)).
Definition HARN_P (k : MCX) : MCX := WNORM BX false (MUse (4 + JH0) NB_G (WNORM BX true k)).
Definition HARN_L (k : MCX) : MCX := WNORM BX false (MUse (5 + JH0) NB_G (WNORM BX true k)).
(* [comment removed for export] *)
Definition HARN1_E (k : MCX) : MCX := WNORM BX false (MUse JH0 NB_G (MUse (3 + JH0) NB_G (WNORM BX true k))).
Definition HARN1_P (k : MCX) : MCX := WNORM BX false (MUse (1 + JH0) NB_G (MUse (4 + JH0) NB_G (WNORM BX true k))).
Definition HARN1_L (k : MCX) : MCX := WNORM BX false (MUse (2 + JH0) NB_G (MUse (5 + JH0) NB_G (WNORM BX true k))).
(* [comment removed for export] *)
Definition IB_E : nat := 4.
Definition IB_P : nat := 4.
Definition IB_L : nat := 13.
(* [comment removed for export] *)
