(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxFacts FxPlan FxSubst FxEnt FxDrv FxCall FxGenA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcFam AcPri AcConvA AcNPop AcNPopG AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanPNodes AsanBNodes AsanBodyE.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require Import M4Pure HxSurg HxDerive HarnFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HLB Require Import HarnLoop HarnSite HarnFk HarnChain HarnBudget HarnPost.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition a0_var (S : sst) : option positive :=
  match List.filter (fun '(_, c) => Z.eqb c 1) (l_t (rgk S 10)) with [(x, _)] => Some x | _ => None end.
Definition a0_dec (S : sst) : option (positive * Z) := match a0_var S with Some x => Some (x, 3) | None => None end.
(* [comment removed for export] *)
Definition SIZEREP (k : MCH) : MCH := TRY (HDECV a0_dec) (TRY (HLOWBITS a0_dec) (TRY (HVCONST a0_var) k)).

(* [comment removed for export] *)
Definition STOPS_M (rpc : Z) : list Z := [0x44004; 0x73c38; 0x81f7c; 0x82908; 0x401d8; 0x4467c; 0xd4904; 0x639d4; 0xd4500; 0x5329c; 0x61420; 0x61468; 0x615bc; 0x3fd4c; 0x681c0; 0x683a0; rpc].
Definition SEGM (rpc pc : Z) (node : MCH -> MCH) (k : MCH) : MCH := MSegK 20 (PRun F60000 (STOPS_M rpc) []) (KCons pc 0 (node k) KNil).
Definition F5000h : nat := 5000.
Definition P_UNW : plan := PJoin F5000h [] 0x82908 PFin [].
Definition KMALLOC (c rpc : Z) (k : MCH) : MCH :=
  MSegK 20 P_UNW (KCons 0x82908 0 (A1N NUnw
    (SEGM rpc 0x44004 (A2N (NPop c)) (SEGM rpc 0x81f7c (A1N NPut) (SEGM rpc 0x3fd4c (BN (BBand 0)) (SEGM rpc 0xd4904 (A1N NMset)
    (SEGM rpc 0xd4904 (A1N NMsetC) (SEGM rpc rpc (fun x => x) k))))))) KNil).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition a0_div8 (S : sst) : option (lin * Z) := match ldivz (rgk S 10) 8 with Some l => Some (l, 3) | None => None end.
Definition SCALE8 (k : MCH) : MCH := TRY (HSCL a0_div8) k.
(* [comment removed for export] *)
Definition KMALLOCG (rpc : Z) (k : MCH) : MCH :=
  MSegK 20 P_UNW (KCons 0x82908 0 (A1N NUnw
    (SEGM rpc 0x44004 (fun k0 => A2N NPopG (NODE (HFSUML sel_bform) k0)) (SEGM rpc 0x81f7c (A1N NPut) (SEGM rpc 0x3fd4c (BN (BBand 0)) (SEGM rpc 0xd4904 (A1N NMset)
    (SEGM rpc 0xd4904 (A1N NMsetC) (SEGM rpc rpc (fun x => x) k))))))) KNil).
(* [comment removed for export] *)
