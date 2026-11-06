(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxFacts FxPlan FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxBaseH.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXHB Require Import HxPay.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcSteps AcFam AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanPNodes AsanBNodes AsanBodyE AsanBodyP.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4Y Require FcfBD.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require Import HxSurg HarnFam AcFam3 HarnFcdT.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HLB Require Import HarnKind HarnLoop HarnSite HarnFk HarnChain HarnJoin HarnJoinN HarnJoinM HarnDev HarnLong HarnSSO HarnLongL HarnCR HarnCR2 HarnSP HarnK23 HarnS HarnSub HarnBudget HarnReent HarnEnt HarnPost HarnPM HarnMain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition pm_rlin (S : sst) : option lin := ldivz (laddc (lsub (rgk S 8) (rgk S 2)) (- PM_FRAME)) 16.
(* [comment removed for export] *)
Definition SP0T4 : list (positive * Z) := [(1%positive, 32768); (2%positive, 4096); (3%positive, 64); (4%positive, 16)].
Definition is_pc (R : region) : bool := (terms_eqb (List.firstn 4 (l_t (rg_base R))) SP0T4 && Nat.leb (List.length (l_t (rg_base R))) 5 && Z.ltb (sgn64 (l_c (rg_base R))) 0)%bool.
Definition pc_idx (p : Z -> bool) (S : sst) : option nat :=
  match List.filter (fun '(i, R) => (is_pc R && match is_const (rg_size R) with Some z => p z | None => false end)%bool) (List.combine (List.seq 0 (List.length (s_rgs S))) (s_rgs S)) with
  | [(i, _)] => Some i | _ => None end.
Definition szG : Z := 16.   Definition szR2 : Z := DBAND + PM_LOW - PM_R3.   Definition szR3 : Z := PM_R3.   Definition szR4 : Z := 304.      (* [comment removed for export] *)
Definition PMSITE (k : MCH) : MCH :=
  NODE (HPSRK PKEY pm_rlin)
    (SURG (SFront (pc_idx (Z.eqb szR4))) (SURG (SFront (pc_idx (Z.eqb szR3))) (SURG (SFront (pc_idx (Z.eqb szR2)))
    (SURG (SFront (pc_idx (fun z => negb (Z.eqb z szG || Z.eqb z szR2 || Z.eqb z szR3 || Z.eqb z szR4)))) (SURG (SFront (pc_idx (Z.eqb szG))) k))))).
Definition USEJ_MID (j : nat) (nb : positive) (t : nat) (pcS pcH : Z) (kS kH : MCH) (pr : Z) (next : MCH) : MCH :=
  SITEPREP t (MSegK 20 P_USE (KCons 0x90710 0
    (PMSITE (MJoinG (gclean NB_ENT genF) (MUse j nb (POSTUSE NPOST (POSTCHAIN NPOST (POSTBUDGET NPOST (MSegK 20 (PRun F60000 [pcS; pcH] []) (KCons pcS 0 kS (KCons pcH 0 kH KNil))))))) pr next)) KNil)).
Definition USE_D_MID (j : nat) (nb : positive) (next : MCH) : MCH :=
  USEJ_MID j nb 0 0x90258 0x90264 (SITE_SW 0x9026c 0x902a4 0x90f3c 0 (CALLSITE 0 FP0 cs_specs (tb_sso 19)) (INITPREP (STASH_S 0 19 MEnd)))
                               (SITE_H 0x902a4 0x90f3c (CALLSITE_H 0 FP0 cs_specs_h (tb_heap 19)) (INITPREP (STASH_HK 0 19 MEnd))) 0x902a4 next.
Definition USE_F_MID (j : nat) (nb : positive) (next : MCH) : MCH :=
  USEJ_MID j nb 1 0x902d0 0x902dc (SITE_SW 0x902e4 0x90310 0x98cb8 1 (CALLSITE 1 FcfBD.FP0 cs_specs_f (tb_sso 21)) (INITPREP (STASH_S 1 21 MEnd)))
                               (SITE_H 0x90310 0x98cb8 (CALLSITE_H 1 FcfBD.FP0 cs_specs_fh (tb_heap 21)) (INITPREP (STASH_HK 1 21 MEnd))) 0x90310 next.
Definition USE_I_MID (j : nat) (nb : positive) (next : MCH) : MCH :=
  USEJ_MID j nb 2 0x9033c 0x90348 (SITE_SW 0x90350 0x90380 0x9d970 2 (CALLSITEI 2 OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_fci.P0 cs_specs_i (tb_sso 23)) (INITPREP (STASH_S 2 23 MEnd)))
                               (SITE_H 0x90380 0x9d970 (CALLSITE0_H 2 OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_fci.P0 cs_specs_ih (tb_heap 23)) (INITPREP (STASH_HK 2 23 MEnd))) 0x90380 next.
(* [comment removed for export] *)
Definition stk_idx_of (S : sst) : nat :=
  match List.filter (fun '(i, R) => (terms_eqb (l_t (rg_base R)) SP0T4 && match is_const (rg_size R) with Some z => Z.eqb z 8388608 | None => false end)%bool)
                    (List.combine (List.seq 0 (List.length (s_rgs S))) (s_rgs S)) with
  | [(i, _)] => i | _ => O end.
Definition FIN_MID : MCH := MSegK 20 P_T (KCons 0x90528 0 (REGROUP (EXIT7 (MSegK 20 P_T (KCons 0x8fe58 0 MEnd KNil)))) KNil).
(* [comment removed for export] *)
Definition MIDCH (j : nat) (nb : positive) : MCH :=
  MSegK 20 P_HH (KCons 0x90010 0 (NODE HPAF (FMTB (A3N (NLvDrop 0)
    (USE_D_MID j nb (USE_F_MID j nb (USE_I_MID j nb (TAILS FIN_MID))))))) KNil).      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition PC_MID : Z := 0x900e8.      (* [comment removed for export] *)
Definition PC_RET : Z := 0x8fe58.      (* [comment removed for export] *)
Definition ENTRY_MID (k : MCH) : MCH := UDONE (MJoinG genF0 (ENTRY2 MEnd) PC_MID k).
Definition WRAPCH (stk : nat) (jm : nat) (nbm : positive) : MCH :=
  ENTRY_MID (PMCUT (MUse jm nbm (PMJOIN (UDONE (REFRONT (PMFIX stk MEnd)))))).
Definition HARN_ALL_W (gen : list (sst * smodel) -> list (list lin) -> option (sst * smodel * list lin)) (stk : nat) (jm : nat) (nbm : positive) : MCH :=
  MJoinG gen (MSplitB (lvar 4) 0 0 (WRAPCH stk jm nbm) (WRAPCH stk jm nbm)) PC_RET MEnd.
(* [comment removed for export] *)
