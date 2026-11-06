(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxFacts FxPlan FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxBaseH.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXHB Require Import HxPay.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcFam AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanPNodes AsanBNodes AsanBodyE AsanBodyP.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4Y Require FcfBD.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require Import HxSurg HarnFam AcFam3 HarnFcdT.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HLB Require Import HarnKind HarnLoop HarnSite HarnFk HarnChain HarnJoin HarnJoinN HarnJoinM HarnDev HarnLong HarnSSO HarnLongL HarnCR HarnCR2 HarnSP HarnK23 HarnS HarnSub HarnBudget HarnReent HarnEnt HarnPost.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition NPOST : nat := 30.
Definition P_USE : plan := PRun F60000 (STOPS_H ++ [0x90710]) [].
Definition USEJ (j : nat) (nb : positive) (t : nat) (pcS pcH : Z) (kS kH : MCH) (pr : Z) (next : MCH) : MCH :=
  SITEPREP t (MSegK 20 P_USE (KCons 0x90710 0
    (MJoinG (gclean NB_ENT genF) (MUse j nb (POSTUSE NPOST (POSTCHAIN NPOST (POSTBUDGET NPOST (MSegK 20 (PRun F60000 [pcS; pcH] []) (KCons pcS 0 kS (KCons pcH 0 kH KNil))))))) pr next) KNil)).
Definition USE := USEJ 0.
(* [comment removed for export] *)
Definition FCALLW (pa pr pe : Z) (site : MCH -> MCH) : MCH :=
  MSegK 20 P_L (KCons pa 0 (MSplitR 11 0 (MSegK 20 P_N (KCons pr 0 MEnd KNil)) (MSegK 20 P_E (KCons pe 0 (site MEnd) KNil))) KNil).
Definition SITE_SW (pa pr pe : Z) (t : Z) (site : MCH -> MCH) (after : MCH) : MCH :=
  MJoinG genF (FCALLW pa pr pe site) pr after.
Definition USE_DJ (j : nat) (nb : positive) (next : MCH) : MCH :=
  USEJ j nb 0 0x90258 0x90264 (SITE_SW 0x9026c 0x902a4 0x90f3c 0 (CALLSITE 0 FP0 cs_specs (tb_sso 19)) (INITPREP (STASH_S 0 19 MEnd)))
                           (SITE_H 0x902a4 0x90f3c (CALLSITE_H 0 FP0 cs_specs_h (tb_heap 19)) (INITPREP (STASH_HK 0 19 MEnd))) 0x902a4 next.
Definition USE_D := USE_DJ 0.
Definition USE_FJ (j : nat) (nb : positive) (next : MCH) : MCH :=
  USEJ j nb 1 0x902d0 0x902dc (SITE_SW 0x902e4 0x90310 0x98cb8 1 (CALLSITE 1 FcfBD.FP0 cs_specs_f (tb_sso 21)) (INITPREP (STASH_S 1 21 MEnd)))
                           (SITE_H 0x90310 0x98cb8 (CALLSITE_H 1 FcfBD.FP0 cs_specs_fh (tb_heap 21)) (INITPREP (STASH_HK 1 21 MEnd))) 0x90310 next.
Definition USE_F := USE_FJ 0.
Definition USE_IJ (j : nat) (nb : positive) (next : MCH) : MCH :=
  USEJ j nb 2 0x9033c 0x90348 (SITE_SW 0x90350 0x90380 0x9d970 2 (CALLSITEI 2 OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_fci.P0 cs_specs_i (tb_sso 23)) (INITPREP (STASH_S 2 23 MEnd)))
                           (SITE_H 0x90380 0x9d970 (CALLSITE0_H 2 OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_fci.P0 cs_specs_ih (tb_heap 23)) (INITPREP (STASH_HK 2 23 MEnd))) 0x90380 next.
Definition USE_I := USE_IJ 0.
(* [comment removed for export] *)
Definition UDONE (k : MCH) : MCH := TRY (HIXF (fun S => Some (lscale MARKC (rgk S 21)))) k.      (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_FMTB : plan := PRun F60000 [0x901f8; 0x9021c; 0x90228] [].
(* [comment removed for export] *)
Definition genFMTB := genM (fun P als => xf_hist P als ++ [FRange (rget (s_regs P) (rk 22)) 1 5; FBits (rget (s_regs P) (rk 22)) 18446744073709551610 0]).
Definition FMTB (k : MCH) : MCH :=
  MSegK 20 P_FMTB (KCons 0x901f8 0
    (MJoinG genFMTB (MSplitR 10 2 (MSegK 20 P_FMTB (KCons 0x9021c 0 (NODE HFMT (MSegK 20 P_FMTB (KCons 0x90228 0 MEnd KNil))) KNil))
                                (MSegK 20 P_FMTB (KCons 0x90228 0 MEnd KNil))) 0x90228 k) KNil).
Definition PRE_M (k : MCH) : MCH :=
  UDONE (MJoinG genF0 (ENTRY2 MEnd) 0x900e8 (MSegK 20 P_HH (KCons 0x90010 0 (NODE HPAF (FMTB (A3N (NLvDrop 0) k))) KNil))).
(* [comment removed for export] *)
Definition payU (S : sst) : lin := pg_P G1.
Definition payH (S : sst) : lin := laddc (pg_P G1) (-16).
Definition payA (S : sst) : lin := laddc (oshadow (pg_P G1)) (-1).
Definition payB (S : sst) : lin := ladd (oshadow (pg_P G1)) (lvar V_QU).
Definition FS2A (S : sst) : lin := laddc (FSof S) 0x208000.
Definition REFRONT (k : MCH) : MCH :=
  FRONT_AT (fun S => oshadow (FS2A S)) (FRONT_AT FS2A (FRONT_AT payB (FRONT_AT payA (FRONT_AT payU (FRONT_AT payH k))))).
Definition FIN_M : MCH := MSegK 20 P_T (KCons 0x90528 0 (REGROUP (EXIT7 (MSegK 20 P_T (KCons 0x8fe58 0 (UDONE (REFRONT MEnd)) KNil)))) KNil).

(* [comment removed for export] *)
Definition hint_c (k : Z) (S : sst) := at_c S (laddc (FSof S) (8 * k)) 8.
Definition HINTS (k : MCH) : MCH := NODE (HZBK (fun S => at_c S (laddc (FSof S) 96) 1)) (NODE (HZRT (hint_c 0)) (NODE (HZRT (hint_c 2)) (NODE (HZRT (hint_c 4)) (NODE (HZRT (hint_c 5)) k)))).      (* [comment removed for export] *)
Definition FKPREP (k : MCH) : MCH := SURG (SSteps fk_prep_all) (SURG (SSteps fk_prep_sh) k).
(* [comment removed for export] *)
Definition l8_of (l : lin) : sst -> option (lin * Z) := fun _ => match FxEnt.ldivz l 8 with Some l8 => Some (l8, 3) | None => None end.
Definition KSCALE (k : MCH) : MCH := fold_right (fun l k' => NODE (HSCL (l8_of l)) k') k KIND_SCALES.
Definition HARN_PREPK (k : MCH) : MCH := SEPS0 (KSCALE (HINTS (FKPREP (RTPREP (UDONE (REFRONT k)))))).
Definition HARN_PREP : MCH := HARN_PREPK MEnd.
(* [comment removed for export] *)
Definition KHI1 : Z := 0x10007fff8000 - 1.
Definition CLASSK (kL kH : MCH) : MCH := MSplitG IX_FS KHI1 (NODE (HLOWB (fun S => Some (FSof S))) kL) kH.
Definition HARN_CLASSJ (j : nat) (nb : positive) : MCH := PRE_M (USE_DJ j nb (USE_FJ j nb (USE_IJ j nb (TAILS FIN_M)))).
Definition HARN_CLASS := HARN_CLASSJ 0.
(* [comment removed for export] *)
Definition HARN_ALL (gen : list (sst * smodel) -> list (list lin) -> option (sst * smodel * list lin)) (nb0 nb1 nb2 nb3 : positive) : MCH :=
  MJoinG gen (MSplitB (lvar 4) 0 0 (CLASSK (HARN_CLASSJ 0 nb0) (HARN_CLASSJ 1 nb1)) (CLASSK (HARN_CLASSJ 2 nb2) (HARN_CLASSJ 3 nb3))) 0x8fe58 MEnd.
(* [comment removed for export] *)
Definition HARN_ALL2 (gen : list (sst * smodel) -> list (list lin) -> option (sst * smodel * list lin)) (nb0 nb1 : positive) : MCH :=
  MJoinG gen (MSplitB (lvar 4) 0 0 (HARN_CLASSJ 0 nb0) (HARN_CLASSJ 1 nb1)) 0x8fe58 MEnd.
(* [comment removed for export] *)
