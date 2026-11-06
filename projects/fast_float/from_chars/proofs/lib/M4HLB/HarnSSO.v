(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxFacts FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanBodyE AsanBodyP.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4Y Require FcfBD.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require Import HxSurg HarnFam HarnFcdT.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HLB Require Import HarnLoop HarnSite HarnFk HarnChain HarnJoin HarnDev.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition prov9 (S : sst) : lin := rget (s_regs S) (rk 20).                 (* [comment removed for export] *)
Definition prov_h (S : sst) : lin := rget (s_regs S) (rk 20).      (* [comment removed for export] *)     (* [comment removed for export] *)
Definition P_T : plan := PRun F60000 (STOPS_H ++ [0x90528; 0x8fe58; 0xb9d70; 0x681c0; 0x683a0]) [].

Section K.
Variable klong : MCH.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition CRLS1 : MCH :=
  ENTRY (MSegK 20 P_HH (KCons 0x90010 0 (NODE HPAF (MSegK 20 P_H2 (KCons 0x9021c 0 (NODE HFMT (MSegK 20 P_H2 (KCons 0xbb504 0
   (MSplit NL 23 (MSegK 20 P_B (KCons 0x90898 0 (LOOP0 MEnd) KNil)) klong) KNil))) KNil))) KNil)).
Definition CRLSn : MCH :=
  MSegK 20 P_H2 (KCons 0xbb504 0 (MSplitR 11 22 (MSegK 20 P_B (KCons 0x90898 0 (LOOP0 MEnd) KNil)) klong) KNil).
(* [comment removed for export] *)
Definition FCALL (pa pr pe : Z) (k : Z) (site : MCH -> MCH) : MCH :=
  MSegK 20 P_L (KCons pa 0 (MSplitR 11 0 (MSegK 20 P_N (KCons pr 0 (FSH_RW k MEnd) KNil))
                                       (MSegK 20 P_E (KCons pe 0 (site MEnd) KNil))) KNil).
Definition FCALL_D : MCH := FCALL 0x9026c 0x902a4 0x90f3c 0 (CALLSITE 0 FP0 cs_specs (tb_sso 19)).
Definition FCALL_F : MCH := FCALL 0x902e4 0x90310 0x98cb8 1 (CALLSITE 1 FcfBD.FP0 cs_specs_f (tb_sso 20)).
Definition FCALL_I : MCH := FCALL 0x90350 0x90380 0x9d970 2 (CALLSITEI 2 OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_fci.P0 cs_specs_i (tb_sso 22)).
Definition TAIL : MCH := MSegK 20 P_T (KCons 0x90528 0 (EXIT2 (MSegK 20 P_T (KCons 0x8fe58 0 MEnd KNil))) KNil).
Definition JC (body : MCH) (jpc : Z) (k : MCH) : MCH := MJoinG (genJ prov9 G1) body jpc k.
Definition JH (body : MCH) (jpc : Z) (k : MCH) : MCH := MJoinG (genJ prov_h G1) body jpc k.
Definition HARN_SSO1 : MCH :=
  JC CRLS1 0x90968 (JH FCALL_D 0x902a4 (JC CRLSn 0x90968 (JH FCALL_F 0x90310 (JC CRLSn 0x90968 (JH FCALL_I 0x90380 TAIL))))).
(* [comment removed for export] *)
Definition HARN_SSO : MCH := MSplitB (lvar 4) 0 0 HARN_SSO1 HARN_SSO1.
End K.
(* [comment removed for export] *)
