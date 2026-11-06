(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxFacts FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require Import AsanBodyE AsanBodyP.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4X Require FcfAD.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4A_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require Import HxSurg HarnFam HarnFcdT.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HL Require Import HarnLoop HarnSite HarnFk HarnChain HarnJoin HarnDev.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition prov9 (S : sst) : lin := rget (s_regs S) (rk 9).                 (* [comment removed for export] *)
Definition prov_h (S : sst) : lin := laddc (rget (s_regs S) (rk 9)) 48.     (* [comment removed for export] *)
Definition P_T : plan := PRun F60000 (STOPS_H ++ [0x90444; 0x8fe64; 0xb84f4; 0x681cc; 0x683ac]) [].

Section K.
Variable klong : MCH.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition CRLS1 : MCH :=
  ENTRY (MSegK 20 P_HH (KCons 0x8ffc0 0 (NODE HPAF (MSegK 20 P_H2 (KCons 0x8fff8 0 (NODE HFMT (MSegK 20 P_H2 (KCons 0xb9c88 0
   (MSplit NL 23 (MSegK 20 P_B (KCons 0x90688 0 (LOOP0 MEnd) KNil)) klong) KNil))) KNil))) KNil)).
Definition CRLSn : MCH :=
  MSegK 20 P_H2 (KCons 0xb9c88 0 (MSplitR 11 22 (MSegK 20 P_B (KCons 0x90688 0 (LOOP0 MEnd) KNil)) klong) KNil).
(* [comment removed for export] *)
Definition FCALL (pa pr pe : Z) (k : Z) (site : MCH -> MCH) : MCH :=
  MSegK 20 P_L (KCons pa 0 (MSplitR 11 0 (MSegK 20 P_N (KCons pr 0 (FSH_RW k MEnd) KNil))
                                       (MSegK 20 P_E (KCons pe 0 (site MEnd) KNil))) KNil).
Definition FCALL_D : MCH := FCALL 0x901e4 0x90208 0x90c04 0 (CALLSITE 0 FP0 cs_specs (tb_sso 19)).
Definition FCALL_F : MCH := FCALL 0x9024c 0x90260 0x97d00 1 (CALLSITE 1 FcfAD.FP0 cs_specs_f (tb_sso 20)).
Definition FCALL_I : MCH := FCALL 0x902a0 0x902bc 0x9c180 2 (CALLSITEI 2 OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn.M4A_fci.P0 cs_specs_i (tb_sso 22)).
Definition TAIL : MCH := MSegK 20 P_T (KCons 0x90444 0 (EXIT2 (MSegK 20 P_T (KCons 0x8fe64 0 MEnd KNil))) KNil).
Definition JC (body : MCH) (jpc : Z) (k : MCH) : MCH := MJoinG (genJ prov9 G1) body jpc k.
Definition JH (body : MCH) (jpc : Z) (k : MCH) : MCH := MJoinG (genJ prov_h G1) body jpc k.
Definition HARN_SSO1 : MCH :=
  JC CRLS1 0x90740 (JH FCALL_D 0x90208 (JC CRLSn 0x90740 (JH FCALL_F 0x90260 (JC CRLSn 0x90740 (JH FCALL_I 0x902bc TAIL))))).
(* [comment removed for export] *)
Definition HARN_SSO : MCH := MSplitB (lvar 4) 0 0 HARN_SSO1 HARN_SSO1.
End K.
