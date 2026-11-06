(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxMem FxRgs FxFacts FxSubst FxEnt FxPlan FxGenA.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxBaseH.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcFam AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require Import AsanPNodes AsanBNodes AsanBodyE AsanBodyP.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4X Require FcfAD.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4A_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require Import HxSurg HarnFam AcFam3 HarnFcdT.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HL Require Import HarnLoop HarnSite HarnFk HarnChain HarnJoin HarnJoinN HarnJoinM HarnDev HarnLong HarnSSO HarnLongL HarnCR HarnCR2 HarnSP HarnK23.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition genCRLS0V (S F1 : sst) (FS FS1 : fstate) (sh sh1 : shp) : option (sst * positive * fstate * shp * lin) :=
  match genCRLS0 S F1 FS FS1 sh sh1, is_const (rget (s_regs S) (rk 18)) with
  | Some (P, n0, FP, shP, meas), Some c0 =>
      let K := lsub (lconst c0) (lvar n0) in let RM := lvar (n0 + 1) in
      Some (SST (s_pc P) (s_regs P) (s_rgs P) (FRange (lsub (lsub (lconst 22) K) RM) 0 4294967296 :: s_facts P) (s_next P) (s_resv P), n0, FP, shP, meas)
  | _, _ => None
  end.
Definition capsum0 (S : sst) : option (lin * lin) :=
  let prov := rget (s_regs S) (rk 9) in let str := rget (s_regs S) (rk 8) in
  match find_idx (s_rgs S) str 0, find_cell (s_rgs S) (laddc prov 8) with
  | Some (i, o), Some (_, _, rc) =>
      match nth_error (s_rgs S) i, l_t rc with
      | Some R, [(x, 1)] =>
          match Prelude.tget (okey o) (rg_cont R) with
          | Some (BV l 0) => match FxEnt.ldivz l 2 with Some K => Some (lsub (lsub (lconst 22) K) (lvar x), lvar x) | None => None end
          | _ => None
          end
      | _, _ => None
      end
  | _, _ => None
  end.
Definition STOPS_B0V : list Z := [0x90688; 0x906a4; 0x906d8; 0x906f0; 0x90710; 0x90740; 0xd84a4; 0xb84f4].
Definition P_B0V : plan := PRun F60000 STOPS_B0V [].
Definition PUSH0 : MCH := TRY (HFSUM capsum0) (MSegK 20 P_B0V KEND0).
Definition KPUSH0 : @mks NPH := KCons 0x90710 0 PUSH0 (KCons 0x90740 0 MEnd KNil).
Definition BODY0V : MCH := MSplitR 18 105 MVoid (MSegK 20 P_B0V (KCons 0x906a4 0
  (NODE HPC1 (MSegK 20 P_B0V
    (KCons 0x906d8 0 (NODE HPC2 (MSegK 20 P_B0V (KCons 0x906f0 0 (NODE HPLD (MSegK 20 P_B0V KPUSH0)) KPUSH0))) KPUSH0))) KEND0)).
Definition LOOP0V (k : MCH) : MCH := NODE (HREB 8 1) (MLoopG genCRLS0V BODY0V (KCons 0x90740 0 k KNil)).

(* [comment removed for export] *)
Definition SSOBR (pcS pcH : Z) (kS : MCH) : MCH :=
  MJoinG genF (MSegK 20 P_B (KCons 0x90688 0 (LOOP0V MEnd) KNil)) 0x90740 (SEGX pcS pcH pcS (fun k => k) kS).
Definition CRLSB (pcS pcH : Z) (kS kH : MCH) : MCH :=
  MSegK 20 P_H2 (KCons 0xb9c88 0 (MSplitR 11 22 (SSOBR pcS pcH kS) (KLONG2 pcS pcH kS kH)) KNil).
(* [comment removed for export] *)
Definition SITE_S (pa pr pe : Z) (k : Z) (site : MCH -> MCH) (after : MCH) : MCH := MJoinG genF (FCALL pa pr pe k site) pr after.
Definition SITE_H (pr pe : Z) (site : MCH -> MCH) (after : MCH) : MCH := MJoinG genF (MSegK 20 P_E (KCons pe 0 (HEAPSEP (site MEnd)) KNil)) pr after.
Definition STRING (k : nat) (r : Z) (pcS pcH : Z) (fS fH : MCH -> MCH) (pr : Z) (next : MCH) : MCH :=
  MJoinG genF (CRLSB pcS pcH (fS (INITPREP (STASH_S k r MEnd))) (fH (INITPREP (STASH_HK k r MEnd)))) pr next.
(* [comment removed for export] *)
Definition STR_D (first : MCH -> MCH) (next : MCH) : MCH :=
  STRING 0 19 0x901cc 0x901d8 (SITE_S 0x901e4 0x90208 0x90c04 0 (CALLSITE 0 FP0 cs_specs (tb_sso 19)))
                              (SITE_H 0x90208 0x90c04 (CALLSITE_H 0 FP0 cs_specs_h (tb_heap 19))) 0x90208 next.
Definition STR_F (next : MCH) : MCH :=
  STRING 1 20 0x90238 0x90244 (SITE_S 0x9024c 0x90260 0x97d00 1 (CALLSITE 1 FcfAD.FP0 cs_specs_f (tb_sso 20)))
                              (SITE_H 0x90260 0x97d00 (CALLSITE_H 1 FcfAD.FP0 cs_specs_fh (tb_heap 20))) 0x90260 next.
Definition STR_I (next : MCH) : MCH :=
  STRING 2 22 0x9028c 0x90298 (SITE_S 0x902a0 0x902bc 0x9c180 2 (CALLSITEI 2 OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn.M4A_fci.P0 cs_specs_i (tb_sso 22)))
                              (SITE_H 0x902bc 0x9c180 (CALLSITE0_H 2 OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn.M4A_fci.P0 cs_specs_ih (tb_heap 22))) 0x902bc next.

(* [comment removed for export] *)
Definition STOPS_T (rpc : Z) : list Z := [0xb84f4; rpc; 0x681cc; 0x683ac; 0x90444; 0x8fe64].
Definition DEL (k : nat) (rpc : Z) (next : MCH) : MCH :=
  MJoinG genF
    (MSegK 20 (PRun F60000 (STOPS_T rpc) [])
       (KCons 0xb84f4 0 (A3N (NTake k) (FREEX2 rpc (A2N (NGiveX [0; 1; 2]%nat) (A2N (NExtDrop 0) MEnd))))
       (KCons rpc 0 (A3N (NLvDrop k) MEnd) KNil)))
    rpc next.
Definition TAILS (next : MCH) : MCH := DEL 2 0x902d8 (DEL 1 0x90304 (DEL 0 0x9032c (A3N NLvClear next))).
