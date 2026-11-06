(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxMem FxRgs FxFacts FxSubst FxEnt FxPlan FxGenA.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxBaseH.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcFam AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanPNodes AsanBNodes AsanBodyE AsanBodyP.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4Y Require FcfBD.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require Import HxSurg HarnFam HarnLoop HarnSite HarnFk AcFam3 HarnChain HarnJoin HarnJoinN HarnJoinM HarnFcdT HarnDev HarnLong HarnSSO HarnLongL HarnCR HarnCR2 HarnSP HarnK23.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition genCRLS0V (S F1 : sst) (FS FS1 : fstate) (sh sh1 : shp) : option (sst * positive * fstate * shp * lin) :=
  match genCRLS0 S F1 FS FS1 sh sh1, (match is_const (rget (s_regs S) (rk 22)) with Some _ => Some C0B | None => None end) with
  | Some (P, n0, FP, shP, meas), Some c0 =>
      let K := lsub (lconst c0) (lvar n0) in let RM := lvar (n0 + 1) in
      Some (SST (s_pc P) (s_regs P) (s_rgs P) (FRange (lsub (lsub (lconst 22) K) RM) 0 4294967296 :: s_facts P) (s_next P) (s_resv P), n0, FP, shP, meas)
  | _, _ => None
  end.
Definition capsum0 (S : sst) : option (lin * lin) :=
  let prov := rget (s_regs S) (rk 20) in let str := rget (s_regs S) (rk 24) in
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
Definition STOPS_B0V : list Z := [0x90898; 0x908bc; 0x908d4; 0x908fc; 0x90914; 0x90934; 0x90968; 0xd9d20; 0xb9d70].
Definition P_B0V : plan := PRun F60000 STOPS_B0V [].
Definition PUSH0 : MCH := TRY (HFSUM capsum0) (MSegK 20 P_B0V KEND0).
Definition KPUSH0 : @mks NPH := KCons 0x90934 0 PUSH0 (KCons 0x90968 0 MEnd KNil).
(* [comment removed for export] *)
Definition zcform (S : sst) : option lin := Some (lsub (lconst C0B) (rgk S 22)).
Definition BODY0V : MCH := MSplitR 22 22 (TRY (HIXF zcform) (MSegK 20 P_B0V (KCons 0x908bc 0
  (HPC1L P_B0V (MSegK 20 P_B0V
    (KCons 0x908fc 0 (NODE HPC2 (MSegK 20 P_B0V (KCons 0x90914 0 (NODE HPLD (MSegK 20 P_B0V KPUSH0)) KPUSH0))) KPUSH0))) KEND0))) MVoid.      (* [comment removed for export] *)
Definition LOOP0V (k : MCH) : MCH := NODE (HREB 24 1) (MLoopG genCRLS0V BODY0V (KCons 0x90968 0 k KNil)).

(* [comment removed for export] *)
Definition SSOBR (pcS pcH : Z) (kS : MCH) : MCH :=
  MJoinG genF (MSegK 20 P_B (KCons 0x90898 0 (LOOP0V MEnd) KNil)) 0x90968 (SEGX pcS pcH pcS (fun k => k) kS).
Definition CRLSB (pcS pcH : Z) (kS kH : MCH) : MCH :=
  MSegK 20 P_H2 (KCons 0xbb504 0 (MSplitR 11 22 (SSOBR pcS pcH kS) (KLONG2 pcS pcH kS kH)) KNil).
(* [comment removed for export] *)
Definition SITE_S (pa pr pe : Z) (k : Z) (site : MCH -> MCH) (after : MCH) : MCH := MJoinG genF (FCALL pa pr pe k site) pr after.
Definition SITE_H (pr pe : Z) (site : MCH -> MCH) (after : MCH) : MCH := MJoinG genF (MSegK 20 P_E (KCons pe 0 (HEAPSEP (site MEnd)) KNil)) pr after.
Definition STRING (k : nat) (r : Z) (pcS pcH : Z) (fS fH : MCH -> MCH) (pr : Z) (next : MCH) : MCH :=
  MJoinG genF (CRLSB pcS pcH (fS (INITPREP (STASH_S k r MEnd))) (fH (INITPREP (STASH_HK k r MEnd)))) pr next.
(* [comment removed for export] *)
Definition STR_D (first : MCH -> MCH) (next : MCH) : MCH :=
  STRING 0 19 0x90258 0x90264 (SITE_S 0x9026c 0x902a4 0x90f3c 0 (CALLSITE 0 FP0 cs_specs (tb_sso 19)))
                              (SITE_H 0x902a4 0x90f3c (CALLSITE_H 0 FP0 cs_specs_h (tb_heap 19))) 0x902a4 next.
Definition STR_F (next : MCH) : MCH :=
  STRING 1 21 0x902d0 0x902dc (SITE_S 0x902e4 0x90310 0x98cb8 1 (CALLSITE 1 FcfBD.FP0 cs_specs_f (tb_sso 21)))
                              (SITE_H 0x90310 0x98cb8 (CALLSITE_H 1 FcfBD.FP0 cs_specs_fh (tb_heap 21))) 0x90310 next.
Definition STR_I (next : MCH) : MCH :=
  STRING 2 23 0x9033c 0x90348 (SITE_S 0x90350 0x90380 0x9d970 2 (CALLSITEI 2 OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_fci.P0 cs_specs_i (tb_sso 23)))
                              (SITE_H 0x90380 0x9d970 (CALLSITE0_H 2 OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_fci.P0 cs_specs_ih (tb_heap 23))) 0x90380 next.

(* [comment removed for export] *)
Definition STOPS_T (rpc : Z) : list Z := [0xb9d70; rpc; 0x681c0; 0x683a0; 0x90528; 0x8fe58].
Definition DEL (k : nat) (rpc : Z) (next : MCH) : MCH :=
  MJoinG genF
    (MSegK 20 (PRun F60000 (STOPS_T rpc) [])
       (KCons 0xb9d70 0 (A3N (NTake k) (FREEX2 rpc (A2N (NGiveX [0; 1; 2]%nat) (A2N (NExtDrop 0) MEnd))))
       (KCons rpc 0 (A3N (NLvDrop k) MEnd) KNil)))
    rpc next.
Definition TAILS (next : MCH) : MCH := DEL 2 0x9039c (DEL 1 0x903c8 (DEL 0 0x903f0 (A3N NLvClear next))).
(* [comment removed for export] *)
