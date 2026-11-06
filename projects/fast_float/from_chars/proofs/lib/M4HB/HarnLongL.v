(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxRgs FxFacts FxStep FxSubst FxEnt FxDrv FxCall FxPlan FxGenA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanPNodes AsanBNodes AsanBodyE AsanBodyP.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxBaseH.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require Import HxSurg HarnFam HarnLoop HarnSite HarnFk HarnChain HarnDev HarnLong.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Definition genCRLSL := genCRLSLg G1.
Definition STOPS_BL : list Z := [0x90898; 0x908bc; 0x908d4; 0x908fc; 0x90914; 0x90934; 0x90968; 0xd9d20; 0xb9d70; 0xbb5d8].
Definition P_BL : plan := PRun F60000 STOPS_BL [].
Definition KENDL : @mks NPH := KCons 0x90898 0 MEnd (KCons 0x90968 0 MEnd KNil).
(* [comment removed for export] *)
Definition PUSHL : MCH := TRY (HFSUM crls_capsum) (MSegK 20 P_BL KENDL).
Definition KPUSH : @mks NPH := KCons 0x90934 0 PUSHL (KCons 0x90968 0 MEnd KNil).
Definition BODYL : MCH := (MSegK 20 P_BL (KCons 0x908bc 0
  (HPC1L P_BL (MSegK 20 P_BL
    (KCons 0x908fc 0 (NODE HPC2 (MSegK 20 P_BL (KCons 0x90914 0 (NODE HPLD (MSegK 20 P_BL KPUSH)) KPUSH))) KPUSH))) KENDL)).
(* [comment removed for export] *)
Definition size_w (S : sst) : option (nat * Z * nat) := match find_idx (s_rgs S) (rgk S 24) 0 with Some (i, o) => Some (i, o + 8, 8%nat) | None => None end.
(* [comment removed for export] *)
Definition cap_w (S : sst) : option (nat * Z * nat) := match find_idx (s_rgs S) (rgk S 24) 0 with Some (i, o) => Some (i, o, 8%nat) | None => None end.
Definition LOOPL (k : MCH) : MCH := TRY (HZRT size_w) (TRY (HRBK cap_w) (MLoopG genCRLSL BODYL (KCons 0x90968 0 k KNil))).

(* [comment removed for export] *)
Definition reg_key (r : Z) (S : sst) : option positive := match is_const (rgk S r) with Some _ => None | None => Some (rk r) end.
Definition namer_sum (r : Z) (S : sst) : option (lin * lin) :=
  match s_facts S, l_t (rgk S r) with
  | FRange d 0 0 :: _, [(y, 1)] => Some (d, lsub (lvar y) d)
  | _, _ => None
  end.
Definition reg_dec (r : Z) (S : sst) : option (positive * Z) := match l_t (rgk S r) with [(x, 1)] => if Z.eqb (l_c (rgk S r)) 0 then Some (x, 3) else None | _ => None end.
Definition NAMEDEC (r : Z) (k : MCH) : MCH := NODE (HNAMER (reg_key r)) (NODE (HFSUM (namer_sum r)) (NODE (HDECV (reg_dec r)) k)).

(* [comment removed for export] *)
Definition size_decn (S : sst) : option (positive * Z * Z) :=
  match find_cell (s_rgs S) (laddc (rgk S 24) 8) with
  | Some (_, _, l) => match l_t l with [(x, m)] => if Z.eqb m 18446744073709551615 then Some (x, l_c l, 3) else None | _ => None end
  | None => None
  end.
(* [comment removed for export] *)
Definition size_decv (S : sst) : option (positive * Z) :=
  match find_cell (s_rgs S) (laddc (rgk S 24) 8) with
  | Some (_, _, l) => match l_t l with [(x, 1)] => if Z.eqb (l_c l) 0 then Some (x, 3) else None | _ => None end
  | None => None
  end.
Definition SIZEDEC (k : MCH) : MCH := TRY (HDECN size_decn) (TRY (HDECV size_decv) k).
(* [comment removed for export] *)
Definition CAPSUM (k : MCH) : MCH := TRY (HFSUM crls_capsum) k.

(* [comment removed for export] *)
Definition needs_heap (nds : sst -> list need) (L : sst) : list need :=
  match nds L with
  | t :: _ :: r => t :: NBase (oshadow (rgk L 10)) RZ :: r
  | l => l
  end.
Definition cs_specs_h := specs_of (needs_heap needs_fc).
Definition cs_specs_fh := specs_of (needs_heap (needs_fcv 4)).
Definition cs_specs_ih := specs_of (needs_heap needs_fci).
Definition CS_PRE_H (k : MCH) : MCH :=
  SURG (SSplit cs_split_text) (SURG (SRetype cs_rt_text) (TRY (HUNZ cs_unz_ssh) (SURG (SSplit cs_split_ssh)
  (NODE (HTRK h5_cell) (TRY (HZBK cs_zbk_fsh) (TRY (HZBK cs_zbk_tsd) (TRY (HZBK cs_zbk_hme)
  (TRY (HRB1 cs_rb1_fb) (TRY (HRBK cs_rbk_tlsb) (TRY (HRBK cs_rbk_tlse) (TRY (HRBK cs_rbk_beg)
  (TRY (HSCL cs_scl_fs8) (TRY (HSCL cs_scl_fsp) k))))))))))))).
(* [comment removed for export] *)
Definition tb_heap (r : Z) (S : sst) : lin := match find_cell (s_rgs S) (laddc (rgk S r) 16) with Some (_, _, p) => p | None => lconst 0 end.
Definition CS_POST_H (tb : sst -> lin) (k : MCH) : MCH :=
  SURG (SRetype (cs_rw_text tb)) (SURG (SMerge (cs_mrg_text tb)) (SURG (SMerge cs_mrg_ssh) k)).
Definition CALLSITE0_H (j : nat) (P0 : sst) (specs : sst -> list (vop * Z * rkind)) (tb : sst -> lin) (k : MCH) : MCH :=
  CS_PRE_H (SITE j P0 specs (CS_POST_H tb k)).
Definition CALLSITE_H (j : nat) (P0 : sst) (specs : sst -> list (vop * Z * rkind)) (tb : sst -> lin) (k : MCH) : MCH :=
  NODE (HDEC h4_dec) (NODE (HPSR (fun S => Some (Y4 S)))
  (MSplitR 39 0 (NODE (HREPL h4_lo) (CALLSITE0_H j P0 specs tb k))
  (MSplitR 39 1022 (CARVE4 (CS_PRE_H (SITE j P0 specs (CS_POST_H tb (REST4 k)))))
                   (NODE (HREPL h4_hi) (CALLSITE0_H j P0 specs tb k))))).

(* [comment removed for export] *)
Definition S6 : Z := 11571200.   Definition S12 : Z := 137439023104.
Definition SEPW_HI : Z := 18446744073709551616 - S6 - S12.
Definition sepw_form (S : sst) : option lin :=
  match List.filter (fun f => match f with FRange _ 0 hi => Z.eqb hi SEPW_HI | _ => false end) (s_facts S) with
  | FRange l _ _ :: _ => Some l
  | _ => None
  end.
Definition heap_sum1 (S : sst) : option (lin * lin) :=
  match sepw_form S, cell S (lconst 0xe3038) with
  | Some l, Some SBl => let PG := laddc (ladd l (FSof S)) S6 in Some (lsub (rgk S 10) SBl, lsub SBl PG)
  | _, _ => None
  end.
Definition heap_sum2 (S : sst) : option (lin * lin) :=
  match sepw_form S with
  | Some l => let PG := laddc (ladd l (FSof S)) S6 in Some (lsub (rgk S 10) PG, l)
  | None => None
  end.
Definition HEAPSEP (k : MCH) : MCH := MSep (TSepW IX_PG IX_FS) (NODE (HFSUM heap_sum1) (NODE (HFSUM heap_sum2) k)).
(* [comment removed for export] *)
