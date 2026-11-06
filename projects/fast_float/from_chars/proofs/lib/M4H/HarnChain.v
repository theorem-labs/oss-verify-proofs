(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxRgs FxFacts FxStep FxSubst FxEnt FxDrv FxCall FxGenA FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcFam AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require Import AsanPNodes AsanBNodes AsanQcsX.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxBaseH HxPay.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require M4Pure HxSurg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require HarnFam HarnLoop HarnSite HarnFk AcFam3.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4H.M4Pure OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HxSurg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.HxDerive OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnFam OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnLoop OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnSite OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnFk OSSVerify.Proofs.fast_float.from_chars.lib.M4H.AcFam3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition NPH : Type := (anode3 + xnode) + (pnode + (hnode + bnode)).
Definition MCH : Type := @mchain NPH.
Definition NODE (h : hnode) (k : MCH) : MCH := MCall (inr (inr (inl h))) k.
Definition BN (b : bnode) (k : MCH) : MCH := MCall (inr (inr (inr b))) k.
Definition PN (p : pnode) (k : MCH) : MCH := MCall (inr (inl p)) k.
Definition A1N (nk : anode) (k : MCH) : MCH := MCall (inl (inl (A2 (A1 nk)))) k.
Definition A2N (nk : anode2) (k : MCH) : MCH := MCall (inl (inl (A2 nk))) k.
Definition A3N (nk : anode3) (k : MCH) : MCH := MCall (inl (inl nk)) k.
Definition XN (x : xnode) (k : MCH) : MCH := MCall (inl (inr x)) k.
Definition XQS (j : nat) (k : MCH) : MCH := XN (XQcs j) k.     (* [comment removed for export] *)
Definition SURG (h : surg) (k : MCH) : MCH := NODE (HSURG h) k.
Definition KEEPK : list positive := List.map rk [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

(* [comment removed for export] *)
Definition TRY (h : hnode) (k : MCH) : MCH := NODE (HTRY h) k.
Definition CS_PRE (k : MCH) : MCH :=
  SURG (SSteps cs_isolate) (SURG (SSplit cs_split_text) (SURG (SRetype cs_rt_text) (TRY (HUNZ cs_unz_ssh) (SURG (SSplit cs_split_ssh)
  (NODE (HTRK h5_cell) (TRY (HZBK cs_zbk_fsh) (TRY (HZBK cs_zbk_tsd) (TRY (HZBK cs_zbk_hme)
  (TRY (HRB1 cs_rb1_fb) (TRY (HRBK cs_rbk_tlsb) (TRY (HRBK cs_rbk_tlse) (TRY (HRBK cs_rbk_beg)
  (TRY (HSCL cs_scl_fs8) (TRY (HSCL cs_scl_fsp) k)))))))))))))).
(* [comment removed for export] *)
Definition CS_POST (tb : sst -> lin) (k : MCH) : MCH :=
  SURG (SRetype (cs_rw_text tb)) (SURG (SMerge (cs_mrg_text tb)) (SURG (SSteps (cs_mcc_text tb)) (SURG (SMerge cs_mrg_ssh) k))).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SITE (j : nat) (P0 : sst) (specs : sst -> list (vop * Z * rkind)) (k : MCH) : MCH :=
  NODE (HSUBS (cs_want P0 specs)) (NODE (HSITEF j KEEPK [] specs) k).
Definition CALLSITE0 (j : nat) (P0 : sst) (specs : sst -> list (vop * Z * rkind)) (tb : sst -> lin) (k : MCH) : MCH :=
  CS_PRE (SITE j P0 specs (CS_POST tb k)).
(* [comment removed for export] *)
Definition CARVE4 (k : MCH) : MCH := SURG (SSplit (fk_carve_fl 4 Y4)) (SURG (SSplit (fk_carve_ar 4 Y4)) (SURG (SSplit (fk_carve_sh 4 Y4)) k)).
Definition REST4 (k : MCH) : MCH :=
  SURG (SMerge (fk_mrg3_at fk4_fl0 1)) (SURG (SMerge (fk_mrg3_at fk4_ar0 1024)) (SURG (SMerge (fk_mrg3_at fk4_sh0 128)) k)).
Definition CALLSITE (j : nat) (P0 : sst) (specs : sst -> list (vop * Z * rkind)) (tb : sst -> lin) (k : MCH) : MCH :=
  NODE (HDEC h4_dec) (NODE (HPSR (fun S => Some (Y4 S)))
  (MSplitR 39 0 (NODE (HREPL h4_lo) (CALLSITE0 j P0 specs tb k))
  (MSplitR 39 1022 (CARVE4 (CS_PRE (SITE j P0 specs (CS_POST tb (REST4 k)))))
                   (NODE (HREPL h4_hi) (CALLSITE0 j P0 specs tb k))))).
(* [comment removed for export] *)
Definition fsh_piece (k : Z) (S : sst) : lin := laddc (rgk S 24) (8 * k).
Definition FSH_RW (k : Z) (cont : MCH) : MCH :=
  SURG (SRetype (fun S => retype_at S (fsh_piece k S) RT)) (SURG (SRetype (fun S => retype_at S (fsh_piece k S) RW)) cont).
(* [comment removed for export] *)
Definition CALLSITEI (j : nat) (P0 : sst) (specs : sst -> list (vop * Z * rkind)) (tb : sst -> lin) (k : MCH) : MCH := CALLSITE0 j P0 specs tb k.
