(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image FP.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit D_iface D_defs D_libiface Lept_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pix_cells_rc (v : pixv) (rc : Z) : list cell :=
  [C4 (Z_to_bv 64 (p_w v)); C4 (Z_to_bv 64 (p_h v)); C4 (Z_to_bv 64 (p_d v)); C4 (Z_to_bv 64 (p_spp v)); C4 (Z_to_bv 64 (p_wpl v));
   C4 (Z_to_bv 64 rc); C4 (Z_to_bv 64 (p_xres v)); C4 (Z_to_bv 64 (p_yres v)); C4 (Z_to_bv 64 (p_inf v)); C4 (Z_to_bv 64 (p_spec v));
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (p_cmap v)); C8 (Z_to_bv 64 (p_data v))].
(* [comment removed for export] *)
Definition pix_obj_rc (live : list (Z * Z)) (m : mem) (pix : Z) (v : pixv) (cv : cmapv) (rc : Z) : Prop :=
  rw_cells asegs m pix (pix_cells_rc v rc) /\ chunk live pix 64 /\ pix_hdr_ok v
  /\ (p_data v = 0 \/ (chunk live (p_data v) (rsize v) /\ p_data v <> pix))
  /\ (p_cmap v = 0 \/ (cmap_obj live m (p_cmap v) cv /\ p_cmap v <> pix /\ c_arr cv <> pix
                        /\ p_cmap v <> p_data v /\ c_arr cv <> p_data v)).
(* [comment removed for export] *)
Definition pv_res (vd vs : pixv) : pixv :=
  mkPixv (p_w vd) (p_h vd) (p_d vd) (p_spp vd) (p_wpl vd) (p_xres vs) (p_yres vs) (p_inf vd) (p_spec vd) (p_cmap vd) (p_data vd).
Definition pv_inf (vd vs : pixv) : pixv :=
  mkPixv (p_w vd) (p_h vd) (p_d vd) (p_spp vd) (p_wpl vd) (p_xres vd) (p_yres vd) (p_inf vs) (p_spec vd) (p_cmap vd) (p_data vd).
(* [comment removed for export] *)
Definition cmap_nz (v : pixv) (cv : cmapv) : Prop := p_cmap v = 0 \/ 1 <= c_n cv.
